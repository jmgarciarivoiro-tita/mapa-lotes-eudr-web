/* Mapa de Lotes · EUDR — web conectada a Supabase (esquema eudr).
 * La web solo carga, renombra y borra lotes. Los resultados los escribe el worker (worker.py) y llegan en tiempo real.
 */
(function () {
  'use strict';
  const CFG = window.MAPA_LOTES_CONFIG || {};
  const $ = s => document.querySelector(s);
  const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  const fmt = (n, d = 1) => Number(n || 0).toLocaleString('es-AR', { maximumFractionDigits: d, minimumFractionDigits: d });
  const fdt = s => (s ? new Date(s).toLocaleString('es-AR', { dateStyle: 'short', timeStyle: 'short' }) : '—');
  const SEM = {
    verde: { label: 'Apto EUDR (preliminar)', color: '#2e7d32' },
    amarillo: { label: 'Revisar', color: '#d39e00' },
    rojo: { label: 'No apto EUDR', color: '#c62828' },
    pend: { label: 'Analizando…', color: '#78909c' },
    error: { label: 'Error de análisis', color: '#8e1c1c' },
  };
  const ACCION = {
    verde: 'Puede ofrecerse con cláusula EUDR/VISEC. Guardar la evidencia y mantener el monitoreo.',
    amarillo: 'Revisión de un analista con imagen de alta resolución antes de habilitar la cláusula EUDR.',
    rojo: 'No habilitar la soja de este lote para contratos EUDR. Segregar en acopio y avisar al comercial.',
  };
  const COLS = 'id,nombre,productor,origen,geojson,area_ha,estado,semaforo,motivos,bosque_2020,perdida,estado_actual,campanias,ndvi_info,version,error,eudr_at,ndvi_at,proximo_monitoreo,created_by,created_at,logistica';
  const MAX_IMPORT = 300;

  if (!CFG.supabaseUrl || !CFG.supabaseAnonKey || !window.supabase) {
    document.body.innerHTML = '<p style="padding:20px;font-family:sans-serif">Falta config.js (supabaseUrl / supabaseAnonKey).</p>';
    return;
  }
  const sb = window.supabase.createClient(CFG.supabaseUrl, CFG.supabaseAnonKey, { db: { schema: 'eudr' } });

  let me = null, lotes = new Map(), selectedId = null, chart = null, map = null, group = null, channel = null;
  let acopios = [], acopioLayer = null, rutaLayer = null, semFiltro = null;
  const acopioMk = new Map();
  const layerById = new Map(), obsCache = new Map();

  // ---------- utilidades ----------
  let toastTimer = null;
  function toast(msg, kind) {
    const el = $('#toast'); el.textContent = msg; el.className = 'toast show ' + (kind || '');
    clearTimeout(toastTimer); toastTimer = setTimeout(() => { el.className = 'toast'; }, Math.min(12000, 4500 + String(msg).length * 30));
  }
  const semKey = l => (l.estado === 'error' ? 'error' : (l.semaforo || 'pend'));
  const enProceso = l => ['pendiente', 'procesando'].includes(l.estado);
  function decYear(iso) { const d = new Date(iso + 'T12:00:00'); const y = d.getFullYear(); return y + (d - new Date(y, 0, 1)) / (365.25 * 864e5); }
  function decToDate(t) { const y = Math.floor(t); return new Date(y, 0, 1 + Math.round((t - y) * 365)).toLocaleDateString('es-AR'); }

  // ---------- geometrías ----------
  function normRing(ring) {
    const out = [];
    for (const p of ring || []) {
      if (!Array.isArray(p) || p.length < 2) continue;
      const lon = Number(p[0]), lat = Number(p[1]);
      if (!isFinite(lon) || !isFinite(lat) || lon < -180 || lon > 180 || lat < -90 || lat > 90) throw new Error('coordenadas fuera de rango');
      const q = [Math.round(lon * 1e7) / 1e7, Math.round(lat * 1e7) / 1e7];
      if (!out.length || out[out.length - 1][0] !== q[0] || out[out.length - 1][1] !== q[1]) out.push(q);
    }
    if (out.length && (out[0][0] !== out[out.length - 1][0] || out[0][1] !== out[out.length - 1][1])) out.push(out[0].slice());
    if (out.length < 4) throw new Error('polígono con menos de 3 vértices');
    return out;
  }
  function normalizeGeometry(g) {
    if (g && g.type === 'Feature') g = g.geometry;
    if (!g) throw new Error('sin geometría');
    if (g.type === 'Polygon') return { type: 'Polygon', coordinates: g.coordinates.map(normRing) };
    if (g.type === 'MultiPolygon') {
      const ps = g.coordinates.map(p => p.map(normRing));
      return ps.length === 1 ? { type: 'Polygon', coordinates: ps[0] } : { type: 'MultiPolygon', coordinates: ps };
    }
    throw new Error(`tipo ${g.type} no soportado`);
  }

  // ---------- importación KML / KMZ / GeoJSON ----------
  const byTag = (el, t) => Array.from(el.getElementsByTagNameNS('*', t));
  const parseCoords = txt => String(txt || '').trim().split(/\s+/).map(s => s.split(',').map(Number)).filter(p => p.length >= 2 && isFinite(p[0]) && isFinite(p[1]));
  function parseKML(text) {
    const doc = new DOMParser().parseFromString(text, 'application/xml');
    if (doc.getElementsByTagName('parsererror').length) throw new Error('KML inválido');
    const out = []; let skipped = 0;
    for (const pm of byTag(doc, 'Placemark')) {
      const nameEl = Array.from(pm.children).find(c => c.localName === 'name');
      const polys = byTag(pm, 'Polygon').map(p => {
        const ob = byTag(p, 'outerBoundaryIs')[0]; const oc = ob && byTag(ob, 'coordinates')[0];
        if (!oc) return null;
        const rings = [parseCoords(oc.textContent)];
        byTag(p, 'innerBoundaryIs').forEach(ib => { const c = byTag(ib, 'coordinates')[0]; if (c) rings.push(parseCoords(c.textContent)); });
        return rings;
      }).filter(Boolean);
      if (!polys.length) { skipped++; continue; }
      out.push({ nombre: nameEl ? nameEl.textContent.trim() : '', geometry: polys.length === 1 ? { type: 'Polygon', coordinates: polys[0] } : { type: 'MultiPolygon', coordinates: polys } });
    }
    return { feats: out, skipped };
  }
  function parseGeoJSON(obj) {
    const feats = obj.type === 'FeatureCollection' ? obj.features : obj.type === 'Feature' ? [obj] : [{ type: 'Feature', geometry: obj, properties: {} }];
    const out = []; let skipped = 0;
    for (const f of feats || []) {
      const g = f && f.geometry, p = (f && f.properties) || {};
      if (!g || !['Polygon', 'MultiPolygon'].includes(g.type)) { skipped++; continue; }
      out.push({ nombre: p.nombre || p.name || p.Name || p.ProductionPlace || '', productor: p.productor || p.ProducerName || '', geometry: g });
    }
    return { feats: out, skipped };
  }
  // lee un archivo y devuelve sus poligonos. Acepta KML, KMZ (con uno o varios .kml), GeoJSON y ZIP con cualquiera de ellos.
  const MAX_ENTRADAS_ZIP = 500;
  function tipoDe(nombre) { const n = nombre.toLowerCase(); return n.endsWith('.kmz') ? 'kmz' : n.endsWith('.kml') ? 'kml' : (n.endsWith('.geojson') || n.endsWith('.json')) ? 'geojson' : n.endsWith('.zip') ? 'zip' : ''; }
  function textoSeguro(t) { if (t.length > 60e6) throw new Error('contenido demasiado grande'); return t; }
  async function leerZip(data, nombre, prof) {
    if (prof > 2) throw new Error('demasiados niveles de archivos comprimidos');
    const zip = await JSZip.loadAsync(data);
    const ents = Object.values(zip.files).filter(f => !f.dir && !/(^|\/)(__MACOSX|\.)/.test(f.name) && tipoDe(f.name) && (prof === 0 || tipoDe(f.name) !== 'zip'));
    if (ents.length > MAX_ENTRADAS_ZIP) throw new Error(`demasiados archivos dentro (${ents.length})`);
    const out = { feats: [], skipped: 0 };
    for (const f of ents) {
      const t = tipoDe(f.name), base = f.name.split('/').pop().replace(/\.[^.]+$/, '');
      let r;
      if (t === 'kml') r = parseKML(textoSeguro(await f.async('text')));
      else if (t === 'geojson') r = parseGeoJSON(JSON.parse(textoSeguro(await f.async('text'))));
      else if (t === 'kmz' || t === 'zip') r = await leerZip(await f.async('arraybuffer'), f.name, prof + 1);
      else continue;
      if (tipoDe(nombre) === 'zip') r.feats.forEach((x, k) => { if (!x.archivo) { x.archivo = base; if (!String(x.nombre || '').trim()) x.nombre = `${base} ${k + 1}`; } });
      out.feats.push(...r.feats); out.skipped += r.skipped;
    }
    if (!ents.length) throw new Error(prof === 0 && tipoDe(nombre) === 'kmz' ? 'el KMZ no contiene un .kml' : 'el ZIP no contiene KML, KMZ ni GeoJSON');
    return out;
  }
  async function leerArchivo(file) {
    if (file.size > 20e6) throw new Error('archivo mayor a 20 MB');
    const t = tipoDe(file.name);
    if (t === 'kmz' || t === 'zip') return leerZip(file, file.name, 0);
    if (t === 'kml') return parseKML(await file.text());
    if (t === 'geojson') return parseGeoJSON(JSON.parse(await file.text()));
    throw new Error('formato no soportado (KML, KMZ, GeoJSON o ZIP)');
  }
  // huella de la geometria para detectar lotes repetidos (mismo poligono ya cargado)
  function huella(g) {
    try { const n = normalizeGeometry(g); return n.type + JSON.stringify(n.coordinates, (k, v) => (typeof v === 'number' ? Math.round(v * 1e6) : v)); }
    catch (e) { return null; }
  }
  let importando = false;
  async function importar(files) {
    files = files.filter(Boolean);
    if (!files.length) return;
    if (importando) return toast('Ya hay una carga en curso. Esperá a que termine.', 'warn');
    importando = true;
    try {
      const filas = []; let skipped = 0, dup = 0; const errores = [], porArchivo = [];
      const vistas = new Set([...lotes.values()].map(l => huella(l.geojson)).filter(Boolean));
      for (let i = 0; i < files.length; i++) {
        const file = files[i];
        if (files.length > 1) toast(`Leyendo archivo ${i + 1} de ${files.length}: ${file.name}`);
        try {
          const r = await leerArchivo(file);
          skipped += r.skipped; let n = 0;
          r.feats.forEach((f, j) => {
            try {
              const geo = normalizeGeometry(f.geometry), h = huella(geo);
              if (h && vistas.has(h)) { dup++; return; }
              if (h) vistas.add(h);
              const base = f.archivo || file.name.replace(/\.[^.]+$/, '');
              filas.push({
                nombre: (String(f.nombre || '').trim() || `${base} ${j + 1}`).slice(0, 120),
                productor: String(f.productor || '').trim().slice(0, 120) || null,
                origen: `Archivo ${file.name}${f.archivo && f.archivo !== file.name.replace(/\.[^.]+$/, '') ? ' › ' + f.archivo : ''}`.slice(0, 200),
                geojson: geo,
              });
              n++;
            } catch (e) { skipped++; }
          });
          porArchivo.push(`${file.name}: ${n}`);
        } catch (e) { errores.push(`${file.name}: ${e.message}`); }
      }
      if (!filas.length) {
        toast(errores.length ? 'No se pudo importar: ' + errores.join(' · ')
          : dup ? `Todos los polígonos ya estaban cargados (${dup} repetido(s)).` : 'Los archivos no tenían polígonos (los puntos se omiten).', errores.length ? 'err' : 'warn');
        return;
      }
      if (filas.length > MAX_IMPORT) { skipped += filas.length - MAX_IMPORT; filas.length = MAX_IMPORT; }
      await insertar(filas, skipped, { dup, errores, archivos: files.length });
    } finally { importando = false; }
  }
  async function insertar(filas, skipped = 0, info = {}) {
    const data = [];
    for (let i = 0; i < filas.length; i += 100) {
      const r = await sb.from('lotes').insert(filas.slice(i, i + 100)).select(COLS);
      if (r.error) { toast(`No se pudieron guardar ${data.length ? 'todos ' : ''}los lotes: ${r.error.message}${data.length ? ` (se guardaron ${data.length})` : ''}`, 'err'); break; }
      data.push(...r.data);
    }
    if (!data.length) return;
    data.forEach(upsertLocal);
    renderList();
    const ids = data.map(d => d.id);
    const b = L.featureGroup(ids.map(id => layerById.get(id)).filter(Boolean));
    if (b.getLayers().length) map.fitBounds(b.getBounds(), { padding: [50, 50], maxZoom: 15 });
    if (ids[0]) select(ids[0], false);
    const extra = [skipped ? `${skipped} omitido(s)` : '', info.dup ? `${info.dup} repetido(s) no se volvieron a cargar` : '', info.errores && info.errores.length ? `con error: ${info.errores.join(' · ')}` : ''].filter(Boolean).join(', ');
    toast(`${data.length} lote(s) cargado(s)${info.archivos > 1 ? ` desde ${info.archivos} archivos` : ''}${extra ? '; ' + extra : ''}. El semáforo aparece en segundos.`, info.errores && info.errores.length ? 'warn' : '');
  }

  // ---------- mapa ----------
  function initMap() {
    map = L.map('map', { minZoom: 3, maxZoom: 19 }).setView([-31.5, -61.5], 6);
    const osm = L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', { maxZoom: 19, attribution: '© OpenStreetMap' });
    const sat = L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', { maxZoom: 19, attribution: 'Imagen © Esri, Maxar, Earthstar Geographics' });
    sat.addTo(map);
    L.control.layers({ 'Satélite': sat, 'Mapa': osm }, {}, { position: 'topright' }).addTo(map);
    group = L.featureGroup().addTo(map);
    map.pm.setLang('es');
    map.pm.setGlobalOptions({ allowSelfIntersection: false, snappable: true, pathOptions: { color: '#1565c0', weight: 2 } });
    map.pm.addControls({ position: 'topleft', drawMarker: false, drawCircleMarker: false, drawPolyline: false, drawCircle: false, drawText: false,
      drawRectangle: true, drawPolygon: true, editMode: false, dragMode: false, cutPolygon: false, removalMode: false, rotateMode: false });
    map.on('pm:create', async e => {
      const gj = e.layer.toGeoJSON(); map.removeLayer(e.layer);
      try { await insertar([{ nombre: `Lote ${lotes.size + 1}`, productor: null, origen: 'Dibujado en el mapa', geojson: normalizeGeometry(gj.geometry) }]); }
      catch (err) { toast('No se pudo crear el lote: ' + err.message, 'err'); }
    });
    const el = $('#map');
    ['dragenter', 'dragover'].forEach(ev => el.addEventListener(ev, e => { e.preventDefault(); el.classList.add('drop'); }));
    ['dragleave', 'drop'].forEach(ev => el.addEventListener(ev, e => { e.preventDefault(); el.classList.remove('drop'); }));
    el.addEventListener('drop', e => { const f = Array.from(e.dataTransfer?.files || []); if (f.length) importar(f); });
  }
  function styleFor(l) {
    const c = SEM[semKey(l)].color, sel = l.id === selectedId;
    return { color: sel ? '#40c4ff' : c, weight: sel ? 3.5 : 2.4, fillColor: c, fillOpacity: sel ? 0.25 : 0.18, dashArray: enProceso(l) ? '6 4' : null, pmIgnore: true };
  }
  function drawLayer(l) {
    const prev = layerById.get(l.id);
    if (prev) group.removeLayer(prev);
    const lyr = L.geoJSON({ type: 'Feature', geometry: l.geojson, properties: {} }, { pmIgnore: true }).getLayers()[0];
    if (!lyr) return;
    lyr.setStyle(styleFor(l));
    lyr.bindTooltip(() => esc(l.nombre), { sticky: true, direction: 'top', className: 'lote-tip' });
    lyr.on('click', () => select(l.id, false));
    lyr.addTo(group); layerById.set(l.id, lyr);
  }

  // ---------- datos ----------
  function upsertLocal(row) {
    const prev = lotes.get(row.id);
    if (prev && prev.ndvi_at !== row.ndvi_at) obsCache.delete(row.id);
    const l = Object.assign(prev || {}, row);
    lotes.set(l.id, l);
    drawLayer(l);
    return l;
  }
  function removeLocal(id) {
    const lyr = layerById.get(id); if (lyr) group.removeLayer(lyr);
    layerById.delete(id); lotes.delete(id); obsCache.delete(id);
    if (selectedId === id) selectedId = null;
  }
  async function cargarTodo() {
    const out = []; const step = 1000;
    for (let from = 0; ; from += step) {
      const { data, error } = await sb.from('lotes').select(COLS).order('created_at', { ascending: false }).range(from, from + step - 1);
      if (error) { toast('No se pudieron leer los lotes: ' + error.message, 'err'); break; }
      out.push(...data); if (data.length < step) break;
    }
    lotes.clear(); group.clearLayers(); layerById.clear();
    out.forEach(upsertLocal);
    renderList(); renderDetail();
    if (out.length) map.fitBounds(group.getBounds(), { padding: [40, 40], maxZoom: 14 });
  }
  function suscribir() {
    if (channel) sb.removeChannel(channel);
    channel = sb.channel('eudr-cambios')
      .on('postgres_changes', { event: '*', schema: 'eudr', table: 'lotes' }, async p => {
        if (p.eventType === 'DELETE') { removeLocal(p.old.id); renderList(); renderDetail(); return; }
        const { data } = await sb.from('lotes').select(COLS).eq('id', p.new.id).maybeSingle();
        if (!data) return;
        const antes = lotes.get(data.id);
        const cambioSem = antes && antes.semaforo !== data.semaforo && data.semaforo;
        upsertLocal(data); renderList();
        if (selectedId === data.id) renderDetail();
        if (cambioSem) toast(`${data.nombre}: ${SEM[data.semaforo].label}`);
      })
      .on('postgres_changes', { event: '*', schema: 'eudr', table: 'worker_estado' }, p => pintarWorker(p.new))
      .subscribe();
  }
  async function leerWorker() {
    const { data } = await sb.from('worker_estado').select('*').eq('id', 1).maybeSingle();
    pintarWorker(data);
  }
  let workerData = null;
  function pintarWorker(w) {
    if (w) workerData = w;
    const el = $('#workerPill'); const v = workerData && workerData.visto_at ? new Date(workerData.visto_at) : null;
    const seg = v ? (Date.now() - v) / 1000 : Infinity;
    const pend = [...lotes.values()].filter(enProceso).length;
    if (seg < 120) { el.className = 'pill on'; el.textContent = 'Worker en línea' + (pend ? ` · ${pend} en cola` : ''); }
    else { el.className = 'pill warn'; el.textContent = v ? `Worker sin conexión desde ${fdt(v)}` : 'Worker sin conexión'; }
    el.title = v ? `Último latido: ${fdt(v)} · ${workerData.host || ''} · ${workerData.version || ''}` : 'El worker todavía no se conectó';
  }
  setInterval(() => pintarWorker(), 30000);

  // ---------- panel: lista ----------
  // lotes que pasan el filtro de texto (lote, productor o acopio mas cercano), en el orden de la lista
  function filtrados() {
    const q = ($('#filtro').value || '').toLowerCase().trim();
    return [...lotes.values()].filter(l => (!semFiltro || l.semaforo === semFiltro) && (!q || (l.nombre || '').toLowerCase().includes(q) || (l.productor || '').toLowerCase().includes(q)
        || (cercano(l)?.nombre || '').toLowerCase().includes(q)))
      .sort((a, b) => ({ rojo: 0, amarillo: 1 }[a.semaforo] ?? 2) - ({ rojo: 0, amarillo: 1 }[b.semaforo] ?? 2) || (a.nombre || '').localeCompare(b.nombre || ''));
  }
  function indicadores(lista) {
    const cnt = { verde: 0, amarillo: 0, rojo: 0, pend: 0 }; let ha = 0;
    lista.forEach(l => { if (cnt[l.semaforo] !== undefined) cnt[l.semaforo]++; else cnt.pend++; ha += l.area_ha || 0; });
    return { n: lista.length, ha, ...cnt };
  }
  function renderList() {
    const arr = [...lotes.values()];
    const vis = filtrados();
    const k = indicadores(vis);
    const q = ($('#filtro').value || '').trim();
    $('#summary').innerHTML = arr.length ? `
      <button type="button" class="kpi" data-sem="" title="Ver todos los semáforos"><b>${k.n}</b><span>lotes</span></button>
      <button type="button" class="kpi" data-sem="" title="Ver todos los semáforos"><b>${fmt(k.ha, 0)}</b><span>ha</span></button>
      <button type="button" class="kpi v ${semFiltro === 'verde' ? 'on' : ''}" data-sem="verde" title="Filtrar aptos" aria-pressed="${semFiltro === 'verde'}"><b>${k.verde}</b><span>aptos</span></button>
      <button type="button" class="kpi a ${semFiltro === 'amarillo' ? 'on' : ''}" data-sem="amarillo" title="Filtrar a revisar" aria-pressed="${semFiltro === 'amarillo'}"><b>${k.amarillo}</b><span>revisar</span></button>
      <button type="button" class="kpi r ${semFiltro === 'rojo' ? 'on' : ''}" data-sem="rojo" title="Filtrar no aptos" aria-pressed="${semFiltro === 'rojo'}"><b>${k.rojo}</b><span>no aptos</span></button>` : '';
    $('#summary').querySelectorAll('.kpi').forEach(el => el.addEventListener('click', () => {
      const s = el.dataset.sem || null; semFiltro = s && semFiltro !== s ? s : null; renderList();
    }));
    $('#filtroInfo').innerHTML = arr.length && (q || semFiltro) ? `Indicadores del filtro: ${vis.length} de ${arr.length} lotes${semFiltro ? ` · solo <b>${esc(SEM[semFiltro].label)}</b> <button type="button" class="lnk" id="bQuitarSem">quitar</button>` : ''}` : (arr.length ? 'Tocá un indicador de color para filtrar por semáforo.' : '');
    $('#bQuitarSem')?.addEventListener('click', () => { semFiltro = null; renderList(); });
    const list = $('#list');
    if (!arr.length) {
      list.innerHTML = `<div class="empty"><p><b>Todavía no hay lotes.</b></p><ol>
        <li>Subí un archivo <b>KML, KMZ o GeoJSON</b> (o arrastralo al mapa).</li>
        <li>O dibujá el lote con las herramientas de la izquierda.</li></ol>
        <p>El semáforo aparece solo en segundos; el historial satelital, en unos minutos.</p></div>`;
      pintarWorker(); return;
    }
    list.innerHTML = vis.map(l => {
      const k = semKey(l);
      const st = enProceso(l) ? '<span class="state"><i class="spin"></i> analizando</span>'
        : l.estado === 'ndvi_procesando' ? '<span class="state"><i class="spin"></i> NDVI</span>'
        : l.estado === 'error' ? '<span class="state err">error</span>' : '';
      return `<button class="row ${l.id === selectedId ? 'sel' : ''}" data-id="${esc(l.id)}">
        <i class="dot" style="background:${SEM[k].color}"></i>
        <span class="rn">${esc(l.nombre)}<small>${esc(l.productor || 'Sin productor')}${cercano(l) ? ` · ${esc(cercano(l).nombre.split(' - ')[0])} ${fmt(cercano(l).km_total, 0)} km` : ''}</small></span>
        ${st}<span class="rh">${fmt(l.area_ha, 0)} ha</span></button>`;
    }).join('') || '<p class="muted">Sin resultados para la búsqueda.</p>';
    list.querySelectorAll('.row').forEach(b => b.addEventListener('click', () => select(b.dataset.id, true)));
    pintarWorker();
  }
  function select(id, fit) {
    selectedId = id;
    lotes.forEach(l => layerById.get(l.id)?.setStyle(styleFor(l)));
    const lyr = layerById.get(id);
    if (lyr) { lyr.bringToFront(); if (fit) map.fitBounds(lyr.getBounds(), { padding: [60, 60], maxZoom: 16 }); }
    renderList(); renderDetail();
    if (window.innerWidth < 900) $('#detail').scrollIntoView({ behavior: 'smooth', block: 'start' });
  }

  // ---------- logistica: acopios ----------
  function cercano(l) {
    const g = l && l.logistica;
    if (!g || !Array.isArray(g.acopios)) return null;
    return g.acopios.find(a => a.id === g.mas_cercano && a.km_total != null) || null;
  }
  function logisticaHtml(l) {
    const g = l.logistica;
    if (!g) return `<h3>Distancia a acopios</h3><div class="accion"><i class="spin"></i> Calculando distancias por ruta a los acopios…</div>`;
    const c = cercano(l);
    const filas = (g.acopios || []).map(a => {
      const top = a.id === g.mas_cercano;
      const err = a.km_total == null;
      return `<tr class="${top ? 'cerca' : ''}"><td>${esc(a.nombre)}${top ? ' <span class="tag-cerca">Más cercano</span>' : ''}<small>${esc([a.localidad, a.provincia].filter(Boolean).join(', '))}</small></td>
        <td>${err ? '—' : fmt(a.km_total, 0) + ' km'}</td><td>${err ? '—' : fmt(a.km_asfalto, 0)}</td><td>${err ? '—' : fmt(a.km_tierra, 1)}</td>
        <td>${err ? '<span class="muted">sin ruta</span>' : a.minutos + ' min'}</td></tr>`;
    }).join('');
    const eng = c && c.enganche_m > 500 ? `<p class="cap">El lote está a ${fmt(c.enganche_m / 1000, 1)} km del camino más cercano registrado en el mapa: se sumó como acceso.</p>` : '';
    return `<h3>Distancia a acopios</h3>
      ${c ? `<div class="cercano"><b>Acopio más cercano: ${esc(c.nombre)}</b><span>${fmt(c.km_total, 0)} km por ruta · ${fmt(c.km_asfalto, 0)} km asfalto + ${fmt(c.km_tierra, 1)} km tierra · ~${c.minutos} min</span></div>`
        : '<div class="accion">No se pudo calcular la ruta a los acopios. Se reintenta solo.</div>'}
      <div class="tabla-scroll"><table class="chk dist"><tr class="th"><td>Acopio</td><td>Ruta</td><td>Asfalto</td><td>Tierra</td><td>Tiempo</td></tr>${filas}</table></div>
      ${eng}<p class="cap">Ruta por camino priorizando rutas asfaltadas (nacionales y provinciales), desde un punto interior del lote. ${esc(g.motor || '')} · ${fdt(g.calculado_at)}. En caminos sin dato de superficie se asume tierra en vecinales y asfalto en rutas.</p>`;
  }
  async function cargarAcopios() {
    const { data, error } = await sb.from('acopios').select('id,nombre,localidad,provincia,lat,lon,activo').eq('activo', true).order('id');
    if (error) { console.warn('acopios', error.message); return; }
    acopios = data || [];
    if (acopioLayer) map.removeLayer(acopioLayer);
    acopioMk.clear();
    acopioLayer = L.layerGroup(acopios.map(a => {
      const mk = L.marker([a.lat, a.lon], { pmIgnore: true, interactive: true, icon: iconoSilo(false), zIndexOffset: 500, title: a.nombre, alt: 'Acopio ' + a.nombre })
        .bindTooltip(`${esc(a.nombre)} · ${esc(a.localidad || '')}`, { direction: 'top', offset: [0, -34] })
        .bindPopup(() => popupAcopio(a), { offset: [0, -30] });
      acopioMk.set(a.id, mk); return mk;
    })).addTo(map);
    marcarAcopioCercano(lotes.get(selectedId));
  }
  // marcador de acopio: pin con silos (azul; naranja si es el mas cercano al lote seleccionado)
  function iconoSilo(cerca) {
    const c = cerca ? '#e65100' : '#1565c0';
    const svg = `<svg width="34" height="42" viewBox="0 0 34 42" aria-hidden="true">
      <path d="M17 41C17 41 31 26.6 31 16.5A14 14 0 0 0 3 16.5C3 26.6 17 41 17 41Z" fill="${c}" stroke="#fff" stroke-width="2"/>
      <g fill="#fff"><path d="M8.5 12.6a4 2.6 0 0 1 8 0Z"/><rect x="8.5" y="13.2" width="8" height="12" rx=".6"/>
      <path d="M18 15.8l3.2-3 3.3 3Z"/><rect x="18" y="16.2" width="6.5" height="9" rx=".5"/></g>
      <g stroke="${c}" stroke-width=".9"><path d="M8.5 17.2h8M8.5 21.2h8M18 19.2h6.5M18 22.4h6.5"/></g></svg>`;
    return L.divIcon({ className: 'acopio-pin' + (cerca ? ' cerca' : ''), html: svg, iconSize: [34, 42], iconAnchor: [17, 41], popupAnchor: [0, -4] });
  }
  function popupAcopio(a) {
    const n = [...lotes.values()].filter(l => cercano(l)?.id === a.id);
    const ha = n.reduce((s, l) => s + (l.area_ha || 0), 0);
    return `<div class="acopio-pop"><b>${esc(a.nombre)}</b><span>${esc([a.localidad, a.provincia].filter(Boolean).join(', '))}</span><br>
      <span>Acopio más cercano de ${n.length} lote(s)${n.length ? ` · ${fmt(ha, 0)} ha` : ''}</span></div>`;
  }
  function marcarAcopioCercano(l) {
    const c = cercano(l);
    acopioMk.forEach((mk, id) => mk.setIcon(iconoSilo(!!c && c.id === id)));
  }
  function dibujarRuta(l) {
    if (rutaLayer) { map.removeLayer(rutaLayer); rutaLayer = null; }
    marcarAcopioCercano(l);
    const c = cercano(l);
    if (c && c.geometria && c.geometria.type === 'LineString') {
      rutaLayer = L.geoJSON(c.geometria, { pmIgnore: true, style: { color: '#1565c0', weight: 4, opacity: 0.8, dashArray: '8 6' } }).addTo(map);
    }
  }

  // ---------- panel: detalle ----------
  // tabla del chequeo EUDR (se usa en el panel y en el informe)
  function eudrTabla(l) {
    const a = l.area_ha || 0;
    const pct = v => (a ? fmt((v || 0) / a * 100, 1) + '%' : '–');
    const b = l.bosque_2020 || {}, p = l.perdida || {};
    const anios = Object.keys(p.perdida_post2020_por_anio || {}).sort();
    return `
      <h3>Chequeo EUDR</h3>
      <table class="chk">
        <tr><td>Bosque al 31/12/2020 <small>${esc(b.fuente || 'JRC GFC2020')}</small></td><td>${fmt(b.bosque_ha)} ha</td><td>${pct(b.bosque_ha)}</td></tr>
        <tr><td class="ind">· de eso, en el borde (30 m)</td><td>${fmt(b.bosque_en_borde_ha)} ha</td><td>${pct(b.bosque_en_borde_ha)}</td></tr>
        <tr class="${p.perdida_post2020_ha > 0 ? 'hl' : ''}"><td>Pérdida posterior a 2020 <small>${esc(p.fuente || 'Hansen GFC')}</small></td><td>${fmt(p.perdida_post2020_ha)} ha</td><td>${anios.length ? esc(anios.join(', ')) : '—'}</td></tr>
        <tr><td class="ind">· pérdida 2001–2020 (antes del corte)</td><td>${fmt(p.perdida_2001_2020_ha)} ha</td><td></td></tr>
        <tr><td>OTBN Ley 26.331</td><td colspan="2">no consultado todavía</td></tr>
      </table>
      <ul class="motivos">${(l.motivos || []).map(m => `<li><i style="background:${(SEM[m.nivel] || SEM.pend).color}"></i>${esc(m.texto)}</li>`).join('')}</ul>
      <div class="accion"><b>Acción sugerida:</b> ${esc(ACCION[l.semaforo] || '')}</div>`;
  }
  function capNdvi(l) {
    const ni = l.ndvi_info || {};
    return l.ndvi_at ? `${esc(ni.fechas_validas ?? '')} fechas válidas de ${esc(ni.fechas_candidatas ?? '')} · última imagen ${esc(ni.ultima_escena || '—')} · próximo control ${fdt(l.proximo_monitoreo)}. ${esc(ni.criterio || '')}` : 'El historial aparece cuando termina la descarga.';
  }
  function campaniasHtml(l) {
    const camps = Array.isArray(l.campanias) ? l.campanias : [];
    return camps.length ? `<h3>Campañas detectadas <small class="muted">(estimación por fecha de los picos)</small></h3>
        <table class="chk camp">${camps.map(c => `<tr><td>${esc(c.campania)}</td><td>${esc(c.cultivo_estimado)}</td></tr>`).join('')}</table>` : '';
  }
  async function obsDe(l) {
    if (obsCache.has(l.id)) return obsCache.get(l.id);
    const { data, error } = await sb.from('ndvi_obs').select('fecha,ndvi,p25,p75,pct_verde').eq('lote_id', l.id)
      .not('ndvi', 'is', null).is('descarte', null).order('fecha').limit(5000);
    if (error) throw error;
    obsCache.set(l.id, data); return data;
  }
  function renderDetail() {
    const box = $('#detail');
    if (chart) { chart.destroy(); chart = null; }
    const l = lotes.get(selectedId);
    dibujarRuta(l);
    if (!l) { box.hidden = true; box.innerHTML = ''; return; }
    box.hidden = false;
    const k = semKey(l), s = SEM[k], a = l.area_ha || 0;
    const b = l.bosque_2020 || {}, p = l.perdida || {};
    const ni = l.ndvi_info || {}, ea = l.estado_actual, camps = Array.isArray(l.campanias) ? l.campanias : [];
    const propio = me && l.created_by === me.id;
    const eudrHtml = l.semaforo ? eudrTabla(l)
      : l.estado === 'error' ? `<div class="accion"><b>No se pudo analizar.</b> ${esc(l.error || '')}</div>`
      : `<div class="accion"><i class="spin"></i> Analizando bosque 2020 y pérdida de cobertura… suele tardar segundos${workerData && (Date.now() - new Date(workerData.visto_at)) / 1000 > 120 ? ' (el worker está sin conexión: se procesa cuando vuelva)' : ''}.</div>`;
    const ndviEstado = ni.estado === 'procesando' ? `<div class="accion"><i class="spin"></i> Descargando historial satelital${ni.avance ? ` (${esc(ni.avance)} imágenes)` : ''}…</div>`
      : ni.estado === 'error' ? `<div class="accion">Error en el último monitoreo: ${esc(ni.error || '')}. Se reintenta solo.</div>` : '';
    box.innerHTML = `
      <div class="d-head">
        <input class="d-name" id="fNombre" value="${esc(l.nombre)}" maxlength="120" aria-label="Nombre del lote" ${propio ? '' : 'disabled'}>
        <div class="badges"><div class="badge" style="--c:${s.color}"><i></i>${esc(s.label)}</div></div>
      </div>
      <div class="grid2">
        <label>Productor<input id="fProd" value="${esc(l.productor || '')}" maxlength="120" placeholder="Razón social o CUIT" ${propio ? '' : 'disabled'}></label>
        <div class="kv"><span>Superficie</span><b>${fmt(a, 1)} ha</b></div>
        <div class="kv"><span>Geolocalización EUDR</span><b>${a > 4 ? 'Polígono requerido (&gt; 4 ha) ✓' : 'Alcanza con un punto (≤ 4 ha)'}</b></div>
      </div>
      ${eudrHtml}
      ${logisticaHtml(l)}
      <h3>Seguimiento satelital · NDVI</h3>
      ${ndviEstado}
      ${ea ? `<div class="ndvi-meta"><span class="${ea.lote_dividido ? 'warn2' : ''}">Hoy (${esc(ea.ultima_fecha)}): ${esc(ea.texto)}</span></div>` : ''}
      <div class="chart-box"><canvas id="ndviChart" aria-label="Serie NDVI del lote"></canvas></div>
      <p class="cap" id="ndviCap">${capNdvi(l)}</p>
      ${campaniasHtml(l)}
      <details class="evid"><summary>Evidencia del análisis</summary>
        <div>Semáforo: ${fdt(l.eudr_at)} · NDVI: ${fdt(l.ndvi_at)} · Versión: <code>${esc(l.version || '—')}</code></div>
        <div>Fuentes: ${esc(b.fuente || '—')} · ${esc(p.fuente || '—')} · ${esc(ni.fuente || '—')}</div>
        <div>Origen del polígono: ${esc(l.origen || '—')} · Cargado ${fdt(l.created_at)}</div>
      </details>
      <div class="d-actions">
        <button class="btn" id="bZoom">Ver en el mapa</button>
        ${propio ? '<span class="del-wrap" id="delWrap"><button class="btn danger" id="bDel">Eliminar</button></span>' : ''}
      </div>`;
    const guardar = async (campo, valor) => {
      const { error } = await sb.from('lotes').update({ [campo]: valor }).eq('id', l.id);
      if (error) toast('No se pudo guardar: ' + error.message, 'err');
    };
    $('#fNombre')?.addEventListener('change', e => { const v = e.target.value.trim().slice(0, 120); if (v) guardar('nombre', v); });
    $('#fProd')?.addEventListener('change', e => guardar('productor', e.target.value.trim().slice(0, 120) || null));
    $('#bZoom').addEventListener('click', () => { const lyr = layerById.get(l.id); if (lyr) map.fitBounds(lyr.getBounds(), { padding: [60, 60], maxZoom: 16 }); });
    $('#bDel')?.addEventListener('click', () => {
      $('#delWrap').innerHTML = '<span class="confirm">¿Eliminar este lote y su historial? <button class="btn danger" id="bDelOk">Sí, eliminar</button><button class="btn" id="bDelNo">No</button></span>';
      $('#bDelOk').addEventListener('click', async () => {
        const { error } = await sb.from('lotes').delete().eq('id', l.id);
        if (error) toast('No se pudo eliminar: ' + error.message, 'err'); else { removeLocal(l.id); renderList(); renderDetail(); }
      });
      $('#bDelNo').addEventListener('click', () => renderDetail());
    });
    if (l.ndvi_at) dibujarCurva(l);
  }

  const markers = {
    id: 'markers',
    afterDatasetsDraw(c, args, opts) {
      const { ctx, chartArea: ca, scales: { x } } = c;
      const line = (val, color, label, dash, bottom) => {
        if (val == null || val < x.min || val > x.max) return;
        const px = x.getPixelForValue(val);
        ctx.save(); ctx.strokeStyle = color; ctx.lineWidth = 1.3; ctx.setLineDash(dash);
        ctx.beginPath(); ctx.moveTo(px, ca.top); ctx.lineTo(px, ca.bottom); ctx.stroke();
        ctx.setLineDash([]); ctx.fillStyle = color; ctx.font = '600 10px Inter, system-ui, sans-serif';
        ctx.textAlign = px > ca.right - 100 ? 'right' : 'left';
        ctx.fillText(label, px + (ctx.textAlign === 'left' ? 4 : -4), bottom ? ca.bottom - 6 : ca.top + 10); ctx.restore();
      };
      line(2021.0, '#607d8b', 'Corte EUDR 31/12/2020', [3, 3], true);
      (opts.loss || []).forEach(y => line(y, '#c62828', `Pérdida ${Math.floor(y)}`, [5, 3], false));
    },
  };
  async function dibujarCurva(l) {
    let obs;
    try { obs = await obsDe(l); } catch (e) { $('#ndviCap').textContent = 'No se pudo leer la serie: ' + e.message; return; }
    if (selectedId !== l.id || !$('#ndviChart')) return;
    if (chart) chart.destroy();
    chart = new Chart($('#ndviChart'), cfgCurva(l, obs, false));
  }
  // configuracion del grafico NDVI (panel: interactivo · informe: imagen estatica)
  function cfgCurva(l, obs, impresion) {
    const pts = obs.map(o => ({ x: decYear(o.fecha), y: o.ndvi }));
    const hi = obs.filter(o => o.p75 != null).map(o => ({ x: decYear(o.fecha), y: Math.min(1, o.p75) }));
    const lo = obs.filter(o => o.p25 != null).map(o => ({ x: decYear(o.fecha), y: Math.max(0, o.p25) }));
    const loss = Object.keys((l.perdida || {}).perdida_post2020_por_anio || {}).map(Number).filter(y => ((l.perdida.perdida_post2020_por_anio[y]) || 0) >= 0.5).map(y => y + 0.5);
    return {
      type: 'scatter',
      data: { datasets: [
        { data: pts, showLine: true, pointRadius: 1.6, pointHoverRadius: 3, borderWidth: 1.5, borderColor: '#2e7d32', backgroundColor: '#2e7d32', tension: 0.15 },
        { data: hi, showLine: true, pointRadius: 0, borderWidth: 0, fill: false, tension: 0.15 },
        { data: lo, showLine: true, pointRadius: 0, borderWidth: 0, backgroundColor: 'rgba(46,125,50,.14)', fill: '-1', tension: 0.15 },
      ] },
      options: {
        animation: false, responsive: !impresion, maintainAspectRatio: false, devicePixelRatio: impresion ? 2 : undefined,
        interaction: { mode: 'nearest', axis: 'x', intersect: false },
        plugins: { legend: { display: false }, markers: { loss },
          tooltip: { filter: c => c.datasetIndex === 0, callbacks: { title: () => '', label: c => `${decToDate(c.parsed.x)} · NDVI ${c.parsed.y.toFixed(2)}` } } },
        scales: {
          x: { type: 'linear', min: 2020, max: Math.ceil(Math.max(2026.5, pts.at(-1)?.x || 0)), ticks: { stepSize: 1, autoSkip: false, maxRotation: 0, callback: v => (Number.isInteger(v) ? v : '') }, grid: { color: '#eef0ec' } },
          y: { min: 0, max: 1, ticks: { stepSize: 0.2 }, grid: { color: '#eef0ec' }, title: { display: true, text: 'NDVI' } },
        },
      },
      plugins: [markers],
    };
  }
  // dibuja la curva fuera de pantalla y la devuelve como imagen PNG (para el informe)
  function curvaPng(l, obs) {
    const host = document.createElement('div');
    host.style.cssText = 'position:fixed;left:-10000px;top:0;width:900px;height:300px';
    const cv = document.createElement('canvas'); cv.width = 900; cv.height = 300;
    host.appendChild(cv); document.body.appendChild(host);
    let url = '';
    try { const c = new Chart(cv, cfgCurva(l, obs, true)); url = c.toBase64Image('image/png'); c.destroy(); }
    catch (e) { console.warn('curva', e); }
    host.remove();
    return url;
  }

  // ---------- exportar ----------
  function exportGeoJSON() {
    return JSON.stringify({ type: 'FeatureCollection', features: [...lotes.values()].map(l => ({
      type: 'Feature', geometry: l.geojson,
      properties: { ProducerName: l.productor || null, ProducerCountry: 'AR', ProductionPlace: l.nombre, Area: Math.round((l.area_ha || 0) * 100) / 100,
        semaforo: l.semaforo || null, perdida_post2020_ha: l.perdida ? l.perdida.perdida_post2020_ha : null, analisis_fecha: l.eudr_at || null, version: l.version || null },
    })) }, null, 2);
  }
  $('#bExport').addEventListener('click', () => { if (!lotes.size) return toast('No hay lotes para exportar.', 'warn'); $('#exportTxt').value = exportGeoJSON(); $('#modal').hidden = false; });
  $('#bCopy').addEventListener('click', async () => { const ta = $('#exportTxt'); try { await navigator.clipboard.writeText(ta.value); toast('GeoJSON copiado.'); } catch (e) { ta.select(); toast('Seleccionado: copiá con Ctrl+C.', 'warn'); } });
  $('#bDownload').addEventListener('click', () => {
    const blob = new Blob([$('#exportTxt').value], { type: 'application/geo+json' }); const a = document.createElement('a');
    a.href = URL.createObjectURL(blob); a.download = `lotes_eudr_${new Date().toISOString().slice(0, 10)}.geojson`; a.click(); setTimeout(() => URL.revokeObjectURL(a.href), 2000);
  });
  $('#bClose').addEventListener('click', () => { $('#modal').hidden = true; });

  // ---------- informe (lo filtrado) ----------
  const SEMTXT = { verde: 'Apto EUDR (preliminar)', amarillo: 'Revisar', rojo: 'No apto EUDR' };
  function filasInforme(lista) {
    return lista.map(l => {
      const c = cercano(l), p = l.perdida || {}, b = l.bosque_2020 || {}, ea = l.estado_actual || {};
      const dist = {};
      ((l.logistica || {}).acopios || []).forEach(a => { dist[a.id] = a; });
      return { l, c, p, b, ea, dist };
    });
  }
  // lotes elegidos en el modal del informe (por defecto: todos los del filtro actual)
  let infLista = [];
  function infElegidos() {
    const ok = new Set([...document.querySelectorAll('#infLotes input[type=checkbox]:checked')].map(i => i.value));
    return infLista.filter(l => ok.has(String(l.id)));
  }
  function descFiltro() {
    const q = ($('#filtro').value || '').trim();
    const partes = [];
    if (q) partes.push('texto “' + q + '”');
    if (semFiltro) partes.push('semáforo: ' + (SEMTXT[semFiltro] || semFiltro));
    return partes.length ? partes.join(' · ') : 'sin filtro (todos los lotes)';
  }
  // contorno del lote como SVG (orientado al norte), para el informe
  function croquisSvg(l, color) {
    const g = l.geojson; if (!g) return '';
    const polys = g.type === 'Polygon' ? [g.coordinates] : g.type === 'MultiPolygon' ? g.coordinates : [];
    const pts = polys.flatMap(p => p[0] || []);
    if (!pts.length) return '';
    const lat0 = pts.reduce((s, p) => s + p[1], 0) / pts.length, kx = Math.cos(lat0 * Math.PI / 180);
    const xs = pts.map(p => p[0] * kx), ys = pts.map(p => p[1]);
    const minx = Math.min(...xs), maxx = Math.max(...xs), miny = Math.min(...ys), maxy = Math.max(...ys);
    const S = 150, pad = 20, esc2 = (S - 2 * pad) / Math.max(maxx - minx, maxy - miny, 1e-9);
    const ox = pad + ((S - 2 * pad) - (maxx - minx) * esc2) / 2, oy = pad + ((S - 2 * pad) - (maxy - miny) * esc2) / 2;
    const P = p => `${(ox + (p[0] * kx - minx) * esc2).toFixed(1)},${(oy + (maxy - p[1]) * esc2).toFixed(1)}`;
    const d = polys.map(p => p.map(r => 'M' + r.map(P).join('L') + 'Z').join('')).join('');
    return `<svg class="croquis" viewBox="0 0 ${S} ${S}" width="${S}" height="${S}" role="img" aria-label="Contorno del lote">
      <rect width="${S}" height="${S}" fill="#f6f7f4" rx="6"/><path d="${d}" fill="${color}" fill-opacity=".22" stroke="${color}" stroke-width="1.6" fill-rule="evenodd"/>
      <text x="${S - 12}" y="16" font-size="10" font-weight="700" fill="#5f6f66" text-anchor="middle">N</text><path d="M${S - 12} 20 l-3 7 h6z" fill="#5f6f66"/></svg>`;
  }
  function centroAprox(l) {
    const g = l.geojson; const polys = g && g.type === 'Polygon' ? [g.coordinates] : (g && g.coordinates) || [];
    const pts = polys.flatMap(p => p[0] || []); if (!pts.length) return null;
    const lon = (Math.min(...pts.map(p => p[0])) + Math.max(...pts.map(p => p[0]))) / 2, lat = (Math.min(...pts.map(p => p[1])) + Math.max(...pts.map(p => p[1]))) / 2;
    return `${lat.toFixed(5)}, ${lon.toFixed(5)}`;
  }
  // bloque completo de un lote: lo mismo que muestra el panel lateral
  function detalleInforme(l, png) {
    const s = SEM[semKey(l)], a = l.area_ha || 0, ni = l.ndvi_info || {}, ea = l.estado_actual, b = l.bosque_2020 || {}, p = l.perdida || {};
    const eudr = l.semaforo ? eudrTabla(l) : l.estado === 'error' ? `<div class="accion"><b>No se pudo analizar.</b> ${esc(l.error || '')}</div>` : '<div class="accion">Chequeo EUDR en proceso.</div>';
    return `<section class="lote">
      <div class="lhead"><div><h2>${esc(l.nombre)}</h2><span class="badge" style="--c:${s.color}"><i></i>${esc(s.label)}</span></div></div>
      <div class="lgrid">
        <div class="kvs">
          <div class="kv"><span>Productor</span><b>${esc(l.productor || '—')}</b></div>
          <div class="kv"><span>Superficie</span><b>${fmt(a, 1)} ha</b></div>
          <div class="kv"><span>Geolocalización EUDR</span><b>${a > 4 ? 'Polígono requerido (&gt; 4 ha) ✓' : 'Alcanza con un punto (≤ 4 ha)'}</b></div>
          <div class="kv"><span>Ubicación aprox. (lat, lon)</span><b>${esc(centroAprox(l) || '—')}</b></div>
        </div>
        ${croquisSvg(l, s.color)}
      </div>
      ${eudr}
      ${l.logistica ? logisticaHtml(l) : '<h3>Distancia a acopios</h3><div class="accion">Distancias todavía en cálculo.</div>'}
      <h3>Seguimiento satelital · NDVI</h3>
      ${ea ? `<div class="ndvi-meta"><span class="${ea.lote_dividido ? 'warn2' : ''}">Hoy (${esc(ea.ultima_fecha)}): ${esc(ea.texto)}</span></div>` : ''}
      ${png ? `<img class="curva" src="${png}" alt="Serie NDVI de ${esc(l.nombre)}">` : `<div class="accion">${l.ndvi_at ? 'No se pudo leer la serie NDVI.' : 'El historial satelital todavía se está descargando.'}</div>`}
      <p class="cap">${capNdvi(l)}</p>
      ${campaniasHtml(l)}
      <div class="evid"><b>Evidencia del análisis</b>
        <div>Semáforo: ${fdt(l.eudr_at)} · NDVI: ${fdt(l.ndvi_at)} · Versión: <code>${esc(l.version || '—')}</code></div>
        <div>Fuentes: ${esc(b.fuente || '—')} · ${esc(p.fuente || '—')} · ${esc(ni.fuente || '—')}</div>
        <div>Origen del polígono: ${esc(l.origen || '—')} · Cargado ${fdt(l.created_at)}</div>
      </div>
    </section>`;
  }
  const CSS_INFORME = `*{box-sizing:border-box}body{font:12px Inter,system-ui,Arial,sans-serif;color:#1d2a22;margin:24px auto;padding:0 24px;max-width:1040px;-webkit-print-color-adjust:exact;print-color-adjust:exact}
h1{font-size:18px;margin:0}h2{font-size:15px;margin:0 0 6px}h3{font-size:12.5px;margin:16px 0 6px}
.meta{color:#5f6f66;margin:4px 0 14px}.k{display:flex;gap:8px;margin:10px 0;flex-wrap:wrap}.k div{border:1px solid #e3e7e1;border-radius:8px;padding:6px 12px;text-align:center}
.k b{display:block;font-size:16px}.tw{overflow-x:auto}table{border-collapse:collapse;width:100%}th,td{border-bottom:1px solid #e3e7e1;padding:5px 6px;text-align:left;vertical-align:top}
th{background:#f6f7f4;font-size:11px}.n{text-align:right;white-space:nowrap}.v{color:#2e7d32;font-weight:700}.a{color:#a77b00;font-weight:700}.r{color:#c62828;font-weight:700}
.nota{color:#5f6f66;font-size:10.5px;margin-top:14px;line-height:1.4}.bar{margin-bottom:14px;display:flex;gap:8px;align-items:center}.bar button{font:inherit;font-weight:600;padding:7px 12px;border-radius:8px;border:1px solid #1f5f3a;background:#1f5f3a;color:#fff;cursor:pointer}
.lote{break-before:page;page-break-before:always;margin-top:34px;padding-top:18px;border-top:6px solid #f0f2ee}
.titulo-sec{font-size:15px;margin:22px 0 8px}
.lhead{display:flex;justify-content:space-between;align-items:flex-start;gap:12px;border-bottom:2px solid #1f5f3a;padding-bottom:6px;margin-bottom:10px}
.badge{display:inline-flex;align-items:center;gap:6px;font-weight:700;font-size:12px;color:var(--c);border:1px solid var(--c);padding:3px 9px;border-radius:999px}.badge i{width:9px;height:9px;border-radius:50%;background:var(--c)}
.lgrid{display:flex;gap:16px;align-items:flex-start;justify-content:space-between}.kvs{display:grid;grid-template-columns:1fr 1fr;gap:8px 16px;flex:1}
.kv span{display:block;font-size:11px;color:#5f6f66}.kv b{font-size:12.5px}.croquis{flex:none}
table.chk td{padding:5px 4px}.chk td:nth-child(2),.chk td:nth-child(3){text-align:right;white-space:nowrap}.chk td:nth-child(3){color:#5f6f66}
.chk small{display:block;color:#5f6f66;font-size:10.5px}.chk .ind{padding-left:14px;color:#5f6f66}.chk tr.hl td{background:#fff3f3;color:#c62828;font-weight:600}
.chk.camp td:first-child{white-space:nowrap;font-weight:600;width:70px}.chk.camp td:nth-child(2){text-align:left;white-space:normal;color:inherit}
.chk.dist td:nth-child(n+2){text-align:right;white-space:nowrap;color:inherit}.chk.dist tr.th td{font-size:10.5px;color:#5f6f66;font-weight:600}.chk.dist tr.cerca td{background:#f2f8ff;font-weight:600}
.tag-cerca{font-size:9.5px;font-weight:700;background:#1565c0;color:#fff;padding:1px 6px;border-radius:999px;margin-left:4px}
.cercano{background:#e8f1fb;border:1px solid #bcd6f2;border-radius:8px;padding:8px 10px;margin-bottom:6px}.cercano b{color:#0d47a1;display:block}.cercano span{font-size:12px}
.motivos{list-style:none;padding:0;margin:10px 0 0}.motivos li{display:flex;gap:8px;line-height:1.4;margin-bottom:4px}.motivos i{flex:none;width:8px;height:8px;border-radius:50%;margin-top:5px}
.accion{margin-top:8px;background:#f6f7f4;border-radius:8px;padding:8px 10px;line-height:1.45}.spin{display:none}
.ndvi-meta{margin-bottom:6px}.warn2{color:#8a6200;font-weight:600}.curva{width:100%;max-width:900px;height:auto;display:block;border:1px solid #e3e7e1;border-radius:6px}
.cap{font-size:10.5px;color:#5f6f66;margin:5px 0 0;line-height:1.4}.muted{color:#5f6f66;font-weight:400}
.evid{margin-top:12px;font-size:10.5px;color:#5f6f66;line-height:1.5;border-top:1px dashed #e3e7e1;padding-top:6px}.evid b{color:#1d2a22}
@media (max-width:640px){body{margin:12px}.lgrid{flex-direction:column}.kvs{grid-template-columns:1fr}}
@media print{.bar{display:none}body{margin:0;padding:0;max-width:none}.lote{margin-top:0;padding-top:0;border-top:0}body{font-size:10px}h2{font-size:13px}h3{font-size:11px;margin:9px 0 4px;break-after:avoid}table.chk td,th,td{padding:2.5px 4px}.croquis{width:96px;height:96px}.curva{max-height:52mm;width:auto;max-width:100%}.motivos{margin-top:6px}.accion{padding:5px 8px;margin-top:5px}.cercano{padding:5px 8px}.evid{margin-top:6px}@page{size:A4;margin:12mm}.lote{break-inside:auto}table,img,.cercano{break-inside:avoid}}`;
  async function abrirInforme(lista, detalle) {
    if (!lista.length) return toast('Elegí al menos un lote.', 'warn');
    // la ventana se abre ya (si se abre despues de esperar datos, el navegador la bloquea)
    const w = window.open('', '_blank');
    if (!w) return toast('El navegador bloqueó la ventana del informe: permití ventanas emergentes para este sitio.', 'warn');
    w.document.write('<p style="font:14px system-ui;padding:24px">Preparando el informe…</p>');
    const k = indicadores(lista), filas = filasInforme(lista);
    const pngs = new Map();
    if (detalle) {
      const cola = lista.filter(l => l.ndvi_at);
      let i = 0;
      const trabajar = async () => { while (i < cola.length) { const l = cola[i++]; try { pngs.set(l.id, curvaPng(l, await obsDe(l))); } catch (e) { console.warn('ndvi', l.id, e); } } };
      await Promise.all([1, 2, 3, 4].map(trabajar));
    }
    const td = v => `<td>${v}</td>`;
    const html = `<!DOCTYPE html><html lang="es"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>Informe Mapa de Lotes EUDR</title>
<style>${CSS_INFORME}</style></head><body>
<div class="bar"><button onclick="window.print()">Imprimir / Guardar como PDF</button><span class="muted">${lista.length} lote(s)</span></div>
<h1>Mapa de Lotes · Informe EUDR y logística</h1>
<div class="meta">Generado ${esc(new Date().toLocaleString('es-AR'))} · ${esc(me?.email || '')} · Filtro: ${esc(descFiltro())} · ${lista.length} lote(s) incluidos</div>
<div class="k"><div><b>${k.n}</b>lotes</div><div><b>${fmt(k.ha, 0)}</b>ha</div><div class="v"><b>${k.verde}</b>aptos</div><div class="a"><b>${k.amarillo}</b>revisar</div><div class="r"><b>${k.rojo}</b>no aptos</div>${k.pend ? `<div><b>${k.pend}</b>en análisis</div>` : ''}</div>
<h2 class="titulo-sec">Resumen por lote</h2>
<div class="tw"><table><tr><th>Lote</th><th>Productor</th><th class="n">Ha</th><th>Semáforo</th><th>Motivo principal</th><th class="n">Bosque 2020 (ha)</th><th class="n">Pérdida post-2020 (ha)</th><th>Acopio más cercano</th><th class="n">Km ruta</th><th class="n">Km asfalto / tierra</th><th>Estado actual</th></tr>
${filas.map(({ l, c, p, b, ea }) => `<tr>${td(esc(l.nombre))}${td(esc(l.productor || '—'))}<td class="n">${fmt(l.area_ha, 1)}</td>
<td class="${{ verde: 'v', amarillo: 'a', rojo: 'r' }[l.semaforo] || ''}">${esc(SEMTXT[l.semaforo] || (l.estado === 'error' ? 'Error' : 'En análisis'))}</td>
${td(esc(((l.motivos || [])[0] || {}).texto || '—'))}<td class="n">${l.bosque_2020 ? fmt(b.bosque_ha, 1) : '—'}</td><td class="n">${l.perdida ? fmt(p.perdida_post2020_ha, 1) : '—'}</td>
${td(c ? esc(c.nombre) : '—')}<td class="n">${c ? fmt(c.km_total, 0) : '—'}</td><td class="n">${c ? fmt(c.km_asfalto, 0) + ' / ' + fmt(c.km_tierra, 1) : '—'}</td>${td(esc(ea.texto || '—'))}</tr>`).join('')}
</table></div>
${acopios.length ? `<h2 class="titulo-sec">Distancia por ruta a cada acopio (km)</h2><div class="tw"><table><tr><th>Lote</th>${acopios.map(a => `<th class="n">${esc(a.nombre)}</th>`).join('')}</tr>
${filas.map(({ l, dist, c }) => `<tr>${td(esc(l.nombre))}${acopios.map(a => { const d = dist[a.id]; return `<td class="n">${d && d.km_total != null ? (c && c.id === a.id ? '<b>' + fmt(d.km_total, 0) + '</b>' : fmt(d.km_total, 0)) : '—'}</td>`; }).join('')}</tr>`).join('')}</table></div>` : ''}
<p class="nota">Semáforo EUDR preliminar: bosque al 31/12/2020 (JRC GFC2020) y pérdida de cobertura arbórea (Hansen GFC); OTBN no consultado. Distancias por camino priorizando rutas asfaltadas, calculadas con OpenStreetMap (motor local); en caminos sin dato de superficie se asume tierra en vecinales y asfalto en rutas. Este informe no constituye una certificación.</p>
${detalle ? lista.map(l => detalleInforme(l, pngs.get(l.id))).join('') : ''}
</body></html>`;
    try { w.document.open(); w.document.write(html); w.document.close(); }
    catch (e) { toast('No se pudo mostrar el informe: ' + e.message, 'err'); }
  }
  function descargarCSV(lista) {
    if (!lista.length) return toast('Elegí al menos un lote.', 'warn');
    const num = (v, d = 1) => (v == null || v === '' ? '' : Number(v).toFixed(d).replace('.', ','));
    const cel = v => { const t = String(v ?? ''); return /[;"\n]/.test(t) ? '"' + t.replace(/"/g, '""') + '"' : t; };
    const cab = ['Lote', 'Productor', 'Hectareas', 'Semaforo', 'Motivo principal', 'Bosque 2020 ha', 'Perdida post-2020 ha', 'Anios de perdida',
      'Acopio mas cercano', 'Km ruta', 'Km asfalto', 'Km tierra', 'Minutos', ...acopios.map(a => 'Km a ' + a.nombre), 'Estado actual', 'Ultimo analisis EUDR', 'Origen'];
    const filas = filasInforme(lista).map(({ l, c, p, b, ea, dist }) => [l.nombre, l.productor || '', num(l.area_ha), SEMTXT[l.semaforo] || l.estado,
      ((l.motivos || [])[0] || {}).texto || '', l.bosque_2020 ? num(b.bosque_ha) : '', l.perdida ? num(p.perdida_post2020_ha) : '',
      Object.keys(p.perdida_post2020_por_anio || {}).join(' '), c ? c.nombre : '', c ? num(c.km_total) : '', c ? num(c.km_asfalto) : '', c ? num(c.km_tierra) : '',
      c ? c.minutos : '', ...acopios.map(a => (dist[a.id] && dist[a.id].km_total != null ? num(dist[a.id].km_total) : '')), ea.texto || '',
      l.eudr_at ? new Date(l.eudr_at).toLocaleString('es-AR') : '', l.origen || '']);
    const csv = '\ufeff' + [cab, ...filas].map(r => r.map(cel).join(';')).join('\r\n');
    const a = document.createElement('a');
    a.href = URL.createObjectURL(new Blob([csv], { type: 'text/csv;charset=utf-8' }));
    a.download = `informe_lotes_${new Date().toISOString().slice(0, 10)}.csv`; a.click(); setTimeout(() => URL.revokeObjectURL(a.href), 2000);
  }
  $('#bInforme').addEventListener('click', () => {
    infLista = filtrados();
    if (!infLista.length) return toast('No hay lotes en el filtro actual.', 'warn');
    const conFiltro = ($('#filtro').value || '').trim() || semFiltro;
    $('#infTitulo').textContent = `Exportar informe · ${infLista.length} lote(s)${conFiltro ? ' del filtro actual' : ''}`;
    $('#infFiltro').textContent = 'Filtro: ' + descFiltro();
    $('#infLotes').innerHTML = infLista.map(l => `<label><input type="checkbox" value="${esc(l.id)}" checked><i class="dot" style="background:${SEM[semKey(l)].color}"></i><span>${esc(l.nombre)}</span><small>${fmt(l.area_ha, 0)} ha</small></label>`).join('');
    actualizarCuentaInf();
    $('#modalInf').hidden = false;
  });
  function actualizarCuentaInf() {
    const n = infElegidos().length;
    $('#infCuenta').textContent = `${n} de ${infLista.length} lote(s) seleccionados`;
    $('#bInfPdf').disabled = $('#bInfCsv').disabled = !n;
  }
  $('#infLotes').addEventListener('change', actualizarCuentaInf);
  $('#infTodos').addEventListener('click', () => { document.querySelectorAll('#infLotes input').forEach(i => { i.checked = true; }); actualizarCuentaInf(); });
  $('#infNinguno').addEventListener('click', () => { document.querySelectorAll('#infLotes input').forEach(i => { i.checked = false; }); actualizarCuentaInf(); });
  $('#bInfPdf').addEventListener('click', () => { const sel = infElegidos(); $('#modalInf').hidden = true; abrirInforme(sel, $('#infDetalle').checked); });
  $('#bInfCsv').addEventListener('click', () => { descargarCSV(infElegidos()); $('#modalInf').hidden = true; });
  $('#bInfClose').addEventListener('click', () => { $('#modalInf').hidden = true; });
  $('#modalInf').addEventListener('click', e => { if (e.target.id === 'modalInf') $('#modalInf').hidden = true; });
  $('#modal').addEventListener('click', e => { if (e.target.id === 'modal') $('#modal').hidden = true; });
  document.addEventListener('keydown', e => { if (e.key === 'Escape') { $('#modal').hidden = true; $('#modalInf').hidden = true; } });
  $('#fileIn').addEventListener('change', e => { importar(Array.from(e.target.files || [])); e.target.value = ''; });
  $('#filtro').addEventListener('input', renderList);

  // ---------- panel ajustable ----------
  const ANCHO_DEF = 410;
  function anchoMax() { return Math.max(320, Math.min(1100, window.innerWidth - 320)); }
  function fijarAncho(px, guardar) {
    const w = Math.round(Math.min(anchoMax(), Math.max(300, px)));
    document.querySelector('main').style.setProperty('--aside-w', w + 'px');
    $('#resizer').setAttribute('aria-valuenow', w);
    if (guardar) { try { localStorage.setItem('mapaLotes.anchoPanel', String(w)); } catch (e) { /* sin almacenamiento */ } }
    if (map) map.invalidateSize({ pan: false });
  }
  (function initResizer() {
    const rz = $('#resizer'), main = document.querySelector('main');
    let guardado = NaN; try { guardado = Number(localStorage.getItem('mapaLotes.anchoPanel')); } catch (e) { /* nada */ }
    rz.setAttribute('aria-valuemin', 300); rz.setAttribute('aria-valuemax', anchoMax());
    if (guardado > 0) fijarAncho(guardado, false);
    let raf = 0;
    rz.addEventListener('pointerdown', e => {
      if (e.button !== 0) return;
      e.preventDefault(); rz.setPointerCapture(e.pointerId); rz.classList.add('drag'); document.body.classList.add('resizing');
      const mover = ev => { cancelAnimationFrame(raf); raf = requestAnimationFrame(() => fijarAncho(main.getBoundingClientRect().right - ev.clientX, false)); };
      const soltar = () => {
        rz.removeEventListener('pointermove', mover); rz.removeEventListener('pointerup', soltar); rz.removeEventListener('pointercancel', soltar);
        rz.classList.remove('drag'); document.body.classList.remove('resizing');
        fijarAncho($('#panel').getBoundingClientRect().width, true);
      };
      rz.addEventListener('pointermove', mover); rz.addEventListener('pointerup', soltar); rz.addEventListener('pointercancel', soltar);
    });
    rz.addEventListener('dblclick', () => fijarAncho(ANCHO_DEF, true));
    rz.addEventListener('keydown', e => {
      const w = $('#panel').getBoundingClientRect().width;
      if (e.key === 'ArrowLeft') { e.preventDefault(); fijarAncho(w + 30, true); }
      else if (e.key === 'ArrowRight') { e.preventDefault(); fijarAncho(w - 30, true); }
      else if (e.key === 'Home') { e.preventDefault(); fijarAncho(ANCHO_DEF, true); }
    });
    window.addEventListener('resize', () => { const w = $('#panel').getBoundingClientRect().width; if (window.innerWidth > 900 && w > anchoMax()) fijarAncho(anchoMax(), false); });
  })();
  // celular: boton flotante para volver al mapa cuando se baja por el panel
  const esMovil = () => window.matchMedia('(max-width:900px)').matches;
  window.addEventListener('scroll', () => { $('#bVerMapa').hidden = !(esMovil() && window.scrollY > window.innerHeight * 0.45); }, { passive: true });
  $('#bVerMapa').addEventListener('click', () => window.scrollTo({ top: 0, behavior: 'smooth' }));

  // ---------- sesión ----------
  async function entrar(session) {
    me = session.user;
    $('#login').hidden = true; $('#app').hidden = false;
    if (!map) initMap(); else map.invalidateSize();
    await cargarTodo(); await leerWorker(); suscribir(); cargarAcopios();
  }
  function salir() {
    me = null; if (channel) { sb.removeChannel(channel); channel = null; }
    $('#app').hidden = true; $('#login').hidden = false;
  }
  $('#loginForm').addEventListener('submit', async e => {
    e.preventDefault(); $('#lErr').textContent = ''; $('#lBtn').disabled = true;
    const { data, error } = await sb.auth.signInWithPassword({ email: $('#lEmail').value.trim(), password: $('#lPass').value });
    $('#lBtn').disabled = false;
    if (error) { $('#lErr').textContent = error.message === 'Invalid login credentials' ? 'Email o contraseña incorrectos.' : error.message; return; }
    entrar(data.session);
  });
  $('#bLogout').addEventListener('click', async () => { await sb.auth.signOut(); salir(); });
  sb.auth.getSession().then(({ data }) => { if (data.session) entrar(data.session); else $('#login').hidden = false; });
  sb.auth.onAuthStateChange((ev, session) => { if (ev === 'SIGNED_OUT') salir(); });
})();
