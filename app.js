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
  let acopios = [], acopioLayer = null, rutaLayer = null;
  const layerById = new Map(), obsCache = new Map();

  // ---------- utilidades ----------
  let toastTimer = null;
  function toast(msg, kind) {
    const el = $('#toast'); el.textContent = msg; el.className = 'toast show ' + (kind || '');
    clearTimeout(toastTimer); toastTimer = setTimeout(() => { el.className = 'toast'; }, 4500);
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
  async function leerArchivo(file) {
    if (file.size > 20e6) throw new Error('archivo mayor a 20 MB');
    const n = file.name.toLowerCase();
    if (n.endsWith('.kmz')) {
      const zip = await JSZip.loadAsync(file);
      const k = Object.values(zip.files).find(f => !f.dir && f.name.toLowerCase().endsWith('.kml'));
      if (!k) throw new Error('el KMZ no contiene un .kml');
      return parseKML(await k.async('text'));
    }
    if (n.endsWith('.kml')) return parseKML(await file.text());
    if (n.endsWith('.geojson') || n.endsWith('.json')) return parseGeoJSON(JSON.parse(await file.text()));
    throw new Error('formato no soportado (KML, KMZ o GeoJSON)');
  }
  async function importar(files) {
    const filas = []; let skipped = 0; const errores = [];
    for (const file of files) {
      try {
        const r = await leerArchivo(file);
        skipped += r.skipped;
        r.feats.forEach((f, i) => {
          try {
            filas.push({
              nombre: (String(f.nombre || '').trim() || `${file.name.replace(/\.[^.]+$/, '')} ${i + 1}`).slice(0, 120),
              productor: String(f.productor || '').trim().slice(0, 120) || null,
              origen: `Archivo ${file.name}`.slice(0, 200),
              geojson: normalizeGeometry(f.geometry),
            });
          } catch (e) { skipped++; }
        });
      } catch (e) { errores.push(`${file.name}: ${e.message}`); }
    }
    if (!filas.length) { toast(errores.length ? 'No se pudo importar: ' + errores.join(' · ') : 'El archivo no tenía polígonos (los puntos se omiten).', errores.length ? 'err' : 'warn'); return; }
    if (filas.length > MAX_IMPORT) { skipped += filas.length - MAX_IMPORT; filas.length = MAX_IMPORT; }
    await insertar(filas, skipped);
  }
  async function insertar(filas, skipped = 0) {
    const { data, error } = await sb.from('lotes').insert(filas).select(COLS);
    if (error) { toast('No se pudieron guardar los lotes: ' + error.message, 'err'); return; }
    data.forEach(upsertLocal);
    renderList();
    const ids = data.map(d => d.id);
    const b = L.featureGroup(ids.map(id => layerById.get(id)).filter(Boolean));
    if (b.getLayers().length) map.fitBounds(b.getBounds(), { padding: [50, 50], maxZoom: 15 });
    if (ids[0]) select(ids[0], false);
    toast(`${data.length} lote(s) cargado(s)${skipped ? `, ${skipped} omitido(s)` : ''}. El semáforo aparece en segundos.`);
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
    return [...lotes.values()].filter(l => !q || (l.nombre || '').toLowerCase().includes(q) || (l.productor || '').toLowerCase().includes(q)
        || (cercano(l)?.nombre || '').toLowerCase().includes(q))
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
      <div class="kpi"><b>${k.n}</b><span>lotes</span></div>
      <div class="kpi"><b>${fmt(k.ha, 0)}</b><span>ha</span></div>
      <div class="kpi v"><b>${k.verde}</b><span>aptos</span></div>
      <div class="kpi a"><b>${k.amarillo}</b><span>revisar</span></div>
      <div class="kpi r"><b>${k.rojo}</b><span>no aptos</span></div>` : '';
    $('#filtroInfo').textContent = arr.length && q ? `Indicadores del filtro: ${vis.length} de ${arr.length} lotes` : '';
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
      <table class="chk dist"><tr class="th"><td>Acopio</td><td>Ruta</td><td>Asfalto</td><td>Tierra</td><td>Tiempo</td></tr>${filas}</table>
      ${eng}<p class="cap">Ruta por camino priorizando rutas asfaltadas (nacionales y provinciales), desde un punto interior del lote. ${esc(g.motor || '')} · ${fdt(g.calculado_at)}. En caminos sin dato de superficie se asume tierra en vecinales y asfalto en rutas.</p>`;
  }
  async function cargarAcopios() {
    const { data, error } = await sb.from('acopios').select('id,nombre,localidad,provincia,lat,lon,activo').eq('activo', true).order('id');
    if (error) { console.warn('acopios', error.message); return; }
    acopios = data || [];
    if (acopioLayer) map.removeLayer(acopioLayer);
    acopioLayer = L.layerGroup(acopios.map(a => L.marker([a.lat, a.lon], { pmIgnore: true, interactive: true,
      icon: L.divIcon({ className: 'acopio-ico', html: '<span>▲</span>', iconSize: [22, 22], iconAnchor: [11, 11] }) })
      .bindTooltip(`${esc(a.nombre)} · ${esc(a.localidad || '')}`, { direction: 'top' }))).addTo(map);
  }
  function dibujarRuta(l) {
    if (rutaLayer) { map.removeLayer(rutaLayer); rutaLayer = null; }
    const c = cercano(l);
    if (c && c.geometria && c.geometria.type === 'LineString') {
      rutaLayer = L.geoJSON(c.geometria, { pmIgnore: true, style: { color: '#1565c0', weight: 4, opacity: 0.8, dashArray: '8 6' } }).addTo(map);
    }
  }

  // ---------- panel: detalle ----------
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
    const pct = v => (a ? fmt((v || 0) / a * 100, 1) + '%' : '–');
    const b = l.bosque_2020 || {}, p = l.perdida || {};
    const anios = Object.keys(p.perdida_post2020_por_anio || {}).sort();
    const ni = l.ndvi_info || {}, ea = l.estado_actual, camps = Array.isArray(l.campanias) ? l.campanias : [];
    const propio = me && l.created_by === me.id;
    const eudrHtml = l.semaforo ? `
      <h3>Chequeo EUDR</h3>
      <table class="chk">
        <tr><td>Bosque al 31/12/2020 <small>${esc(b.fuente || 'JRC GFC2020')}</small></td><td>${fmt(b.bosque_ha)} ha</td><td>${pct(b.bosque_ha)}</td></tr>
        <tr><td class="ind">· de eso, en el borde (30 m)</td><td>${fmt(b.bosque_en_borde_ha)} ha</td><td>${pct(b.bosque_en_borde_ha)}</td></tr>
        <tr class="${p.perdida_post2020_ha > 0 ? 'hl' : ''}"><td>Pérdida posterior a 2020 <small>${esc(p.fuente || 'Hansen GFC')}</small></td><td>${fmt(p.perdida_post2020_ha)} ha</td><td>${anios.length ? esc(anios.join(', ')) : '—'}</td></tr>
        <tr><td class="ind">· pérdida 2001–2020 (antes del corte)</td><td>${fmt(p.perdida_2001_2020_ha)} ha</td><td></td></tr>
        <tr><td>OTBN Ley 26.331</td><td colspan="2">no consultado todavía</td></tr>
      </table>
      <ul class="motivos">${(l.motivos || []).map(m => `<li><i style="background:${(SEM[m.nivel] || SEM.pend).color}"></i>${esc(m.texto)}</li>`).join('')}</ul>
      <div class="accion"><b>Acción sugerida:</b> ${esc(ACCION[l.semaforo] || '')}</div>`
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
      <p class="cap" id="ndviCap">${l.ndvi_at ? `${esc(ni.fechas_validas ?? '')} fechas válidas de ${esc(ni.fechas_candidatas ?? '')} · última imagen ${esc(ni.ultima_escena || '—')} · próximo control ${fdt(l.proximo_monitoreo)}. ${esc(ni.criterio || '')}` : 'El historial aparece cuando termina la descarga.'}</p>
      ${camps.length ? `<h3>Campañas detectadas <small class="muted">(estimación por fecha de los picos)</small></h3>
        <table class="chk camp">${camps.map(c => `<tr><td>${esc(c.campania)}</td><td>${esc(c.cultivo_estimado)}</td></tr>`).join('')}</table>` : ''}
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
    const pts = obs.map(o => ({ x: decYear(o.fecha), y: o.ndvi }));
    const hi = obs.filter(o => o.p75 != null).map(o => ({ x: decYear(o.fecha), y: Math.min(1, o.p75) }));
    const lo = obs.filter(o => o.p25 != null).map(o => ({ x: decYear(o.fecha), y: Math.max(0, o.p25) }));
    const loss = Object.keys((l.perdida || {}).perdida_post2020_por_anio || {}).map(Number).filter(y => ((l.perdida.perdida_post2020_por_anio[y]) || 0) >= 0.5).map(y => y + 0.5);
    if (chart) chart.destroy();
    chart = new Chart($('#ndviChart'), {
      type: 'scatter',
      data: { datasets: [
        { data: pts, showLine: true, pointRadius: 1.6, pointHoverRadius: 3, borderWidth: 1.5, borderColor: '#2e7d32', backgroundColor: '#2e7d32', tension: 0.15 },
        { data: hi, showLine: true, pointRadius: 0, borderWidth: 0, fill: false, tension: 0.15 },
        { data: lo, showLine: true, pointRadius: 0, borderWidth: 0, backgroundColor: 'rgba(46,125,50,.14)', fill: '-1', tension: 0.15 },
      ] },
      options: {
        animation: false, responsive: true, maintainAspectRatio: false,
        interaction: { mode: 'nearest', axis: 'x', intersect: false },
        plugins: { legend: { display: false }, markers: { loss },
          tooltip: { filter: c => c.datasetIndex === 0, callbacks: { title: () => '', label: c => `${decToDate(c.parsed.x)} · NDVI ${c.parsed.y.toFixed(2)}` } } },
        scales: {
          x: { type: 'linear', min: 2020, max: Math.ceil(Math.max(2026.5, pts.at(-1)?.x || 0)), ticks: { stepSize: 1, autoSkip: false, maxRotation: 0, callback: v => (Number.isInteger(v) ? v : '') }, grid: { color: '#eef0ec' } },
          y: { min: 0, max: 1, ticks: { stepSize: 0.2 }, grid: { color: '#eef0ec' }, title: { display: true, text: 'NDVI' } },
        },
      },
      plugins: [markers],
    });
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
  function abrirInforme() {
    const lista = filtrados();
    if (!lista.length) return toast('No hay lotes en el filtro actual.', 'warn');
    const k = indicadores(lista), q = ($('#filtro').value || '').trim();
    const filas = filasInforme(lista);
    const td = v => `<td>${v}</td>`;
    const html = `<!DOCTYPE html><html lang="es"><head><meta charset="utf-8"><title>Informe Mapa de Lotes EUDR</title>
<style>body{font:12px Inter,system-ui,Arial,sans-serif;color:#1d2a22;margin:24px}h1{font-size:18px;margin:0}h2{font-size:14px;margin:20px 0 8px}
.meta{color:#5f6f66;margin:4px 0 14px}.k{display:flex;gap:8px;margin:10px 0}.k div{border:1px solid #e3e7e1;border-radius:8px;padding:6px 12px;text-align:center}
.k b{display:block;font-size:16px}table{border-collapse:collapse;width:100%}th,td{border-bottom:1px solid #e3e7e1;padding:5px 6px;text-align:left;vertical-align:top}
th{background:#f6f7f4;font-size:11px}.n{text-align:right;white-space:nowrap}.v{color:#2e7d32;font-weight:700}.a{color:#a77b00;font-weight:700}.r{color:#c62828;font-weight:700}
.nota{color:#5f6f66;font-size:10.5px;margin-top:14px;line-height:1.4}.bar{margin-bottom:14px}@media print{.bar{display:none}body{margin:10mm}}</style></head><body>
<div class="bar"><button onclick="window.print()">Imprimir / Guardar como PDF</button></div>
<h1>Mapa de Lotes · Informe EUDR y logística</h1>
<div class="meta">Generado ${esc(new Date().toLocaleString('es-AR'))} · ${esc(me?.email || '')} · Filtro: ${q ? '“' + esc(q) + '”' : 'sin filtro (todos los lotes)'}</div>
<div class="k"><div><b>${k.n}</b>lotes</div><div><b>${fmt(k.ha, 0)}</b>ha</div><div class="v"><b>${k.verde}</b>aptos</div><div class="a"><b>${k.amarillo}</b>revisar</div><div class="r"><b>${k.rojo}</b>no aptos</div>${k.pend ? `<div><b>${k.pend}</b>en análisis</div>` : ''}</div>
<h2>Detalle por lote</h2>
<table><tr><th>Lote</th><th>Productor</th><th class="n">Ha</th><th>Semáforo</th><th>Motivo principal</th><th class="n">Bosque 2020 (ha)</th><th class="n">Pérdida post-2020 (ha)</th><th>Acopio más cercano</th><th class="n">Km ruta</th><th class="n">Km asfalto / tierra</th><th>Estado actual</th></tr>
${filas.map(({ l, c, p, b, ea }) => `<tr>${td(esc(l.nombre))}${td(esc(l.productor || '—'))}<td class="n">${fmt(l.area_ha, 1)}</td>
<td class="${{ verde: 'v', amarillo: 'a', rojo: 'r' }[l.semaforo] || ''}">${esc(SEMTXT[l.semaforo] || (l.estado === 'error' ? 'Error' : 'En análisis'))}</td>
${td(esc(((l.motivos || [])[0] || {}).texto || '—'))}<td class="n">${l.bosque_2020 ? fmt(b.bosque_ha, 1) : '—'}</td><td class="n">${l.perdida ? fmt(p.perdida_post2020_ha, 1) : '—'}</td>
${td(c ? esc(c.nombre) : '—')}<td class="n">${c ? fmt(c.km_total, 0) : '—'}</td><td class="n">${c ? fmt(c.km_asfalto, 0) + ' / ' + fmt(c.km_tierra, 1) : '—'}</td>${td(esc(ea.texto || '—'))}</tr>`).join('')}
</table>
${acopios.length ? `<h2>Distancia por ruta a cada acopio (km)</h2><table><tr><th>Lote</th>${acopios.map(a => `<th class="n">${esc(a.nombre)}</th>`).join('')}</tr>
${filas.map(({ l, dist, c }) => `<tr>${td(esc(l.nombre))}${acopios.map(a => { const d = dist[a.id]; return `<td class="n">${d && d.km_total != null ? (c && c.id === a.id ? '<b>' + fmt(d.km_total, 0) + '</b>' : fmt(d.km_total, 0)) : '—'}</td>`; }).join('')}</tr>`).join('')}</table>` : ''}
<p class="nota">Semáforo EUDR preliminar: bosque al 31/12/2020 (JRC GFC2020) y pérdida de cobertura arbórea (Hansen GFC); OTBN no consultado. Distancias por camino priorizando rutas asfaltadas, calculadas con OpenStreetMap (motor local); en caminos sin dato de superficie se asume tierra en vecinales y asfalto en rutas. Este informe no constituye una certificación.</p>
</body></html>`;
    const w = window.open(URL.createObjectURL(new Blob([html], { type: 'text/html' })), '_blank');
    if (!w) toast('El navegador bloqueó la ventana del informe: permití ventanas emergentes para este sitio.', 'warn');
  }
  function descargarCSV() {
    const lista = filtrados();
    if (!lista.length) return toast('No hay lotes en el filtro actual.', 'warn');
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
    const lista = filtrados();
    if (!lista.length) return toast('No hay lotes en el filtro actual.', 'warn');
    $('#infTitulo').textContent = `Exportar informe · ${lista.length} lote(s)${($('#filtro').value || '').trim() ? ' del filtro actual' : ''}`;
    $('#modalInf').hidden = false;
  });
  $('#bInfPdf').addEventListener('click', () => { abrirInforme(); $('#modalInf').hidden = true; });
  $('#bInfCsv').addEventListener('click', () => { descargarCSV(); $('#modalInf').hidden = true; });
  $('#bInfClose').addEventListener('click', () => { $('#modalInf').hidden = true; });
  $('#modalInf').addEventListener('click', e => { if (e.target.id === 'modalInf') $('#modalInf').hidden = true; });
  $('#modal').addEventListener('click', e => { if (e.target.id === 'modal') $('#modal').hidden = true; });
  document.addEventListener('keydown', e => { if (e.key === 'Escape') { $('#modal').hidden = true; $('#modalInf').hidden = true; } });
  $('#fileIn').addEventListener('change', e => { importar(Array.from(e.target.files || [])); e.target.value = ''; });
  $('#filtro').addEventListener('input', renderList);

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
