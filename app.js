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
  const COLS = 'id,nombre,productor,origen,geojson,area_ha,estado,semaforo,motivos,bosque_2020,perdida,estado_actual,campanias,ndvi_info,version,error,eudr_at,ndvi_at,proximo_monitoreo,created_by,created_at';
  const MAX_IMPORT = 300;

  if (!CFG.supabaseUrl || !CFG.supabaseAnonKey || !window.supabase) {
    document.body.innerHTML = '<p style="padding:20px;font-family:sans-serif">Falta config.js (supabaseUrl / supabaseAnonKey).</p>';
    return;
  }
  const sb = window.supabase.createClient(CFG.supabaseUrl, CFG.supabaseAnonKey, { db: { schema: 'eudr' } });

  let me = null, lotes = new Map(), selectedId = null, chart = null, map = null, group = null, channel = null;
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
  function renderList() {
    const arr = [...lotes.values()];
    const cnt = { verde: 0, amarillo: 0, rojo: 0 }; let ha = 0;
    arr.forEach(l => { if (cnt[l.semaforo] !== undefined) cnt[l.semaforo]++; ha += l.area_ha || 0; });
    $('#summary').innerHTML = arr.length ? `
      <div class="kpi"><b>${arr.length}</b><span>lotes</span></div>
      <div class="kpi"><b>${fmt(ha, 0)}</b><span>ha</span></div>
      <div class="kpi v"><b>${cnt.verde}</b><span>aptos</span></div>
      <div class="kpi a"><b>${cnt.amarillo}</b><span>revisar</span></div>
      <div class="kpi r"><b>${cnt.rojo}</b><span>no aptos</span></div>` : '';
    const q = ($('#filtro').value || '').toLowerCase().trim();
    const vis = arr.filter(l => !q || (l.nombre || '').toLowerCase().includes(q) || (l.productor || '').toLowerCase().includes(q))
      .sort((a, b) => ({ rojo: 0, amarillo: 1 }[a.semaforo] ?? 2) - ({ rojo: 0, amarillo: 1 }[b.semaforo] ?? 2) || (a.nombre || '').localeCompare(b.nombre || ''));
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
        <span class="rn">${esc(l.nombre)}<small>${esc(l.productor || 'Sin productor')}</small></span>
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
  $('#modal').addEventListener('click', e => { if (e.target.id === 'modal') $('#modal').hidden = true; });
  document.addEventListener('keydown', e => { if (e.key === 'Escape') $('#modal').hidden = true; });
  $('#fileIn').addEventListener('change', e => { importar(Array.from(e.target.files || [])); e.target.value = ''; });
  $('#filtro').addEventListener('input', renderList);

  // ---------- sesión ----------
  async function entrar(session) {
    me = session.user;
    $('#login').hidden = true; $('#app').hidden = false;
    if (!map) initMap(); else map.invalidateSize();
    await cargarTodo(); await leerWorker(); suscribir();
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
