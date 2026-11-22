'use strict';

/* ================= Utilidades ================= */
const $ = id => document.getElementById(id);
const fmt = (v, d = 4) => (Number.isFinite(v) ? String(+v.toFixed(d)) : '—');
const fmtP = v => (v < 0.0001 ? v.toExponential(3) : fmt(v, 6));
const suma = a => a.reduce((s, v) => s + v, 0);
const media = a => suma(a) / a.length;
const signo = (v, d = 4) => `${v < 0 ? '−' : '+'} ${fmt(Math.abs(v), d)}`;
let datos = null; // última regresión calculada (X1, Y, r, n)

function pearson(x, y) {
  const mx = media(x), my = media(y);
  let sxy = 0, sxx = 0, syy = 0;
  x.forEach((v, i) => { sxy += (v - mx) * (y[i] - my); sxx += (v - mx) ** 2; syy += (y[i] - my) ** 2; });
  return sxy / Math.sqrt(sxx * syy);
}

/* ---------- Distribuciones ---------- */
function pdfN(x) { return Math.exp(-x * x / 2) / Math.sqrt(2 * Math.PI); }

function cdfN(x) { // Hart (1968), precisión ~1e-15
  const z = Math.abs(x);
  let p;
  if (z > 37) p = 0;
  else {
    const e = Math.exp(-z * z / 2);
    if (z < 7.07106781186547) {
      let n = 3.52624965998911e-2 * z + 0.700383064443688;
      n = n * z + 6.37396220353165; n = n * z + 33.912866078383;
      n = n * z + 112.079291497871; n = n * z + 221.213596169931; n = n * z + 220.206867912376;
      let d = 8.83883476483184e-2 * z + 1.75566716318264;
      d = d * z + 16.064177579207; d = d * z + 86.7807322029461;
      d = d * z + 296.564248779674; d = d * z + 637.333633378831;
      d = d * z + 793.826512519948; d = d * z + 440.413735824752;
      p = e * n / d;
    } else {
      let b = z + 0.65; b = z + 4 / b; b = z + 3 / b; b = z + 2 / b; b = z + 1 / b;
      p = e / b / 2.506628274631;
    }
  }
  return x > 0 ? 1 - p : p;
}

function invN(p) { // Acklam + un paso de refinamiento
  const a = [-39.69683028665376, 220.9460984245205, -275.9285104469687, 138.357751867269, -30.66479806614716, 2.506628277459239];
  const b = [-54.47609879822406, 161.5858368580409, -155.6989798598866, 66.80131188771972, -13.28068155288572];
  const c = [-0.007784894002430293, -0.3223964580411365, -2.400758277161838, -2.549732539343734, 4.374664141464968, 2.938163982698783];
  const d = [0.007784695709041462, 0.3224671290700398, 2.445134137142996, 3.754408661907416];
  let x;
  if (p < 0.02425) {
    const q = Math.sqrt(-2 * Math.log(p));
    x = (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1);
  } else if (p > 1 - 0.02425) {
    const q = Math.sqrt(-2 * Math.log(1 - p));
    x = -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1);
  } else {
    const q = p - 0.5, r = q * q;
    x = (((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1);
  }
  return x - (cdfN(x) - p) / pdfN(x);
}

function lgamma(x) {
  const g = [76.18009172947146, -86.50532032941677, 24.01409824083091, -1.231739572450155, 0.001208650973866179, -0.000005395239384953];
  let y = x, t = x + 5.5, s = 1.000000000190015;
  t -= (x + 0.5) * Math.log(t);
  for (let j = 0; j < 6; j++) s += g[j] / ++y;
  return -t + Math.log(2.5066282746310005 * s / x);
}

function betacf(a, b, x) {
  const F = 1e-300; let c = 1, d = 1 - (a + b) * x / (a + 1);
  if (Math.abs(d) < F) d = F;
  d = 1 / d; let h = d;
  for (let m = 1; m <= 300; m++) {
    const m2 = 2 * m;
    let aa = m * (b - m) * x / ((a - 1 + m2) * (a + m2));
    d = 1 + aa * d; if (Math.abs(d) < F) d = F;
    c = 1 + aa / c; if (Math.abs(c) < F) c = F;
    d = 1 / d; h *= d * c;
    aa = -(a + m) * (a + b + m) * x / ((a + m2) * (a + 1 + m2));
    d = 1 + aa * d; if (Math.abs(d) < F) d = F;
    c = 1 + aa / c; if (Math.abs(c) < F) c = F;
    d = 1 / d;
    const del = d * c; h *= del;
    if (Math.abs(del - 1) < 3e-14) break;
  }
  return h;
}

function betai(x, a, b) {
  if (x <= 0) return 0;
  if (x >= 1) return 1;
  const bt = Math.exp(lgamma(a + b) - lgamma(a) - lgamma(b) + a * Math.log(x) + b * Math.log(1 - x));
  return x < (a + 1) / (a + b + 2) ? bt * betacf(a, b, x) / a : 1 - bt * betacf(b, a, 1 - x) / b;
}

function cdfT(t, v) {
  const p = 0.5 * betai(v / (v + t * t), v / 2, 0.5);
  return t > 0 ? 1 - p : p;
}

function invT(p, v) { // bisección
  let lo = -1000, hi = 1000;
  for (let i = 0; i < 200; i++) {
    const mid = (lo + hi) / 2;
    if (cdfT(mid, v) < p) lo = mid; else hi = mid;
  }
  return (lo + hi) / 2;
}

/* ---------- Álgebra: sistema de ecuaciones normales ---------- */
function resolver(A, c) { // Gauss-Jordan con pivoteo parcial
  const n = c.length, M = A.map((f, i) => [...f, c[i]]);
  for (let i = 0; i < n; i++) {
    let p = i;
    for (let r = i + 1; r < n; r++) if (Math.abs(M[r][i]) > Math.abs(M[p][i])) p = r;
    if (Math.abs(M[p][i]) < 1e-10) return null;
    [M[i], M[p]] = [M[p], M[i]];
    const piv = M[i][i];
    M[i] = M[i].map(v => v / piv);
    for (let r = 0; r < n; r++) {
      if (r === i) continue;
      const f = M[r][i];
      M[r] = M[r].map((v, j) => v - f * M[i][j]);
    }
  }
  return M.map(f => f[n]);
}

/* ---------- Ayudantes de salida ---------- */
const bloque = (titulo, lineas) => `<p><strong>${titulo}</strong><br>${lineas.join('<br>')}</p>`;
const paso = (titulo, texto, formula) =>
  `<div class="paso"><h4>${titulo}</h4><p>${texto}</p>${formula ? `<pre>${formula}</pre>` : ''}</div>`;
const pr = v => `${fmt(v, 4)} (${fmt(v * 100, 2)} %)`;

// P(X ≤ a, Y ≤ b) normal bivariada: integral numérica (Simpson) de φ(t)·Φ((w − ρt)/√(1−ρ²))
function cdfBiv(a, b, mx, sx, my, sy, rho) {
  if (a === -Infinity || b === -Infinity) return 0;
  if (a === Infinity && b === Infinity) return 1;
  const u = (a - mx) / sx, w = (b - my) / sy, s = Math.sqrt(1 - rho * rho);
  if (a === Infinity) return cdfN(w);
  if (b === Infinity) return cdfN(u);
  if (u < -10) return 0;
  const N = 4000, lo = -10, h = (u - lo) / N, f = t => pdfN(t) * cdfN((w - rho * t) / s);
  let tot = f(lo) + f(u);
  for (let i = 1; i < N; i++) tot += f(lo + i * h) * (i % 2 ? 4 : 2);
  return tot * h / 3;
}

/* ================= Pestañas ================= */
document.querySelectorAll('.tab').forEach(t => t.addEventListener('click', () => {
  document.querySelectorAll('.tab').forEach(x => x.classList.toggle('activo', x === t));
  document.querySelectorAll('.seccion').forEach(s => s.classList.toggle('activa', s.id === t.dataset.sec));
}));

/* ================= Sección 1: Regresión ================= */
const tabla = $('tabla');
const MIN_FILAS = 3, MAX_X = 8;
let kMult = 2; // variables independientes en la regresión múltiple
const ICONO = '<svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M9 3h6l1 2h4v2H4V5h4l1-2zM6 9h12l-1 12H7L6 9z"/></svg>';
const nVars = () => ($('tipo').value === 'lineal' ? 1 : kMult);
const nombresX = () => (nVars() === 1 ? ['X'] : Array.from({ length: nVars() }, (_, i) => 'X' + (i + 1)));
const filasTabla = () => [...tabla.querySelectorAll('tr[data-r]')];

function filaHTML(r) {
  const k = nVars();
  let h = `<tr data-r="${r}">`;
  for (let c = 0; c <= k; c++) h += `<td><input type="text" inputmode="decimal" data-r="${r}" data-c="${c}"></td>`;
  return h + `<td class="calc"></td><td class="accion"><button class="borrar" title="Borrar fila" aria-label="Borrar fila">${ICONO}</button></td></tr>`;
}

function construirTabla(filas = MIN_FILAS) {
  const cab = nombresX().map(n => `<th>${n}</th>`).join('') + `<th>Y</th><th>Y'</th><th class="accion"></th>`;
  tabla.innerHTML = `<tr>${cab}</tr>`;
  for (let r = 0; r < filas; r++) tabla.tBodies[0].insertAdjacentHTML('beforeend', filaHTML(r));
  $('res-reg').innerHTML = ''; $('msg-reg').textContent = ''; $('grafica').hidden = true;
  $('btn-var').hidden = $('tipo').value === 'lineal';
  $('btn-var').disabled = kMult >= MAX_X;
  $('instrucciones').textContent = $('tipo').value === 'lineal'
    ? "Escribe los valores de X (variable independiente) y Y (variable dependiente), uno por fila. Se necesitan mínimo 3 datos. Se calculan a, b, la ecuación Y' = a + bX, los valores de Y', r, r² y el diagrama de dispersión. Puedes pegar datos desde Excel."
    : "Escribe los valores de X1, X2, … y Y, uno por fila. Con + Agregar variable X puedes añadir más variables independientes (hasta " + MAX_X + "); necesitas al menos dos filas más que variables X. Se calculan los coeficientes de Y' = a + b1X1 + b2X2 + …, los valores de Y', R y R². Puedes pegar datos desde Excel.";
  renumerar();
}

function renumerar() { // reasigna índices de fila y bloquea borrar si quedan 3
  const f = filasTabla();
  f.forEach((tr, r) => {
    tr.dataset.r = r;
    tr.querySelectorAll('input').forEach(i => { i.dataset.r = r; });
    tr.querySelector('.borrar').disabled = f.length <= MIN_FILAS;
  });
}

function agregarFila() {
  tabla.tBodies[0].insertAdjacentHTML('beforeend', filaHTML(filasTabla().length));
  renumerar();
}

function agregarVariable() {
  if (kMult >= MAX_X) return;
  const previo = filasTabla().map(tr => [...tr.querySelectorAll('input')].map(i => i.value));
  const k = kMult;
  kMult++;
  construirTabla(previo.length);
  previo.forEach((vals, r) => vals.forEach((v, c) => { // la nueva X queda antes de Y
    tabla.querySelector(`input[data-r="${r}"][data-c="${c < k ? c : c + 1}"]`).value = v;
  }));
}

function leerDatos() {
  const k = nVars(), filas = [];
  for (const tr of filasTabla()) {
    const vals = [...tr.querySelectorAll('input')].map(i => i.value.trim().replace(',', '.'));
    if (vals.every(v => v === '')) continue;
    const r = +tr.dataset.r + 1;
    if (vals.some(v => v === '')) throw new Error(`La fila ${r} está incompleta.`);
    const nums = vals.map(Number);
    if (nums.some(v => !Number.isFinite(v))) throw new Error(`La fila ${r} tiene un valor que no es número.`);
    filas.push(nums);
  }
  if (filas.length < k + 2) throw new Error(`Se necesitan al menos ${k + 2} filas completas.`);
  return filas;
}

function calcularRegresion() {
  $('msg-reg').textContent = '';
  try {
    const k = nVars(), filas = leerDatos(), n = filas.length;
    const cols = Array.from({ length: k }, (_, j) => filas.map(f => f[j]));
    const y = filas.map(f => f[k]);
    let coef, html = '', R2, r;

    if (k === 1) {
      const x = cols[0];
      const Sx = suma(x), Sy = suma(y), Sxy = suma(x.map((v, i) => v * y[i]));
      const Sxx = suma(x.map(v => v * v)), Syy = suma(y.map(v => v * v));
      const den = n * Sxx - Sx ** 2;
      if (Math.abs(den) < 1e-12) throw new Error('Todos los valores de X son iguales; no se puede calcular la recta.');
      const b = (n * Sxy - Sx * Sy) / den, a = Sy / n - b * Sx / n;
      coef = [a, b];
      r = (n * Sxy - Sx * Sy) / Math.sqrt(den * (n * Syy - Sy ** 2));
      html += `<h3>Sumatorias</h3><dl><dt>n</dt><dd>${n}</dd><dt>ΣX</dt><dd>${fmt(Sx)}</dd><dt>ΣY</dt><dd>${fmt(Sy)}</dd>
        <dt>ΣXY</dt><dd>${fmt(Sxy)}</dd><dt>ΣX²</dt><dd>${fmt(Sxx)}</dd><dt>ΣY²</dt><dd>${fmt(Syy)}</dd></dl>`;
    } else {
      const P = [Array(n).fill(1), ...cols];
      const A = P.map(pi => P.map(pj => suma(pi.map((v, t) => v * pj[t]))));
      const c = P.map(pi => suma(pi.map((v, t) => v * y[t])));
      coef = resolver(A, c);
      if (!coef) throw new Error('El sistema no tiene solución única: hay variables repetidas o dependientes entre sí.');
      const nom = ['a', ...nombresX().map((_, i) => 'b' + (i + 1))];
      const lineas = A.map((f, i) => f.map((v, j) => `${fmt(v)}·${nom[j]}`).join(' + ') + ` = ${fmt(c[i])}`);
      html += `<h3>Ecuaciones normales</h3><pre>${lineas.join('\n')}</pre>`;
    }

    const yp = filas.map(f => coef[0] + coef.slice(1).reduce((s, b, j) => s + b * f[j], 0));
    const sse = suma(y.map((v, i) => (v - yp[i]) ** 2));
    const sst = suma(y.map(v => (v - media(y)) ** 2));
    R2 = 1 - sse / sst;

    let ec = `Y' = ${fmt(coef[0])}`;
    coef.slice(1).forEach((b, j) => { ec += ` ${signo(b)}${k === 1 ? 'X' : 'X' + (j + 1)}`; });

    if (k === 1) {
      html += `<h3>Resultados</h3><dl><dt>b</dt><dd>${fmt(coef[1])}</dd><dt>a</dt><dd>${fmt(coef[0])}</dd>
        <dt>Ecuación de la recta</dt><dd>${ec}</dd><dt>Coeficiente de correlación (r)</dt><dd>${fmt(r)}</dd>
        <dt>Coeficiente de determinación (R²)</dt><dd>${fmt(R2)} (${fmt(R2 * 100, 2)} % de la variación de Y se explica por X)</dd></dl>`;
    } else {
      const rs = cols.map(c => pearson(c, y));
      html += `<h3>Resultados</h3><dl><dt>a</dt><dd>${fmt(coef[0])}</dd>`
        + coef.slice(1).map((b, j) => `<dt>b${j + 1}</dt><dd>${fmt(b)}</dd>`).join('')
        + `<dt>Ecuación de regresión múltiple</dt><dd>${ec}</dd>`
        + rs.map((v, j) => `<dt>r (X${j + 1} con Y)</dt><dd>${fmt(v)}</dd>`).join('')
        + `<dt>Coef. de correlación múltiple (R)</dt><dd>${fmt(Math.sqrt(Math.max(R2, 0)))}</dd>
        <dt>Coeficiente de determinación (R²)</dt><dd>${fmt(R2)} (${fmt(R2 * 100, 2)} % de la variación de Y se explica por el modelo)</dd></dl>`;
      r = rs[0];
    }
    $('res-reg').innerHTML = html;

    // Y' en la tabla
    let i = 0;
    for (const tr of filasTabla()) {
      const vacia = [...tr.querySelectorAll('input')].every(x => x.value.trim() === '');
      tr.querySelector('td.calc').textContent = vacia ? '' : fmt(yp[i++]);
    }

    datos = { x: cols[0], y, r: k === 1 ? r : pearson(cols[0], y), n };
    if (k === 1) graficar(cols[0], y, x => coef[0] + coef[1] * x, 'X', 'Y');
    else graficar(yp, y, x => x, "Y' (estimada)", 'Y (real)');
  } catch (e) {
    $('msg-reg').textContent = e.message;
  }
}

function graficar(xs, ys, f, etX, etY) {
  const cv = $('grafica'), g = cv.getContext('2d');
  cv.hidden = false;
  const W = cv.width, H = cv.height, L = 60, R = 20, T = 20, B = 50;
  const rango = a => { const mn = Math.min(...a), mx = Math.max(...a), p = (mx - mn || 1) * 0.08; return [mn - p, mx + p]; };
  const [x0, x1] = rango(xs), [y0, y1] = rango([...ys, f(x0), f(x1)]);
  const px = v => L + (v - x0) / (x1 - x0) * (W - L - R);
  const py = v => H - B - (v - y0) / (y1 - y0) * (H - T - B);
  g.clearRect(0, 0, W, H); g.fillStyle = '#fff'; g.fillRect(0, 0, W, H);
  g.strokeStyle = '#1a1a1a'; g.fillStyle = '#1a1a1a'; g.font = '12px Tahoma, sans-serif'; g.lineWidth = 1;
  g.strokeRect(L, T, W - L - R, H - T - B);
  g.textAlign = 'center';
  for (let i = 0; i <= 5; i++) {
    const vx = x0 + (x1 - x0) * i / 5, vy = y0 + (y1 - y0) * i / 5;
    g.fillText(fmt(vx, 2), px(vx), H - B + 16);
    g.textAlign = 'right'; g.fillText(fmt(vy, 2), L - 6, py(vy) + 4); g.textAlign = 'center';
    g.strokeStyle = '#e6e6e6'; g.beginPath(); g.moveTo(px(vx), T); g.lineTo(px(vx), H - B); g.moveTo(L, py(vy)); g.lineTo(W - R, py(vy)); g.stroke();
  }
  g.fillStyle = '#1a1a1a'; g.fillText(etX, (L + W - R) / 2, H - 10);
  g.save(); g.translate(14, (T + H - B) / 2); g.rotate(-Math.PI / 2); g.fillText(etY, 0, 0); g.restore();
  g.strokeStyle = '#b00020'; g.lineWidth = 2;
  g.beginPath(); g.moveTo(px(x0), py(f(x0))); g.lineTo(px(x1), py(f(x1))); g.stroke();
  g.fillStyle = '#1a73e8';
  xs.forEach((v, i) => { g.beginPath(); g.arc(px(v), py(ys[i]), 4, 0, 2 * Math.PI); g.fill(); });
}

$('tipo').addEventListener('change', () => { kMult = 2; construirTabla(); });
$('btn-calcular').addEventListener('click', calcularRegresion);
$('btn-fila').addEventListener('click', agregarFila);
$('btn-var').addEventListener('click', agregarVariable);
$('btn-limpiar').addEventListener('click', () => { kMult = 2; construirTabla(); });
tabla.addEventListener('click', e => { // borrar fila
  const b = e.target.closest('.borrar');
  if (!b || b.disabled) return;
  b.closest('tr').remove();
  renumerar();
});
tabla.addEventListener('paste', e => { // pegar desde Excel
  const txt = e.clipboardData.getData('text');
  if (!/[\t\n]/.test(txt)) return;
  e.preventDefault();
  const r0 = +e.target.dataset.r, c0 = +e.target.dataset.c;
  const filas = txt.trim().split(/\r?\n/).map(l => l.split('\t'));
  while (filasTabla().length < r0 + filas.length) agregarFila();
  filas.forEach((f, i) => f.forEach((v, j) => {
    const el = tabla.querySelector(`input[data-r="${r0 + i}"][data-c="${c0 + j}"]`);
    if (el) el.value = v.trim();
  }));
});

/* ================= Sección 2: IC y prueba de r ================= */
$('c-usar').addEventListener('click', () => {
  if (!datos) { $('msg-cor').textContent = 'Primero calcula la regresión en la sección Regresión.'; return; }
  $('msg-cor').textContent = '';
  $('c-r').value = +datos.r.toFixed(6); $('c-n').value = datos.n;
});

$('c-calcular').addEventListener('click', () => {
  $('msg-cor').textContent = '';
  try {
    const r = parseFloat($('c-r').value), n = parseInt($('c-n').value);
    const alfa = parseFloat($('c-alfa').value), rho0 = parseFloat($('c-rho0').value) || 0;
    const cola = $('c-cola').value;
    if (!(Math.abs(r) < 1)) throw new Error('r debe estar entre −1 y 1 (sin incluirlos).');
    if (!(n >= 4)) throw new Error('n debe ser al menos 4.');
    if (!(alfa > 0 && alfa < 1)) throw new Error('α debe estar entre 0 y 1.');
    if (!(Math.abs(rho0) < 1)) throw new Error('ρ₀ debe estar entre −1 y 1.');

    // ---- Intervalo de confianza (transformación z de Fisher) ----
    const zr = Math.atanh(r), ee = 1 / Math.sqrt(n - 3), zc = invN(1 - alfa / 2);
    const lo = Math.tanh(zr - zc * ee), hi = Math.tanh(zr + zc * ee);

    // ---- Prueba de hipótesis ----
    const usaT = rho0 === 0, gl = n - 2, zr0 = Math.atanh(rho0), r0 = fmt(rho0);
    const est = usaT ? r * Math.sqrt(gl) / Math.sqrt(1 - r * r) : (zr - zr0) * Math.sqrt(n - 3);
    const cdf = usaT ? v => cdfT(v, gl) : cdfN;
    const inv = usaT ? q => invT(q, gl) : invN;
    const bi = cola === 'bi';
    const q = inv(bi ? 1 - alfa / 2 : 1 - alfa);
    const area = bi ? alfa / 2 : alfa;
    let p, rechaza, h1, crit, comp, nomCola;
    if (cola === 'bi') {
      p = 2 * (1 - cdf(Math.abs(est))); rechaza = Math.abs(est) > q; h1 = `ρ ≠ ${r0}`; crit = `±${fmt(q)}`;
      comp = `|${fmt(est)}| ${rechaza ? '&gt;' : '≤'} ${fmt(q)}`; nomCola = 'bilateral';
    } else if (cola === 'der') {
      p = 1 - cdf(est); rechaza = est > q; h1 = `ρ &gt; ${r0}`; crit = fmt(q);
      comp = `${fmt(est)} ${rechaza ? '&gt;' : '≤'} ${fmt(q)}`; nomCola = 'de cola derecha';
    } else {
      p = cdf(est); rechaza = est < -q; h1 = `ρ &lt; ${r0}`; crit = fmt(-q);
      comp = `${fmt(est)} ${rechaza ? '&lt;' : '≥'} ${fmt(-q)}`; nomCola = 'de cola izquierda';
    }
    const letra = usaT ? 't' : 'z';

    const desarrollo = usaT
      ? `t = r·√(n − 2) / √(1 − r²)
t = (${fmt(r)})·√(${n} − 2) / √(1 − (${fmt(r)})²)
t = (${fmt(r)})·√${gl} / √${fmt(1 - r * r)}
t = (${fmt(r)})(${fmt(Math.sqrt(gl))}) / ${fmt(Math.sqrt(1 - r * r))}
t = ${fmt(est)}`
      : `z_r = ½·ln[(1 + r)/(1 − r)] = ${fmt(zr)}
z_ρ₀ = ½·ln[(1 + ρ₀)/(1 − ρ₀)] = ${fmt(zr0)}
z = (z_r − z_ρ₀)·√(n − 3)
z = (${fmt(zr)} − (${fmt(zr0)}))·√(${n} − 3)
z = ${fmt(est)}`;

    const paso3 = usaT
      ? `<p>Se calculan con el tamaño de la muestra: gl = n − 2.</p><pre>gl = n − 2
gl = ${n} − 2
gl = ${gl}</pre>`
      : `<p>Como ρ₀ ≠ 0 se usa la transformación z de Fisher, que sigue una distribución normal estándar; por eso no hay grados de libertad. El error estándar usa n − 3 = ${n - 3}.</p>`;

    const paso4 = `<p>Se busca en la tabla ${usaT ? `t con ${gl} grados de libertad` : 'normal estándar'} el valor que deja un área de ${fmt(area, 6)} en ${bi ? 'cada cola' : 'la cola ' + (cola === 'der' ? 'derecha' : 'izquierda')}.</p><pre>α = ${fmt(alfa, 6)}${bi ? `
α/2 = ${fmt(alfa / 2, 6)}` : ''}${usaT ? `
gl = ${gl}` : ''}
Valor crítico = ${crit}</pre>`;

    const afirma = rho0 === 0
      ? `existe una correlación lineal ${cola === 'der' ? 'positiva ' : cola === 'izq' ? 'negativa ' : ''}significativa entre las dos variables`
      : `la correlación poblacional ρ ${bi ? 'es distinta de' : cola === 'der' ? 'es mayor que' : 'es menor que'} ${r0}`;
    const sig = `${fmt(alfa * 100, 2)} %`;
    const conclusion = `${rechaza ? 'Existe' : 'No existe'} evidencia estadística suficiente, con un nivel de significancia del ${sig}, para afirmar que ${afirma}.`;

    $('res-cor').innerHTML = `
      <h3>Intervalo de confianza del coeficiente de correlación (${fmt((1 - alfa) * 100, 2)} %)</h3>
      <dl><dt>T. Fisher (zᵣ)</dt><dd>${fmt(zr)}</dd><dt>Error estándar (1/√(n−3))</dt><dd>${fmt(ee)}</dd>
      <dt>Valor crítico normal z</dt><dd>${fmt(zc)}</dd>
      <dt>Intervalo de confianza para ρ</dt><dd>${fmt(lo)} ≤ ρ ≤ ${fmt(hi)}</dd></dl><br>

      <h3>Prueba de hipótesis del coeficiente de correlación</h3>
      ${bloque('Datos:', [`n = ${n}`, `r = ${fmt(r)}`, `α = ${fmt(alfa, 6)}`, ...(usaT ? [] : [`ρ₀ = ${r0}`]), `prueba ${nomCola}`])}
      ${bloque('Resultados:', [
        `${letra} = ${fmt(est)}`,
        ...(usaT ? [`gl = ${gl}`] : []),
        `${bi ? 'α/2' : 'α'} = ${fmt(area, 6)}`,
        `Valor crítico = ${crit}`,
        `Valor p = ${fmtP(p)}`,
        `Conclusión: ${rechaza ? 'se rechaza' : 'no se rechaza'} la hipótesis nula`])}
      <p><strong>Desarrollo:</strong></p>

      <div class="paso"><h4>1. Hipótesis nula y alternativa</h4>
        <p>Se plantea que la correlación poblacional vale ${r0} (H₀) contra la alternativa (H₁), según el tipo de prueba.</p>
        <pre>H₀: ρ = ${r0}
H₁: ${h1}</pre></div>

      <div class="paso"><h4>2. Calcular el estadístico de prueba</h4>
        <p>Se sustituyen r = ${fmt(r)} y n = ${n} en la fórmula${usaT ? ' de t' : ' z de Fisher'}.</p>
        <pre>${desarrollo}</pre></div>

      <div class="paso"><h4>3. Determinar los grados de libertad</h4>${paso3}</div>

      <div class="paso"><h4>4. Comparar con el valor crítico</h4>${paso4}</div>

      <div class="paso"><h4>5. Tomar una decisión</h4>
        <p>Se compara el estadístico (${letra} = ${fmt(est)}) con el valor crítico (${crit}) según la prueba ${nomCola}: ${bi ? 'se rechaza H₀ si |' + letra + '| es mayor que el valor crítico' : cola === 'der' ? 'se rechaza H₀ si ' + letra + ' es mayor que el valor crítico' : 'se rechaza H₀ si ' + letra + ' es menor que el valor crítico'}.</p>
        <pre>${comp}</pre>
        <div class="decision"><strong>${rechaza ? 'SE RECHAZA LA HIPÓTESIS NULA' : 'NO SE RECHAZA LA HIPÓTESIS NULA'}</strong></div>
        <p><strong>Conclusión:</strong> ${conclusion}</p></div>`;
  } catch (e) {
    $('msg-cor').textContent = e.message;
  }
});

/* ================= Sección 3: Probabilidad bivariada normal ================= */
const INSTR_N = {
  cond: 'Calcula la distribución de Y cuando X vale exactamente x₀ y la probabilidad P(Y ≤ y₀ | X = x₀).',
  conj: 'Calcula P(x₁ ≤ X ≤ x₂, y₁ ≤ Y ≤ y₂). Deja un límite vacío para usar infinito (−∞ o +∞); escribe al menos uno.',
  marg: 'Calcula P(X ≤ límite) o P(Y ≤ límite). Solo necesitas la media y la desviación estándar de la variable elegida.',
  lin: 'Calcula P(aX + bY ≤ c). Una combinación lineal de variables normales también es normal.',
  dens: 'Calcula la altura de la función de densidad conjunta f(x₀, y₀) en un punto. La densidad no es una probabilidad.'
};

function modoNormal() {
  const m = $('n-tipo').value;
  document.querySelectorAll('#normal [data-m]').forEach(el => { el.hidden = !el.dataset.m.split(' ').includes(m); });
  $('n-instr').textContent = INSTR_N[m];
  $('msg-nor').textContent = ''; $('res-nor').innerHTML = '';
}
$('n-tipo').addEventListener('change', modoNormal);

$('n-usar').addEventListener('click', () => {
  if (!datos) { $('msg-nor').textContent = 'Primero calcula la regresión en la sección Regresión.'; return; }
  $('msg-nor').textContent = '';
  const sd = a => Math.sqrt(suma(a.map(v => (v - media(a)) ** 2)) / (a.length - 1));
  $('n-mx').value = +media(datos.x).toFixed(6); $('n-sx').value = +sd(datos.x).toFixed(6);
  $('n-my').value = +media(datos.y).toFixed(6); $('n-sy').value = +sd(datos.y).toFixed(6);
  $('n-rho').value = +datos.r.toFixed(6);
});

$('n-calcular').addEventListener('click', () => {
  $('msg-nor').textContent = '';
  try {
    const modo = $('n-tipo').value;
    const num = (id, nombre) => {
      const v = parseFloat($(id).value);
      if (Number.isNaN(v)) throw new Error(`Completa ${nombre}.`);
      return v;
    };
    const lim = (id, def) => ($(id).value.trim() === '' ? def : parseFloat($(id).value));
    const inf = a => (Number.isFinite(a) ? fmt(a) : (a > 0 ? '+∞' : '−∞'));
    const zz = (a, m, d) => (Number.isFinite(a) ? fmt((a - m) / d) : inf(a));
    let html = '';

    if (modo === 'marg') {
      const esX = $('n-var').value === 'X', V = esX ? 'X' : 'Y';
      const mu = esX ? num('n-mx', 'μX') : num('n-my', 'μY');
      const sd = esX ? num('n-sx', 'σX') : num('n-sy', 'σY');
      const L = num('n-lim', 'el límite');
      if (sd <= 0) throw new Error(`σ${V} debe ser mayor que 0.`);
      const z = (L - mu) / sd, P = cdfN(z);
      html = `<h3>3. Probabilidad marginal de ${V}</h3>
        ${bloque('Datos:', [`μ${V} = ${fmt(mu)}`, `σ${V} = ${fmt(sd)}`, `límite = ${fmt(L)}`])}
        ${bloque('Resultados:', [`Z = ${fmt(z)}`, `P(${V} ≤ ${fmt(L)}) = ${pr(P)}`, `P(${V} &gt; ${fmt(L)}) = ${pr(1 - P)}`])}
        <p><strong>Desarrollo:</strong></p>
        ${paso('3.1 Distribución marginal', `En una normal bivariada, ${V} por sí sola es normal con su propia media y desviación (no depende de ρ).`, `${V} ~ N(μ = ${fmt(mu)}, σ = ${fmt(sd)})`)}
        ${paso('3.2 Valor estandarizado', 'Se convierte el límite a la normal estándar.', `Z = (${V.toLowerCase()} − μ${V}) / σ${V}\nZ = (${fmt(L)} − ${fmt(mu)}) / ${fmt(sd)}\nZ = ${fmt(z)}`)}
        ${paso('3.3 Probabilidad', 'Se toma el área de la normal estándar.', `P(${V} ≤ ${fmt(L)}) = P(Z ≤ ${fmt(z)}) = ${fmt(P, 4)}\nP(${V} &gt; ${fmt(L)}) = 1 − ${fmt(P, 4)} = ${fmt(1 - P, 4)}`)}`;
    } else {
      const mx = num('n-mx', 'μX'), sx = num('n-sx', 'σX'), my = num('n-my', 'μY'), sy = num('n-sy', 'σY'), rho = num('n-rho', 'ρ');
      if (sx <= 0 || sy <= 0) throw new Error('σX y σY deben ser mayores que 0.');
      const datosBase = [`μX = ${fmt(mx)}`, `σX = ${fmt(sx)}`, `μY = ${fmt(my)}`, `σY = ${fmt(sy)}`, `ρ = ${fmt(rho)}`];

      if (modo === 'lin') {
        const a = num('n-a', 'a'), b = num('n-b', 'b'), c = num('n-c', 'c');
        if (Math.abs(rho) > 1) throw new Error('ρ debe estar entre −1 y 1.');
        const mw = a * mx + b * my;
        const v = a * a * sx * sx + b * b * sy * sy + 2 * a * b * rho * sx * sy, sw = Math.sqrt(v);
        if (!(sw > 1e-12)) throw new Error('La combinación no tiene variación (σ = 0).');
        const z = (c - mw) / sw, P = cdfN(z);
        html = `<h3>4. Combinación lineal aX + bY</h3>
          ${bloque('Datos:', [...datosBase, `a = ${fmt(a)}`, `b = ${fmt(b)}`, `c = ${fmt(c)}`])}
          ${bloque('Resultados:', [`μ = ${fmt(mw)}`, `σ² = ${fmt(v)}`, `σ = ${fmt(sw)}`, `Z = ${fmt(z)}`, `P(aX + bY ≤ ${fmt(c)}) = ${pr(P)}`, `P(aX + bY &gt; ${fmt(c)}) = ${pr(1 - P)}`])}
          <p><strong>Desarrollo:</strong></p>
          ${paso('4.1 Media', 'La media de una combinación lineal es la combinación de las medias.', `μ = a·μX + b·μY\nμ = (${fmt(a)})(${fmt(mx)}) + (${fmt(b)})(${fmt(my)})\nμ = ${fmt(mw)}`)}
          ${paso('4.2 Varianza y desviación estándar', 'Incluye el término de covarianza 2ab·ρ·σX·σY.', `σ² = a²σX² + b²σY² + 2ab·ρ·σX·σY\nσ² = (${fmt(a)})²(${fmt(sx)})² + (${fmt(b)})²(${fmt(sy)})² + 2(${fmt(a)})(${fmt(b)})(${fmt(rho)})(${fmt(sx)})(${fmt(sy)})\nσ² = ${fmt(v)}\nσ = ${fmt(sw)}`)}
          ${paso('4.3 Valor estandarizado', 'Se convierte c a la normal estándar.', `Z = (c − μ) / σ\nZ = (${fmt(c)} − ${fmt(mw)}) / ${fmt(sw)}\nZ = ${fmt(z)}`)}
          ${paso('4.4 Probabilidad', 'Se toma el área de la normal estándar.', `P(aX + bY ≤ ${fmt(c)}) = P(Z ≤ ${fmt(z)}) = ${fmt(P, 4)}\nP(aX + bY &gt; ${fmt(c)}) = 1 − ${fmt(P, 4)} = ${fmt(1 - P, 4)}`)}`;
      } else {
        if (!(Math.abs(rho) < 1)) throw new Error('ρ debe estar entre −1 y 1 (sin incluirlos).');
        if (modo === 'cond') {
          const x0 = num('n-x0', 'x₀'), y0 = num('n-y0', 'y₀');
          const cov = rho * sx * sy, mc = my + rho * (sy / sx) * (x0 - mx), sc = sy * Math.sqrt(1 - rho * rho);
          const z = (y0 - mc) / sc, P = cdfN(z);
          html = `<h3>1. Parámetros y condicional (dado X = x₀)</h3>
            ${bloque('Datos:', [...datosBase, `x₀ = ${fmt(x0)}`, `y₀ = ${fmt(y0)}`])}
            ${bloque('Resultados:', [`Cov(X,Y) = ${fmt(cov)}`, `μY|X=x₀ = ${fmt(mc)}`, `σY|X=x₀ = ${fmt(sc)}`, `Z = ${fmt(z)}`, `P(Y ≤ ${fmt(y0)} | X = ${fmt(x0)}) = ${pr(P)}`, `P(Y &gt; ${fmt(y0)} | X = ${fmt(x0)}) = ${pr(1 - P)}`])}
            <p><strong>Desarrollo:</strong></p>
            ${paso('1.1 Covarianza Cov(X,Y)', 'Mide el grado de variación conjunta de X y Y.', `Cov(X,Y) = ρ·σX·σY\nCov(X,Y) = (${fmt(rho)})(${fmt(sx)})(${fmt(sy)})\nCov(X,Y) = ${fmt(cov)}`)}
            ${paso('1.2 Media condicional μY|X=x₀', 'Es el valor esperado de Y cuando X vale exactamente x₀.', `μY|x₀ = μY + ρ(σY/σX)(x₀ − μX)\nμY|x₀ = ${fmt(my)} + (${fmt(rho)})(${fmt(sy)}/${fmt(sx)})(${fmt(x0)} − ${fmt(mx)})\nμY|x₀ = ${fmt(mc)}`)}
            ${paso('1.3 Desviación estándar condicional σY|X=x₀', 'Indica cuánto varía Y alrededor de esa media condicional.', `σY|x₀ = σY·√(1 − ρ²)\nσY|x₀ = ${fmt(sy)}·√(1 − (${fmt(rho)})²)\nσY|x₀ = ${fmt(sy)}·√${fmt(1 - rho * rho)}\nσY|x₀ = ${fmt(sc)}`)}
            ${paso('1.4 Valor estandarizado Z', 'Convierte el límite y₀ a la normal estándar usando la media y desviación condicionales.', `Z = (y₀ − μY|x₀) / σY|x₀\nZ = (${fmt(y0)} − ${fmt(mc)}) / ${fmt(sc)}\nZ = ${fmt(z)}`)}
            ${paso('1.5 Probabilidades condicionales', 'Se toma el área de la normal estándar.', `P(Y ≤ ${fmt(y0)} | X = ${fmt(x0)}) = P(Z ≤ ${fmt(z)}) = ${fmt(P, 4)}\nP(Y &gt; ${fmt(y0)} | X = ${fmt(x0)}) = 1 − ${fmt(P, 4)} = ${fmt(1 - P, 4)}`)}`;
        } else if (modo === 'dens') {
          const x0 = num('n-fx', 'x₀'), y0 = num('n-fy', 'y₀');
          const zx = (x0 - mx) / sx, zy = (y0 - my) / sy, q = 1 - rho * rho;
          const cte = 1 / (2 * Math.PI * sx * sy * Math.sqrt(q));
          const ex = -1 / (2 * q) * (zx * zx - 2 * rho * zx * zy + zy * zy);
          const f = cte * Math.exp(ex);
          html = `<h3>5. Densidad conjunta f(x₀, y₀)</h3>
            ${bloque('Datos:', [...datosBase, `x₀ = ${fmt(x0)}`, `y₀ = ${fmt(y0)}`])}
            ${bloque('Resultados:', [`Z de X = ${fmt(zx)}`, `Z de Y = ${fmt(zy)}`, `Constante = ${fmtP(cte)}`, `Exponente = ${fmt(ex)}`, `f(${fmt(x0)}, ${fmt(y0)}) = ${fmtP(f)}`])}
            <p>La densidad es la altura de la función en ese punto, no una probabilidad (P(X = x₀, Y = y₀) vale 0 en variables continuas).</p>
            <p><strong>Desarrollo:</strong></p>
            ${paso('5.1 Valores estandarizados', 'Se convierten x₀ y y₀ con Z = (valor − μ) / σ.', `Z de X = (${fmt(x0)} − ${fmt(mx)}) / ${fmt(sx)} = ${fmt(zx)}\nZ de Y = (${fmt(y0)} − ${fmt(my)}) / ${fmt(sy)} = ${fmt(zy)}`)}
            ${paso('5.2 Constante', 'Es el factor que multiplica a la exponencial.', `1 / (2π·σX·σY·√(1 − ρ²))\n= 1 / (2π·${fmt(sx)}·${fmt(sy)}·√(1 − (${fmt(rho)})²))\n= 1 / (2π·${fmt(sx)}·${fmt(sy)}·${fmt(Math.sqrt(q))})\n= ${fmtP(cte)}`)}
            ${paso('5.3 Exponente', 'Combina las dos variables estandarizadas y la correlación.', `−1/(2(1 − ρ²)) · [Z_X² − 2ρ·Z_X·Z_Y + Z_Y²]\n= −1/(2(${fmt(q)})) · [(${fmt(zx)})² − 2(${fmt(rho)})(${fmt(zx)})(${fmt(zy)}) + (${fmt(zy)})²]\n= ${fmt(ex)}`)}
            ${paso('5.4 Densidad conjunta', 'Se multiplica la constante por e elevado al exponente.', `f(x₀, y₀) = constante · e^(exponente)\nf(${fmt(x0)}, ${fmt(y0)}) = ${fmtP(cte)} · e^(${fmt(ex)})\nf(${fmt(x0)}, ${fmt(y0)}) = ${fmtP(f)}`)}`;
        } else {
          const x1 = lim('n-x1', -Infinity), x2 = lim('n-x2', Infinity), y1 = lim('n-y1', -Infinity), y2 = lim('n-y2', Infinity);
          if (['n-x1', 'n-x2', 'n-y1', 'n-y2'].every(id => $(id).value.trim() === '')) throw new Error('Escribe al menos un límite (x₁, x₂, y₁ o y₂).');
          if (x1 >= x2 || y1 >= y2) throw new Error('Cada límite inferior debe ser menor que el superior.');
          const F = (a, b) => cdfBiv(a, b, mx, sx, my, sy, rho);
          const Fa = F(x2, y2), Fb = F(x1, y2), Fc = F(x2, y1), Fd = F(x1, y1);
          const P = Math.min(1, Math.max(0, Fa - Fb - Fc + Fd));
          const vacio = id => ($(id).value.trim() === '' ? ' (no se escribió)' : '');
          html = `<h3>2. Probabilidad conjunta</h3>
            ${bloque('Datos:', [...datosBase, `x₁ = ${inf(x1)}${vacio('n-x1')}`, `x₂ = ${inf(x2)}${vacio('n-x2')}`, `y₁ = ${inf(y1)}${vacio('n-y1')}`, `y₂ = ${inf(y2)}${vacio('n-y2')}`])}
            ${bloque('Resultados:', [`P(${inf(x1)} ≤ X ≤ ${inf(x2)}, ${inf(y1)} ≤ Y ≤ ${inf(y2)}) = ${pr(P)}`])}
            <p><strong>Desarrollo:</strong></p>
            ${paso('2.1 Estandarizar los límites', 'Cada límite se convierte con Z = (límite − μ) / σ.', `Z de x₁ = ${zz(x1, mx, sx)}    Z de x₂ = ${zz(x2, mx, sx)}\nZ de y₁ = ${zz(y1, my, sy)}    Z de y₂ = ${zz(y2, my, sy)}`)}
            ${paso('2.2 Probabilidad del área P(x₁ ≤ X ≤ x₂, y₁ ≤ Y ≤ y₂)', 'Se resta la probabilidad acumulada F(a,b) = P(X ≤ a, Y ≤ b) de las esquinas del rectángulo. F no tiene fórmula cerrada; el programa la integra numéricamente (regla de Simpson) con ρ = ' + fmt(rho) + '.', `P = F(x₂,y₂) − F(x₁,y₂) − F(x₂,y₁) + F(x₁,y₁)\nP = ${fmt(Fa, 6)} − ${fmt(Fb, 6)} − ${fmt(Fc, 6)} + ${fmt(Fd, 6)}\nP = ${fmt(P, 6)}`)}`;
        }
      }
    }
    $('res-nor').innerHTML = html;
  } catch (e) {
    $('msg-nor').textContent = e.message;
  }
});

/* ================= Inicio ================= */
construirTabla();
modoNormal();