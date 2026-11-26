/* PayMexBTC · plataforma operativa del corredor México ⇄ Hong Kong.
 * Un solo script, sin dependencias. Precio de referencia desde un agregador público cuando hay red;
 * todo lo demás (régimen, cobertura, tesorería, oráculo, market making) se calcula aquí en vivo. */
'use strict';

/* ============================================================
 * Utilidades
 * ============================================================ */
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
const clamp = (x, a, b) => Math.min(b, Math.max(a, x));
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));

const store = {
  get(k, d) { try { const v = localStorage.getItem('pmx:' + k); return v == null ? d : JSON.parse(v); } catch { return d; } },
  set(k, v) { try { localStorage.setItem('pmx:' + k, JSON.stringify(v)); } catch { /* almacenamiento no disponible */ } },
};

const NF = {};
function fmt(x, d = 2) {
  if (x == null || !isFinite(x)) return '—';
  const f = NF[d] || (NF[d] = new Intl.NumberFormat('es-MX', { minimumFractionDigits: d, maximumFractionDigits: d }));
  return f.format(x);
}
function compact(x) {
  const a = Math.abs(x);
  if (a >= 1e9) return fmt(x / 1e9, 2) + ' B';
  if (a >= 1e6) return fmt(x / 1e6, 2) + ' M';
  if (a >= 1e4) return fmt(x / 1e3, 1) + ' K';
  return fmt(x, 0);
}
const pct = (x, d = 1) => fmt(x * 100, d) + ' %';
const bps = (x, d = 1) => fmt(x * 1e4, d) + ' pb';
const sgn = (x, d = 2) => (x > 0 ? '+' : '') + fmt(x, d);

const TZ_MX = 'America/Mexico_City', TZ_HK = 'Asia/Hong_Kong';
const TF = {};
function tclock(ts, tz = TZ_MX, sec = false) {
  const k = tz + sec;
  const f = TF[k] || (TF[k] = new Intl.DateTimeFormat('es-MX', { timeZone: tz, hour: '2-digit', minute: '2-digit', second: sec ? '2-digit' : undefined, hour12: false }));
  return f.format(ts);
}
function tdate(ts) {
  return new Intl.DateTimeFormat('es-MX', { timeZone: TZ_MX, day: '2-digit', month: 'short', hour: '2-digit', minute: '2-digit', hour12: false }).format(ts);
}
function hourIn(ts, tz) { return +new Intl.DateTimeFormat('en-US', { timeZone: tz, hour: 'numeric', hour12: false }).format(ts) % 24; }
function minuteOfDayMX(ts) {
  const p = new Intl.DateTimeFormat('en-US', { timeZone: TZ_MX, hour: 'numeric', minute: 'numeric', hour12: false }).formatToParts(ts);
  const h = +p.find((x) => x.type === 'hour').value % 24, m = +p.find((x) => x.type === 'minute').value;
  return h * 60 + m;
}
function ymd(ts) {
  const p = new Intl.DateTimeFormat('en-CA', { timeZone: TZ_MX, year: 'numeric', month: '2-digit', day: '2-digit' }).format(ts);
  return p.replace(/-/g, '');
}

/* Aleatoriedad */
const rnd = Math.random;
function randn() { let u = 0, v = 0; while (!u) u = rnd(); while (!v) v = rnd(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); }
function poisson(l) { if (l <= 0) return 0; if (l > 30) return Math.max(0, Math.round(l + Math.sqrt(l) * randn())); let L = Math.exp(-l), k = 0, p = 1; do { k++; p *= rnd(); } while (p > L); return k - 1; }
function lognormal(mean, sd) { const s2 = Math.log(1 + (sd * sd) / (mean * mean)); return Math.exp(Math.log(mean) - s2 / 2 + Math.sqrt(s2) * randn()); }
function mulberry32(a) { return function () { a |= 0; a = (a + 0x6d2b79f5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const pick = (arr, r = rnd) => arr[Math.floor(r() * arr.length)];
const digits = (n) => Array.from({ length: n }, () => Math.floor(rnd() * 10)).join('');
const PHI = (z) => { const t = 1 / (1 + 0.2316419 * Math.abs(z)); const d = 0.3989423 * Math.exp(-z * z / 2); const p = d * t * (0.3193815 + t * (-0.3565638 + t * (1.781478 + t * (-1.821256 + t * 1.330274)))); return z > 0 ? 1 - p : p; };

/* SHA-256 síncrono (constantes derivadas de primos al arrancar) */
const SHA = (() => {
  const primes = []; for (let n = 2; primes.length < 64; n++) { if (primes.every((p) => n % p)) primes.push(n); }
  const frac = (x) => ((x - Math.floor(x)) * 4294967296) >>> 0;
  const K = new Uint32Array(primes.map((p) => frac(Math.cbrt(p))));
  const H0 = primes.slice(0, 8).map((p) => frac(Math.sqrt(p)));
  const enc = new TextEncoder();
  return function sha256(input) {
    const msg = typeof input === 'string' ? enc.encode(input) : input;
    const l = msg.length, bitLen = l * 8;
    const n = (((l + 9 + 63) >> 6) << 6);
    const buf = new Uint8Array(n); buf.set(msg); buf[l] = 0x80;
    const dv = new DataView(buf.buffer);
    dv.setUint32(n - 4, bitLen >>> 0); dv.setUint32(n - 8, Math.floor(bitLen / 4294967296));
    const H = H0.slice(); const W = new Uint32Array(64);
    for (let o = 0; o < n; o += 64) {
      for (let i = 0; i < 16; i++) W[i] = dv.getUint32(o + i * 4);
      for (let i = 16; i < 64; i++) {
        const a = W[i - 15], b = W[i - 2];
        const s0 = ((a >>> 7) | (a << 25)) ^ ((a >>> 18) | (a << 14)) ^ (a >>> 3);
        const s1 = ((b >>> 17) | (b << 15)) ^ ((b >>> 19) | (b << 13)) ^ (b >>> 10);
        W[i] = (W[i - 16] + s0 + W[i - 7] + s1) >>> 0;
      }
      let [a, b, c, d, e, f, g, h] = H;
      for (let i = 0; i < 64; i++) {
        const S1 = ((e >>> 6) | (e << 26)) ^ ((e >>> 11) | (e << 21)) ^ ((e >>> 25) | (e << 7));
        const ch = (e & f) ^ (~e & g);
        const t1 = (h + S1 + ch + K[i] + W[i]) >>> 0;
        const S0 = ((a >>> 2) | (a << 30)) ^ ((a >>> 13) | (a << 19)) ^ ((a >>> 22) | (a << 10));
        const mj = (a & b) ^ (a & c) ^ (b & c);
        const t2 = (S0 + mj) >>> 0;
        h = g; g = f; f = e; e = (d + t1) >>> 0; d = c; c = b; b = a; a = (t1 + t2) >>> 0;
      }
      H[0] = (H[0] + a) >>> 0; H[1] = (H[1] + b) >>> 0; H[2] = (H[2] + c) >>> 0; H[3] = (H[3] + d) >>> 0;
      H[4] = (H[4] + e) >>> 0; H[5] = (H[5] + f) >>> 0; H[6] = (H[6] + g) >>> 0; H[7] = (H[7] + h) >>> 0;
    }
    return H.map((x) => x.toString(16).padStart(8, '0')).join('');
  };
})();
const hexBytes = (hex) => new Uint8Array(hex.match(/../g).map((h) => parseInt(h, 16)));
const short = (h, n = 10) => h.slice(0, n) + '…' + h.slice(-6);

/* Bech32 (BIP-173) para direcciones de custodia */
const BECH = 'qpzry9x8gf2tvdw0s3jn54khce6mua7l';
function bechPolymod(v) { const G = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]; let chk = 1; for (const x of v) { const b = chk >> 25; chk = ((chk & 0x1ffffff) << 5) ^ x; for (let i = 0; i < 5; i++) if ((b >> i) & 1) chk ^= G[i]; } return chk; }
function bech32(hrp, program) {
  const data = [0]; let acc = 0, bits = 0;
  for (const b of program) { acc = (acc << 8) | b; bits += 8; while (bits >= 5) { bits -= 5; data.push((acc >> bits) & 31); } }
  if (bits) data.push((acc << (5 - bits)) & 31);
  const he = [...hrp].map((c) => c.charCodeAt(0) >> 5).concat([0], [...hrp].map((c) => c.charCodeAt(0) & 31));
  const pm = bechPolymod(he.concat(data, [0, 0, 0, 0, 0, 0])) ^ 1;
  const chk = []; for (let i = 0; i < 6; i++) chk.push((pm >> (5 * (5 - i))) & 31);
  return hrp + '1' + data.concat(chk).map((d) => BECH[d]).join('');
}

/* ============================================================
 * Identificadores mexicanos y de Hong Kong
 * ============================================================ */
const BANKS_MX = { '002': 'Banamex', '012': 'BBVA México', '014': 'Santander', '021': 'HSBC México', '036': 'Inbursa', '044': 'Scotiabank', '058': 'Banregio', '072': 'Banorte', '127': 'Banco Azteca', '137': 'BanCoppel', '646': 'STP' };
function clabeCheck(d17) { const w = [3, 7, 1]; let s = 0; for (let i = 0; i < 17; i++) s += (+d17[i] * w[i % 3]) % 10; return (10 - (s % 10)) % 10; }
function makeClabe(bank) { const b = bank || pick(Object.keys(BANKS_MX).filter((k) => k !== '646')); const d17 = b + digits(3) + digits(11); return d17 + clabeCheck(d17); }
function validClabe(v) {
  if (!/^\d{18}$/.test(v)) return { ok: false, msg: 'La CLABE tiene 18 dígitos.' };
  if (clabeCheck(v.slice(0, 17)) !== +v[17]) return { ok: false, msg: 'El dígito verificador no coincide.' };
  const bank = BANKS_MX[v.slice(0, 3)];
  return { ok: true, msg: (bank || 'Banco ' + v.slice(0, 3)) + ' · dígito verificador correcto' };
}
function validRfc(v) {
  const m = /^([A-ZÑ&]{3,4})(\d{2})(\d{2})(\d{2})([A-Z\d]{3})$/.exec(v);
  if (!m) return { ok: false, msg: '12 caracteres (persona moral) o 13 (física).' };
  const mo = +m[3], da = +m[4];
  if (mo < 1 || mo > 12 || da < 1 || da > 31) return { ok: false, msg: 'La fecha dentro del RFC no es válida.' };
  return { ok: true, msg: m[1].length === 3 ? 'Persona moral' : 'Persona física' };
}
function validFps(v) {
  const s = v.replace(/\s|-/g, '');
  if (/^\d{7}$|^\d{9}$/.test(s)) return { ok: true, msg: 'FPS ID' };
  if (/^\+?852[5679]\d{7}$/.test(s)) return { ok: true, msg: 'Teléfono registrado en FPS' };
  if (/^[^@\s]+@[^@\s]+\.[a-z]{2,}$/i.test(s)) return { ok: true, msg: 'Correo registrado en FPS' };
  return { ok: false, msg: 'FPS ID de 7 o 9 dígitos, +852 y 8 dígitos, o correo.' };
}
const CO_A = ['Importadora', 'Comercializadora', 'Grupo Industrial', 'Distribuidora', 'Manufacturas', 'Textiles', 'Electrónica', 'Autopartes'];
const CO_B = ['del Bajío', 'Pacífico Norte', 'Altamira', 'Sierra Madre', 'Valle de Toluca', 'Golfo Centro', 'Laguna', 'Mixteca'];
const HK_A = ['Kowloon Bay', 'Harbour Gate', 'Victoria Peak', 'Tsim Sha Tsui', 'Kwun Tong', 'Sheung Wan', 'Lantau', 'Wan Chai'];
const HK_B = ['Trading Co., Limited', 'Electronics Ltd.', 'Components Limited', 'Supply Chain Ltd.', 'Textile Co., Limited', 'Precision Parts Ltd.'];
function makeClient() {
  const a = pick(CO_A), b = pick(CO_B);
  const name = a + ' ' + b + ', S.A. de C.V.';
  const ini = (a.replace(/[^A-Z]/g, '') + b.replace(/[^A-Z]/g, '') + 'XXX').slice(0, 3).toUpperCase();
  const yy = String(90 + Math.floor(rnd() * 30)).slice(-2).padStart(2, '0');
  const rfc = ini + yy + String(1 + Math.floor(rnd() * 12)).padStart(2, '0') + String(1 + Math.floor(rnd() * 28)).padStart(2, '0') + pick('ABCDEFGHJKLMNPRSTUVWXYZ'.split('')) + pick('ABCDEFGHJKLMNPRSTUVWXYZ123456789'.split('')) + Math.floor(rnd() * 10);
  const amount = Math.round(lognormal(52000, 60000) / 100) * 100;
  const fps = rnd() < 0.5 ? digits(7) : '+852 ' + pick(['5', '6', '9']) + digits(7);
  return { sender: name, rfc, clabe: makeClabe(), amount: clamp(amount, 2000, 480000), benef: pick(HK_A) + ' ' + pick(HK_B), fps };
}

/* ============================================================
 * Estado
 * ============================================================ */
const MCR = [1.15, 1.35, 1.65];
const REG = [
  { name: 'Baja volatilidad', short: 'Calma', s: 'good', color: 'var(--color-good)' },
  { name: 'Tendencia controlada', short: 'Tendencia', s: 'warn', color: 'var(--color-warn)' },
  { name: 'Estrés sistémico', short: 'Estrés', s: 'crit', color: 'var(--color-crit)' },
];
const CONTRACT = 100;   // USD por contrato perpetuo inverso
const LEV = 5;          // apalancamiento máximo permitido del corto
const GEN = {           // generador de mercado con cambio de régimen (por minuto)
  P: [[0.988, 0.011, 0.001], [0.02, 0.972, 0.008], [0.03, 0.07, 0.90]],
  sd: [0.0007, 0.0014, 0.0034], mu: [0, 0.00022, -0.0006], vol: [0, 0.45, 1.15],
};

const S = {
  usd: 0, mxn: 18.2, hkd: 7.79, anchor: null, src: 'init',
  candles: [], cur: null, genReg: 0, trend: 1, lockUntil: 0,
  funding: 0.00009, hmm: null, filt: [], live: [1, 0, 0], sinceTrain: 0,
  post: null, breaker: false, oracleSrc: [], attacks: {}, lastPayload: null,
  vault: null, mm: null, pairs: null, tape: {}, orders: [], activity: [], seq: 0,
  view: 'panel', engTab: 'hmm', pair: 'PMXMXN', running: false, kelly: null,
};

/* ============================================================
 * Mercado: historia con régimen + ticks en vivo (Merton)
 * ============================================================ */
function genStep(reg) {
  return GEN.mu[reg] * (reg === 1 ? S.trend : 1) + GEN.sd[reg] * randn();
}
function buildHistory(lastPrice) {
  const N = 360, now = Date.now(), m0 = Math.floor(now / 60000) * 60000;
  let reg = 0; const rs = [], regs = [];
  for (let i = 0; i < N; i++) {
    const r = rnd(), row = GEN.P[reg]; reg = r < row[0] ? 0 : r < row[0] + row[1] ? 1 : 2;
    if (i >= N - 40) reg = 0; // la sesión abre en calma; el estrés llega por el mercado o por un choque
    if (reg === 1 && rnd() < 0.05) S.trend *= -1;
    rs.push(genStep(reg)); regs.push(reg);
  }
  const total = rs.reduce((a, b) => a + b, 0);
  let p = lastPrice * Math.exp(-total);
  const out = [];
  for (let i = 0; i < N; i++) {
    const o = p, c = p * Math.exp(rs[i]);
    const wig = GEN.sd[regs[i]] * 0.6;
    out.push({ t: m0 - (N - i) * 60000, o, c, h: Math.max(o, c) * (1 + Math.abs(randn()) * wig), l: Math.min(o, c) * (1 - Math.abs(randn()) * wig), v: Math.exp(3 + GEN.vol[regs[i]] + 0.25 * randn()) });
    p = c;
  }
  S.genReg = reg;
  S.candles = out;
  S.cur = { t: m0, o: p, h: p, l: p, c: p, v: 0, n: 0 };
  S.usd = p;
}
function obsOf(c, prevClose) { return [Math.log(c.c / prevClose), Math.log(Math.max(c.v, 1e-6))]; }
function allObs() { const C = S.candles; const o = []; for (let i = 1; i < C.length; i++) o.push(obsOf(C[i], C[i - 1].c)); return o; }

function marketTick() {
  const now = Date.now();
  const reg = S.genReg;
  // Difusión con saltos por segundo
  let r = GEN.mu[reg] * (reg === 1 ? S.trend : 1) / 60 + (GEN.sd[reg] / Math.sqrt(60)) * randn();
  if (rnd() < (reg === 2 ? 0.004 : 0.0004)) r += (reg === 2 ? -0.004 : 0) + 0.003 * randn();
  // reversión suave hacia la referencia externa
  if (S.anchor && Date.now() > S.lockUntil) r += 0.004 * Math.log(S.anchor.usd / S.usd);
  S.usd *= Math.exp(r);
  S.mxn *= Math.exp(0.00004 * randn() + (S.anchor ? 0.01 * Math.log(S.anchor.mxn / S.mxn) : 0));
  S.hkd = clamp(S.hkd * Math.exp(0.000006 * randn() + (S.anchor ? 0.01 * Math.log(S.anchor.hkd / S.hkd) : 0)), 7.75, 7.85);
  S.funding = clamp(S.funding + 0.000002 * randn() + 0.01 * (0.0001 - S.funding) - (S.live[2] > 0.5 ? 0.0000015 : 0), -0.0004, 0.0006);
  const c = S.cur;
  c.c = S.usd; c.h = Math.max(c.h, S.usd); c.l = Math.min(c.l, S.usd);
  c.v += Math.exp(3 + GEN.vol[reg] + 0.25 * randn()) / 60; c.n++;
  if (now - c.t >= 60000) closeCandle(now);
  else liveRegime();
}
function closeCandle(now) {
  const c = S.cur;
  if (c.n < 50) c.v *= 60 / Math.max(1, c.n);
  const prev = S.candles[S.candles.length - 1];
  S.candles.push({ t: c.t, o: c.o, h: c.h, l: c.l, c: c.c, v: c.v });
  if (S.candles.length > 361) S.candles.shift();
  if (S.hmm) {
    const o = obsOf(c, prev.c);
    const p = filterStep(S.filt[S.filt.length - 1], o, S.hmm);
    S.filt.push(p); if (S.filt.length > 360) S.filt.shift();
  }
  // transición del generador
  if (Date.now() > S.lockUntil) {
    const r = rnd(), row = GEN.P[S.genReg];
    S.genReg = r < row[0] ? 0 : r < row[0] + row[1] ? 1 : 2;
    if (S.genReg === 1 && rnd() < 0.08) S.trend *= -1;
  }
  S.cur = { t: Math.floor(now / 60000) * 60000, o: c.c, h: c.c, l: c.c, c: c.c, v: 0, n: 0 };
  if (++S.sinceTrain >= 15) { S.sinceTrain = 0; setTimeout(trainHMM, 0); }
  liveRegime();
}
function liveRegime() {
  if (!S.hmm) return;
  const c = S.cur, prev = S.candles[S.candles.length - 1];
  if (c.n < 5) { S.live = S.filt[S.filt.length - 1]; return; }
  const vEst = c.v * 60 / c.n;
  // retorno parcial escalado a la duración restante con la volatilidad de cada estado
  const o = [Math.log(c.c / prev.c), Math.log(vEst)];
  S.live = filterStep(S.filt[S.filt.length - 1], o, S.hmm);
}
function applyShock() {
  S.usd *= 0.92; S.cur.c = S.usd; S.cur.l = Math.min(S.cur.l, S.usd); S.cur.v += Math.exp(4.6) * Math.max(1, S.cur.n) / 60;
  S.genReg = 2; S.lockUntil = Date.now() + 6 * 60000;
  liveRegime();
}

/* Referencia externa (agregador público). Sin red, se conserva el último precio conocido. */
async function fetchReference(first) {
  try {
    const ctl = new AbortController(); const to = setTimeout(() => ctl.abort(), 5000);
    const r = await fetch('https://api.coingecko.com/api/v3/simple/price?ids=bitcoin&vs_currencies=usd,mxn,hkd', { signal: ctl.signal, cache: 'no-store' });
    clearTimeout(to);
    if (!r.ok) throw new Error('http ' + r.status);
    const j = await r.json(); const b = j.bitcoin;
    if (!b || !b.usd) throw new Error('sin datos');
    const ref = { usd: b.usd, mxn: b.mxn / b.usd, hkd: b.hkd / b.usd, t: Date.now() };
    if (first && !S.vault) {
      const k = ref.usd / S.usd;
      for (const c of S.candles) { c.o *= k; c.h *= k; c.l *= k; c.c *= k; }
      for (const key of ['o', 'h', 'l', 'c']) S.cur[key] *= k;
      S.usd = ref.usd; S.mxn = ref.mxn; S.hkd = ref.hkd;
      if (S.post) { S.post.mu *= k; S.post.var *= k * k; }
    }
    S.anchor = ref; S.src = 'ext';
    store.set('lastPrice', ref);
  } catch {
    if (S.src === 'init') S.src = 'cache';
  }
  renderFeedSrc();
}

/* ============================================================
 * Motor 1 · HMM (Baum-Welch) — colateralización dinámica
 * ============================================================ */
const LN2PI = 0.9189385332046727;
const logN = (x, m, s) => { const z = (x - m) / s; return -0.5 * z * z - Math.log(s) - LN2PI; };
const emis = (o, k, P) => logN(o[0], P.mu[k][0], P.sd[k][0]) + logN(o[1], P.mu[k][1], P.sd[k][1]);

function baumWelch(obs, maxIt = 40) {
  const T = obs.length, K = 3;
  const order = obs.map((_, i) => i).sort((a, b) => Math.abs(obs[a][0]) - Math.abs(obs[b][0]));
  const cuts = [0, Math.floor(T * 0.55), Math.floor(T * 0.88), T];
  const mu = [], sd = [];
  for (let k = 0; k < K; k++) {
    const g = order.slice(cuts[k], cuts[k + 1]).map((i) => obs[i]);
    const m = [0, 1].map((d) => g.reduce((a, o) => a + o[d], 0) / g.length);
    const s = [0, 1].map((d) => Math.sqrt(g.reduce((a, o) => a + (o[d] - m[d]) ** 2, 0) / g.length) || 1e-4);
    mu.push(m); sd.push([Math.max(s[0], 1e-5), Math.max(s[1], 0.05)]);
  }
  let A = [[0.95, 0.04, 0.01], [0.05, 0.9, 0.05], [0.04, 0.1, 0.86]], pi = [0.6, 0.3, 0.1];
  let ll = -Infinity, it = 0;
  const alpha = Array.from({ length: T }, () => new Float64Array(K));
  const beta = Array.from({ length: T }, () => new Float64Array(K));
  const B = Array.from({ length: T }, () => new Float64Array(K));
  const cs = new Float64Array(T), mx = new Float64Array(T);
  for (it = 1; it <= maxIt; it++) {
    const P = { mu, sd };
    for (let t = 0; t < T; t++) {
      let m = -Infinity; const e = [0, 1, 2].map((k) => emis(obs[t], k, P));
      for (const x of e) m = Math.max(m, x);
      mx[t] = m; for (let k = 0; k < K; k++) B[t][k] = Math.exp(e[k] - m);
    }
    // forward escalado
    for (let t = 0; t < T; t++) {
      let s = 0;
      for (let j = 0; j < K; j++) {
        let a = 0;
        if (t === 0) a = pi[j]; else for (let i = 0; i < K; i++) a += alpha[t - 1][i] * A[i][j];
        alpha[t][j] = a * B[t][j]; s += alpha[t][j];
      }
      cs[t] = s || 1e-300; for (let j = 0; j < K; j++) alpha[t][j] /= cs[t];
    }
    let nll = 0; for (let t = 0; t < T; t++) nll += Math.log(cs[t]) + mx[t];
    // backward escalado
    for (let k = 0; k < K; k++) beta[T - 1][k] = 1;
    for (let t = T - 2; t >= 0; t--) for (let i = 0; i < K; i++) { let s = 0; for (let j = 0; j < K; j++) s += A[i][j] * B[t + 1][j] * beta[t + 1][j]; beta[t][i] = s / cs[t + 1]; }
    // E: gamma y xi
    const g = Array.from({ length: T }, (_, t) => { const r = [0, 1, 2].map((k) => alpha[t][k] * beta[t][k]); const s = r[0] + r[1] + r[2]; return r.map((x) => x / s); });
    const xi = [[0, 0, 0], [0, 0, 0], [0, 0, 0]];
    for (let t = 0; t < T - 1; t++) {
      let s = 0; const tmp = [];
      for (let i = 0; i < K; i++) { tmp.push([]); for (let j = 0; j < K; j++) { const v = alpha[t][i] * A[i][j] * B[t + 1][j] * beta[t + 1][j]; tmp[i].push(v); s += v; } }
      for (let i = 0; i < K; i++) for (let j = 0; j < K; j++) xi[i][j] += tmp[i][j] / s;
    }
    // M
    pi = g[0].map((x) => clamp(x, 1e-4, 1)); { const s = pi[0] + pi[1] + pi[2]; pi = pi.map((x) => x / s); }
    A = xi.map((row) => { const s = row.reduce((a, b) => a + b, 0) || 1; return row.map((x) => Math.max(x / s, 1e-5)); });
    for (let k = 0; k < K; k++) {
      let w = 0; const m = [0, 0], v = [0, 0];
      for (let t = 0; t < T; t++) { w += g[t][k]; m[0] += g[t][k] * obs[t][0]; m[1] += g[t][k] * obs[t][1]; }
      m[0] /= w; m[1] /= w;
      for (let t = 0; t < T; t++) { v[0] += g[t][k] * (obs[t][0] - m[0]) ** 2; v[1] += g[t][k] * (obs[t][1] - m[1]) ** 2; }
      mu[k] = m; sd[k] = [Math.max(Math.sqrt(v[0] / w), 1e-5), Math.max(Math.sqrt(v[1] / w), 0.05)];
    }
    const gain = nll - ll; ll = nll;
    if (it > 2 && Math.abs(gain) < 1e-4) break;
  }
  // ordenar estados por volatilidad del retorno
  const idx = [0, 1, 2].sort((a, b) => sd[a][0] - sd[b][0]);
  return {
    A: idx.map((i) => idx.map((j) => A[i][j])), pi: idx.map((i) => pi[i]),
    mu: idx.map((i) => mu[i]), sd: idx.map((i) => sd[i]), ll, it: Math.min(it, maxIt), T, at: Date.now(),
  };
}
function filterStep(prev, o, P) {
  const pred = [0, 1, 2].map((j) => prev[0] * P.A[0][j] + prev[1] * P.A[1][j] + prev[2] * P.A[2][j]);
  const e = [0, 1, 2].map((k) => emis(o, k, P)); const m = Math.max(...e);
  const post = pred.map((p, k) => p * Math.exp(e[k] - m)); const s = post[0] + post[1] + post[2] || 1;
  return post.map((x) => x / s);
}
function filterAll(obs, P) {
  let p = P.pi.slice(); const out = [];
  for (const o of obs) { p = filterStep(p, o, P); out.push(p); }
  return out;
}
function trainHMM() {
  const obs = allObs();
  S.hmm = baumWelch(obs);
  S.filt = filterAll(obs, S.hmm);
  liveRegime();
}
const mcrNow = (p = S.live) => p[0] * MCR[0] + p[1] * MCR[1] + p[2] * MCR[2];
const regNow = (p = S.live) => p.indexOf(Math.max(...p));

function stressScenario(mag) {
  const P = S.hmm; const N = 1440, S0 = S.post ? S.post.mu : S.usd;
  const v = S.vault, B = vaultBTC(), L = v.supply;
  const crash = Math.log(1 - mag) / 480;
  let p = S.hmm.pi.slice(), lnS = 0; const pts = [];
  let minUn = Infinity, minHd = Infinity, maxM = 0, stressMin = 0, pausedMin = 0, breakAt = null;
  for (let t = 0; t < N; t++) {
    const reg = t < 480 ? 0 : t < 960 ? 2 : 1;
    const r = (reg === 2 ? crash : reg === 1 ? 0.00006 : 0) + GEN.sd[reg] * randn() * (reg === 2 ? 0.8 : 1);
    lnS += r;
    const vol = 3 + GEN.vol[reg] + 0.25 * randn();
    p = filterStep(p, [r, vol], P);
    const St = S0 * Math.exp(lnS);
    const un = B * St / L, hd = (St * B + L - L * St / S0) / L, m = mcrNow(p);
    if (un < minUn) minUn = un; if (hd < minHd) minHd = hd; if (m > maxM) maxM = m;
    if (regNow(p) === 2) stressMin++;
    if (hd < m) pausedMin++;
    if (breakAt == null && un < 1) breakAt = t;
    pts.push({ t, un, hd, m, S: St });
  }
  return { pts, minUn, minHd, maxM, stressMin, pausedMin, breakAt, mag, drop: 1 - Math.min(...pts.map((x) => x.S)) / S0 };
}

/* ============================================================
 * Bóveda, cobertura y tesorería
 * ============================================================ */
function initVault(price) {
  const saved = store.get('vault', null);
  if (saved && saved.v === 2) return saved;
  const L = 4250000, B = 1.8 * L / price;
  const req = L / (LEV * price);
  const margin = req * 1.6, hotHk = B * 0.06, hotMx = B * 0.03;
  return {
    v: 2, supply: L, hedge: { N: L, inv: 1 / price, realized: 0, fundingUsd: 0 },
    btc: { hotMx, hotHk, margin, cold: B - margin - hotHk - hotMx }, seed: (rnd() * 2 ** 31) | 0, born: Date.now(),
  };
}
const vaultBTC = () => { const b = S.vault.btc; return b.hotMx + b.hotHk + b.margin + b.cold; };
function vaultState(Spx = oraclePx()) {
  const v = S.vault, B = vaultBTC(), N = v.hedge.N, L = v.supply;
  const pnlBtc = N * (1 / Spx - v.hedge.inv);
  const V = Spx * (B + pnlBtc);
  const CR = V / L;
  const req = N / (LEV * Spx);
  const marginEff = v.btc.margin + pnlBtc;
  return { B, N, L, pnlBtc, V, CR, req, marginEff, mRatio: marginEff / req, delta: B - N * v.hedge.inv, surplusUsd: V - L, contracts: Math.round(N / CONTRACT) };
}
function hedgeAdjust(dN, origin) {
  const v = S.vault, px = oraclePx();
  const lastR = Math.abs(Math.log(S.cur.c / S.candles[S.candles.length - 1].c));
  const jump = lastR > 3 * GEN.sd[regNow()] ;
  const slices = jump ? Math.ceil(Math.abs(dN) / 5000) + 2 : 1;
  const slip = (0.6 + 8 * Math.sqrt(Math.abs(dN) / 25e6)) / (jump ? 1.6 : 1) * 1e-4 * (1 + 0.3 * Math.abs(randn()));
  const fill = px * (dN > 0 ? 1 - slip : 1 + slip); // vender (abrir corto) un poco abajo; recomprar arriba
  if (dN > 0) {
    const N1 = v.hedge.N + dN;
    v.hedge.inv = (v.hedge.N * v.hedge.inv + dN / fill) / N1; v.hedge.N = N1;
  } else {
    const c = -dN; const pnl = c * (1 / fill - v.hedge.inv);
    v.btc.margin += pnl; v.hedge.realized += pnl; v.hedge.N = Math.max(0, v.hedge.N - c);
  }
  const o = { t: Date.now(), origin, dN, contracts: Math.round(dN / CONTRACT), slices, px: fill, slip };
  S.orders.unshift(o); if (S.orders.length > 40) S.orders.pop();
  return o;
}
function accrueFunding(dtSec) {
  const v = S.vault; const usd = v.hedge.N * S.funding * dtSec / 28800; // el corto cobra cuando el fondeo es positivo
  v.hedge.fundingUsd += usd; v.btc.margin += usd / oraclePx();
}

/* Kelly + cero ruina */
const KP = { mu: 0.11, sig: 0.85, refill: 2, daily: 3.0e6, rho: 0.35, shareHk: 0.7, meanA: 2500, sdA: 3500 };
function flowProfile() {
  // λ por hora (CDMX) en USD; HKT = CDMX + 14
  const bump = (h, a, b) => { const c = (a + b) / 2, w = (b - a) / 2; const d = Math.min(Math.abs(h - c), 24 - Math.abs(h - c)); return Math.exp(-((d / w) ** 4)); };
  const hk = [], mx = [];
  for (let h = 0; h < 24; h++) { hk.push(0.12 + bump(h + 0.5, 19, 28)); mx.push(0.12 + bump(h + 0.5, 9, 18)); }
  const shk = hk.reduce((a, b) => a + b), smx = mx.reduce((a, b) => a + b);
  return { hk: hk.map((x) => (x / shk) * KP.daily * KP.shareHk), mx: mx.map((x) => (x / smx) * KP.daily * (1 - KP.shareHk)) };
}
function q999(usdWindow) {
  const lam = usdWindow / KP.meanA, EA2 = KP.sdA ** 2 + KP.meanA ** 2;
  return usdWindow + 3.09 * Math.sqrt(lam * EA2);
}
function kellyPlan() {
  const px = oraclePx(), vs = vaultState(px), B = vs.B, prof = flowProfile();
  const mdm = minuteOfDayMX(Date.now()), h0 = mdm / 60;
  const win = (arr) => { let s = 0; const W = KP.refill; for (let x = 0; x < W; x += 0.25) s += arr[Math.floor(h0 + x) % 24] * 0.25; return s; };
  const wHk = win(prof.hk), wMx = win(prof.mx);
  const floorHk = q999(wHk) / px, floorMx = q999(wMx) / px;
  const muHk = KP.mu * 2 * KP.shareHk, muMx = KP.mu * 2 * (1 - KP.shareHk);
  const s2 = KP.sig ** 2, det = s2 * (1 - KP.rho ** 2);
  let fHk = 0.5 * (muHk - KP.rho * muMx) / det, fMx = 0.5 * (muMx - KP.rho * muHk) / det;
  fHk = Math.max(0, fHk); fMx = Math.max(0, fMx);
  const floorM = vs.req * 1.5;
  const BUF = 1.6;
  let tHk = Math.max(fHk * B, floorHk * BUF), tMx = Math.max(fMx * B, floorMx * BUF), tM = floorM;
  const minCold = 0.5 * B;
  let capped = false;
  if (B - tHk - tMx - tM < minCold) {
    capped = true;
    const room = Math.max(0, B - minCold - tM - floorHk - floorMx), extra = Math.max(0, tHk - floorHk) + Math.max(0, tMx - floorMx);
    const k = extra > 0 ? Math.min(1, room / extra) : 0;
    tHk = floorHk + Math.max(0, tHk - floorHk) * k; tMx = floorMx + Math.max(0, tMx - floorMx) * k;
  }
  const tCold = B - tHk - tMx - tM;
  const a = S.vault.btc;
  const capHkUsd = Math.max(0, a.hotHk * px - q999(wHk));
  const capMxUsd = Math.max(0, a.hotMx * px - q999(wMx));
  const g = (f) => KP.mu * f - 0.5 * f * f * s2;
  // reglas
  const rules = [];
  const hkH = hourIn(Date.now(), TZ_HK), hkOpen = hkH >= 9 && hkH < 18;
  const hkOpenIn = hkOpen ? 0 : ((9 - hkH) + 24) % 24;
  rules.push(a.hotHk < floorHk
    ? { s: 'warn', t: 'Recargar liquidez HKD desde frío', d: 'Saldo ' + fmt(a.hotHk, 3) + ' BTC bajo el piso Q99.9 de ' + fmt(floorHk, 3) + ' BTC. Mover ' + fmt(tHk - a.hotHk, 3) + ' BTC (multifirma 3 de 5).' }
    : { s: 'good', t: 'Liquidez HKD sobre el piso', d: fmt(a.hotHk, 3) + ' BTC frente a ' + fmt(floorHk, 3) + ' BTC requeridos para ' + fmt(KP.refill, 1) + ' h.' });
  rules.push(a.hotMx < floorMx
    ? { s: 'warn', t: 'Recargar liquidez MXN desde frío', d: 'Mover ' + fmt(tMx - a.hotMx, 3) + ' BTC a la bóveda caliente MX.' }
    : { s: 'good', t: 'Liquidez MXN sobre el piso', d: fmt(a.hotMx, 3) + ' BTC frente a ' + fmt(floorMx, 3) + ' BTC.' });
  rules.push(vs.mRatio < 1.2
    ? { s: 'warn', t: 'Depositar margen de cobertura', d: 'Margen ' + fmt(vs.mRatio, 2) + '× del requerido; objetivo 1.5×. Mover ' + fmt(floorM - vs.marginEff, 3) + ' BTC.' }
    : { s: 'good', t: 'Margen de cobertura suficiente', d: fmt(vs.mRatio, 2) + '× del requerido (mínimo 1.2×).' });
  const over = a.hotMx > 2 * tMx ? 'MXN' : a.hotHk > 2 * tHk ? 'HKD' : null;
  rules.push(over
    ? { s: 'warn', t: 'Barrer excedente caliente ' + over + ' a frío', d: 'El saldo supera 2× el objetivo de Kelly.' }
    : { s: 'good', t: 'Sin excedente caliente', d: 'Ambas bóvedas calientes bajo 2× su objetivo.' });
  rules.push(hkOpenIn > 0 && hkOpenIn <= 2 && a.hotHk < 0.98 * tHk
    ? { s: 'warn', t: 'Precargar antes de la apertura bancaria de Hong Kong', d: 'Abre en ' + hkOpenIn + ' h; llevar HKD caliente a ' + fmt(tHk, 3) + ' BTC.' }
    : { s: 'good', t: 'Precarga de apertura', d: hkOpen ? 'Horario bancario de Hong Kong en curso (' + hkH + ':00 HKT).' : 'Próxima apertura de Hong Kong en ' + hkOpenIn + ' h.' });
  return {
    px, B, prof, h0, fHk, fMx, floorHk, floorMx, floorM, tHk, tMx, tM, tCold, capped, capHkUsd, capMxUsd, wHk, wMx, rules,
    growthFull: g((KP.mu) / s2), growthHalf: g(0.5 * KP.mu / s2),
  };
}
function rebalance(silent) {
  const k = kellyPlan(); const a = S.vault.btc;
  const total = vaultBTC(), pnl = vaultState().pnlBtc;
  const moves = { hotMx: k.tMx - a.hotMx, hotHk: k.tHk - a.hotHk, margin: k.tM - (a.margin + pnl) };
  a.hotMx = k.tMx; a.hotHk = k.tHk; a.margin = k.tM - pnl;
  a.cold = total - a.hotMx - a.hotHk - a.margin;
  persist();
  if (!silent) {
    addActivity({ type: 'rebalanceo', detail: 'Bóveda: HKD ' + sgn(moves.hotHk, 3) + ' · MXN ' + sgn(moves.hotMx, 3) + ' · margen ' + sgn(moves.margin, 3) + ' BTC', inTxt: '—', outTxt: '—', status: 'aplicado' });
    toast('Rebalanceo aplicado');
  }
}

/* ============================================================
 * Motor 4 · Oráculo bayesiano
 * ============================================================ */
const SOURCES = [
  { id: 'GLB-A', name: 'Agregador global A', noise: 0.00025, depth: 42e6 },
  { id: 'GLB-B', name: 'Agregador global B', noise: 0.0003, depth: 35e6 },
  { id: 'PERP', name: 'Índice de perpetuos', noise: 0.0004, depth: 60e6, basis: 0.00015 },
  { id: 'MX-L', name: 'Libro local MXN', noise: 0.0009, depth: 3.1e6 },
  { id: 'HK-L', name: 'Libro local HKD', noise: 0.0008, depth: 4.4e6 },
  { id: 'POOL', name: 'Pool on-chain', noise: 0.0014, depth: 1.6e6 },
];
function oracleTick() {
  const th = S.usd, now = Date.now(), A = S.attacks;
  const obs = SOURCES.map((s) => {
    let px = th * Math.exp(s.noise * randn() + (s.basis || 0)), depth = s.depth * (0.85 + 0.3 * rnd()), off = false, tag = null;
    if (A.flash > now && s.id === 'MX-L') { px = th * (0.81 + 0.01 * randn()); tag = 'flash'; }
    if (A.wash > now && s.id === 'POOL') { px = th * (1.035 + 0.002 * randn()); depth *= 12; tag = 'wash'; }
    if (A.drop > now && ['GLB-A', 'GLB-B', 'PERP', 'HK-L'].includes(s.id)) off = true;
    const sig = th * clamp(0.0006 * Math.sqrt(10e6 / depth), 0.00015, 0.003);
    return { ...s, px, depth, sig, off, tag };
  });
  const t0 = performance.now();
  const live = obs.filter((o) => !o.off);
  const med = live.map((o) => o.px).sort((a, b) => a - b)[Math.floor(live.length / 2)];
  const q = (th * 0.0008) ** 2;
  let mu0, var0;
  if (!S.post) { mu0 = med; var0 = (th * 0.01) ** 2; } else { mu0 = S.post.mu; var0 = S.post.var + q; }
  // EM: pesos de no-atípico, arrancando en la mediana
  const eps = 0.05, broad = (th * 0.05) ** 2;
  let mu = med, v = var0;
  for (const o of live) o.w = 1;
  for (let it = 0; it < 4; it++) {
    for (const o of live) {
      const pv = o.sig * o.sig + v;
      const lin = Math.exp(-((o.px - mu) ** 2) / (2 * pv)) / Math.sqrt(pv);
      const lout = Math.exp(-((o.px - mu) ** 2) / (2 * broad)) / Math.sqrt(broad);
      o.w = ((1 - eps) * lin) / ((1 - eps) * lin + eps * lout + 1e-300);
    }
    let prec = 1 / var0, num = mu0 / var0;
    for (const o of live) { prec += o.w / (o.sig * o.sig); num += (o.w * o.px) / (o.sig * o.sig); }
    v = 1 / prec; mu = num * v;
  }
  const ms = performance.now() - t0;
  for (const o of obs) { o.used = !o.off && o.w > 0.5; o.resid = (o.px - mu) / mu; if (o.off) o.w = 0; }
  const used = obs.filter((o) => o.used).length;
  const sdB = Math.sqrt(v) / mu;
  const wasBreak = S.breaker;
  S.breaker = sdB > 0.002 || used < 3;
  S.post = { mu, var: v, sd: Math.sqrt(v), sdB, used, ms, t: now };
  S.oracleSrc = obs;
  if (S.breaker && !wasBreak) S.breakSince = now;
}
const oraclePx = () => (S.post ? S.post.mu : S.usd);

const SIG = { key: null, pubHex: '', ok: null };
async function initSigner() {
  try {
    if (!crypto.subtle) throw new Error('subtle');
    SIG.key = await crypto.subtle.generateKey({ name: 'ECDSA', namedCurve: 'P-256' }, true, ['sign', 'verify']);
    const raw = new Uint8Array(await crypto.subtle.exportKey('raw', SIG.key.publicKey));
    SIG.pubHex = Array.from(raw, (b) => b.toString(16).padStart(2, '0')).join('');
  } catch { SIG.key = null; }
}
const b64u = (buf) => btoa(String.fromCharCode(...new Uint8Array(buf))).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
async function signPayload() {
  if (!S.post) return;
  const p = S.post;
  const body = {
    v: 1, feed: 'BTC/USD', seq: S.seq, ts: new Date(p.t).toISOString(),
    mu: +p.mu.toFixed(2), sd: +p.sd.toFixed(2), ci95: [+(p.mu - 1.96 * p.sd).toFixed(2), +(p.mu + 1.96 * p.sd).toFixed(2)],
    fx: { MXN: +S.mxn.toFixed(5), HKD: +S.hkd.toFixed(5) },
    sources: S.oracleSrc.map((o) => ({ id: o.id, px: o.off ? null : +o.px.toFixed(2), w: +(o.w || 0).toFixed(4), used: o.used })),
    breaker: S.breaker, regime: REG[regNow()].short, mcr: +mcrNow().toFixed(4),
  };
  const msg = JSON.stringify(body);
  let sig = null, ok = false;
  if (SIG.key) {
    const data = new TextEncoder().encode(msg);
    const s = await crypto.subtle.sign({ name: 'ECDSA', hash: 'SHA-256' }, SIG.key.privateKey, data);
    ok = await crypto.subtle.verify({ name: 'ECDSA', hash: 'SHA-256' }, SIG.key.publicKey, s, data);
    sig = b64u(s);
  }
  S.lastPayload = { body, sig, ok, digest: SHA(msg) };
}

/* ============================================================
 * Motor 5 · Market making (Avellaneda-Stoikov) + LLN
 * ============================================================ */
const AS = {
  PMXMXN: { gamma: 0.1, k: 100, sigma: 0.15, A: 2.2, label: 'PMX/MXN', base: 'PMX', quote: 'MXN', dp: 4 },
  PMXHKD: { gamma: 0.1, k: 285, sigma: 0.004, A: 1.2, label: 'PMX/HKD', base: 'PMX', quote: 'HKD', dp: 4 },
  BTCMXN: { label: 'BTC/MXN', base: 'BTC', quote: 'MXN', dp: 0 },
  BTCHKD: { label: 'BTC/HKD', base: 'BTC', quote: 'HKD', dp: 0 },
};
const COST = { hedge: 2e-4, slip: 0.8e-4, adv: 7e-4, fixed: 0.18 };
function initMM() {
  S.mm = { q: { PMXMXN: 0, PMXHKD: 0 }, n: 0, mean: 0, M2: 0, pts: [], nextN: 1, sum: 0, wins: 0, eSum: 0 };
  for (const k of Object.keys(AS)) S.tape[k] = [];
}
function midOf(pair) {
  if (pair === 'PMXMXN') return S.mxn;
  if (pair === 'PMXHKD') return S.hkd;
  if (pair === 'BTCMXN') return oraclePx() * S.mxn;
  return oraclePx() * S.hkd;
}
function quoteAS(pair) {
  const p = AS[pair], s = midOf(pair);
  const T = 1 - minuteOfDayMX(Date.now()) / 1440;
  if (!p.gamma) {
    const half = (3 + 9 * S.live[2] + 3 * S.live[1]) * 1e-4 * s;
    return { s, r: s, delta: 2 * half, bid: s - half, ask: s + half, T, skew: 0 };
  }
  const q = S.mm.q[pair];
  const skew = q * p.gamma * p.sigma ** 2 * T;
  const r = s - skew;
  const delta = p.gamma * p.sigma ** 2 * T + (2 / p.gamma) * Math.log(1 + p.gamma / p.k);
  const widen = 1 + 0.8 * S.live[2];
  return { s, r, delta: delta * widen, bid: r - (delta * widen) / 2, ask: r + (delta * widen) / 2, T, skew, q };
}
function expectedX(pair = 'PMXMXN') {
  const qt = quoteAS(pair); const half = qt.delta / 2 / qt.s;
  return KP.meanA * (half - COST.hedge - COST.slip) - COST.fixed;
}
function recordX(x, ex) {
  const m = S.mm; m.n++; m.eSum += ex == null ? expectedX() : ex; const d = x - m.mean; m.mean += d / m.n; m.M2 += d * (x - m.mean); m.sum += x; if (x > 0) m.wins++;
  if (m.n >= m.nextN) { m.pts.push({ n: m.n, mean: m.mean, sd: Math.sqrt(m.M2 / Math.max(1, m.n - 1)), e: m.eSum / m.n }); m.nextN = Math.max(m.n + 1, Math.ceil(m.n * 1.04)); if (m.pts.length > 400) m.pts.splice(1, 1); }
}
function fillOnce(pair, dt, quiet) {
  const p = AS[pair], qt = quoteAS(pair);
  let fills = 0;
  for (const side of ['buy', 'sell']) {
    // buy = un cliente compra PMX al ask; sell = un cliente vende al bid
    const dist = side === 'buy' ? qt.ask - qt.s : qt.s - qt.bid;
    const lam = p.A * Math.exp(-p.k * Math.max(0, dist)) * dt;
    const n = poisson(lam);
    for (let i = 0; i < n; i++) {
      const size = lognormal(KP.meanA, KP.sdA);
      const px = side === 'buy' ? qt.ask : qt.bid;
      S.mm.q[pair] += (side === 'buy' ? -size : size) / 1e4;
      const capture = Math.abs(px - qt.s) / qt.s;
      const slip = Math.max(0, COST.slip + 0.6e-4 * randn());
      const x = size * (capture - COST.hedge - slip + COST.adv * randn()) - COST.fixed;
      recordX(x, KP.meanA * (capture - COST.hedge - COST.slip) - COST.fixed);
      if (!quiet) pushTape(pair, side, px, size);
      fills++;
    }
  }
  return fills;
}
function pushTape(pair, side, px, size) {
  const t = S.tape[pair]; t.unshift({ t: Date.now(), side, px, size }); if (t.length > 60) t.pop();
}
function mmTick() {
  fillOnce('PMXMXN', 1); fillOnce('PMXHKD', 1);
  for (const pair of ['BTCMXN', 'BTCHKD']) {
    if (rnd() < 0.7) { const qt = quoteAS(pair); const side = rnd() < 0.5 ? 'buy' : 'sell'; pushTape(pair, side, side === 'buy' ? qt.ask : qt.bid, lognormal(0.04, 0.08)); }
  }
}
function bookLevels(pair) {
  const qt = quoteAS(pair), p = AS[pair];
  const isBtc = p.base === 'BTC';
  const step = isBtc ? Math.max(1, qt.s * 0.6e-4) : Math.max(0.0001, qt.s * 0.4e-4);
  const seed = Math.floor(Date.now() / 4000);
  const r = mulberry32(seed * 7 + pair.length);
  const lv = (side) => Array.from({ length: 10 }, (_, j) => {
    const price = side === 'ask' ? qt.ask + j * step * (1 + j * 0.15) : qt.bid - j * step * (1 + j * 0.15);
    const base = isBtc ? 0.35 : 18000;
    const size = base * (1 + j * 0.45) * (0.55 + 0.9 * r()) * (1 - 0.4 * S.live[2]);
    return { price, size };
  });
  return { qt, asks: lv('ask'), bids: lv('bid') };
}

/* ============================================================
 * Cotización y flujo de transferencia
 * ============================================================ */
function quoteTransfer(mxn) {
  const a = quoteAS('PMXMXN'), b = quoteAS('PMXHKD'), px = oraclePx();
  const pmx = mxn / a.ask;
  const hkd = pmx * b.bid;
  const mid = (mxn / S.mxn) * S.hkd;
  const btc = pmx / px;
  const netSats = 180 + Math.round(rnd() * 40);
  return { mxn, pmx, hkd, btc, mid, rate: hkd / mxn, midRate: S.hkd / S.mxn, costBps: (1 - hkd / mid), ask: a.ask, bid: b.bid, px, netSats, mcr: mcrNow(), reg: regNow() };
}

const STEPS = [
  { key: 'spei', title: 'Depósito SPEI recibido', dur: 2200 },
  { key: 'oracle', title: 'Precio y régimen verificados', dur: 900 },
  { key: 'hedge', title: 'Compra de BTC y cobertura abierta', dur: 1600 },
  { key: 'mint', title: 'Acuñación de PMX', dur: 1100 },
  { key: 'move', title: 'Transferencia a Hong Kong', dur: 1800 },
  { key: 'redeem', title: 'Redención y cierre de cobertura', dur: 1300 },
  { key: 'fps', title: 'Liquidación FPS en HKD', dur: 2000 },
];
function pipeHTML(rec) {
  return STEPS.map((st, i) => {
    const s = rec.steps[i] || { s: 'wait' };
    const icon = s.s === 'done' ? '<svg class="ic"><use href="#i-check"/></svg>' : s.s === 'hold' ? '<svg class="ic"><use href="#i-pause"/></svg>' : s.s === 'fail' ? '<svg class="ic"><use href="#i-alert"/></svg>' : (i + 1);
    const kv = s.kv ? '<dl class="kv">' + s.kv.map(([k, v]) => '<div><dt>' + esc(k) + '</dt><dd>' + v + '</dd></div>').join('') + '</dl>' : '';
    const note = s.note ? '<p class="sub">' + esc(s.note) + '</p>' : '';
    return '<li data-s="' + s.s + '"><span class="dot">' + icon + '</span><div class="step-b"><h3>' + esc(st.title) + (s.t ? ' <time>' + tclock(s.t, TZ_MX, true) + ' CDMX</time>' : '') + '</h3>' + note + kv + '</div></li>';
  }).join('');
}
async function runTransfer(f) {
  if (S.running) return;
  S.running = true;
  const q = quoteTransfer(f.amount);
  const now = Date.now();
  const id = 'PMX-' + ymd(now) + '-' + digits(6);
  const rec = {
    id, type: 'transferencia', ts: now, status: 'en curso', sender: f.sender, rfc: f.rfc, clabe: f.clabe, benef: f.benef, fps: f.fps, bank: f.bank, purpose: f.purpose,
    quote: q, steps: [], chain: [], inTxt: fmt(q.mxn, 2) + ' MXN', outTxt: fmt(q.hkd, 2) + ' HKD', detail: f.benef,
  };
  const pipe = $('#pipe'); pipe.hidden = false;
  $('#pipe-title').textContent = 'Transferencia ' + id;
  $('#pipe-sub').textContent = f.sender + ' → ' + f.benef;
  $('#pipe-receipt').hidden = true; $('#pipe-new').hidden = true;
  const draw = () => { $('#pipe-steps').innerHTML = pipeHTML(rec); };
  draw();
  pipe.scrollIntoView({ behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth', block: 'start' });
  let prev = '0'.repeat(64);
  let route = 'mint';
  const pmx = q.pmx;
  const conc = '646180' + '1234' + digits(7);
  const concClabe = conc + clabeCheck(conc);
  for (let i = 0; i < STEPS.length; i++) {
    rec.steps[i] = { s: 'run' }; draw();
    await sleep(STEPS[i].dur);
    const st = STEPS[i].key; let kv = [], note = null;
    if (st === 'spei') {
      const rastreo = 'PMX' + ymd(Date.now()) + digits(10);
      kv = [['Monto', fmt(q.mxn, 2) + ' MXN'], ['Clave de rastreo', '<span class="hash">' + rastreo + '</span>'], ['CLABE concentradora', '<span class="hash">' + concClabe + '</span>'], ['Banco ordenante', esc(validClabe(f.clabe).msg.split(' ·')[0])]];
      rec.rastreo = rastreo;
    } else if (st === 'oracle') {
      const p = S.post;
      kv = [['BTC/USD posterior', fmt(p.mu, 2)], ['IC 95 %', fmt(p.mu - 1.96 * p.sd, 0) + ' – ' + fmt(p.mu + 1.96 * p.sd, 0)], ['Fuentes usadas', p.used + ' de 6'], ['Régimen', REG[regNow()].name], ['MCR vigente', pct(mcrNow(), 1)]];
    } else if (st === 'hedge') {
      const vs = vaultState();
      const crAfter = (vs.V + pmx) / (vs.L + pmx);
      route = crAfter >= mcrNow() ? 'mint' : 'inv';
      const btc = pmx / oraclePx();
      S.vault.btc.hotMx += btc;
      let o = null;
      if (route === 'mint') o = hedgeAdjust(pmx, id);
      kv = [['BTC comprado', fmt(btc, 8) + ' BTC'], ['Precio', fmt(oraclePx() * S.mxn, 2) + ' MXN']];
      if (o) kv.push(['Contratos abiertos', fmt(o.contracts, 0) + ' × 100 USD'], ['Tramos', String(o.slices)], ['Deslizamiento', bps(o.slip, 2)]);
      else note = 'Colateral ' + pct(crAfter, 1) + ' bajo el MCR de ' + pct(mcrNow(), 1) + ': la acuñación está en pausa y el pago se cubre con inventario PMX del creador de mercado.';
      rec.btc = btc;
    } else if (st === 'mint') {
      if (route === 'mint') {
        S.vault.supply += pmx;
        const vs = vaultState();
        kv = [['PMX acuñados', fmt(pmx, 2)], ['Colateral tras acuñar', pct(vs.CR, 2)], ['MCR exigido', pct(mcrNow(), 1)], ['Bloque interno', '#' + S.seq]];
      } else {
        S.mm.q.PMXMXN -= pmx / 1e4;
        kv = [['PMX de inventario', fmt(pmx, 2)], ['Inventario restante', fmt(S.mm.q.PMXMXN * 1e4, 0) + ' PMX'], ['Bloque interno', '#' + S.seq]];
      }
    } else if (st === 'move') {
      const ph = SHA(id + prev + Date.now());
      kv = [['Ruta', 'Canal Lightning PayMexBTC MX → HK'], ['Hash de pago', '<span class="hash">' + short(ph, 12) + '</span>'], ['Comisión de red', fmt(q.netSats, 0) + ' sats (absorbida)'], ['Tiempo en red', fmt(1.1 + rnd() * 0.9, 2) + ' s']];
      rec.payHash = ph;
    } else if (st === 'redeem') {
      if (S.breaker) {
        rec.steps[i] = { s: 'hold', note: 'Redenciones en pausa: el disyuntor del oráculo está activo. Se reanuda en cuanto la posterior vuelve a su rango.' }; draw();
        while (S.breaker) await sleep(500);
        rec.steps[i] = { s: 'run' }; draw(); await sleep(600);
      }
      const btcOut = pmx / oraclePx();
      S.vault.btc.hotHk -= btcOut;
      let o = null;
      if (route === 'mint') { S.vault.supply -= pmx; o = hedgeAdjust(-pmx, id); }
      kv = [['PMX quemados', fmt(pmx, 2)], ['BTC liberados', fmt(btcOut, 8)]];
      if (o) kv.push(['Contratos cerrados', fmt(-o.contracts, 0)], ['Precio de recompra', fmt(o.px, 2) + ' USD']);
    } else if (st === 'fps') {
      const frn = 'FRN' + ymd(Date.now()) + 'PMX' + digits(8);
      kv = [['Monto acreditado', fmt(q.hkd, 2) + ' HKD'], ['Referencia FPS', '<span class="hash">' + frn + '</span>'], ['Banco', esc(f.bank)], ['Destino', '<span class="hash">' + esc(f.fps) + '</span>']];
      rec.frn = frn;
    }
    const h = SHA(prev + JSON.stringify(kv.map(([k, v]) => [k, v.replace(/<[^>]+>/g, '')])));
    rec.chain.push(h); prev = h;
    kv.push(['Hash del paso', '<span class="hash">' + short(h, 10) + '</span>']);
    rec.steps[i] = { s: 'done', t: Date.now(), kv, note };
    draw();
  }
  rec.status = 'liquidada'; rec.done = Date.now(); rec.secs = (rec.done - rec.ts) / 1000; rec.root = merkleRoot(rec.chain); rec.route = route;
  { const usd = q.mxn / S.mxn, ex = usd * (q.costBps - 2 * COST.hedge - COST.slip) - 2 * COST.fixed; recordX(ex + usd * COST.adv * randn(), ex); }
  $('#pipe-title').textContent = 'Liquidada en ' + fmt(rec.secs, 1) + ' s';
  $('#pipe-sub').textContent = fmt(q.mxn, 2) + ' MXN → ' + fmt(q.hkd, 2) + ' HKD · ' + f.benef;
  $('#pipe-receipt').hidden = false; $('#pipe-new').hidden = false;
  $('#pipe-receipt').onclick = () => openReceipt(rec.id);
  const clean = { ...rec, steps: rec.steps.map((s, i) => ({ step: STEPS[i].title, t: s.t, data: Object.fromEntries((s.kv || []).map(([k, v]) => [k, v.replace(/<[^>]+>/g, '')])), note: s.note || undefined })) };
  addActivity(clean);
  persist();
  S.running = false;
  $('#f-submit').disabled = false; $('#f-submit').removeAttribute('data-state'); $('#f-submit').textContent = 'Enviar ahora';
}
function merkleRoot(leaves) {
  let lv = leaves.slice(); if (!lv.length) return '0'.repeat(64);
  while (lv.length > 1) { const nx = []; for (let i = 0; i < lv.length; i += 2) nx.push(SHA(lv[i] + (lv[i + 1] || lv[i]))); lv = nx; }
  return lv[0];
}

/* ============================================================
 * Actividad y persistencia
 * ============================================================ */
function addActivity(a) {
  const rec = { id: a.id || ('MOV-' + ymd(Date.now()) + '-' + digits(6)), ts: a.ts || Date.now(), ...a };
  S.activity.unshift(rec); if (S.activity.length > 200) S.activity.pop();
  store.set('activity', S.activity);
}
function persist() { store.set('vault', S.vault); }

/* ============================================================
 * Gráficas SVG (marcas finas, cuadrícula recesiva, hover)
 * ============================================================ */
function niceTicks(min, max, n = 4) {
  const span = max - min || Math.abs(max) || 1; const raw = span / n; const mag = 10 ** Math.floor(Math.log10(raw)); const e = raw / mag;
  const step = (e >= 7.5 ? 10 : e >= 3.5 ? 5 : e >= 1.5 ? 2 : 1) * mag;
  const out = []; for (let v = Math.ceil(min / step) * step; v <= max + step * 1e-9; v += step) out.push(+v.toPrecision(12));
  return out;
}
const tip = { el: null };
function showTip(html, x, y) {
  const t = tip.el || (tip.el = $('#tip')); t.innerHTML = html; t.hidden = false;
  const r = t.getBoundingClientRect(); let L = x + 14, T = y + 14;
  if (L + r.width > innerWidth - 8) L = x - r.width - 14; if (T + r.height > innerHeight - 8) T = y - r.height - 14;
  t.style.left = Math.max(8, L) + 'px'; t.style.top = Math.max(8, T) + 'px';
}
function hideTip() { if (tip.el) tip.el.hidden = true; }
const key = (c) => '<i class="k" style="background:' + c + '"></i>';

function lineChart(el, o) {
  const W = el.clientWidth, H = el.clientHeight; if (!W || !H) return;
  const xs = o.xs, n = xs.length; if (n < 2) return;
  const m = { l: o.ml ?? 58, r: o.mr ?? 14, t: 8, b: o.strip ? 34 : 22 };
  let lo = Infinity, hi = -Infinity;
  for (const s of o.series) for (const v of s.values) if (v != null && isFinite(v)) { lo = Math.min(lo, v); hi = Math.max(hi, v); }
  if (o.band) for (let i = 0; i < n; i++) { if (isFinite(o.band.lo[i])) lo = Math.min(lo, o.band.lo[i]); if (isFinite(o.band.hi[i])) hi = Math.max(hi, o.band.hi[i]); }
  for (const r of o.refs || []) { lo = Math.min(lo, r.y); hi = Math.max(hi, r.y); }
  if (o.yMin != null) lo = o.yMin; if (o.yMax != null) hi = o.yMax;
  const pad = (hi - lo) * 0.06 || Math.abs(hi) * 0.01 || 1; if (o.yMin == null) lo -= pad; if (o.yMax == null) hi += pad;
  const x0 = xs[0], x1 = xs[n - 1];
  const pw = W - m.l - m.r, ph = H - m.t - m.b;
  const X = (v) => m.l + ((v - x0) / (x1 - x0 || 1)) * pw;
  const Y = (v) => m.t + (1 - (v - lo) / (hi - lo || 1)) * ph;
  const yt = niceTicks(lo, hi, o.yTicks || 4);
  let g = '<g class="grid">' + yt.map((v) => '<line x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + Y(v).toFixed(1) + '" y2="' + Y(v).toFixed(1) + '"/>').join('') + '</g>';
  g += '<g class="axis">' + yt.map((v) => '<text x="' + (m.l - 8) + '" y="' + (Y(v) + 4).toFixed(1) + '" text-anchor="end">' + esc(o.yFmt(v)) + '</text>').join('');
  const xt = o.xTicks || [];
  g += xt.map((v) => '<text x="' + X(v).toFixed(1) + '" y="' + (H - 6) + '" text-anchor="middle">' + esc(o.xFmt(v)) + '</text>').join('') + '</g>';
  const cid = 'c' + Math.random().toString(36).slice(2, 8);
  g += '<clipPath id="' + cid + '"><rect x="' + m.l + '" y="' + (m.t - 6) + '" width="' + (pw + 6) + '" height="' + (ph + 12) + '"/></clipPath><g clip-path="url(#' + cid + ')">';
  if (o.band) {
    let d = ''; for (let i = 0; i < n; i++) if (isFinite(o.band.hi[i])) d += (d ? 'L' : 'M') + X(xs[i]).toFixed(1) + ',' + Y(o.band.hi[i]).toFixed(1);
    for (let i = n - 1; i >= 0; i--) if (isFinite(o.band.lo[i])) d += 'L' + X(xs[i]).toFixed(1) + ',' + Y(o.band.lo[i]).toFixed(1);
    g += '<path d="' + d + 'Z" style="fill:' + o.band.color + ';fill-opacity:0.12;stroke:none"/>';
  }
  for (const r of o.refs || []) {
    g += '<line class="ref" x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + Y(r.y).toFixed(1) + '" y2="' + Y(r.y).toFixed(1) + '"/>';
    if (r.label) g += '<text class="endlbl" x="' + (W - m.r) + '" y="' + (Y(r.y) - 5).toFixed(1) + '" text-anchor="end">' + esc(r.label) + '</text>';
  }
  o.series.forEach((s) => {
    let d = '', first = null;
    for (let i = 0; i < n; i++) { const v = s.values[i]; if (v == null || !isFinite(v)) continue; d += (d ? 'L' : 'M') + X(xs[i]).toFixed(1) + ',' + Y(v).toFixed(1); if (first == null) first = i; }
    if (s.area && first != null) g += '<path d="' + d + 'L' + X(xs[n - 1]).toFixed(1) + ',' + (m.t + ph) + 'L' + X(xs[first]).toFixed(1) + ',' + (m.t + ph) + 'Z" style="fill:' + s.color + ';fill-opacity:0.10;stroke:none"/>';
    g += '<path class="line" d="' + d + '" style="stroke:' + s.color + (s.dash ? ';stroke-dasharray:5 4' : '') + '"/>';
    if (o.endDot) { const v = s.values[n - 1]; g += '<circle cx="' + X(xs[n - 1]).toFixed(1) + '" cy="' + Y(v).toFixed(1) + '" r="4" style="fill:' + s.color + ';stroke:var(--color-paper-2);stroke-width:2"/>'; }
  });
  g += '</g>';
  if (o.strip) {
    const y = m.t + ph + 6, w = pw / n;
    let d = ''; o.strip.forEach((c, i) => { d += '<rect x="' + (m.l + i * w).toFixed(2) + '" y="' + y + '" width="' + (w + 0.5).toFixed(2) + '" height="6" style="fill:' + c + '"/>'; });
    g += '<g>' + d + '</g>';
  }
  g += '<g class="hov"></g><rect class="hit" x="' + m.l + '" y="0" width="' + pw + '" height="' + H + '"/>';
  el.innerHTML = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="' + esc(o.label || '') + '">' + g + '</svg>';
  el._c = { o, X, Y, xs, m, ph };
  if (!el._bound) {
    el._bound = true;
    el.addEventListener('pointermove', (e) => { el._hx = e.clientX; el._hy = e.clientY; drawHover(el); });
    el.addEventListener('pointerleave', () => { el._hx = null; const h = el.querySelector('.hov'); if (h) h.innerHTML = ''; hideTip(); });
  }
  if (el._hx != null) drawHover(el);
}
function drawHover(el) {
  const c = el._c; if (!c) return; const svg = el.querySelector('svg'); const r = svg.getBoundingClientRect();
  const px = el._hx - r.left; let lo = 0, hi = c.xs.length - 1;
  while (hi - lo > 1) { const mid = (lo + hi) >> 1; if (c.X(c.xs[mid]) < px) lo = mid; else hi = mid; }
  const i = Math.abs(c.X(c.xs[lo]) - px) < Math.abs(c.X(c.xs[hi]) - px) ? lo : hi;
  const x = c.X(c.xs[i]).toFixed(1);
  let g = '<line class="xh" x1="' + x + '" x2="' + x + '" y1="' + c.m.t + '" y2="' + (c.m.t + c.ph) + '"/>';
  for (const s of c.o.series) { const v = s.values[i]; if (v == null || !isFinite(v)) continue; g += '<circle cx="' + x + '" cy="' + c.Y(v).toFixed(1) + '" r="4.5" style="fill:' + s.color + ';stroke:var(--color-paper-2);stroke-width:2"/>'; }
  el.querySelector('.hov').innerHTML = g;
  const html = c.o.tip ? c.o.tip(i) : '<b>' + esc(c.o.xFmt(c.xs[i])) + '</b><br>' + c.o.series.map((s) => key(s.color) + esc(s.name) + ': ' + esc(c.o.yFmt(s.values[i], true))).join('<br>');
  showTip(html, el._hx, el._hy);
}

function barChart(el, o) {
  const W = el.clientWidth, H = el.clientHeight; if (!W || !H) return;
  const nc = o.cats.length, ns = o.series.length;
  const m = { l: o.ml ?? 52, r: 8, t: 10, b: 22 };
  let hi = o.yMax ?? 0; for (const s of o.series) for (const v of s.values) hi = Math.max(hi, v);
  hi = hi * 1.08 || 1;
  const pw = W - m.l - m.r, ph = H - m.t - m.b, gw = pw / nc;
  const Y = (v) => m.t + (1 - v / hi) * ph;
  const yt = niceTicks(0, hi, 3);
  let g = '<g class="grid">' + yt.map((v) => '<line x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + Y(v).toFixed(1) + '" y2="' + Y(v).toFixed(1) + '"/>').join('') + '</g>';
  g += '<g class="axis">' + yt.map((v) => '<text x="' + (m.l - 8) + '" y="' + (Y(v) + 4).toFixed(1) + '" text-anchor="end">' + esc(o.yFmt(v)) + '</text>').join('');
  const every = o.labelEvery || 1;
  o.cats.forEach((c, i) => { if (i % every === 0) g += '<text x="' + (m.l + gw * (i + 0.5)).toFixed(1) + '" y="' + (H - 6) + '" text-anchor="middle"' + (o.highlight === i ? ' style="fill:var(--color-ink);font-weight:600"' : '') + '>' + esc(c) + '</text>'; });
  g += '</g>';
  const touching = ns === 1 && gw < 26;
  const bw = touching ? Math.max(1, gw - 2) : Math.min(24, Math.max(2, (gw - 6 - (ns - 1) * 2) / ns));
  const groupW = ns * bw + (ns - 1) * 2;
  let bars = '';
  o.cats.forEach((_, i) => {
    const gx = m.l + gw * i + (gw - groupW) / 2;
    o.series.forEach((s, j) => {
      const v = s.values[i]; if (!(v > 0)) return;
      const x = gx + j * (bw + 2), y = Y(v), h = m.t + ph - y, rr = Math.min(4, bw / 2, h);
      const col = o.colorAt ? o.colorAt(j, i) : s.color;
      bars += '<path d="M' + x.toFixed(1) + ',' + (y + h).toFixed(1) + 'V' + (y + rr).toFixed(1) + 'Q' + x.toFixed(1) + ',' + y.toFixed(1) + ' ' + (x + rr).toFixed(1) + ',' + y.toFixed(1) + 'H' + (x + bw - rr).toFixed(1) + 'Q' + (x + bw).toFixed(1) + ',' + y.toFixed(1) + ' ' + (x + bw).toFixed(1) + ',' + (y + rr).toFixed(1) + 'V' + (y + h).toFixed(1) + 'Z" style="fill:' + col + '"/>';
    });
  });
  if (o.highlight != null) g = '<rect x="' + (m.l + gw * o.highlight).toFixed(1) + '" y="' + m.t + '" width="' + gw.toFixed(1) + '" height="' + ph + '" style="fill:var(--color-paper-4)"/>' + g;
  g += bars;
  if (o.refX != null) { const x = m.l + gw * o.refX; g += '<line class="ref" x1="' + x.toFixed(1) + '" x2="' + x.toFixed(1) + '" y1="' + m.t + '" y2="' + (m.t + ph) + '"/><text class="endlbl" x="' + (x + 4).toFixed(1) + '" y="' + (m.t + 10) + '">' + esc(o.refLabel || '') + '</text>'; }
  g += o.cats.map((_, i) => '<rect class="hit" data-i="' + i + '" x="' + (m.l + gw * i).toFixed(1) + '" y="0" width="' + gw.toFixed(1) + '" height="' + H + '"/>').join('');
  el.innerHTML = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="' + esc(o.label || '') + '">' + g + '</svg>';
  el._b = o;
  if (!el._bound) {
    el._bound = true;
    el.addEventListener('pointermove', (e) => {
      const t = e.target.closest('.hit'); if (!t) return hideTip(); const i = +t.dataset.i, b = el._b;
      showTip(b.tip ? b.tip(i) : '<b>' + esc(b.cats[i]) + '</b><br>' + b.series.map((s) => key(s.color) + esc(s.name) + ': ' + esc(b.yFmt(s.values[i], true))).join('<br>'), e.clientX, e.clientY);
    });
    el.addEventListener('pointerleave', hideTip);
  }
}
function legend(el, items) {
  el.innerHTML = items.map((it) => '<span><i class="' + (it.kind || '') + '" style="background:' + it.color + '"></i>' + esc(it.name) + '</span>').join('');
}

/* ============================================================
 * Render
 * ============================================================ */
const TITLES = { panel: 'Panel', enviar: 'Enviar dinero', mercado: 'Mercado', reservas: 'Reservas', motores: 'Motores cuantitativos', actividad: 'Actividad' };
let lastTk = {};
function setTk(id, val, raw) {
  const el = $('#' + id); el.textContent = val;
  if (lastTk[id] != null && raw !== lastTk[id]) el.dataset.dir = raw > lastTk[id] ? 'up' : 'down';
  lastTk[id] = raw;
}
function renderHeader() {
  const px = oraclePx();
  setTk('tk-usd', fmt(px, 2), Math.round(px));
  setTk('tk-mxn', fmt(px * S.mxn, 0), Math.round(px * S.mxn));
  setTk('tk-hkd', fmt(px * S.hkd, 0), Math.round(px * S.hkd));
  const peg = pegNow();
  $('#tk-pmx').textContent = fmt(peg, 4) + ' USD';
  const r = regNow(); const R = REG[r];
  const sr = $('#st-regime'); sr.dataset.s = R.s; sr.querySelector('use').setAttribute('href', r === 2 ? '#i-alert' : '#i-check'); sr.lastElementChild.textContent = R.short + ' · MCR ' + pct(mcrNow(), 0);
  const so = $('#st-oracle'); so.dataset.s = S.breaker ? 'crit' : 'good'; so.querySelector('use').setAttribute('href', S.breaker ? '#i-pause' : '#i-check');
  so.lastElementChild.textContent = S.breaker ? 'Redenciones en pausa' : 'Oráculo ' + (S.post ? S.post.used : 0) + '/6';
  $('#clk-mx').textContent = tclock(Date.now(), TZ_MX); $('#clk-hk').textContent = tclock(Date.now(), TZ_HK);
  $('#foot-seq').textContent = 'Bloque interno #' + S.seq;
}
function pegNow() { const q = quoteAS('PMXMXN'); return (q.r / q.s); }
function renderFeedSrc() {
  const el = $('#feed-src');
  if (S.src === 'ext') el.textContent = 'Referencia de precio: agregador público, ' + tclock(S.anchor.t) + ' CDMX. Los motores filtran cada segundo.';
  else if (S.src === 'cache') el.textContent = 'Referencia de precio: último valor conocido. Reintentando conexión.';
  else el.textContent = 'Conectando referencia de precio…';
}

function renderPanel(full) {
  const p = S.post, vs = vaultState(), r = regNow();
  $('#p-price').innerHTML = fmt(p.mu, 2) + ' <small>USD</small>';
  $('#p-price-ci').textContent = 'IC 95 % ' + fmt(p.mu - 1.96 * p.sd, 0) + ' – ' + fmt(p.mu + 1.96 * p.sd, 0) + ' · ' + p.used + ' fuentes';
  const peg = pegNow();
  $('#p-peg').innerHTML = fmt(peg, 4) + ' <small>USD</small>';
  $('#p-peg-sub').textContent = '1 PMX = 1 USD · desviación ' + sgn((peg - 1) * 1e4, 2) + ' pb';
  const m = mcrNow();
  $('#p-cr').innerHTML = pct(vs.CR, 1);
  const fill = $('#p-cr-fill'); fill.style.transform = 'scaleX(' + clamp((vs.CR - 1) / 1.2, 0, 1) + ')'; fill.dataset.s = vs.CR < 1 ? 'crit' : vs.CR < m ? 'warn' : 'good';
  $('#p-cr-mcr').style.left = (clamp((m - 1) / 1.2, 0, 1) * 100) + '%';
  $('#p-cr-sub').textContent = 'MCR exigido ' + pct(m, 1) + (vs.CR < m ? ' · acuñación en pausa' : ' · acuñación abierta');
  $('#p-reg').textContent = REG[r].name;
  $('#p-reg-probs').innerHTML = REG.map((R, i) => '<div><span>' + R.short + '</span><b><i style="background:' + R.color + ';transform:scaleX(' + S.live[i].toFixed(3) + ')"></i></b><span>' + pct(S.live[i], 0) + '</span></div>').join('');
  // gráfica
  const C = S.candles.concat([S.cur]);
  const xs = C.map((c) => c.t), vals = C.map((c) => c.c);
  const filt = S.filt.concat([S.live]);
  const strip = C.map((_, i) => { const f = filt[i - (C.length - filt.length)] || filt[0]; return REG[regNow(f)].color; });
  const xt = []; for (let i = 0; i < C.length; i += 60) xt.push(C[i].t);
  lineChart($('#ch-price'), {
    xs, series: [{ name: 'BTC/USD', color: 'var(--series-2)', values: vals, area: true }], yFmt: (v) => fmt(v, 0), xFmt: (t) => tclock(t), xTicks: xt, strip, endDot: true, label: 'Precio de BTC en USD, últimas 6 horas',
    tip: (i) => { const f = filt[i - (C.length - filt.length)] || filt[0]; const k = regNow(f); return '<b>' + tclock(xs[i]) + ' CDMX</b><br>Cierre ' + fmt(C[i].c, 2) + ' USD<br>Máx ' + fmt(C[i].h, 0) + ' · Mín ' + fmt(C[i].l, 0) + '<br>' + key(REG[k].color) + REG[k].name + ' (' + pct(f[k], 0) + ')'; },
  });
  if (full) legend($('#p-strip-legend'), REG.map((R) => ({ name: R.short, color: R.color })));
  // KPIs
  const k = S.kelly || kellyPlan();
  const mm = S.mm, sdX = Math.sqrt(mm.M2 / Math.max(1, mm.n - 1)), mu = mm.n ? mm.eSum / mm.n : expectedX();
  const cant = mm.n > 1 ? (sdX * sdX) / (sdX * sdX + mm.n * mu * mu) : 1;
  const st = (c, txt) => '<span class="tag" data-s="' + c + '"><svg class="ic"><use href="#' + (c === 'good' ? 'i-check' : c === 'warn' ? 'i-alert' : 'i-pause') + '"/></svg>' + txt + '</span>';
  const rows = [
    ['Colateralización', 'V / L', pct(vs.CR, 2), vs.CR < 1 ? st('crit', 'Bajo paridad') : vs.CR < m ? st('warn', 'Bajo MCR') : st('good', 'Sobre MCR')],
    ['Holgura sobre MCR', 'CR − MCR<sub>t</sub>', sgn((vs.CR - m) * 100, 1) + ' pp', vs.CR - m > 0.05 ? st('good', 'Holgada') : st('warn', 'Ajustada')],
    ['Δ residual', 'B − N / S̄₀', fmt(vs.delta, 3) + ' BTC', st('good', 'Excedente')],
    ['Margen de cobertura', 'M / requerido', fmt(vs.mRatio, 2) + '×', vs.mRatio >= 1.5 ? st('good', 'Suficiente') : vs.mRatio >= 1.2 ? st('warn', 'Vigilar') : st('crit', 'Depositar')],
    ['Fondeo 8 h', 'f · N', sgn(S.funding * 1e4, 2) + ' pb', S.funding >= 0 ? st('good', 'Cobra el corto') : st('warn', 'Paga el corto')],
    ['Incertidumbre del oráculo', 'τ<sub>n</sub> / μ<sub>n</sub>', fmt(p.sdB * 1e4, 2) + ' pb', S.breaker ? st('crit', 'Disyuntor') : st('good', 'Normal')],
    ['Liquidez HKD caliente', 'saldo / Q<sub>99.9</sub>', fmt(S.vault.btc.hotHk / k.floorHk, 2) + '×', S.vault.btc.hotHk >= k.floorHk ? st('good', 'Cubierta') : st('warn', 'Recargar')],
    ['Inventario PMX/MXN', '|q| en lotes de 10 K', fmt(Math.abs(mm.q.PMXMXN), 1), Math.abs(mm.q.PMXMXN) < 10 ? st('good', 'En rango') : st('warn', 'Sesgo alto')],
    ['Resultado medio por operación', 'X̄<sub>n</sub>', (mm.n ? sgn(mm.mean, 3) : '—') + ' USD', mm.mean > 0 ? st('good', 'Positivo') : st('warn', 'Convergiendo')],
    ['Probabilidad de pérdida total', 'σ² / (σ² + nμ²)', mm.n > 1 ? pct(cant, 2) : '—', cant < 0.01 ? st('good', 'Bajo 1 %') : st('warn', 'Sobre 1 %')],
  ];
  $('#kpi-table tbody').innerHTML = rows.map((r) => '<tr><td>' + r[0] + '</td><td>' + r[1] + '</td><td class="num">' + r[2] + '</td><td>' + r[3] + '</td></tr>').join('');
  if (full) renderFeed();
}
function renderFeed() {
  const a = S.activity.slice(0, 6);
  $('#p-feed').innerHTML = a.length ? a.map((x) => '<li><div>' + esc(x.type === 'transferencia' ? x.benef : x.detail) + '<small class="none">' + tdate(x.ts) + ' · ' + esc(x.type) + '</small></div><div class="amt">' + esc(x.outTxt && x.outTxt !== '—' ? x.outTxt : x.inTxt || '') + '<small class="none">' + esc(x.status) + '</small></div></li>').join('')
    : '<li><span class="none">Sin movimientos todavía. La primera transferencia aparece aquí.</span></li>';
}

/* --- Enviar --- */
function readForm() {
  const f = $('#send-form');
  return { sender: f.sender.value.trim(), rfc: f.rfc.value.trim().toUpperCase(), clabe: f.clabe.value.replace(/\s/g, ''), amount: parseFloat(f.amount.value.replace(/[,\s]/g, '')), benef: f.benef.value.trim(), fps: f.fps.value.trim(), bank: f.bank.value, purpose: f.purpose.value };
}
function capMxn() { const k = S.kelly || kellyPlan(); return k.capHkUsd * S.mxn; }
function validateField(name, show) {
  const f = readForm(); let res = { ok: true, msg: '' };
  if (name === 'rfc') res = validRfc(f.rfc);
  if (name === 'clabe') res = validClabe(f.clabe);
  if (name === 'fps') res = validFps(f.fps);
  if (name === 'amount') {
    const cap = capMxn();
    if (!(f.amount > 0)) res = { ok: false, msg: 'Escribe un monto.' };
    else if (f.amount < 500) res = { ok: false, msg: 'El mínimo es 500 MXN.' };
    else if (f.amount > cap) res = { ok: false, msg: 'Supera la capacidad instantánea de ' + fmt(cap, 0) + ' MXN. Rebalancea la bóveda o divide el pago.' };
    else res = { ok: true, msg: 'Capacidad instantánea disponible: ' + fmt(cap, 0) + ' MXN' };
  }
  if (name === 'sender' || name === 'benef') res = f[name].length >= 3 ? { ok: true, msg: '' } : { ok: false, msg: '' };
  const input = $('#send-form [name="' + name + '"]'); const field = input.closest('.field'); const help = field.querySelector('.help');
  if (show) { field.dataset.state = res.ok ? (help ? 'ok' : '') : 'error'; if (help) help.textContent = res.msg; }
  input.setAttribute('aria-invalid', res.ok ? 'false' : 'true');
  return res.ok;
}
function fillForm(c) { const f = $('#send-form'); f.sender.value = c.sender; f.rfc.value = c.rfc; f.clabe.value = c.clabe; f.amount.value = fmt(c.amount, 0); f.benef.value = c.benef; f.fps.value = c.fps; f.bank.selectedIndex = Math.floor(rnd() * f.bank.options.length); f.purpose.selectedIndex = Math.floor(rnd() * 3); ['rfc', 'clabe', 'fps', 'amount'].forEach((n) => validateField(n, true)); renderQuote(); }
function renderQuote() {
  const f = readForm(); const mxn = f.amount > 0 ? f.amount : 0;
  if (!mxn || !S.post) { $('#q-hkd').textContent = '—'; $('#q-rate').textContent = 'Escribe un monto para cotizar.'; $('#q-route').innerHTML = ''; $('#q-fees').innerHTML = ''; return; }
  const q = quoteTransfer(mxn);
  $('#q-hkd').textContent = fmt(q.hkd, 2);
  $('#q-rate').textContent = '1 MXN = ' + fmt(q.rate, 5) + ' HKD · medio ' + fmt(q.midRate, 5);
  const route = (q.mcr > vaultState().CR) ? 'inventario PMX (acuñación en pausa)' : 'acuñación';
  $('#q-route').innerHTML = [
    ['1', 'SPEI a la cuenta concentradora', fmt(mxn, 2) + ' MXN', 'Sin costo para el remitente'],
    ['2', 'MXN → BTC al precio del oráculo', fmt(q.btc, 8) + ' BTC', '1 BTC = ' + fmt(q.px * S.mxn, 0) + ' MXN'],
    ['3', 'BTC → PMX por ' + route, fmt(q.pmx, 2) + ' PMX', 'Ask PMX/MXN ' + fmt(q.ask, 4)],
    ['4', 'PMX → HKD y pago FPS', fmt(q.hkd, 2) + ' HKD', 'Bid PMX/HKD ' + fmt(q.bid, 4)],
  ].map((r) => '<li><span>' + r[0] + '</span><div>' + esc(r[1]) + '<small>' + esc(r[3]) + '</small></div><b>' + esc(r[2]) + '</b></li>').join('');
  $('#q-fees').innerHTML = [
    ['Spread de conversión', bps(q.costBps, 1)],
    ['Red Bitcoin (Lightning)', fmt(q.netSats, 0) + ' sats · incluida'],
    ['SPEI y FPS', 'Sin costo'],
    ['Régimen al cotizar', REG[q.reg].short + ' · MCR ' + pct(q.mcr, 0)],
    ['Costo total frente al tipo medio', fmt((q.mid - q.hkd), 2) + ' HKD'],
  ].map((r, i, a) => '<dt' + (i === a.length - 1 ? ' class="total"' : '') + '>' + esc(r[0]) + '</dt><dd>' + esc(r[1]) + '</dd>').join('');
}

/* --- Mercado --- */
function renderPairs() {
  const foc = document.activeElement && document.activeElement.dataset ? document.activeElement.dataset.pair : null;
  $('#pair-tabs').innerHTML = Object.keys(AS).map((k) => { const q = quoteAS(k); return '<button class="btn small" role="tab" data-pair="' + k + '" aria-selected="' + (S.pair === k) + '" tabindex="' + (S.pair === k ? 0 : -1) + '">' + AS[k].label + '<span>' + fmt((q.bid + q.ask) / 2, AS[k].dp) + '</span></button>'; }).join('');
  if (foc) { const b = $('#pair-tabs [data-pair="' + foc + '"]'); if (b) b.focus({ preventScroll: true }); }
}
function renderMarket() {
  renderPairs();
  const p = AS[S.pair], b = bookLevels(S.pair), q = b.qt;
  $('#ob-title').textContent = 'Libro ' + p.label;
  $('#ob-sub').textContent = 'Spread ' + fmt(q.ask - q.bid, p.dp + (p.dp ? 0 : 0)) + ' ' + p.quote + ' · ' + bps((q.ask - q.bid) / q.s, 1) + (p.gamma ? ' · cotización Avellaneda-Stoikov' : ' · ensanchado por régimen');
  const mx = Math.max(...b.asks.map((x) => x.size), ...b.bids.map((x) => x.size));
  const row = (x, cls, cum) => '<div class="row ' + cls + '"><span>' + fmt(x.price, p.dp) + '</span><span>' + fmt(x.size, p.base === 'BTC' ? 4 : 0) + '</span><span>' + fmt(cum, p.base === 'BTC' ? 4 : 0) + '</span><i class="bar" style="width:100%;transform:scaleX(' + (x.size / mx).toFixed(3) + ')"></i></div>';
  let cum = 0; const asks = b.asks.map((x) => { cum += x.size; return [x, cum]; }).reverse();
  cum = 0; const bids = b.bids.map((x) => { cum += x.size; return [x, cum]; });
  $('#book').innerHTML = '<div class="row head"><span>Precio ' + p.quote + '</span><span>Cantidad ' + p.base + '</span><span>Acumulado</span></div>' + asks.map(([x, c]) => row(x, 'ask', c)).join('') +
    '<div class="mid"><span>' + fmt((q.bid + q.ask) / 2, p.dp + (p.base === 'BTC' ? 0 : 0)) + '</span><small>' + (p.gamma ? 'reserva r = ' + fmt(q.r, 4) : 'oráculo × FX') + '</small></div>' + bids.map(([x, c]) => row(x, 'bid', c)).join('');
  $('#tape').innerHTML = S.tape[S.pair].slice(0, 40).map((t) => '<tr data-side="' + t.side + '"><td>' + tclock(t.t, TZ_MX, true) + '</td><td class="num">' + fmt(t.px, p.dp) + '</td><td class="num">' + fmt(t.size, p.base === 'BTC' ? 4 : 0) + '</td></tr>').join('');
  $('#t-qty-u').textContent = p.base;
  const qq = S.mm.q[S.pair];
  if (p.gamma) {
    const w = clamp(Math.abs(qq) / 20, 0, 1) * 50; const f = $('#inv-fill'); f.style.left = (qq < 0 ? 50 - w : 50) + '%'; f.style.width = w + '%';
    $('#inv-sub').textContent = 'q = ' + sgn(qq, 2) + ' lotes de 10,000 PMX · sesgo de reserva ' + sgn(-q.skew, 5) + ' ' + p.quote;
    $('.inv').hidden = false;
  } else $('.inv').hidden = true;
  renderTicketEst();
}
function walkBook(side, qty) {
  const b = bookLevels(S.pair); const lv = side === 'buy' ? b.asks : b.bids; let left = qty, cost = 0;
  for (const x of lv) { const t = Math.min(left, x.size); cost += t * x.price; left -= t; if (left <= 0) break; }
  return { filled: qty - Math.max(0, left), cost, vwap: cost / Math.max(1e-12, qty - Math.max(0, left)), short: left > 1e-9, mid: (b.qt.bid + b.qt.ask) / 2 };
}
function renderTicketEst() {
  const side = $('#ticket').side.value, p = AS[S.pair];
  const qty = parseFloat($('#t-qty').value.replace(/[,\s]/g, ''));
  const go = $('#t-go'); go.textContent = (side === 'buy' ? 'Comprar ' : 'Vender ') + p.base;
  const field = $('#t-qty').closest('.field'), help = field.querySelector('.help');
  if (!(qty > 0)) { $('#t-est').innerHTML = ''; field.dataset.state = 'error'; help.textContent = 'Escribe una cantidad.'; go.disabled = true; return; }
  const w = walkBook(side, qty);
  if (w.short) { field.dataset.state = 'error'; help.textContent = 'La cantidad supera la profundidad visible del libro.'; go.disabled = true; }
  else { field.dataset.state = ''; help.textContent = ''; go.disabled = false; }
  const fee = w.cost * 0.001;
  $('#t-est').innerHTML = '<dt>Precio medio</dt><dd>' + fmt(w.vwap, p.dp + (p.base === 'BTC' ? 0 : 0)) + ' ' + p.quote + '</dd><dt>Impacto</dt><dd>' + bps(Math.abs(w.vwap - w.mid) / w.mid, 1) + '</dd><dt>Comisión (0.10 %)</dt><dd>' + fmt(fee, 2) + ' ' + p.quote + '</dd><dt class="total">' + (side === 'buy' ? 'Total a pagar' : 'Total a recibir') + '</dt><dd>' + fmt(side === 'buy' ? w.cost + fee : w.cost - fee, 2) + ' ' + p.quote + '</dd>';
}
function submitTicket(e) {
  e.preventDefault();
  const side = $('#ticket').side.value, p = AS[S.pair];
  const qty = parseFloat($('#t-qty').value.replace(/[,\s]/g, '')); if (!(qty > 0)) return;
  const w = walkBook(side, qty); if (w.short) return;
  const fee = w.cost * 0.001;
  pushTape(S.pair, side, w.vwap, qty);
  if (p.gamma) S.mm.q[S.pair] += (side === 'buy' ? -qty : qty) / 1e4;
  addActivity({ type: 'orden', detail: (side === 'buy' ? 'Compra ' : 'Venta ') + p.label + ' a mercado', inTxt: side === 'buy' ? fmt(w.cost + fee, 2) + ' ' + p.quote : fmt(qty, p.base === 'BTC' ? 6 : 2) + ' ' + p.base, outTxt: side === 'buy' ? fmt(qty, p.base === 'BTC' ? 6 : 2) + ' ' + p.base : fmt(w.cost - fee, 2) + ' ' + p.quote, status: 'ejecutada', vwap: w.vwap, pair: p.label, side, qty, fee });
  toast((side === 'buy' ? 'Compra' : 'Venta') + ' ejecutada a ' + fmt(w.vwap, p.dp) + ' ' + p.quote);
  renderMarket();
}

/* --- Reservas --- */
const VAULT_LABELS = [['hotHk', 'Caliente HKD (Lightning)', 'var(--series-2)'], ['hotMx', 'Caliente MXN (Lightning)', 'var(--series-1)'], ['margin', 'Margen de derivados', 'var(--series-3)'], ['cold', 'Fría multifirma 3 de 5', 'var(--series-4)']];
let ADDR = null, MERKLE = null;
function addresses() {
  if (ADDR) return ADDR;
  const seed = S.vault.seed; ADDR = {};
  for (const [k] of VAULT_LABELS) { const h = SHA('pmx-addr-' + seed + '-' + k); ADDR[k] = bech32('bc', hexBytes(k === 'cold' ? h : h.slice(0, 40))); }
  return ADDR;
}
function computeMerkle() {
  const r = mulberry32(S.vault.seed), L = S.vault.supply, n = 2048;
  const w = Array.from({ length: n }, () => Math.pow(-Math.log(r() + 1e-12), 1.6));
  const sw = w.reduce((a, b) => a + b, 0);
  const t0 = performance.now();
  let cents = w.map((x) => Math.floor((x / sw) * L * 100));
  const diff = Math.round(L * 100) - cents.reduce((a, b) => a + b, 0); cents[0] += diff;
  const leaves = cents.map((c, i) => SHA('acct:' + SHA('pmx-' + S.vault.seed + '-' + i).slice(0, 16) + '|bal:' + c));
  const root = merkleRoot(leaves);
  // ruta de la hoja 0
  let idx = 0, lv = leaves, path = 0; while (lv.length > 1) { const nx = []; for (let i = 0; i < lv.length; i += 2) nx.push(SHA(lv[i] + (lv[i + 1] || lv[i]))); lv = nx; idx >>= 1; path++; }
  MERKLE = { root, n, sum: cents.reduce((a, b) => a + b, 0) / 100, ms: performance.now() - t0, path, t: Date.now(), leaf0: leaves[0] };
}
function renderReserves() {
  const vs = vaultState(), px = oraclePx(), a = S.vault.btc;
  $('#r-btc').innerHTML = fmt(vs.B, 4) + ' <small>BTC</small>';
  $('#r-btc-usd').textContent = '≈ ' + fmt(vs.B * px, 0) + ' USD al precio del oráculo';
  $('#r-supply').innerHTML = fmt(vs.L, 0) + ' <small>PMX</small>';
  $('#r-surplus').innerHTML = fmt(vs.surplusUsd, 0) + ' <small>USD</small>';
  $('#r-surplus-sub').textContent = 'Colateral ' + pct(vs.CR, 2) + ' · MCR ' + pct(mcrNow(), 1);
  $('#r-hedge').innerHTML = fmt(vs.contracts, 0) + ' <small>contratos</small>';
  $('#r-hedge-sub').textContent = 'Nocional ' + fmt(vs.N, 0) + ' USD · P&L ' + sgn(vs.pnlBtc, 4) + ' BTC';
  const tot = vs.B;
  $('#r-seg').innerHTML = VAULT_LABELS.map(([k, name, c]) => { const v = k === 'margin' ? a.margin : a[k]; const share = v / tot; return '<div style="flex-grow:' + Math.max(0.0001, share).toFixed(5) + ';background:' + c + '" title="' + esc(name) + '">' + (share > 0.09 ? '<span>' + pct(share, 1) + '</span>' : '') + '</div>'; }).join('');
  legend($('#r-seg-legend'), VAULT_LABELS.map(([k, name, c]) => ({ name: name + ' · ' + fmt(a[k], 3) + ' BTC (' + pct(a[k] / tot, 1) + ')', color: c })));
  const ad = addresses();
  $('#r-addr').innerHTML = VAULT_LABELS.map(([k, name, c]) => '<tr><td><span class="legend"><span><i style="background:' + c + '"></i>' + esc(name) + '</span></span></td><td>' + ad[k] + '</td><td class="num">' + fmt(a[k], 6) + '</td></tr>').join('') + '<tr><td>P&amp;L de cobertura no realizado</td><td>Cuenta de margen</td><td class="num">' + sgn(vs.pnlBtc, 6) + '</td></tr>';
  if (!MERKLE) computeMerkle();
  $('#r-proof').innerHTML = [
    ['Raíz de Merkle', MERKLE.root], ['Hojas (cuentas)', fmt(MERKLE.n, 0) + ' · profundidad ' + MERKLE.path], ['Suma de hojas', fmt(MERKLE.sum, 2) + ' PMX ' + (Math.abs(MERKLE.sum - S.vault.supply) < 0.01 ? '= pasivo total ✓' : '≠ pasivo actual, recalcula')],
    ['Primera hoja', MERKLE.leaf0], ['Calculado', tclock(MERKLE.t, TZ_MX, true) + ' CDMX en ' + fmt(MERKLE.ms, 1) + ' ms'], ['Reserva / pasivo', fmt(vs.B * px, 0) + ' USD / ' + fmt(vs.L, 0) + ' USD'],
  ].map(([k, v]) => '<div><dt>' + esc(k) + '</dt><dd' + (/^[0-9a-f]{64}$/.test(v) ? ' class="hash"' : '') + '>' + esc(v) + '</dd></div>').join('');
}

/* --- Motores --- */
function renderHMM(full) {
  const P = S.hmm; if (!P) return;
  const F = S.filt.slice(-120).concat([S.live]);
  const C = S.candles.slice(-(F.length - 1)).map((c) => c.t).concat([S.cur.t]);
  const xs = C.map((_, i) => i);
  const xt = []; for (let i = 0; i < xs.length; i += 30) xt.push(i);
  lineChart($('#ch-hmm'), {
    xs, series: REG.map((R, k) => ({ name: R.name, color: R.color, values: F.map((f) => f[k]) })), yMin: 0, yMax: 1, yFmt: (v) => pct(v, 0), xFmt: (i) => tclock(C[i]), xTicks: xt, label: 'Probabilidad filtrada por régimen',
    tip: (i) => '<b>' + tclock(C[i]) + ' CDMX</b><br>' + REG.map((R, k) => key(R.color) + R.short + ': ' + pct(F[i][k], 1)).join('<br>') + '<br>MCR ' + pct(mcrNow(F[i]), 1),
  });
  $('#hmm-sub').textContent = 'Últimos 120 minutos. Ahora: ' + REG[regNow()].name + ' (' + pct(S.live[regNow()], 0) + ').';
  $('#hmm-mcr').textContent = pct(mcrNow(), 2);
  if (full) {
    legend($('#hmm-legend'), REG.map((R) => ({ name: R.short, color: R.color, kind: 'line' })));
    $('#hmm-ll').textContent = 'log L = ' + fmt(P.ll, 1) + ' · ' + P.it + ' iteraciones EM sobre ' + P.T + ' minutos · ' + tclock(P.at, TZ_MX, true);
    $('#hmm-A').innerHTML = '<caption>Matriz de transición A (por minuto)</caption><tr><th scope="col">De \\ a</th>' + REG.map((R) => '<th scope="col" class="num">' + R.short + '</th>').join('') + '</tr>' + P.A.map((row, i) => '<tr><th scope="row">' + REG[i].short + '</th>' + row.map((x) => '<td class="num">' + fmt(x, 4) + '</td>').join('') + '</tr>').join('');
    $('#hmm-B').innerHTML = '<caption>Emisiones B: normales por estado</caption><tr><th scope="col">Estado</th><th scope="col" class="num">μ retorno</th><th scope="col" class="num">σ retorno</th><th scope="col" class="num">μ log-volumen</th><th scope="col" class="num">MCR<sub>i</sub></th></tr>' + P.mu.map((mu, i) => '<tr><th scope="row">' + REG[i].short + '</th><td class="num">' + bps(mu[0], 2) + '</td><td class="num">' + bps(P.sd[i][0], 2) + '</td><td class="num">' + fmt(mu[1], 2) + '</td><td class="num">' + pct(MCR[i], 0) + '</td></tr>').join('');
  }
}
let STRESS = null;
function renderStress() {
  if (!STRESS) return;
  const s = STRESS, xs = s.pts.map((p) => p.t);
  lineChart($('#ch-stress'), {
    xs, series: [
      { name: 'Colateral sin cobertura', color: 'var(--series-1)', values: s.pts.map((p) => p.un) },
      { name: 'Colateral con cobertura', color: 'var(--series-2)', values: s.pts.map((p) => p.hd) },
      { name: 'MCR exigido', color: 'var(--series-3)', values: s.pts.map((p) => p.m) },
    ], refs: [{ y: 1, label: 'Paridad 1.00' }], yFmt: (v) => fmt(v, 2) + '×', xFmt: (t) => fmt(t / 60, 0) + ' h', xTicks: [0, 240, 480, 720, 960, 1200, 1439], label: 'Escenario de estrés',
    tip: (i) => { const p = s.pts[i]; return '<b>Hora ' + fmt(p.t / 60, 1) + '</b><br>BTC ' + pct(p.S / s.pts[0].S - 1, 1) + '<br>' + key('var(--series-1)') + 'Sin cobertura ' + fmt(p.un, 3) + '×<br>' + key('var(--series-2)') + 'Con cobertura ' + fmt(p.hd, 3) + '×<br>' + key('var(--series-3)') + 'MCR ' + fmt(p.m, 3) + '×'; },
  });
  legend($('#stress-legend'), [{ name: 'Colateral sin cobertura', color: 'var(--series-1)', kind: 'line' }, { name: 'Colateral con cobertura', color: 'var(--series-2)', kind: 'line' }, { name: 'MCR exigido', color: 'var(--series-3)', kind: 'line' }, { name: 'Paridad', color: 'transparent', kind: 'dash' }]);
  const facts = [
    ['Caída máxima de BTC', pct(s.drop, 1)],
    ['Mínimo con cobertura', fmt(s.minHd, 3) + '× · ' + (s.minHd >= 1 ? 'paridad intacta' : 'bajo paridad')],
    ['Mínimo sin cobertura', fmt(s.minUn, 3) + '× · ' + (s.breakAt == null ? 'paridad intacta' : 'rompe en la hora ' + fmt(s.breakAt / 60, 1))],
    ['MCR máximo exigido', pct(s.maxM, 1)],
    ['Minutos clasificados en estrés', fmt(s.stressMin, 0) + ' de 1,440'],
    ['Minutos con acuñación en pausa', fmt(s.pausedMin, 0)],
  ];
  $('#stress-facts').innerHTML = facts.map(([k, v]) => '<div><dt>' + k + '</dt><dd>' + v + '</dd></div>').join('');
}
let MC = null;
function runMonteCarlo() {
  const vs = vaultState(), S0 = oraclePx(), CR0 = vs.V / vs.L, Bfrac = vs.B * S0 / vs.L;
  const par = { sigma: 0.6, lambda: 10, muJ: -0.06, sJ: 0.1, days: 30, paths: 4000, f8: 0.00008, sf: 0.00012 };
  const dt = 1 / 365, k = Math.exp(par.muJ + par.sJ ** 2 / 2) - 1;
  const un = new Float64Array(par.paths), hd = new Float64Array(par.paths);
  const t0 = performance.now();
  for (let p = 0; p < par.paths; p++) {
    let ln = 0, fund = 0;
    for (let d = 0; d < par.days; d++) {
      ln += (-0.5 * par.sigma ** 2 - par.lambda * k) * dt + par.sigma * Math.sqrt(dt) * randn();
      const nj = poisson(par.lambda * dt); for (let j = 0; j < nj; j++) ln += par.muJ + par.sJ * randn();
      for (let e = 0; e < 3; e++) fund += par.f8 + par.sf * randn();
    }
    const ST = S0 * Math.exp(ln);
    un[p] = Bfrac * ST / S0;
    hd[p] = 1 + (CR0 - 1) * ST / S0 + fund - 0.0004;
  }
  const ms = performance.now() - t0;
  const q = (arr, a) => { const s = Array.from(arr).sort((x, y) => x - y); return s[Math.floor(a * (s.length - 1))]; };
  const below = (arr) => arr.reduce((c, x) => c + (x < 1 ? 1 : 0), 0) / arr.length;
  MC = { par, un, hd, ms, CR0, Bfrac, pUn: below(un), pHd: below(hd), q1Un: q(un, 0.01), q1Hd: q(hd, 0.01), medUn: q(un, 0.5), medHd: q(hd, 0.5) };
}
function histo(arr, lo, hi, nb) { const out = new Array(nb).fill(0), w = (hi - lo) / nb; for (const x of arr) out[clamp(Math.floor((x - lo) / w), 0, nb - 1)]++; return out; }
function renderIto(full) {
  const vs = vaultState();
  $('#ito-n').innerHTML = fmt(vs.N, 0) + ' <small>USD</small>';
  $('#ito-n-sub').textContent = fmt(vs.contracts, 0) + ' contratos × 100 USD · S̄₀ = ' + fmt(1 / S.vault.hedge.inv, 0);
  $('#ito-delta').innerHTML = fmt(vs.delta, 4) + ' <small>BTC</small>';
  $('#ito-margin').innerHTML = fmt(vs.marginEff, 4) + ' <small>BTC</small>';
  $('#ito-margin-sub').textContent = fmt(vs.mRatio, 2) + '× del requerido N / (' + LEV + '·S) = ' + fmt(vs.req, 4) + ' BTC';
  $('#ito-funding').innerHTML = sgn(S.funding * 1e4, 2) + ' <small>pb</small>';
  $('#ito-funding-sub').textContent = (S.funding >= 0 ? 'El corto cobra ' : 'El corto paga ') + fmt(Math.abs(S.funding * vs.N), 0) + ' USD por periodo · acumulado ' + sgn(S.vault.hedge.fundingUsd, 2) + ' USD';
  $('#ito-orders').innerHTML = S.orders.length ? S.orders.slice(0, 12).map((o) => '<tr><td>' + tclock(o.t, TZ_MX, true) + '</td><td class="hash">' + esc(o.origin) + '</td><td class="num">' + sgn(o.dN, 2) + '</td><td class="num">' + sgn(o.contracts, 0) + '</td><td class="num">' + o.slices + '</td><td class="num">' + fmt(o.px, 2) + '</td><td class="num">' + bps(o.slip, 2) + '</td></tr>').join('')
    : '<tr><td colspan="7" class="sub">La cobertura vigente se abrió al constituir la bóveda. Cada transferencia agrega aquí su apertura y su cierre.</td></tr>';
  if (!full) return;
  if (!MC) runMonteCarlo();
  const m = MC, lo = 0.4, hi = 3.0, nb = 26, w = (hi - lo) / nb;
  const cats = Array.from({ length: nb }, (_, i) => fmt(lo + i * w, 1));
  const parity = (1 - lo) / w;
  const colorAt = (base) => (j, i) => (lo + (i + 1) * w <= 1.0001 ? 'var(--color-crit)' : base);
  const tipF = (arr) => (i) => '<b>' + fmt(lo + i * w, 1) + '× – ' + fmt(lo + (i + 1) * w, 1) + '×</b><br>' + fmt(arr[i], 0) + ' trayectorias (' + pct(arr[i] / m.par.paths, 1) + ')';
  const hu = histo(m.un, lo, hi, nb), hh = histo(m.hd, lo, hi, nb), ymax = Math.max(...hu, ...hh);
  barChart($('#ch-ito-a'), { cats, series: [{ name: 'Sin cobertura', color: 'var(--series-1)', values: hu }], yMax: ymax, yFmt: (v) => fmt(v, 0), labelEvery: 5, refX: parity, refLabel: 'Paridad', colorAt: colorAt('var(--series-1)'), tip: tipF(hu), label: 'Distribución de colateral a 30 días sin cobertura' });
  barChart($('#ch-ito-b'), { cats, series: [{ name: 'Con cobertura', color: 'var(--series-2)', values: hh }], yMax: ymax, yFmt: (v) => fmt(v, 0), labelEvery: 5, refX: parity, refLabel: 'Paridad', colorAt: colorAt('var(--series-2)'), tip: tipF(hh), label: 'Distribución de colateral a 30 días con cobertura' });
  $('#ito-params').innerHTML = ['σ = <b>' + pct(m.par.sigma, 0) + '</b> anual', 'λ = <b>' + m.par.lambda + '</b> saltos/año', 'μ<sub>J</sub> = <b>' + pct(m.par.muJ, 0) + '</b>', 'σ<sub>J</sub> = <b>' + pct(m.par.sJ, 0) + '</b>', 'fondeo medio <b>' + bps(m.par.f8, 1) + '</b> / 8 h', 'colateral inicial <b>' + fmt(m.CR0, 3) + '×</b>', '<b>' + fmt(m.par.paths, 0) + '</b> trayectorias en ' + fmt(m.ms, 0) + ' ms'].map((x) => '<span>' + x + '</span>').join('');
  $('#ito-facts').innerHTML = [
    ['P(bajo paridad) sin cobertura', pct(m.pUn, 2)], ['P(bajo paridad) con cobertura', pct(m.pHd, 2)],
    ['Percentil 1 sin cobertura', fmt(m.q1Un, 3) + '×'], ['Percentil 1 con cobertura', fmt(m.q1Hd, 3) + '×'],
    ['Mediana sin cobertura', fmt(m.medUn, 3) + '×'], ['Mediana con cobertura', fmt(m.medHd, 3) + '×'],
  ].map(([k, v]) => '<div><dt>' + k + '</dt><dd>' + v + '</dd></div>').join('');
}
function renderKelly(full) {
  const k = S.kelly = kellyPlan(), a = S.vault.btc;
  const H = Math.floor(k.h0);
  if (full || !renderKelly._h || renderKelly._h !== H) {
    renderKelly._h = H;
    const cats = Array.from({ length: 24 }, (_, h) => String(h).padStart(2, '0'));
    barChart($('#ch-flow'), {
      cats, series: [{ name: 'Pagos en MXN (SPEI)', color: 'var(--series-1)', values: k.prof.mx }, { name: 'Pagos en HKD (FPS)', color: 'var(--series-2)', values: k.prof.hk }], yFmt: (v) => compact(v), labelEvery: 3, highlight: H, label: 'Demanda esperada de liquidación por hora',
      tip: (i) => '<b>' + cats[i] + ':00 CDMX · ' + String((i + 14) % 24).padStart(2, '0') + ':00 HKT</b><br>' + key('var(--series-1)') + 'MXN: ' + fmt(k.prof.mx[i], 0) + ' USD/h<br>' + key('var(--series-2)') + 'HKD: ' + fmt(k.prof.hk[i], 0) + ' USD/h' + (i === H ? '<br>Hora actual' : ''),
    });
    legend($('#kelly-flow-legend'), [{ name: 'Pagos en MXN (SPEI)', color: 'var(--series-1)' }, { name: 'Pagos en HKD (FPS)', color: 'var(--series-2)' }]);
  }
  $('#kelly-sub').textContent = 'Reserva ' + fmt(k.B, 3) + ' BTC · frío mínimo 50 %' + (k.capped ? ' (activo: limita Kelly)' : '');
  const row = (name, kel, floor, tgt, act) => '<tr><td>' + name + '</td><td class="num">' + kel + '</td><td class="num">' + floor + '</td><td class="num">' + fmt(tgt, 3) + '</td><td class="num">' + fmt(act, 3) + '</td></tr>';
  $('#kelly-alloc').innerHTML = row('Caliente HKD', pct(k.fHk, 1), fmt(k.floorHk, 3), k.tHk, a.hotHk) + row('Caliente MXN', pct(k.fMx, 1), fmt(k.floorMx, 3), k.tMx, a.hotMx) + row('Margen', '—', fmt(k.floorM, 3), k.tM, a.margin) + row('Fría', '—', fmt(k.B * 0.5, 3), k.tCold, a.cold);
  $('#kelly-cap').innerHTML = [
    ['Orden máxima a Hong Kong', fmt(k.capHkUsd * S.hkd, 0) + ' HKD'], ['Equivalente en MXN', fmt(k.capHkUsd * S.mxn, 0) + ' MXN'], ['Orden máxima a México', fmt(k.capMxUsd * S.mxn, 0) + ' MXN'],
    ['Demanda HKD próximas ' + fmt(KP.refill, 1) + ' h', fmt(k.wHk, 0) + ' USD'], ['Q99.9 de esa demanda', fmt(q999(k.wHk), 0) + ' USD'], ['Crecimiento medio Kelly / Kelly', fmt(k.growthHalf / k.growthFull, 2)],
  ].map(([x, y]) => '<div><dt>' + x + '</dt><dd>' + y + '</dd></div>').join('');
  $('#kelly-rules').innerHTML = k.rules.map((r) => '<li data-s="' + r.s + '"><svg class="ic"><use href="#' + (r.s === 'good' ? 'i-check' : 'i-alert') + '"/></svg><div>' + esc(r.t) + '<small>' + esc(r.d) + '</small></div></li>').join('');
  $('#k-mu-o').textContent = pct(KP.mu, 1); $('#k-sig-o').textContent = pct(KP.sig, 0); $('#k-ref-o').textContent = fmt(KP.refill, 1) + ' h'; $('#k-d-o').textContent = compact(KP.daily) + ' USD';
}
function prettyJSON(o) {
  return '{\n' + Object.entries(o).map(([k, v]) => {
    if (Array.isArray(v) && v.length && typeof v[0] === 'object') return '  "' + k + '": [\n' + v.map((x) => '    ' + JSON.stringify(x)).join(',\n') + '\n  ]';
    return '  "' + k + '": ' + JSON.stringify(v);
  }).join(',\n') + '\n}';
}
function renderBayes() {
  const p = S.post;
  $('#by-mu').innerHTML = fmt(p.mu, 2) + ' <small>USD</small>';
  $('#by-ci').textContent = 'IC 95 % ' + fmt(p.mu - 1.96 * p.sd, 2) + ' – ' + fmt(p.mu + 1.96 * p.sd, 2);
  $('#by-sd').innerHTML = fmt(p.sd, 2) + ' <small>USD · ' + fmt(p.sdB * 1e4, 2) + ' pb</small>';
  $('#by-lat').innerHTML = (p.ms < 0.1 ? '&lt; 0.1' : fmt(p.ms, 2)) + ' <small>ms</small>';
  $('#by-brk').textContent = S.breaker ? 'Activo' : 'Cerrado';
  $('#by-brk-sub').textContent = S.breaker ? 'Redenciones en pausa desde ' + tclock(S.breakSince, TZ_MX, true) : 'Acuñación y redención operando';
  $('#by-src').innerHTML = S.oracleSrc.map((o) => {
    const state = o.off ? ['warn', 'Sin datos'] : o.used ? ['good', 'Usada'] : ['crit', o.tag === 'flash' ? 'Aislada: flash crash' : o.tag === 'wash' ? 'Aislada: profundidad inflada' : 'Aislada'];
    return '<tr><td>' + esc(o.name) + '</td><td class="num">' + (o.off ? '—' : fmt(o.px, 2)) + '</td><td class="num">' + (o.off ? '—' : compact(o.depth) + ' USD') + '</td><td class="num">' + (o.off ? '—' : sgn(o.resid * 1e4, 1) + ' pb') + '</td><td><span class="wbar"><i style="transform:scaleX(' + (o.w || 0).toFixed(3) + ')"></i></span></td><td><span class="tag" data-s="' + state[0] + '"><svg class="ic"><use href="#' + (state[0] === 'good' ? 'i-check' : 'i-alert') + '"/></svg>' + state[1] + '</span></td></tr>';
  }).join('');
  const L = S.lastPayload;
  if (L) {
    $('#by-payload').textContent = prettyJSON({ ...L.body, sha256: L.digest, alg: 'ES256', sig: L.sig || 'no disponible en este navegador' });
    const v = $('#by-verify'); v.dataset.s = L.ok ? 'good' : 'warn'; v.querySelector('use').setAttribute('href', L.ok ? '#i-check' : '#i-alert'); v.lastElementChild.textContent = L.ok ? 'Firma verificada' : 'Sin firma';
    $('#by-key').textContent = SIG.pubHex ? 'Clave pública P-256 del oráculo · huella ' + SHA(hexBytes(SIG.pubHex)).slice(0, 16) : 'El navegador no expone WebCrypto; se publica solo el hash.';
  }
}
function renderLLN(full) {
  const m = S.mm, muNow = expectedX(), mu = m.n ? m.eSum / m.n : muNow, sd = Math.sqrt(m.M2 / Math.max(1, m.n - 1));
  const qt = quoteAS('PMXMXN');
  $('#ln-mu').innerHTML = sgn(mu, 3) + ' <small>USD</small>';
  $('#ln-mu-sub').textContent = 'Promedio de las cotizaciones vigentes en cada operación · ahora ' + sgn(muNow, 3) + ' USD';
  $('#ln-mean').innerHTML = (m.n ? sgn(m.mean, 3) : '—') + ' <small>USD</small>';
  $('#ln-n').textContent = fmt(m.n, 0) + ' operaciones · σ̂ = ' + fmt(sd, 2) + ' · ganadoras ' + (m.n ? pct(m.wins / m.n, 1) : '—');
  const cant = m.n > 1 ? (sd * sd) / (sd * sd + m.n * mu * mu) : 1;
  $('#ln-p').textContent = m.n > 1 ? pct(cant, 3) : '—';
  $('#ln-p-sub').textContent = 'Cantelli · aproximación normal ' + (m.n > 1 ? pct(PHI(-Math.sqrt(m.n) * mu / sd), 4) : '—');
  $('#ln-nstar').textContent = mu > 0 && sd > 0 ? fmt(Math.ceil(99 * sd * sd / (mu * mu)), 0) : '—';
  const pts = m.pts.filter((p) => p.n >= 10).concat(m.n >= 10 ? [{ n: m.n, mean: m.mean, sd, e: mu }] : []);
  if (pts.length > 2) {
    const xs = pts.map((p) => Math.log10(p.n));
    const xt = [1, 2, 3, 4, 5, 6].filter((v) => v >= xs[0] && v <= xs[xs.length - 1]);
    const lo = pts.map((p) => (p.n > 5 ? p.mean - 1.96 * p.sd / Math.sqrt(p.n) : NaN)), hi = pts.map((p) => (p.n > 5 ? p.mean + 1.96 * p.sd / Math.sqrt(p.n) : NaN));
    lineChart($('#ch-lln'), {
      xs, series: [{ name: 'Media observada', color: 'var(--series-2)', values: pts.map((p) => p.mean) }, { name: 'E[X] acumulado', color: 'var(--color-muted)', dash: true, values: pts.map((p) => p.e) }], band: { lo, hi, color: 'var(--series-2)' }, refs: [{ y: 0, label: '0' }],
      yMin: Math.max(-6, Math.min(-1, ...pts.filter((p) => p.n > 30).map((p) => p.mean - 1.96 * p.sd / Math.sqrt(p.n)))), yMax: Math.min(8, Math.max(2, ...pts.filter((p) => p.n > 30).map((p) => p.mean + 1.96 * p.sd / Math.sqrt(p.n)))),
      yFmt: (v) => fmt(v, 1), xFmt: (v) => compact(10 ** v), xTicks: xt, endDot: true, label: 'Convergencia de la media por operación',
      tip: (i) => '<b>n = ' + fmt(pts[i].n, 0) + '</b><br>' + key('var(--series-2)') + 'Media ' + sgn(pts[i].mean, 3) + ' USD<br>E[X] ' + sgn(pts[i].e, 3) + ' USD<br>Banda ± ' + fmt(1.96 * pts[i].sd / Math.sqrt(pts[i].n), 3),
    });
  }
  if (full) legend($('#ln-legend'), [{ name: 'Media observada', color: 'var(--series-2)', kind: 'line' }, { name: 'Banda 95 %', color: 'color-mix(in oklch, var(--series-2) 30%, transparent)' }, { name: 'E[X] de las cotizaciones', color: 'transparent', kind: 'dash' }]);
  const p = AS.PMXMXN;
  $('#ln-as').innerHTML = [
    ['Precio medio s', fmt(qt.s, 4) + ' MXN'], ['Inventario q', sgn(qt.q, 2) + ' lotes'], ['Horizonte T − t', fmt(qt.T, 3) + ' día'],
    ['Reserva r = s − qγσ²(T − t)', fmt(qt.r, 5)], ['Spread δ = γσ²(T − t) + (2/γ)ln(1 + γ/k)', fmt(qt.delta, 5) + ' MXN'], ['Bid / ask', fmt(qt.bid, 4) + ' / ' + fmt(qt.ask, 4)], ['γ · k · σ', p.gamma + ' · ' + p.k + ' · ' + p.sigma],
  ].map(([x, y]) => '<div><dt>' + x + '</dt><dd>' + y + '</dd></div>').join('');
  $('#ln-econ').innerHTML = [
    ['Medio spread capturado', bps(qt.delta / 2 / qt.s, 2)], ['Comisión de cobertura', '− ' + bps(COST.hedge, 1)], ['Deslizamiento medio', '− ' + bps(COST.slip, 1)], ['Selección adversa', '± ' + bps(COST.adv, 0) + ' (media 0)'],
    ['Red, SPEI y FPS prorrateados', '− ' + fmt(COST.fixed, 2) + ' USD'], ['Resultado esperado', sgn(mu, 3) + ' USD por operación'],
  ].map(([x, y]) => '<div><dt>' + x + '</dt><dd>' + y + '</dd></div>').join('');
}
function renderEngines(full) {
  const t = S.engTab;
  if (t === 'hmm') { renderHMM(full); if (full) renderStress(); }
  if (t === 'ito') renderIto(full);
  if (t === 'kelly') renderKelly(full);
  if (t === 'bayes') renderBayes();
  if (t === 'lln') renderLLN(full);
}

/* --- Actividad --- */
function renderActivity() {
  const a = S.activity; $('#act-empty').hidden = a.length > 0; $('.act').hidden = !a.length;
  $('#act-sub').textContent = a.length ? fmt(a.length, 0) + ' movimientos guardados en este navegador.' : 'Movimientos de esta cuenta.';
  $('#act-body').innerHTML = a.map((x) => {
    const s = x.status === 'liquidada' || x.status === 'ejecutada' || x.status === 'aplicado' ? 'good' : 'warn';
    return '<tr><td>' + tdate(x.ts) + '</td><td>' + esc(x.type) + '</td><td>' + esc(x.type === 'transferencia' ? x.benef : x.detail) + '</td><td class="num">' + esc(x.inTxt || '—') + '</td><td class="num">' + esc(x.outTxt || '—') + '</td><td><span class="tag" data-s="' + s + '"><svg class="ic"><use href="#' + (s === 'good' ? 'i-check' : 'i-alert') + '"/></svg>' + esc(x.status) + '</span></td><td><button class="btn small ghost" type="button" data-receipt="' + esc(x.id) + '">Ver</button></td></tr>';
  }).join('');
}
function openReceipt(id) {
  const x = S.activity.find((a) => a.id === id); if (!x) return;
  const d = $('#receipt');
  $('#rc-title').textContent = x.type === 'transferencia' ? 'Comprobante ' + x.id : 'Movimiento ' + x.id;
  $('#rc-sub').textContent = tdate(x.ts) + ' CDMX';
  const facts = x.type === 'transferencia'
    ? [['Remitente', x.sender], ['RFC', x.rfc], ['Beneficiario', x.benef], ['FPS', x.fps], ['Enviado', x.inTxt], ['Recibido', x.outTxt], ['Tipo aplicado', '1 MXN = ' + fmt(x.quote.rate, 5) + ' HKD'], ['Tiempo total', fmt(x.secs, 1) + ' s'], ['Clave de rastreo SPEI', x.rastreo], ['Referencia FPS', x.frn], ['Raíz de Merkle de pasos', short(x.root, 16)]]
    : [['Detalle', x.detail], ['Entrada', x.inTxt], ['Salida', x.outTxt], ['Estado', x.status]];
  $('#rc-facts').innerHTML = facts.map(([k, v]) => '<div><dt>' + esc(k) + '</dt><dd>' + esc(v == null ? '—' : v) + '</dd></div>').join('');
  $('#rc-json').textContent = JSON.stringify(x, null, 2);
  $('#rc-dl').onclick = () => download(x.id + '.json', x);
  d.showModal();
}
function download(name, obj) {
  const url = URL.createObjectURL(new Blob([JSON.stringify(obj, null, 2)], { type: 'application/json' }));
  const a = document.createElement('a'); a.href = url; a.download = name; document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(url), 1000);
}
let toastT = null;
function toast(msg) { const t = $('#toast'); t.textContent = msg; t.classList.add('on'); clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove('on'), 2600); }

/* ============================================================
 * Navegación
 * ============================================================ */
function route() {
  const v = (location.hash || '#panel').slice(1).split('/')[0];
  S.view = TITLES[v] ? v : 'panel';
  $$('.view').forEach((s) => { s.hidden = s.dataset.view !== S.view; });
  $$('[data-nav]').forEach((a) => { if (a.dataset.nav === S.view) a.setAttribute('aria-current', 'page'); else a.removeAttribute('aria-current'); });
  $('#view-title').textContent = TITLES[S.view];
  document.title = TITLES[S.view] + ' · PayMexBTC';
  hideTip();
  renderView(true);
}
function renderView(full) {
  if (!S.post || !S.hmm) return;
  if (S.view === 'panel') renderPanel(full);
  if (S.view === 'enviar') renderQuote();
  if (S.view === 'mercado') renderMarket();
  if (S.view === 'reservas') renderReserves();
  if (S.view === 'motores') renderEngines(full);
  if (S.view === 'actividad' && full) renderActivity();
}
function selectTab(btn) {
  $$('.tabs [role="tab"]').forEach((b) => { const on = b === btn; b.setAttribute('aria-selected', on); b.tabIndex = on ? 0 : -1; $('#' + b.getAttribute('aria-controls')).hidden = !on; });
  S.engTab = btn.id.replace('tab-', '');
  hideTip();
  renderEngines(true);
}

/* ============================================================
 * Arranque
 * ============================================================ */
function bind() {
  window.addEventListener('hashchange', route);
  // pestañas de motores con flechas
  const tabs = $$('.tabs [role="tab"]');
  tabs.forEach((b, i) => {
    b.addEventListener('click', () => selectTab(b));
    b.addEventListener('keydown', (e) => {
      const d = e.key === 'ArrowRight' ? 1 : e.key === 'ArrowLeft' ? -1 : 0; if (!d) return;
      e.preventDefault(); const n = tabs[(i + d + tabs.length) % tabs.length]; n.focus({ preventScroll: true }); selectTab(n);
    });
  });
  // formulario
  const form = $('#send-form');
  form.addEventListener('input', (e) => { const n = e.target.name; if (['rfc', 'clabe', 'fps', 'amount'].includes(n)) validateField(n, true); renderQuote(); });
  form.rfc.addEventListener('blur', () => { form.rfc.value = form.rfc.value.toUpperCase(); validateField('rfc', true); });
  form.amount.addEventListener('blur', () => { const v = parseFloat(form.amount.value.replace(/[,\s]/g, '')); if (v > 0) form.amount.value = fmt(v, 2); });
  $('#f-fill').addEventListener('click', () => fillForm(makeClient()));
  form.addEventListener('submit', (e) => {
    e.preventDefault();
    if (S.running) return;
    const ok = ['sender', 'rfc', 'clabe', 'amount', 'benef', 'fps'].map((n) => validateField(n, true)).every(Boolean);
    if (!ok) { const bad = form.querySelector('[aria-invalid="true"]'); if (bad) bad.focus(); return; }
    const b = $('#f-submit'); b.disabled = true; b.dataset.state = 'loading'; b.textContent = 'Procesando…';
    runTransfer(readForm());
  });
  $('#pipe-new').addEventListener('click', () => { $('#pipe').hidden = true; fillForm(makeClient()); form.sender.focus(); });
  // mercado
  $('#pair-tabs').addEventListener('click', (e) => { const b = e.target.closest('[data-pair]'); if (!b) return; S.pair = b.dataset.pair; $('#t-qty').value = AS[S.pair].base === 'BTC' ? '0.25' : '5000'; renderMarket(); });
  $('#ticket').addEventListener('input', renderTicketEst);
  $('#ticket').addEventListener('change', renderTicketEst);
  $('#ticket').addEventListener('submit', submitTicket);
  // reservas
  $('#r-rebal').addEventListener('click', () => { rebalance(); renderView(true); });
  $('#r-merkle-go').addEventListener('click', () => { computeMerkle(); renderReserves(); });
  // motores
  $('#hmm-shock').addEventListener('click', () => { applyShock(); renderView(false); toast('Choque aplicado: BTC −8 %. El régimen se reclasifica en vivo.'); });
  $('#hmm-retrain').addEventListener('click', () => { trainHMM(); renderEngines(true); toast('Modelo reentrenado: ' + S.hmm.it + ' iteraciones'); });
  $('#stress-go').addEventListener('click', () => { STRESS = stressScenario(+$('#stress-mag').value); renderStress(); });
  $('#ito-run').addEventListener('click', () => { runMonteCarlo(); renderIto(true); });
  $('#by-flash').addEventListener('click', () => { S.attacks.flash = Date.now() + 20000; toast('Libro MXN reporta −19 % durante 20 s'); });
  $('#by-wash').addEventListener('click', () => { S.attacks.wash = Date.now() + 20000; toast('Pool on-chain: precio +3.5 % con profundidad ×12 durante 20 s'); });
  $('#by-drop').addEventListener('click', () => { S.attacks.drop = Date.now() + 25000; toast('Cuatro fuentes sin datos durante 25 s'); });
  $('#ln-burst').addEventListener('click', () => { let c = 0, g = 0; while (c < 5000 && g++ < 20000) c += fillOnce('PMXMXN', 1, true); renderLLN(false); toast(fmt(c, 0) + ' operaciones procesadas'); });
  $('#ln-reset').addEventListener('click', () => { const q = S.mm.q; initMM(); S.mm.q = q; renderLLN(true); });
  const sl = (id, fn) => $(id).addEventListener('input', (e) => { fn(+e.target.value); renderKelly(true); });
  sl('#k-mu', (v) => { KP.mu = v / 100; }); sl('#k-sig', (v) => { KP.sig = v / 100; }); sl('#k-ref', (v) => { KP.refill = v; }); sl('#k-d', (v) => { KP.daily = v * 1e6; });
  // actividad
  $('#act-body').addEventListener('click', (e) => { const b = e.target.closest('[data-receipt]'); if (b) openReceipt(b.dataset.receipt); });
  $('#act-export').addEventListener('click', () => download('paymexbtc-actividad-' + ymd(Date.now()) + '.json', S.activity));
  $('#rc-close').addEventListener('click', () => $('#receipt').close());
  $('#receipt').addEventListener('click', (e) => { if (e.target === $('#receipt')) $('#receipt').close(); });
  let rz = null; window.addEventListener('resize', () => { clearTimeout(rz); rz = setTimeout(() => renderView(true), 120); });
}

let lastTick = Date.now();
function tick() {
  const now = Date.now(), dt = (now - lastTick) / 1000; lastTick = now;
  marketTick(); oracleTick(); mmTick(); accrueFunding(dt);
  S.seq++;
  if (S.seq % 2 === 0) signPayload().then(() => { if (S.view === 'motores' && S.engTab === 'bayes') renderBayes(); });
  if (S.seq % 3 === 0) S.kelly = kellyPlan();
  if (S.seq % 30 === 0) persist();
  renderHeader();
  renderView(false);
}

async function boot() {
  const last = store.get('lastPrice', null);
  const seed = last && last.usd ? last : { usd: 97500, mxn: 18.25, hkd: 7.785 };
  S.mxn = seed.mxn; S.hkd = seed.hkd;
  S.activity = store.get('activity', []);
  initMM();
  buildHistory(seed.usd);
  bind();
  await Promise.race([fetchReference(true), sleep(2500)]);
  if (!S.anchor) fetchReference(false).then(() => {});
  S.vault = initVault(S.usd);
  const fresh = !S.vault.saved; S.vault.saved = true;
  trainHMM();
  oracleTick();
  if (fresh) rebalance(true);
  S.kelly = kellyPlan();
  for (let i = 0; i < 120; i++) { fillOnce('PMXMXN', 1); fillOnce('PMXHKD', 1); }
  await initSigner();
  await signPayload();
  STRESS = stressScenario(0.22);
  fillForm(makeClient());
  renderFeedSrc();
  renderHeader();
  route();
  setInterval(tick, 1000);
  addEventListener('pagehide', persist);
  setInterval(() => fetchReference(false), 120000);
}
boot();
