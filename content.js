// =====================================================================
// MANGA LIVE GALLERY PRO - panel dibuka lewat klik ikon ekstensi
//
// Ekstensi Chrome MV3:
//  - content.js   : berjalan di document_start + world "MAIN" (hook CORS dipasang segera)
//  - background.js: klik ikon ekstensi -> memanggil window.__mduiToggle() di tab aktif
//  - rules.json   : declarativeNetRequest, menambahkan header CORS pada respons gambar
// Panel TIDAK muncul otomatis. Mesin pemindai baru berjalan setelah panel dibuka pertama kali.
// Setelah mengubah ekstensi: reload ekstensi, lalu reload halaman komik (Ctrl+Shift+R).
// =====================================================================

// --- KONFIGURASI ---
const FORCE_CORS_ON_IMAGES = true; // paksa crossOrigin="anonymous" pada gambar lintas-origin (ada fallback otomatis)
const CORS_FORCE_HOSTS = [];       // [] = semua gambar lintas-origin; isi mis. ['tonarinoyj.jp'] untuk membatasi
const CORS_RETRIES = 2;            // coba ulang dengan CORS sebelum menyerah (error jaringan sesaat bukan alasan fallback)
const TAINT_RETRY_MS = 3000;       // canvas yang gagal dibaca dicoba lagi tiap sekian ms
const DOWNLOAD_DELAY_MS = 400;     // jeda antar unduhan agar tidak diblokir browser
const SCAN_INTERVAL_MS = 500;      // batas frekuensi scan akibat mutasi DOM
const POLL_FAST_MS = 1200;         // polling canvas saat masih ada canvas kosong
const POLL_SLOW_MS = 4000;         // polling canvas saat semua sudah terisi
const THUMB_WIDTH = 120;           // lebar thumbnail preview (hemat memori)
const FP_W = 32, FP_H = 48;        // ukuran sampel fingerprint canvas
const MIN_GROUP = 3;               // minimal jumlah canvas berukuran sama agar dianggap "halaman"
const MIN_CANVAS_BYTES = 3700;     // setara filter lama: dataURL < 5000 karakter = kosong
const MIN_IMG_BYTES = 2200;        // setara filter lama: dataURL < 3000 karakter
const ROW_TOLERANCE = 20;          // toleransi (px) untuk menganggap dua gambar berada di "baris" yang sama
const ORDER_MODES = ['dom', 'dom_rev', 'pos_rtl', 'pos_ltr', 'found'];

// --- STATE ---
// Map: key -> { ready, blob, url, thumbUrl, type, ext, num, seq, ref, domIndex, top, left }
const discoveredImagesMap = new Map();
const rejectedImgs = new Set();          // src yang sudah pasti gagal/terlalu kecil/CORS
let canvasFp = new WeakMap();            // canvas -> fingerprint terakhir
let canvasTaint = new WeakMap();         // canvas -> { name, ts } jika gagal dibaca (dicoba lagi berkala)
const canvasIds = new WeakMap();         // canvas -> id unik
let canvasIdCounter = 0;
let seqCounter = 0;                      // urutan penemuan (mode "ditemukan" + tie-breaker)
let epoch = 0;                           // penanda "generasi" agar callback async lama diabaikan
let pending = 0;                         // jumlah proses encode yang masih berjalan
let isDownloading = false;
let canvasMode = false;                  // true jika halaman komik = kumpulan canvas berukuran sama
// Info slot halaman: posisi canvas di antara elemen saudaranya (placeholder kosong ikut dihitung)
const slotInfo = { cont: 0, total: 0, stable: false };
let started = false;                     // mesin & UI baru dibuat saat panel pertama kali dibuka
let panelVisible = false;
const status = { total: 0, blank: 0, tainted: 0, group: 0, errors: {} };

// Mode urutan (diingat per situs lewat localStorage)
let orderMode = 'dom';
try {
  const saved = localStorage.getItem('mdui-order');
  if (saved && ORDER_MODES.indexOf(saved) !== -1) orderMode = saved;
} catch (e) { /* abaikan */ }

// Elemen UI (diisi oleh buildUI)
let uiContainer = null, gridEl = null, labelEl = null, statusEl = null;
let downloadBtnEl = null, minBtn = null, uiContent = null, coverageEl = null;
let retrySectionEl = null, retryGridEl = null, retryLabelEl = null, retryAllBtn = null;
let coverageConfirmResolve = null;

// =====================================================================
// HOOK CORS - dipasang SEGERA (sebelum script situs menggambar ke canvas)
// =====================================================================
const hookInfo = { active: false, lateStart: document.readyState !== 'loading', forced: 0, fallback: 0 };

function shouldForceCors(value) {
  try {
    const u = new URL(String(value), location.href);
    if (u.protocol !== 'http:' && u.protocol !== 'https:') return false;
    if (u.origin === location.origin) return false;
    if (CORS_FORCE_HOSTS.length === 0) return true;
    return CORS_FORCE_HOSTS.some((h) => u.hostname === h || u.hostname.endsWith('.' + h));
  } catch (e) {
    return false;
  }
}

// --- Pelacak retry CORS: dipakai panel untuk menampilkan gambar yang sedang di-retry ---
// Catatan dibuat HANYA saat gambar mengalami error (gambar normal tidak dicatat).
// id -> { id, url, name, state, tries, max, manual, bust, loaded, img, ref }
// state: 'retrying' | 'fallback' (dimuat tanpa CORS) | 'failed' | 'lost'
const corsTracker = new Map();
let corsIdCounter = 0;

function notifyCors() {
  if (typeof scheduleCorsUI === 'function') scheduleCorsUI();
}

function shortName(url) {
  try {
    const u = new URL(url, location.href);
    const seg = u.pathname.split('/').filter(Boolean).pop() || u.hostname;
    return seg.length > 16 ? '...' + seg.slice(-14) : seg;
  } catch (e) {
    return String(url).slice(-14);
  }
}

// Tambahkan parameter agar browser tidak memakai respons lama dari cache (yang mungkin tanpa header CORS)
function withCacheBust(url) {
  try {
    const u = new URL(url, location.href);
    u.searchParams.set('_mdr', String(Date.now()));
    return u.href;
  } catch (e) {
    return url + (String(url).indexOf('?') === -1 ? '?' : '&') + '_mdr=' + Date.now();
  }
}

function ensureRecord(img) {
  if (!img.__mdRec) {
    const url = img.__mdUrl || '';
    const rec = {
      id: ++corsIdCounter, url: url, name: shortName(url), state: 'retrying',
      tries: 0, max: CORS_RETRIES, manual: false, bust: false, loaded: false,
      img: img, ref: new WeakRef(img)
    };
    img.__mdRec = rec;
    corsTracker.set(rec.id, rec);
  }
  return img.__mdRec;
}

function markRecord(rec, state, extra) {
  Object.assign(rec, extra || {});
  rec.state = state;
  const img = rec.img || rec.ref.deref() || null;
  // Objek gambar dipegang kuat hanya selama belum termuat (supaya retry manual mungkin).
  // Gambar yang sudah termuat (bitmap besar) hanya dipegang lemah agar memori tidak menumpuk.
  const keep = state === 'retrying' || state === 'failed' || (state === 'fallback' && !rec.loaded);
  rec.img = keep ? img : null;
  notifyCors();
}

function dropRecord(img) {
  const rec = img.__mdRec;
  if (!rec) return;
  corsTracker.delete(rec.id);
  img.__mdRec = null;
  notifyCors();
}

function disarmCors(img) {
  if (img.__mdOnError) {
    img.removeEventListener('error', img.__mdOnError);
    img.__mdOnError = null;
  }
}

// Menyerah dengan CORS: muat tanpa CORS supaya situs tetap normal (canvas akan tainted)
function fallbackLoad(img, value, setSrc) {
  disarmCors(img);
  img.__mdForced = false;
  img.removeAttribute('crossorigin');
  hookInfo.fallback++;

  const rec = ensureRecord(img);
  markRecord(rec, 'fallback', { loaded: false });

  const onLoad = function() {
    img.removeEventListener('error', onErr);
    markRecord(rec, 'fallback', { loaded: true });
  };
  const onErr = function() {
    img.removeEventListener('load', onLoad);
    markRecord(rec, 'failed', {});
  };
  img.addEventListener('load', onLoad, { once: true });
  img.addEventListener('error', onErr, { once: true });
  setSrc(value);
}

// Paksa CORS pada img. Saat error: coba lagi dengan CORS (error jaringan sesaat), baru fallback.
function armCors(img, value, setSrc) {
  disarmCors(img);
  if (img.__mdRec) dropRecord(img); // elemen dipakai ulang oleh situs: catatan lama tidak berlaku
  img.crossOrigin = 'anonymous';
  img.__mdForced = true;
  img.__mdTries = 0;
  img.__mdUrl = String(value);
  img.__mdSetSrc = setSrc;
  hookInfo.forced++;

  const onError = function() {
    if (img.__mdOnError !== onError) return; // sudah digantikan (src diganti oleh situs)
    if (img.__mdTries < CORS_RETRIES) {
      img.__mdTries++;
      markRecord(ensureRecord(img), 'retrying', { tries: img.__mdTries, max: CORS_RETRIES, manual: false, bust: false });
      setTimeout(() => {
        if (img.__mdOnError === onError) setSrc(value);
      }, 250 * img.__mdTries);
      return;
    }
    fallbackLoad(img, value, setSrc);
  };

  img.__mdOnError = onError;
  img.addEventListener('error', onError);
  img.addEventListener('load', function() {
    if (!img.__mdForced) return; // load milik fallback (tanpa CORS) diurus fallbackLoad
    if (img.__mdOnError === onError) disarmCors(img);
    dropRecord(img);             // sukses dengan CORS: tidak perlu ditampilkan lagi
  }, { once: true });
}

// Retry manual (tombol di panel): 1) URL asli dengan CORS, 2) bypass cache. Jika tetap gagal: fallback.
function retryCorsRecord(rec) {
  const img = rec.img || (rec.ref && rec.ref.deref());
  const setSrc = img && img.__mdSetSrc;
  const base = img && img.__mdUrl;
  if (!img || !setSrc || !base) {
    markRecord(rec, 'lost', {});
    return;
  }

  disarmCors(img); // hentikan retry otomatis yang mungkin masih berjalan
  const run = (img.__mdRun = (img.__mdRun || 0) + 1);
  img.crossOrigin = 'anonymous';
  img.__mdForced = true;
  let step = 0;

  const attempt = function() {
    markRecord(rec, 'retrying', { tries: step + 1, max: 2, manual: true, bust: step === 1, loaded: false });
    const onLoad = function() {
      img.removeEventListener('error', onErr);
      if (img.__mdRun !== run) return;
      dropRecord(img); // berhasil dengan CORS
    };
    const onErr = function() {
      img.removeEventListener('load', onLoad);
      if (img.__mdRun !== run) return;
      if (step === 0) {
        step = 1;
        attempt();
        return;
      }
      fallbackLoad(img, base, setSrc);
    };
    img.addEventListener('load', onLoad, { once: true });
    img.addEventListener('error', onErr, { once: true });
    setSrc(step === 0 ? base : withCacheBust(base));
  };
  attempt();
}

function installCorsHook() {
  if (!FORCE_CORS_ON_IMAGES) return;
  try {
    const desc = Object.getOwnPropertyDescriptor(HTMLImageElement.prototype, 'src');
    if (!desc || !desc.set || !desc.get) return;

    Object.defineProperty(HTMLImageElement.prototype, 'src', {
      configurable: true,
      enumerable: desc.enumerable,
      get() { return desc.get.call(this); },
      set(value) {
        try {
          disarmCors(this);
          if (shouldForceCors(value) && (!this.hasAttribute('crossorigin') || this.__mdForced)) {
            armCors(this, value, (v) => desc.set.call(this, v));
          }
        } catch (e) { /* abaikan */ }
        desc.set.call(this, value);
      }
    });

    // Jalur kedua: situs yang memakai img.setAttribute('src', ...)
    const nativeSetAttr = Element.prototype.setAttribute;
    Element.prototype.setAttribute = function(name, value) {
      try {
        if (this instanceof HTMLImageElement && String(name).toLowerCase() === 'src') {
          disarmCors(this);
          if (shouldForceCors(value) && (!this.hasAttribute('crossorigin') || this.__mdForced)) {
            armCors(this, value, (v) => nativeSetAttr.call(this, 'src', v));
          }
        }
      } catch (e) { /* abaikan */ }
      return nativeSetAttr.call(this, name, value);
    };

    hookInfo.active = true;
  } catch (e) {
    hookInfo.active = false;
  }
}
installCorsHook();

// =====================================================================
// UTIL
// =====================================================================
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

function isInsideUI(el) {
  return !!uiContainer && uiContainer.contains(el);
}

// Gambar halaman berlabel: alt "page_N" atau class "xxxx_page"
function getPageNumber(el) {
  const m = (el.alt || '').match(/^page_(\d+)$/i);
  return m ? parseInt(m[1], 10) : null;
}

function isPageImg(el) {
  return /^page_\d+$/i.test(el.alt || '') || /_page\b/.test(el.className || '');
}

function getCanvasId(el) {
  let id = canvasIds.get(el);
  if (!id) {
    id = ++canvasIdCounter;
    canvasIds.set(el, id);
  }
  return id;
}

function sharesClass(a, b) {
  if (a.classList.length === 0) return true;
  for (let i = 0; i < a.classList.length; i++) {
    if (b.classList.contains(a.classList[i])) return true;
  }
  return false;
}

// Posisi elemen a di antara saudara sejenis (tag sama + minimal satu class sama).
// Placeholder kosong ikut dihitung, jadi nomor tetap stabil walau canvas dibuat/dibuang.
function slotPosition(a) {
  const parent = a.parentElement;
  if (!parent) return null;
  const kids = parent.children;
  let index = 0, total = 0;
  for (let i = 0; i < kids.length; i++) {
    const c = kids[i];
    if (c.tagName !== a.tagName || !sharesClass(a, c)) continue;
    total++;
    if (c === a) index = total;
  }
  return index > 0 ? { element: a, container: parent, index: index, total: total } : null;
}

// Naik dari elemen ke leluhur pertama yang punya cukup banyak saudara sejenis = "slot" halaman
function computeSlot(el, minSiblings) {
  let a = el;
  for (let depth = 0; a && a.parentElement && depth < 6; depth++) {
    const s = slotPosition(a);
    if (s && s.total >= minSiblings) return s;
    a = a.parentElement;
  }
  return null;
}

function newItem(type, num, el) {
  return {
    ready: false, type: type, num: num, seq: ++seqCounter,
    ref: new WeakRef(el), domIndex: 0, top: 0, left: 0,
    slot: null, slotCont: 0, slotRef: null
  };
}

function revokeItemUrls(item) {
  if (item.url) URL.revokeObjectURL(item.url);
  if (item.thumbUrl && item.thumbUrl !== item.url) URL.revokeObjectURL(item.thumbUrl);
}

// Reset total: bebaskan memori, naikkan "epoch" agar encode yang masih berjalan diabaikan
function clearAll() {
  epoch++;
  discoveredImagesMap.forEach(revokeItemUrls);
  discoveredImagesMap.clear();
  rejectedImgs.clear();
  canvasFp = new WeakMap();
  canvasTaint = new WeakMap();
  seqCounter = 0;
  slotInfo.cont = 0;
  slotInfo.total = 0;
  slotInfo.stable = false;
}

// =====================================================================
// PENGURUTAN
// =====================================================================
// Perbarui posisi elemen sumber tiap item (dipanggil hanya saat render/unduh)
function refreshItemMetrics() {
  const idx = new Map();
  document.querySelectorAll('img, canvas').forEach((el, i) => idx.set(el, i));
  const sx = window.scrollX, sy = window.scrollY;

  discoveredImagesMap.forEach((item) => {
    // Slot: pembungkus halaman (placeholder tetap ada walau canvas-nya dibuang situs)
    const slotEl = item.slotRef && item.slotRef.deref();
    const slotAlive = !!slotEl && slotEl.isConnected;
    if (slotAlive) {
      const s = slotPosition(slotEl);
      if (s) item.slot = s.index;
    }

    const el = item.ref && item.ref.deref();
    const elAlive = !!el && idx.has(el);
    if (elAlive) item.domIndex = idx.get(el);

    // Posisi: pakai elemen sumber; jika sudah dibuang, pakai slot-nya
    const posEl = elAlive ? el : (slotAlive ? slotEl : null);
    if (!posEl) return; // dua-duanya hilang: pakai data terakhir
    const r = posEl.getBoundingClientRect();
    if (r.width > 0 || r.height > 0) { // display:none menghasilkan rect 0, abaikan
      // Relatif terhadap kontainer slot (kontainer reader bergeser saat halaman dibalik)
      const base = slotAlive && slotEl.parentElement ? slotEl.parentElement.getBoundingClientRect() : null;
      item.top = base ? r.top - base.top : r.top + sy;
      item.left = base ? r.left - base.left : r.left + sx;
    }
  });
}

// Urutan DOM: pakai nomor slot (stabil) jika ada, jika tidak pakai indeks DOM
function domCompare(a, b) {
  if (a.slot !== null && b.slot !== null && a.slotCont === b.slotCont) return a.slot - b.slot;
  return a.domIndex - b.domIndex;
}

function compareItems(a, b) {
  // Nomor halaman eksplisit (alt "page_N") selalu menang
  if (a.num !== null && b.num !== null && a.num !== b.num) return a.num - b.num;

  let d = 0;
  switch (orderMode) {
    case 'found':
      d = a.seq - b.seq;
      break;
    case 'dom_rev':
      d = domCompare(b, a);
      break;
    case 'pos_rtl':
    case 'pos_ltr': {
      const dir = orderMode === 'pos_ltr' ? 1 : -1;
      d = Math.abs(a.top - b.top) > ROW_TOLERANCE ? a.top - b.top : dir * (a.left - b.left);
      if (d === 0) d = domCompare(a, b);
      break;
    }
    default: // 'dom'
      d = domCompare(a, b);
  }
  return d !== 0 ? d : a.seq - b.seq;
}

// Mengembalikan [[key, item], ...] yang sudah siap dan terurut
function getSortedReadyEntries() {
  refreshItemMetrics();
  const ready = [];
  discoveredImagesMap.forEach((item, key) => {
    if (item.ready) ready.push([key, item]);
  });
  ready.sort((a, b) => compareItems(a[1], b[1]));
  return ready;
}

// Nomor halaman yang ditampilkan di badge dan dipakai untuk nama file.
// Item dengan slot memakai nomor halaman asli (mis. 16-33 saat reload di tengah bab).
function displayNumber(item, rank) {
  if (item.num !== null) return item.num;
  if (item.slot !== null && slotInfo.total > 0 && item.slotCont === slotInfo.cont) {
    if (orderMode === 'dom') return item.slot;
    if (orderMode === 'dom_rev') return slotInfo.total - item.slot + 1;
  }
  return rank;
}

// Berapa slot halaman yang sudah tertangkap dan mana yang belum
function getCoverage() {
  if (!slotInfo.total) return null;
  const total = slotInfo.total;
  const have = new Set();
  discoveredImagesMap.forEach((it) => {
    if (it.ready && it.slot !== null && it.slotCont === slotInfo.cont) have.add(it.slot);
  });
  if (have.size === 0) return null;

  const missing = [];
  for (let sl = 1; sl <= total; sl++) {
    if (!have.has(sl)) missing.push(orderMode === 'dom_rev' ? total - sl + 1 : sl);
  }
  missing.sort((x, y) => x - y);

  // Ringkas jadi rentang, mis. 1-15, 34-40
  const ranges = [];
  for (let i = 0; i < missing.length;) {
    let j = i;
    while (j + 1 < missing.length && missing[j + 1] === missing[j] + 1) j++;
    ranges.push(i === j ? `${missing[i]}` : `${missing[i]}-${missing[j]}`);
    i = j + 1;
  }
  let text = ranges.slice(0, 6).join(', ');
  if (ranges.length > 6) text += ', ...';
  return { captured: have.size, total: total, missing: missing, text: text };
}

function renderCoverage() {
  if (!coverageEl) return;
  const cov = getCoverage();
  let text = '';
  let color = '#777';
  if (cov) {
    if (cov.missing.length === 0) {
      text = `Cakupan halaman: lengkap (${cov.captured}/${cov.total})`;
      color = '#2ed573';
    } else {
      text = `Cakupan halaman: ${cov.captured}/${cov.total} \u00b7 belum: ${cov.text}. Buka halaman tsb. di reader agar situs merendernya.`;
      color = '#f0b429';
    }
  }
  if (coverageEl.textContent !== text) coverageEl.textContent = text;
  coverageEl.style.color = color;
}

// =====================================================================
// UI
// =====================================================================
function buildUI() {
  const style = document.createElement('style');
  style.textContent = `
    #manga-downloader-ui {
        position: fixed; bottom: 20px; right: 20px; width: 340px;
        background: #11151c; color: #edf2f7; font-family: Inter, ui-sans-serif, system-ui, sans-serif;
        box-shadow: 0 18px 55px rgba(0,0,0,.55); border-radius: 14px;
        z-index: 2147483647; overflow: hidden; font-size: 13px; border: 1px solid #293342;
        display: none; flex-direction: column; max-height: 560px; backdrop-filter: blur(16px);
    }
    .mdui-header {
        background: linear-gradient(135deg,#1d2734,#151b24); padding: 13px 15px; font-weight: bold;
        display: flex; justify-content: space-between; align-items: center; border-bottom: 1px solid #293342;
    }
    .mdui-header-actions { display: flex; gap: 4px; }
    .mdui-brand { display:flex; align-items:center; gap:9px; }
    .mdui-brand small { margin-left:3px; color:#6cdbad; font-size:9px; letter-spacing:.12em; }
    .mdui-brand-mark { width:29px; height:29px; display:grid; place-items:center; color:#6cdbad; background:#1c3b34; border:1px solid #285748; border-radius:8px; }
    .mdui-brand-mark svg { width:19px; height:19px; }
    .mdui-icon-btn { cursor: pointer; width: 28px; height: 28px; display: grid; place-items: center; font-size: 16px; border-radius: 7px; user-select: none; color:#aab6c5; }
    .mdui-icon-btn:hover { background: #303b49; color:#fff; }
    .mdui-body { padding: 14px; display: flex; flex-direction: column; gap: 10px; }
    .mdui-row { display: flex; flex-direction: column; gap: 4px; }
    .mdui-label { font-size: 10px; color: #94a3b8; font-weight: bold; text-transform: uppercase; letter-spacing:.07em; }
    .mdui-status { font-size: 10px; color: #8190a3; line-height: 1.5; }
    .mdui-select { background:#1a222d; color:#e7edf5; border:1px solid #334153; padding:8px 9px; border-radius:7px; outline:none; }
    .mdui-select:focus { border-color:#58c99b; box-shadow:0 0 0 2px rgba(46,213,144,.14); }
    .mdui-input { background:#1a222d; color:#e7edf5; border:1px solid #334153; padding:8px 9px; border-radius:7px; outline:none; width:100%; box-sizing:border-box; }
    .mdui-input:focus { border-color:#58c99b; box-shadow:0 0 0 2px rgba(46,213,144,.14); }

    .mdui-controls-row { display: flex; gap: 6px; margin-top: 5px; }
    .mdui-btn {
        border: 1px solid transparent; padding: 10px 11px; border-radius: 8px; cursor: pointer;
        font-weight: bold; font-size: 11px; letter-spacing:.035em; display: flex; align-items: center; justify-content: center; gap: 7px;
        transition: transform .15s ease, background .15s ease;
    }
    .mdui-btn:hover { transform:translateY(-1px); }
    .mdui-btn-download { background: #20a875; color: #071b14; flex: 2; }
    .mdui-btn-download:hover { background: #35c58d; }
    .mdui-btn-download:disabled { background: #35433f; color:#91a39b; cursor: not-allowed; transform:none; }
    .mdui-btn-refresh { background: #202b39; border-color:#334153; color: #d8e2ee; flex: 1; }
    .mdui-btn-refresh:hover { background: #2b394b; }
    .mdui-btn svg { width:15px; height:15px; flex:none; }

    .mdui-gallery-container {
        border-top: 1px solid #293342; padding: 12px 14px 14px; background:#0e1218;
        overflow-y: auto; flex-grow: 1; display: flex; flex-direction: column; gap: 8px;
    }
    .mdui-gallery-grid {
        display: grid; grid-template-columns: repeat(3, 1fr); gap: 6px; margin-top: 5px;
    }
    .mdui-gallery-item {
        position: relative; border: 1px solid #293342; border-radius: 8px;
        background: #171e28; overflow: hidden; height: 104px; display: flex; align-items: center; justify-content: center;
        transition: border-color .15s ease, opacity .15s ease, transform .15s ease;
    }
    .mdui-gallery-item:hover { border-color:#58c99b; transform:translateY(-1px); }
    .mdui-gallery-item.mdui-unselected { opacity: .48; }
    .mdui-select-image {
        position: absolute; top: 4px; left: 4px; z-index: 1; margin: 0;
        width: 17px; height: 17px; accent-color: #29bd83; cursor: pointer; filter:drop-shadow(0 1px 2px rgba(0,0,0,.55));
    }
    .mdui-selection-actions { display: flex; align-items: center; justify-content: space-between; gap: 6px; }
    .mdui-gallery-img { max-width: 100%; max-height: 100%; object-fit: contain; }
    .mdui-img-badge {
        position: absolute; bottom: 4px; right: 4px; background: rgba(8,12,17,.82);
        color: #73e0b2; font-size: 9px; padding: 3px 5px; border-radius: 4px; font-weight: bold;
        border:1px solid rgba(255,255,255,.08); backdrop-filter:blur(5px);
    }
    .mdui-selection-actions { padding:7px 8px; background:#171e28; border:1px solid #293342; border-radius:7px; }
    .mdui-coverage-confirm { padding:10px; border:1px solid #735727; border-radius:8px; background:#302719; }
    .mdui-coverage-confirm[hidden] { display:none; }
    .mdui-coverage-confirm-text { color:#f5d28c; font-size:11px; line-height:1.5; }
    .mdui-coverage-confirm-actions { display:flex; justify-content:flex-end; gap:6px; margin-top:9px; }
    .mdui-small-btn.confirm-continue { background:#20a875; border-color:#20a875; color:#071b14; }
    .mdui-small-btn { border:1px solid #344254; border-radius:5px; padding:5px 7px; font-size:9px; font-weight:bold; cursor:pointer; color:#dbe6f2; background:#263345; }
    .mdui-small-btn:hover { background:#34465c; }
    .mdui-small-btn.alt { background:transparent; color:#aab6c5; }
    .mdui-small-btn.alt:hover { background:#26303d; }
    @media (max-width: 420px) { #manga-downloader-ui { width:calc(100vw - 24px); right:12px; bottom:12px; } }
  `;
  document.head.appendChild(style);

  const retryStyle = document.createElement('style');
  retryStyle.textContent = `
    .mdui-retry-section { margin-bottom: 8px; }
    .mdui-retry-head { display: flex; align-items: center; justify-content: space-between; gap: 6px; margin-bottom: 5px; }
    .mdui-head-btns { display: flex; gap: 4px; }
    .mdui-retry-item {
        position: relative; border: 1px solid #3a3a43; border-radius: 4px; background: #222; height: 100px;
        display: flex; flex-direction: column; align-items: center; justify-content: center;
        gap: 3px; padding: 4px; text-align: center; overflow: hidden;
    }
    .mdui-retry-item.mdui-st-retrying { border-color: #4b7bec; }
    .mdui-retry-item.mdui-st-fallback { border-color: #f0b429; }
    .mdui-retry-item.mdui-st-failed { border-color: #e55353; }
    .mdui-retry-item.mdui-st-lost { border-color: #666; }
    .mdui-spinner {
        width: 18px; height: 18px; border: 2px solid #4b7bec; border-top-color: transparent;
        border-radius: 50%; animation: mdui-spin 0.8s linear infinite;
    }
    @keyframes mdui-spin { to { transform: rotate(360deg); } }
    .mdui-retry-text { font-size: 10px; font-weight: bold; color: #ddd; line-height: 1.2; }
    .mdui-st-fallback .mdui-retry-text { color: #f0b429; }
    .mdui-st-failed .mdui-retry-text { color: #e55353; }
    .mdui-retry-name { font-size: 9px; color: #777; word-break: break-all; }
    .mdui-mini-btn { position: absolute; border: none; border-radius: 3px; font-size: 11px; cursor: pointer; color: #fff; padding: 1px 5px; }
    .mdui-mini-close { top: 2px; right: 2px; background: rgba(0,0,0,0.5); }
    .mdui-mini-retry { bottom: 2px; left: 2px; background: #4b7bec; }
  `;
  document.head.appendChild(retryStyle);

  uiContainer = document.createElement('div');
  uiContainer.id = 'manga-downloader-ui';
  uiContainer.innerHTML = `
    <div class="mdui-header">
        <span class="mdui-brand"><span class="mdui-brand-mark"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M5 4.8c2.6-.8 5-.4 7 1.2v13c-2-1.6-4.4-2-7-1.2z"/><path d="M19 4.8c-2.6-.8-5-.4-7 1.2v13c2-1.6 4.4-2 7-1.2z"/></svg></span><span>Manga Live Gallery <small>PRO</small></span></span>
        <span class="mdui-header-actions">
            <span class="mdui-icon-btn" id="mdui-min-btn" title="Ciutkan">\u2212</span>
            <span class="mdui-icon-btn" id="mdui-close-btn" title="Tutup (klik ikon ekstensi untuk membuka lagi)">\u2715</span>
        </span>
    </div>
    <div id="mdui-content" style="display: flex; flex-direction: column; overflow: hidden; flex-grow: 1;">
        <div class="mdui-body">
            <div class="mdui-row">
                <span class="mdui-label">Opsi Format Nama File</span>
                <select id="mdui-format" class="mdui-select">
                    <option value="domain_index">NamaWeb_page_1</option>
                    <option value="manga_page_index">manga_page_1</option>
                    <option value="custom">Nama kustom</option>
                </select>
            </div>
            <div class="mdui-row" id="mdui-custom-name-row" style="display:none;">
                <span class="mdui-label">Nama file kustom</span>
                <input id="mdui-custom-name" class="mdui-input" type="text" maxlength="80" placeholder="Contoh: One_Piece" autocomplete="off">
            </div>
            <div class="mdui-row">
                <span class="mdui-label">Urutan Halaman</span>
                <select id="mdui-order" class="mdui-select">
                    <option value="dom">Urutan di halaman (DOM)</option>
                    <option value="dom_rev">DOM terbalik</option>
                    <option value="pos_rtl">Posisi layar: kanan ke kiri</option>
                    <option value="pos_ltr">Posisi layar: kiri ke kanan</option>
                    <option value="found">Urutan ditemukan</option>
                </select>
            </div>
            <div class="mdui-controls-row">
                <button id="mdui-refresh-btn" class="mdui-btn mdui-btn-refresh"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 7v5h-5"/><path d="M19 12a7 7 0 1 1-2-5l3 5"/></svg><span>REFRESH</span></button>
                <button id="mdui-download-btn" class="mdui-btn mdui-btn-download"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M12 3v12"/><path d="m7 10 5 5 5-5"/><path d="M5 20h14"/></svg><span id="mdui-download-label">UNDUH (0) HALAMAN</span></button>
            </div>
            <div class="mdui-selection-actions">
                <span class="mdui-status" id="mdui-selection-count">Dipilih: 0/0</span>
                <span class="mdui-head-btns">
                    <button id="mdui-select-all" class="mdui-small-btn">Pilih semua</button>
                    <button id="mdui-select-none" class="mdui-small-btn alt">Kosongkan</button>
                </span>
            </div>
        </div>
        <div class="mdui-gallery-container">
            <span class="mdui-label" id="mdui-gallery-label">Gambar Terdeteksi di Layar (0):</span>
            <span class="mdui-status" id="mdui-status">Canvas: -</span>
            <span class="mdui-status" id="mdui-coverage"></span>
            <div id="mdui-coverage-confirm" class="mdui-coverage-confirm" role="alertdialog" aria-modal="false" aria-labelledby="mdui-coverage-confirm-text" hidden>
                <div id="mdui-coverage-confirm-text" class="mdui-coverage-confirm-text"></div>
                <div class="mdui-coverage-confirm-actions">
                    <button id="mdui-coverage-cancel" class="mdui-small-btn alt">Batal</button>
                    <button id="mdui-coverage-continue" class="mdui-small-btn confirm-continue">Lanjut unduh</button>
                </div>
            </div>
            <div id="mdui-retry-section" class="mdui-retry-section" style="display: none;">
                <div class="mdui-retry-head">
                    <span class="mdui-label" id="mdui-retry-label">Retry CORS (0)</span>
                    <span class="mdui-head-btns">
                        <button id="mdui-retry-all" class="mdui-small-btn" title="Retry semua gambar yang gagal">\u21bb Retry semua</button>
                        <button id="mdui-retry-clear" class="mdui-small-btn alt" title="Sembunyikan yang sudah tidak berjalan">\u2715 Bersihkan</button>
                    </span>
                </div>
                <div id="mdui-retry-grid" class="mdui-gallery-grid"></div>
            </div>
            <div id="mdui-gallery-grid" class="mdui-gallery-grid"></div>
        </div>
    </div>
  `;
  document.body.appendChild(uiContainer);

  gridEl = document.getElementById('mdui-gallery-grid');
  labelEl = document.getElementById('mdui-gallery-label');
  statusEl = document.getElementById('mdui-status');
  coverageEl = document.getElementById('mdui-coverage');
  retrySectionEl = document.getElementById('mdui-retry-section');
  retryGridEl = document.getElementById('mdui-retry-grid');
  retryLabelEl = document.getElementById('mdui-retry-label');
  retryAllBtn = document.getElementById('mdui-retry-all');
  document.getElementById('mdui-coverage-cancel').addEventListener('click', () => resolveCoverageConfirm(false));
  document.getElementById('mdui-coverage-continue').addEventListener('click', () => resolveCoverageConfirm(true));

  // Tombol per tile (retry / sembunyikan) lewat event delegation
  retryGridEl.addEventListener('click', (e) => {
    const btn = e.target.closest('[data-act]');
    if (!btn) return;
    const node = btn.closest('.mdui-retry-item');
    const rec = node ? corsTracker.get(Number(node.dataset.id)) : null;
    if (!rec) return;
    if (btn.dataset.act === 'retry') retryCorsRecord(rec);
    else if (btn.dataset.act === 'dismiss') dismissRecord(rec);
  });

  retryAllBtn.addEventListener('click', () => {
    Array.from(corsTracker.values()).forEach((rec) => {
      if (recordView(rec).canRetry) retryCorsRecord(rec);
    });
  });

  document.getElementById('mdui-retry-clear').addEventListener('click', () => {
    Array.from(corsTracker.values()).forEach((rec) => {
      if (rec.state !== 'retrying') dismissRecord(rec);
    });
    renderRetryTiles();
  });
  downloadBtnEl = document.getElementById('mdui-download-btn');
  minBtn = document.getElementById('mdui-min-btn');
  uiContent = document.getElementById('mdui-content');
  gridEl.addEventListener('change', (e) => {
    const checkbox = e.target.closest('.mdui-select-image');
    if (!checkbox) return;
    const node = checkbox.closest('.mdui-gallery-item');
    if (node && node._item) node._item.selected = checkbox.checked;
    updateGalleryUI();
  });
  document.getElementById('mdui-select-all').addEventListener('click', () => setGallerySelection(true));
  document.getElementById('mdui-select-none').addEventListener('click', () => setGallerySelection(false));

  const orderSelect = document.getElementById('mdui-order');
  const formatSelect = document.getElementById('mdui-format');
  const customNameRow = document.getElementById('mdui-custom-name-row');
  const updateCustomNameVisibility = () => {
    customNameRow.style.display = formatSelect.value === 'custom' ? 'flex' : 'none';
  };
  formatSelect.addEventListener('change', updateCustomNameVisibility);
  updateCustomNameVisibility();
  orderSelect.value = orderMode;
  orderSelect.addEventListener('change', () => {
    orderMode = orderSelect.value;
    try { localStorage.setItem('mdui-order', orderMode); } catch (e) { /* abaikan */ }
    updateGalleryUI();
  });

  minBtn.addEventListener('click', () => {
    if (uiContent.style.display === 'none') {
      uiContent.style.display = 'flex';
      minBtn.textContent = '\u2212';
    } else {
      resolveCoverageConfirm(false);
      uiContent.style.display = 'none';
      minBtn.textContent = '+';
    }
  });

  document.getElementById('mdui-close-btn').addEventListener('click', () => {
    setPanelVisible(false);
  });

  document.getElementById('mdui-refresh-btn').addEventListener('click', () => {
    scanPageElements(true);
  });

  downloadBtnEl.addEventListener('click', () => {
    downloadAllFromGalleryCache();
  });
}

// =====================================================================
// PANEL RETRY CORS
// =====================================================================
const retryNodes = new Map(); // id catatan -> node
let corsUiQueued = false;

function scheduleCorsUI() {
  if (!panelVisible || corsUiQueued) return;
  corsUiQueued = true;
  requestAnimationFrame(() => {
    corsUiQueued = false;
    renderRetryTiles();
  });
}

function dismissRecord(rec) {
  const img = rec.img || (rec.ref && rec.ref.deref());
  if (img) img.__mdRec = null; // kegagalan berikutnya membuat catatan baru
  corsTracker.delete(rec.id);
  renderRetryTiles();
}

// Tentukan tampilan sebuah catatan: status, teks, spinner, dan apakah bisa di-retry
function recordView(rec) {
  const img = rec.img || (rec.ref && rec.ref.deref());
  let state = rec.state;
  if (!img && state !== 'retrying') state = 'lost'; // objek gambar sudah dibuang situs
  let text = '';
  let spin = false;
  if (state === 'retrying') {
    spin = true;
    text = rec.manual
      ? `Retry manual ${rec.tries}/${rec.max}${rec.bust ? ' (bypass cache)' : ''}`
      : `CORS retry ${rec.tries}/${rec.max}`;
  } else if (state === 'fallback') {
    spin = !rec.loaded;
    text = rec.loaded ? 'Tanpa CORS (tainted)' : 'Memuat tanpa CORS...';
  } else if (state === 'failed') {
    text = 'Gagal dimuat';
  } else {
    text = 'Tidak bisa di-retry (muat ulang halaman)';
  }
  const canRetry = (state === 'fallback' && rec.loaded) || state === 'failed';
  return { state: state, text: text, spin: spin, canRetry: canRetry };
}

function setNodeText(el, text) {
  if (el.textContent !== text) el.textContent = text;
}

function createRetryNode(rec) {
  const node = document.createElement('div');
  node.className = 'mdui-retry-item';
  node.dataset.id = String(rec.id);
  node.innerHTML = `
    <button class="mdui-mini-btn mdui-mini-close" data-act="dismiss" title="Sembunyikan">\u2715</button>
    <div class="mdui-spinner"></div>
    <div class="mdui-retry-text"></div>
    <div class="mdui-retry-name"></div>
    <button class="mdui-mini-btn mdui-mini-retry" data-act="retry" title="Retry sekarang">\u21bb</button>
  `;
  return node;
}

function updateRetryNode(node, rec) {
  const v = recordView(rec);
  node.className = `mdui-retry-item mdui-st-${v.state}`;
  node.title = rec.url;
  node.querySelector('.mdui-spinner').style.display = v.spin ? 'block' : 'none';
  setNodeText(node.querySelector('.mdui-retry-text'), v.text);
  setNodeText(node.querySelector('.mdui-retry-name'), rec.name);
  node.querySelector('[data-act="retry"]').style.display = v.canRetry ? 'block' : 'none';
  return v;
}

function renderRetryTiles() {
  if (!retrySectionEl) return;

  // Hapus node yang catatannya sudah selesai (berhasil dimuat dengan CORS / disembunyikan)
  for (const [id, node] of retryNodes) {
    if (!corsTracker.has(id)) {
      node.remove();
      retryNodes.delete(id);
    }
  }

  let retryable = 0;
  corsTracker.forEach((rec) => {
    let node = retryNodes.get(rec.id);
    if (!node) {
      node = createRetryNode(rec);
      retryNodes.set(rec.id, node);
      retryGridEl.appendChild(node);
    }
    if (updateRetryNode(node, rec).canRetry) retryable++;
  });

  retrySectionEl.style.display = corsTracker.size > 0 ? 'block' : 'none';
  setNodeText(retryLabelEl, `Retry CORS (${corsTracker.size})`);
  retryAllBtn.style.display = retryable > 0 ? 'inline-block' : 'none';
}

// Tampilkan/sembunyikan panel. Data yang sudah terkumpul tetap tersimpan saat panel ditutup.
function setPanelVisible(visible) {
  if (!visible) resolveCoverageConfirm(false);
  panelVisible = visible;
  uiContainer.style.display = visible ? 'flex' : 'none';
  if (visible) {
    scanPageElements(false);
    updateGalleryUI();
    renderStatus();
    renderRetryTiles();
  }
}

function askCoverageConfirm(coverage, selectedCount) {
  const panel = document.getElementById('mdui-coverage-confirm');
  const message = document.getElementById('mdui-coverage-confirm-text');
  message.textContent = `Baru ${coverage.captured} dari ${coverage.total} halaman terdeteksi. Belum tertangkap: ${coverage.text}. Halaman yang belum ada baru dirender saat dibuka di reader. Lanjut unduh ${selectedCount} gambar yang dipilih?`;
  panel.hidden = false;
  panel.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  return new Promise((resolve) => { coverageConfirmResolve = resolve; });
}

function resolveCoverageConfirm(confirmed) {
  if (!coverageConfirmResolve) return;
  const resolve = coverageConfirmResolve;
  coverageConfirmResolve = null;
  const panel = document.getElementById('mdui-coverage-confirm');
  if (panel) panel.hidden = true;
  resolve(confirmed);
}

// Dipanggil oleh background.js saat ikon ekstensi diklik
function togglePanel() {
  if (!document.body) return;
  if (!started) {
    started = true;
    buildUI();
    startEngine();
    setPanelVisible(true);
    return;
  }
  setPanelVisible(!panelVisible);
}
window.__mduiToggle = togglePanel;

// =====================================================================
// FINGERPRINT CANVAS (murah)
// =====================================================================
let fpCanvas, fpCtx;
function initFingerprintCanvas() {
  fpCanvas = document.createElement('canvas');
  fpCanvas.width = FP_W;
  fpCanvas.height = FP_H;
  fpCtx = fpCanvas.getContext('2d', { willReadFrequently: true });
  fpCtx.imageSmoothingQuality = 'high';
}
initFingerprintCanvas();

// Mengembalikan { fp, blank }. blank = semua piksel sampel transparan (canvas belum digambar)
function fingerprint(el) {
  fpCtx.clearRect(0, 0, FP_W, FP_H);
  fpCtx.drawImage(el, 0, 0, FP_W, FP_H);
  const d = fpCtx.getImageData(0, 0, FP_W, FP_H).data;
  let h = 2166136261;
  let opaque = false;
  for (let i = 0; i < d.length; i += 4) {
    if (d[i + 3] !== 0) opaque = true;
    h = Math.imul(h ^ d[i], 16777619);
    h = Math.imul(h ^ d[i + 1], 16777619);
    h = Math.imul(h ^ d[i + 2], 16777619);
  }
  return { fp: `${el.width}x${el.height}:${h >>> 0}`, blank: !opaque };
}

// =====================================================================
// ENCODE ASYNC (toBlob jalan di luar main thread)
// =====================================================================
// cb(blob, thumbBlob) dipanggil setelah keduanya selesai
function encodeSource(source, srcW, srcH, cb) {
  const tw = THUMB_WIDTH;
  const th = Math.max(1, Math.round((srcH * THUMB_WIDTH) / srcW));
  const thumbCanvas = document.createElement('canvas');
  thumbCanvas.width = tw;
  thumbCanvas.height = th;
  thumbCanvas.getContext('2d').drawImage(source, 0, 0, tw, th);

  let blob = null, thumb = null, done = 0;
  const finish = () => { if (++done === 2) cb(blob, thumb); };

  source.toBlob((b) => { blob = b; finish(); }, 'image/webp', 0.95);
  thumbCanvas.toBlob((b) => { thumb = b; finish(); }, 'image/webp', 0.6);
}

function fillItem(item, blob, thumb) {
  item.blob = blob;
  item.url = URL.createObjectURL(blob);
  item.thumbUrl = thumb ? URL.createObjectURL(thumb) : item.url;
  item.ext = blob.type === 'image/png' ? 'png' : 'webp';
  item.ready = true;
}

// =====================================================================
// STATUS DIAGNOSTIK
// =====================================================================
function renderStatus() {
  if (!statusEl) return;
  let text = `Canvas: ${status.total} \u00b7 kosong ${status.blank} \u00b7 tainted ${status.tainted}`;
  const errNames = Object.keys(status.errors);
  if (errNames.length) text += ` [${errNames.map((n) => `${n}\u00d7${status.errors[n]}`).join(', ')}]`;
  if (canvasMode) text += ` \u00b7 mode halaman (${status.group})`;
  if (FORCE_CORS_ON_IMAGES) {
    if (!hookInfo.active) {
      text += ' \u00b7 hook CORS: gagal dipasang';
    } else if (hookInfo.lateStart) {
      text += ' \u00b7 hook CORS: terlambat (reload halaman)';
    } else {
      text += ` \u00b7 hook CORS: aktif (dipaksa ${hookInfo.forced}, fallback ${hookInfo.fallback})`;
      if (hookInfo.fallback > 0) text += ' \u00b7 fallback>0: sebagian gambar gagal dimuat dengan CORS (cek rules.json/cache)';
    }
  }
  if (statusEl.textContent !== text) statusEl.textContent = text;
  renderCoverage();
}

// =====================================================================
// PEMINDAI CANVAS
// =====================================================================
function scanCanvases() {
  const portrait = Array.from(document.querySelectorAll('canvas'))
    .filter((el) => !isInsideUI(el) && el.height > el.width);

  // Deteksi "mode halaman": banyak canvas portrait berukuran sama = halaman komik
  const sizeCount = new Map();
  portrait.forEach((el) => {
    if (el.width < 300) return;
    const k = `${el.width}x${el.height}`;
    sizeCount.set(k, (sizeCount.get(k) || 0) + 1);
  });
  let groupKey = null, groupMax = 0;
  sizeCount.forEach((count, k) => {
    if (count > groupMax) { groupMax = count; groupKey = k; }
  });
  if (groupMax < MIN_GROUP) groupKey = null;

  const groupSet = new Set();
  if (groupKey) {
    portrait.forEach((el) => {
      if (`${el.width}x${el.height}` === groupKey) groupSet.add(el);
    });
  }
  canvasMode = groupKey !== null;

  // Slot halaman: posisi canvas di antara elemen saudaranya, termasuk placeholder kosong.
  // Dengan begitu nomor halaman tetap benar walau situs hanya merender sebagian halaman
  // (mis. reload di tengah bab) dan canvas dibuat/dibuang saat pindah halaman.
  const slotOf = new Map();
  groupSet.forEach((el) => {
    const sl = computeSlot(el, Math.max(MIN_GROUP, groupSet.size));
    if (sl) slotOf.set(el, sl);
  });
  slotOf.forEach((sl) => {
    slotInfo.cont = getCanvasId(sl.container);
    slotInfo.total = sl.total;
    if (sl.total > groupSet.size) slotInfo.stable = true; // ada placeholder = halaman dirender sebagian
  });

  status.total = portrait.length;
  status.blank = 0;
  status.tainted = 0;
  status.group = groupSet.size;
  status.errors = {};
  const countError = (name) => { status.errors[name] = (status.errors[name] || 0) + 1; };

  portrait.forEach((el) => {
    // Canvas yang baru gagal dibaca: lewati sebentar, lalu coba lagi (taint bisa hilang
    // kalau situs menggambar ulang / mengatur ulang ukuran canvas)
    const t = canvasTaint.get(el);
    if (t && Date.now() - t.ts < TAINT_RETRY_MS) {
      status.tainted++;
      countError(t.name);
      return;
    }

    let res;
    try {
      res = fingerprint(el);
    } catch (err) {
      // SecurityError = tainted/CORS; InvalidStateError = mis. OffscreenCanvas.
      // fpCanvas ikut tercemar, jadi buat yang baru.
      initFingerprintCanvas();
      const name = (err && err.name) || 'Error';
      canvasTaint.set(el, { name: name, ts: Date.now() });
      status.tainted++;
      countError(name);
      return;
    }
    canvasTaint.delete(el);

    if (res.blank) status.blank++;
    const prev = canvasFp.get(el);
    if (prev === res.fp) return;      // isi tidak berubah
    canvasFp.set(el, res.fp);
    if (res.blank) return;            // belum digambar, tunggu polling berikutnya

    // Canvas halaman: satu slot per canvas. Canvas lain: dedupe berdasarkan isi.
    const inGroup = groupSet.has(el);
    const slot = inGroup ? (slotOf.get(el) || null) : null;
    const slotIdx = slot ? slot.index : null;
    const slotCont = slot ? getCanvasId(slot.container) : 0;
    const key = inGroup
      ? (slotInfo.stable && slot ? `cv:${getCanvasId(el)}:${slotIdx}` : `cv:${getCanvasId(el)}`)
      : `canvas_${res.fp}`;
    if (!inGroup && discoveredImagesMap.has(key)) return;

    const myEpoch = epoch;
    pending++;
    try {
      encodeSource(el, el.width, el.height, (blob, thumb) => {
        pending--;
        if (myEpoch !== epoch) return;
        if (!blob || blob.size < MIN_CANVAS_BYTES) return;

        const old = discoveredImagesMap.get(key);
        if (old && !inGroup) return;       // dedupe konten sama
        if (old) revokeItemUrls(old);      // canvas halaman yang digambar ulang: ganti

        if (inGroup) {
          // Jika isi yang sama sempat tercatat sebagai canvas "biasa" sebelum mode halaman terbentuk
          const genericKey = `canvas_${res.fp}`;
          const generic = discoveredImagesMap.get(genericKey);
          if (generic) {
            revokeItemUrls(generic);
            discoveredImagesMap.delete(genericKey);
          }
        }

        if (inGroup && slotInfo.stable && slot) {
          // Satu halaman = satu slot: buang item lama di slot yang sama (mis. canvas dibuat ulang)
          discoveredImagesMap.forEach((it, k) => {
            if (k !== key && it.slot === slotIdx && it.slotCont === slotCont) {
              revokeItemUrls(it);
              discoveredImagesMap.delete(k);
            }
          });
        }

        const item = newItem('CANVAS', null, el);
        if (slot) {
          item.slot = slotIdx;
          item.slotCont = slotCont;
          item.slotRef = new WeakRef(slot.element);
        }
        fillItem(item, blob, thumb);
        discoveredImagesMap.set(key, item);
        scheduleUIUpdate();
      });
    } catch (err) {
      pending--;
      // Gagal saat encode (mis. SecurityError dari toBlob): coba lagi nanti
      const name = (err && err.name) || 'Error';
      canvasTaint.set(el, { name: name, ts: Date.now() });
      canvasFp.delete(el);
    }
  });

  renderStatus();
}

// =====================================================================
// PEMINDAI IMG
// =====================================================================
function scanImages() {
  const allImgs = Array.from(document.querySelectorAll('img')).filter((el) => !isInsideUI(el));
  const pageImgs = allImgs.filter(isPageImg);
  const hasPageImgs = pageImgs.length > 0;

  // Di mode halaman canvas, gambar lain (iklan, banner, thumbnail rekomendasi) bukan halaman.
  // Sekaligus bersihkan yang sempat masuk sebelum mode halaman terbentuk.
  if (canvasMode && !hasPageImgs) {
    discoveredImagesMap.forEach((item, key) => {
      if (item.type === 'IMG' && item.num === null) {
        revokeItemUrls(item);
        discoveredImagesMap.delete(key);
      }
    });
    return;
  }

  const imgTargets = hasPageImgs ? pageImgs : allImgs;

  imgTargets.forEach((el) => {
    const src = el.currentSrc || el.src || el.getAttribute('src') || '';
    if (!src || src.startsWith('data:image') || src.includes('app_store') || src.includes('google_play') || src.includes('abj')) return;
    if (discoveredImagesMap.has(src) || rejectedImgs.has(src)) return;
    if (!el.complete || el.naturalWidth === 0) return;

    const isPortraitManga = hasPageImgs || (el.naturalHeight > el.naturalWidth) || (el.height > el.width) || /_page|chapter|manga|secure|blob/i.test(el.className + el.id + (el.alt || '') + src);
    if (!isPortraitManga) return;

    // Reservasi slot SEKARANG (sinkron) supaya dedupe tetap benar walau encode async
    const item = newItem('IMG', getPageNumber(el), el);
    discoveredImagesMap.set(src, item);

    const myEpoch = epoch;
    pending++;
    try {
      const tempCanvas = document.createElement('canvas');
      tempCanvas.width = el.naturalWidth;
      tempCanvas.height = el.naturalHeight;
      tempCanvas.getContext('2d').drawImage(el, 0, 0, tempCanvas.width, tempCanvas.height);

      encodeSource(tempCanvas, tempCanvas.width, tempCanvas.height, (blob, thumb) => {
        pending--;
        if (myEpoch !== epoch) return;
        if (discoveredImagesMap.get(src) !== item) return; // item sudah dibuang (mis. dibersihkan)
        if (!blob || blob.size < MIN_IMG_BYTES) {
          discoveredImagesMap.delete(src);
          rejectedImgs.add(src);
          return;
        }
        fillItem(item, blob, thumb);
        scheduleUIUpdate();
      });
    } catch (err) {
      // Error keamanan (CORS) - jangan dicoba lagi tiap scan
      pending--;
      if (myEpoch === epoch) {
        discoveredImagesMap.delete(src);
        rejectedImgs.add(src);
      }
    }
  });
}

// =====================================================================
// SCAN UTAMA
// =====================================================================
function scanPageElements(forceReset = false) {
  if (forceReset) clearAll();
  scanCanvases(); // canvas dulu: menentukan canvasMode yang dipakai scanImages
  scanImages();
  if (forceReset) updateGalleryUI();
}

// =====================================================================
// RENDER PREVIEW (inkremental)
// =====================================================================
const galleryNodes = new Map(); // key -> node
let uiUpdateQueued = false;

function scheduleUIUpdate() {
  if (!panelVisible || uiUpdateQueued) return; // saat panel tertutup, render ditunda sampai dibuka lagi
  uiUpdateQueued = true;
  requestAnimationFrame(updateGalleryUI);
}

function createGalleryNode(item) {
  const node = document.createElement('div');
  node.className = 'mdui-gallery-item';

  const img = document.createElement('img');
  img.className = 'mdui-gallery-img';
  img.decoding = 'async';
  img.src = item.thumbUrl; // thumbnail kecil, bukan gambar penuh

  const badge = document.createElement('div');
  badge.className = 'mdui-img-badge';

  const checkbox = document.createElement('input');
  checkbox.type = 'checkbox';
  checkbox.className = 'mdui-select-image';
  checkbox.checked = item.selected !== false;
  checkbox.setAttribute('aria-label', 'Pilih gambar untuk diunduh');

  node.appendChild(img);
  node.appendChild(badge);
  node.appendChild(checkbox);
  node._img = img;
  node._badge = badge;
  node._checkbox = checkbox;
  node._item = item;
  return node;
}

function updateGalleryUI() {
  uiUpdateQueued = false;

  // Hapus node yang itemnya sudah tidak ada / belum siap
  for (const [key, node] of galleryNodes) {
    const it = discoveredImagesMap.get(key);
    if (!it || !it.ready) {
      node.remove();
      galleryNodes.delete(key);
    }
  }

  const ready = getSortedReadyEntries();

  ready.forEach(([key, item], idx) => {
    let node = galleryNodes.get(key);
    if (!node) {
      node = createGalleryNode(item);
      galleryNodes.set(key, node);
      gridEl.appendChild(node);
    } else if (node._item !== item) {
      // key sama tapi item baru (setelah reset/refresh/canvas digambar ulang)
      node._item = item;
      node._img.src = item.thumbUrl;
      node._checkbox.checked = item.selected !== false;
    }
    node.style.order = idx; // urutan lewat CSS, tanpa memindah DOM
    node.classList.toggle('mdui-unselected', item.selected === false);
    const label = `${item.type} #${displayNumber(item, idx + 1)}`;
    if (node._badge.textContent !== label) node._badge.textContent = label;
  });

  labelEl.textContent = `Gambar Terdeteksi di Layar (${ready.length}):`;
  const selectedCount = ready.filter(([, item]) => item.selected !== false).length;
  document.getElementById('mdui-selection-count').textContent = `Dipilih: ${selectedCount}/${ready.length}`;
  renderCoverage();
  if (!isDownloading) setDownloadLabel(`UNDUH (${selectedCount}) HALAMAN`);
}

function setDownloadLabel(text) {
  const label = document.getElementById('mdui-download-label');
  if (label) label.textContent = text;
}

function setGallerySelection(selected) {
  discoveredImagesMap.forEach((item) => { if (item.ready) item.selected = selected; });
  updateGalleryUI();
}

// =====================================================================
// UNDUH: Blob URL + jeda antar file
// =====================================================================
async function downloadAllFromGalleryCache() {
  if (isDownloading) return;
  isDownloading = true;
  downloadBtnEl.disabled = true;

  // Tunggu proses encode yang masih berjalan (maks 5 detik)
  for (let waited = 0; pending > 0 && waited < 5000; waited += 100) await sleep(100);

  const list = getSortedReadyEntries().map((entry) => entry[1]).filter((item) => item.selected !== false);

  if (list.length === 0) {
    downloadBtnEl.disabled = false;
    isDownloading = false;
    updateGalleryUI();
    return;
  }

  const cov = getCoverage();
  if (cov && cov.missing.length > 0) {
    const ok = await askCoverageConfirm(cov, list.length);
    if (!ok) {
      downloadBtnEl.disabled = false;
      isDownloading = false;
      updateGalleryUI();
      return;
    }
  }

  const nameFormat = document.getElementById('mdui-format').value;
  const domain = window.location.hostname.replace('www.', '');
  const customName = document.getElementById('mdui-custom-name').value
    .replace(/[<>:"/\\|?*\x00-\x1F]/g, '_').replace(/[. ]+$/g, '').trim();
  const baseName = nameFormat === 'domain_index'
    ? `${domain}_page`
    : nameFormat === 'custom'
      ? `${customName || 'manga'}_page`
      : 'manga_page';

  console.log(`Memulai pengunduhan ${list.length} file dari memori pratinjau...`);

  const usedNames = new Set();
  for (let i = 0; i < list.length; i++) {
    const item = list[i];
    const pageNo = displayNumber(item, i + 1); // sama dengan nomor di badge preview

    let name = `${baseName}_${pageNo}`;
    for (let n = 2; usedNames.has(name); n++) name = `${baseName}_${pageNo}-${n}`; // cegah nama kembar
    usedNames.add(name);

    const a = document.createElement('a');
    a.href = item.url;
    a.download = `${name}.${item.ext}`;
    uiContainer.appendChild(a); // di dalam panel agar tidak memicu observer halaman
    a.click();
    uiContainer.removeChild(a);

    setDownloadLabel(`${i + 1}/${list.length}`);
    await sleep(DOWNLOAD_DELAY_MS);
  }

  // Bersihkan memori setelah selesai agar tidak bertumpuk di bab berikutnya
  clearAll();
  downloadBtnEl.disabled = false;
  isDownloading = false;
  updateGalleryUI();
}

// =====================================================================
// PENJADWALAN SCAN
// =====================================================================
let scanScheduled = false;
function scheduleScan() {
  if (scanScheduled) return;
  scanScheduled = true;
  setTimeout(() => {
    const run = () => {
      scanScheduled = false;
      if (!document.hidden) scanPageElements(false);
    };
    if ('requestIdleCallback' in window) requestIdleCallback(run, { timeout: 1000 });
    else run();
  }, SCAN_INTERVAL_MS);
}

// Menggambar ke canvas TIDAK memicu mutasi DOM, jadi polling murah (fingerprint) mengisi celah itu.
// Cepat selama masih ada canvas kosong, lambat kalau semua sudah terisi.
function pollLoop() {
  if (!document.hidden && !isDownloading) scanCanvases();
  setTimeout(pollLoop, status.blank > 0 ? POLL_FAST_MS : POLL_SLOW_MS);
}

function startEngine() {
  // Mutasi di dalam panel UI sendiri diabaikan; berhenti begitu ketemu satu mutasi dari luar.
  const observer = new MutationObserver((mutations) => {
    for (let i = 0; i < mutations.length; i++) {
      if (!uiContainer.contains(mutations[i].target)) {
        scheduleScan();
        return;
      }
    }
  });
  observer.observe(document.body, {
    childList: true,
    subtree: true,
    attributes: true,
    attributeFilter: ['src', 'class', 'style']
  });

  // Scan saat gambar selesai dimuat (event load tidak bubble, jadi pakai capture)
  document.addEventListener('load', (e) => {
    if (e.target && e.target.tagName === 'IMG' && !isInsideUI(e.target)) scheduleScan();
  }, true);
  document.addEventListener('visibilitychange', () => {
    if (!document.hidden) scheduleScan();
  });

  scheduleScan();
  setTimeout(pollLoop, POLL_FAST_MS);
}
