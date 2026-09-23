import { firebaseConfig } from './firebase-config.js';
import { initializeApp } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js';
import {
  getAuth, onAuthStateChanged, signInWithEmailAndPassword, createUserWithEmailAndPassword,
  signOut, sendPasswordResetEmail, updateProfile
} from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js';
import {
  getFirestore, doc, getDoc, setDoc, updateDoc, addDoc, deleteDoc, collection,
  query, where, orderBy, limit, onSnapshot
} from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js';

const $ = id => document.getElementById(id);
const show = (el, on) => { el.hidden = !on; };

if (!firebaseConfig.apiKey) {
  show($('setupView'), true);
  throw new Error('Firebase not configured');
}

const app = initializeApp(firebaseConfig);
const auth = getAuth(app);
const db = getFirestore(app);

// ---------- State ----------
let me = null;          // { uid, name, email, role }
let users = [];         // admin: all users; member: just me
let shifts = [];        // shifts visible to me
let unsubs = [];
let tab = 'clock';
let map = null, mapLayer = null;

// ---------- Helpers ----------
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;' }[c]));
const isAdmin = () => me?.role === 'admin';
const sameDay = (ts, d = new Date()) => new Date(ts).toDateString() === d.toDateString();
const breakMs = (s, now = Date.now()) => (s.breaks || []).reduce((t, b) => t + ((b.end || now) - b.start), 0);
const workedMs = (s, now = Date.now()) => Math.max(0, (s.end || now) - s.start - breakMs(s, now));
const onBreak = s => (s.breaks || []).some(b => !b.end);
const fmtDur = ms => { const m = Math.floor(ms / 60000); return `${Math.floor(m / 60)}h ${String(m % 60).padStart(2, '0')}m`; };
const fmtClock = ms => { const s = Math.floor(ms / 1000); return `${Math.floor(s / 3600)}:${String(Math.floor(s / 60) % 60).padStart(2, '0')}:${String(s % 60).padStart(2, '0')}`; };
const fmtTime = ts => ts ? new Date(ts).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' }) : '…';
const fmtDate = ts => new Date(ts).toLocaleDateString();
const nameOf = uid => users.find(u => u.id === uid)?.name || shifts.find(s => s.uid === uid)?.name || 'Unknown';
const openShiftOf = uid => shifts.find(s => s.uid === uid && !s.end);
const statusOf = uid => { const s = openShiftOf(uid); return !s ? 'out' : onBreak(s) ? 'brk' : 'in'; };
const STATUS = { in: 'Working', out: 'Clocked out', brk: 'On break' };
const mapsLink = l => l ? `<a href="https://www.google.com/maps?q=${l.lat},${l.lng}" target="_blank" rel="noopener">${l.lat.toFixed(4)}, ${l.lng.toFixed(4)}</a>` : '<span class="muted">none</span>';

function getLocation() {
  return new Promise(resolve => {
    if (!navigator.geolocation) return resolve(null);
    navigator.geolocation.getCurrentPosition(
      p => resolve({ lat: p.coords.latitude, lng: p.coords.longitude, acc: Math.round(p.coords.accuracy) }),
      () => resolve(null),
      { enableHighAccuracy: true, timeout: 12000, maximumAge: 30000 }
    );
  });
}

// ---------- Auth UI ----------
let signingUp = false;
function setAuthMode(up) {
  signingUp = up;
  show($('authName'), up);
  $('authName').required = up;
  $('authTitle').textContent = up ? 'Create your account' : 'Sign in to clock in';
  $('authSubmit').textContent = up ? 'Create account' : 'Sign in';
  $('authToggle').textContent = up ? 'I already have an account' : 'Create an account';
  $('authPass').autocomplete = up ? 'new-password' : 'current-password';
  $('authErr').textContent = '';
}
$('togglePass').onclick = () => {
  const input = $('authPass'), btn = $('togglePass');
  const showing = input.type === 'text';
  input.type = showing ? 'password' : 'text';
  btn.classList.toggle('on', !showing);
  btn.textContent = showing ? '👁' : '🙈';
  btn.title = btn.ariaLabel = showing ? 'Show password' : 'Hide password';
  input.focus();
};
$('authToggle').onclick = () => setAuthMode(!signingUp);
$('authReset').onclick = async () => {
  const email = $('authEmail').value.trim();
  if (!email) { $('authErr').textContent = 'Type your email first.'; return; }
  try { await sendPasswordResetEmail(auth, email); $('authErr').textContent = 'Reset email sent.'; }
  catch (e) { $('authErr').textContent = niceError(e); }
};
$('authForm').onsubmit = async e => {
  e.preventDefault();
  const email = $('authEmail').value.trim(), pass = $('authPass').value, name = $('authName').value.trim();
  $('authSubmit').disabled = true; $('authErr').textContent = '';
  try {
    if (signingUp) {
      const cred = await createUserWithEmailAndPassword(auth, email, pass);
      await updateProfile(cred.user, { displayName: name });
      await setDoc(doc(db, 'users', cred.user.uid), { name, email, role: 'member', createdAt: Date.now() });
    } else {
      await signInWithEmailAndPassword(auth, email, pass);
    }
  } catch (err) { $('authErr').textContent = niceError(err); }
  $('authSubmit').disabled = false;
};
$('signOut').onclick = () => signOut(auth);

function niceError(e) {
  const c = e.code || '';
  if (c.includes('invalid-credential') || c.includes('wrong-password') || c.includes('user-not-found')) return 'Wrong email or password.';
  if (c.includes('email-already-in-use')) return 'That email already has an account.';
  if (c.includes('weak-password')) return 'Password needs at least 6 characters.';
  if (c.includes('invalid-email')) return 'That email looks wrong.';
  if (c.includes('permission-denied')) return 'You don\'t have permission to do that.';
  return e.message || 'Something went wrong.';
}

onAuthStateChanged(auth, async user => {
  unsubs.forEach(u => u()); unsubs = [];
  users = []; shifts = [];
  if (!user) {
    me = null;
    show($('appView'), false); show($('authView'), true); setAuthMode(false);
    return;
  }
  // Load (or create) my profile
  const ref = doc(db, 'users', user.uid);
  let snap = await getDoc(ref);
  if (!snap.exists()) {
    await setDoc(ref, { name: user.displayName || user.email.split('@')[0], email: user.email, role: 'member', createdAt: Date.now() });
    snap = await getDoc(ref);
  }
  show($('authView'), false); show($('appView'), true);
  unsubs.push(onSnapshot(ref, s => {
    const wasAdmin = isAdmin();
    me = { uid: user.uid, id: user.uid, ...s.data() };
    $('meName').textContent = me.name;
    show($('meRole'), isAdmin());
    document.querySelectorAll('[data-admin]').forEach(el => show(el, isAdmin()));
    if (wasAdmin !== isAdmin() || !unsubs.dataReady) subscribeData();
    if (!isAdmin() && (tab === 'team' || tab === 'map')) setTab('clock');
    render();
  }));
});

let dataUnsubs = [];
function subscribeData() {
  dataUnsubs.forEach(u => u()); dataUnsubs = [];
  unsubs.dataReady = true;
  if (isAdmin()) {
    dataUnsubs.push(onSnapshot(collection(db, 'users'), s => { users = s.docs.map(d => ({ id: d.id, ...d.data() })); render(); }));
    dataUnsubs.push(onSnapshot(query(collection(db, 'shifts'), orderBy('start', 'desc'), limit(2000)),
      s => { shifts = s.docs.map(d => ({ id: d.id, ...d.data() })); render(); }, err => console.error(err)));
  } else {
    users = [me];
    dataUnsubs.push(onSnapshot(query(collection(db, 'shifts'), where('uid', '==', me.uid)),
      s => { shifts = s.docs.map(d => ({ id: d.id, ...d.data() })).sort((a, b) => b.start - a.start); render(); }, err => console.error(err)));
  }
  unsubs.push(() => dataUnsubs.forEach(u => u()));
}

// ---------- Clock actions ----------
let busy = false;
async function act(kind) {
  if (busy) return; busy = true; renderClock();
  $('geoNote').textContent = 'Getting your location…';
  try {
    const open = openShiftOf(me.uid);
    if (kind === 'in') {
      const loc = await getLocation();
      await addDoc(collection(db, 'shifts'), { uid: me.uid, name: me.name, start: Date.now(), end: null, breaks: [], inLoc: loc, outLoc: null });
      $('geoNote').textContent = loc ? `Location saved (±${loc.acc} m)` : 'Clocked in without location (permission denied or unavailable).';
    } else if (kind === 'out' && open) {
      const loc = await getLocation();
      const now = Date.now();
      const breaks = (open.breaks || []).map(b => b.end ? b : { ...b, end: now });
      await updateDoc(doc(db, 'shifts', open.id), { end: now, breaks, outLoc: loc });
      $('geoNote').textContent = loc ? `Location saved (±${loc.acc} m)` : 'Clocked out without location.';
    } else if (kind === 'break' && open) {
      const now = Date.now();
      const breaks = [...(open.breaks || [])];
      const i = breaks.findIndex(b => !b.end);
      if (i >= 0) breaks[i] = { ...breaks[i], end: now }; else breaks.push({ start: now, end: null });
      await updateDoc(doc(db, 'shifts', open.id), { breaks });
      $('geoNote').textContent = '';
    }
  } catch (e) { $('geoNote').textContent = niceError(e); }
  busy = false; renderClock();
}

// ---------- Rendering ----------
function renderClock() {
  if (!me) return;
  const st = statusOf(me.uid);
  const badge = $('myStatus');
  badge.className = 'badge s-' + st; badge.textContent = STATUS[st];
  const today = shifts.filter(s => s.uid === me.uid && sameDay(s.start)).reduce((t, s) => t + workedMs(s), 0);
  $('myToday').textContent = fmtClock(today);
  const box = $('myActions');
  const want = st === 'out' ? 'out' : st;
  if (box.dataset.state !== want + busy) {
    box.dataset.state = want + busy;
    box.innerHTML = st === 'out'
      ? `<button class="b-in" data-act="in" ${busy ? 'disabled' : ''}>Clock in</button>`
      : `<button class="b-brk" data-act="break" ${busy ? 'disabled' : ''}>${st === 'brk' ? 'End break' : 'Start break'}</button>
         <button class="b-out" data-act="out" ${busy ? 'disabled' : ''}>Clock out</button>`;
  }
}
$('myActions').onclick = e => { const b = e.target.closest('[data-act]'); if (b) act(b.dataset.act); };

function filtered() {
  const pid = isAdmin() ? $('fPerson').value : me.uid;
  const from = $('fFrom').value ? new Date($('fFrom').value + 'T00:00').getTime() : -Infinity;
  const to = $('fTo').value ? new Date($('fTo').value + 'T23:59:59.999').getTime() : Infinity;
  return shifts.filter(s => (!pid || s.uid === pid) && s.start >= from && s.start <= to);
}

function renderSheet() {
  const sel = $('fPerson'), cur = sel.value;
  sel.innerHTML = '<option value="">Everyone</option>' +
    [...users].sort((a, b) => (a.name || '').localeCompare(b.name || '')).map(u => `<option value="${u.id}">${esc(u.name)}</option>`).join('');
  sel.value = users.some(u => u.id === cur) ? cur : '';

  const rows = filtered();
  $('sCount').textContent = rows.length;
  $('sTotal').textContent = fmtDur(rows.reduce((t, s) => t + workedMs(s), 0));
  $('sBreaks').textContent = fmtDur(rows.reduce((t, s) => t + breakMs(s), 0));
  show($('sheetEmpty'), !rows.length);
  $('sheet').innerHTML = rows.map(s => `<tr>
    <td>${esc(nameOf(s.uid))}</td><td>${fmtDate(s.start)}</td>
    <td>${fmtTime(s.start)}</td><td>${fmtTime(s.end)}</td>
    <td>${fmtDur(breakMs(s))}</td><td><b>${fmtDur(workedMs(s))}</b></td>
    <td>${mapsLink(s.inLoc)}</td>
    ${isAdmin() ? `<td><button class="b-ghost b-sm" data-del="${s.id}">Delete</button></td>` : ''}
  </tr>`).join('');
}
$('sheet').onclick = async e => {
  const b = e.target.closest('[data-del]'); if (!b) return;
  if (confirm('Delete this shift? This can\'t be undone.')) {
    try { await deleteDoc(doc(db, 'shifts', b.dataset.del)); } catch (err) { alert(niceError(err)); }
  }
};
['fPerson', 'fFrom', 'fTo'].forEach(id => $(id).addEventListener('change', () => { renderSheet(); renderMap(); }));

$('exportCsv').onclick = () => {
  const loc = l => l ? `${l.lat},${l.lng}` : '';
  const lines = [['Member', 'Date', 'Clock in', 'Clock out', 'Break minutes', 'Worked minutes', 'In location', 'Out location']]
    .concat(filtered().map(s => [nameOf(s.uid), fmtDate(s.start), fmtTime(s.start), s.end ? fmtTime(s.end) : '',
      Math.round(breakMs(s) / 60000), Math.round(workedMs(s) / 60000), loc(s.inLoc), loc(s.outLoc)]));
  const csv = lines.map(r => r.map(v => `"${String(v).replace(/"/g, '""')}"`).join(',')).join('\n');
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([csv], { type: 'text/csv' }));
  a.download = 'zurmelibble-timesheet.csv'; a.click();
};

function renderTeam() {
  if (!isAdmin()) return;
  const st = users.map(u => statusOf(u.id));
  $('tMembers').textContent = users.length;
  $('tIn').textContent = st.filter(s => s === 'in').length;
  $('tBrk').textContent = st.filter(s => s === 'brk').length;
  $('tHours').textContent = fmtDur(shifts.filter(s => sameDay(s.start)).reduce((t, s) => t + workedMs(s), 0));
  const order = { in: 0, brk: 1, out: 2 };
  $('team').innerHTML = [...users].sort((a, b) => order[statusOf(a.id)] - order[statusOf(b.id)] || (a.name || '').localeCompare(b.name || '')).map(u => {
    const s = statusOf(u.id), open = openShiftOf(u.id);
    const today = shifts.filter(x => x.uid === u.id && sameDay(x.start)).reduce((t, x) => t + workedMs(x), 0);
    const admin = u.role === 'admin';
    return `<tr>
      <td><b>${esc(u.name)}</b><br><span class="muted">${esc(u.email)}</span></td>
      <td><span class="badge s-${s}">${STATUS[s]}</span></td>
      <td>${open ? fmtTime(open.start) : ''}</td>
      <td>${fmtDur(today)}</td>
      <td>${admin ? '<span class="badge s-admin">Admin</span>' : '<span class="muted">Member</span>'}</td>
      <td>${u.id === me.uid ? '' : `<button class="b-ghost b-sm" data-role="${u.id}" data-to="${admin ? 'member' : 'admin'}">${admin ? 'Remove admin' : 'Make admin'}</button>`}</td>
    </tr>`;
  }).join('');
}
$('team').onclick = async e => {
  const b = e.target.closest('[data-role]'); if (!b) return;
  const u = users.find(x => x.id === b.dataset.role);
  const msg = b.dataset.to === 'admin' ? `Make ${u.name} an admin? They'll see everyone's time and locations.` : `Remove admin from ${u.name}?`;
  if (!confirm(msg)) return;
  try { await updateDoc(doc(db, 'users', u.id), { role: b.dataset.to }); } catch (err) { alert(niceError(err)); }
};

function renderMap() {
  if (tab !== 'map' || !isAdmin() || !window.L) return;
  if (!map) {
    map = L.map('map').setView([-15.8, -47.9], 4);
    L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', { maxZoom: 19, attribution: '&copy; OpenStreetMap' }).addTo(map);
    mapLayer = L.layerGroup().addTo(map);
  }
  setTimeout(() => map.invalidateSize(), 0);
  mapLayer.clearLayers();
  const pts = [];
  const css = getComputedStyle(document.documentElement);
  const add = (loc, color, label) => {
    if (!loc) return;
    pts.push([loc.lat, loc.lng]);
    L.circleMarker([loc.lat, loc.lng], { radius: 8, color, fillColor: color, fillOpacity: .8, weight: 2 })
      .bindPopup(label).addTo(mapLayer);
  };
  filtered().forEach(s => {
    const n = esc(nameOf(s.uid));
    add(s.inLoc, css.getPropertyValue('--in').trim(), `<b>${n}</b><br>Clock in ${fmtDate(s.start)} ${fmtTime(s.start)}<br>±${s.inLoc?.acc} m`);
    add(s.outLoc, css.getPropertyValue('--out').trim(), `<b>${n}</b><br>Clock out ${fmtDate(s.end || s.start)} ${fmtTime(s.end)}<br>±${s.outLoc?.acc} m`);
  });
  if (pts.length) map.fitBounds(pts, { padding: [30, 30], maxZoom: 16 });
}

function render() {
  if (!me) return;
  renderClock(); renderSheet(); renderTeam(); renderMap();
}

// ---------- Tabs ----------
function setTab(t) {
  tab = t;
  document.querySelectorAll('nav [data-tab]').forEach(b => b.classList.toggle('active', b.dataset.tab === t));
  document.querySelectorAll('[data-view]').forEach(v => show(v, v.dataset.view === t));
  renderMap();
}
document.querySelector('nav').onclick = e => { const b = e.target.closest('[data-tab]'); if (b) setTab(b.dataset.tab); };

// Live timers
setInterval(renderClock, 1000);
setInterval(() => { renderTeam(); if (tab === 'sheet') renderSheet(); }, 30000);
