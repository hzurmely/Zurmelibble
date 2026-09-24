import { firebaseConfig } from './firebase-config.js';
import { initializeApp } from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js';
import {
  getAuth, onAuthStateChanged, signInWithEmailAndPassword, createUserWithEmailAndPassword,
  signOut, sendPasswordResetEmail, updateProfile, connectAuthEmulator
} from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js';
import {
  getFirestore, doc, getDoc, setDoc, updateDoc, addDoc, deleteDoc, collection,
  query, where, orderBy, limit, onSnapshot, writeBatch, connectFirestoreEmulator, getCountFromServer
} from 'https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js';

const $ = id => document.getElementById(id);
const show = (el, on) => { if (el) el.hidden = !on; };

if (!firebaseConfig.apiKey) {
  show($('setupView'), true);
  throw new Error('Firebase not configured');
}

const app = initializeApp(firebaseConfig);
const auth = getAuth(app);
const db = getFirestore(app);
// Local testing against the Firebase emulator: add ?emulator to the URL.
if (new URLSearchParams(location.search).has('emulator')) {
  connectAuthEmulator(auth, 'http://127.0.0.1:9099', { disableWarnings: true });
  connectFirestoreEmulator(db, '127.0.0.1', 8080);
}

// ---------- State ----------
let user = null;          // Firebase auth user
let profile = null;       // users/{uid}
let memberships = [];     // users/{uid}/memberships
let orgId = null;         // current organisation id
let org = null;           // orgs/{orgId}
let myMember = null;      // orgs/{orgId}/members/{uid}
let members = [];         // members visible to me
let teams = [];           // teams in the org
let shifts = [];          // shifts visible to me
let userUnsubs = [], orgUnsubs = [], dataUnsubs = [];
let dataKey = '';
let tab = 'home';
let directory = [], lists = [], cards = [];
let boardTeam = '', boardMine = false, boardSearch = '', dragging = false, boardSortables = [];
try { boardTeam = localStorage.getItem('zb-board') || ''; } catch (e) {}
let onboarding = false;   // user chose "create or join another"
let map = null, mapLayer = null;
const pendingJoin = (new URLSearchParams(location.search).get('join') || '').toUpperCase();

// ---------- Helpers ----------
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const role = () => myMember?.role || null;
const isAdmin = () => ['owner', 'admin'].includes(role());
const isManager = () => role() === 'manager';
const isStaff = () => isAdmin() || isManager();
// Zurmelibble platform owner (approves new organisations). Enforced in firestore.rules too.
const SUPER_UID = 'dreUCmV8iBcaauMuOVHIv4IlxqG3';
const isSuper = () => user?.uid === SUPER_UID;
const orgStatus = o => o?.status || 'approved';
let allOrgs = [], orgCounts = {}, ownerInfo = {}, platformFilter = 'pending';
// The owner sees "Zurmelibble" in the organisation switcher; picking it opens the platform panel.
let platformMode = false;
try { platformMode = localStorage.getItem('zb-platform') === '1'; } catch (e) {}
function setPlatformMode(on) { platformMode = on; try { on ? localStorage.setItem('zb-platform', '1') : localStorage.removeItem('zb-platform'); } catch (e) {} }
const isActive = () => ['owner', 'admin', 'manager', 'member'].includes(role());
const ROLE_LABEL = { owner: 'Owner', admin: 'Admin', manager: 'Manager', member: 'Member', pending: 'Pending' };
const sameDay = (ts, d = new Date()) => new Date(ts).toDateString() === d.toDateString();
const breakMs = (s, now = Date.now()) => (s.breaks || []).reduce((t, b) => t + ((b.end || now) - b.start), 0);
const workedMs = (s, now = Date.now()) => Math.max(0, (s.end || now) - s.start - breakMs(s, now));
const onBreak = s => (s.breaks || []).some(b => !b.end);
const fmtDur = ms => { const m = Math.floor(ms / 60000); return `${Math.floor(m / 60)}h ${String(m % 60).padStart(2, '0')}m`; };
const fmtClock = ms => { const s = Math.floor(ms / 1000); return `${Math.floor(s / 3600)}:${String(Math.floor(s / 60) % 60).padStart(2, '0')}:${String(s % 60).padStart(2, '0')}`; };
const fmtTime = ts => ts ? new Date(ts).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' }) : '…';
const fmtDate = ts => new Date(ts).toLocaleDateString();
const nameOf = uid => members.find(u => u.uid === uid)?.name || shifts.find(s => s.uid === uid)?.name || 'Unknown';
const teamName = id => id ? (teams.find(t => t.id === id)?.name || 'Deleted team') : 'No team';
const openShiftOf = uid => shifts.find(s => s.uid === uid && !s.end);
const statusOf = uid => { const s = openShiftOf(uid); return !s ? 'out' : onBreak(s) ? 'brk' : 'in'; };
const STATUS = { in: 'Working', out: 'Clocked out', brk: 'On break' };
const todayMs = uid => shifts.filter(s => s.uid === uid && sameDay(s.start)).reduce((t, s) => t + workedMs(s), 0);
const mapsLink = l => l ? `<a href="https://www.google.com/maps?q=${l.lat},${l.lng}" target="_blank" rel="noopener">${l.lat.toFixed(4)}, ${l.lng.toFixed(4)}</a>` : '<span class="muted">none</span>';
const activeMembers = () => members.filter(m => m.role !== 'pending');
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const newCode = () => Array.from(crypto.getRandomValues(new Uint32Array(6)), n => CODE_CHARS[n % CODE_CHARS.length]).join('');
const cleanCode = s => s.toUpperCase().replace(/[^A-Z0-9]/g, '');
const orgRef = (...p) => doc(db, 'orgs', orgId, ...p);
const orgCol = name => collection(db, 'orgs', orgId, name);

// ---------- Location & work sites ----------
const GEO_OPTS = { enableHighAccuracy: true, timeout: 15000, maximumAge: 10000 };
let lastPos = null, geoError = null, watchId = null, outsideSince = null, lastInsideSaved = 0, autoOutBusy = false;
const sites = () => Array.isArray(org?.sites) ? org.sites : [];
function distanceM(a, b) {
  const R = 6371000, rad = x => x * Math.PI / 180;
  const dLat = rad(b.lat - a.lat), dLng = rad(b.lng - a.lng);
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(rad(a.lat)) * Math.cos(rad(b.lat)) * Math.sin(dLng / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(h));
}
const fmtDist = m => m >= 1000 ? `${(m / 1000).toFixed(1)} km` : `${Math.round(m)} m`;
const slack = p => Math.min(p.acc || 0, 50);               // forgive up to 50 m of GPS error
const siteDistances = p => sites().map(s => ({ s, d: distanceM(p, s) })).sort((x, y) => x.d - y.d);
const siteHere = p => siteDistances(p).find(x => x.d <= x.s.radius + slack(p))?.s || null;
const clearlyOutside = p => sites().length > 0 && siteDistances(p).every(x => x.d - slack(p) > x.s.radius);
const geoMsg = e => e?.code === 1
  ? 'Location permission is blocked. Allow location for Zurmelibble to clock in and out.'
  : 'Location is off or unavailable. Turn on location (GPS) to clock in and out.';

function getLocation() {
  return new Promise((resolve, reject) => {
    if (!navigator.geolocation) return reject({ code: 2 });
    navigator.geolocation.getCurrentPosition(
      p => { lastPos = { lat: p.coords.latitude, lng: p.coords.longitude, acc: Math.round(p.coords.accuracy), t: Date.now() }; geoError = null; resolve(lastPos); },
      e => { geoError = e; reject(e); },
      GEO_OPTS
    );
  });
}
function startWatch() {
  if (watchId !== null || !navigator.geolocation) return;
  watchId = navigator.geolocation.watchPosition(
    p => { lastPos = { lat: p.coords.latitude, lng: p.coords.longitude, acc: Math.round(p.coords.accuracy), t: Date.now() }; geoError = null; checkGeofence(); renderGeo(); },
    e => { geoError = e; renderGeo(); },
    GEO_OPTS
  );
}
function stopWatch() {
  if (watchId !== null) navigator.geolocation.clearWatch(watchId);
  watchId = null; outsideSince = null;
}

// While clocked in: leaving every work site for 20 s clocks you out automatically.
async function checkGeofence() {
  const open = user && isActive() ? openShiftOf(user.uid) : null;
  if (!open || !sites().length || !lastPos || autoOutBusy || Date.now() - lastPos.t > 120000) { outsideSince = null; return; }
  if (clearlyOutside(lastPos)) {
    outsideSince ??= Date.now();
    if (Date.now() - outsideSince < 20000) return;
    autoOutBusy = true;
    try {
      // If we last saw them inside a while ago (app was closed), end the shift then.
      const end = open.lastInsideAt && Date.now() - open.lastInsideAt > 5 * 60000 ? open.lastInsideAt : Date.now();
      const near = siteDistances(lastPos)[0];
      await closeShift(open, lastPos, { end, autoOut: true });
      $('geoNote').textContent = `You left ${near.s.name}, so you were clocked out automatically at ${fmtTime(end)}.`;
    } catch (e) { console.error(e); }
    autoOutBusy = false; outsideSince = null;
  } else {
    outsideSince = null;
    if (siteHere(lastPos) && Date.now() - lastInsideSaved > 180000) {
      lastInsideSaved = Date.now();
      updateDoc(orgRef('shifts', open.id), { lastInsideAt: Date.now() }).catch(() => {});
    }
  }
}
setInterval(checkGeofence, 10000);

function renderGeo() {
  const el = $('geoStatus'); if (!el || !isActive()) return;
  let cls = 'muted', txt;
  if (geoError) { cls = 'err'; txt = geoMsg(geoError); }
  else if (!lastPos) txt = 'Checking your location…';
  else if (!sites().length) txt = `Location on (±${lastPos.acc} m)`;
  else {
    const here = siteHere(lastPos);
    if (here) { cls = 'ok'; txt = `You're at ${here.name} (±${lastPos.acc} m)`; }
    else { const n = siteDistances(lastPos)[0]; txt = `You're ${fmtDist(n.d)} from ${n.s.name}. Clock in works within ${n.s.radius} m.`; }
  }
  el.className = cls; el.textContent = txt;
}

function niceError(e) {
  const c = e?.code || '';
  if (c.includes('invalid-credential') || c.includes('wrong-password') || c.includes('user-not-found')) return 'Wrong email or password.';
  if (c.includes('email-already-in-use')) return 'That email already has an account.';
  if (c.includes('weak-password')) return 'Password needs at least 6 characters.';
  if (c.includes('invalid-email')) return 'That email looks wrong.';
  if (c.includes('permission-denied')) return 'You don\'t have permission to do that.';
  return e?.message || 'Something went wrong.';
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
      await setDoc(doc(db, 'users', cred.user.uid), { name, email, createdAt: Date.now(), currentOrg: null }, { merge: true });
    } else {
      await signInWithEmailAndPassword(auth, email, pass);
    }
  } catch (err) { $('authErr').textContent = niceError(err); }
  $('authSubmit').disabled = false;
};
$('signOut').onclick = () => signOut(auth);

// ---------- Session wiring ----------
const stop = list => { list.forEach(u => u()); list.length = 0; };

onAuthStateChanged(auth, async u => {
  stop(userUnsubs); stop(orgUnsubs); stop(dataUnsubs);
  user = u; profile = null; memberships = []; orgId = null; resetOrgData();
  if (!u) {
    stopWatch();
    show($('appView'), false); show($('authView'), true); setAuthMode(false);
    return;
  }
  show($('authView'), false); show($('appView'), true);
  setScreen('loading');
  const ref = doc(db, 'users', u.uid);
  const snap = await getDoc(ref);
  if (!snap.exists()) {
    await setDoc(ref, { name: u.displayName || u.email.split('@')[0], email: u.email, createdAt: Date.now(), currentOrg: null });
  }
  let membershipsLoaded = false;
  userUnsubs.push(onSnapshot(collection(db, 'users', u.uid, 'memberships'), s => {
    memberships = s.docs.map(d => ({ id: d.id, ...d.data() })).sort((a, b) => (a.name || '').localeCompare(b.name || ''));
    membershipsLoaded = true;
    renderSwitcher();
    route();
  }));
  if (u.uid === SUPER_UID) {
    userUnsubs.push(onSnapshot(collection(db, 'orgs'), s => {
      allOrgs = s.docs.map(d => ({ id: d.id, ...d.data() })).sort((x, y) => (y.createdAt || 0) - (x.createdAt || 0));
      render();
    }, err => console.error(err)));
  }
  userUnsubs.push(onSnapshot(ref, s => {
    profile = s.data() || {};
    $('meName').textContent = profile.name || u.email;
    route();
  }));

  // Decide which organisation to open.
  function route() {
    if (!profile || !membershipsLoaded) return;
    let target = profile.currentOrg;
    if (!target || !memberships.some(m => m.id === target)) target = memberships[0]?.id || null;
    if (target !== profile.currentOrg) { updateDoc(ref, { currentOrg: target }).catch(() => {}); }
    if (target !== orgId) openOrg(target);
    else render();
  }
});

function resetOrgData() {
  org = null; myMember = null; members = []; teams = []; shifts = []; dataKey = '';
}

function openOrg(id) {
  stop(orgUnsubs); stop(dataUnsubs); resetOrgData();
  orgId = id;
  if (!id) { render(); return; }
  setScreen('loading');
  orgUnsubs.push(onSnapshot(orgRef('members', user.uid), async s => {
    if (!s.exists()) {
      // I was removed (or cancelled). Clean up my index entry.
      await deleteDoc(doc(db, 'users', user.uid, 'memberships', id)).catch(() => {});
      return;
    }
    myMember = { id: s.id, ...s.data() };
    const key = `${myMember.role}|${myMember.teamId}`;
    if (key !== dataKey) { dataKey = key; subscribeData(); }
    render();
  }, err => { console.error(err); }));
  orgUnsubs.push(onSnapshot(orgRef(), s => { org = s.exists() ? { id: s.id, ...s.data() } : null; render(); }, () => {}));
}

function subscribeData() {
  stop(dataUnsubs);
  members = []; teams = []; shifts = []; directory = []; lists = []; cards = [];
  if (!isActive()) { render(); return; }
  const onErr = err => console.error(err);
  // Board data: everyone in the organisation sees every team's board.
  dataUnsubs.push(onSnapshot(orgCol('members'), s => { directory = s.docs.map(d => ({ id: d.id, ...d.data() })).filter(m => m.role !== 'pending').sort((x, y) => (x.name || '').localeCompare(y.name || '')); render(); }, onErr));
  // Lists only matter for cards made on the old Trello-style board (their status comes from the list).
  dataUnsubs.push(onSnapshot(orgCol('lists'), s => { lists = s.docs.map(d => ({ id: d.id, ...d.data() })); render(); }, onErr));
  dataUnsubs.push(onSnapshot(query(orgCol('cards'), limit(5000)), s => { cards = s.docs.map(d => ({ id: d.id, ...d.data() })); render(); }, onErr));
  dataUnsubs.push(onSnapshot(orgCol('teams'), s => { teams = s.docs.map(d => ({ id: d.id, ...d.data() })).sort((a, b) => a.name.localeCompare(b.name)); render(); }, onErr));
  const setShifts = s => { shifts = s.docs.map(d => ({ id: d.id, ...d.data() })).sort((a, b) => b.start - a.start); render(); };
  const setMembers = s => { members = s.docs.map(d => ({ id: d.id, ...d.data() })); render(); };
  if (isAdmin()) {
    dataUnsubs.push(onSnapshot(orgCol('members'), setMembers, onErr));
    dataUnsubs.push(onSnapshot(query(orgCol('shifts'), orderBy('start', 'desc'), limit(3000)), setShifts, onErr));
  } else if (isManager() && myMember.teamId) {
    dataUnsubs.push(onSnapshot(query(orgCol('members'), where('teamId', '==', myMember.teamId)), setMembers, onErr));
    dataUnsubs.push(onSnapshot(query(orgCol('shifts'), where('teamId', '==', myMember.teamId)), setShifts, onErr));
  } else {
    members = [myMember];
    dataUnsubs.push(onSnapshot(query(orgCol('shifts'), where('uid', '==', user.uid)), setShifts, onErr));
  }
}

// ---------- Screens ----------
function setScreen(name) {
  show($('loadingView'), name === 'loading');
  show($('onboardView'), name === 'onboard');
  show($('pendingView'), name === 'pending');
  show($('reviewView'), name === 'review');
  show($('platformView'), name === 'platform');
  document.body.classList.toggle('noside', name !== 'app');
  // In the app the organisation switcher and Sign out live in the sidebar; elsewhere in the top bar.
  if (name === 'app') { if ($('orgSwitch').parentNode.id !== 'sideOrgBox') { $('sideOrgBox').append($('orgSwitch')); $('sideFoot').append($('signOut')); } }
  else if ($('orgSwitch').parentNode.id !== 'whoBox') { $('whoBox').prepend($('orgSwitch')); $('whoBox').append($('signOut')); }
  show($('meAv'), name === 'app');
  if (name !== 'app') document.body.classList.remove('home-logo-on', 'logo-on');
  if (name !== 'app') document.body.classList.remove('side-open');
  document.querySelectorAll('[data-view]').forEach(v => show(v, name === 'app' && v.dataset.view === tab));
}

function renderSwitcher() {
  const sel = $('orgSwitch');
  const pendingCount = allOrgs.filter(o => orgStatus(o) === 'pending').length;
  sel.innerHTML = (isSuper() ? `<option value="__platform">Zurmelibble${pendingCount ? ` (${pendingCount} waiting)` : ''}</option>` : '') +
    memberships.map(m => `<option value="${m.id}">${esc(m.name)}</option>`).join('') +
    '<option value="__new">＋ Create or join…</option>';
  sel.value = platformMode && isSuper() ? '__platform' : orgId && memberships.some(m => m.id === orgId) ? orgId : '__new';
  show(sel, memberships.length > 0 || isSuper());
}
$('orgSwitch').onchange = async e => {
  const v = e.target.value;
  if (v === '__platform') { setPlatformMode(true); onboarding = false; render(); return; }
  setPlatformMode(false);
  if (v === '__new') { onboarding = true; render(); return; }
  onboarding = false;
  if (v === orgId) { render(); return; }
  await updateDoc(doc(db, 'users', user.uid), { currentOrg: v });
};

// ---------- Onboarding: create / join ----------
$('createOrgForm').onsubmit = async e => {
  e.preventDefault();
  const name = $('newOrgName').value.trim(); if (!name) return;
  const btn = e.submitter; btn.disabled = true; $('createOrgErr').textContent = '';
  try {
    const ref = doc(collection(db, 'orgs'));
    const code = newCode();
    const me = profile.name || user.email;
    const b = writeBatch(db);
    const status = isSuper() ? 'approved' : 'pending';
    b.set(ref, { name, ownerId: user.uid, ownerName: me, ownerEmail: user.email, code, requireApproval: false, status, createdAt: Date.now() });
    b.set(doc(db, 'orgs', ref.id, 'members', user.uid), { uid: user.uid, name: me, email: user.email, role: 'owner', teamId: null, joinedAt: Date.now() });
    b.set(doc(db, 'codes', code), { orgId: ref.id, orgName: name, requireApproval: false, status });
    b.set(doc(db, 'users', user.uid, 'memberships', ref.id), { name, joinedAt: Date.now() });
    b.update(doc(db, 'users', user.uid), { currentOrg: ref.id });
    await b.commit();
    $('newOrgName').value = ''; onboarding = false; tab = 'settings';
  } catch (err) { $('createOrgErr').textContent = niceError(err); }
  btn.disabled = false;
};

$('joinOrgForm').onsubmit = async e => {
  e.preventDefault();
  const code = cleanCode($('joinCode').value); if (!code) return;
  const btn = e.submitter; btn.disabled = true; $('joinOrgErr').textContent = '';
  try {
    const c = await getDoc(doc(db, 'codes', code));
    if (!c.exists()) throw new Error('That code doesn\'t exist. Check it with your admin.');
    const { orgId: id, orgName, requireApproval } = c.data();
    if ((c.data().status || 'approved') !== 'approved') throw new Error(`${orgName} isn't open yet. It's waiting for approval by Zurmelibble.`);
    if (memberships.some(m => m.id === id)) throw new Error(`You're already in ${orgName}.`);
    const existing = await getDoc(doc(db, 'orgs', id, 'members', user.uid));
    const b = writeBatch(db);
    if (!existing.exists()) {
      b.set(doc(db, 'orgs', id, 'members', user.uid), {
        uid: user.uid, name: profile.name || user.email, email: user.email,
        role: requireApproval ? 'pending' : 'member', teamId: null, code, joinedAt: Date.now()
      });
    }
    b.set(doc(db, 'users', user.uid, 'memberships', id), { name: orgName, joinedAt: Date.now() });
    b.update(doc(db, 'users', user.uid), { currentOrg: id });
    await b.commit();
    $('joinCode').value = ''; onboarding = false; tab = 'home';
    if (location.search.includes('join=')) history.replaceState(null, '', location.pathname);
  } catch (err) { $('joinOrgErr').textContent = niceError(err); }
  btn.disabled = false;
};
$('onboardCancel').onclick = () => { onboarding = false; render(); };
$('addOrg').onclick = () => { onboarding = true; render(); };

async function leaveCurrentOrg(confirmMsg) {
  if (!confirm(confirmMsg)) return;
  const id = orgId;
  try {
    const open = openShiftOf(user.uid);
    if (open) await closeShift(open);
    await deleteDoc(doc(db, 'orgs', id, 'members', user.uid));
    await deleteDoc(doc(db, 'users', user.uid, 'memberships', id));
  } catch (err) { alert(niceError(err)); }
}
$('cancelRequest').onclick = () => leaveCurrentOrg('Cancel your request to join?');
$('leaveOrg').onclick = () => leaveCurrentOrg(`Leave ${org?.name || 'this organisation'}? You'll need a new invite code to come back.`);

// ---------- Clock actions ----------
let busy = false;
async function closeShift(open, loc = null, extra = {}) {
  const end = extra.end ?? Date.now();
  const breaks = (open.breaks || []).filter(b => b.start < end).map(b => b.end ? b : { ...b, end });
  await updateDoc(orgRef('shifts', open.id), { end, breaks, outLoc: loc, autoOut: !!extra.autoOut });
}
async function act(kind) {
  if (busy || !isActive()) return; busy = true; renderClock();
  $('geoNote').textContent = kind === 'break' ? '' : 'Getting your location…';
  try {
    const open = openShiftOf(user.uid);
    if (kind === 'in' || kind === 'out') {
      let pos;
      try { pos = await getLocation(); }
      catch (e) { $('geoNote').textContent = geoMsg(e); busy = false; renderClock(); renderGeo(); return; }
      renderGeo();
      if (kind === 'in') {
        const site = siteHere(pos);
        if (sites().length && !site) {
          const n = siteDistances(pos)[0];
          $('geoNote').textContent = `You're ${fmtDist(n.d)} from ${n.s.name}. Get within ${n.s.radius} m to clock in.`;
        } else {
          const now = Date.now();
          await addDoc(orgCol('shifts'), { uid: user.uid, name: myMember.name, teamId: myMember.teamId ?? null, start: now, end: null, breaks: [], inLoc: pos, outLoc: null, siteId: site?.id || null, siteName: site?.name || null, lastInsideAt: now });
          lastInsideSaved = now;
          $('geoNote').textContent = site ? `Clocked in at ${site.name}.` : `Location saved (±${pos.acc} m)`;
        }
      } else if (open) {
        await closeShift(open, pos);
        $('geoNote').textContent = `Clocked out. Location saved (±${pos.acc} m)`;
      }
    } else if (kind === 'break' && open) {
      const now = Date.now();
      const breaks = [...(open.breaks || [])];
      const i = breaks.findIndex(b => !b.end);
      if (i >= 0) breaks[i] = { ...breaks[i], end: now }; else breaks.push({ start: now, end: null });
      await updateDoc(orgRef('shifts', open.id), { breaks });
    }
  } catch (e) { $('geoNote').textContent = niceError(e); }
  busy = false; renderClock(); renderHomeClock();
}
$('myActions').onclick = e => { const b = e.target.closest('[data-act]'); if (b) act(b.dataset.act); };

// ---------- Rendering ----------
// Copy each column header onto its cells so tables can stack as cards on phones.
function labelCells(tbody) {
  const ths = [...(tbody.closest('table').querySelectorAll('thead th'))].map(t => t.textContent.trim());
  tbody.querySelectorAll('tr').forEach(tr => [...tr.children].forEach((td, i) => {
    td.dataset.label = ths[i] || '';
    // Keep a cell's contents together (e.g. time + "auto" badge) when stacked on phones.
    if (td.childNodes.length > 1) td.innerHTML = `<span class="cv">${td.innerHTML}</span>`;
    td.classList.toggle('empty', !td.textContent.trim() && !td.querySelector('select, button, input'));
  }));
}
function renderClock() {
  if (!myMember || !isActive()) return;
  $('clockOrg').textContent = `${org?.name || ''}${myMember.teamId ? ' · ' + teamName(myMember.teamId) : ''}`;
  const st = statusOf(user.uid);
  const badge = $('myStatus');
  badge.className = 'badge s-' + st; badge.textContent = STATUS[st];
  $('myToday').textContent = fmtClock(todayMs(user.uid));
  const box = $('myActions');
  if (box.dataset.state !== st + busy) {
    box.dataset.state = st + busy;
    box.innerHTML = st === 'out'
      ? `<button class="b-in" data-act="in" ${busy ? 'disabled' : ''}>Clock in</button>`
      : `<button class="b-brk" data-act="break" ${busy ? 'disabled' : ''}>${st === 'brk' ? 'End break' : 'Start break'}</button>
         <button class="b-out" data-act="out" ${busy ? 'disabled' : ''}>Clock out</button>`;
  }
}

function filtered() {
  const pid = isStaff() ? $('fPerson').value : user.uid;
  const tid = isAdmin() ? $('fTeam').value : '';
  const from = $('fFrom').value ? new Date($('fFrom').value + 'T00:00').getTime() : -Infinity;
  const to = $('fTo').value ? new Date($('fTo').value + 'T23:59:59.999').getTime() : Infinity;
  return shifts.filter(s => (!pid || s.uid === pid) && (!tid || (tid === '__none' ? !s.teamId : s.teamId === tid)) && s.start >= from && s.start <= to);
}

function fillSelect(sel, first, opts) {
  const cur = sel.value;
  sel.innerHTML = first + opts.map(([v, l]) => `<option value="${v}">${esc(l)}</option>`).join('');
  sel.value = [...sel.options].some(o => o.value === cur) ? cur : '';
}

function renderSheet() {
  fillSelect($('fTeam'), '<option value="">All teams</option><option value="__none">No team</option>', teams.map(t => [t.id, t.name]));
  fillSelect($('fPerson'), '<option value="">Everyone</option>',
    [...activeMembers()].sort((a, b) => (a.name || '').localeCompare(b.name || '')).map(u => [u.uid, u.name]));
  const rows = filtered();
  $('sCount').textContent = rows.length;
  $('sTotal').textContent = fmtDur(rows.reduce((t, s) => t + workedMs(s), 0));
  $('sBreaks').textContent = fmtDur(rows.reduce((t, s) => t + breakMs(s), 0));
  show($('sheetEmpty'), !rows.length);
  $('sheet').innerHTML = rows.map(s => `<tr>
    <td>${esc(nameOf(s.uid))}</td><td>${esc(teamName(s.teamId))}</td><td>${fmtDate(s.start)}</td>
    <td>${fmtTime(s.start)}</td><td>${fmtTime(s.end)}${s.autoOut ? ' <span class="badge s-brk" title="Clocked out automatically after leaving the work site">auto</span>' : ''}</td>
    <td>${fmtDur(breakMs(s))}</td><td><b>${fmtDur(workedMs(s))}</b></td>
    <td>${s.siteName ? esc(s.siteName) + '<br>' : ''}${mapsLink(s.inLoc)}</td>
    ${isStaff() ? `<td><button class="b-ghost b-sm" data-del="${s.id}">Delete</button></td>` : ''}
  </tr>`).join(''); labelCells($('sheet'));
}
$('sheet').onclick = async e => {
  const b = e.target.closest('[data-del]'); if (!b) return;
  if (confirm('Delete this shift? This can\'t be undone.')) {
    try { await deleteDoc(orgRef('shifts', b.dataset.del)); } catch (err) { alert(niceError(err)); }
  }
};
['fTeam', 'fPerson', 'fFrom', 'fTo'].forEach(id => $(id).addEventListener('change', () => { renderSheet(); renderMap(); }));

$('exportCsv').onclick = () => {
  const loc = l => l ? `${l.lat},${l.lng}` : '';
  const lines = [['Member', 'Team', 'Date', 'Clock in', 'Clock out', 'Break minutes', 'Worked minutes', 'Site', 'In location', 'Out location', 'Auto clock-out']]
    .concat(filtered().map(s => [nameOf(s.uid), teamName(s.teamId), fmtDate(s.start), fmtTime(s.start), s.end ? fmtTime(s.end) : '',
      Math.round(breakMs(s) / 60000), Math.round(workedMs(s) / 60000), s.siteName || '', loc(s.inLoc), loc(s.outLoc), s.autoOut ? 'yes' : '']));
  const csv = lines.map(r => r.map(v => `"${String(v).replace(/"/g, '""')}"`).join(',')).join('\n');
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([csv], { type: 'text/csv' }));
  a.download = `${(org?.name || 'zurmelibble').replace(/[^\w-]+/g, '_')}-timesheet.csv`; a.click();
};

const teamOptions = sel => `<option value="">No team</option>` + teams.map(t => `<option value="${t.id}" ${t.id === sel ? 'selected' : ''}>${esc(t.name)}</option>`).join('');

function renderPeople() {
  if (!isStaff()) return;
  const act = activeMembers();
  const st = act.map(u => statusOf(u.uid));
  $('pScope').textContent = isAdmin() ? 'People' : `People in ${teamName(myMember.teamId)}`;
  $('tMembers').textContent = act.length;
  $('tIn').textContent = st.filter(s => s === 'in').length;
  $('tBrk').textContent = st.filter(s => s === 'brk').length;
  $('tHours').textContent = fmtDur(shifts.filter(s => sameDay(s.start)).reduce((t, s) => t + workedMs(s), 0));
  $('peopleHint').textContent = isAdmin()
    ? 'Put people in teams and pick their role. Managers see and manage the time of everyone in their team.'
    : 'You can see and manage the time of everyone in your team.';

  const pend = members.filter(m => m.role === 'pending');
  show($('pendingCard'), isAdmin() && pend.length > 0);
  $('pendingList').innerHTML = pend.map(m => `<tr>
    <td><b>${esc(m.name)}</b><br><span class="muted">${esc(m.email)}</span></td>
    <td><select data-pteam="${m.uid}">${teamOptions(null)}</select></td>
    <td><button class="b-in b-sm" data-approve="${m.uid}">Approve</button> <button class="b-ghost b-sm" data-reject="${m.uid}">Reject</button></td>
  </tr>`).join(''); labelCells($('pendingList'));

  const order = { in: 0, brk: 1, out: 2 };
  $('people').innerHTML = [...act].sort((a, b) => order[statusOf(a.uid)] - order[statusOf(b.uid)] || (a.name || '').localeCompare(b.name || '')).map(u => {
    const s = statusOf(u.uid), open = openShiftOf(u.uid);
    const self = u.uid === user.uid, owner = u.role === 'owner';
    const canEdit = isAdmin() && !owner && !self;
    const roleCell = canEdit
      ? `<select data-role="${u.uid}">${['admin', 'manager', 'member'].map(r => `<option value="${r}" ${u.role === r ? 'selected' : ''}>${ROLE_LABEL[r]}</option>`).join('')}</select>`
      : `<span class="badge ${u.role === 'manager' ? 's-mgr' : u.role === 'member' ? 's-out' : 's-admin'}">${ROLE_LABEL[u.role]}</span>`;
    const teamCell = isAdmin() ? `<select data-team="${u.uid}">${teamOptions(u.teamId)}</select>` : esc(teamName(u.teamId));
    return `<tr>
      <td><b>${esc(u.name)}</b>${self ? ' <span class="muted">(you)</span>' : ''}<br><span class="muted">${esc(u.email)}</span></td>
      <td><span class="badge s-${s}">${STATUS[s]}</span></td>
      <td>${open ? fmtTime(open.start) : ''}</td>
      <td>${fmtDur(todayMs(u.uid))}</td>
      <td>${teamCell}</td>
      <td>${roleCell}</td>
      <td>${canEdit ? `<button class="b-ghost b-sm" data-remove="${u.uid}">Remove</button>` : ''}</td>
    </tr>`;
  }).join(''); labelCells($('people'));
}

async function safe(fn) { try { return await fn(); } catch (err) { alert(niceError(err)); render(); } }

$('people').onchange = e => {
  const t = e.target;
  if (t.dataset.team !== undefined) safe(() => updateDoc(orgRef('members', t.dataset.team), { teamId: t.value || null }));
  if (t.dataset.role !== undefined) {
    const u = members.find(m => m.uid === t.dataset.role);
    if (t.value === 'admin' && !confirm(`Make ${u.name} an admin? They'll see everyone's time and locations and can manage the organisation.`)) { render(); return; }
    safe(() => updateDoc(orgRef('members', u.uid), { role: t.value }));
  }
};
$('people').onclick = e => {
  const b = e.target.closest('[data-remove]'); if (!b) return;
  const u = members.find(m => m.uid === b.dataset.remove);
  if (confirm(`Remove ${u.name} from ${org?.name}? Their past shifts stay in the timesheets.`)) safe(() => deleteDoc(orgRef('members', u.uid)));
};
$('pendingList').onclick = e => {
  const a = e.target.closest('[data-approve]'), r = e.target.closest('[data-reject]');
  if (a) {
    const teamId = document.querySelector(`[data-pteam="${a.dataset.approve}"]`)?.value || null;
    safe(() => updateDoc(orgRef('members', a.dataset.approve), { role: 'member', teamId }));
  }
  if (r) {
    const u = members.find(m => m.uid === r.dataset.reject);
    if (confirm(`Reject ${u.name}'s request?`)) safe(() => deleteDoc(orgRef('members', u.uid)));
  }
};

function renderTeams() {
  if (!isAdmin()) return;
  show($('teamsEmpty'), !teams.length);
  $('teamList').innerHTML = teams.map(t => {
    const ppl = activeMembers().filter(m => m.teamId === t.id);
    const mgrs = ppl.filter(m => m.role === 'manager').map(m => esc(m.name)).join(', ') || '<span class="muted">none</span>';
    const working = ppl.filter(m => statusOf(m.uid) !== 'out').length;
    return `<tr>
      <td><b>${esc(t.name)}</b></td><td>${ppl.length}</td><td>${mgrs}</td><td>${working}</td>
      <td><div class="chips">${(t.subsystems || []).map(s => `<span class="chip">${esc(s.name)}<button class="tiny" title="Remove subsystem" data-subdel="${t.id}|${s.id}">✕</button></span>`).join('')}<button class="b-ghost b-sm" data-subadd="${t.id}">Add subsystem</button></div></td>
      <td><button class="b-ghost b-sm" data-rename="${t.id}">Rename</button> <button class="b-ghost b-sm" data-tdel="${t.id}">Delete</button></td>
    </tr>`;
  }).join(''); labelCells($('teamList'));
}
$('addTeamForm').onsubmit = e => {
  e.preventDefault();
  const name = $('newTeamName').value.trim(); if (!name) return;
  $('newTeamName').value = '';
  safe(() => addDoc(orgCol('teams'), { name, createdAt: Date.now() }));
};
$('teamList').onclick = e => {
  const rn = e.target.closest('[data-rename]'), del = e.target.closest('[data-tdel]');
  const sAdd = e.target.closest('[data-subadd]'), sDel = e.target.closest('[data-subdel]');
  if (sAdd) {
    const t = teams.find(x => x.id === sAdd.dataset.subadd);
    const name = prompt(`New subsystem in ${t.name}`)?.trim();
    if (name) safe(() => updateDoc(orgRef('teams', t.id), { subsystems: [...(t.subsystems || []), { id: Math.random().toString(36).slice(2, 10), name }] }));
    return;
  }
  if (sDel) {
    const [tid, sid] = sDel.dataset.subdel.split('|');
    const t = teams.find(x => x.id === tid), s = (t.subsystems || []).find(x => x.id === sid);
    const n = cards.filter(c => c.subsystemId === sid).length;
    if (!confirm(`Remove the subsystem ${s.name} from ${t.name}?${n ? ` ${n} card(s) will keep the team but lose the subsystem.` : ''}`)) return;
    safe(async () => {
      const b = writeBatch(db);
      b.update(orgRef('teams', tid), { subsystems: t.subsystems.filter(x => x.id !== sid) });
      cards.filter(c => c.subsystemId === sid).forEach(c => b.update(orgRef('cards', c.id), { subsystemId: null }));
      await b.commit();
    });
    return;
  }
  if (rn) {
    const t = teams.find(x => x.id === rn.dataset.rename);
    const name = prompt('New team name', t.name)?.trim();
    if (name) safe(() => updateDoc(orgRef('teams', t.id), { name }));
  }
  if (del) {
    const t = teams.find(x => x.id === del.dataset.tdel);
    const ppl = members.filter(m => m.teamId === t.id);
    if (!confirm(`Delete team ${t.name}? ${ppl.length} ${ppl.length === 1 ? 'person' : 'people'} will be moved to "No team".`)) return;
    safe(async () => {
      const b = writeBatch(db);
      ppl.forEach(m => b.update(orgRef('members', m.uid), { teamId: null }));
      b.delete(orgRef('teams', t.id));
      await b.commit();
    });
  }
};

function renderSettings() {
  $('myMembership').innerHTML = `You're <b>${ROLE_LABEL[role()] || ''}</b> in <b>${esc(org?.name || '')}</b>` +
    (myMember?.teamId ? `, team <b>${esc(teamName(myMember.teamId))}</b>.` : '.');
  show($('leaveOrg'), role() !== 'owner');
  if (!isAdmin() || !org) return;
  $('inviteCode').textContent = org.code;
  $('requireApproval').checked = !!org.requireApproval;
  if (document.activeElement !== $('orgNameInput')) $('orgNameInput').value = org.name;
}
const inviteLink = () => `${location.origin}${location.pathname}?join=${org.code}${org.brand ? '&brand=' + org.brand : ''}`;
$('copyInvite').onclick = async () => {
  const text = `Join ${org.name} on Zurmelibble: ${inviteLink()}\nInvite code: ${org.code}`;
  try { await navigator.clipboard.writeText(text); $('inviteMsg').textContent = 'Invite message copied. Paste it in WhatsApp or email.'; }
  catch { prompt('Copy this invite message:', text); }
};
$('resetCode').onclick = () => {
  if (!confirm('Make a new invite code? The old one will stop working.')) return;
  safe(async () => {
    const code = newCode();
    const b = writeBatch(db);
    b.delete(doc(db, 'codes', org.code));
    b.set(doc(db, 'codes', code), { orgId, orgName: org.name, requireApproval: !!org.requireApproval });
    b.update(orgRef(), { code });
    await b.commit();
    $('inviteMsg').textContent = 'New code created.';
  });
};
$('requireApproval').onchange = e => {
  const v = e.target.checked;
  safe(async () => {
    const b = writeBatch(db);
    b.update(orgRef(), { requireApproval: v });
    b.update(doc(db, 'codes', org.code), { requireApproval: v });
    await b.commit();
  });
};
$('orgNameForm').onsubmit = e => {
  e.preventDefault();
  const name = $('orgNameInput').value.trim(); if (!name) return;
  safe(async () => {
    const b = writeBatch(db);
    b.update(orgRef(), { name });
    b.update(doc(db, 'codes', org.code), { orgName: name });
    b.set(doc(db, 'users', user.uid, 'memberships', orgId), { name }, { merge: true });
    await b.commit();
    $('orgNameMsg').textContent = 'Saved.';
  });
};

function renderMap() {
  if (tab !== 'map' || !isStaff() || !window.L) return;
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
    L.circleMarker([loc.lat, loc.lng], { radius: 8, color, fillColor: color, fillOpacity: .8, weight: 2 }).bindPopup(label).addTo(mapLayer);
  };
  sites().forEach(s => {
    pts.push([s.lat, s.lng]);
    L.circle([s.lat, s.lng], { radius: s.radius, color: css.getPropertyValue('--accent').trim(), weight: 2, fillOpacity: .08 }).bindPopup(`<b>${esc(s.name)}</b><br>Radius ${s.radius} m`).addTo(mapLayer);
  });
  filtered().forEach(s => {
    const n = esc(nameOf(s.uid));
    add(s.inLoc, css.getPropertyValue('--in').trim(), `<b>${n}</b><br>Clock in ${fmtDate(s.start)} ${fmtTime(s.start)}<br>±${s.inLoc?.acc} m`);
    add(s.outLoc, css.getPropertyValue('--out').trim(), `<b>${n}</b><br>Clock out ${fmtDate(s.end || s.start)} ${fmtTime(s.end)}<br>±${s.outLoc?.acc} m`);
  });
  if (pts.length) map.fitBounds(pts, { padding: [30, 30], maxZoom: 16 });
}

// Organisation branding (e.g. CEFAST Aerospace). Set by the project owner on orgs/{id}.brand.
const BRANDS = ['cefast'];
function applyBrand() {
  const b = !onboarding && !(platformMode && isSuper()) && org && BRANDS.includes(org.brand) ? org.brand : '';
  if ((document.documentElement.dataset.brand || '') !== b) {
    if (b) document.documentElement.dataset.brand = b; else delete document.documentElement.dataset.brand;
    if (map) setTimeout(() => map.invalidateSize(), 0);
  }
  try { b ? localStorage.setItem('zb-brand', b) : localStorage.removeItem('zb-brand'); } catch (e) {}
}

function render() {
  if (!user || !profile) return;
  renderSwitcher();
  if (org || onboarding || !orgId || platformMode) applyBrand();
  // Header role badge
  show($('meRole'), !!role() && role() !== 'member' && !onboarding);
  $('meRole').textContent = ROLE_LABEL[role()] || '';
  // Which screen?
  if (platformMode && isSuper()) {
    show($('meRole'), false);
    setScreen('platform'); renderPlatform(); return;
  }
  if (onboarding || (!orgId && memberships.length === 0)) {
    if (pendingJoin && !$('joinCode').value) $('joinCode').value = pendingJoin;
    show($('onboardCancel'), memberships.length > 0);
    setScreen('onboard'); return;
  }
  if (!orgId || !myMember) { setScreen('loading'); return; }
  if (role() === 'pending') {
    $('pendingOrg').textContent = org?.name || memberships.find(m => m.id === orgId)?.name || 'the organisation';
    setScreen('pending'); return;
  }
  if (org && orgStatus(org) !== 'approved') {
    const st = orgStatus(org), owner = role() === 'owner';
    $('reviewTitle').textContent = st === 'pending' ? 'Waiting for approval' : 'Not approved';
    $('reviewText').textContent = st === 'pending'
      ? `${org.name} was sent to Zurmelibble for approval. You'll be able to invite people and clock in as soon as it's approved. This page updates by itself.`
      : `${org.name} wasn't approved by Zurmelibble, so it can't be used right now.`;
    show($('deleteOrgReq'), owner); show($('leaveReviewOrg'), !owner);
    setScreen('review'); return;
  }
  document.querySelectorAll('[data-need]').forEach(el => show(el, el.dataset.need === 'super' ? isSuper() : el.dataset.need === 'admin' ? isAdmin() : isStaff()));
  const allowed = ['home', 'clock', 'mytasks', 'sheet', 'board', 'settings'].concat(isStaff() ? ['people', 'map'] : [], isAdmin() ? ['teams'] : []);
  if (!allowed.includes(tab)) tab = 'home';
  if (tab === 'board') currentBoard();
  document.querySelectorAll('#tabs > [data-tab]').forEach(b => b.classList.toggle('active', b.dataset.tab === tab));
  renderSideBoards();
  $('meAv').textContent = initials(profile.name || user.email); $('meAv').style.setProperty('--h', hue(profile.name || '')); $('meAv').title = profile.name || '';
  $('pageTitle').textContent = tab === 'board' ? currentBoard().name : TITLES[tab];
  document.title = `${tab === 'board' ? currentBoard().name : TITLES[tab]} · ${org?.name || 'Zurmelibble'}`;
  document.body.classList.toggle('wide', tab === 'board' || tab === 'mytasks' || tab === 'home');
  setScreen('app');
  startWatch();
  renderClock(); renderGeo(); renderSheet(); renderPeople(); renderTeams(); renderSettings(); renderSites(); renderMap(); renderBoard(); renderMyTasks(); renderHome();
  syncDrawer();
  queueLogo();
}

// ---------- Organisation awaiting / refused approval ----------
$('deleteOrgReq').onclick = async () => {
  if (!confirm(`Delete ${org.name}? This removes the request completely.`)) return;
  try {
    const b = writeBatch(db);
    b.delete(doc(db, 'codes', org.code));
    b.delete(orgRef('members', user.uid));
    b.delete(orgRef());
    b.delete(doc(db, 'users', user.uid, 'memberships', orgId));
    await b.commit();
  } catch (err) { alert(niceError(err)); }
};
$('leaveReviewOrg').onclick = () => leaveCurrentOrg(`Leave ${org?.name || 'this organisation'}?`);

// ---------- Platform panel (Zurmelibble owner only) ----------
async function loadOrgExtras(o) {
  if (!(o.id in orgCounts)) {
    orgCounts[o.id] = '…';
    getCountFromServer(collection(db, 'orgs', o.id, 'members'))
      .then(c => { orgCounts[o.id] = c.data().count; renderPlatform(); })
      .catch(() => { orgCounts[o.id] = '?'; });
  }
  if (!o.ownerEmail && !(o.id in ownerInfo)) {
    ownerInfo[o.id] = null;
    getDoc(doc(db, 'orgs', o.id, 'members', o.ownerId))
      .then(s => { ownerInfo[o.id] = s.data() || {}; renderPlatform(); }).catch(() => {});
  }
}
function renderPlatform() {
  if (!isSuper() || !platformMode) return;
  const by = st => allOrgs.filter(o => orgStatus(o) === st).length;
  $('pfPending').textContent = by('pending'); $('pfApproved').textContent = by('approved'); $('pfRejected').textContent = by('rejected');
  $('pfFilter').value = platformFilter;
  const list = allOrgs.filter(o => platformFilter === 'all' || orgStatus(o) === platformFilter);
  show($('pfEmpty'), !list.length);
  $('pfEmpty').textContent = platformFilter === 'pending' ? 'No organisations waiting for approval.' : 'Nothing here.';
  $('pfList').innerHTML = list.map(o => {
    loadOrgExtras(o);
    const st = orgStatus(o);
    const ownerName = o.ownerName || ownerInfo[o.id]?.name || '';
    const ownerEmail = o.ownerEmail || ownerInfo[o.id]?.email || '';
    const badge = { pending: 's-pending', approved: 's-in', rejected: 's-out' }[st];
    const actions = st === 'pending'
      ? `<button class="b-in b-sm" data-pf="approve" data-id="${o.id}">Approve</button> <button class="b-ghost b-sm" data-pf="reject" data-id="${o.id}">Reject</button>`
      : st === 'approved'
        ? `<button class="b-ghost b-sm" data-pf="reject" data-id="${o.id}">Suspend</button>`
        : `<button class="b-ghost b-sm" data-pf="approve" data-id="${o.id}">Approve</button>`;
    return `<tr>
      <td><b>${esc(o.name)}</b>${o.brand ? ' <span class="badge s-admin">' + esc(o.brand) + '</span>' : ''}</td>
      <td>${esc(ownerName)}<br><span class="muted">${esc(ownerEmail)}</span></td>
      <td>${o.createdAt ? fmtDate(o.createdAt) : ''}</td>
      <td>${orgCounts[o.id] ?? '…'}</td>
      <td><span class="badge ${badge}">${st === 'rejected' ? 'Rejected' : st === 'pending' ? 'Pending' : 'Approved'}</span></td>
      <td>${actions}</td>
    </tr>`;
  }).join(''); labelCells($('pfList'));
}
$('pfFilter').onchange = e => { platformFilter = e.target.value; renderPlatform(); };
$('pfList').onclick = e => {
  const b = e.target.closest('[data-pf]'); if (!b) return;
  const o = allOrgs.find(x => x.id === b.dataset.id);
  const status = b.dataset.pf === 'approve' ? 'approved' : 'rejected';
  if (status === 'rejected' && !confirm(orgStatus(o) === 'approved'
    ? `Suspend ${o.name}? Nobody in it will be able to clock in or join until you approve it again.`
    : `Reject ${o.name}?`)) return;
  safe(async () => {
    const batch = writeBatch(db);
    batch.update(doc(db, 'orgs', o.id), { status, reviewedAt: Date.now() });
    if (o.code) batch.update(doc(db, 'codes', o.code), { status });
    await batch.commit();
  });
};

// ---------- Work sites (admins) ----------
let siteMap = null, siteLayer = null, sitePoint = null;
function renderSites() {
  if (!isAdmin()) return;
  $('siteList').innerHTML = sites().map(s => `<tr>
    <td><b>${esc(s.name)}</b></td><td>${s.radius} m</td><td>${mapsLink(s)}</td>
    <td><button class="b-ghost b-sm" data-sdel="${s.id}">Delete</button></td></tr>`).join(''); labelCells($('siteList'));
  show($('sitesEmpty'), !sites().length);
  if (tab !== 'settings' || !window.L) return;
  if (!siteMap) {
    siteMap = L.map('siteMap').setView([-19.92, -43.94], 12);
    L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', { maxZoom: 19, attribution: '&copy; OpenStreetMap' }).addTo(siteMap);
    siteLayer = L.layerGroup().addTo(siteMap);
    siteMap.on('click', e => { sitePoint = { lat: e.latlng.lat, lng: e.latlng.lng }; drawSites(); });
    const first = sites()[0];
    if (first) siteMap.setView([first.lat, first.lng], 16);
    else if (lastPos) siteMap.setView([lastPos.lat, lastPos.lng], 16);
  }
  setTimeout(() => siteMap.invalidateSize(), 0);
  drawSites();
}
function drawSites() {
  if (!siteMap) return;
  const css = getComputedStyle(document.documentElement);
  const accent = css.getPropertyValue('--accent').trim(), inC = css.getPropertyValue('--in').trim();
  siteLayer.clearLayers();
  sites().forEach(s => L.circle([s.lat, s.lng], { radius: s.radius, color: accent, weight: 2, fillOpacity: .1 }).bindTooltip(s.name).addTo(siteLayer));
  if (sitePoint) {
    const r = Math.max(20, +$('siteRadius').value || 100);
    L.circle([sitePoint.lat, sitePoint.lng], { radius: r, color: inC, weight: 2, dashArray: '6 6', fillOpacity: .12 }).addTo(siteLayer);
    L.circleMarker([sitePoint.lat, sitePoint.lng], { radius: 5, color: inC, fillColor: inC, fillOpacity: 1 }).addTo(siteLayer);
    $('sitePick').textContent = `New site at ${sitePoint.lat.toFixed(5)}, ${sitePoint.lng.toFixed(5)}. Tap the map to move it.`;
  }
}
$('siteRadius').addEventListener('input', drawSites);
$('siteHere').onclick = async () => {
  $('siteErr').textContent = '';
  try {
    const p = await getLocation();
    sitePoint = { lat: p.lat, lng: p.lng };
    if (siteMap) siteMap.setView([p.lat, p.lng], 17);
    drawSites();
  } catch (e) { $('siteErr').textContent = geoMsg(e); }
};
$('siteForm').onsubmit = e => {
  e.preventDefault();
  $('siteErr').textContent = '';
  if (!sitePoint) { $('siteErr').textContent = 'Tap the map or use your location to place the site first.'; return; }
  const name = $('siteName').value.trim(); if (!name) return;
  const radius = Math.min(5000, Math.max(20, Math.round(+$('siteRadius').value || 100)));
  const site = { id: Math.random().toString(36).slice(2, 10), name, lat: +sitePoint.lat.toFixed(6), lng: +sitePoint.lng.toFixed(6), radius };
  safe(async () => {
    await updateDoc(orgRef(), { sites: [...sites(), site] });
    sitePoint = null; $('siteName').value = ''; $('sitePick').textContent = 'Site added. Tap the map to place another.';
  });
};
$('siteList').onclick = e => {
  const b = e.target.closest('[data-sdel]'); if (!b) return;
  const s = sites().find(x => x.id === b.dataset.sdel);
  if (!confirm(`Delete the work site ${s.name}?${sites().length === 1 ? ' With no sites left, people can clock in anywhere (location is still required).' : ''}`)) return;
  safe(() => updateDoc(orgRef(), { sites: sites().filter(x => x.id !== s.id) }));
};

// ---------- Boards (Plaky-style: one board per team, groups = subsystems) ----------
const STATUSES = [
  { id: 'backlog', label: 'Backlog', cls: 'st-backlog' },
  { id: 'todo', label: 'To do', cls: 'st-todo' },
  { id: 'doing', label: 'In progress', cls: 'st-doing' },
  { id: 'done', label: 'Done', cls: 'st-done' },
];
const PRIOS = [
  { id: 'high', label: 'High', cls: 'pr-high' },
  { id: 'medium', label: 'Medium', cls: 'pr-medium' },
  { id: 'low', label: 'Low', cls: 'pr-low' },
];
const GROUP_COLORS = ['#3d7cf5', '#c99700', '#e2445c', '#8e5bd6', '#6aa84f', '#ff7043', '#00a3b4', '#a1887f'];
const NO_GROUP_COLOR = '#8a8aa3';
const SUB_ICON = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M6 4v10a3 3 0 0 0 3 3h9"/><path d="m15 14 3 3-3 3"/></svg>';
const BOARD_ICON = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="5" y="4" width="14" height="17" rx="2"/><path d="M9 4V3h6v1M9 10h6M9 14h6"/></svg>';
let boardView = 'table', boardHideDone = false, mtSearch = '', mtDone = false;
try { boardView = localStorage.getItem('zb-bview') === 'kanban' ? 'kanban' : 'table'; } catch (e) {}
const collapsed = new Set(), openSubs = new Set();

const subsOf = teamId => teams.find(t => t.id === teamId)?.subsystems || [];
const subName = (teamId, subId) => subsOf(teamId).find(s => s.id === subId)?.name || '';
const personName = uid => directory.find(m => m.uid === uid)?.name || 'Former member';
const initials = n => (n || '?').split(/[\s._-]+/).filter(Boolean).slice(0, 2).map(w => w[0].toUpperCase()).join('') || '?';
const hue = n => [...(n || '')].reduce((h, ch) => (h * 31 + ch.charCodeAt(0)) % 360, 7);
const canDeleteCard = c => isStaff() || c.createdBy === user.uid;
const norm = s => String(s || '').normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase().trim();
// Cards from the old Trello-style board have a list instead of a status.
function cardStatus(c) {
  if (STATUSES.some(s => s.id === c.status)) return c.status;
  const n = norm(lists.find(l => l.id === c.listId)?.name);
  return /done|feito|conclu|pronto/.test(n) ? 'done' : /doing|progress|andamento|fazendo/.test(n) ? 'doing' : 'todo';
}
const statusInfo = c => STATUSES.find(s => s.id === cardStatus(c));
const prioInfo = c => PRIOS.find(p => p.id === c.priority) || null;
function dueInfo(due, done) {
  if (!due) return null;
  const d = new Date(due + 'T23:59:59'), days = (d - Date.now()) / 864e5;
  const label = new Date(due + 'T12:00').toLocaleDateString([], { day: 'numeric', month: 'short', ...(new Date(due).getFullYear() !== new Date().getFullYear() ? { year: 'numeric' } : {}) });
  return { label, cls: done ? 'done' : days < 0 ? 'overdue' : days < 2 ? 'soon' : '' };
}
const childrenOf = id => cards.filter(c => c.parentId === id).sort((x, y) => (x.order ?? 0) - (y.order ?? 0));
// Plaky names that belong to someone who has since joined count as that member.
function linked(c) {
  const uids = new Set(c.assignees || []), names = [];
  (c.assigneeNames || []).forEach(n => { const m = matchMember(n); m ? uids.add(m.uid) : names.push(n); });
  return { uids: [...uids], names };
}
const isMine = c => linked(c).uids.includes(user.uid);

// Boards shown in the sidebar: every team, plus "General" for items without a team.
function boardList() {
  const list = teams.map(t => ({ id: t.id, name: t.name }));
  if (!teams.length || cards.some(c => !c.parentId && (!c.teamId || !teams.some(t => t.id === c.teamId)))) list.push({ id: '__none', name: 'General' });
  return list;
}
function currentBoard() {
  const list = boardList();
  if (!list.some(b => b.id === boardTeam)) boardTeam = list.find(b => b.id === myMember?.teamId)?.id || list[0]?.id || '__none';
  return list.find(b => b.id === boardTeam) || { id: '__none', name: 'General' };
}
const onBoard = (c, bid) => bid === '__none' ? (!c.teamId || !teams.some(t => t.id === c.teamId)) : c.teamId === bid;
function boardGroups(bid, items) {
  const subs = bid === '__none' ? [] : subsOf(bid);
  const groups = subs.map((s, i) => ({ id: s.id, name: s.name, color: GROUP_COLORS[i % GROUP_COLORS.length] }));
  if (!groups.length || items.some(c => !groups.some(g => g.id === c.subsystemId))) groups.push({ id: '', name: groups.length ? 'No group' : 'Items', color: NO_GROUP_COLOR });
  return groups;
}
const inGroup = (c, g, groups) => g.id ? c.subsystemId === g.id : !groups.some(x => x.id && x.id === c.subsystemId);
function matches(c) {
  const q = norm(boardSearch);
  const kids = childrenOf(c.id);
  if (boardMine && !isMine(c) && !kids.some(isMine)) return false;
  if (boardHideDone && cardStatus(c) === 'done') return false;
  if (q && !norm(c.title).includes(q) && !norm(c.desc).includes(q) && !kids.some(k => norm(k.title).includes(q))) return false;
  return true;
}

function peopleHtml(c) {
  const L = linked(c), ppl = [...L.uids.map(u => ({ n: personName(u) })), ...L.names.map(n => ({ n, ext: true }))];
  if (!ppl.length) return '<span class="pp-empty">+</span>';
  const av = p => `<span class="av${p.ext ? ' ext' : ''}" style="--h:${hue(p.n)}" title="${esc(p.n)}${p.ext ? ' (not in Zurmelibble yet)' : ''}">${esc(initials(p.n))}</span>`;
  return `<span class="avs">${ppl.slice(0, 3).map(av).join('')}${ppl.length > 3 ? `<span class="av more" title="${esc(ppl.slice(3).map(p => p.n).join(', '))}">+${ppl.length - 3}</span>` : ''}</span>`;
}
function rowHtml(c, sub) {
  const st = statusInfo(c), pr = prioInfo(c), due = dueInfo(c.due, st.id === 'done');
  const kids = sub ? [] : childrenOf(c.id), open = openSubs.has(c.id);
  return `<div class="trow" data-card="${c.id}">
    <div class="tcell title">${sub ? '' : '<span class="grip" title="Drag to move">⋮⋮</span>'}<span class="ttl" data-open="${c.id}" title="${esc(c.title)}">${esc(c.title)}</span>${c.desc ? '<span class="hasdesc" title="Has notes">≡</span>' : ''}
      ${sub ? '' : `<span class="subtog${open ? ' open' : ''}${kids.length ? '' : ' none'}" data-subtog="${c.id}" title="${kids.length ? 'Show subitems' : 'Add subitems'}">${SUB_ICON}${kids.length || ''}</span>`}</div>
    <div class="tcell"><span class="pill ${st.cls}" data-pop="status" data-id="${c.id}">${st.label}</span></div>
    <div class="tcell date ${due?.cls || ''}"><span>${due ? esc(due.label) : ''}</span><input type="date" value="${c.due || ''}" data-date="${c.id}" aria-label="Due date"></div>
    <div class="tcell ppl" data-pop="people" data-id="${c.id}">${peopleHtml(c)}</div>
    <div class="tcell"><span class="pill ${pr ? pr.cls : 'empty'}" data-pop="prio" data-id="${c.id}">${pr ? pr.label : '+'}</span></div>
  </div>`;
}
const HEAD_COLS = '<div class="tcell">Status</div><div class="tcell">Due date</div><div class="tcell">People</div><div class="tcell">Priority</div>';
function itemHtml(c) {
  let html = rowHtml(c, false);
  if (openSubs.has(c.id)) {
    const kids = childrenOf(c.id);
    html += `<div class="subs"><div class="trow head"><div class="tcell title">Subitem</div>${HEAD_COLS}</div>
      ${kids.map(k => rowHtml(k, true)).join('')}
      <form class="addrow" data-addsub="${c.id}"><input placeholder="+ Add subitem" maxlength="200"></form></div>`;
  }
  return `<div class="titem" data-card="${c.id}">${html}</div>`;
}
function barHtml(items, key, defs) {
  if (!items.length) return '';
  const counts = defs.map(d => ({ d, n: items.filter(c => key(c) === d.id).length })).filter(x => x.n);
  return `<div class="bar" title="${esc(counts.map(x => `${x.d.label}: ${x.n}`).join(' · '))}">${counts.map(x => `<span class="${x.d.cls}" style="width:${(x.n / items.length) * 100}%"></span>`).join('')}</div>`;
}
function groupHtml(bid, g, items) {
  const key = bid + '|' + g.id, isColl = collapsed.has(key);
  const dues = items.map(c => c.due).filter(Boolean).sort();
  const fmt = d => new Date(d + 'T12:00').toLocaleDateString([], { day: 'numeric', month: 'short' });
  const range = dues.length ? (dues[0] === dues.at(-1) ? fmt(dues[0]) : `${fmt(dues[0])} – ${fmt(dues.at(-1))}`) : '';
  const summary = `<div class="sumrow"><div></div><div>${barHtml(items, cardStatus, STATUSES)}</div><div>${range ? `<span class="range">${range}</span>` : ''}</div><div></div><div>${barHtml(items, c => c.priority, PRIOS)}</div></div>`;
  return `<div class="grp${isColl ? ' collapsed' : ''}" style="--g:${g.color}" data-group="${g.id}">
    <div class="grp-head"><span class="chev" data-gcoll="${esc(key)}">▼</span><b>${esc(g.name)}</b><span class="n">${items.length} item${items.length === 1 ? '' : 's'}</span>
      ${isAdmin() && g.id ? `<button type="button" class="tiny" data-gmenu="${g.id}" title="Group options">•••</button>` : ''}</div>
    ${isColl ? summary : `<div class="trow head"><div class="tcell title">Item</div>${HEAD_COLS}</div>
    <div class="gbody" data-group="${g.id}">${items.map(itemHtml).join('')}</div>
    <form class="addrow" data-addgroup="${g.id}"><input placeholder="+ Add item" maxlength="200"></form>
    ${summary}`}
  </div>`;
}
function kanbanHtml(bid, groups, items) {
  const gOf = c => groups.find(g => inGroup(c, g, groups)) || groups.at(-1);
  return `<div class="kan">${STATUSES.map(s => {
    const col = items.filter(c => cardStatus(c) === s.id);
    return `<div class="kcol"><div class="kcol-head ${s.cls}">${s.label}<span class="n">${col.length}</span></div>
      <div class="kcol-cards" data-status="${s.id}">${col.map(c => {
        const g = gOf(c), pr = prioInfo(c), due = dueInfo(c.due, s.id === 'done'), kids = childrenOf(c.id);
        return `<div class="kcard" data-card="${c.id}" style="--g:${g.color}">
          <div class="kcard-tag">${esc(g.name)}</div>
          <div class="kcard-title">${esc(c.title)}</div>
          <div class="kcard-meta">${pr ? `<span class="pill sm ${pr.cls}">${pr.label}</span>` : ''}${due ? `<span class="kdue ${due.cls}">${esc(due.label)}</span>` : ''}${kids.length ? `<span title="Subitems">${kids.filter(k => cardStatus(k) === 'done').length}/${kids.length} ✓</span>` : ''}${c.desc ? '<span title="Has notes">≡</span>' : ''}${(c.assignees || []).length || (c.assigneeNames || []).length ? peopleHtml(c) : ''}</div>
        </div>`;
      }).join('')}</div>
      <form class="kadd" data-status="${s.id}"><input placeholder="+ Add item" maxlength="200"></form></div>`;
  }).join('')}</div>`;
}

function renderSideBoards() {
  const list = isActive() ? boardList() : [];
  $('sideBoards').innerHTML = list.map(b => `<button class="nav-item${tab === 'board' && b.id === boardTeam ? ' active' : ''}" data-tab="board" data-board="${b.id}">${BOARD_ICON}<span>${esc(b.name)}</span></button>`).join('')
    || '<div class="muted" style="padding:4px 10px;font-size:13px">No boards yet</div>';
}
function boardBusy() {
  const a = document.activeElement;
  return dragging || !!(a && a.closest && a.closest('#board') && a.matches('input:not([type=date]):not([type=checkbox])') && a.value);
}
function renderBoard() {
  if (tab !== 'board' || !isActive()) return;
  if (boardBusy()) return;
  const b = currentBoard();
  document.querySelectorAll('[data-view-btn]').forEach(x => x.classList.toggle('active', x.dataset.viewBtn === boardView));
  $('bMine').checked = boardMine; $('bHideDone').checked = boardHideDone;
  const all = cards.filter(c => !c.parentId && onBoard(c, b.id));
  const items = all.filter(matches).sort((x, y) => (x.order ?? 0) - (y.order ?? 0));
  const groups = boardGroups(b.id, all);
  const focused = document.activeElement?.closest?.('#board form') ? [...$('board').querySelectorAll('form')].indexOf(document.activeElement.closest('form')) : -1;
  boardSortables.forEach(s => s.destroy()); boardSortables = [];
  if (boardView === 'kanban') {
    $('board').innerHTML = kanbanHtml(b.id, groups, items);
  } else {
    $('board').innerHTML = `<div class="tscroll"><div class="tgrid">${groups.map(g => groupHtml(b.id, g, items.filter(c => inGroup(c, g, groups)))).join('')}</div></div>
      ${isAdmin() && b.id !== '__none' ? '<button type="button" class="add-group" id="bAddGroup">＋ Add new group</button>' : ''}`;
  }
  if (focused >= 0) $('board').querySelectorAll('form')[focused]?.querySelector('input')?.focus();
  show($('boardEmpty'), !all.length && !boardSearch);
  $('boardEmpty').textContent = `No items on ${b.name} yet. Type in "+ Add item" or press New item.`;
  if (!window.Sortable) return;
  const common = { animation: 150, forceFallback: true, fallbackTolerance: 4, delay: 180, delayOnTouchOnly: true, onStart: () => { dragging = true; } };
  if (boardView === 'kanban') {
    document.querySelectorAll('.kcol-cards').forEach(el => boardSortables.push(new Sortable(el, {
      ...common, group: 'kan', draggable: '.kcard',
      onEnd: ev => { dragging = false; moveItem(ev.item.dataset.card, ev.to, '.kcard', { status: ev.to.dataset.status }); }
    })));
  } else {
    document.querySelectorAll('.gbody').forEach(el => boardSortables.push(new Sortable(el, {
      ...common, group: 'rows', draggable: '.titem', handle: '.grip', delay: 0,
      onEnd: ev => { dragging = false; moveItem(ev.item.dataset.card, ev.to, '.titem', { subsystemId: ev.to.dataset.group || null }); }
    })));
  }
}
function orderBetween(prev, next) {
  if (prev == null && next == null) return 1024;
  if (prev == null) return next - 1024;
  if (next == null) return prev + 1024;
  return (prev + next) / 2;
}
function moveItem(id, toEl, sel, patch) {
  const ids = [...toEl.querySelectorAll(':scope > ' + sel)].map(e => e.dataset.card);
  const i = ids.indexOf(id);
  const ord = x => cards.find(c => c.id === x)?.order ?? null;
  const order = orderBetween(i > 0 ? ord(ids[i - 1]) : null, i < ids.length - 1 ? ord(ids[i + 1]) : null);
  const c = cards.find(x => x.id === id); if (!c) return;
  const kids = childrenOf(id);
  Object.assign(c, patch, { order });   // optimistic
  safe(async () => {
    await updateDoc(orgRef('cards', id), { ...patch, order, updatedAt: Date.now() });
    // Subitems follow their parent to its new group.
    if ('subsystemId' in patch) await Promise.all(kids.filter(k => k.subsystemId !== patch.subsystemId).map(k => updateDoc(orgRef('cards', k.id), { subsystemId: patch.subsystemId, updatedAt: Date.now() })));
  });
  setTimeout(render, 0);
}
function newCard(fields) {
  const teamId = fields.teamId !== undefined ? fields.teamId : (boardTeam && boardTeam !== '__none' ? boardTeam : null);
  const peers = cards.filter(c => (c.parentId || null) === (fields.parentId || null));
  const order = fields.order ?? Math.max(0, ...peers.map(c => c.order ?? 0)) + 1024;
  return addDoc(orgCol('cards'), {
    title: '', desc: '', status: 'todo', priority: null, subsystemId: null, parentId: null, assignees: [], assigneeNames: [], due: null,
    ...fields, teamId, order, createdBy: user.uid, createdByName: myMember.name, createdAt: Date.now(), updatedAt: Date.now()
  });
}
function deleteCardTree(c) {
  const kids = childrenOf(c.id);
  return safe(async () => { const b = writeBatch(db); kids.forEach(k => b.delete(orgRef('cards', k.id))); b.delete(orgRef('cards', c.id)); await b.commit(); });
}
const patchCard = (id, patch) => { const c = cards.find(x => x.id === id); if (c) Object.assign(c, patch); render(); return safe(() => updateDoc(orgRef('cards', id), { ...patch, updatedAt: Date.now() })); };

$('board').addEventListener('submit', e => {
  const f = e.target.closest('form'); if (!f) return;
  e.preventDefault();
  const input = f.querySelector('input'), title = input.value.trim(); if (!title) return;
  input.value = '';
  if (f.dataset.addsub) {
    const p = cards.find(c => c.id === f.dataset.addsub);
    newCard({ title, parentId: p.id, teamId: p.teamId || null, subsystemId: p.subsystemId || null });
  } else if ('addgroup' in f.dataset) {
    newCard({ title, subsystemId: f.dataset.addgroup || null });
  } else if (f.classList.contains('kadd')) {
    const b = currentBoard(), first = boardGroups(b.id, [])[0];
    newCard({ title, status: f.dataset.status, subsystemId: first?.id || null });
  }
});
$('board').addEventListener('focusout', e => { if (e.target.closest('form')) setTimeout(() => { if (!document.activeElement?.closest?.('#board form')) renderBoard(); }, 150); });
$('board').addEventListener('change', e => { const d = e.target.closest('[data-date]'); if (d) patchCard(d.dataset.date, { due: d.value || null }); });
$('board').addEventListener('click', e => {
  const t = e.target;
  const dateIn = t.closest('[data-date]');
  if (dateIn) { try { dateIn.showPicker(); } catch (err) {} return; }
  const pop = t.closest('[data-pop]');
  if (pop) { e.stopPropagation(); openPop(pop.dataset.pop, pop.dataset.id, pop); return; }
  const tog = t.closest('[data-subtog]');
  if (tog) { const id = tog.dataset.subtog; openSubs.has(id) ? openSubs.delete(id) : openSubs.add(id); renderBoard(); if (openSubs.has(id) && !childrenOf(id).length) setTimeout(() => $('board').querySelector(`[data-addsub="${id}"] input`)?.focus({ preventScroll: true }), 0); return; }
  const coll = t.closest('[data-gcoll]');
  if (coll) { const k = coll.dataset.gcoll; collapsed.has(k) ? collapsed.delete(k) : collapsed.add(k); renderBoard(); return; }
  const gm = t.closest('[data-gmenu]');
  if (gm) { e.stopPropagation(); openPop('group', gm.dataset.gmenu, gm); return; }
  if (t.closest('#bAddGroup')) { addGroup(); return; }
  const open = t.closest('[data-open]') || (t.closest('.kcard') && { dataset: { open: t.closest('.kcard').dataset.card } });
  if (open) openCard(open.dataset.open);
});
function addGroup() {
  const b = currentBoard(); if (b.id === '__none') return;
  const name = prompt('New group name, e.g. ADCS')?.trim(); if (!name) return;
  safe(() => updateDoc(orgRef('teams', b.id), { subsystems: [...subsOf(b.id), { id: Math.random().toString(36).slice(2, 10), name }] }));
}
$('bViews').onclick = e => { const v = e.target.closest('[data-view-btn]'); if (!v) return; boardView = v.dataset.viewBtn; try { localStorage.setItem('zb-bview', boardView); } catch (err) {} renderBoard(); };
$('bNew').onclick = async () => {
  const b = currentBoard(), first = boardGroups(b.id, [])[0];
  const ref = await safe(() => newCard({ title: 'New item', subsystemId: first?.id || null }));
  if (ref?.id) setTimeout(() => { openCard(ref.id); $('cTitle').select(); }, 300);
};
$('bMine').onchange = e => { boardMine = e.target.checked; renderBoard(); };
$('bHideDone').onchange = e => { boardHideDone = e.target.checked; renderBoard(); };
$('bSearch').oninput = e => { boardSearch = e.target.value.trim(); renderBoard(); };

// ---------- Popover: status, priority, people, group menu ----------
let popFor = null;
function closePop() { $('pop').hidden = true; popFor = null; }
function openPop(kind, id, anchor) {
  const pop = $('pop');
  if (popFor && popFor.kind === kind && popFor.id === id) { closePop(); return; }
  let html = '';
  if (kind === 'group') {
    html = '<div class="opt" data-gact="rename">Rename group</div><div class="opt" data-gact="delete" style="color:var(--out)">Delete group</div>';
  } else {
    const c = cards.find(x => x.id === id); if (!c) return;
    if (kind === 'status') html = STATUSES.map(s => `<span class="pill ${s.cls}" data-set="status" data-val="${s.id}">${s.label}</span>`).join('');
    if (kind === 'prio') html = PRIOS.map(p => `<span class="pill ${p.cls}" data-set="priority" data-val="${p.id}">${p.label}</span>`).join('') + '<span class="pill empty" data-set="priority" data-val="">Clear</span>';
    if (kind === 'people') {
      const opt = (val, n, on, ext) => `<label class="opt"><input type="checkbox" data-person="${esc(val)}" ${ext ? 'data-ext="1"' : ''} ${on ? 'checked' : ''}><span class="av${ext ? ' ext' : ''}" style="--h:${hue(n)}">${esc(initials(n))}</span><span>${esc(n)}</span></label>`;
      const L = linked(c), mine = directory.filter(m => L.uids.includes(m.uid)), rest = directory.filter(m => !L.uids.includes(m.uid));
      html = '<input class="popq" placeholder="Search people">' +
        mine.map(m => opt(m.uid, m.name, true)).join('') + L.names.map(n => opt(n, n, true, true)).join('') +
        rest.map(m => opt(m.uid, m.name, false)).join('');
    }
  }
  pop.className = kind === 'people' ? 'wide' : '';
  pop.innerHTML = html; pop.hidden = false; popFor = { kind, id };
  const r = anchor.getBoundingClientRect(), w = pop.offsetWidth, h = pop.offsetHeight;
  pop.style.left = Math.max(8, Math.min(r.left + r.width / 2 - w / 2, innerWidth - w - 8)) + 'px';
  pop.style.top = (r.bottom + h + 8 > innerHeight ? Math.max(8, r.top - h - 6) : r.bottom + 6) + 'px';
  pop.querySelector('.popq')?.focus({ preventScroll: true });
}
$('pop').addEventListener('click', e => {
  e.stopPropagation();
  const set = e.target.closest('[data-set]');
  if (set && popFor) { const id = popFor.id; closePop(); patchCard(id, { [set.dataset.set]: set.dataset.val || null }); return; }
  const g = e.target.closest('[data-gact]');
  if (g && popFor) {
    const b = currentBoard(), gid = popFor.id, sub = subsOf(b.id).find(s => s.id === gid); closePop(); if (!sub) return;
    if (g.dataset.gact === 'rename') {
      const name = prompt('Group name', sub.name)?.trim();
      if (name) safe(() => updateDoc(orgRef('teams', b.id), { subsystems: subsOf(b.id).map(s => s.id === gid ? { ...s, name } : s) }));
    } else {
      const inIt = cards.filter(c => c.teamId === b.id && c.subsystemId === gid);
      if (!confirm(inIt.length ? `Delete the group ${sub.name}? Its ${inIt.length} item(s) move to "No group".` : `Delete the group ${sub.name}?`)) return;
      safe(async () => {
        await Promise.all(inIt.map(c => updateDoc(orgRef('cards', c.id), { subsystemId: null, updatedAt: Date.now() })));
        await updateDoc(orgRef('teams', b.id), { subsystems: subsOf(b.id).filter(s => s.id !== gid) });
      });
    }
  }
});
$('pop').addEventListener('input', e => {
  if (!e.target.matches('.popq')) return;
  const q = norm(e.target.value);
  $('pop').querySelectorAll('.opt').forEach(o => { o.hidden = q && !norm(o.textContent).includes(q); });
});
$('pop').addEventListener('change', e => {
  const cb = e.target.closest('[data-person]'); if (!cb || !popFor) return;
  const c = cards.find(x => x.id === popFor.id); if (!c) return;
  const val = cb.dataset.person;
  if (cb.dataset.ext) patchCard(c.id, { assigneeNames: cb.checked ? [...new Set([...(c.assigneeNames || []), val])] : (c.assigneeNames || []).filter(n => n !== val) });
  else patchCard(c.id, cb.checked ? { assignees: [...new Set([...(c.assignees || []), val])] }
    : { assignees: (c.assignees || []).filter(u => u !== val), assigneeNames: (c.assigneeNames || []).filter(n => matchMember(n)?.uid !== val) });
});
document.addEventListener('click', e => { if (!$('pop').hidden && !e.target.closest('#pop')) closePop(); });
document.addEventListener('keydown', e => { if (e.key === 'Escape' && !$('pop').hidden) closePop(); });
window.addEventListener('resize', () => { if (!$('pop').hidden) closePop(); });
document.addEventListener('scroll', e => { if (!$('pop').hidden && !e.target.closest?.('#pop')) closePop(); }, true);

// ---------- Item drawer ----------
let editing = null;
function fillCardSubs(teamId, sel) {
  const subs = subsOf(teamId);
  $('cSub').innerHTML = '<option value="">No group</option>' + subs.map(s => `<option value="${s.id}">${esc(s.name)}</option>`).join('');
  $('cSub').value = subs.some(s => s.id === sel) ? sel : '';
  $('cSub').disabled = !subs.length;
}
function peoplePickHtml(c) {
  const lab = (val, n, on, ext) => `<label><input type="checkbox" value="${esc(val)}" ${ext ? 'data-ext="1"' : ''} ${on ? 'checked' : ''}><span class="av${ext ? ' ext' : ''}" style="--h:${hue(n)}">${esc(initials(n))}</span>${esc(n)}</label>`;
  const L = linked(c);
  return L.names.map(n => lab(n, n, true, true)).join('') + directory.map(m => lab(m.uid, m.name, L.uids.includes(m.uid))).join('') || '<span class="muted">Nobody yet.</span>';
}
function syncDrawer() {
  const c = cards.find(x => x.id === editing); if (!c || !$('cardDlg').open) return;
  const parent = c.parentId ? cards.find(x => x.id === c.parentId) : null;
  const boardNm = c.teamId ? teamName(c.teamId) : 'General', grp = c.subsystemId ? subName(c.teamId, c.subsystemId) : '';
  $('cCrumb').innerHTML = [esc(boardNm), grp ? esc(grp) : '', parent ? `<a data-goto="${parent.id}">${esc(parent.title)}</a>` : ''].filter(Boolean).join(' › ');
  show($('cSubsBox'), !c.parentId);
  const kids = childrenOf(c.id);
  $('cSubsTitle').textContent = kids.length ? `Subitems (${kids.filter(k => cardStatus(k) === 'done').length}/${kids.length} done)` : 'Subitems';
  $('cSubs').innerHTML = kids.map(k => { const st = statusInfo(k); return `<div class="subline"><span class="pill ${st.cls}" data-pop="status" data-id="${k.id}">${st.label}</span><span class="ttl" data-goto="${k.id}">${esc(k.title)}</span>${peopleHtml(k)}</div>`; }).join('');
}
function openCard(id) {
  const c = cards.find(x => x.id === id); if (!c) return;
  closePop();
  editing = id;
  $('cTitle').value = c.title || ''; $('cDesc').value = c.desc || ''; $('cDue').value = c.due || ''; $('cErr').textContent = '';
  $('cStatus').innerHTML = STATUSES.map(s => `<option value="${s.id}">${s.label}</option>`).join('');
  $('cPrio').innerHTML = '<option value="">None</option>' + PRIOS.map(p => `<option value="${p.id}">${p.label}</option>`).join('');
  $('cTeam').innerHTML = '<option value="">General (no team)</option>' + teams.map(t => `<option value="${t.id}">${esc(t.name)}</option>`).join('');
  $('cTeam').value = c.teamId || ''; $('cTeam').disabled = !!c.parentId;
  fillCardSubs(c.teamId, c.subsystemId); if (c.parentId) $('cSub').disabled = true;
  $('cPeople').innerHTML = peoplePickHtml(c);
  $('cMeta').textContent = c.importedFrom === 'plaky' ? `Imported from Plaky on ${fmtDate(c.createdAt)}` : `Created by ${c.createdByName || personName(c.createdBy)} on ${fmtDate(c.createdAt)}`;
  show($('cDelete'), canDeleteCard(c));
  $('cAddSub').querySelector('input').value = '';
  $('cStatus').value = cardStatus(c); $('cPrio').value = c.priority || '';
  if (!$('cardDlg').open) $('cardDlg').showModal();
  syncDrawer();
}
function drawerPatch() {
  const c = cards.find(x => x.id === editing); if (!c) return null;
  const title = $('cTitle').value.trim(); if (!title) return null;
  const teamId = c.parentId ? (c.teamId || null) : ($('cTeam').value || null);
  return { title, desc: $('cDesc').value.trim(), status: $('cStatus').value, priority: $('cPrio').value || null, due: $('cDue').value || null,
    teamId, subsystemId: c.parentId ? (c.subsystemId || null) : ($('cSub').value || null),
    assignees: [...$('cPeople').querySelectorAll('input:checked:not([data-ext])')].map(i => i.value),
    assigneeNames: [...$('cPeople').querySelectorAll('input[data-ext]:checked')].map(i => i.value) };
}
async function saveDrawer() {
  const c = cards.find(x => x.id === editing), patch = drawerPatch(); if (!c || !patch) return;
  await patchCard(c.id, patch);
  // Subitems stay on their parent's board and group.
  const kids = childrenOf(c.id).filter(k => k.teamId !== patch.teamId || k.subsystemId !== patch.subsystemId);
  if (kids.length) safe(() => Promise.all(kids.map(k => updateDoc(orgRef('cards', k.id), { teamId: patch.teamId, subsystemId: patch.subsystemId, updatedAt: Date.now() }))));
}
$('cTeam').onchange = e => fillCardSubs(e.target.value, '');
$('cCancel').onclick = () => $('cardDlg').close();
$('cardDlg').addEventListener('click', e => {
  if (e.target === $('cardDlg')) { $('cardDlg').close(); return; }   // backdrop
  const pop = e.target.closest('[data-pop]');
  if (pop) { e.stopPropagation(); openPop(pop.dataset.pop, pop.dataset.id, pop); return; }
  const go = e.target.closest('[data-goto]');
  if (go) { const patch = drawerPatch(); const cur = cards.find(x => x.id === editing); if (patch && cur && (patch.title !== cur.title || patch.desc !== (cur.desc || ''))) saveDrawer(); openCard(go.dataset.goto); }
});
$('cardForm').onsubmit = e => { e.preventDefault(); saveDrawer(); $('cardDlg').close(); };
$('cAddSub').addEventListener('keydown', e => {
  if (e.key !== 'Enter') return;
  e.preventDefault();
  const input = e.target, title = input.value.trim(); if (!title) return;
  const p = cards.find(c => c.id === editing); if (!p) return;
  input.value = '';
  newCard({ title, parentId: p.id, teamId: p.teamId || null, subsystemId: p.subsystemId || null });
});
$('cDelete').onclick = () => {
  const c = cards.find(x => x.id === editing); if (!c) return;
  const kids = childrenOf(c.id).length;
  if (!confirm(`Delete "${c.title}"${kids ? ` and its ${kids} subitem(s)` : ''}?`)) return;
  $('cardDlg').close();
  deleteCardTree(c);
};
$('cardDlg').addEventListener('close', () => { editing = null; closePop(); render(); });

// ---------- My tasks ----------
function renderMyTasks() {
  if (tab !== 'mytasks' || !isActive()) return;
  const q = norm(mtSearch);
  const mine = cards.filter(c => isMine(c) && (mtDone || cardStatus(c) !== 'done') && (!q || norm(c.title).includes(q)));
  const today = new Date(); today.setHours(0, 0, 0, 0);
  const day = d => Math.round((new Date(d + 'T00:00') - today) / 864e5);
  const buckets = [
    { name: 'Overdue', color: '#e2445c', f: c => c.due && day(c.due) < 0 && cardStatus(c) !== 'done' },
    { name: 'Today', color: '#3d7cf5', f: c => c.due && day(c.due) === 0 },
    { name: 'Next 7 days', color: '#c99700', f: c => c.due && day(c.due) > 0 && day(c.due) <= 7 },
    { name: 'Later', color: '#8e5bd6', f: c => c.due && day(c.due) > 7 },
    { name: 'No due date', color: NO_GROUP_COLOR, f: c => !c.due },
    { name: 'Done, past due', color: '#6aa84f', f: c => c.due && day(c.due) < 0 && cardStatus(c) === 'done' },
  ];
  const where = c => { const p = c.parentId ? cards.find(x => x.id === c.parentId) : null; const bn = c.teamId ? teamName(c.teamId) : 'General'; const g = c.subsystemId ? subName(c.teamId, c.subsystemId) : ''; return [bn, g, p?.title].filter(Boolean).join(' › '); };
  const row = c => {
    const st = statusInfo(c), pr = prioInfo(c), due = dueInfo(c.due, st.id === 'done');
    return `<div class="trow" data-card="${c.id}"><div class="tcell title"><span class="ttl" data-open="${c.id}" title="${esc(c.title)}">${esc(c.title)}</span></div>
      <div class="tcell board-name" title="${esc(where(c))}">${esc(where(c))}</div>
      <div class="tcell"><span class="pill ${st.cls}" data-pop="status" data-id="${c.id}">${st.label}</span></div>
      <div class="tcell date ${due?.cls || ''}"><span>${due ? esc(due.label) : ''}</span><input type="date" value="${c.due || ''}" data-date="${c.id}" aria-label="Due date"></div>
      <div class="tcell"><span class="pill ${pr ? pr.cls : 'empty'}" data-pop="prio" data-id="${c.id}">${pr ? pr.label : '+'}</span></div></div>`;
  };
  $('myTasks').innerHTML = `<div class="tscroll"><div class="tgrid">${buckets.map(b => {
    const list = mine.filter(b.f).sort((x, y) => (x.due || '9').localeCompare(y.due || '9') || (x.order ?? 0) - (y.order ?? 0));
    return list.length ? `<div class="grp" style="--g:${b.color}"><div class="grp-head"><b>${b.name}</b><span class="n">${list.length}</span></div>
      <div class="trow head"><div class="tcell title">Item</div><div class="tcell">Board</div><div class="tcell">Status</div><div class="tcell">Due date</div><div class="tcell">Priority</div></div>
      ${list.map(row).join('')}</div>` : '';
  }).join('')}</div></div>`;
  show($('myTasksEmpty'), !mine.length);
}
$('myTasks').addEventListener('click', e => {
  const dateIn = e.target.closest('[data-date]'); if (dateIn) { try { dateIn.showPicker(); } catch (err) {} return; }
  const pop = e.target.closest('[data-pop]'); if (pop) { e.stopPropagation(); openPop(pop.dataset.pop, pop.dataset.id, pop); return; }
  const o = e.target.closest('[data-open]'); if (o) openCard(o.dataset.open);
});
$('myTasks').addEventListener('change', e => { const d = e.target.closest('[data-date]'); if (d) patchCard(d.dataset.date, { due: d.value || null }); });
$('mtSearch').oninput = e => { mtSearch = e.target.value.trim(); renderMyTasks(); };
$('mtDone').onchange = e => { mtDone = e.target.checked; renderMyTasks(); };

// ---------- Import from Plaky (admins) ----------
const PLAKY_STATUS = { 'feito': 'done', 'pronto': 'done', 'done': 'done', 'em progresso': 'doing', 'working on it': 'doing', 'a fazer': 'todo', 'to do': 'todo', 'backlog': 'backlog', 'parado': 'todo', 'stuck': 'todo' };
const PLAKY_PRIO = { 'alta': 'high', 'high': 'high', 'media': 'medium', 'medium': 'medium', 'baixa': 'low', 'low': 'low' };
const MONTHS = ['jan', 'feb', 'mar', 'apr', 'may', 'jun', 'jul', 'aug', 'sep', 'oct', 'nov', 'dec'];
const MONTHS_PT = ['jan', 'fev', 'mar', 'abr', 'mai', 'jun', 'jul', 'ago', 'set', 'out', 'nov', 'dez'];
function plakyDate(s, year) {
  const m = norm(s).match(/^([a-z]{3})[a-z]*\.?\s+(\d{1,2})(?:,?\s+(\d{4}))?$/) || norm(s).match(/^(\d{1,2})\s+(?:de\s+)?([a-z]{3})[a-z]*\.?(?:\s+(?:de\s+)?(\d{4}))?$/);
  if (!m) return null;
  let mon, d, y;
  if (/^\d/.test(m[1])) { d = +m[1]; mon = m[2]; y = m[3]; } else { mon = m[1]; d = +m[2]; y = m[3]; }
  let mi = MONTHS.indexOf(mon); if (mi < 0) mi = MONTHS_PT.indexOf(mon); if (mi < 0) return null;
  return `${y || year}-${String(mi + 1).padStart(2, '0')}-${String(d).padStart(2, '0')}`;
}
function matchMember(name) {
  const k = norm(name), toks = k.split(/\s+/);
  return directory.find(m => norm(m.name) === k) ||
    directory.find(m => norm((m.email || '').split('@')[0]) === k) ||
    (toks.length > 1 ? directory.find(m => { const t = norm(m.name).split(/\s+/); return t[0] === toks[0] && t.at(-1) === toks.at(-1); }) : null) || null;
}
function parseImport(text) {
  const data = JSON.parse(text);
  const boards = Array.isArray(data.boards) ? data.boards : Object.entries(data.boards || data).map(([name, rows]) => ({ name, rows }));
  if (!boards.length || !boards.every(b => b.name && Array.isArray(b.rows))) throw new Error('This does not look like a Plaky export.');
  return boards;
}
const importKey = (board, row) => norm([board, row[0], row[1], row[2]].join('|'));
function previewImport() {
  $('impErr').textContent = ''; $('impGo').disabled = true;
  const text = $('impText').value.trim();
  if (!text) { $('impPreview').textContent = ''; return null; }
  try {
    const boards = parseImport(text);
    const done = new Set(cards.map(c => c.importKey).filter(Boolean));
    const people = new Set(); boards.forEach(b => b.rows.forEach(r => (r[5] || []).forEach(p => people.add(p))));
    const matched = [...people].filter(matchMember);
    const lines = boards.map(b => {
      const team = teams.find(t => norm(t.name) === norm(b.name));
      const fresh = b.rows.filter(r => !done.has(importKey(b.name, r))).length;
      return `<b>${esc(b.name)}</b>${team ? '' : ' (new board)'}: ${fresh} new of ${b.rows.length} items, groups ${esc([...new Set([...(b.groups || []), ...b.rows.map(r => r[0])])].join(', '))}`;
    });
    $('impPreview').innerHTML = lines.join('<br>') + `<br>People: ${matched.length} of ${people.size} matched to members${matched.length ? ` (${esc(matched.join(', '))})` : ''}. The rest are kept as names on the items.`;
    $('impGo').disabled = false;
    return boards;
  } catch (err) { $('impPreview').textContent = ''; $('impErr').textContent = err.message.startsWith('This') ? err.message : 'Could not read that. Paste the whole export.'; return null; }
}
async function runImport(boards) {
  const year = new Date().getFullYear();
  const done = new Set(cards.map(c => c.importKey).filter(Boolean));
  const writes = [];
  for (const b of boards) {
    let team = teams.find(t => norm(t.name) === norm(b.name));
    if (!team) { const ref = await addDoc(orgCol('teams'), { name: b.name, subsystems: [], createdAt: Date.now() }); team = { id: ref.id, name: b.name, subsystems: [] }; }
    const subs = [...(team.subsystems || [])];
    for (const gname of [...new Set([...(b.groups || []), ...b.rows.map(r => r[0])])].filter(Boolean)) {
      if (!subs.some(s => norm(s.name) === norm(gname))) subs.push({ id: Math.random().toString(36).slice(2, 10), name: gname });
    }
    if (subs.length !== (team.subsystems || []).length) await updateDoc(orgRef('teams', team.id), { subsystems: subs });
    const subId = g => subs.find(s => norm(s.name) === norm(g))?.id || null;
    const parents = {};   // group|title -> card id
    b.rows.forEach((r, i) => {
      const [group, parentTitle, title, status, date, people, prio] = r;
      const key = importKey(b.name, r);
      const id = doc(orgCol('cards')).id;
      if (!parentTitle) parents[norm(group + '|' + title)] = { id, key };
      if (done.has(key)) { const ex = cards.find(c => c.importKey === key); if (ex && !parentTitle) parents[norm(group + '|' + title)] = { id: ex.id, key }; return; }
      const parentId = parentTitle ? parents[norm(group + '|' + parentTitle)]?.id || null : null;
      const assignees = [], assigneeNames = [];
      (people || []).forEach(p => { const m = matchMember(p); m ? assignees.push(m.uid) : assigneeNames.push(p); });
      writes.push([id, {
        title: String(title).slice(0, 200), desc: '', status: PLAKY_STATUS[norm(status)] || 'todo', priority: PLAKY_PRIO[norm(prio)] || null,
        due: date ? plakyDate(date, year) : null, teamId: team.id, subsystemId: subId(group), parentId,
        assignees: [...new Set(assignees)], assigneeNames: [...new Set(assigneeNames)], order: (i + 1) * 1024,
        createdBy: user.uid, createdByName: myMember.name, createdAt: Date.now(), updatedAt: Date.now(), importedFrom: 'plaky', importKey: key
      }]);
    });
  }
  let n = 0;
  for (let i = 0; i < writes.length; i += 20) {
    await Promise.all(writes.slice(i, i + 20).map(([id, data]) => setDoc(orgRef('cards', id), data)));
    n += Math.min(20, writes.length - i);
    $('impPreview').textContent = `Imported ${n} of ${writes.length}…`;
  }
  return writes.length;
}
$('bImport').onclick = () => { $('impText').value = ''; $('impPreview').textContent = ''; $('impErr').textContent = ''; $('impGo').disabled = true; $('impDlg').showModal(); };
$('impText').addEventListener('input', previewImport);
$('impCancel').onclick = () => $('impDlg').close();
$('impForm').onsubmit = async e => {
  e.preventDefault();
  const boards = previewImport(); if (!boards) return;
  $('impGo').disabled = true; $('impText').disabled = true;
  try { const n = await runImport(boards); $('impPreview').textContent = `Done. ${n} item(s) imported.`; }
  catch (err) { console.error(err); $('impErr').textContent = niceError(err); }
  $('impText').disabled = false;
};

// ---------- Home ----------
const ago = ts => { const m = Math.round((Date.now() - ts) / 60000); return m < 1 ? 'just now' : m < 60 ? `${m} min ago` : m < 1440 ? `${Math.round(m / 60)} h ago` : `${Math.round(m / 1440)} d ago`; };
function whereOf(c) {
  const p = c.parentId ? cards.find(x => x.id === c.parentId) : null;
  return [c.teamId ? teamName(c.teamId) : 'General', c.subsystemId ? subName(c.teamId, c.subsystemId) : '', p?.title].filter(Boolean).join(' › ');
}
function taskRow(c, right) {
  const st = statusInfo(c);
  return `<div class="hrow" data-open="${c.id}"><span class="pill ${st.cls}" data-pop="status" data-id="${c.id}">${st.label}</span>
    <span class="t"><b>${esc(c.title)}</b><small>${esc(whereOf(c))}</small></span>${right}</div>`;
}
// Clock card on Home mirrors the Clock tab (updated every second by renderClock).
function renderHomeClock() {
  if (tab !== 'home' || !myMember || !isActive()) return;
  const st = statusOf(user.uid);
  $('homeStatus').className = 'badge s-' + st; $('homeStatus').textContent = STATUS[st];
  $('homeTeam').textContent = myMember.teamId ? teamName(myMember.teamId) : '';
  $('homeToday').textContent = fmtClock(todayMs(user.uid));
  const box = $('homeActions');
  if (box.dataset.state !== st + busy) { box.dataset.state = st + busy; box.innerHTML = $('myActions').innerHTML; }
  $('homeNote').textContent = $('geoNote').textContent || $('geoStatus').textContent;
  $('homeNote').className = $('geoNote').textContent ? 'muted' : $('geoStatus').className;
}
function renderHome() {
  if (tab !== 'home' || !isActive()) return;
  const h = new Date().getHours(), first = (profile?.name || myMember.name || '').split(' ')[0];
  $('homeHello').textContent = `${h < 12 ? 'Good morning' : h < 18 ? 'Good afternoon' : 'Good evening'}${first ? ', ' + first : ''}`;
  $('homeDate').textContent = `${new Date().toLocaleDateString([], { weekday: 'long', day: 'numeric', month: 'long' })} · ${org?.name || ''}`;
  renderHomeClock();
  // Task stats
  const today = new Date(); today.setHours(0, 0, 0, 0);
  const day = d => Math.round((new Date(d + 'T00:00') - today) / 864e5);
  const open = cards.filter(c => isMine(c) && cardStatus(c) !== 'done');
  const over = open.filter(c => c.due && day(c.due) < 0), week = open.filter(c => c.due && day(c.due) >= 0 && day(c.due) <= 7);
  $('hsOpen').textContent = open.length; $('hsOver').textContent = over.length; $('hsWeek').textContent = week.length;
  $('hsOverBox').classList.toggle('alert', over.length > 0);
  // Hours this week (Mon to Sun)
  const monday = new Date(today); monday.setDate(today.getDate() - ((today.getDay() + 6) % 7));
  const days = Array.from({ length: 7 }, (_, i) => { const d = new Date(monday); d.setDate(monday.getDate() + i); return d; });
  const perDay = days.map(d => shifts.filter(s => s.uid === user.uid && sameDay(s.start, d)).reduce((t, s) => t + workedMs(s), 0));
  $('hsHours').textContent = fmtDur(perDay.reduce((a, b) => a + b, 0));
  const max = Math.max(4 * 3600e3, ...perDay);
  $('homeWeek').innerHTML = days.map((d, i) => `<div class="hday${d.toDateString() === new Date().toDateString() ? ' today' : ''}" title="${fmtDur(perDay[i])}">
    <div class="col"><span style="height:${Math.max(2, perDay[i] / max * 100)}%"></span></div>
    <div>${perDay[i] ? (perDay[i] / 3600e3).toFixed(1) + 'h' : ''}</div><div>${d.toLocaleDateString([], { weekday: 'short' })}</div></div>`).join('');
  // My tasks: overdue first, then by due date
  const list = [...open].sort((x, y) => (x.due || '9999').localeCompare(y.due || '9999') || (x.order ?? 0) - (y.order ?? 0)).slice(0, 7);
  $('homeTasks').innerHTML = list.map(c => { const d = dueInfo(c.due, false); return taskRow(c, `<span class="d ${d?.cls || ''}">${d ? esc(d.label) : ''}</span>`); }).join('')
    || '<div class="hempty">No open tasks assigned to you. Add yourself in the People column of a board to see tasks here.</div>';
  // Team: who's working now (staff) or my team (members)
  if (isStaff()) {
    $('homeTeamTitle').textContent = 'Working now';
    const now = activeMembers().filter(m => statusOf(m.uid) !== 'out').sort((a, b) => (openShiftOf(a.uid)?.start || 0) - (openShiftOf(b.uid)?.start || 0));
    $('homeWorking').innerHTML = now.map(m => { const s = openShiftOf(m.uid), st = statusOf(m.uid);
      return `<div class="hrow person"><span class="av" style="--h:${hue(m.name)}">${esc(initials(m.name))}</span><span class="t"><b>${esc(m.name)}</b><small>${st === 'brk' ? 'On break' : 'Since ' + fmtTime(s.start)}${s.siteName ? ' · ' + esc(s.siteName) : ''}</small></span><span class="d">${fmtDur(workedMs(s))}</span></div>`; }).join('')
      || '<div class="hempty">Nobody is clocked in right now.</div>';
  } else {
    const t = myMember.teamId;
    $('homeTeamTitle').textContent = t ? teamName(t) : 'My team';
    const mates = directory.filter(m => t && m.teamId === t);
    $('homeWorking').innerHTML = mates.map(m => `<div class="hrow person"><span class="av" style="--h:${hue(m.name)}">${esc(initials(m.name))}</span><span class="t"><b>${esc(m.name)}${m.uid === user.uid ? ' (you)' : ''}</b><small>${ROLE_LABEL[m.role] || ''}</small></span><span></span></div>`).join('')
      || '<div class="hempty">You\'re not in a team yet. An admin can add you from People.</div>';
  }
  // Boards with progress
  $('homeBoards').innerHTML = boardList().map(b => {
    const items = cards.filter(c => !c.parentId && onBoard(c, b.id));
    const done = items.filter(c => cardStatus(c) === 'done').length, late = items.filter(c => c.due && day(c.due) < 0 && cardStatus(c) !== 'done').length;
    return `<button type="button" class="hboard" data-board="${b.id}"><b>${esc(b.name)}</b>
      ${barHtml(items, cardStatus, STATUSES) || '<div class="bar"></div>'}
      <small>${items.length ? `${done} of ${items.length} done${late ? ` · <span style="color:var(--out)">${late} overdue</span>` : ''}` : 'No items yet'}</small></button>`;
  }).join('') || '<div class="hempty">No boards yet. Admins create one per team in Teams.</div>';
  // Recently updated (ignores the bulk import itself)
  const recent = cards.filter(c => c.updatedAt && !(c.importedFrom && c.updatedAt - c.createdAt < 60000)).sort((a, b) => b.updatedAt - a.updatedAt).slice(0, 6);
  $('homeRecent').innerHTML = recent.map(c => taskRow(c, `<span class="d">${ago(c.updatedAt)}</span>`)).join('') || '<div class="hempty">Nothing changed yet.</div>';
}
// Phones: a small logo sits centred in the top bar on every screen. On Home it starts big above
// the greeting and, as you scroll, shrinks and rises into that centred spot.
let logoRaf = 0;
function placeHomeLogo() {
  logoRaf = 0;
  const el = $('homeLogo');
  const on = isActive() && !document.body.classList.contains('noside') && matchMedia('(max-width: 900px)').matches;
  const home = on && tab === 'home';
  document.body.classList.toggle('logo-on', on);
  document.body.classList.toggle('home-logo-on', home);
  if (!on) { $('pageTitle').style.maxWidth = ''; return; }
  const h0 = el.offsetHeight, w0 = el.offsetWidth; if (!h0) return;
  const pt = $('pageTitle');
  pt.style.maxWidth = '';
  const title = pt.getBoundingClientRect();
  const endH = 30, s1 = endH / h0, w1 = w0 * s1;
  const endTop = title.top + (title.height - endH) / 2;
  // Centred, unless the page title reaches it: then the logo moves right of the title.
  // Only if there's no room before the avatar does the title get cut short with "…".
  const av = $('meAv').getBoundingClientRect(), limit = (av.width ? av.left : innerWidth) - 10;
  let endLeft = Math.max((innerWidth - w1) / 2, title.right + 12);
  if (endLeft + w1 > limit) { endLeft = limit - w1; pt.style.maxWidth = Math.max(40, endLeft - 12 - title.left) + 'px'; }
  let x = endLeft, y = endTop, sc = s1;
  if (home) {
    // Shrink and slide over first (so it never covers the title), rise into the bar over the whole scroll.
    const slot = $('homeLogoSlot').getBoundingClientRect();
    const ease = t => { t = Math.min(1, Math.max(0, t)); return t * t * (3 - 2 * t); };
    const p = scrollY / 120, ex = ease(p * 3), ey = ease(p);
    x = slot.left + (endLeft - slot.left) * ex; y = slot.top + (endTop - slot.top) * ey; sc = 1 + (s1 - 1) * ex;
  }
  el.style.transform = `translate(${x.toFixed(1)}px, ${y.toFixed(1)}px) scale(${sc.toFixed(4)})`;
}
// Phones pin the top bar with position: fixed, so the page needs room for its real height.
function syncTopbarHeight() {
  const h = document.querySelector('.topbar').offsetHeight;
  if (h) document.documentElement.style.setProperty('--topbar-h', h + 'px');
}
const queueLogo = () => { if (!logoRaf) logoRaf = requestAnimationFrame(() => { syncTopbarHeight(); placeHomeLogo(); }); };
addEventListener('scroll', queueLogo, { passive: true });
addEventListener('resize', queueLogo);
$('homeLogo').querySelector('img').addEventListener('load', queueLogo);
$('homeActions').onclick = e => { const b = e.target.closest('[data-act]'); if (b) act(b.dataset.act); };
document.querySelector('[data-view="home"]').addEventListener('click', e => {
  const pop = e.target.closest('[data-pop]'); if (pop) { e.stopPropagation(); openPop(pop.dataset.pop, pop.dataset.id, pop); return; }
  const go = e.target.closest('[data-go]'); if (go) { setTab(go.dataset.go); return; }
  const b = e.target.closest('[data-board]'); if (b) { setTab('board', b.dataset.board); return; }
  const o = e.target.closest('[data-open]'); if (o) openCard(o.dataset.open);
});

// ---------- Tabs ----------
const TITLES = { home: 'Home', clock: 'Clock', mytasks: 'My tasks', sheet: 'Timesheets', people: 'People', teams: 'Teams', map: 'Map', board: 'Board', settings: 'Settings' };
function setTab(t, board) {
  tab = t;
  if (board) { boardTeam = board; try { localStorage.setItem('zb-board', board); } catch (e) {} }
  document.body.classList.remove('side-open');
  render();
  window.scrollTo(0, 0);
}
$('tabs').onclick = e => { const b = e.target.closest('[data-tab]'); if (b) setTab(b.dataset.tab, b.dataset.board); };
$('menuBtn').onclick = () => document.body.classList.toggle('side-open');
$('scrim').onclick = () => document.body.classList.remove('side-open');

// Live timers
setInterval(() => { renderClock(); renderHomeClock(); }, 1000);
setInterval(() => { if (tab === 'people') renderPeople(); if (tab === 'sheet') renderSheet(); }, 30000);
