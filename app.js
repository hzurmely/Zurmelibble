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
let tab = 'clock';
let directory = [], lists = [], cards = [], listsLoaded = false, creatingLists = false;
let boardTeam = '', boardSub = '', boardMine = false, boardSearch = '', dragging = false, boardSortables = [];
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
  members = []; teams = []; shifts = []; directory = []; lists = []; cards = []; listsLoaded = false;
  if (!isActive()) { render(); return; }
  const onErr = err => console.error(err);
  // Board data: everyone in the organisation shares one board.
  dataUnsubs.push(onSnapshot(orgCol('members'), s => { directory = s.docs.map(d => ({ id: d.id, ...d.data() })).filter(m => m.role !== 'pending').sort((x, y) => (x.name || '').localeCompare(y.name || '')); render(); }, onErr));
  dataUnsubs.push(onSnapshot(orgCol('lists'), s => { lists = s.docs.map(d => ({ id: d.id, ...d.data() })).sort((x, y) => x.order - y.order); listsLoaded = true; render(); }, onErr));
  dataUnsubs.push(onSnapshot(query(orgCol('cards'), limit(3000)), s => { cards = s.docs.map(d => ({ id: d.id, ...d.data() })); render(); }, onErr));
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
  show($('tabs'), name === 'app');
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
    $('joinCode').value = ''; onboarding = false; tab = 'clock';
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
  busy = false; renderClock();
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

async function safe(fn) { try { await fn(); } catch (err) { alert(niceError(err)); render(); } }

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
    show($('tabs'), false);
    setScreen('review'); return;
  }
  document.querySelectorAll('[data-need]').forEach(el => show(el, el.dataset.need === 'super' ? isSuper() : el.dataset.need === 'admin' ? isAdmin() : isStaff()));
  const allowed = ['clock', 'sheet', 'board', 'settings'].concat(isStaff() ? ['people', 'map'] : [], isAdmin() ? ['teams'] : []);
  if (!allowed.includes(tab)) tab = 'clock';
  document.querySelectorAll('nav [data-tab]').forEach(b => b.classList.toggle('active', b.dataset.tab === tab));
  document.body.classList.toggle('wide', tab === 'board');
  setScreen('app');
  startWatch();
  renderClock(); renderGeo(); renderSheet(); renderPeople(); renderTeams(); renderSettings(); renderSites(); renderMap(); renderBoard();
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

// ---------- Board (Kanban) ----------
const subsOf = teamId => teams.find(t => t.id === teamId)?.subsystems || [];
const subName = (teamId, subId) => subsOf(teamId).find(s => s.id === subId)?.name || '';
const personName = uid => directory.find(m => m.uid === uid)?.name || 'Former member';
const initials = n => (n || '?').split(/\s+/).filter(Boolean).slice(0, 2).map(w => w[0].toUpperCase()).join('');
const canDeleteCard = c => isStaff() || c.createdBy === user.uid;
function dueInfo(due) {
  if (!due) return null;
  const d = new Date(due + 'T23:59:59'), days = (d - Date.now()) / 864e5;
  return { label: new Date(due + 'T12:00').toLocaleDateString([], { day: 'numeric', month: 'short' }), cls: days < 0 ? 'overdue' : days < 2 ? 'soon' : '' };
}
function visibleCards(listId) {
  const q = boardSearch.toLowerCase();
  return cards.filter(c => c.listId === listId
    && (!boardTeam || (boardTeam === '__none' ? !c.teamId : c.teamId === boardTeam))
    && (!boardSub || c.subsystemId === boardSub)
    && (!boardMine || (c.assignees || []).includes(user.uid))
    && (!q || (c.title || '').toLowerCase().includes(q) || (c.desc || '').toLowerCase().includes(q)))
    .sort((x, y) => (x.order ?? 0) - (y.order ?? 0));
}
function cardHtml(c) {
  const tag = [c.teamId ? teamName(c.teamId) : '', c.subsystemId ? subName(c.teamId, c.subsystemId) : ''].filter(Boolean).join(' · ');
  const due = dueInfo(c.due);
  const avs = (c.assignees || []).slice(0, 4).map(u => `<span class="kav" title="${esc(personName(u))}">${esc(initials(personName(u)))}</span>`).join('');
  return `<div class="kcard" data-card="${c.id}">
    ${tag ? `<div class="kcard-tags">${esc(tag)}</div>` : ''}
    <div class="kcard-title">${esc(c.title)}</div>
    ${(due || c.desc || avs) ? `<div class="kcard-meta">${due ? `<span class="kdue ${due.cls}">Due ${esc(due.label)}</span>` : ''}${c.desc ? '<span title="Has a description">≡</span>' : ''}<span class="kavs">${avs}</span></div>` : ''}
  </div>`;
}
function renderBoardFilters() {
  const tSel = $('bTeam'), sSel = $('bSub');
  tSel.innerHTML = '<option value="">All teams</option><option value="__none">No team</option>' + teams.map(t => `<option value="${t.id}">${esc(t.name)}</option>`).join('');
  tSel.value = [...tSel.options].some(o => o.value === boardTeam) ? boardTeam : (boardTeam = '');
  const subs = boardTeam && boardTeam !== '__none' ? subsOf(boardTeam) : [];
  sSel.innerHTML = '<option value="">All subsystems</option>' + subs.map(s => `<option value="${s.id}">${esc(s.name)}</option>`).join('');
  sSel.value = subs.some(s => s.id === boardSub) ? boardSub : (boardSub = '');
  show(sSel, subs.length > 0);
  $('bMine').checked = boardMine;
}
function renderBoard() {
  if (tab !== 'board' || !isActive()) return;
  if (dragging || document.activeElement?.closest?.('.kadd')) return;
  renderBoardFilters();
  // First visit by an admin: set up the default lists.
  if (listsLoaded && !lists.length && isAdmin() && !creatingLists) {
    creatingLists = true;
    const b = writeBatch(db);
    ['To do', 'Doing', 'Done'].forEach((name, i) => b.set(doc(orgCol('lists')), { name, order: (i + 1) * 1024, createdAt: Date.now() }));
    b.commit().catch(err => console.error(err)).finally(() => { creatingLists = false; });
  }
  show($('boardEmpty'), listsLoaded && !lists.length && !isAdmin());
  $('boardEmpty').textContent = 'The board has no lists yet. An admin needs to open the Board once to set it up.';
  boardSortables.forEach(s => s.destroy()); boardSortables = [];
  $('board').innerHTML = lists.map(l => {
    const vc = visibleCards(l.id);
    return `<div class="klist ${isAdmin() ? 'admin' : ''}" data-list="${l.id}">
      <div class="klist-head"><b>${esc(l.name)}</b><span class="n">${vc.length}</span>
        ${isAdmin() ? `<button class="tiny" data-lren="${l.id}" title="Rename list">✎</button><button class="tiny" data-ldel="${l.id}" title="Delete list">✕</button>` : ''}</div>
      <div class="klist-cards" data-list="${l.id}">${vc.map(cardHtml).join('')}</div>
      <form class="kadd" data-list="${l.id}"><input placeholder="Add a card" maxlength="200"></form>
    </div>`;
  }).join('');
  if (!window.Sortable) return;
  const common = { animation: 150, forceFallback: true, fallbackTolerance: 4, delay: 180, delayOnTouchOnly: true,
    onStart: () => { dragging = true; }, onEnd: () => { dragging = false; setTimeout(render, 0); } };
  document.querySelectorAll('.klist-cards').forEach(el => boardSortables.push(new Sortable(el, {
    ...common, group: 'cards', draggable: '.kcard',
    onEnd: ev => { dragging = false; moveCard(ev.item, ev.to); }
  })));
  if (isAdmin()) boardSortables.push(new Sortable($('board'), {
    ...common, draggable: '.klist', handle: '.klist-head',
    onEnd: () => { dragging = false; reorderLists(); }
  }));
}
function orderBetween(prev, next) {
  if (prev == null && next == null) return 1024;
  if (prev == null) return next - 1024;
  if (next == null) return prev + 1024;
  return (prev + next) / 2;
}
function moveCard(item, toEl) {
  const id = item.dataset.card, listId = toEl.dataset.list;
  const ids = [...toEl.querySelectorAll('.kcard')].map(e => e.dataset.card);
  const i = ids.indexOf(id);
  const ord = x => cards.find(c => c.id === x)?.order ?? null;
  const order = orderBetween(i > 0 ? ord(ids[i - 1]) : null, i < ids.length - 1 ? ord(ids[i + 1]) : null);
  const c = cards.find(x => x.id === id);
  if (c) { c.listId = listId; c.order = order; }   // optimistic
  safe(() => updateDoc(orgRef('cards', id), { listId, order, updatedAt: Date.now() }));
  setTimeout(render, 0);
}
function reorderLists() {
  const ids = [...$('board').querySelectorAll('.klist')].map(e => e.dataset.list);
  safe(async () => {
    const b = writeBatch(db);
    ids.forEach((id, i) => { const l = lists.find(x => x.id === id); if (l && l.order !== (i + 1) * 1024) b.update(orgRef('lists', id), { order: (i + 1) * 1024 }); });
    await b.commit();
  });
  setTimeout(render, 0);
}
$('board').addEventListener('submit', e => {
  const f = e.target.closest('.kadd'); if (!f) return;
  e.preventDefault();
  const input = f.querySelector('input'), title = input.value.trim(); if (!title) return;
  input.value = '';
  const listId = f.dataset.list;
  const max = Math.max(0, ...cards.filter(c => c.listId === listId).map(c => c.order ?? 0));
  const teamId = boardTeam && boardTeam !== '__none' ? boardTeam : (boardTeam === '__none' ? null : myMember.teamId ?? null);
  safe(() => addDoc(orgCol('cards'), { title, desc: '', listId, order: max + 1024, teamId, subsystemId: boardSub || null, assignees: [], due: null, createdBy: user.uid, createdByName: myMember.name, createdAt: Date.now(), updatedAt: Date.now() }));
});
$('board').addEventListener('focusout', e => { if (e.target.closest('.kadd')) setTimeout(() => { if (!document.activeElement?.closest?.('.kadd')) renderBoard(); }, 150); });
$('board').addEventListener('click', e => {
  const ren = e.target.closest('[data-lren]'), del = e.target.closest('[data-ldel]'), card = e.target.closest('.kcard');
  if (ren) {
    const l = lists.find(x => x.id === ren.dataset.lren);
    const name = prompt('List name', l.name)?.trim();
    if (name) safe(() => updateDoc(orgRef('lists', l.id), { name }));
  } else if (del) {
    const l = lists.find(x => x.id === del.dataset.ldel), inList = cards.filter(c => c.listId === l.id);
    if (!confirm(inList.length ? `Delete the list ${l.name} and its ${inList.length} card(s)?` : `Delete the list ${l.name}?`)) return;
    safe(async () => { const b = writeBatch(db); inList.forEach(c => b.delete(orgRef('cards', c.id))); b.delete(orgRef('lists', l.id)); await b.commit(); });
  } else if (card) openCard(card.dataset.card);
});
$('bAddList').onclick = () => {
  const name = prompt('New list name')?.trim(); if (!name) return;
  const max = Math.max(0, ...lists.map(l => l.order ?? 0));
  safe(() => addDoc(orgCol('lists'), { name, order: max + 1024, createdAt: Date.now() }));
};
$('bTeam').onchange = e => { boardTeam = e.target.value; boardSub = ''; renderBoard(); };
$('bSub').onchange = e => { boardSub = e.target.value; renderBoard(); };
$('bMine').onchange = e => { boardMine = e.target.checked; renderBoard(); };
$('bSearch').oninput = e => { boardSearch = e.target.value.trim(); renderBoard(); };

// Card editor
let editing = null;
function fillCardSubs(teamId, sel) {
  const subs = subsOf(teamId);
  $('cSub').innerHTML = '<option value="">None</option>' + subs.map(s => `<option value="${s.id}">${esc(s.name)}</option>`).join('');
  $('cSub').value = subs.some(s => s.id === sel) ? sel : '';
  $('cSub').disabled = !subs.length;
}
function openCard(id) {
  const c = cards.find(x => x.id === id); if (!c) return;
  editing = id;
  $('cTitle').value = c.title || ''; $('cDesc').value = c.desc || ''; $('cDue').value = c.due || ''; $('cErr').textContent = '';
  $('cList').innerHTML = lists.map(l => `<option value="${l.id}">${esc(l.name)}</option>`).join(''); $('cList').value = c.listId;
  $('cTeam').innerHTML = '<option value="">No team</option>' + teams.map(t => `<option value="${t.id}">${esc(t.name)}</option>`).join('');
  $('cTeam').value = c.teamId || '';
  fillCardSubs(c.teamId, c.subsystemId);
  $('cPeople').innerHTML = directory.map(m => `<label><input type="checkbox" value="${m.uid}" ${(c.assignees || []).includes(m.uid) ? 'checked' : ''}>${esc(m.name)}</label>`).join('') || '<span class="muted">Nobody yet.</span>';
  $('cMeta').textContent = `Created by ${c.createdByName || personName(c.createdBy)} on ${fmtDate(c.createdAt)}`;
  show($('cDelete'), canDeleteCard(c));
  $('cardDlg').showModal();
}
$('cTeam').onchange = e => fillCardSubs(e.target.value, '');
$('cCancel').onclick = () => $('cardDlg').close();
$('cardForm').onsubmit = e => {
  e.preventDefault();
  const c = cards.find(x => x.id === editing); if (!c) return;
  const title = $('cTitle').value.trim(); if (!title) return;
  const listId = $('cList').value;
  const patch = { title, desc: $('cDesc').value.trim(), due: $('cDue').value || null, teamId: $('cTeam').value || null, subsystemId: $('cSub').value || null,
    assignees: [...$('cPeople').querySelectorAll('input:checked')].map(i => i.value), updatedAt: Date.now() };
  if (listId !== c.listId) { patch.listId = listId; patch.order = Math.max(0, ...cards.filter(x => x.listId === listId).map(x => x.order ?? 0)) + 1024; }
  $('cardDlg').close();
  safe(() => updateDoc(orgRef('cards', c.id), patch));
};
$('cDelete').onclick = () => {
  const c = cards.find(x => x.id === editing); if (!c) return;
  if (!confirm(`Delete the card "${c.title}"?`)) return;
  $('cardDlg').close();
  safe(() => deleteDoc(orgRef('cards', c.id)));
};

// ---------- Tabs ----------
function setTab(t) { tab = t; render(); }
$('tabs').onclick = e => { const b = e.target.closest('[data-tab]'); if (b) setTab(b.dataset.tab); };

// Live timers
setInterval(renderClock, 1000);
setInterval(() => { if (tab === 'people') renderPeople(); if (tab === 'sheet') renderSheet(); }, 30000);
