import { QRCode, jsQR } from './assets/qr-libs.js';
import initRaptor, { RaptorQDecoder, encode_packets } from './assets/raptorq.js';

const $ = selector => document.querySelector(selector);
const encoder = new TextEncoder();
const decoder = new TextDecoder();

const DISCOVERY_FRAME_PREFIX = 'NCH1';
const SIGNAL_FRAME_PREFIX = 'NCS1';
const SIGNAL_FRAME_MS = 280;
const HANDOFF_TONE_HZ = 1800;
const HANDOFF_BEEP_MS = 150;
const HANDOFF_GAP_MS = 130;
const HANDOFF_BEEP_COUNT = 3;
const HANDOFF_PERIOD_MS = 3000;
const HANDOFF_THRESHOLD_DB = 16;
const HANDOFF_ABSOLUTE_MIN_DB = -85;
const RAPTOR_TRANSPORT_BYTES = 260;
const RAPTOR_REPAIR_PERCENT = 300;
const RAPTOR_FRAME_MAGIC = new Uint8Array([0x4e, 0x43, 0x53, 0x31]); // NCS1
const RAPTOR_HEADER_BYTES = 16;
const RAPTOR_CRC_BYTES = 4;
const MAX_SIGNAL_BYTES = 64 * 1024;
const HEARTBEAT_MS = 4000;
const HEARTBEAT_STALE_MS = 12000;
const MEDIA_CHUNK_BYTES = 16 * 1024;
const BUFFER_HIGH_WATER = 512 * 1024;
const BUFFER_LOW_WATER = 128 * 1024;
const MAX_IMAGE_BYTES = 2 * 1024 * 1024;
const MAX_PENDING_IMAGES = 20;
const MAX_SCAN_PIXELS = 420000;

const ui = {
  connectionNav: $('#connectionNav'),
  connectionNavLabel: $('#connectionNavLabel'),
  metricRtt: $('#metricRtt'),
  metricSent: $('#metricSent'),
  metricReceived: $('#metricReceived'),
  metricRate: $('#metricRate'),
  metricUptime: $('#metricUptime'),
  metricPath: $('#metricPath'),
  recentView: $('#recentView'),
  sendView: $('#sendView'),
  filesView: $('#filesView'),
  recentTitle: $('#recentTitle'),
  recentMeta: $('#recentMeta'),
  recentSearch: $('#recentSearch'),
  recentSort: $('#recentSort'),
  recentItemList: $('#recentItemList'),
  recentLibraryEmpty: $('#recentLibraryEmpty'),
  recentStorageText: $('#recentStorageText'),
  storageBarFill: $('#storageBarFill'),
  stream: $('#messageStream'),
  empty: $('#emptyState'),
  emptyTitle: $('#emptyTitle'),
  emptyCopy: $('#emptyCopy'),
  composer: $('#composer'),
  input: $('#messageInput'),
  send: $('#sendButton'),
  imageButton: $('#imageButton'),
  imageInput: $('#imageInput'),
  imageDraft: $('#imageDraft'),
  imageDraftPreview: $('#imageDraftPreview'),
  imageDraftName: $('#imageDraftName'),
  imageDraftSize: $('#imageDraftSize'),
  removeImage: $('#removeImage'),
  overlay: $('#pairingOverlay'),
  closePairing: $('#closePairing'),
  pairDance: $('#pairDance'),
  pairConnected: $('#pairConnected'),
  opticalStage: $('#opticalStage'),
  scanStage: $('#scanStage'),
  qrStage: $('#qrStage'),
  qrCanvas: $('#pairQrCanvas'),
  discoveryCode: $('#discoveryCode'),
  discoveryQrCanvas: $('#discoveryQrCanvas'),
  detectedOutline: $('#detectedOutline'),
  pairPhase: $('#pairPhase'),
  pairStatusTitle: $('#pairStatusTitle'),
  pairStatus: $('#pairStatus'),
  pairProgress: $('#pairProgress'),
  cameraState: $('#cameraState'),
  alignmentScore: $('#alignmentScore'),
  alignmentHint: $('#alignmentHint'),
  showCode: $('#showCode'),
  scanCode: $('#scanCode'),
  cancelPairing: $('#cancelPairing'),
  scannerVideo: $('#scannerVideo'),
  scannerCanvas: $('#scannerCanvas'),
  disconnectInSheet: $('#disconnectInSheet'),
  filesTitle: $('#filesTitle'),
  clearLibrary: $('#clearLibrary'),
  backToTypes: $('#backToTypes'),
  fileSearch: $('#fileSearch'),
  fileTypeList: $('#fileTypeList'),
  storedFileList: $('#storedFileList'),
  libraryEmpty: $('#libraryEmpty'),
  imageSelectionTools: $('#imageSelectionTools'),
  selectedImageCount: $('#selectedImageCount'),
  selectAllImages: $('#selectAllImages'),
  downloadSelectedImages: $('#downloadSelectedImages'),
  storageSummary: $('#storageSummary'),
  storedCount: $('#storedCount'),
  navButtons: [...document.querySelectorAll('.app-nav [data-view]')],
  toast: $('#toast')
};

let peer = null;
let chatChannel = null;
let mediaChannel = null;
let peerRole = null;
let connectedAt = 0;
let lastPongAt = 0;
let lastRttMs = 0;
let connectionPath = '—';
let heartbeatTimer = 0;
let statsTimer = 0;
let metricsTimer = 0;
let pingSequence = 0;
const pendingPings = new Map();

let sentBytes = 0;
let receivedBytes = 0;
let byteSamples = [];

let signalKind = '';
let signalFrames = [];
let signalFrameIndex = 0;
let signalTimer = 0;
let pairingActive = false;
let pairingSession = '';
let pairingSessionNumber = 0;
let pairingMode = 'discover';
let buildingSignal = false;
let localDiscoveryId = '';
let remoteDiscoveryId = '';
let discoveryTimer = 0;
let raptorReady = null;
let signalDecoder = null;
let signalDecodeKind = '';
let signalSeenPackets = new Set();
let signalAcceptedPackets = 0;
let signalSourceSymbols = 0;
let signalFinishing = false;

let cameraStream = null;
let scannerRaf = 0;
let scannerGeneration = 0;
let scannerBusy = false;
let scannerLastDecode = 0;
let barcodeDetector = null;
let targetLastSeen = 0;
let lastDetectionFeedback = 0;

let audioContext = null;
let handoffAudioStream = null;
let handoffAudioSource = null;
let handoffAnalyser = null;
let handoffAudioRaf = 0;
let handoffBins = null;
let handoffTargetBin = 0;
let handoffOnFrames = 0;
let handoffOnsets = [];
let handoffLastHit = 0;
let handoffTriggered = false;
let handoffOutputTimer = 0;
let handoffListenPurpose = '';
let handoffOutputPurpose = '';
const handoffOscillators = new Set();

let pendingImages = [];
let imageBusy = false;
let incomingImage = null;
let outboundMediaQueue = Promise.resolve();
const objectUrls = new Set();

const LIBRARY_DB_NAME = 'near-chat-direct';
const LIBRARY_DB_VERSION = 1;
let libraryDbPromise = null;
let currentSession = null;
let currentSessionItems = [];
let liveSessionId = '';
let liveSessionPromise = null;
let storedFiles = [];
let recentItems = [];
let selectedFileType = '';
const selectedStoredImageIds = new Set();
let currentView = 'recent';
let recentNewestFirst = true;
let persistenceRequested = false;
let libraryErrorShown = false;

function randomId() {
  if (crypto.randomUUID) return crypto.randomUUID();
  const bytes = crypto.getRandomValues(new Uint8Array(16));
  return [...bytes].map(byte => byte.toString(16).padStart(2, '0')).join('');
}

function idbRequest(request) {
  return new Promise((resolve, reject) => {
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error || new Error('Local storage failed.'));
  });
}

function idbTransaction(transaction) {
  return new Promise((resolve, reject) => {
    transaction.oncomplete = () => resolve();
    transaction.onerror = () => reject(transaction.error || new Error('Local storage failed.'));
    transaction.onabort = () => reject(transaction.error || new Error('Local storage was stopped.'));
  });
}

function openLibraryDb() {
  if (libraryDbPromise) return libraryDbPromise;
  if (!('indexedDB' in window)) return Promise.reject(new Error('Local history is unavailable in this browser.'));
  libraryDbPromise = new Promise((resolve, reject) => {
    const request = indexedDB.open(LIBRARY_DB_NAME, LIBRARY_DB_VERSION);
    request.onupgradeneeded = () => {
      const db = request.result;
      const sessions = db.objectStoreNames.contains('sessions')
        ? request.transaction.objectStore('sessions')
        : db.createObjectStore('sessions', { keyPath: 'id' });
      if (!sessions.indexNames.contains('updatedAt')) sessions.createIndex('updatedAt', 'updatedAt');
      const items = db.objectStoreNames.contains('items')
        ? request.transaction.objectStore('items')
        : db.createObjectStore('items', { keyPath: 'id' });
      if (!items.indexNames.contains('sessionId')) items.createIndex('sessionId', 'sessionId');
      if (!items.indexNames.contains('createdAt')) items.createIndex('createdAt', 'createdAt');
    };
    request.onsuccess = () => {
      request.result.onversionchange = () => request.result.close();
      resolve(request.result);
    };
    request.onerror = () => {
      libraryDbPromise = null;
      reject(request.error || new Error('Local history could not be opened.'));
    };
    request.onblocked = () => {
      libraryDbPromise = null;
      reject(new Error('Close the other NearChat tabs and reload to use local history.'));
    };
  });
  return libraryDbPromise;
}

async function getLatestSession() {
  const db = await openLibraryDb();
  const transaction = db.transaction('sessions', 'readonly');
  const request = transaction.objectStore('sessions').index('updatedAt').openCursor(null, 'prev');
  return new Promise((resolve, reject) => {
    request.onsuccess = () => resolve(request.result?.value || null);
    request.onerror = () => reject(request.error || new Error('Recent session could not be read.'));
  });
}

async function getSessionItems(sessionId) {
  if (!sessionId) return [];
  const db = await openLibraryDb();
  const transaction = db.transaction('items', 'readonly');
  const items = await idbRequest(transaction.objectStore('items').index('sessionId').getAll(sessionId));
  return items.sort((a, b) => a.createdAt - b.createdAt);
}

async function getStoredFiles() {
  const db = await openLibraryDb();
  const transaction = db.transaction('items', 'readonly');
  const items = await idbRequest(transaction.objectStore('items').getAll());
  return items.filter(item => item.kind === 'file' && item.blob instanceof Blob)
    .sort((a, b) => b.createdAt - a.createdAt);
}

async function getRecentItems() {
  const db = await openLibraryDb();
  const transaction = db.transaction('items', 'readonly');
  const items = await idbRequest(transaction.objectStore('items').getAll());
  return items.sort((a, b) => b.createdAt - a.createdAt);
}

async function putSession(session) {
  const db = await openLibraryDb();
  const transaction = db.transaction('sessions', 'readwrite');
  transaction.objectStore('sessions').put(session);
  await idbTransaction(transaction);
}

async function putSessionItem(session, item) {
  const db = await openLibraryDb();
  const transaction = db.transaction(['sessions', 'items'], 'readwrite');
  transaction.objectStore('sessions').put(session);
  transaction.objectStore('items').put(item);
  await idbTransaction(transaction);
}

async function deleteLibraryItem(id) {
  const db = await openLibraryDb();
  const transaction = db.transaction('items', 'readwrite');
  transaction.objectStore('items').delete(id);
  await idbTransaction(transaction);
}

async function clearLibraryData() {
  const db = await openLibraryDb();
  const transaction = db.transaction(['sessions', 'items'], 'readwrite');
  transaction.objectStore('sessions').clear();
  transaction.objectStore('items').clear();
  await idbTransaction(transaction);
}

function requestDurableStorage() {
  if (persistenceRequested) return;
  persistenceRequested = true;
  navigator.storage?.persist?.().catch(() => {});
}

function showAppView(name) {
  const requested = name === 'recent' || name === 'files' ? name : 'send';
  currentView = requested;
  ui.recentView.hidden = requested !== 'recent';
  ui.sendView.hidden = requested !== 'send';
  ui.filesView.hidden = requested !== 'files';
  for (const button of ui.navButtons)
    button.setAttribute('aria-selected', String(button.dataset.view === requested));
  if (requested === 'recent') refreshRecentLibrary().catch(handleLibraryError);
  if (requested === 'files') refreshFileLibrary().catch(handleLibraryError);
}

function sessionTitle(timestamp) {
  const date = new Date(Number(timestamp) || Date.now());
  const today = new Date();
  const sameDay = date.toDateString() === today.toDateString();
  const yesterday = new Date(today);
  yesterday.setDate(today.getDate() - 1);
  const day = sameDay ? 'Today' : date.toDateString() === yesterday.toDateString()
    ? 'Yesterday'
    : date.toLocaleDateString([], { month: 'short', day: 'numeric' });
  return `${day}, ${date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' })}`;
}

function clearRenderedMessages() {
  ui.stream.querySelectorAll('.message-row').forEach(row => row.remove());
  for (const url of objectUrls) URL.revokeObjectURL(url);
  objectUrls.clear();
  ui.empty.hidden = false;
}

function setRecentEmpty() {
  const connected = isConnected();
  const hasMessages = currentSessionItems.length > 0 || Boolean(ui.stream.querySelector('.message-row'));
  ui.empty.hidden = hasMessages;
  ui.emptyTitle.textContent = connected ? 'Ready to send' : currentSession ? 'Nothing in this session' : 'No recent session';
  ui.emptyCopy.textContent = connected
    ? 'Use the box below to send text or images to the other device.'
    : currentSession
      ? 'Connect again to start a new local chat.'
      : 'Connect two devices to start a local chat.';
}

function updateRecentHeader() {
  ui.recentTitle.textContent = currentSession ? sessionTitle(currentSession.createdAt) : 'Recent';
  const count = currentSessionItems.length;
  ui.recentMeta.textContent = currentSession
    ? `${count} ${count === 1 ? 'item' : 'items'} · stored here`
    : 'Stored in this browser';
}

async function renderStoredSession(session) {
  currentSession = session;
  currentSessionItems = session ? await getSessionItems(session.id) : [];
  clearRenderedMessages();
  for (const item of currentSessionItems) {
    if (item.kind === 'text') {
      appendTextMessage({ mine: item.mine, text: item.text, timestamp: item.createdAt,
        state: item.mine ? 'sent' : 'received' });
      continue;
    }
    if (item.kind === 'file' && item.blob instanceof Blob) {
      const url = URL.createObjectURL(item.blob);
      objectUrls.add(url);
      appendImageMessage({ mine: item.mine, url, text: item.text || '', timestamp: item.createdAt,
        state: item.mine ? 'sent' : 'received' });
    }
  }
  setRecentEmpty();
  updateRecentHeader();
  updateStorageSummary();
}

async function ensureLiveSession() {
  if (liveSessionId) return liveSessionId;
  if (liveSessionPromise) return liveSessionPromise;
  const now = Date.now();
  const session = { id: randomId(), createdAt: now, updatedAt: now };
  liveSessionId = session.id;
  currentSession = session;
  currentSessionItems = [];
  clearRenderedMessages();
  setRecentEmpty();
  updateRecentHeader();
  liveSessionPromise = putSession(session).then(() => {
    requestDurableStorage();
    return session.id;
  }).catch(error => {
    liveSessionPromise = null;
    throw error;
  });
  return liveSessionPromise;
}

async function persistLiveItem(item) {
  try {
    const sessionId = await ensureLiveSession();
    const storedItem = { ...item, sessionId };
    const updatedAt = Math.max(Date.now(), Number(item.createdAt) || 0);
    const session = { ...currentSession, id: sessionId, updatedAt };
    await putSessionItem(session, storedItem);
    currentSession = session;
    const existing = currentSessionItems.findIndex(entry => entry.id === storedItem.id);
    if (existing >= 0) currentSessionItems[existing] = storedItem;
    else currentSessionItems.push(storedItem);
    currentSessionItems.sort((a, b) => a.createdAt - b.createdAt);
    updateRecentHeader();
    updateStorageSummary();
    refreshRecentLibrary().catch(handleLibraryError);
    if (storedItem.kind === 'file') refreshFileLibrary().catch(handleLibraryError);
  } catch (error) {
    handleLibraryError(error);
  }
}

function handleLibraryError(error) {
  console.warn('NearChat local history:', error);
  if (!libraryErrorShown) {
    libraryErrorShown = true;
    showToast('Local history is unavailable. Sharing still works.');
  }
}

function showToast(message) {
  ui.toast.textContent = message;
  ui.toast.classList.add('show');
  clearTimeout(showToast.timer);
  showToast.timer = setTimeout(() => ui.toast.classList.remove('show'), 2300);
}

function setPairView(view) {
  ui.pairDance.hidden = view !== 'dance';
  ui.pairConnected.hidden = view !== 'connected';
}

function setPairMode(mode) {
  pairingMode = mode;
  const cameraMode = mode === 'discover' || mode === 'scan';
  ui.scanStage.hidden = !cameraMode;
  ui.qrStage.hidden = cameraMode;
  ui.discoveryCode.hidden = mode !== 'discover';
  ui.showCode.hidden = (mode !== 'discover' && mode !== 'scan') || peerRole !== null;
  ui.scanCode.hidden = mode !== 'offer' || peerRole !== 'initiator';
  if (!cameraMode) ui.opticalStage.dataset.detected = 'false';
}

function openPairing() {
  ui.overlay.hidden = false;
  document.body.style.overflow = 'hidden';
}

function closePairing() {
  stopScanner();
  stopSignalAnimation();
  ui.overlay.hidden = true;
  document.body.style.overflow = '';
}

function setPairingProgress(percent) {
  ui.pairProgress.style.width = `${Math.max(8, Math.min(100, percent))}%`;
}

function setPairingCopy(phase, title, detail, progress) {
  ui.pairPhase.textContent = phase;
  ui.pairStatusTitle.textContent = title;
  ui.pairStatus.textContent = detail;
  setPairingProgress(progress);
}

function ensureAudioContext() {
  if (audioContext) return audioContext;
  const AudioContextClass = window.AudioContext || window.webkitAudioContext;
  if (!AudioContextClass) return null;
  audioContext = new AudioContextClass();
  return audioContext;
}

async function primeAudio() {
  const context = ensureAudioContext();
  if (context?.state === 'suspended') await context.resume();
  return context;
}

function stopHandoffListener() {
  cancelAnimationFrame(handoffAudioRaf);
  handoffAudioRaf = 0;
  try { handoffAudioSource?.disconnect(); } catch {}
  handoffAudioSource = null;
  handoffAnalyser = null;
  handoffBins = null;
  handoffTargetBin = 0;
  handoffAudioStream?.getTracks().forEach(track => track.stop());
  handoffAudioStream = null;
  handoffOnFrames = 0;
  handoffOnsets = [];
  handoffLastHit = 0;
  handoffListenPurpose = '';
}

function clearDiscoveryTimer() {
  clearTimeout(discoveryTimer);
  discoveryTimer = 0;
}

function measureHandoffFrequency() {
  let peak = -Infinity;
  for (let index = handoffTargetBin - 1; index <= handoffTargetBin + 1; index++)
    peak = Math.max(peak, handoffBins[index]);
  const nearby = [];
  for (let index = Math.max(0, handoffTargetBin - 60);
      index <= Math.min(handoffBins.length - 1, handoffTargetBin + 60); index++)
    if (Math.abs(index - handoffTargetBin) > 4 && Number.isFinite(handoffBins[index]))
      nearby.push(handoffBins[index]);
  nearby.sort((a, b) => a - b);
  const floor = nearby.length ? nearby[nearby.length >> 1] : -120;
  return { peak, floor, score: Number.isFinite(peak) ? peak - floor : 0 };
}

function monitorHandoffTone() {
  if (!handoffAnalyser || !handoffAudioStream) return;
  handoffAudioRaf = requestAnimationFrame(monitorHandoffTone);
  const listeningForDiscovery = handoffListenPurpose === 'discovery' &&
    pairingMode === 'discover' && peerRole === null;
  const listeningForAnswer = handoffListenPurpose === 'answer' &&
    pairingMode === 'offer' && peerRole === 'initiator';
  if (!pairingActive || (!listeningForDiscovery && !listeningForAnswer)) return;
  handoffAnalyser.getFloatFrequencyData(handoffBins);
  const sample = measureHandoffFrequency();
  const toneOn = sample.score > HANDOFF_THRESHOLD_DB && sample.peak > HANDOFF_ABSOLUTE_MIN_DB;
  if (!toneOn) {
    handoffOnFrames = 0;
    return;
  }
  handoffOnFrames++;
  if (handoffOnFrames !== 2) return;
  const now = performance.now();
  handoffOnsets.push(now);
  const spacing = HANDOFF_BEEP_MS + HANDOFF_GAP_MS;
  const spacingMinimum = spacing * .5;
  const spacingMaximum = spacing * 2;
  if (handoffOnsets.length > 1 && now - handoffOnsets.at(-2) > spacingMaximum * 1.6)
    handoffOnsets = [now];
  if (handoffOnsets.length > HANDOFF_BEEP_COUNT)
    handoffOnsets = handoffOnsets.slice(-HANDOFF_BEEP_COUNT);
  ui.cameraState.dataset.state = 'warning';
  ui.cameraState.textContent = `${listeningForDiscovery ? 'Discovery' : 'Handoff'} beeps heard · ${handoffOnsets.length} / ${HANDOFF_BEEP_COUNT}`;
  if (handoffOnsets.length !== HANDOFF_BEEP_COUNT || now - handoffLastHit <= 2000) return;
  const gaps = handoffOnsets.slice(1).map((onset, index) => onset - handoffOnsets[index]);
  if (!gaps.every(gap => gap > spacingMinimum && gap < spacingMaximum)) {
    handoffOnsets = [now];
    return;
  }
  handoffLastHit = now;
  handoffTriggered = true;
  navigator.vibrate?.([45, 35, 80]);
  const purpose = handoffListenPurpose;
  stopHandoffListener();
  const action = purpose === 'discovery'
    ? showConnectionCode(true)
    : switchToAnswerScanner(false);
  action.catch(error => {
    if (pairingActive) failPairing(error);
  });
}

async function startHandoffListener(purpose) {
  stopHandoffListener();
  handoffTriggered = false;
  handoffListenPurpose = purpose;
  const context = await primeAudio();
  if (!context || !navigator.mediaDevices?.getUserMedia)
    throw new Error('Audio handoff is unavailable. Use the manual pairing controls.');
  let stream;
  try {
    stream = await navigator.mediaDevices.getUserMedia({
      audio: {
        echoCancellation: false,
        noiseSuppression: false,
        autoGainControl: false,
        channelCount: 1
      },
      video: false
    });
  } catch (error) {
    if (error?.name === 'NotAllowedError') {
      handoffListenPurpose = '';
      throw error;
    }
    try {
      stream = await navigator.mediaDevices.getUserMedia({ audio: true, video: false });
    } catch (fallbackError) {
      handoffListenPurpose = '';
      throw fallbackError;
    }
  }
  const stillValid = pairingActive && handoffListenPurpose === purpose && (
    (purpose === 'discovery' && pairingMode === 'discover' && peerRole === null) ||
    (purpose === 'answer' && (pairingMode === 'preparing' || pairingMode === 'offer') && peerRole === 'initiator')
  );
  if (!stillValid) {
    stream.getTracks().forEach(track => track.stop());
    return;
  }
  handoffAudioStream = stream;
  handoffAudioSource = context.createMediaStreamSource(stream);
  handoffAnalyser = context.createAnalyser();
  handoffAnalyser.fftSize = 4096;
  handoffAnalyser.smoothingTimeConstant = 0;
  handoffBins = new Float32Array(handoffAnalyser.frequencyBinCount);
  handoffTargetBin = Math.round(HANDOFF_TONE_HZ /
    (context.sampleRate / handoffAnalyser.fftSize));
  handoffAudioSource.connect(handoffAnalyser);
  handoffAudioRaf = requestAnimationFrame(monitorHandoffTone);
}

function stopHandoffBeeps() {
  clearInterval(handoffOutputTimer);
  handoffOutputTimer = 0;
  for (const oscillator of handoffOscillators) {
    try { oscillator.stop(); } catch {}
  }
  handoffOscillators.clear();
  handoffOutputPurpose = '';
}

async function playHandoffBeeps(purpose) {
  stopHandoffBeeps();
  const context = await primeAudio();
  if (!context) return false;
  handoffOutputPurpose = purpose;
  const playSequence = () => {
    const validDiscovery = purpose === 'discovery' && handoffOutputPurpose === purpose &&
      pairingMode === 'scan' && peerRole === null;
    const validAnswer = purpose === 'answer' && handoffOutputPurpose === purpose &&
      pairingMode === 'answer' && peerRole === 'responder';
    if (!pairingActive || (!validDiscovery && !validAnswer)) return;
    const startAt = context.currentTime + .06;
    const spacing = (HANDOFF_BEEP_MS + HANDOFF_GAP_MS) / 1000;
    for (let index = 0; index < HANDOFF_BEEP_COUNT; index++) {
      const toneStart = startAt + index * spacing;
      const toneEnd = toneStart + HANDOFF_BEEP_MS / 1000;
      const oscillator = context.createOscillator();
      const gain = context.createGain();
      oscillator.type = 'sine';
      oscillator.frequency.setValueAtTime(HANDOFF_TONE_HZ, toneStart);
      gain.gain.setValueAtTime(.0001, toneStart);
      gain.gain.exponentialRampToValueAtTime(.6, toneStart + .008);
      gain.gain.setValueAtTime(.6, Math.max(toneStart + .009, toneEnd - .015));
      gain.gain.exponentialRampToValueAtTime(.0001, toneEnd);
      oscillator.connect(gain).connect(context.destination);
      handoffOscillators.add(oscillator);
      oscillator.addEventListener('ended', () => handoffOscillators.delete(oscillator), { once: true });
      oscillator.start(toneStart);
      oscillator.stop(toneEnd + .02);
    }
  };
  playSequence();
  handoffOutputTimer = window.setInterval(playSequence, HANDOFF_PERIOD_MS);
  return true;
}

function setConnectionStatus(state, title, detail) {
  const unavailable = state === 'failed' && title === 'WebRTC unavailable';
  const visualState = unavailable
    ? 'unavailable'
    : state === 'connected'
      ? 'connected'
      : state === 'pairing' || state === 'stale'
        ? 'connecting'
        : 'offline';
  const label = unavailable
    ? 'Unavailable'
    : visualState === 'connected'
      ? 'Connected'
      : visualState === 'connecting'
        ? state === 'stale' ? 'Reconnecting' : 'Connecting'
        : 'Reconnect';
  ui.connectionNav.dataset.state = visualState;
  ui.connectionNavLabel.textContent = label;
  ui.connectionNav.setAttribute('aria-label', `${label}. ${detail}`);
  ui.connectionNav.title = `${title}. ${detail}`;
}

function channelIsOpen(channel) {
  return channel?.readyState === 'open';
}

function isConnected() {
  return channelIsOpen(chatChannel);
}

function updateComposer() {
  const connected = isConnected();
  ui.input.disabled = !connected;
  ui.input.placeholder = connected ? 'Message' : 'Connect to start chatting';
  ui.imageButton.disabled = !connected || !channelIsOpen(mediaChannel) || imageBusy;
  ui.send.disabled = !connected || imageBusy || (!ui.input.value.trim() && pendingImages.length === 0);
}

function formatBytes(bytes) {
  if (!Number.isFinite(bytes) || bytes <= 0) return '0 B';
  if (bytes < 1024) return `${Math.round(bytes)} B`;
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(bytes < 10 * 1024 ? 1 : 0)} KB`;
  return `${(bytes / 1024 / 1024).toFixed(1)} MB`;
}

const FILE_TYPE_ORDER = ['Images', 'Video', 'Audio', 'PDF', 'Archives', 'Documents', 'Spreadsheets', 'Other'];
const FILE_TYPE_LABEL = {
  Images: 'IMG', Video: 'VID', Audio: 'AUD', PDF: 'PDF', Archives: 'ZIP',
  Documents: 'DOC', Spreadsheets: 'XLS', Other: 'FILE'
};
const FILE_TYPE_COLOR = {
  Images: '#ef476f', Video: '#ff941a', Audio: '#9575e6', PDF: '#ed5353',
  Archives: '#858990', Documents: '#347fe0', Spreadsheets: '#23845b',
  Other: '#727983', Message: '#347fe0', Link: '#347fe0'
};

function fileType(item) {
  const mime = String(item.mime || item.blob?.type || '').toLowerCase();
  const name = String(item.name || '').toLowerCase();
  if (mime.startsWith('image/')) return 'Images';
  if (mime.startsWith('video/')) return 'Video';
  if (mime.startsWith('audio/')) return 'Audio';
  if (mime === 'application/pdf' || name.endsWith('.pdf')) return 'PDF';
  if (/zip|rar|7z|tar|gzip/.test(mime) || /\.(zip|rar|7z|tar|gz)$/.test(name)) return 'Archives';
  if (/spreadsheet|excel|csv/.test(mime) || /\.(xls|xlsx|csv|ods)$/.test(name)) return 'Spreadsheets';
  if (/text|word|document|presentation|powerpoint/.test(mime) || /\.(txt|rtf|doc|docx|odt|ppt|pptx)$/.test(name))
    return 'Documents';
  return 'Other';
}

function fileDate(timestamp) {
  return new Date(Number(timestamp) || Date.now()).toLocaleString([], {
    month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit'
  });
}

function createFileIcon(kind, label = FILE_TYPE_LABEL[kind] || 'FILE') {
  const namespace = 'http://www.w3.org/2000/svg';
  const icon = document.createElementNS(namespace, 'svg');
  icon.setAttribute('viewBox', '0 0 44 52');
  icon.setAttribute('aria-hidden', 'true');
  icon.classList.add('file-type-icon');
  const body = document.createElementNS(namespace, 'path');
  body.setAttribute('d', 'M7 1.5h20l10 10V46a4.5 4.5 0 0 1-4.5 4.5h-25A4.5 4.5 0 0 1 3 46V6A4.5 4.5 0 0 1 7 1.5Z');
  body.setAttribute('fill', FILE_TYPE_COLOR[kind] || FILE_TYPE_COLOR.Other);
  const fold = document.createElementNS(namespace, 'path');
  fold.setAttribute('d', 'M27 1.5v7a3 3 0 0 0 3 3h7');
  fold.setAttribute('fill', '#ffffff');
  fold.setAttribute('fill-opacity', '.34');
  const text = document.createElementNS(namespace, 'text');
  text.setAttribute('x', '20');
  text.setAttribute('y', '37');
  text.setAttribute('fill', '#fff');
  text.setAttribute('font-size', label.length > 4 ? '7' : '9');
  text.setAttribute('font-weight', '800');
  text.setAttribute('font-family', 'Arial, sans-serif');
  text.setAttribute('text-anchor', 'middle');
  text.textContent = label;
  icon.append(body, fold, text);
  return icon;
}

function updateStorageSummary() {
  const bytes = storedFiles.reduce((sum, item) => sum + (item.size || item.blob?.size || 0), 0);
  const count = storedFiles.length;
  ui.storageSummary.textContent = `${count} ${count === 1 ? 'file' : 'files'} · ${formatBytes(bytes)} stored in this browser`;
  ui.storedCount.textContent = String(count);
  ui.storedCount.hidden = count === 0;
  ui.clearLibrary.disabled = count === 0 && currentSessionItems.length === 0;
  updateStorageMeter();
}

async function updateStorageMeter() {
  const localBytes = storedFiles.reduce((sum, item) => sum + (item.size || item.blob?.size || 0), 0);
  try {
    const estimate = await navigator.storage?.estimate?.();
    if (!estimate?.quota) throw new Error('No quota estimate');
    const usage = Number(estimate.usage) || localBytes;
    const percent = Math.min(100, usage / estimate.quota * 100);
    ui.recentStorageText.textContent = `${formatBytes(usage)} of ${formatBytes(estimate.quota)} browser storage used`;
    ui.storageBarFill.style.width = `${usage ? Math.max(1, percent) : 0}%`;
  } catch {
    ui.recentStorageText.textContent = `${formatBytes(localBytes)} saved by NearChat on this device`;
    ui.storageBarFill.style.width = localBytes ? '4%' : '0';
  }
}

function createItemVisual(item, kind = fileType(item)) {
  if (kind === 'Images' && item.blob instanceof Blob) {
    const image = document.createElement('img');
    image.className = 'file-thumbnail';
    image.alt = '';
    const url = URL.createObjectURL(item.blob);
    const release = () => URL.revokeObjectURL(url);
    image.addEventListener('load', release, { once: true });
    image.addEventListener('error', release, { once: true });
    image.src = url;
    return image;
  }
  return createFileIcon(kind, kind === 'Message' ? 'MSG' : kind === 'Link' ? 'LINK' : undefined);
}

function recentGroup(timestamp) {
  const date = new Date(Number(timestamp) || Date.now());
  const today = new Date();
  const yesterday = new Date(today);
  yesterday.setDate(today.getDate() - 1);
  if (date.toDateString() === today.toDateString()) return 'Today';
  if (date.toDateString() === yesterday.toDateString()) return 'Yesterday';
  return date.toLocaleDateString([], { month: 'long', day: 'numeric', year: 'numeric' });
}

function recentItemName(item) {
  if (item.kind === 'file') return item.name || 'Shared file';
  const text = String(item.text || '').replace(/\s+/g, ' ').trim();
  return text || 'Message';
}

function recentItemKind(item) {
  if (item.kind === 'file') return fileType(item);
  return /^https?:\/\//i.test(String(item.text || '').trim()) ? 'Link' : 'Message';
}

function copyStoredText(item) {
  navigator.clipboard?.writeText?.(String(item.text || ''))
    .then(() => showToast('Message copied'))
    .catch(() => showToast('The message could not be copied.'));
}

function createItemMenu(item) {
  const menu = document.createElement('details');
  menu.className = 'item-menu';
  const summary = document.createElement('summary');
  summary.setAttribute('aria-label', `Actions for ${recentItemName(item)}`);
  summary.textContent = '•••';
  const choices = document.createElement('div');
  choices.className = 'item-menu-popover';
  const primary = document.createElement('button');
  primary.type = 'button';
  primary.textContent = item.kind === 'file' ? 'Save' : 'Copy';
  primary.addEventListener('click', () => {
    menu.open = false;
    if (item.kind === 'file') saveStoredFile(item);
    else copyStoredText(item);
  });
  const remove = document.createElement('button');
  remove.type = 'button';
  remove.className = 'delete-file';
  remove.textContent = 'Delete';
  remove.addEventListener('click', () => {
    menu.open = false;
    removeStoredFile(item);
  });
  choices.append(primary, remove);
  menu.append(summary, choices);
  return menu;
}

function renderRecentLibrary() {
  const query = ui.recentSearch.value.trim().toLowerCase();
  const items = recentItems
    .filter(item => recentItemName(item).toLowerCase().includes(query))
    .sort((a, b) => recentNewestFirst ? b.createdAt - a.createdAt : a.createdAt - b.createdAt);
  ui.recentItemList.replaceChildren();
  ui.recentItemList.hidden = items.length === 0;
  ui.recentLibraryEmpty.hidden = items.length !== 0;
  if (!items.length) {
    const title = ui.recentLibraryEmpty.querySelector('h2');
    const copy = ui.recentLibraryEmpty.querySelector('p');
    title.textContent = query ? 'No matching items' : 'Nothing shared yet';
    copy.textContent = query ? 'Try another search.' : 'Tap Send below to connect a nearby device.';
    return;
  }
  let group = '';
  for (const item of items) {
    const nextGroup = recentGroup(item.createdAt);
    if (nextGroup !== group) {
      group = nextGroup;
      const heading = document.createElement('h2');
      heading.className = 'recent-group-title';
      heading.textContent = group;
      ui.recentItemList.appendChild(heading);
    }
    const kind = recentItemKind(item);
    const row = document.createElement('article');
    row.className = 'recent-item-row';
    const copy = document.createElement('div');
    copy.className = 'recent-item-copy';
    const title = document.createElement('strong');
    title.textContent = recentItemName(item);
    const detail = document.createElement('small');
    detail.textContent = item.kind === 'file'
      ? `${fileDate(item.createdAt)} · ${formatBytes(item.size || item.blob?.size || 0)}`
      : `${fileDate(item.createdAt)} · ${kind}`;
    copy.append(title, detail);
    row.append(createItemVisual(item, kind), copy, createItemMenu(item));
    ui.recentItemList.appendChild(row);
  }
}

async function refreshRecentLibrary() {
  recentItems = await getRecentItems();
  renderRecentLibrary();
  updateStorageMeter();
}

function toggleStoredImageSelection(id) {
  if (selectedStoredImageIds.has(id)) selectedStoredImageIds.delete(id);
  else selectedStoredImageIds.add(id);
  renderFileBrowser();
}

function createFileAction(label, iconClass, extraClass = '') {
  const button = document.createElement('button');
  button.type = 'button';
  button.className = `file-action ${extraClass}`.trim();
  button.setAttribute('aria-label', label);
  button.title = label;
  const icon = document.createElement('span');
  icon.className = iconClass;
  icon.setAttribute('aria-hidden', 'true');
  button.appendChild(icon);
  return button;
}

function renderFileRows(files) {
  ui.storedFileList.replaceChildren();
  for (const item of files) {
    const kind = fileType(item);
    const row = document.createElement('article');
    row.className = 'stored-file-row';
    const visual = createItemVisual(item, kind);
    if (selectedFileType === 'Images' && kind === 'Images') {
      const toggle = document.createElement('button');
      toggle.type = 'button';
      toggle.className = 'selection-toggle';
      toggle.setAttribute('aria-label', `${selectedStoredImageIds.has(item.id) ? 'Unselect' : 'Select'} ${item.name || 'image'}`);
      toggle.setAttribute('aria-pressed', String(selectedStoredImageIds.has(item.id)));
      const checkbox = document.createElement('span');
      checkbox.className = 'checkbox-icon';
      checkbox.setAttribute('aria-hidden', 'true');
      toggle.appendChild(checkbox);
      toggle.addEventListener('click', () => toggleStoredImageSelection(item.id));
      row.append(toggle, visual);
    } else {
      row.appendChild(visual);
    }
    const copy = document.createElement('div');
    copy.className = 'stored-file-copy';
    const name = document.createElement('strong');
    name.textContent = item.name || 'Shared file';
    const detail = document.createElement('small');
    detail.textContent = `${fileDate(item.createdAt)} · ${formatBytes(item.size || item.blob.size)}`;
    copy.append(name, detail);
    const actions = document.createElement('div');
    actions.className = 'file-row-actions';
    actions.dataset.confirming = 'false';
    const download = createFileAction(`Download ${item.name || 'file'}`, 'download-icon');
    download.addEventListener('click', () => downloadStoredFile(item));
    const remove = createFileAction(`Delete ${item.name || 'file'}`, 'trash-icon', 'delete-file');
    const confirmation = document.createElement('div');
    confirmation.className = 'inline-delete-confirm';
    confirmation.hidden = true;
    const question = document.createElement('span');
    question.textContent = 'Delete?';
    const confirm = document.createElement('button');
    confirm.type = 'button';
    confirm.textContent = 'Delete';
    const cancel = document.createElement('button');
    cancel.type = 'button';
    cancel.className = 'cancel-delete';
    cancel.textContent = 'Cancel';
    remove.addEventListener('click', () => {
      actions.dataset.confirming = 'true';
      confirmation.hidden = false;
    });
    cancel.addEventListener('click', () => {
      actions.dataset.confirming = 'false';
      confirmation.hidden = true;
    });
    confirm.addEventListener('click', () => removeStoredFile(item));
    confirmation.append(question, confirm, cancel);
    actions.append(download, remove, confirmation);
    row.append(copy, actions);
    ui.storedFileList.appendChild(row);
  }
}

function updateImageSelectionTools() {
  const imageItems = storedFiles.filter(item => fileType(item) === 'Images');
  const validIds = new Set(imageItems.map(item => item.id));
  for (const id of selectedStoredImageIds)
    if (!validIds.has(id)) selectedStoredImageIds.delete(id);
  const visible = selectedFileType === 'Images' && !ui.fileSearch.value.trim();
  ui.imageSelectionTools.hidden = !visible;
  if (!visible) return;
  const count = selectedStoredImageIds.size;
  const allSelected = imageItems.length > 0 && count === imageItems.length;
  ui.selectedImageCount.textContent = String(count);
  ui.selectedImageCount.hidden = count === 0;
  ui.downloadSelectedImages.disabled = count === 0;
  ui.selectAllImages.dataset.state = allSelected ? 'all' : count > 0 ? 'some' : 'none';
  ui.selectAllImages.setAttribute('aria-pressed', String(allSelected));
  ui.selectAllImages.setAttribute('aria-label', allSelected ? 'Unselect all images' : 'Select all images');
}

function renderFileBrowser() {
  const query = ui.fileSearch.value.trim().toLowerCase();
  ui.fileTypeList.hidden = true;
  ui.storedFileList.hidden = true;
  ui.libraryEmpty.hidden = true;
  ui.imageSelectionTools.hidden = true;
  ui.backToTypes.hidden = !selectedFileType && !query;

  if (!storedFiles.length) {
    ui.filesTitle.textContent = 'Types';
    ui.libraryEmpty.querySelector('h2').textContent = 'No stored files';
    ui.libraryEmpty.querySelector('p').textContent = 'Images and files from your sessions will appear here.';
    ui.libraryEmpty.hidden = false;
    return;
  }

  if (query || selectedFileType) {
    const filtered = storedFiles.filter(item => {
      const matchesType = !selectedFileType || fileType(item) === selectedFileType;
      const matchesQuery = !query || String(item.name || '').toLowerCase().includes(query);
      return matchesType && matchesQuery;
    });
    ui.filesTitle.textContent = query ? 'Search' : selectedFileType;
    if (!filtered.length) {
      ui.libraryEmpty.querySelector('h2').textContent = 'No matching files';
      ui.libraryEmpty.querySelector('p').textContent = 'Try another search or file type.';
      ui.libraryEmpty.hidden = false;
      return;
    }
    renderFileRows(filtered);
    ui.storedFileList.hidden = false;
    updateImageSelectionTools();
    return;
  }

  ui.filesTitle.textContent = 'Types';
  ui.fileTypeList.replaceChildren();
  for (const kind of FILE_TYPE_ORDER) {
    const items = storedFiles.filter(item => fileType(item) === kind);
    if (!items.length) continue;
    const row = document.createElement('button');
    row.type = 'button';
    row.className = 'type-row';
    const copy = document.createElement('span');
    copy.className = 'type-copy';
    const title = document.createElement('strong');
    title.textContent = kind;
    const count = document.createElement('small');
    count.textContent = `${items.length} ${items.length === 1 ? 'item' : 'items'}`;
    copy.append(title, count);
    const size = document.createElement('span');
    size.className = 'type-size';
    size.textContent = formatBytes(items.reduce((sum, item) => sum + (item.size || item.blob.size), 0));
    const arrow = document.createElement('span');
    arrow.className = 'type-arrow';
    arrow.setAttribute('aria-hidden', 'true');
    arrow.textContent = '›';
    row.append(createFileIcon(kind), copy, size, arrow);
    row.addEventListener('click', () => {
      selectedFileType = kind;
      if (kind !== 'Images') selectedStoredImageIds.clear();
      renderFileBrowser();
    });
    ui.fileTypeList.appendChild(row);
  }
  ui.fileTypeList.hidden = false;
}

async function refreshFileLibrary() {
  storedFiles = await getStoredFiles();
  updateStorageSummary();
  renderFileBrowser();
}

function safeDownloadName(name, mime) {
  const cleaned = String(name || '').replace(/[\\/:*?"<>|]/g, '-').slice(0, 120);
  if (cleaned) return cleaned;
  return mime?.startsWith('image/') ? 'near-chat-image' : 'near-chat-file';
}

function storedItemFile(item) {
  const name = safeDownloadName(item.name, item.mime);
  return new File([item.blob], name, { type: item.mime || item.blob.type || 'application/octet-stream' });
}

function triggerFileDownload(file) {
  const url = URL.createObjectURL(file);
  const link = document.createElement('a');
  link.href = url;
  link.download = file.name;
  link.rel = 'noopener';
  document.body.appendChild(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 30000);
}

function downloadStoredFile(item) {
  try {
    triggerFileDownload(storedItemFile(item));
  } catch {
    showToast('The file could not be downloaded.');
  }
}

async function downloadSelectedImageFiles() {
  const selected = storedFiles.filter(item => selectedStoredImageIds.has(item.id) && fileType(item) === 'Images');
  if (!selected.length) return;
  try {
    const files = selected.map(storedItemFile);
    if (navigator.share && navigator.canShare?.({ files })) {
      await navigator.share({ files, title: `${files.length} NearChat images` });
    } else {
      files.forEach(triggerFileDownload);
      showToast(`${files.length} image${files.length === 1 ? '' : 's'} downloaded`);
    }
    selectedStoredImageIds.clear();
    renderFileBrowser();
  } catch (error) {
    if (error?.name !== 'AbortError') showToast('The selected images could not be downloaded.');
  }
}

async function saveStoredFile(item) {
  const file = storedItemFile(item);
  try {
    if (navigator.share && navigator.canShare?.({ files: [file] })) {
      await navigator.share({ files: [file], title: file.name });
      return;
    }
    triggerFileDownload(file);
  } catch (error) {
    if (error?.name !== 'AbortError') showToast('The file could not be saved.');
  }
}

async function removeStoredFile(item) {
  try {
    await deleteLibraryItem(item.id);
    selectedStoredImageIds.delete(item.id);
    if (currentSession?.id === item.sessionId) await renderStoredSession(currentSession);
    await Promise.all([refreshFileLibrary(), refreshRecentLibrary()]);
  } catch (error) {
    handleLibraryError(error);
  }
}

async function clearStoredLibrary() {
  if (!confirm('Clear the recent session and all stored files from this browser?')) return;
  try {
    await clearLibraryData();
    currentSessionItems = [];
    if (isConnected() && liveSessionId && currentSession) {
      currentSession = { ...currentSession, updatedAt: Date.now() };
      await putSession(currentSession);
    } else {
      currentSession = null;
      liveSessionId = '';
      liveSessionPromise = null;
    }
    clearRenderedMessages();
    setRecentEmpty();
    updateRecentHeader();
    selectedFileType = '';
    selectedStoredImageIds.clear();
    ui.fileSearch.value = '';
    await Promise.all([refreshFileLibrary(), refreshRecentLibrary()]);
    showToast('Local history cleared');
  } catch (error) {
    handleLibraryError(error);
  }
}

function formatDuration(milliseconds) {
  const seconds = Math.max(0, Math.floor(milliseconds / 1000));
  const minutes = Math.floor(seconds / 60);
  const hours = Math.floor(minutes / 60);
  if (hours) return `${String(hours).padStart(2, '0')}:${String(minutes % 60).padStart(2, '0')}:${String(seconds % 60).padStart(2, '0')}`;
  return `${String(minutes).padStart(2, '0')}:${String(seconds % 60).padStart(2, '0')}`;
}

function recordBytes(direction, count) {
  if (!Number.isFinite(count) || count <= 0) return;
  if (direction === 'sent') sentBytes += count;
  else receivedBytes += count;
  byteSamples.push({ time: performance.now(), direction, count });
}

function updateMetrics() {
  const now = performance.now();
  byteSamples = byteSamples.filter(sample => now - sample.time <= 5000);
  const sentRate = byteSamples
    .filter(sample => sample.direction === 'sent')
    .reduce((sum, sample) => sum + sample.count, 0) / 5;
  const receivedRate = byteSamples
    .filter(sample => sample.direction === 'received')
    .reduce((sum, sample) => sum + sample.count, 0) / 5;
  ui.metricRtt.textContent = lastRttMs ? `${Math.round(lastRttMs)} ms` : '—';
  ui.metricSent.textContent = formatBytes(sentBytes);
  ui.metricReceived.textContent = formatBytes(receivedBytes);
  ui.metricRate.textContent = `↑${formatBytes(sentRate)}/s · ↓${formatBytes(receivedRate)}/s`;
  ui.metricUptime.textContent = connectedAt ? formatDuration(Date.now() - connectedAt) : '00:00';
  ui.metricPath.textContent = connectionPath;
}

function resetMetrics() {
  sentBytes = 0;
  receivedBytes = 0;
  byteSamples = [];
  connectedAt = 0;
  lastPongAt = 0;
  lastRttMs = 0;
  connectionPath = '—';
  pendingPings.clear();
  updateMetrics();
}

function startMetricTimers() {
  clearInterval(metricsTimer);
  clearInterval(statsTimer);
  metricsTimer = setInterval(updateMetrics, 1000);
  statsTimer = setInterval(readConnectionStats, 3000);
  updateMetrics();
  readConnectionStats();
}

function stopMetricTimers() {
  clearInterval(metricsTimer);
  clearInterval(statsTimer);
  metricsTimer = 0;
  statsTimer = 0;
}

async function readConnectionStats() {
  if (!peer || peer.connectionState === 'closed') return;
  try {
    const reports = await peer.getStats();
    let pair = null;
    for (const report of reports.values()) {
      if (report.type === 'transport' && report.selectedCandidatePairId)
        pair = reports.get(report.selectedCandidatePairId);
      if (!pair && report.type === 'candidate-pair' && report.state === 'succeeded' && report.nominated)
        pair = report;
    }
    if (!pair) return;
    if (!lastRttMs && Number.isFinite(pair.currentRoundTripTime))
      lastRttMs = pair.currentRoundTripTime * 1000;
    const local = reports.get(pair.localCandidateId);
    const remote = reports.get(pair.remoteCandidateId);
    const candidateType = remote?.candidateType || local?.candidateType;
    const route = candidateType === 'host' ? 'LAN' : candidateType === 'srflx' ? 'direct' : candidateType === 'relay' ? 'relay' : 'peer';
    connectionPath = `${route}${local?.protocol ? ` · ${local.protocol}` : ''}`;
  } catch {}
}

function countStringBytes(value) {
  return encoder.encode(value).byteLength;
}

function sendChatPacket(payload) {
  if (!channelIsOpen(chatChannel)) throw new Error('The direct channel is not connected.');
  const text = JSON.stringify(payload);
  chatChannel.send(text);
  recordBytes('sent', countStringBytes(text));
}

function sendMediaPacket(payload) {
  if (!channelIsOpen(mediaChannel)) throw new Error('The image channel is not ready.');
  const text = JSON.stringify(payload);
  mediaChannel.send(text);
  recordBytes('sent', countStringBytes(text));
}

function sendHeartbeat() {
  if (!channelIsOpen(chatChannel)) return;
  const id = `${Date.now().toString(36)}-${++pingSequence}`;
  pendingPings.set(id, performance.now());
  try { sendChatPacket({ type: 'ping', id }); } catch {}
  const now = Date.now();
  if (lastPongAt && now - lastPongAt > HEARTBEAT_STALE_MS)
    setConnectionStatus('stale', 'Connection quiet', 'Waiting for the other device to respond…');
  for (const [pendingId, started] of pendingPings)
    if (performance.now() - started > HEARTBEAT_STALE_MS * 2) pendingPings.delete(pendingId);
}

function startHeartbeat() {
  clearInterval(heartbeatTimer);
  lastPongAt = Date.now();
  sendHeartbeat();
  heartbeatTimer = setInterval(sendHeartbeat, HEARTBEAT_MS);
}

function stopHeartbeat() {
  clearInterval(heartbeatTimer);
  heartbeatTimer = 0;
  pendingPings.clear();
}

function setConnectedUi() {
  if (!connectedAt) connectedAt = Date.now();
  lastPongAt = Date.now();
  pairingActive = false;
  buildingSignal = false;
  clearDiscoveryTimer();
  stopScanner();
  stopHandoffListener();
  stopHandoffBeeps();
  stopSignalAnimation();
  resetSignalDecoder();
  document.body.dataset.connected = 'true';
  showAppView('send');
  ensureLiveSession().catch(handleLibraryError);
  setConnectionStatus('connected', 'Live connection', 'Heartbeat active · messages send directly.');
  navigator.vibrate?.([70, 50, 130]);
  startHeartbeat();
  startMetricTimers();
  updateComposer();
  if (!ui.overlay.hidden) {
    setPairView('connected');
    setTimeout(() => {
      if (isConnected()) closePairing();
    }, 900);
  }
}

function updateConnectionFromPeer() {
  if (!peer) return;
  const state = peer.connectionState;
  if (state === 'connected') {
    if (channelIsOpen(chatChannel)) setConnectedUi();
    else {
      stopHeartbeat();
      setConnectionStatus('stale', 'Chat channel closed', 'Press Connect to pair the devices again.');
      if (currentView === 'send') showAppView('recent');
      updateComposer();
    }
    return;
  }
  if (state === 'connecting' || state === 'new') {
    setConnectionStatus('pairing', 'Connecting', 'Finishing the direct WebRTC handshake…');
    return;
  }
  if (state === 'disconnected') {
    setConnectionStatus('stale', 'Reconnecting', 'The peer route is temporarily unavailable.');
    return;
  }
  if (state === 'failed') {
    stopHeartbeat();
    setConnectionStatus('failed', 'Connection failed', 'Press Connect to pair the devices again.');
    if (currentView === 'send') showAppView('recent');
    updateComposer();
    return;
  }
  if (state === 'closed') {
    setConnectionStatus('offline', 'Not connected', 'Pair two nearby devices to begin.');
    if (currentView === 'send') showAppView('recent');
    updateComposer();
  }
}

function bindChatChannel(channel) {
  chatChannel = channel;
  chatChannel.onopen = () => setConnectedUi();
  chatChannel.onclose = updateConnectionFromPeer;
  chatChannel.onerror = () => setConnectionStatus('stale', 'Channel error', 'Trying to keep the peer connection alive…');
  chatChannel.onmessage = event => {
    if (typeof event.data !== 'string') return;
    recordBytes('received', countStringBytes(event.data));
    let packet;
    try { packet = JSON.parse(event.data); } catch { return; }
    if (packet?.type === 'ping' && typeof packet.id === 'string') {
      try { sendChatPacket({ type: 'pong', id: packet.id }); } catch {}
      return;
    }
    if (packet?.type === 'pong' && typeof packet.id === 'string') {
      const started = pendingPings.get(packet.id);
      if (started != null) {
        lastRttMs = performance.now() - started;
        pendingPings.delete(packet.id);
      }
      lastPongAt = Date.now();
      setConnectionStatus('connected', 'Live connection', `Heartbeat active · ${Math.round(lastRttMs || 0)} ms round trip.`);
      return;
    }
    if (packet?.type === 'message' && typeof packet.text === 'string') {
      const text = packet.text.slice(0, 2000);
      const timestamp = Number(packet.timestamp) || Date.now();
      const id = typeof packet.id === 'string' ? packet.id : randomId();
      appendTextMessage({ mine: false, text, timestamp });
      persistLiveItem({ id, kind: 'text', mine: false, text, createdAt: timestamp });
    }
  };
}

function bindMediaChannel(channel) {
  mediaChannel = channel;
  mediaChannel.binaryType = 'arraybuffer';
  mediaChannel.onopen = updateComposer;
  mediaChannel.onclose = updateComposer;
  mediaChannel.onerror = () => showToast('The image channel had a problem.');
  mediaChannel.onmessage = handleMediaPacket;
}

function setupPeer(role) {
  peerRole = role;
  peer = new RTCPeerConnection({ iceServers: [], bundlePolicy: 'max-bundle' });
  peer.onconnectionstatechange = updateConnectionFromPeer;
  peer.oniceconnectionstatechange = updateConnectionFromPeer;
  peer.ondatachannel = event => {
    if (event.channel.label === 'near-chat') bindChatChannel(event.channel);
    if (event.channel.label === 'near-media') bindMediaChannel(event.channel);
  };
  if (role === 'initiator') {
    bindChatChannel(peer.createDataChannel('near-chat', { ordered: true }));
    bindMediaChannel(peer.createDataChannel('near-media', { ordered: true }));
  }
  setConnectionStatus('pairing', 'Pairing devices', 'Follow the QR handoff shown on both devices.');
  updateComposer();
  return peer;
}

function teardownPeer({ keepMetrics = true } = {}) {
  stopHeartbeat();
  stopMetricTimers();
  try { chatChannel?.close(); } catch {}
  try { mediaChannel?.close(); } catch {}
  try { peer?.close(); } catch {}
  peer = null;
  chatChannel = null;
  mediaChannel = null;
  peerRole = null;
  incomingImage = null;
  document.body.dataset.connected = 'false';
  liveSessionId = '';
  liveSessionPromise = null;
  setRecentEmpty();
  updateRecentHeader();
  if (currentView === 'send') showAppView('recent');
  if (!keepMetrics) resetMetrics();
  updateComposer();
}

function disconnectPeer() {
  teardownPeer();
  stopSignalAnimation();
  stopScanner();
  stopHandoffListener();
  stopHandoffBeeps();
  clearDiscoveryTimer();
  resetSignalDecoder();
  pairingActive = false;
  buildingSignal = false;
  pairingSession = '';
  pairingSessionNumber = 0;
  signalFrames = [];
  setConnectionStatus('offline', 'Not connected', 'Pair two nearby devices to begin.');
  showAppView('recent');
  showToast('Direct connection closed');
}

function bytesToBase64Url(bytes) {
  let binary = '';
  for (let index = 0; index < bytes.length; index += 0x8000)
    binary += String.fromCharCode(...bytes.subarray(index, index + 0x8000));
  return btoa(binary).replaceAll('+', '-').replaceAll('/', '_').replace(/=+$/g, '');
}

function base64UrlToBytes(value) {
  const base64 = value.replaceAll('-', '+').replaceAll('_', '/');
  const padded = base64.padEnd(Math.ceil(base64.length / 4) * 4, '=');
  const binary = atob(padded);
  const bytes = new Uint8Array(binary.length);
  for (let index = 0; index < binary.length; index++) bytes[index] = binary.charCodeAt(index);
  return bytes;
}

async function transformBytes(bytes, Transform) {
  const stream = new Blob([bytes]).stream().pipeThrough(new Transform('gzip'));
  return new Uint8Array(await new Response(stream).arrayBuffer());
}

function randomHex(byteCount = 8) {
  return Array.from(crypto.getRandomValues(new Uint8Array(byteCount)), byte =>
    byte.toString(16).padStart(2, '0')).join('');
}

function ensureRaptor() {
  if (!raptorReady) {
    raptorReady = initRaptor().catch(error => {
      raptorReady = null;
      throw error;
    });
  }
  return raptorReady;
}

const crcTable = (() => {
  const table = new Uint32Array(256);
  for (let index = 0; index < table.length; index++) {
    let value = index;
    for (let bit = 0; bit < 8; bit++)
      value = value & 1 ? 0xedb88320 ^ (value >>> 1) : value >>> 1;
    table[index] = value >>> 0;
  }
  return table;
})();

function crc32(bytes) {
  let value = 0xffffffff;
  for (const byte of bytes) value = crcTable[(value ^ byte) & 0xff] ^ (value >>> 8);
  return (value ^ 0xffffffff) >>> 0;
}

function hasMagic(bytes, magic) {
  return magic.every((byte, index) => bytes[index] === byte);
}

function buildRaptorFrame({ session, encodedLength, packet }) {
  const total = RAPTOR_HEADER_BYTES + packet.length + RAPTOR_CRC_BYTES;
  const output = new Uint8Array(total);
  const view = new DataView(output.buffer);
  output.set(RAPTOR_FRAME_MAGIC, 0);
  view.setUint32(4, session >>> 0, false);
  view.setUint32(8, encodedLength >>> 0, false);
  view.setUint16(12, RAPTOR_TRANSPORT_BYTES, false);
  view.setUint16(14, packet.length, false);
  output.set(packet, RAPTOR_HEADER_BYTES);
  view.setUint32(total - RAPTOR_CRC_BYTES,
    crc32(output.subarray(0, total - RAPTOR_CRC_BYTES)), false);
  return output;
}

function parseRaptorFrame(bytes) {
  if (bytes.length < RAPTOR_HEADER_BYTES + RAPTOR_CRC_BYTES ||
      !hasMagic(bytes, RAPTOR_FRAME_MAGIC)) return null;
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const session = view.getUint32(4, false);
  const encodedLength = view.getUint32(8, false);
  const transportSize = view.getUint16(12, false);
  const packetLength = view.getUint16(14, false);
  const expectedLength = RAPTOR_HEADER_BYTES + packetLength + RAPTOR_CRC_BYTES;
  if (expectedLength !== bytes.length || encodedLength < 2 || encodedLength > MAX_SIGNAL_BYTES ||
      transportSize !== RAPTOR_TRANSPORT_BYTES || packetLength > transportSize) return null;
  const expectedCrc = view.getUint32(bytes.length - RAPTOR_CRC_BYTES, false);
  if (crc32(bytes.subarray(0, bytes.length - RAPTOR_CRC_BYTES)) !== expectedCrc) return null;
  return {
    session,
    encodedLength,
    transportSize,
    packet: bytes.slice(RAPTOR_HEADER_BYTES, RAPTOR_HEADER_BYTES + packetLength)
  };
}

function packetKey(packet) {
  if (packet.length < 4) return '';
  return Array.from(packet.subarray(0, 4), byte =>
    byte.toString(16).padStart(2, '0')).join('');
}

function sourceSymbolEstimate(encodedLength, transportSize) {
  return Math.max(1, Math.ceil(encodedLength / Math.max(1, transportSize - 4)));
}

async function encodeSignalPayload(kind, description) {
  const raw = encoder.encode(JSON.stringify({
    version: 2,
    session: pairingSession,
    kind,
    description: { type: description.type, sdp: description.sdp }
  }));
  let body = raw;
  let compressed = false;
  if ('CompressionStream' in window) {
    try {
      const zipped = await transformBytes(raw, CompressionStream);
      if (zipped.length < raw.length) {
        body = zipped;
        compressed = true;
      }
    } catch {}
  }
  const payload = new Uint8Array(body.length + 1);
  payload[0] = compressed ? 1 : 0;
  payload.set(body, 1);
  return payload;
}

async function decodeSignalPayload(bytes, expectedKind) {
  if (bytes.length < 2 || bytes.length > MAX_SIGNAL_BYTES) throw new Error('The optical handshake was invalid.');
  let body = bytes.subarray(1);
  if (bytes[0] === 1) {
    if (!('DecompressionStream' in window)) throw new Error('This browser cannot decompress the pairing signal.');
    body = await transformBytes(body, DecompressionStream);
  } else if (bytes[0] !== 0) {
    throw new Error('The optical handshake was invalid.');
  }
  const payload = JSON.parse(decoder.decode(body));
  const description = payload?.description;
  if (payload?.version !== 2 || payload.session !== pairingSession || payload.kind !== expectedKind ||
      !description || typeof description.sdp !== 'string' || description.sdp.length > 100000 ||
      (expectedKind === 'O' && description.type !== 'offer') ||
      (expectedKind === 'A' && description.type !== 'answer'))
    throw new Error('The optical handshake did not match this pairing.');
  return description;
}

async function buildSignalFrames(kind, description) {
  const payload = await encodeSignalPayload(kind, description);
  if (payload.length > MAX_SIGNAL_BYTES) throw new Error('The WebRTC handshake is too large to display.');
  await ensureRaptor();
  const packets = Array.from(
    encode_packets(payload, RAPTOR_TRANSPORT_BYTES, RAPTOR_REPAIR_PERCENT),
    packet => new Uint8Array(packet)
  );
  return packets.map(packet => `${SIGNAL_FRAME_PREFIX}|${kind}|${bytesToBase64Url(buildRaptorFrame({
    session: pairingSessionNumber,
    encodedLength: payload.length,
    packet
  }))}`);
}

function renderQr(text, canvas = ui.qrCanvas) {
  const qr = QRCode.create([{ data: text, mode: 'byte' }], { errorCorrectionLevel: 'L' });
  const quiet = 4;
  const modules = qr.modules.size;
  const dimension = modules + quiet * 2;
  const size = canvas === ui.discoveryQrCanvas ? 150 : 330;
  const maximum = canvas === ui.discoveryQrCanvas ? 300 : 660;
  const target = Math.min(maximum, Math.max(size, Math.round((window.devicePixelRatio || 1) * size)));
  const scale = Math.max(2, Math.floor(target / dimension));
  const pixels = dimension * scale;
  const context = canvas.getContext('2d');
  canvas.width = pixels;
  canvas.height = pixels;
  context.fillStyle = '#ffffff';
  context.fillRect(0, 0, pixels, pixels);
  context.fillStyle = '#153f33';
  for (let row = 0; row < modules; row++) {
    for (let column = 0; column < modules; column++) {
      if (!qr.modules.data[row * modules + column]) continue;
      context.fillRect((column + quiet) * scale, (row + quiet) * scale, scale, scale);
    }
  }
}

function stopSignalAnimation() {
  clearInterval(signalTimer);
  signalTimer = 0;
}

function paintSignalFrame() {
  if (!signalFrames.length) return;
  renderQr(signalFrames[signalFrameIndex]);
  signalFrameIndex = (signalFrameIndex + 1) % signalFrames.length;
}

function startSignalAnimation() {
  stopSignalAnimation();
  signalFrameIndex = 0;
  paintSignalFrame();
  if (signalFrames.length > 1) signalTimer = setInterval(paintSignalFrame, SIGNAL_FRAME_MS);
}

function displaySignalFrames(frames, kind) {
  signalKind = kind;
  signalFrames = frames;
  startSignalAnimation();
}

function waitForIceGathering(connection, timeout = 5000) {
  if (connection.iceGatheringState === 'complete') return Promise.resolve();
  return new Promise(resolve => {
    const finish = () => {
      clearTimeout(timer);
      connection.removeEventListener('icegatheringstatechange', check);
      resolve();
    };
    const check = () => {
      if (connection.iceGatheringState === 'complete') finish();
    };
    const timer = setTimeout(finish, timeout);
    connection.addEventListener('icegatheringstatechange', check);
  });
}

function resetSignalDecoder() {
  try { signalDecoder?.free(); } catch {}
  signalDecoder = null;
  signalDecodeKind = '';
  signalSeenPackets = new Set();
  signalAcceptedPackets = 0;
  signalSourceSymbols = 0;
  signalFinishing = false;
}

function parseSignalFrame(raw) {
  const match = typeof raw === 'string' && raw.length < 1200
    ? /^NCS1\|([OA])\|([A-Za-z0-9_-]+)$/.exec(raw)
    : null;
  if (!match) return null;
  let bytes;
  try { bytes = base64UrlToBytes(match[2]); } catch { return null; }
  const frame = parseRaptorFrame(bytes);
  return frame ? { kind: match[1], frame } : null;
}

function parseDiscoveryFrame(raw) {
  const match = typeof raw === 'string' ? /^NCH1\|([0-9a-f]{16})$/.exec(raw) : null;
  return match?.[1] || '';
}

async function becomeDiscoveryScanner() {
  if (!pairingActive || pairingMode !== 'discover' || peerRole || !remoteDiscoveryId) return;
  clearDiscoveryTimer();
  stopHandoffListener();
  setPairMode('scan');
  setPairingCopy('1 · Device found', 'Keep the other QR in view',
    'Sending three beeps so the other device knows to show its connection code.', 18);
  ui.cameraState.dataset.state = 'active';
  ui.cameraState.textContent = 'Other device found · requesting its connection code';
  await playHandoffBeeps('discovery');
}

function handleDiscoveryFrame(raw) {
  if (!pairingActive || pairingMode !== 'discover' || peerRole) return;
  const remoteId = parseDiscoveryFrame(raw);
  if (!remoteId || remoteId === localDiscoveryId || remoteDiscoveryId) return;
  remoteDiscoveryId = remoteId;
  clearDiscoveryTimer();
  ui.alignmentScore.textContent = 'Nearby device found';
  ui.alignmentHint.textContent = 'Hold both devices steady while NearChat chooses who shares first.';
  setPairingCopy('1 · Device found', 'Choosing the first sharing device',
    'Keep both screens visible. The three-beep handoff starts automatically.', 14);
  const preferredScanner = localDiscoveryId < remoteDiscoveryId;
  discoveryTimer = window.setTimeout(() => {
    becomeDiscoveryScanner().catch(error => {
      if (pairingActive) failPairing(error);
    });
  }, preferredScanner ? 140 : 1500);
}

async function createOpticalOffer() {
  if (!pairingActive || buildingSignal) return;
  buildingSignal = true;
  setPairingCopy('2 · Preparing your code', 'Creating the first connection code',
    'The other device should remain in camera mode.', 24);
  try {
    const connection = setupPeer('initiator');
    const offer = await connection.createOffer();
    await connection.setLocalDescription(offer);
    await waitForIceGathering(connection);
    if (!pairingActive || peer !== connection) return;
    const frames = await buildSignalFrames('O', connection.localDescription);
    displaySignalFrames(frames, 'offer');
    setPairMode('offer');
    ui.cameraState.dataset.state = 'active';
    ui.cameraState.textContent = handoffAudioStream
      ? 'Showing code · listening for three beeps'
      : 'Showing code · use Scan answer now after the beeps';
    setPairingCopy('2 · Show this code', 'Point the other camera here',
      'After it reads the code, it will beep. This device will then open its camera automatically.', 36);
  } catch (error) {
    failPairing(error);
  } finally {
    buildingSignal = false;
  }
}

async function createOpticalAnswer(description) {
  if (!pairingActive || buildingSignal || peerRole !== 'responder') return;
  buildingSignal = true;
  setPairingCopy('3 · Preparing the answer', 'First code received',
    'Keep the devices close. This device is preparing the return code.', 68);
  try {
    const connection = peer;
    await connection.setRemoteDescription(description);
    const answer = await connection.createAnswer();
    await connection.setLocalDescription(answer);
    await waitForIceGathering(connection);
    if (!pairingActive || peer !== connection) return;
    const frames = await buildSignalFrames('A', connection.localDescription);
    stopScanner();
    displaySignalFrames(frames, 'answer');
    setPairMode('answer');
    ui.cameraState.dataset.state = 'active';
    ui.cameraState.textContent = 'Answer ready · playing handoff beeps';
    setPairingCopy('3 · Show the answer', 'Turn this code toward the first device',
      'Three beeps tell the first device to open its camera. Hold this screen steady.', 82);
    playHandoffBeeps('answer').catch(() => {});
  } catch (error) {
    failPairing(error);
  } finally {
    buildingSignal = false;
  }
}

async function showConnectionCode(automatic = false) {
  if (!pairingActive || peerRole || buildingSignal) return;
  clearDiscoveryTimer();
  stopHandoffBeeps();
  stopHandoffListener();
  stopScanner();
  pairingSession = randomHex(4);
  pairingSessionNumber = Number.parseInt(pairingSession, 16) >>> 0;
  peerRole = 'initiator';
  setPairMode('preparing');
  renderQr(`NCS0|${pairingSession}|PREPARING`);
  ui.cameraState.dataset.state = 'starting';
  ui.cameraState.textContent = 'Preparing code · requesting beep detection';
  try {
    await startHandoffListener('answer');
  } catch {
    ui.cameraState.dataset.state = 'warning';
    ui.cameraState.textContent = 'Beep detection unavailable · manual scan remains available';
  }
  if (automatic) {
    setPairingCopy('2 · Preparing your code', 'Three discovery beeps received',
      'This device was chosen to share the first connection code.', 24);
  }
  await createOpticalOffer();
}

async function switchToAnswerScanner(manual = true) {
  if (!pairingActive || peerRole !== 'initiator' || pairingMode !== 'offer') return;
  handoffTriggered = true;
  stopHandoffListener();
  stopSignalAnimation();
  setPairMode('scan');
  resetCameraFeedback();
  setPairingCopy('3 · Scan the answer', manual ? 'Open the answer scanner' : 'Handoff beeps received',
    'Point this camera at the answer code now showing on the other device.', 72);
  ui.cameraState.dataset.state = 'starting';
  ui.cameraState.textContent = 'Starting main camera…';
  await startMainCamera();
}

async function finishSignal(kind, bytes) {
  const description = await decodeSignalPayload(bytes, kind);
  if (kind === 'O') {
    if (peerRole !== 'responder' || !peer) return;
    await createOpticalAnswer(description);
    return;
  }
  if (peerRole !== 'initiator' || !peer) return;
  setPairingCopy('4 · Opening the channel', 'Answer received',
    'The QR handoff is complete. Opening WebRTC now…', 94);
  stopScanner();
  stopSignalAnimation();
  await peer.setRemoteDescription(description);
  setConnectionStatus('pairing', 'Connecting', 'Opening the persistent data channel…');
}

async function ingestSignalFrame(raw) {
  if (!pairingActive || signalFinishing) return;
  const parsed = parseSignalFrame(raw);
  if (!parsed) return;
  if (!pairingSession) {
    if (parsed.kind !== 'O' || peerRole) return;
    clearDiscoveryTimer();
    stopHandoffListener();
    stopHandoffBeeps();
    pairingSessionNumber = parsed.frame.session >>> 0;
    pairingSession = pairingSessionNumber.toString(16).padStart(8, '0');
    setupPeer('responder');
    setPairMode('scan');
    setPairingCopy('2 · Reading the first code', 'Connection code found',
      'Hold the camera steady while the complete offer is collected.', 30);
  }
  const expectedKind = peerRole === 'initiator' ? 'A' : peerRole === 'responder' ? 'O' : '';
  if (!expectedKind || parsed.kind !== expectedKind || parsed.frame.session !== pairingSessionNumber) return;

  if (!signalDecoder || signalDecodeKind !== parsed.kind) {
    resetSignalDecoder();
    signalDecodeKind = parsed.kind;
    signalSourceSymbols = sourceSymbolEstimate(parsed.frame.encodedLength, parsed.frame.transportSize);
    try { signalDecoder = new RaptorQDecoder(parsed.frame.encodedLength, parsed.frame.transportSize); }
    catch { resetSignalDecoder(); return; }
  }

  const key = packetKey(parsed.frame.packet);
  if (!key || signalSeenPackets.has(key)) return;
  signalSeenPackets.add(key);
  signalAcceptedPackets++;
  const ratio = Math.min(1, signalAcceptedPackets / Math.max(1, signalSourceSymbols));
  const base = parsed.kind === 'O' ? 42 : 82;
  setPairingProgress(base + ratio * 10);
  ui.pairStatus.textContent = `Reading ${parsed.kind === 'O' ? 'offer' : 'answer'} light frames · ${signalAcceptedPackets} received`;

  try {
    const decoded = signalDecoder.push(parsed.frame.packet);
    if (!decoded) return;
    signalFinishing = true;
    const payload = new Uint8Array(decoded);
    try { signalDecoder.free(); } catch {}
    signalDecoder = null;
    await finishSignal(parsed.kind, payload);
    resetSignalDecoder();
  } catch (error) {
    resetSignalDecoder();
    if (pairingActive) failPairing(error);
  }
}

async function consumeScannedValue(raw) {
  if (typeof raw !== 'string') return;
  if (raw.startsWith(`${DISCOVERY_FRAME_PREFIX}|`)) {
    handleDiscoveryFrame(raw);
    return;
  }
  if (raw.startsWith(`${SIGNAL_FRAME_PREFIX}|`)) await ingestSignalFrame(raw);
}

async function chooseBarcodeDecoder() {
  barcodeDetector = null;
  if (!('BarcodeDetector' in window)) return;
  try {
    const formats = await BarcodeDetector.getSupportedFormats();
    if (formats.includes('qr_code')) barcodeDetector = new BarcodeDetector({ formats: ['qr_code'] });
  } catch {}
}

function captureScannerFrame() {
  const width = ui.scannerVideo.videoWidth;
  const height = ui.scannerVideo.videoHeight;
  if (!width || !height) return null;
  const scale = Math.min(1, Math.sqrt(MAX_SCAN_PIXELS / (width * height)));
  const drawWidth = Math.max(1, Math.round(width * scale));
  const drawHeight = Math.max(1, Math.round(height * scale));
  const canvas = ui.scannerCanvas;
  if (canvas.width !== drawWidth || canvas.height !== drawHeight) {
    canvas.width = drawWidth;
    canvas.height = drawHeight;
  }
  const context = canvas.getContext('2d', { willReadFrequently: true });
  context.drawImage(ui.scannerVideo, 0, 0, drawWidth, drawHeight);
  return context.getImageData(0, 0, drawWidth, drawHeight);
}

function isNearChatOpticalFrame(value) {
  return typeof value === 'string' && (
    value.startsWith(`${DISCOVERY_FRAME_PREFIX}|`) ||
    value.startsWith(`${SIGNAL_FRAME_PREFIX}|`)
  );
}

function barcodeCorners(result) {
  if (Array.isArray(result?.cornerPoints) && result.cornerPoints.length >= 4)
    return result.cornerPoints.map(point => ({ x: point.x, y: point.y }));
  const box = result?.boundingBox;
  if (!box) return null;
  return [
    { x: box.x, y: box.y },
    { x: box.x + box.width, y: box.y },
    { x: box.x + box.width, y: box.y + box.height },
    { x: box.x, y: box.y + box.height }
  ];
}

function jsQrCorners(result) {
  const location = result?.location;
  if (!location) return null;
  const points = [
    location.topLeftCorner,
    location.topRightCorner,
    location.bottomRightCorner,
    location.bottomLeftCorner
  ];
  return points.every(point => Number.isFinite(point?.x) && Number.isFinite(point?.y)) ? points : null;
}

function resetCameraFeedback() {
  targetLastSeen = 0;
  lastDetectionFeedback = 0;
  ui.opticalStage.dataset.detected = 'false';
  ui.alignmentScore.textContent = 'Looking for a NearChat code';
  ui.alignmentHint.textContent = 'Point the main camera at the other screen.';
}

function markTargetLost() {
  if (performance.now() - targetLastSeen < 700) return;
  ui.opticalStage.dataset.detected = 'false';
  ui.alignmentScore.textContent = 'No QR code in view';
  ui.alignmentHint.textContent = 'Move the connection code into the centre frame.';
}

function positionDetectedOutline({ left, right, top, bottom }, frameWidth, frameHeight) {
  const stage = ui.opticalStage.getBoundingClientRect();
  if (!stage.width || !stage.height || !frameWidth || !frameHeight) return;
  const scale = Math.min(stage.width / frameWidth, stage.height / frameHeight);
  const renderedWidth = frameWidth * scale;
  const renderedHeight = frameHeight * scale;
  const offsetX = (stage.width - renderedWidth) / 2;
  const offsetY = (stage.height - renderedHeight) / 2;

  ui.opticalStage.style.setProperty('--detected-left', `${offsetX + left * scale}px`);
  ui.opticalStage.style.setProperty('--detected-top', `${offsetY + top * scale}px`);
  ui.opticalStage.style.setProperty('--detected-width', `${(right - left) * scale}px`);
  ui.opticalStage.style.setProperty('--detected-height', `${(bottom - top) * scale}px`);
}

function updateCameraFeedback(points, frameWidth = ui.scannerVideo.videoWidth, frameHeight = ui.scannerVideo.videoHeight) {
  if (!points?.length || !frameWidth || !frameHeight) return;
  const xs = points.map(point => point.x);
  const ys = points.map(point => point.y);
  const left = Math.min(...xs);
  const right = Math.max(...xs);
  const top = Math.min(...ys);
  const bottom = Math.max(...ys);
  const normalizedX = ((left + right) / 2) / frameWidth;
  const normalizedY = ((top + bottom) / 2) / frameHeight;
  const qrRatio = Math.max((right - left) / frameWidth, (bottom - top) / frameHeight);
  if (![normalizedX, normalizedY, qrRatio].every(Number.isFinite) || qrRatio <= 0) return;

  const now = performance.now();
  const reacquired = !targetLastSeen || now - targetLastSeen > 1000;
  targetLastSeen = now;
  ui.opticalStage.dataset.detected = 'true';
  positionDetectedOutline({ left, right, top, bottom }, frameWidth, frameHeight);

  const centreError = Math.hypot(normalizedX - .5, normalizedY - .5);
  if (qrRatio < .1) {
    ui.alignmentScore.textContent = 'QR detected · move closer';
    ui.alignmentHint.textContent = 'Make the code larger inside the camera view.';
  } else if (qrRatio > .68) {
    ui.alignmentScore.textContent = 'QR detected · move back';
    ui.alignmentHint.textContent = 'Keep the complete code visible.';
  } else if (centreError > .3) {
    ui.alignmentScore.textContent = 'QR detected · centre it';
    ui.alignmentHint.textContent = 'Move the green box into the centre frame.';
  } else {
    ui.alignmentScore.textContent = 'Code detected · hold still';
    ui.alignmentHint.textContent = 'The optical handshake is being received.';
  }

  if (reacquired && (!lastDetectionFeedback || now - lastDetectionFeedback > 1800)) {
    lastDetectionFeedback = now;
    navigator.vibrate?.(45);
  }
}

function scannerLoop(timestamp) {
  const generation = scannerGeneration;
  scannerRaf = requestAnimationFrame(scannerLoop);
  if (!cameraStream || scannerBusy || timestamp - scannerLastDecode < 45) return;
  scannerLastDecode = timestamp;
  scannerBusy = true;
  if (barcodeDetector) {
    barcodeDetector.detect(ui.scannerVideo)
      .then(results => {
        if (generation !== scannerGeneration) return;
        const nearChatResults = results.filter(result => isNearChatOpticalFrame(result.rawValue));
        if (nearChatResults.length) {
          updateCameraFeedback(barcodeCorners(nearChatResults[0]));
          nearChatResults.forEach(result => consumeScannedValue(result.rawValue).catch(() => {}));
        } else markTargetLost();
      })
      .catch(() => {})
      .finally(() => { scannerBusy = false; });
    return;
  }
  try {
    const image = captureScannerFrame();
    const result = image && jsQR(image.data, image.width, image.height, { inversionAttempts: 'dontInvert' });
    if (result && isNearChatOpticalFrame(result.data)) {
      updateCameraFeedback(jsQrCorners(result), image.width, image.height);
      consumeScannedValue(result.data).catch(error => showToast(error.message));
    } else markTargetLost();
  } catch {}
  scannerBusy = false;
}

async function startMainCamera() {
  stopScanner();
  ui.cameraState.dataset.state = 'starting';
  ui.cameraState.textContent = 'Starting main camera…';
  await chooseBarcodeDecoder();
  const stream = await navigator.mediaDevices.getUserMedia({
    video: {
      facingMode: { ideal: 'environment' },
      width: { ideal: 1280 },
      height: { ideal: 720 },
      frameRate: { ideal: 24, max: 30 }
    },
    audio: false
  });
  if (!pairingActive) {
    stream.getTracks().forEach(track => track.stop());
    return;
  }
  cameraStream = stream;
  ui.scannerVideo.srcObject = cameraStream;
  await ui.scannerVideo.play();
  scannerGeneration++;
  scannerLastDecode = 0;
  scannerBusy = false;
  ui.cameraState.dataset.state = 'active';
  ui.cameraState.textContent = 'Main camera active · scanning connection codes';
  scannerRaf = requestAnimationFrame(scannerLoop);
}

function stopScanner() {
  scannerGeneration++;
  cancelAnimationFrame(scannerRaf);
  scannerRaf = 0;
  cameraStream?.getTracks().forEach(track => track.stop());
  cameraStream = null;
  ui.scannerVideo.srcObject = null;
  scannerBusy = false;
}

function failPairing(error) {
  pairingActive = false;
  buildingSignal = false;
  stopScanner();
  stopHandoffListener();
  stopHandoffBeeps();
  clearDiscoveryTimer();
  stopSignalAnimation();
  resetSignalDecoder();
  teardownPeer({ keepMetrics: false });
  ui.cameraState.dataset.state = 'error';
  ui.cameraState.textContent = 'Pairing stopped';
  setConnectionStatus('failed', 'Pairing unavailable', 'Press Connect on both devices to try again.');
  setPairingCopy('Pairing stopped', 'The phones could not connect',
    error?.name === 'NotAllowedError'
      ? 'Camera permission is required to scan connection codes.'
      : error?.message || 'Return to camera mode and try scanning the code again.', 8);
}

function resetPairingState() {
  stopHandoffListener();
  stopHandoffBeeps();
  clearDiscoveryTimer();
  resetSignalDecoder();
  pairingSession = '';
  pairingSessionNumber = 0;
  pairingMode = 'discover';
  localDiscoveryId = '';
  remoteDiscoveryId = '';
  handoffTriggered = false;
  signalKind = '';
  signalFrames = [];
  signalFrameIndex = 0;
  buildingSignal = false;
}

function cancelPairDance() {
  const wasPairing = pairingActive;
  pairingActive = false;
  stopScanner();
  stopHandoffListener();
  stopHandoffBeeps();
  stopSignalAnimation();
  resetPairingState();
  if (wasPairing && !isConnected()) {
    teardownPeer({ keepMetrics: false });
    setConnectionStatus('offline', 'Not connected', 'Pair two nearby devices to begin.');
  }
  closePairing();
}

async function beginPairDance() {
  stopScanner();
  stopHandoffListener();
  stopHandoffBeeps();
  stopSignalAnimation();
  teardownPeer({ keepMetrics: false });
  resetPairingState();
  pairingActive = true;
  localDiscoveryId = randomHex(8);
  openPairing();
  setPairView('dance');
  setPairMode('discover');
  renderQr(`${DISCOVERY_FRAME_PREFIX}|${localDiscoveryId}`, ui.discoveryQrCanvas);
  resetCameraFeedback();
  ui.cameraState.dataset.state = 'starting';
  ui.cameraState.textContent = 'Starting main camera…';
  setPairingCopy('1 · Find the other device', 'Point the cameras at the other screen',
    'Each camera looks for the small QR in the corner. NearChat then chooses who shares first.', 8);
  setConnectionStatus('pairing', 'Finding nearby device', 'Keep the other screen inside the camera view.');
  primeAudio().catch(() => {});
  try {
    await Promise.all([ensureRaptor(), startMainCamera()]);
  } catch (error) {
    if (pairingActive) failPairing(error);
    return;
  }
  if (!pairingActive || pairingMode !== 'discover') return;
  try {
    await startHandoffListener('discovery');
  } catch {
    if (!pairingActive) return;
    ui.cameraState.dataset.state = 'warning';
    ui.cameraState.textContent = 'Automatic beeps unavailable · manual Show remains available';
    ui.pairStatus.textContent = 'Automatic audio handoff is unavailable. Tap Show connection code on one device.';
  }
}

function scrollMessages() {
  requestAnimationFrame(() => { ui.stream.scrollTop = ui.stream.scrollHeight; });
}

function messageTime(timestamp) {
  const date = new Date(Number(timestamp) || Date.now());
  return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
}

function createMessageShell(mine) {
  ui.empty.hidden = true;
  const row = document.createElement('article');
  row.className = `message-row${mine ? ' mine' : ''}`;
  const bubble = document.createElement('div');
  bubble.className = 'message-bubble';
  row.appendChild(bubble);
  ui.stream.appendChild(row);
  scrollMessages();
  return { row, bubble };
}

function appendTextMessage({ mine, text, timestamp = Date.now(), state = 'received' }) {
  const { bubble } = createMessageShell(mine);
  const copy = document.createElement('p');
  copy.textContent = text;
  const meta = document.createElement('div');
  meta.className = 'message-meta';
  const stateNode = document.createElement('span');
  stateNode.textContent = mine ? state : 'received';
  const time = document.createElement('time');
  time.dateTime = new Date(timestamp).toISOString();
  time.textContent = messageTime(timestamp);
  meta.append(stateNode, time);
  bubble.append(copy, meta);
  return { bubble, stateNode };
}

function appendImageMessage({ mine, url = '', text = '', timestamp = Date.now(), state = 'sending', progress = false }) {
  const { bubble } = createMessageShell(mine);
  let image = null;
  let progressFill = null;
  let progressLabel = null;
  if (progress) {
    const progressBox = document.createElement('div');
    progressBox.className = 'message-progress';
    progressLabel = document.createElement('span');
    progressLabel.textContent = mine ? 'Sending image…' : 'Receiving image…';
    const track = document.createElement('div');
    track.className = 'progress-track';
    progressFill = document.createElement('div');
    progressFill.className = 'progress-fill';
    track.appendChild(progressFill);
    progressBox.append(progressLabel, track);
    bubble.appendChild(progressBox);
  } else if (url) {
    image = document.createElement('img');
    image.className = 'message-image';
    image.src = url;
    image.alt = mine ? 'Sent image' : 'Received image';
    bubble.appendChild(image);
  }
  if (text) {
    const copy = document.createElement('p');
    copy.textContent = text;
    bubble.appendChild(copy);
  }
  const meta = document.createElement('div');
  meta.className = 'message-meta';
  const stateNode = document.createElement('span');
  stateNode.textContent = state;
  const time = document.createElement('time');
  time.dateTime = new Date(timestamp).toISOString();
  time.textContent = messageTime(timestamp);
  meta.append(stateNode, time);
  bubble.appendChild(meta);
  return { bubble, image, progressFill, progressLabel, stateNode };
}

function finishIncomingImage() {
  if (!incomingImage || incomingImage.received < incomingImage.size) return;
  const completed = incomingImage;
  const blob = new Blob(completed.chunks, { type: completed.mime });
  const url = URL.createObjectURL(blob);
  objectUrls.add(url);
  const image = document.createElement('img');
  image.className = 'message-image';
  image.src = url;
  image.alt = 'Received image';
  const progressBox = completed.view.progressFill?.parentElement?.parentElement;
  progressBox?.replaceWith(image);
  completed.view.stateNode.textContent = 'received';
  incomingImage = null;
  persistLiveItem({
    id: completed.id,
    kind: 'file',
    mine: false,
    name: completed.name,
    mime: completed.mime,
    size: blob.size,
    text: completed.text,
    blob,
    createdAt: completed.timestamp
  });
  scrollMessages();
}

function handleMediaPacket(event) {
  const size = typeof event.data === 'string'
    ? countStringBytes(event.data)
    : event.data?.byteLength || event.data?.size || 0;
  recordBytes('received', size);
  if (typeof event.data === 'string') {
    let packet;
    try { packet = JSON.parse(event.data); } catch { return; }
    if (packet?.type !== 'image-meta' || typeof packet.id !== 'string' ||
        typeof packet.mime !== 'string' || !Number.isFinite(packet.size) ||
        packet.size < 1 || packet.size > MAX_IMAGE_BYTES) return;
    const timestamp = Number(packet.timestamp) || Date.now();
    const text = typeof packet.text === 'string' ? packet.text.slice(0, 2000) : '';
    const view = appendImageMessage({
      mine: false,
      text,
      timestamp,
      state: `0 / ${formatBytes(packet.size)}`,
      progress: true
    });
    incomingImage = {
      id: packet.id,
      name: typeof packet.name === 'string' ? packet.name.slice(0, 100) : 'Received image',
      mime: /^image\/(?:avif|webp|jpeg|png)$/.test(packet.mime) ? packet.mime : 'image/jpeg',
      size: packet.size,
      text,
      timestamp,
      received: 0,
      chunks: [],
      view
    };
    return;
  }
  if (!incomingImage || !(event.data instanceof ArrayBuffer)) return;
  incomingImage.chunks.push(event.data);
  incomingImage.received += event.data.byteLength;
  const percent = Math.min(100, incomingImage.received / incomingImage.size * 100);
  incomingImage.view.progressFill.style.width = `${percent}%`;
  incomingImage.view.stateNode.textContent = `${formatBytes(incomingImage.received)} / ${formatBytes(incomingImage.size)}`;
  finishIncomingImage();
}

function waitForMediaBuffer() {
  if (!channelIsOpen(mediaChannel)) return Promise.reject(new Error('The image channel disconnected.'));
  if (mediaChannel.bufferedAmount <= BUFFER_HIGH_WATER) return Promise.resolve();
  mediaChannel.bufferedAmountLowThreshold = BUFFER_LOW_WATER;
  return new Promise((resolve, reject) => {
    const finish = () => {
      clearTimeout(timer);
      mediaChannel?.removeEventListener('bufferedamountlow', onLow);
    };
    const onLow = () => { finish(); resolve(); };
    const timer = setTimeout(() => {
      finish();
      if (channelIsOpen(mediaChannel)) resolve();
      else reject(new Error('The image channel disconnected.'));
    }, 5000);
    mediaChannel.addEventListener('bufferedamountlow', onLow, { once: true });
  });
}

async function transferImage(image, text, view, id, timestamp) {
  sendMediaPacket({
    type: 'image-meta',
    id,
    timestamp,
    name: image.name,
    mime: image.blob.type,
    size: image.blob.size,
    text
  });
  let sent = 0;
  for (let offset = 0; offset < image.blob.size; offset += MEDIA_CHUNK_BYTES) {
    await waitForMediaBuffer();
    const chunk = await image.blob.slice(offset, offset + MEDIA_CHUNK_BYTES).arrayBuffer();
    if (!channelIsOpen(mediaChannel)) throw new Error('The image channel disconnected.');
    mediaChannel.send(chunk);
    recordBytes('sent', chunk.byteLength);
    sent += chunk.byteLength;
    view.stateNode.textContent = `${formatBytes(sent)} / ${formatBytes(image.blob.size)}`;
  }
  view.stateNode.textContent = 'sent';
}

async function decodeImageFile(file) {
  if ('createImageBitmap' in window) {
    const bitmap = await createImageBitmap(file, { imageOrientation: 'from-image' });
    return { source: bitmap, width: bitmap.width, height: bitmap.height, close: () => bitmap.close() };
  }
  return new Promise((resolve, reject) => {
    const url = URL.createObjectURL(file);
    const image = new Image();
    image.onload = () => resolve({
      source: image,
      width: image.naturalWidth,
      height: image.naturalHeight,
      close: () => URL.revokeObjectURL(url)
    });
    image.onerror = () => { URL.revokeObjectURL(url); reject(new Error('The image could not be opened.')); };
    image.src = url;
  });
}

function canvasBlob(canvas, type, quality) {
  return new Promise(resolve => canvas.toBlob(resolve, type, quality));
}

async function prepareImage(file) {
  if (!(file instanceof File) || !file.type.startsWith('image/')) throw new Error('Choose an image file.');
  if (file.size > 25 * 1024 * 1024) throw new Error('Choose an image under 25 MB.');
  const decodedImage = await decodeImageFile(file);
  try {
    let scale = Math.min(1, 1600 / decodedImage.width, 1600 / decodedImage.height);
    let quality = .84;
    let blob = null;
    let width = 0;
    let height = 0;
    for (let attempt = 0; attempt < 5; attempt++) {
      width = Math.max(1, Math.round(decodedImage.width * scale));
      height = Math.max(1, Math.round(decodedImage.height * scale));
      const canvas = document.createElement('canvas');
      canvas.width = width;
      canvas.height = height;
      const context = canvas.getContext('2d');
      context.imageSmoothingEnabled = true;
      context.imageSmoothingQuality = 'high';
      context.drawImage(decodedImage.source, 0, 0, width, height);
      blob = await canvasBlob(canvas, 'image/webp', quality) || await canvasBlob(canvas, 'image/jpeg', quality);
      canvas.width = canvas.height = 1;
      if (blob && blob.size <= MAX_IMAGE_BYTES) break;
      quality = Math.max(.58, quality - .08);
      scale *= .82;
    }
    if (!blob || blob.size > MAX_IMAGE_BYTES) throw new Error('The image could not be made small enough to send.');
    return { blob, width, height, name: file.name.slice(0, 100) };
  } finally {
    decodedImage.close();
  }
}

function clearPendingImages() {
  for (const item of pendingImages) URL.revokeObjectURL(item.url);
  pendingImages = [];
  ui.imageInput.value = '';
  ui.imageDraft.hidden = true;
  ui.imageDraftPreview.removeAttribute('src');
  updateComposer();
}

async function selectImages(files) {
  const requestedCount = files.length;
  const selected = Array.from(files)
    .filter(file => file instanceof File && file.type.startsWith('image/'))
    .slice(0, MAX_PENDING_IMAGES);
  if (!selected.length) return;
  imageBusy = true;
  ui.imageButton.disabled = true;
  clearPendingImages();
  showToast(`Preparing ${selected.length === 1 ? 'image' : `${selected.length} images`}…`);
  let skipped = 0;
  try {
    for (const file of selected) {
      try {
        const image = await prepareImage(file);
        pendingImages.push({ image, url: URL.createObjectURL(image.blob) });
      } catch {
        skipped++;
      }
    }
    if (!pendingImages.length) throw new Error('The selected images could not be prepared.');
    const first = pendingImages[0];
    const totalBytes = pendingImages.reduce((total, item) => total + item.image.blob.size, 0);
    ui.imageDraftPreview.src = first.url;
    ui.imageDraftName.textContent = pendingImages.length === 1
      ? first.image.name || 'Image ready'
      : `${pendingImages.length} images ready`;
    ui.imageDraftSize.textContent = pendingImages.length === 1
      ? `${first.image.width} × ${first.image.height} · ${formatBytes(totalBytes)}`
      : `${formatBytes(totalBytes)} total${skipped ? ` · ${skipped} skipped` : ''}`;
    ui.imageDraft.hidden = false;
    if (selected.length === MAX_PENDING_IMAGES && requestedCount > MAX_PENDING_IMAGES)
      showToast(`The first ${MAX_PENDING_IMAGES} images were selected.`);
    else if (skipped) showToast(`${skipped} image${skipped === 1 ? '' : 's'} could not be prepared.`);
  } catch (error) {
    clearPendingImages();
    showToast(error.message || 'The images could not be prepared.');
  } finally {
    imageBusy = false;
    updateComposer();
  }
}

function clipboardFiles(clipboardData) {
  const files = [];
  const seen = new Set();
  const addFile = file => {
    if (!(file instanceof File)) return;
    const key = `${file.name}|${file.type}|${file.size}|${file.lastModified}`;
    if (seen.has(key)) return;
    seen.add(key);
    files.push(file);
  };
  Array.from(clipboardData?.files || []).forEach(addFile);
  for (const item of Array.from(clipboardData?.items || [])) {
    if (item.kind !== 'file') continue;
    addFile(item.getAsFile());
  }
  return files;
}

function insertPastedMessage(text) {
  const cleanText = String(text || '').replace(/[\r\n]+/g, ' ');
  if (!cleanText) return;
  const start = ui.input.selectionStart ?? ui.input.value.length;
  const end = ui.input.selectionEnd ?? start;
  const limit = Number(ui.input.maxLength) || 2000;
  const value = `${ui.input.value.slice(0, start)}${cleanText}${ui.input.value.slice(end)}`.slice(0, limit);
  const caret = Math.min(start + cleanText.length, value.length);
  ui.input.value = value;
  ui.input.focus();
  ui.input.setSelectionRange(caret, caret);
  updateComposer();
}

async function handleClipboardPaste(event) {
  if (event.defaultPrevented || !isConnected() || !event.clipboardData) return;
  const files = clipboardFiles(event.clipboardData);
  const images = files.filter(file => file.type.startsWith('image/'));
  if (images.length) {
    event.preventDefault();
    showAppView('send');
    await selectImages(images);
    return;
  }
  if (files.length) {
    event.preventDefault();
    showToast('Only image files can be pasted for now.');
    return;
  }
  const target = event.target;
  const editable = target instanceof HTMLInputElement || target instanceof HTMLTextAreaElement || target?.isContentEditable;
  if (editable) return;
  const text = event.clipboardData.getData('text/plain');
  if (!text) return;
  event.preventDefault();
  showAppView('send');
  insertPastedMessage(text);
}

async function submitMessage(event) {
  event.preventDefault();
  if (!isConnected()) {
    showToast('Pair with another device first.');
    return;
  }
  const text = ui.input.value.trim();
  const images = pendingImages;
  if (!text && images.length === 0) return;
  ui.input.value = '';
  pendingImages = [];
  ui.imageDraft.hidden = true;
  ui.imageDraftPreview.removeAttribute('src');
  ui.imageInput.value = '';
  updateComposer();

  if (!images.length) {
    const id = randomId();
    const timestamp = Date.now();
    const view = appendTextMessage({ mine: true, text, timestamp, state: 'sending' });
    try {
      sendChatPacket({ type: 'message', id, timestamp, text });
      view.stateNode.textContent = 'sent';
      persistLiveItem({ id, kind: 'text', mine: true, text, createdAt: timestamp });
    } catch (error) {
      view.stateNode.textContent = 'failed';
      showToast(error.message);
    }
    return;
  }

  images.forEach(({ image, url }, index) => {
    objectUrls.add(url);
    const caption = index === 0 ? text : '';
    const id = randomId();
    const timestamp = Date.now() + index;
    const view = appendImageMessage({ mine: true, url, text: caption, timestamp, state: 'queued' });
    persistLiveItem({
      id,
      kind: 'file',
      mine: true,
      name: image.name || 'Sent image',
      mime: image.blob.type,
      size: image.blob.size,
      text: caption,
      blob: image.blob,
      createdAt: timestamp
    });
    const task = outboundMediaQueue.then(() => transferImage(image, caption, view, id, timestamp));
    outboundMediaQueue = task.catch(() => {});
    task.catch(error => {
      view.stateNode.textContent = 'failed';
      showToast(error.message || 'An image could not be sent.');
    });
  });
}

for (const button of ui.navButtons) {
  button.addEventListener('click', () => {
    const target = button.dataset.view;
    if (target === 'send' && !isConnected()) {
      if (pairingActive) openPairing();
      else beginPairDance();
      return;
    }
    if (target === 'send' && currentView === 'send') {
      openPairing();
      setPairView('connected');
      return;
    }
    showAppView(target);
  });
}
ui.recentSearch.addEventListener('input', renderRecentLibrary);
ui.recentSort.addEventListener('click', () => {
  recentNewestFirst = !recentNewestFirst;
  ui.recentSort.firstChild.textContent = recentNewestFirst ? 'Date modified ' : 'Oldest first ';
  renderRecentLibrary();
});
ui.fileSearch.addEventListener('input', () => {
  if (ui.fileSearch.value.trim()) {
    selectedFileType = '';
    selectedStoredImageIds.clear();
  }
  renderFileBrowser();
});
ui.backToTypes.addEventListener('click', () => {
  selectedFileType = '';
  selectedStoredImageIds.clear();
  ui.fileSearch.value = '';
  renderFileBrowser();
});
ui.selectAllImages.addEventListener('click', () => {
  const images = storedFiles.filter(item => fileType(item) === 'Images');
  const allSelected = images.length > 0 && images.every(item => selectedStoredImageIds.has(item.id));
  selectedStoredImageIds.clear();
  if (!allSelected) images.forEach(item => selectedStoredImageIds.add(item.id));
  renderFileBrowser();
});
ui.downloadSelectedImages.addEventListener('click', downloadSelectedImageFiles);
ui.clearLibrary.addEventListener('click', clearStoredLibrary);
ui.disconnectInSheet.addEventListener('click', () => {
  closePairing();
  disconnectPeer();
});
ui.closePairing.addEventListener('click', () => {
  if (pairingActive && !isConnected()) cancelPairDance();
  else closePairing();
});
ui.overlay.addEventListener('click', event => {
  if (event.target !== ui.overlay) return;
  if (pairingActive && !isConnected()) cancelPairDance();
  else closePairing();
});
ui.cancelPairing.addEventListener('click', cancelPairDance);
ui.showCode.addEventListener('click', () => {
  showConnectionCode().catch(error => {
    if (pairingActive) failPairing(error);
  });
});
ui.scanCode.addEventListener('click', () => {
  switchToAnswerScanner(true).catch(error => {
    if (pairingActive) failPairing(error);
  });
});
ui.composer.addEventListener('submit', submitMessage);
ui.input.addEventListener('input', updateComposer);
ui.imageButton.addEventListener('click', () => ui.imageInput.click());
ui.imageInput.addEventListener('change', () => {
  const files = ui.imageInput.files;
  if (files?.length) selectImages(files);
});
ui.removeImage.addEventListener('click', clearPendingImages);
document.addEventListener('paste', event => {
  handleClipboardPaste(event).catch(error => showToast(error.message || 'Clipboard content could not be added.'));
});

document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'visible' && isConnected()) {
    startHeartbeat();
  }
});
window.addEventListener('pageshow', () => {
  if (isConnected()) startHeartbeat();
});
window.addEventListener('pagehide', () => {
  pairingActive = false;
  clearDiscoveryTimer();
  stopScanner();
  stopHandoffListener();
  stopHandoffBeeps();
  stopSignalAnimation();
  resetSignalDecoder();
  stopHeartbeat();
});
window.addEventListener('beforeunload', () => {
  try { audioContext?.close(); } catch {}
  for (const url of objectUrls) URL.revokeObjectURL(url);
});

if (!('RTCPeerConnection' in window)) {
  const sendNav = ui.navButtons.find(button => button.dataset.view === 'send');
  if (sendNav) sendNav.disabled = true;
  setConnectionStatus('failed', 'WebRTC unavailable', 'Open this page in a current mobile browser.');
}

async function initializeLibrary() {
  try {
    const [latest] = await Promise.all([getLatestSession(), refreshFileLibrary(), refreshRecentLibrary()]);
    if (liveSessionId || isConnected()) return;
    if (latest) {
      await renderStoredSession(latest);
    } else {
      setRecentEmpty();
      updateRecentHeader();
    }
    showAppView('recent');
  } catch (error) {
    console.warn('NearChat local history:', error);
    ui.clearLibrary.disabled = true;
    ui.libraryEmpty.querySelector('h2').textContent = 'Local history unavailable';
    ui.libraryEmpty.querySelector('p').textContent = 'You can still connect and share during this visit.';
    ui.recentLibraryEmpty.querySelector('h2').textContent = 'Local history unavailable';
    ui.recentLibraryEmpty.querySelector('p').textContent = 'Tap Send to connect. Items will last only for this visit.';
    ui.recentLibraryEmpty.hidden = false;
    showAppView('recent');
  }
}

updateComposer();
updateMetrics();
initializeLibrary();
