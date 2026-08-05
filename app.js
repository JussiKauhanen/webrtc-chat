import { QRCode, jsQR } from '../assets/qr-libs.js';

const $ = selector => document.querySelector(selector);
const encoder = new TextEncoder();
const decoder = new TextDecoder();

const SIGNAL_PREFIX = 'NCD1';
const FRAME_PREFIX = 'NCP1';
const SIGNAL_CHUNK_CHARS = 620;
const SIGNAL_FRAME_MS = 520;
const HEARTBEAT_MS = 4000;
const HEARTBEAT_STALE_MS = 12000;
const MEDIA_CHUNK_BYTES = 16 * 1024;
const BUFFER_HIGH_WATER = 512 * 1024;
const BUFFER_LOW_WATER = 128 * 1024;
const MAX_IMAGE_BYTES = 2 * 1024 * 1024;
const MAX_SCAN_PIXELS = 420000;

const ui = {
  share: $('#shareButton'),
  disconnect: $('#disconnectButton'),
  statusDot: $('#statusDot'),
  statusText: $('#statusText'),
  statusDetail: $('#statusDetail'),
  metricRtt: $('#metricRtt'),
  metricSent: $('#metricSent'),
  metricReceived: $('#metricReceived'),
  metricRate: $('#metricRate'),
  metricUptime: $('#metricUptime'),
  metricPath: $('#metricPath'),
  stream: $('#messageStream'),
  empty: $('#emptyState'),
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
  pairLoading: $('#pairLoading'),
  pairLoadingTitle: $('#pairLoadingTitle'),
  pairLoadingCopy: $('#pairLoadingCopy'),
  pairQr: $('#pairQr'),
  pairScanner: $('#pairScanner'),
  pairConnected: $('#pairConnected'),
  qrCanvas: $('#pairQrCanvas'),
  qrTitle: $('#qrTitle'),
  qrStatus: $('#qrStatus'),
  scanAnswer: $('#scanAnswerButton'),
  scanInstead: $('#scanInsteadButton'),
  manualCode: $('#manualCode'),
  remoteCode: $('#remoteCode'),
  copyCode: $('#copyCodeButton'),
  useCode: $('#useCodeButton'),
  scannerVideo: $('#scannerVideo'),
  scannerCanvas: $('#scannerCanvas'),
  scannerTitle: $('#scannerTitle'),
  scannerStatus: $('#scannerStatus'),
  cancelScanner: $('#cancelScanner'),
  disconnectInSheet: $('#disconnectInSheet'),
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

let signalCode = '';
let signalKind = '';
let signalFrames = [];
let signalFrameIndex = 0;
let signalTimer = 0;

let cameraStream = null;
let scannerRaf = 0;
let scannerGeneration = 0;
let scannerBusy = false;
let scannerLastDecode = 0;
let barcodeDetector = null;
let scanExpectedType = 'offer';
let scannedBundle = null;
let consumingSignal = false;

let pendingImage = null;
let pendingImageUrl = '';
let imageBusy = false;
let incomingImage = null;
let outboundMediaQueue = Promise.resolve();
const objectUrls = new Set();

function randomId() {
  if (crypto.randomUUID) return crypto.randomUUID();
  const bytes = crypto.getRandomValues(new Uint8Array(16));
  return [...bytes].map(byte => byte.toString(16).padStart(2, '0')).join('');
}

function showToast(message) {
  ui.toast.textContent = message;
  ui.toast.classList.add('show');
  clearTimeout(showToast.timer);
  showToast.timer = setTimeout(() => ui.toast.classList.remove('show'), 2300);
}

function setPairView(view) {
  ui.pairLoading.hidden = view !== 'loading';
  ui.pairQr.hidden = view !== 'qr';
  ui.pairScanner.hidden = view !== 'scanner';
  ui.pairConnected.hidden = view !== 'connected';
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

function setConnectionStatus(state, title, detail) {
  ui.statusDot.dataset.state = state;
  ui.statusText.textContent = title;
  ui.statusDetail.textContent = detail;
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
  ui.send.disabled = !connected || imageBusy || (!ui.input.value.trim() && !pendingImage);
}

function formatBytes(bytes) {
  if (!Number.isFinite(bytes) || bytes <= 0) return '0 B';
  if (bytes < 1024) return `${Math.round(bytes)} B`;
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(bytes < 10 * 1024 ? 1 : 0)} KB`;
  return `${(bytes / 1024 / 1024).toFixed(1)} MB`;
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
  setConnectionStatus('connected', 'Live connection', 'Heartbeat active · messages send directly.');
  ui.share.textContent = 'Connection';
  ui.disconnect.hidden = false;
  startHeartbeat();
  startMetricTimers();
  updateComposer();
  if (!ui.overlay.hidden) {
    stopScanner();
    stopSignalAnimation();
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
      setConnectionStatus('stale', 'Chat channel closed', 'Press Share to pair the devices again.');
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
    setConnectionStatus('failed', 'Connection failed', 'Press Share to pair the devices again.');
    updateComposer();
    return;
  }
  if (state === 'closed') {
    setConnectionStatus('offline', 'Not connected', 'Pair two nearby devices to begin.');
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
      appendTextMessage({ mine: false, text: packet.text.slice(0, 2000), timestamp: packet.timestamp });
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
  setConnectionStatus('pairing', 'Pairing devices', 'Exchange the QR offer and answer.');
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
  ui.disconnect.hidden = true;
  ui.share.textContent = 'Share';
  if (!keepMetrics) resetMetrics();
  updateComposer();
}

function disconnectPeer() {
  teardownPeer();
  stopSignalAnimation();
  stopScanner();
  signalCode = '';
  signalFrames = [];
  setConnectionStatus('offline', 'Not connected', 'Pair two nearby devices to begin.');
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

async function encodeDescription(description) {
  const raw = encoder.encode(JSON.stringify({
    version: 1,
    description: { type: description.type, sdp: description.sdp }
  }));
  let body = raw;
  let mode = 'r';
  if ('CompressionStream' in window) {
    try {
      const compressed = await transformBytes(raw, CompressionStream);
      if (compressed.length < raw.length) {
        body = compressed;
        mode = 'g';
      }
    } catch {}
  }
  return `${SIGNAL_PREFIX}.${mode}.${bytesToBase64Url(body)}`;
}

async function decodeDescription(code) {
  const match = /^NCD1\.([gr])\.([A-Za-z0-9_-]+)$/.exec(code.trim());
  if (!match) throw new Error('That is not a NearChat Direct pairing code.');
  let bytes = base64UrlToBytes(match[2]);
  if (match[1] === 'g') {
    if (!('DecompressionStream' in window))
      throw new Error('This browser cannot open the compressed pairing code.');
    bytes = await transformBytes(bytes, DecompressionStream);
  }
  const payload = JSON.parse(decoder.decode(bytes));
  const description = payload?.description;
  if (payload?.version !== 1 || !description || !['offer', 'answer'].includes(description.type) ||
      typeof description.sdp !== 'string' || description.sdp.length > 100000)
    throw new Error('The pairing code is invalid.');
  return description;
}

function fnvHash(value) {
  let hash = 0x811c9dc5;
  for (let index = 0; index < value.length; index++) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 0x01000193);
  }
  return (hash >>> 0).toString(16).padStart(8, '0');
}

function splitSignalFrames(code) {
  const id = crypto.getRandomValues(new Uint32Array(1))[0].toString(16).padStart(8, '0');
  const hash = fnvHash(code);
  const pieces = [];
  for (let offset = 0; offset < code.length; offset += SIGNAL_CHUNK_CHARS)
    pieces.push(code.slice(offset, offset + SIGNAL_CHUNK_CHARS));
  return pieces.map((piece, index) =>
    `${FRAME_PREFIX}|${id}|${index}|${pieces.length}|${hash}|${piece}`);
}

function renderQr(text) {
  const qr = QRCode.create([{ data: text, mode: 'byte' }], { errorCorrectionLevel: 'L' });
  const quiet = 4;
  const modules = qr.modules.size;
  const dimension = modules + quiet * 2;
  const target = Math.min(660, Math.max(300, Math.round((window.devicePixelRatio || 1) * 330)));
  const scale = Math.max(2, Math.floor(target / dimension));
  const pixels = dimension * scale;
  const context = ui.qrCanvas.getContext('2d');
  ui.qrCanvas.width = pixels;
  ui.qrCanvas.height = pixels;
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
  ui.qrStatus.textContent = `Pairing frame ${signalFrameIndex + 1} of ${signalFrames.length} · keep both screens steady`;
  signalFrameIndex = (signalFrameIndex + 1) % signalFrames.length;
}

function startSignalAnimation() {
  stopSignalAnimation();
  signalFrameIndex = 0;
  paintSignalFrame();
  if (signalFrames.length > 1) signalTimer = setInterval(paintSignalFrame, SIGNAL_FRAME_MS);
}

function showSignalCode(code, kind) {
  signalCode = code;
  signalKind = kind;
  signalFrames = splitSignalFrames(code);
  ui.manualCode.value = code;
  ui.remoteCode.value = '';
  ui.qrTitle.textContent = kind === 'offer' ? 'Scan this invite' : 'Let the first phone scan this answer';
  ui.scanAnswer.hidden = kind !== 'offer';
  ui.scanInstead.textContent = kind === 'offer' ? 'Scan an invite instead' : 'Scan a different invite';
  setPairView('qr');
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

async function createInvite() {
  stopScanner();
  stopSignalAnimation();
  teardownPeer({ keepMetrics: false });
  signalCode = '';
  openPairing();
  setPairView('loading');
  ui.pairLoadingTitle.textContent = 'Creating a private invite…';
  ui.pairLoadingCopy.textContent = 'Gathering a direct route for this device.';
  try {
    const connection = setupPeer('initiator');
    const offer = await connection.createOffer();
    await connection.setLocalDescription(offer);
    await waitForIceGathering(connection);
    const code = await encodeDescription(connection.localDescription);
    showSignalCode(code, 'offer');
  } catch (error) {
    teardownPeer();
    setConnectionStatus('failed', 'Pairing unavailable', 'This browser could not create a WebRTC invite.');
    ui.pairLoadingTitle.textContent = 'Could not create an invite';
    ui.pairLoadingCopy.textContent = error.message || 'WebRTC is not available in this browser.';
  }
}

async function acceptSignalCode(code, expectedType) {
  const description = await decodeDescription(code);
  if (expectedType && description.type !== expectedType)
    throw new Error(`This phone is waiting for a WebRTC ${expectedType}.`);

  stopScanner();
  setPairView('loading');
  if (description.type === 'offer') {
    teardownPeer({ keepMetrics: false });
    ui.pairLoadingTitle.textContent = 'Creating the answer…';
    ui.pairLoadingCopy.textContent = 'The first phone will scan one more QR code.';
    const connection = setupPeer('responder');
    await connection.setRemoteDescription(description);
    const answer = await connection.createAnswer();
    await connection.setLocalDescription(answer);
    await waitForIceGathering(connection);
    const answerCode = await encodeDescription(connection.localDescription);
    showSignalCode(answerCode, 'answer');
    return;
  }

  if (!peer || peerRole !== 'initiator')
    throw new Error('Create an invite on this phone before scanning an answer.');
  ui.pairLoadingTitle.textContent = 'Opening the direct channel…';
  ui.pairLoadingCopy.textContent = 'The QR handshake is complete.';
  await peer.setRemoteDescription(description);
  setConnectionStatus('pairing', 'Connecting', 'Opening the persistent data channel…');
}

function parseSignalFrame(raw) {
  if (typeof raw !== 'string' || !raw.startsWith(`${FRAME_PREFIX}|`)) return null;
  const parts = raw.split('|');
  if (parts.length !== 6 || !/^[0-9a-f]{8}$/.test(parts[1]) ||
      !/^\d+$/.test(parts[2]) || !/^\d+$/.test(parts[3]) || !/^[0-9a-f]{8}$/.test(parts[4])) return null;
  const index = Number(parts[2]);
  const total = Number(parts[3]);
  if (total < 1 || total > 30 || index < 0 || index >= total || !parts[5]) return null;
  return { id: parts[1], index, total, hash: parts[4], piece: parts[5] };
}

async function consumeScannedValue(raw) {
  if (consumingSignal) return;
  if (raw.startsWith(`${SIGNAL_PREFIX}.`)) {
    consumingSignal = true;
    try { await acceptSignalCode(raw, scanExpectedType); }
    finally { consumingSignal = false; }
    return;
  }
  const frame = parseSignalFrame(raw);
  if (!frame) return;
  if (!scannedBundle || scannedBundle.id !== frame.id || scannedBundle.hash !== frame.hash) {
    scannedBundle = { id: frame.id, hash: frame.hash, total: frame.total, pieces: new Map() };
  }
  if (frame.total !== scannedBundle.total) return;
  scannedBundle.pieces.set(frame.index, frame.piece);
  ui.scannerStatus.textContent = `Reading pairing frames · ${scannedBundle.pieces.size} / ${frame.total}`;
  if (scannedBundle.pieces.size !== frame.total) return;
  const code = Array.from({ length: frame.total }, (_, index) => scannedBundle.pieces.get(index)).join('');
  if (fnvHash(code) !== frame.hash) {
    scannedBundle = null;
    ui.scannerStatus.textContent = 'A damaged pairing sequence was ignored.';
    return;
  }
  consumingSignal = true;
  try { await acceptSignalCode(code, scanExpectedType); }
  catch (error) {
    showToast(error.message);
    setPairView('scanner');
    ui.scannerStatus.textContent = error.message;
  } finally {
    consumingSignal = false;
  }
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
        results.forEach(result => consumeScannedValue(result.rawValue).catch(() => {}));
      })
      .catch(() => {})
      .finally(() => { scannerBusy = false; });
    return;
  }
  try {
    const image = captureScannerFrame();
    const result = image && jsQR(image.data, image.width, image.height, { inversionAttempts: 'dontInvert' });
    if (result) consumeScannedValue(result.data).catch(error => showToast(error.message));
  } catch {}
  scannerBusy = false;
}

async function startScanner(expectedType) {
  stopSignalAnimation();
  stopScanner();
  if (expectedType === 'offer') {
    teardownPeer({ keepMetrics: false });
    signalCode = '';
    signalFrames = [];
  }
  scanExpectedType = expectedType;
  scannedBundle = null;
  consumingSignal = false;
  setPairView('scanner');
  ui.scannerTitle.textContent = expectedType === 'answer' ? 'Scan their answer' : 'Scan their invite';
  ui.scannerStatus.textContent = 'Starting camera…';
  try {
    await chooseBarcodeDecoder();
    cameraStream = await navigator.mediaDevices.getUserMedia({
      video: { facingMode: { ideal: 'environment' }, width: { ideal: 1280 } },
      audio: false
    });
    ui.scannerVideo.srcObject = cameraStream;
    await ui.scannerVideo.play();
    scannerGeneration++;
    scannerLastDecode = 0;
    scannerBusy = false;
    ui.scannerStatus.textContent = 'Point the camera at the animated QR code.';
    scannerRaf = requestAnimationFrame(scannerLoop);
  } catch (error) {
    stopScanner();
    ui.scannerStatus.textContent = error?.name === 'NotAllowedError'
      ? 'Camera permission is required. You can paste the code instead.'
      : 'The camera could not be opened.';
  }
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
  const blob = new Blob(incomingImage.chunks, { type: incomingImage.mime });
  const url = URL.createObjectURL(blob);
  objectUrls.add(url);
  const image = document.createElement('img');
  image.className = 'message-image';
  image.src = url;
  image.alt = 'Received image';
  const progressBox = incomingImage.view.progressFill?.parentElement?.parentElement;
  progressBox?.replaceWith(image);
  incomingImage.view.stateNode.textContent = 'received';
  incomingImage = null;
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
    const view = appendImageMessage({
      mine: false,
      text: typeof packet.text === 'string' ? packet.text.slice(0, 2000) : '',
      timestamp: packet.timestamp,
      state: `0 / ${formatBytes(packet.size)}`,
      progress: true
    });
    incomingImage = {
      id: packet.id,
      mime: /^image\/(?:avif|webp|jpeg|png)$/.test(packet.mime) ? packet.mime : 'image/jpeg',
      size: packet.size,
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

async function transferImage(image, text, view) {
  sendMediaPacket({
    type: 'image-meta',
    id: randomId(),
    timestamp: Date.now(),
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

function clearPendingImage() {
  pendingImage = null;
  ui.imageInput.value = '';
  ui.imageDraft.hidden = true;
  ui.imageDraftPreview.removeAttribute('src');
  if (pendingImageUrl) URL.revokeObjectURL(pendingImageUrl);
  pendingImageUrl = '';
  updateComposer();
}

async function selectImage(file) {
  imageBusy = true;
  ui.imageButton.disabled = true;
  showToast('Preparing image…');
  try {
    const image = await prepareImage(file);
    clearPendingImage();
    pendingImage = image;
    pendingImageUrl = URL.createObjectURL(image.blob);
    ui.imageDraftPreview.src = pendingImageUrl;
    ui.imageDraftName.textContent = image.name || 'Image ready';
    ui.imageDraftSize.textContent = `${image.width} × ${image.height} · ${formatBytes(image.blob.size)}`;
    ui.imageDraft.hidden = false;
  } catch (error) {
    clearPendingImage();
    showToast(error.message || 'The image could not be prepared.');
  } finally {
    imageBusy = false;
    updateComposer();
  }
}

async function submitMessage(event) {
  event.preventDefault();
  if (!isConnected()) {
    showToast('Pair with another device first.');
    return;
  }
  const text = ui.input.value.trim();
  const image = pendingImage;
  const imageUrl = pendingImageUrl;
  if (!text && !image) return;
  ui.input.value = '';
  pendingImage = null;
  pendingImageUrl = '';
  ui.imageDraft.hidden = true;
  ui.imageInput.value = '';
  updateComposer();

  if (!image) {
    const view = appendTextMessage({ mine: true, text, state: 'sending' });
    try {
      sendChatPacket({ type: 'message', id: randomId(), timestamp: Date.now(), text });
      view.stateNode.textContent = 'sent';
    } catch (error) {
      view.stateNode.textContent = 'failed';
      showToast(error.message);
    }
    return;
  }

  objectUrls.add(imageUrl);
  const view = appendImageMessage({ mine: true, url: imageUrl, text, state: 'queued' });
  const task = outboundMediaQueue.then(() => transferImage(image, text, view));
  outboundMediaQueue = task.catch(() => {});
  task.catch(error => {
    view.stateNode.textContent = 'failed';
    showToast(error.message || 'The image could not be sent.');
  });
}

ui.share.addEventListener('click', () => {
  if (isConnected()) {
    openPairing();
    setPairView('connected');
    return;
  }
  if (signalCode && peer && !['failed', 'closed'].includes(peer.connectionState)) {
    openPairing();
    showSignalCode(signalCode, signalKind);
    return;
  }
  createInvite();
});
ui.disconnect.addEventListener('click', disconnectPeer);
ui.disconnectInSheet.addEventListener('click', () => {
  closePairing();
  disconnectPeer();
});
ui.closePairing.addEventListener('click', closePairing);
ui.overlay.addEventListener('click', event => {
  if (event.target === ui.overlay) closePairing();
});
ui.scanAnswer.addEventListener('click', () => startScanner('answer'));
ui.scanInstead.addEventListener('click', () => startScanner('offer'));
ui.cancelScanner.addEventListener('click', () => {
  stopScanner();
  if (signalCode) showSignalCode(signalCode, signalKind);
  else {
    setPairView('loading');
    ui.pairLoadingTitle.textContent = 'Scan cancelled';
    ui.pairLoadingCopy.textContent = 'Close this panel or create a new invite.';
  }
});
ui.copyCode.addEventListener('click', async () => {
  try {
    await navigator.clipboard.writeText(ui.manualCode.value);
    showToast('Pairing code copied');
  } catch { showToast('Copy is unavailable. Select the code manually.'); }
});
ui.useCode.addEventListener('click', async () => {
  const code = ui.remoteCode.value.trim();
  if (!code) return;
  try {
    const expected = peerRole === 'initiator' ? 'answer' : 'offer';
    await acceptSignalCode(code, expected);
  } catch (error) { showToast(error.message); }
});
ui.composer.addEventListener('submit', submitMessage);
ui.input.addEventListener('input', updateComposer);
ui.imageButton.addEventListener('click', () => ui.imageInput.click());
ui.imageInput.addEventListener('change', () => {
  const file = ui.imageInput.files?.[0];
  if (file) selectImage(file);
});
ui.removeImage.addEventListener('click', clearPendingImage);

document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'visible' && isConnected()) {
    startHeartbeat();
  }
});
window.addEventListener('pageshow', () => {
  if (isConnected()) startHeartbeat();
});
window.addEventListener('pagehide', () => {
  stopScanner();
  stopSignalAnimation();
  stopHeartbeat();
});
window.addEventListener('beforeunload', () => {
  for (const url of objectUrls) URL.revokeObjectURL(url);
});

if (!('RTCPeerConnection' in window)) {
  ui.share.disabled = true;
  setConnectionStatus('failed', 'WebRTC unavailable', 'Open this page in a current mobile browser.');
}
updateComposer();
updateMetrics();
