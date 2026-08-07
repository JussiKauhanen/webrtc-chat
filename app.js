import { QRCode, jsQR } from './assets/qr-libs.js';
import initRaptor, { RaptorQDecoder, encode_packets } from './assets/raptorq.js';

const $ = selector => document.querySelector(selector);
const $$ = selector => Array.from(document.querySelectorAll(selector));
const encoder = new TextEncoder();
const decoder = new TextDecoder();

const HELLO_PREFIX = 'NCH1';
const SIGNAL_FRAME_PREFIX = 'NCS1';
const SIGNAL_FRAME_MS = 220;
const RAPTOR_TRANSPORT_BYTES = 150;
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
  pairDance: $('#pairDance'),
  pairConnected: $('#pairConnected'),
  qrCanvases: $$('.pair-qr-canvas'),
  pairPhase: $('#pairPhase'),
  pairStatusTitle: $('#pairStatusTitle'),
  pairStatus: $('#pairStatus'),
  pairProgress: $('#pairProgress'),
  cameraState: $('#cameraState'),
  targetingGuide: $('#targetingGuide'),
  trackedPhone: $('#trackedPhone'),
  alignmentScore: $('#alignmentScore'),
  alignmentHint: $('#alignmentHint'),
  cancelPairing: $('#cancelPairing'),
  scannerVideo: $('#scannerVideo'),
  scannerCanvas: $('#scannerCanvas'),
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

let signalKind = '';
let signalFrames = [];
let signalFrameIndex = 0;
let signalTimer = 0;
let pairingActive = false;
let localHello = '';
let remoteHello = '';
let pairingSession = '';
let pairingSessionNumber = 0;
let buildingSignal = false;
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
  ui.pairDance.hidden = view !== 'dance';
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

function setPairingProgress(percent) {
  ui.pairProgress.style.width = `${Math.max(8, Math.min(100, percent))}%`;
}

function setPairingCopy(phase, title, detail, progress) {
  ui.pairPhase.textContent = phase;
  ui.pairStatusTitle.textContent = title;
  ui.pairStatus.textContent = detail;
  setPairingProgress(progress);
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
  pairingActive = false;
  buildingSignal = false;
  stopScanner();
  stopSignalAnimation();
  resetSignalDecoder();
  setConnectionStatus('connected', 'Live connection', 'Heartbeat active · messages send directly.');
  ui.share.textContent = 'Connection';
  ui.disconnect.hidden = false;
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
  setConnectionStatus('pairing', 'Pairing devices', 'Keep both screens face to face.');
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
  resetSignalDecoder();
  pairingActive = false;
  buildingSignal = false;
  localHello = '';
  remoteHello = '';
  pairingSession = '';
  pairingSessionNumber = 0;
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

function fnvHash(value) {
  let hash = 0x811c9dc5;
  for (let index = 0; index < value.length; index++) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 0x01000193);
  }
  return (hash >>> 0).toString(16).padStart(8, '0');
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

function renderQr(text, canvas) {
  const qr = QRCode.create([{ data: text, mode: 'byte' }], { errorCorrectionLevel: 'L' });
  const quiet = 4;
  const modules = qr.modules.size;
  const dimension = modules + quiet * 2;
  const target = Math.min(660, Math.max(300, Math.round((window.devicePixelRatio || 1) * 330)));
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
  ui.qrCanvases.forEach((canvas, index) => {
    renderQr(signalFrames[(signalFrameIndex + index) % signalFrames.length], canvas);
  });
  // Advance every tile by one so the single-code jsQR fallback also sees every frame.
  signalFrameIndex = (signalFrameIndex + 1) % signalFrames.length;
}

function startSignalAnimation() {
  stopSignalAnimation();
  signalFrameIndex = 0;
  paintSignalFrame();
  if (signalFrames.length > 1) signalTimer = setInterval(paintSignalFrame, SIGNAL_FRAME_MS);
}

function helloFrame() {
  return `${HELLO_PREFIX}|${localHello}`;
}

function displayHello() {
  signalKind = 'hello';
  signalFrames = [helloFrame()];
  startSignalAnimation();
}

function displaySignalFrames(frames, kind) {
  const interleaved = [];
  frames.forEach((frame, index) => {
    if (index % 3 === 0) interleaved.push(helloFrame());
    interleaved.push(frame);
  });
  signalKind = kind;
  signalFrames = interleaved;
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

async function createOpticalOffer() {
  if (!pairingActive || buildingSignal) return;
  buildingSignal = true;
  setPairingCopy('2 · Preparing the offer', 'Roles chosen automatically',
    'This phone is preparing the direct route. Keep the screens aligned.', 30);
  try {
    const connection = setupPeer('initiator');
    const offer = await connection.createOffer();
    await connection.setLocalDescription(offer);
    await waitForIceGathering(connection);
    if (!pairingActive || peer !== connection) return;
    const frames = await buildSignalFrames('O', connection.localDescription);
    displaySignalFrames(frames, 'offer');
    setPairingCopy('2 · Sending the offer', 'Keep the screens still',
      'The other phone is collecting the light frames and will answer automatically.', 42);
  } catch (error) {
    failPairing(error);
  } finally {
    buildingSignal = false;
  }
}

async function createOpticalAnswer(description) {
  if (!pairingActive || buildingSignal || peerRole !== 'responder') return;
  buildingSignal = true;
  setPairingCopy('3 · Preparing the answer', 'Offer received',
    'This phone is returning the final handshake through its screen.', 70);
  try {
    const connection = peer;
    await connection.setRemoteDescription(description);
    const answer = await connection.createAnswer();
    await connection.setLocalDescription(answer);
    await waitForIceGathering(connection);
    if (!pairingActive || peer !== connection) return;
    const frames = await buildSignalFrames('A', connection.localDescription);
    displaySignalFrames(frames, 'answer');
    setPairingCopy('3 · Returning the answer', 'Almost connected',
      'Keep the screens aligned until both phones confirm the direct channel.', 82);
  } catch (error) {
    failPairing(error);
  } finally {
    buildingSignal = false;
  }
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
    'The optical handshake is complete. Opening WebRTC now…', 94);
  stopSignalAnimation();
  await peer.setRemoteDescription(description);
  setConnectionStatus('pairing', 'Connecting', 'Opening the persistent data channel…');
}

async function ingestSignalFrame(raw) {
  if (!pairingActive || !pairingSession || signalFinishing) return;
  const parsed = parseSignalFrame(raw);
  if (!parsed) return;
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

async function acceptHello(raw) {
  const match = /^NCH1\|([0-9a-f]{16})$/.exec(raw);
  if (!pairingActive || !match || match[1] === localHello || remoteHello) return;
  remoteHello = match[1];
  if (remoteHello === localHello) {
    localHello = randomHex();
    remoteHello = '';
    displayHello();
    return;
  }

  const ordered = [localHello, remoteHello].sort();
  pairingSession = fnvHash(`${ordered[0]}:${ordered[1]}`);
  pairingSessionNumber = Number.parseInt(pairingSession, 16) >>> 0;
  navigator.vibrate?.(45);
  resetSignalDecoder();

  if (localHello === ordered[0]) {
    peerRole = 'initiator';
    await createOpticalOffer();
  } else {
    setupPeer('responder');
    setPairingCopy('2 · Receiving the offer', 'The phones found each other',
      'Keep the top edges aligned while this phone collects the offer.', 38);
  }
}

async function consumeScannedValue(raw) {
  if (typeof raw !== 'string') return;
  if (raw.startsWith(`${HELLO_PREFIX}|`)) {
    await acceptHello(raw);
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
  return typeof value === 'string' &&
    (value.startsWith(`${HELLO_PREFIX}|`) || value.startsWith(`${SIGNAL_FRAME_PREFIX}|`));
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

function clamp(value, minimum, maximum) {
  return Math.min(maximum, Math.max(minimum, value));
}

function resetTargetingGuide() {
  targetLastSeen = 0;
  ui.targetingGuide.dataset.state = 'searching';
  ui.targetingGuide.style.setProperty('--track-x', '77%');
  ui.targetingGuide.style.setProperty('--track-y', '30%');
  ui.targetingGuide.style.setProperty('--track-scale', '.72');
  ui.alignmentScore.textContent = 'Looking for the other phone';
  ui.alignmentHint.textContent = 'Move its outline over the dashed target.';
}

function markTargetLost() {
  if (performance.now() - targetLastSeen < 700) return;
  ui.targetingGuide.dataset.state = 'searching';
  ui.alignmentScore.textContent = 'Looking for the other phone';
  ui.alignmentHint.textContent = 'Keep its illuminated code inside the camera view.';
}

function updateTargetingGuide(points, frameWidth = ui.scannerVideo.videoWidth, frameHeight = ui.scannerVideo.videoHeight) {
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

  const desiredQrRatio = .13;
  const dx = normalizedX - .5;
  const dy = normalizedY - .5;
  const positionError = Math.min(1.5, Math.hypot(dx, dy) / .42);
  const sizeError = Math.min(1.5, Math.abs(Math.log(qrRatio / desiredQrRatio) / Math.log(2)));
  const score = clamp(1 - positionError * .68 - sizeError * .32, 0, 1);
  const state = score >= .72 ? 'aligned' : score >= .4 ? 'close' : 'far';
  const trackX = clamp(50 + dx * 100, 12, 88);
  const trackY = clamp(50 + dy * 100, 16, 84);
  const trackScale = clamp(qrRatio / desiredQrRatio, .5, 1.55);

  targetLastSeen = performance.now();
  ui.targetingGuide.dataset.state = state;
  ui.targetingGuide.style.setProperty('--track-x', `${trackX.toFixed(1)}%`);
  ui.targetingGuide.style.setProperty('--track-y', `${trackY.toFixed(1)}%`);
  ui.targetingGuide.style.setProperty('--track-scale', trackScale.toFixed(2));
  ui.alignmentScore.textContent = state === 'aligned' ? 'Aligned · hold still' : `${Math.round(score * 100)}% aligned`;

  if (state === 'aligned') ui.alignmentHint.textContent = 'Keep both devices steady while the light frames transfer.';
  else if (qrRatio < desiredQrRatio * .7) ui.alignmentHint.textContent = 'Move the other phone closer.';
  else if (qrRatio > desiredQrRatio * 1.4) ui.alignmentHint.textContent = 'Move the other phone slightly farther away.';
  else ui.alignmentHint.textContent = 'Move the wireframe over the dashed target.';
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
          updateTargetingGuide(barcodeCorners(nearChatResults[0]));
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
      updateTargetingGuide(jsQrCorners(result), image.width, image.height);
      consumeScannedValue(result.data).catch(error => showToast(error.message));
    } else markTargetLost();
  } catch {}
  scannerBusy = false;
}

async function startFrontCamera() {
  stopScanner();
  ui.cameraState.dataset.state = 'starting';
  ui.cameraState.textContent = 'Starting front camera…';
  await chooseBarcodeDecoder();
  const stream = await navigator.mediaDevices.getUserMedia({
    video: {
      facingMode: { ideal: 'user' },
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
  ui.cameraState.textContent = 'Front camera active · scanning light';
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
  stopSignalAnimation();
  resetSignalDecoder();
  teardownPeer({ keepMetrics: false });
  ui.cameraState.dataset.state = 'error';
  ui.cameraState.textContent = 'Pairing stopped';
  setConnectionStatus('failed', 'Pairing unavailable', 'Press Share on both phones to try again.');
  setPairingCopy('Pairing stopped', 'The phones could not connect',
    error?.name === 'NotAllowedError'
      ? 'Front-camera permission is required on both phones.'
      : error?.message || 'Move the phones apart slightly and try again.', 8);
}

function resetPairingState() {
  resetSignalDecoder();
  localHello = '';
  remoteHello = '';
  pairingSession = '';
  pairingSessionNumber = 0;
  signalKind = '';
  signalFrames = [];
  signalFrameIndex = 0;
  buildingSignal = false;
}

function cancelPairDance() {
  const wasPairing = pairingActive;
  pairingActive = false;
  stopScanner();
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
  stopSignalAnimation();
  teardownPeer({ keepMetrics: false });
  resetPairingState();
  pairingActive = true;
  localHello = randomHex();
  openPairing();
  setPairView('dance');
  resetTargetingGuide();
  ui.cameraState.dataset.state = 'starting';
  ui.cameraState.textContent = 'Starting front camera…';
  setPairingCopy('1 · Finding the other phone', 'Put both screens face to face',
    'Keep the top edges aligned, about 25–35 cm apart. The phones will choose their roles automatically.', 8);
  displayHello();
  setConnectionStatus('pairing', 'Pairing devices', 'Both front cameras are looking for the other screen.');
  try {
    await Promise.all([ensureRaptor(), startFrontCamera()]);
  } catch (error) {
    if (pairingActive) failPairing(error);
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
  beginPairDance();
});
ui.disconnect.addEventListener('click', disconnectPeer);
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
  pairingActive = false;
  stopScanner();
  stopSignalAnimation();
  resetSignalDecoder();
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
