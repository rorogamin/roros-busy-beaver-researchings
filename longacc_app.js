const palette = [
  [12, 15, 23, 255],
  [240, 244, 248, 255],
  [239, 68, 68, 255],
  [245, 158, 11, 255],
  [234, 179, 8, 255],
  [34, 197, 94, 255],
  [6, 182, 212, 255],
  [59, 130, 246, 255],
  [168, 85, 247, 255],
  [236, 72, 153, 255],
];

const statePalette = [
  [54, 18, 18, 255],
  [66, 33, 12, 255],
  [74, 55, 12, 255],
  [20, 64, 28, 255],
  [12, 58, 66, 255],
  [18, 44, 92, 255],
  [48, 27, 98, 255],
  [92, 24, 62, 255],
];

const zoomLevels = (() => {
  const levels = new Map([[1, { value: 1 }]]);
  for (let power = 0; power <= 24; power += 1) {
    const base = 2 ** power;
    levels.set(base, { value: base });
    levels.set(3 * base, { value: 3 * base });
    if (power > 0) {
      levels.set(1 / base, { value: 1 / base, downscale: base });
    }
    levels.set(1 / (3 * base), { value: 1 / (3 * base), downscale: 3 * base });
  }
  return Array.from(levels.values()).sort((left, right) => left.value - right.value);
})();

const viewport = document.querySelector('#viewport');
const viewCtx = viewport.getContext('2d', { alpha: false });
const tmInput = document.querySelector('#tm-input');
const startBtn = document.querySelector('#start-btn');
const pauseBtn = document.querySelector('#pause-btn');
const prevBtn = document.querySelector('#prev-btn');
const nextBtn = document.querySelector('#next-btn');
const flipBtn = document.querySelector('#flip-btn');
const zoomInBtn = document.querySelector('#zoom-in-btn');
const zoomOutBtn = document.querySelector('#zoom-out-btn');
const autoFitInput = document.querySelector('#auto-fit-input');
const effortInput = document.querySelector('#effort-input');
const statusText = document.querySelector('#status-text');
const rowsText = document.querySelector('#rows-text');
const widthText = document.querySelector('#width-text');
const stateText = document.querySelector('#state-text');
const timeText = document.querySelector('#time-text');
const avgText = document.querySelector('#avg-text');
const configText = document.querySelector('#config-text');

let bitmapCanvas = document.createElement('canvas');
let bitmapCtx = bitmapCanvas.getContext('2d', { alpha: false });
let renderedRows = 0;
let visitedWidth = 0;
let globalMinX = 0;
let globalMaxX = -1;
let pooledCache = new Map();
let workerReady = false;
let running = false;
let hasSession = false;
let halted = false;
let currentRunId = 0;
let nextRunId = 1;
const pendingSnapshots = [];
let flushScheduled = false;
let accumulatedRunMs = 0;
let runningSinceMs = 0;
let metricsFrameScheduled = false;

const view = {
  scale: 8,
  offsetX: 24,
  offsetY: 24,
  dragging: false,
  dragX: 0,
  dragY: 0,
};

const worker = new Worker('./simulator-worker.js', { type: 'module' });

function setStatus(message) {
  statusText.textContent = message;
}

function currentRunMs() {
  return accumulatedRunMs + (running ? performance.now() - runningSinceMs : 0);
}

function formatDuration(ms) {
  return `${(ms / 1000).toFixed(2)} s`;
}

function formatAvgPerCell(msPerCell) {
  if (!Number.isFinite(msPerCell) || msPerCell <= 0) {
    return '—';
  }
  if (msPerCell >= 1000) {
    return `${(msPerCell / 1000).toFixed(2)} s`;
  }
  if (msPerCell >= 1) {
    return `${msPerCell.toFixed(2)} ms`;
  }
  if (msPerCell >= 0.001) {
    return `${(msPerCell * 1000).toFixed(2)} µs`;
  }
  return `${(msPerCell * 1000000).toFixed(2)} ns`;
}

function refreshPerformanceStats() {
  const elapsedMs = currentRunMs();
  timeText.textContent = formatDuration(elapsedMs);
  const cells = renderedRows * visitedWidth;
  avgText.textContent = cells > 0 ? `${formatAvgPerCell(elapsedMs / cells)}/cell` : '—';
}

function resetPerformanceStats() {
  accumulatedRunMs = 0;
  runningSinceMs = running ? performance.now() : 0;
  metricsFrameScheduled = false;
  refreshPerformanceStats();
}

function scheduleMetricsFrame() {
  if (metricsFrameScheduled || !running) {
    return;
  }
  metricsFrameScheduled = true;
  requestAnimationFrame(() => {
    metricsFrameScheduled = false;
    refreshPerformanceStats();
    if (running) {
      scheduleMetricsFrame();
    }
  });
}

function setRunningState(nextRunning) {
  if (running === nextRunning) {
    return;
  }
  if (nextRunning) {
    runningSinceMs = performance.now();
  } else {
    accumulatedRunMs += performance.now() - runningSinceMs;
  }
  running = nextRunning;
  refreshPerformanceStats();
  if (running) {
    scheduleMetricsFrame();
  }
}

function parseTmList() {
  return tmInput.value
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
}

function writeTmList(lines) {
  tmInput.value = lines.join('\n');
}

function rotateTmList(direction) {
  const lines = parseTmList();
  if (lines.length <= 1) {
    return false;
  }
  if (direction > 0) {
    lines.push(lines.shift());
  } else {
    lines.unshift(lines.pop());
  }
  writeTmList(lines);
  return true;
}

function firstTmSpec() {
  const lines = parseTmList();
  return lines[0] ?? '';
}

function currentEffort() {
  return Math.max(0, Number(effortInput.value) || 0);
}

function flipTmSpec(spec) {
  return spec.replace(/[LR]/g, (direction) => (direction === 'L' ? 'R' : 'L'));
}

function flipCurrentTm() {
  const rawLines = tmInput.value.split(/\r?\n/);
  const index = rawLines.findIndex((line) => line.trim().length > 0);
  if (index < 0) {
    return false;
  }
  rawLines[index] = flipTmSpec(rawLines[index]);
  tmInput.value = rawLines.join('\n');
  return true;
}

function updateButtons() {
  startBtn.disabled = !workerReady;
  pauseBtn.disabled = !workerReady || !hasSession || halted;
  pauseBtn.textContent = running ? 'Pause' : 'Resume';
}

function nearestZoomIndex(target) {
  let bestIndex = 0;
  let bestDistance = Number.POSITIVE_INFINITY;
  zoomLevels.forEach((level, index) => {
    const distance = Math.abs(level.value - target);
    if (distance < bestDistance) {
      bestDistance = distance;
      bestIndex = index;
    }
  });
  return bestIndex;
}

function floorZoomIndex(target) {
  for (let index = zoomLevels.length - 1; index >= 0; index -= 1) {
    if (zoomLevels[index].value <= target) {
      return index;
    }
  }
  return -1;
}

function currentZoomIndex() {
  return nearestZoomIndex(view.scale);
}

function setZoomLevel(index, anchorX = null, anchorY = null) {
  const clampedIndex = Math.max(0, Math.min(zoomLevels.length - 1, index));
  const nextScale = zoomLevels[clampedIndex].value;
  if (anchorX == null || anchorY == null) {
    view.scale = nextScale;
    autoFitInput.checked = false;
    drawViewport();
    return;
  }
  const bounds = viewport.getBoundingClientRect();
  const pointX = anchorX - bounds.left;
  const pointY = anchorY - bounds.top;
  const worldX = (pointX - view.offsetX) / view.scale;
  const worldY = (pointY - view.offsetY) / view.scale;
  view.scale = nextScale;
  view.offsetX = pointX - worldX * view.scale;
  view.offsetY = pointY - worldY * view.scale;
  autoFitInput.checked = false;
  drawViewport();
}

function resizeBitmap(width, height, shiftX = 0, shiftY = 0) {
  const nextCanvas = document.createElement('canvas');
  nextCanvas.width = Math.max(width, 1);
  nextCanvas.height = Math.max(height, 1);
  const nextCtx = nextCanvas.getContext('2d', { alpha: false });
  nextCtx.fillStyle = '#0c0f17';
  nextCtx.fillRect(0, 0, nextCanvas.width, nextCanvas.height);
  if (bitmapCanvas.width > 0 && bitmapCanvas.height > 0 && renderedRows > 0) {
    nextCtx.drawImage(bitmapCanvas, shiftX, shiftY);
  }
  bitmapCanvas = nextCanvas;
  bitmapCtx = nextCtx;
}

function imageBounds() {
  return {
    left: view.offsetX,
    top: view.offsetY,
    right: view.offsetX + currentImageWidth() * view.scale,
    bottom: view.offsetY + currentImageHeight() * view.scale,
  };
}

function maxFitScale() {
  const width = currentImageWidth();
  const height = currentImageHeight();
  if (!width || !height) {
    return 8;
  }
  const bounds = viewport.getBoundingClientRect();
  const rawLimit = Math.min(bounds.width / width, bounds.height / height);
  const fitIndex = floorZoomIndex(rawLimit);
  return fitIndex >= 0 ? zoomLevels[fitIndex].value : zoomLevels[0].value;
}

function shouldAutoFit() {
  if (!renderedRows) {
    return true;
  }
  const bounds = viewport.getBoundingClientRect();
  const image = imageBounds();
  const outOfBounds =
    image.left < 0 ||
    image.top < 0 ||
    image.right > bounds.width ||
    image.bottom > bounds.height;
  return outOfBounds || maxFitScale() > view.scale;
}

function clearImage() {
  pendingSnapshots.length = 0;
  flushScheduled = false;
  renderedRows = 0;
  visitedWidth = 0;
  globalMinX = 0;
  globalMaxX = -1;
  pooledCache = new Map();
  resetPerformanceStats();
  resizeBitmap(1, 1);
  rowsText.textContent = '0';
  widthText.textContent = '0';
  stateText.textContent = '—';
  configText.textContent = '—';
  drawViewport();
}

function appendRow(cells, stateValue) {
  const rowIndex = renderedRows + 1;
  const rowMinX = -rowIndex;
  const stateX = rowMinX - 1;
  const rowMaxX = rowMinX + cells.length - 1;
  const nextMinX = renderedRows > 0 ? Math.min(globalMinX, stateX) : stateX;
  const nextMaxX = renderedRows > 0 ? Math.max(globalMaxX, rowMaxX) : rowMaxX;
  const nextWidth = Math.max(1, nextMaxX - nextMinX + 1);
  const nextHeight = renderedRows + 1;
  if (
    nextWidth !== bitmapCanvas.width ||
    nextHeight !== bitmapCanvas.height ||
    nextMinX !== globalMinX
  ) {
    const shiftX = globalMinX - nextMinX;
    resizeBitmap(nextWidth, nextHeight, shiftX, 0);
    if (renderedRows > 0) {
      view.offsetX -= shiftX * view.scale;
    }
  }
  globalMinX = nextMinX;
  globalMaxX = nextMaxX;
  pooledCache = new Map();
  const image = bitmapCtx.createImageData(bitmapCanvas.width, 1);
  for (let x = 0; x < bitmapCanvas.width; x += 1) {
    const color = palette[0];
    const offset = x * 4;
    image.data[offset + 0] = color[0];
    image.data[offset + 1] = color[1];
    image.data[offset + 2] = color[2];
    image.data[offset + 3] = color[3];
  }
  const stateColor = statePalette[((stateValue ?? 0) % statePalette.length + statePalette.length) % statePalette.length];
  const stateOffset = (stateX - globalMinX) * 4;
  image.data[stateOffset + 0] = stateColor[0];
  image.data[stateOffset + 1] = stateColor[1];
  image.data[stateOffset + 2] = stateColor[2];
  image.data[stateOffset + 3] = stateColor[3];
  const startColumn = rowMinX - globalMinX;
  for (let x = 0; x < cells.length; x += 1) {
    const color = palette[cells[x]] ?? palette[0];
    const offset = (startColumn + x) * 4;
    image.data[offset + 0] = color[0];
    image.data[offset + 1] = color[1];
    image.data[offset + 2] = color[2];
    image.data[offset + 3] = color[3];
  }
  bitmapCtx.putImageData(image, 0, renderedRows);
  renderedRows += 1;
}

function currentImageWidth() {
  return renderedRows > 0 ? bitmapCanvas.width : 0;
}

function currentImageHeight() {
  return renderedRows;
}

function fitView() {
  const width = currentImageWidth();
  const height = currentImageHeight();
  if (!width || !height) {
    view.scale = 8;
    view.offsetX = 24;
    view.offsetY = 0;
    drawViewport();
    return;
  }
  const bounds = viewport.getBoundingClientRect();
  view.scale = maxFitScale();
  view.offsetX = (bounds.width - width * view.scale) / 2;
  view.offsetY = 0;
  drawViewport();
}

function getPooledCanvas(scale) {
  const key = String(scale);
  const cached = pooledCache.get(key);
  if (cached) {
    return cached;
  }
  const level = zoomLevels[nearestZoomIndex(scale)];
  const blockSize = level.downscale;
  const source = bitmapCtx.getImageData(0, 0, bitmapCanvas.width, renderedRows).data;
  const bucketMinX = Math.floor(globalMinX / blockSize);
  const bucketMaxX = Math.floor(globalMaxX / blockSize);
  const bucketCountX = Math.max(1, bucketMaxX - bucketMinX + 1);
  const pooledCanvas = document.createElement('canvas');
  pooledCanvas.width = bucketCountX;
  pooledCanvas.height = Math.max(1, Math.ceil(renderedRows / blockSize));
  const pooledCtx = pooledCanvas.getContext('2d', { alpha: false });
  const pooledImage = pooledCtx.createImageData(pooledCanvas.width, pooledCanvas.height);
  for (let pooledY = 0; pooledY < pooledCanvas.height; pooledY += 1) {
    const sourceY0 = pooledY * blockSize;
    const sourceY1 = Math.min(renderedRows, sourceY0 + blockSize);
    for (let pooledX = 0; pooledX < pooledCanvas.width; pooledX += 1) {
      const bucketX = bucketMinX + pooledX;
      const worldX0 = bucketX * blockSize;
      const worldX1 = worldX0 + blockSize;
      const sourceX0 = Math.max(0, worldX0 - globalMinX);
      const sourceX1 = Math.min(bitmapCanvas.width, worldX1 - globalMinX);
      let sumR = 0;
      let sumG = 0;
      let sumB = 0;
      let sumA = 0;
      let count = 0;
      for (let sourceY = sourceY0; sourceY < sourceY1; sourceY += 1) {
        for (let sourceX = sourceX0; sourceX < sourceX1; sourceX += 1) {
          const sourceOffset = (sourceY * bitmapCanvas.width + sourceX) * 4;
          sumR += source[sourceOffset + 0];
          sumG += source[sourceOffset + 1];
          sumB += source[sourceOffset + 2];
          sumA += source[sourceOffset + 3];
          count += 1;
        }
      }
      const pooledOffset = (pooledY * pooledCanvas.width + pooledX) * 4;
      pooledImage.data[pooledOffset + 0] = Math.round(sumR / count);
      pooledImage.data[pooledOffset + 1] = Math.round(sumG / count);
      pooledImage.data[pooledOffset + 2] = Math.round(sumB / count);
      pooledImage.data[pooledOffset + 3] = Math.round(sumA / count);
    }
  }
  pooledCtx.putImageData(pooledImage, 0, 0);
  const pooled = {
    canvas: pooledCanvas,
    startX: bucketMinX * blockSize,
    blockSize,
  };
  pooledCache.set(key, pooled);
  return pooled;
}

function drawViewport() {
  const bounds = viewport.getBoundingClientRect();
  const dpr = window.devicePixelRatio || 1;
  viewport.width = Math.max(1, Math.floor(bounds.width * dpr));
  viewport.height = Math.max(1, Math.floor(bounds.height * dpr));
  viewCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
  viewCtx.fillStyle = '#0b0d12';
  viewCtx.fillRect(0, 0, bounds.width, bounds.height);
  if (!renderedRows) {
    viewCtx.fillStyle = '#8892a6';
    viewCtx.font = '14px system-ui, sans-serif';
    viewCtx.fillText('Start the simulator to render rows.', 24, 32);
    return;
  }
  viewCtx.imageSmoothingEnabled = false;
  if (view.scale >= 1) {
    viewCtx.drawImage(
      bitmapCanvas,
      view.offsetX,
      view.offsetY,
      bitmapCanvas.width * view.scale,
      renderedRows * view.scale,
    );
    return;
  }
  const pooled = getPooledCanvas(view.scale);
  const imageWidth = bitmapCanvas.width * view.scale;
  const imageHeight = renderedRows * view.scale;
  const pooledOffsetX = view.offsetX + (pooled.startX - globalMinX) * view.scale;
  viewCtx.save();
  viewCtx.beginPath();
  viewCtx.rect(view.offsetX, view.offsetY, imageWidth, imageHeight);
  viewCtx.clip();
  viewCtx.drawImage(
    pooled.canvas,
    pooledOffsetX,
    view.offsetY,
    pooled.canvas.width * pooled.blockSize * view.scale,
    pooled.canvas.height * pooled.blockSize * view.scale,
  );
  viewCtx.restore();
}

function applySnapshot(snapshot) {
  appendRow(snapshot.cells, snapshot.state >= 0 ? snapshot.state : 0);
  rowsText.textContent = String(snapshot.height);
  visitedWidth = snapshot.width;
  widthText.textContent = String(visitedWidth);
  stateText.textContent = snapshot.state >= 0 ? String.fromCharCode(65 + snapshot.state) : 'halt';
  refreshPerformanceStats();
  configText.textContent = snapshot.config || '—';
}

function renderSnapshots(snapshots) {
  if (!snapshots.length) {
    return;
  }
  for (const snapshot of snapshots) {
    applySnapshot(snapshot);
  }
  if (autoFitInput.checked && shouldAutoFit()) {
    fitView();
    return;
  }
  drawViewport();
}

function flushSnapshots() {
  flushScheduled = false;
  if (!pendingSnapshots.length) {
    return;
  }
  const batch = pendingSnapshots.splice(0, pendingSnapshots.length);
  renderSnapshots(batch);
  worker.postMessage({ type: 'rendered', runId: currentRunId, count: batch.length });
  if (pendingSnapshots.length) {
    flushScheduled = true;
    requestAnimationFrame(flushSnapshots);
  }
}

function enqueueSnapshots(snapshots) {
  if (!snapshots.length) {
    return;
  }
  pendingSnapshots.push(...snapshots);
  if (flushScheduled) {
    return;
  }
  flushScheduled = true;
  requestAnimationFrame(flushSnapshots);
}

function startSimulation() {
  const spec = firstTmSpec();
  if (!spec) {
    hasSession = false;
    setRunningState(false);
    halted = false;
    updateButtons();
    setStatus('Error: TM description is empty.');
    return;
  }
  currentRunId = nextRunId;
  nextRunId += 1;
  autoFitInput.checked = true;
  clearImage();
  hasSession = true;
  setRunningState(true);
  halted = false;
  updateButtons();
  setStatus('Running');
  worker.postMessage({
    type: 'start',
    runId: currentRunId,
    spec,
    effort: currentEffort(),
    iterationsPerRow: 1e9,
  });
}

worker.addEventListener('message', (event) => {
  const message = event.data;
  if (message.type === 'ready') {
    workerReady = true;
    updateButtons();
    setStatus('Ready');
    startSimulation();
    return;
  }
  if (message.runId && message.runId !== currentRunId) {
    return;
  }
  if (message.type === 'rows') {
    enqueueSnapshots(message.rows);
    if (message.halted) {
      setRunningState(false);
      halted = true;
      updateButtons();
      setStatus('Halted');
    }
    return;
  }
  if (message.type === 'state') {
    setRunningState(Boolean(message.running));
    halted = Boolean(message.halted);
    updateButtons();
    if (!running && !halted && hasSession) {
      setStatus('Paused');
    }
    return;
  }
  if (message.type === 'error') {
    setRunningState(false);
    hasSession = false;
    halted = false;
    updateButtons();
    setStatus(`Error: ${message.message}`);
  }
});

worker.addEventListener('error', () => {
  setRunningState(false);
  hasSession = false;
  halted = false;
  workerReady = false;
  updateButtons();
  setStatus('WASM assets missing. Run `bash build_web.sh` first.');
});

startBtn.addEventListener('click', startSimulation);
prevBtn.addEventListener('click', () => {
  if (rotateTmList(-1)) {
    startSimulation();
  }
});
nextBtn.addEventListener('click', () => {
  if (rotateTmList(1)) {
    startSimulation();
  }
});
flipBtn.addEventListener('click', () => {
  if (flipCurrentTm()) {
    startSimulation();
  }
});
pauseBtn.addEventListener('click', () => {
  if (running) {
    worker.postMessage({ type: 'pause', runId: currentRunId });
    return;
  }
  setRunningState(true);
  updateButtons();
  setStatus('Running');
  worker.postMessage({ type: 'resume', runId: currentRunId });
});

zoomInBtn.addEventListener('click', () => {
  const bounds = viewport.getBoundingClientRect();
  setZoomLevel(currentZoomIndex() + 1, bounds.left + bounds.width / 2, bounds.top + bounds.height / 2);
});
zoomOutBtn.addEventListener('click', () => {
  const bounds = viewport.getBoundingClientRect();
  setZoomLevel(currentZoomIndex() - 1, bounds.left + bounds.width / 2, bounds.top + bounds.height / 2);
});
autoFitInput.addEventListener('change', () => {
  if (autoFitInput.checked) {
    fitView();
  }
});
effortInput.addEventListener('change', () => {
  startSimulation();
});

viewport.addEventListener('wheel', (event) => {
  event.preventDefault();
  setZoomLevel(currentZoomIndex() + (event.deltaY < 0 ? 1 : -1), event.clientX, event.clientY);
}, { passive: false });

viewport.addEventListener('mousedown', (event) => {
  view.dragging = true;
  view.dragX = event.clientX;
  view.dragY = event.clientY;
  autoFitInput.checked = false;
  viewport.classList.add('dragging');
});

window.addEventListener('mousemove', (event) => {
  if (!view.dragging) return;
  view.offsetX += event.clientX - view.dragX;
  view.offsetY += event.clientY - view.dragY;
  view.dragX = event.clientX;
  view.dragY = event.clientY;
  drawViewport();
});

window.addEventListener('mouseup', () => {
  view.dragging = false;
  viewport.classList.remove('dragging');
});

window.addEventListener('resize', () => {
  if (autoFitInput.checked && shouldAutoFit()) {
    fitView();
    return;
  }
  drawViewport();
});

clearImage();
updateButtons();
