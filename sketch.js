let t = 0;
let glowPoints = [];
let glowTexture;
let featherPower = 2.5;
let lastFeatherPower = -1;
let handPose;
let video;
let hands = [];

let frameCountSinceLastDetect = 0; // 用于控制检测频率

// 新增：音频输入/播放相关（本地 MP3）
let canvasRef;
let sound;
let isSoundLoaded = false;
let isPlaying = false;
// 取消左上角播放按钮，改为空格键控制
let amplitudeAnalyzer;
let micLevelRaw = 0; // 复用命名：表示当前音频源的原始幅度
let micLevelSmoothed = 0; // 复用命名：平滑后的幅度
let audioPhase = 0; // 将音量映射为背景 sin 的自变量
let micPhaseMaxLevel = 0.3; // 将 0..0.3 的音量映射到 0..TWO_PI

// 新增：音量剧烈程度与G键扭动增强
let audioLevelPrev = 0;
let audioSeverity = 0.6;       // 0..1，表示音量突变强度
let severityGain = 50;       // 越大对突变越敏感
let gBoostActive = false;    // 按住G时反向并增强扭动

// 新增：t 步长分母动态控制（音量阈值触发，2s 恢复）
let tStepDenomBase = 30;           // 正常分母 30（请保留用户当前值）
let tStepDenomTriggered = 95;      // 触发时的分母 80
let tStepDenomCurrent = 30;        // 当前使用的分母（帧更新）
let tStepRecoveryMs = 0;           // 剩余恢复时间（ms）
const T_STEP_RECOVERY_MS = 1700;   // 总恢复时长（ms）

// 新增：半径脉冲（音量阈值触发，1s 衰减）
let radiusPulse = 1;         // >=1，触发时置为1.5，随后回落到1

// 新增：基于摄像头灰度深度的点阵背景参数（密度与大小）
let depthDotCell = 20;       // 点阵单元大小（像素，越大越稀疏）
let depthDotSizeMin = 3;     // 最小点直径（像素）
let depthDotSizeMax = 10;    // 最大点直径（像素）
let depthDotAlpha = 102;     // 点透明度（0..255）

// 新增：手势与按键共同控制点径
let handSizeNorm = 0.5;      // 0..1，手势影响（65%权重）
let wsSizeNorm = 0.5;        // 0..1，W/S影响（35%权重）
let effectiveDotSizeMin = 2; // 每帧计算后的实际最小点径
let effectiveDotSizeMax = 10; // 每帧计算后的实际最大点径

// 新增：手势控制点云位移（不再用于主点云，仅保留变量以兼容旧逻辑）
let cloudOffsetX = 0;
let cloudOffsetY = 0;
let targetCloudOffsetX = 0;
let targetCloudOffsetY = 0;
let maxCloudOffset = 300; // 600像素直径的一半
let lastHandCenterX = 0;
let lastHandCenterY = 0;
let isFirstHandDetect = true;

// 新增：手势连线方向驱动的全局位移（平滑）
let handDirOffsetX = 0;
let handDirOffsetY = 0;
let targetHandDirOffsetX = 0;
let targetHandDirOffsetY = 0;
let maxHandDirOffset = 120; // 最大偏移幅度（像素）

// 新增：手势驱动的呼吸波方向（单位向量，默认沿对角线右下→左上）
let waveDirX = 0.7071;
let waveDirY = 0.7071;
let targetWaveDirX = 0.7071;
let targetWaveDirY = 0.7071;
let waveDirSmoothing = 0.20;
const WAVE_SPATIAL_K = 0.0212; // ≈ 0.015 * sqrt(2)，匹配原 (x+y)*0.015 的空间频率

// 新增：封面“stitch”动效参数（Maison Margiela 风格）
const STITCH_LEN = 80;   // 矩形长度
const STITCH_THICK = 8; // 矩形宽度（厚度）
const STITCH_SMOOTH = 0.18; // 插值平滑
let stitchParam = 0;     // 0→尾端在屏幕角；1→靠近中心矩形角

// 新增：渲染优化（缓存摄像头点阵层、手势平滑）
let bgLayer;
let bgUpdateInterval = 4; // 每4帧重绘一次摄像头点阵
let bgFrameCounter = 0;

let thumbDisplay = { x: 0, y: 0 };
let indexDisplay = { x: 0, y: 0 };
let handTargetsInitialized = false;
let handSmoothing = 0.35; // 每帧向目标插值的比例

// 新增：覆盖页与淡出逻辑
let coverState = 'waiting'; // 'waiting' | 'fading' | 'done'
let coverOpacity = 255;
const COVER_FADE_MS = 2000;
let coverFadeStartMs = 0;
const COVER_CLICK_W = 800;
const COVER_CLICK_H = 70;

function preload() {
  handPose = ml5.handPose();
}

function setup() {
  canvasRef = createCanvas(windowWidth, windowHeight);
  pixelDensity(1); // 降低高DPI额外开销
  noFill();
  stroke(255, 99);

  // 支持拖拽 MP3 文件到画布加载
  if (canvasRef && canvasRef.drop) {
    canvasRef.drop(handleFile);
  }

  // 降低视频输入分辨率到 320×240
  video = createCapture(VIDEO);
  video.size(320, 240);
  video.hide();

  // 不直接 detectStart，而是手动调用 detect
  // 因为我们要控制检测频率
  // 初始化先检测一次
  handPose.detect(video, gotHands);

  // 缓存层初始化
  bgLayer = createGraphics(width, height);
  // 自适应：根据视口更新最大手势位移半径
  maxCloudOffset = min(width, height) * 0.3;

  // 随机选出 15 个 glow 点
  let numGlow = 15;
  let indices = [];
  while (indices.length < numGlow) {
    let idx = floor(random(3000));
    if (!indices.includes(idx)) {
      indices.push(idx);
    }
  }
  glowPoints = indices;

  // 先生成一次 glowTexture
  generateGlowTexture(250, 8, featherPower);

  // 初始化幅度分析器（音频加载后再 setInput(sound)）
  amplitudeAnalyzer = new p5.Amplitude(0.8);
}

function draw() {
  // 每隔 3 帧调用一次手部检测
  frameCountSinceLastDetect++;
  if (frameCountSinceLastDetect >= 3) {
    handPose.detect(video, gotHands);
    frameCountSinceLastDetect = 0;
  }

  // 更新音量，并将其映射为背景 sin 的自变量
  if (amplitudeAnalyzer) {
    micLevelRaw = amplitudeAnalyzer.getLevel(); // 0..~1（通常音乐 0..0.3 左右）
    micLevelSmoothed = lerp(micLevelSmoothed, micLevelRaw, 0.2);
    const clamped = constrain(micLevelSmoothed, 0, micPhaseMaxLevel);
    audioPhase = map(clamped, 0, micPhaseMaxLevel, 0, TWO_PI);
  } else {
    micLevelRaw = 0;
    micLevelSmoothed = lerp(micLevelSmoothed, 0, 0.2);
    audioPhase = 0;
  }

  // 新增：计算音量剧烈程度（帧间差分）
  {
    const cur = constrain(micLevelSmoothed, 0, 1);
    const delta = abs(cur - audioLevelPrev);
    const raw = constrain(delta * severityGain, 0, 1);
    audioSeverity = lerp(audioSeverity, raw, 0.35);
    audioLevelPrev = cur;
  }

  // 覆盖页：等待状态直接盖黑并显示提示，避免额外计算
  if (coverState === 'waiting') {
    background(0);
    drawCoverOverlay();
    return;
  }

  // 新增：音量阈值触发全局半径扩张（阈值0.415 → 触发2.1x），并在1s内线性回落
  if (micLevelSmoothed >= 0.415) {
    radiusPulse = max(radiusPulse, 2.1);
  }
  if (radiusPulse > 1) {
    // 线性衰减：从1.5降到1，在1s内完成
    const decayPerMs = 0.5 / 1000; // 每毫秒减少的半径倍率
    radiusPulse = max(1, radiusPulse - decayPerMs * (deltaTime || 16.67));
  }

  // 新增：音量阈值触发 t 步长修改（>=0.410 → 立刻切到 80；在2s内恢复到 30）
  if (micLevelSmoothed >= 0.420) {
    tStepDenomCurrent = tStepDenomTriggered; // 立即使用 80
    tStepRecoveryMs = T_STEP_RECOVERY_MS;    // 重置恢复计时
  }
  if (tStepRecoveryMs > 0) {
    const dt = (deltaTime || 16.67);
    tStepRecoveryMs = max(0, tStepRecoveryMs - dt);
    const k = 1 - (tStepRecoveryMs / T_STEP_RECOVERY_MS); // 0→1
    // 从 80 线性过渡回 30：current = 80 + k*(30-80)
    tStepDenomCurrent = tStepDenomTriggered + k * (tStepDenomBase - tStepDenomTriggered);
  } else {
    tStepDenomCurrent = tStepDenomBase;
  }

  updateFeatherPowerFromHands();
  updateCloudOffsetFromHands(); // 新增：根据手势更新点云偏移
  updateHandDirectionOffset();  // 新增：根据手势连线方向更新全局位移
  updateWaveDirectionFromHand(); // 新增：根据手势连线方向更新呼吸波方向

  // 合成点径控制（手势75% + W/S 25%），映射到尺寸缩放 0.6..4.5（你已调大）
  {
    const mix = constrain(0.75 * handSizeNorm + 0.25 * wsSizeNorm, 0, 1);
    const sizeScale = lerp(0.6, 4.5, mix);
    effectiveDotSizeMin = depthDotSizeMin * sizeScale;
    effectiveDotSizeMax = depthDotSizeMax * sizeScale;
  }

  drawMainScene();
  // drawPlayButton(); // 已取消播放按钮
  drawHandUI();
  drawCoverOverlay(); // 叠加覆盖页淡出
}

// --- 绘制主点云 ---
function drawMainScene() {
  // 使用时间 t 与音量共同驱动背景的 sin（音量权重80%，t权重20%）
  let tInfluence = sin(t) * 0.2; // t只影响20%范围
  let volumeInfluence = sin(audioPhase) * 0.8; // 音量影响80%范围
  let combinedValue = tInfluence + volumeInfluence;
  let blueVal = map(combinedValue, -1, 1, 0, 255);
  let bgCol = color(blueVal, 72, 231);
  background(bgCol);

  // 缓存的摄像头灰度点阵背景
  updateDepthLayer();
  image(bgLayer, 0, 0);

  // 推进时间（用于背景动画）
  t += PI / tStepDenomCurrent;
}

// 左上角音量 HUD（只显示数字，隐藏滑动条）
function drawAudioHUD() {
  resetMatrix();
  const x = 16;
  const y = 90; // 往下偏一点，避免与按钮重叠
  const barWidth = 220;

  // 背板
  noStroke();
  fill(0, 120);
  rect(x - 8, y - 8, barWidth + 160, 32, 6);

  // 数值
  fill(255);
  textSize(20);
  textAlign(LEFT, TOP);
  const status = isSoundLoaded ? (isPlaying ? 'playing' : 'paused') : 'drop mp3';
  text(`audio: ${micLevelSmoothed.toFixed(3)}  (${status})`, x, y);
}

// 新增：覆盖页绘制与淡出
function drawCoverOverlay() {
  if (coverState === 'done') return;

  let alpha = 255;
  if (coverState === 'fading') {
    const elapsed = millis() - coverFadeStartMs;
    const k = constrain(elapsed / COVER_FADE_MS, 0, 1);
    alpha = round(255 * (1 - k));
    if (k >= 1) {
      coverState = 'done';
    }
  }

  push();
  resetMatrix();
  noStroke();
  fill(0, alpha);
  rect(0, 0, width, height);

  // 新增：stitch 动效（先绘制在文字下层）
  drawCoverStitches(alpha);

  // 提示文字（白色，Times New Roman，20px，居中）
  fill(255, alpha);
  textAlign(CENTER, CENTER);
  textFont('Times New Roman');
  const line1 = 'Drag music into the page, make sure the camera permission is turned on, and press F11 to enter full screen for better effect';
  const line2 = 'when you are ready, click the middle area to start - Press spacebar to play/cancel the song.';
  const size1 = 20;
  const size2 = 30;
  const gap = 10;
  const blockH = size1 + gap + size2;
  const yTop = height / 2 - blockH / 2;
  const y1 = yTop + size1 / 2;
  const y2 = yTop + size1 + gap + size2 / 2;
  textSize(size1);
  text(line1, width / 2, y1);
  textSize(size2);
  text(line2, width / 2, y2);
  pop();
}

// 新增：绘制封面四个“stitch”灰色矩形（随鼠标距离插值位置）
function drawCoverStitches(alpha) {
  // 自适应中心点击区域
  const clickW = min(width * 0.6, COVER_CLICK_W);
  const clickH = min(height * 0.25, COVER_CLICK_H);
  const cx = width / 2;
  const cy = height / 2;

  // 计算鼠标与中心矩形的最短距离（在矩形内为0）
  const left = cx - clickW / 2;
  const right = cx + clickW / 2;
  const top = cy - clickH / 2;
  const bottom = cy + clickH / 2;
  const dx = max(max(left - mouseX, 0), mouseX - right);
  const dy = max(max(top - mouseY, 0), mouseY - bottom);
  const distToRect = sqrt(dx * dx + dy * dy);
  const distMax = 0.6 * sqrt(width * width + height * height);
  const targetParam = constrain(distToRect / max(1, distMax), 0, 1);
  stitchParam = lerp(stitchParam, targetParam, STITCH_SMOOTH);

  // 四个屏幕角与中心矩形角
  const cornersScreen = [
    { x: 0, y: 0 },
    { x: width, y: 0 },
    { x: 0, y: height },
    { x: width, y: height },
  ];
  const cornersRect = [
    { x: left, y: top },
    { x: right, y: top },
    { x: left, y: bottom },
    { x: right, y: bottom },
  ];

  noStroke();
  fill(180, alpha); // 灰色
  rectMode(CORNER);

  for (let i = 0; i < 4; i++) {
    const s = cornersScreen[i];
    const r = cornersRect[i];
    const dirX = r.x - s.x;
    const dirY = r.y - s.y;
    const segLen = max(1, sqrt(dirX * dirX + dirY * dirY));
    const nx = dirX / segLen;
    const ny = dirY / segLen;

    // 使矩形“头部”不越过中心矩形角：尾端插值上限
    const tMax = max(0, 1 - STITCH_LEN / segLen);
    const tTail = stitchParam * tMax;

    const tailX = s.x + tTail * dirX;
    const tailY = s.y + tTail * dirY;

    push();
    translate(tailX, tailY);
    rotate(atan2(ny, nx));
    rect(0, -STITCH_THICK / 2, STITCH_LEN, STITCH_THICK, 3);
    pop();
  }
}

// 左上角播放按钮（亮蓝色，透明度 50%）
function drawPlayButton() {}

// 新增：摄像头灰度深度点阵背景
function drawDepthDotBackground() {
  if (!video) return;
  const vw = video.width || 320;
  const vh = video.height || 240;

  // 读取像素
  video.loadPixels();
  if (!video.pixels || video.pixels.length === 0) return;

  const cell = max(6, depthDotCell | 0); // 保底，避免过密

  push();
  noStroke();
  for (let y = 0; y < height; y += cell) {
    const vy = floor(map(y, 0, height, 0, vh - 1));
    for (let x = 0; x < width; x += cell) {
      const vx = floor(map(x, 0, width, 0, vw - 1));
      const idx = 4 * (vy * vw + vx);
      const r = video.pixels[idx];
      const g = video.pixels[idx + 1];
      const b = video.pixels[idx + 2];
      // 标准加权灰度（接近人眼感知）
      let luminance = 0.2126 * r + 0.7152 * g + 0.0722 * b; // 0..255
      luminance = constrain(luminance, 0, 255);

      // 点大小映射（亮 -> 大）
      const dotSize = map(luminance, 0, 255, depthDotSizeMin, depthDotSizeMax);

      fill(luminance, depthDotAlpha);
      circle(x, y, dotSize);
    }
  }
  pop();
}

// 新增：仅每隔若干帧把摄像头点阵渲染到缓存层
function updateDepthLayer() {
  if (!bgLayer) return;
  bgFrameCounter++;
  if (bgFrameCounter % bgUpdateInterval !== 0) {
    // 即使不重绘，也做轻度淡化，让拖影更顺滑
    bgLayer.push();
    bgLayer.blendMode(BLEND);
    bgLayer.noStroke();
    bgLayer.fill(0, 0, 0, 8);
    bgLayer.rect(0, 0, width, height);
    bgLayer.pop();
    return;
  }

  if (!video) return;
  const vw = video.width || 320;
  const vh = video.height || 240;

  video.loadPixels();
  if (!video.pixels || video.pixels.length === 0) return;

  const cell = max(6, depthDotCell | 0);

  // 基础时间与速度因子（音量剧烈程度 0..1 → 0.5x..1.5x）
  const timeBase = t;
  const speedFactor = lerp(0.5, 1.5, constrain(audioSeverity, 0, 1));
  const timeAdj = timeBase * speedFactor;

  const warpAmp = 10;     // 位置扭曲振幅
  const wobbleAmp = 5;    // 点位抖动幅度
  const sizeBeat = 0.8;   // 呼吸幅度（相对尺寸）
  const hueShiftBase = 220; // 基础色相
  const hueRange = 160;     // 色相摆动范围
  const satVal = 90;        // 饱和度（%）

  // 拖影：轻度淡化旧内容
  bgLayer.push();
  bgLayer.blendMode(BLEND);
  bgLayer.noStroke();
  bgLayer.fill(0, 0, 0, 30);
  bgLayer.rect(0, 0, width, height);
  bgLayer.pop();

  bgLayer.push();
  bgLayer.colorMode(HSB, 360, 100, 100, 255);
  bgLayer.noStroke();
  bgLayer.blendMode(ADD);

  // 旋转与扭曲（含G键反向与速度因子）
  const cx = width / 2;
  const cy = height / 2;
  const dir = gBoostActive ? -1 : 1;
  const rotMax = 0.35;
  const rotBase = 0.05;
  const rotSpeed = 0.9;
  const rotAngle = dir * (rotBase + rotMax * audioSeverity) * sin(timeAdj * rotSpeed + audioPhase * 0.5);
  const warpAmpEff = warpAmp * (1 + 2.0 * audioSeverity) * (gBoostActive ? 2.5 : 1.0);
  const hueRangeEff = hueRange * (1 + 1.6 * audioSeverity);

  const cosA = cos(rotAngle);
  const sinA = sin(rotAngle);

  // 抖动幅度：仅由音量剧烈程度驱动，并缩放至0.7当前强度
  const jitterScale = 1 + 0.7 * audioSeverity; // 原为（含多因素）更强，这里仅保留音频并降为0.7倍

  for (let y = 0; y < height; y += cell) {
    for (let x = 0; x < width; x += cell) {
      // 坐标先围绕中心旋转
      const px = x - cx;
      const py = y - cy;
      const xR = px * cosA - py * sinA + cx;
      const yR = px * sinA + py * cosA + cy;

      // 新增：叠加手势连线方向的全局位移
      const xR2 = xR + handDirOffsetX;
      const yR2 = yR + handDirOffsetY;

      // 时空扭曲到视频采样坐标（使用 timeAdj 控制速度）
      const wx = xR2
        + dir * warpAmpEff * sin(yR2 * 0.02 + timeAdj * 0.9)
        + 6 * sin((xR2 + yR2) * 0.01 - timeAdj * 0.6);
      const wy = yR2
        + dir * warpAmpEff * cos(xR2 * 0.02 - timeAdj * 0.8)
        + 6 * cos((xR2 - yR2) * 0.012 + timeAdj * 0.7);

      let vx = floor(map(wx, 0, width, 0, vw - 1));
      let vy = floor(map(wy, 0, height, 0, vh - 1));
      // 新增：轻度 clamp 保护，避免越界采样
      const vxClamped = constrain(vx, 0, vw - 1);
      const vyClamped = constrain(vy, 0, vh - 1);

      const idx = 4 * (vyClamped * vw + vxClamped);
      const r = video.pixels[idx];
      const g = video.pixels[idx + 1];
      const b = video.pixels[idx + 2];
      let luminance = 0.2126 * r + 0.7152 * g + 0.0722 * b; // 0..255
      luminance = constrain(luminance, 0, 255);

      // 呼吸式尺寸变化 + 有效点径 + 全局半径脉冲
      const spatial = (waveDirX * x + waveDirY * y) * WAVE_SPATIAL_K;
      const beat = 1.0 + sizeBeat * sin(timeBase * 1.3 + spatial + audioPhase);
      const baseSize = map(luminance, 0, 255, effectiveDotSizeMin, effectiveDotSizeMax);
      const dotSize = baseSize * beat * radiusPulse;

      // 抖动：速度用 timeAdj，幅度用 jitterScale（无手部扰流与脉冲）
      const jx = wobbleAmp * jitterScale * sin(timeAdj * 1.1 + y * 0.03);
      const jy = wobbleAmp * jitterScale * cos(timeAdj * 1.0 + x * 0.03);

      // 色相循环：受剧烈程度放大色相幅度（颜色速度保持原样）
      const hueVal = (hueShiftBase
        + hueRangeEff * 0.5 * sin(timeBase * 0.7 + x * 0.01)
        + 60 * sin(timeBase * 0.9 + y * 0.012 + audioPhase)
        + 180 * micLevelSmoothed) % 360;

      const bri = map(luminance, 0, 255, 20, 100);
      bgLayer.fill(hueVal, satVal, bri, depthDotAlpha);

      // 新增：绘制也叠加小幅手势方向位移，增强整体位移感
      bgLayer.circle(x + jx + handDirOffsetX * 0.25, y + jy + handDirOffsetY * 0.25, dotSize);
    }
  }
  bgLayer.pop();
}

// 新增：根据手势更新点云偏移
function updateCloudOffsetFromHands() {
  if (hands.length > 0) {
    let hand = hands[0];
    let thumbTip = hand.keypoints[4];
    let indexTip = hand.keypoints[8];
    
    if (thumbTip && indexTip) {
      // 计算手势中心点（映射到画布坐标）
      const thumb = mapVideoToCanvas(thumbTip.x, thumbTip.y);
      const index = mapVideoToCanvas(indexTip.x, indexTip.y);
      const handCenterX = (thumb.x + index.x) / 2;
      const handCenterY = (thumb.y + index.y) / 2;
      
      if (isFirstHandDetect) {
        // 第一次检测，记录初始位置
        lastHandCenterX = handCenterX;
        lastHandCenterY = handCenterY;
        isFirstHandDetect = false;
      } else {
        // 计算手势移动方向
        const moveX = handCenterX - lastHandCenterX;
        const moveY = handCenterY - lastHandCenterY;
        
        // 根据移动方向更新目标偏移（同向移动）
        targetCloudOffsetX += moveX * 0.5; // 0.5是灵敏度，可调
        targetCloudOffsetY += moveY * 0.5;
        
        // 限制在600像素直径的圆内
        const currentDist = sqrt(targetCloudOffsetX * targetCloudOffsetX + targetCloudOffsetY * targetCloudOffsetY);
        if (currentDist > maxCloudOffset) {
          const scale = maxCloudOffset / currentDist;
          targetCloudOffsetX *= scale;
          targetCloudOffsetY *= scale;
        }
        
        // 记录当前位置
        lastHandCenterX = handCenterX;
        lastHandCenterY = handCenterY;
      }
    }
  } else {
    // 没有检测到手，重置首次检测标志
    isFirstHandDetect = true;
  }
  
  // 平滑更新实际偏移
  cloudOffsetX = lerp(cloudOffsetX, targetCloudOffsetX, 0.1);
  cloudOffsetY = lerp(cloudOffsetY, targetCloudOffsetY, 0.1);
}

// 新增：根据手势可视化连线方向更新全局位移
function updateHandDirectionOffset() {
  let targetX = 0;
  let targetY = 0;

  if (hands.length > 0) {
    let hand = hands[0];
    let thumbTip = hand.keypoints[4];
    let indexTip = hand.keypoints[8];
    if (thumbTip && indexTip) {
      const thumb = mapVideoToCanvas(thumbTip.x, thumbTip.y);
      const index = mapVideoToCanvas(indexTip.x, indexTip.y);

      const dx = thumb.x - index.x;  // 指向与 UI 连线一致
      const dy = thumb.y - index.y;
      const dist = sqrt(dx * dx + dy * dy);

      // 0..1 强度（与 updateFeatherPowerFromHands 的窗口保持相近）
      let strength = map(dist, 10, 300, 0, 1);
      strength = constrain(strength, 0, 1);

      const len = max(1, dist);
      let nx = dx / len;
      let ny = dy / len;

      const dir = gBoostActive ? -1 : 1; // G 键反向
      const audioScale = lerp(0.9, 1.4, constrain(audioSeverity, 0, 1));
      const boost = gBoostActive ? 1.6 : 1.0;
      const amplitude = maxHandDirOffset * strength * audioScale * boost;

      targetX = dir * nx * amplitude;
      targetY = dir * ny * amplitude;
    }
  }

  targetHandDirOffsetX = targetX;
  targetHandDirOffsetY = targetY;

  // 平滑过渡，避免抖动
  handDirOffsetX = lerp(handDirOffsetX, targetHandDirOffsetX, 0.18);
  handDirOffsetY = lerp(handDirOffsetY, targetHandDirOffsetY, 0.18);
}

// 新增：根据手势更新“呼吸”传播方向（单位向量），默认维持原对角方向
function updateWaveDirectionFromHand() {
  // 默认方向与原 (x+y) 一致（梯度为 [1,1]），保持既有美学
  let tx = 0.7071;
  let ty = 0.7071;

  if (hands.length > 0) {
    let hand = hands[0];
    let thumbTip = hand.keypoints[4];
    let indexTip = hand.keypoints[8];
    if (thumbTip && indexTip) {
      const thumb = mapVideoToCanvas(thumbTip.x, thumbTip.y);
      const index = mapVideoToCanvas(indexTip.x, indexTip.y);
      const dx = thumb.x - index.x;
      const dy = thumb.y - index.y;
      const dist = sqrt(dx * dx + dy * dy);
      if (dist > 8) {
        tx = dx / dist;
        ty = dy / dist;
      }
    }
  }

  // 平滑过渡，避免卡顿与方向抖动
  targetWaveDirX = tx;
  targetWaveDirY = ty;
  waveDirX = lerp(waveDirX, targetWaveDirX, waveDirSmoothing);
  waveDirY = lerp(waveDirY, targetWaveDirY, waveDirSmoothing);
  const len = max(1e-6, sqrt(waveDirX * waveDirX + waveDirY * waveDirY));
  waveDirX /= len;
  waveDirY /= len;
}

// 处理拖拽到画布的文件
function handleFile(file) {
  if (!file) return;
  const isAudio = file.type === 'audio' || (file.name && /\.(mp3|wav|ogg)$/i.test(file.name));
  if (!isAudio) return;

  // 如已有声音，先停止
  if (sound) {
    try { sound.stop(); } catch (e) {}
    try { sound.disconnect(); } catch (e) {}
  }

  loadSound(file.data,
    (s) => {
      sound = s;
      isSoundLoaded = true;
      isPlaying = false;
      if (amplitudeAnalyzer) {
        amplitudeAnalyzer.setInput(sound);
      }
    },
    (err) => {
      isSoundLoaded = false;
      isPlaying = false;
      // 加载失败保持静音状态
    }
  );
}

// 将 320×240 的视频坐标映射到 1920×1080 的画布坐标
function mapVideoToCanvas(x, y) {
  return {
    x: map(x, 0, video.width, 0, width),
    y: map(y, 0, video.height, 0, height),
  };
}

// --- 手势 UI ---
function drawHandUI() {
  resetMatrix();
  if (hands.length > 0) {
    let hand = hands[0];
    let thumbTip = hand.keypoints[4];
    let indexTip = hand.keypoints[8];

    if (thumbTip && indexTip) {
      // 映射后的画布坐标（作为目标）
      const thumbTarget = mapVideoToCanvas(thumbTip.x, thumbTip.y);
      const indexTarget = mapVideoToCanvas(indexTip.x, indexTip.y);

      // 初始化或逐帧插值到目标（在检测间隔的空档也保持运动）
      if (!handTargetsInitialized) {
        thumbDisplay.x = thumbTarget.x;
        thumbDisplay.y = thumbTarget.y;
        indexDisplay.x = indexTarget.x;
        indexDisplay.y = indexTarget.y;
        handTargetsInitialized = true;
      } else {
        thumbDisplay.x = lerp(thumbDisplay.x, thumbTarget.x, handSmoothing);
        thumbDisplay.y = lerp(thumbDisplay.y, thumbTarget.y, handSmoothing);
        indexDisplay.x = lerp(indexDisplay.x, indexTarget.x, handSmoothing);
        indexDisplay.y = lerp(indexDisplay.y, indexTarget.y, handSmoothing);
      }

      // 画布空间的方向/角度与距离（基于平滑后的显示坐标）
      const dxCanvas = thumbDisplay.x - indexDisplay.x;
      const dyCanvas = thumbDisplay.y - indexDisplay.y;
      const distCanvas = sqrt(dxCanvas * dxCanvas + dyCanvas * dyCanvas);

      // 绿色指尖点（平滑后）
      push();
      fill(0, 255, 0);
      noStroke();
      circle(thumbDisplay.x, thumbDisplay.y, 12);
      circle(indexDisplay.x, indexDisplay.y, 12);
      pop();

      // 红色细线（简化版，提高帧率）
      push();
      stroke(255, 50, 50);
      strokeWeight(1);
      line(thumbDisplay.x, thumbDisplay.y, indexDisplay.x, indexDisplay.y);
      pop();

      // featherPower 文本（映射后位置与朝向）
      push();
      textSize(28);
      textAlign(CENTER, CENTER);
      fill(255);
      stroke(0, 180);
      strokeWeight(3);
      const midX = (thumbDisplay.x + indexDisplay.x) / 2;
      const midY = (thumbDisplay.y + indexDisplay.y) / 2;
      const angle = atan2(dyCanvas, dxCanvas);
      const offset = 40;
      const labelX = midX - sin(angle) * offset;
      const labelY = midY + cos(angle) * offset;
      text(`Power - ${distCanvas.toFixed(2)}`, labelX, labelY);
      
      // 音频音量显示（放在featherPower下方并列）
      textSize(20);
      const audioLabelX = labelX;
      const audioLabelY = labelY + 35;
      text(`audio: ${micLevelSmoothed.toFixed(3)}`, audioLabelX, audioLabelY);
      pop();
    }
  }
}

// --- 更新 featherPower ---
function updateFeatherPowerFromHands() {
  if (hands.length > 0) {
    let hand = hands[0];
    let thumbTip = hand.keypoints[4];
    let indexTip = hand.keypoints[8];
    if (thumbTip && indexTip) {
      let dx = thumbTip.x - indexTip.x;
      let dy = thumbTip.y - indexTip.y;
      let distValue = sqrt(dx * dx + dy * dy); // 视频空间距离
      // 距离映射到 0..1（可调窗：10..250 像素）
      let norm = map(distValue, 10, 250, 0, 1);
      norm = constrain(norm, 0, 1);
      // 平滑更新手势影响（主导 65%）
      handSizeNorm = lerp(handSizeNorm, norm, 0.20);
    }
  }
}

// --- 生成光晕 ---
function generateGlowTexture(size = 250, alphaMax = 8, featherP = 2.5) {
  glowTexture = createGraphics(size, size);
  glowTexture.noStroke();
  for (let r = size / 2; r > 0; r--) {
    let norm = r / (size / 2);
    let alpha = alphaMax * pow(1 - norm, featherP);
    glowTexture.fill(255, alpha);
    glowTexture.ellipse(size / 2, size / 2, r * 3);
  }
  lastFeatherPower = featherPower;
}

// --- 手势回调 ---
function gotHands(results) {
  hands = results;
}

// 点击：用于浏览器音频策略与播放按钮交互
function mousePressed() {
  if (getAudioContext().state !== 'running') {
    userStartAudio();
  }

  // 覆盖页点击：仅当处于等待状态时，点击屏幕中心区域开始淡出
  if (coverState === 'waiting') {
    const clickW = min(width * 0.6, COVER_CLICK_W);
    const clickH = min(height * 0.25, COVER_CLICK_H);
    const dx = abs(mouseX - width / 2);
    const dy = abs(mouseY - height / 2);
    if (dx <= clickW / 2 && dy <= clickH / 2) {
      coverState = 'fading';
      coverFadeStartMs = millis();
    }
  }

  // 播放按钮已移除，改为空格键控制
}

// 新增：快捷键调节点阵密度与大小 + G 键反向增强扭动
function keyPressed() {
  // 密度：A 减小密度（更稀疏 / cell 变大），D 增加密度（更密 / cell 变小）
  if (key === 'A' || key === 'a') {
    depthDotCell = min(64, depthDotCell + 2);
  }
  if (key === 'D' || key === 'd') {
    depthDotCell = max(6, depthDotCell - 2);
  }
  // 大小：W 增大最大点径，S 减小最大点径
  if (key === 'W' || key === 'w') {
    wsSizeNorm = min(1, wsSizeNorm + 0.2);
  }
  if (key === 'S' || key === 's') {
    wsSizeNorm = max(0, wsSizeNorm - 0.2);
  }
  // G：按住时反向扭动并增强振幅
  if (key === 'G' || key === 'g') {
    gBoostActive = true;
  }
  // 空格：播放/暂停音频
  if (key === ' ') {
    if (isSoundLoaded && sound) {
      if (sound.isPlaying()) {
        sound.pause();
        isPlaying = false;
      } else {
        sound.loop();
        isPlaying = true;
      }
    }
  }
}

function keyReleased() {
  if (key === 'G' || key === 'g') {
    gBoostActive = false;
  }
}

function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
  // 重建缓存图层以匹配新尺寸
  bgLayer = createGraphics(width, height);
  // 根据新视口更新手势位移上限
  maxCloudOffset = min(width, height) * 0.3;
}
