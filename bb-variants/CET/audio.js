/**
 * Synthesizer & Sonification Engine for Catch-Em-Turing
 * Built with Web Audio API.
 * Provides subtle retro ambient sound effects:
 * - Tape click/blip on cell write (stereo-panned by cell position)
 * - Step tick (pitch modulated by agent distance)
 * - Triumphant harmonic chime upon collision!
 */

class CETAudio {
  constructor() {
    this.ctx = null;
    this.enabled = false;
    this.volume = 0.25;
  }

  init() {
    if (!this.ctx && (window.AudioContext || window.webkitAudioContext)) {
      const AudioCtx = window.AudioContext || window.webkitAudioContext;
      this.ctx = new AudioCtx();
    }
    if (this.ctx && this.ctx.state === 'suspended') {
      this.ctx.resume();
    }
  }

  toggle() {
    this.enabled = !this.enabled;
    if (this.enabled) {
      this.init();
    }
    return this.enabled;
  }

  playStep(distance = 2, pos = 0) {
    if (!this.enabled || !this.ctx) return;
    try {
      const now = this.ctx.currentTime;
      const osc = this.ctx.createOscillator();
      const gain = this.ctx.createGain();
      const pan = this.ctx.createStereoPanner ? this.ctx.createStereoPanner() : null;

      // Pitch is inversely proportional to distance (closer = higher tension pitch)
      const clampedDist = Math.max(1, Math.min(distance, 50));
      const freq = 200 + (1 / clampedDist) * 600;

      osc.type = 'triangle';
      osc.frequency.setValueAtTime(freq, now);

      gain.gain.setValueAtTime(this.volume * 0.4, now);
      gain.gain.exponentialRampToValueAtTime(0.001, now + 0.04);

      if (pan) {
        const panVal = Math.max(-1, Math.min(pos / 25, 1));
        pan.pan.setValueAtTime(panVal, now);
        osc.connect(gain);
        gain.connect(pan);
        pan.connect(this.ctx.destination);
      } else {
        osc.connect(gain);
        gain.connect(this.ctx.destination);
      }

      osc.start(now);
      osc.stop(now + 0.05);
    } catch (e) {
      // Audio fallback silent
    }
  }

  playCollision() {
    if (!this.enabled || !this.ctx) return;
    try {
      const now = this.ctx.currentTime;
      // Play a sparkling major triad chord (C5 - E5 - G5 - C6)
      const freqs = [523.25, 659.25, 783.99, 1046.50];

      freqs.forEach((freq, idx) => {
        const osc = this.ctx.createOscillator();
        const gain = this.ctx.createGain();

        osc.type = 'sine';
        osc.frequency.setValueAtTime(freq, now + idx * 0.06);

        gain.gain.setValueAtTime(0, now + idx * 0.06);
        gain.gain.linearRampToValueAtTime(this.volume * 0.6, now + idx * 0.06 + 0.02);
        gain.gain.exponentialRampToValueAtTime(0.001, now + idx * 0.06 + 0.6);

        osc.connect(gain);
        gain.connect(this.ctx.destination);

        osc.start(now + idx * 0.06);
        osc.stop(now + idx * 0.06 + 0.7);
      });
    } catch (e) {}
  }
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CETAudio;
}
