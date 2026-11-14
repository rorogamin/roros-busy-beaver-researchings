/* Absorbing Tag System (ATS) simulator core for the browser studio. */
(function (global) {
  'use strict';

  const WINDOW = 400;
  const OVERVIEW_SAMPLES = 512;
  const FULL_LIMIT = 2000;
  const MAX_HISTORY = 1000;

  function isFn(token) {
    return typeof token === 'string';
  }

  function tokenLength(token) {
    return isFn(token) ? token.length : 1;
  }

  function countTokenZeros(token) {
    if (isFn(token)) {
      let count = 0;
      for (let i = 0; i < token.length; i++) if (token[i] === '0') count++;
      return count;
    }
    return token === 0 ? 1 : 0;
  }

  function tapeLength(tokens) {
    let total = 0;
    for (const t of tokens) total += tokenLength(t);
    return total;
  }

  function countZeros(tokens) {
    let total = 0;
    for (const t of tokens) total += countTokenZeros(t);
    return total;
  }

  function formatToken(token) {
    return isFn(token) ? `fn(${token})` : String(token);
  }

  function formatTape(tokens) {
    return '[' + tokens.map(formatToken).join(', ') + ']';
  }

  function parseTape(text) {
    let source = String(text || '').trim();
    if (source.startsWith('[') && source.endsWith(']')) {
      source = source.slice(1, -1);
    }
    const tokens = [];
    let i = 0;
    while (i < source.length) {
      while (i < source.length && (/\s/.test(source[i]) || source[i] === ',')) i++;
      if (i >= source.length) break;

      if (source.slice(i, i + 3) === 'fn(') {
        const close = source.indexOf(')', i + 3);
        if (close < 0) throw new Error(`Unclosed fn( at character ${i + 1}`);
        const alpha = source.slice(i + 3, close);
        if (!alpha || !/^[01]+$/.test(alpha)) {
          throw new Error(`Invalid function argument: fn(${alpha})`);
        }
        tokens.push(alpha);
        i = close + 1;
        continue;
      }

      const ch = source[i];
      if (ch === '0' || ch === '1') {
        tokens.push(Number(ch));
        i++;
        continue;
      }

      throw new Error(`Unexpected character ${JSON.stringify(ch)} at offset ${i}`);
    }
    if (!tokens.length) throw new Error('The tape is empty.');
    return tokens;
  }

  function tokenCategory(token) {
    if (token === 1) return 'prim1';
    if (token === 0) return 'prim0';
    if (token === '1') return 'fn1';
    let zeros = 0;
    let ones = 0;
    for (let i = 0; i < token.length; i++) {
      if (token[i] === '0') zeros++;
      else ones++;
    }
    if (zeros === 0) return 'fnone';
    if (ones === 0) return 'fnzero';
    return 'fnmix';
  }

  class ATSSimulator {
    constructor(tokens) {
      this.reset(tokens);
    }

    reset(tokens) {
      this.initialTokens = tokens.slice();
      this.tape = tokens.slice();
      this.start = 0;
      this.steps = 0;
      this.halted = false;
      this.proof = null;
      this.zeros = countZeros(tokens);
      this.length = tapeLength(tokens);
      this.nonFn1 = 0;
      this.types = new Set();
      for (const t of tokens) {
        this.types.add(t);
        if (t !== '1') this.nonFn1++;
      }
      this.decreases = 0;
      this.maxTokens = tokens.length;
      this.maxLength = this.length;
      this.history = [];
      this.snapshotInterval = 1;
      this.nextSnapshot = 1;
      this._lastTokenCount = tokens.length;
      this._capture();
    }

    tokens() {
      return this.tape.length - this.start;
    }

    tokenAt(index) {
      return this.tape[this.start + index];
    }

    _append(token) {
      this.tape.push(token);
      this.types.add(token);
      this.zeros += countTokenZeros(token);
      this.length += tokenLength(token);
      if (token !== '1') this.nonFn1++;
    }

    _popHead() {
      if (this.start >= this.tape.length) return undefined;
      const token = this.tape[this.start++];
      this.zeros -= countTokenZeros(token);
      this.length -= tokenLength(token);
      if (token !== '1') this.nonFn1--;
      this._maybeTrim();
      return token;
    }

    _popTail() {
      if (this.start >= this.tape.length) return undefined;
      const token = this.tape.pop();
      this.zeros -= countTokenZeros(token);
      this.length -= tokenLength(token);
      if (token !== '1') this.nonFn1--;
      return token;
    }

    _maybeTrim() {
      if (this.start > 4096 && this.start * 2 > this.tape.length) {
        this.tape = this.tape.slice(this.start);
        this.start = 0;
      }
    }

    _absorb() {
      let j = this.start + 1;
      while (j < this.tape.length - 1) {
        const left = this.tape[j];
        const right = this.tape[j + 1];
        if (isFn(left) && !isFn(right)) {
          const next = String(right) + left;
          if (left === '1' && next !== '1') this.nonFn1++;
          this.tape[j] = next;
          this.types.add(next);
          this.tape.splice(j + 1, 1);
          continue;
        }
        j++;
      }
    }

    _oneRule(alpha) {
      const idx = alpha.indexOf('1');
      let rest;
      if (alpha.length > 3) {
        rest = alpha.slice(0, idx) + alpha.slice(idx + 1);
      } else {
        rest = alpha.slice(1);
      }
      this._append('1');
      if (rest) this._append(rest);
    }

    _zeroRule() {
      this._popTail();
    }

    step() {
      if (this.halted) return false;
      if (this.tokens() === 0) {
        this.halted = true;
        return false;
      }

      this._absorb();
      const head = this._popHead();

      if (head === 0) {
        /* primitive zero: nothing */
      } else if (head === 1) {
        const next = this.tape.slice(this.start, this.start + 2);
        for (const token of next) this._append(token);
      } else if (head === '1') {
        const next = this.tape.slice(this.start, this.start + 2);
        for (const token of next) this._append(token);
      } else if (head !== undefined) {
        const alpha = head;
        let c0 = 0;
        let c1 = 0;
        for (let i = 0; i < alpha.length; i++) {
          if (alpha[i] === '0') c0++;
          else c1++;
        }

        if (c1 === 0) {
          /* pure-zero function: behaves as a lone 0 */
        } else {
          const oneFirst = c0 === 0 || c1 > c0 || (c1 === c0 && alpha[0] === '1');
          if (oneFirst) {
            this._oneRule(alpha);
            if (c0 > 0) this._zeroRule();
          } else {
            this._zeroRule();
            this._oneRule(alpha);
          }
        }
      }

      this.steps++;
      const current = this.tokens();
      if (current < this._lastTokenCount) this.decreases++;
      this._lastTokenCount = current;
      if (current > this.maxTokens) this.maxTokens = current;
      if (this.length > this.maxLength) this.maxLength = this.length;

      if (current === 0) {
        this.halted = true;
      } else if (this.zeros === 0 && current >= 2) {
        this.proof = 'zero-free';
      }

      if (this.steps >= this.nextSnapshot) {
        if (this.history.length >= MAX_HISTORY) this._thinHistory();
        this._capture();
        this.nextSnapshot = this.steps + this.snapshotInterval;
      }
      return true;
    }

    advance(count) {
      const n = Math.max(0, Math.floor(count));
      for (let i = 0; i < n; i++) {
        if (!this.step()) break;
      }
      return this.steps;
    }

    _thinHistory() {
      const kept = [];
      for (let i = 0; i < this.history.length; i += 2) kept.push(this.history[i]);
      if (kept.length && kept[kept.length - 1] !== this.history[this.history.length - 1]) {
        kept.push(this.history[this.history.length - 1]);
      }
      this.history = kept;
      this.snapshotInterval *= 2;
    }

    _capture() {
      const n = this.tokens();
      const end = this.tape.length;
      const full = n <= FULL_LIMIT ? this.tape.slice(this.start) : null;
      const head = full
        ? full.slice(0, WINDOW)
        : this.tape.slice(this.start, Math.min(end, this.start + WINDOW));
      const tail = full
        ? full.slice(Math.max(0, full.length - WINDOW))
        : this.tape.slice(Math.max(this.start, end - WINDOW));
      let overview = null;
      if (!full) {
        overview = new Array(OVERVIEW_SAMPLES);
        for (let i = 0; i < OVERVIEW_SAMPLES; i++) {
          const index = this.start + Math.floor((i * n) / OVERVIEW_SAMPLES);
          overview[i] = tokenCategory(this.tape[Math.min(end - 1, index)]);
        }
      }
      this.history.push({
        step: this.steps,
        count: n,
        zeros: this.zeros,
        length: this.length,
        nonFn1: this.nonFn1,
        maxTokens: this.maxTokens,
        types: this.types.size,
        decreases: this.decreases,
        proof: this.proof,
        full,
        head,
        tail,
        overview,
      });
    }
  }

  global.ATSCore = {
    ATSSimulator,
    WINDOW,
    OVERVIEW_SAMPLES,
    FULL_LIMIT,
    isFn,
    tokenLength,
    tapeLength,
    countZeros,
    countTokenZeros,
    formatToken,
    formatTape,
    parseTape,
    tokenCategory,
  };
})(window);
