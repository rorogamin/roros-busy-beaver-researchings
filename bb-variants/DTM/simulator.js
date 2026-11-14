/**
 * Double Turing Machine (DTM) Simulator Engine (Client-side interactive runtime)
 *
 * Supports:
 *   - DTM(n, m)       : 2 rules, each n states x m symbols
 *   - DTM(n, m, a)    : a rules, cycling modulo a (Rule 1 .. Rule a)
 *   - DTM(n, m, a, b) : 2 rules with independent (n,m) and (a,b) table sizes
 *
 * Step semantics:
 *   - Single shared state register starting at A (0), head at 0, tape initially all 0.
 *   - At step t, active rule = rules[t % rules.length].
 *   - Standard Rado / BusyBeaverWiki S(n) step counting: halting transition takes +1 step.
 *   - Out-of-range state/symbol for active rule halts identically to undefined '---'.
 */

(function (global) {
  'use strict';

  function parseRuleString(ruleStr) {
    const blocks = ruleStr.trim().split('_');
    if (!blocks.length || !blocks[0] || blocks[0].length % 3 !== 0) {
      throw new Error(`Invalid rule string: "${ruleStr}"`);
    }
    const states = blocks.length;
    const symbols = blocks[0].length / 3;
    const table = [];
    for (let s = 0; s < states; s++) {
      if (blocks[s].length !== 3 * symbols) {
        throw new Error(`Inconsistent block width in rule: "${ruleStr}"`);
      }
      const row = [];
      for (let y = 0; y < symbols; y++) {
        const tok = blocks[s].slice(3 * y, 3 * y + 3);
        if (tok === '---') {
          row.push(null);
        } else {
          const w = parseInt(tok[0], 10);
          const dChar = tok[1];
          const sChar = tok[2];
          if (Number.isNaN(w) || (dChar !== 'L' && dChar !== 'R')) {
            throw new Error(`Bad transition token "${tok}"`);
          }
          const nx = (sChar === 'Z' || sChar === 'H') ? -1 : (sChar.charCodeAt(0) - 65);
          if (nx < -1 || nx > 25) {
            throw new Error(`Bad next state "${sChar}" in "${tok}"`);
          }
          row.push({ write: w, dir: dChar === 'R' ? 1 : -1, nextState: nx });
        }
      }
      table.push(row);
    }
    return { states, symbols, table };
  }

  function formatRule(rule) {
    return rule.table
      .map((row) =>
        row
          .map((tr) => {
            if (!tr) return '---';
            const d = tr.dir > 0 ? 'R' : 'L';
            const s = tr.nextState < 0 ? 'Z' : String.fromCharCode(65 + tr.nextState);
            return `${tr.write}${d}${s}`;
          })
          .join('')
      )
      .join('_');
  }

  function parseRuleOrder(orderStr, numRules) {
    let s = orderStr.trim();
    if (s.startsWith('{') && s.endsWith('}')) s = s.slice(1, -1).trim();
    if (!s) throw new Error('Empty rule order');
    const tokens = [];
    const re = /[rR](\d+)/g;
    let rebuilt = '';
    let m;
    while ((m = re.exec(s)) !== null) {
      const idx = parseInt(m[1], 10) - 1;
      if (idx < 0 || (numRules !== undefined && idx >= numRules)) {
        throw new Error(`Rule r${idx + 1} out of range for ${numRules} rules`);
      }
      tokens.push(idx);
      rebuilt += `r${m[1]}`;
    }
    const cleaned = s.replace(/[,\s\-]+/g, '').toLowerCase();
    if (!tokens.length || rebuilt.toLowerCase() !== cleaned) {
      throw new Error(`Invalid rule order "${orderStr}" (expected e.g. r1r2r3r2r1r2r2)`);
    }
    return tokens;
  }

  function formatRuleOrder(order) {
    return order.map((r) => `r${r + 1}`).join('');
  }

  function isIdentityOrder(order, numRules) {
    if (!order || order.length !== numRules) return false;
    for (let i = 0; i < numRules; i++) {
      if (order[i] !== i) return false;
    }
    return true;
  }

  function parseDTMSpec(spec) {
    let raw = spec.trim();
    let order = null;
    const match = raw.match(/@?\{([^}]*)\}\s*$/);
    if (match) {
      order = parseRuleOrder(match[1]);
      raw = raw.slice(0, match.index).trim();
    }
    const parts = raw
      .split('|')
      .map((p) => p.trim())
      .filter(Boolean);
    if (!parts.length) throw new Error('Empty DTM specification');
    const rules = parts.map(parseRuleString);
    if (order) {
      for (const r of order) {
        if (r < 0 || r >= rules.length) {
          throw new Error(`Rule r${r + 1} out of range for ${rules.length} rules`);
        }
      }
      if (isIdentityOrder(order, rules.length)) order = null;
    }
    rules.order = order;
    return rules;
  }

  function formatDTMSpec(rules) {
    const base = rules.map(formatRule).join('|');
    if (rules.order && !isIdentityOrder(rules.order, rules.length)) {
      return `${base}{${formatRuleOrder(rules.order)}}`;
    }
    return base;
  }

  function dtmSignature(rules) {
    const k = rules.length;
    const r0 = rules[0];
    if (rules.order && !isIdentityOrder(rules.order, k)) {
      const ordStr = formatRuleOrder(rules.order);
      if (rules.every((r) => r.states === r0.states && r.symbols === r0.symbols)) {
        return `DTM(${r0.states},${r0.symbols},${k},{${ordStr}})`;
      }
      return `DTM[${rules.map((r) => `${r.states}x${r.symbols}`).join(',')};{${ordStr}}]`;
    }
    if (k === 2) {
      const r1 = rules[1];
      if (r0.states === r1.states && r0.symbols === r1.symbols) {
        return `DTM(${r0.states},${r0.symbols})`;
      }
      return `DTM(${r0.states},${r0.symbols},${r1.states},${r1.symbols})`;
    }
    if (rules.every((r) => r.states === r0.states && r.symbols === r0.symbols)) {
      return `DTM(${r0.states},${r0.symbols},${k})`;
    }
    return `DTM[${rules.map((r) => `${r.states}x${r.symbols}`).join(',')}]`;
  }

  function toEquivalentStandardTM(rules) {
    const k = rules.length;
    const r0 = rules[0];
    if (!rules.every((r) => r.states === r0.states && r.symbols === r0.symbols)) {
      return null;
    }
    const sched = (rules.order && rules.order.length) ? rules.order : Array.from({ length: k }, (_, i) => i);
    const L = sched.length;
    const n = r0.states;
    if (L * n > 25) return null;
    const blocks = [];
    for (let p = 0; p < L; p++) {
      const rule = rules[sched[p]];
      const np = (p + 1) % L;
      for (let s = 0; s < n; s++) {
        let blk = '';
        for (let y = 0; y < r0.symbols; y++) {
          const tr = rule.table[s][y];
          if (!tr) blk += '---';
          else if (tr.nextState < 0) blk += `${tr.write}${tr.dir > 0 ? 'R' : 'L'}Z`;
          else blk += `${tr.write}${tr.dir > 0 ? 'R' : 'L'}${String.fromCharCode(65 + np * n + tr.nextState)}`;
        }
        blocks.push(blk);
      }
    }
    return blocks.join('_');
  }

  class DTMSimulator {
    constructor(spec) {
      this.rules = parseDTMSpec(spec || '1RA1LA|1LA1RZ');
      this.reset();
    }

    setRules(rules) {
      this.rules = rules;
      this.reset();
    }

    loadSpec(spec) {
      this.rules = parseDTMSpec(spec);
      this.reset();
    }

    getSpec() {
      return formatDTMSpec(this.rules);
    }

    getSignature() {
      return dtmSignature(this.rules);
    }

    reset() {
      this.tape = new Map();
      this.head = 0;
      this.state = 0;
      this.steps = 0;
      this.halted = false;
      this.haltReason = '';
      this.minPos = 0;
      this.maxPos = 0;
      this.nonZeros = 0;
      this.history = [];
      this.maxHistory = 12000;
    }

    readCell(pos) {
      return this.tape.get(pos) || 0;
    }

    activeScheduleIndex() {
      const len = (this.rules.order && this.rules.order.length) ? this.rules.order.length : this.rules.length;
      return this.steps % len;
    }

    activeRuleIndex() {
      if (this.rules.order && this.rules.order.length) {
        return this.rules.order[this.steps % this.rules.order.length];
      }
      return this.steps % this.rules.length;
    }

    step(recordHistory = true) {
      if (this.halted) return false;
      const rIdx = this.activeRuleIndex();
      const rule = this.rules[rIdx];
      const pos = this.head;
      const sym = this.readCell(pos);
      const st = this.state;

      if (st >= rule.states || sym >= rule.symbols) {
        this.steps += 1;
        this.halted = true;
        this.haltReason = st >= rule.states
          ? `State ${String.fromCharCode(65 + st)} out of bounds in Rule ${rIdx + 1}`
          : `Symbol ${sym} out of bounds in Rule ${rIdx + 1}`;
        if (recordHistory && this.history.length < this.maxHistory) {
          this.history.push({ step: this.steps, ruleIdx: rIdx, state: st, pos, write: sym, nextPos: pos, nextState: -1, halted: true });
        }
        return false;
      }

      const tr = rule.table[st][sym];
      if (!tr) {
        this.steps += 1;
        this.halted = true;
        this.haltReason = `Undefined (---) at Rule ${rIdx + 1}, ${String.fromCharCode(65 + st)}${sym}`;
        if (recordHistory && this.history.length < this.maxHistory) {
          this.history.push({ step: this.steps, ruleIdx: rIdx, state: st, pos, write: sym, nextPos: pos, nextState: -1, halted: true });
        }
        return false;
      }

      if (sym === 0 && tr.write !== 0) this.nonZeros += 1;
      else if (sym !== 0 && tr.write === 0) this.nonZeros -= 1;

      if (tr.write === 0) this.tape.delete(pos);
      else this.tape.set(pos, tr.write);

      if (pos < this.minPos) this.minPos = pos;
      if (pos > this.maxPos) this.maxPos = pos;

      this.head = pos + tr.dir;
      if (this.head < this.minPos) this.minPos = this.head;
      if (this.head > this.maxPos) this.maxPos = this.head;

      this.steps += 1;
      const didHalt = tr.nextState < 0;
      if (didHalt) {
        this.halted = true;
        this.state = -1;
        this.haltReason = `Halted via ${tr.write}${tr.dir > 0 ? 'R' : 'L'}Z (Rule ${rIdx + 1}, ${String.fromCharCode(65 + st)}${sym})`;
      } else {
        this.state = tr.nextState;
      }

      if (recordHistory && this.history.length < this.maxHistory) {
        this.history.push({
          step: this.steps,
          ruleIdx: rIdx,
          state: st,
          pos,
          write: tr.write,
          nextPos: this.head,
          nextState: tr.nextState,
          halted: didHalt,
        });
      }
      return !this.halted;
    }

    runSteps(count, recordHistory = true) {
      let ran = 0;
      for (let i = 0; i < count && !this.halted; i++) {
        this.step(recordHistory);
        ran += 1;
      }
      return ran;
    }
  }

  global.DTMCore = {
    parseRuleString,
    parseRuleOrder,
    formatRuleOrder,
    formatRule,
    parseDTMSpec,
    formatDTMSpec,
    dtmSignature,
    toEquivalentStandardTM,
    DTMSimulator,
  };
})(typeof window !== 'undefined' ? window : globalThis);
