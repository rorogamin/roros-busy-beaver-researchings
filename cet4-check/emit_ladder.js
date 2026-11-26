#!/usr/bin/env node
'use strict';
/*
 * Emit proof/CET4/Ladder.lean from ../ladder.json.
 *
 * Every transition table is derived mechanically from the spec strings, so the
 * Lean ladder cannot drift from the pipeline's ladder through transcription
 * error. Re-run after any change to ladder.json:
 *
 *   node emit_ladder.js
 *
 * Spec format (as parsed by cet_pair_sim.js): blocks separated by '_', one per
 * state; within a block, 3 chars per input symbol: <write><dir><next>, with dir
 * in {L,R} and next in {A,B,C,D}.
 */
const fs = require('fs');
const path = require('path');

const ladderPath = path.join(__dirname, '..', 'ladder.json');
const outPath = path.join(__dirname, 'CET4', 'Ladder.lean');

const j = JSON.parse(fs.readFileSync(ladderPath, 'utf8'));
const byId = new Map(j.entries.map((e) => [e.id, e]));
// `order` is authoritative; `entries` is NOT in ladder order.
const ordered = j.order.map((id) => {
  const e = byId.get(id);
  if (!e) throw new Error(`ladder.json order references unknown id: ${id}`);
  return e;
});

function parseSpec(spec) {
  const blocks = spec.split('_');
  if (blocks.length !== 4) throw new Error(`expected 4 states: ${spec}`);
  const moves = [];
  for (let q = 0; q < 4; q++) {
    const blk = blocks[q];
    if (blk.length !== 6) throw new Error(`expected 2 symbols in state ${q}: ${spec}`);
    for (let b = 0; b < 2; b++) {
      const w = blk[3 * b];
      const d = blk[3 * b + 1];
      const n = blk[3 * b + 2];
      if (w !== '0' && w !== '1') throw new Error(`bad write '${w}' in ${spec}`);
      if (d !== 'L' && d !== 'R') throw new Error(`bad dir '${d}' in ${spec}`);
      if (!'ABCD'.includes(n)) throw new Error(`bad state '${n}' in ${spec}`);
      moves.push({ write: w === '1', dir: d, next: n.charCodeAt(0) - 65 });
    }
  }
  return moves;
}

/* Inverse of parseSpec, used purely as a self-test: if the moves do not encode
   back to the original spec, the parse indexed something wrongly. */
function encodeSpec(moves) {
  const blocks = [];
  for (let q = 0; q < 4; q++) {
    let blk = '';
    for (let b = 0; b < 2; b++) {
      const m = moves[q * 2 + b];
      blk += `${m.write ? 1 : 0}${m.dir}${String.fromCharCode(65 + m.next)}`;
    }
    blocks.push(blk);
  }
  return blocks.join('_');
}

function ident(s) {
  return s.replace(/[^A-Za-z0-9]/g, '');
}

let out = [];
out.push('/-');
out.push('  GENERATED FILE — do not edit.');
out.push('');
out.push('  Emitted by proof/emit_ladder.js from ../ladder.json, in ladder order.');
out.push('  `ladder.json.order` is authoritative; its `entries` array is not in');
out.push('  ladder order, so enumerating `entries` directly misnumbers machines.');
out.push('-/');
out.push('import CET4.Basic');
out.push('');
out.push('namespace CET4');
out.push('');

for (const e of ordered) {
  const name = ident(e.alias);
  for (const [suffix, spec] of [['A1', e.a1], ['A2', e.a2]]) {
    const moves = parseSpec(spec);
    if (encodeSpec(moves) !== spec) {
      throw new Error(`round-trip mismatch for ${e.alias} ${suffix}: ${encodeSpec(moves)} != ${spec}`);
    }
    out.push(`/-- ${e.alias} agent ${suffix === 'A1' ? '1' : '2'} — \`${spec}\` -/`);
    out.push(`def t${name}${suffix} : Table := fun s b =>`);
    out.push('  match s.val * 2 + (if b then 1 else 0) with');
    moves.forEach((m, i) => {
      out.push(`  | ${i} => ⟨${m.write}, Dir.${m.dir}, ${m.next}⟩`);
    });
    out.push('  | _ => ⟨false, Dir.R, 0⟩');
    out.push('');
  }
}

out.push('/-- The ladder, in order 1..11. -/');
out.push('def Ladder : List Pair := [');
ordered.forEach((e, i) => {
  const name = ident(e.alias);
  const comma = i === ordered.length - 1 ? '' : ',';
  out.push(`  ⟨"${e.alias}", t${name}A1, t${name}A2⟩${comma}`);
});
out.push(']');
out.push('');
out.push('/-- The claimed tower height, as recorded in ladder.json (model output). -/');
out.push('def ClaimedR : List (String × Nat) := [');
ordered.forEach((e, i) => {
  const comma = i === ordered.length - 1 ? '' : ',';
  out.push(`  ("${e.alias}", ${e.R})${comma}`);
});
out.push(']');
out.push('');
out.push('end CET4');
out.push('');

fs.writeFileSync(outPath, out.join('\n'));
console.log(`wrote ${path.relative(process.cwd(), outPath)} (${ordered.length} pairs, ${out.length} lines)`);
console.log(ordered.map((e, i) => `  ${i + 1}. ${e.alias}`).join('\n'));
