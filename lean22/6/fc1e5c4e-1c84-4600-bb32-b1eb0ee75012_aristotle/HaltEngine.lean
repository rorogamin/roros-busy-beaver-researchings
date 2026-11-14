module

/-!
# A bit-packed engine for the level cascade

Letters are bits (`false` = `A`, `true` = `B`), packed eight to a byte, least
significant bit first.  A cell state is the byte `2 * c + f` (`c` the cell
content, `f` the flag).  Everything here is plain executable code, written to
run fast when compiled; its correctness is proved in
`RequestProject/Halt/` (theorem `BCM.Eng.halts_of_check`).
-/

@[expose] public section

namespace HaltEngine

/-! ## One cell step -/

/-- One cell step on the state `st` and letter `x` (`true` = `B`):
`(new state, number of emitted letters, emitted letters as bits)`, with new
state `255` for a halt. -/
def cstep (st : UInt8) (x : Bool) : UInt8 × Nat × Nat :=
  if !x then
    if st < 2 then (7, 1, 1)          -- blank cell: emits B, becomes (3, true)
    else if st < 4 then (5, 1, 0)     -- emits A
    else if st < 6 then (st - 2, 0, 0)
    else if st == 6 then (255, 0, 0)  -- (3, false) on A: halt
    else if st == 7 then (5, 1, 1)    -- emits B
    else (st - 4, 0, 0)
  else
    if st < 4 then (st + 4, 0, 0)
    else if st == 4 then (7, 1, 1)    -- emits B
    else if st == 5 then (5, 2, 1)    -- emits B A
    else if st < 8 then (3, 1, 0)     -- emits A
    else (255, 0, 0)

/-- Run `cstep` over a list of letters: `(new state, count, bits)`; on a halt
the state is `255` and count/bits are those emitted before the halt. -/
def crun (st : UInt8) : List Bool → UInt8 × Nat × Nat
  | [] => (st, 0, 0)
  | x :: xs =>
    let (s1, c1, o1) := cstep st x
    if s1 == 255 then (255, 0, 0) else
    let (s2, c2, o2) := crun s1 xs
    (s2, c1 + c2, o1 + o2 * 2 ^ c1)

/-- The eight letters of a byte. -/
def byteBits (b : UInt8) : List Bool := (List.range 8).map (fun j => b.toNat.testBit j)

/-- Entry `256 * st + b` of the byte tables. -/
def entry (k : Nat) : UInt8 × Nat × Nat :=
  crun (UInt8.ofNat (k / 256)) (byteBits (UInt8.ofNat (k % 256)))

/-- Byte table: new state (`255` = halt somewhere in the byte). -/
def nsT : ByteArray := ⟨(Array.range 2560).map (fun k => (entry k).1)⟩
/-- Byte table: number of emitted letters. -/
def cntT : ByteArray := ⟨(Array.range 2560).map (fun k => UInt8.ofNat (entry k).2.1)⟩
/-- Byte table: emitted letters. -/
def outT : Array UInt32 := (Array.range 2560).map (fun k => UInt32.ofNat (entry k).2.2)

/-! ## Feeding a cell -/

/-- An output accumulator: full bytes `out`, and `al < 8` pending bits `acc`. -/
structure Acc where
  out : ByteArray
  acc : UInt64
  al : Nat

/-- Append `c ≤ 24` bits `o` to the accumulator. -/
@[inline] def Acc.add (a : Acc) (c : Nat) (o : UInt64) : Acc :=
  let acc := a.acc ||| (o <<< a.al.toUInt64)
  let al := a.al + c
  if al < 8 then ⟨a.out, acc, al⟩
  else if al < 16 then ⟨a.out.push acc.toUInt8, acc >>> 8, al - 8⟩
  else if al < 24 then ⟨(a.out.push acc.toUInt8).push (acc >>> 8).toUInt8, acc >>> 16, al - 16⟩
  else ⟨((a.out.push acc.toUInt8).push (acc >>> 8).toUInt8).push (acc >>> 16).toUInt8,
    acc >>> 24, al - 24⟩

/-- Result of feeding letters to a cell. -/
inductive FR
  | ok (st : UInt8) (a : Acc)
  | halt (quiet : Bool)

/-- Feed the `nb` full bytes `inp[i], …` to a cell in state `st`. -/
def feedBytes (inp : ByteArray) (i : Nat) (st : UInt8) (a : Acc) : Nat → FR
  | 0 => .ok st a
  | nb + 1 =>
    let k := st.toNat * 256 + (inp.get! i).toNat
    let ns := nsT.get! k
    if ns == 255 then
      .halt (a.out.size == 0 && a.al == 0 && (crun st (byteBits (inp.get! i))).2.1 == 0)
    else feedBytes inp (i + 1) ns (a.add (cntT.get! k).toNat (outT[k]!).toUInt64) nb

/-- Feed the letters `bs` one at a time. -/
def feedBits (st : UInt8) (a : Acc) : List Bool → FR
  | [] => .ok st a
  | x :: xs =>
    let (ns, c, o) := cstep st x
    if ns == 255 then .halt (a.out.size == 0 && a.al == 0)
    else feedBits ns (a.add c (UInt64.ofNat o)) xs

/-- Feed the first `n` letters of `inp`, starting at byte `i`. -/
def feed (inp : ByteArray) (i n : Nat) (st : UInt8) (a : Acc) : FR :=
  match feedBytes inp (i) st a (n / 8) with
  | .ok st' a' =>
    if n % 8 == 0 then .ok st' a' else
    feedBits st' a' ((byteBits (inp.get! (i + n / 8))).take (n % 8))
  | r => r

/-- Close an accumulator: the bytes and the number of letters. -/
def Acc.close (a : Acc) : ByteArray × Nat :=
  if a.al == 0 then (a.out, 8 * a.out.size) else (a.out.push a.acc.toUInt8, 8 * a.out.size + a.al)

/-- A fresh accumulator with the given capacity. -/
def Acc.fresh (cap : Nat) : Acc := ⟨ByteArray.emptyWithCapacity cap, 0, 0⟩

/-! ## Periodic level words -/

/-- Initial state of cell `p`: every cell of the right half-tape starts blank. -/
def initSt (_p : Nat) : UInt8 := 0

/-- An eventually periodic level word `x y^ω` (bytes and letter counts), with
the bookkeeping `a, b`: the level word of the arrival prefix of length
`1 + 5 * (a + b * k)` is `x y^k`. -/
structure PW where
  x : ByteArray
  nx : Nat
  y : ByteArray
  ny : Nat
  a : Nat
  b : Nat

/-- Feed `y` to the cell `r` times. -/
def feedRep (y : ByteArray) (ny : Nat) : Nat → UInt8 → Acc → FR
  | 0, st, a => .ok st a
  | r + 1, st, a =>
    match feed y 0 ny st a with
    | .ok st' a' => feedRep y ny r st' a'
    | h => h

/-- One level step, absorbing `r` periods into the prefix. -/
def PW.tryStep (st : UInt8) (w : PW) (r : Nat) : Option PW :=
  match feed w.x 0 w.nx st (Acc.fresh (w.nx / 8 + 64)) with
  | .halt _ => none
  | .ok s0 a0 =>
    match feedRep w.y w.ny r s0 a0 with
    | .halt _ => none
    | .ok s1 ax =>
      match feed w.y 0 w.ny s1 (Acc.fresh (w.ny / 4 + 64)) with
      | .halt _ => none
      | .ok s2 ay =>
        if s2 == s1 then
          let (x', nx') := ax.close
          let (y', ny') := ay.close
          some ⟨x', nx', y', ny', w.a + r * w.b, w.b⟩
        else
          match feed w.y 0 w.ny s2 ay with
          | .halt _ => none
          | .ok s3 ay2 =>
            if s3 == s1 then
              let (x', nx') := ax.close
              let (y', ny') := ay2.close
              some ⟨x', nx', y', ny', w.a + r * w.b, 2 * w.b⟩
            else none

/-- One level step, absorbing up to two periods if needed. -/
def PW.step (st : UInt8) (w : PW) : Option PW :=
  match w.tryStep st 0 with
  | some v => some v
  | none =>
    match w.tryStep st 1 with
    | some v => some v
    | none => w.tryStep st 2

/-- The level-0 word: the arrival stream `A (BABAB)^ω`, i.e. the bit `0`
followed by the period of bits `1,0,1,0,1`. -/
def pw0 : PW := ⟨⟨#[0]⟩, 1, ⟨#[0b10101]⟩, 5, 0, 1⟩

/-- The periodic level words up to level `q`. -/
def pwUpTo : Nat → Option PW
  | 0 => some pw0
  | q + 1 =>
    match pwUpTo q with
    | none => none
    | some w => w.step (initSt q)

/-! ## Streaming -/

/-- Outcome of pushing a chunk through the levels. -/
inductive CR
  | ok (sts : Array UInt8)
  | halt (lvl : Nat) (quiet : Bool)
  | overflow

/-- Push the letters `inp[i*8 ..][0..n)` through the pipeline levels `j, j+1, …`
(states `sts`). -/
def pushChunk (sts : Array UInt8) (inp : ByteArray) (i n j : Nat) : Nat → CR
  | 0 => .overflow
  | fuel + 1 =>
    if n == 0 then .ok sts else
    if j + 1 ≥ sts.size then .overflow else
    match feed inp i n sts[j]! (Acc.fresh (n / 8 + n / 32 + 64)) with
    | .halt q => .halt j (q && sts[j + 1]! == 0)
    | .ok s a =>
      let (o, m) := a.close
      pushChunk (sts.set! j s) o 0 m (j + 1) fuel

/-- Outcome of streaming. -/
inductive SR
  | halt (lvl : Nat) (quiet : Bool)
  | overflow
  | done (sts : Array UInt8)

/-- Stream the letters of `src` from byte `i` on (`n` letters) in chunks of
`c` bytes. -/
def streamArr (src : ByteArray) (c : Nat) (sts : Array UInt8) (i n : Nat) : Nat → SR
  | 0 => .done sts
  | fuel + 1 =>
    if n == 0 then .done sts else
    let m := min (8 * c) n
    match pushChunk sts src i m 0 (sts.size + 1) with
    | .ok sts' => streamArr src c sts' (i + c) (n - m) fuel
    | .halt l q => .halt l q
    | .overflow => .overflow

/-- Stream `x y^k` into the pipeline. -/
def streamPW (w : PW) (c : Nat) (sts : Array UInt8) : Nat → SR
  | 0 => streamArr w.x c sts 0 w.nx (w.nx + 1)
  | k + 1 =>
    match streamPW w c sts k with
    | .done sts' => streamArr w.y c sts' 0 w.ny (w.ny + 1)
    | r => r

/-- The complete check: compute the periodic words up to level `q`, then
stream `x y^k` through `M` further levels; succeed iff some level halts
quietly. -/
def check (q k M c : Nat) : Bool :=
  match pwUpTo q with
  | none => false
  | some w =>
    match streamPW w c ((Array.range M).map (fun j => initSt (q + j))) k with
    | .halt _ quiet => quiet
    | _ => false

end HaltEngine
