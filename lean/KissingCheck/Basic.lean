/-
Exact integer checker for kissing configurations.

A configuration is an array of integer vectors (rays). Each ray x stands for
the unit vector x / |x|. Two rays x, y are compatible when the angle between
them is at least 60 degrees, that is x·y ≤ |x||y|/2. For integers this is

    x·y ≤ 0   or   4 (x·y)^2 ≤ |x|^2 |y|^2.

This file uses only Lean core, so that it can be compiled to native code.
-/
namespace KissingCheck

/-- Dot product of the first `n` coordinates. -/
def dot (n : Nat) (x y : Array Int) : Int :=
  Nat.fold n (fun k _ acc => acc + x[k]! * y[k]!) 0

/-- The integer form of "cosine at most 1/2", given the two squared norms. -/
def compat (g nx ny : Int) : Bool :=
  decide (g ≤ 0) || decide (4 * (g * g) ≤ nx * ny)

/-- Every ray has exactly `n` coordinates and is nonzero. -/
def wellFormed (n : Nat) (v : Array (Array Int)) : Bool :=
  v.all fun x => x.size == n && decide (0 < dot n x x)

/-- Every pair `j < i` is compatible. Squared norms are computed once. -/
def allPairs (n : Nat) (v : Array (Array Int)) : Bool :=
  let N := v.map fun x => dot n x x
  Nat.all v.size fun i _ => Nat.all i fun j _ =>
    compat (dot n v[i]! v[j]!) N[i]! N[j]!

/-! ## Binary words as natural numbers (bit `k` is coordinate `k`) -/

def popcount (w : Nat) : Nat := Id.run do
  let mut c := 0
  let mut x := w
  while x != 0 do
    c := c + x % 2
    x := x / 2
  return c

/-- Mask of a list of 1-indexed coordinates. -/
def mask1 (s : List Nat) : Nat := s.foldl (fun acc i => acc ||| (1 <<< (i - 1))) 0

/-- All XOR combinations of the generators. -/
def span (gens : List Nat) : Array Nat :=
  gens.foldl (fun acc g => acc ++ acc.map (· ^^^ g)) #[0]

def bitSign (w k : Nat) : Int := if w.testBit k then -1 else 1

/-- The vectors ±2e_i ± 2e_j in dimension `n`. -/
def roots (n : Nat) : Array (Array Int) := Id.run do
  let mut out := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      for si in [2, -2] do
        for sj in [2, -2] do
          out := out.push ((Array.replicate n (0 : Int)).set! i si |>.set! j sj)
  return out

/-- The positions of the set bits of `w` below `n`, in increasing order. -/
def support (n w : Nat) : Array Nat := (Array.range n).filter (w.testBit ·)

/-- The 128 vectors with entries ±1 on the octad `o` (weight 8), 0 elsewhere,
and an odd number of minus signs. -/
def oddSigns (n o : Nat) : Array (Array Int) := Id.run do
  let s := support n o
  let mut out := #[]
  for m in [0:2 ^ s.size] do
    if popcount m % 2 == 1 then
      let mut v := Array.replicate n (0 : Int)
      for t in [0:s.size] do
        v := v.set! s[t]! (bitSign m t)
      out := out.push v
  return out

/-- Change the signs of the coordinates in `h`. -/
def flip (h : Nat) (x : Array Int) : Array Int :=
  x.mapIdx fun k a => bitSign h k * a

end KissingCheck

namespace KissingCheck

/-- Some ray of `v` makes an angle below 60° with `p`. -/
def conflicts (n : Nat) (v : Array (Array Int)) (p : Array Int) : Bool :=
  v.any fun a => !compat (dot n a p) (dot n a a) (dot n p p)

end KissingCheck
