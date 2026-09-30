import KissingCheck.Basic
/-
The 12268-point configuration in dimension 19, built from Ho's twelve
generators. Coordinates of E are 1..20 in the generator lists and 0..19 as bits.
Each ray is a positive multiple of the point described in the paper:
base rays are scaled by 2, diagonal additions by 22, axis additions by 10.
-/
namespace KissingCheck.D19

/-- Generators of the [20,12,4] code E: Ho's [19,12] code with his fifth
extension column appended as coordinate 20. -/
def gens : List Nat := [
  [1,8,9,12,16,17,18,19], [2,10,11,14,15,17,18,20], [3,7,9,13,15,16,17,19],
  [4,7,8,10,12,15,16,19], [5,10,12,13,15,16,17,18], [6,7,8,9,10,13,16,18],
  [1,4,7,9], [1,5,6,18,20], [1,3,12,15,20], [1,10,13,19,20],
  [1,3,5,6,7,13,14,15,18,20], [2,4,6,7,8,13,14,16,17,18]].map mask1

def E : Array Nat := span gens

/-- The weight-8 words of the dual code E^⊥ (the octads). -/
def octads : Array Nat :=
  (Array.range (2 ^ 20)).filter fun w =>
    popcount w == 8 && gens.all fun g => popcount (w &&& g) % 2 == 0

/-- The tetrad T = {1,4,7,9} (bits 0,3,6,8), a weight-4 word of E. -/
def Tbits : List Nat := [0, 3, 6, 8]
def Tmask : Nat := mask1 [1, 4, 7, 9]
/-- The other 16 coordinates, in increasing order. -/
def Hbits : List Nat := (List.range 20).filter (· ∉ Tbits)

/-- R v_T with R = [[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]. -/
def Rmul (v : Array Int) : List Int :=
  let a := v[0]!; let b := v[3]!; let c := v[6]!; let d := v[8]!
  [a + b - c - d, a - b + c - d, a - b - c + d]

def sumT (v : Array Int) : Int := v[0]! + v[3]! + v[6]! + v[8]!

/-- Native coordinates, scaled by 2: (2 v_H, R v_T). -/
def native (v : Array Int) : Array Int :=
  (Hbits.map fun k => (2 : Int) * v[k]!).toArray ++ (Rmul v).toArray

/-- Base: the points of Cohn–Li's C20 orthogonal to 1_T, minus those on the
four octads that contain T. -/
def base : Array (Array Int) :=
  let rts := (roots 20).filter (sumT · == 0)
  let oct := (octads.filter (· &&& Tmask != Tmask)).flatMap fun o =>
    (oddSigns 20 o).filter (sumT · == 0)
  (rts ++ oct).map native

/-- The span W of the five weight-4 words of E. -/
def W : Array Nat := span ((E.filter (popcount · == 4)).toList)

/-- Keep c when c + (smallest word of c + W) is a sum of an even number of
tetrads. The tetrads are disjoint, so that sum has weight divisible by 8. -/
def keep (c : Nat) : Bool :=
  let cmin := (W.map (c ^^^ ·)).foldl min c
  popcount (c ^^^ cmin) % 8 == 0

def addition (c : Nat) : Array Int :=
  let q := (Array.range 20).map (bitSign c)
  let head := Hbits.map fun k => q[k]!
  let tail := Rmul q
  if popcount (c &&& Tmask) % 2 == 1 then
    (head.map (22 * ·)).toArray ++ (tail.map (9 * ·)).toArray   -- λ = 9/11
  else
    (head.map (10 * ·)).toArray ++ (tail.map (7 * ·)).toArray   -- λ = 7/5

def additions : Array (Array Int) :=
  (E.filter fun c =>
    let a := popcount (c &&& Tmask); 1 ≤ a && a ≤ 3 && keep c).map addition

def rays : Array (Array Int) := base ++ additions

/-- The 192 points of C20 ∩ 1_T^⊥ on the four octads that contain T. -/
def deletedBase : Array (Array Int) :=
  ((octads.filter (· &&& Tmask == Tmask)).flatMap fun o =>
    (oddSigns 20 o).filter (sumT · == 0)).map native

end KissingCheck.D19
