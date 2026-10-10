import KissingCheck.Basic
import KissingCheck.D19Reps
/-
The 12276-point configuration in dimension 19, built from Ho's twelve
generators, eight restored base points, seven sign generators and the 14
representatives in `D19Reps.lean`. Coordinates of E are 1..20 in the
generator lists and 0..19 as bits. Each ray is a positive multiple of the
point described in the paper: base rays are scaled by 2, new rays are the
integer vectors of the table.
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

/-- Core: the points of Cohn–Li's C20 orthogonal to 1_T, minus those on the
four octads that contain T (10476 rays). -/
def core : Array (Array Int) :=
  let rts := (roots 20).filter (sumT · == 0)
  let oct := (octads.filter (· &&& Tmask != Tmask)).flatMap fun o =>
    (oddSigns 20 o).filter (sumT · == 0)
  (rts ++ oct).map native

/-- The eight restored points, in coordinates 1..20: (1, 1, -1, -1) on
T = (1, 4, 7, 9) and the eight sign patterns with an odd number of minus signs
on coordinates 3, 6, 8, 19. All lie on the octad T ∪ {3, 6, 8, 19}. -/
def restored20 : List (List Int) := [
  [1, 0, 1, 1, 0, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  [1, 0, 1, 1, 0, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [1, 0, 1, 1, 0, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [1, 0, 1, 1, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  [1, 0, -1, 1, 0, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [1, 0, -1, 1, 0, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  [1, 0, -1, 1, 0, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  [1, 0, -1, 1, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]

def restored : Array (Array Int) := (restored20.map fun v => native v.toArray).toArray

/-- Base: the core plus the eight restored points (10484 rays). -/
def base : Array (Array Int) := core ++ restored

/-- Generators of the sign group G of order 128, as sets of coordinates in 1..20
(all in H). -/
def groupGens : List (List Nat) := [
  [2, 5, 10, 11, 13, 15], [2, 5, 10, 16, 17, 20],
  [2, 5, 12, 14, 15, 17], [2, 10, 13, 14, 16, 18],
  [2, 3, 6, 10, 14, 15], [2, 3, 8, 10, 11, 17], [2, 3, 11, 13, 16, 19]]

/-- A set of head coordinates as a mask on the 19 native coordinates
(bit k is native coordinate k, which is `Hbits[k]`). -/
def nativeMask (s : List Nat) : Nat :=
  (List.range 16).foldl (fun acc k =>
    if s.contains (Hbits[k]! + 1) then acc ||| (1 <<< k) else acc) 0

def G : Array Nat := span (groupGens.map nativeMask)

def parseRow (s : String) : Array Int :=
  ((s.splitOn " ").filter (· ≠ "")).toArray.map fun t => t.toInt?.getD 0

def reps : Array (Array Int) :=
  ((d19RepsText.splitOn "\n").filter (· ≠ "")).toArray.map parseRow

/-- The 1792 new points: the 14 representatives under G. -/
def newPoints : Array (Array Int) := reps.flatMap fun r => G.map (flip · r)

def rays : Array (Array Int) := base ++ newPoints

/-- The 184 points of C20 ∩ 1_T^⊥ on the four octads that contain T, other
than the eight restored points. -/
def deletedBase : Array (Array Int) :=
  (((octads.filter (· &&& Tmask == Tmask)).flatMap fun o =>
    (oddSigns 20 o).filter (sumT · == 0)).map native).filter (!restored.contains ·)

end KissingCheck.D19
