import KissingCheck.Basic
import KissingCheck.D21Reps
/-
The 30779-point configuration in dimension 21. Coordinates are 1..21 in the
text and bits 0..20 here. Base rays have squared norm 8; the 3072 new rays
are the sign changes of 192 integer representatives by a group of order 16.
-/
namespace KissingCheck.D21

/-- The extended Golay code: shifts of 1 + t + t^5 + t^6 + t^7 + t^9 + t^11
(coefficient of t^i at bit i) and an overall parity bit at bit 23. -/
def golayGens : List Nat :=
  (List.range 12).map fun j =>
    let w := [0, 1, 5, 6, 7, 9, 11].foldl (fun acc e => acc ||| (1 <<< (e + j))) 0
    if popcount w % 2 == 1 then w ||| (1 <<< 23) else w

def G : Array Nat := span golayGens

/-- The 210 octads of G that vanish on coordinates 22, 23, 24. -/
def octads : Array Nat :=
  G.filter fun w => popcount w == 8 && w &&& (7 <<< 21) == 0

/-- The octad T = {3,6,10,11,16,18,20,21} that carries the deletions. -/
def Tcoords : List Nat := [3, 6, 10, 11, 16, 18, 20, 21]
def Tmask : Nat := mask1 Tcoords

/-- The 13 deleted sign patterns on T, signs in the order of `Tcoords`
(the `removed_base_representatives` of `data/D21_30779_certificate.json`). -/
def deletedSigns : List (List Int) := [
  [1, 1, -1, 1, 1, 1, 1, 1],
  [1, -1, 1, -1, -1, 1, 1, 1],
  [1, 1, 1, 1, 1, -1, 1, 1],
  [1, 1, -1, -1, 1, 1, -1, 1],
  [1, -1, 1, 1, -1, 1, -1, 1],
  [1, -1, -1, 1, -1, -1, -1, 1],
  [1, 1, -1, -1, 1, 1, 1, -1],
  [1, -1, 1, 1, -1, 1, 1, -1],
  [1, 1, 1, -1, 1, -1, 1, -1],
  [1, -1, -1, 1, -1, -1, 1, -1],
  [1, 1, -1, 1, 1, 1, -1, -1],
  [1, -1, 1, -1, -1, 1, -1, -1],
  [1, 1, 1, 1, 1, -1, -1, -1]]

/-- The vector with the given signs on T and zeros elsewhere. -/
def onT (s : List Int) : Array Int := Id.run do
  let mut v := Array.replicate 21 (0 : Int)
  for (i, a) in Tcoords.zip s do
    v := v.set! (i - 1) a
  return v

def deletedList : Array (Array Int) := (deletedSigns.map onT).toArray

/-- `x` is one of the 13 deleted points (they all lie on T). -/
def deleted (o : Nat) (x : Array Int) : Bool :=
  o == Tmask && deletedList.any (· == x)

def base : Array (Array Int) :=
  roots 21 ++ octads.flatMap fun o => (oddSigns 21 o).filter (!deleted o ·)

/-- The sign group K of order 16 (bit j changes the sign of coordinate j+1).
The first three generators span the order-8 group H (Σ₀ in the paper);
w = 14723 is the fourth. K is Σ in the paper, and T is the octad Q. -/
def K : Array Nat := span [92361, 20689, 346115, 14723]

def parseRow (s : String) : Array Int :=
  ((s.splitOn " ").filter (· ≠ "")).toArray.map fun t => t.toInt?.getD 0

def reps : Array (Array Int) :=
  ((d21RepsText.splitOn "\n").filter (· ≠ "")).toArray.map parseRow

def newPoints : Array (Array Int) := reps.flatMap fun r => K.map (flip · r)

def rays : Array (Array Int) := base ++ newPoints

/-- The 13 deleted points, as odd sign patterns on T. -/
def deletedBase : Array (Array Int) := (oddSigns 21 Tmask).filter (deleted Tmask)

end KissingCheck.D21
