import KissingCheck.Basic
import KissingCheck.D21Reps
/-
The 30761-point configuration in dimension 21. Coordinates are 1..21 in the
text and bits 0..20 here. Base rays have squared norm 8; the 3072 new rays
are the sign changes of 384 integer representatives by a group of order 8.
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

/-- The deleted octad T = {3,6,10,11,16,18,20,21}. -/
def Tmask : Nat := mask1 [3, 6, 10, 11, 16, 18, 20, 21]

/-- Entry at 1-indexed coordinate `i`. -/
def at1 (v : Array Int) (i : Nat) : Int := v[i - 1]!

/-- r* = e3 - e6 - e10 - e11 - e16 - e18 - e20 - e21, which is kept. -/
def rstar : Array Int :=
  (Array.range 21).map fun k =>
    if k + 1 = 3 then 1 else if Tmask.testBit k then -1 else 0

/-- The 31 deleted points: odd sign patterns x on T with x3 = +1,
x6 x10 x18 = -1 and x11 x16 x20 x21 = +1, other than r*. -/
def deleted (o : Nat) (x : Array Int) : Bool :=
  o == Tmask && at1 x 3 == 1 && at1 x 6 * at1 x 10 * at1 x 18 == -1 &&
    at1 x 11 * at1 x 16 * at1 x 20 * at1 x 21 == 1 && x != rstar

def base : Array (Array Int) :=
  roots 21 ++ octads.flatMap fun o => (oddSigns 21 o).filter (!deleted o ·)

/-- The sign group H of order 8 (bit j changes the sign of coordinate j+1). -/
def H : Array Nat := span [92361, 20689, 346115]

def parseRow (s : String) : Array Int :=
  ((s.splitOn " ").filter (· ≠ "")).toArray.map fun t => t.toInt?.getD 0

def reps : Array (Array Int) :=
  ((d21RepsText.splitOn "\n").filter (· ≠ "")).toArray.map parseRow

def newPoints : Array (Array Int) := reps.flatMap fun r => H.map (flip · r)

def rays : Array (Array Int) := base ++ newPoints

/-- The 31 deleted points. -/
def deletedBase : Array (Array Int) := (oddSigns 21 Tmask).filter (deleted Tmask)

end KissingCheck.D21
