import KissingD19D21.Bridge
import KissingCheck.D21
/-!
# τ₂₁ ≥ 30779

`KissingCheck.D21.rays` builds the configuration from the Golay polynomial,
the 13 deleted sign patterns, the four sign generators and the 192
representatives. The two Boolean checks run in native code (`native_decide`);
the rest of the argument is the kernel-checked bridge in `KissingD19D21.Bridge`.
-/
namespace KissingD19D21
open KissingCheck

theorem d21_size : D21.rays.size = 30779 := by native_decide
theorem d21_wellFormed : wellFormed 21 D21.rays = true := by native_decide
theorem d21_allPairs : allPairs 21 D21.rays = true := by native_decide

/-- There are 30779 unit vectors in ℝ²¹ with pairwise inner products at most 1/2. -/
theorem kissing_d21 :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 21)), S.card = 30779 ∧ IsKissingConfig S := by
  rw [← d21_size]
  exact kissing_of_check 21 D21.rays d21_wellFormed d21_allPairs

end KissingD19D21
