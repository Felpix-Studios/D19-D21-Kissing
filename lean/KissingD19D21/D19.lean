import KissingD19D21.Bridge
import KissingCheck.D19
/-!
# τ₁₉ ≥ 12276

`KissingCheck.D19.rays` builds the configuration from Ho's twelve generators,
the eight restored points, the seven sign generators and the 14 representatives.
The two Boolean checks run in native code (`native_decide`); the rest of the
argument is the kernel-checked bridge in `KissingD19D21.Bridge`.
-/
namespace KissingD19D21
open KissingCheck

theorem d19_size : D19.rays.size = 12276 := by native_decide
theorem d19_wellFormed : wellFormed 19 D19.rays = true := by native_decide
theorem d19_allPairs : allPairs 19 D19.rays = true := by native_decide

/-- There are 12276 unit vectors in ℝ¹⁹ with pairwise inner products at most 1/2. -/
theorem kissing_d19 :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 19)), S.card = 12276 ∧ IsKissingConfig S := by
  rw [← d19_size]
  exact kissing_of_check 19 D19.rays d19_wellFormed d19_allPairs

end KissingD19D21
