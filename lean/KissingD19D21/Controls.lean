import KissingCheck
/-!
# Sanity checks

The checker is not vacuous: it rejects a pair at cosine just above 1/2, and
every point removed from the base in either construction is too close to one
of the added points.
-/
namespace KissingD19D21
open KissingCheck

/-- Cosine 1/2 passes; the integer test is exact at the boundary. -/
example : compat 4 8 8 = true := by decide
/-- Cosine 5/8 fails. -/
example : compat 5 8 8 = false := by decide
/-- g = 10^9, nx·ny = 4·10^18 + 3 passes; with nx·ny = 4·10^18 - 1 it fails. -/
example : compat (10 ^ 9) (4 * 10 ^ 18 + 3) 1 = true := by decide
example : compat (10 ^ 9) (4 * 10 ^ 18 - 1) 1 = false := by decide

theorem d19_deleted_count : D19.deletedBase.size = 192 := by native_decide
/-- Each of the 192 deleted points conflicts with some addition. -/
theorem d19_deleted_needed :
    D19.deletedBase.all (conflicts 19 D19.additions) = true := by native_decide

theorem d21_deleted_count : D21.deletedBase.size = 13 := by native_decide
/-- Each of the 13 deleted points conflicts with some new point. -/
theorem d21_deleted_needed :
    D21.deletedBase.all (conflicts 21 D21.newPoints) = true := by native_decide

end KissingD19D21
