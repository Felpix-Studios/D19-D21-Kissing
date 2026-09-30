import Mathlib
import KissingCheck.Basic
/-
From the integer check to kissing configurations of unit vectors in ℝⁿ.

`kissing_of_check` says: if every ray of `v` is nonzero and every pair passes
the integer test `compat`, then the normalized rays are `v.size` distinct unit
vectors in ℝⁿ with pairwise inner products at most 1/2.
-/
open scoped RealInnerProductSpace

namespace KissingD19D21
open KissingCheck

/-- A kissing configuration in ℝⁿ: unit vectors whose pairwise inner products
are at most 1/2 (angular separation at least 60°). -/
def IsKissingConfig {n : ℕ} (S : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ x ∈ S, ‖x‖ = 1) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x, y⟫ ≤ 1 / 2

/-- The same condition in terms of spheres: the unit balls centred at `2x`,
`x ∈ S`, all touch the unit ball at the origin, and no two of them overlap. -/
theorem IsKissingConfig.spheres {n : ℕ} {S : Finset (EuclideanSpace ℝ (Fin n))}
    (hS : IsKissingConfig S) :
    (∀ x ∈ S, ‖(2 : ℝ) • x‖ = 2) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist ((2 : ℝ) • x) ((2 : ℝ) • y) := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · rw [norm_smul, hS.1 x hx]; norm_num
  · have h1 := hS.1 x hx
    have h2 := hS.1 y hy
    have h3 := hS.2 x hx y hy hxy
    have hsq : ‖x - y‖ ^ 2 = 2 - 2 * ⟪x, y⟫ := by
      rw [norm_sub_sq_real, h1, h2]; ring
    have h4 : 1 ≤ ‖x - y‖ := by
      have : (1 : ℝ) ≤ ‖x - y‖ ^ 2 := by rw [hsq]; linarith
      nlinarith [norm_nonneg (x - y)]
    rw [dist_eq_norm, ← smul_sub, norm_smul]
    norm_num
    linarith

/-- The real vector of an integer ray (missing coordinates read as 0). -/
noncomputable def vec (n : ℕ) (x : Array Int) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun k => ((x[k.1]! : Int) : ℝ)

theorem fold_eq_sum (n : ℕ) (f : ℕ → Int) :
    Nat.fold n (fun k _ acc => acc + f k) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.fold_succ, Finset.sum_range_succ, ih]

theorem dot_eq_sum (n : ℕ) (x y : Array Int) :
    dot n x y = ∑ i : Fin n, x[i.1]! * y[i.1]! := by
  rw [Fin.sum_univ_eq_sum_range (fun i => x[i]! * y[i]!) n]
  exact fold_eq_sum n (fun k => x[k]! * y[k]!)

theorem dot_comm (n : ℕ) (x y : Array Int) : dot n x y = dot n y x := by
  simp only [dot_eq_sum, mul_comm]

theorem inner_vec (n : ℕ) (x y : Array Int) :
    ⟪vec n x, vec n y⟫ = ((dot n x y : Int) : ℝ) := by
  rw [dot_eq_sum, PiLp.inner_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [vec, mul_comm]

/-- The normalized ray. -/
noncomputable def unit (n : ℕ) (x : Array Int) : EuclideanSpace ℝ (Fin n) :=
  ‖vec n x‖⁻¹ • vec n x

theorem norm_vec_sq (n : ℕ) (x : Array Int) : ‖vec n x‖ ^ 2 = ((dot n x x : Int) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_vec]

theorem norm_vec_pos (n : ℕ) (x : Array Int) (h : 0 < dot n x x) : 0 < ‖vec n x‖ := by
  have h2 : (0 : ℝ) < ‖vec n x‖ ^ 2 := by rw [norm_vec_sq]; exact_mod_cast h
  exact lt_of_le_of_ne (norm_nonneg _) fun h0 => by rw [← h0] at h2; simp at h2

theorem norm_unit (n : ℕ) (x : Array Int) (h : 0 < dot n x x) : ‖unit n x‖ = 1 := by
  have := norm_vec_pos n x h
  rw [unit, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ this.ne']

theorem inner_unit (n : ℕ) (x y : Array Int) :
    ⟪unit n x, unit n y⟫ = ((dot n x y : Int) : ℝ) / (‖vec n x‖ * ‖vec n y‖) := by
  rw [unit, unit, real_inner_smul_left, real_inner_smul_right, inner_vec]
  field_simp

/-- The integer test gives cosine at most 1/2. -/
theorem inner_unit_le (n : ℕ) (x y : Array Int) (hx : 0 < dot n x x) (hy : 0 < dot n y y)
    (h : compat (dot n x y) (dot n x x) (dot n y y) = true) :
    ⟪unit n x, unit n y⟫ ≤ 1 / 2 := by
  have ha := norm_vec_pos n x hx
  have hb := norm_vec_pos n y hy
  have hab : 0 < ‖vec n x‖ * ‖vec n y‖ := mul_pos ha hb
  rw [inner_unit, div_le_iff₀ hab]
  set g : ℝ := ((dot n x y : Int) : ℝ)
  simp only [compat, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · have : g ≤ 0 := by simp only [g]; exact_mod_cast h
    linarith
  · have h' : 4 * (g * g) ≤ ‖vec n x‖ ^ 2 * ‖vec n y‖ ^ 2 := by
      rw [norm_vec_sq, norm_vec_sq]; simp only [g]; exact_mod_cast h
    nlinarith

theorem nat_all_iff (n : ℕ) (f : (i : ℕ) → i < n → Bool) :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem allPairs_spec (n : ℕ) (v : Array (Array Int)) (h : allPairs n v = true)
    (i j : ℕ) (hi : i < v.size) (hj : j < i) :
    compat (dot n v[i] v[j]) (dot n v[i] v[i]) (dot n v[j] v[j]) = true := by
  have hj' : j < v.size := lt_trans hj hi
  simp only [allPairs] at h
  have := (nat_all_iff _ _).1 ((nat_all_iff _ _).1 h i hi) j hj
  simpa [getElem!_pos, hi, hj', Array.getElem_map] using this

theorem wellFormed_spec (n : ℕ) (v : Array (Array Int)) (h : wellFormed n v = true)
    (i : ℕ) (hi : i < v.size) : 0 < dot n v[i] v[i] := by
  simp only [wellFormed, Array.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h i hi).2

/-- The bridge: a passing integer check gives `v.size` distinct unit vectors
in ℝⁿ with pairwise inner products at most 1/2. -/
theorem kissing_of_check (n : ℕ) (v : Array (Array Int))
    (hw : wellFormed n v = true) (hp : allPairs n v = true) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin n)), S.card = v.size ∧ IsKissingConfig S := by
  let u : Fin v.size → EuclideanSpace ℝ (Fin n) := fun i => unit n v[i]
  have hpos : ∀ i : Fin v.size, 0 < dot n v[i] v[i] := fun i => wellFormed_spec n v hw i i.2
  have hpair : ∀ i j : Fin v.size, i ≠ j → ⟪u i, u j⟫ ≤ 1 / 2 := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · have := allPairs_spec n v hp j i j.2 h
      rw [dot_comm n v[(j : ℕ)] v[(i : ℕ)]] at this
      have hs : compat (dot n v[(i : ℕ)] v[(j : ℕ)]) (dot n v[(i : ℕ)] v[(i : ℕ)])
          (dot n v[(j : ℕ)] v[(j : ℕ)]) = true := by
        simpa [compat, mul_comm] using this
      exact inner_unit_le n _ _ (hpos i) (hpos j) hs
    · exact inner_unit_le n _ _ (hpos i) (hpos j) (allPairs_spec n v hp i j i.2 h)
  have hinj : Function.Injective u := by
    intro i j hij
    by_contra hne
    have h1 := hpair i j hne
    rw [hij, real_inner_self_eq_norm_sq, show u j = unit n v[j] from rfl,
      norm_unit n _ (hpos j)] at h1
    norm_num at h1
  refine ⟨Finset.univ.image u, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact norm_unit n _ (hpos i)
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact hpair i j fun h => hxy (h ▸ rfl)

end KissingD19D21
