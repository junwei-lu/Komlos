import Komlos.Signing
import Komlos.CubeDensity
import Komlos.Stability

/-!
# The Komlós bound `3√(2π)` (paper Theorem 1.1) and the Beck–Fiala bound (Corollary 1.2)

* `Komlos.exists_signs_sum_mem` — paper Corollary 2.3 (symmetric targets);
* `Komlos.komlos` — **paper Theorem 1.1** in coordinates: for `v_1, …, v_n ∈ ℝ^m` with
  `∑_i v_{j,i}² ≤ 1` there are signs `ε_j ∈ {−1, 1}` with `|∑_j ε_j v_{j,i}| < 3√(2π)` for
  every coordinate `i`, i.e. `‖∑ ε_j v_j‖_∞ < 3√(2π)`;
* `Komlos.komlos_euclidean` — the same statement for `v_j : EuclideanSpace ℝ (Fin m)` with
  `‖v_j‖₂ ≤ 1` and the sup norm on `Fin m → ℝ`;
* `Komlos.beck_fiala` — paper Corollary 1.2.

The paper states Theorem 1.1 for positive integers `m, n`; the statements below allow
`m = 0` or `n = 0` as well (they are then trivially true), so they are formally stronger.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

/-- Paper Corollary 2.3 (symmetric targets).  This is the abstract signing reduction
`exists_signs_sum_mem_of_stable` with the invariant `good K := IsGoodConvex K ∧ HasAdmissible K κ`,
which is preserved by every transform `𝒯_{v_j}` by finite-step stability
(`finite_step_stability`, paper Proposition 2.2) and paper Lemma 2.1. -/
theorem exists_signs_sum_mem {d : ℕ} {K : Set (Euc d)} (hK : IsGoodConvex K) (hsymm : K = -K)
    {κ : ℝ} (hκ : 0 ≤ κ) (hadm : HasAdmissible K κ) {n : ℕ} (v : Fin n → Euc d)
    (hv : ∀ j, κ * ‖v j‖ ≤ 1 / 3) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧ ∑ j, ε j • v j ∈ K := by
  refine exists_signs_sum_mem_of_stable (fun K => IsGoodConvex K ∧ HasAdmissible K κ)
    (fun _ h => h.1) v ?_ ⟨hK, hadm⟩ hsymm
  rintro K ⟨hK', ρ, hρ, hcap⟩ j
  obtain ⟨hne, hadm'⟩ := finite_step_stability hK' hκ hρ hcap (hv j)
  exact ⟨hne, isGoodConvex_transform hK' _ hne, hadm'⟩

/-- **Paper Theorem 1.1 (Komlós bound), Euclidean form.**  For `v_j ∈ ℝ^m` with
`‖v_j‖₂ ≤ 1` there are signs `ε_j ∈ {−1,1}` with `∑_j ε_j v_j ∈ (−3√(2π), 3√(2π))^m`. -/
theorem komlos_euclidean (m n : ℕ) (v : Fin n → Euc m) (hv : ∀ j, ‖v j‖ ≤ 1) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |(∑ j, ε j • v j) i| < 3 * Real.sqrt (2 * Real.pi) := by
  -- `C = 3√(2π)`, `K = (−C, C)^m`, `κ = 1/3` (paper, proof of Theorem 1.1)
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hCpos : 0 < 3 * Real.sqrt (2 * Real.pi) := by positivity
  have hκ : Real.sqrt (2 * Real.pi) / (3 * Real.sqrt (2 * Real.pi)) = 1 / 3 := by
    field_simp
  have hadm : HasAdmissible (cube m (3 * Real.sqrt (2 * Real.pi))) (1 / 3) := by
    have := hasAdmissible_cube (d := m) hCpos
    rwa [hκ] at this
  obtain ⟨ε, hε, hmem⟩ := exists_signs_sum_mem (isGoodConvex_cube hCpos) (cube_neg_eq _)
    (by norm_num) hadm v (fun j => by linarith [hv j])
  exact ⟨ε, hε, hmem⟩

/-- **Paper Theorem 1.1 (Komlós bound), coordinate form.**  For every `m, n` and every
family `v_1, …, v_n ∈ ℝ^m` with Euclidean norm at most one (`∑_i v_{j,i}² ≤ 1`), there are
signs `ε_1, …, ε_n ∈ {−1, 1}` such that `‖∑_j ε_j v_j‖_∞ < 3√(2π)`, i.e.
`|∑_j ε_j v_{j,i}| < 3√(2π)` for every coordinate `i`. -/
theorem komlos (m n : ℕ) (v : Fin n → Fin m → ℝ) (hv : ∀ j, ∑ i, v j i ^ 2 ≤ 1) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |∑ j, ε j * v j i| < 3 * Real.sqrt (2 * Real.pi) := by
  obtain ⟨ε, hε, h⟩ := komlos_euclidean m n (fun j => WithLp.toLp 2 (v j)) (fun j => by
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
    simpa [Real.norm_eq_abs, sq_abs] using hv j)
  refine ⟨ε, hε, fun i => ?_⟩
  simpa [WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul] using h i

/-- **Paper Theorem 1.1**, sup-norm form: `‖∑ ε_j v_j‖_∞ < 3√(2π)` with the sup norm of
`Fin m → ℝ`. -/
theorem komlos_supNorm (m n : ℕ) (v : Fin n → Fin m → ℝ) (hv : ∀ j, ∑ i, v j i ^ 2 ≤ 1) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ‖∑ j, ε j • v j‖ < 3 * Real.sqrt (2 * Real.pi) := by
  obtain ⟨ε, hε, h⟩ := komlos m n v hv
  refine ⟨ε, hε, ?_⟩
  rw [pi_norm_lt_iff (by positivity)]
  intro i
  simpa [Finset.sum_apply, smul_eq_mul, Real.norm_eq_abs] using h i

/-- **Paper Corollary 1.2 (Beck–Fiala bound).**  If `A ∈ {0,1}^{m×n}` has at most `t`
nonzero entries in each column, then some signing `ε ∈ {−1,1}^n` has
`‖A ε‖_∞ < 3√(2π t)`. -/
theorem beck_fiala (m n t : ℕ) (ht : 0 < t) (A : Fin m → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hcol : ∀ j, (Finset.univ.filter fun i => A i j ≠ 0).card ≤ t) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |∑ j, A i j * ε j| < 3 * Real.sqrt (2 * Real.pi * t) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htR
  -- every column of `A / √t` has Euclidean norm at most one
  obtain ⟨ε, hε, h⟩ := komlos m n (fun j i => A i j / Real.sqrt t) (fun j => by
    have hsq : ∀ i, (A i j / Real.sqrt t) ^ 2 = (if A i j ≠ 0 then 1 else 0) / t := by
      intro i
      rcases h01 i j with h0 | h1
      · simp [h0]
      · simp [h1, Real.sq_sqrt htR.le]
    simp_rw [hsq]
    rw [← Finset.sum_div, div_le_one htR, Finset.sum_boole]
    exact_mod_cast hcol j)
  refine ⟨ε, hε, fun i => ?_⟩
  have key : ∑ j, A i j * ε j = Real.sqrt t * ∑ j, ε j * (A i j / Real.sqrt t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  calc |∑ j, A i j * ε j| = Real.sqrt t * |∑ j, ε j * (A i j / Real.sqrt t)| := by
        rw [key, abs_mul, abs_of_pos hst]
    _ < Real.sqrt t * (3 * Real.sqrt (2 * Real.pi)) := by gcongr; exact h i
    _ = 3 * Real.sqrt (2 * Real.pi * t) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (t : ℝ)]; ring

end Komlos
