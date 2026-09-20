import Komlos.Literature.Regularized.ProfileBasic
import Komlos.Literature.PLaplacian.RegularityChainRule
import Komlos.Literature.PLaplacian.RegularitySobolev

/-!
# Pointwise facts about the regularized energy densities

Lane `L1` (`reg/variational`) of `REGULARIZED_ROUTE.md`, Revision 2.  This file collects the
*pointwise* algebra of the two densities appearing in
`Komlos.Literature.Regularized.regEnergy` at the exponent `p = 2`:

* the kinetic density `Q(s, ξ) = Korevaar.homogeneousDensity 2 Ψ s ξ = s² Ψ(ξ/s)`, whose junk
  value at `s = 0` is `0`;
* the entropy potential `Korevaar.entropyPotential 2 κ s = (κ/2) s² log s`.

## Main results

* `homogeneousDensity_two_zero`, `homogeneousDensity_two`: the junk value and the
  explicit formula.
* `IsRegProfileWith.homogeneousDensity_two_lower`,
  `IsRegProfileWith.homogeneousDensity_two_upper`: the two-sided bound
  `Ψ 0 * s² + (c/2)‖ξ‖² ≤ Q(s,ξ) ≤ Ψ 0 * s² + (C/2)‖ξ‖²`, valid for **all** `s ≥ 0` provided
  `ξ = 0` when `s = 0` (which is a.e. the case for a weak gradient, see
  `MemW0.weakGrad_eq_zero_on_zero`).
* `neg_quarter_le_sq_mul_log`, `sq_mul_log_le_rpow`, `abs_sq_mul_log_le`: the elementary
  bounds `-1/4 ≤ s² log s` and `s² log s ≤ s^{2+δ}/δ` for `s ≥ 0`, `δ > 0`.
* `MemW0.weakGrad_eq_zero_on_zero`: **the weak gradient of a nonnegative `W₀^{1,2}` function
  vanishes a.e. on its zero set** (Stampacchia).  This is what makes the junk value `0` of
  the kinetic density a.e. correct.  Proof: the smooth truncations
  `G_ε(t) = √(t² + ε²) - ε` satisfy `G_ε(t) → |t|` and `G_ε'(t) → sign t` pointwise, so the
  chain rule `memW0_comp` and `HasWeakGradient.of_tendsto` identify the weak gradient of
  `|w| = w` as `1_{w ≠ 0} ∇w`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {Ψ : Euc d → ℝ} {c C : ℝ}

/-! ### The kinetic density at `p = 2` -/

/-- `t ^ (2 : ℝ) = t ^ (2 : ℕ)` (`Real.rpow_natCast`), used constantly below. -/
theorem rpow_two_eq (t : ℝ) : t ^ (2 : ℝ) = t ^ 2 := by
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The kinetic density at `p = 2`, with a natural-number power. -/
theorem homogeneousDensity_two (Ψ : Euc d → ℝ) (s : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ s ξ = s ^ 2 * Ψ (s⁻¹ • ξ) := by
  rw [Korevaar.homogeneousDensity]
  congr 1
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The junk value of the kinetic density at `s = 0` is `0`. -/
@[simp] theorem homogeneousDensity_two_zero (Ψ : Euc d → ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ 0 ξ = 0 := by
  simp [homogeneousDensity_two]

namespace IsRegProfileWith

/-- **Lower bound for the kinetic density**: `Ψ 0 * s² + (c/2) ‖ξ‖² ≤ s² Ψ(ξ/s)` for `s > 0`. -/
theorem homogeneousDensity_two_lower_of_pos (h : IsRegProfileWith Ψ c C) {s : ℝ} (hs : 0 < s)
    (ξ : Euc d) :
    Ψ 0 * s ^ 2 + c / 2 * ‖ξ‖ ^ 2 ≤ Korevaar.homogeneousDensity 2 Ψ s ξ := by
  rw [homogeneousDensity_two]
  have hq := h.quadratic_lower (s⁻¹ • ξ)
  have hn : ‖s⁻¹ • ξ‖ ^ 2 = s⁻¹ ^ 2 * ‖ξ‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
  rw [hn] at hq
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hq hs2.le
  have hinv : s ^ 2 * (s⁻¹ ^ 2 * ‖ξ‖ ^ 2) = ‖ξ‖ ^ 2 := by
    field_simp
  have hexp : s ^ 2 * (Ψ 0 + c / 2 * (s⁻¹ ^ 2 * ‖ξ‖ ^ 2)) =
      Ψ 0 * s ^ 2 + c / 2 * (s ^ 2 * (s⁻¹ ^ 2 * ‖ξ‖ ^ 2)) := by ring
  rw [hexp, hinv] at hmul
  exact hmul

/-- **Upper bound for the kinetic density**: `s² Ψ(ξ/s) ≤ Ψ 0 * s² + (C/2) ‖ξ‖²` for `s > 0`. -/
theorem homogeneousDensity_two_upper_of_pos (h : IsRegProfileWith Ψ c C) {s : ℝ} (hs : 0 < s)
    (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ s ξ ≤ Ψ 0 * s ^ 2 + C / 2 * ‖ξ‖ ^ 2 := by
  rw [homogeneousDensity_two]
  have hq := h.quadratic_upper (s⁻¹ • ξ)
  have hn : ‖s⁻¹ • ξ‖ ^ 2 = s⁻¹ ^ 2 * ‖ξ‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
  rw [hn] at hq
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hq hs2.le
  have hinv : s ^ 2 * (s⁻¹ ^ 2 * ‖ξ‖ ^ 2) = ‖ξ‖ ^ 2 := by
    field_simp
  have hexp : s ^ 2 * (Ψ 0 + C / 2 * (s⁻¹ ^ 2 * ‖ξ‖ ^ 2)) =
      Ψ 0 * s ^ 2 + C / 2 * (s ^ 2 * (s⁻¹ ^ 2 * ‖ξ‖ ^ 2)) := by ring
  rw [hexp, hinv] at hmul
  exact hmul

/-- The two-sided bound in the form used on the whole space: for `s ≥ 0`, with `ξ = 0`
enforced when `s = 0`. -/
theorem homogeneousDensity_two_lower (h : IsRegProfileWith Ψ c C) {s : ℝ} (hs : 0 ≤ s)
    {ξ : Euc d} (hξ : s = 0 → ξ = 0) :
    Ψ 0 * s ^ 2 + c / 2 * ‖ξ‖ ^ 2 ≤ Korevaar.homogeneousDensity 2 Ψ s ξ := by
  rcases hs.lt_or_eq with hpos | hzero
  · exact h.homogeneousDensity_two_lower_of_pos hpos ξ
  · rw [← hzero, hξ hzero.symm]
    simp

theorem homogeneousDensity_two_upper (h : IsRegProfileWith Ψ c C) {s : ℝ} (hs : 0 ≤ s)
    {ξ : Euc d} (hξ : s = 0 → ξ = 0) :
    Korevaar.homogeneousDensity 2 Ψ s ξ ≤ Ψ 0 * s ^ 2 + C / 2 * ‖ξ‖ ^ 2 := by
  rcases hs.lt_or_eq with hpos | hzero
  · exact h.homogeneousDensity_two_upper_of_pos hpos ξ
  · rw [← hzero, hξ hzero.symm]
    simp

end IsRegProfileWith

/-! ### The entropy potential at `p = 2` -/

/-- `entropyPotential 2 κ s = (κ/2) (s² log s)` with a natural-number power. -/
theorem entropyPotential_two (κ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Korevaar.entropyPotential 2 κ s = κ / 2 * (s ^ 2 * Real.log s) := by
  rw [Korevaar.entropyPotential]
  rcases hs.lt_or_eq with hpos | hzero
  · congr 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  · rw [← hzero]
    simp

/-- `s² log s ≥ -1/4` for `s ≥ 0` (the true minimum is `-1/(2e)`; this crude bound suffices).
Proof: `log s ≥ 1 - 1/s` for `s > 0`, so `s² log s ≥ s² - s ≥ -1/4`. -/
theorem neg_quarter_le_sq_mul_log {s : ℝ} (hs : 0 ≤ s) : -(1 / 4 : ℝ) ≤ s ^ 2 * Real.log s := by
  rcases hs.lt_or_eq with hpos | hzero
  · have hlog : 1 - s⁻¹ ≤ Real.log s := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
      rw [Real.log_inv] at h
      linarith
    have h2 : s ^ 2 * (1 - s⁻¹) ≤ s ^ 2 * Real.log s :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h3 : s ^ 2 * (1 - s⁻¹) = s ^ 2 - s := by
      field_simp
      try ring
    nlinarith [sq_nonneg (s - 1 / 2)]
  · rw [← hzero]; norm_num

/-- `s² log s ≤ s^{2+δ}/δ` for `s ≥ 0` and `δ > 0`.  Proof: `δ log s ≤ s^δ - 1`. -/
theorem sq_mul_log_le_rpow {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) :
    s ^ 2 * Real.log s ≤ s ^ (2 + δ) / δ := by
  rcases hs.lt_or_eq with hpos | hzero
  · have hlog : δ * Real.log s ≤ s ^ δ - 1 := by
      have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos δ)
      rwa [Real.log_rpow hpos] at h
    have hs2 : (0 : ℝ) ≤ s ^ 2 := by positivity
    have h2 : s ^ 2 * (δ * Real.log s) ≤ s ^ 2 * (s ^ δ - 1) :=
      mul_le_mul_of_nonneg_left hlog hs2
    have hsplit : s ^ (2 + δ) = s ^ 2 * s ^ δ := by
      rw [Real.rpow_add hpos, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hsplit, le_div_iff₀ hδ]
    nlinarith [hs2]
  · rw [← hzero]
    simp [Real.zero_rpow, (by positivity : (0:ℝ) < 2 + δ).ne']

/-- The absolute-value form: `|s² log s| ≤ 1/4 + s^{2+δ}/δ` for `s ≥ 0` and `δ > 0`. -/
theorem abs_sq_mul_log_le {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) :
    |s ^ 2 * Real.log s| ≤ 1 / 4 + s ^ (2 + δ) / δ := by
  have h1 := neg_quarter_le_sq_mul_log hs
  have h2 := sq_mul_log_le_rpow hs hδ
  have h3 : (0 : ℝ) ≤ s ^ (2 + δ) / δ := by positivity
  rw [abs_le]
  constructor <;> linarith

end Komlos.Literature.Regularized
