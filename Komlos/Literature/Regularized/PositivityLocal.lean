import Komlos.Literature.Regularized.VariationalBound
import Komlos.Literature.Regularized.ProfileBasic
import Komlos.Literature.Regularized.DeGiorgiNashAux

/-!
# Lane `L2` (`reg/positivity`), step 1: the local (unconstrained) variational problem

`REGULARIZED_ROUTE.md`, Revision 2 (i)–(iii), asks for the regularity of the minimizer `u` of
`regEnergy 2 κ Ψ` under the constraint `∫ u² = 1`.  The De Giorgi machinery, however, is a
*local* theory: it compares `u` with `u - η²(u-k)_+`, which does not satisfy the constraint.
This file removes the constraint once and for all.

## The unconstrained functional

Write `m = regMin 2 κ Ψ K`, `D(s, ξ) = s² Ψ(ξ/s)` (`Korevaar.homogeneousDensity` at `p = 2`)
and `P(s) = (κ/2) s² log s` (`Korevaar.entropyPotential`).  For a competitor `w ≥ 0` in
`W₀^{1,2}(K)` with `t² = ∫ w² > 0` the rescaling `w/t` *is* admissible, and the two densities
scale explicitly:

`D(w/t, ∇w/t) = t⁻² D(w, ∇w)`,  `P(w/t) = t⁻² (P(w) - (κ/2)(log t) w²)`.

Hence `regEnergy (w/t) = t⁻² (∫D + ∫P) - (κ/2) log t ≥ m`, i.e.

`∫ D(w,∇w) + ∫ P(w) ≥ t² m + (κ/2) t² log t`.

Subtracting `Λ ∫ w² = Λ t²` with the multiplier

`Λ = m + κ/4`

and using the elementary `s log s ≥ s - 1` (at `s = t²`) gives `regFree κ Λ Ψ w ≥ -κ/4`, with
**equality at `w = u`** (where `t = 1`).  So `u` minimizes

`regFree κ Λ Ψ w = ∫ [ w² Ψ(∇w/w) + (κ/2) w² log w - Λ w² ]`

over all nonnegative bounded `w ∈ W₀^{1,2}(K)` — the *local* functional the De Giorgi class
estimates consume (`IsRegMinimizer.regFree_le`).

## Contents

* `pos_homogeneousDensity_two`, `pos_homogeneousDensity_two_smul`, `pos_entropyPotential_two`,
  `pos_entropyPotential_two_smul` — the `p = 2` normal forms and the scaling identities.
* `IsRegProfileWith.le_homogeneousDensity`, `IsRegProfileWith.homogeneousDensity_le` — the
  **standard quadratic growth** `Ψ(0) s² + (c/2)‖ξ‖² ≤ D(s,ξ) ≤ Ψ(0) s² + (C/2)‖ξ‖²` of the
  kinetic density.  This is what makes the local functional a quasi-minimum problem with the
  growth De Giorgi's theory needs.
* `MemW0.weakGrad_eq_zero_of_eq_zero` — `∇w = 0` a.e. on `{w = 0}` (the truncation chain rule
  at level `0`); it is what makes the lower bound above valid at `s = 0`, where the junk value
  of `D` is `0`.
* `IsRegComp` — the competitor class of the local problem (nonnegative, bounded, `W₀^{1,2}(K)`),
  with its integrability lemmas.
* `regFree`, `IsRegMinimizer.regFree_le` — the local functional and the local minimality
  property.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Elementary scalar inequalities -/

/-- `s log s ≥ s - 1` for `s ≥ 0` (with `log 0 = 0`): the convexity inequality behind the
choice of the multiplier `Λ = m + κ/4`. -/
theorem pos_sub_one_le_mul_log {s : ℝ} (hs : 0 ≤ s) : s - 1 ≤ s * Real.log s := by
  rcases hs.eq_or_lt with h | h
  · simp [← h]
  · have := Real.one_sub_inv_le_log_of_pos h
    have h2 : s * (1 - s⁻¹) ≤ s * Real.log s := mul_le_mul_of_nonneg_left this hs
    have h3 : s * (1 - s⁻¹) = s - 1 := by field_simp
    linarith [h3 ▸ h2]

/-- `|s² log s|` is bounded on `[0, M]` for `M ≥ 1`. -/
theorem pos_abs_sq_mul_log_le {s M : ℝ} (h0 : 0 ≤ s) (hsM : s ≤ M) (hM : 1 ≤ M) :
    |s ^ 2 * Real.log s| ≤ M ^ 2 * Real.log M + 1 := by
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hM0 : (0 : ℝ) ≤ M ^ 2 * Real.log M := by positivity
  rcases h0.eq_or_lt with h | hspos
  · simp [← h]
    linarith
  rcases le_or_gt s 1 with h1 | h1
  · -- `0 < s ≤ 1`: `|s² log s| = s²(-log s) ≤ s²(1/s - 1) ≤ 1`
    have hneg : Real.log s ≤ 0 := Real.log_nonpos hspos.le h1
    have hlow : 1 - s⁻¹ ≤ Real.log s := Real.one_sub_inv_le_log_of_pos hspos
    have habs : |s ^ 2 * Real.log s| = s ^ 2 * (-Real.log s) := by
      rw [abs_of_nonpos (by nlinarith)]; ring
    have hkey : s ^ 2 * (-Real.log s) ≤ s ^ 2 * (s⁻¹ - 1) := by
      nlinarith [sq_nonneg s]
    have he : s ^ 2 * (s⁻¹ - 1) = s - s ^ 2 := by field_simp; try ring
    rw [habs]
    nlinarith [sq_nonneg s]
  · -- `1 < s ≤ M`
    have hlogs : 0 ≤ Real.log s := Real.log_nonneg h1.le
    have h2 : Real.log s ≤ Real.log M := Real.log_le_log hspos hsM
    have h3 : s ^ 2 ≤ M ^ 2 := by nlinarith
    have habs : |s ^ 2 * Real.log s| = s ^ 2 * Real.log s := by
      rw [abs_of_nonneg (by positivity)]
    rw [habs]
    nlinarith

/-! ### The densities at exponent `2` -/

/-- The kinetic density at `p = 2`, with the natural-number power. -/
theorem pos_homogeneousDensity_two (Ψ : Euc d → ℝ) (s : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ s ξ = s ^ 2 * Ψ (s⁻¹ • ξ) := by
  rw [Korevaar.homogeneousDensity, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- The entropy potential at `p = 2`, with the natural-number power. -/
theorem pos_entropyPotential_two (κ s : ℝ) :
    Korevaar.entropyPotential 2 κ s = κ / 2 * (s ^ 2 * Real.log s) := by
  rw [Korevaar.entropyPotential, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

@[simp] theorem pos_homogeneousDensity_two_zero (Ψ : Euc d → ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ 0 ξ = 0 := by
  rw [pos_homogeneousDensity_two]; ring

@[simp] theorem entropyPotential_two_zero (κ : ℝ) : Korevaar.entropyPotential 2 κ (0 : ℝ) = 0 := by
  rw [pos_entropyPotential_two]; ring

/-- **Joint `2`-homogeneity of the kinetic density.** -/
theorem pos_homogeneousDensity_two_smul (Ψ : Euc d → ℝ) {a : ℝ} (ha : 0 < a) (s : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ (a * s) (a • ξ) =
      a ^ 2 * Korevaar.homogeneousDensity 2 Ψ s ξ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · rw [pos_homogeneousDensity_two, pos_homogeneousDensity_two]
    have hsmul : (a * s)⁻¹ • (a • ξ) = s⁻¹ • ξ := by
      rw [smul_smul, mul_inv, mul_comm a⁻¹ s⁻¹, mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]
    rw [hsmul]
    ring

/-- **The scaling of the entropy potential**: `P(a s) = a² (P(s) + (κ/2)(log a) s²)`. -/
theorem pos_entropyPotential_two_smul (κ : ℝ) {a : ℝ} (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    Korevaar.entropyPotential 2 κ (a * s) =
      a ^ 2 * (Korevaar.entropyPotential 2 κ s + κ / 2 * Real.log a * s ^ 2) := by
  rcases hs.eq_or_lt with h | hspos
  · simp [← h]
  · rw [pos_entropyPotential_two, pos_entropyPotential_two, Real.log_mul ha.ne' hspos.ne']
    ring

/-! ### Quadratic growth of the kinetic density -/

namespace IsRegProfileWith

variable {Ψ : Euc d → ℝ} {c C : ℝ}

/-- **Upper quadratic growth**: `D(s, ξ) ≤ Ψ(0) s² + (C/2) ‖ξ‖²` for `s ≥ 0`. -/
theorem homogeneousDensity_le (h : IsRegProfileWith Ψ c C) {s : ℝ} (hs : 0 ≤ s) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ s ξ ≤ Ψ 0 * s ^ 2 + C / 2 * ‖ξ‖ ^ 2 := by
  rcases hs.eq_or_lt with hz | hspos
  · rw [← hz]
    simp only [pos_homogeneousDensity_two_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, zero_add]
    exact mul_nonneg (by linarith [h.C_nonneg]) (sq_nonneg _)
  · rw [pos_homogeneousDensity_two]
    have hq := h.quadratic_upper (s⁻¹ • ξ)
    have hnorm : ‖s⁻¹ • ξ‖ ^ 2 = (s ^ 2)⁻¹ * ‖ξ‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ s⁻¹), mul_pow]
      rw [← inv_pow]
    rw [hnorm] at hq
    have hs2 : (0 : ℝ) < s ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hq hs2.le
    calc s ^ 2 * Ψ (s⁻¹ • ξ) ≤ s ^ 2 * (Ψ 0 + C / 2 * ((s ^ 2)⁻¹ * ‖ξ‖ ^ 2)) := this
      _ = Ψ 0 * s ^ 2 + C / 2 * ‖ξ‖ ^ 2 := by field_simp; try ring

/-- **Lower quadratic growth**: `Ψ(0) s² + (c/2) ‖ξ‖² ≤ D(s, ξ)` for `s ≥ 0`, provided `ξ = 0`
when `s = 0` (which is the a.e. situation, by `MemW0.weakGrad_eq_zero_of_eq_zero`). -/
theorem le_homogeneousDensity (h : IsRegProfileWith Ψ c C) {s : ℝ} (hs : 0 ≤ s) {ξ : Euc d}
    (hξ : s = 0 → ξ = 0) :
    Ψ 0 * s ^ 2 + c / 2 * ‖ξ‖ ^ 2 ≤ Korevaar.homogeneousDensity 2 Ψ s ξ := by
  rcases hs.eq_or_lt with hz | hspos
  · rw [hξ hz.symm]; simp [← hz]
  · rw [pos_homogeneousDensity_two]
    have hq := h.quadratic_lower (s⁻¹ • ξ)
    have hnorm : ‖s⁻¹ • ξ‖ ^ 2 = (s ^ 2)⁻¹ * ‖ξ‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ s⁻¹), mul_pow]
      rw [← inv_pow]
    rw [hnorm] at hq
    have hs2 : (0 : ℝ) < s ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hq hs2.le
    calc Ψ 0 * s ^ 2 + c / 2 * ‖ξ‖ ^ 2
        = s ^ 2 * (Ψ 0 + c / 2 * ((s ^ 2)⁻¹ * ‖ξ‖ ^ 2)) := by field_simp; try ring
      _ ≤ s ^ 2 * Ψ (s⁻¹ • ξ) := this

/-- The two-sided bound in absolute value. -/
theorem abs_homogeneousDensity_le (h : IsRegProfileWith Ψ c C) {s : ℝ} (hs : 0 ≤ s) {ξ : Euc d}
    (hξ : s = 0 → ξ = 0) :
    |Korevaar.homogeneousDensity 2 Ψ s ξ| ≤ |Ψ 0| * s ^ 2 + C / 2 * ‖ξ‖ ^ 2 := by
  have hup := h.homogeneousDensity_le hs ξ
  have hlo := h.le_homogeneousDensity hs hξ
  have h1 : Ψ 0 * s ^ 2 ≤ |Ψ 0| * s ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have h2 : -(|Ψ 0| * s ^ 2) ≤ Ψ 0 * s ^ 2 := by
    nlinarith [neg_abs_le (Ψ 0), sq_nonneg s]
  have hc2 : 0 ≤ c / 2 * ‖ξ‖ ^ 2 := mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
  have hC2 : 0 ≤ C / 2 * ‖ξ‖ ^ 2 := mul_nonneg (by linarith [h.C_nonneg]) (sq_nonneg _)
  rw [abs_le]
  constructor <;> linarith

end IsRegProfileWith


/-! ### The weak gradient vanishes on the zero set -/

/-- **`∇w = 0` a.e. on `{w = 0}`** for a nonnegative `w ∈ W₀^{1,p}(K)`: the truncation chain rule
`memW0_posPart` at level `0` says `∇(w)_+ = 1_{w>0} ∇w`, and `(w)_+ = w`. -/
theorem _root_.Komlos.Literature.MemW0.weakGrad_eq_zero_of_eq_zero {p : ℝ} (hp : 1 < p)
    {K : Set (Euc d)} {w : Euc d → ℝ}
    (hw : MemW0 p K w) (hw0 : ∀ᵐ x, 0 ≤ w x) :
    ∀ᵐ x, w x = 0 → weakGrad w x = 0 := by
  obtain ⟨-, hgrad⟩ := memW0_posPart hp hw 0
  have heq : (fun x => posPartShift 0 (w x)) =ᵐ[volume] w := by
    filter_upwards [hw0] with x hx
    simp [posPartShift, max_eq_left hx]
  have hwg : HasWeakGradient w (fun x => (if (0 : ℝ) < w x then (1 : ℝ) else 0) • weakGrad w x) :=
    hgrad.congr_left heq
  filter_upwards [hw.hasWeakGradient.ae_eq hwg] with x hx hx0
  conv_lhs => rw [hx]
  simp [hx0]

/-! ### The competitor class of the local problem -/

/-- **Competitors for the local (unconstrained) problem**: nonnegative bounded elements of
`W₀^{1,2}(K)` vanishing off `K`.  Boundedness is what makes the entropy integrable; the
minimizer itself is in this class by `IsRegMinimizer.exists_regComp` (via the `L1` placeholder
`IsRegMinimizer.exists_bound`), and so is every truncation competitor `u - η²(u-k)_+`. -/
structure IsRegComp (K : Set (Euc d)) (w : Euc d → ℝ) : Prop where
  /-- `w ∈ W₀^{1,2}(K)`. -/
  memW0 : MemW0 2 K w
  /-- `w` is nonnegative. -/
  nonneg : ∀ x, 0 ≤ w x
  /-- `w` vanishes off `K`. -/
  eq_zero_of_notMem : ∀ x, x ∉ K → w x = 0
  /-- `w` is bounded above. -/
  exists_le : ∃ M : ℝ, ∀ x, w x ≤ M

namespace IsRegComp

variable {K : Set (Euc d)} {w : Euc d → ℝ}

theorem aestronglyMeasurable (h : IsRegComp K w) : AEStronglyMeasurable w volume :=
  h.memW0.memLp.aestronglyMeasurable

theorem aestronglyMeasurable_grad (h : IsRegComp K w) :
    AEStronglyMeasurable (weakGrad w) volume := h.memW0.memLp_weakGrad.aestronglyMeasurable

/-- `∇w = 0` a.e. where `w = 0`. -/
theorem weakGrad_eq_zero (h : IsRegComp K w) : ∀ᵐ x, w x = 0 → weakGrad w x = 0 :=
  h.memW0.weakGrad_eq_zero_of_eq_zero one_lt_two (Eventually.of_forall h.nonneg)

theorem integrable_sq (h : IsRegComp K w) : Integrable (fun x => w x ^ 2) volume := by
  have hm := h.memW0.memLp
  rw [dgn_ofReal_two] at hm
  exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 hm

theorem integrable_normSq_grad (h : IsRegComp K w) :
    Integrable (fun x => ‖weakGrad w x‖ ^ 2) volume := by
  have hm := h.memW0.memLp_weakGrad
  rw [dgn_ofReal_two] at hm
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable_grad).1 hm

/-- A bounded measurable function vanishing off the (bounded, open) set `K` is integrable. -/
theorem _root_.Komlos.Literature.Regularized.integrable_of_bounded_of_support
    {K : Set (Euc d)} (hK : IsGoodConvex K) {f : Euc d → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hB : ∀ x, |f x| ≤ B)
    (hsupp : ∀ x, x ∉ K → f x = 0) : Integrable f volume := by
  have hKfin : volume K ≠ ⊤ := hK.isBounded.measure_lt_top.ne
  have hdom : Integrable (K.indicator fun _ => B) volume := by
    rw [integrable_indicator_iff hK.isOpen.measurableSet]
    exact integrableOn_const hKfin
  refine hdom.mono hf (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    simpa [Real.norm_eq_abs] using (hB x).trans (le_abs_self B)
  · rw [Set.indicator_of_notMem hx, hsupp x hx]

theorem integrable_entropy (hK : IsGoodConvex K) (h : IsRegComp K w) (κ : ℝ) :
    Integrable (fun x => Korevaar.entropyPotential 2 κ (w x)) volume := by
  obtain ⟨M, hM⟩ := h.exists_le
  set M' : ℝ := max M 1 with hM'
  have hM1 : (1 : ℝ) ≤ M' := le_max_right _ _
  have hwM : ∀ x, w x ≤ M' := fun x => (hM x).trans (le_max_left _ _)
  have hmeas : AEStronglyMeasurable (fun x => Korevaar.entropyPotential 2 κ (w x)) volume := by
    have h1 : AEMeasurable (fun x => Real.log (w x)) volume :=
      Real.measurable_log.comp_aemeasurable h.aestronglyMeasurable.aemeasurable
    have h2 : AEStronglyMeasurable (fun x => w x ^ 2 * Real.log (w x)) volume :=
      (h.aestronglyMeasurable.pow 2).mul h1.aestronglyMeasurable
    refine (h2.const_mul (κ / 2)).congr (Eventually.of_forall fun x => ?_)
    show κ / 2 * (w x ^ 2 * Real.log (w x)) = Korevaar.entropyPotential 2 κ (w x)
    rw [pos_entropyPotential_two]
  refine integrable_of_bounded_of_support (B := |κ| / 2 * (M' ^ 2 * Real.log M' + 1)) hK hmeas
    (fun x => ?_) (fun x hx => by rw [h.eq_zero_of_notMem x hx, entropyPotential_two_zero])
  rw [pos_entropyPotential_two, abs_mul]
  have habs2 : |κ / 2| = |κ| / 2 := by rw [abs_div]; norm_num
  rw [habs2]
  exact mul_le_mul_of_nonneg_left (pos_abs_sq_mul_log_le (h.nonneg x) (hwM x) hM1)
    (by positivity)

theorem aestronglyMeasurable_density (h : IsRegComp K w) {Ψ : Euc d → ℝ} (hΨ : Continuous Ψ) :
    AEStronglyMeasurable
      (fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)) volume := by
  have h3 : AEMeasurable (fun x => (w x)⁻¹ • weakGrad w x) volume :=
    (h.aestronglyMeasurable.aemeasurable.inv).smul h.aestronglyMeasurable_grad.aemeasurable
  have h4 : AEStronglyMeasurable (fun x => Ψ ((w x)⁻¹ • weakGrad w x)) volume :=
    (hΨ.measurable.comp_aemeasurable h3).aestronglyMeasurable
  refine ((h.aestronglyMeasurable.pow 2).mul h4).congr (Eventually.of_forall fun x => ?_)
  show w x ^ 2 * Ψ ((w x)⁻¹ • weakGrad w x)
      = Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)
  rw [pos_homogeneousDensity_two]

theorem integrable_density (h : IsRegComp K w) {Ψ : Euc d → ℝ} {c C : ℝ}
    (hΨ : IsRegProfileWith Ψ c C) :
    Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)) volume := by
  refine Integrable.mono' ((h.integrable_sq.const_mul |Ψ 0|).add
    (h.integrable_normSq_grad.const_mul (C / 2)))
    (h.aestronglyMeasurable_density hΨ.toIsRegProfile.contDiff.continuous) ?_
  filter_upwards [h.weakGrad_eq_zero] with x hx
  rw [Real.norm_eq_abs]
  exact hΨ.abs_homogeneousDensity_le (h.nonneg x) hx

/-- Scaling a competitor by a nonnegative constant. -/
theorem const_mul (h : IsRegComp K w) {a : ℝ} (ha : 0 ≤ a) :
    IsRegComp K (fun x => a * w x) := by
  obtain ⟨M, hM⟩ := h.exists_le
  have hmem : MemW0 2 K (fun x => a * w x) := h.memW0.smul a
  exact ⟨hmem, fun x => mul_nonneg ha (h.nonneg x),
    fun x hx => by rw [h.eq_zero_of_notMem x hx, mul_zero],
    ⟨a * M, fun x => mul_le_mul_of_nonneg_left (hM x) ha⟩⟩

end IsRegComp

/-! ### The local functional -/

/-- The **local (unconstrained) functional** of `REGULARIZED_ROUTE.md`, Revision 2 (i):
`J_Λ(w) = ∫ [ w² Ψ(∇w/w) + (κ/2) w² log w - Λ w² ]`.  With `Λ = regMin 2 κ Ψ K + κ/4` the
constrained minimizer `u` minimizes `J_Λ` over the whole class `IsRegComp K`
(`IsRegMinimizer.regFree_le`). -/
noncomputable def regFree (κ Λ : ℝ) (Ψ : Euc d → ℝ) (w : Euc d → ℝ) : ℝ :=
  ∫ x, (Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) +
    Korevaar.entropyPotential 2 κ (w x) - Λ * w x ^ 2)

/-- `J_Λ(w) = E(w) - Λ ∫ w²`. -/
theorem regFree_eq_regEnergy_sub {K : Set (Euc d)} (hK : IsGoodConvex K) {w : Euc d → ℝ}
    (h : IsRegComp K w) {Ψ : Euc d → ℝ} {c C : ℝ} (hΨ : IsRegProfileWith Ψ c C) (κ Λ : ℝ) :
    regFree κ Λ Ψ w = regEnergy 2 κ Ψ w - Λ * ∫ x, w x ^ 2 := by
  have h1 : Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)) volume :=
    h.integrable_density hΨ
  have h2 : Integrable (fun x => Korevaar.entropyPotential 2 κ (w x)) volume :=
    h.integrable_entropy hK κ
  have h3 : Integrable (fun x => Λ * w x ^ 2) volume := h.integrable_sq.const_mul Λ
  calc regFree κ Λ Ψ w
      = (∫ x, (Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) +
          Korevaar.entropyPotential 2 κ (w x))) - ∫ x, Λ * w x ^ 2 :=
        integral_sub (h1.add h2) h3
    _ = regEnergy 2 κ Ψ w - Λ * ∫ x, w x ^ 2 := by
        rw [integral_add h1 h2, integral_const_mul, regEnergy]


/-! ### Transporting a minimizer along an a.e. equality -/

/-- `IsRegMinimizer` only depends on the a.e.-class of `u` (once the pointwise sign and support
conditions are restored). -/
theorem IsRegMinimizer.congr_ae {κ : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u v : Euc d → ℝ}
    (hu : IsRegMinimizer 2 κ Ψ K u) (hv : v =ᵐ[volume] u) (hv0 : ∀ x, 0 ≤ v x)
    (hvK : ∀ x, x ∉ K → v x = 0) : IsRegMinimizer 2 κ Ψ K v := by
  have hgrad : weakGrad v =ᵐ[volume] weakGrad u :=
    (hu.memW0.hasWeakGradient.congr_left hv.symm).weakGrad_ae_eq
  have henergy : regEnergy 2 κ Ψ v = regEnergy 2 κ Ψ u := by
    simp only [regEnergy]
    congr 1
    · exact integral_congr_ae (by filter_upwards [hv, hgrad] with x h1 h2; rw [h1, h2])
    · exact integral_congr_ae (by filter_upwards [hv] with x h1; rw [h1])
  exact { memW0 := hu.memW0.congr hv.symm
          nonneg := hv0
          eq_zero_of_notMem := hvK
          integral_rpow := by
            rw [← hu.integral_rpow]
            exact integral_congr_ae (by filter_upwards [hv] with x h1; rw [h1])
          energy_eq := by rw [henergy, hu.energy_eq]
          bddBelow := hu.bddBelow }

/-- **The minimizer has a bounded representative in the local competitor class.**  Uses the
lane-`L1` placeholder `IsRegMinimizer.exists_bound` (essential boundedness by truncation
comparison) and truncates at the bound. -/
theorem IsRegMinimizer.exists_regComp {κ : ℝ} (hκ : 0 < κ) {Ψ : Euc d → ℝ} (hΨ : IsRegProfile Ψ)
    {K : Set (Euc d)} (hK : IsGoodConvex K) {u : Euc d → ℝ} (hu : IsRegMinimizer 2 κ Ψ K u) :
    ∃ v : Euc d → ℝ, v =ᵐ[volume] u ∧ IsRegMinimizer 2 κ Ψ K v ∧ IsRegComp K v := by
  obtain ⟨M, hM⟩ := hu.exists_bound hκ hΨ hK
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hae : (fun x => min (u x) (max M 0)) =ᵐ[volume] u := by
    filter_upwards [hM] with x hx
    exact min_eq_left (hx.trans (le_max_left _ _))
  have hv0 : ∀ x, 0 ≤ min (u x) (max M 0) := fun x => le_min (hu.nonneg x) hM0
  have hvK : ∀ x, x ∉ K → min (u x) (max M 0) = 0 := fun x hx => by
    rw [hu.eq_zero_of_notMem x hx]; exact min_eq_left hM0
  have hmin := hu.congr_ae hae hv0 hvK
  exact ⟨_, hae, hmin, ⟨hmin.memW0, hv0, hvK, ⟨max M 0, fun x => min_le_right _ _⟩⟩⟩

/-! ### Scaling -/

/-- The weak gradient of `a w`. -/
theorem weakGrad_const_mul {w : Euc d → ℝ} (hw : ∃ g, HasWeakGradient w g) (a : ℝ) :
    weakGrad (fun x => a * w x) =ᵐ[volume] fun x => a • weakGrad w x := by
  have h0 := (hasWeakGradient_weakGrad hw).smul a
  have h1 : HasWeakGradient (fun x => a * w x) (fun x => a • weakGrad w x) := by
    refine (h0.congr_left (Eventually.of_forall fun x => ?_)).congr_right
      (Eventually.of_forall fun x => ?_) <;> simp
  exact h1.weakGrad_ae_eq

variable {K : Set (Euc d)} {w : Euc d → ℝ}

/-- The kinetic part scales by `a²`. -/
theorem regKin_const_mul (h : IsRegComp K w) {Ψ : Euc d → ℝ} {a : ℝ} (ha : 0 < a) :
    (∫ x, Korevaar.homogeneousDensity 2 Ψ (a * w x) (weakGrad (fun y => a * w y) x)) =
      a ^ 2 * ∫ x, Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [weakGrad_const_mul ⟨weakGrad w, h.memW0.hasWeakGradient⟩ a] with x hx
  rw [hx]
  exact pos_homogeneousDensity_two_smul Ψ ha (w x) (weakGrad w x)

/-- The entropy part scales by `a²` up to the explicit `log a` correction. -/
theorem regEnt_const_mul (hK : IsGoodConvex K) (h : IsRegComp K w) (κ : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ x, Korevaar.entropyPotential 2 κ (a * w x)) =
      a ^ 2 * ((∫ x, Korevaar.entropyPotential 2 κ (w x)) +
        κ / 2 * Real.log a * ∫ x, w x ^ 2) := by
  have hE := h.integrable_entropy hK κ
  have hS := h.integrable_sq
  have hstep : (∫ x, Korevaar.entropyPotential 2 κ (a * w x)) =
      ∫ x, a ^ 2 * (Korevaar.entropyPotential 2 κ (w x) + κ / 2 * Real.log a * w x ^ 2) :=
    integral_congr_ae (Eventually.of_forall fun x =>
      pos_entropyPotential_two_smul κ ha (h.nonneg x))
  rw [hstep, integral_const_mul, integral_add hE (hS.const_mul _), integral_const_mul]

/-! ### Local minimality -/

/-- The value of the local functional at the minimizer is `-κ/4`. -/
theorem IsRegMinimizer.regFree_eq {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ}
    (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K) {u : Euc d → ℝ}
    (hu : IsRegMinimizer 2 κ Ψ K u) (hcomp : IsRegComp K u) :
    regFree κ (regMin 2 κ Ψ K + κ / 4) Ψ u = -(κ / 4) := by
  rw [regFree_eq_regEnergy_sub hK hcomp hΨ, hu.energy_eq, hu.integral_sq]
  ring

/-- **The local lower bound**: every competitor has `regFree ≥ -κ/4`.

This is the content of `REGULARIZED_ROUTE.md`, Revision 2 (i): rescale `w` to `w/‖w‖₂`, which is
admissible, use `regMin ≤ regEnergy(w/‖w‖₂)` and the explicit scaling of the two densities, and
finally the elementary convexity inequality `s log s ≥ s - 1` at `s = ∫ w²`. -/
theorem IsRegMinimizer.neg_le_regFree {κ : ℝ} (hκ : 0 < κ) {Ψ : Euc d → ℝ} {c C : ℝ}
    (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K) {u : Euc d → ℝ}
    (hu : IsRegMinimizer 2 κ Ψ K u) (hw : IsRegComp K w) :
    -(κ / 4) ≤ regFree κ (regMin 2 κ Ψ K + κ / 4) Ψ w := by
  set m : ℝ := regMin 2 κ Ψ K with hm
  have hfree : regFree κ (m + κ / 4) Ψ w = regEnergy 2 κ Ψ w - (m + κ / 4) * ∫ x, w x ^ 2 :=
    regFree_eq_regEnergy_sub hK hw hΨ _ _
  set S : ℝ := ∫ x, w x ^ 2 with hSdef
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  rcases hS0.eq_or_lt with hz | hpos
  · -- `∫ w² = 0`: then `w = 0` a.e. and the local functional vanishes
    have hsq : (fun x => w x ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (w x)) hw.integrable_sq).1
        (hSdef ▸ hz.symm)
    have hw0 : w =ᵐ[volume] 0 := by
      filter_upwards [hsq] with x hx
      have hx' : w x ^ 2 = 0 := by simpa using hx
      have hw' : w x = 0 := by nlinarith [sq_nonneg (w x)]
      show w x = (0 : Euc d → ℝ) x
      rw [hw']
      rfl
    have hgw : weakGrad w =ᵐ[volume] 0 :=
      hw.memW0.hasWeakGradient.ae_eq (HasWeakGradient.zero.congr_left hw0.symm)
    have hzero : regFree κ (m + κ / 4) Ψ w = 0 := by
      rw [regFree]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hw0, hgw] with x h1 h2
      simp only [Pi.zero_apply] at h1 h2
      show Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) +
          Korevaar.entropyPotential 2 κ (w x) - (m + κ / 4) * w x ^ 2 = 0
      rw [h1, h2, pos_homogeneousDensity_two_zero, entropyPotential_two_zero]
      ring
    rw [hzero]
    linarith
  · -- the generic case: rescale to the admissible class
    set t : ℝ := Real.sqrt S with htdef
    have htpos : 0 < t := Real.sqrt_pos.2 hpos
    have ht2 : t ^ 2 = S := Real.sq_sqrt hS0
    have hapos : 0 < t⁻¹ := inv_pos.2 htpos
    have ha2 : (t⁻¹) ^ 2 = S⁻¹ := by rw [inv_pow, ht2]
    have hvcomp : IsRegComp K (fun x => t⁻¹ * w x) := hw.const_mul hapos.le
    have hvint : (∫ x, (t⁻¹ * w x) ^ 2) = 1 := by
      simp_rw [mul_pow]
      rw [integral_const_mul, ← hSdef, ha2, inv_mul_cancel₀ hpos.ne']
    have hadm : IsRegAdmissible 2 K (fun x => t⁻¹ * w x) :=
      { memW0 := hvcomp.memW0
        nonneg := hvcomp.nonneg
        eq_zero_of_notMem := hvcomp.eq_zero_of_notMem
        integral_rpow := by
          rw [← hvint]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          show (t⁻¹ * w x) ^ (2 : ℝ) = (t⁻¹ * w x) ^ 2
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] }
    have hminle : m ≤ regEnergy 2 κ Ψ (fun x => t⁻¹ * w x) := by
      rw [hm, regMin]
      exact ciInf_le hu.bddBelow ⟨_, hadm⟩
    have hexp : regEnergy 2 κ Ψ (fun x => t⁻¹ * w x) =
        (t⁻¹) ^ 2 * (regEnergy 2 κ Ψ w + κ / 2 * Real.log t⁻¹ * S) := by
      simp only [regEnergy]
      rw [regKin_const_mul hw hapos (Ψ := Ψ), regEnt_const_mul hK hw κ hapos, ← hSdef]
      ring
    have hloga : Real.log t⁻¹ = -(Real.log S / 2) := by
      rw [Real.log_inv, htdef, Real.log_sqrt hS0]
    rw [hexp, ha2, hloga] at hminle
    have hkey : m * S ≤ regEnergy 2 κ Ψ w - κ / 4 * (S * Real.log S) := by
      have h1 : S⁻¹ * (regEnergy 2 κ Ψ w + κ / 2 * -(Real.log S / 2) * S) =
          (regEnergy 2 κ Ψ w - κ / 4 * (S * Real.log S)) / S := by
        field_simp
        try ring
      rw [h1] at hminle
      exact (le_div_iff₀ hpos).1 hminle
    have hlog := pos_sub_one_le_mul_log hS0
    have hpos2 : 0 ≤ κ / 4 * (S * Real.log S - S + 1) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hfree]
    nlinarith [hkey, hpos2]

/-- **Local minimality of the constrained minimizer** (`REGULARIZED_ROUTE.md`, Revision 2 (i)):
with the multiplier `Λ = m + κ/4`, the minimizer `u` minimizes the *unconstrained* local
functional `regFree κ Λ Ψ` over all nonnegative bounded `w ∈ W₀^{1,2}(K)`.  This is the form the
De Giorgi class estimates consume: the truncation competitors `u - η²(u-k)_+` are admissible for
it, but not for the constrained problem. -/
theorem IsRegMinimizer.regFree_le {κ : ℝ} (hκ : 0 < κ) {Ψ : Euc d → ℝ} {c C : ℝ}
    (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K) {u : Euc d → ℝ}
    (hu : IsRegMinimizer 2 κ Ψ K u) (hucomp : IsRegComp K u) (hw : IsRegComp K w) :
    regFree κ (regMin 2 κ Ψ K + κ / 4) Ψ u ≤ regFree κ (regMin 2 κ Ψ K + κ / 4) Ψ w := by
  rw [hu.regFree_eq hΨ hK hucomp]
  exact hu.neg_le_regFree hκ hΨ hK hw


end Komlos.Literature.Regularized
