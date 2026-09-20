import Komlos.Literature.Regularized.TruncatedProfileElliptic
import Komlos.Literature.Sobolev.Density
import Komlos.Literature.Regularized.VariationalEnergy

/-!
# Well-definedness of the regularized energy, and the two `regMin` tools

`regEnergy` is written with Bochner integrals, which take the value `0` on a non-integrable
integrand.  Before any statement about `regMin 2 κ Ψ K` can be proved one has to know that the
integrands are genuinely integrable (for the kinetic term) or at least bounded below (for the
entropy term).  This file supplies that, for an arbitrary profile of the class `IsRegProfile`.

## Contents

* `homogeneousDensity_two_*`: the kinetic density `D(t, ξ) = t² Ψ(ξ/t)` at exponent `2` — its
  value `0` at `t = 0`, its `2`-homogeneity, and the two-sided bound
  `Ψ 0 · t² ≤ D(t, ξ) ≤ Ψ 0 · t² + (C/2)‖ξ‖²` coming from the quadratic growth of a regularized
  profile.  Consequently the kinetic integrand of an admissible competitor is squeezed between
  two integrable functions (`integrable_kinetic`), so the kinetic integral is honest, and
  `Ψ 0 ≤ ∫ D` (`le_integral_kinetic`).
* `mul_log_ge_of_pos` and `entropy_integral_ge`: the elementary Jensen bound
  `∫ w² log w ≥ -(1/2) log |K|` for a nonnegative `w` supported in `K` with `∫ w² = 1`
  (from `t log t ≥ t log a + t - a`, `a = 1/|K|`), combined with the junk-value case split, so
  that the entropy integral is bounded below by `-(κ/2)|(1/2) log |K||` unconditionally.
* `isRegAdmissible_smul_testFn`: normalizing a nonnegative test
  function produces an admissible competitor, so the competitor class is nonempty.
* `bddBelow_regEnergy`, `regMin_le_of_isRegAdmissible`, `le_regMin_of_forall`: the two tools for bounding
  `regMin` from above (exhibit a competitor) and from below (bound every competitor).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### `rpow 2` versus the square -/

/-- The real power `t ^ (2 : ℝ)` is the square. -/
theorem rpow_two_eq_sq (t : ℝ) : t ^ (2 : ℝ) = t ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ### Measure-theoretic facts about a good convex body -/

section GoodConvex

variable {K : Set (Euc d)}

theorem _root_.Komlos.IsGoodConvex.measure_pos (hK : IsGoodConvex K) : 0 < volume K :=
  hK.isOpen.measure_pos volume hK.nonempty

theorem _root_.Komlos.IsGoodConvex.measure_ne_top (hK : IsGoodConvex K) : volume K ≠ ⊤ :=
  hK.isBounded.measure_lt_top.ne

theorem _root_.Komlos.IsGoodConvex.toReal_measure_pos (hK : IsGoodConvex K) :
    0 < (volume K).toReal :=
  ENNReal.toReal_pos hK.measure_pos.ne' hK.measure_ne_top

theorem _root_.Komlos.IsGoodConvex.measurableSet (hK : IsGoodConvex K) : MeasurableSet K :=
  hK.isOpen.measurableSet

end GoodConvex

/-! ### The kinetic density at exponent `2` -/

section Kinetic

variable {Ψ : Euc d → ℝ} {c C : ℝ}

/-- `2`-homogeneity of the kinetic density. -/
theorem scalarLimit_homogeneousDensity_two_smul (Ψ : Euc d → ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ)
    (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ (a * t) (a • ξ) =
      a ^ 2 * Korevaar.homogeneousDensity 2 Ψ t ξ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have hat : a * t ≠ 0 := mul_ne_zero ha.ne' ht
    have harg : (a * t)⁻¹ • (a • ξ) = t⁻¹ • ξ := by
      rw [smul_smul]
      congr 1
      field_simp
    simp only [Korevaar.homogeneousDensity, harg, rpow_two_eq_sq]
    ring

/-- The upper half of the two-sided bound for the kinetic density. -/
theorem homogeneousDensity_two_le (h : IsRegProfileWith Ψ c C) {t : ℝ} (ht : 0 ≤ t) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ t ξ ≤ Ψ 0 * t ^ 2 + C / 2 * ‖ξ‖ ^ 2 := by
  rcases ht.eq_or_lt with rfl | htpos
  · simpa using mul_nonneg (by linarith [h.C_nonneg]) (sq_nonneg ‖ξ‖)
  · have hq := h.quadratic_upper (t⁻¹ • ξ)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 htpos), mul_pow, inv_pow] at hq
    have hmul := mul_le_mul_of_nonneg_left hq (sq_nonneg t)
    have hts : t ^ 2 ≠ 0 := pow_ne_zero 2 htpos.ne'
    simp only [Korevaar.homogeneousDensity, rpow_two_eq_sq]
    calc t ^ 2 * Ψ (t⁻¹ • ξ) ≤ t ^ 2 * (Ψ 0 + C / 2 * ((t ^ 2)⁻¹ * ‖ξ‖ ^ 2)) := hmul
      _ = Ψ 0 * t ^ 2 + C / 2 * ‖ξ‖ ^ 2 := by field_simp

/-- The lower half of the two-sided bound for the kinetic density. -/
theorem le_homogeneousDensity_two (h : IsRegProfileWith Ψ c C) {t : ℝ} (ht : 0 ≤ t) (ξ : Euc d) :
    Ψ 0 * t ^ 2 ≤ Korevaar.homogeneousDensity 2 Ψ t ξ := by
  rcases ht.eq_or_lt with rfl | htpos
  · simp
  · have hq := h.quadratic_lower (t⁻¹ • ξ)
    have hc : 0 ≤ c / 2 * ‖(t⁻¹ • ξ : Euc d)‖ ^ 2 :=
      mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
    have h0 : Ψ 0 ≤ Ψ (t⁻¹ • ξ) := by linarith
    simp only [Korevaar.homogeneousDensity, rpow_two_eq_sq]
    have := mul_le_mul_of_nonneg_left h0 (sq_nonneg t)
    linarith [this]

/-- The kinetic density of an admissible competitor is measurable. -/
theorem aestronglyMeasurable_kinetic (hΨ : Continuous Ψ) {w : Euc d → ℝ}
    (hw : AEStronglyMeasurable w volume) (hg : AEStronglyMeasurable (weakGrad w) volume) :
    AEStronglyMeasurable
      (fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)) volume := by
  have hrpow : Continuous fun t : ℝ => t ^ (2 : ℝ) :=
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x 2 (Or.inr (by norm_num))
  have h1 : AEStronglyMeasurable (fun x => w x ^ (2 : ℝ)) volume :=
    hrpow.comp_aestronglyMeasurable hw
  have hinv : AEStronglyMeasurable (fun x => (w x)⁻¹) volume :=
    hw.aemeasurable.inv.aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun x => (w x)⁻¹ • weakGrad w x) volume := hinv.smul hg
  exact h1.mul (hΨ.comp_aestronglyMeasurable h2)

/-- **The kinetic integrand of an admissible competitor is integrable.**  It is squeezed between
`Ψ(0) w²` and `Ψ(0) w² + (C/2)‖∇w‖²`, and `w, ∇w ∈ L²`. -/
theorem integrable_kinetic (h : IsRegProfileWith Ψ c C) {K : Set (Euc d)} {w : Euc d → ℝ}
    (hw : MemW0 2 K w) (hwnn : ∀ x, 0 ≤ w x) :
    Integrable fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) := by
  have hw2 : MemLp w 2 volume := by
    have := hw.memLp; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at this
  have hg2 : MemLp (weakGrad w) 2 volume := by
    have := hw.memLp_weakGrad; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at this
  have hi1 : Integrable fun x => w x ^ 2 := hw2.integrable_sq
  have hi2 : Integrable fun x => ‖weakGrad w x‖ ^ 2 := hg2.norm.integrable_sq
  refine Integrable.mono' (g := fun x => |Ψ 0| * w x ^ 2 + C / 2 * ‖weakGrad w x‖ ^ 2)
    ((hi1.const_mul |Ψ 0|).add (hi2.const_mul (C / 2)))
    (aestronglyMeasurable_kinetic h.toIsRegProfile.contDiff.continuous hw2.1 hg2.1)
    (Eventually.of_forall fun x => ?_)
  have hub := homogeneousDensity_two_le h (hwnn x) (weakGrad w x)
  have hlb := le_homogeneousDensity_two h (hwnn x) (weakGrad w x)
  have habs : Ψ 0 * w x ^ 2 ≤ |Ψ 0| * w x ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have habs' : -(|Ψ 0| * w x ^ 2) ≤ Ψ 0 * w x ^ 2 := by
    have : -|Ψ 0| ≤ Ψ 0 := neg_abs_le _
    nlinarith [sq_nonneg (w x)]
  have hCn : 0 ≤ C / 2 * ‖weakGrad w x‖ ^ 2 :=
    mul_nonneg (by linarith [h.C_nonneg]) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- The kinetic integral of an admissible competitor is at least `Ψ 0`. -/
theorem le_integral_kinetic (h : IsRegProfileWith Ψ c C) {K : Set (Euc d)} {w : Euc d → ℝ}
    (hw : IsRegAdmissible 2 K w) :
    Ψ 0 ≤ ∫ x, Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) := by
  have hw2 : MemLp w 2 volume := by
    have := hw.memW0.memLp; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at this
  have hi1 : Integrable fun x => w x ^ 2 := hw2.integrable_sq
  have hmono := integral_mono (hi1.const_mul (Ψ 0))
    (integrable_kinetic h hw.memW0 hw.nonneg)
    (fun x => le_homogeneousDensity_two h (hw.nonneg x) (weakGrad w x))
  rwa [integral_const_mul, hw.integral_sq, mul_one] at hmono

end Kinetic

/-! ### The entropy -/

section Entropy

/-- `t log a + t - a ≤ t log t` for `t ≥ 0` and `a > 0` (the tangent-line inequality for the
convex function `t ↦ t log t`). -/
theorem mul_log_ge_of_pos {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) :
    t * Real.log a + t - a ≤ t * Real.log t := by
  rcases ht.eq_or_lt with rfl | htpos
  · simpa using ha.le
  · have hlog := Real.log_le_sub_one_of_pos (div_pos ha htpos)
    rw [Real.log_div ha.ne' htpos.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog htpos.le
    have hdiv : t * (a / t - 1) = a - t := by field_simp
    rw [hdiv] at hmul
    nlinarith [hmul]

/-- **The entropy Jensen bound**: for `w ≥ 0` vanishing off `K` with `∫ w² = 1`,
`∫ w² log w ≥ -(1/2) log |K|`.  Apply the tangent-line inequality to `ρ = w²` at `a = 1/|K|`
and integrate; the indicator of `K` makes the constant term integrable. -/
theorem integral_sq_mul_log_ge {K : Set (Euc d)} (hK : IsGoodConvex K) {w : Euc d → ℝ}
    (hw : IsRegAdmissible 2 K w)
    (hint : Integrable fun x => w x ^ 2 * Real.log (w x)) :
    -(1 / 2) * Real.log (volume K).toReal ≤ ∫ x, w x ^ 2 * Real.log (w x) := by
  set V : ℝ := (volume K).toReal with hV
  have hVpos : 0 < V := hK.toReal_measure_pos
  set a : ℝ := 1 / V with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hw2 : MemLp w 2 volume := by
    have := hw.memW0.memLp; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at this
  have hi1 : Integrable fun x => w x ^ 2 := hw2.integrable_sq
  have hiK : Integrable (Set.indicator K fun _ : Euc d => a) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_ne_top)
  -- the pointwise tangent-line inequality, with the constant carried by an indicator
  have hpt : ∀ x : Euc d,
      Real.log a * w x ^ 2 + w x ^ 2 - Set.indicator K (fun _ => a) x ≤
        2 * (w x ^ 2 * Real.log (w x)) := by
    intro x
    have hlog2 : w x ^ 2 * Real.log (w x ^ 2) = 2 * (w x ^ 2 * Real.log (w x)) := by
      rw [Real.log_pow]; push_cast; ring
    rw [← hlog2]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have := mul_log_ge_of_pos hapos (sq_nonneg (w x))
      linarith
    · rw [Set.indicator_of_notMem hx, hw.eq_zero_of_notMem x hx]
      simp
  have hI1 : Integrable (fun x : Euc d => Real.log a * w x ^ 2) volume := hi1.const_mul _
  have hI2 : Integrable (fun x : Euc d => Real.log a * w x ^ 2 + w x ^ 2) volume := hI1.add hi1
  have hI3 : Integrable
      (fun x : Euc d =>
        Real.log a * w x ^ 2 + w x ^ 2 - Set.indicator K (fun _ => a) x) volume := hI2.sub hiK
  have hintegral := integral_mono hI3 (hint.const_mul 2) hpt
  have hlhs : (∫ x : Euc d,
      (Real.log a * w x ^ 2 + w x ^ 2 - Set.indicator K (fun _ => a) x)) =
        Real.log a * 1 + 1 - (volume K).toReal * a := by
    rw [integral_sub hI2 hiK, integral_add hI1 hi1, integral_const_mul, hw.integral_sq,
      integral_indicator_const _ hK.measurableSet, smul_eq_mul]
    rfl
  rw [hlhs, integral_const_mul] at hintegral
  have hVa : (volume K).toReal * a = 1 := by rw [ha, ← hV]; field_simp
  have hloga : Real.log a = -Real.log V := by
    rw [ha, one_div, Real.log_inv]
  rw [hVa, hloga] at hintegral
  linarith

/-- **The entropy integral is bounded below**, unconditionally: if the entropy integrand is
integrable the Jensen bound applies, and otherwise the Bochner integral is `0`. -/
theorem entropy_integral_ge {κ : ℝ} (hκ : 0 < κ) {K : Set (Euc d)} (hK : IsGoodConvex K)
    {w : Euc d → ℝ} (hw : IsRegAdmissible 2 K w) :
    -(κ / 2) * |(1 / 2) * Real.log (volume K).toReal| ≤
      ∫ x, Korevaar.entropyPotential 2 κ (w x) := by
  have hrw : (fun x => Korevaar.entropyPotential 2 κ (w x)) =
      fun x => κ / 2 * (w x ^ 2 * Real.log (w x)) := by
    funext x
    simp [Korevaar.entropyPotential]
  rw [hrw, integral_const_mul]
  by_cases hint : Integrable fun x => w x ^ 2 * Real.log (w x)
  · have h := integral_sq_mul_log_ge hK hw hint
    have hb : -|(1 / 2) * Real.log (volume K).toReal| ≤
        ∫ x, w x ^ 2 * Real.log (w x) := le_trans (by
      have := le_abs_self ((1 / 2) * Real.log (volume K).toReal)
      linarith) h
    have := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ κ / 2)
    linarith
  · rw [integral_undef hint, mul_zero]
    have : 0 ≤ κ / 2 * |(1 / 2) * Real.log (volume K).toReal| :=
      mul_nonneg (by linarith) (abs_nonneg _)
    linarith

end Entropy

/-! ### Admissible competitors: existence and the two `regMin` tools -/

section Competitors

variable {Ψ : Euc d → ℝ} {κ : ℝ} {K : Set (Euc d)}

/-- The `L²` norm of a test function is positive. -/
theorem integrable_sq_testFn {T : Euc d → ℝ} (hT : IsTestFn K T) :
    Integrable fun x => T x ^ 2 := by
  have hTs2 : HasCompactSupport fun x => T x ^ 2 := by
    have h := hT.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    simpa [Function.comp_def] using h
  exact (hT.contDiff.continuous.pow 2).integrable_of_hasCompactSupport hTs2

/-- The `L²` norm of a test function is positive. -/
theorem integral_sq_testFn_pos {T : Euc d → ℝ} (hT : IsTestFn K T) : 0 < ∫ y, T y ^ 2 := by
  have hTc : Continuous T := hT.contDiff.continuous
  refine (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) (integrable_sq_testFn hT)).2 ?_
  have hne : ∃ x, T x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hT.ne_zero (funext fun x => hcon x)
  obtain ⟨x₀, hx₀⟩ := hne
  have hsub : Function.support (fun x => T x ^ 2) = Function.support T := by
    ext x; simp [Function.mem_support]
  rw [hsub]
  exact (hTc.isOpen_support).measure_pos volume ⟨x₀, hx₀⟩

/-- A positive multiple of a nonnegative test function, normalized in `L²`, is an admissible
competitor. -/
theorem isRegAdmissible_smul_testFn {T : Euc d → ℝ} (hT : IsTestFn K T) (hTnn : ∀ x, 0 ≤ T x)
    {c : ℝ} (hcpos : 0 < c) (hcsq : c ^ 2 * ∫ y, T y ^ 2 = 1) :
    IsRegAdmissible 2 K (c • T) := by
  refine
    { memW0 := (hT.memW0 2).smul c
      nonneg := fun x => mul_nonneg hcpos.le (hTnn x)
      eq_zero_of_notMem := fun x hx => ?_
      integral_rpow := ?_ }
  · have : T x = 0 := by
      by_contra hTx
      exact hx (hT.supp_subset (subset_tsupport T (Function.mem_support.2 hTx)))
    simp [this]
  · have hpt : ∀ x : Euc d, (c • T) x ^ (2 : ℝ) = c ^ 2 * T x ^ 2 := by
      intro x
      rw [rpow_two_eq_sq]
      simp [mul_pow]
    simp only [hpt]
    rw [integral_const_mul, hcsq]

/-- Every nonnegative test function has a positive multiple that is admissible. -/
theorem exists_isRegAdmissible_smul_testFn {T : Euc d → ℝ} (hT : IsTestFn K T)
    (hTnn : ∀ x, 0 ≤ T x) :
    ∃ c : ℝ, 0 < c ∧ c ^ 2 * (∫ y, T y ^ 2) = 1 ∧ IsRegAdmissible 2 K (c • T) := by
  have hTpos : 0 < ∫ y, T y ^ 2 := integral_sq_testFn_pos hT
  refine ⟨(∫ y, T y ^ 2) ^ (-(1 : ℝ) / 2), Real.rpow_pos_of_pos hTpos _, ?_, ?_⟩
  · have hsq : ((∫ y, T y ^ 2) ^ (-(1 : ℝ) / 2)) ^ 2 = (∫ y, T y ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hTpos.le]
      norm_num
      rw [Real.rpow_neg_one]
    rw [hsq, inv_mul_cancel₀ hTpos.ne']
  · refine isRegAdmissible_smul_testFn hT hTnn (Real.rpow_pos_of_pos hTpos _) ?_
    have hsq : ((∫ y, T y ^ 2) ^ (-(1 : ℝ) / 2)) ^ 2 = (∫ y, T y ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hTpos.le]
      norm_num
      rw [Real.rpow_neg_one]
    rw [hsq, inv_mul_cancel₀ hTpos.ne']

/-- **The competitor energies are bounded below.** -/
theorem bddBelow_regEnergy (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K) :
    BddBelow (Set.range fun w : {w : Euc d → ℝ // IsRegAdmissible 2 K w} =>
      regEnergy 2 κ Ψ w.1) := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  refine ⟨Ψ 0 + -(κ / 2) * |(1 / 2) * Real.log (volume K).toReal|, ?_⟩
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  exact add_le_add (le_integral_kinetic h hw) (entropy_integral_ge hκ hK hw)

/-- **Upper tool**: an admissible competitor bounds `regMin` from above. -/
theorem regMin_le_of_isRegAdmissible (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K)
    {w : Euc d → ℝ} (hw : IsRegAdmissible 2 K w) :
    regMin 2 κ Ψ K ≤ regEnergy 2 κ Ψ w :=
  ciInf_le (bddBelow_regEnergy hκ hΨ hK) (⟨w, hw⟩ : {w : Euc d → ℝ // IsRegAdmissible 2 K w})

/-- **Lower tool**: a bound valid for every admissible competitor bounds `regMin` from below. -/
theorem le_regMin_of_forall (hK : IsGoodConvex K) {b : ℝ}
    (h : ∀ w : Euc d → ℝ, IsRegAdmissible 2 K w → b ≤ regEnergy 2 κ Ψ w) :
    b ≤ regMin 2 κ Ψ K := by
  have := nonempty_isRegAdmissible hK
  exact le_ciInf fun w => h w.1 w.2

end Competitors

end Komlos.Literature.Regularized
