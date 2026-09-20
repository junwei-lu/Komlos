import Komlos.Literature.Regularized.PositivityLowerLevel

/-!
# Lane `L2p` (`reg/pos-lower`), step 4c: the logarithmic profile

The master logarithmic Caccioppoli inequality
(`IsRegMinimizer.log_caccioppoli_master`) holds for every profile `Φ` that vanishes with its
derivative on `[0,a]`; its only term of uncontrolled sign is `∫ η² (v H'(v)) ⟪∇Ψ(q),q⟫` with
`H(t) = t Φ(t)`.  This file builds the profile that makes that term harmless:

`H_a(t) = smoothStep((log t − log a)/L)`,  `L = ½ log(1/a)`,  `Φ_a = H_a / t`,

where `smoothStep` is the cubic step `3x² − 2x³` clamped to `[0,1]`.  Two properties matter:

* `t H_a'(t) = smoothStep'((log t − log a)/L)/L` — the switch is *logarithmic*, so this is
  `O(1/L)`, i.e. as small as we please;
* `smoothStep x ≥ x²` and `smoothStep' x ≤ 6x` on `[0,1]`, so the absorption condition
  `C t H_a' ≤ (c/2) H_a` holds as soon as `log(t/a) ≥ 12C/c` — a threshold of **bounded
  logarithmic width, independent of `L`**.  (An exponentially flat switch such as
  `Real.smoothTransition` fails here: its "small" region has logarithmic width `∼ L/log L`.)

`smoothStep` is only `C¹`, which is all `memW0_comp_sub_of_hasDerivAt` needs.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

/-! ### The cubic smooth step -/

/-- The clamped cubic step `3x² - 2x³`: `0` on `(-∞,0]`, `1` on `[1,∞)`, `C¹` everywhere. -/
noncomputable def smoothStep (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else 3 * x ^ 2 - 2 * x ^ 3

/-- The derivative of `smoothStep`. -/
noncomputable def smoothStepDeriv (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 0 else 6 * x - 6 * x ^ 2

theorem smoothStep_of_nonpos {x : ℝ} (hx : x ≤ 0) : smoothStep x = 0 := by
  rw [smoothStep, if_pos hx]

theorem smoothStepDeriv_of_nonpos {x : ℝ} (hx : x ≤ 0) : smoothStepDeriv x = 0 := by
  rw [smoothStepDeriv, if_pos hx]

theorem smoothStep_of_one_le {x : ℝ} (hx : 1 ≤ x) : smoothStep x = 1 := by
  rw [smoothStep, if_neg (by linarith), if_pos hx]

theorem smoothStepDeriv_of_one_le {x : ℝ} (hx : 1 ≤ x) : smoothStepDeriv x = 0 := by
  rw [smoothStepDeriv, if_neg (by linarith), if_pos hx]

theorem smoothStep_of_mem {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    smoothStep x = 3 * x ^ 2 - 2 * x ^ 3 := by
  rw [smoothStep, if_neg (by linarith), if_neg (by linarith)]

theorem smoothStepDeriv_of_mem {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    smoothStepDeriv x = 6 * x - 6 * x ^ 2 := by
  rw [smoothStepDeriv, if_neg (by linarith), if_neg (by linarith)]

theorem smoothStep_nonneg (x : ℝ) : 0 ≤ smoothStep x := by
  rcases le_or_gt x 0 with h | h
  · rw [smoothStep_of_nonpos h]
  rcases le_or_gt 1 x with h1 | h1
  · rw [smoothStep_of_one_le h1]; norm_num
  · rw [smoothStep_of_mem h h1]; nlinarith

theorem smoothStep_le_one (x : ℝ) : smoothStep x ≤ 1 := by
  rcases le_or_gt x 0 with h | h
  · rw [smoothStep_of_nonpos h]; norm_num
  rcases le_or_gt 1 x with h1 | h1
  · rw [smoothStep_of_one_le h1]
  · rw [smoothStep_of_mem h h1]
    nlinarith [mul_nonneg (sq_nonneg (1 - x)) (by linarith : (0 : ℝ) ≤ 1 + 2 * x)]

theorem smoothStepDeriv_nonneg (x : ℝ) : 0 ≤ smoothStepDeriv x := by
  rcases le_or_gt x 0 with h | h
  · rw [smoothStepDeriv_of_nonpos h]
  rcases le_or_gt 1 x with h1 | h1
  · rw [smoothStepDeriv_of_one_le h1]
  · rw [smoothStepDeriv_of_mem h h1]; nlinarith

/-- `smoothStep' x ≤ 6 x₊`: the derivative is small near the switch-on point. -/
theorem smoothStepDeriv_le (x : ℝ) : smoothStepDeriv x ≤ 6 * max x 0 := by
  rcases le_or_gt x 0 with h | h
  · rw [smoothStepDeriv_of_nonpos h]
    have : (0 : ℝ) ≤ max x 0 := le_max_right _ _
    linarith
  rcases le_or_gt 1 x with h1 | h1
  · rw [smoothStepDeriv_of_one_le h1]
    have : (0 : ℝ) ≤ max x 0 := le_max_right _ _
    linarith
  · rw [smoothStepDeriv_of_mem h h1, max_eq_left h.le]
    nlinarith

/-- `x² ≤ smoothStep x` for `0 ≤ x ≤ 1`: the switch is *not* flat at the switch-on point. -/
theorem sq_le_smoothStep {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ 2 ≤ smoothStep x := by
  rcases h0.eq_or_lt with h | h
  · rw [← h, smoothStep_of_nonpos le_rfl]; norm_num
  rcases eq_or_lt_of_le h1 with h1' | h1'
  · rw [h1', smoothStep_of_one_le le_rfl]; norm_num
  · rw [smoothStep_of_mem h h1']; nlinarith

theorem hasDerivAt_smoothStep (x : ℝ) : HasDerivAt smoothStep (smoothStepDeriv x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- locally zero
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_ |>.congr_deriv
      (smoothStepDeriv_of_nonpos hx.le).symm
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact smoothStep_of_nonpos (le_of_lt hy)
  · -- the switch-on point
    subst hx
    rw [smoothStepDeriv_of_nonpos le_rfl]
    have hleft : HasDerivWithinAt smoothStep 0 (Iic (0 : ℝ)) 0 := by
      refine (hasDerivWithinAt_const (0 : ℝ) (Iic (0 : ℝ)) 0).congr ?_ ?_
      · intro y hy; exact smoothStep_of_nonpos hy
      · exact smoothStep_of_nonpos le_rfl
    have hcub : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2 * y ^ 3) 0 0 := by
      have h1 : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2 * y ^ 3)
          (3 * (2 * (0 : ℝ) ^ 1) - 2 * (3 * (0 : ℝ) ^ 2)) 0 :=
        ((hasDerivAt_pow 2 (0 : ℝ)).const_mul 3).sub ((hasDerivAt_pow 3 (0 : ℝ)).const_mul 2)
      refine h1.congr_deriv ?_
      norm_num
    have hright : HasDerivWithinAt smoothStep 0 (Ici (0 : ℝ)) 0 := by
      refine (hcub.hasDerivWithinAt (s := Ici (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds one_pos)] with
          y hy hy1
        rcases eq_or_lt_of_le (mem_Ici.1 hy) with h | h
        · rw [← h, smoothStep_of_nonpos le_rfl]; norm_num
        · exact smoothStep_of_mem h (mem_Iio.1 hy1)
      · rw [smoothStep_of_nonpos le_rfl]; norm_num
    have := hleft.union hright
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this
  · rcases lt_trichotomy x 1 with h1 | h1 | h1
    · -- interior of the switch
      rw [smoothStepDeriv_of_mem hx h1]
      have hcub : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2 * y ^ 3) (6 * x - 6 * x ^ 2) x := by
        have h1' : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2 * y ^ 3)
            (3 * (2 * x ^ 1) - 2 * (3 * x ^ 2)) x :=
          ((hasDerivAt_pow 2 x).const_mul 3).sub ((hasDerivAt_pow 3 x).const_mul 2)
        refine h1'.congr_deriv ?_
        ring
      refine hcub.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx h1] with y hy
      exact smoothStep_of_mem hy.1 hy.2
    · -- the switch-off point
      subst h1
      rw [smoothStepDeriv_of_one_le le_rfl]
      have hcub : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2 * y ^ 3) 0 1 := by
        have h1' : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2 * y ^ 3)
            (3 * (2 * (1 : ℝ) ^ 1) - 2 * (3 * (1 : ℝ) ^ 2)) 1 :=
          ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 3).sub ((hasDerivAt_pow 3 (1 : ℝ)).const_mul 2)
        refine h1'.congr_deriv ?_
        norm_num
      have hleft : HasDerivWithinAt smoothStep 0 (Iic (1 : ℝ)) 1 := by
        refine (hcub.hasDerivWithinAt (s := Iic (1 : ℝ))).congr_of_eventuallyEq ?_ ?_
        · filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with y hy hy0
          rcases eq_or_lt_of_le (mem_Iic.1 hy) with h | h
          · rw [h, smoothStep_of_one_le le_rfl]; norm_num
          · exact smoothStep_of_mem (mem_Ioi.1 hy0) h
        · rw [smoothStep_of_one_le le_rfl]; norm_num
      have hright : HasDerivWithinAt smoothStep 0 (Ici (1 : ℝ)) 1 := by
        refine (hasDerivWithinAt_const (1 : ℝ) (Ici (1 : ℝ)) 1).congr ?_ ?_
        · intro y hy; exact smoothStep_of_one_le hy
        · exact smoothStep_of_one_le le_rfl
      have := hleft.union hright
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this
    · -- locally one
      refine (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq ?_ |>.congr_deriv
        (smoothStepDeriv_of_one_le h1.le).symm
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact smoothStep_of_one_le (le_of_lt hy)

theorem continuous_smoothStepDeriv : Continuous smoothStepDeriv := by
  have hcont : ∀ x : ℝ, ContinuousAt smoothStepDeriv x := by
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact (smoothStepDeriv_of_nonpos (le_of_lt hy)).symm
    · subst hx
      rw [ContinuousAt, smoothStepDeriv_of_nonpos le_rfl]
      have hsq : Tendsto (fun y : ℝ => 6 * max y 0) (𝓝 0) (𝓝 0) := by
        have : Continuous fun y : ℝ => 6 * max y 0 := by fun_prop
        simpa using this.tendsto 0
      refine squeeze_zero' (Eventually.of_forall fun y => smoothStepDeriv_nonneg y)
        (Eventually.of_forall fun y => smoothStepDeriv_le y) hsq
    · rcases lt_trichotomy x 1 with h1 | h1 | h1
      · refine ContinuousAt.congr (f := fun y : ℝ => 6 * y - 6 * y ^ 2) (by fun_prop) ?_
        filter_upwards [Ioo_mem_nhds hx h1] with y hy
        exact (smoothStepDeriv_of_mem hy.1 hy.2).symm
      · subst h1
        rw [ContinuousAt, smoothStepDeriv_of_one_le le_rfl]
        have hcl : Tendsto (fun y : ℝ => 6 * y - 6 * y ^ 2) (𝓝 1) (𝓝 0) := by
          have : Continuous fun y : ℝ => 6 * y - 6 * y ^ 2 := by fun_prop
          simpa using this.tendsto 1
        have hsplit : ∀ y : ℝ, |smoothStepDeriv y| ≤ |6 * y - 6 * y ^ 2| := by
          intro y
          rcases le_or_gt y 0 with h | h
          · rw [smoothStepDeriv_of_nonpos h]; simp
          rcases le_or_gt 1 y with h1 | h1
          · rw [smoothStepDeriv_of_one_le h1]; simp
          · rw [smoothStepDeriv_of_mem h h1]
        refine squeeze_zero_norm (a := fun y : ℝ => |6 * y - 6 * y ^ 2|) (fun y => ?_) ?_
        · rw [Real.norm_eq_abs]
          exact hsplit y
        · have := hcl.abs
          simpa using this
      · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
        filter_upwards [Ioi_mem_nhds h1] with y hy
        exact (smoothStepDeriv_of_one_le (le_of_lt hy)).symm
  exact continuous_iff_continuousAt.2 hcont

/-! ### The logarithmic profile -/

/-- The logarithmic switch `H_a(t) = smoothStep((log t - log a)/L)`. -/
noncomputable def logSwitch (a L t : ℝ) : ℝ := smoothStep ((Real.log t - Real.log a) / L)

/-- The profile `Φ_a(t) = H_a(t)/t`, extended by `0` to `t ≤ 0`. -/
noncomputable def logProfile (a L t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else logSwitch a L t / t

/-- The derivative of `logProfile`. -/
noncomputable def logProfileDeriv (a L t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else
    (smoothStepDeriv ((Real.log t - Real.log a) / L) / (L * t) * t - logSwitch a L t) / t ^ 2

variable {a L : ℝ}

theorem logArg_nonpos (_ha : 0 < a) (hL : 0 < L) {t : ℝ} (ht0 : 0 < t) (hta : t ≤ a) :
    (Real.log t - Real.log a) / L ≤ 0 := by
  have hnum : Real.log t - Real.log a ≤ 0 := by
    have := Real.log_le_log ht0 hta
    linarith
  rw [div_le_iff₀ hL]
  linarith

theorem logSwitch_of_le (ha : 0 < a) (hL : 0 < L) {t : ℝ} (ht0 : 0 < t) (hta : t ≤ a) :
    logSwitch a L t = 0 :=
  smoothStep_of_nonpos (logArg_nonpos ha hL ht0 hta)

theorem logProfile_of_le (ha : 0 < a) (hL : 0 < L) {t : ℝ} (hta : t ≤ a) :
    logProfile a L t = 0 := by
  rcases le_or_gt t 0 with h | h
  · rw [logProfile, if_pos h]
  · rw [logProfile, if_neg (by linarith), logSwitch_of_le ha hL h hta, zero_div]

theorem logProfileDeriv_of_le (ha : 0 < a) (hL : 0 < L) {t : ℝ} (hta : t ≤ a) :
    logProfileDeriv a L t = 0 := by
  rcases le_or_gt t 0 with h | h
  · rw [logProfileDeriv, if_pos h]
  · rw [logProfileDeriv, if_neg (by linarith), logSwitch_of_le ha hL h hta,
      smoothStepDeriv_of_nonpos (logArg_nonpos ha hL h hta)]
    simp

theorem logProfile_nonneg (a L t : ℝ) : 0 ≤ logProfile a L t := by
  rcases le_or_gt t 0 with h | h
  · rw [logProfile, if_pos h]
  · rw [logProfile, if_neg (by linarith)]
    exact div_nonneg (smoothStep_nonneg _) h.le

theorem logSwitch_nonneg (a L t : ℝ) : 0 ≤ logSwitch a L t := smoothStep_nonneg _

theorem logSwitch_le_one (a L t : ℝ) : logSwitch a L t ≤ 1 := smoothStep_le_one _

theorem mul_logProfile (_ha : 0 < a) (_hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    t * logProfile a L t = logSwitch a L t := by
  rw [logProfile, if_neg (by linarith)]
  field_simp

theorem hasDerivAt_logProfile (ha : 0 < a) (hL : 0 < L) (t : ℝ) :
    HasDerivAt (logProfile a L) (logProfileDeriv a L t) t := by
  rcases lt_or_ge t a with hta | hta
  · -- `logProfile` vanishes on `(-∞, a)`
    have hzero : ∀ s : ℝ, s < a → logProfile a L s = 0 := fun s hs =>
      logProfile_of_le ha hL hs.le
    refine ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_).congr_deriv
      (logProfileDeriv_of_le ha hL hta.le).symm
    filter_upwards [Iio_mem_nhds hta] with s hs
    exact hzero s hs
  · -- `t ≥ a > 0`
    have ht0 : 0 < t := lt_of_lt_of_le ha hta
    have hlog : HasDerivAt (fun s : ℝ => (Real.log s - Real.log a) / L) (t⁻¹ / L) t :=
      (Real.hasDerivAt_log ht0.ne'|>.sub_const (Real.log a)).div_const L
    have hS : HasDerivAt (logSwitch a L)
        (smoothStepDeriv ((Real.log t - Real.log a) / L) * (t⁻¹ / L)) t := by
      have h := (hasDerivAt_smoothStep ((Real.log t - Real.log a) / L)).comp t hlog
      have hc : (smoothStep ∘ fun s : ℝ => (Real.log s - Real.log a) / L)
          = logSwitch a L := rfl
      rw [hc] at h
      exact h
    have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have hdiv := hS.div hid ht0.ne'
    have heq : ∀ᶠ s in 𝓝 t, logProfile a L s = logSwitch a L s / s := by
      filter_upwards [Ioi_mem_nhds ht0] with s hs
      rw [logProfile, if_neg (by linarith [mem_Ioi.1 hs])]
    refine (hdiv.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [logProfileDeriv, if_neg (by linarith)]
    field_simp
    try ring

/-- The key cancellation: `t Φ_a(t) + t² Φ_a'(t) = t H_a'(t) = smoothStep'(h)/L`. -/
theorem mul_logProfile_add_sq_mul_deriv (_ha : 0 < a) (_hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    t * logProfile a L t + t ^ 2 * logProfileDeriv a L t =
      smoothStepDeriv ((Real.log t - Real.log a) / L) / L := by
  rw [logProfile, logProfileDeriv, if_neg (by linarith), if_neg (by linarith)]
  field_simp
  ring

theorem continuousOn_logProfileDeriv (ha : 0 < a) (hL : 0 < L) (S : ℝ) :
    ContinuousOn (logProfileDeriv a L) (Icc 0 S) := by
  intro t ht
  rcases lt_or_ge t a with hta | hta
  · refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℝ))
      continuousWithinAt_const ?_ (logProfileDeriv_of_le ha hL hta.le)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hta)] with s hs
    exact logProfileDeriv_of_le ha hL (le_of_lt hs)
  · have ht0 : 0 < t := lt_of_lt_of_le ha hta
    refine ContinuousAt.continuousWithinAt ?_
    have hcont : ContinuousAt (fun s : ℝ =>
        (smoothStepDeriv ((Real.log s - Real.log a) / L) / (L * s) * s
          - logSwitch a L s) / s ^ 2) t := by
      have h1 : ContinuousAt (fun s : ℝ => (Real.log s - Real.log a) / L) t :=
        ((Real.continuousAt_log ht0.ne').sub continuousAt_const).div_const L
      have h2 : ContinuousAt (fun s : ℝ =>
          smoothStepDeriv ((Real.log s - Real.log a) / L)) t :=
        (continuous_smoothStepDeriv.continuousAt).comp h1
      have h3 : ContinuousAt (fun s : ℝ => logSwitch a L s) t := by
        have : Continuous smoothStep :=
          (Differentiable.continuous (fun x => (hasDerivAt_smoothStep x).differentiableAt))
        exact (this.continuousAt).comp h1
      have h4 : ContinuousAt (fun s : ℝ => L * s) t := by fun_prop
      refine ContinuousAt.div (ContinuousAt.sub (ContinuousAt.mul
        (ContinuousAt.div h2 h4 (by positivity)) continuousAt_id) h3) ?_ ?_
      · fun_prop
      · positivity
    refine hcont.congr ?_
    filter_upwards [Ioi_mem_nhds ht0] with s hs
    rw [logProfileDeriv, if_neg (by linarith [mem_Ioi.1 hs])]

/-! ### The smoothed level function -/

/-- `levelFun k ε z = ∫_k^z smoothStep((s−k)/ε)`: a `C¹` approximation of `(z − k)₊` from
below, with derivative `smoothStep((z−k)/ε) ∈ [0,1]` increasing to `1_{z>k}` as `ε ↓ 0`. -/
noncomputable def levelFun (k ε z : ℝ) : ℝ := ∫ s in k..z, smoothStep ((s - k) / ε)

theorem continuous_smoothStep : Continuous smoothStep :=
  Differentiable.continuous fun x => (hasDerivAt_smoothStep x).differentiableAt

theorem hasDerivAt_levelFun (k ε z : ℝ) :
    HasDerivAt (levelFun k ε) (smoothStep ((z - k) / ε)) z := by
  have hc : Continuous fun s : ℝ => smoothStep ((s - k) / ε) := by
    exact continuous_smoothStep.comp (by fun_prop)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem levelFun_of_le {k ε z : ℝ} (hε : 0 < ε) (hz : z ≤ k) : levelFun k ε z = 0 := by
  rw [levelFun, intervalIntegral.integral_of_ge hz]
  have hzero : ∀ s ∈ Set.Ioc z k, smoothStep ((s - k) / ε) = 0 := by
    intro s hs
    refine smoothStep_of_nonpos ?_
    rw [div_le_iff₀ hε]
    linarith [hs.2]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hzero]
  simp

theorem levelFun_nonneg {k ε z : ℝ} (hε : 0 < ε) : 0 ≤ levelFun k ε z := by
  rcases le_or_gt z k with hz | hz
  · rw [levelFun_of_le hε hz]
  · rw [levelFun, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      fun s _ => smoothStep_nonneg _

/-- `levelFun k ε z ≤ (z − k)₊`. -/
theorem levelFun_le {k ε z : ℝ} (hε : 0 < ε) : levelFun k ε z ≤ max (z - k) 0 := by
  rcases le_or_gt z k with hz | hz
  · rw [levelFun_of_le hε hz]
    exact le_max_right _ _
  · rw [levelFun, intervalIntegral.integral_of_le hz.le, max_eq_left (by linarith)]
    have hbound : (∫ s in Set.Ioc k z, smoothStep ((s - k) / ε)) ≤
        ∫ _s in Set.Ioc k z, (1 : ℝ) := by
      refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc
        fun s _ => smoothStep_le_one _
      · exact (continuous_smoothStep.comp (by fun_prop)).integrableOn_Ioc
      · exact MeasureTheory.integrableOn_const
          (measure_Ioc_lt_top (μ := MeasureTheory.volume)).ne
    have hone : (∫ _s in Set.Ioc k z, (1 : ℝ)) = z - k := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.Measure.real,
        Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ z - k)]
    linarith [hbound, hone.le, hone.ge]

/-- The Young-inequality ratio: `(levelFun)² ≤ (z − k)₊² · smoothStep((z−k)/ε)`. -/
theorem levelFun_sq_le {k ε z : ℝ} (hε : 0 < ε) :
    levelFun k ε z ^ 2 ≤ max (z - k) 0 ^ 2 * smoothStep ((z - k) / ε) := by
  rcases le_or_gt z k with hz | hz
  · rw [levelFun_of_le hε hz]
    have : (0 : ℝ) ≤ max (z - k) 0 ^ 2 * smoothStep ((z - k) / ε) :=
      mul_nonneg (sq_nonneg _) (smoothStep_nonneg _)
    simpa using this
  · have hmono : ∀ s ∈ Set.Ioc k z, smoothStep ((s - k) / ε) ≤ smoothStep ((z - k) / ε) := by
      intro s hs
      have hsz : (s - k) / ε ≤ (z - k) / ε := by
        rw [div_le_iff₀ hε]
        have hrw : (z - k) / ε * ε = z - k := by field_simp
        rw [hrw]
        linarith [hs.2]
      -- `smoothStep` is monotone
      have hmonof : Monotone smoothStep := by
        refine monotone_of_deriv_nonneg (fun x => (hasDerivAt_smoothStep x).differentiableAt)
          fun x => ?_
        rw [(hasDerivAt_smoothStep x).deriv]
        exact smoothStepDeriv_nonneg x
      exact hmonof hsz
    have hle : levelFun k ε z ≤ (z - k) * smoothStep ((z - k) / ε) := by
      rw [levelFun, intervalIntegral.integral_of_le hz.le]
      have hbound : (∫ s in Set.Ioc k z, smoothStep ((s - k) / ε)) ≤
          ∫ _s in Set.Ioc k z, smoothStep ((z - k) / ε) := by
        refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc hmono
        · exact (continuous_smoothStep.comp (by fun_prop)).integrableOn_Ioc
        · exact MeasureTheory.integrableOn_const
            (measure_Ioc_lt_top (μ := MeasureTheory.volume)).ne
      have hone : (∫ _s in Set.Ioc k z, smoothStep ((z - k) / ε))
          = (z - k) * smoothStep ((z - k) / ε) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real,
          Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ z - k)]
      linarith [hbound, hone.le, hone.ge]
    have h0 : 0 ≤ levelFun k ε z := levelFun_nonneg hε
    have hs1 : smoothStep ((z - k) / ε) ≤ 1 := smoothStep_le_one _
    have hs0 : 0 ≤ smoothStep ((z - k) / ε) := smoothStep_nonneg _
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ z - k)]
    have hsq := mul_self_le_mul_self h0 hle
    have hσ2 : smoothStep ((z - k) / ε) ^ 2 ≤ smoothStep ((z - k) / ε) := by nlinarith
    nlinarith [hsq, hσ2, sq_nonneg (z - k)]

/-! ### The level-set logarithmic profile -/

/-- `Φ(t) = f(log δ − log(t+δ)) · H_a(t)/t`: the logarithmic profile weighted by a
nondecreasing function of the *shifted* logarithm `Z_δ(t) = log δ − log(t+δ)`.  Weighting by
`Z_δ` rather than by `−log t` is what makes the resulting Caccioppoli estimate a `DG⁺` energy
inequality **for `Z_δ`**: the good term acquires the factor `t/(t+δ)`, which converts
`‖∇v‖²/v²` into `‖∇Z_δ‖²` exactly. -/
noncomputable def shiftLogProfile (f : ℝ → ℝ) (δ a L t : ℝ) : ℝ :=
  f (Real.log δ - Real.log (t + δ)) * logProfile a L t

/-- The derivative of `shiftLogProfile`. -/
noncomputable def shiftLogProfileDeriv (f fd : ℝ → ℝ) (δ a L t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else
    fd (Real.log δ - Real.log (t + δ)) * (-(t + δ)⁻¹) * logProfile a L t
      + f (Real.log δ - Real.log (t + δ)) * logProfileDeriv a L t

variable {f fd δ : ℝ}

theorem shiftLogProfile_of_le {f : ℝ → ℝ} (ha : 0 < a) (hL : 0 < L) {t : ℝ} (hta : t ≤ a) :
    shiftLogProfile f δ a L t = 0 := by
  rw [shiftLogProfile, logProfile_of_le ha hL hta, mul_zero]

theorem shiftLogProfileDeriv_of_le {f fd : ℝ → ℝ} (ha : 0 < a) (hL : 0 < L) {t : ℝ}
    (hta : t ≤ a) : shiftLogProfileDeriv f fd δ a L t = 0 := by
  rcases le_or_gt t 0 with h | h
  · rw [shiftLogProfileDeriv, if_pos h]
  · rw [shiftLogProfileDeriv, if_neg (by linarith), logProfile_of_le ha hL hta,
      logProfileDeriv_of_le ha hL hta]
    ring

theorem shiftLogProfile_nonneg {f : ℝ → ℝ} (hf : ∀ z, 0 ≤ f z) (δ a L t : ℝ) :
    0 ≤ shiftLogProfile f δ a L t :=
  mul_nonneg (hf _) (logProfile_nonneg a L t)

theorem mul_shiftLogProfile {f : ℝ → ℝ} (ha : 0 < a) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    t * shiftLogProfile f δ a L t
      = f (Real.log δ - Real.log (t + δ)) * logSwitch a L t := by
  rw [shiftLogProfile, ← mul_logProfile ha hL ht]
  ring

theorem hasDerivAt_shiftLogProfile {f fd : ℝ → ℝ} (hfd : ∀ z, HasDerivAt f (fd z) z)
    (hδ : 0 < δ) (ha : 0 < a) (hL : 0 < L) (t : ℝ) :
    HasDerivAt (shiftLogProfile f δ a L) (shiftLogProfileDeriv f fd δ a L t) t := by
  rcases lt_or_ge t a with hta | hta
  · refine ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_).congr_deriv
      (shiftLogProfileDeriv_of_le (f := f) (fd := fd) (δ := δ) ha hL hta.le).symm
    filter_upwards [Iio_mem_nhds hta] with s hs
    exact shiftLogProfile_of_le ha hL (le_of_lt hs)
  · have ht0 : 0 < t := lt_of_lt_of_le ha hta
    have htδ : (0 : ℝ) < t + δ := by linarith
    have hlog : HasDerivAt (fun s : ℝ => Real.log δ - Real.log (s + δ)) (-(t + δ)⁻¹) t := by
      have h1 : HasDerivAt (fun s : ℝ => s + δ) 1 t := (hasDerivAt_id t).add_const δ
      have h2 := h1.log htδ.ne'
      have h3 := h2.const_sub (Real.log δ)
      refine h3.congr_deriv ?_
      rw [one_div]
    have hg : HasDerivAt (fun s : ℝ => f (Real.log δ - Real.log (s + δ)))
        (fd (Real.log δ - Real.log (t + δ)) * (-(t + δ)⁻¹)) t := by
      have h := (hfd (Real.log δ - Real.log (t + δ))).comp t hlog
      have hc : (f ∘ fun s : ℝ => Real.log δ - Real.log (s + δ))
          = fun s : ℝ => f (Real.log δ - Real.log (s + δ)) := rfl
      rw [hc] at h
      exact h
    have hP := hasDerivAt_logProfile ha hL t
    have hmul := hg.mul hP
    refine hmul.congr_deriv ?_
    rw [shiftLogProfileDeriv, if_neg (by linarith)]
    try ring

/-- The key cancellation for the shifted level profile:
`t Φ + t² Φ' = f(Z_δ) · smoothStep'(h)/L − f'(Z_δ) · (t/(t+δ)) · H_a(t)`. -/
theorem mul_shiftLogProfile_add_sq_mul_deriv {f fd : ℝ → ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    t * shiftLogProfile f δ a L t + t ^ 2 * shiftLogProfileDeriv f fd δ a L t =
      f (Real.log δ - Real.log (t + δ)) *
          (smoothStepDeriv ((Real.log t - Real.log a) / L) / L)
        - fd (Real.log δ - Real.log (t + δ)) * (t / (t + δ)) * logSwitch a L t := by
  have htδ : (0 : ℝ) < t + δ := by linarith
  have hkey := mul_logProfile_add_sq_mul_deriv (a := a) (L := L) ha hL ht
  have hmul := mul_logProfile (a := a) (L := L) ha hL ht
  rw [shiftLogProfile, shiftLogProfileDeriv, if_neg (by linarith)]
  have hexp : t * (f (Real.log δ - Real.log (t + δ)) * logProfile a L t) +
      t ^ 2 * (fd (Real.log δ - Real.log (t + δ)) * (-(t + δ)⁻¹) * logProfile a L t
        + f (Real.log δ - Real.log (t + δ)) * logProfileDeriv a L t)
      = f (Real.log δ - Real.log (t + δ)) *
          (t * logProfile a L t + t ^ 2 * logProfileDeriv a L t)
        - fd (Real.log δ - Real.log (t + δ)) * (t / (t + δ)) * (t * logProfile a L t) := by
    field_simp
    ring
  rw [hexp, hkey, hmul]

theorem continuousOn_shiftLogProfileDeriv {f fd : ℝ → ℝ} (hfd : ∀ z, HasDerivAt f (fd z) z)
    (hfdc : Continuous fd) (hδ : 0 < δ) (ha : 0 < a) (hL : 0 < L) (S : ℝ) :
    ContinuousOn (shiftLogProfileDeriv f fd δ a L) (Icc 0 S) := by
  intro t ht
  rcases lt_or_ge t a with hta | hta
  · refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℝ))
      continuousWithinAt_const ?_
      (shiftLogProfileDeriv_of_le (f := f) (fd := fd) (δ := δ) ha hL hta.le)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hta)] with s hs
    exact shiftLogProfileDeriv_of_le ha hL (le_of_lt hs)
  · have ht0 : 0 < t := lt_of_lt_of_le ha hta
    have htδ : (0 : ℝ) < t + δ := by linarith
    refine ContinuousAt.continuousWithinAt ?_
    have hfc : Continuous f := Differentiable.continuous fun z => (hfd z).differentiableAt
    have hlogc : ContinuousAt (fun s : ℝ => Real.log δ - Real.log (s + δ)) t := by
      refine ContinuousAt.sub continuousAt_const ?_
      have hadd : ContinuousAt (fun s : ℝ => s + δ) t := by fun_prop
      exact hadd.log htδ.ne'
    have hPc : ContinuousAt (logProfile a L) t :=
      (hasDerivAt_logProfile ha hL t).continuousAt
    have hPdc : ContinuousAt (logProfileDeriv a L) t := by
      have hcon := continuousOn_logProfileDeriv ha hL (t + 1)
      refine ContinuousOn.continuousAt (s := Ioo (0 : ℝ) (t + 1)) ?_
        (Ioo_mem_nhds ht0 (by linarith))
      exact hcon.mono fun s hs => ⟨hs.1.le, hs.2.le⟩
    have hmain : ContinuousAt (fun s : ℝ =>
        fd (Real.log δ - Real.log (s + δ)) * (-(s + δ)⁻¹) * logProfile a L s
          + f (Real.log δ - Real.log (s + δ)) * logProfileDeriv a L s) t := by
      refine ContinuousAt.add (ContinuousAt.mul (ContinuousAt.mul
        (hfdc.continuousAt.comp hlogc) ?_) hPc) ((hfc.continuousAt.comp hlogc).mul hPdc)
      refine ContinuousAt.neg (ContinuousAt.inv₀ (by fun_prop) htδ.ne')
    refine hmain.congr ?_
    filter_upwards [Ioi_mem_nhds ht0] with s hs
    rw [shiftLogProfileDeriv, if_neg (by linarith [mem_Ioi.1 hs])]

end Komlos.Literature.Regularized
