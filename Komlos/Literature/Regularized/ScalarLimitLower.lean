import Komlos.Literature.Regularized.ScalarLimitGtTwo

/-!
# The lower scalar limit: `λ_{p,F}(K)/p - δ ≤ regMin 2 κ Ψ K`

`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*, lower half.  Unlike the upper half this
has to hold for **every** admissible competitor `w`, so the substitution `u = w^{2/p}` must be
performed in the Sobolev class, not on smooth functions.

## The truncated power `lowPow`

For `1 < p ≤ 2` put `β = 1/p ∈ [1/2, 1)`, so that `2β = 2/p` is the substitution exponent.
The chain rule `Komlos.Literature.memW0_comp` requires a `C¹` function with a *bounded*
derivative vanishing at `0`, which `t ↦ t^{2β}` is not (its derivative is unbounded).  We
therefore use the two-parameter family

`lowPow β τ j t = ∫_0^t 2β · min(s⁺, j) · (min(s⁺,j)² + τ)^{β-1} ds`,

the primitive of an explicit bounded continuous nonnegative derivative.  It coincides with
`powShift β τ` on `[0, j]`, is bounded by `t^{2β}`, vanishes to first order at `0`, and
converges to `t^{2β}` as `τ ↓ 0`, `j ↑ ∞`.

## The two inequalities

* `rpow_mul_le_homogeneousDensity`: pointwise, `(lowPow')^p F(ξ)^p ≤ p · D(t, ξ)` for the
  kinetic density `D` of `regProfile p F R ρ` — because `Ψ_p ≥ F^p/p` for `p ≤ 2`
  (`rpow_div_le_regProfile`) and `lowPow' t ≤ 2β t^{2β-1}`.
* `lambdaSob_mul_le` applied to `u = lowPow β τ j ∘ w ∈ W₀^{1,p}(K)` gives
  `λ ∫ u^p ≤ ∫ F(∇u)^p = ∫ (lowPow'(w))^p F(∇w)^p ≤ p ∫ D`, and `∫ u^p → ∫ w² = 1`.

## Main results

* `lowPow` and its calculus;
* `le_integral_kinetic_regProfile`: `λ_{p,F}(K)/p ≤ ∫ D(w, ∇w)` for `p ≤ 2` and every
  admissible `w`;
* `le_regMin_of_le_two`, and the `p > 2` case `le_regMin_of_gt_two` (proved in
  `Komlos/Literature/Regularized/ScalarLimitGtTwo.lean`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Two elementary inequalities -/

/-- The elementary substitute for Young's inequality: `s^{2-p} t^p ≤ s² + t²`. -/
theorem rpow_mul_rpow_le_sq {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) : s ^ (2 - p) * t ^ p ≤ s ^ 2 + t ^ 2 := by
  have hp0 : (0 : ℝ) < p := by linarith
  have h2p : (0 : ℝ) ≤ 2 - p := by linarith
  rcases le_total s t with hst | hst
  · have h1 : s ^ (2 - p) ≤ t ^ (2 - p) := Real.rpow_le_rpow hs hst h2p
    have h2 : t ^ (2 - p) * t ^ p = t ^ 2 := by
      rw [← Real.rpow_add' ht (by norm_num), show (2 : ℝ) - p + p = 2 by ring, rpow_two_eq_sq]
    have h3 : s ^ (2 - p) * t ^ p ≤ t ^ (2 - p) * t ^ p :=
      mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht _)
    nlinarith [sq_nonneg s, h2, h3]
  · have h1 : t ^ p ≤ s ^ p := Real.rpow_le_rpow ht hst hp0.le
    have h2 : s ^ (2 - p) * s ^ p = s ^ 2 := by
      rw [← Real.rpow_add' hs (by norm_num), show (2 : ℝ) - p + p = 2 by ring, rpow_two_eq_sq]
    have h3 : s ^ (2 - p) * t ^ p ≤ s ^ (2 - p) * s ^ p :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs _)
    nlinarith [sq_nonneg t, h2, h3]

/-- `L^q` membership from integrability of `|f|^q`. -/
theorem memLp_ofReal_of_integrable_rpow {q : ℝ} (hq : 0 < q) {f : Euc d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hint : Integrable fun x => |f x| ^ q) :
    MemLp f (ENNReal.ofReal q) volume := by
  refine (integrable_norm_rpow_iff hf
    (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq) ENNReal.ofReal_ne_top).1 ?_
  rw [ENNReal.toReal_ofReal hq.le]
  simpa only [Real.norm_eq_abs] using hint

/-! ### The truncated power of the lower limit -/

/-- The derivative of the truncated power of the lower scalar limit. -/
noncomputable def lowDeriv (β τ j t : ℝ) : ℝ :=
  2 * β * min (max t 0) j * (min (max t 0) j ^ 2 + τ) ^ (β - 1)

/-- The truncated power of the lower scalar limit: the primitive of `lowDeriv`. -/
noncomputable def lowPow (β τ j t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, lowDeriv β τ j s

section LowPow

variable {β τ j : ℝ}

theorem lowDeriv_nonneg (hβ : 0 ≤ β) (hτ : 0 < τ) (hj : 0 ≤ j) (t : ℝ) :
    0 ≤ lowDeriv β τ j t := by
  have h1 : 0 ≤ min (max t 0) j := le_min (le_max_right _ _) hj
  have h2 : (0 : ℝ) < min (max t 0) j ^ 2 + τ := by positivity
  exact mul_nonneg (mul_nonneg (by linarith) h1) (Real.rpow_nonneg h2.le _)

theorem lowDeriv_zero_arg (hj : 0 ≤ j) : lowDeriv β τ j 0 = 0 := by
  simp [lowDeriv, min_eq_left hj]

theorem continuous_lowDeriv (hτ : 0 < τ) : Continuous (lowDeriv β τ j) := by
  have hbase : Continuous fun t : ℝ => min (max t 0) j ^ 2 + τ :=
    (((continuous_id.max continuous_const).min continuous_const).pow 2).add continuous_const
  have hpos : ∀ t : ℝ, (0 : ℝ) < min (max t 0) j ^ 2 + τ := fun t => by positivity
  have hrpow : Continuous fun t : ℝ => (min (max t 0) j ^ 2 + τ) ^ (β - 1) :=
    hbase.rpow_const fun t => Or.inl (hpos t).ne'
  exact ((continuous_const.mul ((continuous_id.max continuous_const).min
    continuous_const)).mul hrpow)

/-- `lowDeriv` is bounded (this is what makes the Sobolev chain rule applicable). -/
theorem lowDeriv_le_const (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hτ : 0 < τ) (hj : 0 ≤ j) (t : ℝ) :
    lowDeriv β τ j t ≤ 2 * β * j * τ ^ (β - 1) := by
  have h1 : 0 ≤ min (max t 0) j := le_min (le_max_right _ _) hj
  have h2 : min (max t 0) j ≤ j := min_le_right _ _
  have hτle : (min (max t 0) j ^ 2 + τ) ^ (β - 1) ≤ τ ^ (β - 1) :=
    Real.rpow_le_rpow_of_nonpos hτ (by nlinarith [sq_nonneg (min (max t 0) j)]) (by linarith)
  have hτ0 : (0 : ℝ) < (min (max t 0) j ^ 2 + τ) ^ (β - 1) := by
    refine Real.rpow_pos_of_pos ?_ _
    positivity
  calc lowDeriv β τ j t = 2 * β * min (max t 0) j * (min (max t 0) j ^ 2 + τ) ^ (β - 1) := rfl
    _ ≤ 2 * β * j * (min (max t 0) j ^ 2 + τ) ^ (β - 1) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) hτ0.le
    _ ≤ 2 * β * j * τ ^ (β - 1) := mul_le_mul_of_nonneg_left hτle (by positivity)

/-- The pointwise bound by the derivative of the untruncated power. -/
theorem lowDeriv_le_rpow (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hτ : 0 < τ) (hj : 0 ≤ j) {t : ℝ}
    (ht : 0 ≤ t) : lowDeriv β τ j t ≤ 2 * β * t ^ (2 * β - 1) := by
  have hβ0 : 0 < β := by linarith
  set s : ℝ := min (max t 0) j with hs
  have hs0 : 0 ≤ s := le_min (le_max_right _ _) hj
  have hst : s ≤ t := by rw [hs, max_eq_left ht]; exact min_le_left _ _
  rcases hs0.eq_or_lt with hs0' | hspos
  · rw [lowDeriv, ← hs, ← hs0', ]
    simp only [zero_mul, mul_zero]
    positivity
  · have hsq : (0 : ℝ) < s ^ 2 := by positivity
    have h1 : (s ^ 2 + τ) ^ (β - 1) ≤ (s ^ 2) ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hsq (by linarith) (by linarith)
    have h2 : (s ^ 2) ^ (β - 1) = s ^ (2 * β - 2) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs0]
      congr 1
      push_cast
      ring
    have h3 : s * s ^ (2 * β - 2) = s ^ (2 * β - 1) := by
      rw [show (2 * β - 1 : ℝ) = 1 + (2 * β - 2) by ring, Real.rpow_add hspos, Real.rpow_one]
    have h4 : s ^ (2 * β - 1) ≤ t ^ (2 * β - 1) :=
      Real.rpow_le_rpow hs0 hst (by linarith)
    calc lowDeriv β τ j t = 2 * β * (s * (s ^ 2 + τ) ^ (β - 1)) := by rw [lowDeriv, ← hs]; ring
      _ ≤ 2 * β * (s * s ^ (2 * β - 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hs0) (by positivity)
          rw [← h2]; exact h1
      _ = 2 * β * s ^ (2 * β - 1) := by rw [h3]
      _ ≤ 2 * β * t ^ (2 * β - 1) := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem intervalIntegrable_lowDeriv (hτ : 0 < τ) (a b : ℝ) :
    IntervalIntegrable (lowDeriv β τ j) volume a b :=
  (continuous_lowDeriv hτ).intervalIntegrable a b

theorem hasDerivAt_lowPow (hτ : 0 < τ) (t : ℝ) :
    HasDerivAt (lowPow β τ j) (lowDeriv β τ j t) t := by
  have hc := continuous_lowDeriv (β := β) (τ := τ) (j := j) hτ
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_lowDeriv hτ 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem differentiable_lowPow (hτ : 0 < τ) : Differentiable ℝ (lowPow β τ j) :=
  fun t => (hasDerivAt_lowPow hτ t).differentiableAt

theorem deriv_lowPow (hτ : 0 < τ) : deriv (lowPow β τ j) = lowDeriv β τ j :=
  funext fun t => (hasDerivAt_lowPow hτ t).deriv

theorem contDiff_lowPow (hτ : 0 < τ) : ContDiff ℝ 1 (lowPow β τ j) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨differentiable_lowPow hτ, by rw [deriv_lowPow hτ]; exact continuous_lowDeriv hτ⟩

@[simp] theorem lowPow_zero_arg : lowPow β τ j 0 = 0 := by simp [lowPow]

theorem lowPow_nonneg (hβ : 0 ≤ β) (hτ : 0 < τ) (hj : 0 ≤ j) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ lowPow β τ j t := by
  have : MonotoneOn (lowPow β τ j) univ := by
    refine monotoneOn_of_deriv_nonneg convex_univ (differentiable_lowPow hτ).continuous.continuousOn
      (differentiable_lowPow hτ).differentiableOn fun x _ => ?_
    rw [deriv_lowPow hτ]
    exact lowDeriv_nonneg hβ hτ hj x
  simpa using this (mem_univ 0) (mem_univ t) ht

/-- `lowPow β τ j t ≤ t^{2β}`. -/
theorem lowPow_le_rpow (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hτ : 0 < τ) (hj : 0 ≤ j) {t : ℝ}
    (ht : 0 ≤ t) : lowPow β τ j t ≤ t ^ (2 * β) := by
  have hβ0 : 0 < β := by linarith
  have hcalc : (∫ s in (0 : ℝ)..t, 2 * β * s ^ (2 * β - 1)) = t ^ (2 * β) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * β - 1))]
    rw [show 2 * β - 1 + 1 = 2 * β by ring, Real.zero_rpow (by positivity), sub_zero]
    field_simp
  rw [lowPow, ← hcalc]
  refine intervalIntegral.integral_mono_on ht (intervalIntegrable_lowDeriv hτ 0 t) ?_ ?_
  · refine Continuous.intervalIntegrable ?_ 0 t
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun x => ?_)
    exact Real.continuousAt_rpow_const x (2 * β - 1) (Or.inr (by linarith))
  · intro x hx
    exact lowDeriv_le_rpow hβ hβ1 hτ hj hx.1

/-- On `[0, j]` the truncated power is the shifted power `powShift β τ`. -/
theorem lowPow_eq_powShift (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) (htj : t ≤ j) :
    lowPow β τ j t = powShift β τ t := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (powShift β τ) (lowDeriv β τ j s) s := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    have he : lowDeriv β τ j s = 2 * β * s * (s ^ 2 + τ) ^ (β - 1) := by
      rw [lowDeriv, max_eq_left hs.1, min_eq_left (hs.2.trans htj)]
    rw [he]
    exact hasDerivAt_powShift hτ β s
  rw [lowPow, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_lowDeriv hτ 0 t)]
  simp [powShift]

end LowPow

/-! ### The Sobolev chain rule for the truncated power -/

section ChainRule

variable {p : ℝ} {K : Set (Euc d)} {w : Euc d → ℝ} {τ j : ℝ}

/-- **`u = lowPow (1/p) τ j ∘ w` lies in `W₀^{1,p}(K)`** with weak gradient
`lowDeriv (1/p) τ j (w) ∇w`.  The chain rule itself is `Komlos.Literature.memW0_comp` at
exponent `2` (where `w` lives); the `L^p` bounds come from `lowPow t ≤ t^{2/p}` and from
`lowDeriv t ≤ (2/p) t^{2/p-1}` together with `s^{2-p} t^p ≤ s² + t²`. -/
theorem memW0_lowPow_comp (hp : 1 < p) (hp2 : p ≤ 2) (hw : IsRegAdmissible 2 K w)
    (hτ : 0 < τ) (hj : 0 ≤ j) :
    MemW0 p K (fun x => lowPow (1 / p) τ j (w x)) ∧
      weakGrad (fun x => lowPow (1 / p) τ j (w x)) =ᵐ[volume]
        fun x => lowDeriv (1 / p) τ j (w x) • weakGrad w x := by
  have hp0 : (0 : ℝ) < p := by linarith
  set β : ℝ := 1 / p with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβhalf : 1 / 2 ≤ β := by
    rw [hβdef, le_div_iff₀ hp0]
    linarith
  have hβ1 : β ≤ 1 := by rw [hβdef, div_le_one hp0]; linarith
  have h2βp : (2 * β - 1) * p = 2 - p := by rw [hβdef]; field_simp
  have h2βp' : 2 * β * p = 2 := by rw [hβdef]; field_simp
  have hwnn := hw.nonneg
  have hw2 : MemLp w 2 volume := by
    have := hw.memW0.memLp; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at this
  have hg2 : MemLp (weakGrad w) 2 volume := by
    have := hw.memW0.memLp_weakGrad; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at this
  have hi1 : Integrable fun x => w x ^ 2 := hw2.integrable_sq
  have hig : Integrable fun x => ‖weakGrad w x‖ ^ 2 := hg2.norm.integrable_sq
  -- the chain rule at exponent `2`
  obtain ⟨hu2, hug0⟩ := memW0_comp (p := 2) (K := K) (f := w) (by norm_num) hw.memW0
    (G := lowPow β τ j) (contDiff_lowPow hτ) (lowPow_zero_arg)
    (L := 2 * β * j * τ ^ (β - 1)) (fun t => by
      rw [deriv_lowPow hτ, abs_of_nonneg (lowDeriv_nonneg hβ0.le hτ hj t)]
      exact lowDeriv_le_const hβ0.le hβ1 hτ hj t)
  have hug : weakGrad (fun x => lowPow β τ j (w x)) =ᵐ[volume]
      fun x => lowDeriv β τ j (w x) • weakGrad w x := by
    simpa only [deriv_lowPow hτ] using hug0
  refine ⟨?_, hug⟩
  -- `u ∈ L^p`
  have hum : AEStronglyMeasurable (fun x => lowPow β τ j (w x)) volume :=
    (contDiff_lowPow hτ).continuous.comp_aestronglyMeasurable hw2.1
  have hule : ∀ x, |lowPow β τ j (w x)| ^ p ≤ w x ^ 2 := by
    intro x
    have h0 : 0 ≤ lowPow β τ j (w x) := lowPow_nonneg hβ0.le hτ hj (hwnn x)
    rw [abs_of_nonneg h0]
    have h1 : lowPow β τ j (w x) ≤ w x ^ (2 * β) := lowPow_le_rpow hβhalf hβ1 hτ hj (hwnn x)
    calc lowPow β τ j (w x) ^ p ≤ (w x ^ (2 * β)) ^ p := Real.rpow_le_rpow h0 h1 hp0.le
      _ = w x ^ (2 * β * p) := by rw [← Real.rpow_mul (hwnn x)]
      _ = w x ^ 2 := by rw [h2βp', rpow_two_eq_sq]
  have hmeas_abs : AEStronglyMeasurable (fun x => |lowPow β τ j (w x)| ^ p) volume := by
    have hc : Continuous fun y : ℝ => |y| ^ p :=
      (continuous_iff_continuousAt.2 fun y =>
        Real.continuousAt_rpow_const y p (Or.inr hp0.le)).comp continuous_abs
    exact hc.comp_aestronglyMeasurable hum
  have huint : Integrable fun x => |lowPow β τ j (w x)| ^ p := by
    refine Integrable.mono' hi1 hmeas_abs (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hule x
  -- the gradient in `L^p`
  have hgm : AEStronglyMeasurable (fun x => lowDeriv β τ j (w x) • weakGrad w x) volume :=
    (((continuous_lowDeriv hτ).comp_aestronglyMeasurable hw2.1)).smul hg2.1
  have hgle : ∀ x, ‖lowDeriv β τ j (w x) • weakGrad w x‖ ^ p ≤
      (2 * β) ^ p * (w x ^ 2 + ‖weakGrad w x‖ ^ 2) := by
    intro x
    have hd0 : 0 ≤ lowDeriv β τ j (w x) := lowDeriv_nonneg hβ0.le hτ hj _
    have hβnn : (0 : ℝ) ≤ 2 * β := by linarith
    have h1 : lowDeriv β τ j (w x) ≤ 2 * β * w x ^ (2 * β - 1) :=
      lowDeriv_le_rpow hβhalf hβ1 hτ hj (hwnn x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0]
    have h2 : (lowDeriv β τ j (w x) * ‖weakGrad w x‖) ^ p ≤
        (2 * β * w x ^ (2 * β - 1) * ‖weakGrad w x‖) ^ p := by
      refine Real.rpow_le_rpow (mul_nonneg hd0 (norm_nonneg _)) ?_ hp0.le
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : (2 * β * w x ^ (2 * β - 1) * ‖weakGrad w x‖) ^ p =
        (2 * β) ^ p * (w x ^ (2 - p) * ‖weakGrad w x‖ ^ p) := by
      rw [Real.mul_rpow (mul_nonneg hβnn (Real.rpow_nonneg (hwnn x) _)) (norm_nonneg _),
        Real.mul_rpow hβnn (Real.rpow_nonneg (hwnn x) _),
        ← Real.rpow_mul (hwnn x), h2βp, mul_assoc]
    have h4 : w x ^ (2 - p) * ‖weakGrad w x‖ ^ p ≤ w x ^ 2 + ‖weakGrad w x‖ ^ 2 :=
      rpow_mul_rpow_le_sq hp hp2 (hwnn x) (norm_nonneg _)
    calc (lowDeriv β τ j (w x) * ‖weakGrad w x‖) ^ p
        ≤ (2 * β) ^ p * (w x ^ (2 - p) * ‖weakGrad w x‖ ^ p) := by rw [← h3]; exact h2
      _ ≤ (2 * β) ^ p * (w x ^ 2 + ‖weakGrad w x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hβnn _)
  have hgmeas_abs : AEStronglyMeasurable
      (fun x => ‖lowDeriv β τ j (w x) • weakGrad w x‖ ^ p) volume := by
    have hc : Continuous fun y : ℝ => y ^ p :=
      continuous_iff_continuousAt.2 fun y => Real.continuousAt_rpow_const y p (Or.inr hp0.le)
    exact hc.comp_aestronglyMeasurable hgm.norm
  have hgint : Integrable fun x => ‖lowDeriv β τ j (w x) • weakGrad w x‖ ^ p := by
    refine Integrable.mono' ((hi1.add hig).const_mul ((2 * β) ^ p)) hgmeas_abs
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hgle x
  have hgmem : MemLp (fun x => lowDeriv β τ j (w x) • weakGrad w x) (ENNReal.ofReal p) volume := by
    refine (integrable_norm_rpow_iff hgm
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0)
      ENNReal.ofReal_ne_top).1 ?_
    rw [ENNReal.toReal_ofReal hp0.le]
    exact hgint
  exact
    { memLp := memLp_ofReal_of_integrable_rpow hp0 hum huint
      ae_eq_zero := Eventually.of_forall fun x hx => by
        rw [hw.eq_zero_of_notMem x hx, lowPow_zero_arg]
      exists_weakGradient :=
        ⟨fun x => lowDeriv β τ j (w x) • weakGrad w x,
          hu2.hasWeakGradient.congr_right hug, hgmem⟩ }

end ChainRule

/-! ### The pointwise kinetic bound and the limit -/

section Kinetic

/-- `lowPow (1/p) τ j t ^ p ≤ t²`. -/
theorem lowPow_rpow_le_sq {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {τ j : ℝ} (hτ : 0 < τ)
    (hj : 0 ≤ j) {t : ℝ} (ht : 0 ≤ t) : lowPow (1 / p) τ j t ^ p ≤ t ^ 2 := by
  have hp0 : (0 : ℝ) < p := by linarith
  set β : ℝ := 1 / p with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβhalf : 1 / 2 ≤ β := by rw [hβdef, le_div_iff₀ hp0]; linarith
  have hβ1 : β ≤ 1 := by rw [hβdef, div_le_one hp0]; linarith
  have h2βp' : 2 * β * p = 2 := by rw [hβdef]; field_simp
  have h0 : 0 ≤ lowPow β τ j t := lowPow_nonneg hβ0.le hτ hj ht
  have h1 : lowPow β τ j t ≤ t ^ (2 * β) := lowPow_le_rpow hβhalf hβ1 hτ hj ht
  calc lowPow β τ j t ^ p ≤ (t ^ (2 * β)) ^ p := Real.rpow_le_rpow h0 h1 hp0.le
    _ = t ^ (2 * β * p) := by rw [← Real.rpow_mul ht]
    _ = t ^ 2 := by rw [h2βp', rpow_two_eq_sq]

/-- **The pointwise kinetic bound.**  `(lowPow')^p F(ξ)^p ≤ p · D(t, ξ)`: the truncated
derivative is at most `(2/p) t^{2/p-1}`, and `Ψ_p ≥ F^p/p` for `p ≤ 2`. -/
theorem rpow_mul_le_homogeneousDensity {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {R ε : ℝ} (hR : 0 < R) {ρ : Euc d → ℝ} (hρ : IsMollifier ρ ε)
    {τ j : ℝ} (hτ : 0 < τ) (hj : 0 ≤ j) {t : ℝ} (ht : 0 ≤ t) (ξ : Euc d) :
    lowDeriv (1 / p) τ j t ^ p * F ξ ^ p ≤
      p * Korevaar.homogeneousDensity 2 (regProfile p F R ρ) t ξ := by
  have hp0 : (0 : ℝ) < p := by linarith
  set β : ℝ := 1 / p with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβhalf : 1 / 2 ≤ β := by rw [hβdef, le_div_iff₀ hp0]; linarith
  have hβ1 : β ≤ 1 := by rw [hβdef, div_le_one hp0]; linarith
  have hβnn : (0 : ℝ) ≤ 2 * β := by linarith
  have h2βeq : 2 * β = 2 / p := by rw [hβdef]; ring
  have hFξ : 0 ≤ F ξ := hF.nonneg ξ
  rcases ht.eq_or_lt with rfl | htpos
  · rw [lowDeriv_zero_arg hj, Real.zero_rpow hp0.ne', zero_mul, homogeneousDensity_two_zero,
      mul_zero]
  · have h2βp : (2 * β - 1) * p = 2 - p := by rw [hβdef]; field_simp
    have hd0 : 0 ≤ lowDeriv β τ j t := lowDeriv_nonneg hβ0.le hτ hj t
    have hd : lowDeriv β τ j t ≤ 2 * β * t ^ (2 * β - 1) := lowDeriv_le_rpow hβhalf hβ1 hτ hj ht
    -- the left-hand side
    have hL : lowDeriv β τ j t ^ p * F ξ ^ p ≤ (2 * β) ^ p * (t ^ (2 - p) * F ξ ^ p) := by
      have h1 : lowDeriv β τ j t ^ p ≤ (2 * β * t ^ (2 * β - 1)) ^ p :=
        Real.rpow_le_rpow hd0 hd hp0.le
      have h2 : (2 * β * t ^ (2 * β - 1)) ^ p = (2 * β) ^ p * t ^ (2 - p) := by
        rw [Real.mul_rpow hβnn (Real.rpow_nonneg htpos.le _), ← Real.rpow_mul htpos.le, h2βp]
      calc lowDeriv β τ j t ^ p * F ξ ^ p ≤ ((2 * β) ^ p * t ^ (2 - p)) * F ξ ^ p := by
            rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hFξ _)
        _ = (2 * β) ^ p * (t ^ (2 - p) * F ξ ^ p) := by ring
    -- the right-hand side
    have hq : F ((2 / p) • (t⁻¹ • ξ)) = 2 / p * t⁻¹ * F ξ := by
      rw [smul_smul, hF.homog, abs_of_pos (by positivity)]
    have harg : (p / 2) • ((2 / p) • (t⁻¹ • ξ)) = t⁻¹ • ξ := by
      rw [smul_smul]
      have : p / 2 * (2 / p) = 1 := by field_simp
      rw [this, one_smul]
    have hΨ : (2 / p * t⁻¹ * F ξ) ^ p / p ≤ regProfile p F R ρ (t⁻¹ • ξ) := by
      have h := rpow_div_le_regProfile hp hp2 hR hF hρ ((2 / p) • (t⁻¹ • ξ))
      rwa [hq, harg] at h
    have hRHS : (2 * β) ^ p * (t ^ (2 - p) * F ξ ^ p) ≤
        p * Korevaar.homogeneousDensity 2 (regProfile p F R ρ) t ξ := by
      have hinv : (t⁻¹ : ℝ) ^ p = (t ^ p)⁻¹ := Real.inv_rpow htpos.le p
      have hexp : t ^ (2 : ℝ) * (t ^ p)⁻¹ = t ^ (2 - p) := by
        rw [← Real.rpow_neg htpos.le, ← Real.rpow_add htpos]
        congr 1
        try ring
      have heq : t ^ (2 : ℝ) * (2 / p * t⁻¹ * F ξ) ^ p =
          (2 * β) ^ p * (t ^ (2 - p) * F ξ ^ p) := by
        rw [Real.mul_rpow (by positivity) hFξ,
          Real.mul_rpow (by positivity) (inv_nonneg.2 htpos.le), hinv, h2βeq]
        rw [← hexp]
        ring
      have hmul := mul_le_mul_of_nonneg_left hΨ
        (by positivity : (0 : ℝ) ≤ p * t ^ (2 : ℝ))
      rw [Korevaar.homogeneousDensity]
      calc (2 * β) ^ p * (t ^ (2 - p) * F ξ ^ p)
          = t ^ (2 : ℝ) * (2 / p * t⁻¹ * F ξ) ^ p := heq.symm
        _ = p * t ^ (2 : ℝ) * ((2 / p * t⁻¹ * F ξ) ^ p / p) := by field_simp; try ring
        _ ≤ p * t ^ (2 : ℝ) * regProfile p F R ρ (t⁻¹ • ξ) := hmul
        _ = p * (t ^ (2 : ℝ) * regProfile p F R ρ (t⁻¹ • ξ)) := by ring
    exact hL.trans hRHS

/-- The truncated power converges to the untruncated one. -/
theorem tendsto_lowPow_rpow {β : ℝ} (hβ0 : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) t) atTop
      (𝓝 (t ^ (2 * β))) := by
  have hev : (fun n : ℕ => powShift β (1 / ((n : ℝ) + 1)) t) =ᶠ[atTop]
      fun n : ℕ => lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) t := by
    filter_upwards [eventually_ge_atTop ⌈t⌉₊] with n hn
    have hcast : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have htn : t ≤ (n : ℝ) + 1 := by linarith [Nat.le_ceil t]
    exact (lowPow_eq_powShift (by positivity) ht htn).symm
  refine Tendsto.congr' hev ?_
  have hτlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrc : Continuous fun x : ℝ => x ^ β :=
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x β (Or.inr hβ0.le)
  have h1 : Tendsto (fun n : ℕ => (t ^ 2 + 1 / ((n : ℝ) + 1)) ^ β) atTop (𝓝 ((t ^ 2) ^ β)) :=
    (hrc.tendsto _).comp (by simpa using tendsto_const_nhds.add hτlim)
  have h2 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ β) atTop (𝓝 0) := by
    have h := (hrc.tendsto (0 : ℝ)).comp hτlim
    rwa [Real.zero_rpow hβ0.ne'] at h
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  have h4 : (t ^ 2) ^ β = t ^ (2 * β) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
    norm_num
  rw [← h4]
  simpa only [powShift] using h3

end Kinetic

/-! ### The lower bound on the kinetic integral -/

/-- **The lower bound on the kinetic integral for `p ≤ 2`**: for every admissible competitor `w`,
`λ_{p,F}(K)/p ≤ ∫ w² Ψ(∇w/w)`.

Apply `lambdaSob_mul_le` to the `W₀^{1,p}` function `u = lowPow (1/p) τ j ∘ w`
(`memW0_lowPow_comp`), bound the resulting `∫ F(∇u)^p` by `p ∫ D(w, ∇w)` pointwise
(`rpow_mul_le_homogeneousDensity`), and let `τ ↓ 0`, `j ↑ ∞`, where `∫ u^p → ∫ w² = 1`. -/
theorem le_integral_kinetic_regProfile {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K)
    {R ε : ℝ} (hR : 0 < R) {ρ : Euc d → ℝ} (hρ : IsMollifier ρ ε)
    {w : Euc d → ℝ} (hw : IsRegAdmissible 2 K w) :
    lambdaGen p F K / p ≤
      ∫ x, Korevaar.homogeneousDensity 2 (regProfile p F R ρ) (w x) (weakGrad w x) := by
  have hp0 : (0 : ℝ) < p := by linarith
  set β : ℝ := 1 / p with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have h2βp' : 2 * β * p = 2 := by rw [hβdef]; field_simp
  have hrc : Continuous fun y : ℝ => y ^ p :=
    continuous_iff_continuousAt.2 fun y => Real.continuousAt_rpow_const y p (Or.inr hp0.le)
  have hΨreg : IsRegProfile (regProfile p F R ρ) := isRegProfile_regProfile hp hR hF hρ
  obtain ⟨c₀, C₀, hΨW⟩ := hΨreg.exists_isRegProfileWith
  have hkin_int : Integrable fun x =>
      Korevaar.homogeneousDensity 2 (regProfile p F R ρ) (w x) (weakGrad w x) :=
    integrable_kinetic hΨW hw.memW0 hw.nonneg
  obtain ⟨CF, hCF⟩ := hF.exists_le_mul_norm
  have hlamEq : lambdaSob p F K = lambdaGen p F K :=
    lambdaSob_eq_lambdaGen hp hF.continuous hF.nonneg hCF hK
  have hw2 : MemLp w 2 volume := by
    have := hw.memW0.memLp; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at this
  have hg2 : MemLp (weakGrad w) 2 volume := by
    have := hw.memW0.memLp_weakGrad; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at this
  have hi1 : Integrable fun x => w x ^ 2 := hw2.integrable_sq
  set C : ℝ := ∫ x, Korevaar.homogeneousDensity 2 (regProfile p F R ρ) (w x) (weakGrad w x)
    with hCdef
  -- the key inequality at each truncation level
  have hkey : ∀ n : ℕ,
      lambdaSob p F K * (∫ x, lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p) ≤ p * C := by
    intro n
    have hτ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hj : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    obtain ⟨hu, hug⟩ := memW0_lowPow_comp hp hp2 hw hτ hj
    have hlam := lambdaSob_mul_le hp0 hF.nonneg hu
    have habs : (∫ x, |lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x)| ^ p) =
        ∫ x, lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show |lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x)| ^ p =
        lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p
      rw [abs_of_nonneg (lowPow_nonneg hβ0.le hτ hj (hw.nonneg x))]
    rw [habs] at hlam
    refine hlam.trans ?_
    have hcongr :
        (fun x => F (weakGrad (fun y => lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w y)) x) ^ p)
          =ᵐ[volume] fun x =>
            lowDeriv β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p * F (weakGrad w x) ^ p := by
      filter_upwards [hug] with x hx
      rw [hx, hF.homog, abs_of_nonneg (lowDeriv_nonneg hβ0.le hτ hj _),
        Real.mul_rpow (lowDeriv_nonneg hβ0.le hτ hj _) (hF.nonneg _)]
    rw [integral_congr_ae hcongr]
    have hptw : ∀ x,
        lowDeriv β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p * F (weakGrad w x) ^ p ≤
          p * Korevaar.homogeneousDensity 2 (regProfile p F R ρ) (w x) (weakGrad w x) :=
      fun x => rpow_mul_le_homogeneousDensity hp hp2 hF hR hρ hτ hj (hw.nonneg x) _
    have hint : Integrable fun x =>
        lowDeriv β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p * F (weakGrad w x) ^ p := by
      refine Integrable.mono' (hkin_int.const_mul p) ?_ (Eventually.of_forall fun x => ?_)
      · exact (hrc.comp_aestronglyMeasurable
          ((continuous_lowDeriv hτ).comp_aestronglyMeasurable hw2.1)).mul
          (hrc.comp_aestronglyMeasurable (hF.continuous.comp_aestronglyMeasurable hg2.1))
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (Real.rpow_nonneg (lowDeriv_nonneg hβ0.le hτ hj _) _)
          (Real.rpow_nonneg (hF.nonneg _) _))]
        exact hptw x
    calc (∫ x, lowDeriv β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p * F (weakGrad w x) ^ p)
        ≤ ∫ x, p * Korevaar.homogeneousDensity 2 (regProfile p F R ρ) (w x) (weakGrad w x) :=
          integral_mono hint (hkin_int.const_mul p) hptw
      _ = p * C := by rw [integral_const_mul]
  -- the truncated integrals converge to `∫ w² = 1`
  have hlim : Tendsto (fun n : ℕ => ∫ x, lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p)
      atTop (𝓝 1) := by
    have hlim0 : Tendsto (fun n : ℕ => ∫ x, lowPow β (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (w x) ^ p)
        atTop (𝓝 (∫ x, w x ^ 2)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => w x ^ 2) ?_ ?_ hi1 ?_
      · refine Eventually.of_forall fun n => ?_
        exact hrc.comp_aestronglyMeasurable
          ((contDiff_lowPow (β := β) (j := (n : ℝ) + 1)
            (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).continuous.comp_aestronglyMeasurable
            hw2.1)
      · refine Eventually.of_forall fun n => Eventually.of_forall fun x => ?_
        have hτ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hj : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (lowPow_nonneg hβ0.le hτ hj (hw.nonneg x)) _)]
        exact lowPow_rpow_le_sq hp hp2 hτ hj (hw.nonneg x)
      · refine Eventually.of_forall fun x => ?_
        have h := (hrc.tendsto (w x ^ (2 * β))).comp (tendsto_lowPow_rpow hβ0 (hw.nonneg x))
        have h3 : (w x ^ (2 * β)) ^ p = w x ^ 2 := by
          rw [← Real.rpow_mul (hw.nonneg x), h2βp', rpow_two_eq_sq]
        rw [h3] at h
        simpa only [Function.comp_def] using h
    rwa [hw.integral_sq] at hlim0
  have hfinal : lambdaSob p F K * 1 ≤ p * C :=
    le_of_tendsto (hlim.const_mul (lambdaSob p F K)) (Eventually.of_forall hkey)
  rw [mul_one, hlamEq] at hfinal
  rw [hCdef] at hfinal ⊢
  rw [div_le_iff₀ hp0]
  linarith [hfinal]

/-! ### The lower scalar limit -/

/-- **The lower scalar limit for `1 < p ≤ 2`**, with the explicit entropy error.  The kinetic
part is `le_integral_kinetic_regProfile` and the entropy part is `entropy_integral_ge`; neither
depends on `R` or `ε`, so no limit in those parameters is needed for `p ≤ 2`. -/
theorem le_regMin_of_le_two {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K)
    {R ε κ : ℝ} (hR : 0 < R) {ρ : Euc d → ℝ} (hρ : IsMollifier ρ ε) (hκ : 0 < κ) :
    lambdaGen p F K / p - κ / 2 * |(1 / 2) * Real.log (volume K).toReal| ≤
      regMin 2 κ (regProfile p F R ρ) K := by
  refine le_regMin_of_forall hK fun w hw => ?_
  rw [regEnergy]
  have h1 := le_integral_kinetic_regProfile hp hp2 hF hK hR hρ hw
  have h2 := entropy_integral_ge hκ hK hw
  linarith

/-- **The lower scalar limit for `p > 2`** (`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*).

For `p > 2` the truncated power satisfies `h_R ≤ s^p/p` (`truncPow_le_rpow_div`), so the profile
lies *below* `F^p/p` and the pointwise argument of `le_integral_kinetic_regProfile` (which uses
`F^p/p ≤ Ψ_p`, valid only for `p ≤ 2`) is unavailable.  This is not an artefact of the choice of
profile: no profile with a *globally* bounded second derivative can dominate `F^p/p` when
`p > 2`, since `s^p/p` grows superquadratically.  The `R → ∞` limit is therefore unavoidable, and
it has to be taken along a minimizing sequence; the argument is carried out in
`Komlos/Literature/Regularized/ScalarLimitGtTwo.lean` (uniform `W^{1,2}` bound from the
quadratic coercivity of `h_{R₀}`, Rellich compactness, lane `L1`'s weak lower semicontinuity at a
fixed truncation radius, monotone convergence in `R₀`, and the chain rule for the concave power
`u = w^{2/p}`). -/
theorem le_regMin_of_gt_two {p : ℝ} (hp2 : 2 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ)
    {Rs εs κs : ℕ → ℝ} {ρs : ℕ → Euc d → ℝ}
    (hRpos : ∀ n, 0 < Rs n) (hRlim : Tendsto Rs atTop atTop)
    (hρ : ∀ n, IsMollifier (ρs n) (εs n)) (hεlim : Tendsto εs atTop (𝓝 0))
    (hκpos : ∀ n, 0 < κs n) (hκlim : Tendsto κs atTop (𝓝 0)) :
    ∀ᶠ n in atTop, lambdaGen p F K / p - δ ≤
      regMin 2 (κs n) (regProfile p F (Rs n) (ρs n)) K :=
  le_regMin_of_gt_two' hp2 hF hK hδ hRpos hRlim hρ hεlim hκpos hκlim

/-- **The lower scalar limit** along any family of regularization parameters with `R → ∞`,
`ε → 0` and `κ → 0`.  For `p ≤ 2` only `κ → 0` is used. -/
theorem eventually_le_regMin_of_params {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ)
    {Rs εs κs : ℕ → ℝ} {ρs : ℕ → Euc d → ℝ}
    (hRpos : ∀ n, 0 < Rs n) (hRlim : Tendsto Rs atTop atTop)
    (hρ : ∀ n, IsMollifier (ρs n) (εs n)) (hεlim : Tendsto εs atTop (𝓝 0))
    (hκpos : ∀ n, 0 < κs n) (hκlim : Tendsto κs atTop (𝓝 0)) :
    ∀ᶠ n in atTop, lambdaGen p F K / p - δ ≤
      regMin 2 (κs n) (regProfile p F (Rs n) (ρs n)) K := by
  rcases le_or_gt p 2 with hp2 | hp2
  · have hκ0 : Tendsto
        (fun n => κs n / 2 * |(1 / 2) * Real.log (volume K).toReal|) atTop (𝓝 0) := by
      simpa using (hκlim.div_const 2).mul_const |(1 / 2) * Real.log (volume K).toReal|
    filter_upwards [hκ0.eventually (eventually_lt_nhds hδ)] with n hn
    have h := le_regMin_of_le_two hp hp2 hF hK (hRpos n) (hρ n) (hκpos n)
    linarith
  · exact le_regMin_of_gt_two hp2 hF hK hδ hRpos hRlim hρ hεlim hκpos hκlim

end Komlos.Literature.Regularized
