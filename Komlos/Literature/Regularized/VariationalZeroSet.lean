import Komlos.Literature.Regularized.VariationalDensity

/-!
# The weak gradient vanishes on the zero set

Lane `L1` (`reg/variational`).  This file proves **Stampacchia's lemma** in the form needed by
the regularized route: if `w ∈ W₀^{1,2}(K)` is nonnegative, then `∇w = 0` a.e. on `{w = 0}`.

This is what makes the junk value `0` of `Korevaar.homogeneousDensity` at `u = 0` a.e.
correct, and hence what makes the two-sided bound
`Ψ 0 w² + (c/2)‖∇w‖² ≤ w² Ψ(∇w/w) ≤ Ψ 0 w² + (C/2)‖∇w‖²` hold a.e. on the whole space
(`REGULARIZED_ROUTE.md`, Revision 2).

## Proof

For `ε > 0` put `H_ε(t) = t + ε - √(t² + ε²)` (`sqrtDefect`).  It is `C^∞`, `H_ε(0) = 0`,
`|H_ε'| ≤ 2`, and `0 ≤ H_ε(t) ≤ min (t, ε)` for `t ≥ 0`.  The chain rule `memW0_comp` gives
`∇(H_ε ∘ w) = H_ε'(w) ∇w`.  As `ε ↓ 0`:

* `H_ε ∘ w → 0` in `L²`, because `|H_ε(w)| ≤ ε` on `K` and `w = 0` a.e. off `K`
  (`K` has finite volume);
* `H_ε'(w) = 1 - w/√(w² + ε²) → 1_{w = 0}` pointwise and boundedly, so
  `H_ε'(w) ∇w → 1_{w=0} ∇w` in `L²` (`tendsto_eLpNorm_smul_sub_smul`).

Hence `1_{w=0} ∇w` is a weak gradient of `0`, so it vanishes a.e.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The smooth defect `t + ε - √(t² + ε²)` -/

/-- The smooth truncation defect `H_ε(t) = t + ε - √(t² + ε²)`: a `C^∞` function vanishing at
`0`, with `0 ≤ H_ε(t) ≤ min (t, ε)` for `t ≥ 0`, and `H_ε'(0) = 1`. -/
noncomputable def sqrtDefect (ε t : ℝ) : ℝ := t + ε - Real.sqrt (t ^ 2 + ε ^ 2)

theorem sqrtDefect_zero {ε : ℝ} (hε : 0 ≤ ε) : sqrtDefect ε 0 = 0 := by
  simp [sqrtDefect, Real.sqrt_sq hε]

theorem sqrtDefect_nonneg {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ sqrtDefect ε t := by
  have h : Real.sqrt (t ^ 2 + ε ^ 2) ≤ t + ε := by
    rw [show t + ε = Real.sqrt ((t + ε) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  simp only [sqrtDefect]
  linarith

theorem sqrtDefect_le_left {ε : ℝ} (_hε : 0 ≤ ε) {t : ℝ} (ht : 0 ≤ t) : sqrtDefect ε t ≤ ε := by
  have h : t ≤ Real.sqrt (t ^ 2 + ε ^ 2) := by
    calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht).symm
      _ ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  simp only [sqrtDefect]
  linarith

/-- The derivative of `H_ε`. -/
theorem hasDerivAt_sqrtDefect {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (sqrtDefect ε) (1 - t / Real.sqrt (t ^ 2 + ε ^ 2)) t := by
  have hpos : 0 < t ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ε ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const (ε ^ 2)
  have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + ε ^ 2))
      (t / Real.sqrt (t ^ 2 + ε ^ 2)) t :=
    (h1.sqrt hpos.ne').congr_deriv (mul_div_mul_left _ _ two_ne_zero)
  have h3 : HasDerivAt (fun s : ℝ => s + ε) 1 t := by
    simpa using (hasDerivAt_id t).add_const ε
  show HasDerivAt (fun s : ℝ => s + ε - Real.sqrt (s ^ 2 + ε ^ 2))
    (1 - t / Real.sqrt (t ^ 2 + ε ^ 2)) t
  exact h3.sub h2

theorem deriv_sqrtDefect {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (sqrtDefect ε) t = 1 - t / Real.sqrt (t ^ 2 + ε ^ 2) :=
  (hasDerivAt_sqrtDefect hε t).deriv

theorem contDiff_sqrtDefect {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (sqrtDefect ε) := by
  have hpos : ∀ t : ℝ, t ^ 2 + ε ^ 2 ≠ 0 := fun t =>
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)).ne'
  exact (contDiff_id.add contDiff_const).sub
    (((contDiff_id.pow 2).add contDiff_const).sqrt hpos)

/-- `|H_ε'| ≤ 2`. -/
theorem abs_deriv_sqrtDefect_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |deriv (sqrtDefect ε) t| ≤ 2 := by
  have hpos : 0 < t ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)
  have hs : 0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.2 hpos
  have habs : |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) := by
    rw [show |t| = Real.sqrt (t ^ 2) from (Real.sqrt_sq_eq_abs t).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  rw [deriv_sqrtDefect hε]
  have hq : |t / Real.sqrt (t ^ 2 + ε ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    exact habs
  calc |1 - t / Real.sqrt (t ^ 2 + ε ^ 2)| ≤ |(1 : ℝ)| + |t / Real.sqrt (t ^ 2 + ε ^ 2)| :=
        abs_sub _ _
    _ ≤ 1 + 1 := by rw [abs_one]; linarith
    _ = 2 := by norm_num

/-- `H_ε'(t) → 1_{t = 0}` as `ε ↓ 0`, for `t ≥ 0`. -/
theorem tendsto_deriv_sqrtDefect {e : ℕ → ℝ} (he : ∀ n, 0 < e n)
    (he0 : Tendsto e atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => deriv (sqrtDefect (e n)) t) atTop
      (𝓝 (if t = 0 then (1 : ℝ) else 0)) := by
  simp only [deriv_sqrtDefect (he _)]
  rcases eq_or_lt_of_le ht with h0 | hpos
  · simp [← h0]
  · rw [if_neg hpos.ne']
    have hcont : Tendsto (fun n => Real.sqrt (t ^ 2 + e n ^ 2)) atTop
        (𝓝 (Real.sqrt (t ^ 2 + 0 ^ 2))) :=
      (Real.continuous_sqrt.tendsto _).comp (by
        simpa using (tendsto_const_nhds (x := t ^ 2)).add ((he0.pow 2)))
    rw [show t ^ 2 + (0 : ℝ) ^ 2 = t ^ 2 by ring, Real.sqrt_sq hpos.le] at hcont
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := t)).div hcont hpos.ne')
    rw [div_self hpos.ne', sub_self] at h
    exact h

/-! ### Stampacchia's lemma -/

/-- **The weak gradient vanishes a.e. on the zero set** of a nonnegative `W₀^{1,2}(K)` function
(Stampacchia; Gilbarg–Trudinger Lemma 7.7).  `K` is only used through `volume K ≠ ⊤`. -/
theorem weakGrad_eq_zero_of_eq_zero {K : Set (Euc d)} (hKm : MeasurableSet K)
    (hKvol : volume K ≠ ⊤) {w : Euc d → ℝ} (hw : MemW0 2 K w) (hw0 : ∀ x, 0 ≤ w x) :
    ∀ᵐ x, w x = 0 → weakGrad w x = 0 := by
  set e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with he_def
  have he : ∀ n, 0 < e n := fun n => Nat.one_div_pos_of_nat
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the chain rule applied to `H_{e n}`
  have hchain := fun n => memW0_comp (K := K) (f := w) one_lt_two hw
    (contDiff_sqrtDefect (he n)) (sqrtDefect_zero (he n).le)
    (L := 2) (fun t => abs_deriv_sqrtDefect_le (he n) t)
  set a : ℕ → Euc d → ℝ := fun n x => deriv (sqrtDefect (e n)) (w x) with ha_def
  set al : Euc d → ℝ := fun x => if w x = 0 then (1 : ℝ) else 0 with hal_def
  have hwg : ∀ n, HasWeakGradient (fun x => sqrtDefect (e n) (w x))
      (fun x => a n x • weakGrad w x) := fun n =>
    (hchain n).1.hasWeakGradient.congr_right (hchain n).2
  -- measurability
  have hwm : AEStronglyMeasurable w volume := hw.memLp.aestronglyMeasurable
  have ham : ∀ n, AEStronglyMeasurable (a n) volume := fun n => by
    have heq : deriv (sqrtDefect (e n)) =
        fun t : ℝ => 1 - t / Real.sqrt (t ^ 2 + e n ^ 2) := by
      funext t
      exact deriv_sqrtDefect (he n) t
    have hc : Continuous (deriv (sqrtDefect (e n))) := by
      rw [heq]
      exact continuous_const.sub (continuous_id.div
        (Real.continuous_sqrt.comp ((continuous_pow 2).add continuous_const)) fun t =>
          (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (he n) 2))).ne')
    exact hc.comp_aestronglyMeasurable hwm
  have hindm : Measurable fun t : ℝ => if t = 0 then (1 : ℝ) else 0 := by
    have heq : (fun t : ℝ => if t = 0 then (1 : ℝ) else 0) =
        ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) := by
      funext t
      simp [Set.indicator_apply]
    rw [heq]
    exact measurable_const.indicator (measurableSet_singleton 0)
  have halm : AEStronglyMeasurable al volume :=
    (hindm.comp_aemeasurable hwm.aemeasurable).aestronglyMeasurable
  have hal1 : ∀ x, |al x| ≤ 1 := fun x => by
    rw [hal_def]; by_cases hx : w x = 0 <;> simp [hx]
  have halmem : MemLp (fun x => al x • weakGrad w x) (ENNReal.ofReal 2) volume :=
    hw.memLp_weakGrad.of_le_mul (c := 1)
      (halm.smul hw.memLp_weakGrad.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, one_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hal1 x))
  -- `H_{e n} ∘ w → 0` in `L²`
  have hind : MemLp (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) volume :=
    memLp_indicator_const _ hKm _ (Or.inr hKvol)
  have hf0 : Tendsto (fun n => eLpNorm ((fun x => sqrtDefect (e n) (w x)) - (0 : Euc d → ℝ))
      (ENNReal.ofReal 2)) atTop (𝓝 0) := by
    have hle : ∀ n, eLpNorm ((fun x => sqrtDefect (e n) (w x)) - (0 : Euc d → ℝ))
        (ENNReal.ofReal 2) ≤
        ENNReal.ofReal (e n) * eLpNorm (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) := by
      intro n
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ _
      filter_upwards [hw.ae_eq_zero] with x hx
      show ‖((fun x => sqrtDefect (e n) (w x)) - (0 : Euc d → ℝ)) x‖ ≤
        e n * ‖K.indicator (fun _ => (1 : ℝ)) x‖
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, Real.norm_eq_abs]
      by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxK]
        simp only [abs_one, mul_one]
        rw [abs_of_nonneg (sqrtDefect_nonneg (he n).le (hw0 x))]
        exact sqrtDefect_le_left (he n).le (hw0 x)
      · rw [Set.indicator_of_notMem hxK, hx hxK, sqrtDefect_zero (he n).le]
        simp
    have hlim : Tendsto (fun n => ENNReal.ofReal (e n) *
        eLpNorm (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const
        ((ENNReal.continuous_ofReal.tendsto 0).comp he0) (Or.inr hind.eLpNorm_ne_top)
      simpa [Function.comp_def] using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle
  -- `H_{e n}'(w) ∇w → 1_{w = 0} ∇w` in `L²`
  have hgrad := tendsto_eLpNorm_smul_sub_smul (μ := volume) (p := 2) one_lt_two
    (a := a) (al := al) (b := fun _ => weakGrad w) (bl := weakGrad w)
    hw.memLp_weakGrad (L := 2) (fun n x => abs_deriv_sqrtDefect_le (he n) (w x))
    (fun x => (hal1 x).trans one_le_two)
    ham halm (fun _ => hw.memLp_weakGrad.aestronglyMeasurable)
    (Eventually.of_forall fun x => tendsto_deriv_sqrtDefect he he0 (hw0 x))
    (by simp)
  -- conclude
  have hzero : HasWeakGradient (0 : Euc d → ℝ) (fun x => al x • weakGrad w x) :=
    HasWeakGradient.of_tendsto one_lt_two hwg MemLp.zero halmem hf0 hgrad
  have hae := HasWeakGradient.ae_eq hzero HasWeakGradient.zero
  filter_upwards [hae] with x hx hwx
  have hal : al x = 1 := by rw [hal_def]; simp [hwx]
  rw [hal, one_smul] at hx
  simpa using hx

end Komlos.Literature.Regularized
