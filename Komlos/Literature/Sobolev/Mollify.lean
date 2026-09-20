import Komlos.Defs

/-!
# Mollification in `L^p`

Vector-valued mollification `mollifyWith ρ g x = ∫ ρ (x - t) • g t dt` on `ℝ^d`, and the `L^p`
facts about it needed by the Sobolev substrate (`Komlos.Literature.Sobolev.Defs`) and by
Rellich–Kondrachov (`Komlos.Literature.Sobolev.Rellich`):

* `enorm_integral_smul_rpow_le_of_prob` — weighted Jensen/Hölder
  `‖∫ w • g‖^p ≤ ∫ w ‖g‖^p` for a probability weight `w`;
* `mollifyWith`, `mollifyWith_eq_convolution`, `mollifyWith_eq_convolution_right` — the
  mollification and its two expressions as a Mathlib `convolution`; continuity, smoothness,
  support, linearity;
* `lintegral_enorm_mollifyWith_rpow_le`, `eLpNorm_mollifyWith_le` — **Young's inequality**
  `‖ρ ⋆ g‖_p ≤ ‖g‖_p` for a probability density `ρ`;
* `tendsto_eLpNorm_mollifyWith_sub` — **approximation of the identity in `L^p`**: for bumps with
  radii `→ 0`, `‖ρ_n ⋆ g − g‖_p → 0` for every `g ∈ L^p`, `1 < p < ∞` (via density of
  `C_c` in `L^p`, Young, and dominated convergence for the continuous compactly supported case);
* `tendsto_lintegral_enorm_sub_of_dominated` — the **generalized dominated convergence theorem**
  (Pratt's lemma: varying dominating functions with convergent integrals);
* `tendsto_integral_comp_of_tendsto_eLpNorm` — **continuity of Nemytskii functionals**
  `g ↦ ∫ Φ(g)` on `L^p` for continuous `Φ` with `|Φ ξ| ≤ C ‖ξ‖^p`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Convolution Pointwise

namespace Komlos.Literature

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-! ### Weighted Jensen and `L^p` norms -/

/-- Weighted Jensen/Hölder: for a probability weight `w ≥ 0` (`∫ w = 1`) and `p > 1`,
`‖∫ w • g‖^p ≤ ∫ w ‖g‖^p`. -/
theorem enorm_integral_smul_rpow_le_of_prob {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → H} (hg : AEStronglyMeasurable g μ) {w : α → ℝ} (hw : AEMeasurable w μ)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∫⁻ t, ENNReal.ofReal (w t) ∂μ = 1) {p : ℝ} (hp : 1 < p) :
    ‖∫ t, w t • g t ∂μ‖ₑ ^ p ≤ ∫⁻ t, ENNReal.ofReal (w t) * ‖g t‖ₑ ^ p ∂μ := by
  set q := Real.conjExponent p with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hwm : AEMeasurable (fun t => ENNReal.ofReal (w t)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hw
  set a : α → ℝ≥0∞ := fun t => ENNReal.ofReal (w t) ^ (1 / q) with ha_def
  set b : α → ℝ≥0∞ := fun t => ENNReal.ofReal (w t) ^ (1 / p) * ‖g t‖ₑ with hb_def
  have ha : AEMeasurable a μ := hwm.pow_const _
  have hb : AEMeasurable b μ := (hwm.pow_const _).mul hg.enorm
  have hab : ∀ t, a t * b t = ENNReal.ofReal (w t) * ‖g t‖ₑ := by
    intro t
    simp only [ha_def, hb_def]
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    have : 1 / q + 1 / p = 1 := by
      simp only [one_div]
      exact hpq.symm.inv_add_inv_eq_one
    rw [this, ENNReal.rpow_one]
  have haq : ∀ t, a t ^ q = ENNReal.ofReal (w t) := by
    intro t
    simp only [ha_def]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have hbp : ∀ t, b t ^ p = ENNReal.ofReal (w t) * ‖g t‖ₑ ^ p := by
    intro t
    simp only [hb_def]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one]
  have holder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm ha hb
  simp only [Pi.mul_apply, hab, haq, hbp, hw1, ENNReal.one_rpow, one_mul] at holder
  calc ‖∫ t, w t • g t ∂μ‖ₑ ^ p
      ≤ (∫⁻ t, ‖w t • g t‖ₑ ∂μ) ^ p :=
        ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm _) hp0.le
    _ = (∫⁻ t, ENNReal.ofReal (w t) * ‖g t‖ₑ ∂μ) ^ p := by
        congr 1
        refine lintegral_congr fun t => ?_
        rw [enorm_smul, Real.enorm_eq_ofReal (hw0 _)]
    _ ≤ ((∫⁻ t, ENNReal.ofReal (w t) * ‖g t‖ₑ ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow holder hp0.le
    _ = ∫⁻ t, ENNReal.ofReal (w t) * ‖g t‖ₑ ^ p ∂μ := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]

omit [NormedSpace ℝ H] in
/-- `∫ ‖f‖^p = ‖f‖_{L^p}^p` for `f ∈ L^p`, `p > 0`. -/
theorem integral_norm_rpow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → H}
    {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    ∫ x, ‖f x‖ ^ p ∂μ = (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [hf.eLpNorm_eq_integral_rpow_norm hp' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _),
    ← Real.rpow_mul (integral_nonneg fun _ => by positivity), inv_mul_cancel₀ hp.ne',
    Real.rpow_one]

omit [NormedSpace ℝ H] in
/-- Conversion: `∫ ‖f‖^p ≤ C^p ∫ ‖g‖^p` gives `‖f‖_{L^p} ≤ C ‖g‖_{L^p}`. -/
theorem eLpNorm_le_of_lintegral_rpow_le' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {H' : Type*} [NormedAddCommGroup H'] {p : ℝ} (hp : 0 < p) {f : α → H} {g : α → H'}
    {C : ℝ≥0∞} (h : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ C ^ p * ∫⁻ x, ‖g x‖ₑ ^ p ∂μ) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ C * eLpNorm g (ENNReal.ofReal p) μ := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp' hpt, ENNReal.toReal_ofReal hp.le]
  calc (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p)
      ≤ (C ^ p * ∫⁻ x, ‖g x‖ₑ ^ p ∂μ) ^ (1 / p) := ENNReal.rpow_le_rpow h (by positivity)
    _ = C * (∫⁻ x, ‖g x‖ₑ ^ p ∂μ) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-! ### Mollification -/

/-- The mollification `(mollifyWith ρ g) x = ∫ ρ (x - t) • g t dt` of a vector-valued `g` by a
scalar kernel `ρ`. -/
noncomputable def mollifyWith (ρ : Euc d → ℝ) (g : Euc d → H) (x : Euc d) : H :=
  ∫ t, ρ (x - t) • g t

/-- `mollifyWith ρ g = ρ ⋆ g` (kernel on the left). -/
theorem mollifyWith_eq_convolution (ρ : Euc d → ℝ) (g : Euc d → H) :
    mollifyWith ρ g = ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
  funext x
  rw [mollifyWith, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply]
  have := integral_sub_left_eq_self (fun t => ρ t • g (x - t)) volume x
  simp only [sub_sub_cancel] at this
  exact this

/-- For scalar `f`, `mollifyWith ρ f = f ⋆ ρ` (kernel on the right). -/
theorem mollifyWith_eq_convolution_right (ρ f : Euc d → ℝ) :
    mollifyWith ρ f = f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ := by
  funext x
  rw [mollifyWith, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]

theorem integrable_mollifyWith_integrand {ρ : Euc d → ℝ} (hρ : Continuous ρ)
    (hρs : HasCompactSupport ρ) {g : Euc d → H} (hg : LocallyIntegrable g) (x : Euc d) :
    Integrable fun t => ρ (x - t) • g t :=
  hg.integrable_smul_left_of_hasCompactSupport (hρ.comp (continuous_const.sub continuous_id))
    (hρs.comp_homeomorph (Homeomorph.subLeft x))

theorem mollifyWith_sub {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hρs : HasCompactSupport ρ)
    {g g' : Euc d → H} (hg : LocallyIntegrable g) (hg' : LocallyIntegrable g') :
    mollifyWith ρ (g - g') = mollifyWith ρ g - mollifyWith ρ g' := by
  funext x
  simp only [mollifyWith, Pi.sub_apply, smul_sub]
  exact integral_sub (integrable_mollifyWith_integrand hρ hρs hg x)
    (integrable_mollifyWith_integrand hρ hρs hg' x)

theorem continuous_mollifyWith {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hρs : HasCompactSupport ρ)
    {g : Euc d → H} (hg : LocallyIntegrable g) : Continuous (mollifyWith ρ g) := by
  rw [mollifyWith_eq_convolution]
  exact hρs.continuous_convolution_left _ hρ hg

theorem contDiff_mollifyWith {n : ℕ∞} {ρ : Euc d → ℝ} (hρ : ContDiff ℝ n ρ)
    (hρs : HasCompactSupport ρ) {g : Euc d → H} (hg : LocallyIntegrable g) :
    ContDiff ℝ n (mollifyWith ρ g) := by
  rw [mollifyWith_eq_convolution]
  exact hρs.contDiff_convolution_left _ hρ hg

theorem support_mollifyWith_subset (ρ : Euc d → ℝ) (g : Euc d → H) :
    Function.support (mollifyWith ρ g) ⊆ Function.support ρ + Function.support g := by
  rw [mollifyWith_eq_convolution]
  exact support_convolution_subset _

/-- `∫ ρ (x - t) dt = 1` (as a lower integral) for a probability density `ρ`. -/
theorem lintegral_ofReal_sub_left_eq_one {ρ : Euc d → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρi : Integrable ρ) (hρ1 : ∫ y, ρ y = 1) (x : Euc d) :
    ∫⁻ t, ENNReal.ofReal (ρ (x - t)) = 1 := by
  rw [lintegral_sub_left_eq_self (fun t => ENNReal.ofReal (ρ t)) x,
    ← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1, ENNReal.ofReal_one]

/-- **Young's inequality** for mollification, `∫⁻` form: `∫ ‖ρ ⋆ g‖^p ≤ ∫ ‖g‖^p` for a continuous
probability density `ρ ≥ 0` and `p > 1`. -/
theorem lintegral_enorm_mollifyWith_rpow_le {g : Euc d → H} (hg : AEStronglyMeasurable g volume)
    {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρi : Integrable ρ)
    (hρ1 : ∫ y, ρ y = 1) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, ‖mollifyWith ρ g x‖ₑ ^ p ≤ ∫⁻ t, ‖g t‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hρm : Measurable fun q : Euc d × Euc d => ENNReal.ofReal (ρ (q.1 - q.2)) :=
    ENNReal.measurable_ofReal.comp (hρ.measurable.comp (measurable_fst.sub measurable_snd))
  have hgm : AEMeasurable (fun q : Euc d × Euc d => ‖g q.2‖ₑ ^ p) (volume.prod volume) :=
    (hg.enorm.pow_const p).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hρint : ∀ t, ∫⁻ x, ENNReal.ofReal (ρ (x - t)) = 1 := by
    intro t
    rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (ρ x)) t,
      ← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1, ENNReal.ofReal_one]
  calc ∫⁻ x, ‖mollifyWith ρ g x‖ₑ ^ p
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖g t‖ₑ ^ p := by
        refine lintegral_mono fun x => ?_
        exact enorm_integral_smul_rpow_le_of_prob hg
          (hρ.measurable.comp (measurable_const.sub measurable_id)).aemeasurable (fun t => hρ0 _)
          (lintegral_ofReal_sub_left_eq_one hρ0 hρi hρ1 x) hp
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ (x - t)) * ‖g t‖ₑ ^ p :=
        lintegral_lintegral_swap (hρm.aemeasurable.mul hgm)
    _ = ∫⁻ t, (∫⁻ x, ENNReal.ofReal (ρ (x - t))) * ‖g t‖ₑ ^ p := by
        refine lintegral_congr fun t => ?_
        exact lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le enorm_ne_top)
    _ = ∫⁻ t, ‖g t‖ₑ ^ p := by
        refine lintegral_congr fun t => ?_
        rw [hρint t, one_mul]

/-- **Young's inequality** for mollification: `‖ρ ⋆ g‖_{L^p} ≤ ‖g‖_{L^p}` for a continuous
probability density `ρ ≥ 0` and `p > 1`. -/
theorem eLpNorm_mollifyWith_le {g : Euc d → H} (hg : AEStronglyMeasurable g volume)
    {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρi : Integrable ρ)
    (hρ1 : ∫ y, ρ y = 1) {p : ℝ} (hp : 1 < p) :
    eLpNorm (mollifyWith ρ g) (ENNReal.ofReal p) ≤ eLpNorm g (ENNReal.ofReal p) := by
  have h := eLpNorm_le_of_lintegral_rpow_le' (μ := volume) (C := 1) (f := mollifyWith ρ g) (g := g)
    (by linarith : 0 < p) (by
      rw [ENNReal.one_rpow, one_mul]
      exact lintegral_enorm_mollifyWith_rpow_le hg hρ hρ0 hρi hρ1 hp)
  rwa [one_mul] at h

/-- The mollification of a bounded function is bounded by the same constant. -/
theorem norm_mollifyWith_le_of_norm_le {g : Euc d → H} {ρ : Euc d → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρi : Integrable ρ) (hρ1 : ∫ y, ρ y = 1) {M : ℝ} (hM : ∀ t, ‖g t‖ ≤ M) (x : Euc d) :
    ‖mollifyWith ρ g x‖ ≤ M := by
  have h1 : Integrable fun t => ρ (x - t) * M := (hρi.comp_sub_left x).mul_const M
  have h2 : ∫ t, ρ (x - t) * M = M := by
    rw [integral_mul_const, integral_sub_left_eq_self ρ volume x, hρ1, one_mul]
  rw [mollifyWith, ← h2]
  refine norm_integral_le_of_norm_le h1 (Eventually.of_forall fun t => ?_)
  rw [norm_smul, Real.norm_of_nonneg (hρ0 _)]
  exact mul_le_mul_of_nonneg_left (hM t) (hρ0 _)

/-! ### Approximation of the identity in `L^p` -/

/-- For continuous compactly supported `v` and bumps with radii `→ 0`, `‖ρ_n ⋆ v − v‖_p → 0`
(uniform bound on a fixed compact plus pointwise convergence, by dominated convergence). -/
theorem tendsto_eLpNorm_mollifyWith_sub_of_continuous [CompleteSpace H]
    {φ : ℕ → ContDiffBump (0 : Euc d)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {v : Euc d → H} (hv : Continuous v)
    (hvs : HasCompactSupport v) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n => eLpNorm (mollifyWith ((φ n).normed volume) v - v) (ENNReal.ofReal p)) atTop
      (𝓝 0) := by
  set ρ : ℕ → Euc d → ℝ := fun n => (φ n).normed volume with hρ_def
  obtain ⟨M, hM⟩ := hv.bounded_above_of_compact_support hvs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R, hR⟩ := hvs.isBounded.subset_closedBall (0 : Euc d)
  set S : Set (Euc d) := Metric.closedBall 0 (R + 1) with hS_def
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hvsupp : Function.support v ⊆ Metric.closedBall 0 R := subset_tsupport v |>.trans hR
  have hev : ∀ᶠ n : ℕ in atTop, (φ n).rOut ≤ 1 :=
    (hφ.eventually (gt_mem_nhds one_pos)).mono fun n h => h.le
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp
  -- pointwise bound and support control, for `rOut n ≤ 1`
  have hbound : ∀ n, (φ n).rOut ≤ 1 → ∀ x,
      ‖mollifyWith (ρ n) v x - v x‖ₑ ^ p ≤ S.indicator (fun _ => ENNReal.ofReal (M + M) ^ p) x := by
    intro n hn x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ hp.le
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (add_le_add ?_ (hM x)))
      exact norm_mollifyWith_le_of_norm_le (φ n).nonneg_normed (φ n).integrable_normed
        (φ n).integral_normed hM x
    · rw [Set.indicator_of_notMem hx]
      have h1 : mollifyWith (ρ n) v x = 0 := by
        by_contra h
        have hmem := support_mollifyWith_subset (ρ n) v h
        obtain ⟨a, ha, b, hb, rfl⟩ := hmem
        have ha' : ‖a‖ < (φ n).rOut := by
          have ha2 : a ∈ Function.support ((φ n).normed volume) := ha
          rw [ContDiffBump.support_normed_eq] at ha2
          simpa using ha2
        have hb' : ‖b‖ ≤ R := by simpa using hvsupp hb
        apply hx
        simp only [hS_def, Metric.mem_closedBall, dist_zero_right]
        calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
          _ ≤ R + 1 := by linarith
      have h2 : v x = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun h => hx ?_
        have := hR h
        simp only [hS_def, Metric.mem_closedBall, dist_zero_right] at this ⊢
        linarith
      simp [h1, h2, hp]
  have hfin : ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal (M + M) ^ p) x ≠ ⊤ := by
    rw [lintegral_indicator_const hSm]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      measure_closedBall_lt_top.ne
  have hmeas : ∀ n, Measurable fun x => ‖mollifyWith (ρ n) v x - v x‖ₑ ^ p := fun n =>
    (ENNReal.continuous_rpow_const.comp
      ((continuous_mollifyWith (φ n).continuous_normed (φ n).hasCompactSupport_normed
        (hv.integrable_of_hasCompactSupport hvs).locallyIntegrable).sub hv).enorm).measurable
  have hlim : ∀ x, Tendsto (fun n => ‖mollifyWith (ρ n) v x - v x‖ₑ ^ p) atTop (𝓝 0) := by
    intro x
    have h1 : Tendsto (fun n => mollifyWith (ρ n) v x) atTop (𝓝 (v x)) := by
      simp only [hρ_def, mollifyWith_eq_convolution]
      exact ContDiffBump.convolution_tendsto_right_of_continuous hφ hv x
    have h2 : Tendsto (fun n => mollifyWith (ρ n) v x - v x) atTop (𝓝 0) := by
      simpa using h1.sub_const (v x)
    have h3 : Tendsto (fun n => ‖mollifyWith (ρ n) v x - v x‖ₑ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto (0 : H)).comp h2
    have h4 := (ENNReal.continuous_rpow_const (y := p)).tendsto 0 |>.comp h3
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos hp] using h4
  have hDCT := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun n x => ‖mollifyWith (ρ n) v x - v x‖ₑ ^ p) (f := fun _ => 0)
    (S.indicator fun _ => ENNReal.ofReal (M + M) ^ p) (Eventually.of_forall hmeas)
    (hev.mono fun n hn => Eventually.of_forall (hbound n hn)) hfin
    (Eventually.of_forall hlim)
  simp only [lintegral_zero] at hDCT
  have h := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0 |>.comp hDCT
  rw [ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / p)] at h
  refine h.congr fun n => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  rfl

/-- **Approximation of the identity in `L^p`**: for bumps with radii `→ 0` and `g ∈ L^p`,
`1 < p`, `‖ρ_n ⋆ g − g‖_{L^p} → 0`. -/
theorem tendsto_eLpNorm_mollifyWith_sub [CompleteSpace H] {φ : ℕ → ContDiffBump (0 : Euc d)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {p : ℝ} (hp : 1 < p) {g : Euc d → H}
    (hg : MemLp g (ENNReal.ofReal p)) :
    Tendsto (fun n => eLpNorm (mollifyWith ((φ n).normed volume) g - g) (ENNReal.ofReal p)) atTop
      (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hgl : LocallyIntegrable g := hg.locallyIntegrable hp1
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδ : ε / 2 / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne').ne'
  obtain ⟨v, hvs, hgv, hv, -⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofReal_ne_top hδ
  have hvl : LocallyIntegrable v := (hv.integrable_of_hasCompactSupport hvs).locallyIntegrable
  have h3 := tendsto_eLpNorm_mollifyWith_sub_of_continuous hφ hv hvs (p := p) (by linarith)
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 h3) (ε / 2) hε2] with n hn
  have hρc : Continuous ((φ n).normed volume) := (φ n).continuous_normed
  have hρs : HasCompactSupport ((φ n).normed volume) := (φ n).hasCompactSupport_normed
  have hm1 : AEStronglyMeasurable (mollifyWith ((φ n).normed volume) (g - v)) volume :=
    (continuous_mollifyWith hρc hρs (hgl.sub hvl)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (mollifyWith ((φ n).normed volume) v - v) volume :=
    ((continuous_mollifyWith hρc hρs hvl).sub hv).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (v - g) volume := hv.aestronglyMeasurable.sub hg.1
  have hdecomp : mollifyWith ((φ n).normed volume) g - g =
      mollifyWith ((φ n).normed volume) (g - v) +
        ((mollifyWith ((φ n).normed volume) v - v) + (v - g)) := by
    rw [mollifyWith_sub hρc hρs hgl hvl]
    abel
  have e1 : eLpNorm (mollifyWith ((φ n).normed volume) (g - v)) (ENNReal.ofReal p) ≤ ε / 2 / 2 :=
    (eLpNorm_mollifyWith_le (hg.1.sub hv.aestronglyMeasurable) hρc (φ n).nonneg_normed
      (φ n).integrable_normed (φ n).integral_normed hp).trans hgv
  have e3 : eLpNorm (v - g) (ENNReal.ofReal p) ≤ ε / 2 / 2 := by
    rw [eLpNorm_sub_comm]
    exact hgv
  rw [hdecomp]
  refine ((eLpNorm_add_le hm1 (hm2.add hm3) hp1).trans
    (add_le_add le_rfl (eLpNorm_add_le hm2 hm3 hp1))).trans ?_
  refine (add_le_add e1 (add_le_add hn e3)).trans (le_of_eq ?_)
  rw [add_comm (ε / 2) (ε / 2 / 2), ← add_assoc, ENNReal.add_halves, ENNReal.add_halves]

/-- The mollification of an `L^p` function by a normalized bump is in `L^p` (Young). -/
theorem memLp_mollifyWith_normed {p : ℝ} (hp : 1 < p) {g : Euc d → H}
    (hg : MemLp g (ENNReal.ofReal p)) (φ : ContDiffBump (0 : Euc d)) :
    MemLp (mollifyWith (φ.normed volume) g) (ENNReal.ofReal p) :=
  ⟨(continuous_mollifyWith φ.continuous_normed φ.hasCompactSupport_normed
      (hg.locallyIntegrable (ENNReal.one_le_ofReal.2 hp.le))).aestronglyMeasurable,
    (eLpNorm_mollifyWith_le hg.1 φ.continuous_normed φ.nonneg_normed φ.integrable_normed
      φ.integral_normed hp).trans_lt hg.2⟩

/-! ### Generalized dominated convergence and Nemytskii functionals -/

/-- **Generalized dominated convergence** (Pratt's lemma): if `h n → hLim` a.e., `‖h n‖ ≤ G n` with
`G n → GLim` a.e. and `∫ G n → ∫ GLim` (all `G` integrable), then `∫⁻ ‖h n − hLim‖ₑ → 0`. -/
theorem tendsto_lintegral_enorm_sub_of_dominated {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : ℕ → α → ℝ} {hLim : α → ℝ} {G : ℕ → α → ℝ} {GLim : α → ℝ}
    (hh : ∀ n, AEStronglyMeasurable (h n) μ) (hhLim : AEStronglyMeasurable hLim μ)
    (hG : ∀ n, Integrable (G n) μ) (hGLim : Integrable GLim μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ ≤ G n x) (hboundLim : ∀ᵐ x ∂μ, ‖hLim x‖ ≤ GLim x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 (hLim x)))
    (hGlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 (GLim x)))
    (hGint : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ x, GLim x ∂μ))) :
    Tendsto (fun n => ∫⁻ x, ‖h n x - hLim x‖ₑ ∂μ) atTop (𝓝 0) := by
  set D : ℕ → α → ℝ≥0∞ := fun n x => ENNReal.ofReal (G n x + GLim x - ‖h n x - hLim x‖) with hD
  set A : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ENNReal.ofReal (G n x + GLim x) ∂μ with hA
  set ALim : ℝ≥0∞ := ENNReal.ofReal (∫ x, GLim x ∂μ + ∫ x, GLim x ∂μ) with hALim
  have hsplit : ∀ n, ∀ᵐ x ∂μ, ENNReal.ofReal (G n x + GLim x) = D n x + ‖h n x - hLim x‖ₑ := by
    intro n
    filter_upwards [hbound n, hboundLim] with x h1 h2
    have h3 : ‖h n x - hLim x‖ ≤ G n x + GLim x := (norm_sub_le _ _).trans (add_le_add h1 h2)
    simp only [hD]
    rw [← ofReal_norm, ENNReal.ofReal_sub _ (norm_nonneg _),
      tsub_add_cancel_of_le (ENNReal.ofReal_le_ofReal h3)]
  have hDm : ∀ n, AEMeasurable (D n) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hG n).1.aemeasurable.add hGLim.1.aemeasurable).sub ((hh n).sub hhLim).norm.aemeasurable)
  have hAeq : ∀ n, A n = ∫⁻ x, D n x ∂μ + ∫⁻ x, ‖h n x - hLim x‖ₑ ∂μ := fun n => by
    simp only [hA]
    rw [← lintegral_add_left' (hDm n)]
    exact lintegral_congr_ae (hsplit n)
  have hnn : ∀ n, 0 ≤ᵐ[μ] fun x => G n x + GLim x := fun n => by
    filter_upwards [hbound n, hboundLim] with x h1 h2
    exact add_nonneg ((norm_nonneg _).trans h1) ((norm_nonneg _).trans h2)
  have e1 : ∀ n, A n = ENNReal.ofReal (∫ x, G n x ∂μ + ∫ x, GLim x ∂μ) := fun n => by
    simp only [hA]
    rw [← integral_add (hG n) hGLim]
    exact (ofReal_integral_eq_lintegral_ofReal ((hG n).add hGLim) (hnn n)).symm
  have hAlim : Tendsto A atTop (𝓝 ALim) := by
    have hAfun : A = fun n => ENNReal.ofReal (∫ x, G n x ∂μ + ∫ x, GLim x ∂μ) := funext e1
    rw [hAfun, hALim]
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hGint.add tendsto_const_nhds)
  have hAtop : ALim ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfatou : ALim ≤ liminf (fun n => ∫⁻ x, D n x ∂μ) atTop := by
    have hnnLim : 0 ≤ᵐ[μ] fun x => GLim x + GLim x := by
      filter_upwards [hboundLim] with x h2
      exact add_nonneg ((norm_nonneg _).trans h2) ((norm_nonneg _).trans h2)
    calc ALim = ∫⁻ x, ENNReal.ofReal (GLim x + GLim x) ∂μ := by
          rw [hALim, ← integral_add hGLim hGLim]
          exact ofReal_integral_eq_lintegral_ofReal (hGLim.add hGLim) hnnLim
      _ = ∫⁻ x, liminf (fun n => D n x) atTop ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim, hGlim] with x h1 h2
          have h3 : Tendsto (fun n => G n x + GLim x - ‖h n x - hLim x‖) atTop
              (𝓝 (GLim x + GLim x - ‖hLim x - hLim x‖)) :=
            (h2.add_const _).sub (h1.sub_const _).norm
          have h4 : Tendsto (fun n => D n x) atTop (𝓝 (ENNReal.ofReal (GLim x + GLim x))) := by
            have := (ENNReal.continuous_ofReal.tendsto _).comp h3
            simpa only [Function.comp_def, sub_self, norm_zero, sub_zero] using this
          exact h4.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, D n x ∂μ) atTop := lintegral_liminf_le' hDm
  have hDle : ∀ n, ∫⁻ x, D n x ∂μ ≤ A n := fun n => by rw [hAeq n]; exact le_self_add
  have hDlim : Tendsto (fun n => ∫⁻ x, D n x ∂μ) atTop (𝓝 ALim) := by
    refine tendsto_of_le_liminf_of_limsup_le hfatou ?_
    calc limsup (fun n => ∫⁻ x, D n x ∂μ) atTop ≤ limsup A atTop :=
          limsup_le_limsup (Eventually.of_forall hDle)
      _ = ALim := hAlim.limsup_eq
  have hsub : ∀ n, ∫⁻ x, ‖h n x - hLim x‖ₑ ∂μ = A n - ∫⁻ x, D n x ∂μ := fun n => by
    rw [hAeq n, ENNReal.add_sub_cancel_left]
    exact ne_top_of_le_ne_top (by rw [e1 n]; exact ENNReal.ofReal_ne_top) (hDle n)
  simp_rw [hsub]
  have := ENNReal.Tendsto.sub hAlim hDlim (Or.inl hAtop)
  rwa [tsub_self] at this

omit [NormedSpace ℝ H] in
/-- `‖g n‖_{L^p} → ‖gLim‖_{L^p}` when `g n → gLim` in `L^p` (`1 ≤ p`). -/
theorem tendsto_eLpNorm_of_tendsto_eLpNorm_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : ℕ → α → H} {gLim : α → H} (hg : ∀ n, AEStronglyMeasurable (g n) μ)
    (hgLim : MemLp gLim p μ) (hlim : Tendsto (fun n => eLpNorm (g n - gLim) p μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (g n) p μ) atTop (𝓝 (eLpNorm gLim p μ)) := by
  have hup : ∀ n, eLpNorm (g n) p μ ≤ eLpNorm (g n - gLim) p μ + eLpNorm gLim p μ := fun n => by
    have := eLpNorm_add_le ((hg n).sub hgLim.1) hgLim.1 hp
    simpa only [sub_add_cancel] using this
  have hlow : ∀ n, eLpNorm gLim p μ - eLpNorm (g n - gLim) p μ ≤ eLpNorm (g n) p μ := fun n => by
    rw [tsub_le_iff_left]
    have := eLpNorm_add_le (hgLim.1.sub (hg n)) (hg n) hp
    rw [sub_add_cancel, eLpNorm_sub_comm] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_ hlow hup
  · have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := eLpNorm gLim p μ)) hlim
      (Or.inl hgLim.eLpNorm_ne_top)
    simpa using this
  · simpa using hlim.add (tendsto_const_nhds (x := eLpNorm gLim p μ))

omit [NormedSpace ℝ H] in
/-- **Continuity of Nemytskii functionals on `L^p`**: if `Φ` is continuous with
`‖Φ ξ‖ ≤ C ‖ξ‖^p` and `g n → gLim` in `L^p` (`1 ≤ p`), then `∫ Φ (g n) → ∫ Φ (gLim)`. -/
theorem tendsto_integral_comp_of_tendsto_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ} (hp : 1 ≤ p) {Φ : H → ℝ} (hΦ : Continuous Φ) {C : ℝ}
    (hΦC : ∀ ξ, ‖Φ ξ‖ ≤ C * ‖ξ‖ ^ p) {g : ℕ → α → H} {gLim : α → H}
    (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p) μ) (hgLim : MemLp gLim (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun n => eLpNorm (g n - gLim) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, Φ (g n x) ∂μ) atTop (𝓝 (∫ x, Φ (gLim x) ∂μ)) := by
  have hp0 : 0 < p := by linarith
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hnorm : ∀ {f : α → H}, MemLp f (ENNReal.ofReal p) μ →
      Integrable (fun x => C * ‖f x‖ ^ p) μ := fun hf => by
    have := hf.integrable_norm_rpow hp' ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hp0.le] at this
    exact this.const_mul C
  have hint : ∀ {f : α → H}, MemLp f (ENNReal.ofReal p) μ →
      Integrable (fun x => Φ (f x)) μ := fun hf =>
    (hnorm hf).mono' (hΦ.comp_aestronglyMeasurable hf.1) (Eventually.of_forall fun x => hΦC _)
  have hnormlim : Tendsto (fun n => ∫ x, C * ‖g n x‖ ^ p ∂μ) atTop
      (𝓝 (∫ x, C * ‖gLim x‖ ^ p ∂μ)) := by
    simp_rw [integral_const_mul, integral_norm_rpow_eq hp0 (hg _), integral_norm_rpow_eq hp0 hgLim]
    refine tendsto_const_nhds.mul (((Real.continuous_rpow_const hp0.le).tendsto _).comp ?_)
    exact (ENNReal.tendsto_toReal hgLim.eLpNorm_ne_top).comp
      (tendsto_eLpNorm_of_tendsto_eLpNorm_sub hp1 (fun n => (hg n).1) hgLim hlim)
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hlim' : Tendsto (fun k => eLpNorm (g (ns k) - gLim) (ENNReal.ofReal p) μ) atTop (𝓝 0) :=
    hlim.comp hns
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp' (fun k => (hg (ns k)).1)
    hgLim.1 hlim').exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  refine tendsto_integral_of_L1 _ (hint hgLim).1 (Eventually.of_forall fun k => hint (hg _)) ?_
  refine tendsto_lintegral_enorm_sub_of_dominated (h := fun k x => Φ (g (ns (ms k)) x))
    (hLim := fun x => Φ (gLim x)) (G := fun k x => C * ‖g (ns (ms k)) x‖ ^ p)
    (GLim := fun x => C * ‖gLim x‖ ^ p) (fun k => (hint (hg _)).1) (hint hgLim).1
    (fun k => hnorm (hg _)) (hnorm hgLim) (fun k => Eventually.of_forall fun x => hΦC _)
    (Eventually.of_forall fun x => hΦC _)
    (hae.mono fun x hx => (hΦ.tendsto _).comp hx) (hae.mono fun x hx => ?_)
    (hnormlim.comp (hns.comp hms.tendsto_atTop))
  exact tendsto_const_nhds.mul
    (((Real.continuous_rpow_const hp0.le).tendsto _).comp ((continuous_norm.tendsto _).comp hx))

end Komlos.Literature
