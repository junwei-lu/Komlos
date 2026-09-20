import Komlos.Literature.PLaplacian.FluxMonotone

/-!
# Local Sobolev cutoffs for the difference-quotient argument

The homogeneous Caccioppoli argument is local. Its Sobolev test construction therefore needs
cutoffs of a potential and its gradient, rather than global `L^p` hypotheses on either field.
The lemmas here isolate that localization from the nonlinear equation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-- A bounded scalar multiplier supported in `S` needs only `L^p` data on `S`. -/
theorem memLp_smul_of_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : ℝ≥0∞} {S : Set (Euc d)} (hS : MeasurableSet S)
    {G : Euc d → E} (hG : MemLp G q (volume.restrict S)) {η : Euc d → ℝ}
    (hη : AEStronglyMeasurable η volume) (hηS : tsupport η ⊆ S) {A : ℝ}
    (hA : ∀ x, |η x| ≤ A) : MemLp (fun x => η x • G x) q volume := by
  have hGi : MemLp (S.indicator G) q volume := (memLp_indicator_iff_restrict hS).mpr hG
  have heq : (fun x => η x • S.indicator G x) = fun x => η x • G x := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hηS h))]
      simp
  rw [← heq]
  refine hGi.of_le_mul (c := A) (hη.smul hGi.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)

/-- A bounded vector multiplier supported in `S` needs only local scalar `L^p` data. -/
theorem memLp_smul_of_right_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : ℝ≥0∞} {S : Set (Euc d)} (hS : MeasurableSet S)
    {v : Euc d → ℝ} (hv : MemLp v q (volume.restrict S)) {H : Euc d → E}
    (hH : AEStronglyMeasurable H volume) (hHS : tsupport H ⊆ S) {B : ℝ}
    (hB : ∀ x, ‖H x‖ ≤ B) : MemLp (fun x => v x • H x) q volume := by
  have hvi : MemLp (S.indicator v) q volume := (memLp_indicator_iff_restrict hS).mpr hv
  have heq : (fun x => S.indicator v x • H x) = fun x => v x • H x := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hHS h))]
      simp
  rw [← heq]
  refine hvi.of_le_mul (c := B) (hvi.aestronglyMeasurable.smul hH)
    (Eventually.of_forall fun x => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

/-- The weak product rule localizes a Sobolev potential whenever the potential and gradient
are `L^p` on the cutoff support. No global `L^p` hypothesis is required. -/
theorem HasWeakGradient.memW0_cutoff {p : ℝ} {v : Euc d → ℝ} {G : Euc d → Euc d}
    (hvG : HasWeakGradient v G) {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η)
    (hv : MemLp v (ENNReal.ofReal p) (volume.restrict (tsupport η)))
    (hG : MemLp G (ENNReal.ofReal p) (volume.restrict (tsupport η))) {A B : ℝ}
    (hA : ∀ x, |η x| ≤ A) (hB : ∀ x, ‖gradient η x‖ ≤ B) :
    MemW0 p (tsupport η) (fun x => η x * v x) ∧
      HasWeakGradient (fun x => η x * v x)
        (fun x => η x • G x + v x • gradient η x) := by
  have hηm : AEStronglyMeasurable η volume := hη.continuous.aestronglyMeasurable
  have hDηm : AEStronglyMeasurable (gradient η) volume :=
    (continuous_gradient (hη.of_le (by simp))).aestronglyMeasurable
  have hDηs : tsupport (gradient η) ⊆ tsupport η := by
    refine closure_minimal ?_ (isClosed_tsupport η)
    intro x hx
    by_contra hn
    exact hx (gradient_eq_zero_of_notMem_tsupport hn)
  have hprod := hvG.contDiff_mul hη
  refine ⟨⟨?_, ?_, ⟨_, hprod, ?_⟩⟩, hprod⟩
  · exact memLp_smul_of_tsupport_subset (isClosed_tsupport η).measurableSet hv hηm
      Subset.rfl hA
  · exact Eventually.of_forall fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · exact memLp_add_fun
      (memLp_smul_of_tsupport_subset (isClosed_tsupport η).measurableSet hG hηm Subset.rfl hA)
      (memLp_smul_of_right_tsupport_subset (isClosed_tsupport η).measurableSet hv hDηm
        hDηs hB)

/-- A globally differentiable potential with a locally integrable classical gradient has that
gradient distributionally. Integration by parts requires integrability, not a continuous
gradient. -/
theorem hasWeakGradient_of_differentiable_of_locallyIntegrable_gradient {v : Euc d → ℝ}
    (hv : Differentiable ℝ v) (hG : LocallyIntegrable (gradient v)) :
    HasWeakGradient v (gradient v) where
  locallyIntegrable := hv.continuous.locallyIntegrable
  locallyIntegrable_grad := hG
  integral_mul_fderiv ψ hψ hψs e := by
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hDψ : Continuous fun x => fderiv ℝ ψ x e :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hi₁ : Integrable fun x => fderiv ℝ v x e * ψ x := by
      have hinner := (hG.integrable_smul_left_of_hasCompactSupport hψ.continuous hψs).inner_const
        (𝕜 := ℝ) e
      simpa only [fderiv_apply_eq_inner_gradient, real_inner_smul_left, mul_comm] using hinner
    have hi₂ : Integrable fun x => v x * fderiv ℝ ψ x e :=
      (hv.continuous.mul hDψ).integrable_of_hasCompactSupport (hψs.fderiv_apply ℝ e).mul_left
    have hi₃ : Integrable fun x => v x * ψ x :=
      (hv.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψs.mul_left
    have heq := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e)
      (f := v) (g := ψ) hi₁ hi₂ hi₃ (fun x _ => hv x)
      (fun x _ => hψ1.differentiable one_ne_zero x)
    simpa only [fderiv_apply_eq_inner_gradient] using heq

/-- Local classical differentiability and local `p`-energy suffice to cut a potential off
into `W₀^{1,p}`. No continuity of the gradient or behavior of the potential outside `U` is
required. The displayed field is the weak gradient of the localized potential. -/
theorem memW0_cutoff_of_differentiableOn {p : ℝ} (hp : 1 ≤ p)
    {U : Set (Euc d)} (hU : IsOpen U) {v : Euc d → ℝ} {G : Euc d → Euc d}
    (hvG : ∀ x ∈ U, DifferentiableAt ℝ v x ∧ gradient v x = G x)
    (hG : MemLp G (ENNReal.ofReal p) (volume.restrict U))
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) {A : ℝ} (hA : ∀ x, |η x| ≤ A) :
    MemW0 p (tsupport η) (fun x => η x * v x) ∧
      HasWeakGradient (fun x => η x * v x)
        (fun x => η x • G x + v x • gradient η x) := by
  have hηd : Differentiable ℝ η := (hη.of_le (by simp) : ContDiff ℝ 1 η).differentiable one_ne_zero
  have hvs : HasCompactSupport (fun x => η x * v x) := hηs.mul_right
  have hdiff : Differentiable ℝ (fun x => η x * v x) := by
    intro x
    by_cases hx : x ∈ U
    · exact (hηd x).mul (hvG x hx).1
    · have hxη : x ∉ tsupport η := fun h => hx (hηU h)
      refine ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).congr_of_eventuallyEq ?_).differentiableAt
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxη] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
  have hvc : ContinuousOn v U := fun x hx => (hvG x hx).1.continuousAt.continuousWithinAt
  have hDηc : Continuous (gradient η) := continuous_gradient (hη.of_le (by simp))
  have hvDηs : tsupport (fun x => v x • gradient η x) ⊆ tsupport η := by
    refine closure_minimal ?_ (isClosed_tsupport η)
    intro x hx
    by_contra hn
    apply hx
    change v x • gradient η x = 0
    rw [gradient_eq_zero_of_notMem_tsupport hn, smul_zero]
  have hvDηc : Continuous (fun x => v x • gradient η x) :=
    continuous_of_continuousOn_of_tsupport_subset hU (hvc.smul hDηc.continuousOn)
      (hvDηs.trans hηU)
  have hvDηcs : HasCompactSupport (fun x => v x • gradient η x) :=
    hηs.of_isClosed_subset (isClosed_tsupport _) hvDηs
  have hgrad : gradient (fun x => η x * v x) = fun x => η x • G x + v x • gradient η x := by
    funext x
    by_cases hx : x ∈ U
    · rw [gradient_mul_apply (hηd x) (hvG x hx).1, (hvG x hx).2]
    · have hxη : x ∉ tsupport η := fun h => hx (hηU h)
      rw [gradient_eq_zero_of_notMem_tsupport
        (fun h => hxη (tsupport_mul_subset_left h)),
        image_eq_zero_of_notMem_tsupport hxη, gradient_eq_zero_of_notMem_tsupport hxη]
      simp
  have hgradLp : MemLp (gradient (fun x => η x * v x)) (ENNReal.ofReal p) := by
    rw [hgrad]
    exact memLp_add_fun
      (memLp_smul_of_tsupport_subset hU.measurableSet hG
        hη.continuous.aestronglyMeasurable hηU hA)
      (hvDηc.memLp_of_hasCompactSupport hvDηcs)
  have hweak := hasWeakGradient_of_differentiable_of_locallyIntegrable_gradient hdiff
    (hgradLp.locallyIntegrable (ENNReal.one_le_ofReal.mpr hp))
  refine ⟨⟨hdiff.continuous.memLp_of_hasCompactSupport hvs, ?_,
    ⟨_, hweak, hgradLp⟩⟩, ?_⟩
  · exact Eventually.of_forall fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · rwa [hgrad] at hweak

/-- On a smaller ball, mollification only sees the gradient inside the larger ball when
the kernel radius fits in the intervening gap. -/
theorem mollifyWith_normed_indicator_eq_on_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : Euc d → E} (φ : ContDiffBump (0 : Euc d))
    {x₀ : Euc d} {r R : ℝ} (hφ : φ.rOut < R - r) {x : Euc d}
    (hx : x ∈ Metric.ball x₀ r) :
    mollifyWith (φ.normed volume) ((Metric.ball x₀ R).indicator G) x =
      mollifyWith (φ.normed volume) G x := by
  unfold mollifyWith
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  by_cases hxy : φ.normed volume (x - y) = 0
  · simp only [hxy, zero_smul]
  · have hxy' : x - y ∈ Function.support (φ.normed volume) := hxy
    rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at hxy'
    have hy : y ∈ Metric.ball x₀ R := by
      rw [Metric.mem_ball]
      have hdist : dist y x < φ.rOut := by
        rwa [dist_comm, dist_eq_norm]
      have hx' := Metric.mem_ball.mp hx
      have htri := dist_triangle y x x₀
      linarith
    simp only [indicator_of_mem hy]

/-- Finite `p`-oscillation on a nonzero finite measure space implies `L^p` membership.
Choosing one finite slice fixes the additive constant without requiring an `L^p` mean bound. -/
theorem memLp_of_lintegral_lintegral_sub_rpow_lt_top {p : ℝ} (hp : 0 < p)
    {μ : Measure (Euc d)} [IsFiniteMeasure μ] [NeZero μ] {v : Euc d → ℝ}
    (hv : AEStronglyMeasurable v μ)
    (hfin : (∫⁻ x, ∫⁻ y, ‖v y - v x‖ₑ ^ p ∂μ ∂μ) < ⊤) :
    MemLp v (ENNReal.ofReal p) μ := by
  have hmeas : AEMeasurable (fun x => ∫⁻ y, ‖v y - v x‖ₑ ^ p ∂μ) μ := by
    have hprod : AEMeasurable (fun q : Euc d × Euc d => ‖v q.2 - v q.1‖ₑ ^ p)
        (μ.prod μ) :=
      (hv.aemeasurable.comp_snd.sub hv.aemeasurable.comp_fst).enorm.pow_const p
    exact hprod.lintegral_prod_right'
  obtain ⟨x, hx⟩ := (ae_lt_top' hmeas hfin.ne).exists
  have hsub : MemLp (fun y => v y - v x) (ENNReal.ofReal p) μ := by
    refine ⟨hv.sub aestronglyMeasurable_const, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hx.ne
  have hsum := hsub.add (memLp_const (v x) : MemLp (fun _ : Euc d => v x)
    (ENNReal.ofReal p) μ)
  exact hsum.ae_eq (Eventually.of_forall fun y => by simp)

/-- Finite local `p`-energy of a weak gradient implies local `L^p` membership of its
potential. Mollification and the double-integral Poincaré estimate give a finite oscillation
integral; Fatou's lemma and a finite slice then fix the additive constant. -/
theorem HasWeakGradient.memLp_restrict_ball {p : ℝ} (hp : 1 < p)
    {v : Euc d → ℝ} {G : Euc d → Euc d} (hvG : HasWeakGradient v G)
    {x₀ : Euc d} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hG : MemLp G (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))) :
    MemLp v (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ r)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let B := Metric.ball x₀ r
  let Gc := (Metric.ball x₀ R).indicator G
  have hGc : MemLp Gc (ENNReal.ofReal p) :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr hG
  let u : ℕ → Euc d → ℝ := fun n => mollifyWith ((mollifierBump n).normed volume) v
  have huc : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    (contDiff_mollifyWith (n := ⊤) (ContDiffBump.contDiff_normed _)
      (mollifierBump n).hasCompactSupport_normed hvG.locallyIntegrable).of_le
      (by exact_mod_cast le_top)
  have hug : ∀ n, gradient (u n) = mollifyWith ((mollifierBump n).normed volume) G :=
    fun n => gradient_mollifyWith hvG (ContDiffBump.contDiff_normed _)
      (mollifierBump n).hasCompactSupport_normed
  have hae : ∀ᵐ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)) := by
    filter_upwards [ae_tendsto_convolution_stdBump hvG.locallyIntegrable] with x hx
    exact hx.congr fun n => by simp only [u, mollifyWith_eq_convolution_right]
  let J : ℝ≥0∞ := ∫⁻ z, ‖Gc z‖ₑ ^ p
  have hJ : J ≠ ⊤ := by
    dsimp [J]
    rw [lintegral_enorm_rpow_eq_eLpNorm_rpow hp0]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le hGc.eLpNorm_ne_top
  let C : ℝ≥0∞ := 2 ^ d * ENNReal.ofReal (2 * r) ^ p * volume B
  have hC : C ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
        (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)) measure_ball_lt_top.ne
  have hsmall : ∀ᶠ n : ℕ in atTop, (mollifierBump (d := d) n).rOut < R - r :=
    (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 _ (sub_pos.mpr hrR)
  have hgrad_bound : ∀ᶠ n : ℕ in atTop, ∫⁻ z in B, ‖gradient (u n) z‖ₑ ^ p ≤ J := by
    filter_upwards [hsmall] with n hn
    calc ∫⁻ z in B, ‖gradient (u n) z‖ₑ ^ p =
        ∫⁻ z in B, ‖mollifyWith ((mollifierBump n).normed volume) Gc z‖ₑ ^ p := by
          apply setLIntegral_congr_fun measurableSet_ball
          intro z hz
          rw [hug n]
          exact congrArg (fun ξ : Euc d => ‖ξ‖ₑ ^ p)
            (mollifyWith_normed_indicator_eq_on_ball (mollifierBump n) hn hz).symm
      _ ≤ ∫⁻ z, ‖mollifyWith ((mollifierBump n).normed volume) Gc z‖ₑ ^ p :=
        setLIntegral_le_lintegral _ _
      _ ≤ J := lintegral_enorm_mollifyWith_rpow_le hGc.aestronglyMeasurable
        (mollifierBump n).continuous_normed (mollifierBump n).nonneg_normed
        (mollifierBump n).integrable_normed (mollifierBump n).integral_normed hp
  have hdiam : ∀ x ∈ B, ∀ y ∈ B, ‖y - x‖ ≤ 2 * r := by
    intro x hx y hy
    have hx' := Metric.mem_ball.mp hx
    have hy' := Metric.mem_ball.mp hy
    have htri := dist_triangle y x₀ x
    rw [dist_comm x₀ x] at htri
    rw [← dist_eq_norm]
    linarith
  have hsmooth : ∀ᶠ n : ℕ in atTop,
      ∫⁻ x in B, ∫⁻ y in B, ‖u n y - u n x‖ₑ ^ p ≤ C * J := by
    filter_upwards [hgrad_bound] with n hn
    exact (lintegral_lintegral_sub_rpow_le_of_contDiff hp (huc n)
      (convex_ball x₀ r) measurableSet_ball hdiam).trans (mul_le_mul_right hn C)
  have hinner : ∀ᵐ x, ∫⁻ y in B, ‖v y - v x‖ₑ ^ p ≤
      liminf (fun n => ∫⁻ y in B, ‖u n y - u n x‖ₑ ^ p) atTop := by
    filter_upwards [hae] with x hx
    have hae' : ∀ᵐ y ∂(volume.restrict B), ‖v y - v x‖ₑ ^ p =
        liminf (fun n => ‖u n y - u n x‖ₑ ^ p) atTop := by
      filter_upwards [ae_restrict_of_ae hae] with y hy
      have h₁ := hy.sub hx
      have h₂ : Tendsto (fun n => ‖u n y - u n x‖ₑ ^ p) atTop
          (𝓝 (‖v y - v x‖ₑ ^ p)) :=
        (ENNReal.continuous_rpow_const.tendsto _).comp
          ((continuous_enorm.tendsto _).comp h₁)
      exact h₂.liminf_eq.symm
    rw [lintegral_congr_ae hae']
    refine lintegral_liminf_le fun n => ?_
    exact (ENNReal.continuous_rpow_const.comp
      (continuous_enorm.comp ((huc n).continuous.sub continuous_const))).measurable
  have hmeasF : ∀ n, Measurable fun x => ∫⁻ y in B, ‖u n y - u n x‖ₑ ^ p := fun n => by
    have hc : Continuous fun q : Euc d × Euc d => ‖u n q.2 - u n q.1‖ₑ ^ p :=
      ENNReal.continuous_rpow_const.comp (continuous_enorm.comp
        (((huc n).continuous.comp continuous_snd).sub ((huc n).continuous.comp continuous_fst)))
    exact hc.measurable.lintegral_prod_right'
  have hosc : (∫⁻ x in B, ∫⁻ y in B, ‖v y - v x‖ₑ ^ p) ≤ C * J := by
    refine (lintegral_mono_ae (ae_restrict_of_ae hinner)).trans ?_
    refine (lintegral_liminf_le hmeasF).trans ?_
    simpa using (liminf_le_liminf hsmooth)
  haveI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  haveI : NeZero (volume.restrict B) := ⟨by
    intro he
    have hzero : volume B = 0 := by
      simpa using congrArg (fun μ : Measure (Euc d) => μ Set.univ) he
    exact (Metric.measure_ball_pos volume x₀ hr).ne' hzero⟩
  exact memLp_of_lintegral_lintegral_sub_rpow_lt_top hp0
    (hvG.locallyIntegrable.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
    (hosc.trans_lt (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hC hJ)))

end Komlos.Literature
