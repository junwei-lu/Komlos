import Komlos.Literature.Sobolev.Defs

/-!
# Campanato's criterion and `C¹` regularity from continuous weak gradients

Real-analysis inputs of the interior `C^{1,α}` step (`holder_gradient_of_continuous` in
`RegularityHolder.lean`) towards Mosconi–Riey–Squassina 2024, Proposition 4.5 (paper Appendix A,
*Eigenfunction inputs*). Nothing here involves the equation.

## Main results

* `norm_mollifyWith_sub_le` — a mollification is `ε`-close to `c` when the function is `ε`-close
  to `c` a.e. on the support ball of the kernel.
* `gradient_mollifyWith_indicator` — the gradient of a mollification is the mollification of a
  *local* weak gradient, near points whose kernel ball stays inside the set.
* `contDiffOn_of_weakGradient` — a function continuous on an open set `U` with a continuous local
  weak gradient `G` is `C¹` on `U` with `∇φ = G` (mollify, then uniform convergence of
  derivatives, `hasFDerivAt_of_tendstoUniformlyOn`).
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff Convolution RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Mollification estimates -/

/-- A mollification `mollifyWith ρ g x` is `ε`-close to `c` if `‖g - c‖ ≤ ε` a.e. on the ball of
radius `δ` around `x`, for a continuous compactly supported probability kernel `ρ` supported in
`ball 0 δ`. -/
theorem norm_mollifyWith_sub_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] {ρ : Euc d → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1) {δ : ℝ}
    (hρδ : Function.support ρ ⊆ Metric.ball 0 δ) {g : Euc d → H} (hg : LocallyIntegrable g)
    {x : Euc d} {c : H} {ε : ℝ} (hε : ∀ᵐ t, t ∈ Metric.ball x δ → ‖g t - c‖ ≤ ε) :
    ‖mollifyWith ρ g x - c‖ ≤ ε := by
  have hi : Integrable fun t => ρ (x - t) • g t := integrable_mollifyWith_integrand hρc hρs hg x
  have hρx : Integrable fun t => ρ (x - t) :=
    (hρc.integrable_of_hasCompactSupport hρs).comp_sub_left x
  have h1 : ∫ t, ρ (x - t) = 1 := by rw [integral_sub_left_eq_self ρ volume x, hρ1]
  have e : mollifyWith ρ g x - c = ∫ t, ρ (x - t) • (g t - c) := by
    simp only [smul_sub]
    rw [integral_sub hi (hρx.smul_const c), integral_smul_const, h1, one_smul, mollifyWith]
  have hb : ∫ t, ρ (x - t) * ε = ε := by rw [integral_mul_const, h1, one_mul]
  rw [e, ← hb]
  refine norm_integral_le_of_norm_le (hρx.mul_const ε) ?_
  filter_upwards [hε] with t ht
  rw [norm_smul, Real.norm_of_nonneg (hρ0 _)]
  by_cases htb : t ∈ Metric.ball x δ
  · exact mul_le_mul_of_nonneg_left (ht htb) (hρ0 _)
  · have h0 : ρ (x - t) = 0 := by
      by_contra hne
      refine htb ?_
      have h2 := hρδ hne
      rw [Metric.mem_ball, dist_zero_right] at h2
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
      exact h2
    rw [h0, zero_mul, zero_mul]

/-- **The gradient of a mollification from a local weak gradient**: if `G` is a weak gradient of
`φ` on the set `U` (tested against smooth functions supported in `U`), `φ` and `G` are
integrable on the measurable set `s`, and the kernel `ρ` is supported in `closedBall 0 δ` with
`closedBall x δ ⊆ s ∩ U`, then `∇(ρ ⋆ 1_s φ)(x) = (ρ ⋆ 1_s G)(x)`. -/
theorem gradient_mollifyWith_indicator {U : Set (Euc d)} {φ : Euc d → ℝ} {G : Euc d → Euc d}
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : Euc d, ∫ x, φ x * fderiv ℝ ψ x v = -∫ x, inner ℝ (G x) v * ψ x)
    {s : Set (Euc d)} (hs : MeasurableSet s) (hφs : IntegrableOn φ s) (hGs : IntegrableOn G s)
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρs : HasCompactSupport ρ) {δ : ℝ}
    (hρδ : tsupport ρ ⊆ Metric.closedBall 0 δ) {x : Euc d}
    (hx : Metric.closedBall x δ ⊆ s ∩ U) :
    gradient (mollifyWith ρ (s.indicator φ)) x = mollifyWith ρ (s.indicator G) x := by
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hfi : Integrable (s.indicator φ) := (integrable_indicator_iff hs).2 hφs
  have hGi : Integrable (s.indicator G) := (integrable_indicator_iff hs).2 hGs
  have hder := hρs.hasFDerivAt_convolution_right (L := L) hfi.locallyIntegrable hρ1 x
  set ψ : Euc d → ℝ := fun t => ρ (x - t) with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := hρ.comp (contDiff_const.sub contDiff_id)
  have hψs : HasCompactSupport ψ := hρs.comp_homeomorph (Homeomorph.subLeft x)
  -- points `t` with `x - t` in the support of `ρ` lie in `closedBall x δ`
  have hmem : ∀ t, x - t ∈ tsupport ρ → t ∈ Metric.closedBall x δ := by
    intro t ht
    have h2 := hρδ ht
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact h2
  have hψsupp : tsupport ψ ⊆ Metric.closedBall x δ := by
    intro t ht
    have h1 : tsupport ψ = (Homeomorph.subLeft x) ⁻¹' tsupport ρ :=
      tsupport_comp_eq_preimage ρ (Homeomorph.subLeft x)
    rw [h1] at ht
    exact hmem t ht
  have hψd : ∀ t v, fderiv ℝ ψ t v = -(fderiv ℝ ρ (x - t) v) := by
    intro t v
    have h : HasFDerivAt ψ ((fderiv ℝ ρ (x - t)).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) t :=
      ((hρ1.differentiable one_ne_zero) (x - t)).hasFDerivAt.comp t
        ((hasFDerivAt_id t).const_sub x)
    rw [h.fderiv]
    simp
  have hgi : Integrable fun t => ρ (x - t) • s.indicator G t :=
    hGi.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hψs
  refine ext_inner_right ℝ fun v => ?_
  rw [mollifyWith_eq_convolution_right, ← fderiv_apply_eq_inner_gradient, hder.fderiv,
    convolution_precompR_apply L hfi.locallyIntegrable (hρs.fderiv (𝕜 := ℝ))
      (hρ1.continuous_fderiv one_ne_zero), convolution_def]
  simp only [hL, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have key := hweak ψ hψ hψs (hψsupp.trans fun t ht => (hx ht).2) v
  have e1 : ∫ t, s.indicator φ t * fderiv ℝ ρ (x - t) v = ∫ t, -(φ t * fderiv ℝ ψ t v) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show s.indicator φ t * fderiv ℝ ρ (x - t) v = -(φ t * fderiv ℝ ψ t v)
    rw [hψd, mul_neg, neg_neg]
    by_cases hts : t ∈ s
    · rw [indicator_of_mem hts]
    · have h0 : fderiv ℝ ρ (x - t) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h =>
          hts (hx (hmem t (tsupport_fderiv_subset ℝ h))).1
      rw [indicator_of_notMem hts, h0]
      simp
  have e2 : ∫ t, inner ℝ (G t) v * ψ t = ∫ t, inner ℝ (s.indicator G t) v * ρ (x - t) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show inner ℝ (G t) v * ρ (x - t) = inner ℝ (s.indicator G t) v * ρ (x - t)
    by_cases hts : t ∈ s
    · rw [indicator_of_mem hts]
    · have h0 : ρ (x - t) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hts (hx (hmem t h)).1
      rw [h0, mul_zero, mul_zero]
  rw [e1, integral_neg, key, neg_neg, e2, mollifyWith, real_inner_comm, ← integral_inner hgi v]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show inner ℝ (s.indicator G t) v * ρ (x - t) = inner ℝ v (ρ (x - t) • s.indicator G t)
  rw [inner_smul_right, real_inner_comm, mul_comm]

/-! ### `C¹` from a continuous weak gradient -/

/-- Eventually the radius `1/(n+1)` of the standard mollifier is below any `δ > 0`. -/
theorem eventually_one_div_lt {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (Nat.one_div_le_one_div hn).trans_lt hN

/-- **Differentiability from a continuous local weak gradient**: if `φ` and `G` are continuous
on the open set `U` and `G` is a weak gradient of `φ` on `U` (tested against smooth functions
supported in `U`), then `φ` has derivative `⟪G x₀, ·⟫` at every `x₀ ∈ U`.

Proof: mollify `1_s φ` on a closed ball `s ∋ x₀` inside `U`; near `x₀` the mollifications
converge uniformly to `φ` and their gradients (`gradient_mollifyWith_indicator`) converge
uniformly to `G` (uniform continuity on `s`, `norm_mollifyWith_sub_le`), so
`hasFDerivAt_of_tendstoUniformlyOn` applies. -/
theorem hasFDerivAt_of_weakGradient {U : Set (Euc d)} (hU : IsOpen U) {φ : Euc d → ℝ}
    {G : Euc d → Euc d} (hφ : ContinuousOn φ U) (hG : ContinuousOn G U)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : Euc d, ∫ x, φ x * fderiv ℝ ψ x v = -∫ x, inner ℝ (G x) v * ψ x)
    {x₀ : Euc d} (hx₀ : x₀ ∈ U) : HasFDerivAt φ (toDual ℝ (Euc d) (G x₀)) x₀ := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set s := Metric.closedBall x₀ (r / 2) with hs_def
  have hsU : s ⊆ U := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrU
  have hsc : IsCompact s := isCompact_closedBall x₀ _
  have hφs : IntegrableOn φ s := (hφ.mono hsU).integrableOn_compact hsc
  have hGs : IntegrableOn G s := (hG.mono hsU).integrableOn_compact hsc
  have hfi : Integrable (s.indicator φ) := (integrable_indicator_iff measurableSet_closedBall).2 hφs
  have hGi : Integrable (s.indicator G) := (integrable_indicator_iff measurableSet_closedBall).2 hGs
  have hφu : UniformContinuousOn φ s := hsc.uniformContinuousOn_of_continuous (hφ.mono hsU)
  have hGu : UniformContinuousOn G s := hsc.uniformContinuousOn_of_continuous (hG.mono hsU)
  set f : ℕ → Euc d → ℝ := fun n => mollifyWith ((mollifierBump (d := d) n).normed volume)
    (s.indicator φ) with hf_def
  have hfc : ∀ n, ContDiff ℝ ∞ (f n) := fun n =>
    contDiff_mollifyWith (n := ⊤) (ContDiffBump.contDiff_normed _)
      (ContDiffBump.hasCompactSupport_normed _) hfi.locallyIntegrable
  have hr4 : 0 < r / 4 := by positivity
  -- the kernel ball around a point of `ball x₀ (r/4)` lies in `s ∩ U`
  have hball : ∀ n : ℕ, 1 / ((n : ℝ) + 1) < r / 4 → ∀ y ∈ Metric.ball x₀ (r / 4),
      Metric.closedBall y (1 / ((n : ℝ) + 1)) ⊆ s ∩ U := by
    intro n hn y hy z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball] at hy
    have hzs : z ∈ s := by
      rw [hs_def, Metric.mem_closedBall]
      linarith [dist_triangle z y x₀]
    exact ⟨hzs, hsU hzs⟩
  have hunif : TendstoUniformlyOn f φ atTop (Metric.ball x₀ (r / 4)) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuousOn_iff.1 hφu (ε / 2) (half_pos hε)
    filter_upwards [eventually_one_div_lt (lt_min hδ hr4)] with n hn y hy
    have hn1 : 1 / ((n : ℝ) + 1) < δ := hn.trans_le (min_le_left _ _)
    have hn2 : 1 / ((n : ℝ) + 1) < r / 4 := hn.trans_le (min_le_right _ _)
    have hys : y ∈ s := (hball n hn2 y hy (Metric.mem_closedBall_self (by positivity))).1
    rw [dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt (norm_mollifyWith_sub_le
      (ContDiffBump.contDiff_normed (n := 0) _).continuous
      (ContDiffBump.hasCompactSupport_normed _) (fun _ => ContDiffBump.nonneg_normed _ _)
      (ContDiffBump.integral_normed _) (ContDiffBump.support_normed_eq _).subset
      hfi.locallyIntegrable (Eventually.of_forall fun t ht => ?_)) (half_lt_self hε)
    have hts : t ∈ s := (hball n hn2 y hy (Metric.ball_subset_closedBall ht)).1
    rw [indicator_of_mem hts, ← dist_eq_norm]
    exact (hδφ t hts y hys (lt_trans (Metric.mem_ball.1 ht) hn1)).le
  have hunif' : TendstoUniformlyOn (fun n y => fderiv ℝ (f n) y)
      (fun y => toDual ℝ (Euc d) (G y)) atTop (Metric.ball x₀ (r / 4)) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1 hGu (ε / 2) (half_pos hε)
    filter_upwards [eventually_one_div_lt (lt_min hδ hr4)] with n hn y hy
    have hn1 : 1 / ((n : ℝ) + 1) < δ := hn.trans_le (min_le_left _ _)
    have hn2 : 1 / ((n : ℝ) + 1) < r / 4 := hn.trans_le (min_le_right _ _)
    have hys : y ∈ s := (hball n hn2 y hy (Metric.mem_closedBall_self (by positivity))).1
    have hgrad : gradient (f n) y =
        mollifyWith ((mollifierBump (d := d) n).normed volume) (s.indicator G) y :=
      gradient_mollifyWith_indicator hweak measurableSet_closedBall hφs hGs
        (ContDiffBump.contDiff_normed _) (ContDiffBump.hasCompactSupport_normed _)
        (ContDiffBump.tsupport_normed_eq _).subset (hball n hn2 y hy)
    rw [← toDual_gradient, hgrad, LinearIsometryEquiv.dist_map, dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt (norm_mollifyWith_sub_le
      (ContDiffBump.contDiff_normed (n := 0) _).continuous
      (ContDiffBump.hasCompactSupport_normed _) (fun _ => ContDiffBump.nonneg_normed _ _)
      (ContDiffBump.integral_normed _) (ContDiffBump.support_normed_eq _).subset
      hGi.locallyIntegrable (Eventually.of_forall fun t ht => ?_)) (half_lt_self hε)
    have hts : t ∈ s := (hball n hn2 y hy (Metric.ball_subset_closedBall ht)).1
    rw [indicator_of_mem hts, ← dist_eq_norm]
    exact (hδG t hts y hys (lt_trans (Metric.mem_ball.1 ht) hn1)).le
  exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hunif'
    (fun n y _ => ((hfc n).differentiable (by simp) y).hasFDerivAt)
    (fun y hy => hunif.tendsto_at hy) (Metric.mem_ball_self hr4)

/-- **`C¹` from a continuous local weak gradient**: a function continuous on the open set `U`
whose weak gradient on `U` (tested against smooth functions supported in `U`) is continuous on
`U` is `C¹` on `U`, with classical gradient `G`. -/
theorem contDiffOn_of_weakGradient {U : Set (Euc d)} (hU : IsOpen U) {φ : Euc d → ℝ}
    {G : Euc d → Euc d} (hφ : ContinuousOn φ U) (hG : ContinuousOn G U)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : Euc d, ∫ x, φ x * fderiv ℝ ψ x v = -∫ x, inner ℝ (G x) v * ψ x) :
    ContDiffOn ℝ 1 φ U ∧ ∀ x ∈ U, gradient φ x = G x := by
  have hd : ∀ x ∈ U, HasFDerivAt φ (toDual ℝ (Euc d) (G x)) x := fun x hx =>
    hasFDerivAt_of_weakGradient hU hφ hG hweak hx
  have hgrad : ∀ x ∈ U, gradient φ x = G x := fun x hx => by
    unfold gradient
    rw [(hd x hx).fderiv, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨?_, hgrad⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm,
    contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,
    fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  exact ((toDual ℝ (Euc d)).continuous.comp_continuousOn hG).congr fun x hx => (hd x hx).fderiv


/-! ### Classical versus weak gradients -/

/-- A function continuous on an open set `U` whose topological support lies in `U` is
continuous. -/
theorem continuous_of_continuousOn_of_tsupport_subset {X E : Type*} [TopologicalSpace X]
    [TopologicalSpace E] [Zero E] {f : X → E} {U : Set X} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hfU : tsupport f ⊆ U) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.continuousAt (hU.mem_nhds hx)
  · have h : (fun _ => (0 : E)) =ᶠ[𝓝 x] f :=
      (notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hfU h)).symm
    exact continuousAt_const.congr h

/-- **Integration by parts on an open set**: if `φ` is `C¹` on an open set `U` and `ψ` is a `C¹`
compactly supported function with `tsupport ψ ⊆ U`, then `∫ φ ∂_v ψ = -∫ (∂_v φ) ψ`. Only `ψ`
needs to be differentiable outside `U`, so no cutoff of `φ` is required. -/
theorem integral_mul_fderiv_eq_neg_of_contDiffOn {U : Set (Euc d)} (hU : IsOpen U)
    {φ : Euc d → ℝ} (hφ : ContDiffOn ℝ 1 φ U) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψs : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (v : Euc d) :
    ∫ x, φ x * fderiv ℝ ψ x v = -∫ x, fderiv ℝ φ x v * ψ x := by
  have hφc : ContinuousOn φ U := hφ.continuousOn
  have hDφ : ContinuousOn (fun x => fderiv ℝ φ x v) U :=
    (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hDψ : Continuous fun x => fderiv ℝ ψ x v :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsDψ : tsupport (fun x => fderiv ℝ ψ x v) ⊆ tsupport ψ :=
    (tsupport_comp_subset (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp) (fderiv ℝ ψ)).trans
      (tsupport_fderiv_subset ℝ)
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · refine Continuous.integrable_of_hasCompactSupport ?_ hψs.mul_left
    exact continuous_of_continuousOn_of_tsupport_subset hU (hDφ.mul hψ.continuous.continuousOn)
      (tsupport_mul_subset_right.trans hψU)
  · refine Continuous.integrable_of_hasCompactSupport ?_ (hψs.fderiv_apply ℝ v).mul_left
    exact continuous_of_continuousOn_of_tsupport_subset hU (hφc.mul hDψ.continuousOn)
      (tsupport_mul_subset_right.trans (hsDψ.trans hψU))
  · refine Continuous.integrable_of_hasCompactSupport ?_ hψs.mul_left
    exact continuous_of_continuousOn_of_tsupport_subset hU (hφc.mul hψ.continuous.continuousOn)
      (tsupport_mul_subset_right.trans hψU)
  · exact fun x hx => (hφ.differentiableOn one_ne_zero x (hψU hx)).differentiableAt
      (hU.mem_nhds (hψU hx))
  · exact fun x _ => hψ.differentiable one_ne_zero x

/-- **The classical gradient of a `C¹` representative is the weak gradient** on an open set: if
`φ =ᵐ u`, `g` is a weak gradient of `u`, and `φ` is `C¹` on an open set `U`, then `∇φ = g` almost
everywhere on `U`. -/
theorem ae_gradient_eq_of_hasWeakGradient {u φ : Euc d → ℝ} {g : Euc d → Euc d}
    (hg : HasWeakGradient u g) (hφu : φ =ᵐ[volume] u) {U : Set (Euc d)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 1 φ U) : ∀ᵐ x, x ∈ U → gradient φ x = g x := by
  have hGc : ContinuousOn (gradient φ) U :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hφ.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hloc : LocallyIntegrableOn (fun x => g x - gradient φ x) U volume :=
    (hg.locallyIntegrable_grad.locallyIntegrableOn U).sub
      (hGc.locallyIntegrableOn hU.measurableSet)
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [key] with x hx hxU
    exact (sub_eq_zero.1 (hx hxU)).symm
  intro ψ hψ hψs hψU
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have i1 : Integrable fun x => ψ x • g x :=
    hg.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport hψ.continuous hψs
  have i2 : Integrable fun x => ψ x • gradient φ x := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hψs.smul_right
    exact continuous_of_continuousOn_of_tsupport_subset hU (hψ.continuous.continuousOn.smul hGc)
      ((tsupport_smul_subset_left _ _).trans hψU)
  show ∫ x, ψ x • (g x - gradient φ x) = 0
  simp only [smul_sub]
  rw [integral_sub i1 i2, sub_eq_zero]
  refine ext_inner_left ℝ fun v => ?_
  rw [← integral_inner i1 v, ← integral_inner i2 v]
  have h1 := hg.integral_mul_fderiv ψ hψ hψs v
  have h2 := integral_mul_fderiv_eq_neg_of_contDiffOn hU hφ hψ1 hψs hψU v
  have h3 : ∫ x, u x * fderiv ℝ ψ x v = ∫ x, φ x * fderiv ℝ ψ x v :=
    integral_congr_ae (hφu.mono fun x hx => by simp only [hx])
  have e : ∀ h : Euc d → Euc d,
      (fun x => ⟪v, ψ x • h x⟫) = fun x => ⟪h x, v⟫ * ψ x := fun h => by
    funext x
    rw [inner_smul_right, real_inner_comm, mul_comm]
  rw [e g, e (gradient φ)]
  simp only [fderiv_apply_eq_inner_gradient φ] at h2
  linarith

/-! ### `C¹` from Hölder bounds on difference quotients -/

/-- **Dyadic difference quotients converge uniformly** under a Hölder bound on second differences:
if `|(G(y + s e) - G y) - (G(z + s e) - G z)| ≤ C s ‖y - z‖^α` for `0 < s ≤ ρ` and
`y, z ∈ ball x ρ`, with `‖e‖ = 1`, then the difference quotients `(G(y + s_n e) - G y)/s_n`,
`s_n = ρ/2^{n+2}`, converge uniformly on `ball x (ρ/2)`: consecutive quotients differ by at most
`(C/2) s_{n+1}^α`. -/
theorem exists_tendstoUniformlyOn_difference_quotient {x e : Euc d} (he : ‖e‖ = 1) {ρ C α : ℝ}
    (hρ : 0 < ρ) (hα : 0 < α) {G : Euc d → ℝ}
    (hq : ∀ s : ℝ, 0 < s → s ≤ ρ → ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
      |(G (y + s • e) - G y) - (G (z + s • e) - G z)| ≤ C * s * dist y z ^ α) :
    ∃ H : Euc d → ℝ, TendstoUniformlyOn
      (fun (n : ℕ) y => (G (y + (ρ / 2 ^ (n + 2)) • e) - G y) / (ρ / 2 ^ (n + 2))) H atTop
      (Metric.ball x (ρ / 2)) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Euc d → ℝ,
      D = fun n y => (G (y + (ρ / 2 ^ (n + 2)) • e) - G y) / (ρ / 2 ^ (n + 2)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ α := by positivity
  have hq1 : (1 / 2 : ℝ) ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max C 0 / 2 * (ρ / 8) ^ α := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    positivity
  have hstep : ∀ y ∈ Metric.ball x (ρ / 2), ∀ n : ℕ,
      dist (D n y) (D (n + 1) y) ≤ c * ((1 / 2 : ℝ) ^ α) ^ n := by
    intro y hy n
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ρ / 8 * (1 / 2) ^ n := ⟨_, rfl⟩
    have hσ0 : 0 < σ := by
      rw [hσ]
      positivity
    have hσ8 : σ ≤ ρ / 8 := by
      rw [hσ]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    have e0 : ρ / 8 * (1 / 2) ^ n = ρ / 2 ^ (n + 3) := by
      rw [one_div_pow, pow_add]
      field_simp
      norm_num
    have e1 : ρ / 2 ^ (n + 1 + 2) = σ := by
      rw [hσ, e0, show n + 1 + 2 = n + 3 by ring]
    have e2 : ρ / 2 ^ (n + 2) = 2 * σ := by
      have h23 : (2 : ℝ) ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
      rw [hσ, e0, h23, ← mul_div_assoc, mul_div_mul_left _ _ two_ne_zero]
    have hy' : y ∈ Metric.ball x ρ := Metric.ball_subset_ball (by linarith) hy
    have hyσ : y + σ • e ∈ Metric.ball x ρ := by
      rw [Metric.mem_ball] at hy ⊢
      calc dist (y + σ • e) x ≤ dist (y + σ • e) y + dist y x := dist_triangle _ _ _
        _ = σ + dist y x := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
              Real.norm_of_nonneg hσ0.le]
        _ < ρ := by linarith
    have h := hq σ hσ0 (by linarith) (y + σ • e) hyσ y hy'
    have hdist : dist (y + σ • e) y = σ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_of_nonneg hσ0.le]
    rw [hdist] at h
    have e3 : y + σ • e + σ • e = y + (2 * σ) • e := by
      rw [add_assoc, ← add_smul, two_mul]
    rw [e3] at h
    have hpow : σ ^ α = (ρ / 8) ^ α * ((1 / 2 : ℝ) ^ α) ^ n := by
      rw [hσ, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
        mul_comm (n : ℝ) α]
    rw [hD, Real.dist_eq]
    simp only
    rw [e1, e2]
    have e4 : (G (y + (2 * σ) • e) - G y) / (2 * σ) - (G (y + σ • e) - G y) / σ =
        ((G (y + (2 * σ) • e) - G (y + σ • e)) - (G (y + σ • e) - G y)) / (2 * σ) := by
      field_simp
      ring
    rw [e4, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * σ), div_le_iff₀ (by positivity)]
    calc |(G (y + (2 * σ) • e) - G (y + σ • e)) - (G (y + σ • e) - G y)|
        ≤ C * σ * σ ^ α := h
      _ ≤ max C 0 * σ * σ ^ α := by
          gcongr
          exact le_max_left _ _
      _ = c * ((1 / 2 : ℝ) ^ α) ^ n * (2 * σ) := by
          rw [hc, hpow]
          ring
  choose! H hH using fun y (hy : y ∈ Metric.ball x (ρ / 2)) =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ c hq1 (hstep y hy))
  refine ⟨H, Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  have hlim : Tendsto (fun n : ℕ => c * ((1 / 2 : ℝ) ^ α) ^ n / (1 - (1 / 2 : ℝ) ^ α)) atTop
      (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul c).div_const
      (1 - (1 / 2 : ℝ) ^ α)
    simpa using h
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn y hy
  rw [dist_comm]
  have h := dist_le_of_le_geometric_of_tendsto _ c hq1 (hstep y hy) (hH y hy) n
  rw [hD] at h
  exact h.trans_lt hn

/-! ### Campanato's criterion -/

section Campanato

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The measure of a closed ball in `ℝ^d`: `|B(x, r)| = r^d |B(0, 1)|`. -/
theorem volume_real_closedBall (x : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall x r) =
      r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) := by
  rw [measureReal_def, measureReal_def, Measure.addHaar_closedBall' volume x hr,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr d)]

theorem volume_real_closedBall_pos : 0 < volume.real (Metric.closedBall (0 : Euc d) 1) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume 0 one_pos).ne'
    measure_closedBall_lt_top.ne

/-- The distance of an average over `s` to a constant `m` is at most `|s|⁻¹ ∫_t ‖g - m‖` for
`s ⊆ t`. -/
theorem norm_setAverage_sub_le {s t : Set (Euc d)} (hs0 : volume s ≠ 0) (hsfin : volume s ≠ ⊤)
    (hst : s ⊆ t) (htfin : volume t ≠ ⊤) {g : Euc d → E} (hgt : IntegrableOn g t) (m : E) :
    ‖(⨍ y in s, g y) - m‖ ≤ (volume.real s)⁻¹ * ∫ y in t, ‖g y - m‖ := by
  have hgs : IntegrableOn g s := hgt.mono_set hst
  have hreal : 0 < volume.real s := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hs0 hsfin
  have e : (⨍ y in s, g y) - m = (volume.real s)⁻¹ • ∫ y in s, (g y - m) := by
    rw [setAverage_eq, integral_sub hgs (integrableOn_const hsfin), setIntegral_const, smul_sub,
      smul_smul, inv_mul_cancel₀ hreal.ne', one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hreal.le)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_)
    (inv_nonneg.2 hreal.le)
  exact setIntegral_mono_set (hgt.sub (integrableOn_const htfin)).norm
    (Eventually.of_forall fun _ => norm_nonneg _) hst.eventuallyLE

/-- **One Campanato step**: if `∫_{B(x,t)} ‖g - m‖ ≤ C t^{d+α}` and `B(z,s) ⊆ B(x,t)` with
`t ≤ 2s`, then the average of `g` over `B(z,s)` is within `C 2^d |B₁|⁻¹ t^α` of `m`. -/
theorem norm_setAverage_sub_le_of_campanato {g : Euc d → E} (hg : LocallyIntegrable g)
    {x z : Euc d} {s t C α : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ 2 * s)
    (hsub : Metric.closedBall z s ⊆ Metric.closedBall x t) (hC : 0 ≤ C) {m : E}
    (hm : ∫ y in Metric.closedBall x t, ‖g y - m‖ ≤ C * t ^ ((d : ℝ) + α)) :
    ‖(⨍ y in Metric.closedBall z s, g y) - m‖ ≤
      C * 2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1) * t ^ α := by
  have hω := volume_real_closedBall_pos (d := d)
  have hvol := volume_real_closedBall z hs.le
  have h1 := norm_setAverage_sub_le (Metric.measure_closedBall_pos volume z hs).ne'
    measure_closedBall_lt_top.ne hsub measure_closedBall_lt_top.ne
    (hg.integrableOn_isCompact (isCompact_closedBall x t)) m
  have hpow : t ^ ((d : ℝ) + α) = t ^ d * t ^ α := by rw [Real.rpow_add ht, Real.rpow_natCast]
  have htd : t ^ d ≤ 2 ^ d * s ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ ht.le hts d
  calc ‖(⨍ y in Metric.closedBall z s, g y) - m‖
      ≤ (volume.real (Metric.closedBall z s))⁻¹ * ∫ y in Metric.closedBall x t, ‖g y - m‖ := h1
    _ ≤ (s ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))⁻¹ *
          (C * (2 ^ d * s ^ d * t ^ α)) := by
        rw [hvol]
        refine mul_le_mul_of_nonneg_left (hm.trans ?_) (by positivity)
        rw [hpow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htd (Real.rpow_nonneg ht.le _)) hC
    _ = C * 2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1) * t ^ α := by
        field_simp

/-- **Campanato chain along concentric balls**: under Campanato bounds at the points of `S` on all
scales `≤ R₀`, `‖avg_{B(x,s)} g - avg_{B(x,t)} g‖ ≤ B t^α` for `x ∈ S` and `0 < s ≤ t ≤ R₀`, with
`B` independent of `x`, `s`, `t` (induction on the number of halvings from `t` to `s`). -/
theorem exists_norm_setAverage_sub_setAverage_le {g : Euc d → E} (hg : LocallyIntegrable g)
    {S : Set (Euc d)} {α C R₀ : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hcamp : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ →
      ∃ m : E, ∫ y in Metric.closedBall x r, ‖g y - m‖ ≤ C * r ^ ((d : ℝ) + α)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ R₀ →
      ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖ ≤ B * t ^ α := by
  have hω := volume_real_closedBall_pos (d := d)
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ,
      C₁ = C * 2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    positivity
  have h2α : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow one_lt_two hα
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * C₁ * 2 ^ α / (2 ^ α - 1) := ⟨_, rfl⟩
  have hB2 : 2 * C₁ ≤ B := by
    rw [hB, le_div_iff₀ (by linarith)]
    nlinarith
  have hB0 : 0 ≤ B := by linarith
  have hBq : B / 2 ^ α + 2 * C₁ = B := by
    have h2 : (2 : ℝ) ^ α - 1 ≠ 0 := by linarith
    have h3 : (2 : ℝ) ^ α ≠ 0 := by positivity
    rw [hB]
    field_simp
    ring
  refine ⟨B, hB0, fun x hx => ?_⟩
  -- comparable radii
  have hnear : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 2 * s → t ≤ R₀ →
      ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖ ≤
        2 * C₁ * t ^ α := by
    intro s t hs hst hts htR
    have ht : 0 < t := hs.trans_le hst
    obtain ⟨m, hm⟩ := hcamp x hx t ht htR
    have h1 := norm_setAverage_sub_le_of_campanato hg hs ht hts
      (Metric.closedBall_subset_closedBall hst) hC hm
    have h2 := norm_setAverage_sub_le_of_campanato hg ht ht (by linarith) subset_rfl hC hm
    rw [← hC₁] at h1 h2
    calc ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖
        = ‖((⨍ y in Metric.closedBall x s, g y) - m) -
            ((⨍ y in Metric.closedBall x t, g y) - m)‖ := by
          congr 1
          abel
      _ ≤ ‖(⨍ y in Metric.closedBall x s, g y) - m‖ +
            ‖(⨍ y in Metric.closedBall x t, g y) - m‖ := norm_sub_le _ _
      _ ≤ C₁ * t ^ α + C₁ * t ^ α := add_le_add h1 h2
      _ = 2 * C₁ * t ^ α := by ring
  have hind : ∀ k : ℕ, ∀ t : ℝ, 0 < t → t ≤ R₀ → ∀ s : ℝ, t / 2 ^ k ≤ s → s ≤ t →
      ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖ ≤
        B * t ^ α := by
    intro k
    induction k with
    | zero =>
      intro t ht htR s hs hst
      have hst' : s = t := le_antisymm hst (by simpa using hs)
      rw [hst', sub_self, norm_zero]
      exact mul_nonneg hB0 (Real.rpow_nonneg ht.le _)
    | succ k ih =>
      intro t ht htR s hs hst
      have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
      by_cases h2 : t ≤ 2 * s
      · exact (hnear s t hs0 hst h2 htR).trans
          (mul_le_mul_of_nonneg_right hB2 (Real.rpow_nonneg ht.le _))
      · push Not at h2
        have hs' : t / 2 / 2 ^ k ≤ s := by
          rw [div_div, ← pow_succ']
          exact hs
        have h1 := ih (t / 2) (by positivity) (by linarith) s hs' (by linarith)
        have h3 := hnear (t / 2) t (by positivity) (by linarith) (by linarith) htR
        have e : (t / 2) ^ α = t ^ α / 2 ^ α := Real.div_rpow ht.le zero_le_two α
        calc ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖
            ≤ ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x (t / 2), g y‖ +
                ‖(⨍ y in Metric.closedBall x (t / 2), g y) -
                  ⨍ y in Metric.closedBall x t, g y‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ B * (t / 2) ^ α + 2 * C₁ * t ^ α := add_le_add h1 h3
          _ = (B / 2 ^ α + 2 * C₁) * t ^ α := by rw [e]; ring
          _ = B * t ^ α := by rw [hBq]
  intro s t hs hst htR
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t / 2 ^ k ≤ s := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (t / s) one_lt_two
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hs] at hk
    rw [div_le_iff₀ (by positivity)]
    linarith
  exact hind k t (hs.trans_le hst) htR s hk hst

/-- For `α > 0`, `B ≥ 0`, `R > 0`, `ε > 0` there is `t ∈ (0, R]` with `B t^α < ε`. -/
theorem exists_pos_le_mul_rpow_lt {α B R ε : ℝ} (hα : 0 < α) (hB : 0 ≤ B) (hR : 0 < R)
    (hε : 0 < ε) : ∃ t : ℝ, 0 < t ∧ t ≤ R ∧ B * t ^ α < ε := by
  have hq : 0 < ε / (B + 1) := div_pos hε (by linarith)
  refine ⟨min R ((ε / (B + 1)) ^ α⁻¹), lt_min hR (Real.rpow_pos_of_pos hq _),
    min_le_left _ _, ?_⟩
  have h1 : (min R ((ε / (B + 1)) ^ α⁻¹)) ^ α ≤ ε / (B + 1) := by
    calc (min R ((ε / (B + 1)) ^ α⁻¹)) ^ α ≤ ((ε / (B + 1)) ^ α⁻¹) ^ α :=
          Real.rpow_le_rpow (lt_min hR (Real.rpow_pos_of_pos hq _)).le (min_le_right _ _) hα.le
      _ = ε / (B + 1) := Real.rpow_inv_rpow hq.le hα.ne'
  calc B * (min R ((ε / (B + 1)) ^ α⁻¹)) ^ α ≤ B * (ε / (B + 1)) :=
        mul_le_mul_of_nonneg_left h1 hB
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Campanato's criterion** (Campanato 1963; Giaquinta, *Multiple integrals in the calculus of
variations and nonlinear elliptic systems*, Theorem III.1.2): if a locally integrable `g` has mean
oscillation `∫_{B(x,r)} ‖g - m_{x,r}‖ ≤ C r^{d+α}` on the balls of radius `r ≤ R₀` centred in a
compact set `S ⊆ U` (constants depending on `S`), then the limits of the averages of `g` over
shrinking balls define a representative of `g` on the open set `U` (Lebesgue differentiation)
that is continuous on `U` and Hölder continuous on every compact subset of `U`. -/
theorem exists_holder_of_campanato {U : Set (Euc d)} (hU : IsOpen U) {g : Euc d → E}
    (hg : LocallyIntegrable g)
    (hcamp : ∀ S : Set (Euc d), IsCompact S → S ⊆ U → ∃ α C R₀ : ℝ, 0 < α ∧ 0 < R₀ ∧
      ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ m : E, ∫ y in Metric.closedBall x r, ‖g y - m‖ ≤ C * r ^ ((d : ℝ) + α)) :
    ∃ G : Euc d → E, G =ᵐ[volume.restrict U] g ∧ ContinuousOn G U ∧
      ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
        ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r G S := by
  have hω := volume_real_closedBall_pos (d := d)
  -- nonnegative constants
  have hcamp' : ∀ S : Set (Euc d), IsCompact S → S ⊆ U → ∃ α C R₀ : ℝ, 0 < α ∧ 0 ≤ C ∧
      0 < R₀ ∧ ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ m : E, ∫ y in Metric.closedBall x r, ‖g y - m‖ ≤ C * r ^ ((d : ℝ) + α) := by
    intro S hS hSU
    obtain ⟨α, C, R₀, hα, hR₀, h⟩ := hcamp S hS hSU
    refine ⟨α, max C 0, R₀, hα, le_max_right _ _, hR₀, fun x hx r hr hrR => ?_⟩
    obtain ⟨m, hm⟩ := h x hx r hr hrR
    exact ⟨m, hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hr.le _))⟩
  obtain ⟨a, ha⟩ : ∃ a : Euc d → ℕ → E,
      a = fun x (n : ℕ) => ⨍ y in Metric.closedBall x (1 / ((n : ℝ) + 1)), g y := ⟨_, rfl⟩
  -- the averages at scale `1/(n+1)` are eventually close to the average at scale `t`
  have hclose : ∀ (S : Set (Euc d)) (α R₀ B : ℝ), (∀ x ∈ S, ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ R₀ →
      ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖ ≤ B * t ^ α) →
      ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ R₀ → ∀ᶠ n in atTop,
        ‖a x n - ⨍ y in Metric.closedBall x t, g y‖ ≤ B * t ^ α := by
    intro S α R₀ B hB x hx t ht htR
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt ht
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [ha]
    exact hB x hx _ t (by positivity) ((Nat.one_div_le_one_div hn).trans hN.le) htR
  -- convergence of the averages
  have hconv : ∀ x ∈ U, ∃ L, Tendsto (a x) atTop (𝓝 L) := by
    intro x hx
    obtain ⟨α, C, R₀, hα, hC, hR₀, h⟩ := hcamp' {x} isCompact_singleton
      (singleton_subset_iff.2 hx)
    obtain ⟨B, hB0, hB⟩ := exists_norm_setAverage_sub_setAverage_le hg hα hC h
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨t, ht, htR, htε⟩ :=
      exists_pos_le_mul_rpow_lt hα (by positivity : (0 : ℝ) ≤ 2 * B) hR₀ hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hclose {x} α R₀ B hB x rfl t ht htR)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖a x n - a x N‖
        ≤ ‖a x n - ⨍ y in Metric.closedBall x t, g y‖ +
            ‖(⨍ y in Metric.closedBall x t, g y) - a x N‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖a x n - ⨍ y in Metric.closedBall x t, g y‖ +
            ‖a x N - ⨍ y in Metric.closedBall x t, g y‖ := by rw [norm_sub_rev _ (a x N)]
      _ ≤ B * t ^ α + B * t ^ α := add_le_add (hN n hn) (hN N le_rfl)
      _ = 2 * B * t ^ α := by ring
      _ < ε := htε
  obtain ⟨G, hG⟩ : ∃ G : Euc d → E, G = fun x => limUnder atTop (a x) := ⟨_, rfl⟩
  have hGlim : ∀ x ∈ U, Tendsto (a x) atTop (𝓝 (G x)) := fun x hx => by
    rw [hG]
    exact tendsto_nhds_limUnder (hconv x hx)
  -- Hölder continuity on compact sets
  have hholder : ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
      ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r G S := by
    intro S hS hSU
    obtain ⟨α, C, R₀, hα, hC, hR₀, h⟩ := hcamp' S hS hSU
    obtain ⟨B, hB0, hB⟩ := exists_norm_setAverage_sub_setAverage_le hg hα hC h
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ,
        C₁ = C * 2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1) := ⟨_, rfl⟩
    have hC₁0 : 0 ≤ C₁ := by
      rw [hC₁]
      positivity
    have hGavg : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ R₀ →
        ‖G x - ⨍ y in Metric.closedBall x t, g y‖ ≤ B * t ^ α := fun x hx t ht htR =>
      le_of_tendsto (((hGlim x (hSU hx)).sub_const _).norm) (hclose S α R₀ B hB x hx t ht htR)
    -- a bound for `G` on `S`
    obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ y in Metric.cthickening R₀ S, ‖g y‖ := ⟨_, rfl⟩
    have hI0 : 0 ≤ I := by
      rw [hI]
      exact integral_nonneg fun y => norm_nonneg (g y)
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M =
        (R₀ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))⁻¹ * I + B * R₀ ^ α :=
      ⟨_, rfl⟩
    have hM0 : 0 ≤ M := by
      rw [hM]
      positivity
    have hGM : ∀ x ∈ S, ‖G x‖ ≤ M := by
      intro x hx
      have h1 := hGavg x hx R₀ hR₀ le_rfl
      have h2 := norm_setAverage_sub_le (Metric.measure_closedBall_pos volume x hR₀).ne'
        measure_closedBall_lt_top.ne (Metric.closedBall_subset_cthickening hx R₀)
        hS.cthickening.measure_lt_top.ne (hg.integrableOn_isCompact hS.cthickening) (0 : E)
      simp only [sub_zero] at h2
      rw [volume_real_closedBall x hR₀.le, ← hI] at h2
      calc ‖G x‖ = ‖(G x - ⨍ y in Metric.closedBall x R₀, g y) +
            ⨍ y in Metric.closedBall x R₀, g y‖ := by rw [sub_add_cancel]
        _ ≤ ‖G x - ⨍ y in Metric.closedBall x R₀, g y‖ +
            ‖⨍ y in Metric.closedBall x R₀, g y‖ := norm_add_le _ _
        _ ≤ B * R₀ ^ α + (R₀ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))⁻¹ * I :=
            add_le_add h1 h2
        _ = M := by rw [hM]; ring
    obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = (2 * B + 2 * C₁) * 2 ^ α + 2 * M * (2 / R₀) ^ α :=
      ⟨_, rfl⟩
    have hKc0 : 0 ≤ Kc := by
      rw [hKc]
      positivity
    have hbound : ∀ x ∈ S, ∀ y ∈ S, ‖G x - G y‖ ≤ Kc * dist x y ^ α := by
      intro x hx y hy
      rcases (dist_nonneg : 0 ≤ dist x y).eq_or_lt with h0 | hpos
      · rw [← h0, Real.zero_rpow hα.ne', mul_zero, dist_eq_zero.1 h0.symm, sub_self, norm_zero]
      rcases le_or_gt (2 * dist x y) R₀ with hle | hgt
      · have h2δ : 0 < 2 * dist x y := by positivity
        obtain ⟨m, hm⟩ := h x hx (2 * dist x y) h2δ hle
        have h1 := hGavg x hx (2 * dist x y) h2δ hle
        have h2 := hGavg y hy (dist x y) hpos (by linarith)
        have hsub : Metric.closedBall y (dist x y) ⊆ Metric.closedBall x (2 * dist x y) := by
          intro z hz
          rw [Metric.mem_closedBall] at hz ⊢
          linarith [dist_triangle z y x, dist_comm x y]
        have h3 := norm_setAverage_sub_le_of_campanato hg h2δ h2δ (by linarith) subset_rfl hC hm
        have h4 := norm_setAverage_sub_le_of_campanato hg hpos h2δ le_rfl hsub hC hm
        rw [← hC₁] at h3 h4
        have hδα : dist x y ^ α ≤ (2 * dist x y) ^ α :=
          Real.rpow_le_rpow dist_nonneg (by linarith) hα.le
        have e2 : (2 * dist x y) ^ α = 2 ^ α * dist x y ^ α :=
          Real.mul_rpow zero_le_two dist_nonneg
        have hKc' : (2 * B + 2 * C₁) * 2 ^ α ≤ Kc := by
          rw [hKc]
          exact le_add_of_nonneg_right (by positivity)
        calc ‖G x - G y‖
            = ‖((G x - ⨍ z in Metric.closedBall x (2 * dist x y), g z) +
                ((⨍ z in Metric.closedBall x (2 * dist x y), g z) - m)) -
                (((⨍ z in Metric.closedBall y (dist x y), g z) - m) +
                  (G y - ⨍ z in Metric.closedBall y (dist x y), g z))‖ := by
              congr 1
              abel
          _ ≤ (‖G x - ⨍ z in Metric.closedBall x (2 * dist x y), g z‖ +
                ‖(⨍ z in Metric.closedBall x (2 * dist x y), g z) - m‖) +
                (‖(⨍ z in Metric.closedBall y (dist x y), g z) - m‖ +
                  ‖G y - ⨍ z in Metric.closedBall y (dist x y), g z‖) :=
              (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
          _ ≤ (B * (2 * dist x y) ^ α + C₁ * (2 * dist x y) ^ α) +
                (C₁ * (2 * dist x y) ^ α + B * dist x y ^ α) :=
              add_le_add (add_le_add h1 h3) (add_le_add h4 h2)
          _ ≤ (2 * B + 2 * C₁) * (2 * dist x y) ^ α := by nlinarith
          _ = (2 * B + 2 * C₁) * 2 ^ α * dist x y ^ α := by rw [e2]; ring
          _ ≤ Kc * dist x y ^ α :=
              mul_le_mul_of_nonneg_right hKc' (Real.rpow_nonneg dist_nonneg _)
      · have h1 : 1 ≤ (2 * dist x y / R₀) ^ α :=
          Real.one_le_rpow ((one_le_div hR₀).2 hgt.le) hα.le
        have e : (2 * dist x y / R₀) ^ α = (2 / R₀) ^ α * dist x y ^ α := by
          rw [← Real.mul_rpow (div_pos two_pos hR₀).le dist_nonneg]
          congr 1
          ring
        have hKc' : 2 * M * (2 / R₀) ^ α ≤ Kc := by
          rw [hKc]
          exact le_add_of_nonneg_left (by positivity)
        calc ‖G x - G y‖ ≤ ‖G x‖ + ‖G y‖ := norm_sub_le _ _
          _ ≤ 2 * M := by linarith [hGM x hx, hGM y hy]
          _ ≤ 2 * M * (2 * dist x y / R₀) ^ α := le_mul_of_one_le_right (by positivity) h1
          _ = 2 * M * (2 / R₀) ^ α * dist x y ^ α := by rw [e]; ring
          _ ≤ Kc * dist x y ^ α :=
              mul_le_mul_of_nonneg_right hKc' (Real.rpow_nonneg dist_nonneg _)
    refine ⟨Real.toNNReal Kc, Real.toNNReal α, Real.toNNReal_pos.2 hα, fun x hx y hy => ?_⟩
    have e1 : ((Real.toNNReal Kc : NNReal) : ℝ≥0∞) = ENNReal.ofReal Kc := rfl
    rw [edist_dist, edist_dist, Real.coe_toNNReal _ hα.le, e1,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le, ← ENNReal.ofReal_mul hKc0]
    exact ENNReal.ofReal_le_ofReal (by rw [dist_eq_norm]; exact hbound x hx y hy)
  have hcont : ContinuousOn G U := fun x hx => by
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨C, r, hr, hC⟩ := hholder (Metric.closedBall x (ρ / 2)) (isCompact_closedBall x _)
      ((Metric.closedBall_subset_ball (by linarith)).trans hρU)
    exact (((hC.continuousOn hr) x (Metric.mem_closedBall_self (by linarith))).continuousAt
      (Metric.closedBall_mem_nhds x (by linarith))).continuousWithinAt
  refine ⟨G, ?_, hcont, hholder⟩
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average volume hg 1
  rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards [hleb] with x hx hxU
  have h1 : Tendsto (a x) atTop (𝓝 (g x)) := by
    rw [ha]
    exact hx (fun _ => x) (fun n : ℕ => 1 / ((n : ℝ) + 1))
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩)
      (Eventually.of_forall fun n => Metric.mem_closedBall_self (by
        rw [one_mul]; positivity))
  exact tendsto_nhds_unique (hGlim x hxU) h1

end Campanato

end Komlos.Literature
