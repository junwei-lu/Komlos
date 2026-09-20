import Komlos.Literature.PLaplacian.SmoothStrictNorm
import Komlos.Literature.PLaplacian.RegularityHolder

/-!
# Auxiliary material for the assembly of paper Appendix A

* `IsSmoothStrictNorm.add_le`, `lipschitzWith`, `norm_gradient_le`: a smooth strictly convex norm
  is subadditive and Lipschitz, so `∇F` is bounded;
* `IsSmoothStrictNorm.inner_gradient_self` (Euler's identity `⟪∇F(ξ), ξ⟫ = F(ξ)`),
  `inner_flux_self` (`⟪a(ξ), ξ⟫ = F(ξ)^p`), `norm_flux_le`, `measurable_flux`;
* `trunc`: the smooth truncation `Θ(r) = r · T(r - 1)` (`T` the smooth transition), with `Θ = 0`
  on `(-∞, 1]`, `Θ = id` on `[2, ∞)`, `0 ≤ Θ ≤ id` on `[0, ∞)`, and a bounded derivative;
* `truncS`: its rescaling `θ_s(r) = s Θ(r/s)`, used to truncate `U` near its zero set;
* `exists_mollifier_seq`: mollification of `C¹` compactly supported functions (bump convolution),
  with uniform convergence of the functions and their gradients;
* `lambdaGen_le_rayleighGen_of_contDiff_one`, `weak_ineq_of_contDiff_one`: density of smooth
  test functions for the Rayleigh quotient and for weak inequalities;
* `weak_ineq_of_off_critical`: the cutoff across a compact convex critical set (paper Appendix A,
  *Including the critical set*), with the smooth cutoff family `exists_cutoff_family` (a
  hand-scaled bump convolved with an indicator) and the convex parallel-body volume estimate
  `exists_volume_annulus_le` (dilation if `C` has interior, compression along a normal otherwise);
* `integral_inner_gradient_eq_neg_integral_divergence` (integration by parts on `ℝ^d`),
  `eq_zero_of_integral_mul_testFn_eq_zero` (fundamental lemma of the calculus of variations),
  `EigenfunctionData.divergence_flux_gradient_add_eq_zero` (the strong form
  `div a(∇u) + λ u^{p-1} = 0` on `{∇u ≠ 0}`).

This file contains no `sorry`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Smooth strictly convex norms: Lipschitz bounds and Euler's identity -/

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- Subadditivity (the triangle inequality), from convexity and homogeneity. -/
theorem add_le (x y : Euc d) : F (x + y) ≤ F x + F y := by
  have h := hF.convexOn.2 (mem_univ x) (mem_univ y) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have h2 : F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) = 1 / 2 * F (x + y) := by
    rw [← smul_add, hF.homog, abs_of_pos (by norm_num)]
  simp only [smul_eq_mul] at h
  linarith

/-- `|F x - F y| ≤ F (x - y)`. -/
theorem abs_sub_le (x y : Euc d) : |F x - F y| ≤ F (x - y) := by
  have h1 := hF.add_le (x - y) y
  have h2 := hF.add_le (y - x) x
  rw [sub_add_cancel] at h1 h2
  have h3 : F (y - x) = F (x - y) := by rw [← neg_sub x y, hF.even]
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- `F` is Lipschitz. -/
theorem lipschitzWith : ∃ M : NNReal, LipschitzWith M F := by
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  refine ⟨⟨max M 0, le_max_right _ _⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  calc |F x - F y| ≤ F (x - y) := hF.abs_sub_le x y
    _ ≤ M * ‖x - y‖ := hM _
    _ ≤ max M 0 * ‖x - y‖ := by gcongr; exact le_max_left _ _

/-- `∇F` is bounded (by the Lipschitz constant). -/
theorem norm_gradient_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ, ‖gradient F ξ‖ ≤ M := by
  obtain ⟨M, hM⟩ := hF.lipschitzWith
  refine ⟨M, M.coe_nonneg, fun ξ => ?_⟩
  by_cases hd : DifferentiableAt ℝ F ξ
  · have := hd.hasFDerivAt.le_of_lipschitz hM
    rwa [gradient, LinearIsometryEquiv.norm_map]
  · rw [gradient_eq_zero_of_not_differentiableAt hd, norm_zero]
    exact M.coe_nonneg

/-- **Euler's identity** for the `1`-homogeneous `F`: `⟪∇F(ξ), ξ⟫ = F(ξ)`. -/
theorem inner_gradient_self (ξ : Euc d) : ⟪gradient F ξ, ξ⟫ = F ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [hF.map_zero]
  have hd : HasFDerivAt F (fderiv ℝ F ξ) ξ :=
    ((hF.contDiffAt hξ).differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun c : ℝ => c • ξ) ξ 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const ξ
  have h1 : HasDerivAt (fun c : ℝ => F (c • ξ)) (fderiv ℝ F ξ ξ) 1 :=
    hd.comp_hasDerivAt_of_eq (1 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun c : ℝ => F (c • ξ)) (F ξ) 1 := by
    have heq : (fun c : ℝ => c * F ξ) =ᶠ[𝓝 (1 : ℝ)] fun c => F (c • ξ) := by
      filter_upwards [eventually_gt_nhds zero_lt_one] with c hc
      rw [hF.homog, abs_of_pos hc]
    have := ((hasDerivAt_id (1 : ℝ)).mul_const (F ξ)).congr_of_eventuallyEq heq.symm
    simpa using this
  rw [inner_gradient_left]
  exact h1.unique h2

/-- `⟪a(ξ), ξ⟫ = F(ξ)^p` for the flux `a(ξ) = F(ξ)^{p-1} ∇F(ξ)`. -/
theorem inner_flux_self {p : ℝ} (hp : 1 < p) (ξ : Euc d) : ⟪flux p F ξ, ξ⟫ = F ξ ^ p := by
  rw [flux, real_inner_smul_left, hF.inner_gradient_self]
  rcases eq_or_ne (F ξ) 0 with h | h
  · rw [h, Real.zero_rpow (by linarith : p - 1 ≠ 0), Real.zero_rpow (by linarith : p ≠ 0),
      mul_zero]
  · rw [← Real.rpow_add_one h, sub_add_cancel]

/-- `‖a(ξ)‖ ≤ C ‖ξ‖^{p-1}`. -/
theorem norm_flux_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ‖flux p F ξ‖ ≤ C * ‖ξ‖ ^ (p - 1) := by
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  obtain ⟨G, hG0, hG⟩ := hF.norm_gradient_le
  have hp1 : 0 ≤ p - 1 := by linarith
  refine ⟨max M 0 ^ (p - 1) * G, by positivity, fun ξ => ?_⟩
  rw [flux, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hF.nonneg ξ) _)]
  have h1 : F ξ ≤ max M 0 * ‖ξ‖ :=
    (hM ξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  calc F ξ ^ (p - 1) * ‖gradient F ξ‖ ≤ (max M 0 * ‖ξ‖) ^ (p - 1) * G := by
        gcongr
        · exact hF.nonneg ξ
        · exact hG ξ
    _ = max M 0 ^ (p - 1) * G * ‖ξ‖ ^ (p - 1) := by
        rw [Real.mul_rpow (le_max_right _ _) (norm_nonneg _)]; ring

/-- `∇F` is continuous away from the origin. -/
theorem continuousOn_gradient : ContinuousOn (gradient F) {0}ᶜ := by
  have h := hF.contDiffOn.continuousOn_fderiv_of_isOpen isOpen_compl_singleton
    (by exact_mod_cast le_top)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn h

/-- The flux `a = F^{p-1} ∇F` is continuous on `ℝ^d` (at the origin by `‖a(ξ)‖ ≤ C‖ξ‖^{p-1}`). -/
theorem continuous_flux {p : ℝ} (hp : 1 < p) : Continuous (flux p F) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · obtain ⟨C, hC0, hC⟩ := hF.norm_flux_le hp
    rw [ContinuousAt, flux_zero hp hF, tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    have h1 : Tendsto (fun ζ : Euc d => C * ‖ζ‖ ^ (p - 1)) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun ζ : Euc d => ‖ζ‖ ^ (p - 1)) (𝓝 0) (𝓝 (‖(0 : Euc d)‖ ^ (p - 1))) :=
        (continuous_norm.tendsto 0).rpow_const (Or.inr (by linarith))
      rw [norm_zero, Real.zero_rpow (by linarith)] at this
      simpa using this.const_mul C
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun ζ => norm_nonneg _) hC
  · have hc : ContinuousOn (fun ξ => F ξ ^ (p - 1) • gradient F ξ) {0}ᶜ :=
      (hF.continuousOn.rpow_const fun x _ => Or.inr (by linarith)).smul hF.continuousOn_gradient
    exact hc.continuousAt (isOpen_compl_singleton.mem_nhds hξ)

end IsSmoothStrictNorm

/-- The gradient of any function is measurable (`measurable_fderiv`). -/
theorem measurable_gradient' (f : Euc d → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

/-- The flux `a = F^{p-1} ∇F` is measurable. -/
theorem measurable_flux {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) (p : ℝ) :
    Measurable (flux p F) :=
  (hF.continuous.measurable.pow_const (p - 1)).smul (measurable_gradient' F)

/-! ### The smooth truncation `Θ` -/

/-- The smooth truncation `Θ(r) = r · T(r - 1)`, `T = Real.smoothTransition`: `Θ = 0` on
`(-∞, 1]`, `Θ(r) = r` on `[2, ∞)`, and `0 ≤ Θ(r) ≤ r` for `r ≥ 0`. -/
noncomputable def trunc (r : ℝ) : ℝ := r * Real.smoothTransition (r - 1)

theorem contDiff_trunc {n : ℕ∞} : ContDiff ℝ n trunc :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem continuous_trunc : Continuous trunc := (contDiff_trunc (n := 0)).continuous

theorem trunc_of_le_one {r : ℝ} (h : r ≤ 1) : trunc r = 0 := by
  simp [trunc, Real.smoothTransition.zero_of_nonpos (by linarith : r - 1 ≤ 0)]

theorem trunc_of_two_le {r : ℝ} (h : 2 ≤ r) : trunc r = r := by
  simp [trunc, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ r - 1)]

theorem trunc_nonneg {r : ℝ} (h : 0 ≤ r) : 0 ≤ trunc r :=
  mul_nonneg h (Real.smoothTransition.nonneg _)

theorem trunc_le {r : ℝ} (h : 0 ≤ r) : trunc r ≤ r :=
  (mul_le_of_le_one_right h (Real.smoothTransition.le_one _))

/-- The derivative of the truncation. -/
noncomputable def trunc' (r : ℝ) : ℝ := deriv trunc r

theorem hasDerivAt_trunc (r : ℝ) : HasDerivAt trunc (trunc' r) r :=
  ((contDiff_trunc (n := 1)).differentiable one_ne_zero r).hasDerivAt

theorem continuous_trunc' : Continuous trunc' :=
  (contDiff_trunc (n := 1)).continuous_deriv le_rfl

theorem trunc'_of_lt_one {r : ℝ} (h : r < 1) : trunc' r = 0 := by
  have heq : trunc =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [eventually_lt_nhds h] with x hx
    exact trunc_of_le_one hx.le
  rw [trunc', heq.deriv_eq, deriv_const]

theorem trunc'_of_two_lt {r : ℝ} (h : 2 < r) : trunc' r = 1 := by
  have heq : trunc =ᶠ[𝓝 r] id := by
    filter_upwards [eventually_gt_nhds h] with x hx
    exact trunc_of_two_le hx.le
  rw [trunc', heq.deriv_eq, deriv_id]

/-- `Θ'` is bounded. -/
theorem exists_bound_trunc' : ∃ C : ℝ, 0 ≤ C ∧ ∀ r, |trunc' r| ≤ C := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    continuous_trunc'.continuousOn
  refine ⟨max B 1, le_max_of_le_right zero_le_one, fun r => ?_⟩
  by_cases hr : r ∈ Icc (0 : ℝ) 3
  · exact (le_of_eq (Real.norm_eq_abs _).symm).trans ((hB r hr).trans (le_max_left _ _))
  · rw [mem_Icc, not_and_or, not_le, not_le] at hr
    rcases hr with hr | hr
    · rw [trunc'_of_lt_one (by linarith), abs_zero]; exact le_max_of_le_right zero_le_one
    · rw [trunc'_of_two_lt (by linarith), abs_one]; exact le_max_right _ _

/-- The rescaled truncation `θ_s(r) = s Θ(r / s)`. -/
noncomputable def truncS (s r : ℝ) : ℝ := s * trunc (r / s)

theorem truncS_of_le {s r : ℝ} (hs : 0 < s) (h : r ≤ s) : truncS s r = 0 := by
  rw [truncS, trunc_of_le_one (by rwa [div_le_one hs]), mul_zero]

theorem truncS_of_ge {s r : ℝ} (hs : 0 < s) (h : 2 * s ≤ r) : truncS s r = r := by
  rw [truncS, trunc_of_two_le (by rwa [le_div_iff₀ hs]), mul_div_cancel₀ _ hs.ne']

theorem truncS_nonneg {s r : ℝ} (hs : 0 < s) (h : 0 ≤ r) : 0 ≤ truncS s r :=
  mul_nonneg hs.le (trunc_nonneg (div_nonneg h hs.le))

theorem truncS_le {s r : ℝ} (hs : 0 < s) (h : 0 ≤ r) : truncS s r ≤ r := by
  have := trunc_le (div_nonneg h hs.le)
  calc truncS s r = s * trunc (r / s) := rfl
    _ ≤ s * (r / s) := by gcongr
    _ = r := mul_div_cancel₀ _ hs.ne'

theorem hasDerivAt_truncS {s : ℝ} (hs : 0 < s) (r : ℝ) :
    HasDerivAt (truncS s) (trunc' (r / s)) r := by
  have h1 : HasDerivAt (fun r : ℝ => r / s) (1 / s) r := by
    simpa using (hasDerivAt_id r).div_const s
  have h2 := ((hasDerivAt_trunc (r / s)).comp r h1).const_mul s
  refine h2.congr_deriv ?_
  field_simp

theorem contDiff_truncS {n : ℕ∞} (s : ℝ) : ContDiff ℝ n (truncS s) :=
  contDiff_const.mul (contDiff_trunc.comp (contDiff_id.div_const s))

/-- `θ_s(r) → r` as `s ↓ 0` (eventually equal for `r > 0`, identically zero at `r = 0`). -/
theorem tendsto_truncS {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun s => truncS s r) (𝓝[>] 0) (𝓝 r) := by
  rcases hr.eq_or_lt with rfl | hr
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (truncS_of_le hs hs.le).symm
  · refine tendsto_const_nhds.congr' ?_
    have hmem : Ioo (0 : ℝ) (r / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hmem] with s hs
    exact (truncS_of_ge hs.1 (by linarith [hs.2])).symm

/-- `θ_s'(r) = Θ'(r/s) → 1` as `s ↓ 0` for `r > 0`. -/
theorem tendsto_trunc'_div {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s => trunc' (r / s)) (𝓝[>] 0) (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  have hmem : Ioo (0 : ℝ) (r / 3) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hmem] with s hs
  refine (trunc'_of_two_lt ?_).symm
  rw [lt_div_iff₀ hs.1]
  linarith [hs.2]

/-! ### Mollification of `C¹` compactly supported functions -/

section Mollify

open scoped Convolution

/-- The standard bump of outer radius `ε` (inner radius `ε/2`). -/
noncomputable def stdBump {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : Euc d) :=
  ⟨ε / 2, ε, by positivity, by linarith⟩

/-- The mollification `ψ_ε = φ_ε ⋆ V` with the normalized standard bump. -/
noncomputable def mollify {ε : ℝ} (hε : 0 < ε) (V : Euc d → ℝ) : Euc d → ℝ :=
  (stdBump hε).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V

variable {ε : ℝ} (hε : 0 < ε) {V : Euc d → ℝ}

theorem mollify_contDiff (hV : Continuous V) : ContDiff ℝ (⊤ : ℕ∞) (mollify hε V) :=
  HasCompactSupport.contDiff_convolution_left _ (stdBump hε).hasCompactSupport_normed
    (stdBump hε).contDiff_normed hV.locallyIntegrable

theorem mollify_nonneg (hV0 : ∀ x, 0 ≤ V x) (x : Euc d) : 0 ≤ mollify hε V x := by
  rw [mollify, convolution_def]
  refine integral_nonneg fun t => ?_
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_nonneg ((stdBump hε).nonneg_normed t) (hV0 _)

theorem support_mollify_subset :
    Function.support (mollify hε V) ⊆ Metric.ball 0 ε + Function.support V := by
  rw [mollify]
  refine Set.Subset.trans (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)) ?_
  rw [(stdBump hε).support_normed_eq]
  exact le_rfl

theorem tsupport_mollify_subset {S : Set (Euc d)} (hS : IsClosed S)
    (h : Metric.ball 0 ε + Function.support V ⊆ S) : tsupport (mollify hε V) ⊆ S :=
  closure_minimal ((support_mollify_subset hε).trans h) hS

/-- Uniform closeness of a bump convolution to the function, for `E'`-valued functions. -/
theorem dist_bump_convolution_le {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] {g : Euc d → E'} (hg : AEStronglyMeasurable g volume) {δ : ℝ}
    (hδ : ∀ x y, dist x y < ε → dist (g x) (g y) ≤ δ) (x₀ : Euc d) :
    dist (((stdBump hε).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x₀) (g x₀)
      ≤ δ :=
  ContDiffBump.dist_normed_convolution_le hg fun x hx => hδ x x₀ (by simpa [stdBump] using hx)

/-- The derivative of the mollification is the mollification of the derivative. -/
theorem fderiv_mollify (hV : ContDiff ℝ 1 V) (hVs : HasCompactSupport V) (x₀ : Euc d) :
    fderiv ℝ (mollify hε V) x₀ =
      ((stdBump hε).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ V) x₀ := by
  have h := HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hVs
    (((stdBump hε).continuous_normed (μ := volume)).locallyIntegrable (μ := volume)) hV x₀
  rw [mollify, h.fderiv]
  have hL : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompR (Euc d) =
      (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (Euc d →L[ℝ] ℝ) →L[ℝ] (Euc d →L[ℝ] ℝ)) := by
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun T =>
      ContinuousLinearMap.ext fun v => ?_
    simp [ContinuousLinearMap.precompR]
  rw [hL]

/-- Uniform convergence of bump convolutions of a uniformly continuous `E'`-valued function
along a sequence of radii `ε n → 0`. -/
theorem tendstoUniformly_bump_convolution {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] {g : Euc d → E'} (hg : UniformContinuous g) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformly
      (fun n => (stdBump (hε n)).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) g
      atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro η hη
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuous_iff.1 hg (η / 2) (half_pos hη)
  filter_upwards [hlim.eventually (eventually_le_nhds hr)] with n hn x
  have := dist_bump_convolution_le (hε n) hg.continuous.aestronglyMeasurable (δ := η / 2)
    (fun x y hxy => (hmod (hxy.trans_le hn)).le) x
  rw [dist_comm]
  linarith

/-- **Mollification** of a nonnegative `C¹` function with compact support in the open set `K`:
smooth nonnegative functions `ψ n` supported in a fixed compact `S ⊆ K`, converging uniformly
to `V` together with their gradients. -/
theorem exists_mollifier_seq {K : Set (Euc d)} (hK : IsOpen K) {V : Euc d → ℝ}
    (hV : ContDiff ℝ 1 V) (hVs : HasCompactSupport V) (hVK : tsupport V ⊆ K)
    (hV0 : ∀ x, 0 ≤ V x) :
    ∃ (S : Set (Euc d)) (ψ : ℕ → Euc d → ℝ), IsCompact S ∧ S ⊆ K ∧ tsupport V ⊆ S ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n)) ∧ (∀ n, tsupport (ψ n) ⊆ S) ∧ (∀ n x, 0 ≤ ψ n x) ∧
      TendstoUniformly ψ V atTop ∧
      TendstoUniformly (fun n => gradient (ψ n)) (gradient V) atTop := by
  obtain ⟨δ, hδ, hδK⟩ := hVs.exists_cthickening_subset_open hK hVK
  set S := Metric.cthickening δ (tsupport V) with hS
  have hSc : IsCompact S := hVs.cthickening
  have hε : ∀ n : ℕ, 0 < δ / ((n : ℝ) + 1) := fun n => by positivity
  have hlim : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    rw [mul_one_div]
  refine ⟨S, fun n => mollify (hε n) V, hSc, hδK, Metric.self_subset_cthickening _,
    fun n => mollify_contDiff _ hV.continuous, fun n => ?_, fun n x => mollify_nonneg _ hV0 x,
    ?_, ?_⟩
  · refine tsupport_mollify_subset _ hSc.isClosed ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine Metric.mem_cthickening_of_dist_le _ b δ _ (subset_closure hb) ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    have h1 : ‖a‖ < δ / ((n : ℝ) + 1) := by simpa using ha
    have h2 : δ / ((n : ℝ) + 1) ≤ δ := div_le_self hδ.le (by linarith [n.cast_nonneg (α := ℝ)])
    exact h1.le.trans h2
  · exact tendstoUniformly_bump_convolution
      (hVs.uniformContinuous_of_continuous hV.continuous) hε hlim
  · have h1 := tendstoUniformly_bump_convolution
      ((hVs.fderiv ℝ).uniformContinuous_of_continuous (hV.continuous_fderiv one_ne_zero)) hε hlim
    have h2 := (InnerProductSpace.toDual ℝ (Euc d)).symm.isometry.uniformContinuous
      |>.comp_tendstoUniformly h1
    have heq : (fun n => gradient (mollify (hε n) V)) = fun n =>
        (InnerProductSpace.toDual ℝ (Euc d)).symm ∘
          ((stdBump (hε n)).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ V) := by
      funext n x
      simp only [Function.comp_def, gradient, fderiv_mollify (hε n) hV hVs]
    have heq' : gradient V = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ V := rfl
    rw [heq, heq']
    exact h2

end Mollify

/-! ### Dominated convergence under uniform convergence on a compact support -/

/-- A function vanishing outside a compact set and continuous there is bounded. -/
theorem exists_bound_of_zero_outside {E : Type*} [NormedAddCommGroup E] {S : Set (Euc d)}
    (hS : IsCompact S) {f : Euc d → E} (hf : ContinuousOn f S) (h0 : ∀ x ∉ S, f x = 0) :
    ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hf
  refine ⟨max B 0, fun x => ?_⟩
  by_cases hx : x ∈ S
  · exact (hB x hx).trans (le_max_left _ _)
  · rw [h0 x hx, norm_zero]; exact le_max_right _ _

/-- **Dominated convergence under uniform convergence**: if `f n → g` uniformly, the `f n` vanish
outside the compact `S`, `g` is bounded, and `Φ x` is continuous with `Φ x 0 = 0` and locally
bounded uniformly in `x ∈ S`, then `∫ Φ x (f n x) → ∫ Φ x (g x)`. -/
theorem tendsto_integral_comp_of_tendstoUniformly {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S : Set (Euc d)} (hS : IsCompact S) {f : ℕ → Euc d → E} {g : Euc d → E}
    (hfS : ∀ n, ∀ x ∉ S, f n x = 0) (hgb : ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B)
    (hlim : TendstoUniformly f g atTop) {Φ : Euc d → E → ℝ} (hΦc : ∀ x, Continuous (Φ x))
    (hΦ0 : ∀ x, Φ x 0 = 0) (hΦm : ∀ n, AEStronglyMeasurable (fun x => Φ x (f n x)) volume)
    (hΦb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ S, ∀ ξ : E, ‖ξ‖ ≤ R → |Φ x ξ| ≤ C) :
    Tendsto (fun n => ∫ x, Φ x (f n x)) atTop (𝓝 (∫ x, Φ x (g x))) := by
  obtain ⟨B, hB⟩ := hgb
  obtain ⟨C, hC⟩ := hΦb (B + 1)
  have hev : ∀ᶠ n in atTop, ∀ x, ‖f n x‖ ≤ B + 1 := by
    filter_upwards [Metric.tendstoUniformly_iff.1 hlim 1 one_pos] with n hn x
    have h1 := hn x
    rw [dist_comm, dist_eq_norm] at h1
    calc ‖f n x‖ = ‖g x + (f n x - g x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖g x‖ + ‖f n x - g x‖ := norm_add_le _ _
      _ ≤ B + 1 := by linarith [hB x]
  refine tendsto_integral_filter_of_dominated_convergence (S.indicator fun _ => C)
    (Eventually.of_forall hΦm) ?_ ?_ ?_
  · filter_upwards [hev] with n hn
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, Real.norm_eq_abs]; exact hC x hx _ (hn x)
    · rw [indicator_of_notMem hx, hfS n x hx, hΦ0, norm_zero]
  · exact (integrable_indicator_iff hS.measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  · exact Eventually.of_forall fun x => ((hΦc x).tendsto (g x)).comp (hlim.tendsto_at x)

/-! ### Density of smooth test functions and the weak inequality for `C¹` test functions -/

/-- A nonzero nonnegative function is positive somewhere. -/
theorem exists_pos_of_ne_zero {V : Euc d → ℝ} (hV0 : ∀ x, 0 ≤ V x) (hne : V ≠ 0) :
    ∃ x₀, 0 < V x₀ := by
  by_contra h
  exact hne (funext fun x => le_antisymm (not_lt.1 fun h' => h ⟨x, h'⟩) (hV0 x))

/-- Along a uniformly convergent sequence to a function positive at `x₀`, the terms are
eventually nonzero. -/
theorem eventually_ne_zero_of_tendstoUniformly {ψ : ℕ → Euc d → ℝ} {V : Euc d → ℝ}
    (hψV : TendstoUniformly ψ V atTop) {x₀ : Euc d} (hx₀ : 0 < V x₀) :
    ∀ᶠ n in atTop, ψ n ≠ 0 := by
  filter_upwards [Metric.tendstoUniformly_iff.1 hψV (V x₀) hx₀] with n hn h0
  have := hn x₀
  rw [h0, Pi.zero_apply, dist_zero_right, Real.norm_eq_abs, abs_of_pos hx₀] at this
  exact lt_irrefl _ this

/-- **Density**: `λ_{p,F}(K) ≤ rayleighGen p F V` for every nonzero nonnegative `C¹` function `V`
with compact support in the open set `K` (mollification). -/
theorem lambdaGen_le_rayleighGen_of_contDiff_one {p : ℝ} (hp : 0 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsOpen K) {V : Euc d → ℝ}
    (hV : ContDiff ℝ 1 V) (hVs : HasCompactSupport V) (hVK : tsupport V ⊆ K)
    (hV0 : ∀ x, 0 ≤ V x) (hne : V ≠ 0) : lambdaGen p F K ≤ rayleighGen p F V := by
  obtain ⟨S, ψ, hSc, hSK, hVS, hψ, hψS, hψ0, hψV, hψg⟩ := exists_mollifier_seq hK hV hVs hVK hV0
  obtain ⟨x₀, hx₀⟩ := exists_pos_of_ne_zero hV0 hne
  have hψ1 : ∀ n, ContDiff ℝ 1 (ψ n) := fun n => (hψ n).of_le (by exact_mod_cast le_top)
  have hle : ∀ᶠ n in atTop, lambdaGen p F K ≤ rayleighGen p F (ψ n) := by
    filter_upwards [eventually_ne_zero_of_tendstoUniformly hψV hx₀] with n hn
    exact lambdaGen_le_rayleighGen hF.nonneg p
      ⟨hψ n, hSc.of_isClosed_subset (isClosed_tsupport _) (hψS n), (hψS n).trans hSK, hn⟩
  refine ge_of_tendsto ?_ hle
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  have hgS : ∀ n, ∀ x ∉ S, gradient (ψ n) x = 0 := fun n x hx =>
    gradient_eq_zero_of_notMem_tsupport fun h => hx (hψS n h)
  have hgb : ∃ B, ∀ x, ‖gradient V x‖ ≤ B :=
    exists_bound_of_zero_outside hSc (continuous_gradient hV).continuousOn fun x hx =>
      gradient_eq_zero_of_notMem_tsupport fun h => hx (hVS h)
  have hVb : ∃ B, ∀ x, ‖V x‖ ≤ B :=
    exists_bound_of_zero_outside hSc hV.continuous.continuousOn fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hVS h)
  have hnum : Tendsto (fun n => ∫ x, F (gradient (ψ n) x) ^ p) atTop
      (𝓝 (∫ x, F (gradient V x) ^ p)) := by
    refine tendsto_integral_comp_of_tendstoUniformly hSc hgS hgb hψg (Φ := fun _ ξ => F ξ ^ p)
      (fun _ => hF.continuous.rpow_const fun _ => Or.inr hp.le)
      (fun _ => by simp [hF.map_zero, Real.zero_rpow hp.ne'])
      (fun n => ((hF.continuous.comp (continuous_gradient (hψ1 n))).rpow_const
        fun _ => Or.inr hp.le).aestronglyMeasurable) fun R => ?_
    refine ⟨(max M 0 * max R 0) ^ p, fun x _ ξ hξ => ?_⟩
    rw [abs_of_nonneg (Real.rpow_nonneg (hF.nonneg ξ) p)]
    refine Real.rpow_le_rpow (hF.nonneg ξ) ?_ hp.le
    calc F ξ ≤ M * ‖ξ‖ := hM ξ
      _ ≤ max M 0 * max R 0 := by
          gcongr
          · exact le_max_left _ _
          · exact hξ.trans (le_max_left _ _)
  have hden : Tendsto (fun n => ∫ x, |ψ n x| ^ p) atTop (𝓝 (∫ x, |V x| ^ p)) := by
    refine tendsto_integral_comp_of_tendstoUniformly hSc
      (fun n x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hψS n h)) hVb hψV
      (Φ := fun _ r => |r| ^ p) (fun _ => continuous_abs.rpow_const fun _ => Or.inr hp.le)
      (fun _ => by simp [Real.zero_rpow hp.ne'])
      (fun n => ((hψ1 n).continuous.abs.rpow_const fun _ => Or.inr hp.le).aestronglyMeasurable)
      fun R => ?_
    refine ⟨max R 0 ^ p, fun x _ r hr => ?_⟩
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg r) p)]
    refine Real.rpow_le_rpow (abs_nonneg r) ?_ hp.le
    rw [Real.norm_eq_abs] at hr
    exact hr.trans (le_max_left _ _)
  have hpos : 0 < ∫ x, |V x| ^ p := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hV.continuous.abs.rpow_const fun _ => Or.inr hp.le)
      (hVs.comp_left (g := fun r : ℝ => |r| ^ p) (by simp [Real.zero_rpow hp.ne']))
      (fun x => Real.rpow_nonneg (abs_nonneg _) p) (x := x₀) ?_
    exact (Real.rpow_pos_of_pos (abs_pos.2 hx₀.ne') p).ne'
  exact hnum.div hden hpos.ne'

/-- **The weak inequality extends to `C¹` test functions**: if
`∫ ⟪A, ∇ψ⟫ ≤ Λ ∫ h ψ` for all nonnegative smooth test functions `ψ` of the open set `K`, with `A`
and `h` bounded and measurable, then the same holds for every nonzero nonnegative `C¹` function
`V` with compact support in `K`. -/
theorem weak_ineq_of_contDiff_one {K : Set (Euc d)} (hK : IsOpen K) {A : Euc d → Euc d}
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) {h : Euc d → ℝ} (hhm : Measurable h)
    (hhb : ∃ C : ℝ, ∀ x, |h x| ≤ C) {Λ : ℝ}
    (hweak : ∀ ψ : Euc d → ℝ, IsTestFn K ψ → (∀ x, 0 ≤ ψ x) →
      ∫ x, ⟪A x, gradient ψ x⟫ ≤ Λ * ∫ x, h x * ψ x)
    {V : Euc d → ℝ} (hV : ContDiff ℝ 1 V) (hVs : HasCompactSupport V) (hVK : tsupport V ⊆ K)
    (hV0 : ∀ x, 0 ≤ V x) (hne : V ≠ 0) :
    ∫ x, ⟪A x, gradient V x⟫ ≤ Λ * ∫ x, h x * V x := by
  obtain ⟨S, ψ, hSc, hSK, hVS, hψ, hψS, hψ0, hψV, hψg⟩ := exists_mollifier_seq hK hV hVs hVK hV0
  obtain ⟨x₀, hx₀⟩ := exists_pos_of_ne_zero hV0 hne
  obtain ⟨CA, hCA⟩ := hAb
  obtain ⟨Ch, hCh⟩ := hhb
  have hψ1 : ∀ n, ContDiff ℝ 1 (ψ n) := fun n => (hψ n).of_le (by exact_mod_cast le_top)
  have hle : ∀ᶠ n in atTop,
      ∫ x, ⟪A x, gradient (ψ n) x⟫ ≤ Λ * ∫ x, h x * ψ n x := by
    filter_upwards [eventually_ne_zero_of_tendstoUniformly hψV hx₀] with n hn
    exact hweak (ψ n)
      ⟨hψ n, hSc.of_isClosed_subset (isClosed_tsupport _) (hψS n), (hψS n).trans hSK, hn⟩ (hψ0 n)
  have hgS : ∀ n, ∀ x ∉ S, gradient (ψ n) x = 0 := fun n x hx =>
    gradient_eq_zero_of_notMem_tsupport fun h => hx (hψS n h)
  have hgb : ∃ B, ∀ x, ‖gradient V x‖ ≤ B :=
    exists_bound_of_zero_outside hSc (continuous_gradient hV).continuousOn fun x hx =>
      gradient_eq_zero_of_notMem_tsupport fun h => hx (hVS h)
  have hVb : ∃ B, ∀ x, ‖V x‖ ≤ B :=
    exists_bound_of_zero_outside hSc hV.continuous.continuousOn fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hVS h)
  have h1 : Tendsto (fun n => ∫ x, ⟪A x, gradient (ψ n) x⟫) atTop
      (𝓝 (∫ x, ⟪A x, gradient V x⟫)) := by
    refine tendsto_integral_comp_of_tendstoUniformly hSc hgS hgb hψg (Φ := fun x ξ => ⟪A x, ξ⟫)
      (fun x => continuous_const.inner continuous_id) (fun x => inner_zero_right _)
      (fun n => (hAm.inner (continuous_gradient (hψ1 n)).measurable).aestronglyMeasurable)
      fun R => ⟨CA * R, fun x _ ξ hξ => ?_⟩
    calc |⟪A x, ξ⟫| ≤ ‖A x‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
      _ ≤ CA * R := mul_le_mul (hCA x) hξ (norm_nonneg _) ((norm_nonneg _).trans (hCA x))
  have h2 : Tendsto (fun n => ∫ x, h x * ψ n x) atTop (𝓝 (∫ x, h x * V x)) := by
    refine tendsto_integral_comp_of_tendstoUniformly hSc
      (fun n x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hψS n h)) hVb hψV
      (Φ := fun x r => h x * r) (fun x => continuous_const.mul continuous_id)
      (fun x => mul_zero _)
      (fun n => (hhm.mul (hψ1 n).continuous.measurable).aestronglyMeasurable)
      fun R => ⟨Ch * R, fun x _ r hr => ?_⟩
    rw [abs_mul]
    rw [Real.norm_eq_abs] at hr
    exact mul_le_mul (hCh x) hr (abs_nonneg _) ((abs_nonneg _).trans (hCh x))
  exact le_of_tendsto_of_tendsto h1 (h2.const_mul Λ) hle

/-! ### The truncation `θ_s ∘ U` -/

/-- The gradient of a nonnegative function vanishes at its zeros. -/
theorem gradient_eq_zero_of_eq_zero {U : Euc d → ℝ} (hU0 : ∀ x, 0 ≤ U x) {x : Euc d}
    (hx : U x = 0) : gradient U x = 0 := by
  by_cases hd : DifferentiableAt ℝ U x
  · have hmin : IsLocalMin U x := Eventually.of_forall fun y => hx ▸ hU0 y
    have := hmin.hasFDerivAt_eq_zero hd.hasFDerivAt
    simp [gradient, this]
  · exact gradient_eq_zero_of_not_differentiableAt hd

section TruncU

variable {K : Set (Euc d)} (hK : IsGoodConvex K) {U : Euc d → ℝ} (hUc : Continuous U)
  (hU0 : ∀ x, 0 ≤ U x) (hsupp : Function.support U ⊆ K) (hC1 : ContDiffOn ℝ 1 U K)
  {s : ℝ} (hs : 0 < s)

include hsupp in
theorem eq_zero_of_notMem_of_support_subset {x : Euc d} (hx : x ∉ K) : U x = 0 :=
  Function.notMem_support.1 fun h => hx (hsupp h)

include hUc hsupp hs in
/-- Near a point outside `K`, the truncation `θ_s ∘ U` vanishes. -/
theorem truncU_eventually_zero {x : Euc d} (hx : x ∉ K) :
    (fun y => truncS s (U y)) =ᶠ[𝓝 x] fun _ => 0 := by
  have h0 : U x = 0 := eq_zero_of_notMem_of_support_subset hsupp hx
  have : ∀ᶠ y in 𝓝 x, U y < s :=
    hUc.continuousAt.eventually_lt continuousAt_const (by rw [h0]; exact hs)
  filter_upwards [this] with y hy
  exact truncS_of_le hs hy.le

include hK hUc hsupp hC1 hs in
/-- `θ_s ∘ U ∈ C¹(ℝ^d)`. -/
theorem truncU_contDiff : ContDiff ℝ 1 fun x => truncS s (U x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ K
  · exact (contDiff_truncS s).contDiffAt.comp x (hC1.contDiffAt (hK.isOpen.mem_nhds hx))
  · exact contDiffAt_const.congr_of_eventuallyEq (truncU_eventually_zero hUc hsupp hs hx)

include hs in
theorem truncU_support_subset : Function.support (fun x => truncS s (U x)) ⊆ {x | s ≤ U x} := by
  intro x hx
  by_contra h
  exact hx (truncS_of_le hs (not_le.1 h).le)

include hK hUc hsupp hs in
theorem isCompact_superlevel : IsCompact {x | s ≤ U x} :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_const hUc)
    (hK.isBounded.subset fun x hx => hsupp (Function.mem_support.2 (by
      have : s ≤ U x := hx
      linarith)))

include hUc hs in
theorem truncU_tsupport_subset_superlevel : tsupport (fun x => truncS s (U x)) ⊆ {x | s ≤ U x} :=
  closure_minimal (truncU_support_subset hs) (isClosed_le continuous_const hUc)

include hK hUc hsupp hs in
theorem truncU_hasCompactSupport : HasCompactSupport fun x => truncS s (U x) :=
  (isCompact_superlevel hK hUc hsupp hs).of_isClosed_subset (isClosed_tsupport _)
    (truncU_tsupport_subset_superlevel hUc hs)

include hUc hsupp hs in
theorem truncU_tsupport_subset : tsupport (fun x => truncS s (U x)) ⊆ K :=
  (truncU_tsupport_subset_superlevel hUc hs).trans fun x hx =>
    hsupp (Function.mem_support.2 (by
      have : s ≤ U x := hx
      linarith))

include hU0 hs in
theorem truncU_nonneg (x : Euc d) : 0 ≤ truncS s (U x) := truncS_nonneg hs (hU0 x)

include hK hUc hU0 hsupp hC1 hs in
/-- `∇(θ_s ∘ U) = θ_s'(U) ∇U`. -/
theorem truncU_hasGradientAt (x : Euc d) :
    HasGradientAt (fun x => truncS s (U x)) (trunc' (U x / s) • gradient U x) x := by
  by_cases hx : x ∈ K
  · have hU : HasGradientAt U (gradient U x) x :=
      ((hC1.differentiableOn one_ne_zero).differentiableAt (hK.isOpen.mem_nhds hx)).hasGradientAt
    have h := (hasDerivAt_truncS hs (U x)).comp_hasFDerivAt x hU.hasFDerivAt
    rw [hasGradientAt_iff_hasFDerivAt, map_smul]
    exact h
  · rw [gradient_eq_zero_of_eq_zero hU0 (eq_zero_of_notMem_of_support_subset hsupp hx),
      smul_zero]
    exact HasGradientAt.congr_of_eventuallyEq (hasGradientAt_const x (0 : ℝ))
      (truncU_eventually_zero hUc hsupp hs hx)

include hK hUc hU0 hsupp hC1 hs in
theorem truncU_gradient (x : Euc d) :
    gradient (fun x => truncS s (U x)) x = trunc' (U x / s) • gradient U x :=
  (truncU_hasGradientAt hK hUc hU0 hsupp hC1 hs x).gradient

end TruncU

/-! ### The cutoff across the critical set (paper Appendix A, *Including the critical set*) -/

section Cutoff

open Metric

/-- The gradient of a product. -/
theorem gradient_mul {f g : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  simp only [gradient, fderiv_fun_mul hf hg, map_add, map_smul]

/-- The gradient of a locally constant function vanishes. -/
theorem gradient_eq_zero_of_eventuallyEq_const {f : Euc d → ℝ} {x : Euc d} {c : ℝ}
    (h : ∀ᶠ y in 𝓝 x, f y = c) : gradient f x = 0 :=
  (HasGradientAt.congr_of_eventuallyEq (hasGradientAt_const x c) h).gradient

/-! #### A hand-scaled bump `ρ_δ(y) = δ^{-d} ρ₁(y/δ)` with `∫ ‖∇ρ_δ‖ = O(1/δ)` -/

open scoped Convolution

/-- The reference bump `ρ₁` (the normalized standard bump of outer radius `1`). -/
noncomputable def refBump : Euc d → ℝ := (stdBump (one_pos : (0 : ℝ) < 1)).normed volume

theorem refBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (refBump (d := d)) :=
  (stdBump one_pos).contDiff_normed

theorem refBump_contDiff_one : ContDiff ℝ 1 (refBump (d := d)) :=
  refBump_contDiff.of_le (by exact_mod_cast le_top)

theorem refBump_nonneg (y : Euc d) : 0 ≤ refBump y := (stdBump one_pos).nonneg_normed y

theorem refBump_integral : ∫ y, refBump (d := d) y = 1 := (stdBump one_pos).integral_normed

theorem refBump_tsupport : tsupport (refBump (d := d)) = Metric.closedBall 0 1 :=
  (stdBump one_pos).tsupport_normed_eq

theorem refBump_eq_zero {y : Euc d} (hy : 1 ≤ ‖y‖) : refBump y = 0 := by
  refine Function.notMem_support.1 fun h => ?_
  rw [refBump, (stdBump one_pos).support_normed_eq] at h
  have : ‖y‖ < 1 := by simpa [stdBump] using h
  linarith

/-- A bound on `‖∇ρ₁‖`. -/
theorem exists_bound_fderiv_refBump :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Euc d, ‖fderiv ℝ (refBump (d := d)) y‖ ≤ K := by
  obtain ⟨K, hK⟩ := exists_bound_of_zero_outside (isCompact_closedBall (0 : Euc d) 1)
    (refBump_contDiff_one.continuous_fderiv one_ne_zero).continuousOn fun y hy =>
      Function.notMem_support.1 fun h => hy (refBump_tsupport ▸ support_fderiv_subset ℝ h)
  exact ⟨max K 0, le_max_right _ _, fun y => (hK y).trans (le_max_left _ _)⟩

/-- The bump at scale `δ`: `ρ_δ(y) = δ^{-d} ρ₁(y/δ)`. -/
noncomputable def scaledBump (δ : ℝ) (y : Euc d) : ℝ := (δ ^ d)⁻¹ * refBump (δ⁻¹ • y)

section ScaledBump

variable {δ : ℝ} (hδ : 0 < δ)

theorem scaledBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (scaledBump (d := d) δ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun y : Euc d => δ⁻¹ • y) := contDiff_id.const_smul δ⁻¹
  exact contDiff_const.mul (refBump_contDiff.comp h)

theorem scaledBump_contDiff_one : ContDiff ℝ 1 (scaledBump (d := d) δ) :=
  scaledBump_contDiff.of_le (by exact_mod_cast le_top)

theorem scaledBump_continuous : Continuous (scaledBump (d := d) δ) :=
  scaledBump_contDiff_one.continuous

include hδ

theorem scaledBump_nonneg (y : Euc d) : 0 ≤ scaledBump δ y :=
  mul_nonneg (by positivity) (refBump_nonneg _)

theorem scaledBump_eq_zero {y : Euc d} (hy : δ ≤ ‖y‖) : scaledBump δ y = 0 := by
  rw [scaledBump, refBump_eq_zero, mul_zero]
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, le_inv_mul_iff₀ hδ, mul_one]
  exact hy

theorem scaledBump_support_subset : Function.support (scaledBump (d := d) δ) ⊆ Metric.ball 0 δ :=
  fun y hy => by
    by_contra h
    rw [Metric.mem_ball, dist_zero_right, not_lt] at h
    exact hy (scaledBump_eq_zero hδ h)

theorem scaledBump_tsupport_subset :
    tsupport (scaledBump (d := d) δ) ⊆ Metric.closedBall 0 δ :=
  closure_minimal ((scaledBump_support_subset hδ).trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

theorem scaledBump_hasCompactSupport : HasCompactSupport (scaledBump (d := d) δ) :=
  (isCompact_closedBall (0 : Euc d) δ).of_isClosed_subset (isClosed_tsupport _)
    (scaledBump_tsupport_subset hδ)

theorem scaledBump_integral : ∫ y, scaledBump (d := d) δ y = 1 := by
  have h : (fun y : Euc d => scaledBump δ y) = fun y => (δ ^ d)⁻¹ * refBump (δ⁻¹ • y) := rfl
  rw [h, integral_const_mul, Measure.integral_comp_smul volume refBump δ⁻¹,
    finrank_euclideanSpace_fin, refBump_integral, inv_pow, inv_inv, abs_of_pos (pow_pos hδ d),
    smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_pos hδ d).ne']

theorem scaledBump_integrable : Integrable (scaledBump (d := d) δ) :=
  scaledBump_continuous.integrable_of_hasCompactSupport (scaledBump_hasCompactSupport hδ)

/-- `‖∇ρ_δ(y)‖ ≤ δ^{-d} δ^{-1} K`. -/
theorem norm_fderiv_scaledBump_le {K : ℝ} (hK : ∀ y, ‖fderiv ℝ (refBump (d := d)) y‖ ≤ K)
    (y : Euc d) : ‖fderiv ℝ (scaledBump δ) y‖ ≤ (δ ^ d)⁻¹ * δ⁻¹ * K := by
  have h1 : HasFDerivAt (fun y : Euc d => δ⁻¹ • y) (δ⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) y :=
    (hasFDerivAt_id y).const_smul δ⁻¹
  have h2 : HasFDerivAt refBump (fderiv ℝ refBump (δ⁻¹ • y)) (δ⁻¹ • y) :=
    (refBump_contDiff_one.differentiable one_ne_zero _).hasFDerivAt
  have h3 := (h2.comp y h1).const_mul ((δ ^ d)⁻¹)
  have h : scaledBump (d := d) δ = fun y => (δ ^ d)⁻¹ * (refBump ∘ fun y => δ⁻¹ • y) y := rfl
  rw [h, h3.fderiv, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  calc (δ ^ d)⁻¹ * ‖(fderiv ℝ refBump (δ⁻¹ • y)).comp (δ⁻¹ • ContinuousLinearMap.id ℝ (Euc d))‖
      ≤ (δ ^ d)⁻¹ * (K * (δ⁻¹ * 1)) := by
        gcongr
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        · exact hK _
        · rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hδ).le]
          gcongr
          exact ContinuousLinearMap.norm_id_le
    _ = (δ ^ d)⁻¹ * δ⁻¹ * K := by ring

/-- `∫ ‖∇ρ_δ‖ ≤ K vol(B₁) / δ`. -/
theorem integral_norm_fderiv_scaledBump_le {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ (refBump (d := d)) y‖ ≤ K) :
    ∫ y, ‖fderiv ℝ (scaledBump (d := d) δ) y‖ ≤
      K * (volume (Metric.closedBall (0 : Euc d) 1)).toReal / δ := by
  have hsupp : ∀ y, y ∉ Metric.closedBall (0 : Euc d) δ → fderiv ℝ (scaledBump δ) y = 0 :=
    fun y hy => Function.notMem_support.1 fun h =>
      hy (scaledBump_tsupport_subset hδ (support_fderiv_subset ℝ h))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  calc ∫ y, ‖fderiv ℝ (scaledBump (d := d) δ) y‖
      ≤ ∫ y, (Metric.closedBall (0 : Euc d) δ).indicator (fun _ => (δ ^ d)⁻¹ * δ⁻¹ * K) y := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          ((integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
            (integrableOn_const (measure_closedBall_lt_top (μ := volume)).ne))
          (Eventually.of_forall fun y => ?_)
        dsimp only
        by_cases hy : y ∈ Metric.closedBall (0 : Euc d) δ
        · rw [indicator_of_mem hy]; exact norm_fderiv_scaledBump_le hδ hK y
        · rw [indicator_of_notMem hy, hsupp y hy, norm_zero]
    _ = (volume (Metric.closedBall (0 : Euc d) δ)).toReal * ((δ ^ d)⁻¹ * δ⁻¹ * K) := by
        rw [integral_indicator Metric.isClosed_closedBall.measurableSet, setIntegral_const,
          smul_eq_mul, measureReal_def]
    _ = K * (volume (Metric.closedBall (0 : Euc d) 1)).toReal / δ := by
        rw [Measure.addHaar_closedBall' volume (0 : Euc d) hδ.le, finrank_euclideanSpace_fin,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
        field_simp

end ScaledBump

/-- **Smooth cutoffs at scale `δ`** around an arbitrary set `C`, with gradient `O(1/δ)`, the
constant depending only on the dimension (paper: "Choose a Lipschitz cutoff `χ_δ` which is zero
within distance `δ` of `C`, one beyond distance `2δ`, and has gradient bounded by `1/δ`"; here
smooth, zero within `2δ`, one beyond `4δ`): the convolution of `ρ_δ` with the indicator of the
complement of `cthickening (3δ) C`. -/
theorem exists_cutoff_family :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (C : Set (Euc d)) (δ : ℝ), ∃ χ : Euc d → ℝ, 0 < δ →
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x ∈ cthickening (2 * δ) C, χ x = 0) ∧ (∀ x ∉ cthickening (4 * δ) C, χ x = 1) ∧
      ∀ x, ‖gradient χ x‖ ≤ K₀ / δ := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_fderiv_refBump (d := d)
  refine ⟨K * (volume (Metric.closedBall (0 : Euc d) 1)).toReal, by positivity, fun C δ => ?_⟩
  by_cases hδ : 0 < δ
  swap
  · exact ⟨0, fun h => absurd h hδ⟩
  set g : Euc d → ℝ := (cthickening (3 * δ) C)ᶜ.indicator 1 with hg
  have hgm : Measurable g := measurable_one.indicator isClosed_cthickening.measurableSet.compl
  have hg0 : ∀ x, 0 ≤ g x := fun x => indicator_nonneg (fun _ _ => zero_le_one) x
  have hg1 : ∀ x, g x ≤ 1 := fun x => by
    by_cases hx : x ∈ (cthickening (3 * δ) C)ᶜ
    · rw [hg, indicator_of_mem hx, Pi.one_apply]
    · rw [hg, indicator_of_notMem hx]
      exact zero_le_one
  have hgli : LocallyIntegrable g volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator isClosed_cthickening.measurableSet.compl
  have hρc : Continuous (scaledBump (d := d) δ) := scaledBump_continuous
  have hρint := scaledBump_integrable (d := d) hδ
  refine ⟨scaledBump δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g, fun _ =>
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact HasCompactSupport.contDiff_convolution_left _ (scaledBump_hasCompactSupport hδ)
      scaledBump_contDiff hgli
  · intro x
    rw [convolution_def]
    refine integral_nonneg fun t => ?_
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_nonneg (scaledBump_nonneg hδ t) (hg0 _)
  · intro x
    rw [convolution_def]
    have hint : Integrable fun t => ContinuousLinearMap.lsmul ℝ ℝ (scaledBump δ t) (g (x - t)) := by
      refine hρint.mono' ?_ (Eventually.of_forall fun t => ?_)
      · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        exact (hρc.measurable.mul (hgm.comp (measurable_const.sub measurable_id)))
          |>.aestronglyMeasurable
      · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (scaledBump_nonneg hδ t), abs_of_nonneg (hg0 _)]
        exact mul_le_of_le_one_right (scaledBump_nonneg hδ t) (hg1 _)
    calc ∫ t, ContinuousLinearMap.lsmul ℝ ℝ (scaledBump δ t) (g (x - t))
        ≤ ∫ t, scaledBump δ t := by
          refine integral_mono hint hρint fun t => ?_
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
          exact mul_le_of_le_one_right (scaledBump_nonneg hδ t) (hg1 _)
      _ = 1 := scaledBump_integral hδ
  · intro x hx
    rw [convolution_def]
    have h0 : ∀ t, ContinuousLinearMap.lsmul ℝ ℝ (scaledBump δ t) (g (x - t)) = 0 := fun t => by
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      by_cases ht : ‖t‖ < δ
      · have hmem : x - t ∈ cthickening (3 * δ) C := by
          rw [mem_cthickening_iff] at hx ⊢
          calc infEDist (x - t) C ≤ infEDist x C + edist (x - t) x :=
                infEDist_le_infEDist_add_edist
            _ ≤ ENNReal.ofReal (2 * δ) + ENNReal.ofReal δ := by
                gcongr
                rw [edist_dist, dist_eq_norm, sub_sub_cancel_left, norm_neg]
                exact ENNReal.ofReal_le_ofReal ht.le
            _ = ENNReal.ofReal (3 * δ) := by
                rw [← ENNReal.ofReal_add (by positivity) hδ.le]; ring_nf
        rw [hg, indicator_of_notMem (not_not.2 hmem), mul_zero]
      · rw [scaledBump_eq_zero hδ (not_lt.1 ht), zero_mul]
    simp only [h0, integral_zero]
  · intro x hx
    rw [convolution_def]
    have h1 : ∀ t, ContinuousLinearMap.lsmul ℝ ℝ (scaledBump δ t) (g (x - t)) = scaledBump δ t :=
      fun t => by
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        by_cases ht : ‖t‖ < δ
        · have hmem : x - t ∉ cthickening (3 * δ) C := by
            intro h
            apply hx
            rw [mem_cthickening_iff] at h ⊢
            calc infEDist x C ≤ infEDist (x - t) C + edist x (x - t) :=
                  infEDist_le_infEDist_add_edist
              _ ≤ ENNReal.ofReal (3 * δ) + ENNReal.ofReal δ := by
                  gcongr
                  rw [edist_dist, dist_eq_norm, sub_sub_cancel]
                  exact ENNReal.ofReal_le_ofReal ht.le
              _ = ENNReal.ofReal (4 * δ) := by
                  rw [← ENNReal.ofReal_add (by positivity) hδ.le]; ring_nf
          rw [hg, indicator_of_mem hmem, Pi.one_apply, mul_one]
        · rw [scaledBump_eq_zero hδ (not_lt.1 ht), zero_mul]
    simp only [h1]
    exact scaledBump_integral hδ
  · intro x
    have hd := HasCompactSupport.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (scaledBump_hasCompactSupport hδ) scaledBump_contDiff_one hgli x
    rw [gradient, LinearIsometryEquiv.norm_map, hd.fderiv, convolution_def]
    have hfint : Integrable fun t => ‖fderiv ℝ (scaledBump (d := d) δ) t‖ :=
      (scaledBump_contDiff_one.continuous_fderiv one_ne_zero).norm.integrable_of_hasCompactSupport
        ((scaledBump_hasCompactSupport hδ).fderiv ℝ).norm
    calc ‖∫ t, ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Euc d)) (fderiv ℝ (scaledBump δ) t)
          (g (x - t))‖
        ≤ ∫ t, ‖((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Euc d)) (fderiv ℝ (scaledBump δ) t)
            (g (x - t))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, ‖fderiv ℝ (scaledBump (d := d) δ) t‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hfint
            (Eventually.of_forall fun t => ?_)
          have : ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Euc d)) (fderiv ℝ (scaledBump δ) t)
              (g (x - t)) = g (x - t) • fderiv ℝ (scaledBump δ) t := by
            ext v
            simp [ContinuousLinearMap.precompL_apply, mul_comm]
          dsimp only
          rw [this, norm_smul, Real.norm_of_nonneg (hg0 _)]
          exact mul_le_of_le_one_left (norm_nonneg _) (hg1 _)
      _ ≤ K * (volume (Metric.closedBall (0 : Euc d) 1)).toReal / δ :=
          integral_norm_fderiv_scaledBump_le hδ hK

/-- `(1 + a)^n - 1 ≤ a · n · (1 + a)^n` for `a ≥ 0`. -/
theorem pow_sub_one_le_mul {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n - 1 ≤ a * n * (1 + a) ^ n := by
  have h := mul_geom_sum (1 + a) n
  rw [add_sub_cancel_left] at h
  rw [← h]
  have hle : ∑ i ∈ Finset.range n, (1 + a) ^ i ≤ ∑ _i ∈ Finset.range n, (1 + a) ^ n :=
    Finset.sum_le_sum fun i hi =>
      pow_le_pow_right₀ (by linarith) (Finset.mem_range.1 hi).le
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  calc a * ∑ i ∈ Finset.range n, (1 + a) ^ i ≤ a * (n * (1 + a) ^ n) :=
        mul_le_mul_of_nonneg_left hle ha
    _ = a * n * (1 + a) ^ n := by ring

/-- If the convex set `C` contains `closedBall c ρ`, its `r`-thickening lies in the homothetic
image `c + (1 + r/ρ)(C - c)` (the dilation trick for the parallel body of a convex body). -/
theorem cthickening_subset_homothety {C : Set (Euc d)} (hC : IsCompact C) (hCc : Convex ℝ C)
    {c : Euc d} {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall c ρ ⊆ C) {r : ℝ} (hr : 0 < r) :
    Metric.cthickening r C ⊆ AffineMap.homothety c (1 + r / ρ) '' C := by
  intro x hx
  rw [hC.cthickening_eq_biUnion_closedBall hr.le] at hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hxy
  set s : ℝ := r / ρ with hs
  have hs0 : 0 < s := div_pos hr hρ
  set a : ℝ := (1 + s)⁻¹ with ha
  set b : ℝ := s * a with hb
  have h1s : 0 < 1 + s := by linarith
  have ha0 : 0 < a := inv_pos.2 h1s
  have hb0 : 0 < b := mul_pos hs0 ha0
  have hab : a + b = 1 := by
    rw [hb, ha]; field_simp
  have hab' : (1 + s) * a = 1 := by rw [ha]; field_simp
  -- the auxiliary point `w ∈ closedBall c ρ`
  set w : Euc d := c + (a / b) • (x - y) with hw
  have hab2 : a / b = s⁻¹ := by rw [hb]; field_simp
  have hwC : w ∈ C := by
    refine hball ?_
    rw [Metric.mem_closedBall, dist_eq_norm, hw, add_sub_cancel_left, norm_smul, hab2,
      Real.norm_of_nonneg (inv_pos.2 hs0).le]
    calc s⁻¹ * ‖x - y‖ ≤ s⁻¹ * r := by gcongr
      _ = ρ := by rw [hs]; field_simp
  -- the point `z = a • y + b • w ∈ C` satisfies `homothety c (1 + s) z = x`
  refine ⟨a • y + b • w, hCc hy hwC ha0.le hb0.le hab, ?_⟩
  have hz : a • y + b • w = c + a • (x - c) := by
    rw [hw, smul_add, smul_smul, mul_div_cancel₀ _ hb0.ne']
    have : b • c = c - a • c := by
      rw [show b = 1 - a by linarith, sub_smul, one_smul]
    rw [this]
    simp only [smul_sub]
    abel
  rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, hz, add_sub_cancel_left, smul_smul,
    hab', one_smul, sub_add_cancel]

/-- **Case of nonempty interior**: if `closedBall c ρ ⊆ C`, then
`vol(C_{4δ}) - vol(C_δ) ≤ K₁ δ` for `0 < δ ≤ 1` (dilation trick). -/
theorem volume_annulus_le_of_ball_subset {C : Set (Euc d)} (hC : IsCompact C) (hCc : Convex ℝ C)
    {c : Euc d} {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall c ρ ⊆ C) :
    ∃ K₁ : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (volume (cthickening (4 * δ) C \ cthickening δ C)).toReal ≤ K₁ * δ := by
  refine ⟨4 / ρ * d * (1 + 4 / ρ) ^ d * (volume C).toReal, fun δ hδ hδ1 => ?_⟩
  have hsub : cthickening δ C ⊆ cthickening (4 * δ) C := cthickening_mono (by linarith) C
  have hfin : volume (cthickening δ C) ≠ ⊤ :=
    (hC.cthickening : IsCompact (cthickening δ C)).measure_lt_top.ne
  have hfin4 : volume (cthickening (4 * δ) C) ≠ ⊤ :=
    (hC.cthickening : IsCompact (cthickening (4 * δ) C)).measure_lt_top.ne
  rw [measure_sdiff hsub isClosed_cthickening.measurableSet.nullMeasurableSet hfin,
    ENNReal.toReal_sub_of_le (measure_mono hsub) hfin4]
  set a : ℝ := 4 * δ / ρ with ha
  have ha0 : 0 ≤ a := by positivity
  have h1 : (volume (cthickening (4 * δ) C)).toReal ≤ (1 + a) ^ d * (volume C).toReal := by
    have hle := measure_mono (μ := volume)
      (cthickening_subset_homothety hC hCc hρ hball (by linarith : 0 < 4 * δ))
    rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at hle
    have hne : ENNReal.ofReal |(1 + 4 * δ / ρ) ^ d| * volume C ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.measure_lt_top.ne
    refine (ENNReal.toReal_mono hne hle).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity)]
  have h2 : (volume C).toReal ≤ (volume (cthickening δ C)).toReal :=
    ENNReal.toReal_mono hfin (measure_mono (self_subset_cthickening _))
  have h3 : (1 + a) ^ d - 1 ≤ a * d * (1 + a) ^ d := pow_sub_one_le_mul ha0 d
  have h4 : (1 + a) ^ d ≤ (1 + 4 / ρ) ^ d := by
    refine pow_le_pow_left₀ (by positivity) ?_ d
    rw [ha]
    have : 4 * δ / ρ ≤ 4 / ρ := by
      rw [div_le_div_iff_of_pos_right hρ]; linarith
    linarith
  have hvol : 0 ≤ (volume C).toReal := ENNReal.toReal_nonneg
  calc (volume (cthickening (4 * δ) C)).toReal - (volume (cthickening δ C)).toReal
      ≤ (1 + a) ^ d * (volume C).toReal - (volume C).toReal := by linarith
    _ = ((1 + a) ^ d - 1) * (volume C).toReal := by ring
    _ ≤ a * d * (1 + a) ^ d * (volume C).toReal := by gcongr
    _ ≤ a * d * (1 + 4 / ρ) ^ d * (volume C).toReal := by gcongr
    _ = 4 / ρ * d * (1 + 4 / ρ) ^ d * (volume C).toReal * δ := by rw [ha]; ring

/-- A convex set with empty interior lies in a hyperplane through any of its points. -/
theorem exists_unit_normal_of_interior_empty {C : Set (Euc d)} (hCc : Convex ℝ C)
    (hint : interior C = ∅) {x₀ : Euc d} (hx₀ : x₀ ∈ C) :
    ∃ u : Euc d, ‖u‖ = 1 ∧ ∀ x ∈ C, ⟪u, x - x₀⟫ = 0 := by
  have hspan : affineSpan ℝ C ≠ ⊤ := by
    intro h
    have := hCc.interior_nonempty_iff_affineSpan_eq_top.2 h
    rw [hint] at this
    exact Set.not_nonempty_empty this
  have hdir : (affineSpan ℝ C).direction < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hspan ?_
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x₀, mem_affineSpan ℝ hx₀⟩).1 h
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hdir
  set n : Euc d :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm (LinearMap.toContinuousLinearMap f) with hn
  have hnf : ∀ v, ⟪n, v⟫ = f v := fun v => by
    rw [hn, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  have hn0 : n ≠ 0 := by
    intro h
    apply hf0
    ext v
    have := hnf v
    rw [h, inner_zero_left] at this
    simp [← this]
  refine ⟨‖n‖⁻¹ • n, ?_, fun x hx => ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hn0)]
  · rw [real_inner_smul_left, hnf]
    have hmem : x -ᵥ x₀ ∈ (affineSpan ℝ C).direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hx₀)
    have := hker hmem
    rw [LinearMap.mem_ker, vsub_eq_sub] at this
    rw [this, mul_zero]

/-- The compression `v ↦ v - (1 - δ) ⟪u, v⟫ u` along a unit vector `u`. -/
noncomputable def compression (u : Euc d) (δ : ℝ) : Euc d →ₗ[ℝ] Euc d :=
  LinearMap.id - (1 - δ) • (innerₛₗ ℝ u).smulRight u

theorem compression_apply (u : Euc d) (δ : ℝ) (v : Euc d) :
    compression u δ v = v - (1 - δ) • (⟪u, v⟫ • u) := by
  simp [compression, innerₛₗ_apply_apply]

/-- `∑ i, u i * u i = 1` for a unit vector. -/
theorem sum_mul_self_eq_one {u : Euc d} (hu : ‖u‖ = 1) : ∑ i, u i * u i = 1 := by
  have := real_inner_self_eq_norm_sq u
  rw [hu, one_pow, PiLp.inner_apply] at this
  simp only [RCLike.inner_apply, conj_trivial] at this
  simpa [sq] using this

/-- The compression has determinant `δ`. -/
theorem det_compression {u : Euc d} (hu : ‖u‖ = 1) (δ : ℝ) :
    LinearMap.det (compression u δ) = δ := by
  classical
  set b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis with hb
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b (compression u δ) =
      1 + Matrix.replicateCol Unit (fun i => -(1 - δ) * u i) * Matrix.replicateRow Unit u := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Fintype.sum_unique, Matrix.replicateCol_apply, Matrix.replicateRow_apply, hb,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, compression_apply,
      EuclideanSpace.inner_single_right]
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
      RCLike.conj_to_real, one_mul]
    ring
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct]
  have : ∑ i, u i * (-(1 - δ) * u i) = -(1 - δ) * ∑ i, u i * u i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, sum_mul_self_eq_one hu]
  ring

/-- The slab `{|⟪u, v⟫| ≤ 4δ, ‖v‖ ≤ R + 4}` is contained in the compression (by `δ`) of the slab
`{|⟪u, v⟫| ≤ 4, ‖v‖ ≤ R + 8}`. -/
theorem slab_subset_image_compression {u : Euc d} (hu : ‖u‖ = 1) {δ R : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    {v : Euc d | |⟪u, v⟫| ≤ 4 * δ ∧ ‖v‖ ≤ R + 4} ⊆
      compression u δ '' {v : Euc d | |⟪u, v⟫| ≤ 4 ∧ ‖v‖ ≤ R + 8} := by
  rintro v ⟨hv1, hv2⟩
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  refine ⟨v + (δ⁻¹ - 1) • (⟪u, v⟫ • u), ⟨?_, ?_⟩, ?_⟩
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, huu, mul_one]
    have : ⟪u, v⟫ + (δ⁻¹ - 1) * ⟪u, v⟫ = δ⁻¹ * ⟪u, v⟫ := by ring
    rw [this, abs_mul, abs_of_pos (inv_pos.2 hδ)]
    calc δ⁻¹ * |⟪u, v⟫| ≤ δ⁻¹ * (4 * δ) := by gcongr
      _ = 4 := by field_simp
  · have h1 : 0 ≤ δ⁻¹ - 1 := by
      rw [sub_nonneg]; exact one_le_inv_iff₀.2 ⟨hδ, hδ1⟩
    calc ‖v + (δ⁻¹ - 1) • (⟪u, v⟫ • u)‖ ≤ ‖v‖ + ‖(δ⁻¹ - 1) • (⟪u, v⟫ • u)‖ := norm_add_le _ _
      _ = ‖v‖ + (δ⁻¹ - 1) * (|⟪u, v⟫| * 1) := by
          rw [norm_smul, norm_smul, hu, Real.norm_of_nonneg h1, Real.norm_eq_abs]
      _ ≤ (R + 4) + (δ⁻¹ - 1) * (4 * δ * 1) := by gcongr
      _ = R + 8 - 4 * δ := by field_simp; ring
      _ ≤ R + 8 := by linarith
  · rw [compression_apply, inner_add_right, real_inner_smul_right, real_inner_smul_right, huu,
      mul_one]
    have : (1 - δ) • ((⟪u, v⟫ + (δ⁻¹ - 1) * ⟪u, v⟫) • u) = (δ⁻¹ - 1) • (⟪u, v⟫ • u) := by
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
      ring
    rw [this, add_sub_cancel_right]

/-- **Case of empty interior**: `vol(C_{4δ}) ≤ K₁ δ` for `0 < δ ≤ 1`, since `C` lies in a
hyperplane (compression along the normal). -/
theorem volume_cthickening_le_of_interior_empty {C : Set (Euc d)} (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCne : C.Nonempty) (hint : interior C = ∅) :
    ∃ K₁ : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (volume (cthickening (4 * δ) C)).toReal ≤ K₁ * δ := by
  obtain ⟨x₀, hx₀⟩ := hCne
  obtain ⟨u, hu, hu0⟩ := exists_unit_normal_of_interior_empty hCc hint hx₀
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall x₀
  refine ⟨(volume (Metric.closedBall (0 : Euc d) (R + 8))).toReal, fun δ hδ hδ1 => ?_⟩
  set S₁ : Set (Euc d) := {v | |⟪u, v⟫| ≤ 4 ∧ ‖v‖ ≤ R + 8} with hS₁
  set Sδ : Set (Euc d) := {v | |⟪u, v⟫| ≤ 4 * δ ∧ ‖v‖ ≤ R + 4} with hSδ
  -- `C_{4δ} ⊆ x₀ +ᵥ Sδ`
  have hsub : cthickening (4 * δ) C ⊆ x₀ +ᵥ Sδ := by
    intro y hy
    rw [hC.cthickening_eq_biUnion_closedBall (by linarith)] at hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hyz
    have hzR : ‖z - x₀‖ ≤ R := by
      have := hR hz; rwa [Metric.mem_closedBall, dist_eq_norm] at this
    refine ⟨y - x₀, ⟨?_, ?_⟩, by simp⟩
    · have : ⟪u, y - x₀⟫ = ⟪u, y - z⟫ := by
        rw [show y - x₀ = (y - z) + (z - x₀) by abel, inner_add_right, hu0 z hz, add_zero]
      rw [this]
      calc |⟪u, y - z⟫| ≤ ‖u‖ * ‖y - z‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * (4 * δ) := by gcongr; rw [hu]
        _ = 4 * δ := one_mul _
    · calc ‖y - x₀‖ = ‖(y - z) + (z - x₀)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y - z‖ + ‖z - x₀‖ := norm_add_le _ _
        _ ≤ 4 * δ + R := by gcongr
        _ ≤ R + 4 := by linarith
  have hS₁ball : S₁ ⊆ Metric.closedBall (0 : Euc d) (R + 8) := fun v hv => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.2
  calc (volume (cthickening (4 * δ) C)).toReal
      ≤ (volume (x₀ +ᵥ Sδ)).toReal :=
        ENNReal.toReal_mono (by rw [measure_vadd]; exact
          ((measure_mono (slab_subset_image_compression hu hδ hδ1)).trans_lt (by
            rw [Measure.addHaar_image_linearMap]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              ((measure_mono hS₁ball).trans_lt (measure_closedBall_lt_top (μ := volume))))).ne)
          (measure_mono hsub)
    _ = (volume Sδ).toReal := by rw [measure_vadd]
    _ ≤ (volume (compression u δ '' S₁)).toReal :=
        ENNReal.toReal_mono (by
          rw [Measure.addHaar_image_linearMap]
          exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((measure_mono hS₁ball).trans_lt (measure_closedBall_lt_top (μ := volume)))).ne)
          (measure_mono (slab_subset_image_compression hu hδ hδ1))
    _ = δ * (volume S₁).toReal := by
        rw [Measure.addHaar_image_linearMap, det_compression hu, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos hδ]
    _ ≤ δ * (volume (Metric.closedBall (0 : Euc d) (R + 8))).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
          (measure_closedBall_lt_top (μ := volume)).ne (measure_mono hS₁ball)) hδ.le
    _ = (volume (Metric.closedBall (0 : Euc d) (R + 8))).toReal * δ := mul_comm _ _

/-- **Volume of a convex annulus** (paper: "Convexity of `C` gives `∫|∇χ_δ| ≤ C₂`, uniformly for
small `δ`: the `2δ`-parallel body has volume increment `O(δ)`. This holds whether or not `C` has
interior"). -/
theorem exists_volume_annulus_le {C : Set (Euc d)} (hC : IsCompact C) (hCc : Convex ℝ C) :
    ∃ K₁ : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (volume (cthickening (4 * δ) C \ cthickening δ C)).toReal ≤ K₁ * δ := by
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact ⟨0, fun δ _ _ => by simp [cthickening_empty]⟩
  by_cases hint : (interior C).Nonempty
  · obtain ⟨c, hc⟩ := hint
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hc)
    exact volume_annulus_le_of_ball_subset hC hCc (half_pos hρ)
      ((Metric.closedBall_subset_ball (half_lt_self hρ)).trans hball)
  · rw [Set.not_nonempty_iff_eq_empty] at hint
    obtain ⟨K₁, hK₁⟩ := volume_cthickening_le_of_interior_empty hC hCc hCne hint
    refine ⟨K₁, fun δ hδ hδ1 => ?_⟩
    have hfin : volume (cthickening (4 * δ) C) ≠ ⊤ :=
      (hC.cthickening : IsCompact (cthickening (4 * δ) C)).measure_lt_top.ne
    exact (ENNReal.toReal_mono hfin (measure_mono sdiff_subset)).trans (hK₁ δ hδ hδ1)

/-- For a nonempty closed set `C` and `x ∉ C`, `x` is eventually outside `cthickening (4δ) C` as
`δ ↓ 0`. -/
theorem eventually_notMem_cthickening {C : Set (Euc d)} (hC : IsCompact C) {x : Euc d}
    (hx : x ∉ C) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), x ∉ cthickening (4 * δ) C := by
  obtain ⟨r, hr, hrC⟩ := Metric.mem_nhds_iff.1 (hC.isClosed.isOpen_compl.mem_nhds hx)
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < r / 4)] with δ hδ hmem
  rw [hC.cthickening_eq_biUnion_closedBall (by linarith [hδ.1])] at hmem
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hmem
  refine hrC (Metric.mem_ball.2 ?_) hy
  have := Metric.mem_closedBall.1 hxy
  rw [dist_comm]
  linarith [hδ.2]

/-- **Including the critical set** (paper (A.weak-global)): a weak inequality
`∫ ⟪A, ∇ψ⟫ ≤ Λ ∫ h ψ`, valid for nonnegative smooth test functions supported away from a compact
convex set `C ⊆ Ω` on which the continuous flux `A` vanishes, extends to all nonnegative smooth
test functions of the open set `Ω` (for bounded measurable `A`, bounded measurable `h ≥ 0` and
`Λ ≥ 0`). -/
theorem weak_ineq_of_off_critical {Ω : Set (Euc d)} {C : Set (Euc d)}
    (hC : IsCompact C) (hCc : Convex ℝ C) (hCΩ : C ⊆ Ω) {A : Euc d → Euc d} (hAm : Measurable A)
    (hAb : ∃ B : ℝ, ∀ x, ‖A x‖ ≤ B) (hAc : ContinuousOn A Ω) (hAC : ∀ x ∈ C, A x = 0)
    {h : Euc d → ℝ} (hhm : Measurable h) (hhb : ∃ B : ℝ, ∀ x, |h x| ≤ B) (hh0 : ∀ x, 0 ≤ h x)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hoff : ∀ ψ : Euc d → ℝ, IsTestFn (Ω \ C) ψ → (∀ x, 0 ≤ ψ x) →
      ∫ x, ⟪A x, gradient ψ x⟫ ≤ Λ * ∫ x, h x * ψ x)
    {ψ : Euc d → ℝ} (hψ : IsTestFn Ω ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    ∫ x, ⟪A x, gradient ψ x⟫ ≤ Λ * ∫ x, h x * ψ x := by
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact hoff ψ (by simpa using hψ) hψ0
  obtain ⟨K₀, hK₀, hcut⟩ := exists_cutoff_family (d := d)
  choose χ hχ using hcut C
  obtain ⟨K₁, hK₁⟩ := exists_volume_annulus_le hC hCc
  obtain ⟨BA, hBA⟩ := hAb
  obtain ⟨Bh, hBh⟩ := hhb
  set S := tsupport ψ with hS
  have hSc : IsCompact S := hψ.hasCompactSupport
  have hSΩ : S ⊆ Ω := hψ.supp_subset
  have hψc : Continuous ψ := hψ.contDiff.continuous
  have hψ1 : ContDiff ℝ 1 ψ := hψ.contDiff_one
  have hgc : Continuous (gradient ψ) := continuous_gradient hψ1
  obtain ⟨Bψ, hBψ⟩ := exists_bound_of_zero_outside hSc hψc.continuousOn
    fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hBψ' : ∀ x, |ψ x| ≤ Bψ := fun x => by simpa only [Real.norm_eq_abs] using hBψ x
  have hBψ0 : 0 ≤ Bψ := (norm_nonneg _).trans (hBψ 0)
  obtain ⟨Bg, hBg⟩ := exists_bound_of_zero_outside hSc hgc.continuousOn
    fun x hx => gradient_eq_zero_of_notMem_tsupport hx
  have hgS : ∀ x ∉ S, gradient ψ x = 0 := fun x hx => gradient_eq_zero_of_notMem_tsupport hx
  have hψS : ∀ x ∉ S, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  -- the integrand `⟪A, ∇ψ⟫` is bounded, measurable, supported in `S`
  have hIm : Measurable fun x => ⟪A x, gradient ψ x⟫ := hAm.inner hgc.measurable
  have hIint : Integrable fun x => ⟪A x, gradient ψ x⟫ := by
    refine Integrable.mono' ((integrable_indicator_iff hSc.measurableSet).2
      (integrableOn_const (C := BA * Bg) hSc.measure_lt_top.ne)) hIm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hBA x) (hBg x) (norm_nonneg _) ((norm_nonneg _).trans (hBA x)))
    · rw [indicator_of_notMem hx, hgS x hx, inner_zero_right, norm_zero]
  have hhψint : Integrable fun x => h x * ψ x := by
    refine Integrable.mono' ((integrable_indicator_iff hSc.measurableSet).2
      (integrableOn_const (C := Bh * Bψ) hSc.measure_lt_top.ne))
      (hhm.mul hψc.measurable).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hBh x) (hBψ' x) (abs_nonneg _) ((abs_nonneg _).trans (hBh x))
    · rw [indicator_of_notMem hx, hψS x hx, mul_zero, norm_zero]
  -- the modulus of `A` near `C` on `S`
  have hmod : ∀ ε > 0, ∃ r > 0, ∀ x ∈ S, ∀ y ∈ C, dist x y < r → ‖A x‖ ≤ ε := by
    intro ε hε
    have hSC : IsCompact (S ∪ C) := hSc.union hC
    have huc := hSC.uniformContinuousOn_of_continuous (hAc.mono (union_subset hSΩ hCΩ))
    obtain ⟨r, hr, hmodr⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
    refine ⟨r, hr, fun x hx y hy hxy => ?_⟩
    have := hmodr x (Or.inl hx) y (Or.inr hy) hxy
    rw [hAC y hy, dist_zero_right] at this
    exact this.le
  -- the cutoff inequality with error, for `0 < δ ≤ 1`
  have key : ∀ δ, 0 < δ → δ ≤ 1 → ∀ ε, 0 ≤ ε →
      (∀ x ∈ S, ∀ y ∈ C, dist x y ≤ 4 * δ → ‖A x‖ ≤ ε) →
      ∫ x, χ δ x * ⟪A x, gradient ψ x⟫ ≤ (Λ * ∫ x, h x * ψ x) + Bψ * ε * (K₀ * K₁) := by
    intro δ hδ hδ1 ε hε hεA
    obtain ⟨hχs, hχ0, hχ1, hχC, hχout, hχg⟩ := hχ δ hδ
    have hχc : Continuous (χ δ) := hχs.continuous
    have hχ1' : ContDiff ℝ 1 (χ δ) := hχs.of_le (by exact_mod_cast le_top)
    -- `∇χ` vanishes off the annulus `R`
    set R := cthickening (4 * δ) C \ cthickening δ C with hR
    have hRm : MeasurableSet R :=
      isClosed_cthickening.measurableSet.diff isClosed_cthickening.measurableSet
    have hRfin : volume R ≠ ⊤ :=
      ((measure_mono sdiff_subset).trans_lt
        (hC.cthickening : IsCompact (cthickening (4 * δ) C)).measure_lt_top).ne
    have hgχ : ∀ x, x ∉ R → gradient (χ δ) x = 0 := by
      intro x hx
      rw [hR, Set.mem_sdiff, not_and_or, not_not] at hx
      rcases hx with hx | hx
      · refine gradient_eq_zero_of_eventuallyEq_const (c := 1) ?_
        filter_upwards [isClosed_cthickening.isOpen_compl.mem_nhds hx] with y hy
        exact hχout y hy
      · refine gradient_eq_zero_of_eventuallyEq_const (c := 0) ?_
        have hmem : thickening (2 * δ) C ∈ 𝓝 x :=
          isOpen_thickening.mem_nhds
            ((cthickening_subset_thickening' (by linarith) (by linarith) C) hx)
        filter_upwards [hmem] with y hy
        exact hχC y (thickening_subset_cthickening _ _ hy)
    -- the test function `ψ χ`
    have hφs : ContDiff ℝ (⊤ : ℕ∞) (ψ * χ δ) := hψ.contDiff.mul hχs
    have hφsupp : tsupport (ψ * χ δ) ⊆ Ω \ C := by
      intro x hx
      refine ⟨hSΩ (tsupport_mul_subset_left hx), fun hxC => ?_⟩
      have h1 : x ∈ tsupport (χ δ) := tsupport_mul_subset_right hx
      have h2 : tsupport (χ δ) ⊆ (thickening (2 * δ) C)ᶜ := by
        refine closure_minimal ?_ isOpen_thickening.isClosed_compl
        intro y hy hyC
        exact hy (hχC y (thickening_subset_cthickening _ _ hyC))
      exact h2 h1 (self_subset_thickening (by linarith) C hxC)
    have hφc : HasCompactSupport (ψ * χ δ) := hψ.hasCompactSupport.mul_right
    have hφ0 : ∀ x, 0 ≤ (ψ * χ δ) x := fun x => mul_nonneg (hψ0 x) (hχ0 x)
    have hφg : ∀ x, gradient (ψ * χ δ) x = ψ x • gradient (χ δ) x + χ δ x • gradient ψ x :=
      fun x => gradient_mul (hψ1.differentiable one_ne_zero x) (hχ1'.differentiable one_ne_zero x)
    have hineq : ∫ x, ⟪A x, gradient (ψ * χ δ) x⟫ ≤ Λ * ∫ x, h x * (ψ * χ δ) x := by
      by_cases hφz : ψ * χ δ = 0
      · have h1 : ∀ x, gradient (ψ * χ δ) x = 0 := fun x => by
          rw [hφz]; exact gradient_const x (0 : ℝ)
        have h2 : ∀ x, (ψ * χ δ) x = 0 := fun x => by rw [hφz]; rfl
        simp only [h1, h2, inner_zero_right, mul_zero, integral_zero, le_refl]
      · exact hoff (ψ * χ δ) ⟨hφs, hφc, hφsupp, hφz⟩ hφ0
    -- split the gradient
    have hI2m : Measurable fun x => ψ x * ⟪A x, gradient (χ δ) x⟫ :=
      hψc.measurable.mul (hAm.inner (continuous_gradient hχ1').measurable)
    have hI2int : Integrable fun x => ψ x * ⟪A x, gradient (χ δ) x⟫ := by
      refine Integrable.mono' ((integrable_indicator_iff hSc.measurableSet).2
        (integrableOn_const (C := Bψ * (BA * (K₀ / δ))) hSc.measure_lt_top.ne))
        hI2m.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx, norm_mul]
        refine mul_le_mul (hBψ x) ((norm_inner_le_norm _ _).trans
          (mul_le_mul (hBA x) (hχg x) (norm_nonneg _) ((norm_nonneg _).trans (hBA x))))
          (norm_nonneg _) hBψ0
      · rw [indicator_of_notMem hx, hψS x hx, zero_mul, norm_zero]
    have hI1int : Integrable fun x => χ δ x * ⟪A x, gradient ψ x⟫ := by
      refine hIint.norm.mono' (hχc.measurable.mul hIm).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (hχ0 x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 x)
    have hsplit : ∫ x, ⟪A x, gradient (ψ * χ δ) x⟫ =
        (∫ x, χ δ x * ⟪A x, gradient ψ x⟫) + ∫ x, ψ x * ⟪A x, gradient (χ δ) x⟫ := by
      calc ∫ x, ⟪A x, gradient (ψ * χ δ) x⟫
          = ∫ x, (χ δ x * ⟪A x, gradient ψ x⟫ + ψ x * ⟪A x, gradient (χ δ) x⟫) := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            simp only [hφg, inner_add_right, real_inner_smul_right]
            ring
        _ = _ := integral_add hI1int hI2int
    -- the error term
    have herr : |∫ x, ψ x * ⟪A x, gradient (χ δ) x⟫| ≤ Bψ * ε * (K₀ * K₁) := by
      have hbound : ∀ x, |ψ x * ⟪A x, gradient (χ δ) x⟫| ≤
          R.indicator (fun _ => Bψ * ε * (K₀ / δ)) x := by
        intro x
        by_cases hxR : x ∈ R
        · rw [indicator_of_mem hxR, abs_mul]
          by_cases hx : x ∈ S
          · have hAx : ‖A x‖ ≤ ε := by
              have hmem := hxR.1
              rw [hC.cthickening_eq_biUnion_closedBall (by linarith)] at hmem
              obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hmem
              exact hεA x hx y hy (Metric.mem_closedBall.1 hxy)
            calc |ψ x| * |⟪A x, gradient (χ δ) x⟫|
                ≤ Bψ * (ε * (K₀ / δ)) := by
                  refine mul_le_mul (hBψ' x) ?_ (abs_nonneg _) hBψ0
                  refine (abs_real_inner_le_norm _ _).trans ?_
                  exact mul_le_mul hAx (hχg x) (norm_nonneg _) hε
              _ = Bψ * ε * (K₀ / δ) := by ring
          · rw [hψS x hx, abs_zero, zero_mul]
            positivity
        · rw [indicator_of_notMem hxR, hgχ x hxR, inner_zero_right, mul_zero, abs_zero]
      calc |∫ x, ψ x * ⟪A x, gradient (χ δ) x⟫|
          ≤ ∫ x, |ψ x * ⟪A x, gradient (χ δ) x⟫| := by
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
              (fun x => ψ x * ⟪A x, gradient (χ δ) x⟫)
        _ ≤ ∫ x, R.indicator (fun _ => Bψ * ε * (K₀ / δ)) x :=
            integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
              ((integrable_indicator_iff hRm).2 (integrableOn_const hRfin))
              (Eventually.of_forall hbound)
        _ = (volume R).toReal * (Bψ * ε * (K₀ / δ)) := by
            rw [integral_indicator hRm, setIntegral_const, smul_eq_mul, measureReal_def]
        _ ≤ K₁ * δ * (Bψ * ε * (K₀ / δ)) :=
            mul_le_mul_of_nonneg_right (hK₁ δ hδ hδ1) (by positivity)
        _ = Bψ * ε * (K₀ * K₁) := by field_simp
    -- assemble
    have hΛle : Λ * ∫ x, h x * (ψ * χ δ) x ≤ Λ * ∫ x, h x * ψ x := by
      refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg ?_ hhψint ?_) hΛ
      · exact Eventually.of_forall fun x => mul_nonneg (hh0 x) (hφ0 x)
      · refine Eventually.of_forall fun x => ?_
        simp only [Pi.mul_apply]
        rw [← mul_assoc]
        exact mul_le_of_le_one_right (mul_nonneg (hh0 x) (hψ0 x)) (hχ1 x)
    have := neg_le_abs (∫ x, ψ x * ⟪A x, gradient (χ δ) x⟫)
    linarith [hsplit, hineq, hΛle, herr]
  -- the limit `δ ↓ 0` of the cutoff integrals
  have hlim : Tendsto (fun δ => ∫ x, χ δ x * ⟪A x, gradient ψ x⟫) (𝓝[>] 0)
      (𝓝 (∫ x, ⟪A x, gradient ψ x⟫)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖⟪A x, gradient ψ x⟫‖)
      ?_ ?_ hIint.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact ((hχ δ hδ).1.continuous.measurable.mul hIm).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      refine Eventually.of_forall fun x => ?_
      obtain ⟨-, hχ0, hχ1, -⟩ := hχ δ hδ
      rw [norm_mul, Real.norm_of_nonneg (hχ0 x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 x)
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ C
      · simp [hAC x hx]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_notMem_cthickening hC hx, self_mem_nhdsWithin] with δ hδ hδ0
        rw [(hχ δ hδ0).2.2.2.2.1 x hδ, one_mul]
  -- conclusion
  have hfinal : ∀ ε > 0,
      ∫ x, ⟪A x, gradient ψ x⟫ ≤ (Λ * ∫ x, h x * ψ x) + Bψ * ε * (K₀ * K₁) := by
    intro ε hε
    obtain ⟨r, hr, hrA⟩ := hmod ε hε
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < min 1 (r / 8))] with δ hδ
    have hδ1 : δ ≤ 1 := hδ.2.le.trans (min_le_left _ _)
    have hδr : 4 * δ < r := by
      have := hδ.2.trans_le (min_le_right _ _)
      linarith
    exact key δ hδ.1 hδ1 ε hε.le fun x hx y hy hxy => hrA x hx y hy (by linarith)
  refine le_of_forall_pos_le_add fun ε' hε' => ?_
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ Bψ * (K₀ * K₁) ≤ M :=
    ⟨|Bψ * (K₀ * K₁)|, abs_nonneg _, le_abs_self _⟩
  have hMpos : 0 < M + 1 := by positivity
  refine (hfinal (ε' / (M + 1)) (by positivity)).trans ?_
  have hle : Bψ * (ε' / (M + 1)) * (K₀ * K₁) ≤ ε' := by
    calc Bψ * (ε' / (M + 1)) * (K₀ * K₁) = (Bψ * (K₀ * K₁)) * (ε' / (M + 1)) := by ring
      _ ≤ M * (ε' / (M + 1)) := mul_le_mul_of_nonneg_right hM (by positivity)
      _ = ε' * (M / (M + 1)) := by ring
      _ ≤ ε' * 1 := by gcongr; exact (div_le_one hMpos).2 (by linarith)
      _ = ε' := mul_one _
  linarith

end Cutoff

/-! ### Integration by parts on `ℝ^d` and the fundamental lemma of the calculus of variations -/

section IBP

/-- The divergence `div W (x) = ∑ i ⟪e_i, DW(x) e_i⟫` of a vector field on `ℝ^d`. -/
noncomputable def divergence (W : Euc d → Euc d) (x : Euc d) : ℝ :=
  ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), fderiv ℝ W x (EuclideanSpace.single i (1 : ℝ))⟫

/-- A function vanishing outside a compact set has compact support. -/
theorem hasCompactSupport_of_zero_outside {E : Type*} [NormedAddCommGroup E] {K : Set (Euc d)}
    (hK : IsCompact K) {g : Euc d → E} (hg : ∀ x ∉ K, g x = 0) : HasCompactSupport g :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun x hx => by_contra fun h => hx (hg x h)) hK.isClosed)

/-- A function continuous on an open set `Ω`, multiplied by a continuous function vanishing
outside a closed subset `K ⊆ Ω`, is continuous on `ℝ^d`. -/
theorem continuous_mul_of_continuousOn {Ω : Set (Euc d)} (hΩ : IsOpen Ω) {f g : Euc d → ℝ}
    (hf : ContinuousOn f Ω) (hg : Continuous g) {K : Set (Euc d)} (hK : IsClosed K)
    (hKΩ : K ⊆ Ω) (hgK : ∀ x ∉ K, g x = 0) : Continuous fun x => f x * g x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (hf.continuousAt (hΩ.mem_nhds hx)).mul hg.continuousAt
  · have hmem : Kᶜ ∈ 𝓝 x := hK.isOpen_compl.mem_nhds fun h => hx (hKΩ h)
    refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    rw [hgK y hy, mul_zero]

/-- **Integration by parts on `ℝ^d`**: for a vector field `W ∈ C¹(Ω)` (`Ω` open) and
`ψ ∈ C¹` with compact support in `Ω`, `∫ ⟪W, ∇ψ⟫ = -∫ ψ · div W`. -/
theorem integral_inner_gradient_eq_neg_integral_divergence {Ω : Set (Euc d)} (hΩ : IsOpen Ω)
    {W : Euc d → Euc d} (hW : ContDiffOn ℝ 1 W Ω) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψs : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∫ x, ⟪W x, gradient ψ x⟫ = -∫ x, ψ x * divergence W x := by
  set e : Fin d → Euc d := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have hWd : ∀ x ∈ Ω, DifferentiableAt ℝ W x := fun x hx =>
    (hW.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hx)
  have hWc : ContinuousOn W Ω := hW.continuousOn
  have hWf : ContinuousOn (fderiv ℝ W) Ω := hW.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hψc : Continuous ψ := hψ.continuous
  have hψf : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hψK : ∀ x ∉ tsupport ψ, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hψfK : ∀ x ∉ tsupport ψ, fderiv ℝ ψ x = 0 := fun x hx => by
    by_contra h; exact hx (support_fderiv_subset ℝ (Function.mem_support.2 h))
  have hK : IsClosed (tsupport ψ) := isClosed_tsupport ψ
  -- the components `f i = ⟪e i, W⟫`
  set f : Fin d → Euc d → ℝ := fun i x => ⟪e i, W x⟫ with hf
  have hfd : ∀ i, ∀ x ∈ Ω, HasFDerivAt (f i) ((innerSL ℝ (e i)).comp (fderiv ℝ W x)) x :=
    fun i x hx => (innerSL ℝ (e i)).hasFDerivAt.comp x (hWd x hx).hasFDerivAt
  have hfc : ∀ i, ContinuousOn (f i) Ω := fun i =>
    (innerSL ℝ (e i)).continuous.comp_continuousOn hWc
  have hfderiv : ∀ i, ∀ x ∈ Ω, fderiv ℝ (f i) x (e i) = ⟪e i, fderiv ℝ W x (e i)⟫ :=
    fun i x hx => by rw [(hfd i x hx).fderiv]; rfl
  have hfderivc : ∀ i, ContinuousOn (fun x => fderiv ℝ (f i) x (e i)) Ω := fun i =>
    (continuousOn_const.inner (hWf.clm_apply continuousOn_const)).congr fun x hx =>
      hfderiv i x hx
  -- integrability of the three products
  have hint1 : ∀ i, Integrable fun x => f i x * fderiv ℝ ψ x (e i) := fun i =>
    (continuous_mul_of_continuousOn hΩ (hfc i) (hψf.clm_apply continuous_const) hK hψΩ
      fun x hx => by rw [hψfK x hx]; rfl).integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun x hx => by rw [hψfK x hx]; simp)
  have hint2 : ∀ i, Integrable fun x => fderiv ℝ (f i) x (e i) * ψ x := fun i =>
    (continuous_mul_of_continuousOn hΩ (hfderivc i) hψc hK hψΩ hψK).integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun x hx => by rw [hψK x hx, mul_zero])
  have hint3 : ∀ i, Integrable fun x => f i x * ψ x := fun i =>
    (continuous_mul_of_continuousOn hΩ (hfc i) hψc hK hψΩ hψK).integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun x hx => by rw [hψK x hx, mul_zero])
  -- integration by parts in each coordinate direction
  have hibp : ∀ i, ∫ x, f i x * fderiv ℝ ψ x (e i) = -∫ x, fderiv ℝ (f i) x (e i) * ψ x :=
    fun i => integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := e i) (hint2 i) (hint1 i)
      (hint3 i) (fun x hx => (hfd i x (hψΩ hx)).differentiableAt)
      (fun x _ => hψ.differentiable one_ne_zero x)
  -- summing over `i`
  have hL : ∫ x, ⟪W x, gradient ψ x⟫ = ∑ i, ∫ x, f i x * fderiv ℝ ψ x (e i) := by
    rw [← integral_finsetSum _ fun i _ => hint1 i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner (W x) (gradient ψ x)
    simp only [EuclideanSpace.basisFun_apply] at this
    dsimp only
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ⟪W x, EuclideanSpace.single i (1 : ℝ)⟫ * ⟪EuclideanSpace.single i (1 : ℝ), gradient ψ x⟫ =
      ⟪EuclideanSpace.single i (1 : ℝ), W x⟫ * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))
    rw [real_inner_comm (EuclideanSpace.single i (1 : ℝ)) (W x),
      real_inner_comm (gradient ψ x) (EuclideanSpace.single i (1 : ℝ)), inner_gradient_left]
  have hR : ∑ i, -∫ x, fderiv ℝ (f i) x (e i) * ψ x = -∫ x, ψ x * divergence W x := by
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hint2 i]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : x ∈ Ω
    · simp only [divergence, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfderiv i x hx, mul_comm]
    · rw [hψK x fun h => hx (hψΩ h)]
      simp
  rw [hL, ← hR]
  exact Finset.sum_congr rfl fun i _ => hibp i

/-- **The fundamental lemma of the calculus of variations**: if `g` is continuous on the open
set `Ω` and `∫ g ψ = 0` for every nonnegative smooth test function `ψ` of `Ω`, then `g = 0` on
`Ω`. -/
theorem eq_zero_of_integral_mul_testFn_eq_zero {Ω : Set (Euc d)} (hΩ : IsOpen Ω)
    {g : Euc d → ℝ} (hg : ContinuousOn g Ω)
    (h : ∀ ψ : Euc d → ℝ, IsTestFn Ω ψ → (∀ x, 0 ≤ ψ x) → ∫ x, g x * ψ x = 0) {x₀ : Euc d}
    (hx₀ : x₀ ∈ Ω) : g x₀ = 0 := by
  by_contra hne
  have hcont : ContinuousAt g x₀ := hg.continuousAt (hΩ.mem_nhds hx₀)
  have hev : ∀ᶠ y in 𝓝 x₀, dist (g y) (g x₀) < |g x₀| / 2 :=
    Metric.tendsto_nhds.1 hcont _ (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hev (hΩ.mem_nhds hx₀))
  set φ : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hφdef
  have hφsupp : tsupport φ ⊆ Metric.ball x₀ r := by
    rw [φ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by simp [hφdef]; linarith)
  have hφx₀ : φ x₀ = 1 :=
    φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by simp [hφdef]; positivity))
  have hφ : IsTestFn Ω φ :=
    ⟨φ.contDiff, φ.hasCompactSupport, hφsupp.trans fun y hy => (hball hy).2, fun h0 => by
      have := congrFun h0 x₀
      rw [hφx₀, Pi.zero_apply] at this
      exact one_ne_zero this⟩
  have h0 := h φ hφ φ.nonneg'
  have hφK : ∀ y ∉ tsupport φ, φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  -- the sign of `g` on the ball
  have hsign : ∀ y ∈ Metric.ball x₀ r, 0 < g y * g x₀ := fun y hy => by
    have h1 : dist (g y) (g x₀) < |g x₀| / 2 := (hball hy).1
    rw [Real.dist_eq, abs_sub_lt_iff] at h1
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · rw [abs_of_neg hneg] at h1
      nlinarith
    · rw [abs_of_pos hpos] at h1
      nlinarith
  have hcontφ : Continuous fun y => g y * g x₀ * φ y :=
    continuous_mul_of_continuousOn hΩ (hg.mul continuousOn_const) φ.continuous
      (isClosed_tsupport φ) (hφsupp.trans fun y hy => (hball hy).2) hφK
  have hpos : 0 < ∫ y, g y * g x₀ * φ y := by
    refine hcontφ.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hasCompactSupport_of_zero_outside φ.hasCompactSupport fun y hy => by
        rw [hφK y hy, mul_zero])
      (fun y => ?_) (x := x₀) ?_
    · by_cases hy : y ∈ Metric.ball x₀ r
      · exact mul_nonneg (hsign y hy).le φ.nonneg
      · rw [hφK y fun h => hy (hφsupp h), mul_zero]
        exact le_rfl
    · rw [hφx₀, mul_one]
      exact (hsign x₀ (Metric.mem_ball_self hr)).ne'
  have : ∫ y, g y * g x₀ * φ y = g x₀ * ∫ y, g y * φ y := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [this, h0, mul_zero] at hpos
  exact lt_irrefl _ hpos

end IBP

/-! ### The strong form of the eigenvalue equation on the `C²` region -/

section StrongForm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- `∇F` is `C^∞` away from the origin. -/
theorem IsSmoothStrictNorm.contDiffOn_gradient : ContDiffOn ℝ (⊤ : ℕ∞) (gradient F) {0}ᶜ := by
  have h := hF.contDiffOn.fderiv_of_isOpen (m := (⊤ : ℕ∞)) isOpen_compl_singleton
    (by simp)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h

/-- The flux `a = F^{p-1} ∇F` is `C^∞` away from the origin. -/
theorem IsSmoothStrictNorm.contDiffOn_flux (p : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (flux p F) {0}ᶜ :=
  (hF.contDiffOn.rpow_const_of_ne fun x hx => (hF.pos x hx).ne').smul hF.contDiffOn_gradient

end StrongForm

end Komlos.Literature
