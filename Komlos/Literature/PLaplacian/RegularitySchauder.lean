import Komlos.Literature.PLaplacian.GradientBound
import Komlos.Literature.PLaplacian.RegularityCampanato
import Komlos.Literature.PLaplacian.SchauderAux
import Komlos.Literature.PLaplacian.CampanatoIteration
import Komlos.Literature.PLaplacian.SchauderHarmonic
import Komlos.Literature.PLaplacian.EigenfunctionAux

/-!
# The `C²` step off the critical set: ellipticity of the flux and linear Schauder theory

Towards Mosconi–Riey–Squassina 2024, Proposition 4.5 and the sentence of paper Appendix A,
*Eigenfunction inputs*: "Where `∇u_i ≠ 0`, the equation is locally uniformly elliptic with smooth
coefficients, so local elliptic regularity gives `u_i ∈ C²`".

## Main results

* `IsSmoothStrictNorm.inner_fderiv_flux_pos` — `A(ξ) = Da(ξ)` is positive definite for `ξ ≠ 0`
  (paper (A.ellipticity), pointwise).
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff Interval

namespace Komlos.Literature

variable {d : ℕ}

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- `∇F` is `C^∞` away from the origin. (The same statement is
`IsSmoothStrictNorm.contDiffOn_gradient` in `WangXia/EigenvalueConvexAssemblyAux`, which is not
imported here.) -/
theorem contDiffOn_gradient' : ContDiffOn ℝ (⊤ : ℕ∞) (gradient F) {0}ᶜ := by
  have h := hF.contDiffOn.fderiv_of_isOpen (m := (⊤ : ℕ∞)) isOpen_compl_singleton (by simp)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h

/-- The flux `a = F^{p-1} ∇F` is `C^∞` away from the origin. -/
theorem contDiffOn_flux' (p : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (flux p F) {0}ᶜ :=
  (hF.contDiffOn.rpow_const_of_ne fun x hx => (hF.pos x hx).ne').smul hF.contDiffOn_gradient'

/-- The flux is differentiable at every `ξ ≠ 0`. -/
theorem hasFDerivAt_flux' (p : ℝ) {ξ : Euc d} (hξ : ξ ≠ 0) :
    HasFDerivAt (flux p F) (fderiv ℝ (flux p F) ξ) ξ :=
  (((hF.contDiffOn_flux' p).differentiableOn (by simp)).differentiableAt
    (isOpen_compl_singleton.mem_nhds hξ)).hasFDerivAt

/-- **Positive definiteness of `A(ξ) = Da(ξ)`** for `ξ ≠ 0` (paper (A.ellipticity), the lower
bound, pointwise): along the line `t ↦ ξ + t ζ`, with `h(t) = F(ξ + t ζ)`,
`⟪A(ξ) ζ, ζ⟫ = h^{p-2} ((p-1) h'² + h h'')`, while `D²(F²)(ξ)[ζ, ζ] = 2 (h'² + h h'') > 0`
(`hessian_sq_pos`) and `h'' ≥ 0` (convexity of `F`). -/
theorem inner_fderiv_flux_pos {p : ℝ} (hp : 1 < p) {ξ : Euc d} (hξ : ξ ≠ 0) {ζ : Euc d}
    (hζ : ζ ≠ 0) : 0 < ⟪fderiv ℝ (flux p F) ξ ζ, ζ⟫ := by
  have hF2 : ContDiffAt ℝ 2 F ξ := (hF.contDiffAt hξ).of_le (WithTop.coe_le_coe.2 le_top)
  have hf : 0 < F ξ := hF.pos ξ hξ
  have hline : HasDerivAt (fun t : ℝ => ξ + t • ζ) ζ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add ξ
  have hne : ∀ᶠ t : ℝ in 𝓝 0, ξ + t • ζ ≠ 0 := by
    have hc : Continuous fun t : ℝ => ξ + t • ζ := by fun_prop
    exact hc.continuousAt.eventually (isOpen_compl_singleton.mem_nhds (by simpa using hξ))
  have hh0 : HasDerivAt (fun t : ℝ => F (ξ + t • ζ)) (fderiv ℝ F ξ ζ) 0 := by
    simpa using (eventually_hasDerivAt_line hF2 ζ).self_of_nhds
  have hh' := hasDerivAt_fderiv_line hF2 ζ
  -- (i) `⟪A(ξ)ζ, ζ⟫` is the derivative of `t ↦ ⟪a(ξ + tζ), ζ⟫ = h^{p-1} h'`
  have h1 : HasDerivAt (fun t : ℝ => ⟪flux p F (ξ + t • ζ), ζ⟫)
      ⟪fderiv ℝ (flux p F) ξ ζ, ζ⟫ 0 := by
    have hc : HasDerivAt (fun t : ℝ => flux p F (ξ + t • ζ)) (fderiv ℝ (flux p F) ξ ζ) 0 :=
      (hF.hasFDerivAt_flux' p hξ).comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    simpa using hc.inner ℝ (hasDerivAt_const (0 : ℝ) ζ)
  have e : (fun t : ℝ => ⟪flux p F (ξ + t • ζ), ζ⟫) =
      fun t => F (ξ + t • ζ) ^ (p - 1) * fderiv ℝ F (ξ + t • ζ) ζ := by
    funext t
    rw [flux, real_inner_smul_left, inner_gradient_left]
  have h2 : HasDerivAt (fun t : ℝ => F (ξ + t • ζ) ^ (p - 1) * fderiv ℝ F (ξ + t • ζ) ζ)
      (fderiv ℝ F ξ ζ * (p - 1) * F ξ ^ (p - 1 - 1) * fderiv ℝ F ξ ζ +
        F ξ ^ (p - 1) * fderiv ℝ (fderiv ℝ F) ξ ζ ζ) 0 := by
    have hr := hh0.rpow_const (p := p - 1) (Or.inl (by simpa using hf.ne'))
    have h := hr.mul hh'
    rw [zero_smul, add_zero] at h
    exact h
  rw [e] at h1
  have hAeq := h1.unique h2
  -- (ii) `D²(F²)(ξ)[ζ,ζ] = 2 (h'² + h h'')`
  have hev : (fun t : ℝ => fderiv ℝ (fun x => F x ^ 2) (ξ + t • ζ) ζ) =ᶠ[𝓝 0]
      fun t => 2 * F (ξ + t • ζ) * fderiv ℝ F (ξ + t • ζ) ζ := by
    filter_upwards [hne] with t ht
    have hd : HasFDerivAt F (fderiv ℝ F (ξ + t • ζ)) (ξ + t • ζ) :=
      ((hF.contDiffAt ht).differentiableAt (by simp)).hasFDerivAt
    rw [(hd.pow 2).fderiv]
    simp
  have h3 : HasDerivAt (fun t : ℝ => 2 * F (ξ + t • ζ) * fderiv ℝ F (ξ + t • ζ) ζ)
      (2 * fderiv ℝ F ξ ζ * fderiv ℝ F ξ ζ + 2 * F ξ * fderiv ℝ (fderiv ℝ F) ξ ζ ζ) 0 := by
    have h := (hh0.const_mul 2).mul hh'
    rw [zero_smul, add_zero] at h
    exact h
  have hsq := (hasDerivAt_fderiv_line (hF.contDiffAt_sq hξ) ζ).unique
    (h3.congr_of_eventuallyEq hev)
  have hpos := hF.hessian_sq_pos ξ hξ ζ hζ
  rw [hsq] at hpos
  -- (iii) `h'' ≥ 0` by convexity of `h`
  have hq : 0 ≤ fderiv ℝ (fderiv ℝ F) ξ ζ ζ := by
    obtain ⟨δ, hδ, hδne⟩ := Metric.eventually_nhds_iff.1 hne
    have hconv : ConvexOn ℝ univ (fun t : ℝ => F (ξ + t • ζ)) := by
      have h0 := hF.convexOn.comp_affineMap (AffineMap.lineMap ξ (ξ + ζ))
      have e0 : (F ∘ AffineMap.lineMap ξ (ξ + ζ)) = fun t : ℝ => F (ξ + t • ζ) := by
        funext t
        simp [AffineMap.lineMap_apply, add_comm]
      rwa [e0, preimage_univ] at h0
    have hdiff : ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun t : ℝ => F (ξ + t • ζ))
        (fderiv ℝ F (ξ + t • ζ) ζ) t := by
      intro t ht
      have htδ : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_lt]
        exact ⟨ht.1, ht.2⟩
      have hd : HasFDerivAt F (fderiv ℝ F (ξ + t • ζ)) (ξ + t • ζ) :=
        ((hF.contDiffAt (hδne htδ)).differentiableAt (by simp)).hasFDerivAt
      have hl : HasDerivAt (fun t : ℝ => ξ + t • ζ) ζ t := by
        simpa using ((hasDerivAt_id t).smul_const ζ).const_add ξ
      exact hd.comp_hasDerivAt t hl
    have hmono := (hconv.subset (subset_univ _) (convex_Ioo _ _)).monotoneOn_deriv
      fun t ht => (hdiff t ht).differentiableAt
    have hlim := hh'.tendsto_slope_zero_right
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    have ht' : t ∈ Ioo (-δ) δ := ⟨by linarith [ht.1], ht.2⟩
    have h0' : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
    have hm := hmono h0' ht' ht.1.le
    rw [(hdiff 0 h0').deriv, (hdiff t ht').deriv] at hm
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hm ⊢
    exact mul_nonneg (inv_nonneg.2 ht.1.le) (by linarith)
  -- (iv) combine
  have hkey : 0 < (p - 1) * (fderiv ℝ F ξ ζ * fderiv ℝ F ξ ζ) +
      F ξ * fderiv ℝ (fderiv ℝ F) ξ ζ ζ := by
    have hfq := mul_nonneg hf.le hq
    rcases le_total p 2 with hp2 | hp2
    · nlinarith [mul_pos (sub_pos.2 hp) (by linarith : (0 : ℝ) < fderiv ℝ F ξ ζ *
        fderiv ℝ F ξ ζ + F ξ * fderiv ℝ (fderiv ℝ F) ξ ζ ζ)]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p - 2)
        (mul_self_nonneg (fderiv ℝ F ξ ζ))]
  have hfp : F ξ ^ (p - 1) = F ξ ^ (p - 1 - 1) * F ξ := by
    rw [← Real.rpow_add_one hf.ne']
    ring_nf
  rw [hAeq, hfp]
  have e2 : fderiv ℝ F ξ ζ * (p - 1) * F ξ ^ (p - 1 - 1) * fderiv ℝ F ξ ζ +
      F ξ ^ (p - 1 - 1) * F ξ * fderiv ℝ (fderiv ℝ F) ξ ζ ζ =
      F ξ ^ (p - 1 - 1) * ((p - 1) * (fderiv ℝ F ξ ζ * fderiv ℝ F ξ ζ) +
        F ξ * fderiv ℝ (fderiv ℝ F) ξ ζ ζ) := by ring
  rw [e2]
  exact mul_pos (Real.rpow_pos_of_pos hf _) hkey

/-- **Uniform ellipticity, boundedness and Lipschitz continuity of `A = Da` on a compact convex
set avoiding `0`** (paper (A.ellipticity) on compact sets): there are `μ > 0`, `Λ`, `L` with
`μ ‖ζ‖² ≤ ⟪A(ξ)ζ, ζ⟫`, `‖A(ξ)‖ ≤ Λ` and `‖A(ξ) - A(η)‖ ≤ L ‖ξ - η‖` for `ξ, η ∈ N`. -/
theorem exists_fderiv_flux_bounds {p : ℝ} (hp : 1 < p) {N : Set (Euc d)} (hN : IsCompact N)
    (hNcv : Convex ℝ N) (hN0 : (0 : Euc d) ∉ N) :
    ∃ μ Λ L : ℝ, 0 < μ ∧ 0 ≤ Λ ∧ 0 ≤ L ∧
      (∀ ξ ∈ N, ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪fderiv ℝ (flux p F) ξ ζ, ζ⟫) ∧
      (∀ ξ ∈ N, ‖fderiv ℝ (flux p F) ξ‖ ≤ Λ) ∧
      (∀ ξ ∈ N, ∀ η ∈ N, ‖fderiv ℝ (flux p F) ξ - fderiv ℝ (flux p F) η‖ ≤ L * ‖ξ - η‖) := by
  have hN0' : N ⊆ {0}ᶜ := fun ξ hξ h => hN0 (by rw [mem_singleton_iff] at h; rwa [← h])
  have hA1 : ContDiffOn ℝ 1 (fderiv ℝ (flux p F)) {0}ᶜ :=
    (hF.contDiffOn_flux' p).fderiv_of_isOpen isOpen_compl_singleton (WithTop.coe_le_coe.2 le_top)
  have hAc : ContinuousOn (fderiv ℝ (flux p F)) N := hA1.continuousOn.mono hN0'
  obtain ⟨μ, hμ, hμA⟩ : ∃ μ : ℝ, 0 < μ ∧
      ∀ ξ ∈ N, ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪fderiv ℝ (flux p F) ξ ζ, ζ⟫ := by
    by_cases hne : (N ×ˢ Metric.sphere (0 : Euc d) 1).Nonempty
    · have hcont : ContinuousOn (fun z : Euc d × Euc d => ⟪fderiv ℝ (flux p F) z.1 z.2, z.2⟫)
          (N ×ˢ Metric.sphere (0 : Euc d) 1) :=
        ((hAc.comp continuousOn_fst fun z hz => hz.1).clm_apply continuousOn_snd).inner
          continuousOn_snd
      obtain ⟨z, hz, hmin⟩ := (hN.prod (isCompact_sphere 0 1)).exists_isMinOn hne hcont
      refine ⟨⟪fderiv ℝ (flux p F) z.1 z.2, z.2⟫, hF.inner_fderiv_flux_pos hp
        (fun h => hN0 (h ▸ hz.1)) (ne_zero_of_mem_sphere' hz.2), fun ξ hξ ζ => ?_⟩
      rcases eq_or_ne ζ 0 with rfl | hζ
      · simp
      have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
      have hn' : ‖ζ‖ ≠ 0 := hn.ne'
      have hmem : (ξ, ‖ζ‖⁻¹ • ζ) ∈ N ×ˢ Metric.sphere (0 : Euc d) 1 :=
        ⟨hξ, by simp [norm_smul, inv_mul_cancel₀ hn']⟩
      have h1 : ⟪fderiv ℝ (flux p F) z.1 z.2, z.2⟫ ≤
          ⟪fderiv ℝ (flux p F) ξ (‖ζ‖⁻¹ • ζ), ‖ζ‖⁻¹ • ζ⟫ := hmin hmem
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
      calc ⟪fderiv ℝ (flux p F) z.1 z.2, z.2⟫ * ‖ζ‖ ^ 2
          ≤ ‖ζ‖⁻¹ * (‖ζ‖⁻¹ * ⟪fderiv ℝ (flux p F) ξ ζ, ζ⟫) * ‖ζ‖ ^ 2 := by gcongr
        _ = ⟪fderiv ℝ (flux p F) ξ ζ, ζ⟫ := by field_simp
    · refine ⟨1, one_pos, fun ξ hξ ζ => ?_⟩
      rcases eq_or_ne ζ 0 with rfl | hζ
      · simp
      exact absurd ⟨(ξ, ‖ζ‖⁻¹ • ζ), hξ,
        by simp [norm_smul, inv_mul_cancel₀ (norm_pos_iff.2 hζ).ne']⟩ hne
  obtain ⟨Λ, hΛ⟩ := hN.exists_bound_of_continuousOn hAc
  obtain ⟨K, hK⟩ := (hA1.mono hN0').exists_lipschitzOnWith one_ne_zero hNcv hN
  refine ⟨μ, max Λ 0, K, hμ, le_max_right _ _, K.2, hμA,
    fun ξ hξ => (hΛ ξ hξ).trans (le_max_left _ _), fun ξ hξ η hη => ?_⟩
  have h := hK.dist_le_mul ξ hξ η hη
  rwa [dist_eq_norm, dist_eq_norm] at h

/-- **Mean value formula for the flux** on a convex set avoiding `0`:
`a(η) - a(ξ) = (∫₀¹ A(ξ + t (η - ξ)) dt) (η - ξ)`. -/
theorem flux_sub_eq_integral_fderiv (p : ℝ) {N : Set (Euc d)} (hNcv : Convex ℝ N)
    (hN0 : (0 : Euc d) ∉ N) {ξ η : Euc d} (hξ : ξ ∈ N) (hη : η ∈ N) :
    flux p F η - flux p F ξ =
      (∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F) (ξ + t • (η - ξ))) (η - ξ) := by
  have hne : ∀ t ∈ uIcc (0 : ℝ) 1, ξ + t • (η - ξ) ≠ 0 := by
    intro t ht h
    rw [uIcc_of_le zero_le_one] at ht
    exact hN0 (h ▸ hNcv.add_smul_sub_mem hξ hη ht)
  have hA1 : ContinuousOn (fderiv ℝ (flux p F)) {0}ᶜ :=
    (hF.contDiffOn_flux' p).continuousOn_fderiv_of_isOpen isOpen_compl_singleton
      (by exact_mod_cast le_top)
  have hcont : ContinuousOn (fun t : ℝ => fderiv ℝ (flux p F) (ξ + t • (η - ξ))) (uIcc 0 1) :=
    hA1.comp (by fun_prop : Continuous fun t : ℝ => ξ + t • (η - ξ)).continuousOn
      fun t ht => hne t ht
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => flux p F (ξ + t • (η - ξ)))
      (fderiv ℝ (flux p F) (ξ + t • (η - ξ)) (η - ξ)) t := by
    intro t ht
    have hl : HasDerivAt (fun t : ℝ => ξ + t • (η - ξ)) (η - ξ) t := by
      simpa using ((hasDerivAt_id t).smul_const (η - ξ)).const_add ξ
    exact (hF.hasFDerivAt_flux' p (hne t ht)).comp_hasDerivAt t hl
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((ContinuousLinearMap.apply ℝ (Euc d) (η - ξ)).continuous.comp_continuousOn
      hcont).intervalIntegrable
  rw [one_smul, zero_smul, add_zero, add_sub_cancel] at hFTC
  rw [← hFTC]
  exact (ContinuousLinearMap.apply ℝ (Euc d) (η - ξ)).intervalIntegral_comp_comm
    hcont.intervalIntegrable

/-- **Bounds for the averaged derivative** `∫₀¹ A(ξ + t (η - ξ)) dt` over segments in a convex
set `N` avoiding `0` on which `A = Da` is uniformly elliptic, bounded and Lipschitz. -/
theorem integral_fderiv_flux_bounds (p : ℝ) {N : Set (Euc d)} (hNcv : Convex ℝ N)
    (hN0 : (0 : Euc d) ∉ N) {μ Λ L : ℝ}
    (hμ : ∀ ξ ∈ N, ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪fderiv ℝ (flux p F) ξ ζ, ζ⟫)
    (hΛ : ∀ ξ ∈ N, ‖fderiv ℝ (flux p F) ξ‖ ≤ Λ)
    (hL : ∀ ξ ∈ N, ∀ η ∈ N, ‖fderiv ℝ (flux p F) ξ - fderiv ℝ (flux p F) η‖ ≤ L * ‖ξ - η‖)
    (hL0 : 0 ≤ L) {ξ η ξ' η' : Euc d} (hξ : ξ ∈ N) (hη : η ∈ N) (hξ' : ξ' ∈ N) (hη' : η' ∈ N) :
    (∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F) (ξ + t • (η - ξ))) ζ, ζ⟫) ∧
      ‖∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F) (ξ + t • (η - ξ))‖ ≤ Λ ∧
      ‖(∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F) (ξ + t • (η - ξ))) -
        ∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F) (ξ' + t • (η' - ξ'))‖ ≤
          L * (‖ξ - ξ'‖ + ‖η - η'‖) := by
  have hseg : ∀ {a b : Euc d}, a ∈ N → b ∈ N → ∀ t ∈ uIcc (0 : ℝ) 1, a + t • (b - a) ∈ N := by
    intro a b ha hb t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact hNcv.add_smul_sub_mem ha hb ht
  have hA1 : ContinuousOn (fderiv ℝ (flux p F)) {0}ᶜ :=
    (hF.contDiffOn_flux' p).continuousOn_fderiv_of_isOpen isOpen_compl_singleton
      (by exact_mod_cast le_top)
  have hcont : ∀ {a b : Euc d}, a ∈ N → b ∈ N →
      ContinuousOn (fun t : ℝ => fderiv ℝ (flux p F) (a + t • (b - a))) (uIcc 0 1) := by
    intro a b ha hb
    exact hA1.comp (by fun_prop : Continuous fun t : ℝ => a + t • (b - a)).continuousOn
      fun t ht h => hN0 (h ▸ hseg ha hb t ht)
  have hIoc : ∀ t ∈ Ι (0 : ℝ) 1, t ∈ uIcc (0 : ℝ) 1 := fun t ht => by
    rw [uIoc_of_le zero_le_one] at ht
    rw [uIcc_of_le zero_le_one]
    exact ⟨ht.1.le, ht.2⟩
  refine ⟨fun ζ => ?_, ?_, ?_⟩
  · set T : (Euc d →L[ℝ] Euc d) →L[ℝ] ℝ :=
      (innerSL ℝ ζ).comp (ContinuousLinearMap.apply ℝ (Euc d) ζ) with hT
    have h1 := T.intervalIntegral_comp_comm ((hcont hξ hη).intervalIntegrable (μ := volume))
    have h2 : ∀ t : ℝ, T (fderiv ℝ (flux p F) (ξ + t • (η - ξ))) =
        ⟪fderiv ℝ (flux p F) (ξ + t • (η - ξ)) ζ, ζ⟫ := fun t => by
      rw [hT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply,
        real_inner_comm]
    have h3 : T (∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F) (ξ + t • (η - ξ))) =
        ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F) (ξ + t • (η - ξ))) ζ, ζ⟫ := by
      rw [hT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply,
        real_inner_comm]
    rw [← h3, ← h1]
    simp only [h2]
    calc μ * ‖ζ‖ ^ 2 = ∫ t in (0 : ℝ)..1, μ * ‖ζ‖ ^ 2 := by simp
      _ ≤ ∫ t in (0 : ℝ)..1, ⟪fderiv ℝ (flux p F) (ξ + t • (η - ξ)) ζ, ζ⟫ := by
          refine intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const ?_
            fun t ht => hμ _ (hseg hξ hη t (by rwa [uIcc_of_le zero_le_one])) ζ
          exact (((hcont hξ hη).clm_apply continuousOn_const).inner
            continuousOn_const).intervalIntegrable
  · refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht =>
      hΛ _ (hseg hξ hη t (hIoc t ht))).trans ?_
    simp
  · rw [← intervalIntegral.integral_sub (hcont hξ hη).intervalIntegrable
      (hcont hξ' hη').intervalIntegrable]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := L * (‖ξ - ξ'‖ + ‖η - η'‖)) fun t ht => ?_).trans (by simp)
    have ht' := hIoc t ht
    rw [uIcc_of_le zero_le_one] at ht'
    refine (hL _ (hseg hξ hη t (hIoc t ht)) _ (hseg hξ' hη' t (hIoc t ht))).trans ?_
    have e : ξ + t • (η - ξ) - (ξ' + t • (η' - ξ')) = (1 - t) • (ξ - ξ') + t • (η - η') := by
      module
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    calc ‖(1 - t) • (ξ - ξ') + t • (η - η')‖ ≤ ‖(1 - t) • (ξ - ξ')‖ + ‖t • (η - η')‖ :=
          norm_add_le _ _
      _ = (1 - t) * ‖ξ - ξ'‖ + t * ‖η - η'‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht'.2]),
            Real.norm_of_nonneg ht'.1]
      _ ≤ ‖ξ - ξ'‖ + ‖η - η'‖ := by
          nlinarith [norm_nonneg (ξ - ξ'), norm_nonneg (η - η'), ht'.1, ht'.2]

end IsSmoothStrictNorm


/-! ### Linear Schauder theory

The interior Schauder estimate is proved by Campanato's method. Its independent inputs
are the constant-coefficient estimates in `SchauderConst`, the Sobolev freezing comparison
in `FrozenRegularity` and `SchauderFreezing`, and the interpolation bootstrap in
`InteriorGradientBound`. The elementary iteration is imported from `CampanatoIteration`.

`SchauderHarmonic` assembles the uniform comparison and perturbed decay only after the
bootstrap has established the uniform gradient bound. Thus the proof has no circular
dependency on the uniform Schauder estimate proved below.
-/

/-- **Perturbed gradient-energy decay** (Gilbarg–Trudinger, Theorem 8.32, steps 1–2 of Campanato's
method). Writing `Φ(x, s) = ∫_{B(x,s)} ‖∇w - (∇w)_{B(x,s)}‖²` for the gradient energy oscillation,
the constant-coefficient base decay (each `∂_i h` solves `div(A(x₀) ∇·) = 0`; a linear change of
variables reduces `A(x₀)` to the Laplacian, whose solutions have the Morrey decay `Φ_h(ρ) ≲
(ρ/r)^{d+2} Φ_h(r)` from interior derivative estimates) together with the freezing comparison
`‖w - h‖` on `B_r` (energy error `≲ [A]_α² r^{2α}(Φ(r) + data)` via Caccioppoli and the
`α`-Hölder continuity of `A`) yield, uniformly over `x₀, A, g, w` obeying the standing hypotheses,
`Φ(x, ρ) ≤ C₁ (ρ/r)^{d+2} Φ(x, r) + C₂ r^{d+2α}` for all `0 < ρ ≤ r ≤ R₀`.

This is supplied by the proved local harmonic/Weyl theory, the variational frozen
replacement, and the independent interpolation bootstrap in this repository. -/
theorem schauder_perturbed_energy_decay (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hμ : 0 < μ) (hR : 0 < R) :
    ∃ C₁ C₂ R₀ : ℝ, 0 < R₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.ball x₀ R, ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ →
        (∫ y in Metric.closedBall x ρ,
            ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
          C₁ * (ρ / r) ^ ((d : ℝ) + 2) *
            (∫ y in Metric.closedBall x r,
              ‖gradient w y - (⨍ z in Metric.closedBall x r, gradient w z)‖ ^ 2) +
          C₂ * r ^ ((d : ℝ) + 2 * α) := by
  -- The whole Campanato step is assembled in `Komlos/Literature/PLaplacian/SchauderHarmonic.lean`,
  -- which builds the `ℝ^d` weakly-harmonic theory this rests on (`IsWeakConstSolutionOn`, the
  -- linear change of variables `y = A₀^{1/2} x` reducing the constant-coefficient equation to the
  -- Laplacian, and the `L²` Campanato excess `sqExcess`), and reduces the statement to the two
  -- classical inputs `exists_constCoeff_gradient_lipschitz` (the `ℝ^d` interior derivative
  -- estimate: Weyl's lemma and the mean value property, neither in Mathlib) and
  -- `exists_frozen_comparison` (the freezing comparison).
  exact exists_perturbed_sqExcess_decay d (Λ := Λ) hα hα1 hμ hR

/-- **Interior gradient sup bound** (the `C¹` half of Gilbarg–Trudinger, Theorem 8.32). A `C¹`
weak solution of `div(A ∇w) = g` with `A` uniformly elliptic, bounded and `α`-Hölder and
`|g|, |w| ≤ Λ` has an interior gradient bound `‖∇w‖ ≤ M` on `B_R`, with `M` depending only on
`d, α, μ, Λ, R` — in particular *uniformly over the family of data*.

**Proved** here from two inputs:

* the uniform Caccioppoli energy estimate `exists_linear_energy_bound`
  (`Komlos.Literature.PLaplacian.GradientBound`), which bounds `∫_{B(z, 3R/8)} ‖∇w‖²` by a
  constant depending only on `d, μ, Λ, R`;
* the perturbed decay `schauder_perturbed_energy_decay` (still cited).

The energy bound both starts the Campanato iteration — replacing the a priori sup bound that
GT 8.32 feeds into it, which is what made the argument circular — and, through the mean-value
principle "some point of `B̄(x, r)` has `‖∇w‖² ≤ (E+1)/|B_r|`", converts the resulting *uniform*
Hölder estimate for `∇w` into the pointwise bound. -/
theorem schauder_interior_gradient_bound (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hμ : 0 < μ) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.closedBall x₀ R, ‖gradient w x‖ ≤ M := by
  -- The route, uniform in `x₀, A, g, w` (Gilbarg–Trudinger, Theorem 8.32):
  --  1. `exists_linear_energy_bound` (Caccioppoli, proved in `PLaplacian/GradientBound.lean`)
  --     gives a uniform `L²` bound `E` for `∇w` on the balls `B̄(z, 3R/8)`;
  --  2. this starts the `campanato_iteration_uniform` applied to
  --     `Φ(z, ρ) = ∫_{B(z,ρ)} ‖∇w - (∇w)_{B(z,ρ)}‖²` with the perturbed decay
  --     `schauder_perturbed_energy_decay`, giving `Φ(z, ρ) ≤ C₃ ρ^{d+2α}`;
  --  3. `setIntegral_norm_sub_setAverage_le_of_sq` and `exists_holder_of_campanato_uniform`
  --     turn this into a *uniform* Hölder bound `‖∇w z - ∇w z'‖ ≤ B |z - z'|^α` for nearby
  --     points of `B̄(x₀, 5R/4)`;
  --  4. finally, the `L²` bound produces, in every ball `B̄(x, ρ)`, a point `y` with
  --     `‖∇w y‖² ≤ (E + 1)/|B_ρ|`, and the Hölder bound transports it to `x`.
  have hω : (0 : ℝ) < volume.real (Metric.closedBall (0 : Euc d) 1) := volume_real_closedBall_pos
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  -- 1. The Caccioppoli energy bound, used on balls of radius `R / 4`.
  obtain ⟨E, hE0, hE⟩ := exists_linear_energy_bound d (μ := μ) (Λ := Λ) (R := R / 4) hμ
    (by linarith)
  -- 2. The perturbed energy decay, used on balls of radius `R / 4`.
  obtain ⟨C₁, C₂, Rd, hRd, hC₁0, hC₂0, hdec⟩ := schauder_perturbed_energy_decay d
    (α := α) (μ := μ) (Λ := Λ) (R := R / 4) hα hα1 hμ (by linarith)
  -- 3. The working scale `R₁`.
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = min Rd (R / 8) := ⟨_, rfl⟩
  have hR₁pos : 0 < R₁ := by rw [hR₁]; exact lt_min hRd (by linarith)
  have hR₁Rd : R₁ ≤ Rd := by rw [hR₁]; exact min_le_left _ _
  have hR₁R : R₁ ≤ R / 8 := by rw [hR₁]; exact min_le_right _ _
  -- 4. The (uniform) Campanato iteration constant.
  have hβ0 : (0 : ℝ) ≤ (d : ℝ) + 2 * α := by linarith
  have hβγ : (d : ℝ) + 2 * α < (d : ℝ) + 2 := by linarith
  obtain ⟨c₀, hc₀0, hc₀⟩ := campanato_iteration_uniform (a := C₁) (b := C₂)
    (β := (d : ℝ) + 2 * α) (γ := (d : ℝ) + 2) (R₀ := R₁) hC₁0 hC₂0 hβ0 hβγ hR₁pos
  -- 5. The resulting `L²`- and `L¹`-Campanato constants.
  have hRβ : (0 : ℝ) < R₁ ^ ((d : ℝ) + 2 * α) := Real.rpow_pos_of_pos hR₁pos _
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ,
      C₃ = c₀ * (E + C₂ * R₁ ^ ((d : ℝ) + 2 * α)) * (R₁ ^ ((d : ℝ) + 2 * α))⁻¹ := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by
    have h3 : (0 : ℝ) ≤ C₂ * R₁ ^ ((d : ℝ) + 2 * α) := mul_nonneg hC₂0 hRβ.le
    rw [hC₃]
    exact mul_nonneg (mul_nonneg hc₀0 (by linarith)) (inv_nonneg.2 hRβ.le)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ,
      C₄ = (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := by rw [hC₄]; linarith
  -- 6. The uniform Hölder constant coming out of Campanato's criterion.
  obtain ⟨B, hB0, hB⟩ := exists_holder_of_campanato_uniform (d := d) (E := Euc d)
    (α := α) (C := C₄) (R₀ := R₁) hα hC₄0
  -- 7. The final constant.
  obtain ⟨rr, hrr⟩ : ∃ rr : ℝ, rr = R₁ / 2 := ⟨_, rfl⟩
  have hrr0 : 0 < rr := by rw [hrr]; linarith
  have hvolpos : (0 : ℝ) < rr ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) := by
    exact mul_pos (pow_pos hrr0 d) hω
  refine ⟨Real.sqrt ((E + 1) / (rr ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))) +
      B * rr ^ α,
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hB0 (Real.rpow_nonneg hrr0.le _)), ?_⟩
  intro x₀ A g w hell hAbd hAhol hgc hgbd hw hwbd hwlip hweak
  have hΛ0 : 0 ≤ Λ :=
    le_trans (norm_nonneg (A x₀)) (hAbd x₀ (Metric.mem_ball_self (by linarith)))
  -- `A` is continuous, being `α`-Hölder.
  have hAcont : ContinuousOn A (Metric.ball x₀ (2 * R)) := by
    refine Metric.continuousOn_iff.2 fun b hb ε hε => ?_
    obtain ⟨δ, hδ0, -, hδε⟩ :=
      exists_pos_le_mul_rpow_lt (α := α) (B := Λ) (R := 1) (ε := ε) hα hΛ0 one_pos hε
    refine ⟨δ, hδ0, fun a ha hab => ?_⟩
    have h1 : ‖A a - A b‖ ≤ Λ * dist a b ^ α := hAhol a ha b hb
    have h2 : Λ * dist a b ^ α ≤ Λ * δ ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hab.le hα.le) hΛ0
    rw [dist_eq_norm]
    linarith
  -- Continuity of `∇w` on the ball where the equation holds.
  have hgradcont : ContinuousOn (gradient w) (Metric.ball x₀ (2 * R)) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hw.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
  -- Restriction of every hypothesis to a ball of radius `R / 2` around an interior point.
  have hsubball : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      Metric.ball z (2 * (R / 4)) ⊆ Metric.ball x₀ (2 * R) := by
    intro z hz y hy
    rw [Metric.mem_ball] at hy
    rw [Metric.mem_ball]
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ < 2 * (R / 4) + 3 * R / 2 := by linarith
      _ ≤ 2 * R := by linarith
  have hAcont' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ContinuousOn A (Metric.ball z (2 * (R / 4))) := fun z hz => hAcont.mono (hsubball z hz)
  have hell' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A y ζ, ζ⟫ :=
    fun z hz y hy => hell y (hsubball z hz hy)
  have hAbd' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), ‖A y‖ ≤ Λ :=
    fun z hz y hy => hAbd y (hsubball z hz hy)
  have hAhol' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), ∀ y' ∈ Metric.ball z (2 * (R / 4)),
        ‖A y - A y'‖ ≤ Λ * dist y y' ^ α :=
    fun z hz y hy y' hy' => hAhol y (hsubball z hz hy) y' (hsubball z hz hy')
  have hgc' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ContinuousOn g (Metric.ball z (2 * (R / 4))) := fun z hz => hgc.mono (hsubball z hz)
  have hgbd' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), |g y| ≤ Λ :=
    fun z hz y hy => hgbd y (hsubball z hz hy)
  have hw' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ContDiffOn ℝ 1 w (Metric.ball z (2 * (R / 4))) := fun z hz => hw.mono (hsubball z hz)
  have hwbd' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), |w y| ≤ Λ :=
    fun z hz y hy => hwbd y (hsubball z hz hy)
  have hwlip' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∃ Cw : ℝ, ∀ y ∈ Metric.ball z (2 * (R / 4)), ∀ y' ∈ Metric.ball z (2 * (R / 4)),
        ‖gradient w y - gradient w y'‖ ≤ Cw * dist y y' ^ α := by
    intro z hz
    obtain ⟨Cw, hCw⟩ := hwlip
    exact ⟨Cw, fun y hy y' hy' => hCw y (hsubball z hz hy) y' (hsubball z hz hy')⟩
  have hweak' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball z (2 * (R / 4)) →
        ∫ y, ⟪A y (gradient w y), gradient ψ y⟫ = ∫ y, g y * ψ y :=
    fun z hz ψ h1 h2 h3 => hweak ψ h1 h2 (h3.trans (hsubball z hz))
  -- The Caccioppoli energy bound, centred anywhere in `closedBall x₀ (3R/2)`.
  have hEz : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      (∫ y in Metric.closedBall z (3 * (R / 4) / 2), ‖gradient w y‖ ^ 2) ≤ E := fun z hz =>
    hE z A g w (hAcont' z hz) (hell' z hz) (hAbd' z hz) (hgc' z hz) (hgbd' z hz) (hw' z hz)
      (hwbd' z hz) (hweak' z hz)
  -- The perturbed energy decay, centred anywhere in `closedBall x₀ (5R/4)`.
  have hdecx : ∀ x : Euc d, dist x x₀ ≤ 5 * R / 4 → ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ Rd →
      (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
        C₁ * (ρ / r) ^ ((d : ℝ) + 2) *
          (∫ y in Metric.closedBall x r,
            ‖gradient w y - (⨍ z in Metric.closedBall x r, gradient w z)‖ ^ 2) +
        C₂ * r ^ ((d : ℝ) + 2 * α) := by
    intro x hx
    have hz : dist x x₀ ≤ 3 * R / 2 := by linarith
    exact hdec x A g w (hell' x hz) (hAbd' x hz) (hAhol' x hz) (hgc' x hz) (hgbd' x hz)
      (hw' x hz) (hwbd' x hz) (hwlip' x hz) (hweak' x hz) x
      (Metric.mem_ball_self (by linarith))
  -- Continuity and integrability of `∇w` on the small balls.
  have hcont : ∀ x : Euc d, dist x x₀ ≤ 5 * R / 4 → ∀ r : ℝ, r ≤ R₁ →
      ContinuousOn (gradient w) (Metric.closedBall x r) := by
    intro x hx r hr
    refine hgradcont.mono fun y hy => ?_
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      _ ≤ R₁ + 5 * R / 4 := add_le_add (hy.trans hr) hx
      _ < 2 * R := by linarith
  have hintg : ∀ x : Euc d, dist x x₀ ≤ 5 * R / 4 → ∀ r : ℝ, r ≤ R₁ →
      IntegrableOn (gradient w) (Metric.closedBall x r) :=
    fun x hx r hr => (hcont x hx r hr).integrableOn_compact (isCompact_closedBall x r)
  -- **Step 1**: the `L²` Campanato bound from the iteration, started by the energy bound.
  have hcampsq : ∀ x : Euc d, dist x x₀ ≤ 5 * R / 4 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ R₁ →
      (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
        C₃ * ρ ^ ((d : ℝ) + 2 * α) := by
    intro x hx ρ hρ hρR
    have hmain : (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
        c₀ * ((∫ y in Metric.closedBall x R₁,
              ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖ ^ 2) +
            C₂ * R₁ ^ ((d : ℝ) + 2 * α)) * (ρ / R₁) ^ ((d : ℝ) + 2 * α) :=
      hc₀ (fun s => ∫ y in Metric.closedBall x s,
          ‖gradient w y - (⨍ z in Metric.closedBall x s, gradient w z)‖ ^ 2)
        (fun _ => setIntegral_nonneg measurableSet_closedBall fun _ _ => sq_nonneg _)
        (fun s t hs hst htR => integral_norm_sub_setAverage_sq_mono hs hst (hcont x hx t htR))
        (fun s t hs hst htR => hdecx x hx s t hs hst (htR.trans hR₁Rd)) ρ hρ hρR
    have hΦR : (∫ y in Metric.closedBall x R₁,
        ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖ ^ 2) ≤ E := by
      have h0 : (∫ y in Metric.closedBall x R₁,
          ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖ ^ 2) ≤
          ∫ y in Metric.closedBall x R₁, ‖gradient w y - (0 : Euc d)‖ ^ 2 :=
        integral_norm_sub_setAverage_sq_le_const hR₁pos (hcont x hx R₁ le_rfl) (0 : Euc d)
      have h1 : (∫ y in Metric.closedBall x R₁, ‖gradient w y - (0 : Euc d)‖ ^ 2) =
          ∫ y in Metric.closedBall x R₁, ‖gradient w y‖ ^ 2 := by
        refine setIntegral_congr_fun measurableSet_closedBall fun y _ => ?_
        rw [sub_zero]
      have hsub : Metric.closedBall x R₁ ⊆ Metric.closedBall x (3 * (R / 4) / 2) :=
        Metric.closedBall_subset_closedBall (by linarith)
      have h2 : (∫ y in Metric.closedBall x R₁, ‖gradient w y‖ ^ 2) ≤
          ∫ y in Metric.closedBall x (3 * (R / 4) / 2), ‖gradient w y‖ ^ 2 := by
        refine setIntegral_mono_set ?_ (Eventually.of_forall fun _ => sq_nonneg _)
          hsub.eventuallyLE
        have hc : ContinuousOn (gradient w) (Metric.closedBall x (3 * (R / 4) / 2)) := by
          refine hgradcont.mono fun y hy => ?_
          rw [Metric.mem_closedBall] at hy
          rw [Metric.mem_ball]
          calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
            _ ≤ 3 * (R / 4) / 2 + 5 * R / 4 := add_le_add hy hx
            _ < 2 * R := by linarith
        exact (hc.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _)
      have h3 := hEz x (by linarith)
      linarith
    calc (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2)
        ≤ c₀ * ((∫ y in Metric.closedBall x R₁,
              ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖ ^ 2) +
            C₂ * R₁ ^ ((d : ℝ) + 2 * α)) * (ρ / R₁) ^ ((d : ℝ) + 2 * α) := hmain
      _ ≤ c₀ * (E + C₂ * R₁ ^ ((d : ℝ) + 2 * α)) * (ρ / R₁) ^ ((d : ℝ) + 2 * α) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hc₀0)
            (Real.rpow_nonneg (div_nonneg hρ.le hR₁pos.le) _)
      _ = C₃ * ρ ^ ((d : ℝ) + 2 * α) := by
          rw [hC₃, Real.div_rpow hρ.le hR₁pos.le, div_eq_mul_inv]
          ring
  -- **Step 2**: the `L¹` Campanato bound.
  have hcamp1 : ∀ x : Euc d, dist x x₀ ≤ 5 * R / 4 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ R₁ →
      (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖) ≤
        C₄ * ρ ^ ((d : ℝ) + α) := by
    intro x hx ρ hρ hρR
    rw [hC₄]
    exact setIntegral_norm_sub_setAverage_le_of_sq hρ (hcont x hx ρ hρR)
      (hcampsq x hx ρ hρ hρR)
  -- **Step 3**: the averages of `∇w` over small balls converge to its value.
  obtain ⟨Cw, hCw⟩ := hwlip
  obtain ⟨Cw', hCw'⟩ : ∃ Cw' : ℝ, Cw' = max Cw 0 := ⟨_, rfl⟩
  have hCw'0 : 0 ≤ Cw' := by rw [hCw']; exact le_max_right _ _
  have hlim : ∀ x ∈ Metric.closedBall x₀ (5 * R / 4), ∀ ε : ℝ, 0 < ε → ∀ u : ℝ, 0 < u →
      ∃ s : ℝ, 0 < s ∧ s ≤ u ∧
        ‖(⨍ y in Metric.closedBall x s, gradient w y) - gradient w x‖ ≤ ε := by
    intro x hxm ε hε u hu
    rw [Metric.mem_closedBall] at hxm
    obtain ⟨s, hs, hsu, hsε⟩ := exists_pos_le_mul_rpow_lt hα hCw'0 (lt_min hu hR₁pos) hε
    have hsR₁ : s ≤ R₁ := hsu.trans (min_le_right _ _)
    refine ⟨s, hs, hsu.trans (min_le_left _ _), ?_⟩
    refine norm_setAverage_sub_le_of_forall hs (hintg x hxm s hsR₁) ?_
    intro y hy
    rw [Metric.mem_closedBall] at hy
    have hxb : x ∈ Metric.ball x₀ (2 * R) := by
      rw [Metric.mem_ball]; linarith
    have hyb : y ∈ Metric.ball x₀ (2 * R) := by
      rw [Metric.mem_ball]
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ ≤ R₁ + 5 * R / 4 := add_le_add (hy.trans hsR₁) hxm
        _ < 2 * R := by linarith
    calc ‖gradient w y - gradient w x‖ ≤ Cw * dist y x ^ α := hCw y hyb x hxb
      _ ≤ Cw' * dist y x ^ α :=
          mul_le_mul_of_nonneg_right (by rw [hCw']; exact le_max_left _ _)
            (Real.rpow_nonneg dist_nonneg _)
      _ ≤ Cw' * s ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hy hα.le) hCw'0
      _ ≤ ε := hsε.le
  -- **Step 4**: the uniform Hölder bound on `closedBall x₀ (5R/4)`.
  have hHol : ∀ x ∈ Metric.closedBall x₀ (5 * R / 4), ∀ y ∈ Metric.closedBall x₀ (5 * R / 4),
      dist x y ≤ rr → ‖gradient w x - gradient w y‖ ≤ B * rr ^ α := by
    intro x hx y hy hxy
    exact hB (gradient w) (Metric.closedBall x₀ (5 * R / 4))
      (fun z hz r _ hrR => hintg z (Metric.mem_closedBall.1 hz) r hrR)
      (fun z hz r hr hrR => ⟨⨍ y in Metric.closedBall z r, gradient w y,
        hcamp1 z (Metric.mem_closedBall.1 hz) r hr hrR⟩)
      hlim x hx y hy rr hrr0 hxy (by rw [hrr]; linarith)
  -- **Conclusion.**
  intro x hxm
  rw [Metric.mem_closedBall] at hxm
  have hx54 : x ∈ Metric.closedBall x₀ (5 * R / 4) :=
    Metric.mem_closedBall.2 (by linarith)
  have hxd : dist x x₀ ≤ 5 * R / 4 := by linarith
  have hrrR₁ : rr ≤ R₁ := by rw [hrr]; linarith
  -- a point of `B̄(x, rr)` where `‖∇w‖²` does not exceed the average of the energy
  have hsqint : IntegrableOn (fun y => ‖gradient w y‖ ^ 2) (Metric.closedBall x rr) :=
    (((hcont x hxd rr hrrR₁).norm).pow 2).integrableOn_compact (isCompact_closedBall x rr)
  have hEx : (∫ y in Metric.closedBall x rr, ‖gradient w y‖ ^ 2) ≤ E := by
    have hsub : Metric.closedBall x rr ⊆ Metric.closedBall x (3 * (R / 4) / 2) :=
      Metric.closedBall_subset_closedBall (by rw [hrr]; linarith)
    have hc : ContinuousOn (gradient w) (Metric.closedBall x (3 * (R / 4) / 2)) := by
      refine hgradcont.mono fun y hy => ?_
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ ≤ 3 * (R / 4) / 2 + 5 * R / 4 := add_le_add hy hxd
        _ < 2 * R := by linarith
    have h2 : (∫ y in Metric.closedBall x rr, ‖gradient w y‖ ^ 2) ≤
        ∫ y in Metric.closedBall x (3 * (R / 4) / 2), ‖gradient w y‖ ^ 2 :=
      setIntegral_mono_set ((hc.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _))
        (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE
    exact h2.trans (hEz x (by linarith))
  have hvne : (rr ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) ≠ 0 := hvolpos.ne'
  have hex : ∃ y ∈ Metric.closedBall x rr, ‖gradient w y‖ ^ 2 ≤
      (E + 1) / (rr ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) := by
    by_contra hcon
    push_neg at hcon
    have h1 : (∫ _y in Metric.closedBall x rr,
          (E + 1) / (rr ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))) ≤
        ∫ y in Metric.closedBall x rr, ‖gradient w y‖ ^ 2 :=
      setIntegral_mono_on (integrableOn_const measure_closedBall_lt_top.ne) hsqint
        measurableSet_closedBall fun y hy => (hcon y hy).le
    rw [setIntegral_const, smul_eq_mul, volume_real_closedBall x hrr0.le] at h1
    have heq : (rr ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) *
        ((E + 1) / (rr ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))) = E + 1 := by
      field_simp <;> ring
    rw [heq] at h1
    linarith
  obtain ⟨y, hymem, hy2⟩ := hex
  have hy54 : y ∈ Metric.closedBall x₀ (5 * R / 4) := by
    rw [Metric.mem_closedBall]
    rw [Metric.mem_closedBall] at hymem
    calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      _ ≤ rr + R := add_le_add hymem hxm
      _ ≤ 5 * R / 4 := by rw [hrr]; linarith
  have hynorm : ‖gradient w y‖ ≤
      Real.sqrt ((E + 1) / (rr ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))) := by
    have h0 : ‖gradient w y‖ = Real.sqrt (‖gradient w y‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h0]
    exact Real.sqrt_le_sqrt hy2
  have hdxy : dist x y ≤ rr := by
    rw [Metric.mem_closedBall] at hymem
    rw [dist_comm]
    exact hymem
  have hhol := hHol x hx54 y hy54 hdxy
  have htri : ‖gradient w x‖ - ‖gradient w y‖ ≤ ‖gradient w x - gradient w y‖ :=
    le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
  linarith [hynorm, hhol, htri]

/-- **Interior Schauder estimate on the closed ball** — the assembly of the Campanato method
(Gilbarg–Trudinger, Theorem 8.32). Identical to `schauder_C2` but with the conclusion on the closed
ball `closedBall x₀ R`; `schauder_C2` is its restriction to the open ball. -/
theorem schauder_interior_estimate (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hμ : 0 < μ)
    (hR : 0 < R) :
    ∃ C : ℝ, ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.closedBall x₀ R, ‖gradient w x‖ ≤ C ∧
        ∀ y ∈ Metric.closedBall x₀ R, ‖gradient w x - gradient w y‖ ≤ C * dist x y ^ α := by
  -- The route, uniform in `x₀, A, g, w`:
  --  1. `campanato_iteration_uniform` applied to `Φ(x, ρ) = ∫_{B(x,ρ)} ‖∇w - (∇w)_{B(x,ρ)}‖²`
  --     with the perturbed decay `schauder_perturbed_energy_decay` (`γ = d+2 > β = d+2α` since
  --     `α < 1`) and the initial energy `Φ(x, R₁) ≤ (2M)² vol(B_{R₁})` from
  --     `schauder_interior_gradient_bound`, giving `Φ(x, ρ) ≤ C₃ ρ^{d+2α}` on `B_R`.
  --  2. `setIntegral_norm_sub_setAverage_le_of_sq` (Young) upgrades this to the `L¹` Campanato
  --     bound `∫_{B(x,ρ)} ‖∇w - (∇w)_{B(x,ρ)}‖ ≤ C₄ ρ^{d+α}`.
  --  3. `exists_holder_of_campanato_uniform` turns that into `‖∇w x - ∇w y‖ ≤ B |x-y|^α` for
  --     nearby points; far-apart points use the sup bound `M`.
  have hω : (0 : ℝ) < volume.real (Metric.closedBall (0 : Euc d) 1) := volume_real_closedBall_pos
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  -- 1. The interior gradient bound, used on balls of radius `R / 4`.
  obtain ⟨M, hM0, hM⟩ := schauder_interior_gradient_bound d (α := α) (μ := μ) (Λ := Λ)
    (R := R / 4) hα hα1 hμ (by linarith)
  -- 2. The perturbed energy decay, used on balls of radius `R / 4`.
  obtain ⟨C₁, C₂, Rd, hRd, hC₁0, hC₂0, hdec⟩ := schauder_perturbed_energy_decay d
    (α := α) (μ := μ) (Λ := Λ) (R := R / 4) hα hα1 hμ (by linarith)
  -- 3. The working scale `R₁`.
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = min Rd (R / 8) := ⟨_, rfl⟩
  have hR₁pos : 0 < R₁ := by rw [hR₁]; exact lt_min hRd (by linarith)
  have hR₁Rd : R₁ ≤ Rd := by rw [hR₁]; exact min_le_left _ _
  have hR₁R : R₁ ≤ R / 8 := by rw [hR₁]; exact min_le_right _ _
  -- 4. The (uniform) Campanato iteration constant.
  have hβ0 : (0 : ℝ) ≤ (d : ℝ) + 2 * α := by linarith
  have hβγ : (d : ℝ) + 2 * α < (d : ℝ) + 2 := by linarith
  obtain ⟨c₀, hc₀0, hc₀⟩ := campanato_iteration_uniform (a := C₁) (b := C₂)
    (β := (d : ℝ) + 2 * α) (γ := (d : ℝ) + 2) (R₀ := R₁) hC₁0 hC₂0 hβ0 hβγ hR₁pos
  -- 5. The resulting `L²`- and `L¹`-Campanato constants.
  have hRβ : (0 : ℝ) < R₁ ^ ((d : ℝ) + 2 * α) := Real.rpow_pos_of_pos hR₁pos _
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = c₀ *
      ((2 * M) ^ 2 * (R₁ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) +
        C₂ * R₁ ^ ((d : ℝ) + 2 * α)) * (R₁ ^ ((d : ℝ) + 2 * α))⁻¹ := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by
    have h2 : (0 : ℝ) ≤ (2 * M) ^ 2 * (R₁ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hR₁pos.le d) hω.le)
    have h3 : (0 : ℝ) ≤ C₂ * R₁ ^ ((d : ℝ) + 2 * α) := mul_nonneg hC₂0 hRβ.le
    rw [hC₃]
    exact mul_nonneg (mul_nonneg hc₀0 (by linarith)) (inv_nonneg.2 hRβ.le)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ,
      C₄ = (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := by rw [hC₄]; linarith
  -- 6. The uniform Hölder constant coming out of Campanato's criterion.
  obtain ⟨B, hB0, hB⟩ := exists_holder_of_campanato_uniform (d := d) (E := Euc d)
    (α := α) (C := C₄) (R₀ := R₁) hα hC₄0
  have hRα : (0 : ℝ) < (R₁ / 2) ^ α := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨max M (max B (2 * M / (R₁ / 2) ^ α)), ?_⟩
  intro x₀ A g w hell hAbd hAhol hgc hgbd hw hwbd hwlip hweak
  -- Continuity of `∇w` on the ball where the equation holds.
  have hgradcont : ContinuousOn (gradient w) (Metric.ball x₀ (2 * R)) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hw.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
  -- Restriction of every hypothesis to a ball of radius `R / 2` around an interior point.
  have hsubball : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      Metric.ball z (2 * (R / 4)) ⊆ Metric.ball x₀ (2 * R) := by
    intro z hz y hy
    rw [Metric.mem_ball] at hy
    rw [Metric.mem_ball]
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ < 2 * (R / 4) + 3 * R / 2 := by linarith
      _ ≤ 2 * R := by linarith
  have hell' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A y ζ, ζ⟫ :=
    fun z hz y hy => hell y (hsubball z hz hy)
  have hAbd' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), ‖A y‖ ≤ Λ :=
    fun z hz y hy => hAbd y (hsubball z hz hy)
  have hAhol' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), ∀ y' ∈ Metric.ball z (2 * (R / 4)),
        ‖A y - A y'‖ ≤ Λ * dist y y' ^ α :=
    fun z hz y hy y' hy' => hAhol y (hsubball z hz hy) y' (hsubball z hz hy')
  have hgc' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ContinuousOn g (Metric.ball z (2 * (R / 4))) := fun z hz => hgc.mono (hsubball z hz)
  have hgbd' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), |g y| ≤ Λ :=
    fun z hz y hy => hgbd y (hsubball z hz hy)
  have hw' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ContDiffOn ℝ 1 w (Metric.ball z (2 * (R / 4))) := fun z hz => hw.mono (hsubball z hz)
  have hwbd' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ y ∈ Metric.ball z (2 * (R / 4)), |w y| ≤ Λ :=
    fun z hz y hy => hwbd y (hsubball z hz hy)
  have hwlip' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∃ Cw : ℝ, ∀ y ∈ Metric.ball z (2 * (R / 4)), ∀ y' ∈ Metric.ball z (2 * (R / 4)),
        ‖gradient w y - gradient w y'‖ ≤ Cw * dist y y' ^ α := by
    intro z hz
    obtain ⟨Cw, hCw⟩ := hwlip
    exact ⟨Cw, fun y hy y' hy' => hCw y (hsubball z hz hy) y' (hsubball z hz hy')⟩
  have hweak' : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 →
      ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball z (2 * (R / 4)) →
        ∫ y, ⟪A y (gradient w y), gradient ψ y⟫ = ∫ y, g y * ψ y :=
    fun z hz ψ h1 h2 h3 => hweak ψ h1 h2 (h3.trans (hsubball z hz))
  -- The interior gradient bound, on the slightly larger ball `closedBall x₀ (3R/2)`.
  have hgradM : ∀ z : Euc d, dist z x₀ ≤ 3 * R / 2 → ‖gradient w z‖ ≤ M := fun z hz =>
    hM z A g w (hell' z hz) (hAbd' z hz) (hAhol' z hz) (hgc' z hz) (hgbd' z hz)
      (hw' z hz) (hwbd' z hz) (hwlip' z hz) (hweak' z hz) z
      (Metric.mem_closedBall_self (by linarith))
  -- The perturbed energy decay, centred at any point of `closedBall x₀ R`.
  have hdecx : ∀ x : Euc d, dist x x₀ ≤ R → ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ Rd →
      (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
        C₁ * (ρ / r) ^ ((d : ℝ) + 2) *
          (∫ y in Metric.closedBall x r,
            ‖gradient w y - (⨍ z in Metric.closedBall x r, gradient w z)‖ ^ 2) +
        C₂ * r ^ ((d : ℝ) + 2 * α) := by
    intro x hx
    have hz : dist x x₀ ≤ 3 * R / 2 := by linarith
    exact hdec x A g w (hell' x hz) (hAbd' x hz) (hAhol' x hz) (hgc' x hz) (hgbd' x hz)
      (hw' x hz) (hwbd' x hz) (hwlip' x hz) (hweak' x hz) x
      (Metric.mem_ball_self (by linarith))
  -- Continuity and integrability of `∇w` on the small balls.
  have hcont : ∀ x : Euc d, dist x x₀ ≤ R → ∀ r : ℝ, r ≤ R₁ →
      ContinuousOn (gradient w) (Metric.closedBall x r) := by
    intro x hx r hr
    refine hgradcont.mono fun y hy => ?_
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      _ ≤ R₁ + R := add_le_add (hy.trans hr) hx
      _ < 2 * R := by linarith
  have hintg : ∀ x : Euc d, dist x x₀ ≤ R → ∀ r : ℝ, r ≤ R₁ →
      IntegrableOn (gradient w) (Metric.closedBall x r) :=
    fun x hx r hr => (hcont x hx r hr).integrableOn_compact (isCompact_closedBall x r)
  -- **Step 1**: the `L²` Campanato bound from the iteration.
  have hcampsq : ∀ x : Euc d, dist x x₀ ≤ R → ∀ ρ : ℝ, 0 < ρ → ρ ≤ R₁ →
      (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
        C₃ * ρ ^ ((d : ℝ) + 2 * α) := by
    intro x hx ρ hρ hρR
    have hmain : (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
        c₀ * ((∫ y in Metric.closedBall x R₁,
              ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖ ^ 2) +
            C₂ * R₁ ^ ((d : ℝ) + 2 * α)) * (ρ / R₁) ^ ((d : ℝ) + 2 * α) :=
      hc₀ (fun s => ∫ y in Metric.closedBall x s,
          ‖gradient w y - (⨍ z in Metric.closedBall x s, gradient w z)‖ ^ 2)
        (fun _ => setIntegral_nonneg measurableSet_closedBall fun _ _ => sq_nonneg _)
        (fun s t hs hst htR => integral_norm_sub_setAverage_sq_mono hs hst (hcont x hx t htR))
        (fun s t hs hst htR => hdecx x hx s t hs hst (htR.trans hR₁Rd)) ρ hρ hρR
    have hΦR : (∫ y in Metric.closedBall x R₁,
        ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖ ^ 2) ≤
        (2 * M) ^ 2 * (R₁ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) := by
      have hMball : ∀ z ∈ Metric.closedBall x R₁, ‖gradient w z‖ ≤ M := by
        intro z hz
        rw [Metric.mem_closedBall] at hz
        refine hgradM z ?_
        calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
          _ ≤ R₁ + R := add_le_add hz hx
          _ ≤ 3 * R / 2 := by linarith
      have havg : ‖(⨍ z in Metric.closedBall x R₁, gradient w z)‖ ≤ M := by
        have h := norm_setAverage_sub_le_of_forall (f := gradient w) (x := x) (r := R₁)
          (c := (0 : Euc d)) (K := M) hR₁pos (hintg x hx R₁ le_rfl)
          (fun z hz => by rw [sub_zero]; exact hMball z hz)
        rwa [sub_zero] at h
      have hbd2 : ∀ y ∈ Metric.closedBall x R₁,
          ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖ ≤ 2 * M := by
        intro y hy
        calc ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖
            ≤ ‖gradient w y‖ + ‖(⨍ z in Metric.closedBall x R₁, gradient w z)‖ :=
              norm_sub_le _ _
          _ ≤ M + M := add_le_add (hMball y hy) havg
          _ = 2 * M := by ring
      have h := setIntegral_norm_sub_sq_le (hcont x hx R₁ le_rfl) hbd2
      rwa [volume_real_closedBall x hR₁pos.le] at h
    calc (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2)
        ≤ c₀ * ((∫ y in Metric.closedBall x R₁,
              ‖gradient w y - (⨍ z in Metric.closedBall x R₁, gradient w z)‖ ^ 2) +
            C₂ * R₁ ^ ((d : ℝ) + 2 * α)) * (ρ / R₁) ^ ((d : ℝ) + 2 * α) := hmain
      _ ≤ c₀ * ((2 * M) ^ 2 * (R₁ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) +
            C₂ * R₁ ^ ((d : ℝ) + 2 * α)) * (ρ / R₁) ^ ((d : ℝ) + 2 * α) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hc₀0)
            (Real.rpow_nonneg (div_nonneg hρ.le hR₁pos.le) _)
      _ = C₃ * ρ ^ ((d : ℝ) + 2 * α) := by
          rw [hC₃, Real.div_rpow hρ.le hR₁pos.le, div_eq_mul_inv]
          ring
  -- **Step 2**: the `L¹` Campanato bound.
  have hcamp1 : ∀ x : Euc d, dist x x₀ ≤ R → ∀ ρ : ℝ, 0 < ρ → ρ ≤ R₁ →
      (∫ y in Metric.closedBall x ρ,
          ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖) ≤
        C₄ * ρ ^ ((d : ℝ) + α) := by
    intro x hx ρ hρ hρR
    rw [hC₄]
    exact setIntegral_norm_sub_setAverage_le_of_sq hρ (hcont x hx ρ hρR)
      (hcampsq x hx ρ hρ hρR)
  -- **Step 3**: the averages of `∇w` over small balls converge to its value.
  obtain ⟨Cw, hCw⟩ := hwlip
  obtain ⟨Cw', hCw'⟩ : ∃ Cw' : ℝ, Cw' = max Cw 0 := ⟨_, rfl⟩
  have hCw'0 : 0 ≤ Cw' := by rw [hCw']; exact le_max_right _ _
  have hlim : ∀ x ∈ Metric.closedBall x₀ R, ∀ ε : ℝ, 0 < ε → ∀ u : ℝ, 0 < u →
      ∃ s : ℝ, 0 < s ∧ s ≤ u ∧
        ‖(⨍ y in Metric.closedBall x s, gradient w y) - gradient w x‖ ≤ ε := by
    intro x hxm ε hε u hu
    rw [Metric.mem_closedBall] at hxm
    obtain ⟨s, hs, hsu, hsε⟩ := exists_pos_le_mul_rpow_lt hα hCw'0 (lt_min hu hR₁pos) hε
    have hsR₁ : s ≤ R₁ := hsu.trans (min_le_right _ _)
    refine ⟨s, hs, hsu.trans (min_le_left _ _), ?_⟩
    refine norm_setAverage_sub_le_of_forall hs (hintg x hxm s hsR₁) ?_
    intro y hy
    rw [Metric.mem_closedBall] at hy
    have hxb : x ∈ Metric.ball x₀ (2 * R) := by
      rw [Metric.mem_ball]; linarith
    have hyb : y ∈ Metric.ball x₀ (2 * R) := by
      rw [Metric.mem_ball]
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ ≤ R₁ + R := add_le_add (hy.trans hsR₁) hxm
        _ < 2 * R := by linarith
    calc ‖gradient w y - gradient w x‖ ≤ Cw * dist y x ^ α := hCw y hyb x hxb
      _ ≤ Cw' * dist y x ^ α :=
          mul_le_mul_of_nonneg_right (by rw [hCw']; exact le_max_left _ _)
            (Real.rpow_nonneg dist_nonneg _)
      _ ≤ Cw' * s ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hy hα.le) hCw'0
      _ ≤ ε := hsε.le
  -- **Conclusion.**
  intro x hxm
  rw [Metric.mem_closedBall] at hxm
  refine ⟨le_trans (hgradM x (by linarith)) (le_max_left _ _), ?_⟩
  intro y hym
  rw [Metric.mem_closedBall] at hym
  rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist x y) with h0 | h0
  · have hxy : x = y := dist_eq_zero.1 h0.symm
    subst hxy
    rw [sub_self, norm_zero]
    exact mul_nonneg (le_trans hM0 (le_max_left _ _)) (Real.rpow_nonneg dist_nonneg _)
  · by_cases hsmall : 2 * dist x y ≤ R₁
    · have hb := hB (gradient w) (Metric.closedBall x₀ R)
        (fun z hz r _ hrR => hintg z (Metric.mem_closedBall.1 hz) r hrR)
        (fun z hz r hr hrR => ⟨⨍ y in Metric.closedBall z r, gradient w y,
          hcamp1 z (Metric.mem_closedBall.1 hz) r hr hrR⟩)
        hlim x (Metric.mem_closedBall.2 hxm) y (Metric.mem_closedBall.2 hym)
        (dist x y) h0 le_rfl hsmall
      exact hb.trans (mul_le_mul_of_nonneg_right
        (le_trans (le_max_left B (2 * M / (R₁ / 2) ^ α))
          (le_max_right M (max B (2 * M / (R₁ / 2) ^ α))))
        (Real.rpow_nonneg dist_nonneg _))
    · push_neg at hsmall
      have hRne : ((R₁ : ℝ) / 2) ^ α ≠ 0 := hRα.ne'
      have h1 : ‖gradient w x - gradient w y‖ ≤ 2 * M :=
        calc ‖gradient w x - gradient w y‖ ≤ ‖gradient w x‖ + ‖gradient w y‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hgradM x (by linarith)) (hgradM y (by linarith))
          _ = 2 * M := by ring
      have h2 : ((R₁ : ℝ) / 2) ^ α ≤ dist x y ^ α :=
        Real.rpow_le_rpow (by linarith) (by linarith) hα.le
      calc ‖gradient w x - gradient w y‖ ≤ 2 * M := h1
        _ = 2 * M / (R₁ / 2) ^ α * (R₁ / 2) ^ α := by field_simp
        _ ≤ 2 * M / (R₁ / 2) ^ α * dist x y ^ α :=
            mul_le_mul_of_nonneg_left h2 (div_nonneg (by linarith) hRα.le)
        _ ≤ max M (max B (2 * M / (R₁ / 2) ^ α)) * dist x y ^ α :=
            mul_le_mul_of_nonneg_right
              (le_trans (le_max_right B (2 * M / (R₁ / 2) ^ α))
                (le_max_right M (max B (2 * M / (R₁ / 2) ^ α))))
              (Real.rpow_nonneg dist_nonneg _)

/-- **Interior Schauder estimate for linear divergence-form equations** (Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Theorem 8.32, with `b = c = d = 0` and
`f = 0`; the linear-elliptic input of the `C²` step of paper Appendix A, *Eigenfunction inputs*:
"local elliptic regularity gives `u_i ∈ C²`"): for `0 < α < 1`, `μ > 0`, `Λ` and `R > 0` there is
`C` such that every `w ∈ C^{1,α}(B_{2R})`, `B_r = ball x₀ r`, solving `div(A ∇w) = -g` weakly in
`B_{2R}`, with `A` uniformly elliptic (constant `μ`), bounded and `α`-Hölder (constant `Λ`) and
`|g|, |w| ≤ Λ` on `B_{2R}`, satisfies `|∇w| ≤ C` and `|∇w(x) - ∇w(y)| ≤ C |x - y|^α` on `B_R`. -/
theorem schauder_C2 (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hμ : 0 < μ)
    (hR : 0 < R) :
    ∃ C : ℝ, ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.ball x₀ R, ‖gradient w x‖ ≤ C ∧
        ∀ y ∈ Metric.ball x₀ R, ‖gradient w x - gradient w y‖ ≤ C * dist x y ^ α := by
  -- The estimate on the open ball `B_R` is the restriction of the interior estimate on the closed
  -- ball `closedBall x₀ R` (`schauder_interior_estimate`), since `ball x₀ R ⊆ closedBall x₀ R`.
  obtain ⟨C, hC⟩ := schauder_interior_estimate (d := d) (α := α) (μ := μ) (Λ := Λ) (R := R)
    hα hα1 hμ hR
  refine ⟨C, fun x₀ A g w hell hAbd hAhol hgc hgbd hw hwbd hwlip hweak x hx => ?_⟩
  obtain ⟨hb, hh⟩ :=
    hC x₀ A g w hell hAbd hAhol hgc hgbd hw hwbd hwlip hweak x (Metric.ball_subset_closedBall hx)
  exact ⟨hb, fun y hy => hh y (Metric.ball_subset_closedBall hy)⟩

/-! ### Translated and linearized weak equations -/

/-- **The weak flux equation for translates**: if `φ` solves `∫ ⟪a(∇φ), ∇ψ⟫ = λ ∫ φ^{p-1} ψ` for
test functions supported in `U`, then `∫ ⟪a(∇φ(· + v)), ∇ψ⟫ = λ ∫ φ(· + v)^{p-1} ψ` for test
functions `ψ` with `tsupport ψ + v ⊆ U`. -/
theorem integral_inner_flux_translate {p : ℝ} {F : Euc d → ℝ} {U : Set (Euc d)} {φ : Euc d → ℝ}
    {lam : ℝ}
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ = lam * ∫ x, φ x ^ (p - 1) * ψ x)
    (v : Euc d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψU : ∀ x ∈ tsupport ψ, x + v ∈ U) :
    ∫ x, ⟪flux p F (gradient φ (x + v)), gradient ψ x⟫ =
      lam * ∫ x, φ (x + v) ^ (p - 1) * ψ x := by
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : Euc d → ℝ, ψ' = fun y => ψ (y + -v) := ⟨_, rfl⟩
  have hψ'c : ContDiff ℝ ∞ ψ' := by
    rw [hψ']
    exact hψ.comp (contDiff_id.add contDiff_const)
  have hψ's : HasCompactSupport ψ' := by
    have h := hψs.comp_homeomorph (Homeomorph.addRight (-v))
    have he : ψ ∘ Homeomorph.addRight (-v) = ψ' := by
      rw [hψ']
      rfl
    rwa [he] at h
  have hψ'U : tsupport ψ' ⊆ U := by
    intro y hy
    have h1 : tsupport ψ' = (Homeomorph.addRight (-v)) ⁻¹' tsupport ψ := by
      rw [← tsupport_comp_eq_preimage ψ (Homeomorph.addRight (-v)), hψ']
      rfl
    rw [h1] at hy
    have h2 := hψU _ hy
    simpa using h2
  have hgrad : ∀ y, gradient ψ' y = gradient ψ (y + -v) := fun y => by
    rw [hψ']
    unfold gradient
    rw [fderiv_comp_add_right]
  have e1 : ∫ x, ⟪flux p F (gradient φ (x + v)), gradient ψ x⟫ =
      ∫ y, ⟪flux p F (gradient φ y), gradient ψ' y⟫ := by
    rw [← integral_add_right_eq_self (fun y => ⟪flux p F (gradient φ y), gradient ψ' y⟫) v]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ⟪flux p F (gradient φ (x + v)), gradient ψ x⟫ =
      ⟪flux p F (gradient φ (x + v)), gradient ψ' (x + v)⟫
    rw [hgrad, add_neg_cancel_right]
  have e2 : ∫ x, φ (x + v) ^ (p - 1) * ψ x = ∫ y, φ y ^ (p - 1) * ψ' y := by
    rw [← integral_add_right_eq_self (fun y => φ y ^ (p - 1) * ψ' y) v]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show φ (x + v) ^ (p - 1) * ψ x = φ (x + v) ^ (p - 1) * ψ' (x + v)
    rw [hψ']
    simp only [add_neg_cancel_right]
  rw [e1, e2]
  exact hweak ψ' hψ'c hψ's hψ'U

/-- **The linearized difference equation**: under the weak flux equation on `U`, for a test
function `ψ` such that on `tsupport ψ` the points `x, x + v` lie in `U` and the gradients
`∇φ(x), ∇φ(x + v)` lie in a convex set `N ∌ 0`,
`∫ ⟪A_v(x) (∇φ(x+v) - ∇φ(x)), ∇ψ⟫ = λ ∫ (φ(x+v)^{p-1} - φ(x)^{p-1}) ψ`, where
`A_v(x) = ∫₀¹ A(∇φ(x) + t (∇φ(x+v) - ∇φ(x))) dt` (`flux_sub_eq_integral_fderiv`). -/
theorem integral_inner_linearized_eq {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {U : Set (Euc d)} (hU : IsOpen U) {φ : Euc d → ℝ} {lam : ℝ}
    (hφ1 : ContDiffOn ℝ 1 φ U)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ = lam * ∫ x, φ x ^ (p - 1) * ψ x)
    {N : Set (Euc d)} (hNcv : Convex ℝ N) (hN0 : (0 : Euc d) ∉ N) (v : Euc d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψU : ∀ x ∈ tsupport ψ, x ∈ U ∧ x + v ∈ U ∧ gradient φ x ∈ N ∧ gradient φ (x + v) ∈ N) :
    ∫ x, ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F)
        (gradient φ x + t • (gradient φ (x + v) - gradient φ x)))
          (gradient φ (x + v) - gradient φ x), gradient ψ x⟫ =
      lam * ∫ x, (φ (x + v) ^ (p - 1) - φ x ^ (p - 1)) * ψ x := by
  set U' : Set (Euc d) := U ∩ (fun x => x + v) ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.inter (hU.preimage (continuous_id.add continuous_const))
  have hsU' : tsupport ψ ⊆ U' := fun x hx => ⟨(hψU x hx).1, (hψU x hx).2.1⟩
  have hgc : ContinuousOn (gradient φ) U :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hφ1.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hgc' : ContinuousOn (fun x => gradient φ (x + v)) U' :=
    hgc.comp (continuous_id.add continuous_const).continuousOn fun x hx => hx.2
  have hψg : Continuous (gradient ψ) := continuous_gradient (hψ.of_le (by simp))
  have hsg : tsupport (gradient ψ) ⊆ tsupport ψ := by
    refine closure_minimal (fun x hx => ?_) (isClosed_tsupport _)
    by_contra h
    exact hx (by rw [gradient_eq_zero_of_notMem_tsupport h])
  have hint : ∀ f : Euc d → Euc d, ContinuousOn f U' →
      Integrable fun x => ⟪flux p F (f x), gradient ψ x⟫ := by
    intro f hf
    have hsupp : Function.support (fun x => ⟪flux p F (f x), gradient ψ x⟫) ⊆
        Function.support (gradient ψ) := by
      intro x hx
      by_contra h
      have h0 : gradient ψ x = 0 := Function.notMem_support.1 h
      exact hx (by simp only [h0, inner_zero_right])
    refine Continuous.integrable_of_hasCompactSupport ?_
      ((hasCompactSupport_gradient hψs).mono' (hsupp.trans subset_closure))
    exact continuous_of_continuousOn_of_tsupport_subset hU'o
      (((hF.continuous_flux' hp).comp_continuousOn hf).inner hψg.continuousOn)
      ((closure_mono hsupp).trans (hsg.trans hsU'))
  have hint2 : ∀ g : Euc d → ℝ, ContinuousOn g U' → Integrable fun x => g x * ψ x := by
    intro g hg
    exact (continuous_of_continuousOn_of_tsupport_subset hU'o
      (hg.mul hψ.continuous.continuousOn)
        (tsupport_mul_subset_right.trans hsU')).integrable_of_hasCompactSupport hψs.mul_left
  have hpt : ∀ x, ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F)
      (gradient φ x + t • (gradient φ (x + v) - gradient φ x)))
        (gradient φ (x + v) - gradient φ x), gradient ψ x⟫ =
      ⟪flux p F (gradient φ (x + v)), gradient ψ x⟫ - ⟪flux p F (gradient φ x), gradient ψ x⟫ := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · obtain ⟨-, -, hN1, hN2⟩ := hψU x hx
      rw [← hF.flux_sub_eq_integral_fderiv p hNcv hN0 hN1 hN2, inner_sub_left]
    · have h0 : gradient ψ x = 0 := gradient_eq_zero_of_notMem_tsupport hx
      simp only [h0, inner_zero_right, sub_zero]
  have i1 : Integrable fun x => ⟪flux p F (gradient φ (x + v)), gradient ψ x⟫ := hint _ hgc'
  have i2 : Integrable fun x => ⟪flux p F (gradient φ x), gradient ψ x⟫ :=
    hint _ (hgc.mono fun x hx => hx.1)
  have hφc : ContinuousOn φ U := hφ1.continuousOn
  have i3 : Integrable fun x => φ (x + v) ^ (p - 1) * ψ x :=
    hint2 _ ((hφc.comp (continuous_id.add continuous_const).continuousOn
      fun x hx => hx.2).rpow_const fun _ _ => Or.inr (by linarith))
  have i4 : Integrable fun x => φ x ^ (p - 1) * ψ x :=
    hint2 _ ((hφc.mono fun x hx => hx.1).rpow_const fun _ _ => Or.inr (by linarith))
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub i1 i2,
    integral_inner_flux_translate hweak v hψ hψs (fun x hx => (hψU x hx).2.1),
    hweak ψ hψ hψs (fun x hx => (hψU x hx).1), ← mul_sub, ← integral_sub i3 i4]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show φ (x + v) ^ (p - 1) * ψ x - φ x ^ (p - 1) * ψ x =
    (φ (x + v) ^ (p - 1) - φ x ^ (p - 1)) * ψ x
  ring


/-! ### `C¹` from Hölder bounds on second differences -/

/-- A function continuous on an open set `V`, times a continuous compactly supported function
whose support lies in `V`, is integrable. -/
theorem integrable_mul_of_continuousOn {V : Set (Euc d)} (hV : IsOpen V) {f g : Euc d → ℝ}
    (hf : ContinuousOn f V) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgV : tsupport g ⊆ V) : Integrable fun y => f y * g y :=
  (continuous_of_continuousOn_of_tsupport_subset hV (hf.mul hg.continuousOn)
    (tsupport_mul_subset_right.trans hgV)).integrable_of_hasCompactSupport hgs.mul_left

/-- **Taylor bound for smooth functions with Lipschitz derivative**: if `Dψ` is `L`-Lipschitz,
then `|ψ(y - s e) - ψ(y) + s Dψ(y) e| ≤ L s²` for `‖e‖ = 1`, `s ≥ 0`. -/
theorem abs_sub_add_fderiv_le {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) {L : NNReal}
    (hL : LipschitzWith L (fderiv ℝ ψ)) {e : Euc d} (he : ‖e‖ = 1) (y : Euc d) {s : ℝ}
    (hs : 0 ≤ s) : |ψ (y - s • e) - ψ y + s * fderiv ℝ ψ y e| ≤ L * s ^ 2 := by
  set g : Euc d → ℝ := fun z => ψ z - fderiv ℝ ψ y (z - y) with hg
  have hgd : ∀ z, HasFDerivAt g (fderiv ℝ ψ z - fderiv ℝ ψ y) z := by
    intro z
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ z) z := (hψ.differentiable one_ne_zero z).hasFDerivAt
    have h2 : HasFDerivAt (fun z => fderiv ℝ ψ y (z - y)) (fderiv ℝ ψ y) z := by
      have h3 := (fderiv ℝ ψ y).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const y)
      rw [ContinuousLinearMap.comp_id] at h3
      exact h3
    exact h1.sub h2
  have hseg : ∀ z ∈ segment ℝ y (y - s • e), ‖fderiv ℝ ψ z - fderiv ℝ ψ y‖ ≤ L * s := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    show ‖fderiv ℝ ψ (y + θ • (y - s • e - y)) - fderiv ℝ ψ y‖ ≤ L * s
    have h := hL.dist_le_mul (y + θ • (y - s • e - y)) y
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ L.2)
    rw [sub_sub_cancel_left, norm_smul, norm_neg, norm_smul, he, mul_one,
      Real.norm_of_nonneg hθ.1, Real.norm_of_nonneg hs]
    nlinarith [hθ.1, hθ.2]
  have hmv := (convex_segment y (y - s • e)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hgd z).hasFDerivWithinAt) hseg (left_mem_segment ℝ y (y - s • e))
    (right_mem_segment ℝ y (y - s • e))
  have e1 : g (y - s • e) - g y = ψ (y - s • e) - ψ y + s * fderiv ℝ ψ y e := by
    simp only [hg, sub_self, map_zero, sub_zero, sub_sub_cancel_left, map_neg, map_smul,
      smul_eq_mul]
    ring
  rw [e1, Real.norm_eq_abs, sub_sub_cancel_left, norm_neg, norm_smul, he, mul_one,
    Real.norm_of_nonneg hs] at hmv
  calc |ψ (y - s • e) - ψ y + s * fderiv ℝ ψ y e| ≤ L * s * s := hmv
    _ = L * s ^ 2 := by ring

/-- Integrability of the products appearing when a translation acts on a test function
supported in `ball x (ρ/4)`, for `‖v‖ ≤ ρ/4` and `G` continuous on `ball x ρ`. -/
theorem integrable_mul_translate {x v : Euc d} {ρ : ℝ} (hv : ‖v‖ ≤ ρ / 4)
    {G : Euc d → ℝ} (hG : ContinuousOn G (Metric.ball x ρ)) {ψ : Euc d → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψx : tsupport ψ ⊆ Metric.ball x (ρ / 4)) :
    Integrable (fun y => G (y + v) * ψ y) ∧ Integrable (fun y => G y * ψ y) ∧
      Integrable (fun y => G y * ψ (y - v)) := by
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg v]
  refine ⟨?_, integrable_mul_of_continuousOn Metric.isOpen_ball hG hψc hψs
    (hψx.trans (Metric.ball_subset_ball (by linarith))), ?_⟩
  · have hc : Continuous fun y : Euc d => y + v := by fun_prop
    refine integrable_mul_of_continuousOn (Metric.isOpen_ball.preimage hc)
      (hG.comp hc.continuousOn (Set.mapsTo_preimage _ _)) hψc hψs fun y hy => ?_
    have hy' := hψx hy
    rw [Set.mem_preimage, Metric.mem_ball]
    rw [Metric.mem_ball] at hy'
    calc dist (y + v) x ≤ dist (y + v) y + dist y x := dist_triangle _ _ _
      _ < ρ := by
          rw [dist_eq_norm, add_sub_cancel_left]
          linarith
  · have hc : Continuous fun y : Euc d => ψ (y - v) := by fun_prop
    refine integrable_mul_of_continuousOn Metric.isOpen_ball hG hc
      (hψs.comp_homeomorph (Homeomorph.subRight v)) fun y hy => ?_
    have h1 : tsupport (fun y => ψ (y - v)) = (Homeomorph.subRight v) ⁻¹' tsupport ψ :=
      tsupport_comp_eq_preimage ψ (Homeomorph.subRight v)
    rw [h1] at hy
    have hy' : y - v ∈ Metric.ball x (ρ / 4) := hψx hy
    rw [Metric.mem_ball] at hy' ⊢
    calc dist y x ≤ dist y (y - v) + dist (y - v) x := dist_triangle _ _ _
      _ < ρ := by
          rw [dist_eq_norm, sub_sub_cancel]
          linarith

/-- **Moving a difference from `G` onto the test function**:
`∫ (G(y + v) - G y) ψ y = ∫ G y (ψ(y - v) - ψ y)` (translation invariance of Lebesgue measure). -/
theorem integral_difference_eq {x v : Euc d} {ρ : ℝ} (hv : ‖v‖ ≤ ρ / 4)
    {G : Euc d → ℝ} (hG : ContinuousOn G (Metric.ball x ρ)) {ψ : Euc d → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψx : tsupport ψ ⊆ Metric.ball x (ρ / 4)) :
    ∫ y, (G (y + v) - G y) * ψ y = ∫ y, G y * (ψ (y - v) - ψ y) := by
  obtain ⟨i1, i2, i3⟩ := integrable_mul_translate hv hG hψc hψs hψx
  have htr : ∫ y, G (y + v) * ψ y = ∫ y, G y * ψ (y - v) := by
    rw [← integral_add_right_eq_self (fun y => G y * ψ (y - v)) v]
    simp only [add_sub_cancel_right]
  have e1 : ∫ y, (G (y + v) - G y) * ψ y = ∫ y, (G (y + v) * ψ y - G y * ψ y) :=
    integral_congr_ae (Eventually.of_forall fun y => by
      show (G (y + v) - G y) * ψ y = G (y + v) * ψ y - G y * ψ y
      ring)
  have e2 : ∫ y, G y * (ψ (y - v) - ψ y) = ∫ y, (G y * ψ (y - v) - G y * ψ y) :=
    integral_congr_ae (Eventually.of_forall fun y => by
      show G y * (ψ (y - v) - ψ y) = G y * ψ (y - v) - G y * ψ y
      ring)
  rw [e1, e2, integral_sub i1 i2, integral_sub i3 i2, htr]

/-- Uniform convergence on an open set containing the support of a test function passes to the
integrals against it. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn {V : Set (Euc d)} (hV : IsOpen V)
    {D : ℕ → Euc d → ℝ} {H : Euc d → ℝ} (hDc : ∀ n, ContinuousOn (D n) V)
    (hH : TendstoUniformlyOn D H atTop V) {ψ : Euc d → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψV : tsupport ψ ⊆ V) :
    Tendsto (fun n => ∫ y, D n y * ψ y) atTop (𝓝 (∫ y, H y * ψ y)) := by
  have hHc : ContinuousOn H V := hH.continuousOn (Frequently.of_forall hDc)
  have iH : Integrable fun y => H y * ψ y := integrable_mul_of_continuousOn hV hHc hψc hψs hψV
  have iψ : Integrable fun y => |ψ y| := (hψc.integrable_of_hasCompactSupport hψs).abs
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ y, |ψ y| := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact integral_nonneg fun y => abs_nonneg _
  have hε' : 0 < ε / (I + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hH _ hε')
  refine ⟨N, fun n hn => ?_⟩
  have iDn : Integrable fun y => D n y * ψ y :=
    integrable_mul_of_continuousOn hV (hDc n) hψc hψs hψV
  rw [dist_eq_norm, ← integral_sub iDn iH]
  calc ‖∫ y, (D n y * ψ y - H y * ψ y)‖ ≤ ∫ y, ε / (I + 1) * |ψ y| := by
        refine norm_integral_le_of_norm_le (iψ.const_mul _) (Eventually.of_forall fun y => ?_)
        by_cases hy : ψ y = 0
        · simp [hy]
        · have h1 := hN n hn y (hψV (subset_tsupport _ hy))
          rw [Real.dist_eq] at h1
          rw [← sub_mul, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact h1.le) (abs_nonneg _)
    _ = ε / (I + 1) * I := by rw [integral_const_mul, hI]
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- The difference quotients of a test function converge to its directional derivative in the
weak sense, with rate `L r` (`abs_sub_add_fderiv_le`), against `G` supported near the ball. -/
theorem norm_integral_mul_difference_quotient_sub_le {x e : Euc d} (he : ‖e‖ = 1) {ρ r : ℝ}
    (hr : 0 < r) (hrρ : r ≤ ρ / 4) {G ψ : Euc d → ℝ} (hψ1 : ContDiff ℝ 1 ψ)
    (hψx : tsupport ψ ⊆ Metric.ball x (ρ / 4)) {L : NNReal} (hL : LipschitzWith L (fderiv ℝ ψ))
    (i1 : Integrable fun y => G y * ((ψ (y - r • e) - ψ y) / r))
    (i2 : Integrable fun y => -(G y * fderiv ℝ ψ y e))
    (iG : Integrable ((Metric.closedBall x (ρ / 2)).indicator fun y => |G y|)) :
    ‖(∫ y, G y * ((ψ (y - r • e) - ψ y) / r)) - ∫ y, -(G y * fderiv ℝ ψ y e)‖ ≤
      L * r * ∫ y, (Metric.closedBall x (ρ / 2)).indicator (fun y => |G y|) y := by
  have hr' : r ≠ 0 := hr.ne'
  have hnorm : ‖r • e‖ = r := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hr.le]
  have hsub42 : Metric.ball x (ρ / 4) ⊆ Metric.closedBall x (ρ / 2) := fun y hy => by
    rw [Metric.mem_ball] at hy
    rw [Metric.mem_closedBall]
    linarith
  have hdψs : tsupport (fun y => fderiv ℝ ψ y e) ⊆ tsupport ψ :=
    (tsupport_comp_subset (g := fun T : Euc d →L[ℝ] ℝ => T e) (by simp) (fderiv ℝ ψ)).trans
      (tsupport_fderiv_subset ℝ)
  rw [← integral_sub i1 i2, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (iG.const_mul _) (Eventually.of_forall fun y => ?_)
  show ‖G y * ((ψ (y - r • e) - ψ y) / r) - -(G y * fderiv ℝ ψ y e)‖ ≤
    L * r * (Metric.closedBall x (ρ / 2)).indicator (fun y => |G y|) y
  by_cases hy : y ∈ Metric.closedBall x (ρ / 2)
  · rw [indicator_of_mem hy, sub_neg_eq_add, ← mul_add, Real.norm_eq_abs, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have h1 := abs_sub_add_fderiv_le hψ1 hL he y hr.le
    have e1 : (ψ (y - r • e) - ψ y) / r + fderiv ℝ ψ y e =
        (ψ (y - r • e) - ψ y + r * fderiv ℝ ψ y e) / r := by
      field_simp
    rw [e1, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    calc |ψ (y - r • e) - ψ y + r * fderiv ℝ ψ y e| ≤ L * r ^ 2 := h1
      _ = L * r * r := by ring
  · rw [indicator_of_notMem hy, mul_zero]
    have hy1 : ψ y = 0 := by
      by_contra h
      exact hy (hsub42 (hψx (subset_tsupport _ h)))
    have hy2 : ψ (y - r • e) = 0 := by
      by_contra h
      have h' := hψx (subset_tsupport _ h)
      refine hy ?_
      rw [Metric.mem_ball] at h'
      rw [Metric.mem_closedBall]
      calc dist y x ≤ dist y (y - r • e) + dist (y - r • e) x := dist_triangle _ _ _
        _ ≤ ρ / 2 := by
            rw [dist_eq_norm, sub_sub_cancel, hnorm]
            linarith
    have hy3 : fderiv ℝ ψ y e = 0 := by
      by_contra h
      exact hy (hsub42 (hψx (hdψs (subset_tsupport _ h))))
    simp [hy1, hy2, hy3]

/-- **The uniform limit of dyadic difference quotients is a weak directional derivative**: if `G`
is continuous on `closedBall x ρ` and `(G(y + s_n e) - G y)/s_n → H` uniformly on `ball x (ρ/2)`
(`s_n = ρ/2^{n+2}`, `‖e‖ = 1`), then `∫ G ∂_e ψ = -∫ H ψ` for every smooth `ψ` supported in
`ball x (ρ/4)`. -/
theorem integral_mul_fderiv_eq_of_tendstoUniformlyOn {x e : Euc d} (he : ‖e‖ = 1) {ρ : ℝ}
    (hρ : 0 < ρ) {G H : Euc d → ℝ} (hG : ContinuousOn G (Metric.closedBall x ρ))
    (hH : TendstoUniformlyOn
      (fun (n : ℕ) y => (G (y + (ρ / 2 ^ (n + 2)) • e) - G y) / (ρ / 2 ^ (n + 2))) H atTop
      (Metric.ball x (ρ / 2)))
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψx : tsupport ψ ⊆ Metric.ball x (ρ / 4)) :
    ∫ y, G y * fderiv ℝ ψ y e = -∫ y, H y * ψ y := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun n => ρ / 2 ^ (n + 2) := ⟨_, rfl⟩
  have hs' : ∀ n, s n = ρ / 2 ^ (n + 2) := fun n => by rw [hs]
  simp only [← hs'] at hH
  have hs0 : ∀ n, 0 < s n := fun n => by
    rw [hs']
    positivity
  have hse : ∀ n, s n = ρ / 4 * (1 / 2) ^ n := fun n => by
    rw [hs', one_div_pow, pow_add]
    field_simp
    norm_num
  have hs4 : ∀ n, s n ≤ ρ / 4 := fun n => by
    rw [hse]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hslim : Tendsto s atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (ρ / 4)
    rw [mul_zero] at h
    exact h.congr fun n => (hse n).symm
  have hnorm : ∀ n, ‖s n • e‖ = s n := fun n => by
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (hs0 n).le]
  have hGball : ContinuousOn G (Metric.ball x ρ) := hG.mono Metric.ball_subset_closedBall
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hsub42 : Metric.ball x (ρ / 4) ⊆ Metric.ball x (ρ / 2) :=
    Metric.ball_subset_ball (by linarith)
  have hDc : ∀ n, ContinuousOn (fun y => (G (y + s n • e) - G y) / s n)
      (Metric.ball x (ρ / 2)) := by
    intro n
    have hc : Continuous fun y : Euc d => y + s n • e := by fun_prop
    refine ((hGball.comp hc.continuousOn fun y hy => ?_).sub
      (hGball.mono (Metric.ball_subset_ball (by linarith)))).div_const _
    rw [Metric.mem_ball] at hy
    show y + s n • e ∈ Metric.ball x ρ
    rw [Metric.mem_ball]
    calc dist (y + s n • e) x ≤ dist (y + s n • e) y + dist y x := dist_triangle _ _ _
      _ < ρ := by
          rw [dist_eq_norm, add_sub_cancel_left, hnorm]
          linarith [hs4 n]
  have hlim1 : Tendsto (fun n => ∫ y, (G (y + s n • e) - G y) / s n * ψ y) atTop
      (𝓝 (∫ y, H y * ψ y)) :=
    tendsto_integral_mul_of_tendstoUniformlyOn Metric.isOpen_ball hDc hH hψ.continuous hψs
      (hψx.trans hsub42)
  have hD : ∀ n, ∫ y, (G (y + s n • e) - G y) / s n * ψ y =
      ∫ y, G y * ((ψ (y - s n • e) - ψ y) / s n) := by
    intro n
    have h := integral_difference_eq (v := s n • e) (by rw [hnorm]; exact hs4 n) hGball
      hψ.continuous hψs hψx
    calc ∫ y, (G (y + s n • e) - G y) / s n * ψ y
        = (∫ y, (G (y + s n • e) - G y) * ψ y) / s n := by
          rw [← integral_div]
          congr 1
          funext y
          ring
      _ = (∫ y, G y * (ψ (y - s n • e) - ψ y)) / s n := by rw [h]
      _ = ∫ y, G y * ((ψ (y - s n • e) - ψ y) / s n) := by
          rw [← integral_div]
          congr 1
          funext y
          ring
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hψs.fderiv (𝕜 := ℝ))
    (hψ.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)) one_ne_zero
  have hdψs : tsupport (fun y => fderiv ℝ ψ y e) ⊆ tsupport ψ :=
    (tsupport_comp_subset (g := fun T : Euc d →L[ℝ] ℝ => T e) (by simp) (fderiv ℝ ψ)).trans
      (tsupport_fderiv_subset ℝ)
  have iGd : Integrable fun y => -(G y * fderiv ℝ ψ y e) :=
    (integrable_mul_of_continuousOn Metric.isOpen_ball hGball
      ((hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hψs.fderiv_apply ℝ e)
      (hdψs.trans (hψx.trans (Metric.ball_subset_ball (by linarith))))).neg
  have iGB : Integrable ((Metric.closedBall x (ρ / 2)).indicator fun y => |G y|) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      ((hG.mono (Metric.closedBall_subset_closedBall (by linarith))).abs.integrableOn_compact
        (isCompact_closedBall x _))
  have i1 : ∀ n, Integrable fun y => G y * ((ψ (y - s n • e) - ψ y) / s n) := by
    intro n
    obtain ⟨-, i2, i3⟩ := integrable_mul_translate (v := s n • e) (by rw [hnorm]; exact hs4 n)
      hGball hψ.continuous hψs hψx
    refine ((i3.sub i2).div_const (s n)).congr (Eventually.of_forall fun y => ?_)
    show (G y * ψ (y - s n • e) - G y * ψ y) / s n = G y * ((ψ (y - s n • e) - ψ y) / s n)
    ring
  have hlim2 : Tendsto (fun n => ∫ y, G y * ((ψ (y - s n • e) - ψ y) / s n)) atTop
      (𝓝 (∫ y, -(G y * fderiv ℝ ψ y e))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_integral_mul_difference_quotient_sub_le he (hs0 n) (hs4 n) hψ1 hψx hL
        (i1 n) iGd iGB) ?_)
    have h := (hslim.const_mul (L : ℝ)).mul_const
      (∫ y, (Metric.closedBall x (ρ / 2)).indicator (fun y => |G y|) y)
    simpa using h
  have huniq := tendsto_nhds_unique (hlim1.congr hD) hlim2
  rw [integral_neg] at huniq
  linarith


/-- **`C¹` from Hölder bounds on second differences**: a function `G` continuous on the open set
`U` such that every `x ∈ U` has a ball, `closedBall x ρ ⊆ U`, on which
`|(G(y + s eᵢ) - G y) - (G(z + s eᵢ) - G z)| ≤ C s |y - z|^α` for the coordinate vectors `eᵢ`
and `0 < s ≤ ρ`, is `C¹` on `U`. The dyadic difference quotients converge uniformly
(`exists_tendstoUniformlyOn_difference_quotient`) to continuous weak partial derivatives
(`integral_mul_fderiv_eq_of_tendstoUniformlyOn`), so `contDiffOn_of_weakGradient` applies. -/
theorem contDiffOn_of_holder_difference {U : Set (Euc d)} {G : Euc d → ℝ}
    (hG : ContinuousOn G U)
    (hq : ∀ x ∈ U, ∃ ρ C α : ℝ, 0 < ρ ∧ 0 < α ∧ Metric.closedBall x ρ ⊆ U ∧
      ∀ i : Fin d, ∀ s : ℝ, 0 < s → s ≤ ρ → ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
        |(G (y + s • EuclideanSpace.single i 1) - G y) -
          (G (z + s • EuclideanSpace.single i 1) - G z)| ≤ C * s * dist y z ^ α) :
    ContDiffOn ℝ 1 G U := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  obtain ⟨ρ, C, α, hρ, hα, hρU, hb⟩ := hq x hx
  have he : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hGc : ContinuousOn G (Metric.closedBall x ρ) := hG.mono hρU
  choose H hH using fun i : Fin d =>
    exists_tendstoUniformlyOn_difference_quotient (he i) hρ hα (hb i)
  have hDc : ∀ (i : Fin d) (n : ℕ), ContinuousOn
      (fun y => (G (y + (ρ / 2 ^ (n + 2)) • EuclideanSpace.single i (1 : ℝ)) - G y) /
        (ρ / 2 ^ (n + 2))) (Metric.ball x (ρ / 2)) := by
    intro i n
    have hs4 : ρ / 2 ^ (n + 2) ≤ ρ / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h4 : (4 : ℝ) ≤ 2 ^ (n + 2) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have hc : Continuous fun y : Euc d =>
        y + (ρ / 2 ^ (n + 2)) • EuclideanSpace.single i (1 : ℝ) := by
      fun_prop
    refine ((hGc.comp hc.continuousOn fun y hy => ?_).sub
      (hGc.mono (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall (by linarith))))).div_const _
    rw [Metric.mem_ball] at hy
    rw [Metric.mem_closedBall]
    calc dist (y + (ρ / 2 ^ (n + 2)) • EuclideanSpace.single i (1 : ℝ)) x
        ≤ dist (y + (ρ / 2 ^ (n + 2)) • EuclideanSpace.single i (1 : ℝ)) y + dist y x :=
          dist_triangle _ _ _
      _ ≤ ρ := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
            Real.norm_of_nonneg (by positivity)]
          linarith
  have hHc : ∀ i, ContinuousOn (H i) (Metric.ball x (ρ / 2)) := fun i =>
    (hH i).continuousOn (Frequently.of_forall (hDc i))
  refine ⟨Metric.ball x (ρ / 4), Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_⟩
  have hsub4 : Metric.ball x (ρ / 4) ⊆ Metric.closedBall x ρ :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hsub : U ∩ Metric.ball x (ρ / 4) = Metric.ball x (ρ / 4) :=
    inter_eq_right.2 (hsub4.trans hρU)
  rw [hsub]
  have hsub42 : Metric.ball x (ρ / 4) ⊆ Metric.ball x (ρ / 2) :=
    Metric.ball_subset_ball (by linarith)
  obtain ⟨Hv, hHv⟩ : ∃ Hv : Euc d → Euc d,
      Hv = fun y => ∑ i, H i y • EuclideanSpace.single i (1 : ℝ) := ⟨_, rfl⟩
  have hHvc : ContinuousOn Hv (Metric.ball x (ρ / 4)) := by
    rw [hHv]
    exact continuousOn_finsetSum _ fun i _ => ((hHc i).mono hsub42).smul continuousOn_const
  refine (contDiffOn_of_weakGradient Metric.isOpen_ball (hGc.mono hsub4) hHvc
    fun ψ hψ hψs hψU v => ?_).1
  have hcoord : ∀ i, ∫ y, G y * fderiv ℝ ψ y (EuclideanSpace.single i 1) =
      -∫ y, H i y * ψ y := fun i =>
    integral_mul_fderiv_eq_of_tendstoUniformlyOn (he i) hρ hGc (hH i) hψ hψs hψU
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v).symm
  have iG : ∀ i, Integrable fun y => G y * fderiv ℝ ψ y (EuclideanSpace.single i 1) := fun i =>
    integrable_mul_of_continuousOn Metric.isOpen_ball (hGc.mono hsub4)
      ((hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hψs.fderiv_apply ℝ _)
      ((tsupport_comp_subset (g := fun T : Euc d →L[ℝ] ℝ => T (EuclideanSpace.single i 1))
        (by simp) (fderiv ℝ ψ)).trans ((tsupport_fderiv_subset ℝ).trans hψU))
  have iH : ∀ i, Integrable fun y => H i y * ψ y := fun i =>
    integrable_mul_of_continuousOn Metric.isOpen_ball ((hHc i).mono hsub42) hψ.continuous hψs hψU
  have e1 : ∀ y, G y * fderiv ℝ ψ y v =
      ∑ i, v i * (G y * fderiv ℝ ψ y (EuclideanSpace.single i 1)) := fun y => by
    conv_lhs => rw [hv]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    ring
  have e2 : ∀ y, ⟪Hv y, v⟫ * ψ y = ∑ i, v i * (H i y * ψ y) := fun y => by
    rw [hHv]
    simp only [sum_inner, real_inner_smul_left, EuclideanSpace.inner_single_left, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_one, one_mul]
    ring
  rw [integral_congr_ae (Eventually.of_forall e1), integral_congr_ae (Eventually.of_forall e2),
    integral_finsetSum _ fun i _ => (iG i).const_mul (v i),
    integral_finsetSum _ fun i _ => (iH i).const_mul (v i), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, hcoord i, mul_neg]


/-! ### The Schauder estimate applied to difference quotients of `∇φ` -/

/-- The gradient of the difference quotient `(φ(· + v) - φ)/s` of a function that is `C¹` on an
open set containing `x` and `x + v`. -/
theorem gradient_difference_quotient {U : Set (Euc d)} (hU : IsOpen U) {φ : Euc d → ℝ}
    (hφ1 : ContDiffOn ℝ 1 φ U) {v : Euc d} (s : ℝ) {x : Euc d} (hx : x ∈ U) (hxv : x + v ∈ U) :
    HasFDerivAt (fun y => (φ (y + v) - φ y) / s) (s⁻¹ • (fderiv ℝ φ (x + v) - fderiv ℝ φ x)) x ∧
      gradient (fun y => (φ (y + v) - φ y) / s) x = s⁻¹ • (gradient φ (x + v) - gradient φ x) := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ (x + v)) (x + v) :=
    ((hφ1.differentiableOn one_ne_zero (x + v) hxv).differentiableAt
      (hU.mem_nhds hxv)).hasFDerivAt
  have h2 : HasFDerivAt φ (fderiv ℝ φ x) x :=
    ((hφ1.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have h3 : HasFDerivAt (fun y => φ (y + v)) (fderiv ℝ φ (x + v)) x := by
    have h := h1.comp x ((hasFDerivAt_id x).add_const v)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have h4 : HasFDerivAt (fun y => (φ (y + v) - φ y) / s)
      (s⁻¹ • (fderiv ℝ φ (x + v) - fderiv ℝ φ x)) x := by
    refine ((h3.sub h2).const_smul s⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    show (φ (y + v) - φ y) / s = s⁻¹ • (φ (y + v) - φ y)
    rw [smul_eq_mul, div_eq_inv_mul]
  refine ⟨h4, ext_inner_right ℝ fun u => ?_⟩
  rw [inner_gradient_left, h4.fderiv, real_inner_smul_left, inner_sub_left, inner_gradient_left,
    inner_gradient_left]
  simp

/-- A difference quotient of a Lipschitz function is bounded by the Lipschitz constant. -/
theorem abs_difference_quotient_le {S : Set (Euc d)} {f : Euc d → ℝ} {K : ℝ}
    (hK : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ K * dist x y) {x v : Euc d} (hx : x ∈ S)
    (hxv : x + v ∈ S) {s : ℝ} (hs : 0 < s) (hv : ‖v‖ = s) : |(f (x + v) - f x) / s| ≤ K := by
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have h := hK (x + v) hxv x hx
  rwa [dist_eq_norm, add_sub_cancel_left, hv] at h

/-- **The weak equation of a difference quotient**: `w = (φ(· + v) - φ)/s` solves
`∫ ⟪A_v ∇w, ∇ψ⟫ = ∫ λ (φ(x+v)^{p-1} - φ(x)^{p-1})/s ψ` for test functions supported in a set on
which `x, x + v ∈ U` and `∇φ(x), ∇φ(x+v) ∈ N` (`integral_inner_linearized_eq`). -/
theorem integral_inner_difference_quotient_eq {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {U : Set (Euc d)} (hU : IsOpen U) {φ : Euc d → ℝ} {lam : ℝ}
    (hφ1 : ContDiffOn ℝ 1 φ U)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ = lam * ∫ x, φ x ^ (p - 1) * ψ x)
    {N : Set (Euc d)} (hNcv : Convex ℝ N) (hN0 : (0 : Euc d) ∉ N) (v : Euc d) (s : ℝ)
    {B : Set (Euc d)}
    (hB : ∀ x ∈ B, x ∈ U ∧ x + v ∈ U ∧ gradient φ x ∈ N ∧ gradient φ (x + v) ∈ N)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ B) :
    ∫ x, ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F)
        (gradient φ x + t • (gradient φ (x + v) - gradient φ x)))
          (gradient (fun y => (φ (y + v) - φ y) / s) x), gradient ψ x⟫ =
      ∫ x, lam * (φ (x + v) ^ (p - 1) - φ x ^ (p - 1)) / s * ψ x := by
  have hpt : ∀ x, ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F)
      (gradient φ x + t • (gradient φ (x + v) - gradient φ x)))
        (gradient (fun y => (φ (y + v) - φ y) / s) x), gradient ψ x⟫ =
      s⁻¹ * ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (flux p F)
        (gradient φ x + t • (gradient φ (x + v) - gradient φ x)))
          (gradient φ (x + v) - gradient φ x), gradient ψ x⟫ := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · obtain ⟨hxU, hxvU, -, -⟩ := hB x (hψB hx)
      rw [(gradient_difference_quotient hU hφ1 s hxU hxvU).2, map_smul, real_inner_smul_left]
    · rw [gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right, inner_zero_right, mul_zero]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_inner_linearized_eq hp hF hU hφ1 hweak hNcv hN0 v hψ hψs
      (fun x hx => hB x (hψB hx)), ← mul_assoc, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show s⁻¹ * lam * ((φ (x + v) ^ (p - 1) - φ x ^ (p - 1)) * ψ x) =
    lam * (φ (x + v) ^ (p - 1) - φ x ^ (p - 1)) / s * ψ x
  ring

/-- **The Schauder estimate applied to difference quotients** (the difference-quotient argument
of Gilbarg–Trudinger §8.11 with the interior estimate `schauder_C2`): on a ball `B(x₀, 6R)` inside
`U` on which `∇φ` takes values in a convex set `N ∌ 0` where `A = Da` is uniformly elliptic,
bounded and Lipschitz, `∇φ` is `α`-Hölder and `φ`, `φ^{p-1}` are Lipschitz, every difference
quotient `w = (φ(· + v) - φ)/s`, `‖v‖ = s ≤ R`, solves the linear equation
`div(A_v ∇w) = -λ (φ(·+v)^{p-1} - φ^{p-1})/s` with uniformly controlled data, so
`|∇w(y) - ∇w(z)| ≤ C |y - z|^α` on `B(x₀, R)` with `C` independent of `v`. -/
theorem exists_schauder_difference_bound {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {U : Set (Euc d)} (hU : IsOpen U) {φ : Euc d → ℝ} {lam : ℝ}
    (hφ1 : ContDiffOn ℝ 1 φ U)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ = lam * ∫ x, φ x ^ (p - 1) * ψ x)
    {N : Set (Euc d)} (hNcv : Convex ℝ N) (hN0 : (0 : Euc d) ∉ N) {μ Λ₁ L : ℝ} (hμ : 0 < μ)
    (hμA : ∀ ξ ∈ N, ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪fderiv ℝ (flux p F) ξ ζ, ζ⟫)
    (hΛA : ∀ ξ ∈ N, ‖fderiv ℝ (flux p F) ξ‖ ≤ Λ₁)
    (hLA : ∀ ξ ∈ N, ∀ η ∈ N, ‖fderiv ℝ (flux p F) ξ - fderiv ℝ (flux p F) η‖ ≤ L * ‖ξ - η‖)
    (hL0 : 0 ≤ L) {x₀ : Euc d} {R α C' K₁ K₂ : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hS : Metric.closedBall x₀ (6 * R) ⊆ U)
    (hSN : ∀ x ∈ Metric.closedBall x₀ (6 * R), gradient φ x ∈ N)
    (hHol : ∀ x ∈ Metric.closedBall x₀ (6 * R), ∀ y ∈ Metric.closedBall x₀ (6 * R),
      ‖gradient φ x - gradient φ y‖ ≤ C' * dist x y ^ α)
    (hK₁ : ∀ x ∈ Metric.closedBall x₀ (6 * R), ∀ y ∈ Metric.closedBall x₀ (6 * R),
      |φ x - φ y| ≤ K₁ * dist x y)
    (hK₂ : ∀ x ∈ Metric.closedBall x₀ (6 * R), ∀ y ∈ Metric.closedBall x₀ (6 * R),
      |φ x ^ (p - 1) - φ y ^ (p - 1)| ≤ K₂ * dist x y) :
    ∃ CS : ℝ, ∀ (v : Euc d) (s : ℝ), 0 < s → s ≤ R → ‖v‖ = s →
      ∀ y ∈ Metric.ball x₀ R, ∀ z ∈ Metric.ball x₀ R,
        ‖(gradient φ (y + v) - gradient φ y) - (gradient φ (z + v) - gradient φ z)‖ ≤
          CS * s * dist y z ^ α := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = max (max Λ₁ (2 * L * C')) (max (|lam| * K₂) K₁) := ⟨_, rfl⟩
  have hΛ1 : Λ₁ ≤ Λ := hΛ ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hΛ2 : 2 * L * C' ≤ Λ := hΛ ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hΛ3 : |lam| * K₂ ≤ Λ := hΛ ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hΛ4 : K₁ ≤ Λ := hΛ ▸ (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨CS, hCS⟩ := schauder_C2 d (Λ := Λ) hα hα1 hμ (by positivity : (0 : ℝ) < 2 * R)
  refine ⟨CS, fun v s hs hsR hv y hy z hz => ?_⟩
  have hmem : ∀ x ∈ Metric.ball x₀ (2 * (2 * R)),
      x ∈ Metric.closedBall x₀ (6 * R) ∧ x + v ∈ Metric.closedBall x₀ (6 * R) := by
    intro x hx
    rw [Metric.mem_ball] at hx
    refine ⟨Metric.mem_closedBall.2 (by linarith), Metric.mem_closedBall.2 ?_⟩
    calc dist (x + v) x₀ ≤ dist (x + v) x + dist x x₀ := dist_triangle _ _ _
      _ ≤ 6 * R := by
          rw [dist_eq_norm, add_sub_cancel_left, hv]
          linarith
  have hdist : ∀ x y : Euc d, dist (x + v) (y + v) = dist x y := fun x y => by
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub]
  obtain ⟨A, hA⟩ : ∃ A : Euc d → Euc d →L[ℝ] Euc d, A = fun x => ∫ t in (0 : ℝ)..1,
      fderiv ℝ (flux p F) (gradient φ x + t • (gradient φ (x + v) - gradient φ x)) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Euc d → ℝ, w = fun x => (φ (x + v) - φ x) / s := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Euc d → ℝ,
      g = fun x => lam * (φ (x + v) ^ (p - 1) - φ x ^ (p - 1)) / s := ⟨_, rfl⟩
  have hAb : ∀ x ∈ Metric.ball x₀ (2 * (2 * R)), ∀ y ∈ Metric.ball x₀ (2 * (2 * R)),
      (∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) ∧ ‖A x‖ ≤ Λ₁ ∧
        ‖A x - A y‖ ≤ L * (‖gradient φ x - gradient φ y‖ +
          ‖gradient φ (x + v) - gradient φ (y + v)‖) := fun x hx y hy => by
    rw [hA]
    exact hF.integral_fderiv_flux_bounds p hNcv hN0 hμA hΛA hLA hL0 (hSN _ (hmem x hx).1)
      (hSN _ (hmem x hx).2) (hSN _ (hmem y hy).1) (hSN _ (hmem y hy).2)
  have hgradw : ∀ x ∈ Metric.ball x₀ (2 * (2 * R)),
      gradient w x = s⁻¹ • (gradient φ (x + v) - gradient φ x) := fun x hx => by
    rw [hw]
    exact (gradient_difference_quotient hU hφ1 s (hS (hmem x hx).1) (hS (hmem x hx).2)).2
  have h3 : ∀ x ∈ Metric.ball x₀ (2 * (2 * R)), ∀ y ∈ Metric.ball x₀ (2 * (2 * R)),
      ‖A x - A y‖ ≤ Λ * dist x y ^ α := fun x hx y hy => by
    have hx1 := hHol _ (hmem x hx).1 _ (hmem y hy).1
    have hx2 := hHol _ (hmem x hx).2 _ (hmem y hy).2
    rw [hdist] at hx2
    refine (hAb x hx y hy).2.2.trans ?_
    calc L * (‖gradient φ x - gradient φ y‖ + ‖gradient φ (x + v) - gradient φ (y + v)‖)
        ≤ L * (C' * dist x y ^ α + C' * dist x y ^ α) :=
          mul_le_mul_of_nonneg_left (add_le_add hx1 hx2) hL0
      _ = 2 * L * C' * dist x y ^ α := by ring
      _ ≤ Λ * dist x y ^ α := mul_le_mul_of_nonneg_right hΛ2 (Real.rpow_nonneg dist_nonneg _)
  have h4 : ContinuousOn g (Metric.ball x₀ (2 * (2 * R))) := by
    rw [hg]
    have hc : Continuous fun x : Euc d => x + v := by fun_prop
    have hφc : ContinuousOn φ U := hφ1.continuousOn
    refine ContinuousOn.div_const (continuousOn_const.mul (ContinuousOn.sub ?_ ?_)) s
    · exact (hφc.comp hc.continuousOn fun x hx => hS (hmem x hx).2).rpow_const
        fun _ _ => Or.inr (by linarith)
    · exact (hφc.mono fun x hx => hS (hmem x hx).1).rpow_const fun _ _ => Or.inr (by linarith)
  have h5 : ∀ x ∈ Metric.ball x₀ (2 * (2 * R)), |g x| ≤ Λ := fun x hx => by
    rw [hg]
    show |lam * (φ (x + v) ^ (p - 1) - φ x ^ (p - 1)) / s| ≤ Λ
    have hd : |(φ (x + v) ^ (p - 1) - φ x ^ (p - 1)) / s| ≤ K₂ :=
      abs_difference_quotient_le (f := fun x => φ x ^ (p - 1)) hK₂ (hmem x hx).1 (hmem x hx).2
        hs hv
    rw [mul_div_assoc, abs_mul]
    exact (mul_le_mul_of_nonneg_left hd (abs_nonneg lam)).trans hΛ3
  have h6 : ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * (2 * R))) := by
    rw [hw]
    have hc : ContDiff ℝ 1 fun x : Euc d => x + v := by fun_prop
    exact ((hφ1.comp hc.contDiffOn fun x hx => hS (hmem x hx).2).sub
      (hφ1.mono fun x hx => hS (hmem x hx).1)).div_const s
  have h7 : ∀ x ∈ Metric.ball x₀ (2 * (2 * R)), |w x| ≤ Λ := fun x hx => by
    rw [hw]
    exact (abs_difference_quotient_le hK₁ (hmem x hx).1 (hmem x hx).2 hs hv).trans hΛ4
  have h8 : ∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * (2 * R)), ∀ y ∈ Metric.ball x₀ (2 * (2 * R)),
      ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α := by
    refine ⟨s⁻¹ * (2 * C'), fun x hx y hy => ?_⟩
    rw [hgradw x hx, hgradw y hy, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    have hx1 := hHol _ (hmem x hx).1 _ (hmem y hy).1
    have hx2 := hHol _ (hmem x hx).2 _ (hmem y hy).2
    rw [hdist] at hx2
    have e : (gradient φ (x + v) - gradient φ x) - (gradient φ (y + v) - gradient φ y) =
        (gradient φ (x + v) - gradient φ (y + v)) - (gradient φ x - gradient φ y) := by abel
    calc s⁻¹ * ‖(gradient φ (x + v) - gradient φ x) - (gradient φ (y + v) - gradient φ y)‖
        ≤ s⁻¹ * (‖gradient φ (x + v) - gradient φ (y + v)‖ + ‖gradient φ x - gradient φ y‖) := by
          rw [e]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.2 hs.le)
      _ ≤ s⁻¹ * (C' * dist x y ^ α + C' * dist x y ^ α) :=
          mul_le_mul_of_nonneg_left (add_le_add hx2 hx1) (inv_nonneg.2 hs.le)
      _ = s⁻¹ * (2 * C') * dist x y ^ α := by ring
  have h9 : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball x₀ (2 * (2 * R)) →
      ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x := fun ψ hψ hψs hψB => by
    rw [hA, hw, hg]
    exact integral_inner_difference_quotient_eq hp hF hU hφ1 hweak hNcv hN0 v s
      (fun x hx => ⟨hS (hmem x hx).1, hS (hmem x hx).2, hSN _ (hmem x hx).1,
        hSN _ (hmem x hx).2⟩) hψ hψs hψB
  have hconc := hCS x₀ A g w (fun x hx ζ => (hAb x hx x hx).1 ζ)
    (fun x hx => (hAb x hx x hx).2.1.trans hΛ1) h3 h4 h5 h6 h7 h8 h9
  have hy4 : y ∈ Metric.ball x₀ (2 * (2 * R)) := Metric.ball_subset_ball (by linarith) hy
  have hz4 : z ∈ Metric.ball x₀ (2 * (2 * R)) := Metric.ball_subset_ball (by linarith) hz
  have hb := (hconc y (Metric.ball_subset_ball (by linarith) hy)).2 z
    (Metric.ball_subset_ball (by linarith) hz)
  rw [hgradw y hy4, hgradw z hz4, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le),
    inv_mul_le_iff₀ hs] at hb
  calc ‖(gradient φ (y + v) - gradient φ y) - (gradient φ (z + v) - gradient φ z)‖
      ≤ s * (CS * dist y z ^ α) := hb
    _ = CS * s * dist y z ^ α := by ring

/-- **Hölder bounds for the difference quotients of `∇φ` near a noncritical point**: if `φ` is
`C¹` and positive on the open set `U`, `∇φ` is locally Hölder, `φ` solves the weak flux equation
on `U`, and `∇φ(x₀) ≠ 0`, then on a ball around `x₀` the coordinate difference quotients of `∇φ`
are uniformly Hölder: `‖Δ_{s eᵢ}∇φ(y) - Δ_{s eᵢ}∇φ(z)‖ ≤ C s |y - z|^α`. Near `x₀`, `∇φ` stays in
the closed ball `N = B̄(∇φ(x₀), |∇φ(x₀)|/2)`, which avoids `0`, so `A = Da` is uniformly elliptic
there (`exists_fderiv_flux_bounds`) and `exists_schauder_difference_bound` applies. -/
theorem exists_holder_difference_gradient {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {U : Set (Euc d)} (hU : IsOpen U) {φ : Euc d → ℝ} {lam : ℝ}
    (hφ1 : ContDiffOn ℝ 1 φ U) (hφ0 : ∀ x ∈ U, 0 < φ x)
    (hφα : ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
      ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r (gradient φ) S)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ = lam * ∫ x, φ x ^ (p - 1) * ψ x)
    {x₀ : Euc d} (hx₀ : x₀ ∈ U) (hne : gradient φ x₀ ≠ 0) :
    ∃ ρ C α : ℝ, 0 < ρ ∧ 0 < α ∧ Metric.closedBall x₀ ρ ⊆ U ∧
      ∀ i : Fin d, ∀ s : ℝ, 0 < s → s ≤ ρ → ∀ y ∈ Metric.ball x₀ ρ, ∀ z ∈ Metric.ball x₀ ρ,
        ‖(gradient φ (y + s • EuclideanSpace.single i 1) - gradient φ y) -
          (gradient φ (z + s • EuclideanSpace.single i 1) - gradient φ z)‖ ≤
            C * s * dist y z ^ α := by
  have hn : 0 < ‖gradient φ x₀‖ := norm_pos_iff.2 hne
  have hN0 : (0 : Euc d) ∉ Metric.closedBall (gradient φ x₀) (‖gradient φ x₀‖ / 2) := by
    rw [Metric.mem_closedBall, dist_zero_left]
    linarith
  obtain ⟨μ, Λ₁, L, hμ, -, hL0, hμA, hΛA, hLA⟩ :=
    hF.exists_fderiv_flux_bounds hp (isCompact_closedBall _ _) (convex_closedBall _ _) hN0
  have hgc : ContinuousOn (gradient φ) U :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hφ1.continuousOn_fderiv_of_isOpen hU le_rfl)
  obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  obtain ⟨δ, hδ, hδN⟩ :=
    Metric.continuousAt_iff.1 (hgc.continuousAt (hU.mem_nhds hx₀)) _ (half_pos hn)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = min r₁ δ / 8 := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    rw [hR]
    exact div_pos (lt_min hr₁ hδ) (by norm_num)
  have h6r : 6 * R < r₁ := by
    rw [hR]
    linarith [min_le_left r₁ δ]
  have h6δ : 6 * R < δ := by
    rw [hR]
    linarith [min_le_right r₁ δ]
  have hS : Metric.closedBall x₀ (6 * R) ⊆ U :=
    (Metric.closedBall_subset_ball h6r).trans hr₁U
  have hSN : ∀ x ∈ Metric.closedBall x₀ (6 * R),
      gradient φ x ∈ Metric.closedBall (gradient φ x₀) (‖gradient φ x₀‖ / 2) := fun x hx =>
    Metric.mem_closedBall.2 (hδN (lt_of_le_of_lt (Metric.mem_closedBall.1 hx) h6δ)).le
  obtain ⟨Cφ, rφ, hrφ, hHφ⟩ := hφα _ (isCompact_closedBall x₀ (6 * R)) hS
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = min (rφ : ℝ) (1 / 2) := ⟨_, rfl⟩
  have hα0 : 0 < α := by
    rw [hα]
    exact lt_min hrφ (by norm_num)
  have hα1 : α < 1 := by
    rw [hα]
    exact (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨C', hC'⟩ := HolderOnWith.exists_holderOnWith_of_le ⟨Cφ, hHφ⟩
    (show α.toNNReal ≤ rφ from Real.toNNReal_le_iff_le_coe.2 (by rw [hα]; exact min_le_left _ _))
    Metric.isBounded_closedBall
  have hHol : ∀ x ∈ Metric.closedBall x₀ (6 * R), ∀ y ∈ Metric.closedBall x₀ (6 * R),
      ‖gradient φ x - gradient φ y‖ ≤ C' * dist x y ^ α := fun x hx y hy => by
    have h := hC'.dist_le hx hy
    rwa [Real.coe_toNNReal _ hα0.le, dist_eq_norm] at h
  obtain ⟨K₁, hK₁⟩ := (hφ1.mono hS).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  obtain ⟨K₂, hK₂⟩ := ((hφ1.rpow_const_of_ne fun x hx => (hφ0 x hx).ne').mono
    hS).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨CS, hCS⟩ := exists_schauder_difference_bound hp hF hU hφ1 hweak (convex_closedBall _ _)
    hN0 hμ hμA hΛA hLA hL0 hR0 hα0 hα1 hS hSN hHol
    (fun x hx y hy => by
      have h := hK₁.dist_le_mul x hx y hy
      rwa [Real.dist_eq] at h)
    (fun x hx y hy => by
      have h := hK₂.dist_le_mul x hx y hy
      rwa [Real.dist_eq] at h)
  refine ⟨R, CS, α, hR0, hα0, (Metric.closedBall_subset_closedBall (by linarith)).trans hS,
    fun i s hs hsR y hy z hz => ?_⟩
  exact hCS _ s hs hsR (by rw [norm_smul, Real.norm_of_nonneg hs.le]; simp) y hy z hz

end Komlos.Literature
