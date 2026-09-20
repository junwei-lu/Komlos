import Komlos.Literature.Sobolev.Defs

/-!
# Density of `C_c^∞(K)` in `W₀^{1,p}(K)` at the level of the eigenvalue

For a bounded open convex `K` and a continuous integrand `0 ≤ F ≤ C ‖·‖`, the anisotropic
`p`-eigenvalue over smooth test functions `lambdaGen p F K` is at most the Sobolev eigenvalue
`lambdaSob p F K` over `W₀^{1,p}(K)` (paper (3.7); the reverse inequality is
`lambdaSob_le_lambdaGen`), so the two agree (`lambdaSob_eq_lambdaGen`). The proof is the
contract-and-mollify argument of the smooth density bridge `Komlos.exists_smooth_approx` (paper,
proof of Lemma 3.2, first paragraph), now carried out for `W^{1,p}` functions and their weak
gradients:

* `integral_comp_dilate`, `eLpNorm_comp_dilate`, `memLp_comp_dilate` — change of variables under
  the dilation `x ↦ x₀ + r⁻¹ • (x − x₀)`;
* `HasWeakGradient.comp_dilate` — the weak gradient of `f (x₀ + r⁻¹ • (x − x₀))` is
  `r⁻¹ • ∇f (x₀ + r⁻¹ • (x − x₀))`;
* `lambdaGen_le_div_of_isCompact` — for `f ∈ W^{1,p}` vanishing outside a compact `L ⊆ K`, the
  mollifications `ρ_n ⋆ f` are test functions on `K` whose Rayleigh quotients converge to
  `(∫ F(∇f)^p) / ∫ |f|^p` (`tendsto_eLpNorm_mollifyWith_sub` for `f` and `∇f`, and continuity of
  Nemytskii functionals `tendsto_integral_comp_of_tendsto_eLpNorm`);
* `lambdaGen_le_sobolevRayleigh`, `lambdaGen_le_lambdaSob` — contract `f ∈ W₀^{1,p}(K)` by a
  factor `r < 1` towards an interior point (`dilate_closure_add_ball_subset`), apply the previous
  step, and let `r ↑ 1`.

The last section upgrades a *weak equation* from test functions to Sobolev functions.  Since
`MemW0` is defined pointwise, with no closure operation (see `Komlos.Literature.MemW0`), the
density of `C_c^∞` in `W₀^{1,p}` is a theorem and not a definitional unfolding:

* `exists_contDiff_tendsto_eLpNorm_of_hasWeakGradient`, `MemW0.exists_contDiff_tendsto_eLpNorm` —
  `C_c^∞(Ω)` is dense in `W₀^{1,p}(K)` for `K` compact inside the open set `Ω`, in the graph norm
  (mollify with radii below the distance from `K` to `Ωᶜ`);
* `enorm_integral_le_of_enorm_le_mul`, `integrable_of_enorm_le_enorm_mul`,
  `tendsto_integral_inner_of_tendsto_eLpNorm`, `tendsto_integral_mul_of_tendsto_eLpNorm` — Hölder:
  pairing against a fixed `L^{p'}` function is continuous along `L^p`-convergent sequences;
* `integral_inner_weakGrad_eq_of_memW0` and its localized and `p = 2` variants
  `integral_inner_weakGrad_eq_of_memW0_indicator`, `integral_inner_weakGrad_eq_of_memW0_two` —
  if `∫ ⟪Φ, ∇χ⟫ = ∫ g χ` for every `χ ∈ C_c^∞(Ω)`, then the same holds for every
  `ψ ∈ W₀^{1,p}(K)`, `K` compact `⊆ Ω`.  This is one of the missing inputs of
  `Komlos.Literature.exists_frozen_replacement_data` (`PLaplacian/SchauderHarmonic.lean`).
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff Convolution

namespace Komlos.Literature

variable {d : ℕ} {p : ℝ}

/-! ### Change of variables under a dilation -/

/-- Change of variables for the Bochner integral under the dilation `x ↦ x₀ + r⁻¹ • (x − x₀)`
(which multiplies Lebesgue measure by `r ^ d`); no integrability is needed. -/
theorem integral_comp_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : Euc d → E) (x₀ : Euc d) {r : ℝ} (hr : 0 < r) :
    ∫ x, G (x₀ + r⁻¹ • (x - x₀)) = r ^ d • ∫ x, G x := by
  rw [integral_sub_right_eq_self (fun x => G (x₀ + r⁻¹ • x)) x₀,
    Measure.integral_comp_inv_smul volume (fun x => G (x₀ + x)) r, integral_add_left_eq_self G x₀,
    finrank_euclideanSpace_fin, abs_of_pos (pow_pos hr d)]

/-- The dilation `x ↦ x₀ + r⁻¹ • (x − x₀)` is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_dilate (x₀ : Euc d) {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (fun x : Euc d => x₀ + r⁻¹ • (x - x₀)) volume volume :=
  ((measurePreserving_add_left volume x₀).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hr.ne'))).comp
    (measurePreserving_sub_right volume x₀).quasiMeasurePreserving

/-- `‖f (x₀ + r⁻¹ • (· − x₀))‖_{L^q} = (r ^ d)^{1/q} ‖f‖_{L^q}`. -/
theorem eLpNorm_comp_dilate {E : Type*} [NormedAddCommGroup E] (f : Euc d → E) (x₀ : Euc d)
    {r : ℝ} (hr : 0 < r) {q : ℝ} (hq : 0 < q) :
    eLpNorm (fun x => f (x₀ + r⁻¹ • (x - x₀))) (ENNReal.ofReal q) =
      ENNReal.ofReal (r ^ d) ^ (1 / q) * eLpNorm f (ENNReal.ofReal q) := by
  have hq' : ENNReal.ofReal q ≠ 0 := by simpa using hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq' ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le,
    lintegral_comp_dilate (fun x => ‖f x‖ₑ ^ q) x₀ hr,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

/-- Dilations preserve `L^q`. -/
theorem memLp_comp_dilate {E : Type*} [NormedAddCommGroup E] {f : Euc d → E} {q : ℝ}
    (hq : 0 < q) (hf : MemLp f (ENNReal.ofReal q)) (x₀ : Euc d) {r : ℝ} (hr : 0 < r) :
    MemLp (fun x => f (x₀ + r⁻¹ • (x - x₀))) (ENNReal.ofReal q) := by
  refine ⟨hf.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_dilate x₀ hr), ?_⟩
  rw [eLpNorm_comp_dilate f x₀ hr hq]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    hf.2

/-! ### Weak gradients under a dilation -/

/-- The affine homeomorphism `y ↦ x₀ + r • (y − x₀)` (`r ≠ 0`). -/
noncomputable def contractHomeomorph (x₀ : Euc d) {r : ℝ} (hr : r ≠ 0) : Euc d ≃ₜ Euc d :=
  (Homeomorph.subRight x₀).trans ((Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addLeft x₀))

theorem contractHomeomorph_apply (x₀ : Euc d) {r : ℝ} (hr : r ≠ 0) (y : Euc d) :
    contractHomeomorph x₀ hr y = x₀ + r • (y - x₀) := rfl

/-- `∂_v [ψ (x₀ + r • (· − x₀))] (y) = r ∂_v ψ (x₀ + r • (y − x₀))`. -/
theorem fderiv_comp_contract_apply {ψ : Euc d → ℝ} (hψ : Differentiable ℝ ψ) (x₀ : Euc d)
    (r : ℝ) (y v : Euc d) :
    fderiv ℝ (fun y => ψ (x₀ + r • (y - x₀))) y v = r * fderiv ℝ ψ (x₀ + r • (y - x₀)) v := by
  have h1 : HasFDerivAt (fun y : Euc d => x₀ + r • (y - x₀))
      (r • ContinuousLinearMap.id ℝ (Euc d)) y :=
    (((hasFDerivAt_id y).sub_const x₀).const_smul r).const_add x₀
  have h2 : HasFDerivAt (fun y => ψ (x₀ + r • (y - x₀)))
      ((fderiv ℝ ψ (x₀ + r • (y - x₀))).comp (r • ContinuousLinearMap.id ℝ (Euc d))) y :=
    (hψ _).hasFDerivAt.comp y h1
  rw [h2.fderiv]
  simp

/-- **Weak gradients under a dilation**: if `g` is a weak gradient of `f` (both in `L^q`,
`1 ≤ q`), then `x ↦ r⁻¹ • g (x₀ + r⁻¹ • (x − x₀))` is a weak gradient of
`x ↦ f (x₀ + r⁻¹ • (x − x₀))` (change of variables in the integration-by-parts identity, with
the pulled-back test function `ψ (x₀ + r • (· − x₀))`). -/
theorem HasWeakGradient.comp_dilate {f : Euc d → ℝ} {g : Euc d → Euc d}
    (hfg : HasWeakGradient f g) {q : ℝ} (hq : 1 ≤ q) (hf : MemLp f (ENNReal.ofReal q))
    (hg : MemLp g (ENNReal.ofReal q)) (x₀ : Euc d) {r : ℝ} (hr : 0 < r) :
    HasWeakGradient (fun x => f (x₀ + r⁻¹ • (x - x₀)))
      (fun x => r⁻¹ • g (x₀ + r⁻¹ • (x - x₀))) := by
  have hq0 : 0 < q := by linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq
  refine ⟨(memLp_comp_dilate hq0 hf x₀ hr).locallyIntegrable hq1,
    ((memLp_comp_dilate hq0 hg x₀ hr).const_smul r⁻¹).locallyIntegrable hq1,
    fun ψ hψ hψs v => ?_⟩
  set ψ' : Euc d → ℝ := fun y => ψ (x₀ + r • (y - x₀)) with hψ'_def
  have hψ' : ContDiff ℝ ∞ ψ' :=
    hψ.comp (contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul r))
  have hψ's : HasCompactSupport ψ' := by
    have h := hψs.comp_homeomorph (contractHomeomorph x₀ hr.ne')
    have he : ψ ∘ contractHomeomorph x₀ hr.ne' = ψ' :=
      funext fun y => by simp only [Function.comp_apply, contractHomeomorph_apply, hψ'_def]
    rwa [he] at h
  have key := hfg.integral_mul_fderiv ψ' hψ' hψ's v
  have hinv : ∀ x : Euc d, x₀ + r • (x₀ + r⁻¹ • (x - x₀) - x₀) = x := fun x => by
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  have hL : ∀ x, f (x₀ + r⁻¹ • (x - x₀)) * fderiv ℝ ψ x v =
      r⁻¹ * (f (x₀ + r⁻¹ • (x - x₀)) * fderiv ℝ ψ' (x₀ + r⁻¹ • (x - x₀)) v) := fun x => by
    rw [hψ'_def, fderiv_comp_contract_apply (hψ.differentiable (by simp)) x₀ r, hinv,
      mul_left_comm, inv_mul_cancel_left₀ hr.ne']
  have hR : ∀ x, inner ℝ (r⁻¹ • g (x₀ + r⁻¹ • (x - x₀))) v * ψ x =
      r⁻¹ * (inner ℝ (g (x₀ + r⁻¹ • (x - x₀))) v * ψ' (x₀ + r⁻¹ • (x - x₀))) := fun x => by
    simp only [hψ'_def, hinv, inner_smul_left, RCLike.conj_to_real]
    ring
  have e1 : ∫ x, f (x₀ + r⁻¹ • (x - x₀)) * fderiv ℝ ψ x v =
      r⁻¹ * (r ^ d • ∫ y, f y * fderiv ℝ ψ' y v) := by
    rw [← integral_comp_dilate (fun y => f y * fderiv ℝ ψ' y v) x₀ hr, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hL)
  have e2 : ∫ x, inner ℝ (r⁻¹ • g (x₀ + r⁻¹ • (x - x₀))) v * ψ x =
      r⁻¹ * (r ^ d • ∫ y, inner ℝ (g y) v * ψ' y) := by
    rw [← integral_comp_dilate (fun y => inner ℝ (g y) v * ψ' y) x₀ hr, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hR)
  show ∫ x, f (x₀ + r⁻¹ • (x - x₀)) * fderiv ℝ ψ x v =
    -∫ x, inner ℝ (r⁻¹ • g (x₀ + r⁻¹ • (x - x₀))) v * ψ x
  rw [e1, e2, key, smul_eq_mul, smul_eq_mul]
  ring

/-! ### Mollifying a function supported in a compact subset of `K` -/

/-- A growth bound `F ≤ C ‖·‖` with `F ≥ 0` gives `‖F ξ ^ p‖ ≤ (max C 0)^p ‖ξ‖^p`. -/
theorem norm_rpow_le_of_le_mul_norm {F : Euc d → ℝ} (hF0 : ∀ ξ, 0 ≤ F ξ) {C : ℝ}
    (hFC : ∀ ξ, F ξ ≤ C * ‖ξ‖) (hp0 : 0 < p) (ξ : Euc d) :
    ‖F ξ ^ p‖ ≤ max C 0 ^ p * ‖ξ‖ ^ p := by
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hF0 ξ) p),
    ← Real.mul_rpow (le_max_right _ _) (norm_nonneg _)]
  exact Real.rpow_le_rpow (hF0 ξ)
    ((hFC ξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) hp0.le

/-- `∫ |f|^p > 0` for `f ∈ L^p` not a.e. zero. -/
theorem integral_abs_rpow_pos (hp0 : 0 < p) {f : Euc d → ℝ} (hf : MemLp f (ENNReal.ofReal p))
    (hf0 : ¬ f =ᵐ[volume] 0) : 0 < ∫ x, |f x| ^ p := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have h1 := integral_norm_rpow_eq hp0 hf
  simp only [Real.norm_eq_abs] at h1
  rw [h1]
  exact Real.rpow_pos_of_pos (ENNReal.toReal_pos
    (fun h => hf0 ((eLpNorm_eq_zero_iff hf.1 hp').1 h)) hf.eLpNorm_ne_top) p

/-- **Mollification gives test functions with converging Rayleigh quotients**: if `f ∈ L^p` has
weak gradient `g ∈ L^p`, vanishes outside a compact `L` inside the open set `K`, and is not a.e.
zero, then `λ_{p,F}(K) ≤ (∫ F(g)^p) / ∫ |f|^p` for a continuous integrand `0 ≤ F ≤ C ‖·‖`. -/
theorem lambdaGen_le_div_of_isCompact (hp : 1 < p) {F : Euc d → ℝ} (hF : Continuous F)
    (hF0 : ∀ ξ, 0 ≤ F ξ) {C : ℝ} (hFC : ∀ ξ, F ξ ≤ C * ‖ξ‖) {K : Set (Euc d)} (hKo : IsOpen K)
    {L : Set (Euc d)} (hL : IsCompact L) (hLK : L ⊆ K) {f : Euc d → ℝ} {g : Euc d → Euc d}
    (hfg : HasWeakGradient f g) (hf : MemLp f (ENNReal.ofReal p))
    (hg : MemLp g (ENNReal.ofReal p)) (hfL : ∀ x, x ∉ L → f x = 0) (hf0 : ¬ f =ᵐ[volume] 0) :
    lambdaGen p F K ≤ (∫ x, F (g x) ^ p) / ∫ x, |f x| ^ p := by
  have hp0 : 0 < p := by linarith
  obtain ⟨δ, hδ, hLδ⟩ := hL.exists_cthickening_subset_open hKo hLK
  set φ : ℕ → ContDiffBump (0 : Euc d) := fun n => mollifierBump n with hφ_def
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set u : ℕ → Euc d → ℝ := fun n => mollifyWith ((φ n).normed volume) f with hu_def
  have hgrad : ∀ n, gradient (u n) = mollifyWith ((φ n).normed volume) g := fun n =>
    gradient_mollifyWith hfg (φ n).contDiff_normed (φ n).hasCompactSupport_normed
  have hu_memLp : ∀ n, MemLp (u n) (ENNReal.ofReal p) := fun n =>
    memLp_mollifyWith_normed hp hf (φ n)
  have hG_memLp : ∀ n, MemLp (gradient (u n)) (ENNReal.ofReal p) := fun n => by
    rw [hgrad n]
    exact memLp_mollifyWith_normed hp hg (φ n)
  have hu_lim : Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p)) atTop (𝓝 0) :=
    tendsto_eLpNorm_mollifyWith_sub hφ hp hf
  have hG_lim : Tendsto (fun n => eLpNorm (gradient (u n) - g) (ENNReal.ofReal p)) atTop
      (𝓝 0) := by
    simp only [hgrad]
    exact tendsto_eLpNorm_mollifyWith_sub hφ hp hg
  have hnum : Tendsto (fun n => ∫ x, F (gradient (u n) x) ^ p) atTop
      (𝓝 (∫ x, F (g x) ^ p)) :=
    tendsto_integral_comp_of_tendsto_eLpNorm hp.le (hF.rpow_const fun _ => Or.inr hp0.le)
      (norm_rpow_le_of_le_mul_norm hF0 hFC hp0) hG_memLp hg hG_lim
  have hden : Tendsto (fun n => ∫ x, |u n x| ^ p) atTop (𝓝 (∫ x, |f x| ^ p)) :=
    tendsto_integral_comp_of_tendsto_eLpNorm (C := 1) hp.le
      (continuous_abs.rpow_const fun _ => Or.inr hp0.le)
      (fun t => le_of_eq (by simp [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) p)]))
      hu_memLp hf hu_lim
  have hden_pos := integral_abs_rpow_pos hp0 hf hf0
  have hray : Tendsto (fun n => rayleighGen p F (u n)) atTop
      (𝓝 ((∫ x, F (g x) ^ p) / ∫ x, |f x| ^ p)) :=
    hnum.div hden hden_pos.ne'
  have hev_ne : ∀ᶠ n in atTop, u n ≠ 0 := by
    filter_upwards [hden.eventually (lt_mem_nhds hden_pos)] with n hn h0
    rw [h0] at hn
    simp [Real.zero_rpow hp0.ne'] at hn
  have hev_supp : ∀ᶠ n in atTop, (φ n).rOut < δ := hφ.eventually (gt_mem_nhds hδ)
  refine ge_of_tendsto hray ?_
  filter_upwards [hev_ne, hev_supp] with n hne hn
  have hsupp : Function.support (u n) ⊆ Metric.cthickening δ L := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := support_mollifyWith_subset _ _ hx
    rw [ContDiffBump.support_normed_eq] at ha
    have ha' : ‖a‖ < (φ n).rOut := by simpa using ha
    have hbL : b ∈ L := by
      by_contra h
      exact hb (hfL b h)
    refine Metric.mem_cthickening_of_dist_le _ b δ L hbL ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    linarith
  have hcpt : IsCompact (Metric.cthickening δ L) := hL.cthickening
  exact lambdaGen_le_rayleighGen hF0 p
    ⟨contDiff_mollifyWith (φ n).contDiff_normed (φ n).hasCompactSupport_normed
        hfg.locallyIntegrable,
      HasCompactSupport.of_support_subset_isCompact hcpt hsupp,
      (closure_minimal hsupp Metric.isClosed_cthickening).trans hLδ, hne⟩

/-! ### Contraction and the density bridge -/

/-- `λ_{p,F}(K) ≤` the Sobolev Rayleigh quotient of any nonzero `f ∈ W₀^{1,p}(K)`, for a bounded
open convex `K` and a continuous integrand `0 ≤ F ≤ C ‖·‖` (contract by `r < 1` towards an
interior point, mollify, and let `r ↑ 1`). -/
theorem lambdaGen_le_sobolevRayleigh (hp : 1 < p) {F : Euc d → ℝ} (hF : Continuous F)
    (hF0 : ∀ ξ, 0 ≤ F ξ) {C : ℝ} (hFC : ∀ ξ, F ξ ≤ C * ‖ξ‖) {K : Set (Euc d)}
    (hK : IsGoodConvex K) {f : Euc d → ℝ} (hf : MemW0 p K f) (hf0 : ¬ f =ᵐ[volume] 0) :
    lambdaGen p F K ≤ sobolevRayleigh p F f := by
  have hp0 : 0 < p := by linarith
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  obtain ⟨x₀, hx₀⟩ := hK.nonempty
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hK.isOpen x₀ hx₀
  set g := weakGrad f with hg_def
  have hfg : HasWeakGradient f g := hf.hasWeakGradient
  have hgp : MemLp g (ENNReal.ofReal p) := hf.memLp_weakGrad
  -- the representative vanishing everywhere outside `K`
  set f' := K.indicator f with hf'_def
  have hff' : f =ᵐ[volume] f' := by
    filter_upwards [hf.ae_eq_zero] with x hx
    by_cases hxK : x ∈ K
    · rw [hf'_def, Set.indicator_of_mem hxK]
    · rw [hf'_def, Set.indicator_of_notMem hxK, hx hxK]
  have hf'g : HasWeakGradient f' g := hfg.congr_left hff'
  have hf'p : MemLp f' (ENNReal.ofReal p) := hf.memLp.ae_eq hff'
  have hf'K : ∀ x, x ∉ K → f' x = 0 := fun x hx => Set.indicator_of_notMem hx f
  have hf'0 : ¬ f' =ᵐ[volume] 0 := fun h => hf0 (hff'.trans h)
  have hden_eq : ∫ x, |f' x| ^ p = ∫ x, |f x| ^ p :=
    integral_congr_ae (hff'.mono fun x hx => by simp only [hx])
  -- for each contraction ratio `r ∈ (0, 1)`
  have hstep : ∀ r : ℝ, 0 < r → r < 1 →
      lambdaGen p F K ≤ (∫ x, F (r⁻¹ • g x) ^ p) / ∫ x, |f x| ^ p := by
    intro r hr0 hr1
    have hL : IsCompact ((fun y => x₀ + r • (y - x₀)) '' closure K) :=
      hK.isBounded.isCompact_closure.image
        (continuous_const.add ((continuous_id.sub continuous_const).const_smul r))
    have hLK : (fun y => x₀ + r • (y - x₀)) '' closure K ⊆ K := fun y hy =>
      dilate_closure_add_ball_subset hK.convex hK.isOpen hball hr0.le hr1
        (mul_pos (by linarith) hδ) ⟨y, hy, 0, Metric.mem_closedBall_self le_rfl, add_zero y⟩
    have hfrg := hf'g.comp_dilate hp.le hf'p hgp x₀ hr0
    have hfrp := memLp_comp_dilate hp0 hf'p x₀ hr0
    have hgrp : MemLp (fun x => r⁻¹ • g (x₀ + r⁻¹ • (x - x₀))) (ENNReal.ofReal p) :=
      (memLp_comp_dilate hp0 hgp x₀ hr0).const_smul r⁻¹
    have hfrL : ∀ x, x ∉ (fun y => x₀ + r • (y - x₀)) '' closure K →
        f' (x₀ + r⁻¹ • (x - x₀)) = 0 := by
      intro x hx
      refine hf'K _ fun hmem => hx ⟨x₀ + r⁻¹ • (x - x₀), subset_closure hmem, ?_⟩
      show x₀ + r • (x₀ + r⁻¹ • (x - x₀) - x₀) = x
      rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_sub_cancel]
    have hfr0 : ¬ (fun x => f' (x₀ + r⁻¹ • (x - x₀))) =ᵐ[volume] 0 := by
      intro h
      have h1 : ENNReal.ofReal (r ^ d) ^ (1 / p) * eLpNorm f' (ENNReal.ofReal p) = 0 := by
        rw [← eLpNorm_comp_dilate f' x₀ hr0 hp0]
        exact (eLpNorm_eq_zero_iff hfrp.1 hp').2 h
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (pow_pos hr0 d))
          ENNReal.ofReal_ne_top).ne' h2
      · exact hf'0 ((eLpNorm_eq_zero_iff hf'p.1 hp').1 h2)
    have key := lambdaGen_le_div_of_isCompact hp hF hF0 hFC hK.isOpen hL hLK hfrg hfrp hgrp
      hfrL hfr0
    have hnum : ∫ x, F (r⁻¹ • g (x₀ + r⁻¹ • (x - x₀))) ^ p = r ^ d * ∫ x, F (r⁻¹ • g x) ^ p :=
      (integral_comp_dilate (fun y => F (r⁻¹ • g y) ^ p) x₀ hr0).trans (smul_eq_mul _ _)
    have hden : ∫ x, |f' (x₀ + r⁻¹ • (x - x₀))| ^ p = r ^ d * ∫ x, |f x| ^ p := by
      rw [← hden_eq]
      exact (integral_comp_dilate (fun y => |f' y| ^ p) x₀ hr0).trans (smul_eq_mul _ _)
    refine key.trans (le_of_eq ?_)
    show (∫ x, F (r⁻¹ • g (x₀ + r⁻¹ • (x - x₀))) ^ p) /
      (∫ x, |f' (x₀ + r⁻¹ • (x - x₀))| ^ p) = _
    rw [hnum, hden, mul_div_mul_left _ _ (pow_pos hr0 d).ne']
  -- let the contraction ratio tend to `1`
  set r : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 1) / 2 with hr_def
  have hk1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k =>
    (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hr0 : ∀ k, 0 < r k := fun k => by
    have := hk1 k
    simp only [hr_def]
    linarith
  have hr1 : ∀ k, r k < 1 := fun k => by
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    simp only [hr_def]
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 2)
    simpa [hr_def] using this
  have hlim : Tendsto (fun k => ∫ x, F ((r k)⁻¹ • g x) ^ p) atTop (𝓝 (∫ x, F (g x) ^ p)) := by
    have hconv : Tendsto (fun k => eLpNorm ((r k)⁻¹ • g - g) (ENNReal.ofReal p)) atTop
        (𝓝 0) := by
      have e : ∀ k, (r k)⁻¹ • g - g = ((r k)⁻¹ - 1) • g := fun k => by rw [sub_smul, one_smul]
      simp_rw [e, eLpNorm_const_smul]
      have h1 : Tendsto (fun k => (r k)⁻¹ - 1) atTop (𝓝 0) := by
        simpa using (hrlim.inv₀ one_ne_zero).sub_const 1
      have h2 : Tendsto (fun k => ‖(r k)⁻¹ - 1‖ₑ) atTop (𝓝 0) := by
        simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto (0 : ℝ)).comp h1
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const h2 (Or.inr hgp.eLpNorm_ne_top)
    exact tendsto_integral_comp_of_tendsto_eLpNorm (g := fun k => (r k)⁻¹ • g) hp.le
      (hF.rpow_const fun _ => Or.inr hp0.le) (norm_rpow_le_of_le_mul_norm hF0 hFC hp0)
      (fun k => hgp.const_smul _) hgp hconv
  show lambdaGen p F K ≤ (∫ x, F (g x) ^ p) / ∫ x, |f x| ^ p
  exact ge_of_tendsto' (hlim.div_const (∫ x, |f x| ^ p)) fun k => hstep (r k) (hr0 k) (hr1 k)

/-- **Density of `C_c^∞(K)` in `W₀^{1,p}(K)` at the level of the eigenvalue** (paper (3.7): the
eigenvalue over `W_0^{1,p}(K)` equals the one over smooth test functions; the reverse inequality
is `lambdaSob_le_lambdaGen`), for a bounded open convex `K` and a continuous integrand
`0 ≤ F ≤ C ‖·‖`.

The growth hypothesis `hFC` is necessary: for a continuous `F ≥ ‖·‖` of super-polynomial growth
some `f ∈ W₀^{1,p}(K)` has `F(∇f)^p ∉ L¹`, so its Bochner-integral Rayleigh quotient is `0` and
`lambdaSob = 0 < lambdaGen`. -/
theorem lambdaGen_le_lambdaSob (hp : 1 < p) {F : Euc d → ℝ} (hF : Continuous F)
    (hF0 : ∀ ξ, 0 ≤ F ξ) {C : ℝ} (hFC : ∀ ξ, F ξ ≤ C * ‖ξ‖) {K : Set (Euc d)}
    (hK : IsGoodConvex K) :
    lambdaGen p F K ≤ lambdaSob p F K := by
  have := hK.nonempty_testFn
  have := nonempty_memW0_of_testFn (K := K) p
  exact le_ciInf fun f => lambdaGen_le_sobolevRayleigh hp hF hF0 hFC hK f.2.1 f.2.2

/-- The smooth and Sobolev eigenvalues agree (paper (3.7)). -/
theorem lambdaSob_eq_lambdaGen (hp : 1 < p) {F : Euc d → ℝ} (hF : Continuous F)
    (hF0 : ∀ ξ, 0 ≤ F ξ) {C : ℝ} (hFC : ∀ ξ, F ξ ≤ C * ‖ξ‖) {K : Set (Euc d)}
    (hK : IsGoodConvex K) :
    lambdaSob p F K = lambdaGen p F K := by
  have := hK.nonempty_testFn
  exact le_antisymm (lambdaSob_le_lambdaGen hF0) (lambdaGen_le_lambdaSob hp hF hF0 hFC hK)

/-! ### Upgrading a weak equation from `C_c^∞(Ω)` to `W₀^{1,p}(Ω)` -/

section TestUpgrade

variable {Ω : Set (Euc d)}

/-- **Hölder for a pointwise dominated scalar pairing**: if `‖b x‖ ≤ ‖φ x‖ ‖h x‖` pointwise then
`‖∫ b‖ ≤ ‖φ‖_{L^{p'}} ‖h‖_{L^p}`, where `p' = Real.conjExponent p`. -/
theorem enorm_integral_le_of_enorm_le_mul {H H' : Type*} [NormedAddCommGroup H]
    [NormedAddCommGroup H'] (hp : 1 < p) {b : Euc d → ℝ} {φ : Euc d → H'} {h : Euc d → H}
    (hφ : AEStronglyMeasurable φ volume) (hh : AEStronglyMeasurable h volume)
    (hb : ∀ x, ‖b x‖ₑ ≤ ‖φ x‖ₑ * ‖h x‖ₑ) :
    ‖∫ x, b x‖ₑ ≤
      eLpNorm φ (ENNReal.ofReal (Real.conjExponent p)) * eLpNorm h (ENNReal.ofReal p) := by
  -- Mirrors the proof of `enorm_integral_mul_le` (`Sobolev/Defs.lean`), which is known to
  -- elaborate: a `.trans` chain with the goal's orientation fixed FIRST by `rw`.  Stating this
  -- as a `calc` left metavariables that timed out at `whnf`, then at `isDefEq`
  -- (cluster jobs 46577602, 46578117).
  have key : ∫⁻ x, ‖b x‖ₑ
      ≤ eLpNorm h (ENNReal.ofReal p) * eLpNorm φ (ENNReal.ofReal (Real.conjExponent p)) := by
    refine (lintegral_mono fun x => ?_).trans (lintegral_enorm_mul_enorm_le hp hh hφ)
    have hx : ‖b x‖ₑ ≤ ‖φ x‖ₑ * ‖h x‖ₑ := hb x
    rwa [mul_comm (‖h x‖ₑ) (‖φ x‖ₑ)]
  -- `eLpNorm` takes the measure explicitly here: left implicit it stays a metavariable and the
  -- `rw` pattern does not match the goal's `volume`.
  rw [mul_comm (eLpNorm φ (ENNReal.ofReal (Real.conjExponent p)) volume)
    (eLpNorm h (ENNReal.ofReal p) volume)]
  exact (enorm_integral_le_lintegral_enorm _).trans key

/-- **Hölder integrability**: a scalar function pointwise dominated by `‖φ‖ ‖h‖` with
`φ ∈ L^{p'}` and `h ∈ L^p` is integrable. -/
theorem integrable_of_enorm_le_enorm_mul {H H' : Type*} [NormedAddCommGroup H]
    [NormedAddCommGroup H'] (hp : 1 < p) {b : Euc d → ℝ} {φ : Euc d → H'} {h : Euc d → H}
    (hbm : AEStronglyMeasurable b volume)
    (hφ : MemLp φ (ENNReal.ofReal (Real.conjExponent p))) (hh : MemLp h (ENNReal.ofReal p))
    (hb : ∀ x, ‖b x‖ₑ ≤ ‖φ x‖ₑ * ‖h x‖ₑ) :
    Integrable b volume := by
  refine ⟨hbm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hh.2 hφ.2)
  exact (lintegral_mono fun x => (hb x).trans_eq (mul_comm _ _)).trans
    (lintegral_enorm_mul_enorm_le hp hh.1 hφ.1)

/-- `⟪Φ, H⟫` is integrable when `Φ ∈ L^{p'}` and `H ∈ L^p` (Cauchy–Schwarz and Hölder). -/
theorem integrable_inner_of_memLp (hp : 1 < p) {Φ H : Euc d → Euc d}
    (hΦ : MemLp Φ (ENNReal.ofReal (Real.conjExponent p))) (hH : MemLp H (ENNReal.ofReal p)) :
    Integrable (fun x => inner ℝ (Φ x) (H x)) volume :=
  integrable_of_enorm_le_enorm_mul hp (AEStronglyMeasurable.inner (𝕜 := ℝ) hΦ.1 hH.1) hΦ hH
    fun x => enorm_real_inner_le _ _

/-- `g * v` is integrable when `g ∈ L^{p'}` and `v ∈ L^p` (Hölder). -/
theorem integrable_mul_of_memLp (hp : 1 < p) {g v : Euc d → ℝ}
    (hg : MemLp g (ENNReal.ofReal (Real.conjExponent p))) (hv : MemLp v (ENNReal.ofReal p)) :
    Integrable (fun x => g x * v x) volume :=
  integrable_of_enorm_le_enorm_mul hp (hg.1.mul hv.1) hg hv fun x => le_of_eq (enorm_mul _ _)

/-- **The `L^{p'}` pairing is continuous along `L^p`-convergent sequences** (vector form):
if `Φ ∈ L^{p'}` and `G n → G₀` in `L^p`, then `∫ ⟪Φ, G n⟫ → ∫ ⟪Φ, G₀⟫`. -/
theorem tendsto_integral_inner_of_tendsto_eLpNorm (hp : 1 < p) {Φ : Euc d → Euc d}
    (hΦ : MemLp Φ (ENNReal.ofReal (Real.conjExponent p))) {G : ℕ → Euc d → Euc d}
    {G₀ : Euc d → Euc d} (hG : ∀ n, MemLp (G n) (ENNReal.ofReal p))
    (hG₀ : MemLp G₀ (ENNReal.ofReal p))
    (hlim : Tendsto (fun n => eLpNorm (G n - G₀) (ENNReal.ofReal p)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, inner ℝ (Φ x) (G n x)) atTop
      (𝓝 (∫ x, inner ℝ (Φ x) (G₀ x))) := by
  refine tendsto_of_enorm_sub_le (E := fun n =>
    eLpNorm Φ (ENNReal.ofReal (Real.conjExponent p)) * eLpNorm (G n - G₀) (ENNReal.ofReal p))
    (by simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hΦ.eLpNorm_ne_top)) fun n => ?_
  rw [← integral_sub (integrable_inner_of_memLp hp hΦ (hG n))
    (integrable_inner_of_memLp hp hΦ hG₀)]
  have h := enorm_integral_le_of_enorm_le_mul hp (b := fun x => inner ℝ (Φ x) ((G n - G₀) x))
    (φ := Φ) (h := G n - G₀) hΦ.1 ((hG n).1.sub hG₀.1) fun x => enorm_real_inner_le _ _
  simpa only [Pi.sub_apply, inner_sub_right] using h

/-- **The `L^{p'}` pairing is continuous along `L^p`-convergent sequences** (scalar form):
if `g ∈ L^{p'}` and `v n → v₀` in `L^p`, then `∫ g v n → ∫ g v₀`. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm (hp : 1 < p) {g : Euc d → ℝ}
    (hg : MemLp g (ENNReal.ofReal (Real.conjExponent p))) {v : ℕ → Euc d → ℝ} {v₀ : Euc d → ℝ}
    (hv : ∀ n, MemLp (v n) (ENNReal.ofReal p)) (hv₀ : MemLp v₀ (ENNReal.ofReal p))
    (hlim : Tendsto (fun n => eLpNorm (v n - v₀) (ENNReal.ofReal p)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, g x * v n x) atTop (𝓝 (∫ x, g x * v₀ x)) := by
  refine tendsto_of_enorm_sub_le (E := fun n =>
    eLpNorm g (ENNReal.ofReal (Real.conjExponent p)) * eLpNorm (v n - v₀) (ENNReal.ofReal p))
    (by simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hg.eLpNorm_ne_top)) fun n => ?_
  rw [← integral_sub (integrable_mul_of_memLp hp hg (hv n))
    (integrable_mul_of_memLp hp hg hv₀)]
  have h := enorm_integral_le_of_enorm_le_mul hp (b := fun x => g x * (v n - v₀) x)
    (φ := g) (h := v n - v₀) hg.1 ((hv n).1.sub hv₀.1) fun x => le_of_eq (enorm_mul _ _)
  simpa only [Pi.sub_apply, mul_sub] using h

/-- **`C_c^∞(Ω)` approximates `W^{1,p}` functions supported in a compact subset of `Ω`**: if `f`
has weak gradient `G`, both in `L^p`, and `f` vanishes outside a compact `L ⊆ Ω` with `Ω` open,
then there are `u n ∈ C_c^∞` with `tsupport (u n) ⊆ Ω`, `u n → f` and `∇(u n) → G` in `L^p`.

Proof: mollify with the standard bumps `mollifierBump`, shifted so that every radius is smaller
than a `δ` with `cthickening δ L ⊆ Ω` (`IsCompact.exists_cthickening_subset_open`); then
`support (ρ ⋆ f) ⊆ cthickening δ L` (`support_mollifyWith_subset`), `∇(ρ ⋆ f) = ρ ⋆ G`
(`gradient_mollifyWith`), and both convergences are `tendsto_eLpNorm_mollifyWith_sub`. -/
theorem exists_contDiff_tendsto_eLpNorm_of_hasWeakGradient (hp : 1 < p) (hΩ : IsOpen Ω)
    {L : Set (Euc d)} (hL : IsCompact L) (hLΩ : L ⊆ Ω) {f : Euc d → ℝ} {G : Euc d → Euc d}
    (hfG : HasWeakGradient f G) (hf : MemLp f (ENNReal.ofReal p))
    (hG : MemLp G (ENNReal.ofReal p)) (hfL : ∀ x, x ∉ L → f x = 0) :
    ∃ u : ℕ → Euc d → ℝ, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, tsupport (u n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (gradient (u n) - G) (ENNReal.ofReal p)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hLδ⟩ := hL.exists_cthickening_subset_open hΩ hLΩ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  set φ : ℕ → ContDiffBump (0 : Euc d) := fun n => mollifierBump (max n N) with hφ_def
  have hrOut : ∀ n, (φ n).rOut < δ := by
    intro n
    have hle : ((N : ℝ) + 1) ≤ ((max n N : ℕ) : ℝ) + 1 := by
      have h1 : (N : ℝ) ≤ ((max n N : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
      linarith
    have h2 : 1 / (((max n N : ℕ) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hle
    simp only [hφ_def]
    show 1 / (((max n N : ℕ) : ℝ) + 1) < δ
    exact lt_of_le_of_lt h2 hN
  have hφlim : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [hφ_def]
    have hmax : max n N = n := by omega
    show (1 : ℝ) / ((n : ℝ) + 1) = 1 / (((max n N : ℕ) : ℝ) + 1)
    rw [hmax]
  set u : ℕ → Euc d → ℝ := fun n => mollifyWith ((φ n).normed volume) f with hu_def
  have hsupp : ∀ n, Function.support (u n) ⊆ Metric.cthickening δ L := by
    intro n x hx
    simp only [hu_def] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := support_mollifyWith_subset ((φ n).normed volume) f hx
    rw [ContDiffBump.support_normed_eq] at ha
    have ha' : ‖a‖ < (φ n).rOut := by simpa using ha
    have hbL : b ∈ L := by
      by_contra h
      exact hb (hfL b h)
    refine Metric.mem_cthickening_of_dist_le _ b δ L hbL ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    linarith [hrOut n]
  have hcpt : IsCompact (Metric.cthickening δ L) := hL.cthickening
  have hgrad : ∀ n, gradient (u n) = mollifyWith ((φ n).normed volume) G := fun n =>
    gradient_mollifyWith hfG (φ n).contDiff_normed (φ n).hasCompactSupport_normed
  refine ⟨u, fun n => contDiff_mollifyWith (φ n).contDiff_normed
      (φ n).hasCompactSupport_normed hfG.locallyIntegrable,
    fun n => HasCompactSupport.of_support_subset_isCompact hcpt (hsupp n),
    fun n => (closure_minimal (hsupp n) Metric.isClosed_cthickening).trans hLδ, ?_, ?_⟩
  · simp only [hu_def]
    exact tendsto_eLpNorm_mollifyWith_sub hφlim hp hf
  · simp only [hgrad]
    exact tendsto_eLpNorm_mollifyWith_sub hφlim hp hG

/-- **`C_c^∞(Ω)` is dense in `W₀^{1,p}(K)` for compact `K ⊆ Ω`**: every `f ∈ W₀^{1,p}(K)` is the
`L^p`-limit, together with its weak gradient, of smooth functions compactly supported in `Ω`.

Note that `MemW0` is *not* defined as a closure (see `Komlos.Literature.MemW0`), so this is a
genuine theorem; it is proved by mollification of the representative `K.indicator f`. -/
theorem MemW0.exists_contDiff_tendsto_eLpNorm (hp : 1 < p) (hΩ : IsOpen Ω) {K : Set (Euc d)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {f : Euc d → ℝ} (hf : MemW0 p K f) :
    ∃ u : ℕ → Euc d → ℝ, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, tsupport (u n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (gradient (u n) - weakGrad f) (ENNReal.ofReal p)) atTop
        (𝓝 0) := by
  set f' := K.indicator f with hf'_def
  have hff' : f =ᵐ[volume] f' := by
    filter_upwards [hf.ae_eq_zero] with x hx
    by_cases hxK : x ∈ K
    · rw [hf'_def, Set.indicator_of_mem hxK]
    · rw [hf'_def, Set.indicator_of_notMem hxK, hx hxK]
  have hf'K : ∀ x, x ∉ K → f' x = 0 := fun x hx => Set.indicator_of_notMem hx f
  obtain ⟨u, h1, h2, h3, h4, h5⟩ :=
    exists_contDiff_tendsto_eLpNorm_of_hasWeakGradient hp hΩ hK hKΩ
      (hf.hasWeakGradient.congr_left hff') (hf.memLp.ae_eq hff') hf.memLp_weakGrad hf'K
  refine ⟨u, h1, h2, h3, h4.congr fun n => eLpNorm_congr_ae ?_, h5⟩
  filter_upwards [hff'] with x hx
  simp only [Pi.sub_apply, hx]

/-- **Test-function upgrade for `W₀^{1,p}`**: a weak equation `∫ ⟪Φ, ∇χ⟫ = ∫ g χ` that holds for
every `χ ∈ C_c^∞(Ω)` holds for every `ψ ∈ W₀^{1,p}(K)` with `K` a compact subset of the open set
`Ω`, provided `Φ` and `g` lie in the conjugate space `L^{p'}`, `p' = Real.conjExponent p`.

This is the `C_c^∞`-density input needed by `Komlos.Literature.exists_frozen_replacement_data`
(`PLaplacian/SchauderHarmonic.lean`), whose hypothesis tests `w`'s equation against
`C_c^∞(B(x₀, 2R))` while its conclusion tests it against a `ψ ∈ W₀^{1,2}`.  Since `MemW0` is
defined without any closure operation, the density is a theorem, not a definition unfolding:
it is `MemW0.exists_contDiff_tendsto_eLpNorm`, and the limit is taken with Hölder against the
fixed `Φ ∈ L^{p'}`, `g ∈ L^{p'}` (`tendsto_integral_inner_of_tendsto_eLpNorm`,
`tendsto_integral_mul_of_tendsto_eLpNorm`). -/
theorem integral_inner_weakGrad_eq_of_memW0 (hp : 1 < p) (hΩ : IsOpen Ω) {Φ : Euc d → Euc d}
    (hΦ : MemLp Φ (ENNReal.ofReal (Real.conjExponent p))) {g : Euc d → ℝ}
    (hg : MemLp g (ENNReal.ofReal (Real.conjExponent p)))
    (hweak : ∀ χ : Euc d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ x, inner ℝ (Φ x) (gradient χ x) = ∫ x, g x * χ x)
    {K : Set (Euc d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) {ψ : Euc d → ℝ} (hψ : MemW0 p K ψ) :
    ∫ x, inner ℝ (Φ x) (weakGrad ψ x) = ∫ x, g x * ψ x := by
  obtain ⟨u, hcd, hcs, hts, hu, hgr⟩ := hψ.exists_contDiff_tendsto_eLpNorm hp hΩ hK hKΩ
  have hu1 : ∀ n, ContDiff ℝ 1 (u n) := fun n => (hcd n).of_le (by simp)
  have hup : ∀ n, MemLp (u n) (ENNReal.ofReal p) := fun n =>
    (hcd n).continuous.memLp_of_hasCompactSupport (hcs n)
  have hgp : ∀ n, MemLp (gradient (u n)) (ENNReal.ofReal p) := fun n =>
    (continuous_gradient (hu1 n)).memLp_of_hasCompactSupport (hasCompactSupport_gradient (hcs n))
  have hA : Tendsto (fun n => ∫ x, inner ℝ (Φ x) (gradient (u n) x)) atTop
      (𝓝 (∫ x, inner ℝ (Φ x) (weakGrad ψ x))) :=
    tendsto_integral_inner_of_tendsto_eLpNorm hp hΦ hgp hψ.memLp_weakGrad hgr
  have hB : Tendsto (fun n => ∫ x, g x * u n x) atTop (𝓝 (∫ x, g x * ψ x)) :=
    tendsto_integral_mul_of_tendsto_eLpNorm hp hg hup hψ.memLp hu
  exact tendsto_nhds_unique (hA.congr fun n => hweak (u n) (hcd n) (hcs n) (hts n)) hB

/-- **Test-function upgrade, localized integrability**: only the restrictions of `Φ` and `g` to
`Ω` are required to be `L^{p'}`; off `Ω` they are arbitrary.  The price is the extra hypothesis
`hψK`, that the weak gradient of `ψ` vanishes a.e. outside `K` — which is exactly what makes the
conclusion insensitive to the values of `Φ` off `Ω`, and which a consumer producing `ψ` with a
prescribed `weakGrad ψ =ᵐ K.indicator _` has for free. -/
theorem integral_inner_weakGrad_eq_of_memW0_indicator (hp : 1 < p) (hΩ : IsOpen Ω)
    {Φ : Euc d → Euc d} (hΦ : MemLp (Ω.indicator Φ) (ENNReal.ofReal (Real.conjExponent p)))
    {g : Euc d → ℝ} (hg : MemLp (Ω.indicator g) (ENNReal.ofReal (Real.conjExponent p)))
    (hweak : ∀ χ : Euc d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ x, inner ℝ (Φ x) (gradient χ x) = ∫ x, g x * χ x)
    {K : Set (Euc d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) {ψ : Euc d → ℝ} (hψ : MemW0 p K ψ)
    (hψK : ∀ᵐ x, x ∉ K → weakGrad ψ x = 0) :
    ∫ x, inner ℝ (Φ x) (weakGrad ψ x) = ∫ x, g x * ψ x := by
  have e1 : (fun x => inner ℝ (Ω.indicator Φ x) (weakGrad ψ x)) =ᵐ[volume]
      fun x => inner ℝ (Φ x) (weakGrad ψ x) := by
    filter_upwards [hψK] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ]
    · rw [hx (fun hxK => hxΩ (hKΩ hxK)), inner_zero_right, inner_zero_right]
  have e2 : (fun x => Ω.indicator g x * ψ x) =ᵐ[volume] fun x => g x * ψ x := by
    filter_upwards [hψ.ae_eq_zero] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ]
    · rw [hx (fun hxK => hxΩ (hKΩ hxK)), mul_zero, mul_zero]
  have hweak' : ∀ χ : Euc d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ x, inner ℝ (Ω.indicator Φ x) (gradient χ x) = ∫ x, Ω.indicator g x * χ x := by
    intro χ hχ hχs hχΩ
    have f1 : (fun x => inner ℝ (Ω.indicator Φ x) (gradient χ x)) =ᵐ[volume]
        fun x => inner ℝ (Φ x) (gradient χ x) := by
      refine Eventually.of_forall fun x => ?_
      -- beta-reduce first: `rw` cannot see through `(fun x => _) x`
      show inner ℝ (Ω.indicator Φ x) (gradient χ x) = inner ℝ (Φ x) (gradient χ x)
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]
      · rw [gradient_eq_zero_of_notMem_tsupport (fun h => hxΩ (hχΩ h)), inner_zero_right,
          inner_zero_right]
    have f2 : (fun x => Ω.indicator g x * χ x) =ᵐ[volume] fun x => g x * χ x := by
      refine Eventually.of_forall fun x => ?_
      -- beta-reduce first: `rw` cannot see through `(fun x => _) x`
      show Ω.indicator g x * χ x = g x * χ x
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hxΩ (hχΩ h)), mul_zero, mul_zero]
    rw [integral_congr_ae f1, integral_congr_ae f2]
    exact hweak χ hχ hχs hχΩ
  have key := integral_inner_weakGrad_eq_of_memW0 hp hΩ hΦ hg hweak' hK hKΩ hψ
  rwa [integral_congr_ae e1, integral_congr_ae e2] at key

/-- The `p = 2` case of `integral_inner_weakGrad_eq_of_memW0_indicator`, the shape needed by
`Komlos.Literature.exists_frozen_replacement_data`. -/
theorem integral_inner_weakGrad_eq_of_memW0_two (hΩ : IsOpen Ω) {Φ : Euc d → Euc d}
    (hΦ : MemLp (Ω.indicator Φ) 2) {g : Euc d → ℝ} (hg : MemLp (Ω.indicator g) 2)
    (hweak : ∀ χ : Euc d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ x, inner ℝ (Φ x) (gradient χ x) = ∫ x, g x * χ x)
    {K : Set (Euc d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) {ψ : Euc d → ℝ} (hψ : MemW0 2 K ψ)
    (hψK : ∀ᵐ x, x ∉ K → weakGrad ψ x = 0) :
    ∫ x, inner ℝ (Φ x) (weakGrad ψ x) = ∫ x, g x * ψ x := by
  have he : ENNReal.ofReal (Real.conjExponent (2 : ℝ)) = 2 := by
    rw [Real.HolderConjugate.conjExponent_eq Real.HolderConjugate.two_two]
    simp
  refine integral_inner_weakGrad_eq_of_memW0_indicator one_lt_two hΩ ?_ ?_ hweak hK hKΩ hψ hψK
  · rwa [he]
  · rwa [he]

end TestUpgrade

end Komlos.Literature
