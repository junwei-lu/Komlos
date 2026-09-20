import Komlos.Literature.WangXia.InfConv
import Komlos.Literature.WangXia.EigenvalueConvexAssemblyAux

/-!
# The Hessian comparison for the perturbed infimal convolution (paper Appendix A)

This file provides the second-order material of paper Appendix A, paragraph *The differential
inequality away from the critical set*, used to close `weak_ineq_U_off_critical`:

* second-order necessary conditions: `nonneg_of_isLocalMin_of_hasDerivAt_deriv` (one variable),
  `inner_fderiv_gradient_nonneg_of_isLocalMin` (the Hessian at a local minimum is positive
  semidefinite), `inner_fderiv_gradient_nonneg_of_convexOn` (the Hessian of a convex function is
  positive semidefinite), `inner_fderiv_gradient_comm` (symmetry of the Hessian);
* `sum_inner_single_apply_le`: the trace inequality `tr(A H) ≤ tr(A H')` for a symmetric positive
  semidefinite `A` and `H ≤ H'` in the quadratic-form order (paper: "taking its trace against
  `A(q_η) > 0`");
* divergence calculus: `divergence_congr`, `divergence_comp`, `divergence_smul`;
* the flux: `flux_smul_of_neg` (homogeneity), `divergence_flux_gradient_exp_neg` (paper:
  "`div a(∇e^{-v}) = e^{-(p-1)v}((p-1)F(∇v)^p - div a(∇v))`"), `inner_fderiv_flux_comm`,
  `inner_fderiv_flux_nonneg` (`A(q) = Da(q)` is symmetric positive semidefinite);
* `InfConvData.isMinimizer_of_gradient_eq` (a stationary feasible pair is a minimizer),
  `InfConvData.IsMinimizer.contDiffAt_gradient_w` (`w_η ∈ C²` near a point whose minimizing pair
  has `C¹` gradients, by the implicit function theorem), and the Hessian comparison
  `InfConvData.IsMinimizer.inner_fderiv_gradient_w_le`
  (`D²w_η ≤ (1-t)(D²v₀(x₀) + 2ηI) + t(D²v₁(x₁) + 2ηI)`, from the second-order upper bound
  obtained by shifting both components of the minimizing pair);
* the log-eigenfunction equation `div a(∇v) = λ + (p-1)F(∇v)^p` (paper (A.log-eigenfunction)) is
  `EigenfunctionData.divergence_flux_gradient_neg_log` in `EigenvalueConvexOffCritical`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Gradient calculus helpers -/

theorem HasGradientAt.add' {f g : Euc d → ℝ} {f' g' x : Euc d} (hf : HasGradientAt f f' x)
    (hg : HasGradientAt g g' x) : HasGradientAt (fun y => f y + g y) (f' + g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf hg ⊢
  rw [map_add]
  exact hf.add hg

theorem HasGradientAt.sub' {f g : Euc d → ℝ} {f' g' x : Euc d} (hf : HasGradientAt f f' x)
    (hg : HasGradientAt g g' x) : HasGradientAt (fun y => f y - g y) (f' - g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf hg ⊢
  rw [map_sub]
  exact hf.sub hg

theorem HasGradientAt.const_mul' {f : Euc d → ℝ} {f' x : Euc d} (hf : HasGradientAt f f' x)
    (c : ℝ) : HasGradientAt (fun y => c * f y) (c • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  rw [map_smul]
  exact hf.const_mul c

theorem hasGradientAt_inner_const_sub (c x₀ x : Euc d) :
    HasGradientAt (fun y => ⟪c, y - x₀⟫) c x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : HasFDerivAt (fun y : Euc d => ⟪c, y - x₀⟫) (innerSL ℝ c) x := by
    have := (innerSL ℝ c).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  refine h.congr_fderiv ?_
  ext y
  simp [InnerProductSpace.toDual_apply_apply]

/-- The gradient of `y ↦ exp (-(a v y))`. -/
theorem hasGradientAt_exp_neg_mul {v : Euc d → ℝ} {x g : Euc d} (hv : HasGradientAt v g x)
    (a : ℝ) :
    HasGradientAt (fun y => Real.exp (-(a * v y))) (-(a * Real.exp (-(a * v x))) • g) x := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(a * s))) (-(a * Real.exp (-(a * v x))))
      (v x) := by
    have := ((hasDerivAt_id (v x)).const_mul a).neg.exp
    simpa [mul_comm] using this
  have h := hexp.comp_hasFDerivAt x (hasGradientAt_iff_hasFDerivAt.1 hv)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h.congr_fderiv ?_
  rw [map_smul]

/-! ### Second-order necessary conditions -/

/-- **Second-order necessary condition** (one variable): at a local minimum `x₀` of `f`, if `f` is
differentiable near `x₀` and `deriv f` has derivative `f''` at `x₀`, then `0 ≤ f''`. -/
theorem nonneg_of_isLocalMin_of_hasDerivAt_deriv {f : ℝ → ℝ} {x₀ f'' : ℝ}
    (hmin : IsLocalMin f x₀) (hd : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ f x)
    (hd2 : HasDerivAt (deriv f) f'' x₀) : 0 ≤ f'' := by
  by_contra hlt
  replace hlt : f'' < 0 := not_le.1 hlt
  have h0 : deriv f x₀ = 0 := hmin.deriv_eq_zero
  have hsign : ∀ᶠ x in 𝓝 x₀, SignType.sign (deriv f x) = SignType.sign (x₀ - x) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg (by rw [hd2.deriv]; exact hlt) h0
  have hneg : ∀ᶠ b in 𝓝[>] x₀, deriv f b < 0 :=
    deriv_neg_right_of_sign_deriv (nhdsWithin_le_nhds hsign)
  obtain ⟨u, hu, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hneg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hd.and hmin)
  set δ : ℝ := min (u - x₀) r / 2 with hδ
  have hδpos : 0 < δ := by
    have : 0 < min (u - x₀) r := lt_min (sub_pos.2 (mem_Ioi.1 hu)) hr
    positivity
  have hδu : δ < u - x₀ := by
    have : min (u - x₀) r ≤ u - x₀ := min_le_left _ _
    linarith
  have hδr : δ < r := by
    have : min (u - x₀) r ≤ r := min_le_right _ _
    linarith
  have hmem : ∀ x ∈ Icc x₀ (x₀ + δ), x ∈ Metric.ball x₀ r := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hx.1, hx.2]
  have hanti : StrictAntiOn f (Icc x₀ (x₀ + δ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · exact fun x hx => ((hball (hmem x hx)).1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hIoo ⟨hx.1, by linarith [hx.2]⟩
  have h1 : f (x₀ + δ) < f x₀ :=
    hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have h2 : f x₀ ≤ f (x₀ + δ) := (hball (hmem _ ⟨by linarith, le_rfl⟩)).2
  linarith

/-- **Second-order necessary condition**: at a local minimum `x` of `f : ℝ^d → ℝ`, with `f`
differentiable near `x` and `∇f` differentiable at `x`, the Hessian `D(∇f)(x)` is positive
semidefinite. -/
theorem inner_fderiv_gradient_nonneg_of_isLocalMin {f : Euc d → ℝ} {x : Euc d}
    {H : Euc d →L[ℝ] Euc d} (hmin : IsLocalMin f x) (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hH : HasFDerivAt (gradient f) H x) (ζ : Euc d) : 0 ≤ ⟪H ζ, ζ⟫ := by
  set φ : ℝ → ℝ := fun s => f (x + s • ζ) with hφ
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • ζ) ζ s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const ζ).const_add x
  have hcont : Continuous fun s : ℝ => x + s • ζ := by fun_prop
  have hlim : Tendsto (fun s : ℝ => x + s • ζ) (𝓝 0) (𝓝 x) := by
    simpa using hcont.tendsto 0
  have hφmin : IsLocalMin φ 0 := by
    have hmin' : IsLocalMin f ((fun s : ℝ => x + s • ζ) 0) := by simpa using hmin
    exact hmin'.comp_continuous (g := fun s : ℝ => x + s • ζ) hcont.continuousAt
  have hφd : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt φ ⟪gradient f (x + s • ζ), ζ⟫ s := by
    filter_upwards [hlim.eventually hd] with s hs
    have h1 := (hasGradientAt_iff_hasFDerivAt.1 hs.hasGradientAt).comp_hasDerivAt s (hline s)
    rw [InnerProductSpace.toDual_apply_apply] at h1
    exact h1
  have hderiv : deriv φ =ᶠ[𝓝 (0 : ℝ)] fun s => ⟪gradient f (x + s • ζ), ζ⟫ := by
    filter_upwards [hφd] with s hs
    exact hs.deriv
  have h2 : HasDerivAt (fun s : ℝ => ⟪gradient f (x + s • ζ), ζ⟫) ⟪H ζ, ζ⟫ 0 := by
    have h3 : HasDerivAt (fun s : ℝ => gradient f (x + s • ζ)) (H ζ) 0 :=
      hH.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) (by simp)
    have := h3.inner ℝ (hasDerivAt_const (0 : ℝ) ζ)
    simpa using this
  have hd2 : HasDerivAt (deriv φ) ⟪H ζ, ζ⟫ 0 := h2.congr_of_eventuallyEq hderiv
  exact nonneg_of_isLocalMin_of_hasDerivAt_deriv hφmin
    (hφd.mono fun s hs => hs.differentiableAt) hd2

/-- The Hessian of a convex function (differentiable on an open convex set, with differentiable
gradient at `x`) is positive semidefinite at `x`. -/
theorem inner_fderiv_gradient_nonneg_of_convexOn {Ω : Set (Euc d)} (hΩ : IsOpen Ω)
    {f : Euc d → ℝ} (hf : ConvexOn ℝ Ω f) (hd : DifferentiableOn ℝ f Ω) {x : Euc d} (hx : x ∈ Ω)
    {H : Euc d →L[ℝ] Euc d} (hH : HasFDerivAt (gradient f) H x) (ζ : Euc d) : 0 ≤ ⟪H ζ, ζ⟫ := by
  set g : Euc d → ℝ := fun y => f y - ⟪gradient f x, y - x⟫ with hg
  have hmin : IsLocalMin g x := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    have := convexOn_inner_gradient_le_sub hf hx hy (hd.hasGradientAt (hΩ.mem_nhds hx))
    simp only [hg, sub_self, inner_zero_right, sub_zero]
    linarith
  have hgrad : ∀ y ∈ Ω, HasGradientAt g (gradient f y - gradient f x) y := fun y hy =>
    HasGradientAt.sub' (hd.hasGradientAt (hΩ.mem_nhds hy)) (hasGradientAt_inner_const_sub _ _ _)
  have hdg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (hgrad y hy).differentiableAt
  have hHg : HasFDerivAt (gradient g) H x := by
    have h1 : HasFDerivAt (fun y => gradient f y - gradient f x) H x := hH.sub_const _
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (hgrad y hy).gradient
  exact inner_fderiv_gradient_nonneg_of_isLocalMin hmin hdg hHg ζ

/-- **Symmetry of the Hessian**: if `f` is differentiable near `x` and `∇f` is differentiable at
`x` with derivative `H`, then `H` is symmetric. -/
theorem inner_fderiv_gradient_comm {f : Euc d → ℝ} {x : Euc d} {H : Euc d →L[ℝ] Euc d}
    (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hH : HasFDerivAt (gradient f) H x)
    (ζ ζ' : Euc d) : ⟪H ζ, ζ'⟫ = ⟪ζ, H ζ'⟫ := by
  set T : Euc d →L[ℝ] Euc d →L[ℝ] ℝ :=
    (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := Euc d)).toContinuousLinearMap with hT
  have hTapp : ∀ a b : Euc d, T a b = ⟪a, b⟫ := fun a b =>
    (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := Euc d)).toContinuousLinearMap_apply a b
  have hf' : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y := hd.mono fun y hy => hy.hasFDerivAt
  have hf'' : HasFDerivAt (fderiv ℝ f) (T.comp H) x := by
    have heq : fderiv ℝ f = fun y => T (gradient f y) := by
      funext y
      ext ζ
      rw [hTapp, inner_gradient_left]
    rw [heq]
    exact T.hasFDerivAt.comp x hH
  have := second_derivative_symmetric_of_eventually_of_real hf' hf'' ζ ζ'
  simp only [ContinuousLinearMap.comp_apply, hTapp] at this
  rw [this, real_inner_comm]

/-! ### The trace inequality -/

/-- **Trace monotonicity**: for a symmetric positive semidefinite `A` and `H ≤ H'` in the
quadratic-form order, `tr(A H) ≤ tr(A H')`, where `tr(A H) = ∑ᵢ ⟪eᵢ, A(H eᵢ)⟫`. -/
theorem sum_inner_single_apply_le {A H H' : Euc d →L[ℝ] Euc d}
    (hAs : ∀ ζ ζ', ⟪A ζ, ζ'⟫ = ⟪ζ, A ζ'⟫) (hA : ∀ ζ, 0 ≤ ⟪A ζ, ζ⟫)
    (hle : ∀ ζ, ⟪H ζ, ζ⟫ ≤ ⟪H' ζ, ζ⟫) :
    ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (H (EuclideanSpace.single i (1 : ℝ)))⟫ ≤
      ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (H' (EuclideanSpace.single i (1 : ℝ)))⟫ := by
  set N : Euc d →L[ℝ] Euc d := H' - H with hN
  have hN0 : ∀ ζ, 0 ≤ ⟪N ζ, ζ⟫ := fun ζ => by
    rw [hN, _root_.sub_apply, inner_sub_left]
    linarith [hle ζ]
  have hAsym : (A : Euc d →ₗ[ℝ] Euc d).IsSymmetric := fun ζ ζ' => hAs ζ ζ'
  set b := hAsym.eigenvectorBasis finrank_euclideanSpace_fin with hb
  have key : 0 ≤ ∑ i, ⟪EuclideanSpace.single i (1 : ℝ),
      A (N (EuclideanSpace.single i (1 : ℝ)))⟫ := by
    have h1 : ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (N (EuclideanSpace.single i (1 : ℝ)))⟫ =
        LinearMap.trace ℝ (Euc d) ((A : Euc d →ₗ[ℝ] Euc d) * (N : Euc d →ₗ[ℝ] Euc d)) := by
      rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin d) ℝ)]
      simp [EuclideanSpace.basisFun_apply]
    rw [h1, LinearMap.trace_mul_comm, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_nonneg fun j _ => ?_
    have hev : (A : Euc d →ₗ[ℝ] Euc d) (b j) =
        hAsym.eigenvalues finrank_euclideanSpace_fin j • b j := by
      have := hAsym.apply_eigenvectorBasis finrank_euclideanSpace_fin j
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using this
    have hnorm : ‖b j‖ = 1 := b.orthonormal.1 j
    have hα : 0 ≤ hAsym.eigenvalues finrank_euclideanSpace_fin j := by
      have h := hA (b j)
      rw [← ContinuousLinearMap.coe_coe A, hev, real_inner_smul_left, real_inner_self_eq_norm_sq,
        hnorm] at h
      simpa using h
    rw [Module.End.mul_apply, hev, map_smul, real_inner_smul_right]
    exact mul_nonneg hα (by rw [real_inner_comm]; exact hN0 _)
  have hsplit : ∀ i, ⟪EuclideanSpace.single i (1 : ℝ), A (H' (EuclideanSpace.single i (1 : ℝ)))⟫ =
      ⟪EuclideanSpace.single i (1 : ℝ), A (H (EuclideanSpace.single i (1 : ℝ)))⟫ +
      ⟪EuclideanSpace.single i (1 : ℝ), A (N (EuclideanSpace.single i (1 : ℝ)))⟫ := fun i => by
    rw [hN, _root_.sub_apply, map_sub, inner_sub_right]
    ring
  simp only [hsplit, Finset.sum_add_distrib]
  linarith

/-! ### Divergence calculus -/

/-- The divergence only depends on the germ of the vector field. -/
theorem divergence_congr {W₁ W₂ : Euc d → Euc d} {x : Euc d} (h : W₁ =ᶠ[𝓝 x] W₂) :
    divergence W₁ x = divergence W₂ x := by
  simp only [divergence, h.fderiv_eq]

/-- The divergence of a composition `a ∘ G`, by the chain rule. -/
theorem divergence_comp {a G : Euc d → Euc d} {x : Euc d} {a' G' : Euc d →L[ℝ] Euc d}
    (ha : HasFDerivAt a a' (G x)) (hG : HasFDerivAt G G' x) :
    divergence (fun y => a (G y)) x =
      ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), a' (G' (EuclideanSpace.single i (1 : ℝ)))⟫ := by
  have h : HasFDerivAt (fun y => a (G y)) (a'.comp G') x := ha.comp x hG
  simp only [divergence, h.fderiv, ContinuousLinearMap.comp_apply]

/-- The product rule for the divergence: `div (c W) = ⟪∇c, W⟫ + c div W`. -/
theorem divergence_smul {c : Euc d → ℝ} {W : Euc d → Euc d} {x : Euc d} {g : Euc d}
    {W' : Euc d →L[ℝ] Euc d} (hc : HasGradientAt c g x) (hW : HasFDerivAt W W' x) :
    divergence (fun y => c y • W y) x = ⟪g, W x⟫ + c x * divergence W x := by
  have hc' : HasFDerivAt c (InnerProductSpace.toDual ℝ (Euc d) g) x :=
    hasGradientAt_iff_hasFDerivAt.1 hc
  have h : HasFDerivAt (fun y => c y • W y)
      (c x • W' + (InnerProductSpace.toDual ℝ (Euc d) g).smulRight (W x)) x := hc'.smul hW
  simp only [divergence, h.fderiv, hW.fderiv, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply, inner_add_right,
    inner_smul_right, Finset.sum_add_distrib, InnerProductSpace.toDual_apply_apply]
  rw [Finset.mul_sum, ← (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner g (W x)]
  simp only [EuclideanSpace.basisFun_apply]
  ring

/-! ### The flux: homogeneity, symmetry and positivity of `A = Da` -/

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- `∇F(cξ) = -∇F(ξ)` for `c < 0` and `ξ ≠ 0` (`F` is even and `1`-homogeneous). -/
theorem gradient_smul_of_neg {c : ℝ} (hc : c < 0) {ξ : Euc d} (hξ : ξ ≠ 0) :
    gradient F (c • ξ) = -gradient F ξ := by
  have hcξ : c • ξ ≠ 0 := smul_ne_zero hc.ne hξ
  have h1 : HasFDerivAt F (fderiv ℝ F (c • ξ)) (c • ξ) :=
    ((hF.contDiffAt hcξ).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fun y => F (c • y))
      ((fderiv ℝ F (c • ξ)).comp (c • ContinuousLinearMap.id ℝ (Euc d))) ξ :=
    h1.comp ξ ((hasFDerivAt_id ξ).const_smul c)
  have h3 : HasFDerivAt (fun y => F (c • y)) (|c| • fderiv ℝ F ξ) ξ := by
    have heq : (fun y => F (c • y)) = fun y => |c| * F y := funext fun y => hF.homog c y
    rw [heq]
    exact ((hF.contDiffAt hξ).differentiableAt (by simp)).hasFDerivAt.const_mul |c|
  have h4 := h2.unique h3
  refine ext_inner_right ℝ fun h => ?_
  have := congrArg (fun L : Euc d →L[ℝ] ℝ => L h) h4
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, ← inner_gradient_left,
    abs_of_neg hc] at this
  rw [inner_neg_left]
  refine mul_left_cancel₀ hc.ne ?_
  linear_combination this

/-- Homogeneity of the flux: `a(cξ) = -|c|^{p-1} a(ξ)` for `c < 0`. -/
theorem flux_smul_of_neg {p : ℝ} (hp : 1 < p) {c : ℝ} (hc : c < 0) (ξ : Euc d) :
    flux p F (c • ξ) = -(|c| ^ (p - 1) • flux p F ξ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [flux_zero hp hF]
  rw [flux, flux, hF.homog, hF.gradient_smul_of_neg hc hξ,
    Real.mul_rpow (abs_nonneg c) (hF.nonneg ξ), smul_neg, smul_smul]

/-- The flux is differentiable at every `q ≠ 0`. -/
theorem hasFDerivAt_flux (p : ℝ) {q : Euc d} (hq : q ≠ 0) :
    HasFDerivAt (flux p F) (fderiv ℝ (flux p F) q) q :=
  (((hF.contDiffOn_flux p).differentiableOn (by simp)).differentiableAt
    (isOpen_compl_singleton.mem_nhds hq)).hasFDerivAt

/-- The flux is differentiable near every `q ≠ 0`. -/
theorem eventually_differentiableAt_flux (p : ℝ) {q : Euc d} (hq : q ≠ 0) :
    ∀ᶠ ξ in 𝓝 q, DifferentiableAt ℝ (flux p F) ξ := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hq] with ξ hξ
  exact (hF.hasFDerivAt_flux p hξ).differentiableAt

/-- The potential `G = F^p / p` of the flux: `a = ∇G` away from the origin. -/
theorem hasGradientAt_flux_potential {p : ℝ} (hp : 1 < p) {ξ : Euc d} (hξ : ξ ≠ 0) :
    HasGradientAt (fun x => F x ^ p / p) (flux p F ξ) ξ := by
  have hFξ : 0 < F ξ := hF.pos ξ hξ
  have hd : HasDerivAt (fun s : ℝ => s ^ p / p) (F ξ ^ (p - 1)) (F ξ) := by
    have := (Real.hasDerivAt_rpow_const (x := F ξ) (p := p) (Or.inl hFξ.ne')).div_const p
    have hp0 : p ≠ 0 := by linarith
    exact this.congr_deriv (mul_div_cancel_left₀ _ hp0)
  have hg : HasGradientAt F (gradient F ξ) ξ :=
    ((hF.contDiffAt hξ).differentiableAt (by simp)).hasGradientAt
  have h := hd.comp_hasFDerivAt ξ (hasGradientAt_iff_hasFDerivAt.1 hg)
  rw [hasGradientAt_iff_hasFDerivAt, flux, map_smul]
  exact h

/-- `F^p / p` is convex. -/
theorem convexOn_flux_potential {p : ℝ} (hp : 1 < p) :
    ConvexOn ℝ univ fun x => F x ^ p / p := by
  have h1 : ConvexOn ℝ univ fun x => F x ^ p := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hc := hF.convexOn.2 (mem_univ x) (mem_univ y) ha hb hab
    have h2 := (convexOn_rpow hp.le).2 (mem_Ici.2 (hF.nonneg x)) (mem_Ici.2 (hF.nonneg y))
      ha hb hab
    simp only [smul_eq_mul] at hc h2 ⊢
    calc F (a • x + b • y) ^ p ≤ (a * F x + b * F y) ^ p :=
          Real.rpow_le_rpow (hF.nonneg _) hc (by linarith)
      _ ≤ a * F x ^ p + b * F y ^ p := h2
  have hp0 : 0 < p := by linarith
  simpa [div_eq_inv_mul] using h1.smul (inv_pos.2 hp0).le

/-- **Symmetry of `A(q) = Da(q)`** for `q ≠ 0`. -/
theorem inner_fderiv_flux_comm {p : ℝ} (hp : 1 < p) {q : Euc d} (hq : q ≠ 0) (ζ ζ' : Euc d) :
    ⟪fderiv ℝ (flux p F) q ζ, ζ'⟫ = ⟪ζ, fderiv ℝ (flux p F) q ζ'⟫ := by
  set G : Euc d → ℝ := fun x => F x ^ p / p with hG
  have hev : ∀ᶠ ξ in 𝓝 q, ξ ≠ 0 := isOpen_compl_singleton.mem_nhds hq
  have hd : ∀ᶠ ξ in 𝓝 q, DifferentiableAt ℝ G ξ := by
    filter_upwards [hev] with ξ hξ
    exact (hF.hasGradientAt_flux_potential hp hξ).differentiableAt
  have hgrad : flux p F =ᶠ[𝓝 q] gradient G := by
    filter_upwards [hev] with ξ hξ
    exact (hF.hasGradientAt_flux_potential hp hξ).gradient.symm
  have hH : HasFDerivAt (gradient G) (fderiv ℝ (flux p F) q) q :=
    (hF.hasFDerivAt_flux p hq).congr_of_eventuallyEq hgrad.symm
  exact inner_fderiv_gradient_comm hd hH ζ ζ'

/-- **Positivity of `A(q) = Da(q)`** for `q ≠ 0` (paper (A.ellipticity), the lower bound; here
only positive semidefiniteness is used). -/
theorem inner_fderiv_flux_nonneg {p : ℝ} (hp : 1 < p) {q : Euc d} (hq : q ≠ 0) (ζ : Euc d) :
    0 ≤ ⟪fderiv ℝ (flux p F) q ζ, ζ⟫ := by
  set G : Euc d → ℝ := fun x => F x ^ p / p with hG
  have hev : ∀ᶠ ξ in 𝓝 q, ξ ≠ 0 := isOpen_compl_singleton.mem_nhds hq
  have hgrad : flux p F =ᶠ[𝓝 q] gradient G := by
    filter_upwards [hev] with ξ hξ
    exact (hF.hasGradientAt_flux_potential hp hξ).gradient.symm
  have hH : HasFDerivAt (gradient G) (fderiv ℝ (flux p F) q) q :=
    (hF.hasFDerivAt_flux p hq).congr_of_eventuallyEq hgrad.symm
  have hq0 : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hball : ∀ ξ ∈ Metric.ball q ‖q‖, ξ ≠ 0 := fun ξ hξ h0 => by
    rw [h0, Metric.mem_ball, dist_zero_left] at hξ
    exact lt_irrefl _ hξ
  refine inner_fderiv_gradient_nonneg_of_convexOn Metric.isOpen_ball
    ((hF.convexOn_flux_potential hp).subset (subset_univ _) (convex_ball q ‖q‖)) ?_
    (Metric.mem_ball_self hq0) hH ζ
  exact fun ξ hξ =>
    (hF.hasGradientAt_flux_potential hp (hball ξ hξ)).differentiableAt.differentiableWithinAt

end IsSmoothStrictNorm

/-! ### The flux-divergence of `e^{-v}` -/

theorem HasGradientAt.neg' {f : Euc d → ℝ} {f' x : Euc d} (hf : HasGradientAt f f' x) :
    HasGradientAt (fun y => -f y) (-f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  rw [map_neg]
  exact hf.neg

/-- **The flux-divergence of `e^{-v}`** (paper Appendix A: "Evenness and homogeneity give, at
noncritical points, `div a(∇e^{-v}) = e^{-(p-1)v}((p-1)F(∇v)^p - div a(∇v))`"): for `v`
differentiable near `x` with `∇v` differentiable at `x` and `∇v(x) ≠ 0`. -/
theorem divergence_flux_gradient_exp_neg {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {v : Euc d → ℝ} {x : Euc d}
    (hv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y) (hv' : DifferentiableAt ℝ (gradient v) x)
    (hx : gradient v x ≠ 0) :
    divergence (fun y => flux p F (gradient (fun y => Real.exp (-v y)) y)) x =
      Real.exp (-((p - 1) * v x)) *
        ((p - 1) * F (gradient v x) ^ p - divergence (fun y => flux p F (gradient v y)) x) := by
  -- the gradient of `e^{-v}` near `x`
  have hgrad : ∀ᶠ y in 𝓝 x,
      gradient (fun y => Real.exp (-v y)) y = (-Real.exp (-v y)) • gradient v y := by
    filter_upwards [hv] with y hy
    have h := hasGradientAt_exp_neg_mul hy.hasGradientAt 1
    simp only [one_mul] at h
    exact h.gradient
  -- the flux field of `e^{-v}` is `-e^{-(p-1)v} a(∇v)`
  have hflux : (fun y => flux p F (gradient (fun y => Real.exp (-v y)) y)) =ᶠ[𝓝 x]
      fun y => (-Real.exp (-((p - 1) * v y))) • flux p F (gradient v y) := by
    filter_upwards [hgrad] with y hy
    rw [hy, hF.flux_smul_of_neg hp (neg_neg_of_pos (Real.exp_pos _)), abs_neg,
      abs_of_pos (Real.exp_pos _), ← Real.exp_mul, neg_smul]
    congr 3
    ring
  rw [divergence_congr hflux]
  -- product rule
  have hm : HasGradientAt (fun y => -Real.exp (-((p - 1) * v y)))
      (((p - 1) * Real.exp (-((p - 1) * v x))) • gradient v x) x := by
    have h := HasGradientAt.neg' (hasGradientAt_exp_neg_mul hv.self_of_nhds.hasGradientAt (p - 1))
    rwa [neg_smul, neg_neg] at h
  have hW : HasFDerivAt (fun y => flux p F (gradient v y))
      ((fderiv ℝ (flux p F) (gradient v x)).comp (fderiv ℝ (gradient v) x)) x :=
    (hF.hasFDerivAt_flux p hx).comp x hv'.hasFDerivAt
  rw [divergence_smul hm hW, real_inner_smul_left, real_inner_comm, hF.inner_flux_self hp]
  ring

/-! ### `C²` regularity of the perturbed infimal convolution and the Hessian comparison -/

namespace InfConvData

variable {D : InfConvData d}

/-- A feasible pair satisfying the stationarity condition
`∇v₀(x₀) + 2ηx₀ = ∇v₁(x₁) + 2ηx₁` is a minimizing pair (by convexity of the perturbed
objective). -/
theorem isMinimizer_of_gradient_eq {η : ℝ} (hη : 0 ≤ η) {z : Euc d} {p : Euc d × Euc d}
    (hp : p ∈ D.feasible z)
    (hstat : gradient D.v₀ p.1 + (2 * η) • p.1 = gradient D.v₁ p.2 + (2 * η) • p.2) :
    D.IsMinimizer η z p := by
  refine ⟨hp, fun q hq => ?_⟩
  set g := gradient D.v₀ p.1 + (2 * η) • p.1 with hg
  have hg₀ : HasGradientAt (pert D.v₀ η) g p.1 := hasGradientAt_pert (D.h₀.hasGradientAt hp.1) η
  have hg₁ : HasGradientAt (pert D.v₁ η) g p.2 := by
    rw [hstat]
    exact hasGradientAt_pert (D.h₁.hasGradientAt hp.2.1) η
  have h0 := convexOn_inner_gradient_le_sub (convexOn_pert D.h₀.convexOn hη) hp.1 hq.1 hg₀
  have h1 := convexOn_inner_gradient_le_sub (convexOn_pert D.h₁.convexOn hη) hp.2.1 hq.2.1 hg₁
  have hcombo : (1 - D.t) • (q.1 - p.1) + D.t • (q.2 - p.2) = 0 := by
    have e1 := hp.2.2
    have e2 := hq.2.2
    calc (1 - D.t) • (q.1 - p.1) + D.t • (q.2 - p.2)
        = ((1 - D.t) • q.1 + D.t • q.2) - ((1 - D.t) • p.1 + D.t • p.2) := by module
      _ = 0 := by rw [e1, e2, sub_self]
  have hsum : (1 - D.t) * ⟪g, q.1 - p.1⟫ + D.t * ⟪g, q.2 - p.2⟫ = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcombo,
      inner_zero_right]
  have e0 := mul_le_mul_of_nonneg_left h0 D.one_sub_t_pos.le
  have e1 := mul_le_mul_of_nonneg_left h1 D.t_pos.le
  show D.obj η p ≤ D.obj η q
  simp only [obj]
  linarith

/-- The stationarity map `(z, (x₀, x₁)) ↦ (∇v₀(x₀) + 2ηx₀ - ∇v₁(x₁) - 2ηx₁, (1-t)x₀ + tx₁ - z)`
whose zero set is the graph of the minimizing pair (paper Appendix A: "implicit
differentiation"). -/
noncomputable def statMap (D : InfConvData d) (η : ℝ) (q : Euc d × (Euc d × Euc d)) :
    Euc d × Euc d :=
  (gradient D.v₀ q.2.1 + (2 * η) • q.2.1 - (gradient D.v₁ q.2.2 + (2 * η) • q.2.2),
    (1 - D.t) • q.2.1 + D.t • q.2.2 - q.1)

/-- **`w_η ∈ C²` near a point whose minimizing pair has `C¹` gradients** (paper Appendix A:
"implicit differentiation gives `D²w_η`"): for `η > 0`, if `∇v_i` is `C¹` at `x_i`, then `∇w_η`
is `C¹` at `z`. Proof by the implicit function theorem for the stationarity map, whose partial
Jacobian `(h₀, h₁) ↦ (B₀h₀ - B₁h₁, (1-t)h₀ + th₁)` is invertible since `B_i = D²v_i + 2ηI ≻ 0`;
the implicit function is the minimizing pair (`isMinimizer_of_gradient_eq`). -/
theorem IsMinimizer.contDiffAt_gradient_w {η : ℝ} (hη : 0 < η) {z : Euc d}
    {p : Euc d × Euc d} (hp : D.IsMinimizer η z p) (h₀ : ContDiffAt ℝ 1 (gradient D.v₀) p.1)
    (h₁ : ContDiffAt ℝ 1 (gradient D.v₁) p.2) : ContDiffAt ℝ 1 (gradient (D.w η)) z := by
  -- the Hessians of `v_i` at `p.i` are positive semidefinite
  set H₀ := fderiv ℝ (gradient D.v₀) p.1 with hH₀def
  set H₁ := fderiv ℝ (gradient D.v₁) p.2 with hH₁def
  have hH₀ : HasFDerivAt (gradient D.v₀) H₀ p.1 := (h₀.differentiableAt one_ne_zero).hasFDerivAt
  have hH₁ : HasFDerivAt (gradient D.v₁) H₁ p.2 := (h₁.differentiableAt one_ne_zero).hasFDerivAt
  have hH₀n : ∀ ζ, 0 ≤ ⟪H₀ ζ, ζ⟫ := fun ζ =>
    inner_fderiv_gradient_nonneg_of_convexOn D.h₀.isOpen D.h₀.convexOn
      (D.h₀.contDiffOn.differentiableOn one_ne_zero) hp.fst_mem hH₀ ζ
  have hH₁n : ∀ ζ, 0 ≤ ⟪H₁ ζ, ζ⟫ := fun ζ =>
    inner_fderiv_gradient_nonneg_of_convexOn D.h₁.isOpen D.h₁.convexOn
      (D.h₁.contDiffOn.differentiableOn one_ne_zero) hp.snd_mem hH₁ ζ
  -- `C¹` of the stationarity map at `(z, p)`
  have hcd : ContDiffAt ℝ 1 (D.statMap η) (z, p) := by
    have e₀ : ContDiffAt ℝ 1 (fun q : Euc d × (Euc d × Euc d) => gradient D.v₀ q.2.1) (z, p) :=
      ContDiffAt.comp (g := gradient D.v₀) (f := fun q : Euc d × (Euc d × Euc d) => q.2.1)
        (z, p) h₀ contDiffAt_snd.fst
    have e₁ : ContDiffAt ℝ 1 (fun q : Euc d × (Euc d × Euc d) => gradient D.v₁ q.2.2) (z, p) :=
      ContDiffAt.comp (g := gradient D.v₁) (f := fun q : Euc d × (Euc d × Euc d) => q.2.2)
        (z, p) h₁ contDiffAt_snd.snd
    unfold statMap
    fun_prop
  -- its derivative
  set P₀ : Euc d × (Euc d × Euc d) →L[ℝ] Euc d :=
    (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)).comp
      (ContinuousLinearMap.snd ℝ (Euc d) (Euc d × Euc d)) with hP₀def
  set P₁ : Euc d × (Euc d × Euc d) →L[ℝ] Euc d :=
    (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).comp
      (ContinuousLinearMap.snd ℝ (Euc d) (Euc d × Euc d)) with hP₁def
  set Pz : Euc d × (Euc d × Euc d) →L[ℝ] Euc d :=
    ContinuousLinearMap.fst ℝ (Euc d) (Euc d × Euc d) with hPzdef
  have hP₀ : HasFDerivAt (fun q : Euc d × (Euc d × Euc d) => q.2.1) P₀ (z, p) :=
    hasFDerivAt_snd.fst
  have hP₁ : HasFDerivAt (fun q : Euc d × (Euc d × Euc d) => q.2.2) P₁ (z, p) :=
    hasFDerivAt_snd.snd
  have hPz : HasFDerivAt (fun q : Euc d × (Euc d × Euc d) => q.1) Pz (z, p) := hasFDerivAt_fst
  have hg₀ : HasFDerivAt
      (fun q : Euc d × (Euc d × Euc d) => gradient D.v₀ q.2.1 + (2 * η) • q.2.1)
      (H₀.comp P₀ + (2 * η) • P₀) (z, p) :=
    (hH₀.comp (z, p) hP₀).add (hP₀.const_smul (2 * η))
  have hg₁ : HasFDerivAt
      (fun q : Euc d × (Euc d × Euc d) => gradient D.v₁ q.2.2 + (2 * η) • q.2.2)
      (H₁.comp P₁ + (2 * η) • P₁) (z, p) :=
    (hH₁.comp (z, p) hP₁).add (hP₁.const_smul (2 * η))
  set L : Euc d × (Euc d × Euc d) →L[ℝ] Euc d × Euc d :=
    (H₀.comp P₀ + (2 * η) • P₀ - (H₁.comp P₁ + (2 * η) • P₁)).prod
      ((1 - D.t) • P₀ + D.t • P₁ - Pz) with hLdef
  have hfd : HasFDerivAt (D.statMap η) L (z, p) :=
    (hg₀.sub hg₁).prodMk (((hP₀.const_smul (1 - D.t)).add (hP₁.const_smul D.t)).sub hPz)
  -- the partial Jacobian in `(x₀, x₁)` is invertible
  have hinj : Function.Injective (L ∘L ContinuousLinearMap.inr ℝ (Euc d) (Euc d × Euc d)) := by
    refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
    simp only [hLdef, hP₀def, hP₁def, hPzdef, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.prod_apply, _root_.sub_apply,
      _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', sub_zero, Prod.mk_eq_zero] at hh
    obtain ⟨e1, e2⟩ := hh
    have e1' : H₀ h.1 + (2 * η) • h.1 = H₁ h.2 + (2 * η) • h.2 := sub_eq_zero.1 e1
    have e2' : D.t • h.2 = -((1 - D.t) • h.1) := eq_neg_of_add_eq_zero_right e2
    have c2 : D.t • (H₁ h.2 + (2 * η) • h.2) = -((1 - D.t) • (H₁ h.1 + (2 * η) • h.1)) := by
      have hy : H₁ (D.t • h.2) = -((1 - D.t) • H₁ h.1) := by rw [e2', map_neg, map_smul]
      rw [smul_add, ← map_smul, hy, smul_comm D.t (2 * η) h.2, e2']
      module
    have c1 : D.t • (H₀ h.1 + (2 * η) • h.1) = -((1 - D.t) • (H₁ h.1 + (2 * η) • h.1)) := by
      rw [e1']; exact c2
    have c3 := congrArg (fun v => ⟪v, h.1⟫) c1
    simp only [real_inner_smul_left, inner_add_left, inner_neg_left,
      real_inner_self_eq_norm_sq] at c3
    have h2 : 2 * η * ‖h.1‖ ^ 2 ≤ 0 := by
      linarith [mul_nonneg D.t_pos.le (hH₀n h.1), mul_nonneg D.one_sub_t_pos.le (hH₁n h.1)]
    have hn : ‖h.1‖ ^ 2 ≤ 0 := by nlinarith
    have h1z : h.1 = 0 :=
      norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm hn (sq_nonneg _)))
    have h2z : h.2 = 0 := by
      rw [h1z, smul_zero, neg_zero] at e2'
      exact (smul_eq_zero.1 e2').resolve_left D.t_pos.ne'
    exact Prod.ext h1z h2z
  have hsurj : Function.Surjective (L ∘L ContinuousLinearMap.inr ℝ (Euc d) (Euc d × Euc d)) :=
    LinearMap.injective_iff_surjective.1 hinj
  have if₂ : (fderiv ℝ (D.statMap η) (z, p) ∘L
      ContinuousLinearMap.inr ℝ (Euc d) (Euc d × Euc d)).IsInvertible := by
    rw [hfd.fderiv]
    exact ⟨(LinearEquiv.ofBijective
      ((L ∘L ContinuousLinearMap.inr ℝ (Euc d) (Euc d × Euc d) : _ →L[ℝ] _) : _ →ₗ[ℝ] _)
      ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ContinuousLinearMap.ext fun v => rfl⟩
  -- the implicit function is the minimizing pair
  set ψ := hcd.implicitFunction one_ne_zero if₂ with hψdef
  have hψz : ψ z = p := hcd.implicitFunction_apply_self one_ne_zero if₂
  have hψcd : ContDiffAt ℝ 1 ψ z := hcd.contDiffAt_implicitFunction one_ne_zero if₂
  have hev : ∀ᶠ z' in 𝓝 z, D.statMap η (z', ψ z') = D.statMap η (z, p) :=
    hcd.eventually_apply_implicitFunction one_ne_zero if₂
  have hstat0 : D.statMap η (z, p) = 0 := by
    simp only [statMap, hp.gradient_eq, hp.combo_eq, sub_self, Prod.mk_zero_zero]
  have hmin : ∀ᶠ z' in 𝓝 z,
      gradient (D.w η) z' = gradient D.v₀ (ψ z').1 + (2 * η) • (ψ z').1 := by
    have hK : ∀ᶠ z' in 𝓝 z, ψ z' ∈ D.K₀ ×ˢ D.K₁ := by
      have hmem : D.K₀ ×ˢ D.K₁ ∈ 𝓝 (ψ z) := by
        rw [hψz]
        exact prod_mem_nhds (D.h₀.isOpen.mem_nhds hp.fst_mem) (D.h₁.isOpen.mem_nhds hp.snd_mem)
      exact hψcd.continuousAt.eventually_mem hmem
    filter_upwards [hK, hev] with z' hz' hst
    rw [hstat0] at hst
    simp only [statMap, Prod.mk_eq_zero, sub_eq_zero] at hst
    have hfeas : ψ z' ∈ D.feasible z' := ⟨hz'.1, hz'.2, hst.2⟩
    have hm := D.isMinimizer_of_gradient_eq hη.le hfeas hst.1
    rw [hm.gradient_w hη.le]
    rfl
  have hcd' : ContDiffAt ℝ 1 (fun z' => gradient D.v₀ (ψ z').1 + (2 * η) • (ψ z').1) z := by
    have e : ContDiffAt ℝ 1 (fun z' => gradient D.v₀ (ψ z').1) z := by
      have h₀' : ContDiffAt ℝ 1 (gradient D.v₀) (ψ z).1 := by rw [hψz]; exact h₀
      exact ContDiffAt.comp (g := gradient D.v₀) (f := fun z' => (ψ z').1) z h₀' hψcd.fst
    exact e.add (hψcd.fst.const_smul (2 * η))
  exact hcd'.congr_of_eventuallyEq hmin

/-- **The Hessian comparison** (paper Appendix A: "`D²w_η = ((1-t)B₀⁻¹ + tB₁⁻¹)⁻¹ ≤ (1-t)B₀ + tB₁`,
the arithmetic–harmonic inequality"): here obtained directly as the second-order necessary
condition for the upper bound `w_η(y) ≤ (1-t)(v₀+η|·|²)(x₀ + y - z) + t(v₁+η|·|²)(x₁ + y - z)`
(shifting both components of the minimizing pair), which touches `w_η` at `z`:
`⟪D²w_η(z) ζ, ζ⟫ ≤ (1-t)(⟪D²v₀(x₀) ζ, ζ⟫ + 2η‖ζ‖²) + t(⟪D²v₁(x₁) ζ, ζ⟫ + 2η‖ζ‖²)`. -/
theorem IsMinimizer.inner_fderiv_gradient_w_le {η : ℝ} (hη : 0 ≤ η) {z : Euc d}
    {p : Euc d × Euc d} (hp : D.IsMinimizer η z p) {H H₀ H₁ : Euc d →L[ℝ] Euc d}
    (hH : HasFDerivAt (gradient (D.w η)) H z) (hH₀ : HasFDerivAt (gradient D.v₀) H₀ p.1)
    (hH₁ : HasFDerivAt (gradient D.v₁) H₁ p.2) (ζ : Euc d) :
    ⟪H ζ, ζ⟫ ≤ (1 - D.t) * (⟪H₀ ζ, ζ⟫ + 2 * η * ‖ζ‖ ^ 2) +
      D.t * (⟪H₁ ζ, ζ⟫ + 2 * η * ‖ζ‖ ^ 2) := by
  have hz := hp.mem_Kt
  -- the comparison function `g`
  set g : Euc d → ℝ := fun y =>
    (1 - D.t) * pert D.v₀ η (p.1 + (y - z)) + D.t * pert D.v₁ η (p.2 + (y - z)) with hg
  have hT₀ : ∀ y, HasFDerivAt (fun y => p.1 + (y - z)) (ContinuousLinearMap.id ℝ (Euc d)) y :=
    fun y => ((hasFDerivAt_id y).sub_const z).const_add p.1
  have hT₁ : ∀ y, HasFDerivAt (fun y => p.2 + (y - z)) (ContinuousLinearMap.id ℝ (Euc d)) y :=
    fun y => ((hasFDerivAt_id y).sub_const z).const_add p.2
  have hev₀ : ∀ᶠ y in 𝓝 z, p.1 + (y - z) ∈ D.K₀ := by
    have hc : Continuous fun y : Euc d => p.1 + (y - z) := by fun_prop
    have := hc.tendsto z
    simp only [sub_self, add_zero] at this
    exact this.eventually (D.h₀.isOpen.mem_nhds hp.fst_mem)
  have hev₁ : ∀ᶠ y in 𝓝 z, p.2 + (y - z) ∈ D.K₁ := by
    have hc : Continuous fun y : Euc d => p.2 + (y - z) := by fun_prop
    have := hc.tendsto z
    simp only [sub_self, add_zero] at this
    exact this.eventually (D.h₁.isOpen.mem_nhds hp.snd_mem)
  have hevK : ∀ᶠ y in 𝓝 z, y ∈ D.Kt := D.isOpen_Kt.mem_nhds hz
  -- `g - w_η` has a local minimum at `z`
  have hgz : g z = D.obj η p := by simp [hg, obj]
  have hmin : IsLocalMin (fun y => g y - D.w η y) z := by
    filter_upwards [hev₀, hev₁] with y hy₀ hy₁
    have hfeas : (p.1 + (y - z), p.2 + (y - z)) ∈ D.feasible y := by
      refine ⟨hy₀, hy₁, ?_⟩
      have := hp.combo_eq
      calc (1 - D.t) • (p.1 + (y - z)) + D.t • (p.2 + (y - z))
          = ((1 - D.t) • p.1 + D.t • p.2) + (y - z) := by module
        _ = y := by rw [this]; abel
    have hle : D.w η y ≤ g y := D.w_le_obj hη hfeas
    show g z - D.w η z ≤ g y - D.w η y
    rw [hgz, hp.w_eq, sub_self]
    linarith
  -- the gradient of `g - w_η` near `z`
  have hgrad : ∀ᶠ y in 𝓝 z, HasGradientAt (fun y => g y - D.w η y)
      ((1 - D.t) • (gradient D.v₀ (p.1 + (y - z)) + (2 * η) • (p.1 + (y - z))) +
        D.t • (gradient D.v₁ (p.2 + (y - z)) + (2 * η) • (p.2 + (y - z))) -
        gradient (D.w η) y) y := by
    filter_upwards [hev₀, hev₁, hevK] with y hy₀ hy₁ hyK
    have hw : HasGradientAt (D.w η) (gradient (D.w η) y) y :=
      (D.differentiableOn_w hη).hasGradientAt (D.isOpen_Kt.mem_nhds hyK)
    have h0 : HasGradientAt (fun y => pert D.v₀ η (p.1 + (y - z)))
        (gradient D.v₀ (p.1 + (y - z)) + (2 * η) • (p.1 + (y - z))) y := by
      have h := hasGradientAt_pert (D.h₀.hasGradientAt hy₀) η
      rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
      have := h.comp y (hT₀ y)
      rwa [ContinuousLinearMap.comp_id] at this
    have h1 : HasGradientAt (fun y => pert D.v₁ η (p.2 + (y - z)))
        (gradient D.v₁ (p.2 + (y - z)) + (2 * η) • (p.2 + (y - z))) y := by
      have h := hasGradientAt_pert (D.h₁.hasGradientAt hy₁) η
      rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
      have := h.comp y (hT₁ y)
      rwa [ContinuousLinearMap.comp_id] at this
    exact HasGradientAt.sub' (HasGradientAt.add' (HasGradientAt.const_mul' h0 (1 - D.t))
      (HasGradientAt.const_mul' h1 D.t)) hw
  -- the Hessian of `g - w_η` at `z`
  set M : Euc d →L[ℝ] Euc d :=
    (1 - D.t) • (H₀ + (2 * η) • ContinuousLinearMap.id ℝ (Euc d)) +
      D.t • (H₁ + (2 * η) • ContinuousLinearMap.id ℝ (Euc d)) - H with hM
  have hG : HasFDerivAt (fun y =>
      (1 - D.t) • (gradient D.v₀ (p.1 + (y - z)) + (2 * η) • (p.1 + (y - z))) +
        D.t • (gradient D.v₁ (p.2 + (y - z)) + (2 * η) • (p.2 + (y - z))) -
        gradient (D.w η) y) M z := by
    have hH₀' : HasFDerivAt (gradient D.v₀) H₀ (p.1 + (z - z)) := by simpa using hH₀
    have hH₁' : HasFDerivAt (gradient D.v₁) H₁ (p.2 + (z - z)) := by simpa using hH₁
    have e0 : HasFDerivAt (fun y => gradient D.v₀ (p.1 + (y - z))) H₀ z := by
      have := hH₀'.comp z (hT₀ z)
      rwa [ContinuousLinearMap.comp_id] at this
    have e1 : HasFDerivAt (fun y => gradient D.v₁ (p.2 + (y - z))) H₁ z := by
      have := hH₁'.comp z (hT₁ z)
      rwa [ContinuousLinearMap.comp_id] at this
    have e0' : HasFDerivAt (fun y => (2 * η) • (p.1 + (y - z)))
        ((2 * η) • ContinuousLinearMap.id ℝ (Euc d)) z := (hT₀ z).const_smul (2 * η)
    have e1' : HasFDerivAt (fun y => (2 * η) • (p.2 + (y - z)))
        ((2 * η) • ContinuousLinearMap.id ℝ (Euc d)) z := (hT₁ z).const_smul (2 * η)
    exact (((e0.add e0').const_smul (1 - D.t)).add ((e1.add e1').const_smul D.t)).sub hH
  have hM' : HasFDerivAt (gradient (fun y => g y - D.w η y)) M z :=
    hG.congr_of_eventuallyEq (hgrad.mono fun y hy => hy.gradient)
  have hpsd := inner_fderiv_gradient_nonneg_of_isLocalMin hmin
    (hgrad.mono fun y hy => hy.differentiableAt) hM' ζ
  simp only [hM, _root_.sub_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hpsd
  linarith

end InfConvData


end Komlos.Literature
