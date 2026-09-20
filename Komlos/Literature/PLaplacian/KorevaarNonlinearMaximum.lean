import Komlos.Literature.PLaplacian.KorevaarAux

/-!
# Nonlinear two-point maximum conditions

These are pointwise consequences of the anisotropic flux equation at a smooth,
noncritical local maximum of the concavity function. A strictly increasing affine
zeroth-order reaction excludes a positive local maximum. For the transformed
eigenfunction equation, whose zeroth-order coefficient vanishes, the full pair
second variation instead forces the three Hessian quadratic forms to be equal and nonnegative.
Neither conclusion asserts a differential inequality on a neighborhood.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Korevaar

variable {d : ℕ}

/-- Translating the endpoints with different velocities translates their midpoint
with the average velocity. -/
theorem midpoint_add_smul_pair (x y ξ η : Euc d) (t : ℝ) :
    midpoint ℝ (x + t • ξ) (y + t • η) = midpoint ℝ x y + t • ((1 / 2 : ℝ) • (ξ + η)) := by
  simp only [midpoint_eq_smul_add, invOf_eq_inv, smul_add, smul_smul]
  module

/-- The full pair second variation at a local maximum, allowing the endpoint
velocities to be different. -/
theorem inner_hessian_pair_le_of_isLocalMax {v : Euc d → ℝ} {x y : Euc d}
    {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v) Hx x) (hHy : HasFDerivAt (gradient v) Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y))
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y))
    (ξ η : Euc d) :
    ⟪Hm ((1 / 2 : ℝ) • (ξ + η)), (1 / 2 : ℝ) • (ξ + η)⟫ ≤
      (⟪Hx ξ, ξ⟫ + ⟪Hy η, η⟫) / 2 := by
  let ζ : Euc d := (1 / 2 : ℝ) • (ξ + η)
  let f : ℝ → ℝ := fun t =>
    -v (midpoint ℝ x y + t • ζ) + (v (x + t • ξ) + v (y + t • η)) / 2
  have hcont : Continuous fun t : ℝ => ((x + t • ξ, y + t • η) : Euc d × Euc d) := by
    fun_prop
  have hten : Tendsto (fun t : ℝ => ((x + t • ξ, y + t • η) : Euc d × Euc d))
      (𝓝 0) (𝓝 (x, y)) := by simpa using hcont.tendsto 0
  have hmin : IsLocalMin f 0 := by
    filter_upwards [hten.eventually hmax] with t ht
    change f 0 ≤ f t
    dsimp [f, ζ]
    simp only [concavityFn, midpoint_add_smul_pair] at ht
    simp only [zero_smul, add_zero]
    linarith
  obtain ⟨hx1, hx2⟩ := hasDerivAt_inner_gradient_line hdx hHx ξ
  obtain ⟨hy1, hy2⟩ := hasDerivAt_inner_gradient_line hdy hHy η
  obtain ⟨hm1, hm2⟩ := hasDerivAt_inner_gradient_line hdm hHm ζ
  let f' : ℝ → ℝ := fun t => -⟪gradient v (midpoint ℝ x y + t • ζ), ζ⟫ +
    (⟪gradient v (x + t • ξ), ξ⟫ + ⟪gradient v (y + t • η), η⟫) / 2
  have hf : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt f (f' t) t := by
    filter_upwards [hx1, hy1, hm1] with t hxt hyt hmt
    exact hmt.neg.add ((hxt.add hyt).div_const 2)
  have hderiv : deriv f =ᶠ[𝓝 (0 : ℝ)] f' := hf.mono fun t ht => ht.deriv
  have hf' : HasDerivAt f' (-⟪Hm ζ, ζ⟫ + (⟪Hx ξ, ξ⟫ + ⟪Hy η, η⟫) / 2) 0 :=
    hm2.neg.add ((hx2.add hy2).div_const 2)
  have hnonneg := nonneg_of_isLocalMin_of_hasDerivAt_deriv hmin
    (hf.mono fun t ht => ht.differentiableAt) (hf'.congr_of_eventuallyEq hderiv)
  change ⟪Hm ζ, ζ⟫ ≤ (⟪Hx ξ, ξ⟫ + ⟪Hy η, η⟫) / 2
  linarith

/-- Saturation of the diagonal second variation forces the three Hessian quadratic
forms to coincide and be nonnegative. This uses the full pair inequality. -/
theorem hessian_rigidity_of_pair_le_of_diagonal_eq {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hpair : ∀ ξ η : Euc d,
      ⟪Hm ((1 / 2 : ℝ) • (ξ + η)), (1 / 2 : ℝ) • (ξ + η)⟫ ≤
        (⟪Hx ξ, ξ⟫ + ⟪Hy η, η⟫) / 2)
    (hdiag : ∀ ζ : Euc d, ⟪Hm ζ, ζ⟫ = (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2)
    (ζ : Euc d) :
    ⟪Hx ζ, ζ⟫ = ⟪Hm ζ, ζ⟫ ∧ ⟪Hy ζ, ζ⟫ = ⟪Hm ζ, ζ⟫ ∧ 0 ≤ ⟪Hm ζ, ζ⟫ := by
  have hsum : 0 ≤ (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2 := by
    simpa using hpair ζ (-ζ)
  have hdiff : ⟪Hx ζ, ζ⟫ - ⟪Hy ζ, ζ⟫ = 0 := by
    refine eq_zero_of_quadratic_nonneg hsum fun t => ?_
    have h := hpair ((1 + t) • ζ) ((1 - t) • ζ)
    have hmid : (1 / 2 : ℝ) • ((1 + t) • ζ + (1 - t) • ζ) = ζ := by module
    rw [hmid, hdiag] at h
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h
    nlinarith
  have hd := hdiag ζ
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The two-point maximum principle for a differentiable flux with symmetric
positive semidefinite derivative at the common gradient and a strictly increasing
affine reaction in the value. This also applies at a critical point when the flux
and the solution have the displayed derivatives there. -/
theorem concavityFn_nonpos_of_isLocalMax_of_affine_reaction
    {fluxA : Euc d → Euc d} {A Hx Hy Hm : Euc d →L[ℝ] Euc d}
    {v reaction : Euc d → ℝ} {x y : Euc d} {κ : ℝ} (hκ : 0 < κ)
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v) Hx x) (hHy : HasFDerivAt (gradient v) Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y))
    (hflux : HasFDerivAt fluxA A (gradient v x))
    (hAs : ∀ ξ η : Euc d, ⟪A ξ, η⟫ = ⟪ξ, A η⟫)
    (hA0 : ∀ ξ : Euc d, 0 ≤ ⟪A ξ, ξ⟫)
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y))
    (hEx : divergence (fun z => fluxA (gradient v z)) x = κ * v x + reaction (gradient v x))
    (hEy : divergence (fun z => fluxA (gradient v z)) y = κ * v y + reaction (gradient v y))
    (hEm : divergence (fun z => fluxA (gradient v z)) (midpoint ℝ x y) =
      κ * v (midpoint ℝ x y) + reaction (gradient v (midpoint ℝ x y))) :
    concavityFn v x y ≤ 0 := by
  obtain ⟨hqm, hqy⟩ := gradient_eq_of_isLocalMax_pair hdx.self_of_nhds.hasGradientAt
    hdy.self_of_nhds.hasGradientAt hdm.self_of_nhds.hasGradientAt hmax
  have hAy : HasFDerivAt fluxA A (gradient v y) := by rw [hqy]; exact hflux
  have hAm : HasFDerivAt fluxA A (gradient v (midpoint ℝ x y)) := by rw [hqm]; exact hflux
  have hxtrace := divergence_comp (a := fluxA) (G := gradient v) hflux hHx
  have hytrace := divergence_comp (a := fluxA) (G := gradient v) hAy hHy
  have hmtrace := divergence_comp (a := fluxA) (G := gradient v) hAm hHm
  have htrace := trace_midpoint_le hAs hA0
    (inner_hessian_midpoint_le_of_isLocalMax hdx hdy hdm hHx hHy hHm hmax)
  rw [← hmtrace, ← hxtrace, ← hytrace, hEm, hEx, hEy, hqm, hqy] at htrace
  have hmul : κ * concavityFn v x y ≤ 0 := by dsimp [concavityFn]; nlinarith
  by_contra hpos
  exact (not_lt_of_ge hmul) (mul_pos hκ (not_le.1 hpos))

/-- A positive affine zeroth-order term gives a genuine nonlinear two-point maximum
principle. At a smooth noncritical local maximum, gradient matching cancels the
arbitrary gradient reaction and the elliptic trace inequality forces `C ≤ 0`. -/
theorem concavityFn_nonpos_of_isLocalMax_of_strict_reaction
    {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {v reaction : Euc d → ℝ} {x y : Euc d} {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    {κ : ℝ} (hκ : 0 < κ)
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v) Hx x) (hHy : HasFDerivAt (gradient v) Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y)) (hq : gradient v x ≠ 0)
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y))
    (hEx : divergence (fun z => flux p F (gradient v z)) x = κ * v x + reaction (gradient v x))
    (hEy : divergence (fun z => flux p F (gradient v z)) y = κ * v y + reaction (gradient v y))
    (hEm : divergence (fun z => flux p F (gradient v z)) (midpoint ℝ x y) =
      κ * v (midpoint ℝ x y) + reaction (gradient v (midpoint ℝ x y))) :
    concavityFn v x y ≤ 0 := by
  exact concavityFn_nonpos_of_isLocalMax_of_affine_reaction hκ hdx hdy hdm hHx hHy hHm
    (hF.hasFDerivAt_flux' p hq) (inner_fderiv_flux_comm hF hp hq)
    (inner_fderiv_flux_nonneg hF hp hq) hmax hEx hEy hEm

/-- For the transformed eigenfunction equation, the same nonlinear trace calculation
has zero zeroth-order coefficient. Its pointwise conclusion is Hessian rigidity,
not exclusion of a positive maximum. -/
theorem hessian_rigidity_of_isLocalMax_of_equation {p : ℝ} (hp : 1 < p)
    {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {v : Euc d → ℝ} {x y : Euc d}
    {Hx Hy Hm : Euc d →L[ℝ] Euc d} {lam : ℝ}
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v) Hx x) (hHy : HasFDerivAt (gradient v) Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y)) (hq : gradient v x ≠ 0)
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y))
    (hEx : divergence (fun z => flux p F (gradient v z)) x = lam + (p - 1) * F (gradient v x) ^ p)
    (hEy : divergence (fun z => flux p F (gradient v z)) y = lam + (p - 1) * F (gradient v y) ^ p)
    (hEm : divergence (fun z => flux p F (gradient v z)) (midpoint ℝ x y) =
      lam + (p - 1) * F (gradient v (midpoint ℝ x y)) ^ p) (ζ : Euc d) :
    ⟪Hx ζ, ζ⟫ = ⟪Hm ζ, ζ⟫ ∧ ⟪Hy ζ, ζ⟫ = ⟪Hm ζ, ζ⟫ ∧ 0 ≤ ⟪Hm ζ, ζ⟫ := by
  obtain ⟨hqm, hqy⟩ := gradient_eq_of_isLocalMax_pair hdx.self_of_nhds.hasGradientAt
    hdy.self_of_nhds.hasGradientAt hdm.self_of_nhds.hasGradientAt hmax
  exact hessian_rigidity_of_pair_le_of_diagonal_eq
    (inner_hessian_pair_le_of_isLocalMax hdx hdy hdm hHx hHy hHm hmax)
    (inner_hessian_midpoint_eq_of_equation hp hF hdx hdy hdm hHx hHy hHm hq hqy hqm hmax
      hEx hEy hEm) ζ


end Komlos.Literature.Korevaar
