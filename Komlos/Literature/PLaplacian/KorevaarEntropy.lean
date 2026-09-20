import Komlos.Literature.PLaplacian.KorevaarApproximation

/-!
# The homogeneous kinetic energy with an entropy perturbation

For a smooth even profile `Ψ`, the coupled density is `Q(u,ξ)=u^p Ψ(ξ/u)`
on the positive half-space. Adding `(κ/p) u^p log u` to the energy gives a
positive affine term `κ v` in the equation for `v=-log u`. The normalization
multiplier only changes the gradient reaction by a constant.

This is a variational-to-PDE bridge. Construction and regularity of minimizers
remain separate obligations. In particular the kinetic density alone does not
give a positive affine coefficient.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Korevaar

variable {d : ℕ}

/-- A jointly homogeneous kinetic density, used on `u>0`. -/
noncomputable def homogeneousDensity (p : ℝ) (Ψ : Euc d → ℝ) (u : ℝ) (ξ : Euc d) : ℝ :=
  u ^ p * Ψ (u⁻¹ • ξ)

/-- Its derivative in the gradient variable when `A=∇Ψ`. -/
noncomputable def homogeneousFlux (p : ℝ) (A : Euc d → Euc d) (u : ℝ) (ξ : Euc d) : Euc d :=
  u ^ (p - 1) • A (u⁻¹ • ξ)

/-- Its derivative in the value variable when `A=∇Ψ`. -/
noncomputable def homogeneousValueDerivative (p : ℝ) (Ψ : Euc d → ℝ)
    (A : Euc d → Euc d) (u : ℝ) (ξ : Euc d) : ℝ :=
  u ^ (p - 1) * (p * Ψ (u⁻¹ • ξ) - ⟪A (u⁻¹ • ξ), u⁻¹ • ξ⟫)

/-- Entropy potential used together with the constraint `∫u^p=1`. -/
noncomputable def entropyPotential (p κ u : ℝ) : ℝ := κ / p * (u ^ p * Real.log u)

/-- The displayed flux is the actual gradient derivative of the homogeneous density. -/
theorem hasGradientAt_homogeneousDensity {p u : ℝ} (hu : 0 < u)
    {Ψ : Euc d → ℝ} {A : Euc d → Euc d} {ξ : Euc d}
    (hΨ : HasGradientAt Ψ (A (u⁻¹ • ξ)) (u⁻¹ • ξ)) :
    HasGradientAt (homogeneousDensity p Ψ u) (homogeneousFlux p A u ξ) ξ := by
  have hscale : u ^ p * u⁻¹ = u ^ (p - 1) := by
    rw [Real.rpow_sub_one hu.ne', div_eq_mul_inv]
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((hasGradientAt_iff_hasFDerivAt.1 hΨ).comp ξ
    ((hasFDerivAt_id ξ).const_smul u⁻¹)).const_mul (u ^ p)
  refine h.congr_fderiv ?_
  ext η
  simp [homogeneousFlux, InnerProductSpace.toDual_apply_apply, mul_assoc, ← hscale]

/-- The displayed scalar term is the actual value derivative of the homogeneous density. -/
theorem hasDerivAt_homogeneousDensity {p u : ℝ} (hu : 0 < u)
    {Ψ : Euc d → ℝ} {A : Euc d → Euc d} {ξ : Euc d}
    (hΨ : HasGradientAt Ψ (A (u⁻¹ • ξ)) (u⁻¹ • ξ)) :
    HasDerivAt (fun t => homogeneousDensity p Ψ t ξ)
      (homogeneousValueDerivative p Ψ A u ξ) u := by
  have hscale : u ^ p * u⁻¹ = u ^ (p - 1) := by
    rw [Real.rpow_sub_one hu.ne', div_eq_mul_inv]
  have hinv := ((hasDerivAt_id u).inv hu.ne').smul_const ξ
  have hcomp := (hasGradientAt_iff_hasFDerivAt.1 hΨ).comp_hasDerivAt u hinv
  rw [InnerProductSpace.toDual_apply_apply] at hcomp
  have h := (Real.hasDerivAt_rpow_const (x := u) (p := p) (Or.inl hu.ne')).mul hcomp
  refine h.congr_deriv ?_
  dsimp [homogeneousValueDerivative]
  simp only [real_inner_smul_right]
  rw [Real.rpow_sub_one hu.ne']
  field_simp
  ring

/-- Derivative of the entropy potential; the additive `κ/p` is absorbed into the
normalization multiplier in the Euler–Lagrange equation. -/
theorem hasDerivAt_entropyPotential {p κ u : ℝ} (hp : p ≠ 0) (hu : 0 < u) :
    HasDerivAt (entropyPotential p κ)
      (u ^ (p - 1) * (κ * Real.log u + κ / p)) u := by
  have h := ((Real.hasDerivAt_rpow_const (x := u) (p := p) (Or.inl hu.ne')).mul
    (Real.hasDerivAt_log hu.ne')).const_mul (κ / p)
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hu.ne']
  field_simp

/-- Weighted-flux product rule behind the logarithmic transformation. It does not
require a nonzero gradient, only differentiability of the chosen regularized flux. -/
theorem divergence_exp_weighted_flux {p : ℝ} {A : Euc d → Euc d} {v : Euc d → ℝ} {x : Euc d}
    (hv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y)
    (hgv : DifferentiableAt ℝ (gradient v) x) (hA : DifferentiableAt ℝ A (gradient v x)) :
    divergence (fun y => (-Real.exp (-((p - 1) * v y))) • A (gradient v y)) x =
      Real.exp (-((p - 1) * v x)) *
        ((p - 1) * ⟪A (gradient v x), gradient v x⟫ -
          divergence (fun y => A (gradient v y)) x) := by
  have hm : HasGradientAt (fun y => -Real.exp (-((p - 1) * v y)))
      (((p - 1) * Real.exp (-((p - 1) * v x))) • gradient v x) x := by
    have h := hasGradientAt_neg'
      (hasGradientAt_exp_neg_mul hv.self_of_nhds.hasGradientAt (p - 1))
    rwa [neg_smul, neg_neg] at h
  have hW : HasFDerivAt (fun y => A (gradient v y))
      ((fderiv ℝ A (gradient v x)).comp (fderiv ℝ (gradient v) x)) x :=
    hA.hasFDerivAt.comp x hgv.hasFDerivAt
  rw [divergence_smul hm hW, real_inner_smul_left, real_inner_comm]
  ring

/-- The actual Euler–Lagrange equation for the homogeneous kinetic density plus
entropy transforms to a strict affine-reaction equation. Derivatives in the input
are the derivatives of the displayed energy densities, not independently postulated
flux formulas. The identity is local and includes a zero gradient when `A` is
differentiable there. -/
theorem log_equation_of_entropy_euler_lagrange {p κ Λ : ℝ} (hp : p ≠ 0)
    {Ψ : Euc d → ℝ} {A : Euc d → Euc d}
    (hΨ : ∀ q, HasGradientAt Ψ (A q) q) (hΨeven : ∀ q, Ψ (-q) = Ψ q)
    (hAodd : ∀ q, A (-q) = -A q) {u v : Euc d → ℝ} {x : Euc d}
    (hu : u =ᶠ[𝓝 x] fun y => Real.exp (-v y))
    (hv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y)
    (hgv : DifferentiableAt ℝ (gradient v) x) (hA : DifferentiableAt ℝ A (gradient v x))
    (hEL : -divergence (fun y => gradient (homogeneousDensity p Ψ (u y)) (gradient u y)) x +
      deriv (fun t => homogeneousDensity p Ψ t (gradient u x)) (u x) +
      deriv (entropyPotential p κ) (u x) = Λ * u x ^ (p - 1)) :
    divergence (fun y => A (gradient v y)) x = κ * v x + (Λ - κ / p) +
      p * (⟪A (gradient v x), gradient v x⟫ - Ψ (gradient v x)) := by
  have hpos : ∀ᶠ y in 𝓝 x, 0 < u y := hu.mono fun y hy => by rw [hy]; exact Real.exp_pos _
  have hgrad : ∀ᶠ y in 𝓝 x,
      gradient u y = (-Real.exp (-v y)) • gradient v y := by
    filter_upwards [hv, hu.eventuallyEq_nhds] with y hy huy
    rw [huy.gradient_eq]
    have h := hasGradientAt_exp_neg_mul hy.hasGradientAt 1
    simpa only [one_mul] using h.gradient
  have hratio : ∀ᶠ y in 𝓝 x, (u y)⁻¹ • gradient u y = -gradient v y := by
    filter_upwards [hu, hgrad] with y huy hgy
    rw [huy, hgy, smul_smul]
    simp [Real.exp_ne_zero, mul_neg]
  have hpow : ∀ y, Real.exp (-v y) ^ (p - 1) = Real.exp (-((p - 1) * v y)) := by
    intro y
    rw [← Real.exp_mul]
    congr 1
    ring
  have hflux : (fun y => gradient (homogeneousDensity p Ψ (u y)) (gradient u y)) =ᶠ[𝓝 x]
      fun y => (-Real.exp (-((p - 1) * v y))) • A (gradient v y) := by
    filter_upwards [hpos, hu, hratio] with y hpy huy hry
    rw [(hasGradientAt_homogeneousDensity hpy (hΨ _)).gradient]
    dsimp [homogeneousFlux]
    rw [hry, hAodd, huy, hpow]
    simp only [smul_neg, neg_smul]
  have hdiv := divergence_exp_weighted_flux (p := p) hv hgv hA
  rw [← divergence_congr hflux] at hdiv
  rw [(hasDerivAt_homogeneousDensity hpos.self_of_nhds (hΨ _)).deriv,
    (hasDerivAt_entropyPotential hp hpos.self_of_nhds).deriv, hdiv] at hEL
  dsimp [homogeneousValueDerivative] at hEL
  rw [hratio.self_of_nhds, hΨeven, hAodd, inner_neg_neg, hu.self_of_nhds, hpow,
    Real.log_exp] at hEL
  have hcancel : Real.exp (-((p - 1) * v x)) *
      (divergence (fun y => A (gradient v y)) x - κ * v x - (Λ - κ / p) -
        p * (⟪A (gradient v x), gradient v x⟫ - Ψ (gradient v x))) = 0 := by
    linear_combination hEL
  have hzero := (mul_eq_zero.1 hcancel).resolve_left (Real.exp_pos _).ne'
  linarith

end Komlos.Literature.Korevaar
