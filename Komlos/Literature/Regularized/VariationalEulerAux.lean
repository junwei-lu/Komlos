import Komlos.Literature.Regularized.VariationalBound

/-!
# Pointwise derivatives of the regularized densities along a line

Lane `L1` (`reg/variational`).  Preparation for the weak Euler–Lagrange equation: the
derivative of `r ↦ Q(s + r σ, ξ + r η)` where `Q(s, ξ) = s² Ψ(ξ/s)` is the kinetic density.
On `s > 0` the density is smooth, and the chain rule gives

`d/dr Q(s + rσ, ξ + rη) = σ · D_value(s + rσ, ξ + rη) + ⟪Flux(s + rσ, ξ + rη), η⟫`

with `Flux = Korevaar.homogeneousFlux 2 (∇Ψ)` and
`D_value = Korevaar.homogeneousValueDerivative 2 Ψ (∇Ψ)`, exactly the two expressions
appearing in the frozen statement `IsRegMinimizer.weak_euler_lagrange`.

The file also records the quantitative bounds used to dominate the difference quotients.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ}

/-! ### The flux and the value derivative at `p = 2` -/

theorem homogeneousFlux_two (A : Euc d → Euc d) (s : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousFlux 2 A s ξ = s • A (s⁻¹ • ξ) := by
  rw [Korevaar.homogeneousFlux, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

theorem homogeneousValueDerivative_two (Ψ : Euc d → ℝ) (A : Euc d → Euc d) (s : ℝ)
    (ξ : Euc d) :
    Korevaar.homogeneousValueDerivative 2 Ψ A s ξ
      = s * (2 * Ψ (s⁻¹ • ξ) - ⟪A (s⁻¹ • ξ), s⁻¹ • ξ⟫) := by
  rw [Korevaar.homogeneousValueDerivative, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

/-! ### The derivative along a line -/

/-- **The derivative of the kinetic density along a line** in the `(value, gradient)` plane. -/
theorem hasDerivAt_homogeneousDensity_line (hΨ : IsRegProfile Ψ) (s σ : ℝ) (ξ η : Euc d)
    {τ : ℝ} (hpos : 0 < s + τ * σ) :
    HasDerivAt (fun r : ℝ => Korevaar.homogeneousDensity 2 Ψ (s + r * σ) (ξ + r • η))
      (σ * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (s + τ * σ) (ξ + τ • η)
        + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (s + τ * σ) (ξ + τ • η), η⟫) τ := by
  have hane : s + τ * σ ≠ 0 := hpos.ne'
  have hA : HasDerivAt (fun r : ℝ => s + r * σ) σ τ := by
    simpa using ((hasDerivAt_id τ).mul_const σ).const_add s
  have hAinv : HasDerivAt (fun r : ℝ => (s + r * σ)⁻¹) (-σ / (s + τ * σ) ^ 2) τ := hA.inv hane
  have hV : HasDerivAt (fun r : ℝ => ξ + r • η) η τ := by
    simpa using ((hasDerivAt_id τ).smul_const η).const_add ξ
  have hB : HasDerivAt (fun r : ℝ => (s + r * σ)⁻¹ • (ξ + r • η))
      ((s + τ * σ)⁻¹ • η + (-σ / (s + τ * σ) ^ 2) • (ξ + τ • η)) τ :=
    (hAinv.smul hV).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  have hΨb : HasDerivAt (fun r : ℝ => Ψ ((s + r * σ)⁻¹ • (ξ + r • η)))
      (⟪gradient Ψ ((s + τ * σ)⁻¹ • (ξ + τ • η)),
        (s + τ * σ)⁻¹ • η + (-σ / (s + τ * σ) ^ 2) • (ξ + τ • η)⟫) τ := by
    have hg := (hasGradientAt_iff_hasFDerivAt.1
      (hΨ.differentiable ((s + τ * σ)⁻¹ • (ξ + τ • η))).hasGradientAt).comp_hasDerivAt τ hB
    rw [InnerProductSpace.toDual_apply_apply] at hg
    simpa only [Function.comp_def] using hg
  have hsq : HasDerivAt (fun r : ℝ => (s + r * σ) ^ 2) (2 * (s + τ * σ) * σ) τ := by
    have h := hA.pow 2
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    push_cast
    ring
  have hprod := hsq.mul hΨb
  have hrw : (fun r : ℝ => Korevaar.homogeneousDensity 2 Ψ (s + r * σ) (ξ + r • η))
      = fun r : ℝ => (s + r * σ) ^ 2 * Ψ ((s + r * σ)⁻¹ • (ξ + r • η)) := by
    funext r
    exact homogeneousDensity_two Ψ _ _
  rw [hrw]
  refine hprod.congr_deriv ?_
  rw [homogeneousValueDerivative_two, homogeneousFlux_two]
  simp only [inner_add_right, real_inner_smul_right, real_inner_smul_left]
  field_simp
  ring

/-- **The derivative of the entropy potential along a line.** -/
theorem hasDerivAt_entropyPotential_line (κ : ℝ) (s σ : ℝ) {τ : ℝ} (hpos : 0 < s + τ * σ) :
    HasDerivAt (fun r : ℝ => Korevaar.entropyPotential 2 κ (s + r * σ))
      (σ * deriv (Korevaar.entropyPotential 2 κ) (s + τ * σ)) τ := by
  have hA : HasDerivAt (fun r : ℝ => s + r * σ) σ τ := by
    simpa using ((hasDerivAt_id τ).mul_const σ).const_add s
  have hP := Korevaar.hasDerivAt_entropyPotential (p := 2) (κ := κ) two_ne_zero hpos
  have h := hP.comp τ hA
  have hcomp : (Korevaar.entropyPotential 2 κ ∘ fun r : ℝ => s + r * σ)
      = fun r : ℝ => Korevaar.entropyPotential 2 κ (s + r * σ) := rfl
  rw [hcomp] at h
  refine h.congr_deriv ?_
  rw [hP.deriv]
  ring

end Komlos.Literature.Regularized
