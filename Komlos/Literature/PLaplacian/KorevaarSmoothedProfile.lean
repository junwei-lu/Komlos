import Komlos.Literature.PLaplacian.KorevaarEntropy
import Komlos.Literature.Sobolev.Mollify

/-!
# Smooth convex profiles for the entropy regularization

Convolution smooths the entire kinetic profile, including the critical gradient.
It preserves convexity under a nonnegative kernel and evenness under an even
kernel. This supplies actual differentiable elliptic fluxes for the entropy
Euler–Lagrange transformation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Korevaar

variable {d : ℕ}

/-- Convolution written with the kernel at the integration variable. -/
theorem mollifyWith_eq_kernel_integral (ρ Φ : Euc d → ℝ) (x : Euc d) :
    mollifyWith ρ Φ x = ∫ y, ρ y * Φ (x - y) := by
  rw [mollifyWith_eq_convolution, convolution_def]
  rfl

/-- Mollification by a nonnegative compactly supported kernel preserves convexity. -/
theorem convexOn_mollifyWith {ρ Φ : Euc d → ℝ} (hρ : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hΦ : Continuous Φ) (hconv : ConvexOn ℝ univ Φ) :
    ConvexOn ℝ univ (mollifyWith ρ Φ) := by
  have hi : ∀ x : Euc d, Integrable (fun y => ρ y * Φ (x - y)) := fun x =>
    (hρ.mul (hΦ.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρs.mul_right
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [mollifyWith_eq_kernel_integral, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi x).const_mul a) ((hi y).const_mul b)]
  refine integral_mono (hi _) (((hi x).const_mul a).add ((hi y).const_mul b)) fun z => ?_
  have h := hconv.2 (mem_univ (x - z)) (mem_univ (y - z)) ha hb hab
  have heq : a • (x - z) + b • (y - z) = a • x + b • y - z := by
    have hz : a • z + b • z = z := by rw [← add_smul, hab, one_smul]
    calc a • (x - z) + b • (y - z) = a • x + b • y - (a • z + b • z) := by module
      _ = a • x + b • y - z := by rw [hz]
  rw [heq] at h
  simp only [smul_eq_mul] at h
  have hmul := mul_le_mul_of_nonneg_left h (hρ0 z)
  nlinarith

/-- An even kernel preserves evenness of a profile. -/
theorem mollifyWith_even {ρ Φ : Euc d → ℝ} (hρ : ∀ x, ρ (-x) = ρ x)
    (hΦ : ∀ x, Φ (-x) = Φ x) (x : Euc d) :
    mollifyWith ρ Φ (-x) = mollifyWith ρ Φ x := by
  rw [mollifyWith_eq_kernel_integral, mollifyWith_eq_kernel_integral]
  calc ∫ y, ρ y * Φ (-x - y) = ∫ y, ρ (-y) * Φ (-x - -y) :=
      (integral_neg_eq_self (fun y => ρ y * Φ (-x - y)) volume).symm
    _ = ∫ y, ρ y * Φ (x - y) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have heq : -x - -y = -(x - y) := by abel
      show ρ (-y) * Φ (-x - -y) = ρ y * Φ (x - y)
      rw [hρ, heq, hΦ]

/-- The smoothed anisotropic kinetic profile. The kernel may already carry its
scale parameter; it is not necessary to introduce a second scaling convention. -/
noncomputable def smoothedProfile (p : ℝ) (F ρ : Euc d → ℝ) : Euc d → ℝ :=
  mollifyWith ρ (fun q => F q ^ p / p)

/-- The mollified profile is smooth at every point, including the origin. -/
theorem contDiff_smoothedProfile {p : ℝ} (hp : 0 ≤ p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρs : HasCompactSupport ρ) : ContDiff ℝ ∞ (smoothedProfile p F ρ) := by
  exact contDiff_mollifyWith hρ hρs ((hF.continuous_rpow hp).div_const p).locallyIntegrable

/-- Convexity of the mollified kinetic profile. -/
theorem convexOn_smoothedProfile {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {ρ : Euc d → ℝ} (hρ : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) :
    ConvexOn ℝ univ (smoothedProfile p F ρ) := by
  have hp0 : 0 ≤ p := by linarith
  apply convexOn_mollifyWith hρ hρs hρ0 ((hF.continuous_rpow hp0).div_const p)
  refine ⟨convex_univ, fun x hx y hy a b ha hb hab => ?_⟩
  have h := (convexOn_rpow_of_isSmoothStrictNorm hF hp.le).2 hx hy ha hb hab
  have hd := div_le_div_of_nonneg_right h hp0
  simpa only [smul_eq_mul, add_div, mul_div_assoc] using hd

/-- Evenness of the mollified kinetic profile for a symmetric kernel. -/
theorem smoothedProfile_even (p : ℝ) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {ρ : Euc d → ℝ} (hρ : ∀ x, ρ (-x) = ρ x) (q : Euc d) :
    smoothedProfile p F ρ (-q) = smoothedProfile p F ρ q :=
  mollifyWith_even hρ (fun x => by rw [hF.even]) q

/-- The gradient of a differentiable even profile is odd. -/
theorem gradient_odd_of_even {Ψ : Euc d → ℝ} (hd : Differentiable ℝ Ψ)
    (heven : ∀ q, Ψ (-q) = Ψ q) (q : Euc d) : gradient Ψ (-q) = -gradient Ψ q := by
  have h : HasGradientAt (fun y => Ψ (-y)) (-gradient Ψ (-q)) q := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hcomp := (hd (-q)).hasFDerivAt.comp q (hasFDerivAt_id q).neg
    refine hcomp.congr_fderiv ?_
    ext η
    simp [InnerProductSpace.toDual_apply_apply, ← inner_gradient_left]
  have heq : (fun y => Ψ (-y)) = Ψ := funext heven
  rw [heq] at h
  simpa only [neg_neg] using congrArg Neg.neg h.gradient.symm

/-- Convexity makes the derivative of the gradient positive semidefinite wherever
that derivative exists. The proof uses monotonicity of derivatives along lines. -/
theorem inner_fderiv_gradient_nonneg_of_convex {Ψ : Euc d → ℝ}
    (hd : Differentiable ℝ Ψ) (hconv : ConvexOn ℝ univ Ψ)
    {q : Euc d} {H : Euc d →L[ℝ] Euc d} (hH : HasFDerivAt (gradient Ψ) H q) (ξ : Euc d) :
    0 ≤ ⟪H ξ, ξ⟫ := by
  let f : ℝ → ℝ := fun t => Ψ (q + t • ξ)
  have hf : ∀ t, HasDerivAt f ⟪gradient Ψ (q + t • ξ), ξ⟫ t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => q + s • ξ) ξ t := by
      simpa using ((hasDerivAt_id t).smul_const ξ).const_add q
    have h := (hasGradientAt_iff_hasFDerivAt.1 (hd (q + t • ξ)).hasGradientAt).comp_hasDerivAt t hline
    rwa [InnerProductSpace.toDual_apply_apply] at h
  have hfc : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
    have h := hconv.2 (mem_univ (q + s • ξ)) (mem_univ (q + t • ξ)) ha hb hab
    have heq : a • (q + s • ξ) + b • (q + t • ξ) = q + (a * s + b * t) • ξ := by
      have hq : a • q + b • q = q := by rw [← add_smul, hab, one_smul]
      calc a • (q + s • ξ) + b • (q + t • ξ) =
          (a • q + b • q) + (a * s + b * t) • ξ := by module
        _ = q + (a * s + b * t) • ξ := by rw [hq]
    simpa only [f, smul_eq_mul, heq] using h
  have hm : Monotone (deriv f) := fun s t hst =>
    hfc.monotoneOn_deriv (fun t _ => (hf t).differentiableAt) (mem_univ s) (mem_univ t) hst
  have heq : deriv f = fun t => ⟪gradient Ψ (q + t • ξ), ξ⟫ := funext fun t => (hf t).deriv
  rw [heq] at hm
  obtain ⟨_, hsecond⟩ := hasDerivAt_inner_gradient_line (Filter.Eventually.of_forall hd) hH ξ
  have hnonneg := hm.deriv_nonneg (x := 0)
  rwa [hsecond.deriv] at hnonneg

/-- A smooth convex profile supplies the exact elliptic-flux interface used by the
global strict-reaction theorem, at every gradient including zero. -/
theorem exists_elliptic_fderiv_gradient_of_contDiff_convex {Ψ : Euc d → ℝ}
    (hΨ : ContDiff ℝ 2 Ψ) (hconv : ConvexOn ℝ univ Ψ) (q : Euc d) :
    ∃ H : Euc d →L[ℝ] Euc d, HasFDerivAt (gradient Ψ) H q ∧
      (∀ ξ η : Euc d, ⟪H ξ, η⟫ = ⟪ξ, H η⟫) ∧ (∀ ξ : Euc d, 0 ≤ ⟪H ξ, ξ⟫) := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hgc : ContDiffOn ℝ 1 (gradient Ψ) univ := by
    have h := hΨ.contDiffOn.fderiv_of_isOpen (m := 1) isOpen_univ (by norm_num)
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h
  have hg : HasFDerivAt (gradient Ψ) (fderiv ℝ (gradient Ψ) q) q :=
    ((hgc.differentiableOn one_ne_zero).differentiableAt (isOpen_univ.mem_nhds (mem_univ q))).hasFDerivAt
  exact ⟨_, hg, inner_fderiv_gradient_comm (Filter.Eventually.of_forall hd) hg,
    inner_fderiv_gradient_nonneg_of_convex hd hconv hg⟩

end Komlos.Literature.Korevaar
