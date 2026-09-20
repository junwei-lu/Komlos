import Komlos.Literature.PLaplacian.RegularityChainRule
import Komlos.Literature.PLaplacian.RegularitySobolev

/-!
# Weak calculus for the interior regularity ladder

Auxiliary facts for `Komlos.Literature.PLaplacian.RegularityInterior` (the De Giorgi–Nash–Moser
chain for the first eigenfunction of the anisotropic `p`-Laplacian, towards Mosconi–Riey–Squassina
2024, Proposition 4.5; paper Appendix A, *Eigenfunction inputs*).

* `IsSmoothStrictNorm.euler_inner_gradient` — Euler's identity `⟪∇F(ξ), ξ⟫ = F(ξ)` for the
  `1`-homogeneous norm `F`; hence `⟪a(ξ), ξ⟫ = F(ξ)^p` (`inner_flux_self_eq_rpow`) and
  `|⟪a(ξ), ζ⟫| ≤ L F(ξ)^{p-1} ‖ζ‖` (`abs_inner_flux_le`) for the flux `a = flux p F`.
* `rpow_sub_one_mul_le_half_add` — the Young inequality `s^{p-1} t ≤ s^p/2 + 2^{p-1} t^p`.
* `HasWeakGradient.contDiff_mul` — the **weak product rule** `∇(ζ f) = ζ ∇f + f ∇ζ` for a smooth
  multiplier `ζ`; `MemW0.contDiff_mul` — `ζ f ∈ W₀^{1,p}(K)` when `ζ` and `∇ζ` are bounded.
* `gradient_pow_apply` — `∇(η^m) = m η^{m-1} ∇η`.

(The WangXia assembly files declare `IsSmoothStrictNorm.inner_gradient_self`, `inner_flux_self`
and `norm_flux_le`; the names here differ to avoid a clash, since those files import this one
transitively.)
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Generic-domain wrappers (lambda forms) -/

/-- `MemLp.add` with the sum written as a lambda (stated over a generic domain so that the
unification of `f + g` with `fun x => f x + g x` is cheap). -/
theorem memLp_add_fun {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {q : ℝ≥0∞} {f g : α → E} (hf : MemLp f q μ) (hg : MemLp g q μ) :
    MemLp (fun x => f x + g x) q μ :=
  hf.add hg

/-- `LocallyIntegrable.add` with the sum written as a lambda. -/
theorem locallyIntegrable_add_fun {α E : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {f g : α → E} (hf : LocallyIntegrable f μ)
    (hg : LocallyIntegrable g μ) : LocallyIntegrable (fun x => f x + g x) μ :=
  hf.add hg

/-! ### Euler's identity and the flux -/

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- **Euler's identity** for the `1`-homogeneous norm `F`: `⟪∇F(ξ), ξ⟫ = F(ξ)`. -/
theorem euler_inner_gradient (ξ : Euc d) : ⟪gradient F ξ, ξ⟫ = F ξ := by
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
theorem inner_flux_self_eq_rpow {p : ℝ} (hp : 1 < p) (ξ : Euc d) :
    ⟪flux p F ξ, ξ⟫ = F ξ ^ p := by
  rw [flux, real_inner_smul_left, hF.euler_inner_gradient]
  rcases eq_or_ne (F ξ) 0 with h | h
  · rw [h, Real.zero_rpow (by linarith : p - 1 ≠ 0), Real.zero_rpow (by linarith : p ≠ 0),
      mul_zero]
  · rw [← Real.rpow_add_one h, sub_add_cancel]

/-- `‖a(ξ)‖ ≤ L F(ξ)^{p-1}` when `‖∇F‖ ≤ L`. -/
theorem norm_flux_le_mul_rpow {p : ℝ} {L : ℝ} (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) (ξ : Euc d) :
    ‖flux p F ξ‖ ≤ L * F ξ ^ (p - 1) := by
  rw [flux, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (hF.nonneg ξ) _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hL ξ) (Real.rpow_nonneg (hF.nonneg ξ) _)

/-- `|⟪a(ξ), ζ⟫| ≤ L F(ξ)^{p-1} ‖ζ‖` when `‖∇F‖ ≤ L`. -/
theorem abs_inner_flux_le {p : ℝ} {L : ℝ} (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) (ξ ζ : Euc d) :
    |⟪flux p F ξ, ζ⟫| ≤ L * F ξ ^ (p - 1) * ‖ζ‖ :=
  (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hF.norm_flux_le_mul_rpow hL ξ) (norm_nonneg _))

end IsSmoothStrictNorm

/-! ### A Young inequality -/

/-- **Young's inequality** in the form used for the Caccioppoli absorption:
`s^{p-1} t ≤ s^p/2 + 2^{p-1} t^p` for `s, t ≥ 0` and `p > 1`. -/
theorem rpow_sub_one_mul_le_half_add {p : ℝ} (hp : 1 < p) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s ^ (p - 1) * t ≤ s ^ p / 2 + 2 ^ (p - 1) * t ^ p := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hpow : ∀ r : ℝ, 0 ≤ r → r ^ (p - 1) * r = r ^ p := fun r hr => by
    rw [← Real.rpow_add_one' hr (ne_of_gt (by linarith)), sub_add_cancel]
  rcases le_total s (2 * t) with h | h
  · have h1 : s ^ (p - 1) * t ≤ (2 * t) ^ (p - 1) * t :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs h hp1) ht
    have h2 : (2 * t) ^ (p - 1) * t = 2 ^ (p - 1) * t ^ p := by
      rw [Real.mul_rpow (by norm_num) ht, mul_assoc, hpow t ht]
    have h3 : 0 ≤ s ^ p / 2 := by positivity
    linarith
  · have h1 : s ^ (p - 1) * t ≤ s ^ (p - 1) * (s / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hs _)
    have h2 : s ^ (p - 1) * (s / 2) = s ^ p / 2 := by
      rw [← mul_div_assoc, hpow s hs]
    have h3 : 0 ≤ 2 ^ (p - 1) * t ^ p := by positivity
    linarith

/-! ### The weak product rule -/

/-- **Weak product rule**: if `g` is a weak gradient of `f` and `ζ` is smooth, then
`ζ ∇f + f ∇ζ` is a weak gradient of `ζ f` (test the identity for `f` with `ζ ψ`). -/
theorem HasWeakGradient.contDiff_mul {f : Euc d → ℝ} {g : Euc d → Euc d}
    (hg : HasWeakGradient f g) {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) :
    HasWeakGradient (fun x => ζ x * f x) (fun x => ζ x • g x + f x • gradient ζ x) where
  locallyIntegrable := hg.locallyIntegrable.continuous_mul hζ.continuous
  locallyIntegrable_grad :=
    locallyIntegrable_add_fun (hg.locallyIntegrable_grad.continuous_smul hζ.continuous)
      (hg.locallyIntegrable.smul_continuous (continuous_gradient (hζ.of_le (by simp))))
  integral_mul_fderiv ψ hψ hψs v := by
    have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hχ : ContDiff ℝ ∞ (fun x => ζ x * ψ x) := hζ.mul hψ
    have hχs : HasCompactSupport (fun x => ζ x * ψ x) := hψs.mul_left
    have key := hg.integral_mul_fderiv _ hχ hχs v
    have hder : ∀ x, fderiv ℝ (fun x => ζ x * ψ x) x v =
        ζ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ ζ x v := by
      intro x
      have h : HasFDerivAt (fun x => ζ x * ψ x) (ζ x • fderiv ℝ ψ x + ψ x • fderiv ℝ ζ x) x :=
        (hζ1.differentiable one_ne_zero x).hasFDerivAt.mul
          (hψ1.differentiable one_ne_zero x).hasFDerivAt
      rw [h.fderiv]
      rfl
    have hDψ : Continuous fun x => fderiv ℝ ψ x v :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hDζ : Continuous fun x => fderiv ℝ ζ x v :=
      (hζ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hsDψ : HasCompactSupport fun x => fderiv ℝ ψ x v :=
      (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
    have i1 : Integrable fun x => f x * (ζ x * fderiv ℝ ψ x v) := by
      refine (hg.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (hζ.continuous.mul hDψ) hsDψ.mul_left).congr (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have i2 : Integrable fun x => f x * (ψ x * fderiv ℝ ζ x v) := by
      refine (hg.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (hψ.continuous.mul hDζ) hψs.mul_right).congr (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have i3 : Integrable fun x => inner ℝ (g x) v * (ζ x * ψ x) := by
      refine (Integrable.const_inner (𝕜 := ℝ) v
        (hg.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport hχ.continuous
          hχs)).congr (Eventually.of_forall fun x => ?_)
      simp only [inner_smul_right]
      rw [real_inner_comm, mul_comm]
    have e1 : ∫ x, f x * fderiv ℝ (fun x => ζ x * ψ x) x v =
        (∫ x, f x * (ζ x * fderiv ℝ ψ x v)) + ∫ x, f x * (ψ x * fderiv ℝ ζ x v) := by
      rw [← integral_add i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hder]
      ring
    have e2 : ∫ x, inner ℝ (ζ x • g x + f x • gradient ζ x) v * ψ x =
        (∫ x, inner ℝ (g x) v * (ζ x * ψ x)) + ∫ x, f x * (ψ x * fderiv ℝ ζ x v) := by
      rw [← integral_add i3 i2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [inner_add_left, real_inner_smul_left, fderiv_apply_eq_inner_gradient]
      ring
    have e3 : ∫ x, ζ x * f x * fderiv ℝ ψ x v = ∫ x, f x * (ζ x * fderiv ℝ ψ x v) :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    show ∫ x, ζ x * f x * fderiv ℝ ψ x v = -∫ x, inner ℝ (ζ x • g x + f x • gradient ζ x) v * ψ x
    rw [e3, e2]
    rw [e1] at key
    linarith

/-- **`W₀^{1,p}` is stable under multiplication by a smooth function with bounded values and
bounded gradient**, with the product-rule weak gradient. -/
theorem MemW0.contDiff_mul {p : ℝ} {K : Set (Euc d)} {f : Euc d → ℝ} (hf : MemW0 p K f)
    {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) {A B : ℝ} (hA : ∀ x, |ζ x| ≤ A)
    (hB : ∀ x, ‖gradient ζ x‖ ≤ B) :
    MemW0 p K (fun x => ζ x * f x) ∧
      weakGrad (fun x => ζ x * f x) =ᵐ[volume]
        fun x => ζ x • weakGrad f x + f x • gradient ζ x := by
  have hwg := hf.hasWeakGradient.contDiff_mul hζ
  have hζm : AEStronglyMeasurable ζ volume := hζ.continuous.aestronglyMeasurable
  have hGm : AEStronglyMeasurable (gradient ζ) volume :=
    (continuous_gradient (hζ.of_le (by simp))).aestronglyMeasurable
  refine ⟨⟨?_, ?_, ⟨_, hwg, ?_⟩⟩, hwg.weakGrad_ae_eq⟩
  · refine hf.memLp.of_le_mul (c := A) (hζm.mul hf.memLp.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)
  · filter_upwards [hf.ae_eq_zero] with x hx hxK
    rw [hx hxK, mul_zero]
  · refine memLp_add_fun ?_ ?_
    · refine hf.memLp_weakGrad.of_le_mul (c := A)
        (hζm.smul hf.memLp_weakGrad.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)
    · refine hf.memLp.of_le_mul (c := B) (hf.memLp.aestronglyMeasurable.smul hGm)
        (Eventually.of_forall fun x => ?_)
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

/-- `∇(η^m) = m η^{m-1} ∇η` for differentiable `η`. -/
theorem gradient_pow_apply {η : Euc d → ℝ} {x : Euc d} (hη : DifferentiableAt ℝ η x) (m : ℕ) :
    gradient (fun y => η y ^ m) x = ((m : ℝ) * η x ^ (m - 1)) • gradient η x := by
  refine gradient_eq_smul_of_hasFDerivAt ?_
  have h := hη.hasFDerivAt.pow m
  simpa only [nsmul_eq_mul] using h

/-! ### The inputs of the Moser iteration

The chain rule `memW0_comp` is proved in `Komlos.Literature.PLaplacian.RegularityChainRule` and the
Sobolev inequality `sobolev_inequality` in `Komlos.Literature.PLaplacian.RegularitySobolev`. -/

end Komlos.Literature
