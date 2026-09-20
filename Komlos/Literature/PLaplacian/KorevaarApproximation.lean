import Komlos.Literature.PLaplacian.KorevaarMaxPrinciple
import Komlos.Literature.PLaplacian.KorevaarNonlinearMaximum

/-!
# Global concavity for strict-reaction approximations

The pointwise nonlinear maximum lemma becomes a global convexity theorem once the
boundary-pair estimate gives attainment. This applies at critical points as well:
the regularized flux and gradient must have actual derivatives there.

This supplies an endpoint for a regularized-minimizer construction. No existence,
regularity, convergence, or boundary estimate for those minimizers is asserted here.
The entropy transformation at the end explains how a positive affine reaction can
arise from a perturbation of the original eigenfunction equation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Korevaar

variable {d : ℕ}

/-- A classical equation with a differentiable elliptic flux and an affine reaction
in the value. The derivative assumptions include points where the gradient vanishes. -/
structure IsSmoothAffineReactionSolution (Ω : Set (Euc d))
    (fluxA : Euc d → Euc d) (reaction v : Euc d → ℝ) (κ : ℝ) : Prop where
  differentiable : DifferentiableOn ℝ v Ω
  gradient_differentiable : DifferentiableOn ℝ (gradient v) Ω
  elliptic : ∀ x ∈ Ω, ∃ A : Euc d →L[ℝ] Euc d,
    HasFDerivAt fluxA A (gradient v x) ∧
      (∀ ξ η : Euc d, ⟪A ξ, η⟫ = ⟪ξ, A η⟫) ∧ (∀ ξ : Euc d, 0 ≤ ⟪A ξ, ξ⟫)
  equation : ∀ x ∈ Ω, divergence (fun z => fluxA (gradient v z)) x =
    κ * v x + reaction (gradient v x)

/-- The local two-point maximum lemma applies throughout an open convex domain
to an actual smooth affine-reaction solution, including at critical maxima. -/
theorem IsSmoothAffineReactionSolution.concavityFn_nonpos_of_isLocalMax
    {Ω : Set (Euc d)} {fluxA : Euc d → Euc d} {reaction v : Euc d → ℝ} {κ : ℝ}
    (hsol : IsSmoothAffineReactionSolution Ω fluxA reaction v κ) (hκ : 0 < κ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) {x y : Euc d} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y)) :
    concavityFn v x y ≤ 0 := by
  have hm : midpoint ℝ x y ∈ Ω := hconv.midpoint_mem hx hy
  have hd : ∀ a ∈ Ω, ∀ᶠ z in 𝓝 a, DifferentiableAt ℝ v z := by
    intro a ha
    filter_upwards [hΩ.mem_nhds ha] with z hz
    exact hsol.differentiable.differentiableAt (hΩ.mem_nhds hz)
  have hH : ∀ a ∈ Ω, HasFDerivAt (gradient v) (fderiv ℝ (gradient v) a) a :=
    fun a ha => (hsol.gradient_differentiable.differentiableAt (hΩ.mem_nhds ha)).hasFDerivAt
  obtain ⟨A, hA, hAs, hA0⟩ := hsol.elliptic x hx
  exact concavityFn_nonpos_of_isLocalMax_of_affine_reaction hκ
    (hd x hx) (hd y hy) (hd _ hm) (hH x hx) (hH y hy) (hH _ hm)
    hA hAs hA0 hmax (hsol.equation x hx) (hsol.equation y hy) (hsol.equation _ hm)

/-- Global convexity of the negative logarithm of a positive strict-reaction solution.
The boundary hypothesis is the epsilon formulation needed by the proved attainment
theorem; the interior input is the actual PDE rather than a concavity hypothesis. -/
theorem convexOn_neg_log_of_affine_reaction {K : Set (Euc d)} (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hzero : ∀ x, x ∉ K → φ x = 0)
    (hpos : ∀ x ∈ interior K, 0 < φ x)
    {fluxA : Euc d → Euc d} {reaction : Euc d → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hsol : IsSmoothAffineReactionSolution (interior K) fluxA reaction
      (fun x => -Real.log (φ x)) κ)
    (hbdry : ∀ x₀ ∈ frontier K, ∀ y₀ ∈ frontier K, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ q in 𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d),
        concavityFn (fun z => -Real.log (φ z)) q.1 q.2 < ε) :
    ConvexOn ℝ (interior K) (fun x => -Real.log (φ x)) := by
  have hconv : Convex ℝ (interior K) := hK.convex.interior
  refine convexOn_of_concavityFn_nonpos hconv
    ((hφc.continuousOn.log fun x hx => (hpos x hx).ne').neg) ?_
  intro x hx y hy
  by_contra hC
  have hCpos : 0 < concavityFn (fun z => -Real.log (φ z)) x y := not_le.1 hC
  obtain ⟨q, hq, hmax⟩ := exists_isMaxOn_concavityFn hK hφc hzero hpos hx hy
    (fun x₀ hx₀ y₀ hy₀ => hbdry x₀ hx₀ y₀ hy₀ _ hCpos)
  have hloc : IsLocalMax
      (fun z : Euc d × Euc d => concavityFn (fun w => -Real.log (φ w)) z.1 z.2) q := by
    filter_upwards [(isOpen_interior.prod isOpen_interior).mem_nhds hq] with z hz
    exact isMaxOn_iff.1 hmax z hz
  have hnonpos := hsol.concavityFn_nonpos_of_isLocalMax hκ isOpen_interior hconv hq.1 hq.2 hloc
  have hle := isMaxOn_iff.1 hmax (x, y) (show (x, y) ∈ interior K ×ˢ interior K from ⟨hx, hy⟩)
  exact (not_lt_of_ge (hle.trans hnonpos)) hCpos

/-- Pointwise limits of positive strict-reaction approximations have convex negative
logarithm. The flux, reaction, and positive affine coefficient may vary with the
approximation index; in particular the coefficient may tend to zero. The hypotheses
ask for the PDE and its boundary estimate for each approximant, not its concavity. -/
theorem convexOn_neg_log_of_tendsto_affine_reaction {K : Set (Euc d)} (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} {φn : ℕ → Euc d → ℝ}
    (hcont : ∀ n, Continuous (φn n)) (hzero : ∀ n x, x ∉ K → φn n x = 0)
    (hpos : ∀ n x, x ∈ interior K → 0 < φn n x)
    {fluxA : ℕ → Euc d → Euc d} {reaction : ℕ → Euc d → ℝ} {κ : ℕ → ℝ}
    (hκ : ∀ n, 0 < κ n)
    (hsol : ∀ n, IsSmoothAffineReactionSolution (interior K) (fluxA n) (reaction n)
      (fun x => -Real.log (φn n x)) (κ n))
    (hbdry : ∀ n, ∀ x₀ ∈ frontier K, ∀ y₀ ∈ frontier K, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ q in 𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d),
        concavityFn (fun z => -Real.log (φn n z)) q.1 q.2 < ε)
    (hlim : ∀ x ∈ interior K, Tendsto (fun n => φn n x) atTop (𝓝 (φ x)))
    (hφpos : ∀ x ∈ interior K, 0 < φ x) :
    ConvexOn ℝ (interior K) (fun x => -Real.log (φ x)) := by
  have hconv : Convex ℝ (interior K) := hK.convex.interior
  have hcn : ∀ n, ConvexOn ℝ (interior K) (fun x => -Real.log (φn n x)) := fun n =>
    convexOn_neg_log_of_affine_reaction hK (hcont n) (hzero n) (hpos n) (hκ n)
      (hsol n) (hbdry n)
  have hlog : ∀ x ∈ interior K,
      Tendsto (fun n => -Real.log (φn n x)) atTop (𝓝 (-Real.log (φ x))) :=
    fun x hx => ((hlim x hx).log (hφpos x hx).ne').neg
  refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
  have hm : a • x + b • y ∈ interior K := hconv hx hy ha hb hab
  simp only [smul_eq_mul]
  refine le_of_tendsto_of_tendsto (hlog _ hm)
    (((hlog x hx).const_mul a).add ((hlog y hy).const_mul b)) ?_
  exact Filter.Eventually.of_forall fun n => by
    simpa only [smul_eq_mul] using (hcn n).2 hx hy ha hb hab

/-- The entropy perturbation of the eigenfunction reaction produces a positive
affine term in the logarithmic equation. This is only a transformed PDE identity;
it does not construct a solution or regularize a critical gradient. -/
theorem divergence_flux_gradient_neg_log_entropy {p : ℝ} (hp : 1 < p)
    {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {φ : Euc d → ℝ} {x : Euc d} {lam κ : ℝ}
    (hpos : ∀ᶠ y in 𝓝 x, 0 < φ y)
    (hv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => -Real.log (φ y)) y)
    (hv' : DifferentiableAt ℝ (gradient fun y => -Real.log (φ y)) x)
    (hx' : gradient (fun y => -Real.log (φ y)) x ≠ 0)
    (hstrong : divergence (fun y => flux p F (gradient φ y)) x +
      (lam - κ * Real.log (φ x)) * φ x ^ (p - 1) = 0) :
    divergence (fun y => flux p F (gradient (fun y => -Real.log (φ y)) y)) x =
      κ * (-Real.log (φ x)) + (lam + (p - 1) * F (gradient (fun y => -Real.log (φ y)) x) ^ p) := by
  have h := divergence_flux_gradient_neg_log hp hF hpos hv hv' hx' hstrong
  rw [h]
  ring

end Komlos.Literature.Korevaar
