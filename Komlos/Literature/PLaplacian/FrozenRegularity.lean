import Komlos.Literature.PLaplacian.FrozenDirichlet
import Komlos.Literature.PLaplacian.WeylGlobal
import Komlos.Literature.Sobolev.Density

/-!
# Sobolev inputs for the frozen Dirichlet comparison

The variational replacement is an `L²` field.  This file supplies its distributional
interpretation, without assuming continuity at the boundary of the comparison ball.
The energy estimate in `FrozenComparison` already accepts this Sobolev regularity.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-- The weak gradient of a Sobolev function supported in a closed set vanishes almost
everywhere outside that set.  Local uniqueness of weak gradients proves this directly. -/
theorem MemW0.weakGrad_eq_zero_of_isClosed {p : ℝ} {K : Set (Euc d)}
    {ψ : Euc d → ℝ} (hψ : MemW0 p K ψ) (hK : IsClosed K) :
    ∀ᵐ y, y ∉ K → weakGrad ψ y = 0 := by
  have h := weakGrad_ae_eq_gradient_of_ae_eq hψ.hasWeakGradient
    (v := fun _ => (0 : ℝ)) contDiff_const hK.isOpen_compl hψ.ae_eq_zero
  filter_upwards [h] with y hy hyK
  simpa using hy hyK

/-- A compactly supported smooth function is a Sobolev test function even when it is
identically zero (unlike `IsTestFn`, which excludes zero for the Rayleigh quotient). -/
theorem memW0_of_contDiff_supported {K : Set (Euc d)} {ζ : Euc d → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ) (hζK : tsupport ζ ⊆ K) (p : ℝ) :
    MemW0 p K ζ where
  memLp := hζ.continuous.memLp_of_hasCompactSupport hζs
  ae_eq_zero := Eventually.of_forall fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hz => hy (hζK hz)
  exists_weakGradient :=
    ⟨gradient ζ, hasWeakGradient_gradient (hζ.of_le (by simp)) hζs,
      (continuous_gradient (hζ.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_gradient hζs)⟩

/-- The Sobolev frozen replacement gives a genuine distributional solution for
`u = w - ψ` on the comparison ball (Gilbarg–Trudinger, Theorem 8.32, step 2).
The global `C¹` and support hypotheses on `w` are obtained by an interior cutoff in
applications, and carry no boundary assumption on `ψ`. -/
theorem exists_frozen_weak_replacement (hd : 0 < d)
    {A₀ : Euc d →L[ℝ] Euc d} {μ Λ : ℝ}
    (hμ : 0 < μ) (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    (hA : ‖A₀‖ ≤ Λ) (hsymm : ∀ ξ η : Euc d, ⟪A₀ ξ, η⟫ = ⟪A₀ η, ξ⟫)
    {c : Euc d} {s : ℝ} (hs : 0 ≤ s) {w : Euc d → ℝ}
    (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w) :
    ∃ ψ : Euc d → ℝ, MemW0 2 (Metric.closedBall c s) ψ ∧
      HasWeakGradient (fun y => w y - ψ y) (fun y => gradient w y - weakGrad ψ y) ∧
      MemLp (fun y => gradient w y - weakGrad ψ y) 2 ∧
      (∀ ζ : Euc d → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ Metric.ball c s →
        ∫ y, ⟪A₀ (gradient w y - weakGrad ψ y), gradient ζ y⟫ = 0) ∧
      ∀ ζ : Euc d → ℝ, MemW0 2 (Metric.closedBall c s) ζ →
        ∫ y, ⟪A₀ (gradient w y - weakGrad ψ y), weakGrad ζ y⟫ = 0 := by
  have hG : MemLp (gradient w) (ENNReal.ofReal 2) :=
    (continuous_gradient hw).memLp_of_hasCompactSupport (hasCompactSupport_gradient hws)
  obtain ⟨ψ, hψW, hH, hsol⟩ :=
    FrozenDirichlet.exists_frozen_replacement_field hd hμ hell hA hsymm hs hG
  have hu : HasWeakGradient (fun y => w y - ψ y)
      (fun y => gradient w y - weakGrad ψ y) := by
    convert (hasWeakGradient_gradient hw hws).add (hψW.hasWeakGradient.smul (-1)) using 1 <;>
      ext y <;> simp [sub_eq_add_neg]
  refine ⟨ψ, hψW, hu, ?_, ?_, hsol⟩
  · simpa using hH
  · intro ζ hζ hζs hζB
    have hζW := memW0_of_contDiff_supported hζ hζs
      (hζB.trans Metric.ball_subset_closedBall) 2
    have heq := (hasWeakGradient_gradient (hζ.of_le (by simp)) hζs).weakGrad_ae_eq
    have hzero := hsol ζ hζW
    rw [← hzero]
    apply integral_congr_ae
    filter_upwards [heq] with y hy
    rw [hy]

/-- Mixed derivatives commute when the first function has only a weak gradient;
all second derivatives fall on the smooth test function. -/
theorem HasWeakGradient.integral_inner_mul_fderiv_comm {u : Euc d → ℝ}
    {G : Euc d → Euc d} (hu : HasWeakGradient u G) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (e f : Euc d) :
    ∫ y, ⟪G y, e⟫ * fderiv ℝ ψ y f = ∫ y, ⟪G y, f⟫ * fderiv ℝ ψ y e := by
  have hψd : Differentiable ℝ ψ := (contDiff_infty_iff_fderiv.1 hψ).1
  have hψD : ContDiff ℝ ∞ (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψ).2
  have hψDd : Differentiable ℝ (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψD).1
  have key : ∀ v w : Euc d, ∫ y, ⟪G y, v⟫ * fderiv ℝ ψ y w
      = -∫ y, u y * fderiv ℝ (fderiv ℝ ψ) y v w := by
    intro v w
    have hc : ContDiff ℝ ∞ fun z : Euc d => fderiv ℝ ψ z w :=
      hψD.clm_apply (contDiff_const (c := w))
    have h := hu.integral_mul_fderiv _ hc (hψs.fderiv_apply ℝ w) v
    simp only [fderiv_fderiv_apply_const hψDd w v] at h
    linarith [h]
  have hsymm : ∀ y : Euc d,
      fderiv ℝ (fderiv ℝ ψ) y e f = fderiv ℝ (fderiv ℝ ψ) y f e := fun y =>
    second_derivative_symmetric (fun z => (hψd z).hasFDerivAt) (hψDd y).hasFDerivAt e f
  rw [key e f, key f e]
  simp only [hsymm]

/-- A constant antisymmetric matrix annihilates the divergence of a weak gradient.
This extends the corresponding `C¹` result to the Sobolev frozen replacement. -/
theorem HasWeakGradient.integral_inner_antisymm_eq_zero {N : Euc d →L[ℝ] Euc d}
    (hN : ∀ p q : Euc d, ⟪N p, q⟫ = -⟪p, N q⟫) {u : Euc d → ℝ} {G : Euc d → Euc d}
    (hu : HasWeakGradient u G)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) :
    ∫ y, ⟪N (G y), gradient ψ y⟫ = 0 := by
  obtain ⟨b, -⟩ : ∃ b : OrthonormalBasis (Fin d) ℝ (Euc d), True :=
    ⟨EuclideanSpace.basisFun (Fin d) ℝ, trivial⟩
  have hψDc : Continuous (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψ).2.continuous
  -- every product of a directional derivative of `u` with one of `ψ` is integrable
  have hint : ∀ v w : Euc d,
      Integrable (fun y : Euc d => ⟪G y, v⟫ * fderiv ℝ ψ y w) volume := by
    intro v w
    have hi := hu.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport
      (hψDc.clm_apply continuous_const) (hψs.fderiv_apply ℝ w)
    simpa only [inner_smul_left, RCLike.conj_to_real, mul_comm] using
      hi.inner_const (𝕜 := ℝ) v
  -- expand `⟪N ∇u, ∇ψ⟫` in the orthonormal basis, moving `N` onto the basis vector
  have hexp1 : ∀ y : Euc d, -⟪N (G y), gradient ψ y⟫
      = ∑ i : Fin d, ⟪G y, N (b i)⟫ * fderiv ℝ ψ y (b i) := by
    intro y
    rw [← b.sum_inner_mul_inner (N (G y)) (gradient ψ y), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hN (G y) (b i), real_inner_comm (gradient ψ y) (b i),
      fderiv_apply_eq_inner_gradient ψ y (b i)]
    ring
  -- the same expansion after moving `N` onto `∇ψ` instead: the two signs differ
  have hexp2 : ∀ y : Euc d, ⟪N (G y), gradient ψ y⟫
      = ∑ i : Fin d, ⟪G y, b i⟫ * fderiv ℝ ψ y (N (b i)) := by
    intro y
    have hswap : ⟪N (G y), gradient ψ y⟫ = -⟪N (gradient ψ y), G y⟫ := by
      rw [hN (gradient ψ y) (G y), neg_neg]
      exact real_inner_comm (gradient ψ y) (N (G y))
    rw [hswap, ← b.sum_inner_mul_inner (N (gradient ψ y)) (G y),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hN (gradient ψ y) (b i), real_inner_comm (G y) (b i),
      fderiv_apply_eq_inner_gradient ψ y (N (b i))]
    ring
  have hJ1 : (∫ y, ⟪N (G y), gradient ψ y⟫)
      = ∑ i : Fin d, ∫ y, ⟪G y, b i⟫ * fderiv ℝ ψ y (N (b i)) := by
    simp only [hexp2]
    exact integral_finsetSum Finset.univ fun i _ => hint (b i) (N (b i))
  have hJ2 : -(∫ y, ⟪N (G y), gradient ψ y⟫)
      = ∑ i : Fin d, ∫ y, ⟪G y, N (b i)⟫ * fderiv ℝ ψ y (b i) := by
    have hneg : -(∫ y, ⟪N (G y), gradient ψ y⟫)
        = ∫ y, -⟪N (G y), gradient ψ y⟫ :=
      (integral_neg fun y : Euc d => ⟪N (G y), gradient ψ y⟫).symm
    rw [hneg]
    simp only [hexp1]
    exact integral_finsetSum Finset.univ fun i _ => hint (N (b i)) (b i)
  -- the two sums agree term by term, by the symmetry of the mixed integrals
  have hsum : ∑ i : Fin d, ∫ y, ⟪G y, N (b i)⟫ * fderiv ℝ ψ y (b i)
      = ∑ i : Fin d, ∫ y, ⟪G y, b i⟫ * fderiv ℝ ψ y (N (b i)) :=
    Finset.sum_congr rfl fun i _ =>
      hu.integral_inner_mul_fderiv_comm hψ hψs (N (b i)) (b i)
  linarith [hJ1, hJ2, hsum]

/-- The antisymmetric cancellation remains valid for compactly supported `W₀^{1,2}`
test functions, by the proved smooth-test density theorem. -/
theorem HasWeakGradient.integral_inner_antisymm_weakGrad_eq_zero
    {N : Euc d →L[ℝ] Euc d} (hN : ∀ p q : Euc d, ⟪N p, q⟫ = -⟪p, N q⟫)
    {u : Euc d → ℝ} {G : Euc d → Euc d} (hu : HasWeakGradient u G) (hG : MemLp G 2)
    {K : Set (Euc d)} (hK : IsCompact K) {ζ : Euc d → ℝ} (hζ : MemW0 2 K ζ) :
    ∫ y, ⟪N (G y), weakGrad ζ y⟫ = 0 := by
  have hweak : ∀ χ : Euc d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Set.univ →
      ∫ y, ⟪N (G y), gradient χ y⟫ = ∫ y, (0 : ℝ) * χ y := by
    intro χ hχ hχs _
    simpa using hu.integral_inner_antisymm_eq_zero hN hχ hχs
  have h := integral_inner_weakGrad_eq_of_memW0_two isOpen_univ
    (Φ := fun y => N (G y)) (by simpa [Function.comp_def] using N.comp_memLp' hG)
    (g := fun _ => (0 : ℝ)) (by simp) hweak hK (subset_univ K) hζ
    (hζ.weakGrad_eq_zero_of_isClosed hK.isClosed)
  simpa using h

/-- The weak divergence-form pairing only sees the symmetric part of a constant
matrix, including when both gradients are Sobolev gradients. -/
theorem HasWeakGradient.integral_inner_symPart_weakGrad_eq
    (A : Euc d →L[ℝ] Euc d) {u : Euc d → ℝ} {G : Euc d → Euc d}
    (hu : HasWeakGradient u G) (hG : MemLp G 2)
    {K : Set (Euc d)} (hK : IsCompact K) {ζ : Euc d → ℝ} (hζ : MemW0 2 K ζ) :
    ∫ y, ⟪symPart A (G y), weakGrad ζ y⟫ = ∫ y, ⟪A (G y), weakGrad ζ y⟫ := by
  have hζG : MemLp (weakGrad ζ) 2 := by simpa using hζ.memLp_weakGrad
  have hsplit : ∀ y : Euc d, ⟪A (G y), weakGrad ζ y⟫ =
      ⟪symPart A (G y), weakGrad ζ y⟫ + ⟪antisymPart A (G y), weakGrad ζ y⟫ := by
    intro y
    rw [← inner_add_left, symPart_add_antisymPart]
  have hSi : Integrable (fun y => ⟪symPart A (G y), weakGrad ζ y⟫) := by
    simpa only [Function.comp_def] using
      integrable_inner_of_memLp_two ((symPart A).comp_memLp' hG) hζG
  have hNi : Integrable (fun y => ⟪antisymPart A (G y), weakGrad ζ y⟫) := by
    simpa only [Function.comp_def] using
      integrable_inner_of_memLp_two ((antisymPart A).comp_memLp' hG) hζG
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hSi hNi,
    hu.integral_inner_antisymm_weakGrad_eq_zero (antisymPart_antisymm A) hG hK hζ,
    add_zero]

/-- A frozen Dirichlet replacement is smooth in the comparison ball and has an `L²`
gradient up to its boundary.  This is the precise regularity needed for the freezing energy
estimate; no classical derivative is prescribed on the boundary sphere.
(Gilbarg–Trudinger, Theorem 8.32, step 2.) -/
theorem exists_frozen_smooth_replacement (hd : 0 < d)
    {A₀ : Euc d →L[ℝ] Euc d} {μ Λ : ℝ}
    (hμ : 0 < μ) (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    (hA : ‖A₀‖ ≤ Λ) {c : Euc d} {s : ℝ} (hs : 0 < s) {w : Euc d → ℝ}
    (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w) :
    ∃ h ψ : Euc d → ℝ, ContDiffOn ℝ ∞ h (Metric.ball c s) ∧
      MemLp (gradient h) 2 (volume.restrict (Metric.closedBall c s)) ∧
      MemW0 2 (Metric.closedBall c s) ψ ∧
      weakGrad ψ =ᵐ[volume] (Metric.closedBall c s).indicator
        (fun y => gradient w y - gradient h y) ∧
      (∀ ζ : Euc d → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ Metric.ball c s → ∫ y, ⟪A₀ (gradient h y), gradient ζ y⟫ = 0) ∧
      (∫ y, ⟪A₀ (gradient h y), weakGrad ψ y⟫) = 0 := by
  have hellS : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪symPart A₀ ζ, ζ⟫ := by
    intro ζ
    rw [symPart_inner_self]
    exact hell ζ
  have hsymm : ∀ ξ η : Euc d, ⟪symPart A₀ ξ, η⟫ = ⟪symPart A₀ η, ξ⟫ := by
    intro ξ η
    rw [symPart_symm, real_inner_comm ξ (symPart A₀ η)]
  obtain ⟨ψ, hψW, hu, hG, hsol, htest⟩ := exists_frozen_weak_replacement hd hμ hellS
    ((norm_symPart_le A₀).trans hA) hsymm hs.le hw hws
  obtain ⟨h, hh, _, hhgrad⟩ := exists_contDiffOn_ae_eq_gradient_of_weakSolution
    (symPart_symm A₀) hμ hellS Metric.isOpen_ball hu hsol
  have htestA : ∀ ζ : Euc d → ℝ, MemW0 2 (Metric.closedBall c s) ζ →
      ∫ y, ⟪A₀ (gradient w y - weakGrad ψ y), weakGrad ζ y⟫ = 0 := by
    intro ζ hζ
    rw [← hu.integral_inner_symPart_weakGrad_eq A₀ hG (isCompact_closedBall c s) hζ]
    exact htest ζ hζ
  have hnotSphere : ∀ᵐ y : Euc d, y ∉ Metric.sphere c s := by
    rw [ae_iff]
    simpa [Metric.sphere, dist_eq_norm] using Measure.addHaar_sphere_of_ne_zero (volume : Measure (Euc d)) c hs.ne'
  have hhgradClosed : ∀ᵐ y : Euc d, y ∈ Metric.closedBall c s →
      gradient w y - weakGrad ψ y = gradient h y := by
    filter_upwards [hhgrad, hnotSphere] with y hy hys hyB
    apply hy
    have hylt : dist y c < s := lt_of_le_of_ne (Metric.mem_closedBall.mp hyB)
      (by simpa only [Metric.mem_sphere] using hys)
    exact Metric.mem_ball.mpr hylt
  have hψzero := hψW.weakGrad_eq_zero_of_isClosed Metric.isClosed_closedBall
  have hψgrad : weakGrad ψ =ᵐ[volume] (Metric.closedBall c s).indicator
      (fun y => gradient w y - gradient h y) := by
    filter_upwards [hhgradClosed, hψzero] with y hy hz
    by_cases hyB : y ∈ Metric.closedBall c s
    · rw [Set.indicator_of_mem hyB, ← hy hyB]
      abel
    · rw [Set.indicator_of_notMem hyB, hz hyB]
  have hH : MemLp (gradient h) 2 (volume.restrict (Metric.closedBall c s)) :=
    (hG.mono_measure Measure.restrict_le_self).ae_eq
      ((ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).2 hhgradClosed)
  have htransfer : ∀ ζ : Euc d → ℝ, MemW0 2 (Metric.closedBall c s) ζ →
      (∫ y, ⟪A₀ (gradient h y), weakGrad ζ y⟫) = 0 := by
    intro ζ hζ
    rw [← htestA ζ hζ]
    apply integral_congr_ae
    filter_upwards [hhgradClosed, hζ.weakGrad_eq_zero_of_isClosed Metric.isClosed_closedBall]
      with y hy hz
    by_cases hyB : y ∈ Metric.closedBall c s
    · rw [hy hyB]
    · rw [hz hyB, inner_zero_right, inner_zero_right]
  refine ⟨h, ψ, hh, hH, hψW, hψgrad, ?_, htransfer ψ hψW⟩
  intro ζ hζ hζs hζB
  have hζW := memW0_of_contDiff_supported hζ hζs
    (hζB.trans Metric.ball_subset_closedBall) 2
  have heq := (hasWeakGradient_gradient (hζ.of_le (by simp)) hζs).weakGrad_ae_eq
  rw [← htransfer ζ hζW]
  apply integral_congr_ae
  filter_upwards [heq] with y hy
  rw [hy]

/-- Local `C¹` data can be used in the frozen replacement after a smooth cutoff;
the comparison ball is strictly inside the domain. -/
theorem exists_frozen_smooth_replacement_on_ball (hd : 0 < d)
    {A₀ : Euc d →L[ℝ] Euc d} {μ Λ : ℝ}
    (hμ : 0 < μ) (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    (hA : ‖A₀‖ ≤ Λ) {c : Euc d} {s : ℝ} (hs : 0 < s)
    {U : Set (Euc d)} (hU : IsOpen U) {w : Euc d → ℝ} (hw : ContDiffOn ℝ 1 w U)
    (hsub : Metric.closedBall c (2 * s) ⊆ U) :
    ∃ h ψ : Euc d → ℝ, ContDiffOn ℝ ∞ h (Metric.ball c s) ∧
      MemLp (gradient h) 2 (volume.restrict (Metric.closedBall c s)) ∧
      MemW0 2 (Metric.closedBall c s) ψ ∧
      weakGrad ψ =ᵐ[volume] (Metric.closedBall c s).indicator
        (fun y => gradient w y - gradient h y) ∧
      (∀ ζ : Euc d → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ Metric.ball c s → ∫ y, ⟪A₀ (gradient h y), gradient ζ y⟫ = 0) ∧
      (∫ y, ⟪A₀ (gradient h y), weakGrad ψ y⟫) = 0 := by
  obtain ⟨Cη, _, hcut⟩ := exists_uniform_cutoff (d := d) (a := 3 * s / 2)
    (b := 7 * s / 4) (by linarith) (by linarith)
  obtain ⟨η, hη, _, _, hηone, hηsupp, _⟩ := hcut c
  let w' : Euc d → ℝ := fun y => η y * w y
  have hsupp : tsupport w' ⊆ Metric.closedBall c (7 * s / 4) := by
    exact tsupport_mul_subset_left.trans hηsupp
  have hsub' : Metric.closedBall c (7 * s / 4) ⊆ U :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hsub
  have hw' : ContDiff ℝ 1 w' := contDiff_one_of_contDiffOn hU
    Metric.isClosed_closedBall hsub' ((hη.of_le (by simp)).contDiffOn.mul hw) hsupp
  have hw's : HasCompactSupport w' :=
    (isCompact_closedBall c (7 * s / 4)).of_isClosed_subset (isClosed_tsupport w') hsupp
  have hgrad : ∀ y ∈ Metric.closedBall c s, gradient w' y = gradient w y := by
    intro y hy
    have hy' : y ∈ Metric.ball c (3 * s / 2) :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith))
    have heq : w' =ᶠ[𝓝 y] w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy'] with z hz
      show η z * w z = w z
      rw [hηone z (Metric.ball_subset_closedBall hz), one_mul]
    exact congrArg ((InnerProductSpace.toDual ℝ (Euc d)).symm) heq.fderiv_eq
  obtain ⟨h, ψ, hh, hH, hψ, hψgrad, hsol, htest⟩ :=
    exists_frozen_smooth_replacement hd hμ hell hA hs hw' hw's
  refine ⟨h, ψ, hh, hH, hψ, hψgrad.trans ?_, hsol, htest⟩
  refine Eventually.of_forall fun y => ?_
  by_cases hy : y ∈ Metric.closedBall c s
  · simp only [Set.indicator_of_mem hy, hgrad y hy]
  · simp only [Set.indicator_of_notMem hy]

end Komlos.Literature
