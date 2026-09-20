import Komlos.Literature.PLaplacian.BoundaryBarrier
import Komlos.Literature.PLaplacian.RegularityHolder

/-!
# Weak first eigenfunctions, and the reductions used by the concavity machinery

The direct method (`exists_eigenfunction_weak`) produces a weak first eigenfunction
`u ∈ W₀^{1,p}(K)` (paper Appendix A, *Eigenfunction inputs*).  This file bundles its
conclusions as `IsWeakFirstEigenfunction` and proves the elementary reductions the Korevaar
machinery of `Korevaar*.lean` consumes.

## History (lane `L7`, `NOTES_integrate.md`)

This file used to end with the **degenerate** regularity theorem of Mosconi–Riey–Squassina
2024, Proposition 4.5 (`mrs_regularity`, `mrs_regularity_core`, `boundary_regularity`,
`lieberman_gradient_bound`, `exists_scaled_interior_gradient_bound`).  That theorem rested on
`exists_degiorgi_uniform_flux_energy_bounds` (`DiffQuotCaccioppoli.lean`), an analytic input
that was never proved.  The regularized route of `REGULARIZED_ROUTE.md` (Revision 2) replaced
the whole degenerate eigenfunction/Korevaar/Wang–Xia chain, so that tail — and its dependency
cone — was deleted by lane `L7`.  What is kept here is exactly what the surviving files use.

## Main results

* `IsWeakFirstEigenfunction p F K u`, `exists_isWeakFirstEigenfunction`,
  `IsWeakFirstEigenfunction.not_ae_eq_zero`, `IsWeakFirstEigenfunction.isWeakEigensolution`;
* classical-versus-weak gradients: `eq_zero_of_notMem_of_ae_eq`, `gradient_ae_eq_weakGrad`;
* gluing an interior representative with `0` outside `K`: `pos_of_ae_lower_bound`,
  `continuous_indicator_of_tendsto`, `gradient_indicator_of_mem`, `indicator_ae_eq_of_ae_eq`;
* boundary reductions: `nonneg_of_ae_eq_on_open`, `exists_supporting_functional`,
  `tendsto_zero_of_barrier`, `boundary_holder_barrier`;
* `weak_flux_eq_of_representative`, `exists_frontier_infDist`.

## Proof of the gradient identification

On the open set `K`, `φ` is `C¹`; for a test function `ψ` supported in `K`, integration by parts
(`integral_mul_fderiv_eq_neg_of_contDiffOn`, no cutoff needed since only `ψ` has to be
differentiable off `K`) and the weak-gradient identity of `u = φ` a.e. give
`∫ ψ • (∇_w u - ∇φ) = 0`, so `∇φ = ∇_w u` a.e. on `K` by the fundamental lemma of the calculus of
variations on open sets (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). The same argument
applies on the open set `(closure K)ᶜ`, where `φ = 0`; the remaining set `∂K` is Lebesgue-null
because `K` is convex (`Convex.addHaar_frontier`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Weak first eigenfunctions -/

/-- A **weak first eigenfunction** of the anisotropic `p`-Laplacian on `K` (paper Appendix A,
*Eigenfunction inputs*: "The direct method gives a nonnegative, nonzero first eigenfunction
`u_i ∈ W_0^{1,p}(K_i)`"): a nonnegative `u ∈ W₀^{1,p}(K)` vanishing outside `K`, normalized by
`∫ |u|^p = 1`, attaining the Rayleigh infimum `∫ F(∇u)^p = λ_{p,F}(K)`, and solving the weak
eigenvalue equation `∫ ⟪a(∇u), ∇ψ⟫ = λ_{p,F}(K) ∫ u^{p-1} ψ` against smooth test functions. These
are the conclusions of `exists_eigenfunction_weak`. -/
structure IsWeakFirstEigenfunction (p : ℝ) (F : Euc d → ℝ) (K : Set (Euc d))
    (u : Euc d → ℝ) : Prop where
  /-- `u ∈ W₀^{1,p}(K)`. -/
  memW0 : MemW0 p K u
  /-- `u ≥ 0`. -/
  nonneg : ∀ x, 0 ≤ u x
  /-- `u` vanishes outside `K`. -/
  eq_zero_of_notMem : ∀ x, x ∉ K → u x = 0
  /-- The normalization `∫ |u|^p = 1`. -/
  integral_abs_rpow : ∫ x, |u x| ^ p = 1
  /-- `u` attains the Rayleigh infimum: `∫ F(∇u)^p = λ_{p,F}(K)`. -/
  energy : ∫ x, F (weakGrad u x) ^ p = lambdaGen p F K
  /-- The weak eigenvalue equation `∫ ⟪a(∇u), ∇ψ⟫ = λ ∫ u^{p-1} ψ` for `ψ ∈ C_c^∞(K)`. -/
  weakEL : ∀ ψ : Euc d → ℝ, IsTestFn K ψ →
    ∫ x, ⟪flux p F (weakGrad u x), gradient ψ x⟫ = lambdaGen p F K * ∫ x, u x ^ (p - 1) * ψ x

/-- The direct method produces a weak first eigenfunction (`exists_eigenfunction_weak`). -/
theorem exists_isWeakFirstEigenfunction {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) :
    ∃ u : Euc d → ℝ, IsWeakFirstEigenfunction p F K u := by
  obtain ⟨u, hu, hu0, huK, hu1, hE, hEL⟩ := exists_eigenfunction_weak hp hF hK
  exact ⟨u, hu, hu0, huK, hu1, hE, hEL⟩

/-- A weak first eigenfunction is not almost everywhere zero (`∫ |u|^p = 1`). -/
theorem IsWeakFirstEigenfunction.not_ae_eq_zero {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    {K : Set (Euc d)} {u : Euc d → ℝ} (hu : IsWeakFirstEigenfunction p F K u) :
    ¬ u =ᵐ[volume] 0 := by
  intro h
  have h1 : (fun x => |u x| ^ p) =ᵐ[volume] fun _ => (0 : ℝ) :=
    h.mono fun x hx => by
      simp only [hx, Pi.zero_apply, abs_zero, Real.zero_rpow (zero_lt_one.trans hp).ne']
  have h2 := hu.integral_abs_rpow
  rw [integral_congr_ae h1, integral_zero] at h2
  exact zero_ne_one h2

/-- **A weak first eigenfunction solves the eigenvalue equation against all of `W₀^{1,p}(K)`**
(`weak_euler_lagrange` with `lambdaSob = lambdaGen`, paper Appendix A, *Eigenfunction inputs*), so
the regularity ladder of `RegularityInterior.lean` applies to it. -/
theorem IsWeakFirstEigenfunction.isWeakEigensolution {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {u : Euc d → ℝ}
    (hu : IsWeakFirstEigenfunction p F K u) :
    IsWeakEigensolution p F K (lambdaGen p F K) u where
  memW0 := hu.memW0
  nonneg := hu.nonneg
  weakEq ψ hψ := by
    obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
    have hlam : lambdaSob p F K = lambdaGen p F K :=
      lambdaSob_eq_lambdaGen hp hF.continuous hF.nonneg hM hK
    have hmin : ∫ x, F (weakGrad u x) ^ p = lambdaSob p F K * ∫ x, |u x| ^ p := by
      rw [hu.energy, hu.integral_abs_rpow, mul_one, hlam]
    rw [weak_euler_lagrange hp hF hu.memW0 hmin hψ, hlam]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show |u x| ^ (p - 2) * u x * ψ x = u x ^ (p - 1) * ψ x
    have h1 := abs_rpow_sub_two_mul_abs hp (u x)
    rw [abs_of_nonneg (hu.nonneg x)] at h1 ⊢
    rw [h1]

/-! ### Classical versus weak gradients -/

/-- **Zero boundary values of a continuous representative**: if `φ` is continuous, `φ =ᵐ u`, and
`u` vanishes outside a nonempty open convex set `K`, then `φ` vanishes outside `K` (including on
`∂K`, which lies in the closure of the exterior of `K`). -/
theorem eq_zero_of_notMem_of_ae_eq {K : Set (Euc d)} (hK : IsGoodConvex K) {u φ : Euc d → ℝ}
    (huK : ∀ x, x ∉ K → u x = 0) (hφc : Continuous φ) (hφu : φ =ᵐ[volume] u) :
    ∀ x, x ∉ K → φ x = 0 := by
  have hext : EqOn φ 0 (closure K)ᶜ := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isClosed_closure.isOpen_compl
      hφc.continuousOn continuousOn_const
    refine (ae_restrict_iff' isClosed_closure.isOpen_compl.measurableSet).2 ?_
    filter_upwards [hφu] with x hx hxK
    rw [hx, huK x fun h => hxK (subset_closure h)]
    rfl
  have hint : (interior K).Nonempty := by
    rw [hK.isOpen.interior_eq]
    exact hK.nonempty
  have hcl : closure (closure K)ᶜ = Kᶜ := by
    rw [closure_compl, hK.convex.interior_closure_eq_interior_of_nonempty_interior hint,
      hK.isOpen.interior_eq]
  intro x hx
  have hmem : x ∈ closure (closure K)ᶜ := by
    rw [hcl]
    exact hx
  exact closure_minimal (fun y hy => hext hy) (isClosed_eq hφc continuous_const) hmem

/-- **The classical gradient of the regular representative is the weak gradient**: if `φ` is a
representative of `u ∈ W₀^{1,p}(K)` that vanishes outside the good convex set `K` and is `C¹` on
`K`, then `∇φ = ∇_w u` almost everywhere on `ℝ^d`. Hence integrals of `∇φ` (the Rayleigh quotient,
the weak Euler–Lagrange equation) agree with those of the weak gradient. -/
theorem gradient_ae_eq_weakGrad {p : ℝ} {K : Set (Euc d)} (hK : IsGoodConvex K)
    {u φ : Euc d → ℝ} (hu : MemW0 p K u) (hφu : φ =ᵐ[volume] u) (hφK : ∀ x, x ∉ K → φ x = 0)
    (hφ1 : ContDiffOn ℝ 1 φ K) : gradient φ =ᵐ[volume] weakGrad u := by
  have hin := ae_gradient_eq_of_hasWeakGradient hu.hasWeakGradient hφu hK.isOpen hφ1
  have hout := ae_gradient_eq_of_hasWeakGradient hu.hasWeakGradient hφu
    isClosed_closure.isOpen_compl
    (contDiffOn_const.congr fun x hx => hφK x fun h => hx (subset_closure h))
  have hfr : ∀ᵐ x : Euc d, x ∉ frontier K :=
    measure_eq_zero_iff_ae_notMem.1 (hK.convex.addHaar_frontier volume)
  filter_upwards [hin, hout, hfr] with x h1 h2 h3
  by_cases hxK : x ∈ K
  · exact h1 hxK
  · refine h2 fun hx => h3 ⟨hx, ?_⟩
    rwa [hK.isOpen.interior_eq]

/-! ### Gluing the interior representative -/

/-- **Positivity from local lower bounds**: if `φ` is continuous on the open set `U`, `φ = u`
a.e. on `U`, and `u` is a.e. bounded below by a positive constant on every compact subset of `U`,
then `φ > 0` on `U` (a point with `φ ≤ c` would give a ball of positive measure where `φ < c`). -/
theorem pos_of_ae_lower_bound {U : Set (Euc d)} (hU : IsOpen U) {φ u : Euc d → ℝ}
    (hφc : ContinuousOn φ U) (hφu : φ =ᵐ[volume.restrict U] u)
    (hlow : ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂(volume.restrict S), c ≤ u x) :
    ∀ x ∈ U, 0 < φ x := by
  intro x₀ hx₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hS : Metric.closedBall x₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨c, hc, hcu⟩ := hlow _ (isCompact_closedBall x₀ (r / 2)) hS
  refine lt_of_lt_of_le hc (not_lt.1 fun hlt => ?_)
  have hev : ∀ᶠ y in 𝓝 x₀, φ y < c :=
    (hφc.continuousAt (hU.mem_nhds hx₀)).eventually (gt_mem_nhds hlt)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have h1 : ∀ᵐ y, y ∈ Metric.closedBall x₀ (r / 2) → c ≤ u y :=
    (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).1 hcu
  have h2 : ∀ᵐ y, y ∈ U → φ y = u y := (ae_restrict_iff' hU.measurableSet).1 hφu
  have hρ : 0 < min δ (r / 2) := lt_min hδ (half_pos hr)
  have hnull : volume (Metric.ball x₀ (min δ (r / 2))) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [h1, h2] with y hy1 hy2 hy
    have hyδ : y ∈ Metric.ball x₀ δ := Metric.ball_subset_ball (min_le_left _ _) hy
    have hyr : y ∈ Metric.closedBall x₀ (r / 2) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) hy)
    have := hδball y hyδ
    rw [hy2 (hS hyr)] at this
    exact absurd (hy1 hyr) (not_le.2 this)
  exact (Metric.measure_ball_pos volume x₀ hρ).ne' hnull

/-- Gluing with `0` outside an open set: if `φ` is continuous on the open set `K` and tends to `0`
at every frontier point (within `K`), then `K.indicator φ` is continuous. -/
theorem continuous_indicator_of_tendsto {K : Set (Euc d)} (hK : IsOpen K) {φ : Euc d → ℝ}
    (hφc : ContinuousOn φ K) (hbd : ∀ x₀ ∈ frontier K, Tendsto φ (𝓝[K] x₀) (𝓝 0)) :
    Continuous (K.indicator φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ K
  · have heq : φ =ᶠ[𝓝 x] K.indicator φ := by
      filter_upwards [hK.mem_nhds hx] with y hy
      exact (indicator_of_mem hy φ).symm
    exact (hφc.continuousAt (hK.mem_nhds hx)).congr heq
  by_cases hxc : x ∈ closure K
  · have hfr : x ∈ frontier K := by
      rw [hK.frontier_eq]
      exact ⟨hxc, hx⟩
    rw [ContinuousAt, indicator_of_notMem hx]
    have h1 : Tendsto (K.indicator φ) (𝓝[K] x) (𝓝 0) :=
      (hbd x hfr).congr' (eventually_nhdsWithin_of_forall fun y hy => (indicator_of_mem hy φ).symm)
    have h2 : Tendsto (K.indicator φ) (𝓝[Kᶜ] x) (𝓝 0) :=
      tendsto_const_nhds.congr'
        (eventually_nhdsWithin_of_forall fun y hy => (indicator_of_notMem hy φ).symm)
    have h3 := h1.sup h2
    rwa [← nhdsWithin_union, union_compl_self, nhdsWithin_univ] at h3
  · have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] K.indicator φ := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      exact (indicator_of_notMem (fun h => hy (subset_closure h)) φ).symm
    exact continuousAt_const.congr heq

/-- The indicator of an open set agrees with `φ` near points of the set, so their gradients agree
there. -/
theorem gradient_indicator_of_mem {K : Set (Euc d)} (hK : IsOpen K) {φ : Euc d → ℝ} {x : Euc d}
    (hx : x ∈ K) : gradient (K.indicator φ) x = gradient φ x := by
  have heq : K.indicator φ =ᶠ[𝓝 x] φ := by
    filter_upwards [hK.mem_nhds hx] with y hy
    exact indicator_of_mem hy φ
  unfold gradient
  rw [heq.fderiv_eq]

/-- A representative of `u` on the open set `K`, glued with `0` outside `K`, is a representative of
`u` on `ℝ^d` when `u` vanishes outside `K`. -/
theorem indicator_ae_eq_of_ae_eq {K : Set (Euc d)} (hK : IsOpen K) {φ u : Euc d → ℝ}
    (hφu : φ =ᵐ[volume.restrict K] u) (huK : ∀ x, x ∉ K → u x = 0) :
    K.indicator φ =ᵐ[volume] u := by
  filter_upwards [(ae_restrict_iff' hK.measurableSet).1 hφu] with x hx
  by_cases hxK : x ∈ K
  · rw [indicator_of_mem hxK]
    exact hx hxK
  · rw [indicator_of_notMem hxK, huK x hxK]

/-! ### Boundary regularity: geometric and analytic reductions

The boundary conclusions of `boundary_regularity` are the **zero boundary values** and the
**bounded gradient up to `∂K`**. The first is now fully proved: nonnegativity of the continuous
representative, the supporting functional at a convex boundary point (Mathlib's geometric
Hahn–Banach), the squeeze that turns a boundary barrier into `φ → 0`, and — in
`Komlos.Literature.PLaplacian.BoundaryBarrier` — the **weak comparison principle** for the
degenerate anisotropic `p`-Laplacian together with Lieberman's linear convex-domain barrier, which
give `boundary_holder_barrier` with exponent `γ = 1`. The second, `lieberman_gradient_bound`, is
now **assembled** here: `exists_uniform_linear_barrier` (proved) supplies a barrier constant that
is uniform over the supporting functionals of `K`, so that `φ ≤ 4 A r` on `B(x, 2r)` for
`r = dist(x, Kᶜ)/2`, and the geometry (`exists_frontier_infDist`) locates the boundary point.
The scaling reduction to a fixed-radius unit-ball estimate is proved in
`Komlos.Literature.PLaplacian.ScaledGradient` (`weak_rescale`,
`exists_scaled_interior_gradient_bound_of_unit_ball`). The unit-ball estimate is also reduced
to the quantitative gradient sup estimate in `DeGiorgiGradient.lean`. The remaining
De Giorgi/Moser input is `exists_degiorgi_uniform_flux_energy_bounds` in
`DiffQuotCaccioppoli.lean`; its sup-bound clause supplies this argument. -/

/-- **Nonnegativity of a continuous representative on an open set**: if `φ` is continuous on the
open set `U`, agrees a.e. on `U` with a pointwise nonnegative `u`, then `φ ≥ 0` on all of `U`. A
point with `φ < 0` would, by continuity, force `φ < 0` on a ball of positive measure, contradicting
`φ = u ≥ 0` a.e. there. -/
theorem nonneg_of_ae_eq_on_open {U : Set (Euc d)} (hU : IsOpen U) {φ u : Euc d → ℝ}
    (hφc : ContinuousOn φ U) (hφu : φ =ᵐ[volume.restrict U] u) (hu0 : ∀ x, 0 ≤ u x) :
    ∀ x ∈ U, 0 ≤ φ x := by
  intro x₀ hx₀
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hev : ∀ᶠ y in 𝓝 x₀, φ y < 0 :=
    (hφc.continuousAt (hU.mem_nhds hx₀)).eventually (gt_mem_nhds hneg)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have h2 : ∀ᵐ y, y ∈ U → φ y = u y := (ae_restrict_iff' hU.measurableSet).1 hφu
  have hρ : 0 < min δ r := lt_min hδ hr
  have hnull : volume (Metric.ball x₀ (min δ r)) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [h2] with y hy2 hy
    have hyδ : y ∈ Metric.ball x₀ δ := Metric.ball_subset_ball (min_le_left δ r) hy
    have hyU : y ∈ U := hball (Metric.ball_subset_ball (min_le_right δ r) hy)
    have hlt : φ y < 0 := hδball y hyδ
    rw [hy2 hyU] at hlt
    exact absurd (hu0 y) (not_le.2 hlt)
  exact (Metric.measure_ball_pos volume x₀ hρ).ne' hnull

/-- **Supporting functional at a convex boundary point** (geometric Hahn–Banach): for a good
convex (in particular open) set `K` and a boundary point `x₀ ∈ frontier K`, there is a continuous
linear functional `ℓ` strictly separating `K` from `x₀`, i.e. `ℓ x < ℓ x₀` for every `x ∈ K`. The
half-space `{ℓ < ℓ x₀}` contains `K` and has `x₀` on its bounding hyperplane; it carries the
boundary barrier of `boundary_holder_barrier`. -/
theorem exists_supporting_functional {K : Set (Euc d)} (hK : IsGoodConvex K) {x₀ : Euc d}
    (hx₀ : x₀ ∈ frontier K) : ∃ ℓ : Euc d →L[ℝ] ℝ, ∀ x ∈ K, ℓ x < ℓ x₀ := by
  have hx₀K : x₀ ∉ K := by
    rw [hK.isOpen.frontier_eq] at hx₀
    exact hx₀.2
  exact geometric_hahn_banach_open_point hK.convex hK.isOpen hx₀K

/-- **Boundary vanishing from a Hölder barrier**: if `φ ≥ 0` on the open set `K` and is dominated
there by the supporting-half-space barrier `x ↦ C (ℓ x₀ - ℓ x)^γ` with exponent `γ > 0`, then
`φ(x) → 0` as `x → x₀` within `K`. As `x → x₀` the linear functional `ℓ x → ℓ x₀`, so the barrier
tends to `0` (continuity of `t ↦ t^γ` at `0`, with value `0^γ = 0`); squeezing `0 ≤ φ ≤` barrier
gives the limit. -/
theorem tendsto_zero_of_barrier {K : Set (Euc d)} {φ : Euc d → ℝ} (hφ0 : ∀ x ∈ K, 0 ≤ φ x)
    {x₀ : Euc d} (ℓ : Euc d →L[ℝ] ℝ) {C γ : ℝ} (hγ : 0 < γ)
    (hbar : ∀ x ∈ K, φ x ≤ C * (ℓ x₀ - ℓ x) ^ γ) :
    Tendsto φ (𝓝[K] x₀) (𝓝 0) := by
  have hfc : Tendsto (fun x => ℓ x₀ - ℓ x) (𝓝[K] x₀) (𝓝 0) := by
    have hc : Continuous fun x => ℓ x₀ - ℓ x := continuous_const.sub ℓ.continuous
    simpa using (hc.tendsto x₀).mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun t : ℝ => t ^ γ) (𝓝 (0 : ℝ)) (𝓝 0) :=
    (Real.continuous_rpow_const hγ.le).tendsto' 0 0 (Real.zero_rpow hγ.ne')
  have hg0 : Tendsto (fun x => C * (ℓ x₀ - ℓ x) ^ γ) (𝓝[K] x₀) (𝓝 0) := by
    have hcomp : Tendsto (fun x => (ℓ x₀ - ℓ x) ^ γ) (𝓝[K] x₀) (𝓝 0) := hpow.comp hfc
    simpa using hcomp.const_mul C
  exact squeeze_zero' (eventually_nhdsWithin_of_forall hφ0)
    (eventually_nhdsWithin_of_forall hbar) hg0

/-- **Boundary barrier bound** (weak comparison principle for the degenerate anisotropic
`p`-Laplacian against a supporting-half-space barrier; Lieberman 1988, *Boundary regularity for
solutions of degenerate elliptic equations*, Nonlinear Anal. 12; MRS24, Proposition 4.5): a bounded
nonnegative weak eigensolution `u`, represented by `φ` on `K`, is dominated near a convex boundary
point `x₀` by the barrier built from the supporting functional `ℓ` (`exists_supporting_functional`):
there are `C` and an exponent `γ > 0` with `φ x ≤ C (ℓ x₀ - ℓ x)^γ` for every `x ∈ K`.

**Proved** in `Komlos.Literature.PLaplacian.BoundaryBarrier` with the *linear* exponent `γ = 1`
(Lieberman's convex-domain barrier): `exists_linear_barrier` compares `u` on the supporting
half-space `{ℓ < ℓ x₀} ⊇ K` with the smooth supersolution `Φ = A (1 - e^{ℓ · - ℓ x₀})`, whose flux
`a(∇Φ) = c • a(-n)` has `-div a(∇Φ) = (p-1) F(n)^p c > 0` bounded below on the bounded set `K`, so
that for `A` large it dominates `λ ‖u‖_∞^{p-1}`; the weak comparison principle
`ae_le_of_comparison` (strict monotonicity of the flux plus Dirichlet–Poincaré) gives `u ≤ Φ` a.e.
on `K`, and `Φ ≤ A (ℓ x₀ - ℓ ·)`. The a.e. bound is upgraded to a pointwise bound for the
continuous representative by `le_of_ae_le_on_open`. -/
theorem boundary_holder_barrier {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} (hK : IsGoodConvex K) {lam : ℝ} {u : Euc d → ℝ}
    (hu : IsWeakEigensolution p F K lam u) (hbdd : ∃ M : ℝ, ∀ᵐ x, u x ≤ M) {φ : Euc d → ℝ}
    (hφu : φ =ᵐ[volume.restrict K] u) (hφ1 : ContDiffOn ℝ 1 φ K) {x₀ : Euc d}
    (hx₀ : x₀ ∈ frontier K) (ℓ : Euc d →L[ℝ] ℝ) (hℓ : ∀ x ∈ K, ℓ x < ℓ x₀) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ x ∈ K, φ x ≤ C * (ℓ x₀ - ℓ x) ^ γ := by
  obtain ⟨M, hM⟩ := hbdd
  have hM' : ∀ᵐ x : Euc d, u x ≤ max M 0 :=
    hM.mono fun x hx => le_trans hx (le_max_left _ _)
  obtain ⟨A, hA0, hbar⟩ :=
    exists_linear_barrier hp hF hK hu (le_max_right M 0) hM' ℓ hℓ
  refine ⟨A, 1, one_pos, fun x hx => ?_⟩
  rw [Real.rpow_one]
  refine le_of_ae_le_on_open hK.isOpen hφ1.continuousOn
    (continuous_const.mul (continuous_const.sub ℓ.continuous)).continuousOn ?_ x hx
  have hbar' : ∀ᵐ y ∂(volume.restrict K), u y ≤ A * (ℓ x₀ - ℓ y) :=
    (ae_restrict_iff' hK.isOpen.measurableSet).2 hbar
  filter_upwards [hφu, hbar'] with y h1 h2
  rw [h1]
  exact h2

/-! ### The scaled interior gradient estimate -/

/-- **The weak flux equation for a `C¹` representative.**  If `u` is a weak eigensolution on the
open set `K` and `φ` is a `C¹` representative of `u` there, then `φ` itself solves
`∫ ⟪a(∇φ), ∇ψ⟫ = λ ∫ φ^{p-1} ψ` against every `ψ ∈ C_c^∞(K)`: the weak gradient of `u` is `∇φ`
a.e. on `K` (`ae_gradient_eq_of_hasWeakGradient`), and both sides only see `K`.  (This is the
block extracted from the proof of `contDiffOn_two_of_gradient_ne_zero`.) -/
theorem weak_flux_eq_of_representative {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} (hK : IsOpen K)
    {lam : ℝ} {u : Euc d → ℝ} (hu : IsWeakEigensolution p F K lam u) {φ : Euc d → ℝ}
    (hφu : φ =ᵐ[volume.restrict K] u) (hφ1 : ContDiffOn ℝ 1 φ K) :
    ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ K →
      ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ = lam * ∫ x, φ x ^ (p - 1) * ψ x := by
  classical
  obtain ⟨φ', hφ'⟩ : ∃ φ' : Euc d → ℝ, φ' = K.piecewise φ u := ⟨_, rfl⟩
  have hφ'u : φ' =ᵐ[volume] u := by
    rw [hφ']
    filter_upwards [(ae_restrict_iff' hK.measurableSet).1 hφu] with x hx
    by_cases hxK : x ∈ K
    · rw [piecewise_eq_of_mem _ _ _ hxK]
      exact hx hxK
    · rw [piecewise_eq_of_notMem _ _ _ hxK]
  have hφ'1 : ContDiffOn ℝ 1 φ' K :=
    hφ1.congr fun x hx => by rw [hφ', piecewise_eq_of_mem _ _ _ hx]
  have hgrad' : ∀ x ∈ K, gradient φ' x = gradient φ x := fun x hx => by
    have heq : φ' =ᶠ[𝓝 x] φ := by
      filter_upwards [hK.mem_nhds hx] with y hy
      rw [hφ', piecewise_eq_of_mem _ _ _ hy]
    unfold gradient
    rw [heq.fderiv_eq]
  have hae := ae_gradient_eq_of_hasWeakGradient hu.memW0.hasWeakGradient hφ'u hK hφ'1
  intro ψ hψ hψs hψK
  have h := hu.weakEq ψ (memW0_of_contDiff (hψ.of_le (by simp)) hψs hψK p)
  have e1 : ∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ =
      ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [weakGrad_ae_eq_gradient (hψ.of_le (by simp)) hψs, hae] with x h1 h2
    show ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ = ⟪flux p F (gradient φ x), gradient ψ x⟫
    rw [h1]
    by_cases hxK : x ∈ K
    · rw [← h2 hxK, hgrad' x hxK]
    · rw [gradient_eq_zero_of_notMem_tsupport fun h => hxK (hψK h), inner_zero_right,
        inner_zero_right]
  have e2 : ∫ x, u x ^ (p - 1) * ψ x = ∫ x, φ x ^ (p - 1) * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' hK.measurableSet).1 hφu] with x hx
    show u x ^ (p - 1) * ψ x = φ x ^ (p - 1) * ψ x
    by_cases hxK : x ∈ K
    · rw [hx hxK]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hxK (hψK h), mul_zero, mul_zero]
  rw [← e1, ← e2]
  exact h

/-- **The nearest point of `Kᶜ` lies on `∂K`.**  For an open `K` and `x ∈ K`, a point of `Kᶜ`
realising `infDist x Kᶜ` is a boundary point: otherwise it has a neighbourhood missing
`closure K`, and moving it a little towards `x` would produce a strictly closer point of `Kᶜ`. -/
theorem exists_frontier_infDist {K : Set (Euc d)} (hK : IsOpen K) (hKc : (Kᶜ).Nonempty)
    {x : Euc d} (hx : x ∈ K) :
    ∃ w ∈ frontier K, dist x w = Metric.infDist x Kᶜ := by
  obtain ⟨w, hw, hwd⟩ := (isClosed_compl_iff.2 hK).exists_infDist_eq_dist hKc x
  have hxw : x ≠ w := fun h => hw (h ▸ hx)
  have hdpos : 0 < dist x w := dist_pos.2 hxw
  refine ⟨w, ?_, hwd.symm⟩
  rw [frontier_eq_closure_inter_closure]
  refine ⟨?_, subset_closure hw⟩
  by_contra hwc
  obtain ⟨ε, hε0, hεsub⟩ :=
    Metric.isOpen_iff.1 isClosed_closure.isOpen_compl w hwc
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = min (1 / 2) (ε / (2 * dist x w)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [htdef]
    exact lt_min (by norm_num) (div_pos hε0 (by linarith))
  have ht1 : t ≤ 1 / 2 := by rw [htdef]; exact min_le_left _ _
  have hne : dist x w ≠ 0 := hdpos.ne'
  have htε : t * dist x w < ε := by
    have h1 : t ≤ ε / (2 * dist x w) := by rw [htdef]; exact min_le_right _ _
    have h2 : (0 : ℝ) < 2 * dist x w := by linarith
    have h4 : t * (2 * dist x w) ≤ ε / (2 * dist x w) * (2 * dist x w) :=
      mul_le_mul_of_nonneg_right h1 h2.le
    have h5 : ε / (2 * dist x w) * (2 * dist x w) = ε := by field_simp <;> ring
    linarith [mul_pos ht0 hdpos, h4, h5]
  obtain ⟨w', hw'def⟩ : ∃ w' : Euc d, w' = w + t • (x - w) := ⟨_, rfl⟩
  have hdist : dist w' w = t * dist x w := by
    rw [hw'def, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le,
      dist_eq_norm]
  have hw'mem : w' ∈ Kᶜ := by
    have h1 : w' ∈ Metric.ball w ε := by
      rw [Metric.mem_ball, hdist]
      exact htε
    have h2 := hεsub h1
    exact fun hw'K => h2 (subset_closure hw'K)
  have hxw' : dist x w' = (1 - t) * dist x w := by
    have hsub : x - w' = (1 - t) • (x - w) := by rw [hw'def]; module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg (by linarith), dist_eq_norm]
  have hlt : dist x w' < dist x w := by
    rw [hxw']
    nlinarith [mul_pos ht0 hdpos]
  have hge : Metric.infDist x Kᶜ ≤ dist x w' := Metric.infDist_le_dist_of_mem hw'mem
  rw [hwd] at hge
  linarith
end Komlos.Literature
