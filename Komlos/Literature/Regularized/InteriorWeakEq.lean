import Komlos.Literature.Regularized.InteriorWeakEqAux

/-!
# The weak equation for `v` against bounded `W₀^{1,2}` test functions (lane `L3a`, link 3)

Link 3 of lane `L3` (`reg/c2`) of `REGULARIZED_ROUTE.md`, Revision 2 (v): the weak equation

`∫ ⟪∇Ψ(∇v), ∇ψ⟫ = -∫ (κ v + 2 m + B(∇v)) ψ`

of `IsWeakLogSol`, which is stated against `ψ ∈ C_c^∞(U)`, holds for every **bounded**
`ψ ∈ W₀^{1,2}(T)` with `T` a compact subset of a ball `B(y, s)` whose closure lies in `U`.

`IsWeakLogSol.weakEq_memW0` is link 3 of the interior-regularity chain described in
`Komlos/Literature/Regularized/InteriorRegularity.lean`.

## Why boundedness is needed

The homogeneous case (`IsRegHarmonic.weakEq_memW0`) follows from the project's density theorem
`Komlos.Literature.integral_inner_weakGrad_eq_of_memW0_two`, because the right-hand side is `0`.
Here the right-hand side `f = κ v + 2 m + B(∇v)` is only `L¹` on a ball — `B` has quadratic
growth in `∇v` and `∇v ∈ L²` — so the `L²`–`L²` duality of that theorem does not apply to the
term `∫ f ψ`.  What does apply is dominated convergence, provided the approximating test
functions are *uniformly bounded*: that is `exists_contDiff_tendsto_eLpNorm_bounded`
(`InteriorWeakEqAux.lean`), the repository's mollification argument with the sup bound recorded.

## The proof

Approximate `ψ` by `u n ∈ C_c^∞(B(y,s))` with `|u n| ≤ Mψ`, `u n → ψ` and `∇u n → ∇ψ` in `L²`.

* the flux term `∫ ⟪∇Ψ(G), ∇u n⟫` converges to `∫ ⟪∇Ψ(G), ∇ψ⟫` by `L²`–`L²` duality
  (`Komlos.Literature.tendsto_integral_inner_of_tendsto_eLpNorm`), after replacing `∇Ψ ∘ G` by
  its restriction to `B(y,s)` — legitimate because `∇u n` is supported in `B(y,s)` and `∇ψ`
  vanishes a.e. off `T`;
* the right-hand side `∫ f (u n)` converges to `∫ f ψ` along a subsequence on which `u n → ψ`
  a.e. (`L²` convergence gives convergence in measure, hence an a.e. convergent subsequence),
  by dominated convergence with the dominating function `Mψ |f| 1_{closedBall y s} ∈ L¹`
  (`IsWeakLogSol.integrableOn_rhs`).

Both limits exist, and `IsWeakLogSol.weakEq` identifies the two sequences, so the limits agree.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ m : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-- **(3) The weak equation for `v` against bounded `W₀^{1,2}` test functions.**  This is the
frozen statement `Komlos.Literature.Regularized.IsWeakLogSol.weakEq_memW0` of
`InteriorRegularity.lean`, verbatim.

See the module docstring: the flux term passes to the limit by `L²`–`L²` duality and the
(merely `L¹`) right-hand side by dominated convergence along an a.e. convergent subsequence of
uniformly bounded smooth approximants. -/
theorem IsWeakLogSol.weakEq_memW0 (hΨ : IsRegProfile Ψ) (hsol : IsWeakLogSol κ m Ψ U v G)
    {y : Euc d} {s : ℝ} (hs : Metric.closedBall y s ⊆ U) {T : Set (Euc d)} (hT : IsCompact T)
    (hTs : T ⊆ Metric.ball y s) {ψ : Euc d → ℝ} (hψ : MemW0 2 T ψ)
    (hψg : ∀ᵐ x, x ∉ T → weakGrad ψ x = 0) {Mψ : ℝ} (hψb : ∀ x, |ψ x| ≤ Mψ) :
    (∫ x, ⟪gradient Ψ (G x), weakGrad ψ x⟫) = -∫ x, regLogRhs κ m Ψ v G x * ψ x := by
  obtain ⟨c, C, hC⟩ := hΨ.exists_isRegProfileWith
  have hballU : Metric.ball y s ⊆ U := Metric.ball_subset_closedBall.trans hs
  -- the flux, restricted to the ball, is `L²`
  have hΦB : MemLp ((Metric.ball y s).indicator fun x => gradient Ψ (G x)) 2 := by
    rw [indicator_gradient_comp' hΨ]
    exact memLp_gradient_comp' hC (hsol.memLp_indicator' hs)
  have hΦB' : MemLp ((Metric.ball y s).indicator fun x => gradient Ψ (G x))
      (ENNReal.ofReal (Real.conjExponent (2 : ℝ))) := by
    rwa [ofReal_conjExponent_two]
  -- the approximating sequence
  obtain ⟨u, hcd, hcs, hts, hub, hu, hgr⟩ :=
    hψ.exists_contDiff_tendsto_eLpNorm_bounded one_lt_two Metric.isOpen_ball hT hTs hψb
  have hu1 : ∀ n, ContDiff ℝ 1 (u n) := fun n => (hcd n).of_le (by simp)
  have hgrn : ∀ n, MemLp (gradient (u n)) (ENNReal.ofReal (2 : ℝ)) := fun n =>
    (continuous_gradient (hu1 n)).memLp_of_hasCompactSupport (hasCompactSupport_gradient (hcs n))
  -- ### the flux term
  have hA0 : Tendsto (fun n => ∫ x,
      ⟪(Metric.ball y s).indicator (fun z => gradient Ψ (G z)) x, gradient (u n) x⟫) atTop
      (𝓝 (∫ x, ⟪(Metric.ball y s).indicator (fun z => gradient Ψ (G z)) x, weakGrad ψ x⟫)) := by
    have hwψ : MemLp (weakGrad ψ) (ENNReal.ofReal (2 : ℝ)) := hψ.memLp_weakGrad
    exact Komlos.Literature.tendsto_integral_inner_of_tendsto_eLpNorm one_lt_two hΦB' hgrn hwψ hgr
  have hrepl : ∀ n, (∫ x,
      ⟪(Metric.ball y s).indicator (fun z => gradient Ψ (G z)) x, gradient (u n) x⟫) =
      ∫ x, ⟪gradient Ψ (G x), gradient (u n) x⟫ := by
    intro n
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ⟪(Metric.ball y s).indicator (fun z => gradient Ψ (G z)) x, gradient (u n) x⟫ =
      ⟪gradient Ψ (G x), gradient (u n) x⟫
    by_cases hx : x ∈ Metric.ball y s
    · rw [Set.indicator_of_mem hx]
    · have hx' : x ∉ tsupport (u n) := fun h => hx (hts n h)
      rw [gradient_eq_zero_of_notMem_tsupport hx', inner_zero_right, inner_zero_right]
  have hreplψ : (∫ x,
      ⟪(Metric.ball y s).indicator (fun z => gradient Ψ (G z)) x, weakGrad ψ x⟫) =
      ∫ x, ⟪gradient Ψ (G x), weakGrad ψ x⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [hψg] with x hx
    show ⟪(Metric.ball y s).indicator (fun z => gradient Ψ (G z)) x, weakGrad ψ x⟫ =
      ⟪gradient Ψ (G x), weakGrad ψ x⟫
    by_cases hxb : x ∈ Metric.ball y s
    · rw [Set.indicator_of_mem hxb]
    · rw [hx fun h => hxb (hTs h), inner_zero_right, inner_zero_right]
  have hA : Tendsto (fun n => ∫ x, ⟪gradient Ψ (G x), gradient (u n) x⟫) atTop
      (𝓝 (∫ x, ⟪gradient Ψ (G x), weakGrad ψ x⟫)) := by
    rw [← hreplψ]
    exact hA0.congr fun n => hrepl n
  -- ### the equation for each approximant
  have heq : ∀ n, (∫ x, ⟪gradient Ψ (G x), gradient (u n) x⟫) =
      -∫ x, regLogRhs κ m Ψ v G x * u n x := fun n =>
    hsol.weakEq (u n) (hcd n) (hcs n) ((hts n).trans hballU)
  -- ### an a.e. convergent subsequence
  have hmeasu : ∀ n, AEStronglyMeasurable (u n) volume :=
    fun n => (hcd n).continuous.aestronglyMeasurable
  have hmeasψ : AEStronglyMeasurable ψ volume := hψ.memLp.aestronglyMeasurable
  have htim : TendstoInMeasure volume u atTop ψ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by simp) hmeasu hmeasψ hu
  obtain ⟨ns, hns, hae⟩ := htim.exists_seq_tendsto_ae
  -- ### dominated convergence on the right-hand side
  have hfint : IntegrableOn (regLogRhs κ m Ψ v G) (Metric.closedBall y s) volume :=
    hsol.integrableOn_rhs hΨ hs
  have hMψ0 : 0 ≤ Mψ := (abs_nonneg (ψ y)).trans (hψb y)
  set bound : Euc d → ℝ :=
    (Metric.closedBall y s).indicator (fun x => Mψ * |regLogRhs κ m Ψ v G x|) with hbound
  have hboundint : Integrable bound volume := by
    rw [hbound, integrable_indicator_iff measurableSet_closedBall]
    exact (hfint.abs).const_mul Mψ
  have hbound0 : ∀ x, 0 ≤ bound x := by
    intro x
    rw [hbound]
    by_cases hx : x ∈ Metric.closedBall y s
    · rw [Set.indicator_of_mem hx]; positivity
    · rw [Set.indicator_of_notMem hx]
  have hdom : ∀ n, ∀ᵐ x ∂volume, ‖regLogRhs κ m Ψ v G x * u n x‖ ≤ bound x := by
    intro n
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x ∈ Metric.ball y s
    · have hx' : x ∈ Metric.closedBall y s := Metric.ball_subset_closedBall hx
      rw [hbound, Set.indicator_of_mem hx', mul_comm Mψ]
      exact mul_le_mul_of_nonneg_left (hub n x) (abs_nonneg _)
    · have hx' : x ∉ tsupport (u n) := fun h => hx (hts n h)
      rw [image_eq_zero_of_notMem_tsupport hx', abs_zero, mul_zero]
      exact hbound0 x
  have hmf : AEStronglyMeasurable (regLogRhs κ m Ψ v G) volume :=
    (hsol.measurable_rhs hΨ).aestronglyMeasurable
  have hlim : ∀ᵐ x ∂volume, Tendsto
      (fun k => regLogRhs κ m Ψ v G x * u (ns k) x) atTop
      (𝓝 (regLogRhs κ m Ψ v G x * ψ x)) := by
    filter_upwards [hae] with x hx
    exact hx.const_mul _
  have hB : Tendsto (fun k => ∫ x, regLogRhs κ m Ψ v G x * u (ns k) x) atTop
      (𝓝 (∫ x, regLogRhs κ m Ψ v G x * ψ x)) :=
    tendsto_integral_of_dominated_convergence bound
      (fun k => hmf.mul (hmeasu (ns k))) hboundint (fun k => hdom (ns k)) hlim
  -- ### conclusion
  have hA' : Tendsto (fun k => ∫ x, ⟪gradient Ψ (G x), gradient (u (ns k)) x⟫) atTop
      (𝓝 (∫ x, ⟪gradient Ψ (G x), weakGrad ψ x⟫)) := hA.comp hns.tendsto_atTop
  have hB' : Tendsto (fun k => ∫ x, ⟪gradient Ψ (G x), gradient (u (ns k)) x⟫) atTop
      (𝓝 (-∫ x, regLogRhs κ m Ψ v G x * ψ x)) := by
    refine (hB.neg).congr fun k => ?_
    rw [← heq (ns k)]
  exact tendsto_nhds_unique hA' hB'

end Komlos.Literature.Regularized
