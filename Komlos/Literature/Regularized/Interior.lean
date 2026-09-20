import Komlos.Literature.Regularized.InteriorWeakEqLog
import Komlos.Literature.Regularized.InteriorC2

/-!
# `exists_regEigenData` for the regularized route (lane `L3`)

The last two steps of lane `L3` (`reg/c2`) of `REGULARIZED_ROUTE.md`, Revision 2 (v):

* **step 6, the pointwise equation** (`IsWeakLogSol.divergence_eq`): once `v` is known to be `C²`
  on the open set `U`, the weak equation
  `∫ ⟪∇Ψ(∇v), ∇ψ⟫ = -∫ (κ v + 2 m + B(∇v)) ψ` integrates by parts
  (`Korevaar.integral_inner_gradient_eq_neg_integral_divergence`) into
  `∫ (div ∇Ψ(∇v) - κ v - 2 m - B(∇v)) ψ = 0` for every test function, and the fundamental lemma
  of the calculus of variations (`Korevaar.eq_zero_of_integral_mul_testFn_eq_zero`, applicable
  because the bracket is continuous on `U`) gives the pointwise equation;
* **the assembly** (`exists_regEigenData`): `exists_pos_continuous_minimizer` (`L1` + `L2`),
  `exists_isWeakLogSol` (step 1), `IsWeakLogSol.contDiffOn_two` (steps 2–5) and the pointwise
  equation are packaged into a `RegEigenData 2 κ Ψ K`.

`exists_regEigenData` is the frozen lane statement of
`REGULARIZED_ROUTE.md` (Revision 2) for lane `L3`; it used to be a named `sorry` in
`Interface.lean`, which lane `L7` deleted in favour of this proof.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ m : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-! ### Auxiliary continuity facts -/

/-- On an open set, the gradient of a `C²` function is `C¹`. -/
theorem contDiffOn_gradient_of_two {Ω : Set (Euc d)} (hΩ : IsOpen Ω) {v : Euc d → ℝ}
    (hv : ContDiffOn ℝ 2 v Ω) : ContDiffOn ℝ 1 (gradient v) Ω := by
  have h := hv.fderiv_of_isOpen (m := 1) hΩ (by norm_num)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h

/-- The divergence of a `C¹` vector field is continuous. -/
theorem continuousOn_divergence {W : Euc d → Euc d} {Ω : Set (Euc d)} (hΩ : IsOpen Ω)
    (hW : ContDiffOn ℝ 1 W Ω) : ContinuousOn (Korevaar.divergence W) Ω := by
  have hfd : ContinuousOn (fderiv ℝ W) Ω := hW.continuousOn_fderiv_of_isOpen hΩ le_rfl
  unfold Korevaar.divergence
  exact continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.inner (hfd.clm_apply continuousOn_const)

/-! ### Step 6: the pointwise equation -/

/-- **The pointwise equation from the weak one** (lane `L3`, step 6).  A `C²` weak solution of
`div ∇Ψ(∇v) = κ v + 2 m + B(∇v)` on the open set `U` satisfies the equation pointwise on `U`.

The two ingredients are `Korevaar.integral_inner_gradient_eq_neg_integral_divergence`
(integration by parts for a `C¹` field against a compactly supported test function) and
`Korevaar.eq_zero_of_integral_mul_testFn_eq_zero` (the fundamental lemma of the calculus of
variations for a function continuous on `U`). -/
theorem IsWeakLogSol.divergence_eq (hΨ : IsRegProfile Ψ) (hsol : IsWeakLogSol κ m Ψ U v G)
    (h2 : ContDiffOn ℝ 2 v U) (hG : ∀ᵐ x ∂(volume.restrict U), G x = gradient v x) :
    ∀ x ∈ U, Korevaar.divergence (fun y => gradient Ψ (gradient v y)) x =
      κ * v x + 2 * m +
        2 * (⟪gradient Ψ (gradient v x), gradient v x⟫ - Ψ (gradient v x)) := by
  have hU : IsOpen U := hsol.isOpen
  have hGU : ∀ᵐ x, x ∈ U → G x = gradient v x := (ae_restrict_iff' hU.measurableSet).1 hG
  have hgv : ContDiffOn ℝ 1 (gradient v) U := contDiffOn_gradient_of_two hU h2
  have hW : ContDiffOn ℝ 1 (fun y => gradient Ψ (gradient v y)) U := by
    have hg1 : ContDiff ℝ 1 (gradient Ψ) := hΨ.contDiff_gradient.of_le (by simp)
    have h := hg1.comp_contDiffOn hgv
    simpa only [Function.comp_def] using h
  have hvc : ContinuousOn v U := hsol.continuousOn
  have hgvc : ContinuousOn (gradient v) U := hgv.continuousOn
  have hdivc : ContinuousOn (Korevaar.divergence fun y => gradient Ψ (gradient v y)) U :=
    continuousOn_divergence hU hW
  have hrhsc : ContinuousOn (fun y => κ * v y + 2 * m + regNatGrowth Ψ (gradient v y)) U :=
    ((continuousOn_const.mul hvc).add continuousOn_const).add
      ((continuous_regNatGrowth hΨ).comp_continuousOn hgvc)
  have hgc : ContinuousOn (fun y => Korevaar.divergence
      (fun z => gradient Ψ (gradient v z)) y -
        (κ * v y + 2 * m + regNatGrowth Ψ (gradient v y))) U := hdivc.sub hrhsc
  -- the tested identity
  have key : ∀ ψ : Euc d → ℝ, IsTestFn U ψ → (∀ x, 0 ≤ ψ x) →
      ∫ x, (Korevaar.divergence (fun z => gradient Ψ (gradient v z)) x -
        (κ * v x + 2 * m + regNatGrowth Ψ (gradient v x))) * ψ x = 0 := by
    intro ψ hψ _
    have hψK : ∀ x ∉ tsupport ψ, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    have hψcont : Continuous ψ := hψ.contDiff.continuous
    have hcs : HasCompactSupport ψ := hψ.hasCompactSupport
    have hsupp : tsupport ψ ⊆ U := hψ.supp_subset
    -- integration by parts
    have hibp := Korevaar.integral_inner_gradient_eq_neg_integral_divergence hU hW
      (hψ.contDiff.of_le (by simp)) hcs hsupp
    -- the weak equation, with `G` replaced by `∇v`
    have hweak := hsol.weakEq ψ hψ.contDiff hcs hsupp
    have e1 : (∫ x, ⟪gradient Ψ (G x), gradient ψ x⟫) =
        ∫ x, ⟪gradient Ψ (gradient v x), gradient ψ x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [hGU] with x hx
      show ⟪gradient Ψ (G x), gradient ψ x⟫ = ⟪gradient Ψ (gradient v x), gradient ψ x⟫
      by_cases hxs : x ∈ tsupport ψ
      · rw [hx (hsupp hxs)]
      · rw [gradient_eq_zero_of_notMem_tsupport hxs, inner_zero_right, inner_zero_right]
    have e2 : (∫ x, regLogRhs κ m Ψ v G x * ψ x) =
        ∫ x, (κ * v x + 2 * m + regNatGrowth Ψ (gradient v x)) * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hGU] with x hx
      show regLogRhs κ m Ψ v G x * ψ x =
        (κ * v x + 2 * m + regNatGrowth Ψ (gradient v x)) * ψ x
      by_cases hxs : x ∈ tsupport ψ
      · simp only [regLogRhs, hx (hsupp hxs)]
      · rw [hψK x hxs, mul_zero, mul_zero]
    rw [e1, e2] at hweak
    -- integrability of the two products
    have hint1 : Integrable fun x =>
        Korevaar.divergence (fun z => gradient Ψ (gradient v z)) x * ψ x :=
      (Korevaar.continuous_mul_of_continuousOn hU hdivc hψcont (isClosed_tsupport ψ) hsupp
        hψK).integrable_of_hasCompactSupport
        (Korevaar.hasCompactSupport_of_zero_outside hcs fun x hx => by
          rw [hψK x hx, mul_zero])
    have hint2 : Integrable fun x =>
        (κ * v x + 2 * m + regNatGrowth Ψ (gradient v x)) * ψ x :=
      (Korevaar.continuous_mul_of_continuousOn hU hrhsc hψcont (isClosed_tsupport ψ) hsupp
        hψK).integrable_of_hasCompactSupport
        (Korevaar.hasCompactSupport_of_zero_outside hcs fun x hx => by
          rw [hψK x hx, mul_zero])
    have hsplit : (∫ x, (Korevaar.divergence (fun z => gradient Ψ (gradient v z)) x -
          (κ * v x + 2 * m + regNatGrowth Ψ (gradient v x))) * ψ x) =
        (∫ x, Korevaar.divergence (fun z => gradient Ψ (gradient v z)) x * ψ x) -
          ∫ x, (κ * v x + 2 * m + regNatGrowth Ψ (gradient v x)) * ψ x := by
      rw [← integral_sub hint1 hint2]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    have hcomm : (∫ x, ψ x * Korevaar.divergence (fun z => gradient Ψ (gradient v z)) x) =
        ∫ x, Korevaar.divergence (fun z => gradient Ψ (gradient v z)) x * ψ x :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [hsplit, ← hcomm]
    rw [hibp] at hweak
    linarith [hweak]
  intro x hx
  have h0 := Korevaar.eq_zero_of_integral_mul_testFn_eq_zero hU hgc key hx
  simp only [regNatGrowth] at h0
  linarith

/-! ### The assembly -/

/-- **(L3, `reg/c2`)** The classical data of the regularized route: this is the frozen statement
`Komlos.Literature.Regularized.exists_regEigenData` of `Interface.lean`, verbatim.

`exists_pos_continuous_minimizer` produces a continuous minimizer `φ`, positive on `K` and
vanishing off `K` (lanes `L1`, `L2` plus the `=ᵐ`-transfer of minimality);
`exists_isWeakLogSol` turns the weak Euler–Lagrange equation into the weak equation for
`v = -log φ`; `IsWeakLogSol.contDiffOn_two` is the interior regularity chain of
`InteriorRegularity.lean`; and `IsWeakLogSol.divergence_eq` converts the weak equation into the
pointwise one, which is `RegEigenData.equation` at `p = 2`. -/
theorem exists_regEigenData {K : Set (Euc d)} (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) : Nonempty (RegEigenData 2 κ Ψ K) := by
  obtain ⟨φ, hφc, hφ0, hφpos, hφmin⟩ := exists_pos_continuous_minimizer hκ hΨ hK
  obtain ⟨G, hsol⟩ := exists_isWeakLogSol hκ hΨ hK hφc hφ0 hφpos hφmin
  obtain ⟨h2, hG⟩ := hsol.contDiffOn_two hΨ
  exact ⟨{ φ := φ
           continuous := hφc
           eq_zero_of_notMem := hφ0
           pos := hφpos
           isRegMinimizer := hφmin
           contDiffOn_two := h2
           equation := fun x hx => hsol.divergence_eq hΨ h2 hG x hx }⟩

end Komlos.Literature.Regularized
