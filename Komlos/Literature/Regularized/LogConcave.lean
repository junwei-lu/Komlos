import Komlos.Literature.Regularized.Korevaar2
import Komlos.Literature.Regularized.Interior
import Komlos.Literature.Regularized.ProfileBasic
import Komlos.Literature.Regularized.DomainLimitMinimizer
import Komlos.Literature.Regularized.DomainLimitEnergy

/-!
# Log-concavity of the regularized minimizer

This is the conclusion of the `L4` lane of `REGULARIZED_ROUTE.md` ("Korevaar with two
functions"): for `D : RegEigenData 2 κ Ψ K`, the function `-log D.φ` is convex on `K`.

## The argument

Fix `x₀ ∈ K` and let `K_n = x₀ + s_n (K - x₀)` with `s_n ↑ 1` be the inner domains of
`Komlos/Literature/Regularized/DomainLimitDomain.lean`; they are `IsGoodConvex`, increase, have
`closure K_n ⊆ K`, and exhaust `K`.  On each of them `exists_regEigenData` produces data `D_n`.

1. `RegEigenData.isSmoothAffineReactionSolution` packages `-log D.φ` and `-log D_n.φ` as
   solutions of the *same* quasilinear equation `div ∇Ψ(∇v) = κ v + c + reaction(∇v)` with flux
   `∇Ψ`, reaction `regReaction Ψ q = 2 (⟪∇Ψ q, q⟫ - Ψ q)` and constants `c = 2 regMin K`,
   `c' = 2 regMin K_n`.  The ellipticity field is `IsRegProfile.exists_elliptic_fderiv_gradient`.
2. `RegEigenData.mul_le_exp_mul_sq` feeds this to `mul_le_exp_mul_sq_of_affine_reaction`; the
   compact superlevel sets of `D_n.φ` inside `K_n` come from continuity together with
   `D_n.eq_zero_of_notMem` (the superlevel set is closed in the compact `closure K_n`), and the
   upper bound for `D_n.φ` from continuity on that compact set.
3. `tendsto_regMin_innerDomain` (`DomainLimitEnergy`) makes the errors
   `δ_n = 2 max 0 ((c' - c)/κ)` tend to `0`.
4. `exists_subseq_ae_tendsto_innerDomain` (`DomainLimitMinimizer`) gives a subsequence along
   which `D_n.φ → D.φ` a.e., and `convexOn_neg_log_of_tendsto_midpoint` concludes.

`RegEigenData.convexOn_neg_log` is the frozen lane statement of `L4` (formerly a named
`sorry` in `Interface.lean`, deleted by lane `L7` in favour of this proof).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

open Korevaar

variable {d : ℕ} {κ : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)}

/-! ### The regularized equation as an affine-reaction solution -/

/-- On an open set, the gradient of a `C²` function is `C¹`. -/
theorem contDiffOn_gradient_of_contDiffOn {Ω : Set (Euc d)} (hΩ : IsOpen Ω) {v : Euc d → ℝ}
    (hv : ContDiffOn ℝ 2 v Ω) : ContDiffOn ℝ 1 (gradient v) Ω := by
  have h := hv.fderiv_of_isOpen (m := 1) hΩ (by norm_num)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h

/-- The gradient-dependent part of the reaction term of the regularized logarithmic equation
(`REGULARIZED_ROUTE.md`, Revision 2): `2 (⟪∇Ψ q, q⟫ - Ψ q)`.  It is the *same* function for
every domain; only the additive constant `2 regMin 2 κ Ψ K` changes, which is exactly the shape
`Korevaar2.mul_le_exp_mul_sq_of_affine_reaction` requires. -/
noncomputable def regReaction (Ψ : Euc d → ℝ) (q : Euc d) : ℝ :=
  2 * (⟪gradient Ψ q, q⟫ - Ψ q)

/-- **The classical data of the regularized route is an affine-reaction solution.**  The flux is
`∇Ψ`, the reaction is `regReaction Ψ` and the constant is `2 · regMin 2 κ Ψ K`; this is exactly
`RegEigenData.equation` at `p = 2`, and the ellipticity field is
`IsRegProfile.exists_elliptic_fderiv_gradient`. -/
theorem RegEigenData.isSmoothAffineReactionSolution (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) (D : RegEigenData 2 κ Ψ K) :
    IsSmoothAffineReactionSolution K (gradient Ψ)
      (fun q => 2 * regMin 2 κ Ψ K + regReaction Ψ q)
      (fun x => -Real.log (D.φ x)) κ where
  differentiable := D.contDiffOn_two.differentiableOn (by norm_num)
  gradient_differentiable :=
    (contDiffOn_gradient_of_contDiffOn hK.isOpen D.contDiffOn_two).differentiableOn (by simp)
  elliptic x _ := hΨ.exists_elliptic_fderiv_gradient _
  equation x hx := by
    simp only [regReaction]
    rw [D.equation x hx]
    ring

/-! ### The two-function midpoint inequality on an inner domain -/

/-- **The Korevaar midpoint inequality between an inner domain and `K`.**  With `D` the data on
`K` and `D'` the data on an inner domain `K'` with `closure K' ⊆ K`,

  `D'.φ x * D'.φ y ≤ exp (2 max 0 (2 (m(K') - m(K))/κ)) * D.φ (midpoint x y)²`  for `x, y ∈ K'`.

This is `Korevaar2.mul_le_exp_mul_sq_of_affine_reaction` applied to the two solutions of
`RegEigenData.isSmoothAffineReactionSolution`. -/
theorem RegEigenData.mul_le_exp_mul_sq (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) (D : RegEigenData 2 κ Ψ K) {K' : Set (Euc d)} (hK' : IsGoodConvex K')
    (hcl : closure K' ⊆ K) (D' : RegEigenData 2 κ Ψ K') {x y : Euc d} (hx : x ∈ K')
    (hy : y ∈ K') :
    D'.φ x * D'.φ y ≤
      Real.exp (2 * max 0 ((2 * regMin 2 κ Ψ K' - 2 * regMin 2 κ Ψ K) / κ)) *
        D.φ (midpoint ℝ x y) ^ 2 := by
  have hKc : IsCompact (closure K') := hK'.isBounded.isCompact_closure
  -- `D'.φ` is bounded on `K'`
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn D'.continuous.continuousOn
  have hub : ∃ B : ℝ, ∀ z ∈ K', D'.φ z ≤ B :=
    ⟨B, fun z hz => (le_abs_self _).trans (hB z (subset_closure hz))⟩
  -- the superlevel sets of `D'.φ` inside `K'` are compact
  have hcompact : ∀ ε : ℝ, 0 < ε → IsCompact {z ∈ K' | ε ≤ D'.φ z} := by
    intro ε hε
    have hset : {z ∈ K' | ε ≤ D'.φ z} = closure K' ∩ {z | ε ≤ D'.φ z} := by
      ext z
      constructor
      · rintro ⟨hz, hzε⟩
        exact ⟨subset_closure hz, hzε⟩
      · rintro ⟨hz, hzε⟩
        simp only [Set.mem_ofPred_eq] at hzε
        refine ⟨?_, hzε⟩
        by_contra hzn
        rw [D'.eq_zero_of_notMem z hzn] at hzε
        linarith
    rw [hset]
    exact hKc.inter_right (isClosed_le continuous_const D'.continuous)
  exact mul_le_exp_mul_sq_of_affine_reaction (c := 2 * regMin 2 κ Ψ K)
    (c' := 2 * regMin 2 κ Ψ K') (reaction := regReaction Ψ) hκ hK.isOpen hK'.isOpen hK'.convex
    hK'.isBounded hcl D.continuous.continuousOn D.pos D'.continuous.continuousOn D'.pos hub
    hcompact (D.isSmoothAffineReactionSolution hΨ hK) (D'.isSmoothAffineReactionSolution hΨ hK')
    hx hy

/-! ### Log-concavity -/

/-- **(L4, `reg/korevaar`)** Log-concavity of the regularized minimizer: Korevaar's concavity
maximum principle run with two functions on the inner domains `K_n ⋐ K`, then `K_n ↑ K`.

This is the frozen lane statement `RegEigenData.convexOn_neg_log`, formerly a named `sorry` of
`Interface.lean`. -/
theorem RegEigenData.convexOn_neg_log (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) (D : RegEigenData 2 κ Ψ K) :
    ConvexOn ℝ K (fun x => -Real.log (D.φ x)) := by
  obtain ⟨x₀, hx₀⟩ := hK.nonempty
  have hKngood : ∀ n, IsGoodConvex (innerDomain x₀ K n) := fun n =>
    isGoodConvex_innerDomain hK hx₀ n
  have hKncl : ∀ n, closure (innerDomain x₀ K n) ⊆ K := fun n =>
    closure_innerDomain_subset hK hx₀ n
  have Dn : ∀ n, RegEigenData 2 κ Ψ (innerDomain x₀ K n) := fun n =>
    (exists_regEigenData hκ hΨ (hKngood n)).some
  -- the errors tend to zero
  have hscal : Tendsto (fun n => regMin 2 κ Ψ (innerDomain x₀ K n)) atTop
      (𝓝 (regMin 2 κ Ψ K)) := tendsto_regMin_innerDomain hκ hΨ hK hx₀ D Dn
  set δ : ℕ → ℝ := fun n =>
    2 * max 0 ((2 * regMin 2 κ Ψ (innerDomain x₀ K n) - 2 * regMin 2 κ Ψ K) / κ) with hδ_def
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h2 : Tendsto
        (fun n => 2 * regMin 2 κ Ψ (innerDomain x₀ K n) - 2 * regMin 2 κ Ψ K) atTop (𝓝 0) := by
      have h := (hscal.const_mul (2 : ℝ)).sub_const (2 * regMin 2 κ Ψ K)
      simpa using h
    have h1 : Tendsto
        (fun n => (2 * regMin 2 κ Ψ (innerDomain x₀ K n) - 2 * regMin 2 κ Ψ K) / κ) atTop
        (𝓝 0) := by simpa using h2.div_const κ
    have h3 : Tendsto
        (fun n => max 0 ((2 * regMin 2 κ Ψ (innerDomain x₀ K n) - 2 * regMin 2 κ Ψ K) / κ))
        atTop (𝓝 (max 0 0)) := tendsto_const_nhds.max h1
    rw [max_self] at h3
    have h4 := h3.const_mul (2 : ℝ)
    rw [mul_zero] at h4
    exact h4
  -- the a.e. convergent subsequence
  obtain ⟨σ, hσ, hae⟩ := exists_subseq_ae_tendsto_innerDomain hκ hΨ hK hx₀ D Dn
  have hδσ : Tendsto (fun k => δ (σ k)) atTop (𝓝 0) := hδ.comp hσ.tendsto_atTop
  refine convexOn_neg_log_of_tendsto_midpoint hK.isOpen hK.convex D.continuous.continuousOn D.pos
    (δ := fun k => δ (σ k)) (Kn := fun k => innerDomain x₀ K (σ k))
    (φn := fun k => (Dn (σ k)).φ) hδσ ?_ ?_ ?_ hae
  · exact fun j k hjk => monotone_innerDomain hK hx₀ (hσ.monotone hjk)
  · refine Set.Subset.antisymm (Set.iUnion_subset fun k => innerDomain_subset hK hx₀ (σ k)) ?_
    intro x hx
    have hx' : x ∈ ⋃ n, innerDomain x₀ K n := by rw [iUnion_innerDomain hK hx₀]; exact hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx'
    exact Set.mem_iUnion.2 ⟨n, monotone_innerDomain hK hx₀ hσ.le_apply hn⟩
  · intro k x hx y hy
    exact RegEigenData.mul_le_exp_mul_sq hκ hΨ hK D (hKngood (σ k)) (hKncl (σ k)) (Dn (σ k)) hx hy

end Komlos.Literature.Regularized
