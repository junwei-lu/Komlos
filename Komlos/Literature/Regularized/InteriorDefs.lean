import Komlos.Literature.Regularized.ProfileBasic
import Komlos.Literature.PLaplacian.RegularitySchauder

/-!
# Interior regularity for the regularized route: the local objects (lane `L3`)

Lane `L3` (`reg/c2`) of `REGULARIZED_ROUTE.md`, Revision 2 (v).  The lane proves
`exists_regEigenData` (in
`Komlos/Literature/Regularized/Interior.lean`): the minimizer of the regularized energy has a
positive continuous representative `φ` whose negative logarithm `v = -log φ` is `C²` on `K` and
satisfies the pointwise equation of `RegEigenData.equation`.

This file fixes the local objects the chain is stated with.  Everything is *local*: the
statements live on an open set `U` (in the application `U = K`, or a ball `B ⋐ K`), and `v` is
never assumed to be globally Sobolev — near `∂K` it blows up.

## Main definitions

* `HasWeakGradientOn U v G` — `G` is a weak gradient of `v` on the open set `U`, tested against
  smooth functions compactly supported in `U`.  The shape of `integral_eq` is *exactly* the
  `hweak` hypothesis of `Komlos.Literature.contDiffOn_of_weakGradient`
  (`PLaplacian/RegularityCampanato.lean`), so that a continuous local weak gradient upgrades to a
  classical one with no glue.
* `regNatGrowth Ψ q = 2 (⟪∇Ψ q, q⟫ - Ψ q)` — the *natural growth* term `B(q)` of
  `REGULARIZED_ROUTE.md`, Revision 2 (v).
* `regLogRhs κ m Ψ v G = κ v + 2 m + B(G)` — the right-hand side of the equation for `v`.
* `IsWeakLogSol κ m Ψ U v G` — `v` is a weak solution of `div ∇Ψ(∇v) = κ v + 2 m + B(∇v)` on `U`.

## Main results

* `regNatGrowth_add_nonneg`, `regNatGrowth_le`, `abs_regNatGrowth_le` — the two-sided bound
  `|B(q)| ≤ 2 C ‖q‖² + 2 |Ψ 0|`, with `C` the upper ellipticity constant.  The lower bound is
  convexity (`IsRegProfile.zero_le_inner_gradient_sub`), the upper one is
  `⟪∇Ψ q, q⟫ ≤ C ‖q‖²` together with `Ψ q ≥ Ψ 0`.
* `continuous_regNatGrowth` — `B` is continuous.
* `HasWeakGradientOn.contDiffOn_one` — a continuous local weak gradient is the classical one.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {Ψ : Euc d → ℝ} {c C : ℝ}

/-! ### Local weak gradients -/

/-- `G` is a **weak gradient of `v` on the open set `U`**: for every smooth `ψ` compactly
supported in `U` and every direction `e`, `∫ v ∂_e ψ = -∫ ⟪G, e⟫ ψ`.

This is the *local* notion; `v` is not assumed integrable, or even defined, outside `U` in any
useful way (in the application `v = -log φ` blows up at `∂K`).  The shape is the `hweak`
hypothesis of `Komlos.Literature.contDiffOn_of_weakGradient`. -/
structure HasWeakGradientOn (U : Set (Euc d)) (v : Euc d → ℝ) (G : Euc d → Euc d) : Prop where
  /-- The integration-by-parts identity against smooth functions compactly supported in `U`. -/
  integral_eq : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∀ e : Euc d, ∫ x, v x * fderiv ℝ ψ x e = -∫ x, ⟪G x, e⟫ * ψ x

namespace HasWeakGradientOn

/-- A local weak gradient restricts to smaller open sets. -/
theorem mono {U U' : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}
    (h : HasWeakGradientOn U v G) (hU : U' ⊆ U) : HasWeakGradientOn U' v G :=
  ⟨fun ψ hψ hψs hψU => h.integral_eq ψ hψ hψs (hψU.trans hU)⟩

/-- **A continuous local weak gradient is the classical gradient**: if `v` is continuous on the
open set `U` and has a continuous weak gradient `G` there, then `v` is `C¹` on `U` and
`∇v = G` on `U`.  (`Komlos.Literature.contDiffOn_of_weakGradient`.) -/
theorem contDiffOn_one {U : Set (Euc d)} (hU : IsOpen U) {v : Euc d → ℝ} {G : Euc d → Euc d}
    (hv : ContinuousOn v U) (hG : ContinuousOn G U) (h : HasWeakGradientOn U v G) :
    ContDiffOn ℝ 1 v U ∧ ∀ x ∈ U, gradient v x = G x :=
  Komlos.Literature.contDiffOn_of_weakGradient hU hv hG h.integral_eq

end HasWeakGradientOn

/-! ### The natural growth term and the right-hand side -/

/-- The **natural growth term** `B(q) = 2 (⟪∇Ψ q, q⟫ - Ψ q)` of the equation for `v = -log u`
(`REGULARIZED_ROUTE.md`, Revision 2 (v); at a general exponent it is
`p (⟪∇Ψ q, q⟫ - Ψ q)`, and Revision 2 runs at `p = 2`). -/
noncomputable def regNatGrowth (Ψ : Euc d → ℝ) (q : Euc d) : ℝ :=
  2 * (⟪gradient Ψ q, q⟫ - Ψ q)

/-- The right-hand side of the equation for `v`: `κ v + 2 m + B(∇v)`, written with an abstract
vector field `G` in place of `∇v`. -/
noncomputable def regLogRhs (κ m : ℝ) (Ψ : Euc d → ℝ) (v : Euc d → ℝ) (G : Euc d → Euc d)
    (x : Euc d) : ℝ :=
  κ * v x + 2 * m + regNatGrowth Ψ (G x)

/-- `B(q) + 2 Ψ 0 ≥ 0`: the tangent plane of the convex `Ψ` at `q`, evaluated at the origin,
lies below `Ψ 0`. -/
theorem regNatGrowth_add_nonneg (hΨ : IsRegProfile Ψ) (q : Euc d) :
    0 ≤ regNatGrowth Ψ q + 2 * Ψ 0 := by
  have h := hΨ.zero_le_inner_gradient_sub q
  simp only [regNatGrowth]
  linarith

/-- `B(q) ≤ 2 C ‖q‖² - 2 Ψ 0`, with `C` the upper ellipticity constant: `⟪∇Ψ q, q⟫ ≤ C ‖q‖²`
(linear growth of `∇Ψ` and Cauchy–Schwarz) and `Ψ q ≥ Ψ 0` (quadratic lower bound). -/
theorem regNatGrowth_le (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    regNatGrowth Ψ q ≤ 2 * C * ‖q‖ ^ 2 - 2 * Ψ 0 := by
  have h1 : ⟪gradient Ψ q, q⟫ ≤ ‖gradient Ψ q‖ * ‖q‖ := real_inner_le_norm _ _
  have h2 : ‖gradient Ψ q‖ ≤ C * ‖q‖ := h.norm_gradient_le q
  have h3 : Ψ 0 + c / 2 * ‖q‖ ^ 2 ≤ Ψ q := h.quadratic_lower q
  have h4 : 0 ≤ c / 2 * ‖q‖ ^ 2 := mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
  have h5 : ‖gradient Ψ q‖ * ‖q‖ ≤ C * ‖q‖ * ‖q‖ :=
    mul_le_mul_of_nonneg_right h2 (norm_nonneg q)
  simp only [regNatGrowth]
  nlinarith [sq_nonneg ‖q‖]

/-- The two-sided bound `|B(q)| ≤ 2 C ‖q‖² + 2 |Ψ 0|`. -/
theorem abs_regNatGrowth_le (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    |regNatGrowth Ψ q| ≤ 2 * C * ‖q‖ ^ 2 + 2 * |Ψ 0| := by
  have h1 := regNatGrowth_add_nonneg h.toIsRegProfile q
  have h2 := regNatGrowth_le h q
  have h3 : Ψ 0 ≤ |Ψ 0| := le_abs_self _
  have h4 : -|Ψ 0| ≤ Ψ 0 := neg_abs_le _
  rw [abs_le]
  constructor <;> nlinarith

/-- `B` is continuous. -/
theorem continuous_regNatGrowth (hΨ : IsRegProfile Ψ) : Continuous (regNatGrowth Ψ) := by
  have hg : Continuous (gradient Ψ) := hΨ.contDiff_gradient.continuous
  exact continuous_const.mul ((hg.inner continuous_id).sub hΨ.contDiff.continuous)

/-! ### Weak solutions of the logarithmic equation -/

/-- **`v` is a weak solution of `div ∇Ψ(∇v) = κ v + 2 m + B(∇v)` on the open set `U`**
(`REGULARIZED_ROUTE.md`, Revision 2 (v)): the equation satisfied by `v = -log φ` for a minimizer
`φ` of the regularized energy, with `m = regMin 2 κ Ψ K`.

Testing against `ψ ∈ C_c^∞(U)` and integrating the divergence by parts turns the pointwise
equation into `∫ ⟪∇Ψ(∇v), ∇ψ⟫ = -∫ (κ v + 2 m + B(∇v)) ψ`, which is `weakEq`. -/
structure IsWeakLogSol (κ m : ℝ) (Ψ : Euc d → ℝ) (U : Set (Euc d)) (v : Euc d → ℝ)
    (G : Euc d → Euc d) : Prop where
  /-- `U` is open. -/
  isOpen : IsOpen U
  /-- `v` is continuous on `U` (in particular locally bounded there). -/
  continuousOn : ContinuousOn v U
  /-- `v` is globally measurable. -/
  measurable : Measurable v
  /-- `G` is globally measurable. -/
  measurable_grad : Measurable G
  /-- `G` is a weak gradient of `v` on `U`. -/
  hasWeakGradientOn : HasWeakGradientOn U v G
  /-- `G` is square integrable on every closed ball inside `U`. -/
  integrableOn_sq : ∀ (x₀ : Euc d) (r : ℝ), Metric.closedBall x₀ r ⊆ U →
    IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ r) volume
  /-- The weak equation. -/
  weakEq : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    (∫ x, ⟪gradient Ψ (G x), gradient ψ x⟫) = -∫ x, regLogRhs κ m Ψ v G x * ψ x

namespace IsWeakLogSol

variable {κ m : ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-- A weak solution on `U` restricts to any open `U' ⊆ U`. -/
theorem mono {U' : Set (Euc d)} (h : IsWeakLogSol κ m Ψ U v G) (hU' : IsOpen U')
    (hsub : U' ⊆ U) : IsWeakLogSol κ m Ψ U' v G where
  isOpen := hU'
  continuousOn := h.continuousOn.mono hsub
  measurable := h.measurable
  measurable_grad := h.measurable_grad
  hasWeakGradientOn := h.hasWeakGradientOn.mono hsub
  integrableOn_sq x₀ r hr := h.integrableOn_sq x₀ r (hr.trans hsub)
  weakEq ψ hψ hψs hψU := h.weakEq ψ hψ hψs (hψU.trans hsub)

/-- The weak equation transported to a field that agrees with `G` on `U`. -/
theorem congr_grad {G' : Euc d → Euc d} (h : IsWeakLogSol κ m Ψ U v G) (hG' : Measurable G')
    (heq : ∀ x ∈ U, G' x = G x) : IsWeakLogSol κ m Ψ U v G' where
  isOpen := h.isOpen
  continuousOn := h.continuousOn
  measurable := h.measurable
  measurable_grad := hG'
  hasWeakGradientOn :=
    ⟨fun ψ hψ hψs hψU e => by
      rw [h.hasWeakGradientOn.integral_eq ψ hψ hψs hψU e]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ⟪G x, e⟫ * ψ x = ⟪G' x, e⟫ * ψ x
      by_cases hx : x ∈ tsupport ψ
      · rw [heq x (hψU hx)]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]⟩
  integrableOn_sq x₀ r hr := by
    refine ((h.integrableOn_sq x₀ r hr).congr_fun (fun x hx => ?_) measurableSet_closedBall)
    rw [heq x (hr hx)]
  weakEq ψ hψ hψs hψU := by
    have e1 : (∫ x, ⟪gradient Ψ (G' x), gradient ψ x⟫) =
        ∫ x, ⟪gradient Ψ (G x), gradient ψ x⟫ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ⟪gradient Ψ (G' x), gradient ψ x⟫ = ⟪gradient Ψ (G x), gradient ψ x⟫
      by_cases hx : x ∈ tsupport ψ
      · rw [heq x (hψU hx)]
      · rw [gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right, inner_zero_right]
    have e2 : (∫ x, regLogRhs κ m Ψ v G' x * ψ x) =
        ∫ x, regLogRhs κ m Ψ v G x * ψ x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show regLogRhs κ m Ψ v G' x * ψ x = regLogRhs κ m Ψ v G x * ψ x
      by_cases hx : x ∈ tsupport ψ
      · simp only [regLogRhs, heq x (hψU hx)]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
    rw [e1, e2]
    exact h.weakEq ψ hψ hψs hψU

end IsWeakLogSol

end Komlos.Literature.Regularized
