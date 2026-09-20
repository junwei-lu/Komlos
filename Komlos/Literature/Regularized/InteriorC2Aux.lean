import Komlos.Literature.Regularized.InteriorSchauderDrift

/-!
# Difference quotients of the logarithmic equation (lane `L3c`)

The linear equation satisfied by the difference quotients

`w_s(x) = (v(x + h) - v(x)) / s`,   `‖h‖ = s`,

of a weak solution `v` of `div ∇Ψ(∇v) = κ v + 2 m + B(∇v)` (`IsWeakLogSol`), together with the
bounds its data satisfy.  Everything here is the exact analogue, for the globally smooth and
globally uniformly elliptic `∇Ψ`, of what
`Komlos.Literature.integral_inner_difference_quotient_eq` does for the degenerate flux
`a = F^{p-1} ∇F` away from the origin; the simplification is that `∇Ψ` is smooth *everywhere*,
so no convex set avoiding the origin has to be carried around.

## Contents

* `gradient_sub_eq_integral_fderiv` — the mean value formula
  `∇Ψ(η) - ∇Ψ(ξ) = (∫₀¹ D²Ψ(ξ + t(η - ξ)) dt)(η - ξ)`;
* `integral_fderiv_gradient_bounds` — ellipticity, boundedness and Lipschitz dependence of the
  averaged Hessian `∫₀¹ D²Ψ(ξ + t(η - ξ)) dt`;
* `diffQuotCoeff` — that averaged Hessian along `(∇v(x), ∇v(x + h))`, the coefficient field of
  the difference-quotient equation;
* `IsWeakLogSol.integral_inner_translate` — the weak equation for the translate `v(· + h)`;
* `IsWeakLogSol.integral_inner_diffQuot` — **the difference-quotient equation**
  `∫ ⟪A_h ∇w_s, ∇ψ⟫ = ∫ g_s ψ` with
  `g_s = -(κ w_s + (B(∇v(· + h)) - B(∇v))/s)`.

The right-hand side `g_s` is **not** bounded uniformly in `s`: the natural-growth term `B(∇v)`
is only Hölder, so its difference quotient blows up like `s^{β-1}`.  What *is* uniform is the
bound `|g_s| ≤ |κ| K + L ‖∇w_s‖` with `L` a Lipschitz constant of `B` on a ball containing the
values of `∇v` — a right-hand side with a *first-order* term, which is exactly what
`Komlos/Literature/Regularized/InteriorSchauderDrift.lean` handles.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace Interval

namespace Komlos.Literature.Regularized

open Komlos.Literature

variable {d : ℕ} {Ψ : Euc d → ℝ} {c C : ℝ}

/-! ### The Hessian of a regularized profile -/

/-- `D²Ψ = D(∇Ψ)` is `C¹`. -/
theorem IsRegProfile.contDiff_fderiv_gradient (hΨ : IsRegProfile Ψ) :
    ContDiff ℝ 1 (fderiv ℝ (gradient Ψ)) := by
  rw [← contDiffOn_univ]
  exact hΨ.contDiff_gradient.contDiffOn.fderiv_of_isOpen isOpen_univ
    (WithTop.coe_le_coe.2 le_top)

/-- `D²Ψ` is continuous. -/
theorem IsRegProfile.continuous_fderiv_gradient (hΨ : IsRegProfile Ψ) :
    Continuous (fderiv ℝ (gradient Ψ)) :=
  hΨ.contDiff_fderiv_gradient.continuous

/-- The natural-growth term `B(q) = 2(⟪∇Ψ q, q⟫ - Ψ q)` is `C¹`. -/
theorem contDiff_regNatGrowth (hΨ : IsRegProfile Ψ) : ContDiff ℝ 1 (regNatGrowth Ψ) := by
  have h1 : ContDiff ℝ 1 (gradient Ψ) := hΨ.contDiff_gradient.of_le (by simp)
  have h2 : ContDiff ℝ 1 Ψ := hΨ.contDiff.of_le (by simp)
  have : ContDiff ℝ 1 fun q : Euc d => 2 * (⟪gradient Ψ q, q⟫ - Ψ q) :=
    contDiff_const.mul ((h1.inner ℝ contDiff_id).sub h2)
  exact this

/-- **Mean value formula for `∇Ψ`**: `∇Ψ(η) - ∇Ψ(ξ) = (∫₀¹ D²Ψ(ξ + t(η - ξ)) dt)(η - ξ)`.
The analogue of `Komlos.Literature.IsSmoothStrictNorm.flux_sub_eq_integral_fderiv`, valid on all
of `Euc d` because `∇Ψ` is globally smooth. -/
theorem gradient_sub_eq_integral_fderiv (hΨ : IsRegProfile Ψ) (ξ η : Euc d) :
    gradient Ψ η - gradient Ψ ξ =
      (∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ))) (η - ξ) := by
  have hline : Continuous fun t : ℝ => ξ + t • (η - ξ) := by fun_prop
  have hcont : ContinuousOn (fun t : ℝ => fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ)))
      (uIcc 0 1) := (hΨ.continuous_fderiv_gradient.comp hline).continuousOn
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => gradient Ψ (ξ + t • (η - ξ)))
      (fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ)) (η - ξ)) t := by
    intro t _
    have hl : HasDerivAt (fun t : ℝ => ξ + t • (η - ξ)) (η - ξ) t := by
      simpa using ((hasDerivAt_id t).smul_const (η - ξ)).const_add ξ
    exact (hΨ.hasFDerivAt_gradient _).comp_hasDerivAt t hl
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((ContinuousLinearMap.apply ℝ (Euc d) (η - ξ)).continuous.comp_continuousOn
      hcont).intervalIntegrable
  rw [one_smul, zero_smul, add_zero, add_sub_cancel] at hFTC
  rw [← hFTC]
  exact (ContinuousLinearMap.apply ℝ (Euc d) (η - ξ)).intervalIntegral_comp_comm
    hcont.intervalIntegrable

/-- **Bounds for the averaged Hessian** `∫₀¹ D²Ψ(ξ + t(η - ξ)) dt`: it inherits the ellipticity
constants of `D²Ψ` and depends Lipschitz-continuously on the endpoints, with the Lipschitz
constant of `D²Ψ` on a convex set containing them. -/
theorem integral_fderiv_gradient_bounds (h : IsRegProfileWith Ψ c C) {N : Set (Euc d)}
    (hNcv : Convex ℝ N) {L : ℝ}
    (hL : ∀ ξ ∈ N, ∀ η ∈ N, ‖fderiv ℝ (gradient Ψ) ξ - fderiv ℝ (gradient Ψ) η‖ ≤ L * ‖ξ - η‖)
    (hL0 : 0 ≤ L) {ξ η ξ' η' : Euc d} (hξ : ξ ∈ N) (hη : η ∈ N) (hξ' : ξ' ∈ N) (hη' : η' ∈ N) :
    (∀ ζ, c * ‖ζ‖ ^ 2 ≤
        ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ))) ζ, ζ⟫) ∧
      ‖∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ))‖ ≤ C ∧
      ‖(∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ))) -
        ∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (ξ' + t • (η' - ξ'))‖ ≤
          L * (‖ξ - ξ'‖ + ‖η - η'‖) := by
  have hΨ := h.toIsRegProfile
  have hseg : ∀ {a b : Euc d}, a ∈ N → b ∈ N → ∀ t ∈ uIcc (0 : ℝ) 1, a + t • (b - a) ∈ N := by
    intro a b ha hb t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact hNcv.add_smul_sub_mem ha hb ht
  have hcont : ∀ a b : Euc d,
      ContinuousOn (fun t : ℝ => fderiv ℝ (gradient Ψ) (a + t • (b - a))) (uIcc 0 1) := by
    intro a b
    exact (hΨ.continuous_fderiv_gradient.comp (by fun_prop :
      Continuous fun t : ℝ => a + t • (b - a))).continuousOn
  have hIoc : ∀ t ∈ Ι (0 : ℝ) 1, t ∈ uIcc (0 : ℝ) 1 := fun t ht => by
    rw [uIoc_of_le zero_le_one] at ht
    rw [uIcc_of_le zero_le_one]
    exact ⟨ht.1.le, ht.2⟩
  refine ⟨fun ζ => ?_, ?_, ?_⟩
  · set T : (Euc d →L[ℝ] Euc d) →L[ℝ] ℝ :=
      (innerSL ℝ ζ).comp (ContinuousLinearMap.apply ℝ (Euc d) ζ) with hT
    have h1 := T.intervalIntegral_comp_comm ((hcont ξ η).intervalIntegrable (μ := volume))
    have h2 : ∀ t : ℝ, T (fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ))) =
        ⟪fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ)) ζ, ζ⟫ := fun t => by
      rw [hT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        innerSL_apply_apply, real_inner_comm]
    have h3 : T (∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ))) =
        ⟪(∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ))) ζ, ζ⟫ := by
      rw [hT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        innerSL_apply_apply, real_inner_comm]
    rw [← h3, ← h1]
    simp only [h2]
    calc c * ‖ζ‖ ^ 2 = ∫ _t in (0 : ℝ)..1, c * ‖ζ‖ ^ 2 := by simp
      _ ≤ ∫ t in (0 : ℝ)..1, ⟪fderiv ℝ (gradient Ψ) (ξ + t • (η - ξ)) ζ, ζ⟫ := by
          refine intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const ?_
            fun t _ => h.lower _ ζ
          exact (((hcont ξ η).clm_apply continuousOn_const).inner
            continuousOn_const).intervalIntegrable
  · refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t _ =>
      h.norm_fderiv_gradient_le _).trans ?_
    simp
  · rw [← intervalIntegral.integral_sub (hcont ξ η).intervalIntegrable
      (hcont ξ' η').intervalIntegrable]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := L * (‖ξ - ξ'‖ + ‖η - η'‖)) fun t ht => ?_).trans (by simp)
    have ht' := hIoc t ht
    rw [uIcc_of_le zero_le_one] at ht'
    refine (hL _ (hseg hξ hη t (hIoc t ht)) _ (hseg hξ' hη' t (hIoc t ht))).trans ?_
    have e : ξ + t • (η - ξ) - (ξ' + t • (η' - ξ')) = (1 - t) • (ξ - ξ') + t • (η - η') := by
      module
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    calc ‖(1 - t) • (ξ - ξ') + t • (η - η')‖ ≤ ‖(1 - t) • (ξ - ξ')‖ + ‖t • (η - η')‖ :=
          norm_add_le _ _
      _ = (1 - t) * ‖ξ - ξ'‖ + t * ‖η - η'‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht'.2]),
            Real.norm_of_nonneg ht'.1]
      _ ≤ ‖ξ - ξ'‖ + ‖η - η'‖ := by
          nlinarith [norm_nonneg (ξ - ξ'), norm_nonneg (η - η'), ht'.1, ht'.2]

/-- **Lipschitz constants for `D²Ψ` and for the natural-growth term `B`** on a ball.  Both are
`C¹` functions, hence Lipschitz on the compact convex set `B̄(0, M)`. -/
theorem exists_profile_lipschitz (hΨ : IsRegProfile Ψ) (M : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ ξ ∈ Metric.closedBall (0 : Euc d) M, ∀ η ∈ Metric.closedBall (0 : Euc d) M,
        ‖fderiv ℝ (gradient Ψ) ξ - fderiv ℝ (gradient Ψ) η‖ ≤ L * ‖ξ - η‖) ∧
      (∀ ξ ∈ Metric.closedBall (0 : Euc d) M, ∀ η ∈ Metric.closedBall (0 : Euc d) M,
        |regNatGrowth Ψ ξ - regNatGrowth Ψ η| ≤ L * ‖ξ - η‖) := by
  obtain ⟨L₁, hL₁⟩ := hΨ.contDiff_fderiv_gradient.contDiffOn.exists_lipschitzOnWith
    (s := Metric.closedBall (0 : Euc d) M) one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  obtain ⟨L₂, hL₂⟩ := (contDiff_regNatGrowth hΨ).contDiffOn.exists_lipschitzOnWith
    (s := Metric.closedBall (0 : Euc d) M) one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  refine ⟨max (L₁ : ℝ) (L₂ : ℝ), le_trans L₁.2 (le_max_left _ _), ?_, ?_⟩
  · intro ξ hξ η hη
    have h := hL₁.dist_le_mul ξ hξ η hη
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro ξ hξ η hη
    have h := hL₂.dist_le_mul ξ hξ η hη
    rw [Real.dist_eq, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-! ### The coefficient field of the difference-quotient equation -/

/-- The **averaged Hessian along a difference quotient**:
`A_h(x) = ∫₀¹ D²Ψ(∇v(x) + t (∇v(x + h) - ∇v(x))) dt`, the coefficient field of the linear
equation satisfied by `(v(· + h) - v)/s`. -/
noncomputable def diffQuotCoeff (Ψ : Euc d → ℝ) (v : Euc d → ℝ) (hv : Euc d) (x : Euc d) :
    Euc d →L[ℝ] Euc d :=
  ∫ t in (0 : ℝ)..1,
    fderiv ℝ (gradient Ψ) (gradient v x + t • (gradient v (x + hv) - gradient v x))

/-- `A_h(x)` applied to the difference of the gradients is the difference of the fluxes. -/
theorem diffQuotCoeff_apply (hΨ : IsRegProfile Ψ) (v : Euc d → ℝ) (hv x : Euc d) :
    diffQuotCoeff Ψ v hv x (gradient v (x + hv) - gradient v x) =
      gradient Ψ (gradient v (x + hv)) - gradient Ψ (gradient v x) :=
  (gradient_sub_eq_integral_fderiv hΨ (gradient v x) (gradient v (x + hv))).symm

/-! ### The weak equation of a difference quotient -/

/-- The right-hand side of the difference-quotient equation,
`g_s = -(f(· + h) - f)/s` with `f = κ v + 2 m + B(∇v)`. -/
noncomputable def diffQuotRhs (κ m : ℝ) (Ψ : Euc d → ℝ) (v : Euc d → ℝ) (hvec : Euc d) (s : ℝ)
    (x : Euc d) : ℝ :=
  -((regLogRhs κ m Ψ v (gradient v) (x + hvec) - regLogRhs κ m Ψ v (gradient v) x) / s)

/-- **The weak equation for a translate.**  If `v` solves the logarithmic equation weakly on `U`,
then `v(· + h)` solves the translated equation against test functions whose support is shifted
into `U`.  (Change of variables, exactly as in
`Komlos.Literature.integral_inner_flux_translate`.) -/
theorem IsWeakLogSol.integral_inner_translate {κ m : ℝ} {U : Set (Euc d)} {v : Euc d → ℝ}
    {Gv : Euc d → Euc d} (hsol : IsWeakLogSol κ m Ψ U v Gv) (hvec : Euc d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψU : ∀ x ∈ tsupport ψ, x + hvec ∈ U) :
    (∫ x, ⟪gradient Ψ (Gv (x + hvec)), gradient ψ x⟫) =
      -∫ x, regLogRhs κ m Ψ v Gv (x + hvec) * ψ x := by
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : Euc d → ℝ, ψ' = fun y => ψ (y + -hvec) := ⟨_, rfl⟩
  have hψ'c : ContDiff ℝ ∞ ψ' := by
    rw [hψ']
    exact hψ.comp (contDiff_id.add contDiff_const)
  have hψ's : HasCompactSupport ψ' := by
    have h := hψs.comp_homeomorph (Homeomorph.addRight (-hvec))
    have he : ψ ∘ Homeomorph.addRight (-hvec) = ψ' := by
      rw [hψ']
      rfl
    rwa [he] at h
  have hψ'U : tsupport ψ' ⊆ U := by
    intro y hy
    have h1 : tsupport ψ' = (Homeomorph.addRight (-hvec)) ⁻¹' tsupport ψ := by
      rw [← tsupport_comp_eq_preimage ψ (Homeomorph.addRight (-hvec)), hψ']
      rfl
    rw [h1] at hy
    have h2 := hψU _ hy
    simpa using h2
  have hgrad : ∀ y, gradient ψ' y = gradient ψ (y + -hvec) := fun y => by
    rw [hψ']
    unfold gradient
    rw [fderiv_comp_add_right]
  have e1 : (∫ x, ⟪gradient Ψ (Gv (x + hvec)), gradient ψ x⟫) =
      ∫ y, ⟪gradient Ψ (Gv y), gradient ψ' y⟫ := by
    rw [← integral_add_right_eq_self (fun y => ⟪gradient Ψ (Gv y), gradient ψ' y⟫) hvec]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ⟪gradient Ψ (Gv (x + hvec)), gradient ψ x⟫ =
      ⟪gradient Ψ (Gv (x + hvec)), gradient ψ' (x + hvec)⟫
    rw [hgrad, add_neg_cancel_right]
  have e2 : (∫ x, regLogRhs κ m Ψ v Gv (x + hvec) * ψ x) =
      ∫ y, regLogRhs κ m Ψ v Gv y * ψ' y := by
    rw [← integral_add_right_eq_self (fun y => regLogRhs κ m Ψ v Gv y * ψ' y) hvec]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show regLogRhs κ m Ψ v Gv (x + hvec) * ψ x =
      regLogRhs κ m Ψ v Gv (x + hvec) * ψ' (x + hvec)
    rw [hψ']
    simp only [add_neg_cancel_right]
  rw [e1, e2]
  exact hsol.weakEq ψ' hψ'c hψ's hψ'U

/-- **The difference-quotient equation.**  On a set `Bset` where both `x` and `x + h` lie in `U`,
the difference quotient `w_s = (v(· + h) - v)/s` is a weak solution of the *linear* equation

`div (A_h ∇w_s) = g_s`,   `A_h = ∫₀¹ D²Ψ(∇v + t (∇v(· + h) - ∇v)) dt`,
`g_s = -(f(· + h) - f)/s`,

with `f = κ v + 2 m + B(∇v)` the right-hand side of the logarithmic equation.  The coefficient
field is the mean value `diffQuotCoeff`, so it inherits the ellipticity constants of `D²Ψ`. -/
theorem IsWeakLogSol.integral_inner_diffQuot (hΨ : IsRegProfile Ψ) {κ m : ℝ} {U : Set (Euc d)}
    {v : Euc d → ℝ} (hsol : IsWeakLogSol κ m Ψ U v (gradient v)) (hv1 : ContDiffOn ℝ 1 v U)
    (hvec : Euc d) (s : ℝ) {Bset : Set (Euc d)} (hB : ∀ x ∈ Bset, x ∈ U ∧ x + hvec ∈ U)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψB : tsupport ψ ⊆ Bset) :
    (∫ x, ⟪diffQuotCoeff Ψ v hvec x (gradient (fun y => (v (y + hvec) - v y) / s) x),
        gradient ψ x⟫) = ∫ x, diffQuotRhs κ m Ψ v hvec s x * ψ x := by
  have hU : IsOpen U := hsol.isOpen
  set U' : Set (Euc d) := U ∩ (fun x => x + hvec) ⁻¹' U with hU'def
  have hU'o : IsOpen U' := hU.inter (hU.preimage (continuous_id.add continuous_const))
  have hsU' : tsupport ψ ⊆ U' := fun x hx => ⟨(hB x (hψB hx)).1, (hB x (hψB hx)).2⟩
  have hshift : Continuous fun x : Euc d => x + hvec := by fun_prop
  have hmapsU' : MapsTo (fun x : Euc d => x + hvec) U' U := fun x hx => hx.2
  have hgv : ContinuousOn (gradient v) U :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hv1.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hgv' : ContinuousOn (fun x => gradient v (x + hvec)) U' :=
    hgv.comp hshift.continuousOn hmapsU'
  have hrhs : ContinuousOn (regLogRhs κ m Ψ v (gradient v)) U := by
    have h : ContinuousOn (fun y => κ * v y + 2 * m + regNatGrowth Ψ (gradient v y)) U :=
      ((continuousOn_const.mul hv1.continuousOn).add continuousOn_const).add
        ((continuous_regNatGrowth hΨ).comp_continuousOn hgv)
    exact h
  have hrhs' : ContinuousOn (fun x => regLogRhs κ m Ψ v (gradient v) (x + hvec)) U' :=
    hrhs.comp hshift.continuousOn hmapsU'
  have hψg : Continuous (gradient ψ) := continuous_gradient (hψ.of_le (by simp))
  have hsg : tsupport (gradient ψ) ⊆ tsupport ψ := by
    refine closure_minimal (fun x hx => ?_) (isClosed_tsupport _)
    by_contra h
    exact hx (by rw [gradient_eq_zero_of_notMem_tsupport h])
  have hint : ∀ f : Euc d → Euc d, ContinuousOn f U' →
      Integrable fun x => ⟪gradient Ψ (f x), gradient ψ x⟫ := by
    intro f hf
    have hsupp : Function.support (fun x => ⟪gradient Ψ (f x), gradient ψ x⟫) ⊆
        Function.support (gradient ψ) := by
      intro x hx
      by_contra h
      have h0 : gradient ψ x = 0 := Function.notMem_support.1 h
      exact hx (by simp only [h0, inner_zero_right])
    refine Continuous.integrable_of_hasCompactSupport ?_
      ((hasCompactSupport_gradient hψs).mono' (hsupp.trans subset_closure))
    exact continuous_of_continuousOn_of_tsupport_subset hU'o
      ((hΨ.contDiff_gradient.continuous.comp_continuousOn hf).inner hψg.continuousOn)
      ((closure_mono hsupp).trans (hsg.trans hsU'))
  have hint2 : ∀ g : Euc d → ℝ, ContinuousOn g U' → Integrable fun x => g x * ψ x :=
    fun g hg => integrable_mul_of_continuousOn hU'o hg hψ.continuous hψs hsU'
  -- the pointwise identity for the left-hand side
  have hpt : ∀ x : Euc d,
      ⟪diffQuotCoeff Ψ v hvec x (gradient (fun y => (v (y + hvec) - v y) / s) x),
          gradient ψ x⟫ =
        s⁻¹ * (⟪gradient Ψ (gradient v (x + hvec)), gradient ψ x⟫ -
          ⟪gradient Ψ (gradient v x), gradient ψ x⟫) := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · obtain ⟨hxU, hxvU⟩ := hB x (hψB hx)
      rw [(gradient_difference_quotient hU hv1 s hxU hxvU).2, map_smul, real_inner_smul_left,
        diffQuotCoeff_apply hΨ v hvec x, inner_sub_left]
    · rw [gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right, inner_zero_right,
        inner_zero_right]
      ring
  have hi1 : Integrable fun x => ⟪gradient Ψ (gradient v (x + hvec)), gradient ψ x⟫ :=
    hint _ hgv'
  have hi0 : Integrable fun x => ⟪gradient Ψ (gradient v x), gradient ψ x⟫ :=
    hint _ (hgv.mono inter_subset_left)
  have hj1 : Integrable fun x => regLogRhs κ m Ψ v (gradient v) (x + hvec) * ψ x :=
    hint2 _ hrhs'
  have hj0 : Integrable fun x => regLogRhs κ m Ψ v (gradient v) x * ψ x :=
    hint2 _ (hrhs.mono inter_subset_left)
  have hlhs : (∫ x, ⟪diffQuotCoeff Ψ v hvec x
        (gradient (fun y => (v (y + hvec) - v y) / s) x), gradient ψ x⟫) =
      s⁻¹ * ((∫ x, ⟪gradient Ψ (gradient v (x + hvec)), gradient ψ x⟫) -
        ∫ x, ⟪gradient Ψ (gradient v x), gradient ψ x⟫) := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
      integral_sub hi1 hi0]
  have hrhseq : (∫ x, diffQuotRhs κ m Ψ v hvec s x * ψ x) =
      -(s⁻¹ * ((∫ x, regLogRhs κ m Ψ v (gradient v) (x + hvec) * ψ x) -
        ∫ x, regLogRhs κ m Ψ v (gradient v) x * ψ x)) := by
    have hpt2 : ∀ x : Euc d, diffQuotRhs κ m Ψ v hvec s x * ψ x =
        -(s⁻¹ * (regLogRhs κ m Ψ v (gradient v) (x + hvec) * ψ x -
          regLogRhs κ m Ψ v (gradient v) x * ψ x)) := by
      intro x
      simp only [diffQuotRhs]
      field_simp
      try ring
    rw [integral_congr_ae (Eventually.of_forall hpt2), integral_neg, integral_const_mul,
      integral_sub hj1 hj0]
  rw [hlhs, hrhseq]
  have htrans := hsol.integral_inner_translate (Ψ := Ψ) hvec hψ hψs
    fun x hx => (hB x (hψB hx)).2
  have hbase := hsol.weakEq ψ hψ hψs (hsU'.trans inter_subset_left)
  rw [htrans, hbase]
  ring


end Komlos.Literature.Regularized
