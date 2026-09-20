import Komlos.Literature.Regularized.InteriorC2Aux
import Komlos.Literature.Regularized.InteriorCampanato

/-!
# `C²` regularity of the logarithmic solution (lane `L3c`, link 8)

This file proves `IsWeakLogSol.contDiffOn_two`, the frozen statement
`Komlos.Literature.Regularized.IsWeakLogSol.contDiffOn_two` of
`Komlos/Literature/Regularized/InteriorRegularity.lean` (link 6 there, link 8 of lane `L3c`),
verbatim.

## The argument

Let `v` be a weak solution of `div ∇Ψ(∇v) = κ v + 2 m + B(∇v)` on the open set `U`.  Link 4
(`IsWeakLogSol.exists_holder_gradient`) gives `v ∈ C^{1,β}_loc(U)` with `∇v = G` a.e.  Fix
`x₀ ∈ U` and a ball `B̄(x₀, 6R) ⊆ U` with `2R ≤ 1`.  For a shift `h` with `‖h‖ = s ≤ R` the
difference quotient `w_s = (v(· + h) - v)/s` solves, weakly on `B(x₀, 2R)`
(`IsWeakLogSol.integral_inner_diffQuot`),

`div (A_h ∇w_s) = g_s`,  `A_h = ∫₀¹ D²Ψ(∇v + t(∇v(· + h) - ∇v)) dt`,
`g_s = -(f(· + h) - f)/s`,  `f = κ v + 2 m + B(∇v)`.

The data are uniform in `h`:

* `A_h` is `c`-elliptic and `C`-bounded (the ellipticity constants of `D²Ψ`) and `α`-Hölder with
  constant `2 L [∇v]_α`, `L` a Lipschitz constant of `D²Ψ` on a ball containing the values of
  `∇v` (`integral_fderiv_gradient_bounds`);
* `|w_s| ≤ K`, `K` a Lipschitz constant of `v`;
* `|g_s| ≤ |κ| K + L ‖∇w_s‖` — **not** a uniform bound, because `B(∇v)` is only Hölder, but a
  bound with a first-order term, which is what `exists_schauder_drift_holder` handles.

`exists_schauder_drift_holder` therefore bounds `[∇w_s]_{α; B(x₀, R/4)}` by a constant
independent of `h`, i.e.

`‖(∇v(y + h) - ∇v y) - (∇v(z + h) - ∇v z)‖ ≤ C s |y - z|^α`,

and `Komlos.Literature.contDiffOn_of_holder_difference` upgrades that to `∇v ∈ C¹`, i.e.
`v ∈ C²`.

**Link 7 of the lane (`exists_schauder_divergence_estimate`, the interior Schauder estimate for
a divergence-form right-hand side `div F`) is not used.**  Writing `Δ_h f` as `div (e ∫₀¹ f(· + t h e) dt)`
is one way to keep the right-hand side of the difference-quotient equation bounded in a
`C^{0,α}` sense; the route taken here instead keeps it in the *first-order* form
`|g| ≤ a + b ‖∇w‖`, which the scaled Schauder estimate absorbs.  See the report of the lane.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace Interval

namespace Komlos.Literature.Regularized

open Komlos.Literature

variable {d : ℕ} {κ m c C : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ}
  {G : Euc d → Euc d}

/-! ### Transporting the weak equation to the classical gradient -/

/-- A weak solution stays one when its gradient field is replaced by an almost everywhere equal
measurable one.  This is how the a.e. identification `G = ∇v` of link 4 is used. -/
theorem IsWeakLogSol.congr_grad_ae {G' : Euc d → Euc d} (h : IsWeakLogSol κ m Ψ U v G)
    (hG' : Measurable G') (heq : ∀ᵐ x ∂(volume.restrict U), G' x = G x) :
    IsWeakLogSol κ m Ψ U v G' := by
  have hU : IsOpen U := h.isOpen
  have hGU : ∀ᵐ x, x ∈ U → G' x = G x := (ae_restrict_iff' hU.measurableSet).1 heq
  refine
    { isOpen := hU
      continuousOn := h.continuousOn
      measurable := h.measurable
      measurable_grad := hG'
      hasWeakGradientOn := ⟨fun ψ hψ hψs hψU e => ?_⟩
      integrableOn_sq := fun x₀ r hr => ?_
      weakEq := fun ψ hψ hψs hψU => ?_ }
  · rw [h.hasWeakGradientOn.integral_eq ψ hψ hψs hψU e]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hGU] with x hx
    show ⟪G x, e⟫ * ψ x = ⟪G' x, e⟫ * ψ x
    by_cases hxs : x ∈ tsupport ψ
    · rw [hx (hψU hxs)]
    · rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero, mul_zero]
  · refine (h.integrableOn_sq x₀ r hr).congr ?_
    have hsub : ∀ᵐ x ∂(volume.restrict (Metric.closedBall x₀ r)), G' x = G x :=
      ae_restrict_of_ae_restrict_of_subset hr heq
    filter_upwards [hsub] with x hx
    show ‖G x‖ ^ 2 = ‖G' x‖ ^ 2
    rw [hx]
  · have e1 : (∫ x, ⟪gradient Ψ (G' x), gradient ψ x⟫) =
        ∫ x, ⟪gradient Ψ (G x), gradient ψ x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [hGU] with x hx
      show ⟪gradient Ψ (G' x), gradient ψ x⟫ = ⟪gradient Ψ (G x), gradient ψ x⟫
      by_cases hxs : x ∈ tsupport ψ
      · rw [hx (hψU hxs)]
      · rw [gradient_eq_zero_of_notMem_tsupport hxs, inner_zero_right, inner_zero_right]
    have e2 : (∫ x, regLogRhs κ m Ψ v G' x * ψ x) =
        ∫ x, regLogRhs κ m Ψ v G x * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hGU] with x hx
      show regLogRhs κ m Ψ v G' x * ψ x = regLogRhs κ m Ψ v G x * ψ x
      by_cases hxs : x ∈ tsupport ψ
      · simp only [regLogRhs, hx (hψU hxs)]
      · rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero, mul_zero]
    rw [e1, e2]
    exact h.weakEq ψ hψ hψs hψU

/-! ### Uniform Hölder bounds for the difference quotients of `∇v` -/

/-- **The difference quotients of `∇v` are uniformly Hölder.**  Near any point of `U` there is a
ball on which

`‖(∇v(y + h) - ∇v y) - (∇v(z + h) - ∇v z)‖ ≤ C ‖h‖ ‖y - z‖^α`

for every small shift `h`, with `C` independent of `h`.  This is the analogue, for the
logarithmic equation with natural growth, of
`Komlos.Literature.exists_holder_difference_gradient`; the natural-growth term is handled by the
first-order right-hand side of `exists_schauder_drift_holder`. -/
theorem exists_logsol_difference_bound (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ m Ψ U v (gradient v)) (hv1 : ContDiffOn ℝ 1 v U)
    (hvα : ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
      ∃ Ch r : NNReal, 0 < r ∧ HolderOnWith Ch r (gradient v) S)
    {x₀ : Euc d} (hx₀ : x₀ ∈ U) :
    ∃ ρ Cb α : ℝ, 0 < ρ ∧ 0 < α ∧ Metric.closedBall x₀ ρ ⊆ U ∧
      ∀ i : Fin d, ∀ s : ℝ, 0 < s → s ≤ ρ → ∀ y ∈ Metric.ball x₀ ρ, ∀ z ∈ Metric.ball x₀ ρ,
        ‖(gradient v (y + s • EuclideanSpace.single i 1) - gradient v y) -
          (gradient v (z + s • EuclideanSpace.single i 1) - gradient v z)‖ ≤
            Cb * s * dist y z ^ α := by
  have hU : IsOpen U := hsol.isOpen
  obtain ⟨cc, CC, hc⟩ := hΨ.exists_isRegProfileWith
  -- the working radius
  obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = min r₁ 1 / 16 := ⟨_, rfl⟩
  have hmin0 : 0 < min r₁ 1 := lt_min hr₁ one_pos
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have h6r : 6 * R < r₁ := by
    rw [hRdef]
    have := min_le_left r₁ (1 : ℝ)
    linarith
  have h2R1 : 2 * R ≤ 1 := by
    rw [hRdef]
    have := min_le_right r₁ (1 : ℝ)
    linarith
  have hS : Metric.closedBall x₀ (6 * R) ⊆ U :=
    (Metric.closedBall_subset_ball h6r).trans hr₁U
  -- continuity and bounds for `∇v` on the big ball
  have hgc : ContinuousOn (gradient v) U :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hv1.continuousOn_fderiv_of_isOpen hU le_rfl)
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall x₀ (6 * R)).exists_bound_of_continuousOn
    (hgc.mono hS)
  obtain ⟨L, hL0, hLA, hLB⟩ := exists_profile_lipschitz hΨ M₁
  -- the Hölder exponent and constant of `∇v`
  obtain ⟨Cφ, rφ, hrφ, hHφ⟩ := hvα _ (isCompact_closedBall x₀ (6 * R)) hS
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = min (rφ : ℝ) (1 / 2) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; exact lt_min hrφ (by norm_num)
  have hα1 : α < 1 := by rw [hαdef]; exact (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨Cα, hCα⟩ := HolderOnWith.exists_holderOnWith_of_le ⟨Cφ, hHφ⟩
    (show α.toNNReal ≤ rφ from Real.toNNReal_le_iff_le_coe.2 (by rw [hαdef]; exact min_le_left _ _))
    Metric.isBounded_closedBall
  have hHol : ∀ x ∈ Metric.closedBall x₀ (6 * R), ∀ y ∈ Metric.closedBall x₀ (6 * R),
      ‖gradient v x - gradient v y‖ ≤ (Cα : ℝ) * dist x y ^ α := fun x hx y hy => by
    have h := hCα.dist_le hx hy
    rwa [Real.coe_toNNReal _ hα0.le, dist_eq_norm] at h
  -- the Lipschitz constant of `v`
  obtain ⟨K₁, hK₁⟩ := (hv1.mono hS).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  have hK₁' : ∀ x ∈ Metric.closedBall x₀ (6 * R), ∀ y ∈ Metric.closedBall x₀ (6 * R),
      |v x - v y| ≤ (K₁ : ℝ) * dist x y := fun x hx y hy => by
    have h := hK₁.dist_le_mul x hx y hy
    rwa [Real.dist_eq] at h
  -- the right-hand side of the logarithmic equation is continuous on `U`
  have hrhsc : ContinuousOn (regLogRhs κ m Ψ v (gradient v)) U := by
    have h : ContinuousOn (fun y => κ * v y + 2 * m + regNatGrowth Ψ (gradient v y)) U :=
      ((continuousOn_const.mul hv1.continuousOn).add continuousOn_const).add
        ((continuous_regNatGrowth hΨ).comp_continuousOn hgc)
    exact h
  -- the uniform Schauder constant
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = max CC (2 * L * (Cα : ℝ)) := ⟨_, rfl⟩
  have hΛC : CC ≤ Λ := by rw [hΛdef]; exact le_max_left _ _
  have hΛ2 : 2 * L * (Cα : ℝ) ≤ Λ := by rw [hΛdef]; exact le_max_right _ _
  have hΛ0 : 0 ≤ Λ := le_trans hc.C_nonneg hΛC
  obtain ⟨M, hM0, hM⟩ := exists_schauder_drift_holder d (α := α) (μ := cc) (Λ := Λ)
    (a := |κ| * (K₁ : ℝ)) (b := L) (W := (K₁ : ℝ)) (R := 2 * R) hα0 hα1 hc.c_pos hΛ0
    (by positivity) hL0 K₁.2 (by linarith) h2R1
  -- the uniform estimate for a fixed shift
  have key : ∀ (hvec : Euc d) (s : ℝ), 0 < s → s ≤ R → ‖hvec‖ = s →
      ∀ y ∈ Metric.ball x₀ (2 * R / 8), ∀ z ∈ Metric.ball x₀ (2 * R / 8),
        ‖(gradient v (y + hvec) - gradient v y) -
          (gradient v (z + hvec) - gradient v z)‖ ≤ M * s * dist y z ^ α := by
    intro hvec s hs hsR hvn
    have hmem : ∀ x ∈ Metric.ball x₀ (2 * R),
        x ∈ Metric.closedBall x₀ (6 * R) ∧ x + hvec ∈ Metric.closedBall x₀ (6 * R) := by
      intro x hx
      rw [Metric.mem_ball] at hx
      refine ⟨Metric.mem_closedBall.2 (by linarith), Metric.mem_closedBall.2 ?_⟩
      calc dist (x + hvec) x₀ ≤ dist (x + hvec) x + dist x x₀ := dist_triangle _ _ _
        _ ≤ 6 * R := by
            rw [dist_eq_norm, add_sub_cancel_left, hvn]
            linarith
    have hdistshift : ∀ x y : Euc d, dist (x + hvec) (y + hvec) = dist x y := fun x y => by
      rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub]
    have hmb : ∀ x ∈ Metric.ball x₀ (2 * R),
        gradient v x ∈ Metric.closedBall (0 : Euc d) M₁ := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hM₁ x (hmem x hx).1
    have hmb' : ∀ x ∈ Metric.ball x₀ (2 * R),
        gradient v (x + hvec) ∈ Metric.closedBall (0 : Euc d) M₁ := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hM₁ _ (hmem x hx).2
    have hAb : ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        (∀ ζ, cc * ‖ζ‖ ^ 2 ≤ ⟪diffQuotCoeff Ψ v hvec x ζ, ζ⟫) ∧
          ‖diffQuotCoeff Ψ v hvec x‖ ≤ CC ∧
          ‖diffQuotCoeff Ψ v hvec x - diffQuotCoeff Ψ v hvec y‖ ≤
            L * (‖gradient v x - gradient v y‖ +
              ‖gradient v (x + hvec) - gradient v (y + hvec)‖) := by
      intro x hx y hy
      simp only [diffQuotCoeff]
      exact integral_fderiv_gradient_bounds hc (convex_closedBall (0 : Euc d) M₁) hLA hL0
        (hmb x hx) (hmb' x hx) (hmb y hy) (hmb' y hy)
    -- the objects of the linear equation
    obtain ⟨w, hwdef⟩ : ∃ w : Euc d → ℝ, w = fun x => (v (x + hvec) - v x) / s := ⟨_, rfl⟩
    have hgradw : ∀ x ∈ Metric.ball x₀ (2 * R),
        gradient w x = s⁻¹ • (gradient v (x + hvec) - gradient v x) := by
      intro x hx
      rw [hwdef]
      exact (gradient_difference_quotient hU hv1 s (hS (hmem x hx).1) (hS (hmem x hx).2)).2
    have hell : ∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ,
        cc * ‖ζ‖ ^ 2 ≤ ⟪diffQuotCoeff Ψ v hvec x ζ, ζ⟫ := fun x hx ζ => (hAb x hx x hx).1 ζ
    have hAbd : ∀ x ∈ Metric.ball x₀ (2 * R), ‖diffQuotCoeff Ψ v hvec x‖ ≤ Λ :=
      fun x hx => (hAb x hx x hx).2.1.trans hΛC
    have hAhol : ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖diffQuotCoeff Ψ v hvec x - diffQuotCoeff Ψ v hvec y‖ ≤ Λ * dist x y ^ α := by
      intro x hx y hy
      have h1 := hHol _ (hmem x hx).1 _ (hmem y hy).1
      have h2 := hHol _ (hmem x hx).2 _ (hmem y hy).2
      rw [hdistshift] at h2
      refine (hAb x hx y hy).2.2.trans ?_
      calc L * (‖gradient v x - gradient v y‖ + ‖gradient v (x + hvec) - gradient v (y + hvec)‖)
          ≤ L * ((Cα : ℝ) * dist x y ^ α + (Cα : ℝ) * dist x y ^ α) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 h2) hL0
        _ = 2 * L * (Cα : ℝ) * dist x y ^ α := by ring
        _ ≤ Λ * dist x y ^ α :=
            mul_le_mul_of_nonneg_right hΛ2 (Real.rpow_nonneg dist_nonneg _)
    have hshiftc : Continuous fun x : Euc d => x + hvec := by fun_prop
    have hgcont : ContinuousOn (diffQuotRhs κ m Ψ v hvec s) (Metric.ball x₀ (2 * R)) := by
      have h1 : ContinuousOn (fun x => regLogRhs κ m Ψ v (gradient v) (x + hvec))
          (Metric.ball x₀ (2 * R)) :=
        hrhsc.comp hshiftc.continuousOn fun x hx => hS (hmem x hx).2
      have h2 : ContinuousOn (regLogRhs κ m Ψ v (gradient v)) (Metric.ball x₀ (2 * R)) :=
        hrhsc.mono fun x hx => hS (hmem x hx).1
      have h3 : ContinuousOn (fun x => -((regLogRhs κ m Ψ v (gradient v) (x + hvec) -
          regLogRhs κ m Ψ v (gradient v) x) / s)) (Metric.ball x₀ (2 * R)) :=
        ((h1.sub h2).div_const s).neg
      exact h3
    have hw1 : ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) := by
      rw [hwdef]
      have hcd : ContDiff ℝ 1 fun x : Euc d => x + hvec := by fun_prop
      exact ((hv1.comp hcd.contDiffOn fun x hx => hS (hmem x hx).2).sub
        (hv1.mono fun x hx => hS (hmem x hx).1)).div_const s
    have hwhol : ∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α := by
      refine ⟨s⁻¹ * (2 * (Cα : ℝ)), fun x hx y hy => ?_⟩
      rw [hgradw x hx, hgradw y hy, ← smul_sub, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      have h1 := hHol _ (hmem x hx).1 _ (hmem y hy).1
      have h2 := hHol _ (hmem x hx).2 _ (hmem y hy).2
      rw [hdistshift] at h2
      have e : (gradient v (x + hvec) - gradient v x) - (gradient v (y + hvec) - gradient v y) =
          (gradient v (x + hvec) - gradient v (y + hvec)) - (gradient v x - gradient v y) := by
        abel
      calc s⁻¹ * ‖(gradient v (x + hvec) - gradient v x) -
            (gradient v (y + hvec) - gradient v y)‖
          ≤ s⁻¹ * (‖gradient v (x + hvec) - gradient v (y + hvec)‖ +
              ‖gradient v x - gradient v y‖) := by
            rw [e]
            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.2 hs.le)
        _ ≤ s⁻¹ * ((Cα : ℝ) * dist x y ^ α + (Cα : ℝ) * dist x y ^ α) :=
            mul_le_mul_of_nonneg_left (add_le_add h2 h1) (inv_nonneg.2 hs.le)
        _ = s⁻¹ * (2 * (Cα : ℝ)) * dist x y ^ α := by ring
    have hweakeq : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪diffQuotCoeff Ψ v hvec x (gradient w x), gradient ψ x⟫ =
          ∫ x, diffQuotRhs κ m Ψ v hvec s x * ψ x := by
      intro ψ hψ hψs hψB
      rw [hwdef]
      exact hsol.integral_inner_diffQuot hΨ hv1 hvec s
        (fun x hx => ⟨hS (hmem x hx).1, hS (hmem x hx).2⟩) hψ hψs hψB
    have hwbd : ∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ (K₁ : ℝ) := by
      intro x hx
      rw [hwdef]
      exact abs_difference_quotient_le hK₁' (hmem x hx).1 (hmem x hx).2 hs hvn
    have hgbd : ∀ x ∈ Metric.ball x₀ (2 * R),
        |diffQuotRhs κ m Ψ v hvec s x| ≤ |κ| * (K₁ : ℝ) + L * ‖gradient w x‖ := by
      intro x hx
      have hΔ : ‖gradient v (x + hvec) - gradient v x‖ = s * ‖gradient w x‖ := by
        rw [hgradw x hx, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← mul_assoc,
          mul_inv_cancel₀ hs.ne', one_mul]
      have hBd : |regNatGrowth Ψ (gradient v (x + hvec)) - regNatGrowth Ψ (gradient v x)| ≤
          L * (s * ‖gradient w x‖) := by
        have h := hLB _ (hmb' x hx) _ (hmb x hx)
        rwa [hΔ] at h
      have hvd : |v (x + hvec) - v x| ≤ (K₁ : ℝ) * s := by
        have h := hK₁' _ (hmem x hx).2 _ (hmem x hx).1
        rwa [dist_eq_norm, add_sub_cancel_left, hvn] at h
      have e : regLogRhs κ m Ψ v (gradient v) (x + hvec) - regLogRhs κ m Ψ v (gradient v) x
          = κ * (v (x + hvec) - v x) +
            (regNatGrowth Ψ (gradient v (x + hvec)) - regNatGrowth Ψ (gradient v x)) := by
        simp only [regLogRhs]
        ring
      show |-((regLogRhs κ m Ψ v (gradient v) (x + hvec) -
        regLogRhs κ m Ψ v (gradient v) x) / s)| ≤ _
      rw [abs_neg, abs_div, abs_of_pos hs, div_le_iff₀ hs, e]
      calc |κ * (v (x + hvec) - v x) +
            (regNatGrowth Ψ (gradient v (x + hvec)) - regNatGrowth Ψ (gradient v x))|
          ≤ |κ * (v (x + hvec) - v x)| +
            |regNatGrowth Ψ (gradient v (x + hvec)) - regNatGrowth Ψ (gradient v x)| :=
            abs_add_le _ _
        _ ≤ |κ| * ((K₁ : ℝ) * s) + L * (s * ‖gradient w x‖) := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left hvd (abs_nonneg κ)) hBd
        _ = (|κ| * (K₁ : ℝ) + L * ‖gradient w x‖) * s := by ring
    have hconc := hM x₀ (diffQuotCoeff Ψ v hvec) (diffQuotRhs κ m Ψ v hvec s) w hell hAbd
      hAhol hgcont hw1 hwhol hweakeq hwbd hgbd
    intro y hy z hz
    have hsub : Metric.ball x₀ (2 * R / 8) ⊆ Metric.ball x₀ (2 * R) :=
      Metric.ball_subset_ball (by linarith)
    have hb := (hconc y hy).2 z hz
    rw [hgradw y (hsub hy), hgradw z (hsub hz), ← smul_sub, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_le_iff₀ hs] at hb
    calc ‖(gradient v (y + hvec) - gradient v y) - (gradient v (z + hvec) - gradient v z)‖
        ≤ s * (M * dist y z ^ α) := hb
      _ = M * s * dist y z ^ α := by ring
  refine ⟨R / 8, M, α, by linarith, hα0,
    (Metric.closedBall_subset_closedBall (by linarith)).trans hS, ?_⟩
  intro i s hs hsρ y hy z hz
  have hsub : Metric.ball x₀ (R / 8) ⊆ Metric.ball x₀ (2 * R / 8) :=
    Metric.ball_subset_ball (by linarith)
  exact key (s • EuclideanSpace.single i 1) s hs (by linarith)
    (by rw [norm_smul, Real.norm_of_nonneg hs.le]; simp) y (hsub hy) z (hsub hz)


/-! ### `C²` regularity -/

/-- **`C²` regularity, with the `C^{1,β}` input supplied as a hypothesis.**  This is the whole
content of link 8 of the lane: it is `sorry`-free, and it is the form in which the dependence on
link 6 (`IsWeakLogSol.exists_holder_gradient`) is visible.

`exists_logsol_difference_bound` bounds the second differences of `∇v` uniformly in the shift,
and `Komlos.Literature.contDiffOn_of_holder_difference` turns that into `∂_j v ∈ C¹` for every
`j`, i.e. `∇v ∈ C¹` and `v ∈ C²`. -/
theorem IsWeakLogSol.contDiffOn_two_of_holder_gradient (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ m Ψ U v G) (hv1 : ContDiffOn ℝ 1 v U)
    (hae : ∀ᵐ x ∂(volume.restrict U), G x = gradient v x)
    (hvα : ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
      ∃ Ch r : NNReal, 0 < r ∧ HolderOnWith Ch r (gradient v) S) :
    ContDiffOn ℝ 2 v U ∧ ∀ᵐ x ∂(volume.restrict U), G x = gradient v x := by
  classical
  refine ⟨?_, hae⟩
  have hU : IsOpen U := hsol.isOpen
  have hsol' : IsWeakLogSol κ m Ψ U v (gradient v) :=
    hsol.congr_grad_ae (measurable_gradient v)
      (by filter_upwards [hae] with x hx using hx.symm)
  have hgc : ContinuousOn (gradient v) U :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hv1.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hG : ∀ j : Fin d, ContDiffOn ℝ 1 (fun x => gradient v x j) U := by
    intro j
    refine contDiffOn_of_holder_difference
      ((PiLp.continuous_apply 2 _ j).comp_continuousOn hgc) fun x hx => ?_
    obtain ⟨ρ, Cb, α, hρ, hα, hρU, hb⟩ := exists_logsol_difference_bound hΨ hsol' hv1 hvα hx
    refine ⟨ρ, Cb, α, hρ, hα, hρU, fun i s hs hsρ y hy z hz => ?_⟩
    refine le_trans ?_ (hb i s hs hsρ y hy z hz)
    have h := PiLp.norm_apply_le
      ((gradient v (y + s • EuclideanSpace.single i 1) - gradient v y) -
        (gradient v (z + s • EuclideanSpace.single i 1) - gradient v z)) j
    simpa [Real.norm_eq_abs] using h
  have hgrad1 : ContDiffOn ℝ 1 (gradient v) U := contDiffOn_euclidean.2 hG
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ v) U :=
    ((InnerProductSpace.toDual ℝ (Euc d)).contDiff.comp_contDiffOn hgrad1).congr
      fun x _ => toDual_gradient.symm
  exact (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU).2
    ⟨hv1.differentiableOn one_ne_zero, fun h => by simp at h, hfd⟩


/-- **(L3, link 6 of `InteriorRegularity.lean`; link 8 of lane `L3c`)** `v` is `C²` on `U`, with
`∇v = G` a.e.  This is the frozen statement
`Komlos.Literature.Regularized.IsWeakLogSol.contDiffOn_two`, verbatim.

It is `IsWeakLogSol.contDiffOn_two_of_holder_gradient` applied to link 6,
`IsWeakLogSol.exists_holder_gradient` — the *only* placeholder this lane consumes.  In
particular link 7 (`exists_schauder_divergence_estimate`) is **not** used. -/
theorem IsWeakLogSol.contDiffOn_two (hΨ : IsRegProfile Ψ) (hsol : IsWeakLogSol κ m Ψ U v G) :
    ContDiffOn ℝ 2 v U ∧ ∀ᵐ x ∂(volume.restrict U), G x = gradient v x := by
  obtain ⟨hv1, hae, hvα⟩ := hsol.exists_holder_gradient hΨ
  exact hsol.contDiffOn_two_of_holder_gradient hΨ hv1 hae hvα


end Komlos.Literature.Regularized
