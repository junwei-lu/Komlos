import Komlos.Literature.Regularized.PositivityLowerLog

/-!
# Lane `L2p` (`reg/pos-lower`), step 4a: the one-sided first variation

`REGULARIZED_ROUTE.md`, Revision 2 (iii).  The full Euler–Lagrange equation of the regularized
energy is not available before positivity is known (the integrand `w²Ψ(∇w/w)` is not
differentiable in `w` at `w = 0`), but the **increasing** variations `v ↦ v + tψ`, `ψ ≥ 0`, are
legitimate for every `t > 0`, and they give a one-sided inequality.

This file provides

* the **sharp convexity inequality** `Ψ q - ⟪∇Ψ q, q⟫ ≤ Ψ 0 - (c/2)‖q‖²`
  (`IsRegProfileWith.sub_inner_le`) — a two-line strengthening of
  `ProfileBasic.zero_le_inner_gradient_sub` which keeps the quadratic term.  It is *the* source
  of the good term in the logarithmic Caccioppoli estimate: with the weaker form
  `Ψ q - ⟪∇Ψ q, q⟫ ≤ Ψ 0` the estimate degenerates completely;
* the pointwise derivatives of the two densities along a line in the `(value, gradient)` plane
  (`hasDerivAt_homogeneousDensity_line'`, `hasDerivAt_entropyPotential_line'`); these duplicate
  lane `L1`'s `VariationalEulerAux` under primed names, because the `Variational*` and
  `Positivity*` cones of `Komlos/Literature/Regularized/` share several declaration names
  (`homogeneousDensity_two`, `entropyPotential_two`, …) and therefore cannot be imported into
  one module;
* the algebraic regrouping `inner_flux_add_valueDerivative` of the first-variation integrand,
  which is what makes the `1/v`-type test functions usable: the singular parts of the value
  derivative and of the flux term cancel.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)}

/-! ### The sharp convexity inequality -/

/-- **Sharp convexity inequality**: `Ψ q - ⟪∇Ψ q, q⟫ ≤ Ψ 0 - (c/2) ‖q‖²`.

This is `add_inner_add_half_le` at the pair `(q, -q)`, *keeping* the strong-convexity term that
`ProfileBasic.zero_le_inner_gradient_sub` throws away.  Sharpness matters: the quantity
`Ψ q - ⟪∇Ψ q, q⟫` is exactly the coefficient of the test function in the first variation of the
kinetic density along `v ↦ v + t η²/v`, and the `-(c/2)‖q‖²` is the whole good term of the
logarithmic Caccioppoli inequality. -/
theorem IsRegProfileWith.sub_inner_le (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    Ψ q - ⟪gradient Ψ q, q⟫ ≤ Ψ 0 - c / 2 * ‖q‖ ^ 2 := by
  have hmain := h.add_inner_add_half_le q (-q)
  rw [add_neg_cancel, inner_neg_right, norm_neg] at hmain
  linarith

/-! ### The `p = 2` normal forms of the flux and of the value derivative -/

theorem homogeneousFlux_two' (A : Euc d → Euc d) (s : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousFlux 2 A s ξ = s • A (s⁻¹ • ξ) := by
  rw [Korevaar.homogeneousFlux, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

theorem homogeneousValueDerivative_two' (Ψ : Euc d → ℝ) (A : Euc d → Euc d) (s : ℝ)
    (ξ : Euc d) :
    Korevaar.homogeneousValueDerivative 2 Ψ A s ξ
      = s * (2 * Ψ (s⁻¹ • ξ) - ⟪A (s⁻¹ • ξ), s⁻¹ • ξ⟫) := by
  rw [Korevaar.homogeneousValueDerivative, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

/-- The value derivative of the entropy potential at `p = 2`, as an explicit function (with the
correct junk value `0` at `s = 0`, where `deriv` would have to be computed by hand). -/
noncomputable def entropyDeriv (κ s : ℝ) : ℝ := κ * s * Real.log s + κ / 2 * s

theorem entropyDeriv_zero (κ : ℝ) : entropyDeriv κ 0 = 0 := by
  rw [entropyDeriv]; simp

theorem hasDerivAt_entropyPotential_two {κ s : ℝ} (hs : 0 < s) :
    HasDerivAt (Korevaar.entropyPotential 2 κ) (entropyDeriv κ s) s := by
  have h := Korevaar.hasDerivAt_entropyPotential (p := 2) (κ := κ) two_ne_zero hs
  refine h.congr_deriv ?_
  rw [entropyDeriv, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  ring

/-! ### Derivatives along a line -/

/-- **The derivative of the kinetic density along a line** in the `(value, gradient)` plane
(lane `L1`'s `VariationalEulerAux.hasDerivAt_homogeneousDensity_line`, duplicated here under a
primed name; see the module docstring). -/
theorem hasDerivAt_homogeneousDensity_line' (hΨ : IsRegProfile Ψ) (s σ : ℝ) (ξ η : Euc d)
    {τ : ℝ} (hpos : 0 < s + τ * σ) :
    HasDerivAt (fun r : ℝ => Korevaar.homogeneousDensity 2 Ψ (s + r * σ) (ξ + r • η))
      (σ * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (s + τ * σ) (ξ + τ • η)
        + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (s + τ * σ) (ξ + τ • η), η⟫) τ := by
  have hane : s + τ * σ ≠ 0 := hpos.ne'
  have hA : HasDerivAt (fun r : ℝ => s + r * σ) σ τ := by
    simpa using ((hasDerivAt_id τ).mul_const σ).const_add s
  have hAinv : HasDerivAt (fun r : ℝ => (s + r * σ)⁻¹) (-σ / (s + τ * σ) ^ 2) τ := hA.inv hane
  have hV : HasDerivAt (fun r : ℝ => ξ + r • η) η τ := by
    simpa using ((hasDerivAt_id τ).smul_const η).const_add ξ
  have hB : HasDerivAt (fun r : ℝ => (s + r * σ)⁻¹ • (ξ + r • η))
      ((s + τ * σ)⁻¹ • η + (-σ / (s + τ * σ) ^ 2) • (ξ + τ • η)) τ :=
    (hAinv.smul hV).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  have hΨb : HasDerivAt (fun r : ℝ => Ψ ((s + r * σ)⁻¹ • (ξ + r • η)))
      (⟪gradient Ψ ((s + τ * σ)⁻¹ • (ξ + τ • η)),
        (s + τ * σ)⁻¹ • η + (-σ / (s + τ * σ) ^ 2) • (ξ + τ • η)⟫) τ := by
    have hg := (hasGradientAt_iff_hasFDerivAt.1
      (hΨ.differentiable ((s + τ * σ)⁻¹ • (ξ + τ • η))).hasGradientAt).comp_hasDerivAt τ hB
    rw [InnerProductSpace.toDual_apply_apply] at hg
    simpa only [Function.comp_def] using hg
  have hsq : HasDerivAt (fun r : ℝ => (s + r * σ) ^ 2) (2 * (s + τ * σ) * σ) τ := by
    have h := hA.pow 2
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    push_cast
    ring
  have hprod := hsq.mul hΨb
  have hrw : (fun r : ℝ => Korevaar.homogeneousDensity 2 Ψ (s + r * σ) (ξ + r • η))
      = fun r : ℝ => (s + r * σ) ^ 2 * Ψ ((s + r * σ)⁻¹ • (ξ + r • η)) := by
    funext r
    exact homogeneousDensity_two Ψ _ _
  rw [hrw]
  refine hprod.congr_deriv ?_
  rw [homogeneousValueDerivative_two', homogeneousFlux_two']
  simp only [inner_add_right, real_inner_smul_right, real_inner_smul_left]
  field_simp
  ring

/-- **The derivative of the entropy potential along a line.** -/
theorem hasDerivAt_entropyPotential_line' (κ : ℝ) (s σ : ℝ) {τ : ℝ} (hpos : 0 < s + τ * σ) :
    HasDerivAt (fun r : ℝ => Korevaar.entropyPotential 2 κ (s + r * σ))
      (σ * entropyDeriv κ (s + τ * σ)) τ := by
  have hA : HasDerivAt (fun r : ℝ => s + r * σ) σ τ := by
    simpa using ((hasDerivAt_id τ).mul_const σ).const_add s
  have hP := hasDerivAt_entropyPotential_two (κ := κ) hpos
  have h := hP.comp τ hA
  have hcomp : (Korevaar.entropyPotential 2 κ ∘ fun r : ℝ => s + r * σ)
      = fun r : ℝ => Korevaar.entropyPotential 2 κ (s + r * σ) := rfl
  rw [hcomp] at h
  refine h.congr_deriv ?_
  ring

/-! ### Regrouping the first-variation integrand -/

/-- **The algebraic regrouping of the first-variation integrand.**  For a test function whose
value is `P` and whose gradient is `A • ξ + E` at the point in question,

`D_value(s,ξ) P + ⟪Flux(s,ξ), A ξ + E⟫
  = 2 (s P) [Ψ(q) - ⟪∇Ψ(q), q⟫] + (s P + s² A) ⟪∇Ψ(q), q⟫ + s ⟪∇Ψ(q), E⟫`,  `q = ξ/s`.

The point of the regrouping: for the logarithmic test functions `P ≈ η²/s`, `A ≈ -η²/s²` the
first two coefficients are `s P ≈ η²` and `s P + s² A ≈ 0`, so the singular `1/s` disappears and
the sharp convexity inequality applies to the first bracket.  Valid at `s = 0` as well, where
both sides vanish. -/
theorem inner_flux_add_valueDerivative (Ψ : Euc d → ℝ) (s : ℝ) (ξ : Euc d) (P A : ℝ)
    (E : Euc d) :
    Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) s ξ * P
        + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) s ξ, A • ξ + E⟫ =
      2 * (s * P) * (Ψ (s⁻¹ • ξ) - ⟪gradient Ψ (s⁻¹ • ξ), s⁻¹ • ξ⟫)
        + (s * P + s ^ 2 * A) * ⟪gradient Ψ (s⁻¹ • ξ), s⁻¹ • ξ⟫
        + s * ⟪gradient Ψ (s⁻¹ • ξ), E⟫ := by
  rw [homogeneousValueDerivative_two', homogeneousFlux_two']
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · have h1 : ⟪s • gradient Ψ (s⁻¹ • ξ), A • ξ + E⟫
        = s * A * ⟪gradient Ψ (s⁻¹ • ξ), ξ⟫ + s * ⟪gradient Ψ (s⁻¹ • ξ), E⟫ := by
      rw [inner_add_right, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right]
      ring
    have h2 : ⟪gradient Ψ (s⁻¹ • ξ), s⁻¹ • ξ⟫ = s⁻¹ * ⟪gradient Ψ (s⁻¹ • ξ), ξ⟫ :=
      real_inner_smul_right _ _ _
    rw [h1, h2]
    field_simp
    ring

/-! ### The one-sided Euler–Lagrange inequality -/

/-- The integrand of the first variation of the local functional `regFree κ Λ Ψ` at `v` in the
direction `ψ`. -/
noncomputable def varIntegrand (κ Λ : ℝ) (Ψ : Euc d → ℝ) (v ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (v x) (weakGrad v x) * ψ x
    + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (v x) (weakGrad v x), weakGrad ψ x⟫
    + (entropyDeriv κ (v x) - 2 * Λ * v x) * ψ x

theorem varIntegrand_eq_zero {κ Λ : ℝ} {v ψ : Euc d → ℝ} {x : Euc d}
    (hψ : ψ x = 0) (hg : weakGrad ψ x = 0) : varIntegrand κ Λ Ψ v ψ x = 0 := by
  rw [varIntegrand, hψ, hg]
  simp

/-- **The pointwise bound on the first-variation integrand along the family `v + τψ`.**
On `{v > a}` every term is controlled by the value bound `Sm` of `v + τψ`, the bound `B` of `ψ`
and the bound `N` of the two gradients; the crucial point is the factor `1/a` in front of `N²`,
which is what the restriction `ψ = 0` on `{v ≤ a}` buys. -/
theorem abs_varDeriv_le (hΨ : IsRegProfileWith Ψ c C) {κ Λ a Sm B N s P : ℝ} {ξ Eg : Euc d}
    (hκ : 0 < κ) (ha : 0 < a) (has : a < s) (hsS : s ≤ Sm)
    (hP0 : 0 ≤ P) (hPB : P ≤ B) (hB0 : 0 < B)
    (hξN : ‖ξ‖ ≤ N) (hEN : ‖Eg‖ ≤ N) :
    |P * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) s ξ
        + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) s ξ, Eg⟫
        + P * entropyDeriv κ s - Λ * (2 * s * P)|
      ≤ (2 * B * |Ψ 0| * Sm + B * Sm * (κ * (|Real.log a| + |Real.log Sm|) + κ / 2)
          + 2 * |Λ| * Sm * B) + (2 * B * C / a + C) * N ^ 2 := by
  have hC0 : (0 : ℝ) ≤ C := hΨ.C_nonneg
  have hc0 : (0 : ℝ) < c := hΨ.c_pos
  have hs0 : (0 : ℝ) < s := lt_trans ha has
  have hN0 : (0 : ℝ) ≤ N := le_trans (norm_nonneg ξ) hξN
  have hqnorm : ‖s⁻¹ • ξ‖ = ‖ξ‖ / s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0), inv_mul_eq_div]
  have hξ2 : ‖ξ‖ ^ 2 ≤ N ^ 2 := by nlinarith [norm_nonneg ξ]
  -- the two profile bounds
  have habsΨ : |Ψ (s⁻¹ • ξ)| ≤ |Ψ 0| + C / 2 * (‖ξ‖ / s) ^ 2 := by
    have h1 := hΨ.quadratic_upper (s⁻¹ • ξ)
    have h2 := hΨ.quadratic_lower (s⁻¹ • ξ)
    rw [hqnorm] at h1 h2
    have hcq : 0 ≤ c / 2 * (‖ξ‖ / s) ^ 2 := by positivity
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (Ψ 0)], by linarith [le_abs_self (Ψ 0)]⟩
  have habsIn : |⟪gradient Ψ (s⁻¹ • ξ), s⁻¹ • ξ⟫| ≤ C * (‖ξ‖ / s) ^ 2 := by
    have h1 : |⟪gradient Ψ (s⁻¹ • ξ), s⁻¹ • ξ⟫| ≤ ‖gradient Ψ (s⁻¹ • ξ)‖ * ‖s⁻¹ • ξ‖ :=
      abs_real_inner_le_norm _ _
    have h2 := hΨ.norm_gradient_le (s⁻¹ • ξ)
    rw [hqnorm] at h1 h2
    have h3 : (0 : ℝ) ≤ ‖ξ‖ / s := by positivity
    nlinarith [norm_nonneg (gradient Ψ (s⁻¹ • ξ))]
  -- term 1: the value derivative
  have hT1 : |P * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) s ξ| ≤
      2 * B * |Ψ 0| * Sm + (2 * B * C / a) * N ^ 2 := by
    rw [homogeneousValueDerivative_two', abs_mul, abs_of_nonneg hP0, abs_mul, abs_of_pos hs0]
    have hsum : |2 * Ψ (s⁻¹ • ξ) - ⟪gradient Ψ (s⁻¹ • ξ), s⁻¹ • ξ⟫| ≤
        2 * |Ψ 0| + 2 * C * (‖ξ‖ / s) ^ 2 := by
      have h2 : |(2 : ℝ) * Ψ (s⁻¹ • ξ)| = 2 * |Ψ (s⁻¹ • ξ)| := by
        rw [abs_mul]; norm_num
      refine le_trans (abs_sub _ _) ?_
      rw [h2]
      linarith [habsΨ, habsIn]
    have hfin : P * (s * |2 * Ψ (s⁻¹ • ξ) - ⟪gradient Ψ (s⁻¹ • ξ), s⁻¹ • ξ⟫|) ≤
        B * (s * (2 * |Ψ 0| + 2 * C * (‖ξ‖ / s) ^ 2)) :=
      mul_le_mul hPB (mul_le_mul_of_nonneg_left hsum hs0.le) (by positivity) hB0.le
    have hexp : B * (s * (2 * |Ψ 0| + 2 * C * (‖ξ‖ / s) ^ 2)) =
        2 * B * |Ψ 0| * s + 2 * B * C * ‖ξ‖ ^ 2 / s := by
      field_simp
      try ring
    have hb1 : 2 * B * |Ψ 0| * s ≤ 2 * B * |Ψ 0| * Sm :=
      mul_le_mul_of_nonneg_left hsS (by positivity)
    have hb2 : 2 * B * C * ‖ξ‖ ^ 2 / s ≤ (2 * B * C / a) * N ^ 2 := by
      have hBC : (0 : ℝ) ≤ 2 * B * C := by positivity
      rw [div_le_iff₀ hs0]
      have hrw : (2 * B * C / a) * N ^ 2 * s = (2 * B * C) * N ^ 2 * (s / a) := by
        field_simp
        try ring
      rw [hrw]
      have hsa1 : (1 : ℝ) ≤ s / a := (one_le_div ha).2 has.le
      nlinarith [mul_le_mul_of_nonneg_left hξ2 hBC,
        mul_nonneg (mul_nonneg hBC (sq_nonneg N)) (by linarith : (0 : ℝ) ≤ s / a - 1)]
    linarith [hfin, hexp.le, hexp.ge]
  -- term 2: the flux
  have hT2 : |⟪Korevaar.homogeneousFlux 2 (gradient Ψ) s ξ, Eg⟫| ≤ C * N ^ 2 := by
    rw [homogeneousFlux_two']
    have h1 : |⟪s • gradient Ψ (s⁻¹ • ξ), Eg⟫| ≤ ‖s • gradient Ψ (s⁻¹ • ξ)‖ * ‖Eg‖ :=
      abs_real_inner_le_norm _ _
    have h2 : ‖s • gradient Ψ (s⁻¹ • ξ)‖ = s * ‖gradient Ψ (s⁻¹ • ξ)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    have h3 := hΨ.norm_gradient_le (s⁻¹ • ξ)
    rw [hqnorm] at h3
    have h4 : s * ‖gradient Ψ (s⁻¹ • ξ)‖ ≤ C * ‖ξ‖ := by
      have h5 : s * (C * (‖ξ‖ / s)) = C * ‖ξ‖ := by field_simp; try ring
      calc s * ‖gradient Ψ (s⁻¹ • ξ)‖ ≤ s * (C * (‖ξ‖ / s)) :=
            mul_le_mul_of_nonneg_left h3 hs0.le
        _ = C * ‖ξ‖ := h5
    have h6 : ‖s • gradient Ψ (s⁻¹ • ξ)‖ * ‖Eg‖ ≤ (C * ‖ξ‖) * N := by
      rw [h2]
      exact mul_le_mul h4 hEN (norm_nonneg _) (by positivity)
    have h7 : (C * ‖ξ‖) * N ≤ C * N ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hC0 hN0) (sub_nonneg.2 hξN)]
    linarith [h1, h6, h7]
  -- term 3: the entropy
  have hT3 : |P * entropyDeriv κ s| ≤ B * Sm * (κ * (|Real.log a| + |Real.log Sm|) + κ / 2) := by
    rw [entropyDeriv, abs_mul, abs_of_nonneg hP0]
    have hlog : |Real.log s| ≤ |Real.log a| + |Real.log Sm| := by
      have h1 : Real.log a ≤ Real.log s := Real.log_le_log ha has.le
      have h2 : Real.log s ≤ Real.log Sm := Real.log_le_log hs0 hsS
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log Sm)],
        by linarith [le_abs_self (Real.log Sm), abs_nonneg (Real.log a)]⟩
    have hSm0 : 0 < Sm := lt_of_lt_of_le hs0 hsS
    have hb : |κ * s * Real.log s + κ / 2 * s| ≤
        Sm * (κ * (|Real.log a| + |Real.log Sm|) + κ / 2) := by
      have hb1 : |κ * s * Real.log s| = κ * s * |Real.log s| := by
        rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos hs0]
      have hb2 : |κ / 2 * s| = κ / 2 * s := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < κ / 2), abs_of_pos hs0]
      have hb3 := abs_add_le (κ * s * Real.log s) (κ / 2 * s)
      rw [hb1, hb2] at hb3
      have hb4 : κ * s * |Real.log s| ≤ κ * Sm * (|Real.log a| + |Real.log Sm|) := by
        have := mul_le_mul hsS hlog (abs_nonneg _) hSm0.le
        nlinarith [hκ.le, abs_nonneg (Real.log s)]
      have hb5 : κ / 2 * s ≤ κ / 2 * Sm := mul_le_mul_of_nonneg_left hsS (by positivity)
      nlinarith [hb3, hb4, hb5]
    have hfin := mul_le_mul hPB hb (abs_nonneg _) hB0.le
    nlinarith [hfin]
  -- term 4: the linear term
  have hT4 : |Λ * (2 * s * P)| ≤ 2 * |Λ| * Sm * B := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hs0, abs_of_nonneg hP0]
    have h1 : |(2 : ℝ)| = 2 := by norm_num
    rw [h1]
    have h2 : (0 : ℝ) ≤ |Λ| := abs_nonneg _
    nlinarith [mul_le_mul hsS hPB hP0 (le_trans hs0.le hsS), h2]
  -- assemble
  have h1 := abs_sub (P * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) s ξ
      + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) s ξ, Eg⟫ + P * entropyDeriv κ s)
    (Λ * (2 * s * P))
  have h2 := abs_add_le (P * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) s ξ
      + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) s ξ, Eg⟫) (P * entropyDeriv κ s)
  have h3 := abs_add_le (P * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) s ξ)
    (⟪Korevaar.homogeneousFlux 2 (gradient Ψ) s ξ, Eg⟫)
  linarith [hT1, hT2, hT3, hT4, h1, h2, h3]

set_option maxHeartbeats 1000000 in
/-- **The one-sided Euler–Lagrange inequality** (`REGULARIZED_ROUTE.md`, Revision 2 (iii)).

The minimizer `v` of the local functional `regFree κ Λ Ψ` (`IsRegMinimizer.regFree_le`) can be
perturbed *upwards*: `v + tψ` is again a competitor for every `t > 0` and every nonnegative
bounded `ψ ∈ W₀^{1,2}(K)`.  Hence the right derivative of `t ↦ regFree κ Λ Ψ (v + tψ)` at
`t = 0` is nonnegative, which is the displayed inequality.

The hypotheses `hψ0`/`hgψ0` — that `ψ` and its weak gradient vanish where `v ≤ a` — are what
makes the first variation *legitimate*: the value derivative of the kinetic density is
`Q_s(v, ∇v) = v(2Ψ(∇v/v) - ⟪∇Ψ(∇v/v), ∇v/v⟫)`, of size `‖∇v‖²/v`, which is **not** integrable
a priori.  Restricting the direction to `{v > a}` bounds all the difference quotients by
`K₀ 1_K + K₁(‖∇v‖² + ‖∇ψ‖²)` (`abs_varDeriv_le`), uniformly for `t ∈ (0, 1]`, so dominated
convergence applies. -/
theorem IsRegMinimizer.zero_le_integral_varIntegrand (hκ : 0 < κ)
    (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K) {v : Euc d → ℝ}
    (hv : IsRegMinimizer 2 κ Ψ K v) (hcomp : IsRegComp K v)
    {ψ : Euc d → ℝ} (hψcomp : IsRegComp K ψ) {a : ℝ} (ha : 0 < a)
    (hψ0 : ∀ x, v x ≤ a → ψ x = 0) (hgψ0 : ∀ᵐ x, v x ≤ a → weakGrad ψ x = 0) :
    Integrable (varIntegrand κ (regMin 2 κ Ψ K + κ / 4) Ψ v ψ) volume ∧
      0 ≤ ∫ x, varIntegrand κ (regMin 2 κ Ψ K + κ / 4) Ψ v ψ x := by
  classical
  obtain ⟨Λ, hΛdef⟩ : ∃ L : ℝ, L = regMin 2 κ Ψ K + κ / 4 := ⟨_, rfl⟩
  rw [← hΛdef]
  obtain ⟨M₀, hM₀⟩ := hcomp.exists_le
  obtain ⟨B₀, hB₀⟩ := hψcomp.exists_le
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max M₀ 1 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max B₀ 1 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; exact le_max_right _ _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
  have hvM : ∀ x, v x ≤ M := fun x => by rw [hMdef]; exact (hM₀ x).trans (le_max_left _ _)
  have hψB : ∀ x, ψ x ≤ B := fun x => by rw [hBdef]; exact (hB₀ x).trans (le_max_left _ _)
  have hv0 : ∀ x, 0 ≤ v x := hcomp.nonneg
  have hψnn : ∀ x, 0 ≤ ψ x := hψcomp.nonneg
  have hC0 : (0 : ℝ) ≤ C := hΨ.C_nonneg
  -- the perturbed competitors
  have hgrad : ∀ t : ℝ, HasWeakGradient (fun x => v x + t * ψ x)
      (fun x => weakGrad v x + t • weakGrad ψ x) := by
    intro t
    have h := hcomp.memW0.hasWeakGradient.add (hψcomp.memW0.hasWeakGradient.smul t)
    refine (h.congr_left (Eventually.of_forall fun x => ?_)).congr_right
      (Eventually.of_forall fun x => ?_) <;> simp
  have hwcomp : ∀ t : ℝ, 0 ≤ t → IsRegComp K (fun x => v x + t * ψ x) := by
    intro t ht
    refine ⟨⟨?_, ?_, ⟨_, hgrad t, ?_⟩⟩,
      fun x => add_nonneg (hv0 x) (mul_nonneg ht (hψnn x)), fun x hx => ?_,
      ⟨M + t * B, fun x => ?_⟩⟩
    · exact hcomp.memW0.memLp.add (hψcomp.memW0.memLp.const_mul t)
    · filter_upwards [hcomp.memW0.ae_eq_zero, hψcomp.memW0.ae_eq_zero] with x h1 h2 hx
      rw [h1 hx, h2 hx]; ring
    · exact hcomp.memW0.memLp_weakGrad.add (hψcomp.memW0.memLp_weakGrad.const_smul t)
    · rw [hcomp.eq_zero_of_notMem x hx, hψcomp.eq_zero_of_notMem x hx]; ring
    · exact add_le_add (hvM x) (mul_le_mul_of_nonneg_left (hψB x) ht)
  -- the integrand of `regFree` along the family
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → Euc d → ℝ, F = fun t x =>
      Korevaar.homogeneousDensity 2 Ψ (v x + t * ψ x) (weakGrad v x + t • weakGrad ψ x)
        + Korevaar.entropyPotential 2 κ (v x + t * ψ x) - Λ * (v x + t * ψ x) ^ 2 := ⟨_, rfl⟩
  have hFae : ∀ t : ℝ, (fun x => Korevaar.homogeneousDensity 2 Ψ
      ((fun y => v y + t * ψ y) x) (weakGrad (fun y => v y + t * ψ y) x)
      + Korevaar.entropyPotential 2 κ ((fun y => v y + t * ψ y) x)
      - Λ * ((fun y => v y + t * ψ y) x) ^ 2) =ᵐ[volume] F t := by
    intro t
    filter_upwards [(hgrad t).weakGrad_ae_eq] with x hx
    simp only [hFdef]
    rw [hx]
  have hFintegrable : ∀ t : ℝ, 0 ≤ t → Integrable (F t) volume := by
    intro t ht
    have hc := hwcomp t ht
    exact (((hc.integrable_density hΨ).add (hc.integrable_entropy hK κ)).sub
      (hc.integrable_sq.const_mul Λ)).congr (hFae t)
  have hFint : ∀ t : ℝ, 0 ≤ t → (∫ x, F t x) = regFree κ Λ Ψ (fun x => v x + t * ψ x) := by
    intro t _
    rw [regFree]
    exact (integral_congr_ae (hFae t)).symm
  have hF0 : (∫ x, F 0 x) = regFree κ Λ Ψ v := by
    have h := hFint 0 le_rfl
    have heq : (fun x => v x + (0 : ℝ) * ψ x) = v := by funext x; ring
    rwa [heq] at h
  have hquot : ∀ t : ℝ, 0 < t → 0 ≤ ∫ x, (F t x - F 0 x) / t := by
    intro t ht
    have hle := hv.regFree_le hκ hΨ hK hcomp (hwcomp t ht.le)
    rw [← hΛdef] at hle
    rw [integral_div, integral_sub (hFintegrable t ht.le) (hFintegrable 0 le_rfl),
      hFint t ht.le, hF0]
    exact div_nonneg (by linarith) ht.le
  -- the pointwise derivative along the family
  obtain ⟨G, hGdef⟩ : ∃ G : Euc d → ℝ → ℝ, G = fun x τ =>
      ψ x * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (v x + τ * ψ x)
          (weakGrad v x + τ • weakGrad ψ x)
        + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (v x + τ * ψ x)
            (weakGrad v x + τ • weakGrad ψ x), weakGrad ψ x⟫
        + ψ x * entropyDeriv κ (v x + τ * ψ x)
        - Λ * (2 * (v x + τ * ψ x) * ψ x) := ⟨_, rfl⟩
  have hGderiv : ∀ x, a < v x → ∀ τ : ℝ, 0 ≤ τ →
      HasDerivAt (fun r : ℝ => F r x) (G x τ) τ := by
    intro x hx τ hτ
    have hpos : 0 < v x + τ * ψ x := by
      have h1 : 0 ≤ τ * ψ x := mul_nonneg hτ (hψnn x)
      linarith
    have h1 := hasDerivAt_homogeneousDensity_line' hΨ.toIsRegProfile (v x) (ψ x)
      (weakGrad v x) (weakGrad ψ x) hpos
    have h2 := hasDerivAt_entropyPotential_line' κ (v x) (ψ x) hpos
    have h3 : HasDerivAt (fun r : ℝ => Λ * (v x + r * ψ x) ^ 2)
        (Λ * (2 * (v x + τ * ψ x) * ψ x)) τ := by
      have hA : HasDerivAt (fun r : ℝ => v x + r * ψ x) (ψ x) τ := by
        simpa using ((hasDerivAt_id τ).mul_const (ψ x)).const_add (v x)
      have h4 := (hA.pow 2).const_mul Λ
      refine h4.congr_deriv ?_
      push_cast
      ring
    have h5 := (h1.add h2).sub h3
    simp only [hFdef, hGdef]
    exact h5
  -- the dominating function
  obtain ⟨K₀, hK₀def⟩ : ∃ k : ℝ, k = 2 * B * |Ψ 0| * (M + B)
      + B * (M + B) * (κ * (|Real.log a| + |Real.log (M + B)|) + κ / 2)
      + 2 * |Λ| * (M + B) * B := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁def⟩ : ∃ k : ℝ, k = 2 * (2 * B * C / a + C) := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀def]; positivity
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁def]; positivity
  obtain ⟨Dom, hDomdef⟩ : ∃ D : Euc d → ℝ, D = fun x =>
      K.indicator (fun _ => K₀) x
        + K₁ * (‖weakGrad v x‖ ^ 2 + ‖weakGrad ψ x‖ ^ 2) := ⟨_, rfl⟩
  have hDom0 : ∀ x, 0 ≤ Dom x := by
    intro x
    have h1 : 0 ≤ K.indicator (fun _ => K₀) x := Set.indicator_nonneg (fun _ _ => hK₀0) x
    have h2 : 0 ≤ K₁ * (‖weakGrad v x‖ ^ 2 + ‖weakGrad ψ x‖ ^ 2) := by positivity
    rw [hDomdef]
    exact add_nonneg h1 h2
  have hDomint : Integrable Dom volume := by
    have h1 : Integrable (K.indicator fun _ => K₀) volume := by
      rw [integrable_indicator_iff hK.isOpen.measurableSet]
      exact integrableOn_const hK.isBounded.measure_lt_top.ne
    have h2 : Integrable
        (fun x => K₁ * (‖weakGrad v x‖ ^ 2 + ‖weakGrad ψ x‖ ^ 2)) volume :=
      (hcomp.integrable_normSq_grad.add hψcomp.integrable_normSq_grad).const_mul K₁
    rw [hDomdef]
    exact h1.add h2
  have hGbound : ∀ x, a < v x → ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → |G x τ| ≤ Dom x := by
    intro x hx τ hτ0 hτ1
    have hxK : x ∈ K := by
      by_contra hxK
      rw [hcomp.eq_zero_of_notMem x hxK] at hx
      linarith
    have hτψ : 0 ≤ τ * ψ x := mul_nonneg hτ0 (hψnn x)
    have hsa : a < v x + τ * ψ x := by linarith
    have hsM : v x + τ * ψ x ≤ M + B := by
      have h1 : τ * ψ x ≤ B := by
        calc τ * ψ x ≤ 1 * ψ x := mul_le_mul_of_nonneg_right hτ1 (hψnn x)
          _ = ψ x := one_mul _
          _ ≤ B := hψB x
      linarith [hvM x]
    have hξN : ‖weakGrad v x + τ • weakGrad ψ x‖ ≤
        ‖weakGrad v x‖ + ‖weakGrad ψ x‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0]
      have h1 : τ * ‖weakGrad ψ x‖ ≤ ‖weakGrad ψ x‖ := by
        calc τ * ‖weakGrad ψ x‖ ≤ 1 * ‖weakGrad ψ x‖ :=
              mul_le_mul_of_nonneg_right hτ1 (norm_nonneg _)
          _ = ‖weakGrad ψ x‖ := one_mul _
      linarith
    have hEN : ‖weakGrad ψ x‖ ≤ ‖weakGrad v x‖ + ‖weakGrad ψ x‖ := by
      linarith [norm_nonneg (weakGrad v x)]
    have hmain := abs_varDeriv_le (Λ := Λ) (Sm := M + B) hΨ hκ ha hsa hsM (hψnn x) (hψB x)
      hB0 hξN hEN
    have hNsq : (‖weakGrad v x‖ + ‖weakGrad ψ x‖) ^ 2 ≤
        2 * (‖weakGrad v x‖ ^ 2 + ‖weakGrad ψ x‖ ^ 2) := by
      nlinarith [sq_nonneg (‖weakGrad v x‖ - ‖weakGrad ψ x‖)]
    have hGx : G x τ = ψ x * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ)
          (v x + τ * ψ x) (weakGrad v x + τ • weakGrad ψ x)
        + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (v x + τ * ψ x)
            (weakGrad v x + τ • weakGrad ψ x), weakGrad ψ x⟫
        + ψ x * entropyDeriv κ (v x + τ * ψ x)
        - Λ * (2 * (v x + τ * ψ x) * ψ x) := by rw [hGdef]
    rw [hGx]
    simp only [hDomdef]
    rw [Set.indicator_of_mem hxK, hK₀def, hK₁def]
    have hpos : (0 : ℝ) ≤ 2 * B * C / a + C := by positivity
    nlinarith [hmain, mul_le_mul_of_nonneg_left hNsq hpos]
  -- dominated convergence along `t = 1/(n+1)`
  obtain ⟨tn, htndef⟩ : ∃ t : ℕ → ℝ, t = fun n : ℕ => 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have htn0 : ∀ n, 0 < tn n := fun n => by rw [htndef]; positivity
  have htn1 : ∀ n, tn n ≤ 1 := fun n => by
    rw [htndef]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by linarith)]
    linarith
  have htnlim : Tendsto tn atTop (𝓝 0) := by
    rw [htndef]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hzero : ∀ x, ψ x = 0 → weakGrad ψ x = 0 → ∀ t : ℝ, F t x = F 0 x := by
    intro x hψx hgψx t
    simp only [hFdef, hψx, hgψx]
    norm_num
  have hlim : ∀ᵐ x, Tendsto (fun n => (F (tn n) x - F 0 x) / tn n) atTop
      (𝓝 (varIntegrand κ Λ Ψ v ψ x)) := by
    filter_upwards [hgψ0] with x hgx
    rcases le_or_gt (v x) a with hle | hgt
    · have hψx : ψ x = 0 := hψ0 x hle
      have hgψx : weakGrad ψ x = 0 := hgx hle
      rw [varIntegrand_eq_zero hψx hgψx]
      have hc : ∀ n, (F (tn n) x - F 0 x) / tn n = 0 := by
        intro n; rw [hzero x hψx hgψx (tn n)]; simp
      simp [hc]
    · have hd := hGderiv x hgt 0 le_rfl
      have hG0 : G x 0 = varIntegrand κ Λ Ψ v ψ x := by
        rw [hGdef, varIntegrand]
        norm_num
        ring
      rw [hG0] at hd
      have hslope := hasDerivAt_iff_tendsto_slope.1 hd
      have hnhds : Tendsto tn atTop (𝓝[≠] (0 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htnlim
          (Eventually.of_forall fun n => (htn0 n).ne')
      have hcomp2 := hslope.comp hnhds
      refine hcomp2.congr fun n => ?_
      simp [slope_def_field, div_eq_inv_mul]
  have hdom : ∀ n, ∀ᵐ x, ‖(F (tn n) x - F 0 x) / tn n‖ ≤ Dom x := by
    intro n
    filter_upwards [hgψ0] with x hgx
    rcases le_or_gt (v x) a with hle | hgt
    · rw [hzero x (hψ0 x hle) (hgx hle) (tn n)]
      simpa using hDom0 x
    · have hdiff : ∀ τ ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun r : ℝ => F r x) τ :=
        fun τ hτ => (hGderiv x hgt τ hτ.1).differentiableAt
      have hbd : ∀ τ ∈ Icc (0 : ℝ) 1, ‖deriv (fun r : ℝ => F r x) τ‖ ≤ Dom x := by
        intro τ hτ
        rw [(hGderiv x hgt τ hτ.1).deriv, Real.norm_eq_abs]
        exact hGbound x hgt τ hτ.1 hτ.2
      have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hdiff hbd
        (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ⟨(htn0 n).le, htn1 n⟩
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (htn0 n), div_le_iff₀ (htn0 n)]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_pos (htn0 n)] at hmvt
      linarith [hmvt]
  have hmeasF : ∀ n, AEStronglyMeasurable (fun x => (F (tn n) x - F 0 x) / tn n) volume := by
    intro n
    have h := (((hFintegrable (tn n) (htn0 n).le).1).sub
      (hFintegrable 0 le_rfl).1).mul_const ((tn n)⁻¹)
    exact h.congr (Eventually.of_forall fun x => (div_eq_mul_inv _ _).symm)
  have hVmeas : AEStronglyMeasurable (varIntegrand κ Λ Ψ v ψ) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeasF hlim
  have hVbound : ∀ᵐ x, ‖varIntegrand κ Λ Ψ v ψ x‖ ≤ Dom x := by
    filter_upwards [hlim, ae_all_iff.2 hdom] with x hx hb
    exact le_of_tendsto hx.norm (Eventually.of_forall hb)
  have hVint : Integrable (varIntegrand κ Λ Ψ v ψ) volume :=
    Integrable.mono' hDomint hVmeas hVbound
  refine ⟨hVint, ?_⟩
  have hconv := tendsto_integral_of_dominated_convergence Dom hmeasF hDomint hdom hlim
  exact ge_of_tendsto hconv (Eventually.of_forall fun n => hquot (tn n) (htn0 n))

/-! ### Cut-off test functions built from a profile of the minimizer -/

set_option maxHeartbeats 1000000 in
/-- **The one-sided Euler–Lagrange inequality for the test functions `η² Φ(v)`.**

`Φ` is a profile that vanishes, together with its derivative, on `[0, a]`; the test function
`ψ = η² Φ(v)` then vanishes with its gradient on `{v ≤ a}`, which is exactly the hypothesis of
`IsRegMinimizer.zero_le_integral_varIntegrand`.  The profiles used downstream are regularized
versions of `Φ(t) = f(-log t)/t`: they produce the logarithmic Caccioppoli estimate, and the
cut at `a` is what keeps every integral finite.

Besides the inequality the statement records the two facts about `ψ` that the pointwise
computation needs: that it is a competitor, and the formula for its weak gradient. -/
theorem IsRegMinimizer.zero_le_varIntegrand_cutoff (hκ : 0 < κ)
    (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K) {v : Euc d → ℝ}
    (hv : IsRegMinimizer 2 κ Ψ K v) (hcomp : IsRegComp K v) {S : ℝ} (hS : 0 ≤ S)
    (hvS : ∀ x, v x ∈ Icc 0 S)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    {Φ Φ' : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hΦd : ∀ t ∈ Icc (0 : ℝ) S, HasDerivAt Φ (Φ' t) t) (hΦc : ContinuousOn Φ' (Icc 0 S))
    (hΦnn : ∀ t, 0 ≤ Φ t) (hΦ0 : ∀ t, t ≤ a → Φ t = 0) (hΦ'0 : ∀ t, t ≤ a → Φ' t = 0) :
    IsRegComp K (fun x => η x ^ 2 * Φ (v x)) ∧
      weakGrad (fun x => η x ^ 2 * Φ (v x)) =ᵐ[volume]
        (fun x => η x ^ 2 • (Φ' (v x) • weakGrad v x)
          + Φ (v x) • gradient (fun y => η y ^ 2) x) ∧
      0 ≤ ∫ x, varIntegrand κ (regMin 2 κ Ψ K + κ / 4) Ψ v (fun y => η y ^ 2 * Φ (v y)) x := by
  classical
  have hΦzero : Φ 0 = 0 := hΦ0 0 ha.le
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by exact_mod_cast le_top)
  have hηsq : ContDiff ℝ ∞ (fun x => η x ^ 2) := hη.pow 2
  have hηsqs : HasCompactSupport (fun x => η x ^ 2) := by
    rw [HasCompactSupport, tsupport_sq]; exact hηs
  have hηsqK : tsupport (fun x => η x ^ 2) ⊆ K := by rw [tsupport_sq]; exact hηK
  -- `Φ ∘ v` lies in `W₀^{1,2}(K)`
  obtain ⟨hΦW, hΦg⟩ :=
    memW0_comp_sub_of_hasDerivAt (p := 2) one_lt_two hcomp.memW0 hS hvS hΦd hΦc
  simp only [hΦzero, sub_zero] at hΦW hΦg
  obtain ⟨hψW, hψg⟩ := hΦW.contDiff_mul_const_add hηsq hηsqs hηsqK 0
  simp only [zero_add] at hψW hψg
  -- the weak gradient of `ψ`
  have hψgrad : weakGrad (fun x => η x ^ 2 * Φ (v x)) =ᵐ[volume]
      (fun x => η x ^ 2 • (Φ' (v x) • weakGrad v x)
        + Φ (v x) • gradient (fun y => η y ^ 2) x) := by
    filter_upwards [hψg, hΦg] with x h1 h2
    rw [h1, h2]
  -- `ψ` is a competitor
  have hΦcont : ContinuousOn Φ (Icc 0 S) := fun t ht =>
    (hΦd t ht).continuousAt.continuousWithinAt
  obtain ⟨Bφ, hBφ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_bound_of_continuousOn hΦcont
  obtain ⟨Aη, hAη⟩ := (hηsq.continuous).bounded_above_of_compact_support hηsqs
  have hψcomp : IsRegComp K (fun x => η x ^ 2 * Φ (v x)) := by
    refine ⟨hψW, fun x => mul_nonneg (sq_nonneg _) (hΦnn (v x)), fun x hx => ?_,
      ⟨Aη * Bφ, fun x => ?_⟩⟩
    · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport fun hmem => hx (hηK hmem)
      rw [hηx]; ring
    · have h1 : η x ^ 2 ≤ Aη := le_trans (le_abs_self _) (by
        rw [← Real.norm_eq_abs]; exact hAη x)
      have h2 : Φ (v x) ≤ Bφ := le_trans (le_abs_self _) (by
        rw [← Real.norm_eq_abs]; exact hBφ (v x) (hvS x))
      exact mul_le_mul h1 h2 (hΦnn (v x)) (le_trans (sq_nonneg (η x)) h1)
  refine ⟨hψcomp, hψgrad, ?_⟩
  -- the two vanishing hypotheses
  have hψ0 : ∀ x, v x ≤ a → (fun y => η y ^ 2 * Φ (v y)) x = 0 := by
    intro x hx
    simp only []
    rw [hΦ0 (v x) hx]
    ring
  have hgψ0 : ∀ᵐ x, v x ≤ a → weakGrad (fun y => η y ^ 2 * Φ (v y)) x = 0 := by
    filter_upwards [hψgrad] with x hx hle
    rw [hx, hΦ0 (v x) hle, hΦ'0 (v x) hle]
    simp
  exact (hv.zero_le_integral_varIntegrand hκ hΨ hK hcomp hψcomp ha hψ0 hgψ0).2

/-- **The first-variation integrand at a cut-off test function, regrouped.**
With `ψ = η² Φ(v)` and `H(t) = t Φ(t)` (so `t H'(t) = t Φ(t) + t² Φ'(t)`),

`varIntegrand = 2 η² H(v) [Ψ(q) − ⟪∇Ψ(q),q⟫] + η² (v H'(v)) ⟪∇Ψ(q),q⟫
                 + v ⟪∇Ψ(q), Φ(v) ∇(η²)⟫ + η² H(v) (κ log v + κ/2 − 2Λ)`,  `q = ∇v/v`.

Every singular `1/v` has cancelled: the first bracket is bounded above by
`Ψ(0) − (c/2)‖q‖²` (`IsRegProfileWith.sub_inner_le`), which is the good term of the
logarithmic Caccioppoli inequality; the second is the only term whose sign is not automatic,
and it is the one that the choice of the profile `Φ` has to control. -/
theorem varIntegrand_cutoff_eq (Ψ : Euc d → ℝ) (κ Λ : ℝ) (v : Euc d → ℝ) {Φ Φ' : ℝ → ℝ}
    {η : Euc d → ℝ} {x : Euc d}
    (hg : weakGrad (fun y => η y ^ 2 * Φ (v y)) x
      = η x ^ 2 • (Φ' (v x) • weakGrad v x) + Φ (v x) • gradient (fun y => η y ^ 2) x) :
    varIntegrand κ Λ Ψ v (fun y => η y ^ 2 * Φ (v y)) x =
      2 * (η x ^ 2 * (v x * Φ (v x))) *
          (Ψ ((v x)⁻¹ • weakGrad v x) -
            ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫)
        + η x ^ 2 * (v x * Φ (v x) + v x ^ 2 * Φ' (v x)) *
            ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
        + v x * ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x),
            Φ (v x) • gradient (fun y => η y ^ 2) x⟫
        + η x ^ 2 * (v x * Φ (v x)) * (κ * Real.log (v x) + κ / 2 - 2 * Λ) := by
  simp only [varIntegrand]
  rw [hg, smul_smul]
  rw [inner_flux_add_valueDerivative Ψ (v x) (weakGrad v x) (η x ^ 2 * Φ (v x))
    (η x ^ 2 * Φ' (v x)) (Φ (v x) • gradient (fun y => η y ^ 2) x), entropyDeriv]
  ring

/-! ### The master logarithmic Caccioppoli inequality -/

set_option maxHeartbeats 1000000 in
/-- **The master logarithmic Caccioppoli inequality** (`REGULARIZED_ROUTE.md`, Revision 2 (iii)).

With `q = ∇v/v` and `H(t) = t Φ(t)` for a profile `Φ` vanishing with its derivative on `[0, a]`,

`c ∫ η² H(v) ‖q‖² ≤ ∫ [ 2Ψ(0) η² H(v) + η² (v H'(v)) ⟪∇Ψ(q), q⟫
                        + v ⟪∇Ψ(q), Φ(v) ∇(η²)⟫ + η² H(v) (κ log v + κ/2 − 2Λ) ]`.

This is the one-sided Euler–Lagrange inequality (`zero_le_varIntegrand_cutoff`), regrouped
(`varIntegrand_cutoff_eq`) and estimated with the **sharp** convexity inequality
`Ψ(q) − ⟪∇Ψ(q), q⟫ ≤ Ψ(0) − (c/2)‖q‖²` (`IsRegProfileWith.sub_inner_le`).

Taking `Φ(t) ≈ 1/t` (so `H ≈ 1`, `v H' ≈ 0`) turns the left-hand side into `c ∫ η² |∇ log v|²`
and the right-hand side into `O(∫η² + ∫‖∇η‖²)`; the whole point of the profile `Φ` is to make
the second term on the right — the only one whose sign is not automatic — small. -/
theorem IsRegMinimizer.log_caccioppoli_master (hκ : 0 < κ)
    (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K) {v : Euc d → ℝ}
    (hv : IsRegMinimizer 2 κ Ψ K v) (hcomp : IsRegComp K v) {S : ℝ} (hS : 0 ≤ S)
    (hvS : ∀ x, v x ∈ Icc 0 S)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    {Φ Φ' : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hΦd : ∀ t ∈ Icc (0 : ℝ) S, HasDerivAt Φ (Φ' t) t) (hΦc : ContinuousOn Φ' (Icc 0 S))
    (hΦnn : ∀ t, 0 ≤ Φ t) (hΦ0 : ∀ t, t ≤ a → Φ t = 0) (hΦ'0 : ∀ t, t ≤ a → Φ' t = 0) :
    Integrable (fun x => η x ^ 2 * (v x * Φ (v x)) *
        ‖(v x)⁻¹ • weakGrad v x‖ ^ 2) volume ∧
      Integrable (fun x => 2 * Ψ 0 * (η x ^ 2 * (v x * Φ (v x)))
        + η x ^ 2 * (v x * Φ (v x) + v x ^ 2 * Φ' (v x)) *
            ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
        + v x * ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x),
            Φ (v x) • gradient (fun y => η y ^ 2) x⟫
        + η x ^ 2 * (v x * Φ (v x)) *
            (κ * Real.log (v x) + κ / 2 - 2 * (regMin 2 κ Ψ K + κ / 4))) volume ∧
      c * (∫ x, η x ^ 2 * (v x * Φ (v x)) * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2) ≤
        ∫ x, (2 * Ψ 0 * (η x ^ 2 * (v x * Φ (v x)))
          + η x ^ 2 * (v x * Φ (v x) + v x ^ 2 * Φ' (v x)) *
              ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
          + v x * ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x),
              Φ (v x) • gradient (fun y => η y ^ 2) x⟫
          + η x ^ 2 * (v x * Φ (v x)) *
              (κ * Real.log (v x) + κ / 2 - 2 * (regMin 2 κ Ψ K + κ / 4))) := by
  classical
  obtain ⟨Λ, hΛdef⟩ : ∃ L : ℝ, L = regMin 2 κ Ψ K + κ / 4 := ⟨_, rfl⟩
  rw [← hΛdef]
  have hC0 : (0 : ℝ) ≤ C := hΨ.C_nonneg
  have hc0 : (0 : ℝ) < c := hΨ.c_pos
  obtain ⟨hψcomp, hψgrad, hzero⟩ := hv.zero_le_varIntegrand_cutoff hκ hΨ hK hcomp hS hvS
    hη hηs hηK ha hΦd hΦc hΦnn hΦ0 hΦ'0
  rw [← hΛdef] at hzero
  have hVint : Integrable (varIntegrand κ Λ Ψ v (fun y => η y ^ 2 * Φ (v y))) volume := by
    have := (hv.zero_le_integral_varIntegrand hκ hΨ hK hcomp hψcomp ha
      (fun x hx => by show η x ^ 2 * Φ (v x) = 0; rw [hΦ0 (v x) hx]; ring)
      (by filter_upwards [hψgrad] with x hx hle
          rw [hx, hΦ0 (v x) hle, hΦ'0 (v x) hle]
          simp)).1
    rwa [← hΛdef] at this
  -- bounds on the profile and the cutoff
  have hΦcont : ContinuousOn Φ (Icc 0 S) := fun t ht =>
    (hΦd t ht).continuousAt.continuousWithinAt
  obtain ⟨hΦvm, Bφ, hBφ⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hΦcont
    hcomp.aestronglyMeasurable hvS
  obtain ⟨hΦ'vm, Bφ', hBφ'⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hΦc
    hcomp.aestronglyMeasurable hvS
  have hηsq : ContDiff ℝ ∞ (fun x => η x ^ 2) := hη.pow 2
  have hηsqs : HasCompactSupport (fun x => η x ^ 2) := by
    rw [HasCompactSupport, tsupport_sq]; exact hηs
  obtain ⟨Aη, hAη⟩ := (hηsq.continuous).bounded_above_of_compact_support hηsqs
  have hBφ0 : (0 : ℝ) ≤ Bφ := le_trans (abs_nonneg (Φ (v 0))) (hBφ 0)
  have hAη0 : (0 : ℝ) ≤ Aη := le_trans (norm_nonneg _) (hAη 0)
  -- measurability of the ingredients
  have hqm : AEStronglyMeasurable (fun x => (v x)⁻¹ • weakGrad v x) volume :=
    ((hcomp.aestronglyMeasurable.aemeasurable.inv).smul
      hcomp.aestronglyMeasurable_grad.aemeasurable).aestronglyMeasurable
  have hgqm : AEStronglyMeasurable (fun x => gradient Ψ ((v x)⁻¹ • weakGrad v x)) volume :=
    (continuous_gradient (hΨ.toIsRegProfile.contDiff.of_le
      (by exact_mod_cast le_top))).comp_aestronglyMeasurable hqm
  have hηm : Continuous (fun x : Euc d => η x ^ 2) := hηsq.continuous
  -- the good term is integrable
  have hGm : AEStronglyMeasurable (fun x => η x ^ 2 * (v x * Φ (v x)) *
      ‖(v x)⁻¹ • weakGrad v x‖ ^ 2) volume :=
    ((hηm.aestronglyMeasurable.mul (hcomp.aestronglyMeasurable.mul hΦvm)).mul
      (hqm.norm.pow 2))
  have hGnn : ∀ x, 0 ≤ η x ^ 2 * (v x * Φ (v x)) * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2 := by
    intro x
    have h1 : 0 ≤ v x * Φ (v x) := mul_nonneg (hcomp.nonneg x) (hΦnn (v x))
    positivity
  have hGbd : ∀ x, ‖η x ^ 2 * (v x * Φ (v x)) * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2‖ ≤
      (Aη * (S * Bφ) / a ^ 2) * ‖weakGrad v x‖ ^ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hGnn x)]
    rcases le_or_gt (v x) a with hle | hgt
    · rw [hΦ0 (v x) hle]
      have : (0 : ℝ) ≤ (Aη * (S * Bφ) / a ^ 2) * ‖weakGrad v x‖ ^ 2 := by positivity
      simpa using this
    · have hv0 : 0 < v x := lt_trans ha hgt
      have hqn : ‖(v x)⁻¹ • weakGrad v x‖ ^ 2 = ‖weakGrad v x‖ ^ 2 / v x ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hv0), mul_pow, inv_pow]
        field_simp
      have hq2 : ‖(v x)⁻¹ • weakGrad v x‖ ^ 2 ≤ ‖weakGrad v x‖ ^ 2 / a ^ 2 := by
        rw [hqn]
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        nlinarith [hgt, ha.le]
      have h1 : η x ^ 2 ≤ Aη := le_trans (le_abs_self _) (by
        rw [← Real.norm_eq_abs]; exact hAη x)
      have h2 : Φ (v x) ≤ Bφ := le_trans (le_abs_self _) (hBφ x)
      have h3 : v x * Φ (v x) ≤ S * Bφ :=
        mul_le_mul (hvS x).2 h2 (hΦnn (v x)) hS
      have h4 : (0 : ℝ) ≤ η x ^ 2 * (v x * Φ (v x)) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg hv0.le (hΦnn (v x)))
      have h5 : η x ^ 2 * (v x * Φ (v x)) ≤ Aη * (S * Bφ) :=
        mul_le_mul h1 h3 (mul_nonneg hv0.le (hΦnn (v x))) hAη0
      have h6 : (0 : ℝ) ≤ ‖(v x)⁻¹ • weakGrad v x‖ ^ 2 := sq_nonneg _
      calc η x ^ 2 * (v x * Φ (v x)) * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2
          ≤ (Aη * (S * Bφ)) * (‖weakGrad v x‖ ^ 2 / a ^ 2) :=
            mul_le_mul h5 hq2 h6 (by positivity)
        _ = (Aη * (S * Bφ) / a ^ 2) * ‖weakGrad v x‖ ^ 2 := by ring
  have hGint : Integrable (fun x => η x ^ 2 * (v x * Φ (v x)) *
      ‖(v x)⁻¹ • weakGrad v x‖ ^ 2) volume :=
    Integrable.mono' (hcomp.integrable_normSq_grad.const_mul _) hGm
      (Eventually.of_forall hGbd)
  -- the difference between the two sides of the regrouping
  have hdiff : ∀ᵐ x, (2 * Ψ 0 * (η x ^ 2 * (v x * Φ (v x)))
        + η x ^ 2 * (v x * Φ (v x) + v x ^ 2 * Φ' (v x)) *
            ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
        + v x * ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x),
            Φ (v x) • gradient (fun y => η y ^ 2) x⟫
        + η x ^ 2 * (v x * Φ (v x)) * (κ * Real.log (v x) + κ / 2 - 2 * Λ))
      - varIntegrand κ Λ Ψ v (fun y => η y ^ 2 * Φ (v y)) x
      = 2 * (η x ^ 2 * (v x * Φ (v x))) *
          (Ψ 0 - Ψ ((v x)⁻¹ • weakGrad v x)
            + ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫) := by
    filter_upwards [hψgrad] with x hx
    rw [varIntegrand_cutoff_eq Ψ κ Λ v hx]
    ring
  have hdiffbd : ∀ᵐ x, |2 * (η x ^ 2 * (v x * Φ (v x))) *
      (Ψ 0 - Ψ ((v x)⁻¹ • weakGrad v x)
        + ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫)|
      ≤ 2 * C * (η x ^ 2 * (v x * Φ (v x)) * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2) := by
    refine Eventually.of_forall fun x => ?_
    have hHnn : (0 : ℝ) ≤ η x ^ 2 * (v x * Φ (v x)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (hcomp.nonneg x) (hΦnn (v x)))
    have hlow : 0 ≤ Ψ 0 - Ψ ((v x)⁻¹ • weakGrad v x)
        + ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫ := by
      have := hΨ.zero_le_inner_gradient_sub ((v x)⁻¹ • weakGrad v x)
      linarith
    have hup : Ψ 0 - Ψ ((v x)⁻¹ • weakGrad v x)
        + ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
        ≤ C * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2 := by
      have h1 := hΨ.quadratic_lower ((v x)⁻¹ • weakGrad v x)
      have h2 : ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
          ≤ C * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2 := by
        have h3 : ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
            ≤ ‖gradient Ψ ((v x)⁻¹ • weakGrad v x)‖ * ‖(v x)⁻¹ • weakGrad v x‖ :=
          real_inner_le_norm _ _
        have h4 := hΨ.norm_gradient_le ((v x)⁻¹ • weakGrad v x)
        nlinarith [norm_nonneg ((v x)⁻¹ • weakGrad v x)]
      have h5 : (0 : ℝ) ≤ c / 2 * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2 := by positivity
      linarith
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hup (by positivity : (0:ℝ) ≤ 2 * (η x ^ 2 * (v x * Φ (v x))))]
  have hdm : AEStronglyMeasurable (fun x => 2 * (η x ^ 2 * (v x * Φ (v x))) *
      (Ψ 0 - Ψ ((v x)⁻¹ • weakGrad v x)
        + ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫)) volume := by
    have h1 : AEStronglyMeasurable (fun x => Ψ ((v x)⁻¹ • weakGrad v x)) volume :=
      (hΨ.toIsRegProfile.contDiff.continuous).comp_aestronglyMeasurable hqm
    exact ((hηm.aestronglyMeasurable.mul (hcomp.aestronglyMeasurable.mul hΦvm)).const_mul 2).mul
      (((aestronglyMeasurable_const.sub h1).add (hgqm.inner hqm)))
  have hdint : Integrable (fun x => 2 * (η x ^ 2 * (v x * Φ (v x))) *
      (Ψ 0 - Ψ ((v x)⁻¹ • weakGrad v x)
        + ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫)) volume := by
    refine Integrable.mono' (hGint.const_mul (2 * C)) hdm ?_
    filter_upwards [hdiffbd] with x hx
    rwa [Real.norm_eq_abs]
  -- the "bad" side is integrable
  have hBint : Integrable (fun x => 2 * Ψ 0 * (η x ^ 2 * (v x * Φ (v x)))
      + η x ^ 2 * (v x * Φ (v x) + v x ^ 2 * Φ' (v x)) *
          ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
      + v x * ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x),
          Φ (v x) • gradient (fun y => η y ^ 2) x⟫
      + η x ^ 2 * (v x * Φ (v x)) * (κ * Real.log (v x) + κ / 2 - 2 * Λ)) volume := by
    refine (hVint.add hdint).congr ?_
    filter_upwards [hdiff] with x hx
    simp only [Pi.add_apply]
    linarith [hx]
  refine ⟨hGint, hBint, ?_⟩
  -- the final comparison
  have hptw : ∀ᵐ x, varIntegrand κ Λ Ψ v (fun y => η y ^ 2 * Φ (v y)) x ≤
      (2 * Ψ 0 * (η x ^ 2 * (v x * Φ (v x)))
        + η x ^ 2 * (v x * Φ (v x) + v x ^ 2 * Φ' (v x)) *
            ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x), (v x)⁻¹ • weakGrad v x⟫
        + v x * ⟪gradient Ψ ((v x)⁻¹ • weakGrad v x),
            Φ (v x) • gradient (fun y => η y ^ 2) x⟫
        + η x ^ 2 * (v x * Φ (v x)) * (κ * Real.log (v x) + κ / 2 - 2 * Λ))
      - c * (η x ^ 2 * (v x * Φ (v x)) * ‖(v x)⁻¹ • weakGrad v x‖ ^ 2) := by
    filter_upwards [hdiff] with x hx
    have hHnn : (0 : ℝ) ≤ η x ^ 2 * (v x * Φ (v x)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (hcomp.nonneg x) (hΦnn (v x)))
    have hsharp := hΨ.sub_inner_le ((v x)⁻¹ • weakGrad v x)
    nlinarith [hx, mul_le_mul_of_nonneg_left hsharp
      (by positivity : (0:ℝ) ≤ 2 * (η x ^ 2 * (v x * Φ (v x))))]
  have hfin := integral_mono_ae hVint (hBint.sub (hGint.const_mul c)) hptw
  simp only [Pi.sub_apply] at hfin
  rw [integral_sub hBint (hGint.const_mul c), integral_const_mul] at hfin
  linarith [hzero, hfin]

end Komlos.Literature.Regularized
