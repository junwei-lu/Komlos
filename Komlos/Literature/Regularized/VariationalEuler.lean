import Komlos.Literature.Regularized.VariationalEulerAux

/-!
# The weak Euler–Lagrange equation

Lane `L1` (`reg/variational`), the frozen statement `IsRegMinimizer.weak_euler_lagrange`
(proved here as `IsRegMinimizer.weak_euler_lagrange`).

## The unconstrained variational characterisation

Rescaling shows that a minimizer of the *constrained* problem minimizes the *unconstrained*
functional

`J(w) = ∫ Q(w, ∇w) + ∫ P(w) - (m + κ/4) ∫ w²`

over nonnegative elements of `W₀^{1,2}(K)`: indeed, writing `N = ∫ w²` and `z = w/√N`,

`∫ Q(w,∇w) + ∫ P(w) = N · E(z) + N (κ/4) log N ≥ N m + (κ/4)(N - 1)`

(`energy_ge_of_memW0`, using `N log N ≥ N - 1`), with equality at `w = u`.  Hence
`J(w) ≥ -κ/4 = J(u)`.

Taking `w = u + τ ψ` with `ψ` a test function and differentiating at `τ = 0` (legitimate
because `u ≥ δ > 0` on `tsupport ψ`, so the integrand is smooth in `τ` there and the
difference quotients are dominated) gives

`∫ ⟪Flux(u,∇u), ∇ψ⟫ + ∫ (D_value(u,∇u) + P'(u)) ψ = (m + κ/4) · 2 ∫ u ψ`,

which is the frozen statement.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### A bound for a continuous function with compact support -/

theorem exists_pos_bound_of_hasCompactSupport {f : Euc d → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) : ∃ Cf : ℝ, 0 < Cf ∧ ∀ x, |f x| ≤ Cf := by
  rcases eq_empty_or_nonempty (tsupport f) with hemp | hne
  · refine ⟨1, one_pos, fun x => ?_⟩
    have : f x = 0 := image_eq_zero_of_notMem_tsupport (by rw [hemp]; exact notMem_empty x)
    simp [this]
  · obtain ⟨x₀, hx₀, hmax⟩ := hfs.exists_isMaxOn hne hf.abs.continuousOn
    refine ⟨|f x₀| + 1, by positivity, fun x => ?_⟩
    by_cases hx : x ∈ tsupport f
    · have := hmax hx
      simp only [Set.mem_ofPred_eq] at this
      linarith
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
      positivity

/-- A vector-valued version. -/
theorem exists_pos_bound_of_hasCompactSupport' {f : Euc d → Euc d} (hf : Continuous f)
    (hfs : HasCompactSupport f) : ∃ Cf : ℝ, 0 < Cf ∧ ∀ x, ‖f x‖ ≤ Cf := by
  obtain ⟨Cf, hCf, hb⟩ := exists_pos_bound_of_hasCompactSupport (f := fun x => ‖f x‖)
    hf.norm (hfs.comp_left (g := fun v : Euc d => ‖v‖) norm_zero)
  exact ⟨Cf, hCf, fun x => le_trans (le_abs_self _) (hb x)⟩

/-! ### Quantitative bounds for the flux and the value derivative -/

theorem deriv_entropyPotential_two {κ a : ℝ} (ha : 0 < a) :
    deriv (Korevaar.entropyPotential 2 κ) a = a * (κ * Real.log a + κ / 2) := by
  rw [(Korevaar.hasDerivAt_entropyPotential (p := 2) (κ := κ) two_ne_zero ha).deriv,
    show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

theorem abs_deriv_entropyPotential_two_le {κ : ℝ} (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) :
    |deriv (Korevaar.entropyPotential 2 κ) a| ≤ a * (κ * |Real.log a| + κ / 2) := by
  rw [deriv_entropyPotential_two ha, abs_mul, abs_of_pos ha]
  refine mul_le_mul_of_nonneg_left ?_ ha.le
  calc |κ * Real.log a + κ / 2| ≤ |κ * Real.log a| + |κ / 2| := abs_add_le _ _
    _ = κ * |Real.log a| + κ / 2 := by
        rw [abs_mul, abs_of_nonneg hκ, abs_of_nonneg (by linarith : (0 : ℝ) ≤ κ / 2)]

theorem norm_smul_inv_eq (a : ℝ) (ha : 0 < a) (b : Euc d) : ‖a⁻¹ • b‖ = ‖b‖ / a := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)]
  field_simp

theorem norm_flux_two_le (h : IsRegProfileWith Ψ c C) {a : ℝ} (ha : 0 < a) (b : Euc d) :
    ‖Korevaar.homogeneousFlux 2 (gradient Ψ) a b‖ ≤ C * ‖b‖ := by
  rw [homogeneousFlux_two, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  calc a * ‖gradient Ψ (a⁻¹ • b)‖ ≤ a * (C * ‖a⁻¹ • b‖) :=
        mul_le_mul_of_nonneg_left (h.norm_gradient_le _) ha.le
    _ = C * ‖b‖ := by rw [norm_smul_inv_eq a ha]; field_simp

theorem abs_valueDerivative_two_le (h : IsRegProfileWith Ψ c C) {a : ℝ} (ha : 0 < a)
    (b : Euc d) :
    |Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) a b|
      ≤ 2 * |Ψ 0| * a + 2 * C * (‖b‖ ^ 2 / a) := by
  rw [homogeneousValueDerivative_two]
  have hq := norm_smul_inv_eq a ha b
  have h1 : |Ψ (a⁻¹ • b)| ≤ |Ψ 0| + C / 2 * ‖a⁻¹ • b‖ ^ 2 := by
    have hlo := h.quadratic_lower (a⁻¹ • b)
    have hhi := h.quadratic_upper (a⁻¹ • b)
    have hc2 : 0 ≤ c / 2 * ‖a⁻¹ • b‖ ^ 2 := mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (Ψ 0)], by linarith [le_abs_self (Ψ 0)]⟩
  have h2 : |⟪gradient Ψ (a⁻¹ • b), a⁻¹ • b⟫| ≤ C * ‖a⁻¹ • b‖ ^ 2 := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    calc ‖gradient Ψ (a⁻¹ • b)‖ * ‖a⁻¹ • b‖ ≤ (C * ‖a⁻¹ • b‖) * ‖a⁻¹ • b‖ :=
          mul_le_mul_of_nonneg_right (h.norm_gradient_le _) (norm_nonneg _)
      _ = C * ‖a⁻¹ • b‖ ^ 2 := by ring
  have h3 : |2 * Ψ (a⁻¹ • b) - ⟪gradient Ψ (a⁻¹ • b), a⁻¹ • b⟫|
      ≤ 2 * |Ψ 0| + 2 * C * ‖a⁻¹ • b‖ ^ 2 := by
    have h4 : |2 * Ψ (a⁻¹ • b)| = 2 * |Ψ (a⁻¹ • b)| := by
      rw [abs_mul]; norm_num
    calc |2 * Ψ (a⁻¹ • b) - ⟪gradient Ψ (a⁻¹ • b), a⁻¹ • b⟫|
        ≤ |2 * Ψ (a⁻¹ • b)| + |⟪gradient Ψ (a⁻¹ • b), a⁻¹ • b⟫| := abs_sub _ _
      _ ≤ 2 * |Ψ 0| + 2 * C * ‖a⁻¹ • b‖ ^ 2 := by rw [h4]; linarith [h1, h2]
  have h5 := mul_le_mul_of_nonneg_left h3 ha.le
  have h6 : a * ‖a⁻¹ • b‖ ^ 2 = ‖b‖ ^ 2 / a := by
    rw [hq, div_pow]
    field_simp
  have h7 : a * (2 * |Ψ 0| + 2 * C * ‖a⁻¹ • b‖ ^ 2)
      = 2 * |Ψ 0| * a + 2 * C * (‖b‖ ^ 2 / a) := by rw [← h6]; ring
  rw [abs_mul, abs_of_pos ha]
  linarith [h5, h7]

/-! ### The unconstrained lower bound -/

/-- `N log N ≥ N - 1` for `N ≥ 0`, with strict inequality unless `N = 1`. -/
theorem sub_one_le_mul_log {N : ℝ} (hN : 0 ≤ N) : N - 1 ≤ N * Real.log N := by
  rcases hN.lt_or_eq with hpos | hzero
  · have h1 : 1 - N⁻¹ ≤ Real.log N := by
      have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
      rw [Real.log_inv] at h2
      linarith
    have h3 : N * (1 - N⁻¹) ≤ N * Real.log N := mul_le_mul_of_nonneg_left h1 hpos.le
    have h4 : N * (1 - N⁻¹) = N - 1 := by field_simp
    linarith
  · rw [← hzero]
    simp

theorem sub_one_lt_mul_log {N : ℝ} (hN : 0 ≤ N) (hne : N ≠ 1) : N - 1 < N * Real.log N := by
  rcases hN.lt_or_eq with hpos | hzero
  · have hinv : (N : ℝ)⁻¹ ≠ 1 := by
      intro hc
      exact hne (by field_simp at hc; linarith)
    have h1 : 1 - N⁻¹ < Real.log N := by
      have h2 := Real.log_lt_sub_one_of_pos (inv_pos.2 hpos) hinv
      rw [Real.log_inv] at h2
      linarith
    have h3 : N * (1 - N⁻¹) < N * Real.log N := mul_lt_mul_of_pos_left h1 hpos
    have h4 : N * (1 - N⁻¹) = N - 1 := by field_simp
    linarith
  · rw [← hzero]
    simp

/-- **Rescaling**: for a nonnegative element of `W₀^{1,2}(K)` with `∫ w² > 0`,
`∫ Q(w,∇w) + ∫ P(w) ≥ (∫ w²) m + (κ/4)((∫ w²) - 1)`. -/
theorem energy_ge_of_memW0_aux (h : IsRegProfileWith Ψ c C) (hκ : 0 < κ) (hK : IsGoodConvex K)
    {w : Euc d → ℝ} (hw : MemW0 2 K w) (hw0 : ∀ x, 0 ≤ w x) (hwK : ∀ x, x ∉ K → w x = 0)
    (hNpos : 0 < ∫ x, w x ^ 2) :
    Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)) volume ∧
      Integrable (fun x => Korevaar.entropyPotential 2 κ (w x)) volume ∧
      (∫ x, w x ^ 2) * regMin 2 κ Ψ K
          + κ / 4 * ((∫ x, w x ^ 2) * Real.log (∫ x, w x ^ 2))
        ≤ (∫ x, Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x))
          + ∫ x, Korevaar.entropyPotential 2 κ (w x) := by
  set N : ℝ := ∫ x, w x ^ 2 with hNdef
  set t : ℝ := Real.sqrt N with htdef
  have ht0 : 0 < t := Real.sqrt_pos.2 hNpos
  have ht2 : t ^ 2 = N := Real.sq_sqrt hNpos.le
  set z : Euc d → ℝ := fun x => t⁻¹ * w x with hzdef
  have hzx : ∀ x, z x = t⁻¹ * w x := fun _ => rfl
  have hzmem : MemW0 2 K z := (hw.smul t⁻¹).congr (Eventually.of_forall fun _ => rfl)
  have hzg : weakGrad z =ᵐ[volume] fun x => t⁻¹ • weakGrad w x :=
    ((hw.hasWeakGradient.smul t⁻¹).congr_left (Eventually.of_forall fun _ => rfl)).weakGrad_ae_eq
  have hzsq : ∀ x, N * z x ^ 2 = w x ^ 2 := by
    intro x
    rw [hzx, ← ht2]
    field_simp
  have hwsq : Integrable (fun x => w x ^ 2) volume := by
    have h1 := hw.memLp.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    refine h1.congr (Eventually.of_forall fun x => ?_)
    show ‖w x‖ ^ (ENNReal.ofReal 2).toReal = w x ^ 2
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), Real.norm_eq_abs, rpow_two_eq, sq_abs]
  have hzsqi : Integrable (fun x => z x ^ 2) volume := by
    have := hwsq.const_mul (t⁻¹ ^ 2)
    refine this.congr (Eventually.of_forall fun x => ?_)
    show t⁻¹ ^ 2 * w x ^ 2 = z x ^ 2
    rw [hzx]; ring
  have hzint : ∫ x, z x ^ 2 = 1 := by
    have heq : (∫ x, N * z x ^ 2) = ∫ x, w x ^ 2 :=
      integral_congr_ae (Eventually.of_forall hzsq)
    rw [integral_const_mul, ← hNdef] at heq
    have h2 : N * (∫ x, z x ^ 2) = N * 1 := by rw [mul_one]; exact heq
    exact mul_left_cancel₀ hNpos.ne' h2
  have hzadm : IsRegAdmissible 2 K z := by
    refine ⟨hzmem, fun x => mul_nonneg (le_of_lt (inv_pos.2 ht0)) (hw0 x), ?_, ?_⟩
    · intro x hx
      rw [hzx, hwK x hx, mul_zero]
    · rw [← hzint]
      exact integral_congr_ae (Eventually.of_forall fun x => rpow_two_eq _)
  -- pointwise identities
  have hQpt : ∀ᵐ x, Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)
      = N * Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x) := by
    filter_upwards [hzg] with x hgz
    have hwz : w x = t * z x := by rw [hzx, ← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul]
    have hgw : weakGrad w x = t • weakGrad z x := by
      rw [hgz, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
    rw [hwz, hgw, homogeneousDensity_two_smul Ψ ht0.ne', ht2]
  have hPpt : ∀ᵐ x, Korevaar.entropyPotential 2 κ (w x)
      = N * Korevaar.entropyPotential 2 κ (z x) + N * (κ / 4 * Real.log N) * z x ^ 2 := by
    refine Eventually.of_forall fun x => ?_
    have hwz : w x = t * z x := by rw [hzx, ← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul]
    have hz0 : 0 ≤ z x := mul_nonneg (le_of_lt (inv_pos.2 ht0)) (hw0 x)
    have hlogt : Real.log t = Real.log N / 2 := by rw [htdef, Real.log_sqrt hNpos.le]
    rw [hwz, entropyPotential_two_smul ht0 hz0, ht2, hlogt]
    ring
  have hIz := hzadm.integrable_kinetic h hK
  have hJz := hzadm.integrable_entropy hκ.le hK
  have hIw : Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)) volume :=
    (hIz.const_mul N).congr (hQpt.mono fun x hx => hx.symm)
  have hJw : Integrable (fun x => Korevaar.entropyPotential 2 κ (w x)) volume := by
    refine Integrable.congr ((hJz.const_mul N).add (hzsqi.const_mul (N * (κ / 4 * Real.log N))))
      ?_
    filter_upwards [hPpt] with x hx
    show N * Korevaar.entropyPotential 2 κ (z x) + N * (κ / 4 * Real.log N) * z x ^ 2
      = Korevaar.entropyPotential 2 κ (w x)
    rw [hx]
  refine ⟨hIw, hJw, ?_⟩
  have eQ : (∫ x, Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x))
      = N * ∫ x, Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x) := by
    rw [← integral_const_mul]
    exact integral_congr_ae hQpt
  have eP : (∫ x, Korevaar.entropyPotential 2 κ (w x))
      = N * (∫ x, Korevaar.entropyPotential 2 κ (z x)) + N * (κ / 4 * Real.log N) := by
    rw [integral_congr_ae hPpt,
      integral_add (hJz.const_mul N) (hzsqi.const_mul (N * (κ / 4 * Real.log N))),
      integral_const_mul, integral_const_mul, hzint, mul_one]
  have hEz : regMin 2 κ Ψ K ≤ (∫ x, Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x))
      + ∫ x, Korevaar.entropyPotential 2 κ (z x) := regMin_le_regEnergy h hκ.le hK hzadm
  rw [eQ, eP]
  have hmul : N * regMin 2 κ Ψ K
      ≤ N * ((∫ x, Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x))
        + ∫ x, Korevaar.entropyPotential 2 κ (z x)) := mul_le_mul_of_nonneg_left hEz hNpos.le
  linarith [hmul]

/-- **Rescaling**: for a nonnegative element of `W₀^{1,2}(K)`,
`∫ Q(w,∇w) + ∫ P(w) ≥ (∫ w²) m + (κ/4)(∫ w²) log (∫ w²)`. -/
theorem energy_ge_of_memW0_gen (h : IsRegProfileWith Ψ c C) (hκ : 0 < κ) (hK : IsGoodConvex K)
    {w : Euc d → ℝ} (hw : MemW0 2 K w) (hw0 : ∀ x, 0 ≤ w x) (hwK : ∀ x, x ∉ K → w x = 0) :
    Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)) volume ∧
      Integrable (fun x => Korevaar.entropyPotential 2 κ (w x)) volume ∧
      (∫ x, w x ^ 2) * regMin 2 κ Ψ K
          + κ / 4 * ((∫ x, w x ^ 2) * Real.log (∫ x, w x ^ 2))
        ≤ (∫ x, Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x))
          + ∫ x, Korevaar.entropyPotential 2 κ (w x) := by
  have hwsq0 : Integrable (fun x => w x ^ 2) volume := by
    have h1 := hw.memLp.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
    refine h1.congr (Eventually.of_forall fun x => ?_)
    show ‖w x‖ ^ (ENNReal.ofReal 2).toReal = w x ^ 2
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), Real.norm_eq_abs, rpow_two_eq, sq_abs]
  have hNnn : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rcases hNnn.lt_or_eq with hNpos | hNzero
  · exact energy_ge_of_memW0_aux h hκ hK hw hw0 hwK hNpos
  · -- `∫ w² = 0`: the competitor vanishes a.e. and both sides are `0`
    have hw00 : (fun x => w x ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hwsq0).1 hNzero.symm
    have hwz : w =ᵐ[volume] 0 := by
      filter_upwards [hw00] with x hx
      have hx1 : w x ^ 2 = 0 := hx
      have := congrArg Real.sqrt hx1
      rwa [Real.sqrt_sq (hw0 x), Real.sqrt_zero] at this
    have hgz : weakGrad w =ᵐ[volume] 0 :=
      (hw.hasWeakGradient.congr_left hwz).ae_eq HasWeakGradient.zero
    have hQz : (fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x))
        =ᵐ[volume] 0 := by
      filter_upwards [hwz] with x hx
      have hx0 : w x = 0 := hx
      rw [hx0]
      simp
    have hPz : (fun x => Korevaar.entropyPotential 2 κ (w x)) =ᵐ[volume] 0 := by
      filter_upwards [hwz] with x hx
      have hx0 : w x = 0 := hx
      rw [hx0, entropyPotential_two κ le_rfl]
      simp
    refine ⟨(integrable_zero _ _ _).congr hQz.symm, (integrable_zero _ _ _).congr hPz.symm, ?_⟩
    rw [integral_congr_ae hQz, integral_congr_ae hPz, ← hNzero]
    simp

/-! ### The first variation -/

set_option maxHeartbeats 1000000 in
/-- **(L1, `reg/variational`)** The weak Euler–Lagrange equation of the regularized energy.
This is the frozen statement `IsRegMinimizer.weak_euler_lagrange` of the interface. -/
theorem IsRegMinimizer.weak_euler_lagrange (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u)
    (hcont : Continuous u) (hpos : ∀ x ∈ K, 0 < u x)
    {ψ : Euc d → ℝ} (hψ : IsTestFn K ψ) :
    (∫ x, ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (u x) (weakGrad u x), gradient ψ x⟫) +
      (∫ x, (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (u x) (weakGrad u x) +
            deriv (Korevaar.entropyPotential 2 κ) (u x)) * ψ x) =
        (2 * regMin 2 κ Ψ K + κ / 2) * ∫ x, u x * ψ x := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  set m : ℝ := regMin 2 κ Ψ K with hm
  -- bounds for the test function and the minimizer
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    exists_pos_bound_of_hasCompactSupport hψ.contDiff.continuous hψ.hasCompactSupport
  obtain ⟨Gψ, hGψ0, hGψ⟩ := exists_pos_bound_of_hasCompactSupport'
    (continuous_gradient hψ.contDiff_one) (hasCompactSupport_gradient hψ.hasCompactSupport)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  have husupp : HasCompactSupport u :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) R)
      (fun x hx => hu.eq_zero_of_notMem x fun hxK => hx (hR hxK))
  obtain ⟨Cu, hCu0, hCu⟩ := exists_pos_bound_of_hasCompactSupport hcont husupp
  -- positivity on the support of the test function
  have hSK : tsupport ψ ⊆ K := hψ.supp_subset
  have hSne : (tsupport ψ).Nonempty :=
    (Function.support_nonempty_iff.2 hψ.ne_zero).mono subset_closure
  obtain ⟨x₀, hx₀S, hminon⟩ := hψ.hasCompactSupport.exists_isMinOn hSne hcont.continuousOn
  have hδ0 : 0 < u x₀ := hpos x₀ (hSK hx₀S)
  have hδ : ∀ x ∈ tsupport ψ, u x₀ ≤ u x := fun x hx => by
    have : x ∈ {y | u x₀ ≤ u y} := hminon hx
    exact this
  set δ : ℝ := u x₀ with hδdef
  -- the admissible interval of parameters
  set a₁ : ℝ := ∫ x, u x * ψ x with ha₁
  set ε : ℝ := min (min 1 (δ / (2 * Cψ))) (1 / (4 * |a₁| + 1)) with hεdef
  have hε0 : 0 < ε := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hε1 : ε ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεδ : ε * Cψ ≤ δ / 2 := by
    have h1 : ε ≤ δ / (2 * Cψ) := le_trans (min_le_left _ _) (min_le_right _ _)
    calc ε * Cψ ≤ δ / (2 * Cψ) * Cψ := mul_le_mul_of_nonneg_right h1 hCψ0.le
      _ = δ / 2 := by field_simp
  have hεa : ε * (4 * |a₁| + 1) ≤ 1 := by
    have h1 : ε ≤ 1 / (4 * |a₁| + 1) := min_le_right _ _
    calc ε * (4 * |a₁| + 1) ≤ 1 / (4 * |a₁| + 1) * (4 * |a₁| + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := by field_simp
  -- the perturbed competitors
  have hψ0 : ∀ x, x ∉ tsupport ψ → ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hgψ0 : ∀ x, x ∉ tsupport ψ → gradient ψ x = 0 := by
    intro x hx
    have h1 : fderiv ℝ ψ x = 0 := by
      by_contra hne
      exact hx (support_fderiv_subset ℝ (by simpa using hne))
    rw [gradient, h1, map_zero]
  have hposS : ∀ τ : ℝ, |τ| < ε → ∀ x ∈ tsupport ψ, δ / 2 ≤ u x + τ * ψ x := by
    intro τ hτ x hx
    have h1 : |τ * ψ x| ≤ |τ| * Cψ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCψ x) (abs_nonneg _)
    have h2 : |τ| * Cψ ≤ ε * Cψ := mul_le_mul_of_nonneg_right hτ.le hCψ0.le
    have h3 : |τ * ψ x| ≤ δ / 2 := by linarith [hεδ]
    have h4 := hδ x hx
    have h5 := neg_abs_le (τ * ψ x)
    linarith
  have hposAll : ∀ τ : ℝ, |τ| < ε → ∀ x, 0 ≤ u x + τ * ψ x := by
    intro τ hτ x
    by_cases hx : x ∈ tsupport ψ
    · have := hposS τ hτ x hx
      linarith
    · rw [hψ0 x hx, mul_zero, add_zero]
      exact hu.nonneg x
  have hwmem : ∀ τ : ℝ, MemW0 2 K (fun x => u x + τ * ψ x) := fun τ =>
    (hu.memW0.add ((hψ.memW0 2).smul τ)).congr (Eventually.of_forall fun _ => rfl)
  have hwg : ∀ τ : ℝ, weakGrad (fun x => u x + τ * ψ x) =ᵐ[volume]
      fun x => weakGrad u x + τ • gradient ψ x := by
    intro τ
    have h1 := hu.memW0.hasWeakGradient.add
      ((hasWeakGradient_gradient hψ.contDiff_one hψ.hasCompactSupport).smul τ)
    exact ((h1.congr_left (Eventually.of_forall fun _ => rfl)).congr_right
      (Eventually.of_forall fun _ => rfl)).weakGrad_ae_eq
  have hwK : ∀ (τ : ℝ) (x : Euc d), x ∉ K → u x + τ * ψ x = 0 := by
    intro τ x hx
    rw [hu.eq_zero_of_notMem x hx, hψ0 x fun hs => hx (hSK hs), mul_zero, add_zero]
  -- the two scalar functions of `τ`
  set F : ℝ → Euc d → ℝ := fun τ x =>
    Korevaar.homogeneousDensity 2 Ψ (u x + τ * ψ x) (weakGrad u x + τ • gradient ψ x)
      + Korevaar.entropyPotential 2 κ (u x + τ * ψ x) with hFdef
  set Fd : ℝ → Euc d → ℝ := fun τ x =>
    ψ x * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (u x + τ * ψ x)
        (weakGrad u x + τ • gradient ψ x)
      + ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (u x + τ * ψ x)
          (weakGrad u x + τ • gradient ψ x), gradient ψ x⟫
      + ψ x * deriv (Korevaar.entropyPotential 2 κ) (u x + τ * ψ x) with hFddef
  set G : ℝ → ℝ := fun τ => ∫ x, F τ x with hGdef
  set N : ℝ → ℝ := fun τ => ∫ x, (u x + τ * ψ x) ^ 2 with hNdef
  -- `N` is a quadratic polynomial
  have hψ2 : MemLp ψ 2 (volume : Measure (Euc d)) := by
    have := (hψ.memW0 2).memLp
    rwa [ofReal_two] at this
  have hψsq : Integrable (fun x => ψ x ^ 2) volume := integrable_sq_of_memLp hψ2
  have huψ : Integrable (fun x => u x * ψ x) volume :=
    integrable_mul_of_memLp hu.memLp2 hψ2
  have hNpoly : ∀ τ : ℝ, N τ = 1 + 2 * τ * a₁ + τ ^ 2 * ∫ x, ψ x ^ 2 := by
    intro τ
    have hexp : ∀ x, (u x + τ * ψ x) ^ 2
        = u x ^ 2 + 2 * τ * (u x * ψ x) + τ ^ 2 * ψ x ^ 2 := fun x => by ring
    have hI : Integrable (fun x => u x ^ 2 + 2 * τ * (u x * ψ x)) volume :=
      (hu.integrable_sq.add (huψ.const_mul (2 * τ))).congr (Eventually.of_forall fun _ => rfl)
    rw [hNdef]
    show (∫ x, (u x + τ * ψ x) ^ 2) = 1 + 2 * τ * a₁ + τ ^ 2 * ∫ x, ψ x ^ 2
    rw [integral_congr_ae (Eventually.of_forall hexp),
      integral_add hI (hψsq.const_mul (τ ^ 2)), integral_const_mul,
      integral_add hu.integrable_sq (huψ.const_mul (2 * τ)), integral_const_mul,
      hu.integral_sq, ha₁]
  have hN0 : N 0 = 1 := by rw [hNpoly]; ring
  have hNpos : ∀ τ : ℝ, |τ| < ε → 1 / 2 ≤ N τ := by
    intro τ hτ
    rw [hNpoly]
    have h1 : |2 * τ * a₁| ≤ 2 * ε * |a₁| := by
      rw [abs_mul, abs_mul]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
      have h2 : |τ| * |a₁| ≤ ε * |a₁| := mul_le_mul_of_nonneg_right hτ.le (abs_nonneg _)
      linarith [h2]
    have h3 : 2 * ε * |a₁| ≤ 1 / 2 := by nlinarith [hεa, abs_nonneg a₁, hε0]
    have h4 : (0 : ℝ) ≤ τ ^ 2 * ∫ x, ψ x ^ 2 :=
      mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    have h5 := neg_abs_le (2 * τ * a₁)
    linarith
  -- `G 0 = m`
  have hG0 : G 0 = m := by
    have hpt : ∀ x, F 0 x = Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)
        + Korevaar.entropyPotential 2 κ (u x) := by
      intro x
      simp [hFdef]
    rw [hGdef]
    show (∫ x, F 0 x) = m
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_add (hu.integrable_kinetic h hK) (hu.integrable_entropy hκ.le hK)]
    exact hu.energy_eq
  -- the unconstrained lower bound
  have hGlower : ∀ τ : ℝ, |τ| < ε → N τ * m + κ / 4 * (N τ - 1) ≤ G τ := by
    intro τ hτ
    have hNτ : 0 < ∫ x, (u x + τ * ψ x) ^ 2 := by
      have h1 := hNpos τ hτ
      rw [hNdef] at h1
      linarith
    obtain ⟨hI1, hI2, hineq⟩ :=
      energy_ge_of_memW0_gen h hκ hK (hwmem τ) (hposAll τ hτ) (hwK τ)
    have hI1' : Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (u x + τ * ψ x)
        (weakGrad u x + τ • gradient ψ x)) volume := by
      refine hI1.congr ?_
      filter_upwards [hwg τ] with x hx
      rw [hx]
    have heq1 : (∫ x, Korevaar.homogeneousDensity 2 Ψ (u x + τ * ψ x)
          (weakGrad (fun y => u y + τ * ψ y) x))
        = ∫ x, Korevaar.homogeneousDensity 2 Ψ (u x + τ * ψ x)
            (weakGrad u x + τ • gradient ψ x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwg τ] with x hx
      rw [hx]
    have hGτ : G τ = (∫ x, Korevaar.homogeneousDensity 2 Ψ (u x + τ * ψ x)
          (weakGrad u x + τ • gradient ψ x))
        + ∫ x, Korevaar.entropyPotential 2 κ (u x + τ * ψ x) := by
      rw [hGdef]
      exact integral_add hI1' hI2
    rw [hGτ, ← heq1]
    have hNeq : N τ = ∫ x, (u x + τ * ψ x) ^ 2 := rfl
    rw [hNeq]
    have hlog := sub_one_le_mul_log (N := ∫ x, (u x + τ * ψ x) ^ 2) (le_of_lt hNτ)
    nlinarith [hineq, hlog, hκ]
  -- the derivative of `N`
  have hNderiv : HasDerivAt N (2 * a₁) 0 := by
    have ha : HasDerivAt (fun τ : ℝ => 2 * τ * a₁) (2 * a₁) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const a₁
    have hb : HasDerivAt (fun τ : ℝ => τ ^ 2 * ∫ x, ψ x ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x, ψ x ^ 2)
    have hc : HasDerivAt (fun τ : ℝ => 1 + 2 * τ * a₁ + τ ^ 2 * ∫ x, ψ x ^ 2) (2 * a₁) 0 := by
      have hh := (ha.const_add (1 : ℝ)).add hb
      have h2 : HasDerivAt (fun τ : ℝ => 1 + 2 * τ * a₁ + τ ^ 2 * ∫ x, ψ x ^ 2)
          (2 * a₁ + 0) 0 := hh.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
      simpa using h2
    exact hc.congr_of_eventuallyEq (Eventually.of_forall fun τ => hNpoly τ)
  -- shared measurability data and constants
  have hSmeas : MeasurableSet (tsupport ψ) := (isClosed_tsupport ψ).measurableSet
  have hSvol : volume (tsupport ψ) ≠ ⊤ := hψ.hasCompactSupport.measure_lt_top.ne
  have hψc : Continuous ψ := hψ.contDiff.continuous
  have hgψc : Continuous (gradient ψ) := continuous_gradient hψ.contDiff_one
  have hgm : AEStronglyMeasurable (weakGrad u) volume := hu.aestronglyMeasurable_weakGrad
  have hCsum : (0 : ℝ) < Cu + Cψ := by linarith
  set Lb : ℝ := (Cu + Cψ) + |Real.log (δ / 2)| with hLbdef
  have hLb0 : (0 : ℝ) ≤ Lb := by
    have := abs_nonneg (Real.log (δ / 2))
    rw [hLbdef]; linarith
  have hLb : ∀ a : ℝ, δ / 2 ≤ a → a ≤ Cu + Cψ → |Real.log a| ≤ Lb := by
    intro a h1 h2
    have ha0 : 0 < a := lt_of_lt_of_le (by linarith) h1
    have hu1 : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
    have hl1 : Real.log (δ / 2) ≤ Real.log a := Real.log_le_log (by linarith) h1
    have hl2 := neg_abs_le (Real.log (δ / 2))
    have hl3 := abs_nonneg (Real.log (δ / 2))
    rw [abs_le, hLbdef]
    constructor <;> linarith
  set A0 : ℝ := Cψ * (2 * |Ψ 0| * (Cu + Cψ)) + Cψ * ((Cu + Cψ) * (κ * Lb + κ / 2)) + C * Gψ
    with hA0def
  set B0 : ℝ := Cψ * (2 * C / (δ / 2)) + C * Gψ with hB0def
  have hκLb : (0 : ℝ) ≤ κ * Lb + κ / 2 := by nlinarith [hκ, hLb0]
  have hA00 : (0 : ℝ) ≤ A0 := by
    have h1 : (0 : ℝ) ≤ Cψ * (2 * |Ψ 0| * (Cu + Cψ)) :=
      mul_nonneg hCψ0.le (mul_nonneg (by linarith [abs_nonneg (Ψ 0)]) hCsum.le)
    have h2 : (0 : ℝ) ≤ Cψ * ((Cu + Cψ) * (κ * Lb + κ / 2)) :=
      mul_nonneg hCψ0.le (mul_nonneg hCsum.le hκLb)
    have h3 : (0 : ℝ) ≤ C * Gψ := mul_nonneg h.C_nonneg hGψ0.le
    rw [hA0def]; linarith
  have hB00 : (0 : ℝ) ≤ B0 := by
    have h1 : (0 : ℝ) ≤ Cψ * (2 * C / (δ / 2)) :=
      mul_nonneg hCψ0.le (div_nonneg (by linarith [h.C_nonneg]) (by linarith))
    have h3 : (0 : ℝ) ≤ C * Gψ := mul_nonneg h.C_nonneg hGψ0.le
    rw [hB0def]; linarith
  set bnd : Euc d → ℝ := (tsupport ψ).indicator
    (fun y => A0 + B0 * (2 * ‖weakGrad u y‖ ^ 2 + 2 * Gψ ^ 2)) with hbnddef
  have hbndint : Integrable bnd volume := by
    rw [hbnddef]
    refine (integrable_indicator_iff hSmeas).2 ?_
    have h1 : IntegrableOn (fun _ : Euc d => A0) (tsupport ψ) volume := integrableOn_const hSvol
    have hA : IntegrableOn (fun y => 2 * ‖weakGrad u y‖ ^ 2) (tsupport ψ) volume :=
      (hu.integrable_normSq_weakGrad.const_mul 2).integrableOn
    have hB : IntegrableOn (fun _ : Euc d => 2 * Gψ ^ 2) (tsupport ψ) volume :=
      integrableOn_const hSvol
    have h2 : IntegrableOn (fun y => B0 * (2 * ‖weakGrad u y‖ ^ 2 + 2 * Gψ ^ 2))
        (tsupport ψ) volume :=
      ((hA.add hB).const_mul B0).congr (Eventually.of_forall fun _ => rfl)
    exact (h1.add h2).congr (Eventually.of_forall fun _ => rfl)
  -- the pointwise bound for the derivative
  have hFdzero : ∀ (τ : ℝ) (x : Euc d), x ∉ tsupport ψ → Fd τ x = 0 := by
    intro τ x hx
    rw [hFddef]
    simp [hψ0 x hx, hgψ0 x hx]
  have hbound_pt : ∀ τ : ℝ, |τ| < ε → ∀ x, |Fd τ x| ≤ bnd x := by
    intro τ hτ x
    by_cases hx : x ∈ tsupport ψ
    · rw [hbnddef, Set.indicator_of_mem hx]
      have hτ1 : |τ| ≤ 1 := le_trans hτ.le hε1
      have hax : δ / 2 ≤ u x + τ * ψ x := hposS τ hτ x hx
      have hax0 : 0 < u x + τ * ψ x := lt_of_lt_of_le (by linarith) hax
      have hτψ : |τ * ψ x| ≤ Cψ := by
        rw [abs_mul]
        calc |τ| * |ψ x| ≤ 1 * Cψ := mul_le_mul hτ1 (hCψ x) (abs_nonneg _) zero_le_one
          _ = Cψ := one_mul _
      have haxu : u x + τ * ψ x ≤ Cu + Cψ := by
        have h1 := le_abs_self (u x)
        have h2 := le_abs_self (τ * ψ x)
        linarith [hCu x, hτψ]
      have hbx : ‖weakGrad u x + τ • gradient ψ x‖ ≤ ‖weakGrad u x‖ + Gψ := by
        have hsm : ‖τ • gradient ψ x‖ ≤ Gψ := by
          rw [norm_smul, Real.norm_eq_abs]
          calc |τ| * ‖gradient ψ x‖ ≤ 1 * Gψ :=
                mul_le_mul hτ1 (hGψ x) (norm_nonneg _) zero_le_one
            _ = Gψ := one_mul _
        calc ‖weakGrad u x + τ • gradient ψ x‖
            ≤ ‖weakGrad u x‖ + ‖τ • gradient ψ x‖ := norm_add_le _ _
          _ ≤ ‖weakGrad u x‖ + Gψ := by linarith
      have hbsq : ‖weakGrad u x + τ • gradient ψ x‖ ^ 2
          ≤ 2 * ‖weakGrad u x‖ ^ 2 + 2 * Gψ ^ 2 := by
        nlinarith [norm_nonneg (weakGrad u x + τ • gradient ψ x), norm_nonneg (weakGrad u x),
          hGψ0.le, hbx, sq_nonneg (‖weakGrad u x‖ - Gψ)]
      -- the three terms
      have hVD := abs_valueDerivative_two_le h hax0 (weakGrad u x + τ • gradient ψ x)
      have hdiv : 2 * C * (‖weakGrad u x + τ • gradient ψ x‖ ^ 2 / (u x + τ * ψ x))
          ≤ 2 * C / (δ / 2) * ‖weakGrad u x + τ • gradient ψ x‖ ^ 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by linarith [h.C_nonneg])
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) hax
      have hVD' : |Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (u x + τ * ψ x)
            (weakGrad u x + τ • gradient ψ x)|
          ≤ 2 * |Ψ 0| * (Cu + Cψ) + 2 * C / (δ / 2)
              * ‖weakGrad u x + τ • gradient ψ x‖ ^ 2 := by
        have hΨ0 : (0 : ℝ) ≤ 2 * |Ψ 0| := by linarith [abs_nonneg (Ψ 0)]
        nlinarith [hVD, hdiv, haxu, hΨ0]
      have h1 : |ψ x * Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (u x + τ * ψ x)
            (weakGrad u x + τ • gradient ψ x)|
          ≤ Cψ * (2 * |Ψ 0| * (Cu + Cψ))
            + Cψ * (2 * C / (δ / 2)) * ‖weakGrad u x + τ • gradient ψ x‖ ^ 2 := by
        rw [abs_mul]
        have := mul_le_mul (hCψ x) hVD' (abs_nonneg _) hCψ0.le
        nlinarith [this]
      have h2 : |⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (u x + τ * ψ x)
            (weakGrad u x + τ • gradient ψ x), gradient ψ x⟫|
          ≤ C * Gψ + C * Gψ * ‖weakGrad u x + τ • gradient ψ x‖ ^ 2 := by
        have hf := norm_flux_two_le h hax0 (weakGrad u x + τ • gradient ψ x)
        have hcs := abs_real_inner_le_norm
          (Korevaar.homogeneousFlux 2 (gradient Ψ) (u x + τ * ψ x)
            (weakGrad u x + τ • gradient ψ x)) (gradient ψ x)
        have hmul : ‖Korevaar.homogeneousFlux 2 (gradient Ψ) (u x + τ * ψ x)
              (weakGrad u x + τ • gradient ψ x)‖ * ‖gradient ψ x‖
            ≤ (C * ‖weakGrad u x + τ • gradient ψ x‖) * Gψ :=
          mul_le_mul hf (hGψ x) (norm_nonneg _)
            (mul_nonneg h.C_nonneg (norm_nonneg _))
        have hsq : ‖weakGrad u x + τ • gradient ψ x‖
            ≤ 1 + ‖weakGrad u x + τ • gradient ψ x‖ ^ 2 := by
          nlinarith [sq_nonneg (‖weakGrad u x + τ • gradient ψ x‖ - 1)]
        nlinarith [hcs, hmul, hsq, mul_nonneg h.C_nonneg hGψ0.le]
      have h3 : |ψ x * deriv (Korevaar.entropyPotential 2 κ) (u x + τ * ψ x)|
          ≤ Cψ * ((Cu + Cψ) * (κ * Lb + κ / 2)) := by
        rw [abs_mul]
        have hP := abs_deriv_entropyPotential_two_le hκ.le hax0
        have hlog := hLb _ hax haxu
        have hP' : |deriv (Korevaar.entropyPotential 2 κ) (u x + τ * ψ x)|
            ≤ (Cu + Cψ) * (κ * Lb + κ / 2) := by
          refine le_trans hP ?_
          have hk1 : κ * |Real.log (u x + τ * ψ x)| + κ / 2 ≤ κ * Lb + κ / 2 := by
            nlinarith [hκ, hlog]
          have hk0 : (0 : ℝ) ≤ κ * |Real.log (u x + τ * ψ x)| + κ / 2 := by
            nlinarith [hκ, abs_nonneg (Real.log (u x + τ * ψ x))]
          exact mul_le_mul haxu hk1 hk0 hCsum.le
        exact mul_le_mul (hCψ x) hP' (abs_nonneg _) hCψ0.le
      have hsum : |Fd τ x| ≤ A0 + B0 * ‖weakGrad u x + τ • gradient ψ x‖ ^ 2 := by
        rw [hFddef]
        refine le_trans (abs_add_le _ _) ?_
        refine le_trans (add_le_add (abs_add_le _ _) (le_refl _)) ?_
        rw [hA0def, hB0def]
        linarith [h1, h2, h3]
      refine le_trans hsum ?_
      have := mul_le_mul_of_nonneg_left hbsq hB00
      linarith
    · rw [hFdzero τ x hx, hbnddef, Set.indicator_of_notMem hx, abs_zero]
  -- measurability
  have hmeasF : ∀ τ : ℝ, AEStronglyMeasurable (F τ) volume := by
    intro τ
    have ha : AEMeasurable (fun x => u x + τ * ψ x) volume :=
      hcont.aemeasurable.add (hψc.aemeasurable.const_mul τ)
    have hb : AEMeasurable (fun x => weakGrad u x + τ • gradient ψ x) volume :=
      hgm.aemeasurable.add (hgψc.aemeasurable.const_smul τ)
    have hQ : AEStronglyMeasurable (fun x => Korevaar.homogeneousDensity 2 Ψ (u x + τ * ψ x)
        (weakGrad u x + τ • gradient ψ x)) volume := by
      simp only [homogeneousDensity_two]
      exact ((ha.pow_const 2).mul (h.toIsRegProfile.contDiff.continuous.measurable.comp_aemeasurable
        (ha.inv.smul hb))).aestronglyMeasurable
    have hP : AEStronglyMeasurable (fun x => Korevaar.entropyPotential 2 κ (u x + τ * ψ x))
        volume := by
      have : AEStronglyMeasurable
          (fun x => κ / 2 * ((u x + τ * ψ x) ^ (2 : ℝ) * Real.log (u x + τ * ψ x))) volume :=
        (((ha.pow_const (2 : ℝ)).mul
          (Real.measurable_log.comp_aemeasurable ha)).const_mul (κ / 2)).aestronglyMeasurable
      exact this
    exact hQ.add hP
  have hmeasFd : ∀ τ : ℝ, AEStronglyMeasurable (Fd τ) volume := by
    intro τ
    have ha : AEMeasurable (fun x => u x + τ * ψ x) volume :=
      hcont.aemeasurable.add (hψc.aemeasurable.const_mul τ)
    have hb : AEMeasurable (fun x => weakGrad u x + τ • gradient ψ x) volume :=
      hgm.aemeasurable.add (hgψc.aemeasurable.const_smul τ)
    have hq : AEMeasurable (fun x => (u x + τ * ψ x)⁻¹ • (weakGrad u x + τ • gradient ψ x))
        volume := ha.inv.smul hb
    have hgrad : AEMeasurable (fun x => gradient Ψ ((u x + τ * ψ x)⁻¹
        • (weakGrad u x + τ • gradient ψ x))) volume :=
      (h.toIsRegProfile.contDiff_gradient.continuous.measurable).comp_aemeasurable hq
    have hVD : AEStronglyMeasurable (fun x => ψ x *
        Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (u x + τ * ψ x)
          (weakGrad u x + τ • gradient ψ x)) volume := by
      simp only [homogeneousValueDerivative_two]
      refine (hψc.aemeasurable.mul (ha.mul (((h.toIsRegProfile.contDiff.continuous.measurable.comp_aemeasurable
        hq).const_mul 2).sub ?_))).aestronglyMeasurable
      exact (hgrad.aestronglyMeasurable.inner hq.aestronglyMeasurable).aemeasurable
    have hFl : AEStronglyMeasurable (fun x =>
        ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (u x + τ * ψ x)
          (weakGrad u x + τ • gradient ψ x), gradient ψ x⟫) volume := by
      simp only [homogeneousFlux_two]
      exact ((ha.smul hgrad).aestronglyMeasurable).inner hgψc.aestronglyMeasurable
    have hPd : AEStronglyMeasurable (fun x => ψ x *
        deriv (Korevaar.entropyPotential 2 κ) (u x + τ * ψ x)) volume :=
      (hψc.aemeasurable.mul ((measurable_deriv _).comp_aemeasurable ha)).aestronglyMeasurable
    exact (hVD.add hFl).add hPd
  -- the pointwise derivative
  have hdiff : ∀ᵐ x : Euc d, ∀ τ ∈ Metric.ball (0 : ℝ) ε,
      HasDerivAt (fun r => F r x) (Fd τ x) τ := by
    refine Eventually.of_forall fun x => fun τ hτ => ?_
    have hτ' : |τ| < ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hτ
      exact hτ
    by_cases hx : x ∈ tsupport ψ
    · have hax0 : 0 < u x + τ * ψ x :=
        lt_of_lt_of_le (by linarith) (hposS τ hτ' x hx)
      have h1 := hasDerivAt_homogeneousDensity_line h.toIsRegProfile (u x) (ψ x)
        (weakGrad u x) (gradient ψ x) hax0
      have h2 := hasDerivAt_entropyPotential_line κ (u x) (ψ x) hax0
      exact h1.add h2
    · have hconst : ∀ r : ℝ, F r x = F 0 x := by
        intro r
        rw [hFdef]
        simp [hψ0 x hx, hgψ0 x hx]
      rw [hFdzero τ x hx]
      exact (hasDerivAt_const τ (F 0 x)).congr_of_eventuallyEq
        (Eventually.of_forall fun r => hconst r)
  -- `F 0` is integrable
  have hF0int : Integrable (F 0) volume := by
    have hpt : ∀ x, F 0 x = Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)
        + Korevaar.entropyPotential 2 κ (u x) := by
      intro x
      simp [hFdef]
    refine Integrable.congr (((hu.integrable_kinetic h hK).add
      (hu.integrable_entropy hκ.le hK))) ?_
    exact Eventually.of_forall fun x => (hpt x).symm
  -- differentiation under the integral sign
  have hGmain : Integrable (Fd 0) volume ∧ HasDerivAt G (∫ x, Fd 0 x) 0 := by
    refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bnd)
      (Metric.ball_mem_nhds (0 : ℝ) hε0) (Eventually.of_forall hmeasF) hF0int (hmeasFd 0)
      ?_ hbndint hdiff
    refine Eventually.of_forall fun x => fun τ hτ => ?_
    have hτ' : |τ| < ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hτ
      exact hτ
    rw [Real.norm_eq_abs]
    exact hbound_pt τ hτ' x
  have hGderiv : HasDerivAt G (∫ x, Fd 0 x) 0 := hGmain.2
  have hIflux : Integrable (fun x => ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (u x)
      (weakGrad u x), gradient ψ x⟫) volume := by
    have hum : AEMeasurable u volume := hcont.aemeasurable
    have hq : AEMeasurable (fun x => (u x)⁻¹ • weakGrad u x) volume :=
      hum.inv.smul hgm.aemeasurable
    have hgrad : AEMeasurable (fun x => gradient Ψ ((u x)⁻¹ • weakGrad u x)) volume :=
      (h.toIsRegProfile.contDiff_gradient.continuous.measurable).comp_aemeasurable hq
    have hmeas : AEStronglyMeasurable (fun x =>
        ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (u x) (weakGrad u x), gradient ψ x⟫) volume := by
      simp only [homogeneousFlux_two]
      exact ((hum.smul hgrad).aestronglyMeasurable).inner hgψc.aestronglyMeasurable
    have hbnd2 : Integrable ((tsupport ψ).indicator
        (fun y => C * Gψ * (1 + ‖weakGrad u y‖ ^ 2))) volume := by
      refine (integrable_indicator_iff hSmeas).2 ?_
      have hA : IntegrableOn (fun _ : Euc d => (1 : ℝ)) (tsupport ψ) volume :=
        integrableOn_const hSvol
      have hB : IntegrableOn (fun y => ‖weakGrad u y‖ ^ 2) (tsupport ψ) volume :=
        hu.integrable_normSq_weakGrad.integrableOn
      exact ((hA.add hB).const_mul (C * Gψ)).congr (Eventually.of_forall fun _ => rfl)
    refine Integrable.mono' hbnd2 hmeas (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ tsupport ψ
    · rw [Set.indicator_of_mem hx]
      have hax0 : 0 < u x := hpos x (hSK hx)
      have hf := norm_flux_two_le h hax0 (weakGrad u x)
      have hcs := abs_real_inner_le_norm
        (Korevaar.homogeneousFlux 2 (gradient Ψ) (u x) (weakGrad u x)) (gradient ψ x)
      have hmul : ‖Korevaar.homogeneousFlux 2 (gradient Ψ) (u x) (weakGrad u x)‖
            * ‖gradient ψ x‖ ≤ (C * ‖weakGrad u x‖) * Gψ :=
        mul_le_mul hf (hGψ x) (norm_nonneg _) (mul_nonneg h.C_nonneg (norm_nonneg _))
      have hsq : ‖weakGrad u x‖ ≤ 1 + ‖weakGrad u x‖ ^ 2 := by
        nlinarith [sq_nonneg (‖weakGrad u x‖ - 1)]
      have hCG : (0 : ℝ) ≤ C * Gψ := mul_nonneg h.C_nonneg hGψ0.le
      nlinarith [hcs, hmul, hsq, hCG]
    · rw [hgψ0 x hx, inner_zero_right, abs_zero, Set.indicator_of_notMem hx]
  have hIrest : Integrable (fun x =>
      (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (u x) (weakGrad u x)
        + deriv (Korevaar.entropyPotential 2 κ) (u x)) * ψ x) volume := by
    refine Integrable.congr (hGmain.1.sub hIflux) ?_
    refine Eventually.of_forall fun x => ?_
    show Fd 0 x - ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (u x) (weakGrad u x),
        gradient ψ x⟫ = _
    rw [hFddef]
    simp only [zero_mul, add_zero, zero_smul]
    ring
  -- the local minimum
  set Φ : ℝ → ℝ := fun τ => G τ - (m + κ / 4) * N τ with hΦdef
  have hΦmin : IsLocalMin Φ 0 := by
    have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε0
    filter_upwards [hball] with τ hτ
    have hτ' : |τ| < ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hτ
      exact hτ
    have h1 := hGlower τ hτ'
    show Φ 0 ≤ Φ τ
    rw [hΦdef]
    simp only []
    rw [hG0, hN0]
    nlinarith [h1]
  have hΦderiv : HasDerivAt Φ ((∫ x, Fd 0 x) - (m + κ / 4) * (2 * a₁)) 0 :=
    hGderiv.sub (hNderiv.const_mul (m + κ / 4))
  have hzero := hΦmin.hasDerivAt_eq_zero hΦderiv
  -- split the integral of `Fd 0`
  have hsplit : (∫ x, Fd 0 x)
      = (∫ x, ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (u x) (weakGrad u x), gradient ψ x⟫)
        + ∫ x, (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (u x) (weakGrad u x)
            + deriv (Korevaar.entropyPotential 2 κ) (u x)) * ψ x := by
    rw [← integral_add hIflux hIrest]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show Fd 0 x = _
    simp only [hFddef, zero_mul, add_zero, zero_smul]
    ring
  rw [hsplit] at hzero
  have : (2 * m + κ / 2) * a₁ = (m + κ / 4) * (2 * a₁) := by ring
  rw [this]
  linarith [hzero]

end Komlos.Literature.Regularized
