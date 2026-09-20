import Komlos.Literature.Regularized.InteriorWeakEqAux
import Komlos.Literature.Regularized.InteriorRep

/-!
# The weak equation for `v = -log φ` (lane `L3a`, link 1)

Link 1 of lane `L3` (`reg/c2`) of `REGULARIZED_ROUTE.md`, Revision 2 (v):
`exists_isWeakLogSol`, proved here.

## The algebra, proved here

At `p = 2`, writing `u = φ`, `v = -log u`, `q = ∇v` and `∇u = -u q`, the three densities of
`Komlos.Literature.Korevaar` collapse (using `Ψ(-q) = Ψ q` and `∇Ψ(-q) = -∇Ψ q`) to

* `homogeneousFlux 2 (∇Ψ) u (-(u • q)) = -(u • ∇Ψ q)`
  (`homogeneousFlux_two_of_neg`);
* `homogeneousValueDerivative 2 Ψ (∇Ψ) u (-(u • q)) = u (2 Ψ q - ⟪∇Ψ q, q⟫)`
  (`homogeneousValueDerivative_two_of_neg`);
* `deriv (entropyPotential 2 κ) u = u (κ log u + κ/2)` (`log_deriv_entropyPotential_two`).

Substituting the test function `χ = ψ / u`, whose gradient is `u⁻¹ ∇ψ + (ψ u⁻¹) q`, and the
multiplier `Λ = 2 m + κ/2`, the integrand of `IsRegMinimizer.weak_euler_lagrange` becomes
*exactly* minus the integrand of the weak equation of `IsWeakLogSol`:

`⟪∇Ψ(∇v), ∇ψ⟫ + (κ v + 2 m + B(∇v)) ψ = 0`,   `B(q) = 2 (⟪∇Ψ q, q⟫ - Ψ q)`.

This is `euler_lagrange_substitution`, an identity of real numbers, proved below with no
analysis at all.

## The analytic half

`χ = ψ / φ` is *not* an admissible test function for `IsRegMinimizer.weak_euler_lagrange`,
which quantifies over `IsTestFn K` (smooth), because `φ` is only continuous at this stage.
Rather than mollify `φ` — which would make the substitution smooth but force a uniform
convergence argument — the Euler–Lagrange equation itself is upgraded to *bounded* `W₀^{1,2}`
test functions (`weakEL_memW0`), by the very argument of link 3: the flux is globally `L²`
(`memLp_flux_two`) while the zeroth-order density is only `L¹` near the support
(`integrableOn_valueDerivative_add_entropy`), so the approximants must be uniformly bounded,
which is `exists_contDiff_tendsto_eLpNorm_bounded`.

`χ` is then produced without any smoothness of `φ`: the primitive `P` of
`s ↦ -((max s δ)²)⁻¹` is `C¹` with `P t = t⁻¹ + c_P` for `t ≥ δ` (`exists_inv_profile`), so
`χ = ψ (P ∘ φ - c_P)` lies in `W₀^{1,2}(tsupport ψ)` by the chain rule
`Komlos.Literature.memW0_comp` and the product rule `MemW0.contDiff_mul`, is bounded, and
equals `ψ/φ` on `tsupport ψ` because `φ ≥ δ > 0` there.  The same device, with the primitive of
`s ↦ -(max s δ)⁻¹`, gives the chain rule `hasWeakGradientOn_neg_log` for `v = -log φ`; the
additive constant it introduces is killed by `integral_fderiv_apply_eq_zero`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)}

/-! ### The `p = 2` densities along `∇u = -u ∇v` -/

/-- `u⁻¹ • (-(u • q)) = -q` for `u ≠ 0`. -/
theorem inv_smul_neg_smul {u : ℝ} (hu : u ≠ 0) (q : Euc d) : u⁻¹ • (-(u • q)) = -q := by
  rw [smul_neg, smul_smul, inv_mul_cancel₀ hu, one_smul]

/-- **The flux at `p = 2`**: `homogeneousFlux 2 (∇Ψ) u (-(u q)) = -(u ∇Ψ q)`, because `∇Ψ` is
odd (`IsRegProfile.gradient_neg`). -/
theorem homogeneousFlux_two_of_neg (hΨ : IsRegProfile Ψ) {u : ℝ} (hu : 0 < u) (q : Euc d) :
    Korevaar.homogeneousFlux 2 (gradient Ψ) u (-(u • q)) = -(u • gradient Ψ q) := by
  rw [Korevaar.homogeneousFlux, inv_smul_neg_smul hu.ne' q, hΨ.gradient_neg,
    show (2 : ℝ) - 1 = 1 from by norm_num, Real.rpow_one, smul_neg]

/-- **The value derivative at `p = 2`**:
`homogeneousValueDerivative 2 Ψ (∇Ψ) u (-(u q)) = u (2 Ψ q - ⟪∇Ψ q, q⟫)`, because `Ψ` is even and
`∇Ψ` is odd. -/
theorem homogeneousValueDerivative_two_of_neg (hΨ : IsRegProfile Ψ) {u : ℝ} (hu : 0 < u)
    (q : Euc d) :
    Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) u (-(u • q)) =
      u * (2 * Ψ q - ⟪gradient Ψ q, q⟫) := by
  rw [Korevaar.homogeneousValueDerivative, inv_smul_neg_smul hu.ne' q, hΨ.gradient_neg, hΨ.even,
    show (2 : ℝ) - 1 = 1 from by norm_num, Real.rpow_one, inner_neg_neg]

/-- **The entropy derivative at `p = 2`**: `(entropyPotential 2 κ)' u = u (κ log u + κ/2)`. -/
theorem log_deriv_entropyPotential_two {u : ℝ} (hu : 0 < u) :
    deriv (Korevaar.entropyPotential 2 κ) u = u * (κ * Real.log u + κ / 2) := by
  rw [(Korevaar.hasDerivAt_entropyPotential (by norm_num) hu).deriv,
    show (2 : ℝ) - 1 = 1 from by norm_num, Real.rpow_one]

/-! ### The substitution `χ = ψ / u` -/

/-- **The pointwise identity behind link 1.**  With `u > 0`, `q = ∇v`, `∇u = -u q`,
`gψ = ∇ψ` and the test function `χ = ψ / u` (so `∇χ = u⁻¹ ∇ψ + (ψ u⁻¹) q`), the integrand of
the weak Euler–Lagrange equation of `IsRegMinimizer.weak_euler_lagrange`, *minus* its right-hand
side `Λ u χ` with `Λ = 2 m + κ/2`, equals minus the integrand
`⟪∇Ψ(∇v), ∇ψ⟫ + (κ v + 2 m + B(∇v)) ψ` of the weak equation of `IsWeakLogSol`.

Consequently, once the substitution is justified analytically, the two weak formulations are
the same statement.  Note `v = -log u`, so `κ v = -κ log u`. -/
theorem euler_lagrange_substitution (hΨ : IsRegProfile Ψ) {m u ψ : ℝ} (hu : 0 < u)
    (q gψ : Euc d) :
    ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) u (-(u • q)), u⁻¹ • gψ + (ψ * u⁻¹) • q⟫ +
        (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) u (-(u • q)) +
          deriv (Korevaar.entropyPotential 2 κ) u) * (ψ * u⁻¹) -
        (2 * m + κ / 2) * (u * (ψ * u⁻¹)) =
      -(⟪gradient Ψ q, gψ⟫ + (κ * (-Real.log u) + 2 * m + regNatGrowth Ψ q) * ψ) := by
  rw [homogeneousFlux_two_of_neg hΨ hu q, homogeneousValueDerivative_two_of_neg hΨ hu q,
    log_deriv_entropyPotential_two hu]
  rw [inner_neg_left, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_left]
  simp only [regNatGrowth]
  field_simp
  ring

/-! ### Two elementary inputs for the chain rule -/

/-- `∫ ∂_e ψ = 0` for a `C¹` compactly supported `ψ`: integrate by parts against the *constant*
field `e`, whose divergence vanishes.  This is what makes the additive constant in the profile
`L_δ` below harmless. -/
theorem integral_fderiv_apply_eq_zero {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψs : HasCompactSupport ψ) (e : Euc d) : ∫ x, fderiv ℝ ψ x e = 0 := by
  have h := Komlos.Literature.Korevaar.integral_inner_gradient_eq_neg_integral_divergence
    (Ω := (Set.univ : Set (Euc d))) isOpen_univ (W := fun _ : Euc d => e) contDiffOn_const hψ
    hψs (Set.subset_univ _)
  have hdiv : ∀ x : Euc d, Korevaar.divergence (fun _ : Euc d => e) x = 0 := by
    intro x
    simp [Korevaar.divergence]
  simp only [hdiv, mul_zero, integral_zero, neg_zero] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show fderiv ℝ ψ x e = ⟪e, gradient ψ x⟫
  rw [fderiv_apply_eq_inner_gradient, real_inner_comm]

/-- **The logarithmic profile.**  For every `δ > 0` there is a `C¹` function `L` with `L 0 = 0`,
`|L'| ≤ δ⁻¹`, and `L t = -log t + c` (a *fixed* constant `c`) and `L' t = -t⁻¹` for `t ≥ δ`.

`L` is the primitive of the continuous bounded function `s ↦ -(max s δ)⁻¹`; the value formula
comes from the fundamental theorem of calculus applied twice, to `L` and to `Real.log`, on
`[δ, t]`. -/
theorem exists_log_profile {δ : ℝ} (hδ : 0 < δ) :
    ∃ (L : ℝ → ℝ) (c : ℝ), ContDiff ℝ 1 L ∧ L 0 = 0 ∧ (∀ t, |deriv L t| ≤ δ⁻¹) ∧
      (∀ t, δ ≤ t → L t = -Real.log t + c) ∧ ∀ t, δ ≤ t → deriv L t = -t⁻¹ := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → ℝ, γ = fun s => -(max s δ)⁻¹ := ⟨_, rfl⟩
  have hmaxpos : ∀ s : ℝ, 0 < max s δ := fun s => lt_of_lt_of_le hδ (le_max_right _ _)
  have hγc : Continuous γ := by
    rw [hγ]
    exact ((continuous_id.max continuous_const).inv₀ fun s => (hmaxpos s).ne').neg
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, L = fun t => ∫ s in (0 : ℝ)..t, γ s := ⟨_, rfl⟩
  have hLd : ∀ t, HasDerivAt L (γ t) t := fun t => by
    rw [hL]
    exact intervalIntegral.integral_hasDerivAt_right (hγc.intervalIntegrable _ _)
      (hγc.stronglyMeasurableAtFilter _ _) hγc.continuousAt
  have hderiv : deriv L = γ := funext fun t => (hLd t).deriv
  have hLC : ContDiff ℝ 1 L :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hLd t).differentiableAt, by rw [hderiv]; exact hγc⟩
  have hL0 : L 0 = 0 := by rw [hL]; simp
  have hbound : ∀ t, |deriv L t| ≤ δ⁻¹ := by
    intro t
    rw [hderiv, hγ]
    show |-(max t δ)⁻¹| ≤ δ⁻¹
    rw [abs_neg, abs_of_nonneg (inv_nonneg.2 (hmaxpos t).le)]
    simpa [one_div] using one_div_le_one_div_of_le hδ (le_max_right t δ)
  have hdv : ∀ t, δ ≤ t → deriv L t = -t⁻¹ := by
    intro t ht
    rw [hderiv, hγ]
    show -(max t δ)⁻¹ = -t⁻¹
    rw [max_eq_left ht]
  refine ⟨L, L δ + Real.log δ, hLC, hL0, hbound, ?_, hdv⟩
  intro t ht
  have huIcc : Set.uIcc δ t = Set.Icc δ t := Set.uIcc_of_le ht
  have hmem : ∀ s ∈ Set.uIcc δ t, 0 < s := by
    intro s hs
    rw [huIcc] at hs
    exact lt_of_lt_of_le hδ hs.1
  have hinvc : ContinuousOn (fun s : ℝ => s⁻¹) (Set.uIcc δ t) :=
    continuousOn_id.inv₀ fun s hs => (hmem s hs).ne'
  have h1 : (∫ s in δ..t, γ s) = L t - L δ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hLd s)
      (hγc.intervalIntegrable _ _)
  have h2 : (∫ s in δ..t, s⁻¹) = Real.log t - Real.log δ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => Real.hasDerivAt_log (hmem s hs).ne')
      (hinvc.intervalIntegrable)
  have h3 : (∫ s in δ..t, γ s) = -∫ s in δ..t, s⁻¹ := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [huIcc] at hs
    show γ s = -s⁻¹
    rw [hγ]
    show -(max s δ)⁻¹ = -s⁻¹
    rw [max_eq_left hs.1]
  rw [h2] at h3
  linarith [h1, h3]

/-- **The reciprocal profile.**  For every `δ > 0` there is a `C¹` function `P` with `P 0 = 0`,
`|P'| ≤ δ⁻²`, and `P t = t⁻¹ + c` (a *fixed* constant `c`) and `P' t = -(t²)⁻¹` for `t ≥ δ`.

Same construction as `exists_log_profile`: `P` is the primitive of the continuous bounded
function `s ↦ -((max s δ)²)⁻¹`. -/
theorem exists_inv_profile {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : ℝ → ℝ) (cP : ℝ), ContDiff ℝ 1 P ∧ P 0 = 0 ∧ (∀ t, |deriv P t| ≤ (δ ^ 2)⁻¹) ∧
      (∀ t, δ ≤ t → P t = t⁻¹ + cP) ∧ ∀ t, δ ≤ t → deriv P t = -(t ^ 2)⁻¹ := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → ℝ, γ = fun s => -((max s δ) ^ 2)⁻¹ := ⟨_, rfl⟩
  have hmaxpos : ∀ s : ℝ, 0 < max s δ := fun s => lt_of_lt_of_le hδ (le_max_right _ _)
  have hγc : Continuous γ := by
    rw [hγ]
    exact (((continuous_id.max continuous_const).pow 2).inv₀ fun s =>
      (pow_pos (hmaxpos s) 2).ne').neg
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ, P = fun t => ∫ s in (0 : ℝ)..t, γ s := ⟨_, rfl⟩
  have hPd : ∀ t, HasDerivAt P (γ t) t := fun t => by
    rw [hP]
    exact intervalIntegral.integral_hasDerivAt_right (hγc.intervalIntegrable _ _)
      (hγc.stronglyMeasurableAtFilter _ _) hγc.continuousAt
  have hderiv : deriv P = γ := funext fun t => (hPd t).deriv
  have hPC : ContDiff ℝ 1 P :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hPd t).differentiableAt, by rw [hderiv]; exact hγc⟩
  have hP0 : P 0 = 0 := by rw [hP]; simp
  have hbound : ∀ t, |deriv P t| ≤ (δ ^ 2)⁻¹ := by
    intro t
    rw [hderiv, hγ]
    show |-((max t δ) ^ 2)⁻¹| ≤ (δ ^ 2)⁻¹
    rw [abs_neg, abs_of_nonneg (inv_nonneg.2 (pow_nonneg (hmaxpos t).le 2))]
    have h1 : δ ^ 2 ≤ (max t δ) ^ 2 := by
      have := le_max_right t δ
      nlinarith [hδ.le, hmaxpos t]
    simpa [one_div] using one_div_le_one_div_of_le (by positivity) h1
  have hdv : ∀ t, δ ≤ t → deriv P t = -(t ^ 2)⁻¹ := by
    intro t ht
    rw [hderiv, hγ]
    show -((max t δ) ^ 2)⁻¹ = -(t ^ 2)⁻¹
    rw [max_eq_left ht]
  refine ⟨P, P δ - δ⁻¹, hPC, hP0, hbound, ?_, hdv⟩
  intro t ht
  have huIcc : Set.uIcc δ t = Set.Icc δ t := Set.uIcc_of_le ht
  have hmem : ∀ s ∈ Set.uIcc δ t, 0 < s := by
    intro s hs
    rw [huIcc] at hs
    exact lt_of_lt_of_le hδ hs.1
  have hcont : ContinuousOn (fun s : ℝ => -(s ^ 2)⁻¹) (Set.uIcc δ t) :=
    (((continuousOn_id.pow 2).inv₀ fun s hs => (pow_pos (hmem s hs) 2).ne')).neg
  have h1 : (∫ s in δ..t, γ s) = P t - P δ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hPd s)
      (hγc.intervalIntegrable _ _)
  have h2 : (∫ s in δ..t, -(s ^ 2)⁻¹) = t⁻¹ - δ⁻¹ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hasDerivAt_inv (hmem s hs).ne') hcont.intervalIntegrable
  have h3 : (∫ s in δ..t, γ s) = ∫ s in δ..t, -(s ^ 2)⁻¹ := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [huIcc] at hs
    show γ s = -(s ^ 2)⁻¹
    rw [hγ]
    show -((max s δ) ^ 2)⁻¹ = -(s ^ 2)⁻¹
    rw [max_eq_left hs.1]
  rw [h2] at h3
  linarith [h1, h3]

/-! ### The `p = 2` densities: unfolded form and size bounds -/

/-- `homogeneousFlux 2 (∇Ψ) u ξ = u • ∇Ψ (u⁻¹ • ξ)`. -/
theorem log_homogeneousFlux_two (A : Euc d → Euc d) (u : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousFlux 2 A u ξ = u • A (u⁻¹ • ξ) := by
  rw [Korevaar.homogeneousFlux, show (2 : ℝ) - 1 = 1 from by norm_num, Real.rpow_one]

/-- `homogeneousValueDerivative 2 Ψ A u ξ = u * (2 Ψ (u⁻¹ ξ) - ⟪A (u⁻¹ ξ), u⁻¹ ξ⟫)`. -/
theorem log_homogeneousValueDerivative_two (Ψ : Euc d → ℝ) (A : Euc d → Euc d) (u : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousValueDerivative 2 Ψ A u ξ =
      u * (2 * Ψ (u⁻¹ • ξ) - ⟪A (u⁻¹ • ξ), u⁻¹ • ξ⟫) := by
  rw [Korevaar.homogeneousValueDerivative, show (2 : ℝ) - 1 = 1 from by norm_num, Real.rpow_one]

/-- `‖flux‖ ≤ C ‖ξ‖`: the flux inherits the linear growth of `∇Ψ`, uniformly in `u ≥ 0`. -/
theorem norm_homogeneousFlux_two_le (h : IsRegProfileWith Ψ c C) {u : ℝ} (hu : 0 ≤ u)
    (ξ : Euc d) : ‖Korevaar.homogeneousFlux 2 (gradient Ψ) u ξ‖ ≤ C * ‖ξ‖ := by
  rw [log_homogeneousFlux_two]
  rcases eq_or_lt_of_le hu with h0 | hpos
  · rw [← h0, zero_smul, norm_zero]
    exact mul_nonneg h.C_nonneg (norm_nonneg _)
  · rw [norm_smul, Real.norm_of_nonneg hu]
    have h1 : ‖gradient Ψ (u⁻¹ • ξ)‖ ≤ C * ‖u⁻¹ • ξ‖ := h.norm_gradient_le _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hu)] at h1
    have h2 : u * ‖gradient Ψ (u⁻¹ • ξ)‖ ≤ u * (C * (u⁻¹ * ‖ξ‖)) :=
      mul_le_mul_of_nonneg_left h1 hu
    have h3 : u * (C * (u⁻¹ * ‖ξ‖)) = C * ‖ξ‖ := by
      field_simp
    linarith

/-- `|valueDerivative| ≤ 2 u |Ψ 0| + 2 C ‖ξ‖²/u`: the value derivative has the quadratic growth
of `Ψ`, with the `1/u` coming from the `2`-homogeneity. -/
theorem abs_homogeneousValueDerivative_two_le (h : IsRegProfileWith Ψ c C) {u : ℝ} (hu : 0 < u)
    (ξ : Euc d) :
    |Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) u ξ| ≤
      2 * u * |Ψ 0| + 2 * C * ‖ξ‖ ^ 2 / u := by
  rw [log_homogeneousValueDerivative_two]
  obtain ⟨ξ', hξ'⟩ : ∃ q : Euc d, q = u⁻¹ • ξ := ⟨_, rfl⟩
  have hnorm : ‖ξ'‖ = u⁻¹ * ‖ξ‖ := by
    rw [hξ', norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hu.le)]
  have hΨup : Ψ ξ' ≤ Ψ 0 + C / 2 * ‖ξ'‖ ^ 2 := h.quadratic_upper ξ'
  have hΨlo : Ψ 0 ≤ Ψ ξ' := by
    have := h.quadratic_lower ξ'
    nlinarith [sq_nonneg ‖ξ'‖, h.c_pos]
  have hΨabs : |Ψ ξ'| ≤ |Ψ 0| + C / 2 * ‖ξ'‖ ^ 2 := by
    have h1 : Ψ 0 ≤ |Ψ 0| := le_abs_self _
    have h2 : -|Ψ 0| ≤ Ψ 0 := neg_abs_le _
    have h3 : (0:ℝ) ≤ C / 2 * ‖ξ'‖ ^ 2 := by
      have := h.C_nonneg
      positivity
    rw [abs_le]
    constructor <;> linarith
  have hinner : |⟪gradient Ψ ξ', ξ'⟫| ≤ C * ‖ξ'‖ ^ 2 := by
    have h1 : |⟪gradient Ψ ξ', ξ'⟫| ≤ ‖gradient Ψ ξ'‖ * ‖ξ'‖ := abs_real_inner_le_norm _ _
    have h2 : ‖gradient Ψ ξ'‖ ≤ C * ‖ξ'‖ := h.norm_gradient_le ξ'
    nlinarith [norm_nonneg ξ', norm_nonneg (gradient Ψ ξ')]
  have hbr : |2 * Ψ ξ' - ⟪gradient Ψ ξ', ξ'⟫| ≤ 2 * |Ψ 0| + 2 * C * ‖ξ'‖ ^ 2 := by
    have h4 : Ψ ξ' ≤ |Ψ ξ'| := le_abs_self _
    have h5 : -|Ψ ξ'| ≤ Ψ ξ' := neg_abs_le _
    have h6 : ⟪gradient Ψ ξ', ξ'⟫ ≤ |⟪gradient Ψ ξ', ξ'⟫| := le_abs_self _
    have h7 : -|⟪gradient Ψ ξ', ξ'⟫| ≤ ⟪gradient Ψ ξ', ξ'⟫ := neg_abs_le _
    rw [abs_le]
    constructor <;> linarith
  rw [← hξ', abs_mul, abs_of_nonneg hu.le]
  have hfin : u * (2 * |Ψ 0| + 2 * C * ‖ξ'‖ ^ 2) = 2 * u * |Ψ 0| + 2 * C * ‖ξ‖ ^ 2 / u := by
    rw [hnorm]
    field_simp
    try ring
  calc u * |2 * Ψ ξ' - ⟪gradient Ψ ξ', ξ'⟫| ≤ u * (2 * |Ψ 0| + 2 * C * ‖ξ'‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbr hu.le
    _ = 2 * u * |Ψ 0| + 2 * C * ‖ξ‖ ^ 2 / u := hfin

/-! ### Integrability of the two Euler–Lagrange densities -/

/-- **The flux is globally `L²`**: `‖homogeneousFlux 2 (∇Ψ) u ξ‖ ≤ C ‖ξ‖` uniformly in `u ≥ 0`,
and `∇φ ∈ L²`. -/
theorem memLp_flux_two (hΨ : IsRegProfile Ψ) {φ : Euc d → ℝ} (hφc : Continuous φ)
    (hφnn : ∀ x, 0 ≤ φ x) (hφW : MemW0 2 K φ) :
    MemLp (fun x => Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x))
      (ENNReal.ofReal (2 : ℝ)) volume := by
  obtain ⟨c, C, hCΨ⟩ := hΨ.exists_isRegProfileWith
  have hmwg : AEStronglyMeasurable (weakGrad φ) volume := hφW.memLp_weakGrad.aestronglyMeasurable
  have hmξ : AEStronglyMeasurable (fun x => (φ x)⁻¹ • weakGrad φ x) volume :=
    (hφc.measurable.inv.aestronglyMeasurable).smul hmwg
  have hmΦ : AEStronglyMeasurable
      (fun x => Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x)) volume := by
    refine AEStronglyMeasurable.congr (f := fun x => φ x • gradient Ψ ((φ x)⁻¹ • weakGrad φ x))
      (hφc.aestronglyMeasurable.smul
        (hΨ.contDiff_gradient.continuous.comp_aestronglyMeasurable hmξ)) ?_
    exact Eventually.of_forall fun x => (log_homogeneousFlux_two (gradient Ψ) (φ x) _).symm
  refine (hφW.memLp_weakGrad.const_smul C).mono hmΦ (Eventually.of_forall fun x => ?_)
  show ‖Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x)‖ ≤ ‖(C • weakGrad φ) x‖
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hCΨ.C_nonneg]
  exact norm_homogeneousFlux_two_le hCΨ (hφnn x) _

/-- The zeroth-order Euler–Lagrange density is measurable. -/
theorem aestronglyMeasurable_valueDerivative_add_entropy (hΨ : IsRegProfile Ψ) {φ : Euc d → ℝ}
    (hφc : Continuous φ) (hφW : MemW0 2 K φ) :
    AEStronglyMeasurable (fun x =>
      Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
        deriv (Korevaar.entropyPotential 2 κ) (φ x)) volume := by
  have hmwg : AEStronglyMeasurable (weakGrad φ) volume := hφW.memLp_weakGrad.aestronglyMeasurable
  have hmξ : AEStronglyMeasurable (fun x => (φ x)⁻¹ • weakGrad φ x) volume :=
    (hφc.measurable.inv.aestronglyMeasurable).smul hmwg
  refine AEStronglyMeasurable.congr
    (f := fun x => φ x * (2 * Ψ ((φ x)⁻¹ • weakGrad φ x) -
      ⟪gradient Ψ ((φ x)⁻¹ • weakGrad φ x), (φ x)⁻¹ • weakGrad φ x⟫) +
      deriv (Korevaar.entropyPotential 2 κ) (φ x)) ?_ ?_
  · refine AEStronglyMeasurable.add ?_ ?_
    · refine hφc.aestronglyMeasurable.mul (AEStronglyMeasurable.sub ?_ ?_)
      · exact aestronglyMeasurable_const.mul
          (hΨ.contDiff.continuous.comp_aestronglyMeasurable hmξ)
      · exact (hΨ.contDiff_gradient.continuous.comp_aestronglyMeasurable hmξ).inner hmξ
    · exact ((measurable_deriv _).comp hφc.measurable).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    show φ x * (2 * Ψ ((φ x)⁻¹ • weakGrad φ x) -
        ⟪gradient Ψ ((φ x)⁻¹ • weakGrad φ x), (φ x)⁻¹ • weakGrad φ x⟫) +
        deriv (Korevaar.entropyPotential 2 κ) (φ x) =
      Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
        deriv (Korevaar.entropyPotential 2 κ) (φ x)
    rw [log_homogeneousValueDerivative_two]

/-- **The zeroth-order density is `L¹` on compact subsets of `K`.**  Its natural growth is
`2 C ‖∇φ‖²/φ`, which is integrable once `φ` is bounded below — that is, on a compact subset of
the open set `K`, where `φ` is continuous and positive. -/
theorem integrableOn_valueDerivative_add_entropy (hΨ : IsRegProfile Ψ) {φ : Euc d → ℝ}
    (hφc : Continuous φ) (hφpos : ∀ x ∈ K, 0 < φ x) (hφW : MemW0 2 K φ)
    {S : Set (Euc d)} (hS : IsCompact S) (hSK : S ⊆ K) :
    IntegrableOn (fun x =>
      Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
        deriv (Korevaar.entropyPotential 2 κ) (φ x)) S volume := by
  obtain ⟨c, C, hCΨ⟩ := hΨ.exists_isRegProfileWith
  have hmwg : AEStronglyMeasurable (weakGrad φ) volume := hφW.memLp_weakGrad.aestronglyMeasurable
  have hmF := aestronglyMeasurable_valueDerivative_add_entropy (κ := κ) hΨ hφc hφW
  rcases Set.eq_empty_or_nonempty S with he | hne
  · rw [he]
    exact integrableOn_empty
  obtain ⟨x₁, hx₁, hmin⟩ := hS.exists_isMinOn hne hφc.continuousOn
  have hδ : 0 < φ x₁ := hφpos x₁ (hSK hx₁)
  have hAcont : ContinuousOn (fun x => 2 * φ x * |Ψ 0| +
      |φ x| * (|κ| * |Real.log (φ x)| + |κ| / 2)) S := by
    have hlog : ContinuousOn (fun x => Real.log (φ x)) S := fun x hx =>
      ((Real.continuousAt_log (hφpos x (hSK hx)).ne').comp hφc.continuousAt).continuousWithinAt
    exact ((continuousOn_const.mul hφc.continuousOn).mul continuousOn_const).add
      (hφc.continuousOn.abs.mul ((continuousOn_const.mul hlog.abs).add continuousOn_const))
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn hAcont
  have hwg2 : Integrable (fun x => ‖weakGrad φ x‖ ^ 2) volume := by
    have h := hφW.memLp_weakGrad
    rw [ofReal_two'] at h
    exact (memLp_two_iff_integrable_sq_norm hmwg).1 h
  have hFbd : ∀ x ∈ S,
      |Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
        deriv (Korevaar.entropyPotential 2 κ) (φ x)| ≤
      A + 2 * C / φ x₁ * ‖weakGrad φ x‖ ^ 2 := by
    intro x hx
    have hxpos : 0 < φ x := hφpos x (hSK hx)
    have hxge : φ x₁ ≤ φ x := hmin hx
    have h1 := abs_homogeneousValueDerivative_two_le hCΨ hxpos (weakGrad φ x)
    have h2 : deriv (Korevaar.entropyPotential 2 κ) (φ x) =
        φ x * (κ * Real.log (φ x) + κ / 2) := log_deriv_entropyPotential_two hxpos
    have h3 : |φ x * (κ * Real.log (φ x) + κ / 2)| ≤
        |φ x| * (|κ| * |Real.log (φ x)| + |κ| / 2) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have ha := le_abs_self (κ * Real.log (φ x))
      have hb := neg_abs_le (κ * Real.log (φ x))
      have hc := le_abs_self (κ / 2)
      have hd := neg_abs_le (κ / 2)
      have he : |κ * Real.log (φ x)| = |κ| * |Real.log (φ x)| := abs_mul _ _
      have hf : |κ / 2| = |κ| / 2 := by rw [abs_div]; norm_num
      rw [abs_le]
      constructor <;> linarith
    have hAx : 2 * φ x * |Ψ 0| + |φ x| * (|κ| * |Real.log (φ x)| + |κ| / 2) ≤ A := by
      have hb := hA x hx
      rw [Real.norm_eq_abs] at hb
      exact (le_abs_self _).trans hb
    have hquot : 2 * C * ‖weakGrad φ x‖ ^ 2 / φ x ≤ 2 * C / φ x₁ * ‖weakGrad φ x‖ ^ 2 := by
      have hCn : 0 ≤ 2 * C * ‖weakGrad φ x‖ ^ 2 := by
        have := hCΨ.C_nonneg
        positivity
      have hinv : (φ x)⁻¹ ≤ (φ x₁)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hδ hxge
      rw [div_eq_mul_inv]
      calc 2 * C * ‖weakGrad φ x‖ ^ 2 * (φ x)⁻¹
          ≤ 2 * C * ‖weakGrad φ x‖ ^ 2 * (φ x₁)⁻¹ := mul_le_mul_of_nonneg_left hinv hCn
        _ = 2 * C / φ x₁ * ‖weakGrad φ x‖ ^ 2 := by field_simp; try ring
    rw [h2]
    have h5 := le_abs_self (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x)
      (weakGrad φ x))
    have h6 := neg_abs_le (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x)
      (weakGrad φ x))
    have h7 := le_abs_self (φ x * (κ * Real.log (φ x) + κ / 2))
    have h8 := neg_abs_le (φ x * (κ * Real.log (φ x) + κ / 2))
    rw [abs_le]
    constructor <;> linarith
  have hdom : IntegrableOn (fun x => A + 2 * C / φ x₁ * ‖weakGrad φ x‖ ^ 2) S volume :=
    (integrableOn_const hS.measure_lt_top.ne).add ((hwg2.restrict).const_mul _)
  refine Integrable.mono' hdom hmF.restrict ?_
  filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
  rw [Real.norm_eq_abs]
  exact hFbd x hx

/-! ### The weak Euler–Lagrange equation against bounded `W₀^{1,2}` test functions -/

/-- **The Euler–Lagrange equation for bounded Sobolev test functions.**  The frozen statement
`IsRegMinimizer.weak_euler_lagrange` quantifies over *smooth* test functions; the substitution
`χ = ψ / φ` of link 1 is not smooth (`φ` is only continuous), so the equation has to be upgraded
first.

The upgrade is the argument of link 3 (`IsWeakLogSol.weakEq_memW0`) run on the
Euler–Lagrange functional: the flux `homogeneousFlux 2 (∇Ψ) φ ∇φ` is globally `L²` (it is
bounded by `C ‖∇φ‖`), while the zeroth-order density
`homogeneousValueDerivative + (entropyPotential)'` is only `L¹` near `Ω` — its natural growth is
`2C‖∇φ‖²/φ` — so the approximating test functions must be uniformly bounded.  That is
`exists_contDiff_tendsto_eLpNorm_bounded`; the flux term passes to the limit by `L²`–`L²`
duality and the zeroth-order term by dominated convergence along an a.e.-convergent
subsequence. -/
theorem weakEL_memW0 (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hφpos : ∀ x ∈ K, 0 < φ x)
    (hφmin : IsRegMinimizer 2 κ Ψ K φ)
    {Ω : Set (Euc d)} (hΩ : IsOpen Ω) (hcl : IsCompact (closure Ω))
    (hclK : closure Ω ⊆ K) {T : Set (Euc d)} (hT : IsCompact T) (hTΩ : T ⊆ Ω)
    {χ : Euc d → ℝ} (hχ : MemW0 2 T χ) {Mχ : ℝ} (hχb : ∀ x, |χ x| ≤ Mχ) :
    (∫ x, ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x), weakGrad χ x⟫) +
      (∫ x, (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
            deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x) =
        (2 * regMin 2 κ Ψ K + κ / 2) * ∫ x, φ x * χ x := by
  obtain ⟨c, C, hCΨ⟩ := hΨ.exists_isRegProfileWith
  have hφnn : ∀ x, 0 ≤ φ x := hφmin.nonneg
  have hmwg : AEStronglyMeasurable (weakGrad φ) volume :=
    hφmin.memW0.memLp_weakGrad.aestronglyMeasurable
  have hmξ : AEStronglyMeasurable (fun x => (φ x)⁻¹ • weakGrad φ x) volume :=
    (hφc.measurable.inv.aestronglyMeasurable).smul hmwg
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Euc d → Euc d,
      ∀ x, Φ x = Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : Euc d → ℝ, ∀ x, F x =
      Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
        deriv (Korevaar.entropyPotential 2 κ) (φ x) := ⟨_, fun _ => rfl⟩
  simp only [← hΦdef, ← hFdef]
  -- ### the flux is globally `L²`, the zeroth-order density `L¹` near `Ω`
  have hΦ2 : MemLp Φ (ENNReal.ofReal (2 : ℝ)) volume :=
    (memLp_flux_two hΨ hφc hφnn hφmin.memW0).ae_eq
      (Eventually.of_forall fun x => (hΦdef x).symm)
  have hmF : AEStronglyMeasurable F volume :=
    (aestronglyMeasurable_valueDerivative_add_entropy (κ := κ) hΨ hφc hφmin.memW0).congr
      (Eventually.of_forall fun x => (hFdef x).symm)
  have hF1 : IntegrableOn F (closure Ω) volume :=
    (integrableOn_valueDerivative_add_entropy hΨ hφc hφpos hφmin.memW0 hcl hclK).congr
      (Eventually.of_forall fun x => (hFdef x).symm)
  -- ### the approximating sequence
  obtain ⟨u, hcd, hcs, hts, hub, hu, hgr⟩ :=
    hχ.exists_contDiff_tendsto_eLpNorm_bounded one_lt_two hΩ hT hTΩ hχb
  have hu1 : ∀ n, ContDiff ℝ 1 (u n) := fun n => (hcd n).of_le (by simp)
  have hgrn : ∀ n, MemLp (gradient (u n)) (ENNReal.ofReal (2 : ℝ)) volume := fun n =>
    (continuous_gradient (hu1 n)).memLp_of_hasCompactSupport (hasCompactSupport_gradient (hcs n))
  have hun : ∀ n, MemLp (u n) (ENNReal.ofReal (2 : ℝ)) volume := fun n =>
    (hcd n).continuous.memLp_of_hasCompactSupport (hcs n)
  have hEL : ∀ n, (∫ x, ⟪Φ x, gradient (u n) x⟫) + (∫ x, F x * u n x) =
      (2 * regMin 2 κ Ψ K + κ / 2) * ∫ x, φ x * u n x := by
    intro n
    by_cases hz : u n = 0
    · have h0 : ∀ x, u n x = 0 := fun x => by rw [hz]; rfl
      have hg0 : ∀ x, gradient (u n) x = 0 := by
        intro x
        have he : u n = fun _ => (0 : ℝ) := by funext y; exact h0 y
        rw [he]
        exact (hasGradientAt_const (x := x) (c := (0 : ℝ))).gradient
      simp [h0, hg0]
    · have hTF : IsTestFn K (u n) :=
        ⟨hcd n, hcs n, (hts n).trans (subset_closure.trans hclK), hz⟩
      have h := hφmin.weak_euler_lagrange hκ hΨ hK hφc hφpos hTF
      simpa only [← hΦdef, ← hFdef] using h
  -- ### the limits
  have hΦ' : MemLp Φ (ENNReal.ofReal (Real.conjExponent (2 : ℝ))) volume := by
    rw [ofReal_conjExponent_two]
    rwa [ofReal_two'] at hΦ2
  have hφ' : MemLp φ (ENNReal.ofReal (Real.conjExponent (2 : ℝ))) volume := by
    rw [ofReal_conjExponent_two]
    have h := hφmin.memW0.memLp
    rwa [ofReal_two'] at h
  have hAlim : Tendsto (fun n => ∫ x, ⟪Φ x, gradient (u n) x⟫) atTop
      (𝓝 (∫ x, ⟪Φ x, weakGrad χ x⟫)) :=
    Komlos.Literature.tendsto_integral_inner_of_tendsto_eLpNorm one_lt_two hΦ' hgrn
      hχ.memLp_weakGrad hgr
  have hClim : Tendsto (fun n => ∫ x, φ x * u n x) atTop (𝓝 (∫ x, φ x * χ x)) :=
    Komlos.Literature.tendsto_integral_mul_of_tendsto_eLpNorm one_lt_two hφ' hun hχ.memLp hu
  have hmu : ∀ n, AEStronglyMeasurable (u n) volume := fun n =>
    (hcd n).continuous.aestronglyMeasurable
  have htim : TendstoInMeasure volume u atTop χ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by simp) hmu hχ.memLp.aestronglyMeasurable hu
  obtain ⟨ns, hns, hae⟩ := htim.exists_seq_tendsto_ae
  have hMχ0 : 0 ≤ Mχ := (abs_nonneg (χ 0)).trans (hχb 0)
  obtain ⟨bnd, hbnddef⟩ : ∃ b : Euc d → ℝ,
      b = (closure Ω).indicator fun x => Mχ * |F x| := ⟨_, rfl⟩
  have hbndint : Integrable bnd volume := by
    rw [hbnddef, integrable_indicator_iff hcl.isClosed.measurableSet]
    exact (hF1.abs).const_mul Mχ
  have hbnd0 : ∀ x, 0 ≤ bnd x := by
    intro x
    rw [hbnddef]
    by_cases hx : x ∈ closure Ω
    · rw [Set.indicator_of_mem hx]; positivity
    · rw [Set.indicator_of_notMem hx]
  have hdom : ∀ n, ∀ᵐ x ∂volume, ‖F x * u n x‖ ≤ bnd x := by
    intro n
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x ∈ Ω
    · have hx' : x ∈ closure Ω := subset_closure hx
      rw [hbnddef, Set.indicator_of_mem hx', mul_comm Mχ]
      exact mul_le_mul_of_nonneg_left (hub n x) (abs_nonneg _)
    · have hx' : x ∉ tsupport (u n) := fun h => hx (hts n h)
      rw [image_eq_zero_of_notMem_tsupport hx', abs_zero, mul_zero]
      exact hbnd0 x
  have hBlim : Tendsto (fun k => ∫ x, F x * u (ns k) x) atTop (𝓝 (∫ x, F x * χ x)) := by
    refine tendsto_integral_of_dominated_convergence bnd
      (fun k => hmF.mul (hmu (ns k))) hbndint (fun k => hdom (ns k)) ?_
    filter_upwards [hae] with x hx
    exact hx.const_mul _
  have hfin : Tendsto (fun k => (2 * regMin 2 κ Ψ K + κ / 2) * ∫ x, φ x * u (ns k) x) atTop
      (𝓝 ((∫ x, ⟪Φ x, weakGrad χ x⟫) + ∫ x, F x * χ x)) :=
    ((hAlim.comp hns.tendsto_atTop).add hBlim).congr fun k => hEL (ns k)
  exact tendsto_nhds_unique hfin
    ((hClim.comp hns.tendsto_atTop).const_mul (2 * regMin 2 κ Ψ K + κ / 2))

/-! ### The two analytic inputs -/

/-- **The chain rule for `v = -log φ`.**  On the open set `K`, where the continuous `φ` is
positive, `v` has the local weak gradient `-φ⁻¹ ∇φ`.

`g` is any measurable representative of `weakGrad φ`; the statement is insensitive to the choice
because both sides of the integration-by-parts identity only see the a.e.-class. -/

theorem hasWeakGradientOn_neg_log (hK : IsGoodConvex K) {φ : Euc d → ℝ} (hφc : Continuous φ)
    (hφpos : ∀ x ∈ K, 0 < φ x) (hφW : MemW0 2 K φ) {g : Euc d → Euc d}
    (hg : weakGrad φ =ᵐ[volume] g) :
    HasWeakGradientOn K (fun x => -Real.log (φ x)) (fun x => -((φ x)⁻¹ • g x)) := by
  refine ⟨fun ψ hψ hψs hψK e => ?_⟩
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  rcases eq_empty_or_nonempty (tsupport ψ) with he | hne
  · have hψ0 : ψ = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (by rw [he]; exact Set.notMem_empty x)
    simp [hψ0]
  -- `φ` is bounded below on `tsupport ψ`
  obtain ⟨x₁, hx₁, hmin⟩ := hψs.isCompact.exists_isMinOn hne hφc.continuousOn
  have hδ : 0 < φ x₁ := hφpos x₁ (hψK hx₁)
  have hφx : ∀ x ∈ tsupport ψ, φ x₁ ≤ φ x := fun x hx => hmin hx
  -- the profile
  obtain ⟨L, c, hLC, hL0, hLb, hLval, hLdv⟩ := exists_log_profile hδ
  obtain ⟨hLW, hLg⟩ := Komlos.Literature.memW0_comp one_lt_two hφW hLC hL0 hLb
  have key := hLW.hasWeakGradient.integral_mul_fderiv ψ hψ hψs e
  -- basic continuity facts
  have hDψ : Continuous fun x => fderiv ℝ ψ x e :=
    (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDψ0 : ∀ x, x ∉ tsupport ψ → fderiv ℝ ψ x e = 0 := fun x hx => by
    rw [fderiv_apply_eq_inner_gradient, gradient_eq_zero_of_notMem_tsupport hx, inner_zero_left]
  have hDψs : HasCompactSupport fun x => fderiv ℝ ψ x e :=
    Komlos.Literature.Korevaar.hasCompactSupport_of_zero_outside hψs hDψ0
  have hlogc : ContinuousOn (fun x => -Real.log (φ x)) K := continuousOn_neg_log hφc hφpos
  have hi1 : Integrable fun x => -Real.log (φ x) * fderiv ℝ ψ x e := by
    refine (Komlos.Literature.Korevaar.continuous_mul_of_continuousOn hK.isOpen hlogc hDψ
      (isClosed_tsupport ψ) hψK hDψ0).integrable_of_hasCompactSupport ?_
    exact Komlos.Literature.Korevaar.hasCompactSupport_of_zero_outside hψs fun x hx => by
      rw [hDψ0 x hx, mul_zero]
  have hi2 : Integrable fun x => c * fderiv ℝ ψ x e :=
    (hDψ.const_mul c).integrable_of_hasCompactSupport hDψs.mul_left
  -- the left-hand side
  have eLa : (∫ x, L (φ x) * fderiv ℝ ψ x e) =
      ∫ x, (-Real.log (φ x) * fderiv ℝ ψ x e + c * fderiv ℝ ψ x e) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show L (φ x) * fderiv ℝ ψ x e =
      -Real.log (φ x) * fderiv ℝ ψ x e + c * fderiv ℝ ψ x e
    by_cases hx : x ∈ tsupport ψ
    · rw [hLval (φ x) (hφx x hx)]; ring
    · rw [hDψ0 x hx, mul_zero, mul_zero, mul_zero, add_zero]
  have eLb : (∫ x, (-Real.log (φ x) * fderiv ℝ ψ x e + c * fderiv ℝ ψ x e)) =
      (∫ x, -Real.log (φ x) * fderiv ℝ ψ x e) + ∫ x, c * fderiv ℝ ψ x e :=
    integral_add hi1 hi2
  have eLc : (∫ x, c * fderiv ℝ ψ x e) = 0 := by
    rw [integral_const_mul, integral_fderiv_apply_eq_zero hψ1 hψs e, mul_zero]
  -- the right-hand side
  have eR : (∫ x, ⟪weakGrad (fun z => L (φ z)) x, e⟫ * ψ x) =
      ∫ x, ⟪-((φ x)⁻¹ • g x), e⟫ * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [hLg, hg] with x h1 h2
    show ⟪weakGrad (fun z => L (φ z)) x, e⟫ * ψ x = ⟪-((φ x)⁻¹ • g x), e⟫ * ψ x
    by_cases hx : x ∈ tsupport ψ
    · rw [h1, h2, hLdv (φ x) (hφx x hx), neg_smul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  show (∫ x, -Real.log (φ x) * fderiv ℝ ψ x e) = -∫ x, ⟪-((φ x)⁻¹ • g x), e⟫ * ψ x
  rw [← eR, ← key, eLa, eLb, eLc, add_zero]

/-- **The weak equation for `v = -log φ`, tested against `ψ ∈ C_c^∞(K)`.**  This is the
substitution `χ = ψ / φ` in `IsRegMinimizer.weak_euler_lagrange`, whose *algebra* is
`euler_lagrange_substitution` above; what is missing is only the approximation legitimising the
non-smooth test function `χ`. -/
-- TODO(reg/c2a): approximate `χ = ψ/φ` by `χ_n = ψ / mollifyWith ρ_n φ ∈ IsTestFn K`
-- (`φ ≥ δ > 0` on a ball containing `tsupport ψ`, so `mollifyWith ρ_n φ ≥ δ/2` for large `n` by
-- uniform convergence on compacts); `∇χ_n → u⁻¹ ∇ψ + (ψ u⁻¹) ∇v` in `L²` by
-- `Komlos.Literature.gradient_mollifyWith`, the flux is `L²` and the value-derivative term `L¹`
-- on that ball, so `IsRegMinimizer.weak_euler_lagrange hκ hΨ hK hφmin hφc hφpos` passes to the
-- limit; then apply `euler_lagrange_substitution` pointwise and integrate.
theorem weakEq_neg_log (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hφ0 : ∀ x, x ∉ K → φ x = 0)
    (hφpos : ∀ x ∈ K, 0 < φ x) (hφmin : IsRegMinimizer 2 κ Ψ K φ)
    {g : Euc d → Euc d} (hg : weakGrad φ =ᵐ[volume] g)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (hψK : tsupport ψ ⊆ K) :
    (∫ x, ⟪gradient Ψ (-((φ x)⁻¹ • g x)), gradient ψ x⟫) =
      -∫ x, regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
        (fun z => -((φ z)⁻¹ • g z)) x * ψ x := by
  obtain ⟨c, C, hCΨ⟩ := hΨ.exists_isRegProfileWith
  have hC0 : 0 ≤ C := hCΨ.C_nonneg
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hφnn : ∀ x, 0 ≤ φ x := hφmin.nonneg
  rcases Set.eq_empty_or_nonempty (tsupport ψ) with he | hTne
  · have hψ0 : ∀ x, ψ x = 0 := fun x =>
      image_eq_zero_of_notMem_tsupport (by rw [he]; exact Set.notMem_empty x)
    have hgz : ∀ x, gradient ψ x = 0 := fun x =>
      gradient_eq_zero_of_notMem_tsupport (by rw [he]; exact Set.notMem_empty x)
    simp [hψ0, hgz]
  have hT : IsCompact (tsupport ψ) := hψs
  -- ### a compact neighbourhood of `tsupport ψ` inside `K`
  obtain ⟨ε, hε, hεK⟩ := hT.exists_cthickening_subset_open hK.isOpen hψK
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set (Euc d), Ω = Metric.thickening ε (tsupport ψ) := ⟨_, rfl⟩
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact Metric.isOpen_thickening
  have hTΩ : tsupport ψ ⊆ Ω := by rw [hΩdef]; exact Metric.self_subset_thickening hε _
  have hclsub : closure Ω ⊆ Metric.cthickening ε (tsupport ψ) := by
    rw [hΩdef]
    exact closure_minimal (Metric.thickening_subset_cthickening ε (tsupport ψ))
      Metric.isClosed_cthickening
  have hcl : IsCompact (closure Ω) :=
    hT.cthickening.of_isClosed_subset isClosed_closure hclsub
  have hclK : closure Ω ⊆ K := hclsub.trans hεK
  -- ### `φ` is bounded below on `tsupport ψ`
  obtain ⟨x₁, hx₁, hmin⟩ := hT.exists_isMinOn hTne hφc.continuousOn
  have hδ : 0 < φ x₁ := hφpos x₁ (hψK hx₁)
  -- ### the test function `χ = ψ (P ∘ φ - c_P)`, equal to `ψ/φ` on `tsupport ψ`
  obtain ⟨P, cP, hPC, hP0, hPb, hPval, hPdv⟩ := exists_inv_profile hδ
  obtain ⟨hPW, hPg⟩ := Komlos.Literature.memW0_comp one_lt_two hφmin.memW0 hPC hP0 hPb
  obtain ⟨Mψ, hMψ⟩ := hψ.continuous.bounded_above_of_compact_support hψs
  obtain ⟨Bψ, hBψ⟩ := (continuous_gradient hψ1).bounded_above_of_compact_support
    (hasCompactSupport_gradient hψs)
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
  have hBψ0 : 0 ≤ Bψ := (norm_nonneg _).trans (hBψ 0)
  obtain ⟨hχ1, hχ1g⟩ := hPW.contDiff_mul hψ (A := Mψ) (B := Bψ)
    (fun x => by rw [← Real.norm_eq_abs]; exact hMψ x) hBψ
  have hψW : MemW0 2 K ψ := Komlos.Literature.memW0_of_contDiff hψ1 hψs hψK 2
  have hcW : MemW0 2 K ((-cP) • ψ) := hψW.smul (-cP)
  have hcg : weakGrad ((-cP) • ψ) =ᵐ[volume] fun x => (-cP) • gradient ψ x :=
    ((Komlos.Literature.hasWeakGradient_gradient hψ1 hψs).smul (-cP)).weakGrad_ae_eq
  obtain ⟨χ, hχdef⟩ : ∃ χ : Euc d → ℝ, ∀ x, χ x = ψ x * P (φ x) + (-cP) * ψ x :=
    ⟨_, fun _ => rfl⟩
  have hχeq : ((fun x => ψ x * P (φ x)) + ((-cP) • ψ)) = χ := by
    funext x
    rw [hχdef x]
    rfl
  have hχW : MemW0 2 K χ := hχeq ▸ (hχ1.add hcW)
  have hχgrad : weakGrad χ =ᵐ[volume]
      fun x => ψ x • (deriv P (φ x) • g x) + (P (φ x) - cP) • gradient ψ x := by
    have hsum : weakGrad χ =ᵐ[volume]
        weakGrad (fun x => ψ x * P (φ x)) + weakGrad ((-cP) • ψ) := by
      rw [← hχeq]
      exact (hχ1.hasWeakGradient.add hcW.hasWeakGradient).weakGrad_ae_eq
    filter_upwards [hsum, hχ1g, hcg, hPg, hg] with x h1 h2 h3 h4 h5
    show weakGrad χ x = ψ x • (deriv P (φ x) • g x) + (P (φ x) - cP) • gradient ψ x
    rw [h1]
    simp only [Pi.add_apply]
    rw [h2, h3, h4, h5]
    module
  have hχ0 : ∀ x, x ∉ tsupport ψ → χ x = 0 := fun x hx => by
    rw [hχdef x, image_eq_zero_of_notMem_tsupport hx]
    ring
  have hχT : MemW0 2 (tsupport ψ) χ :=
    ⟨hχW.memLp, Eventually.of_forall hχ0, hχW.exists_weakGradient⟩
  -- the sup bound for `χ`
  have hKc : IsCompact (closure K) := hK.isBounded.isCompact_closure
  have hφs : HasCompactSupport φ :=
    Komlos.Literature.Korevaar.hasCompactSupport_of_zero_outside hKc
      (fun x hx => hφ0 x fun h => hx (subset_closure h))
  obtain ⟨Mφ, hMφ⟩ := hφc.bounded_above_of_compact_support hφs
  obtain ⟨MP, hMP⟩ := (isCompact_Icc (a := -Mφ) (b := Mφ)).exists_bound_of_continuousOn
    hPC.continuous.continuousOn
  have hχb : ∀ x, |χ x| ≤ Mψ * (MP + |cP|) := by
    intro x
    have heq : χ x = ψ x * (P (φ x) - cP) := by rw [hχdef x]; ring
    have hin : φ x ∈ Set.Icc (-Mφ) Mφ := by
      have hb := hMφ x
      rw [Real.norm_eq_abs, abs_le] at hb
      exact ⟨hb.1, hb.2⟩
    have hPx : |P (φ x)| ≤ MP := by
      have hb := hMP _ hin
      rwa [Real.norm_eq_abs] at hb
    have hψx : |ψ x| ≤ Mψ := by rw [← Real.norm_eq_abs]; exact hMψ x
    have h1 : |P (φ x) - cP| ≤ MP + |cP| := by
      have ha := le_abs_self (P (φ x))
      have hb := neg_abs_le (P (φ x))
      have hcc := le_abs_self cP
      have hd := neg_abs_le cP
      rw [abs_le]
      constructor <;> linarith
    rw [heq, abs_mul]
    exact mul_le_mul hψx h1 (abs_nonneg _) hMψ0
  -- ### the Euler–Lagrange equation for `χ`
  have hEL := weakEL_memW0 hκ hΨ hK hφc hφpos hφmin hΩopen hcl hclK hT hTΩ hχT hχb
  -- ### the pointwise identity
  have hpt : ∀ᵐ x ∂volume,
      (⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x), weakGrad χ x⟫ +
        (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
          deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x -
        (2 * regMin 2 κ Ψ K + κ / 2) * (φ x * χ x)) =
      -(⟪gradient Ψ (-((φ x)⁻¹ • g x)), gradient ψ x⟫ +
        regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
          (fun z => -((φ z)⁻¹ • g z)) x * ψ x) := by
    filter_upwards [hg, hχgrad] with x hgx hχgx
    by_cases hx : x ∈ tsupport ψ
    · have hφx : 0 < φ x := hφpos x (hψK hx)
      have hφge : φ x₁ ≤ φ x := hmin hx
      have hPv : P (φ x) = (φ x)⁻¹ + cP := hPval (φ x) hφge
      have hPd : deriv P (φ x) = -((φ x) ^ 2)⁻¹ := hPdv (φ x) hφge
      have hflux : weakGrad φ x = -(φ x • -((φ x)⁻¹ • g x)) := by
        rw [hgx, smul_neg, smul_smul, mul_inv_cancel₀ hφx.ne', one_smul, neg_neg]
      have hχv : χ x = ψ x * (φ x)⁻¹ := by rw [hχdef x, hPv]; ring
      have hχg : weakGrad χ x =
          (φ x)⁻¹ • gradient ψ x + (ψ x * (φ x)⁻¹) • (-((φ x)⁻¹ • g x)) := by
        rw [hχgx, hPv, hPd, show ((φ x) ^ 2)⁻¹ = (φ x)⁻¹ * (φ x)⁻¹ from by rw [sq, mul_inv]]
        module
      rw [hflux, hχv, hχg]
      simp only [regLogRhs]
      exact euler_lagrange_substitution (κ := κ) (m := regMin 2 κ Ψ K) (ψ := ψ x) hΨ hφx
        (-((φ x)⁻¹ • g x)) (gradient ψ x)
    · have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hgψx : gradient ψ x = 0 := gradient_eq_zero_of_notMem_tsupport hx
      have hχx : χ x = 0 := hχ0 x hx
      have hχgx0 : weakGrad χ x = 0 := by rw [hχgx, hψx, hgψx]; simp
      rw [hχx, hχgx0, hψx, hgψx]
      simp
  -- ### integrability
  have hmg : AEStronglyMeasurable g volume :=
    hφmin.memW0.memLp_weakGrad.aestronglyMeasurable.congr hg
  have hgL2 : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := hφmin.memW0.memLp_weakGrad.ae_eq hg
  have hgsq : Integrable (fun x => ‖g x‖ ^ 2) volume := by
    have h := hgL2
    rw [ofReal_two'] at h
    exact (memLp_two_iff_integrable_sq_norm hmg).1 h
  have hΦ' : MemLp (fun x => Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x))
      (ENNReal.ofReal (Real.conjExponent (2 : ℝ))) volume := by
    rw [ofReal_conjExponent_two]
    have h := memLp_flux_two hΨ hφc hφnn hφmin.memW0
    rwa [ofReal_two'] at h
  have hφ' : MemLp φ (ENNReal.ofReal (Real.conjExponent (2 : ℝ))) volume := by
    rw [ofReal_conjExponent_two]
    have h := hφmin.memW0.memLp
    rwa [ofReal_two'] at h
  have hint_a : Integrable (fun x =>
      ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x), weakGrad χ x⟫) volume :=
    Komlos.Literature.integrable_inner_of_memLp one_lt_two hΦ' hχT.memLp_weakGrad
  have hint_c : Integrable (fun x => (2 * regMin 2 κ Ψ K + κ / 2) * (φ x * χ x)) volume :=
    (Komlos.Literature.integrable_mul_of_memLp one_lt_two hφ' hχT.memLp).const_mul _
  have hF1 := integrableOn_valueDerivative_add_entropy (κ := κ) hΨ hφc hφpos hφmin.memW0 hcl hclK
  have hmF := aestronglyMeasurable_valueDerivative_add_entropy (κ := κ) hΨ hφc hφmin.memW0
  have hint_b : Integrable (fun x =>
      (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
        deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x) volume := by
    refine integrable_of_bound_on_set (S := closure Ω) hcl.isClosed.measurableSet
      (hmF.mul hχT.memLp.aestronglyMeasurable)
      (b := fun x => Mψ * (MP + |cP|) *
        |Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
          deriv (Korevaar.entropyPotential 2 κ) (φ x)|)
      ((hF1.abs).const_mul _) ?_ ?_
    · intro x _
      rw [Real.norm_eq_abs, abs_mul]
      calc |Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
              deriv (Korevaar.entropyPotential 2 κ) (φ x)| * |χ x|
          ≤ |Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
              deriv (Korevaar.entropyPotential 2 κ) (φ x)| * (Mψ * (MP + |cP|)) :=
            mul_le_mul_of_nonneg_left (hχb x) (abs_nonneg _)
        _ = Mψ * (MP + |cP|) *
              |Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
                deriv (Korevaar.entropyPotential 2 κ) (φ x)| := by ring
    · intro x hx
      rw [hχ0 x fun h => hx (subset_closure (hTΩ h)), mul_zero]
  have hgL1 : IntegrableOn g (tsupport ψ) volume := by
    have hdom : IntegrableOn (fun x => 2⁻¹ * (‖g x‖ ^ 2 + 1)) (tsupport ψ) volume :=
      ((hgsq.restrict).add (integrableOn_const hT.measure_lt_top.ne)).const_mul _
    refine Integrable.mono' hdom hmg.restrict (Eventually.of_forall fun x => ?_)
    nlinarith [sq_nonneg (‖g x‖ - 1), norm_nonneg (g x)]
  have hmG : AEStronglyMeasurable (fun x => -((φ x)⁻¹ • g x)) volume :=
    ((hφc.measurable.inv.aestronglyMeasurable).smul hmg).neg
  have hint_t1 : Integrable (fun x =>
      ⟪gradient Ψ (-((φ x)⁻¹ • g x)), gradient ψ x⟫) volume := by
    refine integrable_of_bound_on_set (S := tsupport ψ) (isClosed_tsupport ψ).measurableSet
      ((hΨ.contDiff_gradient.continuous.comp_aestronglyMeasurable hmG).inner
        (continuous_gradient hψ1).aestronglyMeasurable)
      (b := fun x => C * (φ x₁)⁻¹ * Bψ * ‖g x‖) ((hgL1.norm).const_mul _) ?_ ?_
    · intro x hx
      have hφx : 0 < φ x := hφpos x (hψK hx)
      have hφge : φ x₁ ≤ φ x := hmin hx
      have h1 : ‖gradient Ψ (-((φ x)⁻¹ • g x))‖ ≤ C * ‖-((φ x)⁻¹ • g x)‖ :=
        hCΨ.norm_gradient_le _
      have h2 : ‖-((φ x)⁻¹ • g x)‖ = (φ x)⁻¹ * ‖g x‖ := by
        rw [norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hφx.le)]
      have h3 : (φ x)⁻¹ ≤ (φ x₁)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hδ hφge
      rw [Real.norm_eq_abs]
      calc |⟪gradient Ψ (-((φ x)⁻¹ • g x)), gradient ψ x⟫|
          ≤ ‖gradient Ψ (-((φ x)⁻¹ • g x))‖ * ‖gradient ψ x‖ := abs_real_inner_le_norm _ _
        _ ≤ (C * ((φ x)⁻¹ * ‖g x‖)) * Bψ := by
            refine mul_le_mul ?_ (hBψ x) (norm_nonneg _) ?_
            · rw [← h2]; exact h1
            · have hgn : (0:ℝ) ≤ ‖g x‖ := norm_nonneg _
              have : (0:ℝ) ≤ (φ x)⁻¹ := inv_nonneg.2 hφx.le
              positivity
        _ ≤ (C * ((φ x₁)⁻¹ * ‖g x‖)) * Bψ := by
            have hgn : (0:ℝ) ≤ ‖g x‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hgn) hC0) hBψ0
        _ = C * (φ x₁)⁻¹ * Bψ * ‖g x‖ := by ring
    · intro x hx
      rw [gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right]
  obtain ⟨A2, hA2⟩ := hT.exists_bound_of_continuousOn
    (f := fun x => κ * -Real.log (φ x) + 2 * regMin 2 κ Ψ K)
    ((continuousOn_const.mul (fun x hx =>
      (((Real.continuousAt_log (hφpos x (hψK hx)).ne').comp
        hφc.continuousAt).neg).continuousWithinAt)).add continuousOn_const)
  have hint_t2 : Integrable (fun x =>
      regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
        (fun z => -((φ z)⁻¹ • g z)) x * ψ x) volume := by
    refine integrable_of_bound_on_set (S := tsupport ψ) (isClosed_tsupport ψ).measurableSet
      ((((measurable_const.mul (Real.measurable_log.comp hφc.measurable).neg).add
        measurable_const).aestronglyMeasurable.add
        ((continuous_regNatGrowth hΨ).comp_aestronglyMeasurable hmG)).mul
        hψ.continuous.aestronglyMeasurable)
      (b := fun x => Mψ * (A2 + 2 * |Ψ 0| + 2 * C * ((φ x₁)⁻¹ * (φ x₁)⁻¹) * ‖g x‖ ^ 2))
      ?_ ?_ ?_
    · refine Integrable.const_mul ?_ Mψ
      exact (integrableOn_const hT.measure_lt_top.ne).add ((hgsq.restrict).const_mul _)
    · intro x hx
      have hφx : 0 < φ x := hφpos x (hψK hx)
      have hφge : φ x₁ ≤ φ x := hmin hx
      have h3 : (φ x)⁻¹ ≤ (φ x₁)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hδ hφge
      have hB := abs_regNatGrowth_le hCΨ (-((φ x)⁻¹ • g x))
      have h2 : ‖-((φ x)⁻¹ • g x)‖ = (φ x)⁻¹ * ‖g x‖ := by
        rw [norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hφx.le)]
      have hgn : (0:ℝ) ≤ ‖g x‖ := norm_nonneg _
      have hinvnn : (0:ℝ) ≤ (φ x)⁻¹ := inv_nonneg.2 hφx.le
      have hδinv : (0:ℝ) ≤ (φ x₁)⁻¹ := inv_nonneg.2 hδ.le
      have hBb : |regNatGrowth Ψ (-((φ x)⁻¹ • g x))| ≤
          2 * C * ((φ x₁)⁻¹ * (φ x₁)⁻¹) * ‖g x‖ ^ 2 + 2 * |Ψ 0| := by
        rw [h2] at hB
        have h4 : (φ x)⁻¹ * ‖g x‖ ≤ (φ x₁)⁻¹ * ‖g x‖ := mul_le_mul_of_nonneg_right h3 hgn
        have h5 : (0:ℝ) ≤ (φ x)⁻¹ * ‖g x‖ := mul_nonneg hinvnn hgn
        have hsq : ((φ x)⁻¹ * ‖g x‖) ^ 2 ≤ ((φ x₁)⁻¹ * (φ x₁)⁻¹) * ‖g x‖ ^ 2 := by
          nlinarith
        have h6 : 2 * C * ((φ x)⁻¹ * ‖g x‖) ^ 2 ≤
            2 * C * (((φ x₁)⁻¹ * (φ x₁)⁻¹) * ‖g x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by linarith)
        linarith
      have hA2x : |κ * -Real.log (φ x) + 2 * regMin 2 κ Ψ K| ≤ A2 := by
        have hb := hA2 x hx
        rwa [Real.norm_eq_abs] at hb
      have hψx : |ψ x| ≤ Mψ := by rw [← Real.norm_eq_abs]; exact hMψ x
      have hrhs : |regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
          (fun z => -((φ z)⁻¹ • g z)) x| ≤
          A2 + 2 * |Ψ 0| + 2 * C * ((φ x₁)⁻¹ * (φ x₁)⁻¹) * ‖g x‖ ^ 2 := by
        show |κ * -Real.log (φ x) + 2 * regMin 2 κ Ψ K +
          regNatGrowth Ψ (-((φ x)⁻¹ • g x))| ≤ _
        have ha := le_abs_self (κ * -Real.log (φ x) + 2 * regMin 2 κ Ψ K)
        have hb := neg_abs_le (κ * -Real.log (φ x) + 2 * regMin 2 κ Ψ K)
        have hcc := le_abs_self (regNatGrowth Ψ (-((φ x)⁻¹ • g x)))
        have hd := neg_abs_le (regNatGrowth Ψ (-((φ x)⁻¹ • g x)))
        rw [abs_le]
        constructor <;> linarith
      have hnn : (0:ℝ) ≤ A2 + 2 * |Ψ 0| + 2 * C * ((φ x₁)⁻¹ * (φ x₁)⁻¹) * ‖g x‖ ^ 2 :=
        le_trans (abs_nonneg _) hrhs
      rw [Real.norm_eq_abs, abs_mul]
      calc |regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
              (fun z => -((φ z)⁻¹ • g z)) x| * |ψ x|
          ≤ (A2 + 2 * |Ψ 0| + 2 * C * ((φ x₁)⁻¹ * (φ x₁)⁻¹) * ‖g x‖ ^ 2) * Mψ :=
            mul_le_mul hrhs hψx (abs_nonneg _) hnn
        _ = Mψ * (A2 + 2 * |Ψ 0| + 2 * C * ((φ x₁)⁻¹ * (φ x₁)⁻¹) * ‖g x‖ ^ 2) := by ring
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  -- ### conclude
  have hzero : (∫ x,
      (⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x), weakGrad χ x⟫ +
        (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
          deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x -
        (2 * regMin 2 κ Ψ K + κ / 2) * (φ x * χ x))) = 0 := by
    have hab : Integrable (fun x =>
        ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x), weakGrad χ x⟫ +
          (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
            deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x) volume := hint_a.add hint_b
    have hs1 : (∫ x,
        (⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x), weakGrad χ x⟫ +
          (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
            deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x -
          (2 * regMin 2 κ Ψ K + κ / 2) * (φ x * χ x))) =
        (∫ x, (⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x), weakGrad χ x⟫ +
            (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
              deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x)) -
          ∫ x, (2 * regMin 2 κ Ψ K + κ / 2) * (φ x * χ x) := integral_sub hab hint_c
    have hs2 : (∫ x, (⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x),
          weakGrad χ x⟫ +
          (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
            deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x)) =
        (∫ x, ⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x), weakGrad χ x⟫) +
          ∫ x, (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
            deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x := integral_add hint_a hint_b
    rw [hs1, hs2, hEL, integral_const_mul]
    ring
  have hsum0 : (∫ x, (⟪gradient Ψ (-((φ x)⁻¹ • g x)), gradient ψ x⟫ +
      regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
        (fun z => -((φ z)⁻¹ • g z)) x * ψ x)) = 0 := by
    have heq : (fun x => ⟪gradient Ψ (-((φ x)⁻¹ • g x)), gradient ψ x⟫ +
        regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
          (fun z => -((φ z)⁻¹ • g z)) x * ψ x) =ᵐ[volume]
        fun x => -(⟪Korevaar.homogeneousFlux 2 (gradient Ψ) (φ x) (weakGrad φ x),
              weakGrad χ x⟫ +
            (Korevaar.homogeneousValueDerivative 2 Ψ (gradient Ψ) (φ x) (weakGrad φ x) +
              deriv (Korevaar.entropyPotential 2 κ) (φ x)) * χ x -
            (2 * regMin 2 κ Ψ K + κ / 2) * (φ x * χ x)) := by
      filter_upwards [hpt] with x hx
      rw [hx]
      ring
    rw [integral_congr_ae heq, integral_neg, hzero, neg_zero]
  have hsplit : (∫ x, (⟪gradient Ψ (-((φ x)⁻¹ • g x)), gradient ψ x⟫ +
      regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
        (fun z => -((φ z)⁻¹ • g z)) x * ψ x)) =
      (∫ x, ⟪gradient Ψ (-((φ x)⁻¹ • g x)), gradient ψ x⟫) +
        ∫ x, regLogRhs κ (regMin 2 κ Ψ K) Ψ (fun z => -Real.log (φ z))
          (fun z => -((φ z)⁻¹ • g z)) x * ψ x := integral_add hint_t1 hint_t2
  rw [hsplit] at hsum0
  linarith

/-! ### The lane statement -/

/-- **(1) The weak equation for `v = -log φ`** (lane `L3`, step 1), step 1 of Revision 2 (v) of
`REGULARIZED_ROUTE.md`.

The gradient field is `G = -(φ⁻¹ • weakGrad φ)` (measurable, and `0` off `K` because `φ = 0`
there and `(0 : ℝ)⁻¹ = 0`); it is square integrable on every closed ball inside `K` because `φ`
is bounded below there by a positive constant.  The algebra turning the weak Euler–Lagrange
equation into the weak equation of `IsWeakLogSol` is `euler_lagrange_substitution`, proved
above. -/
-- TODO(reg/c2a): the analytic half of the substitution `χ = ψ / φ`.  Three steps remain:
-- (i) the chain rule: `v = -log φ` has the local weak gradient `G = -(φ⁻¹ • weakGrad φ)` on `K`
--     (compose `weakGrad φ` with a `C¹` profile agreeing with `-log` on `[δ/2, ∞)` and having a
--     bounded derivative, `Komlos.Literature.memW0_comp`, on a ball where `φ ≥ δ > 0`);
-- (ii) the approximation `χ_n = ψ / mollifyWith ρ_n φ ∈ IsTestFn K`, which converges to `ψ/φ`
--     uniformly and in `W^{1,2}` (`Komlos.Literature.gradient_mollifyWith`,
--     `tendsto_eLpNorm_mollifyWith_sub`), so that
--     `IsRegMinimizer.weak_euler_lagrange hκ hΨ hK hφmin hφc hφpos` passes to the limit (the
--     flux is `L²`, the value-derivative term `L¹`, on the ball containing `tsupport ψ`);
-- (iii) `euler_lagrange_substitution` pointwise, then integrate.
theorem exists_isWeakLogSol (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hφ0 : ∀ x, x ∉ K → φ x = 0)
    (hφpos : ∀ x ∈ K, 0 < φ x) (hφmin : IsRegMinimizer 2 κ Ψ K φ) :
    ∃ G : Euc d → Euc d,
      IsWeakLogSol κ (regMin 2 κ Ψ K) Ψ K (fun x => -Real.log (φ x)) G := by
  -- a measurable representative of `weakGrad φ`
  obtain ⟨g, hgm, hgae⟩ : ∃ g : Euc d → Euc d, Measurable g ∧ weakGrad φ =ᵐ[volume] g :=
    ⟨hφmin.memW0.memLp_weakGrad.aestronglyMeasurable.mk _,
      hφmin.memW0.memLp_weakGrad.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      hφmin.memW0.memLp_weakGrad.aestronglyMeasurable.ae_eq_mk⟩
  have hgL2 : MemLp g (ENNReal.ofReal (2 : ℝ)) volume :=
    hφmin.memW0.memLp_weakGrad.ae_eq hgae
  have hgsq : Integrable (fun x => ‖g x‖ ^ 2) volume := by
    rw [ofReal_two'] at hgL2
    exact (memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).1 hgL2
  refine ⟨fun x => -((φ x)⁻¹ • g x),
    { isOpen := hK.isOpen
      continuousOn := continuousOn_neg_log hφc hφpos
      measurable := measurable_neg_log hφc
      measurable_grad := ((hφc.measurable.inv).smul hgm).neg
      hasWeakGradientOn := hasWeakGradientOn_neg_log hK hφc hφpos hφmin.memW0 hgae
      integrableOn_sq := ?_
      weakEq := fun ψ hψ hψs hψK =>
        weakEq_neg_log hκ hΨ hK hφc hφ0 hφpos hφmin hgae hψ hψs hψK }⟩
  intro y s hsub
  rcases eq_empty_or_nonempty (Metric.closedBall y s) with he | hne
  · rw [he]
    exact integrableOn_empty
  obtain ⟨x₁, hx₁, hmin⟩ :=
    (isCompact_closedBall y s).exists_isMinOn hne hφc.continuousOn
  have hδ : 0 < φ x₁ := hφpos x₁ (hsub hx₁)
  refine Integrable.mono' ((hgsq.restrict).const_mul ((φ x₁)⁻¹ ^ 2))
    (((hφc.measurable.inv).smul hgm).neg.norm.pow_const 2).aestronglyMeasurable.restrict
    ((ae_restrict_mem measurableSet_closedBall).mono fun x hx => ?_)
  have hle : φ x₁ ≤ φ x := hmin hx
  have hxpos : 0 < φ x := lt_of_lt_of_le hδ hle
  have hinv : (φ x)⁻¹ ≤ (φ x₁)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hδ hle
  have heq : ‖-((φ x)⁻¹ • g x)‖ ^ 2 = ((φ x)⁻¹) ^ 2 * ‖g x‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), heq]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (inv_nonneg.2 hxpos.le) hinv 2) (sq_nonneg _)

end Komlos.Literature.Regularized
