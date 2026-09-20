import Komlos.Literature.Regularized.DomainLimitScalar
import Komlos.Literature.Regularized.ProfileBasic

/-!
# Convergence of the regularized minimum along the inner domains

Step 4 of the `L4` lane of `REGULARIZED_ROUTE.md`:

  `regMin 2 κ Ψ (x₀ + s (K - x₀)) → regMin 2 κ Ψ K`   as `s ↑ 1`.

The inequality `regMin 2 κ Ψ K ≤ regMin 2 κ Ψ K_n` is `regMin_le_regMin_of_subset`
(zero extension: the admissible class only grows with the domain).  The other direction
dilates the minimizer `w = D.φ` of `K` into the inner domain:

  `w_s(x) = (s^d)^{-1/2} w (x₀ + s⁻¹ (x - x₀))`

is admissible for `x₀ + s (K - x₀)`, because `∫ w_s² = (s^d)⁻¹ s^d ∫ w² = 1`, and its weak
gradient is `(s^d)^{-1/2} s⁻¹ ∇w (x₀ + s⁻¹ (· - x₀))` (`HasWeakGradient.comp_dilate`).  Since
the kinetic density is jointly `2`-homogeneous, the change of variables
`integral_comp_dilate` gives exactly

  `E(w_s) = ∫ w² Ψ(s⁻¹ ∇w/w) + ∫ (κ/2) w² log w + (κ/2) log ((s^d)^{-1/2})`,

and the Taylor bound `Ψ(t q) ≤ Ψ q + (C(t-1) + (C/2)(t-1)²)‖q‖²` of `ProfileBasic` (with
`t = s⁻¹ ≥ 1`) bounds the kinetic term by `∫ w² Ψ(∇w/w) + (C(t-1)+(C/2)(t-1)²) ∫‖∇w‖²`.
Both error terms vanish as `s ↑ 1`.

## Main results

* `exists_dilate_regEnergy_le` — the dilation estimate at a fixed ratio `s`;
* `eventually_regMin_innerDomain_le`, `tendsto_regMin_innerDomain` — the limit `s ↑ 1`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)}

/-! ### `rpow`-to-`npow` normalization of the two densities -/

/-- `x ^ (2 : ℝ) = x ^ (2 : ℕ)`, valid for every real `x`. -/
theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem homogeneousDensity_two_eq (Ψ : Euc d → ℝ) (u : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ u ξ = u ^ 2 * Ψ (u⁻¹ • ξ) := by
  rw [Korevaar.homogeneousDensity, rpow_two]

theorem entropyPotential_two_eq (κ u : ℝ) :
    Korevaar.entropyPotential 2 κ u = κ / 2 * (u ^ 2 * Real.log u) := by
  rw [Korevaar.entropyPotential, rpow_two]

/-! ### Scaling identities for the two densities -/

/-- The kinetic density is jointly `2`-homogeneous. -/
theorem homogeneousDensity_const_mul (Ψ : Euc d → ℝ) {a : ℝ} (ha : a ≠ 0) (u : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ (a * u) (a • ξ)
      = a ^ 2 * Korevaar.homogeneousDensity 2 Ψ u ξ := by
  have h1 : (a * u)⁻¹ • (a • ξ) = u⁻¹ • ξ := by
    rw [smul_smul, mul_inv, mul_comm a⁻¹ u⁻¹, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  rw [homogeneousDensity_two_eq, homogeneousDensity_two_eq, h1, mul_pow]
  ring

/-- Scaling of the entropy potential: `P(a u) = a² P(u) + (κ/2) a² (log a) u²` for `u ≥ 0`. -/
theorem entropyPotential_const_mul (κ : ℝ) {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 0 ≤ u) :
    Korevaar.entropyPotential 2 κ (a * u)
      = a ^ 2 * Korevaar.entropyPotential 2 κ u + κ / 2 * (a ^ 2 * Real.log a) * u ^ 2 := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h]
    simp [entropyPotential_two_eq]
  · rw [entropyPotential_two_eq, entropyPotential_two_eq, Real.log_mul ha.ne' h.ne', mul_pow]
    ring

/-! ### Two elementary pointwise bounds -/

/-- `u² ‖u⁻¹ ξ‖² ≤ ‖ξ‖²`, with equality unless `u = 0`. -/
theorem sq_mul_norm_inv_smul_le (u : ℝ) (ξ : Euc d) : u ^ 2 * ‖u⁻¹ • ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  rcases eq_or_ne u 0 with h0 | h0
  · simp [h0]
  · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← mul_assoc]
    have h : u ^ 2 * (u⁻¹) ^ 2 = 1 := by field_simp
    rw [h, one_mul]

/-- `|u² log u| ≤ u³ + u` for `u ≥ 0`: for `u ≤ 1` use `log (1/u) ≤ 1/u - 1`, for `u ≥ 1` use
`log u ≤ u - 1`. -/
theorem abs_sq_mul_log_le_cube_add {u : ℝ} (hu : 0 ≤ u) : |u ^ 2 * Real.log u| ≤ u ^ 3 + u := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h]; simp
  rcases le_or_gt u 1 with h1 | h1
  · have hlog : Real.log u ≤ 0 := Real.log_nonpos h.le h1
    have hkey : -Real.log u ≤ u⁻¹ - 1 := by
      have hh := Real.log_le_sub_one_of_pos (inv_pos.2 h)
      rwa [Real.log_inv] at hh
    have habs : |u ^ 2 * Real.log u| = u ^ 2 * (-Real.log u) := by
      rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) hlog)]
      ring
    have hmul : u ^ 2 * (-Real.log u) ≤ u ^ 2 * (u⁻¹ - 1) :=
      mul_le_mul_of_nonneg_left hkey (sq_nonneg u)
    have heq : u ^ 2 * (u⁻¹ - 1) = u - u ^ 2 := by field_simp; try ring
    rw [habs]
    nlinarith [pow_nonneg hu 3, sq_nonneg u]
  · have hlog : 0 ≤ Real.log u := Real.log_nonneg h1.le
    have hle : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos h
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg u) hlog)]
    nlinarith [sq_nonneg u]

/-- **The Taylor bound for the kinetic density in the gradient variable**: for `t ≥ 1`,
`D(u, t ξ) ≤ D(u, ξ) + (C (t-1) + (C/2)(t-1)²) ‖ξ‖²`. -/
theorem homogeneousDensity_smul_le (h : IsRegProfileWith Ψ c C) {t : ℝ} (ht : 1 ≤ t)
    (u : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ u (t • ξ) ≤
      Korevaar.homogeneousDensity 2 Ψ u ξ + (C * (t - 1) + C / 2 * (t - 1) ^ 2) * ‖ξ‖ ^ 2 := by
  have ht0 : (0 : ℝ) ≤ t - 1 := by linarith
  set q : Euc d := u⁻¹ • ξ with hq
  have hsm : u⁻¹ • (t • ξ) = q + (t - 1) • q := by
    have h1 : u⁻¹ • (t • ξ) = t • q := by rw [hq, smul_comm]
    rw [h1, sub_smul, one_smul]
    abel
  have htaylor := h.le_add_inner_add_half q ((t - 1) • q)
  have hinner : ⟪gradient Ψ q, (t - 1) • q⟫ = (t - 1) * ⟪gradient Ψ q, q⟫ :=
    real_inner_smul_right _ _ _
  have hcs : ⟪gradient Ψ q, q⟫ ≤ C * ‖q‖ ^ 2 := by
    calc ⟪gradient Ψ q, q⟫ ≤ ‖gradient Ψ q‖ * ‖q‖ := real_inner_le_norm _ _
      _ ≤ C * ‖q‖ * ‖q‖ := mul_le_mul_of_nonneg_right (h.norm_gradient_le q) (norm_nonneg _)
      _ = C * ‖q‖ ^ 2 := by ring
  have hnorm : ‖(t - 1) • q‖ ^ 2 = (t - 1) ^ 2 * ‖q‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hstep : Ψ (u⁻¹ • (t • ξ)) ≤ Ψ q + (C * (t - 1) + C / 2 * (t - 1) ^ 2) * ‖q‖ ^ 2 := by
    rw [hsm]
    rw [hinner, hnorm] at htaylor
    nlinarith [htaylor, hcs, ht0, sq_nonneg (t - 1), h.C_nonneg, sq_nonneg ‖q‖]
  have hA0 : (0 : ℝ) ≤ C * (t - 1) + C / 2 * (t - 1) ^ 2 := by
    have := h.C_nonneg
    nlinarith [sq_nonneg (t - 1)]
  rw [homogeneousDensity_two_eq, homogeneousDensity_two_eq]
  have hmul : u ^ 2 * Ψ (u⁻¹ • (t • ξ)) ≤
      u ^ 2 * (Ψ q + (C * (t - 1) + C / 2 * (t - 1) ^ 2) * ‖q‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hstep (sq_nonneg u)
  have hq2 : u ^ 2 * ‖q‖ ^ 2 ≤ ‖ξ‖ ^ 2 := sq_mul_norm_inv_smul_le u ξ
  nlinarith [hmul, hq2, hA0]

/-! ### Integrability of the two densities -/

/-- `‖f‖² is integrable when `f ∈ L²`. -/
theorem integrable_sq_of_memLp_two {E : Type*} [NormedAddCommGroup E] {f : Euc d → E}
    (hf : MemLp f (ENNReal.ofReal 2) volume) : Integrable (fun x => ‖f x‖ ^ 2) volume := by
  have h := hf.integrable_norm_rpow (by simp) (by simp)
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] at h
  exact h.congr (Eventually.of_forall fun x => rpow_two _)

/-- The kinetic density of a continuous `L²` function against an `L²` field is integrable: it is
dominated by `|Ψ 0| w² + (C/2) ‖ξ‖²` by the quadratic growth of `Ψ`. -/
theorem integrable_homogeneousDensity (h : IsRegProfileWith Ψ c C) {w : Euc d → ℝ}
    (hwc : Continuous w) (hw2 : Integrable (fun x => w x ^ 2) volume)
    {ξ : Euc d → Euc d} (hξm : AEStronglyMeasurable ξ volume)
    (hξ2 : Integrable (fun x => ‖ξ x‖ ^ 2) volume) :
    Integrable (fun y => Korevaar.homogeneousDensity 2 Ψ (w y) (ξ y)) volume := by
  have hΨc : Continuous Ψ := h.toIsRegProfile.contDiff.continuous
  have hmeas : AEStronglyMeasurable
      (fun y => Korevaar.homogeneousDensity 2 Ψ (w y) (ξ y)) volume := by
    have h1 : AEStronglyMeasurable (fun y => (w y)⁻¹ • ξ y) volume :=
      AEStronglyMeasurable.smul (hwc.measurable.inv.aestronglyMeasurable) hξm
    have h2 : AEStronglyMeasurable (fun y => Ψ ((w y)⁻¹ • ξ y)) volume :=
      hΨc.comp_aestronglyMeasurable h1
    have h3 : AEStronglyMeasurable (fun y => w y ^ 2 * Ψ ((w y)⁻¹ • ξ y)) volume :=
      ((hwc.pow 2).aestronglyMeasurable).mul h2
    refine h3.congr (Eventually.of_forall fun y => ?_)
    exact (homogeneousDensity_two_eq Ψ (w y) (ξ y)).symm
  refine Integrable.mono' ((hw2.const_mul |Ψ 0|).add (hξ2.const_mul (C / 2))) hmeas ?_
  refine Eventually.of_forall fun y => ?_
  have hub : Ψ ((w y)⁻¹ • ξ y) ≤ Ψ 0 + C / 2 * ‖(w y)⁻¹ • ξ y‖ ^ 2 :=
    h.quadratic_upper _
  have hlb : Ψ 0 ≤ Ψ ((w y)⁻¹ • ξ y) := by
    have := h.quadratic_lower ((w y)⁻¹ • ξ y)
    nlinarith [h.c_pos, sq_nonneg ‖(w y)⁻¹ • ξ y‖]
  have habs : |Ψ ((w y)⁻¹ • ξ y)| ≤ |Ψ 0| + C / 2 * ‖(w y)⁻¹ • ξ y‖ ^ 2 := by
    rw [abs_le]
    constructor
    · have h0 : -|Ψ 0| ≤ Ψ 0 := neg_abs_le _
      have hnn : 0 ≤ C / 2 * ‖(w y)⁻¹ • ξ y‖ ^ 2 :=
        mul_nonneg (by linarith [h.C_nonneg]) (sq_nonneg _)
      linarith
    · have h0 : Ψ 0 ≤ |Ψ 0| := le_abs_self _
      linarith
  have hkey : ‖Korevaar.homogeneousDensity 2 Ψ (w y) (ξ y)‖ ≤
      |Ψ 0| * w y ^ 2 + C / 2 * ‖ξ y‖ ^ 2 := by
    rw [homogeneousDensity_two_eq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (w y))]
    have h1 : w y ^ 2 * |Ψ ((w y)⁻¹ • ξ y)| ≤
        w y ^ 2 * (|Ψ 0| + C / 2 * ‖(w y)⁻¹ • ξ y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left habs (sq_nonneg _)
    have h2 : w y ^ 2 * ‖(w y)⁻¹ • ξ y‖ ^ 2 ≤ ‖ξ y‖ ^ 2 := sq_mul_norm_inv_smul_le _ _
    nlinarith [h.C_nonneg, sq_nonneg (w y)]
  exact hkey

/-- The entropy potential of a nonnegative continuous compactly supported function is
integrable: it is dominated by `(|κ|/2)(w³ + w)`. -/
theorem integrable_entropyPotential (κ : ℝ) {w : Euc d → ℝ} (hwc : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwcs : HasCompactSupport w) :
    Integrable (fun y => Korevaar.entropyPotential 2 κ (w y)) volume := by
  have hdomc : Continuous fun y => |κ| / 2 * (w y ^ 3 + w y) := by fun_prop
  have hdoms : HasCompactSupport fun y => |κ| / 2 * (w y ^ 3 + w y) := by
    refine HasCompactSupport.intro hwcs.isCompact fun x hx => ?_
    have hx0 : w x = 0 := by
      by_contra hne
      exact hx (subset_closure (by simpa [Function.mem_support] using hne))
    simp [hx0]
  have hmeas : AEStronglyMeasurable (fun y => Korevaar.entropyPotential 2 κ (w y)) volume := by
    have h1 : Measurable fun y => κ / 2 * (w y ^ 2 * Real.log (w y)) :=
      (measurable_const.mul (((hwc.pow 2).measurable).mul
        (Real.measurable_log.comp hwc.measurable)))
    simpa only [entropyPotential_two_eq] using h1.aestronglyMeasurable
  refine Integrable.mono' (hdomc.integrable_of_hasCompactSupport hdoms) hmeas ?_
  refine Eventually.of_forall fun y => ?_
  rw [entropyPotential_two_eq, Real.norm_eq_abs, abs_mul, abs_div]
  have h1 := abs_sq_mul_log_le_cube_add (hw0 y)
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  have hpos : (0 : ℝ) ≤ |κ| / 2 := by positivity
  exact mul_le_mul_of_nonneg_left h1 hpos

/-! ### The dilated competitor -/

/-- **The dilation estimate** (`REGULARIZED_ROUTE.md`, `L4`, step 4, second half).  For
`0 < s ≤ 1` the dilate `w_s(x) = (s^d)^{-1/2} D.φ (x₀ + s⁻¹ (x - x₀))` of the minimizer on `K`
is admissible on `x₀ + s (K - x₀)` and its energy exceeds `regMin 2 κ Ψ K` by at most
`(C(s⁻¹-1) + (C/2)(s⁻¹-1)²) ∫‖∇D.φ‖² - (κ d/4) log s`, which vanishes as `s ↑ 1`. -/
theorem exists_dilate_regEnergy_le (hprof : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (x₀ : Euc d) (D : RegEigenData 2 κ Ψ K)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ ws : Euc d → ℝ, IsRegAdmissible 2 (dilateSet x₀ s K) ws ∧
      regEnergy 2 κ Ψ ws ≤ regMin 2 κ Ψ K +
        ((C * (s⁻¹ - 1) + C / 2 * (s⁻¹ - 1) ^ 2) * (∫ x, ‖weakGrad D.φ x‖ ^ 2)
          - κ * d / 4 * Real.log s) := by
  have hadm : IsRegAdmissible 2 K D.φ := D.isRegMinimizer.toIsRegAdmissible
  have hwc : Continuous D.φ := D.continuous
  have hw0 : ∀ x, 0 ≤ D.φ x := hadm.nonneg
  have hwK : ∀ x, x ∉ K → D.φ x = 0 := hadm.eq_zero_of_notMem
  have hwp : MemLp D.φ (ENNReal.ofReal 2) volume := hadm.memW0.memLp
  have hgp : MemLp (weakGrad D.φ) (ENNReal.ofReal 2) volume := hadm.memW0.memLp_weakGrad
  have hwg : HasWeakGradient D.φ (weakGrad D.φ) := hadm.memW0.hasWeakGradient
  have hw2 : Integrable (fun x => D.φ x ^ 2) volume := by
    refine (integrable_sq_of_memLp_two hwp).congr (Eventually.of_forall fun x => ?_)
    show ‖D.φ x‖ ^ 2 = D.φ x ^ 2
    rw [Real.norm_eq_abs, sq_abs]
  have hg2 : Integrable (fun x => ‖weakGrad D.φ x‖ ^ 2) volume := integrable_sq_of_memLp_two hgp
  have hwsq : ∫ x, D.φ x ^ 2 = 1 := hadm.integral_sq
  have hwcs : HasCompactSupport D.φ :=
    HasCompactSupport.intro hK.isBounded.isCompact_closure fun x hx =>
      hwK x fun hxK => hx (subset_closure hxK)
  have hent : Integrable (fun y => Korevaar.entropyPotential 2 κ (D.φ y)) volume :=
    integrable_entropyPotential κ hwc hw0 hwcs
  have hkin : Integrable
      (fun y => Korevaar.homogeneousDensity 2 Ψ (D.φ y) (weakGrad D.φ y)) volume :=
    integrable_homogeneousDensity hprof hwc hw2 hgp.1 hg2
  have hs1' : 1 ≤ s⁻¹ := by
    have hh := mul_inv_cancel₀ hs0.ne'
    nlinarith [inv_pos.2 hs0]
  have hgsm : AEStronglyMeasurable (fun x => s⁻¹ • weakGrad D.φ x) volume :=
    AEStronglyMeasurable.const_smul hgp.1 s⁻¹
  have hgs2 : Integrable (fun x => ‖s⁻¹ • weakGrad D.φ x‖ ^ 2) volume := by
    refine (hg2.const_mul (s⁻¹ ^ 2)).congr (Eventually.of_forall fun x => ?_)
    show s⁻¹ ^ 2 * ‖weakGrad D.φ x‖ ^ 2 = ‖s⁻¹ • weakGrad D.φ x‖ ^ 2
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hkin' : Integrable
      (fun y => Korevaar.homogeneousDensity 2 Ψ (D.φ y) (s⁻¹ • weakGrad D.φ y)) volume :=
    integrable_homogeneousDensity hprof hwc hw2 hgsm hgs2
  -- the normalizing constant of the dilation
  obtain ⟨cc, hcc0, hccsd, hcclog⟩ :
      ∃ cc : ℝ, 0 < cc ∧ cc ^ 2 * s ^ d = 1 ∧
        κ / 2 * Real.log cc = -(κ * d / 4 * Real.log s) := by
    have hd0 : (0 : ℝ) < s ^ d := pow_pos hs0 d
    refine ⟨(Real.sqrt (s ^ d))⁻¹, inv_pos.2 (Real.sqrt_pos.2 hd0), ?_, ?_⟩
    · rw [inv_pow, Real.sq_sqrt hd0.le, inv_mul_cancel₀ hd0.ne']
    · rw [Real.log_inv, Real.log_sqrt hd0.le, Real.log_pow]
      ring
  have hdcc : s ^ d * cc ^ 2 = 1 := by linear_combination hccsd
  -- the dilated competitor and its weak gradient
  set ws : Euc d → ℝ := fun x => cc * D.φ (x₀ + s⁻¹ • (x - x₀)) with hws_def
  set gs : Euc d → Euc d :=
    fun x => cc • (s⁻¹ • weakGrad D.φ (x₀ + s⁻¹ • (x - x₀))) with hgs_def
  have hwsg : HasWeakGradient ws gs :=
    (hwg.comp_dilate (q := 2) (by norm_num) hwp hgp x₀ hs0).smul cc
  have hwsp : MemLp ws (ENNReal.ofReal 2) volume :=
    (memLp_comp_dilate (by norm_num : (0:ℝ) < 2) hwp x₀ hs0).const_smul cc
  have hgsp : MemLp gs (ENNReal.ofReal 2) volume :=
    ((memLp_comp_dilate (by norm_num : (0:ℝ) < 2) hgp x₀ hs0).const_smul s⁻¹).const_smul cc
  have hzero : ∀ x, x ∉ dilateSet x₀ s K → ws x = 0 := by
    intro x hx
    have hnot : x₀ + s⁻¹ • (x - x₀) ∉ K := fun h => hx ((dilateSet_mem_iff hs0.ne').2 h)
    simp only [hws_def]
    rw [hwK _ hnot, mul_zero]
  have hnormsq : ∫ x, ws x ^ 2 = 1 := by
    have hpt : ∀ x, ws x ^ 2 = (fun y => cc ^ 2 * D.φ y ^ 2) (x₀ + s⁻¹ • (x - x₀)) := by
      intro x
      simp only [hws_def]
      rw [mul_pow]
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_comp_dilate (fun y => cc ^ 2 * D.φ y ^ 2) x₀ hs0, smul_eq_mul,
      integral_const_mul, hwsq, mul_one]
    exact hdcc
  have hadms : IsRegAdmissible 2 (dilateSet x₀ s K) ws :=
    { memW0 :=
        { memLp := hwsp
          ae_eq_zero := Eventually.of_forall hzero
          exists_weakGradient := ⟨gs, hwsg, hgsp⟩ }
      nonneg := fun x => mul_nonneg hcc0.le (hw0 _)
      eq_zero_of_notMem := hzero
      integral_rpow := by
        rw [← hnormsq]
        exact integral_congr_ae (Eventually.of_forall fun x => rpow_two _) }
  refine ⟨ws, hadms, ?_⟩
  have hgsae : weakGrad ws =ᵐ[volume] gs :=
    HasWeakGradient.ae_eq (hasWeakGradient_weakGrad ⟨gs, hwsg⟩) hwsg
  -- the kinetic part after the change of variables
  have hkinI : ∫ x, Korevaar.homogeneousDensity 2 Ψ (ws x) (weakGrad ws x)
      = ∫ y, Korevaar.homogeneousDensity 2 Ψ (D.φ y) (s⁻¹ • weakGrad D.φ y) := by
    have h1 : ∫ x, Korevaar.homogeneousDensity 2 Ψ (ws x) (weakGrad ws x)
        = ∫ x, Korevaar.homogeneousDensity 2 Ψ (ws x) (gs x) :=
      integral_congr_ae (hgsae.mono fun x hx => by
        show Korevaar.homogeneousDensity 2 Ψ (ws x) (weakGrad ws x)
            = Korevaar.homogeneousDensity 2 Ψ (ws x) (gs x)
        rw [hx])
    have hpt : ∀ x, Korevaar.homogeneousDensity 2 Ψ (ws x) (gs x)
        = (fun y => cc ^ 2 * Korevaar.homogeneousDensity 2 Ψ (D.φ y) (s⁻¹ • weakGrad D.φ y))
            (x₀ + s⁻¹ • (x - x₀)) := by
      intro x
      simp only [hws_def, hgs_def]
      exact homogeneousDensity_const_mul Ψ hcc0.ne' _ _
    rw [h1, integral_congr_ae (Eventually.of_forall hpt),
      integral_comp_dilate
        (fun y => cc ^ 2 * Korevaar.homogeneousDensity 2 Ψ (D.φ y) (s⁻¹ • weakGrad D.φ y))
        x₀ hs0,
      smul_eq_mul, integral_const_mul, ← mul_assoc, hdcc, one_mul]
  -- the entropy part after the change of variables
  have hentI : ∫ x, Korevaar.entropyPotential 2 κ (ws x)
      = (∫ y, Korevaar.entropyPotential 2 κ (D.φ y)) + κ / 2 * Real.log cc := by
    have hpt : ∀ x, Korevaar.entropyPotential 2 κ (ws x)
        = (fun y => cc ^ 2 * Korevaar.entropyPotential 2 κ (D.φ y)
            + κ / 2 * (cc ^ 2 * Real.log cc) * D.φ y ^ 2) (x₀ + s⁻¹ • (x - x₀)) := by
      intro x
      simp only [hws_def]
      exact entropyPotential_const_mul κ hcc0 (hw0 _)
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_comp_dilate
        (fun y => cc ^ 2 * Korevaar.entropyPotential 2 κ (D.φ y)
          + κ / 2 * (cc ^ 2 * Real.log cc) * D.φ y ^ 2) x₀ hs0,
      smul_eq_mul, integral_add (hent.const_mul _) (hw2.const_mul _), integral_const_mul,
      integral_const_mul, hwsq, mul_one]
    linear_combination ((∫ y, Korevaar.entropyPotential 2 κ (D.φ y)) +
      κ / 2 * Real.log cc) * hccsd
  -- the Taylor bound for the kinetic part
  have hsum : Integrable
      (fun y => Korevaar.homogeneousDensity 2 Ψ (D.φ y) (weakGrad D.φ y)
        + (C * (s⁻¹ - 1) + C / 2 * (s⁻¹ - 1) ^ 2) * ‖weakGrad D.φ y‖ ^ 2) volume :=
    hkin.add (hg2.const_mul _)
  have hkinle : ∫ y, Korevaar.homogeneousDensity 2 Ψ (D.φ y) (s⁻¹ • weakGrad D.φ y)
      ≤ (∫ y, Korevaar.homogeneousDensity 2 Ψ (D.φ y) (weakGrad D.φ y))
        + (C * (s⁻¹ - 1) + C / 2 * (s⁻¹ - 1) ^ 2) * ∫ x, ‖weakGrad D.φ x‖ ^ 2 := by
    have hmono : ∫ y, Korevaar.homogeneousDensity 2 Ψ (D.φ y) (s⁻¹ • weakGrad D.φ y)
        ≤ ∫ y, (Korevaar.homogeneousDensity 2 Ψ (D.φ y) (weakGrad D.φ y)
            + (C * (s⁻¹ - 1) + C / 2 * (s⁻¹ - 1) ^ 2) * ‖weakGrad D.φ y‖ ^ 2) :=
      integral_mono hkin' hsum fun y => homogeneousDensity_smul_le hprof hs1' _ _
    rwa [integral_add hkin (hg2.const_mul _), integral_const_mul] at hmono
  have henergy : regEnergy 2 κ Ψ D.φ = regMin 2 κ Ψ K := D.isRegMinimizer.energy_eq
  simp only [regEnergy] at henergy ⊢
  rw [hkinI, hentI, hcclog]
  linarith [hkinle]

/-- **The regularized minima of the inner domains are eventually close to `regMin 2 κ Ψ K`**
(`REGULARIZED_ROUTE.md`, `L4`, step 4, second half): dilate the minimizer of `K` into the inner
domain and let the ratio tend to `1`. -/
theorem eventually_regMin_innerDomain_le (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) (D : RegEigenData 2 κ Ψ K)
    (Dn : ∀ n, RegEigenData 2 κ Ψ (innerDomain x₀ K n)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, regMin 2 κ Ψ (innerDomain x₀ K n) ≤ regMin 2 κ Ψ K + ε := by
  obtain ⟨c, C, hprof⟩ := hΨ.exists_isRegProfileWith
  have hinv : Tendsto (fun n => (innerRatio n)⁻¹) atTop (𝓝 1) := by
    have h := tendsto_innerRatio.inv₀ (one_ne_zero)
    simpa using h
  have hlog : Tendsto (fun n => Real.log (innerRatio n)) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp tendsto_innerRatio
    simpa only [Function.comp_def, Real.log_one] using h
  have h1 : Tendsto (fun n => (innerRatio n)⁻¹ - 1) atTop (𝓝 0) := by
    simpa using hinv.sub_const 1
  have hA : Tendsto (fun n : ℕ => C * ((innerRatio n)⁻¹ - 1)
      + C / 2 * ((innerRatio n)⁻¹ - 1) ^ 2) atTop (𝓝 0) := by
    have ha := h1.const_mul C
    have hb := (h1.pow 2).const_mul (C / 2)
    simpa using ha.add hb
  have herr : Tendsto (fun n : ℕ =>
      (C * ((innerRatio n)⁻¹ - 1) + C / 2 * ((innerRatio n)⁻¹ - 1) ^ 2)
          * (∫ x, ‖weakGrad D.φ x‖ ^ 2)
        - κ * d / 4 * Real.log (innerRatio n)) atTop (𝓝 0) := by
    have h2 := hA.mul_const (∫ x, ‖weakGrad D.φ x‖ ^ 2)
    have h3 := hlog.const_mul (κ * d / 4)
    have h4 := h2.sub h3
    simpa using h4
  filter_upwards [herr.eventually (gt_mem_nhds hε)] with n hn
  obtain ⟨ws, hws, hle⟩ := exists_dilate_regEnergy_le hprof hK x₀ D
    (innerRatio_pos n) (innerRatio_lt_one n).le
  have hws' : IsRegAdmissible 2 (innerDomain x₀ K n) ws := hws
  have hmin : regMin 2 κ Ψ (innerDomain x₀ K n) ≤ regEnergy 2 κ Ψ ws :=
    regMin_le_regEnergy_of_bddBelow (Dn n).isRegMinimizer.bddBelow hws'
  linarith

/-- **Convergence of the regularized minima along the inner domains**
(`REGULARIZED_ROUTE.md`, `L4`, step 4). -/
theorem tendsto_regMin_innerDomain (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) (D : RegEigenData 2 κ Ψ K)
    (Dn : ∀ n, RegEigenData 2 κ Ψ (innerDomain x₀ K n)) :
    Tendsto (fun n => regMin 2 κ Ψ (innerDomain x₀ K n)) atTop (𝓝 (regMin 2 κ Ψ K)) := by
  have hmono : ∀ n, regMin 2 κ Ψ K ≤ regMin 2 κ Ψ (innerDomain x₀ K n) := fun n =>
    regMin_le_regMin_of_subset (innerDomain_subset hK hx₀ n) D.isRegMinimizer.bddBelow
      (Dn n).isRegMinimizer
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact Eventually.of_forall fun n => lt_of_lt_of_le ha (hmono n)
  · filter_upwards [eventually_regMin_innerDomain_le hκ hΨ hK hx₀ D Dn
      (ε := (a - regMin 2 κ Ψ K) / 2) (by linarith)] with n hn
    linarith

end Komlos.Literature.Regularized
