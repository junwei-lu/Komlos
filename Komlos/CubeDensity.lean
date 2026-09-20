import Komlos.Variation
import Komlos.CubeDensityAux

/-!
# The cube density (paper Lemma 2.4)

`ρ_C(x) = C^{-d} ∏_i cos²(π x_i / (2C)) 𝟙_{(−C,C)^d}(x)` belongs to `𝒫((−C,C)^d)` and
satisfies `V_u ρ_C ≤ (√(2π)/C) ‖u‖₂`.

Proof outline (paper): `ρ_C ∈ C¹_c`, so `V_u ρ_C ≤ ∫ |∂_u ρ_C| = (π/C) 𝔼|∑ u_i T_i|` where
the `T_i = tan(π X_i/(2C))` are i.i.d. with density `2/(π(1+t²)²)`.  This density is the
Gaussian scale mixture `∫_0^∞ √(s/2π) e^{−s t²/2} · (s^{1/2} e^{−s/2}/√(2π)) ds`
(`S ~ χ²₃`, `𝔼 S⁻¹ = 1`), and conditioning on the scales plus Jensen gives
`𝔼|∑ u_i T_i| ≤ √(2/π) ‖u‖₂`.

Implementation: `ρ_C(x) = C^{-d} ∏_i bump C (x_i)` with the `C¹` profile
`Komlos.bump` of `Komlos.CubeDensityAux`; the derivative is
`∂_u ρ_C = −(π/C) ρ_C ∑ u_i tan(π x_i/(2C))` (`fderiv_cubeDensity_apply`), the substitution
`x_i = (2C/π) arctan t_i` is `lintegral_piMap_image`, and the probabilistic core is
`integral_abs_linear_tDensity_le_of_integrable` (with Jensen replaced by AM–GM).
-/

open MeasureTheory Set Filter Topology Real
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-- The open cube `(−C, C)^d`. -/
def cube (d : ℕ) (C : ℝ) : Set (Euc d) := {x | ∀ i, |x i| < C}

/-- The cube density (paper (2.13)). -/
noncomputable def cubeDensity (d : ℕ) (C : ℝ) : Euc d → ℝ :=
  (cube d C).indicator fun x => (C ^ d)⁻¹ * ∏ i, Real.cos (Real.pi * x i / (2 * C)) ^ 2

/-- The cube is nonempty, bounded, open, convex and symmetric. -/
theorem isGoodConvex_cube {C : ℝ} (hC : 0 < C) : IsGoodConvex (cube d C) where
  nonempty := ⟨0, fun i => by simp [hC]⟩
  isBounded := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨Real.sqrt d * C, fun x hx => norm_le_of_forall_abs_le hC.le fun i => (hx i).le⟩
  isOpen := by
    have : cube d C = ⋂ i, {x : Euc d | |x i| < C} := by ext; simp [cube]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  convex := by
    intro x hx y hy a b ha hb hab i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have h1 : a * |x i| ≤ a * C := mul_le_mul_of_nonneg_left (hx i).le ha
    have h2 : b * |y i| ≤ b * C := mul_le_mul_of_nonneg_left (hy i).le hb
    have h3 : a * C + b * C = C := by rw [← add_mul, hab, one_mul]
    calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
      _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < C := by
        rcases ha.lt_or_eq with ha' | ha'
        · have := mul_lt_mul_of_pos_left (hx i) ha'; linarith
        · subst ha'
          have hb1 : b = 1 := by linarith
          subst hb1
          have := hy i; simp only [zero_mul, one_mul, zero_add]; linarith

theorem cube_neg_eq (C : ℝ) : cube d C = -cube d C := by
  ext x; simp [cube]

/-! ### Product structure and regularity -/

/-- `ρ_C(x) = C^{-d} ∏_i bump C (x_i)` everywhere. -/
lemma cubeDensity_eq {C : ℝ} (hC : 0 < C) (x : Euc d) :
    cubeDensity d C x = (C ^ d)⁻¹ * ∏ i, bump C (x i) := by
  unfold cubeDensity
  by_cases hx : x ∈ cube d C
  · rw [indicator_of_mem hx]; congr 1
    exact Finset.prod_congr rfl fun i _ => (bump_of_lt (hx i)).symm
  · rw [indicator_of_notMem hx]
    obtain ⟨i, hi⟩ : ∃ i, ¬ |x i| < C := by simpa [cube] using hx
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (bump_of_not_lt hC hi), mul_zero]

lemma cubeDensity_eq_fun {C : ℝ} (hC : 0 < C) :
    cubeDensity d C = fun x => (C ^ d)⁻¹ * ∏ i, bump C (x i) := funext (cubeDensity_eq hC)

lemma contDiff_bump_coord {C : ℝ} (hC : 0 < C) (i : Fin d) :
    ContDiff ℝ 1 fun x : Euc d => bump C (x i) :=
  (contDiff_bump hC).comp (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff

/-- The cube density is `C¹` with compact support. -/
theorem cubeDensity_contDiff {C : ℝ} (hC : 0 < C) : ContDiff ℝ 1 (cubeDensity d C) := by
  rw [cubeDensity_eq_fun hC]
  exact contDiff_const.mul (contDiff_prod fun i _ => contDiff_bump_coord hC i)

theorem cubeDensity_hasCompactSupport {C : ℝ} (hC : 0 < C) :
    HasCompactSupport (cubeDensity d C) := by
  refine HasCompactSupport.intro (isCompact_closedCube (d := d) hC.le) fun x hx => ?_
  apply indicator_of_notMem
  intro hx'
  exact hx fun i => (hx' i).le

lemma cubeDensity_nonneg {C : ℝ} (hC : 0 < C) (x : Euc d) : 0 ≤ cubeDensity d C x := by
  rw [cubeDensity_eq hC x]
  exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => bump_nonneg C _)

/-- `∫ ρ_C = 1`. -/
lemma integral_cubeDensity {C : ℝ} (hC : 0 < C) : ∫ x, cubeDensity d C x = 1 := by
  rw [cubeDensity_eq_fun hC, integral_euc_eq_integral_pi]
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod (f := fun _ => bump C)]
  simp [integral_bump hC, Finset.prod_const, hC.ne']

/-- Paper Lemma 2.4, membership: `ρ_C ∈ 𝒫((−C, C)^d)`. -/
theorem cubeDensity_memP {C : ℝ} (hC : 0 < C) : MemP (cube d C) (cubeDensity d C) where
  measurable := (cubeDensity_contDiff hC).continuous.measurable
  nonneg := cubeDensity_nonneg hC
  integrable := (cubeDensity_contDiff hC).continuous.integrable_of_hasCompactSupport
    (cubeDensity_hasCompactSupport hC)
  integral_eq_one := integral_cubeDensity hC
  ae_zero_outside := Eventually.of_forall fun _ hx => indicator_of_notMem hx _
  dirVar_ne_top := fun u => ne_top_of_le_ne_top
    (lintegral_enorm_fderiv_apply_lt_top (cubeDensity_contDiff hC)
      (cubeDensity_hasCompactSupport hC) u).ne
    (dirVar_le_lintegral_fderiv u _ (cubeDensity_contDiff hC) (cubeDensity_hasCompactSupport hC))

/-! ### The derivative `∂_u ρ_C = −(π/C) ρ_C ∑ u_i tan(π x_i/(2C))` -/

lemma pi_mul_div_mem_Ioo {C s : ℝ} (hC : 0 < C) (h : |s| < C) :
    Real.pi * s / (2 * C) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  rw [abs_lt] at h
  have hp : 0 < Real.pi / (2 * C) := by positivity
  have e1 : Real.pi * s / (2 * C) = Real.pi / (2 * C) * s := by ring
  have e2 : Real.pi / (2 * C) * C = Real.pi / 2 := by field_simp
  rw [e1]
  constructor
  · have := mul_lt_mul_of_pos_left h.1 hp; rw [mul_neg, e2] at this; exact this
  · have := mul_lt_mul_of_pos_left h.2 hp; rw [e2] at this; exact this

/-- `g_C' = −(π/C) g_C tan(π s/(2C))` (both sides vanish for `|s| ≥ C`). -/
lemma bump'_eq {C : ℝ} (hC : 0 < C) (s : ℝ) :
    bump' C s = -(Real.pi / C) * bump C s * Real.tan (Real.pi * s / (2 * C)) := by
  by_cases h : |s| < C
  · rw [bump'_of_lt h, bump_of_lt h, Real.tan_eq_sin_div_cos]
    have hcos : Real.cos (Real.pi * s / (2 * C)) ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo (pi_mul_div_mem_Ioo hC h)).ne'
    field_simp
  · rw [bump'_of_not_lt hC h, bump_of_not_lt hC h]; ring

lemma hasFDerivAt_cubeDensity {C : ℝ} (hC : 0 < C) (x : Euc d) :
    HasFDerivAt (cubeDensity d C)
      ((C ^ d)⁻¹ • ∑ i, (∏ j ∈ Finset.univ.erase i, bump C (x j)) •
        (bump' C (x i) • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ))) x := by
  rw [cubeDensity_eq_fun hC]
  classical
  refine HasFDerivAt.const_mul ?_ _
  refine HasFDerivAt.finsetProd (g := fun i (x : Euc d) => bump C (x i))
    (g' := fun i => bump' C (x i) • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) fun i _ => ?_
  exact (hasDerivAt_bump hC (x i)).comp_hasFDerivAt (f := fun x : Euc d => x i) x
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt

/-- The directional derivative of the cube density (paper Lemma 2.4, "differentiation"). -/
theorem fderiv_cubeDensity_apply {C : ℝ} (hC : 0 < C) (x u : Euc d) :
    fderiv ℝ (cubeDensity d C) x u =
      -(Real.pi / C) * cubeDensity d C x * ∑ i, u i * Real.tan (Real.pi * x i / (2 * C)) := by
  classical
  rw [(hasFDerivAt_cubeDensity hC x).fderiv]
  simp only [_root_.smul_apply, _root_.sum_apply, smul_eq_mul]
  have hproj : ∀ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) u = u i := fun i => rfl
  simp only [hproj]
  rw [cubeDensity_eq hC, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bump'_eq hC, ← Finset.prod_erase_mul Finset.univ (fun j => bump C (x j)) (Finset.mem_univ i)]
  ring

/-! ### The density of `T_i = tan(π X_i/(2C))` -/

lemma integrable_q : Integrable (fun t : ℝ => 2 / (Real.pi * (1 + t ^ 2) ^ 2)) := by
  refine (integrable_inv_one_add_sq.const_mul (2 / Real.pi)).mono' ?_
    (Eventually.of_forall fun t => ?_)
  · exact (by fun_prop : Measurable fun t : ℝ => 2 / (Real.pi * (1 + t ^ 2) ^ 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    have e : 2 / (Real.pi * (1 + t ^ 2) ^ 2) = 2 / Real.pi * (1 + t ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
      rw [pow_two]; field_simp
    rw [e]
    exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ h1)

lemma integrable_abs_mul_q :
    Integrable (fun t : ℝ => |t| * (2 / (Real.pi * (1 + t ^ 2) ^ 2))) := by
  refine (integrable_inv_one_add_sq.const_mul (2 / Real.pi)).mono' ?_
    (Eventually.of_forall fun t => ?_)
  · exact (by fun_prop :
      Measurable fun t : ℝ => |t| * (2 / (Real.pi * (1 + t ^ 2) ^ 2))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : |t| ≤ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
    have e : |t| * (2 / (Real.pi * (1 + t ^ 2) ^ 2)) =
        2 / Real.pi * (1 + t ^ 2)⁻¹ * (|t| / (1 + t ^ 2)) := by
      field_simp
    rw [e]
    exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ h1 (by positivity))

/-- The integrand `|∑ u_i t_i| ∏ 2/(π(1+t_i²)²)` is integrable on `ℝ^d`. -/
lemma integrable_tDensity_integrand (u : Fin d → ℝ) :
    Integrable (fun t : Fin d → ℝ =>
      |∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2))) :=
  integrable_abs_linear_mul_prod (g := fun _ t => 2 / (Real.pi * (1 + t ^ 2) ^ 2))
    (fun _ => integrable_q) (fun _ => integrable_abs_mul_q) u

/-- The probabilistic core of paper Lemma 2.4: for the product density
`∏_i 2/(π(1+t_i²)²)` on `ℝ^d`, `𝔼|∑ u_i T_i| ≤ √(2/π) ‖u‖₂`. -/
theorem integral_abs_linear_tDensity_le (u : Fin d → ℝ) :
    ∫ t : Fin d → ℝ, |∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2)) ≤
      Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i, u i ^ 2) :=
  integral_abs_linear_tDensity_le_of_integrable u (integrable_tDensity_integrand u)

/-- `∫ |∂_u ρ_C| = (π/C) 𝔼|∑ u_i T_i|` (the change of variables `T_i = tan(π x_i/(2C))`). -/
theorem lintegral_fderiv_cubeDensity {C : ℝ} (hC : 0 < C) (u : Euc d) :
    ∫⁻ x, ‖fderiv ℝ (cubeDensity d C) x u‖ₑ =
      ENNReal.ofReal ((Real.pi / C) *
        ∫ t : Fin d → ℝ, |∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2))) := by
  have hpt : ∀ x, ‖fderiv ℝ (cubeDensity d C) x u‖ₑ = ENNReal.ofReal ((Real.pi / C) *
      cubeDensity d C x * |∑ i, u i * Real.tan (Real.pi * x i / (2 * C))|) := by
    intro x
    rw [fderiv_cubeDensity_apply hC, Real.enorm_eq_ofReal_abs, abs_mul, abs_mul, abs_neg,
      abs_of_pos (by positivity : 0 < Real.pi / C), abs_of_nonneg (cubeDensity_nonneg hC x)]
  simp_rw [hpt]
  rw [lintegral_euc_eq_lintegral_pi]
  beta_reduce
  set φ : Fin d → ℝ → ℝ := fun _ t => 2 * C / Real.pi * Real.arctan t with hφ
  set φ' : Fin d → ℝ → ℝ := fun _ t => 2 * C / Real.pi * (1 / (1 + t ^ 2)) with hφ'
  have hder : ∀ i t, HasDerivAt (φ i) (φ' i t) t := fun i t =>
    (Real.hasDerivAt_arctan t).const_mul _
  have hinj : ∀ i, Function.Injective (φ i) := fun i a b hab =>
    Real.arctan_injective (mul_left_cancel₀ (by positivity) hab)
  have hφeval : ∀ t : ℝ, Real.pi * (2 * C / Real.pi * Real.arctan t) / (2 * C) = Real.arctan t := by
    intro t; field_simp
  have hsupp : Function.support (fun y : Fin d → ℝ => ENNReal.ofReal ((Real.pi / C) *
      cubeDensity d C (WithLp.toLp 2 y) * |∑ i, u i * Real.tan (Real.pi * y i / (2 * C))|)) ⊆
      range (piMap φ) := by
    intro y hy
    rw [Function.mem_support] at hy
    have hmem : WithLp.toLp 2 y ∈ cube d C := by
      by_contra h
      apply hy
      rw [cubeDensity, indicator_of_notMem h]; simp
    refine ⟨fun i => Real.tan (Real.pi * y i / (2 * C)), ?_⟩
    funext i
    simp only [piMap, φ]
    have hi : |y i| < C := hmem i
    obtain ⟨h1, h2⟩ := pi_mul_div_mem_Ioo hC hi
    rw [Real.arctan_tan h1 h2]
    field_simp
  rw [← setLIntegral_eq_of_support_subset hsupp, lintegral_piMap_image hder hinj]
  have hpt2 : ∀ t : Fin d → ℝ, ENNReal.ofReal |∏ i, φ' i (t i)| *
      ENNReal.ofReal ((Real.pi / C) * cubeDensity d C (WithLp.toLp 2 (piMap φ t)) *
        |∑ i, u i * Real.tan (Real.pi * piMap φ t i / (2 * C))|) =
      ENNReal.ofReal ((Real.pi / C) *
        (|∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2)))) := by
    intro t
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    have htan : ∀ i, Real.tan (Real.pi * piMap φ t i / (2 * C)) = t i := by
      intro i; simp only [piMap, φ]; rw [hφeval, Real.tan_arctan]
    have hρ : cubeDensity d C (WithLp.toLp 2 (piMap φ t)) = (C ^ d)⁻¹ * ∏ i, 1 / (1 + t i ^ 2) := by
      rw [cubeDensity_eq hC]; congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [piMap, φ]
      have hlt : |2 * C / Real.pi * Real.arctan (t i)| < C := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * C / Real.pi)]
        have : |Real.arctan (t i)| < Real.pi / 2 :=
          abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
        calc 2 * C / Real.pi * |Real.arctan (t i)| < 2 * C / Real.pi * (Real.pi / 2) :=
              mul_lt_mul_of_pos_left this (by positivity)
          _ = C := by field_simp
      rw [bump_of_lt hlt, hφeval, Real.cos_sq_arctan]
    simp_rw [htan]
    rw [hρ, abs_of_nonneg (Finset.prod_nonneg fun i _ => by simp only [φ']; positivity)]
    have hCd : (C ^ d)⁻¹ = ∏ _i : Fin d, C⁻¹ := by simp [Finset.prod_const]
    have hprod : (∏ i, φ' i (t i)) * ((∏ _i : Fin d, C⁻¹) * ∏ i, 1 / (1 + t i ^ 2)) =
        ∏ i, 2 / (Real.pi * (1 + t i ^ 2) ^ 2) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [φ']; field_simp
    rw [hCd]
    calc (∏ i, φ' i (t i)) * (Real.pi / C * ((∏ _i : Fin d, C⁻¹) * ∏ i, 1 / (1 + t i ^ 2)) *
          |∑ i, u i * t i|)
        = (∏ i, φ' i (t i)) * ((∏ _i : Fin d, C⁻¹) * ∏ i, 1 / (1 + t i ^ 2)) *
          (Real.pi / C * |∑ i, u i * t i|) := by ring
      _ = _ := by rw [hprod]; ring
  simp_rw [hpt2]
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul]
  · exact (integrable_tDensity_integrand u).const_mul _
  · exact Eventually.of_forall fun t => by positivity

/-- Paper Lemma 2.4, (2.14): `V_u ρ_C ≤ (√(2π)/C) ‖u‖₂`. -/
theorem dirVar_cubeDensity_le {C : ℝ} (hC : 0 < C) (u : Euc d) :
    dirVar u (cubeDensity d C) ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi) / C * ‖u‖) := by
  refine (dirVar_le_lintegral_fderiv u _ (cubeDensity_contDiff hC)
    (cubeDensity_hasCompactSupport hC)).trans ?_
  rw [lintegral_fderiv_cubeDensity hC]
  apply ENNReal.ofReal_le_ofReal
  have h := integral_abs_linear_tDensity_le (fun i => u i)
  have hπ : Real.pi * Real.sqrt (2 / Real.pi) = Real.sqrt (2 * Real.pi) := by
    calc Real.pi * Real.sqrt (2 / Real.pi)
        = Real.sqrt (Real.pi ^ 2) * Real.sqrt (2 / Real.pi) := by
          rw [Real.sqrt_sq Real.pi_pos.le]
      _ = Real.sqrt (Real.pi ^ 2 * (2 / Real.pi)) := (Real.sqrt_mul (sq_nonneg _) _).symm
      _ = Real.sqrt (2 * Real.pi) := by
          congr 1
          rw [pow_two, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ Real.pi_pos.ne',
            mul_comm]
  calc Real.pi / C * ∫ t : Fin d → ℝ, |∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2))
      ≤ Real.pi / C * (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i, u i ^ 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = Real.sqrt (2 * Real.pi) / C * ‖u‖ := by
        rw [EuclideanSpace.norm_eq]
        simp only [Real.norm_eq_abs, sq_abs]
        rw [← hπ]
        ring

/-- Paper Lemma 2.4 packaged as the invariant: `(−C,C)^d` admits a density with
`κ = √(2π)/C`. -/
theorem hasAdmissible_cube {C : ℝ} (hC : 0 < C) :
    HasAdmissible (cube d C) (Real.sqrt (2 * Real.pi) / C) :=
  ⟨cubeDensity d C, cubeDensity_memP hC, fun u => dirVar_cubeDensity_le hC u⟩

end Komlos
