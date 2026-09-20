import Komlos.Defs

/-!
# Auxiliary material for the cube density (paper Lemma 2.4)

Helper lemmas for `Komlos.CubeDensity`:

* the one-dimensional profile `bump C s = cos²(π s/(2C)) 𝟙_{|s|<C}` (via clamping), its
  derivative `bump'`, the `C¹` property and `∫ bump C = C`;
* a coordinatewise change of variables on `Fin d → ℝ` (`piMap`, diagonal Jacobian);
* transfer of integrals between `Euc d` and `Fin d → ℝ`, and the closed cube is compact;
* product measures with product densities (`pi_withDensity_prod`, ported from a reference
  project), the Gaussian law of a linear form under a product Gaussian
  (`integral_abs_linear_pi_gaussianReal`), `𝔼|N(0,v)| = √(2v/π)`;
* the Gamma integrals `∫_0^∞ s e^{-rs} = r^{-2}`, `∫_0^∞ √s e^{-s/2} = √(2π)`,
  `∫_0^∞ s^{-1/2} e^{-s/2} = √(2π)`;
* integrability of `|∑ u_i t_i| ∏_i g_i(t_i)` from one-dimensional first moments;
* the Gaussian scale mixture `2/(π(1+t²)²) = ∫_0^∞ (s/2π) e^{-(1+t²)s/2} ds`
  (`mixKernel`, `chiDensity`) and the probabilistic core of paper Lemma 2.4,
  `integral_abs_linear_tDensity_le_of_integrable`: `𝔼|∑ u_i T_i| ≤ √(2/π) ‖u‖₂`
  (conditioning on the scales, `𝔼|N(0,σ²)| = σ√(2/π)`, and AM–GM in place of Jensen).
-/

open MeasureTheory Set Filter Topology ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Komlos

variable {d : ℕ}

/-! ### The one-dimensional profile -/

/-- Clamp `s` to `[-C, C]`. -/
noncomputable def clampC (C s : ℝ) : ℝ := max (-C) (min C s)

lemma clampC_of_abs_lt {C s : ℝ} (h : |s| < C) : clampC C s = s := by
  rw [abs_lt] at h; unfold clampC; rw [min_eq_right h.2.le, max_eq_right h.1.le]

lemma clampC_of_le {C s : ℝ} (hC : 0 < C) (h : C ≤ s) : clampC C s = C := by
  unfold clampC; rw [min_eq_left h, max_eq_right (neg_le_self hC.le)]

lemma clampC_of_ge {C s : ℝ} (h : s ≤ -C) : clampC C s = -C := by
  unfold clampC; rw [max_eq_left (le_trans (min_le_right _ _) h)]

lemma continuous_clampC (C : ℝ) : Continuous (clampC C) := by
  unfold clampC; fun_prop

/-- The one-dimensional profile `g_C(s) = cos²(π s/(2C)) 𝟙_{|s|<C}` (paper Lemma 2.4),
written via clamping so that continuity is immediate. -/
noncomputable def bump (C s : ℝ) : ℝ := Real.cos (Real.pi * clampC C s / (2 * C)) ^ 2

/-- Its derivative `-(π/C) cos(π s/(2C)) sin(π s/(2C)) 𝟙_{|s|<C}`. -/
noncomputable def bump' (C s : ℝ) : ℝ :=
  -(Real.pi / C) *
    (Real.cos (Real.pi * clampC C s / (2 * C)) * Real.sin (Real.pi * clampC C s / (2 * C)))

lemma bump_of_lt {C s : ℝ} (h : |s| < C) : bump C s = Real.cos (Real.pi * s / (2 * C)) ^ 2 := by
  rw [bump, clampC_of_abs_lt h]

lemma bump'_of_lt {C s : ℝ} (h : |s| < C) :
    bump' C s = -(Real.pi / C) * (Real.cos (Real.pi * s / (2 * C)) * Real.sin (Real.pi * s / (2 * C))) := by
  rw [bump', clampC_of_abs_lt h]

lemma pi_mul_div_two_mul_self {C : ℝ} (hC : C ≠ 0) : Real.pi * C / (2 * C) = Real.pi / 2 := by
  field_simp

lemma bump_of_not_lt {C s : ℝ} (hC : 0 < C) (h : ¬ |s| < C) : bump C s = 0 := by
  rw [not_lt, le_abs] at h
  rcases h with h | h
  · rw [bump, clampC_of_le hC h, pi_mul_div_two_mul_self hC.ne']; simp
  · rw [bump, clampC_of_ge (by linarith)]
    rw [show Real.pi * -C / (2 * C) = -(Real.pi / 2) by field_simp]; simp

lemma bump'_of_not_lt {C s : ℝ} (hC : 0 < C) (h : ¬ |s| < C) : bump' C s = 0 := by
  rw [not_lt, le_abs] at h
  rcases h with h | h
  · rw [bump', clampC_of_le hC h, pi_mul_div_two_mul_self hC.ne']; simp
  · rw [bump', clampC_of_ge (by linarith)]
    rw [show Real.pi * -C / (2 * C) = -(Real.pi / 2) by field_simp]; simp

lemma bump_nonneg (C s : ℝ) : 0 ≤ bump C s := by unfold bump; positivity

lemma continuous_bump (C : ℝ) : Continuous (bump C) := by
  unfold bump; have := continuous_clampC C; fun_prop

lemma continuous_bump' (C : ℝ) : Continuous (bump' C) := by
  unfold bump'; have := continuous_clampC C; fun_prop

lemma bump_neg {C : ℝ} (hC : 0 < C) (s : ℝ) : bump C (-s) = bump C s := by
  by_cases h : |s| < C
  · rw [bump_of_lt h, bump_of_lt (by rwa [abs_neg]),
      show Real.pi * -s / (2 * C) = -(Real.pi * s / (2 * C)) by ring, Real.cos_neg]
  · rw [bump_of_not_lt hC h, bump_of_not_lt hC (by rwa [abs_neg])]

lemma hasDerivAt_cosSq {C : ℝ} (hC : C ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => Real.cos (Real.pi * s / (2 * C)) ^ 2)
      (-(Real.pi / C) * (Real.cos (Real.pi * s / (2 * C)) * Real.sin (Real.pi * s / (2 * C)))) s := by
  have h1 : HasDerivAt (fun s => Real.pi * s / (2 * C)) (Real.pi / (2 * C)) s := by
    simpa using ((hasDerivAt_id s).const_mul Real.pi).div_const (2 * C)
  have h2 := ((Real.hasDerivAt_cos _).comp s h1).pow 2
  refine h2.congr_deriv ?_
  norm_num
  field_simp

/-- Derivative of the profile at a boundary point `C`: the `HasDerivWithinAt` gluing. -/
lemma hasDerivAt_bump_right {C : ℝ} (hC : 0 < C) : HasDerivAt (bump C) 0 C := by
  have hIci : HasDerivWithinAt (bump C) 0 (Ici C) C := by
    refine (hasDerivWithinAt_const C (Ici C) (0 : ℝ)).congr (fun x hx => ?_) ?_
    · exact bump_of_not_lt hC (not_lt.2 (le_trans hx (le_abs_self x)))
    · exact bump_of_not_lt hC (by rw [abs_of_pos hC]; exact lt_irrefl _)
  have hIic : HasDerivWithinAt (bump C) 0 (Iic C) C := by
    have hd := (hasDerivAt_cosSq hC.ne' C).hasDerivWithinAt (s := Iic C)
    rw [pi_mul_div_two_mul_self hC.ne', Real.cos_pi_div_two, zero_mul, mul_zero] at hd
    refine hd.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Ioc_mem_nhdsLE (by linarith : -C < C)] with x hx
      rcases hx.2.lt_or_eq with h | h
      · exact bump_of_lt (abs_lt.2 ⟨hx.1, h⟩)
      · subst h
        rw [bump_of_not_lt hC (by rw [abs_of_pos hC]; exact lt_irrefl _),
          pi_mul_div_two_mul_self hC.ne', Real.cos_pi_div_two]; simp
    · rw [bump_of_not_lt hC (by rw [abs_of_pos hC]; exact lt_irrefl _),
        pi_mul_div_two_mul_self hC.ne', Real.cos_pi_div_two]; simp
  have := hIic.union hIci
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

lemma hasDerivAt_bump {C : ℝ} (hC : 0 < C) (s : ℝ) : HasDerivAt (bump C) (bump' C s) s := by
  rcases lt_trichotomy |s| C with h | h | h
  · have hev : bump C =ᶠ[𝓝 s] fun s => Real.cos (Real.pi * s / (2 * C)) ^ 2 := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds h] with x hx
      exact bump_of_lt hx
    rw [bump'_of_lt h]
    exact (hasDerivAt_cosSq hC.ne' s).congr_of_eventuallyEq hev
  · rw [bump'_of_not_lt hC h.not_lt]
    rcases (abs_eq hC.le).1 h with rfl | rfl
    · exact hasDerivAt_bump_right hC
    · have h0 : HasDerivAt (bump C) 0 (-(-C)) := by
        rw [neg_neg]; exact hasDerivAt_bump_right hC
      have h1 := h0.comp (-C) (hasDerivAt_neg (-C))
      have h2 : bump C ∘ Neg.neg = bump C := by ext x; simp [bump_neg hC]
      rw [h2, zero_mul] at h1
      exact h1
  · have hev : bump C =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds h] with x hx
      exact bump_of_not_lt hC (not_lt.2 hx.le)
    rw [bump'_of_not_lt hC (not_lt.2 h.le)]
    exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev

lemma contDiff_bump {C : ℝ} (hC : 0 < C) : ContDiff ℝ 1 (bump C) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_bump hC s).differentiableAt, ?_⟩
  have : deriv (bump C) = bump' C := funext fun s => (hasDerivAt_bump hC s).deriv
  rw [this]; exact continuous_bump' C

/-- `∫ g_C = C`. -/
lemma integral_bump {C : ℝ} (hC : 0 < C) : ∫ s, bump C s = C := by
  have h1 : bump C = (Ioo (-C) C).indicator fun s => Real.cos (Real.pi * s / (2 * C)) ^ 2 := by
    ext s
    by_cases h : |s| < C
    · rw [bump_of_lt h, indicator_of_mem (by rwa [mem_Ioo, ← abs_lt])]
    · rw [bump_of_not_lt hC h, indicator_of_notMem (by rwa [mem_Ioo, ← abs_lt])]
  rw [h1, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h2 : ∀ s : ℝ, Real.pi * s / (2 * C) = Real.pi / (2 * C) * s := fun s => by ring
  simp_rw [h2]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) (by positivity),
    integral_cos_sq]
  have h3 : Real.pi / (2 * C) * C = Real.pi / 2 := by field_simp
  have h4 : Real.pi / (2 * C) * -C = -(Real.pi / 2) := by field_simp
  rw [h3, h4]
  simp only [Real.cos_pi_div_two, Real.cos_neg, Real.sin_neg, smul_eq_mul]
  field_simp
  ring


variable {d : ℕ}

/-! ### Coordinatewise change of variables on `Fin d → ℝ` -/

/-- The coordinatewise map `Φ t = (φ i (t i))_i`. -/
def piMap (φ : Fin d → ℝ → ℝ) (t : Fin d → ℝ) : Fin d → ℝ := fun i => φ i (t i)

/-- The diagonal continuous linear map `v ↦ (c i * v i)_i`. -/
noncomputable def diagCLM (c : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => (c i • (1 : ℝ →L[ℝ] ℝ)).comp (ContinuousLinearMap.proj i)

lemma diagCLM_apply (c : Fin d → ℝ) (v : Fin d → ℝ) (i : Fin d) :
    diagCLM c v i = c i * v i := by
  simp [diagCLM]

lemma det_diagCLM (c : Fin d → ℝ) : (diagCLM c).det = ∏ i, c i := by
  rw [diagCLM, ContinuousLinearMap.det_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.det]

lemma hasFDerivAt_piMap {φ φ' : Fin d → ℝ → ℝ} (hφ : ∀ i t, HasDerivAt (φ i) (φ' i t) t)
    (t : Fin d → ℝ) :
    HasFDerivAt (piMap φ) (diagCLM fun i => φ' i (t i)) t := by
  apply hasFDerivAt_pi''
  intro i
  have hp : HasFDerivAt (fun t : Fin d → ℝ => t i)
      (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) t :=
    (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have h := (hφ i (t i)).comp_hasFDerivAt (f := fun t : Fin d → ℝ => t i) t hp
  refine h.congr_fderiv ?_
  ext v
  simp [diagCLM]

lemma injective_piMap {φ : Fin d → ℝ → ℝ} (hinj : ∀ i, Function.Injective (φ i)) :
    Function.Injective (piMap φ) := by
  intro a b hab
  funext i
  exact hinj i (congrFun hab i)

/-- Change of variables for the coordinatewise map (Bochner form). -/
theorem integral_piMap_image {φ φ' : Fin d → ℝ → ℝ} (hφ : ∀ i t, HasDerivAt (φ i) (φ' i t) t)
    (hinj : ∀ i, Function.Injective (φ i)) (g : (Fin d → ℝ) → ℝ) :
    ∫ x in range (piMap φ), g x = ∫ t, |∏ i, φ' i (t i)| * g (piMap φ t) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (Fin d → ℝ))
    MeasurableSet.univ (f := piMap φ) (f' := fun t => diagCLM fun i => φ' i (t i))
    (fun t _ => (hasFDerivAt_piMap hφ t).hasFDerivWithinAt)
    (injective_piMap hinj).injOn g
  rw [image_univ, Measure.restrict_univ] at h
  rw [h]
  congr 1; ext t
  rw [det_diagCLM, smul_eq_mul]

/-- Change of variables for the coordinatewise map (Lebesgue form). -/
theorem lintegral_piMap_image {φ φ' : Fin d → ℝ → ℝ} (hφ : ∀ i t, HasDerivAt (φ i) (φ' i t) t)
    (hinj : ∀ i, Function.Injective (φ i)) (g : (Fin d → ℝ) → ℝ≥0∞) :
    ∫⁻ x in range (piMap φ), g x = ∫⁻ t, ENNReal.ofReal |∏ i, φ' i (t i)| * g (piMap φ t) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (Fin d → ℝ))
    MeasurableSet.univ (f := piMap φ) (f' := fun t => diagCLM fun i => φ' i (t i))
    (fun t _ => (hasFDerivAt_piMap hφ t).hasFDerivWithinAt)
    (injective_piMap hinj).injOn g
  rw [image_univ, Measure.restrict_univ] at h
  rw [h]
  congr 1; ext t
  rw [det_diagCLM]

/-- Integrability transfer for the coordinatewise map. -/
theorem integrableOn_piMap_image_iff {φ φ' : Fin d → ℝ → ℝ}
    (hφ : ∀ i t, HasDerivAt (φ i) (φ' i t) t)
    (hinj : ∀ i, Function.Injective (φ i)) (g : (Fin d → ℝ) → ℝ) :
    IntegrableOn g (range (piMap φ)) ↔
      Integrable (fun t => |∏ i, φ' i (t i)| * g (piMap φ t)) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure (Fin d → ℝ))
    MeasurableSet.univ (f := piMap φ) (f' := fun t => diagCLM fun i => φ' i (t i))
    (fun t _ => (hasFDerivAt_piMap hφ t).hasFDerivWithinAt)
    (injective_piMap hinj).injOn g
  rw [image_univ, integrableOn_univ] at h
  rw [h]
  simp_rw [det_diagCLM, smul_eq_mul]

/-! ### Transfer between `Euc d` and `Fin d → ℝ` -/

lemma integral_euc_eq_integral_pi (f : Euc d → ℝ) :
    ∫ x, f x = ∫ y : Fin d → ℝ, f (WithLp.toLp 2 y) := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]

lemma lintegral_euc_eq_lintegral_pi (f : Euc d → ℝ≥0∞) :
    ∫⁻ x, f x = ∫⁻ y : Fin d → ℝ, f (WithLp.toLp 2 y) := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]


variable {d : ℕ}

/-! ### Product measures with product densities (port of a reference proof) -/

theorem lintegral_fin_prod_eq_prod {n : ℕ} {μ : Fin n → Measure ℝ} [∀ i, SigmaFinite (μ i)]
    {f : Fin n → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have mp := measurePreserving_piFinSuccAbove μ 0
      have h_prod_meas : Measurable fun x : Fin (n + 1) → ℝ => ∏ i, f i (x i) :=
        Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
      have hf0_ae : AEMeasurable (f 0) (μ 0) := (hf 0).aemeasurable
      have h_tail_ae :
          AEMeasurable (fun y : Fin n → ℝ => ∏ i, f i.succ (y i))
            (Measure.pi (fun i => μ i.succ)) :=
        (Finset.measurable_prod _ (fun i _ =>
          (hf _).comp (measurable_pi_apply i))).aemeasurable
      have ih' : ∫⁻ y : Fin n → ℝ, ∏ i, f i.succ (y i) ∂Measure.pi (fun i : Fin n => μ i.succ)
                 = ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ :=
        ih (μ := fun i : Fin n => μ i.succ) (f := fun i : Fin n => f i.succ) (fun i => hf _)
      calc ∫⁻ x : Fin (n + 1) → ℝ, ∏ i, f i (x i) ∂Measure.pi μ
          = ∫⁻ z : ℝ × (Fin n → ℝ), f 0 z.1 * ∏ i, f i.succ (z.2 i)
              ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
            rw [← mp.symm.lintegral_comp h_prod_meas]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
              * ∫⁻ y : Fin n → ℝ, (∏ i : Fin n, f i.succ (y i))
                  ∂Measure.pi (fun i : Fin n => μ i.succ) :=
            lintegral_prod_mul hf0_ae h_tail_ae
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by rw [ih']
        _ = ∏ i, ∫⁻ x, f i x ∂μ i := by
            rw [← Fin.prod_univ_succ (fun i : Fin (n + 1) => ∫⁻ x, f i x ∂μ i)]

theorem pi_withDensity_prod {μ : Fin d → Measure ℝ} [∀ i, SigmaFinite (μ i)]
    {f : Fin d → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
      = Measure.pi (fun i => (μ i).withDensity (f i)) := by
  classical
  refine (Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) fun s hs => ?_).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h_indic : ∀ x : Fin d → ℝ,
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x
        = ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (hx i (Set.mem_univ _))]
    · rw [Set.indicator_of_notMem hx]
      rw [Set.mem_univ_pi] at hx
      simp only [not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  simp_rw [h_indic]
  rw [lintegral_fin_prod_eq_prod (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [lintegral_indicator (hs i), ← withDensity_apply _ (hs i)]

/-! ### Product Gaussians -/

instance isGaussian_pi_gaussianReal (v : Fin d → ℝ≥0) :
    IsGaussian (Measure.pi fun i => gaussianReal 0 (v i)) := by
  have h : HasGaussianLaw (fun ω : Fin d → ℝ => (fun i => ω i))
      (Measure.pi fun i => gaussianReal 0 (v i)) := by
    refine iIndepFun.hasGaussianLaw (Ω := Fin d → ℝ) (E := fun _ => ℝ)
      (X := fun (i : Fin d) (ω : Fin d → ℝ) => ω i) (fun i => ?_) ?_
    · exact ⟨by rw [(measurePreserving_eval _ i).map_eq]; infer_instance⟩
    · exact iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have := h.isGaussian_map
  rwa [Measure.map_id'] at this

/-- `𝔼|N(0, v)| = √(2v/π)`. -/
lemma integral_abs_gaussianReal (v : ℝ≥0) :
    ∫ x, |x| ∂gaussianReal 0 v = Real.sqrt (2 * v / Real.pi) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [gaussianPDFReal_def, smul_eq_mul, sub_zero]
  have hv' : (0 : ℝ) < v := by positivity
  have hb : (0 : ℝ) < 1 / (2 * v) := by positivity
  -- ∫ x, |x| exp(-b x²) = 1/b with b = 1/(2v)
  have key : ∫ x : ℝ, |x| * rexp (-(1 / (2 * v)) * x ^ 2) = 2 * v := by
    have h := integral_comp_abs (f := fun x => x * rexp (-(1 / (2 * v)) * x ^ 2))
    simp only [sq_abs] at h
    rw [h]
    have hc := integral_mul_cexp_neg_mul_sq (b := ((1 / (2 * v) : ℝ) : ℂ)) (by simpa using hb)
    have hre : ∫ r : ℝ in Ioi 0, (r : ℂ) * Complex.exp (-((1 / (2 * v) : ℝ) : ℂ) * (r : ℂ) ^ 2)
        = ((∫ r : ℝ in Ioi 0, r * rexp (-(1 / (2 * v)) * r ^ 2) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1; ext r
      simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rw [hre] at hc
    have hc' : ∫ r : ℝ in Ioi 0, r * rexp (-(1 / (2 * v)) * r ^ 2) = v := by
      have h2 : (2 * ((1 / (2 * (v : ℝ)) : ℝ) : ℂ))⁻¹ = ((v : ℝ) : ℂ) := by
        rw [inv_eq_iff_eq_inv]; push_cast
        rw [mul_one_div, div_mul_eq_div_div, div_self (two_ne_zero' ℂ), one_div]
      rw [h2] at hc
      exact_mod_cast hc
    rw [hc']
  calc ∫ x : ℝ, (Real.sqrt (2 * Real.pi * v))⁻¹ * rexp (-x ^ 2 / (2 * v)) * |x|
      = (Real.sqrt (2 * Real.pi * v))⁻¹ * ∫ x : ℝ, |x| * rexp (-(1 / (2 * v)) * x ^ 2) := by
        rw [← integral_const_mul]; congr 1; ext x; ring_nf
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ * (2 * v) := by rw [key]
    _ = Real.sqrt (2 * v / Real.pi) := by
        rw [show 2 * (v : ℝ) / Real.pi = (2 * v) ^ 2 / (2 * Real.pi * v) by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring,
          Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity), inv_mul_eq_div]

/-- The law of the linear form `∑ u_i t_i` under the product Gaussian. -/
lemma integral_abs_linear_pi_gaussianReal (u : Fin d → ℝ) (v : Fin d → ℝ≥0) :
    ∫ t, |∑ i, u i * t i| ∂(Measure.pi fun i => gaussianReal 0 (v i)) =
      Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i, u i ^ 2 * v i) := by
  let L : StrongDual ℝ (Fin d → ℝ) := ∑ i, u i • ContinuousLinearMap.proj i
  have hL : ∀ t, L t = ∑ i, u i * t i := by intro t; simp [L]
  have h1 : ∫ t, |∑ i, u i * t i| ∂(Measure.pi fun i => gaussianReal 0 (v i)) =
      ∫ x, |x| ∂((Measure.pi fun i => gaussianReal 0 (v i)).map L) := by
    rw [integral_map L.continuous.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|) _)]
    simp_rw [hL]
  have hmean : ∫ t, L t ∂(Measure.pi fun i => gaussianReal 0 (v i)) = 0 := by
    simp_rw [hL]
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul, integral_eval, integral_id_gaussianReal, mul_zero,
        Finset.sum_const_zero]
    · intro i _
      exact (integrable_eval IsGaussian.integrable_id).const_mul _
  have hvar : Var[L; Measure.pi fun i => gaussianReal 0 (v i)] = ∑ i, u i ^ 2 * v i := by
    have : ⇑L = ∑ i, fun t : Fin d → ℝ => (fun x : ℝ => u i * x) (t i) := by
      ext t; simp [L, Finset.sum_apply]
    rw [this, variance_sum_pi]
    · change ∑ i, Var[fun x ↦ u i * (id x); gaussianReal 0 (v i)] = _
      simp_rw [variance_const_mul, variance_id_gaussianReal]
    · exact fun i ↦ IsGaussian.memLp_two_id.const_mul _
  have hnn : 0 ≤ ∑ i, u i ^ 2 * v i := Finset.sum_nonneg fun i _ => by positivity
  rw [h1, IsGaussian.map_eq_gaussianReal L, hmean, hvar, integral_abs_gaussianReal,
    Real.coe_toNNReal _ hnn, show 2 * (∑ i, u i ^ 2 * v i) / Real.pi
      = 2 / Real.pi * ∑ i, u i ^ 2 * v i by ring, Real.sqrt_mul (by positivity)]

/-! ### Gamma integrals -/

lemma integral_mul_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ s in Ioi 0, s * rexp (-(r * s)) = 1 / r ^ 2 := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.Gamma_two, mul_one,
    Real.rpow_two] at h
  rw [h]; ring

lemma integral_sqrt_mul_exp_neg_half_Ioi :
    ∫ s in Ioi 0, Real.sqrt s * rexp (-(1 / 2 * s)) = Real.sqrt (2 * Real.pi) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 3 / 2) (by norm_num) (r := 1 / 2)
    (by norm_num)
  simp_rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at h
  rw [h, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, one_div_one_div, Real.rpow_add two_pos, Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_mul two_pos.le]
  ring

lemma integral_inv_sqrt_mul_exp_neg_half_Ioi :
    ∫ s in Ioi 0, (Real.sqrt s)⁻¹ * rexp (-(1 / 2 * s)) = Real.sqrt (2 * Real.pi) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (by norm_num) (r := 1 / 2)
    (by norm_num)
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] at h
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * rexp (-(1 / 2 * s)))
    (fun s hs => by rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hs)]), h,
    one_div_one_div, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, Real.sqrt_mul two_pos.le]

/-- Integrability of `s^(a-1) e^{-rs}` on `(0, ∞)`. -/
lemma integrableOn_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => s ^ (a - 1) * rexp (-(r * s))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r)
    (by linarith) one_pos hr
  simpa [Real.rpow_one] using this


/-! ### Geometry of the cube in `Euc d` -/

lemma norm_le_of_forall_abs_le {x : Euc d} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, |x i| ≤ C) :
    ‖x‖ ≤ Real.sqrt d * C := by
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin d, C ^ 2) := by
        apply Real.sqrt_le_sqrt; apply Finset.sum_le_sum; intro i _
        rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = Real.sqrt d * C := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hC]

/-- The closed cube is compact. -/
lemma isCompact_closedCube {C : ℝ} (hC : 0 ≤ C) : IsCompact {x : Euc d | ∀ i, |x i| ≤ C} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : {x : Euc d | ∀ i, |x i| ≤ C} = ⋂ i, {x : Euc d | |x i| ≤ C} := by ext; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  · rw [isBounded_iff_forall_norm_le]
    exact ⟨Real.sqrt d * C, fun x hx => norm_le_of_forall_abs_le hC hx⟩

/-! ### Integrability of `|∑ u_i t_i| ∏ g_i(t_i)` -/

/-- Integrability of `|∑ u_i t_i| ∏ g_i(t_i)` on `ℝ^d` from one-dimensional first moments. -/
theorem integrable_abs_linear_mul_prod {g : Fin d → ℝ → ℝ} (hg : ∀ i, Integrable (g i))
    (hg' : ∀ i, Integrable (fun x => |x| * g i x)) (u : Fin d → ℝ) :
    Integrable (fun t : Fin d → ℝ => |∑ i, u i * t i| * ∏ i, g i (t i)) := by
  classical
  let h : Fin d → Fin d → ℝ → ℝ := fun i j x => (if i = j then |x| else 1) * |g j x|
  have hh : ∀ i j, Integrable (h i j) := by
    intro i j
    by_cases hij : i = j
    · simp only [h, hij, if_true]
      refine (hg' j).abs.congr (Eventually.of_forall fun x => ?_)
      simp [abs_mul, abs_abs]
    · simp only [h, hij, if_false, one_mul]
      exact (hg j).abs
  have hB : Integrable (fun t : Fin d → ℝ => ∑ i, |u i| * ∏ j, h i j (t j)) := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact (Integrable.fintype_prod (f := fun j => h i j) fun j => hh i j).const_mul _
  refine hB.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have h1 : AEStronglyMeasurable (fun t : Fin d → ℝ => |∑ i, u i * t i|) volume :=
      (by fun_prop : Continuous fun t : Fin d → ℝ => |∑ i, u i * t i|).aestronglyMeasurable
    exact h1.mul (Integrable.fintype_prod (f := fun i => g i) hg).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_abs, Finset.abs_prod]
    calc |∑ i, u i * t i| * ∏ i, |g i (t i)|
        ≤ (∑ i, |u i| * |t i|) * ∏ i, |g i (t i)| := by
          apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun i _ => abs_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          simp [abs_mul]
      _ = ∑ i, |u i| * ∏ j, h i j (t j) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [h]
          rw [Finset.prod_mul_distrib, Finset.prod_ite_eq, if_pos (Finset.mem_univ i)]
          ring

/-! ### Finiteness of `∫ |∂_u f|` for `C¹` compactly supported `f` -/

lemma lintegral_enorm_fderiv_apply_lt_top {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (u : Euc d) :
    ∫⁻ x, ‖fderiv ℝ f x u‖ₑ < ⊤ := by
  have hc : Continuous fun x => fderiv ℝ f x u :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs : HasCompactSupport fun x => fderiv ℝ f x u := hsupp.fderiv_apply ℝ u
  exact (hc.integrable_of_hasCompactSupport hs).hasFiniteIntegral

/-! ### The Gamma mixture and the Gaussian scale-mixture bound (paper Lemma 2.4) -/

/-! ### The Gamma mixture -/

/-- The mixture kernel `k(s,t) = (2π)⁻¹ s e^{-(1+t²)s/2} 𝟙_{s>0}`. -/
noncomputable def mixKernel (s t : ℝ) : ℝ :=
  (Ioi 0).indicator (fun s => (2 * Real.pi)⁻¹ * (s * Real.exp (-((1 + t ^ 2) / 2 * s)))) s

/-- The `χ²₃`-type density `γ(s) = √s e^{-s/2}/√(2π) 𝟙_{s>0}`. -/
noncomputable def chiDensity (s : ℝ) : ℝ :=
  (Ioi 0).indicator (fun s => Real.sqrt s * Real.exp (-(1 / 2 * s)) / Real.sqrt (2 * Real.pi)) s

lemma mixKernel_nonneg (s t : ℝ) : 0 ≤ mixKernel s t := by
  unfold mixKernel; apply indicator_nonneg; intro s hs; have : 0 < s := hs; positivity

lemma chiDensity_nonneg (s : ℝ) : 0 ≤ chiDensity s := by
  unfold chiDensity; apply indicator_nonneg; intro s hs; have : 0 < s := hs; positivity

lemma mixKernel_of_nonpos {s : ℝ} (hs : s ≤ 0) (t : ℝ) : mixKernel s t = 0 := by
  unfold mixKernel; rw [indicator_of_notMem]; simpa using hs

lemma chiDensity_of_nonpos {s : ℝ} (hs : s ≤ 0) : chiDensity s = 0 := by
  unfold chiDensity; rw [indicator_of_notMem]; simpa using hs

lemma integral_mixKernel (t : ℝ) : ∫ s, mixKernel s t = 2 / (Real.pi * (1 + t ^ 2) ^ 2) := by
  unfold mixKernel
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_mul_exp_neg_mul_Ioi (by positivity : 0 < (1 + t ^ 2) / 2)]
  field_simp

lemma integrable_mixKernel (t : ℝ) : Integrable (fun s => mixKernel s t) := by
  unfold mixKernel
  rw [integrable_indicator_iff measurableSet_Ioi]
  have := integrableOn_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num)
    (r := (1 + t ^ 2) / 2) (by positivity)
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at this
  exact this.const_mul _

lemma measurable_mixKernel : Measurable (fun p : ℝ × ℝ => mixKernel p.1 p.2) := by
  unfold mixKernel
  simp only [Set.indicator_apply, mem_Ioi]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  fun_prop

lemma mixKernel_eq_gaussian (s t : ℝ) :
    mixKernel s t = chiDensity s * gaussianPDFReal 0 (Real.toNNReal (1 / s)) t := by
  unfold mixKernel chiDensity
  by_cases hs : s ∈ Ioi 0
  · rw [indicator_of_mem hs, indicator_of_mem hs, gaussianPDFReal_def]
    simp only [sub_zero]
    have hs' : 0 < s := hs
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [show -((1 + t ^ 2) / 2 * s) = -(1 / 2 * s) + -t ^ 2 / (2 * (1 / s)) by
      field_simp; ring, Real.exp_add]
    have h1 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
    have h2 : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have h3 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs'.le
    have h4 : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
      Real.mul_self_sqrt (by positivity)
    have h5 : Real.sqrt (2 * Real.pi * (1 / s)) = Real.sqrt (2 * Real.pi) / Real.sqrt s := by
      rw [Real.sqrt_mul' _ (by positivity), one_div, Real.sqrt_inv, div_eq_mul_inv]
    have key : ∀ E1 E2 : ℝ, Real.sqrt s * E1 / Real.sqrt (2 * Real.pi) *
        (Real.sqrt s / Real.sqrt (2 * Real.pi) * E2) = (2 * Real.pi)⁻¹ * (s * (E1 * E2)) := by
      intro E1 E2
      rw [show Real.sqrt s * E1 / Real.sqrt (2 * Real.pi) *
          (Real.sqrt s / Real.sqrt (2 * Real.pi) * E2) =
          (Real.sqrt s * Real.sqrt s) * (E1 * E2) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) by ring, h3, h4]
      ring
    rw [h5, inv_div, key]
  · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_mul]

lemma chiDensity_div_eq (s : ℝ) :
    chiDensity s / s = (Ioi 0).indicator
      (fun s => (Real.sqrt s)⁻¹ * Real.exp (-(1 / 2 * s)) * (Real.sqrt (2 * Real.pi))⁻¹) s := by
  unfold chiDensity
  by_cases hs : s ∈ Ioi 0
  · rw [indicator_of_mem hs, indicator_of_mem hs]
    rw [show Real.sqrt s * Real.exp (-(1 / 2 * s)) / Real.sqrt (2 * Real.pi) / s =
      (Real.sqrt s / s) * (Real.exp (-(1 / 2 * s)) / Real.sqrt (2 * Real.pi)) by ring,
      Real.sqrt_div_self', one_div]
    ring
  · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_div]

lemma integral_chiDensity : ∫ s, chiDensity s = 1 := by
  unfold chiDensity
  rw [integral_indicator measurableSet_Ioi, integral_div, integral_sqrt_mul_exp_neg_half_Ioi,
    div_self (by positivity)]

lemma integral_chiDensity_div : ∫ s, chiDensity s / s = 1 := by
  simp_rw [chiDensity_div_eq]
  rw [integral_indicator measurableSet_Ioi, integral_mul_const,
    integral_inv_sqrt_mul_exp_neg_half_Ioi, mul_inv_cancel₀ (by positivity)]

lemma integrable_chiDensity : Integrable chiDensity := by
  unfold chiDensity
  rw [integrable_indicator_iff measurableSet_Ioi]
  have := integrableOn_rpow_mul_exp_neg_mul_Ioi (a := 3 / 2) (by norm_num) (r := 1 / 2)
    (by norm_num)
  simp_rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at this
  exact this.div_const _

lemma integrable_chiDensity_div : Integrable (fun s => chiDensity s / s) := by
  simp_rw [chiDensity_div_eq]
  rw [integrable_indicator_iff measurableSet_Ioi]
  have := integrableOn_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (by norm_num) (r := 1 / 2)
    (by norm_num)
  refine (this.congr_fun (fun s hs => ?_) measurableSet_Ioi).mul_const _
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg (le_of_lt hs),
    ← Real.sqrt_eq_rpow]

lemma measurable_mixKernel_comp {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => mixKernel (f a) (g a) := by
  unfold mixKernel
  simp only [Set.indicator_apply, mem_Ioi]
  refine Measurable.ite (measurableSet_lt measurable_const hf) ?_ measurable_const
  fun_prop

lemma measurable_mixIntegrand (u : Fin d → ℝ) :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      |∑ i, u i * p.1 i| * ∏ i, mixKernel (p.2 i) (p.1 i) := by
  have h1 : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => |∑ i, u i * p.1 i| :=
    (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).abs
  refine h1.mul (Finset.measurable_prod _ fun i _ => ?_)
  exact measurable_mixKernel_comp ((measurable_pi_apply i).comp measurable_snd)
    ((measurable_pi_apply i).comp measurable_fst)

lemma integrable_prod_mixKernel (t : Fin d → ℝ) :
    Integrable (fun s : Fin d → ℝ => ∏ i, mixKernel (s i) (t i)) volume :=
  Integrable.fintype_prod (f := fun i s => mixKernel s (t i)) fun i => integrable_mixKernel (t i)

/-! ### The Gaussian evaluation -/

/-- Lebesgue form of `integral_abs_linear_pi_gaussianReal`. -/
lemma integral_abs_linear_prod_gaussianPDFReal (u : Fin d → ℝ) (v : Fin d → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) :
    ∫ t : Fin d → ℝ, |∑ i, u i * t i| * ∏ i, gaussianPDFReal 0 (v i) (t i) =
      Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i, u i ^ 2 * v i) := by
  rw [← integral_abs_linear_pi_gaussianReal]
  have : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 (v i))) :=
    fun i => by rw [← gaussianReal_of_var_ne_zero _ (hv i)]; infer_instance
  have hpi : (Measure.pi fun i => gaussianReal 0 (v i)) =
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).withDensity
        (fun t => ∏ i, gaussianPDF 0 (v i) (t i)) := by
    rw [pi_withDensity_prod (fun i => measurable_gaussianPDF _ _)]
    congr 1; funext i
    exact gaussianReal_of_var_ne_zero _ (hv i)
  have hm : Measurable (fun t : Fin d → ℝ => ∏ i, gaussianPDF 0 (v i) (t i)) :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF _ _).comp (measurable_pi_apply i)
  rw [hpi, integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun t => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)]
  congr 1; ext t
  simp only [gaussianPDF, smul_eq_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _), mul_comm]

lemma integral_abs_linear_mixKernel (u : Fin d → ℝ) (s : Fin d → ℝ) :
    ∫ t : Fin d → ℝ, |∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i) =
      Real.sqrt (2 / Real.pi) * (∏ i, chiDensity (s i)) *
        Real.sqrt (∑ i, u i ^ 2 * (1 / s i)) := by
  by_cases hs : ∀ i, 0 < s i
  · simp_rw [mixKernel_eq_gaussian, Finset.prod_mul_distrib]
    have hv : ∀ i, Real.toNNReal (1 / s i) ≠ 0 := fun i => by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact one_div_pos.2 (hs i)
    have hre : ∀ t : Fin d → ℝ, |∑ i, u i * t i| * ((∏ i, chiDensity (s i)) *
        ∏ i, gaussianPDFReal 0 (Real.toNNReal (1 / s i)) (t i)) =
        (∏ i, chiDensity (s i)) *
          (|∑ i, u i * t i| * ∏ i, gaussianPDFReal 0 (Real.toNNReal (1 / s i)) (t i)) :=
      fun t => by ring
    simp_rw [hre]
    rw [integral_const_mul, integral_abs_linear_prod_gaussianPDFReal u _ hv]
    simp_rw [Real.coe_toNNReal _ (le_of_lt (one_div_pos.2 (hs _)))]
    ring
  · simp only [not_forall, not_lt] at hs
    obtain ⟨i, hi⟩ := hs
    have h1 : ∀ t : Fin d → ℝ, ∏ j, mixKernel (s j) (t j) = 0 := fun t =>
      Finset.prod_eq_zero (Finset.mem_univ i) (mixKernel_of_nonpos hi _)
    have h2 : ∏ j, chiDensity (s j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (chiDensity_of_nonpos hi)
    simp [h1, h2]

/-! ### The `χ²₃` product integrals -/

/-- `γ` or `γ/s` according to whether `i = j`. -/
noncomputable def chiK (i j : Fin d) (x : ℝ) : ℝ :=
  if i = j then chiDensity x / x else chiDensity x

lemma integrable_chiK (i j : Fin d) : Integrable (chiK i j) := by
  unfold chiK; split_ifs
  · exact integrable_chiDensity_div
  · exact integrable_chiDensity

lemma integral_chiK (i j : Fin d) : ∫ x, chiK i j x = 1 := by
  unfold chiK; split_ifs
  · exact integral_chiDensity_div
  · exact integral_chiDensity

lemma prod_chiK (i : Fin d) (s : Fin d → ℝ) :
    ∏ j, chiK i j (s j) = (∏ j, chiDensity (s j)) * (1 / s i) := by
  classical
  have : ∀ j, chiK i j (s j) = chiDensity (s j) * (if i = j then 1 / s j else 1) := by
    intro j; unfold chiK; split_ifs <;> ring
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq, if_pos (Finset.mem_univ i)]

lemma integral_prod_chiDensity : ∫ s : Fin d → ℝ, ∏ j, chiDensity (s j) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod (f := fun _ => chiDensity)]
  simp [integral_chiDensity]

lemma integral_prod_chiK (i : Fin d) : ∫ s : Fin d → ℝ, ∏ j, chiK i j (s j) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod (f := fun j => chiK i j)]
  simp [integral_chiK]

/-! ### The main inequality -/

theorem integral_abs_linear_tDensity_le_of_integrable (u : Fin d → ℝ)
    (hint : Integrable (fun t : Fin d → ℝ =>
      |∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2)))) :
    ∫ t : Fin d → ℝ, |∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2)) ≤
      Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i, u i ^ 2) := by
  classical
  -- Step A: mixture representation
  have hA : ∀ t : Fin d → ℝ, |∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2)) =
      ∫ s : Fin d → ℝ, |∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i) := by
    intro t
    rw [integral_const_mul, integral_fintype_prod_volume_eq_prod (f := fun i s => mixKernel s (t i))]
    simp_rw [integral_mixKernel]
  -- Step B: Fubini
  have hFm : AEStronglyMeasurable (Function.uncurry fun t s : Fin d → ℝ =>
      |∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i))
      ((volume : Measure (Fin d → ℝ)).prod volume) :=
    (measurable_mixIntegrand u).aestronglyMeasurable
  have hF : Integrable (Function.uncurry fun t s : Fin d → ℝ =>
      |∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i))
      ((volume : Measure (Fin d → ℝ)).prod volume) := by
    rw [integrable_prod_iff hFm]
    constructor
    · refine Eventually.of_forall fun t => ?_
      show Integrable (fun s : Fin d → ℝ => |∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i)) volume
      exact (integrable_prod_mixKernel t).const_mul _
    · show Integrable (fun t : Fin d → ℝ =>
        ∫ s : Fin d → ℝ, ‖|∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i)‖) volume
      refine hint.congr (Eventually.of_forall fun t => ?_)
      show |∑ i, u i * t i| * ∏ i, (2 / (Real.pi * (1 + t i ^ 2) ^ 2)) =
        ∫ s : Fin d → ℝ, ‖|∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i)‖
      rw [hA t]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      show |∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i) =
        ‖|∑ i, u i * t i| * ∏ i, mixKernel (s i) (t i)‖
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (Finset.prod_nonneg fun i _ => mixKernel_nonneg _ _))]
  simp_rw [hA]
  rw [integral_integral_swap hF]
  simp_rw [integral_abs_linear_mixKernel u]
  -- Step C: AM–GM and the product integrals
  set S := ∑ i, u i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hS0.eq_or_lt with h0 | hpos
  · have hu : ∀ i, u i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u i))).1 h0.symm i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simp [hu]
    positivity
  · have hprod_nonneg : ∀ s : Fin d → ℝ, 0 ≤ ∏ i, chiDensity (s i) := fun s =>
      Finset.prod_nonneg fun i _ => chiDensity_nonneg _
    have hbound : ∀ s : Fin d → ℝ,
        Real.sqrt (2 / Real.pi) * (∏ i, chiDensity (s i)) * Real.sqrt (∑ i, u i ^ 2 * (1 / s i)) ≤
        Real.sqrt (2 / Real.pi) / (2 * Real.sqrt S) *
          (∑ i, u i ^ 2 * ∏ j, chiK i j (s j) + S * ∏ j, chiDensity (s j)) := by
      intro s
      have hexp : ∑ i, u i ^ 2 * ∏ j, chiK i j (s j) + S * ∏ j, chiDensity (s j) =
          (∏ j, chiDensity (s j)) * ((∑ i, u i ^ 2 * (1 / s i)) + S) := by
        simp_rw [prod_chiK]
        rw [mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      rw [hexp]
      by_cases hs : ∀ i, 0 < s i
      · have hA0 : 0 ≤ ∑ i, u i ^ 2 * (1 / s i) :=
          Finset.sum_nonneg fun i _ => by have := hs i; positivity
        have key : Real.sqrt (∑ i, u i ^ 2 * (1 / s i)) ≤
            ((∑ i, u i ^ 2 * (1 / s i)) + S) / (2 * Real.sqrt S) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [Real.sq_sqrt hA0, Real.sq_sqrt hS0,
            sq_nonneg (Real.sqrt (∑ i, u i ^ 2 * (1 / s i)) - Real.sqrt S),
            Real.sqrt_nonneg S, Real.sqrt_nonneg (∑ i, u i ^ 2 * (1 / s i))]
        calc Real.sqrt (2 / Real.pi) * (∏ i, chiDensity (s i)) *
              Real.sqrt (∑ i, u i ^ 2 * (1 / s i))
            ≤ Real.sqrt (2 / Real.pi) * (∏ i, chiDensity (s i)) *
              (((∑ i, u i ^ 2 * (1 / s i)) + S) / (2 * Real.sqrt S)) :=
              mul_le_mul_of_nonneg_left key
                (mul_nonneg (Real.sqrt_nonneg _) (hprod_nonneg s))
          _ = _ := by ring
      · simp only [not_forall, not_lt] at hs
        obtain ⟨i, hi⟩ := hs
        have : ∏ j, chiDensity (s j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (chiDensity_of_nonpos hi)
        simp [this]
    have hint2 : Integrable (fun s : Fin d → ℝ => Real.sqrt (2 / Real.pi) / (2 * Real.sqrt S) *
        (∑ i, u i ^ 2 * ∏ j, chiK i j (s j) + S * ∏ j, chiDensity (s j))) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.add ?_ ?_
      · exact integrable_finsetSum _ fun i _ =>
          (Integrable.fintype_prod (f := fun j => chiK i j) fun j => integrable_chiK i j).const_mul _
      · exact (Integrable.fintype_prod (f := fun _ => chiDensity)
          fun j => integrable_chiDensity).const_mul _
    refine (integral_mono_of_nonneg (Eventually.of_forall fun s =>
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hprod_nonneg s)) (Real.sqrt_nonneg _))
      hint2 (Eventually.of_forall hbound)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add, integral_finsetSum, integral_const_mul]
    · simp_rw [integral_const_mul, integral_prod_chiK, integral_prod_chiDensity]
      simp only [mul_one]
      rw [← hS]
      have hsq : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS0
      have hpos' : 0 < Real.sqrt S := Real.sqrt_pos.2 hpos
      have h2 : S + S = 2 * Real.sqrt S * Real.sqrt S := by rw [mul_assoc, hsq]; ring
      rw [h2, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]
    · intro i _
      exact (Integrable.fintype_prod (f := fun j => chiK i j) fun j => integrable_chiK i j).const_mul _
    · exact integrable_finsetSum _ fun i _ =>
        (Integrable.fintype_prod (f := fun j => chiK i j) fun j => integrable_chiK i j).const_mul _
    · exact (Integrable.fintype_prod (f := fun _ => chiDensity)
        fun j => integrable_chiDensity).const_mul _

end Komlos
