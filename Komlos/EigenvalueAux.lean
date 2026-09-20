import Komlos.Cheeger
import Komlos.Variation

/-!
# Auxiliary lemmas for the smooth-density bridges (paper Lemma 3.2, first paragraph)

* `lintegral_fderiv_le_dirVar` — Fatou's lemma along the difference quotients gives
  `∫ |∂_w f| ≤ V_w f` for every `C¹` function `f`; together with `dirVar_le_lintegral_fderiv`
  this is the `W^{1,1}` identity `V_w f = ∫ |∂_w f|` (paper, after (2.1)).
* `dirVar_congr_ae`, `mixtureEnergy_congr_ae` — `V_u` only sees the a.e. class.
* `dirVar_convolution_le` — mollifying with a nonnegative kernel of mass one does not increase
  `V_u` (Young's inequality applied to the translation differences; paper: "has energy at most
  `E_H(ρ_r)`, by convexity and one-homogeneity of `H`").
* `dilateDensity`, `dirVar_dilateDensity_le` — the contraction `ρ_r` of the paper, with
  `V_u ρ_r ≤ r⁻¹ V_u ρ` ("contraction gives ... energy `r⁻¹ E_H(ρ)`").
* `dilate_closure_add_ball_subset` — `dist(K_r, K^c) ≥ (1 − r) δ₀`.
* `exists_smooth_approx` — contract-and-mollify: every `ρ ∈ 𝒫(K)` is approximated in energy
  (up to the factor `r⁻¹`) by a smooth probability density compactly supported in `K`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise Convolution

namespace Komlos

variable {d : ℕ}

/-! ### Fatou: `∫ |∂_w f| ≤ V_w f` -/

/-- Fatou's lemma along the difference quotients `h_n = 1/(n+1)`: for every `C¹` function `f`
(no support hypothesis), `∫ |∂_w f| ≤ V_w f`. -/
theorem lintegral_fderiv_le_dirVar (w : Euc d) (f : Euc d → ℝ) (hf : ContDiff ℝ 1 f) :
    ∫⁻ x, ‖fderiv ℝ f x w‖ₑ ≤ dirVar w f := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun n : ℕ => 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have htpos : ∀ n, 0 < t n := by intro n; rw [ht]; positivity
  have htlim : Tendsto t atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => Set.mem_Ioi.2 (htpos n)⟩
    rw [ht]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hqm : ∀ n, Measurable fun x => ‖f (x + t n • w) - f x‖ₑ / ENNReal.ofReal (t n) := fun n =>
    ((hfc.comp (continuous_id.add continuous_const)).sub hfc).enorm.measurable.div_const _
  have hpt : ∀ x, Tendsto (fun n => ‖f (x + t n • w) - f x‖ₑ / ENNReal.ofReal (t n)) atTop
      (𝓝 ‖fderiv ℝ f x w‖ₑ) := by
    intro x
    have hd : HasDerivAt (fun s : ℝ => f (x + s • w)) (fderiv ℝ f (x + (0 : ℝ) • w) w) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
      simpa [Function.comp_def] using (hfd _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h2 := (continuous_enorm.tendsto _).comp hd.tendsto_slope_zero_right
    simp only [zero_smul, add_zero] at h2
    refine (h2.comp htlim).congr fun n => ?_
    simp only [Function.comp_apply, zero_add]
    rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_inv, abs_of_pos (htpos n),
      ENNReal.ofReal_inv_of_pos (htpos n), div_eq_mul_inv, mul_comm]
  calc ∫⁻ x, ‖fderiv ℝ f x w‖ₑ
      = ∫⁻ x, liminf (fun n => ‖f (x + t n • w) - f x‖ₑ / ENNReal.ofReal (t n)) atTop :=
        lintegral_congr fun x => ((hpt x).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ x, ‖f (x + t n • w) - f x‖ₑ / ENNReal.ofReal (t n)) atTop :=
        lintegral_liminf_le hqm
    _ ≤ dirVar w f := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
        have : ∫⁻ x, ‖f (x + t n • w) - f x‖ₑ / ENNReal.ofReal (t n)
            = (∫⁻ x, ‖f (x + t n • w) - f x‖ₑ) / ENNReal.ofReal (t n) := by
          simp only [div_eq_mul_inv]
          rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (htpos n)).ne')]
        rw [this]
        exact div_le_dirVar w f (htpos n)

/-! ### The directional derivative of a `C¹` compactly supported function -/

/-- `x ↦ ∂_w f(x)` is continuous for `C¹` `f`. -/
theorem continuous_fderiv_apply {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (w : Euc d) :
    Continuous fun x => fderiv ℝ f x w :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- `x ↦ ∂_w f(x)` has compact support when `f` does. -/
theorem hasCompactSupport_fderiv_apply {f : Euc d → ℝ} (hsupp : HasCompactSupport f)
    (w : Euc d) : HasCompactSupport fun x => fderiv ℝ f x w :=
  (hsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L w) (by simp)

/-- `x ↦ ∂_w f(x)` is integrable for `C¹` compactly supported `f`. -/
theorem integrable_fderiv_apply {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (w : Euc d) : Integrable fun x => fderiv ℝ f x w :=
  (continuous_fderiv_apply hf w).integrable_of_hasCompactSupport
    (hasCompactSupport_fderiv_apply hsupp w)

/-- `∫ |∂_w f| < ∞` for `C¹` compactly supported `f`. -/
theorem lintegral_enorm_fderiv_ne_top {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (w : Euc d) : ∫⁻ x, ‖fderiv ℝ f x w‖ₑ ≠ ⊤ :=
  (integrable_fderiv_apply hf hsupp w).hasFiniteIntegral.ne

/-! ### `V_u` only depends on the a.e. class -/

/-- `V_u f = V_u g` when `f = g` a.e. -/
theorem dirVar_congr_ae (u : Euc d) {f g : Euc d → ℝ} (hfg : f =ᵐ[volume] g) :
    dirVar u f = dirVar u g := by
  unfold dirVar
  refine iSup_congr fun h => iSup_congr fun _ => ?_
  congr 1
  refine lintegral_congr_ae ?_
  have h1 : f ∘ (· + h • u) =ᵐ[volume] g ∘ (· + h • u) :=
    hfg.comp_tendsto (measurePreserving_add_right volume (h • u)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [h1, hfg] with x hx1 hx2
  simp only [Function.comp_apply] at hx1
  rw [hx1, hx2]

/-- `E_H f = E_H g` when `f = g` a.e. -/
theorem mixtureEnergy_congr_ae {N : ℕ} (α : Fin N → ℝ) (u : Fin N → Euc d) {f g : Euc d → ℝ}
    (hfg : f =ᵐ[volume] g) : mixtureEnergy α u f = mixtureEnergy α u g := by
  unfold mixtureEnergy
  exact Finset.sum_congr rfl fun l _ => by rw [dirVar_congr_ae (u l) hfg]

/-! ### Mollification does not increase `V_u` -/

/-- Mollifying with a nonnegative continuous compactly supported kernel of mass one does not
increase the directional variation: Young's inequality `‖(g(·+hu) − g) ⋆ φ‖₁ ≤ ‖g(·+hu) − g‖₁`
for every `h > 0`. -/
theorem dirVar_convolution_le (u : Euc d) {g φ : Euc d → ℝ} (hgm : Measurable g)
    (hgi : Integrable g) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ1 : ∫ x, φ x = 1) :
    dirVar u (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) ≤ dirVar u g := by
  refine dirVar_le_of_forall u _ fun h hh => ?_
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hφs
  have hint : ∀ k : Euc d → ℝ, Integrable k → ∀ x, Integrable fun s => k s * φ (x - s) :=
    fun k hk x => hk.mul_bdd (hφc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun s => hC (x - s))
  have hconv : ∀ x, (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) (x + h • u) -
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x
      = ∫ s, (g (s + h • u) - g s) * φ (x - s) := by
    intro x
    simp only [convolution_lsmul, smul_eq_mul]
    have e1 : ∫ t, g t * φ (x + h • u - t) = ∫ s, g (s + h • u) * φ (x - s) := by
      rw [← integral_add_right_eq_self (fun t => g t * φ (x + h • u - t)) (h • u)]
      congr 1; ext s; congr 2; abel
    rw [e1, ← integral_sub (hint _ (hgi.comp_add_right _) x) (hint g hgi x)]
    congr 1; ext s; ring
  have hmeas : Measurable fun p : Euc d × Euc d =>
      ‖g (p.2 + h • u) - g p.2‖ₑ * ‖φ (p.1 - p.2)‖ₑ :=
    ((measurable_enorm_translate_sub hgm (h • u)).comp measurable_snd).mul
      (hφc.comp (continuous_fst.sub continuous_snd)).enorm.measurable
  have hφ1' : ∫⁻ x, ‖φ x‖ₑ = 1 := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hφc.integrable_of_hasCompactSupport hφs)]
    simp_rw [Real.norm_of_nonneg (hφ0 _)]
    rw [hφ1, ENNReal.ofReal_one]
  calc ∫⁻ x, ‖(g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) (x + h • u) -
          (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x‖ₑ
      = ∫⁻ x, ‖∫ s, (g (s + h • u) - g s) * φ (x - s)‖ₑ :=
        lintegral_congr fun x => by rw [hconv x]
    _ ≤ ∫⁻ x, ∫⁻ s, ‖g (s + h • u) - g s‖ₑ * ‖φ (x - s)‖ₑ := by
        refine lintegral_mono fun x => (enorm_integral_le_lintegral_enorm _).trans ?_
        exact lintegral_mono fun s => (enorm_mul _ _).le
    _ = ∫⁻ s, ∫⁻ x, ‖g (s + h • u) - g s‖ₑ * ‖φ (x - s)‖ₑ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s, ‖g (s + h • u) - g s‖ₑ * ∫⁻ x, ‖φ (x - s)‖ₑ :=
        lintegral_congr fun s =>
          lintegral_const_mul _ (hφc.enorm.measurable.comp (measurable_sub_const s))
    _ = (∫⁻ s, ‖g (s + h • u) - g s‖ₑ) * ∫⁻ x, ‖φ x‖ₑ := by
        simp_rw [lintegral_sub_right_eq_self (fun x => ‖φ x‖ₑ) _]
        exact lintegral_mul_const _ (measurable_enorm_translate_sub hgm _)
    _ = ∫⁻ s, ‖g (s + h • u) - g s‖ₑ := by rw [hφ1', mul_one]
    _ ≤ ENNReal.ofReal h * dirVar u g := lintegral_translate_sub_le_of_pos u g hh
    _ = dirVar u g * ENNReal.ofReal h := mul_comm _ _

/-! ### The contraction `ρ_r` -/

/-- Change of variables for the lower integral under the dilation `x ↦ x₀ + r⁻¹ • (x − x₀)`
(which multiplies Lebesgue measure by `r ^ d`); no measurability is needed. -/
theorem lintegral_comp_dilate (G : Euc d → ℝ≥0∞) (x₀ : Euc d) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, G (x₀ + r⁻¹ • (x - x₀)) = ENNReal.ofReal (r ^ d) * ∫⁻ x, G x := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  have h1 : ∫⁻ x, G (x₀ + r⁻¹ • (x - x₀)) = ∫⁻ x, G (x₀ + r⁻¹ • x) :=
    lintegral_sub_right_eq_self (fun x => G (x₀ + r⁻¹ • x)) x₀
  have h2 : ∫⁻ x, G (x₀ + r⁻¹ • x) = ENNReal.ofReal (r ^ d) * ∫⁻ x, G (x₀ + x) := by
    have := lintegral_map_equiv (μ := volume) (fun x => G (x₀ + x))
      (MeasurableEquiv.smul₀ r⁻¹ hr' : Euc d ≃ᵐ Euc d)
    simp only [MeasurableEquiv.coe_smul₀] at this
    rw [← this, Measure.map_addHaar_smul volume hr', lintegral_smul_measure,
      finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hr d), smul_eq_mul]
  have h3 : ∫⁻ x, G (x₀ + x) = ∫⁻ x, G x := lintegral_add_left_eq_self G x₀
  rw [h1, h2, h3]

/-- The contracted density `ρ_r(x) = r^{-d} ρ(x₀ + r⁻¹ (x − x₀))` (paper, proof of Lemma 3.2). -/
noncomputable def dilateDensity (x₀ : Euc d) (r : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : ℝ :=
  (r ^ d)⁻¹ * ρ (x₀ + r⁻¹ • (x - x₀))

theorem dilateDensity_nonneg (x₀ : Euc d) {r : ℝ} (hr : 0 < r) {ρ : Euc d → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) (x : Euc d) : 0 ≤ dilateDensity x₀ r ρ x :=
  mul_nonneg (by positivity) (hρ _)

theorem measurable_dilateDensity (x₀ : Euc d) (r : ℝ) {ρ : Euc d → ℝ} (hρ : Measurable ρ) :
    Measurable (dilateDensity x₀ r ρ) :=
  (hρ.comp (continuous_const.add
    ((continuous_id.sub continuous_const).const_smul r⁻¹)).measurable).const_mul _

theorem integrable_dilateDensity (x₀ : Euc d) {r : ℝ} (hr : 0 < r) {ρ : Euc d → ℝ}
    (hρ : Integrable ρ) : Integrable (dilateDensity x₀ r ρ) := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  have h1 : Integrable fun x => ρ (x₀ + r⁻¹ • x) :=
    (integrable_comp_smul_iff volume (fun x => ρ (x₀ + x)) hr').2 (hρ.comp_add_left x₀)
  exact (h1.comp_sub_right x₀).const_mul _

/-- The contraction preserves mass. -/
theorem integral_dilateDensity (x₀ : Euc d) {r : ℝ} (hr : 0 < r) (ρ : Euc d → ℝ) :
    ∫ x, dilateDensity x₀ r ρ x = ∫ x, ρ x := by
  unfold dilateDensity
  rw [integral_const_mul, integral_sub_right_eq_self (fun x => ρ (x₀ + r⁻¹ • x)) x₀,
    Measure.integral_comp_inv_smul volume (fun x => ρ (x₀ + x)) r, integral_add_left_eq_self ρ x₀,
    finrank_euclideanSpace_fin, abs_of_pos (pow_pos hr d), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (pow_pos hr d).ne', one_mul]

/-- `ρ_r` vanishes outside `x₀ + r (K − x₀)` when `ρ` vanishes outside `K`. -/
theorem dilateDensity_eq_zero (x₀ : Euc d) {r : ℝ} (hr : 0 < r) {ρ : Euc d → ℝ}
    {K : Set (Euc d)} (hρ : ∀ x, x ∉ K → ρ x = 0) {x : Euc d}
    (hx : x ∉ (fun y => x₀ + r • (y - x₀)) '' K) : dilateDensity x₀ r ρ x = 0 := by
  have hmem : x₀ + r⁻¹ • (x - x₀) ∉ K := fun hmem => hx ⟨_, hmem, by
    show x₀ + r • (x₀ + r⁻¹ • (x - x₀) - x₀) = x
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]⟩
  unfold dilateDensity
  rw [hρ _ hmem, mul_zero]

/-- `V_u ρ_r ≤ r⁻¹ V_u ρ` (paper: "contraction gives ... energy `r⁻¹ E_H(ρ)`"). -/
theorem dirVar_dilateDensity_le (u x₀ : Euc d) {r : ℝ} (hr : 0 < r) (ρ : Euc d → ℝ) :
    dirVar u (dilateDensity x₀ r ρ) ≤ ENNReal.ofReal r⁻¹ * dirVar u ρ := by
  refine dirVar_le_of_forall u _ fun h hh => ?_
  have hT : ∀ x : Euc d,
      x₀ + r⁻¹ • (x + h • u - x₀) = (x₀ + r⁻¹ • (x - x₀)) + (r⁻¹ * h) • u := by
    intro x
    rw [mul_smul]; simp only [smul_add, smul_sub]; abel
  have hc : (0 : ℝ) ≤ (r ^ d)⁻¹ := by positivity
  calc ∫⁻ x, ‖dilateDensity x₀ r ρ (x + h • u) - dilateDensity x₀ r ρ x‖ₑ
      = ∫⁻ x, ENNReal.ofReal (r ^ d)⁻¹ *
          ‖ρ (x₀ + r⁻¹ • (x - x₀) + (r⁻¹ * h) • u) - ρ (x₀ + r⁻¹ • (x - x₀))‖ₑ := by
        refine lintegral_congr fun x => ?_
        simp only [dilateDensity, hT]
        rw [← mul_sub, enorm_mul, Real.enorm_of_nonneg hc]
    _ = ENNReal.ofReal (r ^ d)⁻¹ * (ENNReal.ofReal (r ^ d) *
          ∫⁻ y, ‖ρ (y + (r⁻¹ * h) • u) - ρ y‖ₑ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_comp_dilate (fun y => ‖ρ (y + (r⁻¹ * h) • u) - ρ y‖ₑ) x₀ hr]
    _ = ∫⁻ y, ‖ρ (y + (r⁻¹ * h) • u) - ρ y‖ₑ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc, inv_mul_cancel₀ (pow_pos hr d).ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (r⁻¹ * h) * dirVar u ρ :=
        lintegral_translate_sub_le_of_pos u ρ (by positivity)
    _ = ENNReal.ofReal r⁻¹ * dirVar u ρ * ENNReal.ofReal h := by
        rw [ENNReal.ofReal_mul (by positivity)]; ring

/-! ### Geometry of the contracted set -/

/-- The contracted set `x₀ + r (cl K − x₀)` stays at distance `> ε` from `Kᶜ` when
`B(x₀, δ) ⊆ K`, `K` is open and convex, and `ε < (1 − r) δ`
(paper: `dist(K_r, K^c) ≥ (1 − r) δ₀`). -/
theorem dilate_closure_add_ball_subset {K : Set (Euc d)} (hK : Convex ℝ K) (hKo : IsOpen K)
    {x₀ : Euc d} {δ : ℝ} (hball : Metric.ball x₀ δ ⊆ K) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {ε : ℝ} (hε : ε < (1 - r) * δ) :
    (fun y => x₀ + r • (y - x₀)) '' closure K + Metric.closedBall 0 ε ⊆ K := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, z, hz, rfl⟩
  have h1r : 0 < 1 - r := by linarith
  have hz1 : ‖z‖ ≤ ε := mem_closedBall_zero_iff.1 hz
  have hz' : x₀ + (1 - r)⁻¹ • z ∈ interior K := by
    rw [hKo.interior_eq]
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 h1r)]
    calc (1 - r)⁻¹ * ‖z‖ ≤ (1 - r)⁻¹ * ε := mul_le_mul_of_nonneg_left hz1 (inv_pos.2 h1r).le
      _ < (1 - r)⁻¹ * ((1 - r) * δ) := mul_lt_mul_of_pos_left hε (inv_pos.2 h1r)
      _ = δ := inv_mul_cancel_left₀ h1r.ne' δ
  have hmem := hK.combo_interior_closure_mem_interior hz' hy h1r hr0 (sub_add_cancel 1 r)
  rw [hKo.interior_eq] at hmem
  convert hmem using 1
  rw [smul_add, smul_smul, mul_inv_cancel₀ h1r.ne', one_smul]
  module

/-! ### Contract and mollify -/

/-- **Contract-and-mollify** (paper, proof of Lemma 3.2, first paragraph): for `ρ ∈ 𝒫(K)` on a
nonempty bounded open convex `K` and `0 < r < 1`, there is a smooth probability density with
compact support inside `K` whose energy is at most `r⁻¹ E_H(ρ)`. -/
theorem exists_smooth_approx {N : ℕ} (α : Fin N → ℝ) (u : Fin N → Euc d) {K : Set (Euc d)}
    (hK : IsGoodConvex K) {ρ : Euc d → ℝ} (hρ : MemP K ρ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ f : Euc d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ K ∧
      (∀ x, 0 ≤ f x) ∧ ∫ x, f x = 1 ∧
      mixtureEnergy α u f ≤ ENNReal.ofReal r⁻¹ * mixtureEnergy α u ρ := by
  obtain ⟨x₀, hx₀⟩ := hK.nonempty
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hK.isOpen x₀ hx₀
  have h1r : 0 < 1 - r := by linarith
  -- the everywhere-supported representative `K.indicator ρ` of `ρ`
  have hρ'ae : K.indicator ρ =ᵐ[volume] ρ := by
    filter_upwards [hρ.ae_zero_outside] with x hx
    by_cases hxK : x ∈ K
    · exact indicator_of_mem hxK ρ
    · rw [indicator_of_notMem hxK, hx hxK]
  have hρ'm : Measurable (K.indicator ρ) := hρ.measurable.indicator hK.isOpen.measurableSet
  have hρ'0 : ∀ x, 0 ≤ K.indicator ρ x := fun x => indicator_nonneg (fun y _ => hρ.nonneg y) x
  have hρ'i : Integrable (K.indicator ρ) := hρ.integrable.congr hρ'ae.symm
  have hρ'1 : ∫ x, K.indicator ρ x = 1 := by rw [integral_congr_ae hρ'ae, hρ.integral_eq_one]
  have hρ'K : ∀ x, x ∉ K → K.indicator ρ x = 0 := fun x hx => indicator_of_notMem hx ρ
  have hE' : mixtureEnergy α u (K.indicator ρ) = mixtureEnergy α u ρ :=
    mixtureEnergy_congr_ae α u hρ'ae
  -- the contracted density `ρ_r`
  set σ : Euc d → ℝ := dilateDensity x₀ r (K.indicator ρ) with hσ
  have hσm : Measurable σ := measurable_dilateDensity x₀ r hρ'm
  have hσ0 : ∀ x, 0 ≤ σ x := dilateDensity_nonneg x₀ hr0 hρ'0
  have hσi : Integrable σ := integrable_dilateDensity x₀ hr0 hρ'i
  have hσ1 : ∫ x, σ x = 1 := by rw [hσ, integral_dilateDensity x₀ hr0, hρ'1]
  set S : Euc d → Euc d := fun y => x₀ + r • (y - x₀) with hS
  have hSc : Continuous S :=
    continuous_const.add ((continuous_id.sub continuous_const).const_smul r)
  have hσsupp : Function.support σ ⊆ S '' closure K := by
    intro x hx
    by_contra hx'
    exact hx (dilateDensity_eq_zero x₀ hr0 hρ'K fun h => hx' (image_mono subset_closure h))
  have hC₁ : IsCompact (S '' closure K) := hK.isBounded.isCompact_closure.image hSc
  -- the mollifier, of radius `ε < (1 − r) δ`
  set ε : ℝ := (1 - r) * δ / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεlt : ε < (1 - r) * δ := by rw [hε]; exact half_lt_self (by positivity)
  let φ : ContDiffBump (0 : Euc d) := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hφ1 : ∫ x, φ.normed volume x = 1 := φ.integral_normed
  have hφs : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hφsupp : Function.support (φ.normed volume) ⊆ Metric.closedBall 0 ε := by
    rw [φ.support_normed_eq]; exact Metric.ball_subset_closedBall
  -- the smooth approximant `ρ_r ⋆ φ`
  set f : Euc d → ℝ := σ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ.normed volume with hf
  have hfsupp : Function.support f ⊆ S '' closure K + Metric.closedBall 0 ε :=
    (support_convolution_subset _).trans (add_subset_add hσsupp hφsupp)
  have hC₂ : IsCompact (S '' closure K + Metric.closedBall 0 ε) :=
    hC₁.add (isCompact_closedBall 0 ε)
  have hsub : S '' closure K + Metric.closedBall 0 ε ⊆ K :=
    dilate_closure_add_ball_subset hK.convex hK.isOpen hball hr0.le hr1 hεlt
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hφs.contDiff_convolution_right _ hσi.locallyIntegrable φ.contDiff_normed
  · exact HasCompactSupport.of_support_subset_isCompact hC₂ hfsupp
  · exact (closure_minimal hfsupp hC₂.isClosed).trans hsub
  · intro x
    rw [hf, convolution_lsmul]
    exact integral_nonneg fun t => smul_nonneg (hσ0 t) (φ.nonneg_normed _)
  · rw [hf, integral_convolution _ hσi φ.integrable_normed, hσ1, hφ1]
    simp
  · calc mixtureEnergy α u f ≤ mixtureEnergy α u σ := by
          unfold mixtureEnergy
          refine Finset.sum_le_sum fun l _ => ?_
          gcongr
          exact dirVar_convolution_le (u l) hσm hσi φ.continuous_normed hφs φ.nonneg_normed hφ1
      _ ≤ ENNReal.ofReal r⁻¹ * mixtureEnergy α u (K.indicator ρ) := by
          unfold mixtureEnergy
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun l _ => ?_
          rw [mul_left_comm]
          gcongr
          exact dirVar_dilateDensity_le (u l) x₀ hr0 _
      _ = ENNReal.ofReal r⁻¹ * mixtureEnergy α u ρ := by rw [hE']

end Komlos
