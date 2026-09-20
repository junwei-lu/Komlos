import Komlos.Literature.PLaplacian.RegularityChainRule

/-!
# A Poincaré inequality on convex sets without boundary values

The measure-theoretic input of the positivity of weak eigensolutions
(`Komlos.Literature.weak_harnack_pos`, the weak Harnack inequality of Trudinger 1967, towards
Mosconi–Riey–Squassina 2024, Proposition 4.5; paper Appendix A, *Eigenfunction inputs*): for a
convex set `B` of diameter at most `D` and `p > 1`,
`∫_B ∫_B |f(y) - f(x)|^p dy dx ≤ 2^d D^p |B| ∫_B |∇f|^p`
(Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Lemma 7.16, in
integrated form). No boundary values are needed; this is what controls `log u` on a ball in terms
of the energy of `log u`.

## Main results

* `lintegral_comp_add_smul` — `∫ g(a + r y) dy = |r|^{-d} ∫ g`.
* `enorm_sub_le_lintegral_segment` — the fundamental theorem of calculus along a segment.
* `lintegral_lintegral_sub_rpow_le_of_contDiff` — the inequality for `C¹` functions: Hölder on the
  segment, Tonelli, and the change of variables `x ↦ x + t(y - x)` in `y` (for `t ≥ 1/2`) or in
  `x` (for `t < 1/2`), each with Jacobian at least `2^{-d}`.
* `MemW0.lintegral_lintegral_sub_rpow_le` — the inequality on `W₀^{1,p}`, by mollification and
  Fatou.
* `MemW0.measure_mul_lintegral_sub_rpow_le` — the form used for positivity: if `f ≥ a` on a subset
  `E ⊆ B`, then `|E| ∫_B ((a - f)^+)^p ≤ 2^d D^p |B| ∫_B |∇f|^p`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Change of variables for dilations -/

/-- **Change of variables for a dilation**: `∫⁻ g(a + r • y) dy = |r^d|⁻¹ ∫⁻ g` for `r ≠ 0`. -/
theorem lintegral_comp_add_smul {g : Euc d → ℝ≥0∞} (hg : Measurable g) (a : Euc d) {r : ℝ}
    (hr : r ≠ 0) :
    ∫⁻ y, g (a + r • y) = ENNReal.ofReal |(r ^ d)⁻¹| * ∫⁻ y, g y := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (Euc d)) hr
  rw [finrank_euclideanSpace_fin] at hmap
  have h1 : ∫⁻ y, g (a + r • y) = ∫⁻ y, g (a + y) ∂(Measure.map (fun x => r • x) volume) :=
    (lintegral_map (hg.comp (measurable_const_add a)) (measurable_const_smul r)).symm
  rw [h1, hmap, lintegral_smul_measure, smul_eq_mul, lintegral_add_left_eq_self g a]

/-- For `r ≥ 1/2`, the Jacobian factor `|r^d|⁻¹` is at most `2^d`. -/
theorem ofReal_abs_inv_pow_le {r : ℝ} (hr : 1 / 2 ≤ r) :
    ENNReal.ofReal |(r ^ d)⁻¹| ≤ 2 ^ d := by
  have hr0 : 0 < r := by linarith
  have hrd : 0 < r ^ d := pow_pos hr0 d
  rw [abs_of_nonneg (inv_nonneg.2 hrd.le)]
  have h : (r ^ d)⁻¹ ≤ 2 ^ d := by
    rw [inv_le_iff_one_le_mul₀ hrd, ← mul_pow]
    exact one_le_pow₀ (by linarith)
  calc ENNReal.ofReal (r ^ d)⁻¹ ≤ ENNReal.ofReal (2 ^ d) := ENNReal.ofReal_le_ofReal h
    _ = 2 ^ d := by rw [ENNReal.ofReal_pow (by norm_num)]; simp

/-! ### The smooth case -/

/-- **The fundamental theorem of calculus along a segment**: for `f ∈ C¹`,
`|f(y) - f(x)| ≤ |y - x| ∫₀¹ |∇f(x + t(y - x))| dt`. -/
theorem enorm_sub_le_lintegral_segment {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (x y : Euc d) :
    ‖f y - f x‖ₑ ≤ ‖y - x‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖gradient f (x + t • (y - x))‖ₑ := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • (y - x)))
      (fderiv ℝ f (x + t • (y - x)) (y - x)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous fun t : ℝ => fderiv ℝ f (x + t • (y - x)) (y - x) :=
    ((hf.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable 0 1)
  have e1 : x + (1 : ℝ) • (y - x) = y := by rw [one_smul, add_sub_cancel]
  have e0 : x + (0 : ℝ) • (y - x) = x := by rw [zero_smul, add_zero]
  rw [e1, e0, intervalIntegral.integral_of_le zero_le_one] at hftc
  calc ‖f y - f x‖ₑ = ‖∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • (y - x)) (y - x)‖ₑ := by
        rw [hftc]
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x + t • (y - x)) (y - x)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖y - x‖ₑ * ‖gradient f (x + t • (y - x))‖ₑ := by
        refine lintegral_mono fun t => ?_
        rw [fderiv_apply_eq_inner_gradient, mul_comm]
        exact enorm_real_inner_le _ _
    _ = ‖y - x‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖gradient f (x + t • (y - x))‖ₑ :=
        lintegral_const_mul' _ _ enorm_ne_top

/-- The point `x + t(y - x)` written as `t y + (1 - t) x`. -/
theorem add_smul_sub_eq (x y : Euc d) (t : ℝ) : x + t • (y - x) = t • y + (1 - t) • x := by
  rw [smul_sub, sub_smul, one_smul]
  abel

/-- The inner double integral of `G(x + t(y - x))` over `B × B` is at most `2^d |B| ∫ G`, for
`0 < t ≤ 1` (change of variables in `y` if `t ≥ 1/2`, in `x` otherwise). -/
theorem lintegral_lintegral_segment_le {G : Euc d → ℝ≥0∞} (hG : Measurable G) (B : Set (Euc d))
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ∫⁻ x in B, ∫⁻ y in B, G (x + t • (y - x)) ≤ 2 ^ d * volume B * ∫⁻ z, G z := by
  have hc : Continuous fun q : Euc d × Euc d => q.1 + t • (q.2 - q.1) := by fun_prop
  have hmeas : Measurable fun q : Euc d × Euc d => G (q.1 + t • (q.2 - q.1)) :=
    hG.comp hc.measurable
  rcases le_or_gt (1 / 2) t with h | h
  · have hy : ∀ x, ∫⁻ y in B, G (x + t • (y - x)) ≤ 2 ^ d * ∫⁻ z, G z := by
      intro x
      calc ∫⁻ y in B, G (x + t • (y - x)) ≤ ∫⁻ y, G (x + t • (y - x)) :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ y, G ((1 - t) • x + t • y) := by
            refine lintegral_congr fun y => ?_
            rw [add_smul_sub_eq, add_comm]
        _ = ENNReal.ofReal |(t ^ d)⁻¹| * ∫⁻ z, G z :=
            lintegral_comp_add_smul hG _ ht.1.ne'
        _ ≤ 2 ^ d * ∫⁻ z, G z := mul_le_mul_left (ofReal_abs_inv_pow_le h) _
    calc ∫⁻ x in B, ∫⁻ y in B, G (x + t • (y - x)) ≤ ∫⁻ _ in B, 2 ^ d * ∫⁻ z, G z :=
          lintegral_mono fun x => hy x
      _ = 2 ^ d * volume B * ∫⁻ z, G z := by
          rw [setLIntegral_const]
          ring
  · have hx : ∀ y, ∫⁻ x in B, G (x + t • (y - x)) ≤ 2 ^ d * ∫⁻ z, G z := by
      intro y
      calc ∫⁻ x in B, G (x + t • (y - x)) ≤ ∫⁻ x, G (x + t • (y - x)) :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ x, G (t • y + (1 - t) • x) := by
            refine lintegral_congr fun x => ?_
            rw [add_smul_sub_eq]
        _ = ENNReal.ofReal |((1 - t) ^ d)⁻¹| * ∫⁻ z, G z :=
            lintegral_comp_add_smul hG _ (by linarith)
        _ ≤ 2 ^ d * ∫⁻ z, G z := mul_le_mul_left (ofReal_abs_inv_pow_le (by linarith)) _
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    calc ∫⁻ y in B, ∫⁻ x in B, G (x + t • (y - x)) ≤ ∫⁻ _ in B, 2 ^ d * ∫⁻ z, G z :=
          lintegral_mono fun y => hx y
      _ = 2 ^ d * volume B * ∫⁻ z, G z := by
          rw [setLIntegral_const]
          ring

/-- **The double-integral Poincaré inequality for `C¹` functions** on a convex set `B` of
diameter at most `D` (`p > 1`): `∫_B ∫_B |f(y) - f(x)|^p ≤ 2^d D^p |B| ∫_B |∇f|^p`. -/
theorem lintegral_lintegral_sub_rpow_le_of_contDiff {p : ℝ} (hp : 1 < p) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 1 f) {B : Set (Euc d)} (hBc : Convex ℝ B) (hBm : MeasurableSet B) {D : ℝ}
    (hBD : ∀ x ∈ B, ∀ y ∈ B, ‖y - x‖ ≤ D) :
    ∫⁻ x in B, ∫⁻ y in B, ‖f y - f x‖ₑ ^ p ≤
      2 ^ d * ENNReal.ofReal D ^ p * volume B * ∫⁻ z in B, ‖gradient f z‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  set G : Euc d → ℝ≥0∞ := B.indicator fun z => ‖gradient f z‖ₑ ^ p with hG_def
  have hGm : Measurable G :=
    ((continuous_enorm.comp (continuous_gradient hf)).measurable.pow_const p).indicator hBm
  -- the segment estimate
  have hpt : ∀ x ∈ B, ∀ y ∈ B, ‖f y - f x‖ₑ ^ p ≤
      ENNReal.ofReal D ^ p * ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • (y - x)) := by
    intro x hx y hy
    have h1 := enorm_sub_le_lintegral_segment hf x y
    have h2 : ‖y - x‖ₑ ≤ ENNReal.ofReal D := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hBD x hx y hy)
    have hmeas : AEMeasurable (fun t : ℝ => ‖gradient f (x + t • (y - x))‖ₑ)
        (volume.restrict (Ioc 0 1)) :=
      (continuous_enorm.comp ((continuous_gradient hf).comp
        (continuous_const.add (continuous_id.smul continuous_const)))).measurable.aemeasurable
    have h3 := lintegral_Ioc_rpow_le 1 hp hmeas
    rw [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] at h3
    have h4 : ∫⁻ t in Ioc (0 : ℝ) 1, ‖gradient f (x + t • (y - x))‖ₑ ^ p =
        ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • (y - x)) := by
      refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have hmem : x + t • (y - x) ∈ B := hBc.add_smul_sub_mem hx hy ⟨ht.1.le, ht.2⟩
      simp only [hG_def, indicator_of_mem hmem]
    calc ‖f y - f x‖ₑ ^ p
        ≤ (‖y - x‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖gradient f (x + t • (y - x))‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow h1 hp0.le
      _ = ‖y - x‖ₑ ^ p * (∫⁻ t in Ioc (0 : ℝ) 1, ‖gradient f (x + t • (y - x))‖ₑ) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ ENNReal.ofReal D ^ p * ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • (y - x)) := by
          rw [← h4]
          exact mul_le_mul' (ENNReal.rpow_le_rpow h2 hp0.le) h3
  -- measurability of the integrand in `(x, y, t)`
  have hmeas3 : Measurable fun q : (Euc d × Euc d) × ℝ => G (q.1.1 + q.2 • (q.1.2 - q.1.1)) :=
    hGm.comp ((continuous_fst.comp continuous_fst).add (continuous_snd.smul
      ((continuous_snd.comp continuous_fst).sub (continuous_fst.comp continuous_fst)))).measurable
  have hswap_y : ∀ x, ∫⁻ y in B, ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • (y - x)) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in B, G (x + t • (y - x)) := by
    intro x
    have hm : Measurable fun q : Euc d × ℝ => G (x + q.2 • (q.1 - x)) :=
      hGm.comp (continuous_const.add (continuous_snd.smul
        (continuous_fst.sub continuous_const))).measurable
    exact lintegral_lintegral_swap hm.aemeasurable
  have hswap_x : ∫⁻ x in B, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in B, G (x + t • (y - x)) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in B, ∫⁻ y in B, G (x + t • (y - x)) := by
    have hm : Measurable fun q : Euc d × ℝ => ∫⁻ y in B, G (q.1 + q.2 • (y - q.1)) := by
      exact (Measurable.lintegral_prod_right' (ν := volume.restrict B)
        (f := fun r : (Euc d × ℝ) × Euc d => G (r.1.1 + r.1.2 • (r.2 - r.1.1)))
        (hGm.comp ((continuous_fst.comp continuous_fst).add
          ((continuous_snd.comp continuous_fst).smul
            (continuous_snd.sub (continuous_fst.comp continuous_fst)))).measurable))
    exact lintegral_lintegral_swap hm.aemeasurable
  calc ∫⁻ x in B, ∫⁻ y in B, ‖f y - f x‖ₑ ^ p
      ≤ ∫⁻ x in B, ∫⁻ y in B,
          ENNReal.ofReal D ^ p * ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • (y - x)) :=
        setLIntegral_mono' hBm fun x hx => setLIntegral_mono' hBm fun y hy => hpt x hx y hy
    _ = ENNReal.ofReal D ^ p *
          ∫⁻ x in B, ∫⁻ y in B, ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • (y - x)) := by
        rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal D ^ p *
          ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in B, ∫⁻ y in B, G (x + t • (y - x)) := by
        rw [← hswap_x]
        congr 1
        exact lintegral_congr fun x => hswap_y x
    _ ≤ ENNReal.ofReal D ^ p * ∫⁻ _ in Ioc (0 : ℝ) 1, 2 ^ d * volume B * ∫⁻ z, G z := by
        exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc fun t ht =>
          lintegral_lintegral_segment_le hGm B ht) _
    _ = 2 ^ d * ENNReal.ofReal D ^ p * volume B * ∫⁻ z in B, ‖gradient f z‖ₑ ^ p := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one,
          hG_def, lintegral_indicator hBm]
        ring

/-! ### The Sobolev case -/

/-- `‖f‖_{L^q(s)} ≤ ‖g‖_{L^q(s)} + ‖f - g‖_{L^q}` (triangle inequality and `μ|_s ≤ μ`). -/
theorem eLpNorm_restrict_le_add_eLpNorm_sub {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {q : ℝ≥0∞} (hq : 1 ≤ q) {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (s : Set α) :
    eLpNorm f q (μ.restrict s) ≤ eLpNorm g q (μ.restrict s) + eLpNorm (f - g) q μ := by
  have h : g + (f - g) = f := add_sub_cancel g f
  have h1 := eLpNorm_add_le hg.restrict (hf.sub hg).restrict hq (μ := μ.restrict s)
  rw [h] at h1
  exact h1.trans (add_le_add le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self))

/-- **The double-integral Poincaré inequality on `W₀^{1,p}`** on a convex set `B` of finite
measure and diameter at most `D`: `∫_B ∫_B |f(y) - f(x)|^p ≤ 2^d D^p |B| ∫_B |∇f|^p`.
Proof: mollify (`gradient_mollifyWith`), apply the smooth case
`lintegral_lintegral_sub_rpow_le_of_contDiff`, and pass to the limit by Fatou on the left
(`ae_tendsto_convolution_stdBump`) and by `L^p` convergence of the gradients on the right. -/
theorem MemW0.lintegral_lintegral_sub_rpow_le {p : ℝ} (hp : 1 < p) {K : Set (Euc d)}
    {f : Euc d → ℝ} (hf : MemW0 p K f) {B : Set (Euc d)} (hBc : Convex ℝ B)
    (hBm : MeasurableSet B) (hBfin : volume B ≠ ⊤) {D : ℝ}
    (hBD : ∀ x ∈ B, ∀ y ∈ B, ‖y - x‖ ≤ D) :
    ∫⁻ x in B, ∫⁻ y in B, ‖f y - f x‖ₑ ^ p ≤
      2 ^ d * ENNReal.ofReal D ^ p * volume B * ∫⁻ z in B, ‖weakGrad f z‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hg := hf.hasWeakGradient
  have hgp := hf.memLp_weakGrad
  obtain ⟨v, hv⟩ : ∃ v : ℕ → Euc d → ℝ,
      ∀ n, v n = mollifyWith ((mollifierBump n).normed volume) f := ⟨_, fun _ => rfl⟩
  have hvc : ∀ n, ContDiff ℝ 1 (v n) := fun n => by
    rw [hv n]
    exact (contDiff_mollifyWith (n := ⊤) (ContDiffBump.contDiff_normed _)
      (mollifierBump n).hasCompactSupport_normed hg.locallyIntegrable).of_le
      (by exact_mod_cast le_top)
  have hvg : ∀ n, gradient (v n) =
      mollifyWith ((mollifierBump n).normed volume) (weakGrad f) := fun n => by
    rw [hv n]
    exact gradient_mollifyWith hg (ContDiffBump.contDiff_normed _)
      (ContDiffBump.hasCompactSupport_normed _)
  have hae : ∀ᵐ x, Tendsto (fun n => v n x) atTop (𝓝 (f x)) := by
    filter_upwards [ae_tendsto_convolution_stdBump hg.locallyIntegrable] with x hx
    refine hx.congr fun n => ?_
    rw [hv n, mollifyWith_eq_convolution_right]
  -- the constant
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = 2 ^ d * ENNReal.ofReal D ^ p * volume B := ⟨_, rfl⟩
  have hCtop : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
      (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)) hBfin
  -- the gradients converge in `L^p`
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ≥0∞,
      ∀ n, e n = eLpNorm (gradient (v n) - weakGrad f) (ENNReal.ofReal p) := ⟨_, fun _ => rfl⟩
  have he0 : Tendsto e atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_mollifyWith_sub (φ := mollifierBump)
      tendsto_one_div_add_atTop_nhds_zero_nat hp hgp
    refine h.congr fun n => ?_
    rw [he n, hvg n]
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0∞, a = eLpNorm (weakGrad f) (ENNReal.ofReal p) (volume.restrict B) :=
    ⟨_, rfl⟩
  have hatop : a ≠ ⊤ := by
    rw [ha]
    exact ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans_lt hgp.eLpNorm_lt_top).ne
  have hbound : ∀ n, ∫⁻ z in B, ‖gradient (v n) z‖ₑ ^ p ≤ (a + e n) ^ p := by
    intro n
    rw [lintegral_enorm_rpow_eq_eLpNorm_rpow hp0, ha, he n]
    exact ENNReal.rpow_le_rpow (eLpNorm_restrict_le_add_eLpNorm_sub hp1
      (continuous_gradient (hvc n)).aestronglyMeasurable hgp.aestronglyMeasurable B) hp0.le
  -- Fatou in `y`, then in `x`
  have hinner : ∀ᵐ x, ∫⁻ y in B, ‖f y - f x‖ₑ ^ p ≤
      liminf (fun n => ∫⁻ y in B, ‖v n y - v n x‖ₑ ^ p) atTop := by
    filter_upwards [hae] with x hx
    have hae' : ∀ᵐ y ∂(volume.restrict B), ‖f y - f x‖ₑ ^ p =
        liminf (fun n => ‖v n y - v n x‖ₑ ^ p) atTop := by
      filter_upwards [ae_restrict_of_ae hae] with y hy
      have h1 : Tendsto (fun n => v n y - v n x) atTop (𝓝 (f y - f x)) := hy.sub hx
      have h2 : Tendsto (fun n => ‖v n y - v n x‖ₑ ^ p) atTop (𝓝 (‖f y - f x‖ₑ ^ p)) :=
        (ENNReal.continuous_rpow_const.tendsto _).comp ((continuous_enorm.tendsto _).comp h1)
      exact h2.liminf_eq.symm
    rw [lintegral_congr_ae hae']
    refine lintegral_liminf_le fun n => ?_
    have hc : Continuous fun y => ‖v n y - v n x‖ₑ ^ p :=
      ENNReal.continuous_rpow_const.comp (continuous_enorm.comp
        ((hvc n).continuous.sub continuous_const))
    exact hc.measurable
  have hmeasF : ∀ n, Measurable fun x => ∫⁻ y in B, ‖v n y - v n x‖ₑ ^ p := fun n => by
    have hc : Continuous fun q : Euc d × Euc d => ‖v n q.2 - v n q.1‖ₑ ^ p :=
      ENNReal.continuous_rpow_const.comp (continuous_enorm.comp
        (((hvc n).continuous.comp continuous_snd).sub ((hvc n).continuous.comp continuous_fst)))
    exact hc.measurable.lintegral_prod_right'
  have hlim : Tendsto (fun n => C * (a + e n) ^ p) atTop (𝓝 (C * a ^ p)) := by
    have h1 := (tendsto_const_nhds (x := a)).add he0
    rw [add_zero] at h1
    have h2 : Tendsto (fun n => (a + e n) ^ p) atTop (𝓝 (a ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto a).comp h1
    exact ENNReal.Tendsto.const_mul h2 (Or.inr hCtop)
  have hsmooth : ∀ n, ∫⁻ x in B, ∫⁻ y in B, ‖v n y - v n x‖ₑ ^ p ≤ C * (a + e n) ^ p := by
    intro n
    rw [hC]
    exact (lintegral_lintegral_sub_rpow_le_of_contDiff hp (hvc n) hBc hBm hBD).trans
      (mul_le_mul_right (hbound n) _)
  have hfinal : C * a ^ p =
      2 ^ d * ENNReal.ofReal D ^ p * volume B * ∫⁻ z in B, ‖weakGrad f z‖ₑ ^ p := by
    rw [hC, ha, lintegral_enorm_rpow_eq_eLpNorm_rpow hp0]
  refine (lintegral_mono_ae (ae_restrict_of_ae hinner)).trans ?_
  refine (lintegral_liminf_le hmeasF).trans ?_
  refine (liminf_le_liminf (Eventually.of_forall hsmooth)).trans ?_
  rw [hlim.liminf_eq, hfinal]

/-- **Poincaré inequality from a set of large values**: if `f ∈ W₀^{1,p}` and `a ≤ f` on a
measurable `E ⊆ B`, then `|E| ∫_B ((a - f)^+)^p ≤ 2^d D^p |B| ∫_B |∇f|^p` (each `x ∈ B` has
`(a - f(x))^+ ≤ |f(y) - f(x)|` for all `y ∈ E`). -/
theorem MemW0.measure_mul_lintegral_sub_rpow_le {p : ℝ} (hp : 1 < p) {K : Set (Euc d)}
    {f : Euc d → ℝ} (hf : MemW0 p K f) {B : Set (Euc d)} (hBc : Convex ℝ B)
    (hBm : MeasurableSet B) (hBfin : volume B ≠ ⊤) {D : ℝ}
    (hBD : ∀ x ∈ B, ∀ y ∈ B, ‖y - x‖ ≤ D) {E : Set (Euc d)} (hEm : MeasurableSet E)
    (hEB : E ⊆ B) {a : ℝ} (hE : ∀ y ∈ E, a ≤ f y) :
    volume E * ∫⁻ x in B, ENNReal.ofReal (a - f x) ^ p ≤
      2 ^ d * ENNReal.ofReal D ^ p * volume B * ∫⁻ z in B, ‖weakGrad f z‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hEfin : volume E ≠ ⊤ := ((measure_mono hEB).trans_lt hBfin.lt_top).ne
  refine le_trans ?_ (hf.lintegral_lintegral_sub_rpow_le hp hBc hBm hBfin hBD)
  rw [← lintegral_const_mul' _ _ hEfin]
  refine lintegral_mono fun x => ?_
  have h1 : volume E * ENNReal.ofReal (a - f x) ^ p =
      ∫⁻ _ in E, ENNReal.ofReal (a - f x) ^ p := by
    rw [setLIntegral_const, mul_comm]
  have h2 : ∫⁻ _ in E, ENNReal.ofReal (a - f x) ^ p ≤ ∫⁻ y in E, ‖f y - f x‖ₑ ^ p := by
    refine setLIntegral_mono' hEm fun y hy => ENNReal.rpow_le_rpow ?_ hp0.le
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal ((by linarith [hE y hy] : a - f x ≤ f y - f x).trans
      (le_abs_self _))
  rw [h1]
  exact h2.trans (lintegral_mono_set hEB)

end Komlos.Literature
