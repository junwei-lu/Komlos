import Komlos.Rearrangement

/-!
# Auxiliary lemmas for the rearranged height (paper Lemma 4.3)

Measure-theoretic toolbox used in `Komlos.Height`:

* the shear `(y, s) ↦ (y + s v, s)` of `ℝ^d × ℝ` preserves Lebesgue measure
  (`measurePreserving_shear`), which gives the integral formula `lintegral_lift` for functions
  of the form `𝟙_{|s|<3} g(y + s v)` and the a.e. transfer `ae_lift`;
* the layer-cake identity `∫_0^∞ |{f > t}|² dt = ∫∫ min(f(s), f(r)) ds dr`
  (`lintegral_sq_meas_lt`);
* the first absolute moment of a symmetric decreasing rearrangement on a fiber
  (`lintegral_abs_mul_rearr`) and its consequence for `symRearr`
  (`lintegral_abs_mul_symRearr`);
* the reduction of a double integral over the square `(−3,3)²` of an even function of `r − s`
  to `2 ∫_0^6 (6 − h) φ(h) dh` (`lintegral_sq_eq_intervalIntegral`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

section Shear

/-- The shear `(y, s) ↦ (y + s v, s)` of `ℝ^d × ℝ`, as a measurable equivalence. -/
def shear (v : Euc d) : Euc d × ℝ ≃ᵐ Euc d × ℝ where
  toFun p := (p.1 + p.2 • v, p.2)
  invFun p := (p.1 - p.2 • v, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_fst.add (measurable_snd.smul_const v)).prodMk measurable_snd
  measurable_invFun := (measurable_fst.sub (measurable_snd.smul_const v)).prodMk measurable_snd

@[simp]
theorem shear_apply (v : Euc d) (p : Euc d × ℝ) : shear v p = (p.1 + p.2 • v, p.2) := rfl

/-- The shear preserves Lebesgue measure on `ℝ^d × ℝ`. -/
theorem measurePreserving_shear (v : Euc d) :
    MeasurePreserving (shear v) (volume : Measure (Euc d × ℝ)) volume := by
  have h1 : MeasurePreserving (fun p : ℝ × Euc d => (p.1, p.2 + p.1 • v))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    (MeasurePreserving.id _).skew_product (g := fun s y => y + s • v)
      (measurable_snd.add (measurable_fst.smul_const v))
      (Filter.Eventually.of_forall fun s => map_add_right_eq_self _ _)
  have h2 := (Measure.measurePreserving_swap.comp h1).comp
    (Measure.measurePreserving_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure ℝ)))
  have h3 : ⇑(shear v) =
      (Prod.swap ∘ fun p : ℝ × Euc d => (p.1, p.2 + p.1 • v)) ∘ Prod.swap := by
    funext p; rfl
  show MeasurePreserving (shear v) (volume.prod volume) (volume.prod volume)
  rw [h3]; exact h2

/-- Composition with the shear does not change Lebesgue integrals. -/
theorem lintegral_shear (v : Euc d) {f : Euc d × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p : Euc d × ℝ, f (p.1 + p.2 • v, p.2) = ∫⁻ p, f p :=
  (measurePreserving_shear v).lintegral_comp hf

/-- Composition with the shear does not change Bochner integrals. -/
theorem integral_shear (v : Euc d) (f : Euc d × ℝ → ℝ) :
    ∫ p : Euc d × ℝ, f (p.1 + p.2 • v, p.2) = ∫ p, f p :=
  (measurePreserving_shear v).integral_comp' f

/-- An a.e. property of `ℝ^d` transfers to `(y, s) ↦ y + s v`. -/
theorem ae_lift (v : Euc d) {P : Euc d → Prop} (h : ∀ᵐ x, P x) :
    ∀ᵐ p : Euc d × ℝ, P (p.1 + p.2 • v) := by
  have hq : Measure.QuasiMeasurePreserving (fun p : Euc d × ℝ => p.1 + p.2 • v) volume volume := by
    have := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d)))
      (ν := (volume : Measure ℝ))).comp (measurePreserving_shear v).quasiMeasurePreserving
    rw [Measure.volume_eq_prod]
    exact this
  exact hq.ae h

/-- Integrating `𝟙_{|s|<3} g(y + s v)` over `ℝ^d × ℝ` gives `6 ∫ g`. -/
theorem lintegral_lift (v : Euc d) {g : Euc d → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p : Euc d × ℝ, (if |p.2| < 3 then g (p.1 + p.2 • v) else 0) =
      ENNReal.ofReal 6 * ∫⁻ x, g x := by
  have hF : Measurable fun p : Euc d × ℝ => g p.1 * (Ioo (-3 : ℝ) 3).indicator (fun _ => 1) p.2 :=
    (hg.comp measurable_fst).mul
      ((measurable_const.indicator measurableSet_Ioo).comp measurable_snd)
  have : (fun p : Euc d × ℝ => if |p.2| < 3 then g (p.1 + p.2 • v) else 0) =
      fun p => (fun p : Euc d × ℝ => g p.1 * (Ioo (-3 : ℝ) 3).indicator (fun _ => 1) p.2)
        (p.1 + p.2 • v, p.2) := by
    ext p
    by_cases h : |p.2| < 3
    · have : p.2 ∈ Ioo (-3 : ℝ) 3 := by rw [mem_Ioo, ← abs_lt]; exact h
      simp [h, this]
    · have : p.2 ∉ Ioo (-3 : ℝ) 3 := by rw [mem_Ioo, ← abs_lt]; exact h
      simp [h, this]
  rw [this, lintegral_shear v hF, Measure.volume_eq_prod,
    lintegral_prod_mul hg.aemeasurable (measurable_const.indicator measurableSet_Ioo).aemeasurable,
    lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]
  norm_num [mul_comm]

end Shear

section LayerCake

/-- Layer cake for a square: `∫_0^∞ |{f > t}|² dt = ∫∫ min(f(s), f(r)) ds dr` for measurable
nonnegative `f` on `ℝ`. -/
theorem lintegral_sq_meas_lt (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ s, 0 ≤ f s) :
    ∫⁻ t in Ioi (0 : ℝ), (volume {s | t < f s}) ^ 2 =
      ∫⁻ s, ∫⁻ r, ENNReal.ofReal (min (f s) (f r)) := by
  have hg : Measurable fun z : ℝ × ℝ => min (f z.1) (f z.2) :=
    (hf.comp measurable_fst).min (hf.comp measurable_snd)
  have key := lintegral_eq_lintegral_meas_lt ((volume : Measure ℝ).prod volume)
    (f := fun z : ℝ × ℝ => min (f z.1) (f z.2))
    (Filter.Eventually.of_forall fun z => le_min (h0 _) (h0 _)) hg.aemeasurable
  rw [lintegral_prod _ hg.ennreal_ofReal.aemeasurable] at key
  refine Eq.trans ?_ key.symm
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have : {z : ℝ × ℝ | t < min (f z.1) (f z.2)} = {s | t < f s} ×ˢ {r | t < f r} := by
    ext z; simp
  rw [this, Measure.prod_prod, sq]

/-- `∫_{-a}^{a} |s| ds = a²`. -/
theorem setLIntegral_ofReal_abs_Ioo {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ s in Ioo (-a) a, ENNReal.ofReal |s| = ENNReal.ofReal (a ^ 2) := by
  have hint : IntegrableOn (fun s : ℝ => |s|) (Ioo (-a) a) :=
    continuous_abs.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun s => abs_nonneg s)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∫ s in (-a)..(0 : ℝ), |s| = a ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun s => -s) ?_]
    · rw [intervalIntegral.integral_neg, integral_id]; ring
    · intro s hs
      rw [uIcc_of_le (by linarith)] at hs
      exact abs_of_nonpos hs.2
  have h2 : ∫ s in (0 : ℝ)..a, |s| = a ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun s => s) ?_]
    · rw [integral_id]; ring
    · intro s hs
      rw [uIcc_of_le ha] at hs
      exact abs_of_nonneg hs.1
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := -a) (b := 0) (c := a)
    (continuous_abs.intervalIntegrable _ _) (continuous_abs.intervalIntegrable _ _), h1, h2]
  ring

/-- `ENNReal.ofReal (max a 0) = ENNReal.ofReal a`. -/
theorem ofReal_max_zero (a : ℝ) : ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]

/-- The first absolute moment of a symmetric decreasing rearrangement on a fiber: if `μ` is
the distribution function, `∫ |s| ∫_0^∞ 𝟙{2|s| < μ(t)} dt ds = ∫_0^∞ μ(t)²/4 dt`. -/
theorem lintegral_abs_mul_rearr (μ : ℝ → ℝ≥0∞) (hμ : Measurable μ)
    (hfin : ∀ t, 0 < t → μ t ≠ ∞) :
    ∫⁻ s : ℝ, ENNReal.ofReal |s| *
        ∫⁻ t in Ioi (0 : ℝ), {t | ENNReal.ofReal (2 * |s|) < μ t}.indicator (fun _ => 1) t =
      ∫⁻ t in Ioi (0 : ℝ), (μ t) ^ 2 / 4 := by
  have hmeas : Measurable (Function.uncurry fun (s t : ℝ) => ENNReal.ofReal |s| *
      {t | ENNReal.ofReal (2 * |s|) < μ t}.indicator (fun _ => 1) t) := by
    have : Measurable fun z : ℝ × ℝ => ENNReal.ofReal |z.1| *
        {z : ℝ × ℝ | ENNReal.ofReal (2 * |z.1|) < μ z.2}.indicator (fun _ => 1) z :=
      (measurable_fst.abs.ennreal_ofReal).mul (measurable_const.indicator
        (measurableSet_lt ((measurable_const.mul measurable_fst.abs).ennreal_ofReal)
          (hμ.comp measurable_snd)))
    exact this
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  set a : ℝ := (μ t).toReal / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hset : ∀ s : ℝ, ENNReal.ofReal |s| *
      {t | ENNReal.ofReal (2 * |s|) < μ t}.indicator (fun _ => 1) t =
      (Ioo (-a) a).indicator (fun s => ENNReal.ofReal |s|) s := by
    intro s
    have hiff : ENNReal.ofReal (2 * |s|) < μ t ↔ s ∈ Ioo (-a) a := by
      rw [← ENNReal.ofReal_toReal (hfin t ht),
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), mem_Ioo, ← abs_lt, ha]
      constructor <;> intro h <;> linarith
    by_cases h : ENNReal.ofReal (2 * |s|) < μ t
    · rw [indicator_of_mem (show t ∈ {t | ENNReal.ofReal (2 * |s|) < μ t} from h), mul_one,
        indicator_of_mem (hiff.1 h)]
    · rw [indicator_of_notMem (show t ∉ {t | ENNReal.ofReal (2 * |s|) < μ t} from h), mul_zero,
        indicator_of_notMem (mt hiff.2 h)]
  simp_rw [hset]
  rw [lintegral_indicator measurableSet_Ioo, setLIntegral_ofReal_abs_Ioo ha0, ha,
    ← ENNReal.ofReal_toReal (hfin t ht), ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
    show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1
  ring

/-- Fiber version of `lintegral_abs_mul_rearr` with the real-valued (`toReal`) rearrangement:
`∫ |s| g⋆(s) ds = (1/4) ∫∫ min(g(s), g(r)) ds dr` for nonnegative measurable `g ∈ L¹(ℝ)` whose
superlevel sets at positive levels have finite measure. -/
theorem lintegral_abs_mul_rearr_toReal (g : ℝ → ℝ) (hg : Measurable g) (h0 : ∀ s, 0 ≤ g s)
    (hint : ∫⁻ s, ENNReal.ofReal (g s) ≠ ∞)
    (hfin : ∀ t, 0 < t → volume {s | t < g s} ≠ ∞) :
    ∫⁻ s : ℝ, ENNReal.ofReal (|s| * (∫⁻ t in Ioi (0 : ℝ),
        {t | ENNReal.ofReal (2 * |s|) < volume {r | t < g r}}.indicator (fun _ => 1) t).toReal) =
      4⁻¹ * ∫⁻ s, ∫⁻ r, ENNReal.ofReal (min (g s) (g r)) := by
  set μ : ℝ → ℝ≥0∞ := fun t => volume {r | t < g r} with hμdef
  have hμ : Measurable μ :=
    Antitone.measurable fun t₁ t₂ h => measure_mono fun r hr => lt_of_le_of_lt h hr
  have hlayer : ∫⁻ t in Ioi (0 : ℝ), μ t = ∫⁻ s, ENNReal.ofReal (g s) :=
    (lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall h0) hg.aemeasurable).symm
  have hS : ∀ s : ℝ, s ≠ 0 →
      (∫⁻ t in Ioi (0 : ℝ), {t | ENNReal.ofReal (2 * |s|) < μ t}.indicator (fun _ => 1) t) ≠ ∞ := by
    intro s hs
    have hpos : 0 < ENNReal.ofReal (2 * |s|) := ENNReal.ofReal_pos.2 (by positivity)
    have hle : ENNReal.ofReal (2 * |s|) *
        ∫⁻ t in Ioi (0 : ℝ), {t | ENNReal.ofReal (2 * |s|) < μ t}.indicator (fun _ => 1) t ≤
        ∫⁻ t in Ioi (0 : ℝ), μ t := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun t => ?_
      by_cases h : ENNReal.ofReal (2 * |s|) < μ t
      · rw [indicator_of_mem (show t ∈ {t | ENNReal.ofReal (2 * |s|) < μ t} from h), mul_one]
        exact h.le
      · rw [indicator_of_notMem (show t ∉ {t | ENNReal.ofReal (2 * |s|) < μ t} from h), mul_zero]
        exact zero_le
    intro htop
    rw [htop, ENNReal.mul_top hpos.ne', hlayer] at hle
    exact hint (top_le_iff.1 hle)
  have hae : ∀ᵐ s : ℝ, s ≠ 0 := by
    rw [ae_iff]
    have : {s : ℝ | ¬ s ≠ 0} = {0} := by ext s; simp
    rw [this, Real.volume_singleton]
  calc ∫⁻ s : ℝ, ENNReal.ofReal (|s| * (∫⁻ t in Ioi (0 : ℝ),
          {t | ENNReal.ofReal (2 * |s|) < μ t}.indicator (fun _ => 1) t).toReal)
      = ∫⁻ s : ℝ, ENNReal.ofReal |s| *
          ∫⁻ t in Ioi (0 : ℝ), {t | ENNReal.ofReal (2 * |s|) < μ t}.indicator (fun _ => 1) t := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with s hs
        rw [ENNReal.ofReal_mul (abs_nonneg s), ENNReal.ofReal_toReal (hS s hs)]
    _ = ∫⁻ t in Ioi (0 : ℝ), (μ t) ^ 2 / 4 := lintegral_abs_mul_rearr μ hμ hfin
    _ = 4⁻¹ * ∫⁻ t in Ioi (0 : ℝ), (μ t) ^ 2 := by
        rw [← lintegral_const_mul' _ _ (by simp)]
        simp_rw [div_eq_mul_inv, mul_comm]
    _ = 4⁻¹ * ∫⁻ s, ∫⁻ r, ENNReal.ofReal (min (g s) (g r)) := by
        rw [lintegral_sq_meas_lt g hg h0]

/-- For nonnegative integrable `R` on `ℝ^d × ℝ` whose fibers have finite superlevel sets,
`∫ |s| R⋆ = (1/4) ∫ ∫∫ min(R(y,s), R(y,r)) dr ds dy` (paper, proof of Lemma 4.3). -/
theorem lintegral_abs_mul_symRearr (R : Euc d × ℝ → ℝ) (hR : Measurable R) (h0 : ∀ p, 0 ≤ R p)
    (hint : Integrable R) (hfin : ∀ y t, 0 < t → volume {s | t < R (y, s)} ≠ ∞) :
    ∫⁻ p, ENNReal.ofReal (|p.2| * symRearr R p) =
      4⁻¹ * ∫⁻ y, ∫⁻ s, ∫⁻ r, ENNReal.ofReal (min (R (y, s)) (R (y, r))) := by
  have hm : Measurable fun p : Euc d × ℝ => ENNReal.ofReal (|p.2| * symRearr R p) :=
    (measurable_snd.abs.mul (symRearr_measurable R hR)).ennreal_ofReal
  have hint' : Integrable R ((volume : Measure (Euc d)).prod volume) := hint
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable,
    ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr_ae ?_
  filter_upwards [hint'.prod_right_ae] with y hy
  have hfin' : ∫⁻ s, ENNReal.ofReal (R (y, s)) ≠ ∞ := by
    have := hy.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at this
    simp_rw [Real.enorm_eq_ofReal (h0 _)] at this
    exact this.ne
  exact lintegral_abs_mul_rearr_toReal (fun s => R (y, s)) (hR.comp measurable_prodMk_left)
    (fun s => h0 _) hfin' (hfin y)

/-- Commuting the three integrals `∫ dy ∫ ds ∫ dr = ∫ ds ∫ dr ∫ dy` (Tonelli). -/
theorem lintegral_lintegral_lintegral_comm {F : Euc d → ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable fun z : Euc d × ℝ × ℝ => F z.1 z.2.1 z.2.2) :
    ∫⁻ y, ∫⁻ s, ∫⁻ r, F y s r = ∫⁻ s, ∫⁻ r, ∫⁻ y, F y s r := by
  have h1 : Measurable fun z : (Euc d × ℝ) × ℝ => F z.1.1 z.1.2 z.2 :=
    hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h2 : Measurable (Function.uncurry fun (y : Euc d) (s : ℝ) => ∫⁻ r, F y s r) :=
    h1.lintegral_prod_right'
  rw [lintegral_lintegral_swap h2.aemeasurable]
  refine lintegral_congr fun s => ?_
  have h3 : Measurable (Function.uncurry fun (y : Euc d) (r : ℝ) => F y s r) :=
    hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact lintegral_lintegral_swap h3.aemeasurable

end LayerCake

section Square

/-- A bounded measurable function is interval integrable. -/
theorem intervalIntegrable_of_bounded {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ h, |φ h| ≤ C) (a b : ℝ) : IntervalIntegrable φ volume a b := by
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound measure_Ioc_lt_top hφ.aestronglyMeasurable.restrict C
    (Filter.Eventually.of_forall fun h => by simpa [Real.norm_eq_abs] using hC h)

/-- The double integral over the square `(−3,3)²` of an even, nonnegative, bounded, measurable
function of `r − s` equals `2 ∫_0^6 (6 − h) φ(h) dh` (paper, proof of Lemma 4.3). -/
theorem lintegral_sq_eq_intervalIntegral (φ : ℝ → ℝ) (hφ : Measurable φ) (h0 : ∀ h, 0 ≤ φ h)
    {C : ℝ} (hC : ∀ h, φ h ≤ C) (heven : ∀ h, φ (-h) = φ h) :
    ∫⁻ s in Ioo (-3 : ℝ) 3, ∫⁻ r in Ioo (-3 : ℝ) 3, ENNReal.ofReal (φ (r - s)) =
      ENNReal.ofReal (2 * ∫ h in (0 : ℝ)..6, (6 - h) * φ h) := by
  set W : Set (ℝ × ℝ) := Ioo (-3) 3 ×ˢ Ioo (-3) 3 with hWdef
  have hW : MeasurableSet W := measurableSet_Ioo.prod measurableSet_Ioo
  set G : ℝ × ℝ → ℝ≥0∞ := W.indicator fun z => ENNReal.ofReal (φ (z.2 - z.1)) with hGdef
  have hG : Measurable G :=
    ((hφ.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal).indicator hW
  have habs : ∀ h, |φ h| ≤ C := fun h => by rw [abs_of_nonneg (h0 h)]; exact hC h
  -- step 1: the double set integral is the integral of `G` over the product
  have hf0 : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (φ (z.2 - z.1)) :=
    (hφ.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  have step1 : ∫⁻ s in Ioo (-3 : ℝ) 3, ∫⁻ r in Ioo (-3 : ℝ) 3, ENNReal.ofReal (φ (r - s)) =
      ∫⁻ z, G z ∂((volume : Measure ℝ).prod volume) := by
    rw [hGdef, lintegral_indicator hW, ← Measure.prod_restrict, lintegral_prod _ hf0.aemeasurable]
  -- step 2: shear `(s, h) ↦ (s, s + h)`
  have step2 : ∫⁻ z, G z ∂((volume : Measure ℝ).prod volume) =
      ∫⁻ z : ℝ × ℝ, G (z.1, z.1 + z.2) ∂((volume : Measure ℝ).prod volume) :=
    ((measurePreserving_prod_add (volume : Measure ℝ) volume).lintegral_comp hG).symm
  -- step 3: Tonelli, integrating first in `s`
  have step3 : ∫⁻ z : ℝ × ℝ, G (z.1, z.1 + z.2) ∂((volume : Measure ℝ).prod volume) =
      ∫⁻ h, ENNReal.ofReal (φ h * max (6 - |h|) 0) := by
    have hG' : Measurable fun z : ℝ × ℝ => G (z.1, z.1 + z.2) :=
      hG.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
    rw [lintegral_prod_symm _ hG'.aemeasurable]
    refine lintegral_congr fun h => ?_
    have hpt : ∀ s, G (s, s + h) =
        (Ioo (-3 : ℝ) 3 ∩ Ioo (-3 - h) (3 - h)).indicator (fun _ => ENNReal.ofReal (φ h)) s := by
      intro s
      have hmem : (s, s + h) ∈ W ↔ s ∈ Ioo (-3 : ℝ) 3 ∩ Ioo (-3 - h) (3 - h) := by
        simp only [hWdef, mem_prod, mem_Ioo, mem_inter_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
      by_cases hs : (s, s + h) ∈ W
      · rw [hGdef, indicator_of_mem hs, indicator_of_mem (hmem.1 hs)]
        simp
      · rw [hGdef, indicator_of_notMem hs, indicator_of_notMem (mt hmem.2 hs)]
    simp_rw [hpt]
    rw [lintegral_indicator_const (measurableSet_Ioo.inter measurableSet_Ioo), Ioo_inter_Ioo,
      Real.volume_Ioo, ENNReal.ofReal_mul (h0 h), ofReal_max_zero]
    congr 2
    rcases le_total 0 h with hh | hh
    · rw [abs_of_nonneg hh, max_eq_left (by linarith), min_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos hh, max_eq_right (by linarith), min_eq_left (by linarith)]; ring
  -- step 4: back to a real integral
  have hsupp : (fun h : ℝ => φ h * max (6 - |h|) 0) =
      (Icc (-6 : ℝ) 6).indicator fun h => φ h * max (6 - |h|) 0 := by
    ext h
    by_cases hh : h ∈ Icc (-6 : ℝ) 6
    · rw [indicator_of_mem hh]
    · rw [indicator_of_notMem hh]
      have : max (6 - |h|) 0 = 0 := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hh
        refine max_eq_right ?_
        rcases hh with hh | hh
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [this, mul_zero]
  have hint : Integrable fun h : ℝ => φ h * max (6 - |h|) 0 := by
    rw [hsupp, integrable_indicator_iff measurableSet_Icc]
    have hm : Measurable fun h : ℝ => φ h * max (6 - |h|) 0 :=
      hφ.mul ((measurable_const.sub continuous_abs.measurable).max measurable_const)
    refine IntegrableOn.of_bound ?_ hm.aestronglyMeasurable.restrict (C * 6) ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun h hh => ?_
    rw [mem_Icc] at hh
    have h1 : 0 ≤ max (6 - |h|) 0 := le_max_right _ _
    have h2 : max (6 - |h|) 0 ≤ 6 := max_le (by linarith [abs_nonneg h]) (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 h), abs_of_nonneg h1]
    exact mul_le_mul (hC h) h2 h1 (le_trans (h0 h) (hC h))
  have step4 : ∫⁻ h, ENNReal.ofReal (φ h * max (6 - |h|) 0) =
      ENNReal.ofReal (∫ h, φ h * max (6 - |h|) 0) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun h => mul_nonneg (h0 h) (le_max_right _ _))]
  -- step 5: the real integral is an interval integral over `[-6, 6]`
  have step5 : ∫ h, φ h * max (6 - |h|) 0 = ∫ h in (-6 : ℝ)..6, φ h * (6 - |h|) := by
    rw [hsupp, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
    refine intervalIntegral.integral_congr fun h hh => ?_
    rw [uIcc_of_le (by norm_num), mem_Icc] at hh
    have habs6 : |h| ≤ 6 := abs_le.2 ⟨by linarith [hh.1], by linarith [hh.2]⟩
    have : max (6 - |h|) 0 = 6 - |h| := max_eq_left (by linarith)
    rw [this]
  -- step 6: fold by evenness
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun h => φ h * (6 - |h|)) volume a b := fun a b =>
    (intervalIntegrable_of_bounded hφ habs a b).mul_continuousOn
      (continuous_const.sub continuous_abs).continuousOn
  have step6 : ∫ h in (-6 : ℝ)..6, φ h * (6 - |h|) = 2 * ∫ h in (0 : ℝ)..6, (6 - h) * φ h := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii (-6) 0) (hii 0 6)]
    have hneg : ∫ h in (-6 : ℝ)..0, φ h * (6 - |h|) = ∫ h in (0 : ℝ)..6, φ h * (6 - |h|) := by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 6)
        (fun h => φ h * (6 - |h|))
      simp only [heven, abs_neg, neg_zero] at this
      exact this.symm
    have hpos : ∫ h in (0 : ℝ)..6, φ h * (6 - |h|) = ∫ h in (0 : ℝ)..6, (6 - h) * φ h := by
      refine intervalIntegral.integral_congr fun h hh => ?_
      rw [uIcc_of_le (by norm_num), mem_Icc] at hh
      simp only [abs_of_nonneg hh.1]; ring
    rw [hneg, hpos]; ring
  rw [step1, step2, step3, step4, step5, step6]

end Square

section Overlap

variable {ρ : Euc d → ℝ}

/-- `D(h) = ‖ρ − ρ(· + h v)‖₁` as the `toReal` of a Lebesgue integral. -/
theorem integral_abs_sub_translate (hρ : IsProbDensityOn univ ρ) (v : Euc d) (h : ℝ) :
    ∫ x, |ρ x - ρ (x + h • v)| = (∫⁻ x, ‖ρ (x + h • v) - ρ x‖ₑ).toReal := by
  have hint : Integrable fun x => ρ x - ρ (x + h • v) :=
    hρ.integrable.sub (hρ.integrable.comp_add_right (h • v))
  have := integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable
  simp only [Real.norm_eq_abs] at this
  rw [this]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← enorm_neg, neg_sub]

/-- The translation modulus is measurable in `h`. -/
theorem measurable_integral_abs_sub_translate (hρ : IsProbDensityOn univ ρ) (v : Euc d) :
    Measurable fun h : ℝ => ∫ x, |ρ x - ρ (x + h • v)| := by
  simp_rw [integral_abs_sub_translate hρ v]
  refine ENNReal.measurable_toReal.comp ?_
  have : Measurable fun z : ℝ × Euc d => ‖ρ (z.2 + z.1 • v) - ρ z.2‖ₑ :=
    ((hρ.measurable.comp (measurable_snd.add (measurable_fst.smul_const v))).sub
      (hρ.measurable.comp measurable_snd)).enorm
  exact this.lintegral_prod_right'

/-- Paper (3.1): `‖ρ − ρ(· + h v)‖₁ ≤ h V_v ρ` for `h ≥ 0` when `V_v ρ < ∞`. -/
theorem integral_abs_sub_translate_le (hρ : IsProbDensityOn univ ρ) (v : Euc d)
    (hfin : dirVar v ρ ≠ ⊤) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, |ρ x - ρ (x + h • v)| ≤ h * (dirVar v ρ).toReal := by
  rw [integral_abs_sub_translate hρ v]
  have := lintegral_translate_sub_le v ρ hρ.measurable h
  calc (∫⁻ x, ‖ρ (x + h • v) - ρ x‖ₑ).toReal ≤ (ENNReal.ofReal |h| * dirVar v ρ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) this
    _ = h * (dirVar v ρ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg h), abs_of_nonneg hh]

/-- Paper (4.6): the overlap `O(h) = ∫ min(ρ, ρ(· + h v)) = 1 − ½ ‖ρ − ρ(· + h v)‖₁`. -/
theorem integral_min_translate (hρ : IsProbDensityOn univ ρ) (v : Euc d) (h : ℝ) :
    ∫ x, min (ρ x) (ρ (x + h • v)) = 1 - (1 / 2) * ∫ x, |ρ x - ρ (x + h • v)| := by
  have h1 : Integrable ρ := hρ.integrable
  have h2 : Integrable fun x => ρ (x + h • v) := h1.comp_add_right (h • v)
  have h3 : Integrable fun x => |ρ x - ρ (x + h • v)| := (h1.sub h2).abs
  have hpt : ∀ x, min (ρ x) (ρ (x + h • v)) =
      (1 / 2) * ((ρ x + ρ (x + h • v)) - |ρ x - ρ (x + h • v)|) := by
    intro x
    have e1 := max_sub_min_eq_abs (ρ x) (ρ (x + h • v))
    have e2 := min_add_max (ρ x) (ρ (x + h • v))
    rw [abs_sub_comm] at e1
    linarith
  have h12 : Integrable fun x => ρ x + ρ (x + h • v) := h1.add h2
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub h12 h3, integral_add h1 h2, hρ.integral_eq_one,
    integral_add_right_eq_self (μ := volume) (fun x => ρ x) (h • v), hρ.integral_eq_one]
  ring

/-- The overlap is even in `h`. -/
theorem integral_min_translate_neg (ρ : Euc d → ℝ) (v : Euc d) (h : ℝ) :
    ∫ x, min (ρ x) (ρ (x + (-h) • v)) = ∫ x, min (ρ x) (ρ (x + h • v)) := by
  have := integral_add_right_eq_self (μ := volume)
    (fun x => min (ρ x) (ρ (x + (-h) • v))) (h • v)
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [min_comm, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]

/-- The overlap is nonnegative. -/
theorem integral_min_translate_nonneg (hρ : IsProbDensityOn univ ρ) (v : Euc d) (h : ℝ) :
    0 ≤ ∫ x, min (ρ x) (ρ (x + h • v)) :=
  integral_nonneg fun _ => le_min (hρ.nonneg _) (hρ.nonneg _)

/-- The overlap is at most one. -/
theorem integral_min_translate_le_one (hρ : IsProbDensityOn univ ρ) (v : Euc d) (h : ℝ) :
    ∫ x, min (ρ x) (ρ (x + h • v)) ≤ 1 := by
  rw [← hρ.integral_eq_one]
  exact integral_mono (hρ.integrable.inf (hρ.integrable.comp_add_right (h • v))) hρ.integrable
    fun _ => min_le_left _ _

/-- The overlap is measurable in `h`. -/
theorem measurable_integral_min_translate (hρ : IsProbDensityOn univ ρ) (v : Euc d) :
    Measurable fun h : ℝ => ∫ x, min (ρ x) (ρ (x + h • v)) := by
  simp_rw [integral_min_translate hρ v]
  exact measurable_const.sub (measurable_const.mul (measurable_integral_abs_sub_translate hρ v))

/-- `0 ≤ ‖ρ − ρ(· + h v)‖₁ ≤ 2`. -/
theorem integral_abs_sub_translate_le_two (hρ : IsProbDensityOn univ ρ) (v : Euc d) (h : ℝ) :
    ∫ x, |ρ x - ρ (x + h • v)| ≤ 2 := by
  have := integral_min_translate hρ v h
  have := integral_min_translate_nonneg hρ v h
  linarith

end Overlap

end Komlos
