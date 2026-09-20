import Komlos.Defs

/-!
# One-dimensional symmetric decreasing rearrangement (auxiliary to paper Lemma 4.2)

For a real function `f : ℝ → ℝ` we consider its distribution function
`distFn f t = |{s : t < f s}|` (paper (4.1), `μ(y, t)` on a single fiber) and the
rearrangement formula
`rearrFormula f s = ∫_0^∞ 𝟙{2|s| < distFn f t} dt ∈ [0, ∞]`,
whose finite part `symRearr1 f s = (rearrFormula f s).toReal` is the symmetric decreasing
rearrangement `f⋆` (with the paper's convention `f⋆ = 0` where the formula is infinite).
`Komlos.symRearr R (y, s)` is definitionally `symRearr1 (R (y, ·)) s`.

Main facts (all for measurable nonnegative `f`, `g`):
* `lintegral_rearrFormula`: `∫ rearrFormula f = ∫ f` (Tonelli + layer cake);
* `lintegral_symRearr1`: mass preservation `∫ f⋆ = ∫ f` for `f ∈ L¹`;
* `lintegral_ofReal_min_le_lintegral_min_rearrFormula`: `∫ min(f, g) ≤ ∫ min(f⋆, g⋆)`
  (the level sets `{t : 2|s| < distFn f t}` are nested initial segments of `(0, ∞)`, so
  the minimum of two rearrangement formulas is again a rearrangement formula);
* `lintegral_enorm_symRearr1_sub_le`: the contraction `‖f⋆ − g⋆‖₁ ≤ ‖f − g‖₁`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Komlos

/-! ### The distribution function -/

/-- The distribution function `t ↦ |{s : t < f s}|` of a real function on `ℝ`
(paper (4.1) on a single fiber). -/
noncomputable def distFn (f : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ := volume {s | t < f s}

theorem fiberDist_eq_distFn {d : ℕ} (R : Euc d × ℝ → ℝ) (y : Euc d) (t : ℝ) :
    fiberDist R y t = distFn (fun s => R (y, s)) t := rfl

theorem distFn_antitone (f : ℝ → ℝ) : Antitone (distFn f) := fun _ _ h =>
  measure_mono fun _ hs => lt_of_le_of_lt h hs

theorem measurable_distFn (f : ℝ → ℝ) : Measurable (distFn f) :=
  (distFn_antitone f).measurable

/-- `{s : 2|s| < r}` is the centred open interval of length `r` (empty for `r ≤ 0`). -/
theorem setOf_ofReal_twoAbs_lt_ofReal (r : ℝ) :
    {s : ℝ | ENNReal.ofReal (2 * |s|) < ENNReal.ofReal r} = Ioo (-(r / 2)) (r / 2) := by
  ext s
  simp only [mem_ofPred_eq, mem_Ioo, ENNReal.ofReal_lt_ofReal_iff']
  constructor
  · rintro ⟨h1, -⟩
    exact abs_lt.mp (by linarith)
  · rintro ⟨h1, h2⟩
    have h3 : |s| < r / 2 := abs_lt.mpr ⟨h1, h2⟩
    exact ⟨by linarith, by linarith [abs_nonneg s]⟩

/-- `|{s : 2|s| < m}| = m` for every `m ∈ [0, ∞]`: the set is the centred open interval of
length `m`. -/
theorem volume_twoAbs_lt (m : ℝ≥0∞) :
    volume {s : ℝ | ENNReal.ofReal (2 * |s|) < m} = m := by
  rcases eq_or_ne m ⊤ with rfl | hm
  · have : {s : ℝ | ENNReal.ofReal (2 * |s|) < ⊤} = univ :=
      eq_univ_of_forall fun _ => ENNReal.ofReal_lt_top
    rw [this, Real.volume_univ]
  · conv_lhs => rw [← ENNReal.ofReal_toReal hm]
    rw [setOf_ofReal_twoAbs_lt_ofReal, Real.volume_Ioo,
      show m.toReal / 2 - -(m.toReal / 2) = m.toReal by ring, ENNReal.ofReal_toReal hm]

theorem measurable_ofReal_twoAbs : Measurable fun s : ℝ => ENNReal.ofReal (2 * |s|) :=
  (measurable_const.mul continuous_abs.measurable).ennreal_ofReal

/-! ### The rearrangement formula -/

/-- The rearrangement formula `∫_0^∞ 𝟙{2|s| < distFn f t} dt ∈ [0, ∞]` (paper (4.1)). -/
noncomputable def rearrFormula (f : ℝ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ),
    {t | ENNReal.ofReal (2 * |s|) < distFn f t}.indicator (fun _ => (1 : ℝ≥0∞)) t

/-- The symmetric decreasing rearrangement `f⋆`, with the value `0` where the formula is
infinite. -/
noncomputable def symRearr1 (f : ℝ → ℝ) (s : ℝ) : ℝ := (rearrFormula f s).toReal

theorem symRearr_eq_symRearr1 {d : ℕ} (R : Euc d × ℝ → ℝ) (p : Euc d × ℝ) :
    symRearr R p = symRearr1 (fun s => R (p.1, s)) p.2 := rfl

theorem symRearr1_nonneg (f : ℝ → ℝ) (s : ℝ) : 0 ≤ symRearr1 f s := ENNReal.toReal_nonneg

/-- The level set `{t : 2|s| < distFn f t}` is an initial segment of `ℝ`. -/
theorem isLowerSet_levelSet (f : ℝ → ℝ) (s : ℝ) :
    IsLowerSet {t | ENNReal.ofReal (2 * |s|) < distFn f t} :=
  fun _ _ h ht => lt_of_lt_of_le ht (distFn_antitone f h)

theorem measurableSet_levelSet (f : ℝ → ℝ) (s : ℝ) :
    MeasurableSet {t | ENNReal.ofReal (2 * |s|) < distFn f t} :=
  measurableSet_lt measurable_const (measurable_distFn f)

theorem rearrFormula_eq_volume (f : ℝ → ℝ) (s : ℝ) :
    rearrFormula f s = volume ({t | ENNReal.ofReal (2 * |s|) < distFn f t} ∩ Ioi 0) := by
  unfold rearrFormula
  rw [lintegral_indicator_const (measurableSet_levelSet f s), one_mul,
    Measure.restrict_apply (measurableSet_levelSet f s)]

/-- For nested sets the measure of the intersection is the minimum of the measures. -/
theorem measure_inter_eq_min_of_nested {α : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {A B : Set α} (h : A ⊆ B ∨ B ⊆ A) : μ (A ∩ B) = min (μ A) (μ B) := by
  rcases h with h | h
  · rw [inter_eq_left.mpr h, min_eq_left (measure_mono h)]
  · rw [inter_eq_right.mpr h, min_eq_right (measure_mono h)]

/-- The minimum of two rearrangement formulas is the rearrangement formula of the minimum
of the distribution functions (nested centred intervals). -/
theorem min_rearrFormula (f g : ℝ → ℝ) (s : ℝ) :
    min (rearrFormula f s) (rearrFormula g s) =
      volume ({t | ENNReal.ofReal (2 * |s|) < min (distFn f t) (distFn g t)} ∩ Ioi 0) := by
  rw [rearrFormula_eq_volume, rearrFormula_eq_volume, ← measure_inter_eq_min_of_nested]
  · congr 1
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, lt_min_iff]
    tauto
  · rcases (isLowerSet_levelSet f s).total (isLowerSet_levelSet g s) with h | h
    · exact Or.inl (inter_subset_inter_left _ h)
    · exact Or.inr (inter_subset_inter_left _ h)

/-- Tonelli: `∫ |{t > 0 : 2|s| < m t}| ds = ∫_0^∞ m(t) dt` for measurable `m`. -/
theorem lintegral_volume_levelSet (m : ℝ → ℝ≥0∞) (hm : Measurable m) :
    ∫⁻ s, volume ({t | ENNReal.ofReal (2 * |s|) < m t} ∩ Ioi 0) = ∫⁻ t in Ioi 0, m t := by
  have hS : MeasurableSet {q : ℝ × ℝ | ENNReal.ofReal (2 * |q.1|) < m q.2} :=
    measurableSet_lt (measurable_ofReal_twoAbs.comp measurable_fst) (hm.comp measurable_snd)
  have hSm : Measurable ({q : ℝ × ℝ | ENNReal.ofReal (2 * |q.1|) < m q.2}.indicator
      fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hS
  calc ∫⁻ s, volume ({t | ENNReal.ofReal (2 * |s|) < m t} ∩ Ioi 0)
      = ∫⁻ s, ∫⁻ t in Ioi 0, {q : ℝ × ℝ | ENNReal.ofReal (2 * |q.1|) < m q.2}.indicator
          (fun _ => (1 : ℝ≥0∞)) (s, t) := by
        refine lintegral_congr fun s => ?_
        have hs : MeasurableSet {t | ENNReal.ofReal (2 * |s|) < m t} :=
          measurableSet_lt measurable_const hm
        calc volume ({t | ENNReal.ofReal (2 * |s|) < m t} ∩ Ioi 0)
            = ∫⁻ t in Ioi 0,
                {t | ENNReal.ofReal (2 * |s|) < m t}.indicator (fun _ => (1 : ℝ≥0∞)) t := by
              rw [lintegral_indicator_const hs, one_mul, Measure.restrict_apply hs]
          _ = _ := lintegral_congr fun t => by simp only [indicator_apply, mem_ofPred_eq]
    _ = ∫⁻ t in Ioi 0, ∫⁻ s, {q : ℝ × ℝ | ENNReal.ofReal (2 * |q.1|) < m q.2}.indicator
          (fun _ => (1 : ℝ≥0∞)) (s, t) :=
        lintegral_lintegral_swap hSm.aemeasurable
    _ = ∫⁻ t in Ioi 0, m t := by
        refine lintegral_congr fun t => ?_
        have ht : MeasurableSet {s : ℝ | ENNReal.ofReal (2 * |s|) < m t} :=
          measurableSet_lt measurable_ofReal_twoAbs measurable_const
        calc ∫⁻ s, {q : ℝ × ℝ | ENNReal.ofReal (2 * |q.1|) < m q.2}.indicator
              (fun _ => (1 : ℝ≥0∞)) (s, t)
            = ∫⁻ s, {s : ℝ | ENNReal.ofReal (2 * |s|) < m t}.indicator
                (fun _ => (1 : ℝ≥0∞)) s :=
              lintegral_congr fun s => by simp only [indicator_apply, mem_ofPred_eq]
          _ = m t := by rw [lintegral_indicator_const ht, one_mul, volume_twoAbs_lt]

/-- Mass identity for the formula: `∫ rearrFormula f = ∫ f` (Tonelli and layer cake). -/
theorem lintegral_rearrFormula (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ s, 0 ≤ f s) :
    ∫⁻ s, rearrFormula f s = ∫⁻ s, ENNReal.ofReal (f s) := by
  simp_rw [rearrFormula_eq_volume]
  rw [lintegral_volume_levelSet (distFn f) (measurable_distFn f),
    lintegral_eq_lintegral_meas_lt volume (ae_of_all _ h0) hf.aemeasurable]
  rfl

theorem measurable_rearrFormula (f : ℝ → ℝ) : Measurable (rearrFormula f) := by
  have hS : MeasurableSet {q : ℝ × ℝ | ENNReal.ofReal (2 * |q.1|) < distFn f q.2} :=
    measurableSet_lt (measurable_ofReal_twoAbs.comp measurable_fst)
      ((measurable_distFn f).comp measurable_snd)
  have : rearrFormula f = fun s =>
      ∫⁻ t, {q : ℝ × ℝ | ENNReal.ofReal (2 * |q.1|) < distFn f q.2}.indicator
        (fun _ => (1 : ℝ≥0∞)) (s, t) ∂(volume.restrict (Ioi 0)) := by
    ext s
    unfold rearrFormula
    exact lintegral_congr fun t => by simp only [indicator_apply, mem_ofPred_eq]
  rw [this]
  exact (measurable_const.indicator hS).lintegral_prod_right'

theorem measurable_symRearr1 (f : ℝ → ℝ) : Measurable (symRearr1 f) :=
  (measurable_rearrFormula f).ennreal_toReal

theorem ae_rearrFormula_lt_top (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ s, 0 ≤ f s)
    (hfin : ∫⁻ s, ENNReal.ofReal (f s) ≠ ⊤) : ∀ᵐ s, rearrFormula f s < ⊤ :=
  ae_lt_top (measurable_rearrFormula f) (by rwa [lintegral_rearrFormula f hf h0])

theorem ofReal_symRearr1_ae_eq (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ s, 0 ≤ f s)
    (hfin : ∫⁻ s, ENNReal.ofReal (f s) ≠ ⊤) :
    (fun s => ENNReal.ofReal (symRearr1 f s)) =ᵐ[volume] rearrFormula f := by
  filter_upwards [ae_rearrFormula_lt_top f hf h0 hfin] with s hs
  exact ENNReal.ofReal_toReal hs.ne

/-- Mass preservation `∫ f⋆ = ∫ f` for nonnegative `f ∈ L¹(ℝ)` (paper Lemma 4.2). -/
theorem lintegral_symRearr1 (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ s, 0 ≤ f s)
    (hfin : ∫⁻ s, ENNReal.ofReal (f s) ≠ ⊤) :
    ∫⁻ s, ENNReal.ofReal (symRearr1 f s) = ∫⁻ s, ENNReal.ofReal (f s) := by
  rw [lintegral_congr_ae (ofReal_symRearr1_ae_eq f hf h0 hfin), lintegral_rearrFormula f hf h0]

/-! ### The contraction -/

/-- Layer cake and nesting of centred intervals: `∫ min(f, g) ≤ ∫ min(f⋆, g⋆)`
(paper Lemma 4.2, proof of (4.4)). -/
theorem lintegral_ofReal_min_le_lintegral_min_rearrFormula (f g : ℝ → ℝ) (hf : Measurable f)
    (hg : Measurable g) (h0f : ∀ s, 0 ≤ f s) (h0g : ∀ s, 0 ≤ g s) :
    ∫⁻ s, ENNReal.ofReal (min (f s) (g s)) ≤
      ∫⁻ s, min (rearrFormula f s) (rearrFormula g s) := by
  simp_rw [min_rearrFormula]
  rw [lintegral_volume_levelSet _ ((measurable_distFn f).min (measurable_distFn g)),
    lintegral_eq_lintegral_meas_lt volume (ae_of_all _ fun s => le_min (h0f s) (h0g s))
      (hf.min hg).aemeasurable]
  refine lintegral_mono fun t => le_min
    (measure_mono fun s (hs : t < min (f s) (g s)) => ?_)
    (measure_mono fun s (hs : t < min (f s) (g s)) => ?_)
  · exact lt_of_lt_of_le hs (min_le_left _ _)
  · exact lt_of_lt_of_le hs (min_le_right _ _)

/-- `a + b = |a − b| + 2 min(a, b)` for `a, b ≥ 0`, in `ℝ≥0∞`. -/
theorem ofReal_add_ofReal_eq_enorm_sub_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a + ENNReal.ofReal b = ‖a - b‖ₑ + 2 * ENNReal.ofReal (min a b) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add ha hb, two_mul,
    ← ENNReal.ofReal_add (le_min ha hb) (le_min ha hb),
    ← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
  congr 1
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- `∫ φ + ∫ ψ = ‖φ − ψ‖₁ + 2 ∫ min(φ, ψ)` for nonnegative measurable `φ, ψ`. -/
theorem lintegral_add_eq_lintegral_enorm_sub_add (φ ψ : ℝ → ℝ) (hφ : Measurable φ)
    (hψ : Measurable ψ) (h0φ : ∀ s, 0 ≤ φ s) (h0ψ : ∀ s, 0 ≤ ψ s) :
    (∫⁻ s, ENNReal.ofReal (φ s)) + ∫⁻ s, ENNReal.ofReal (ψ s) =
      (∫⁻ s, ‖φ s - ψ s‖ₑ) + 2 * ∫⁻ s, ENNReal.ofReal (min (φ s) (ψ s)) := by
  have hm : Measurable fun s => ‖φ s - ψ s‖ₑ := (hφ.sub hψ).enorm
  rw [← lintegral_add_left hφ.ennreal_ofReal, ← lintegral_const_mul 2 (hφ.min hψ).ennreal_ofReal,
    ← lintegral_add_left hm]
  exact lintegral_congr fun s => ofReal_add_ofReal_eq_enorm_sub_add _ _ (h0φ s) (h0ψ s)

/-- The contraction `‖f⋆ − g⋆‖₁ ≤ ‖f − g‖₁` for nonnegative `f, g ∈ L¹(ℝ)`
(paper Lemma 4.2, one-dimensional form of (4.4)). -/
theorem lintegral_enorm_symRearr1_sub_le (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (h0f : ∀ s, 0 ≤ f s) (h0g : ∀ s, 0 ≤ g s) (hfin : ∫⁻ s, ENNReal.ofReal (f s) ≠ ⊤)
    (hgin : ∫⁻ s, ENNReal.ofReal (g s) ≠ ⊤) :
    ∫⁻ s, ‖symRearr1 f s - symRearr1 g s‖ₑ ≤ ∫⁻ s, ‖f s - g s‖ₑ := by
  have h1 := lintegral_add_eq_lintegral_enorm_sub_add f g hf hg h0f h0g
  have h2 := lintegral_add_eq_lintegral_enorm_sub_add (symRearr1 f) (symRearr1 g)
    (measurable_symRearr1 f) (measurable_symRearr1 g) (symRearr1_nonneg f) (symRearr1_nonneg g)
  rw [lintegral_symRearr1 f hf h0f hfin, lintegral_symRearr1 g hg h0g hgin] at h2
  -- `∫ min(f, g) ≤ ∫ min(f⋆, g⋆)`
  have hA : ∫⁻ s, ENNReal.ofReal (min (f s) (g s)) ≤
      ∫⁻ s, ENNReal.ofReal (min (symRearr1 f s) (symRearr1 g s)) := by
    refine (lintegral_ofReal_min_le_lintegral_min_rearrFormula f g hf hg h0f h0g).trans
      (le_of_eq (lintegral_congr_ae ?_))
    filter_upwards [ae_rearrFormula_lt_top f hf h0f hfin, ae_rearrFormula_lt_top g hg h0g hgin]
      with s hs1 hs2
    unfold symRearr1
    rw [← ENNReal.toReal_min hs1.ne hs2.ne,
      ENNReal.ofReal_toReal ((min_le_left _ _).trans_lt hs1).ne]
  have hfin2 : 2 * ∫⁻ s, ENNReal.ofReal (min (symRearr1 f s) (symRearr1 g s)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfin, hgin⟩) ?_
    rw [h2]
    exact le_add_self
  have key : (∫⁻ s, ‖symRearr1 f s - symRearr1 g s‖ₑ) +
      2 * ∫⁻ s, ENNReal.ofReal (min (symRearr1 f s) (symRearr1 g s)) ≤
      (∫⁻ s, ‖f s - g s‖ₑ) +
        2 * ∫⁻ s, ENNReal.ofReal (min (symRearr1 f s) (symRearr1 g s)) := by
    rw [← h2, h1]
    gcongr
  exact (ENNReal.add_le_add_iff_right hfin2).mp key

end Komlos
