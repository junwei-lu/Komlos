import Komlos.Defs

/-!
# Elementary properties of the directional variation (paper Lemma 3.1 and §2)

Everything here follows from the translation definition `Komlos.dirVar`:
* the translation estimate `‖f(· + h u) − f‖₁ ≤ |h| V_u f` (paper (3.1), first part);
* the limit formula (paper (3.1), second part) — a Fekete-type argument using the
  subadditivity of `h ↦ ‖f(· + h u) − f‖₁` and continuity of translation in `L¹`;
* homogeneity and subadditivity in `u`, convexity in `f`, lower semicontinuity in `L¹`;
* the coordinate bounds `|Df|(ℝ^d) ≤ ∑ V_{e_i} f` used in Lemmas 3.1 and 3.3;
* the `W^{1,1}` bound `V_u f ≤ ∫ |∂_u f|` for `C¹` compactly supported `f`
  (paper, after (2.1)), used for the cube density (Lemma 2.4);
* existence of some `ρ ∈ 𝒫(K)` on every nonempty open set (used in Lemma 3.4 to see
  that `h_H(D_t) < ∞`).

## Implementation notes

* The lower Lebesgue integral `∫⁻` is *not* subadditive on non-measurable functions, so the
  statements involving two different functions (`dirVar_add_fun_le`, `dirVar_le_liminf`)
  carry measurability hypotheses.  `dirVar_le_liminf` is false without them: on `ℝ` take
  `f n = 0` and `g = 𝟙_A` with `A = B ∪ (([0,1) ∖ B) + 1)` for a Bernstein-type set
  `B ⊆ [0,1)` (both `B` and `[0,1) ∖ B` have inner measure `0`); then `∫⁻ 𝟙_A = 0` while
  `(A − 1) Δ A ⊇ [0,1)`, so `dirVar 1 g ≥ 1 > 0`.
* Continuity of translation in `L¹` (`tendsto_lintegral_translate_sub`, and hence the limit
  formula `dirVar_tendsto`) is proved by approximation with continuous compactly supported
  functions, which needs `E` to be locally compact (`[ProperSpace E]`, i.e. finite
  dimensional).  All applications are on `Euc d` or `Euc d × ℝ`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

-- The section variables are the paper's standing hypotheses; not every lemma needs all of them.
set_option linter.unusedSectionVars false

namespace Komlos

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [BorelSpace E] [SecondCountableTopology E] [(volume : Measure E).IsAddHaarMeasure]

/-! ### Auxiliary lemmas on the translation modulus -/

/-- Translation invariance of the Lebesgue integral on `E` (right invariance of a Haar measure on
a commutative group). -/
theorem lintegral_translate (g : E → ℝ≥0∞) (v : E) : ∫⁻ x, g (x + v) = ∫⁻ x, g x :=
  lintegral_add_right_eq_self g v

/-- Triangle inequality for `∫⁻ ‖· − ·‖ₑ`; one of the two differences must be a.e.-measurable
for the lower integral to be additive. -/
theorem lintegral_enorm_sub_le_add {a b c : E → ℝ}
    (hab : AEMeasurable (fun x => ‖a x - b x‖ₑ)) :
    ∫⁻ x, ‖a x - c x‖ₑ ≤ (∫⁻ x, ‖a x - b x‖ₑ) + ∫⁻ x, ‖b x - c x‖ₑ := by
  calc ∫⁻ x, ‖a x - c x‖ₑ ≤ ∫⁻ x, (‖a x - b x‖ₑ + ‖b x - c x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        rw [show a x - c x = (a x - b x) + (b x - c x) by ring]
        exact enorm_add_le _ _
    _ = _ := lintegral_add_left' hab _

theorem aemeasurable_enorm_sub_translate {f : E → ℝ} (hf : AEMeasurable f) (v w : E) :
    AEMeasurable fun x => ‖f (x + v) - f (x + w)‖ₑ :=
  ((hf.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume v).quasiMeasurePreserving).sub
    (hf.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume w).quasiMeasurePreserving)).enorm

theorem aemeasurable_enorm_translate_sub {f : E → ℝ} (hf : AEMeasurable f) (v : E) :
    AEMeasurable fun x => ‖f (x + v) - f x‖ₑ :=
  ((hf.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume v).quasiMeasurePreserving).sub hf).enorm

theorem measurable_enorm_translate_sub {f : E → ℝ} (hf : Measurable f) (v : E) :
    Measurable fun x => ‖f (x + v) - f x‖ₑ :=
  ((hf.comp (measurable_add_const v)).sub hf).enorm

/-- The translation modulus is even. -/
theorem lintegral_translate_sub_neg (u : E) (f : E → ℝ) (h : ℝ) :
    ∫⁻ x, ‖f (x + (-h) • u) - f x‖ₑ = ∫⁻ x, ‖f (x + h • u) - f x‖ₑ := by
  rw [← lintegral_translate (fun x => ‖f (x + (-h) • u) - f x‖ₑ) (h • u)]
  refine lintegral_congr fun x => ?_
  have hx : x + h • u + (-h) • u = x := by
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  show ‖f (x + h • u + (-h) • u) - f (x + h • u)‖ₑ = _
  rw [hx, enorm_sub_rev]

/-- Each difference quotient is bounded by the directional variation. -/
theorem div_le_dirVar (u : E) (f : E → ℝ) {h : ℝ} (hh : 0 < h) :
    (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) / ENNReal.ofReal h ≤ dirVar u f :=
  le_iSup₂ (f := fun (h : ℝ) (_ : 0 < h) =>
    (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) / ENNReal.ofReal h) h hh

/-- Paper (3.1), first part, for `h > 0` (no measurability needed). -/
theorem lintegral_translate_sub_le_of_pos (u : E) (f : E → ℝ) {h : ℝ} (hh : 0 < h) :
    ∫⁻ x, ‖f (x + h • u) - f x‖ₑ ≤ ENNReal.ofReal h * dirVar u f := by
  have := div_le_dirVar u f hh
  rwa [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hh).ne' ENNReal.ofReal_ne_top, mul_comm] at this

/-- To bound `dirVar u f` it suffices to bound every translation modulus linearly. -/
theorem dirVar_le_of_forall (u : E) (f : E → ℝ) {M : ℝ≥0∞}
    (H : ∀ h : ℝ, 0 < h → ∫⁻ x, ‖f (x + h • u) - f x‖ₑ ≤ M * ENNReal.ofReal h) :
    dirVar u f ≤ M :=
  iSup₂_le fun h hh => ENNReal.div_le_of_le_mul (H h hh)

/-- A quantity that is eventually below `u + v` with `v → 0` is below `liminf u`. -/
theorem le_liminf_of_eventually_le_add {ι : Type*} {l : Filter ι} {a : ℝ≥0∞}
    {u v : ι → ℝ≥0∞} (hv : Tendsto v l (𝓝 0)) (h : ∀ᶠ i in l, a ≤ u i + v i) :
    a ≤ liminf u l := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hv' := ENNReal.tendsto_nhds_zero.1 hv ε hε'
  have : a - ε ≤ liminf u l := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [h, hv'] with i hi hvi
    exact tsub_le_iff_right.2 (hi.trans (add_le_add le_rfl hvi))
  exact tsub_le_iff_right.1 this

/-! ### Paper (3.1), first part -/

/-- Paper (3.1), first part: `‖f(· + h u) − f‖₁ ≤ |h| V_u f`, for every real `h`
(the case `h < 0` uses translation invariance of Lebesgue measure). -/
theorem lintegral_translate_sub_le (u : E) (f : E → ℝ) (hf : Measurable f) (h : ℝ) :
    ∫⁻ x, ‖f (x + h • u) - f x‖ₑ ≤ ENNReal.ofReal |h| * dirVar u f := by
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have e := lintegral_translate_sub_neg u f (-h)
    rw [neg_neg] at e
    rw [abs_of_neg hh, e]
    exact lintegral_translate_sub_le_of_pos u f (neg_pos.2 hh)
  · simp
  · rw [abs_of_pos hh]
    exact lintegral_translate_sub_le_of_pos u f hh

/-- Subadditivity of the translation modulus, a.e.-measurable version. -/
theorem lintegral_translate_sub_add_le' (u : E) (f : E → ℝ) (hf : AEMeasurable f) (h k : ℝ) :
    ∫⁻ x, ‖f (x + (h + k) • u) - f x‖ₑ ≤
      (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) + ∫⁻ x, ‖f (x + k • u) - f x‖ₑ := by
  calc ∫⁻ x, ‖f (x + (h + k) • u) - f x‖ₑ
      ≤ (∫⁻ x, ‖f (x + (h + k) • u) - f (x + k • u)‖ₑ) + ∫⁻ x, ‖f (x + k • u) - f x‖ₑ :=
        lintegral_enorm_sub_le_add (aemeasurable_enorm_sub_translate hf _ _)
    _ = (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) + ∫⁻ x, ‖f (x + k • u) - f x‖ₑ := by
        congr 1
        rw [← lintegral_translate (fun x => ‖f (x + h • u) - f x‖ₑ) (k • u)]
        refine lintegral_congr fun x => ?_
        rw [add_assoc, ← add_smul, add_comm k h]

/-- Subadditivity of the translation modulus: `g(h + k) ≤ g(h) + g(k)`. -/
theorem lintegral_translate_sub_add_le (u : E) (f : E → ℝ) (hf : Measurable f) (h k : ℝ) :
    ∫⁻ x, ‖f (x + (h + k) • u) - f x‖ₑ ≤
      (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) + ∫⁻ x, ‖f (x + k • u) - f x‖ₑ :=
  lintegral_translate_sub_add_le' u f hf.aemeasurable h k

/-- Iterated subadditivity: `g(n h) ≤ n g(h)`. -/
theorem lintegral_translate_sub_nsmul_le (u : E) (f : E → ℝ) (hf : AEMeasurable f) (n : ℕ)
    (h : ℝ) :
    ∫⁻ x, ‖f (x + ((n : ℝ) * h) • u) - f x‖ₑ ≤ n * ∫⁻ x, ‖f (x + h • u) - f x‖ₑ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x, ‖f (x + (((n + 1 : ℕ) : ℝ) * h) • u) - f x‖ₑ
        = ∫⁻ x, ‖f (x + ((n : ℝ) * h + h) • u) - f x‖ₑ := by push_cast; ring_nf
      _ ≤ (∫⁻ x, ‖f (x + ((n : ℝ) * h) • u) - f x‖ₑ) + ∫⁻ x, ‖f (x + h • u) - f x‖ₑ :=
          lintegral_translate_sub_add_le' u f hf _ _
      _ ≤ n * (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) + ∫⁻ x, ‖f (x + h • u) - f x‖ₑ :=
          add_le_add ih le_rfl
      _ = _ := by push_cast; ring

/-! ### Continuity of translation and the limit formula -/

/-- Continuity of translation in `L¹` for continuous compactly supported functions
(dominated convergence). -/
theorem tendsto_lintegral_translate_sub_of_continuous [ProperSpace E] (u : E) (g : E → ℝ)
    (hg : Continuous g) (hsupp : HasCompactSupport g) :
    Tendsto (fun h : ℝ => ∫⁻ x, ‖g (x + h • u) - g x‖ₑ) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hsupp
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  obtain ⟨R, hR⟩ := (IsCompact.isBounded hsupp).subset_closedBall (0 : E)
  set B := Metric.closedBall (0 : E) (R + ‖u‖) with hB
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have key : Tendsto (fun h : ℝ => ∫⁻ x, ‖g (x + h • u) - g x‖ₑ) (𝓝 0)
      (𝓝 (∫⁻ x, ‖g (x + (0 : ℝ) • u) - g x‖ₑ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (B.indicator fun _ => ENNReal.ofReal (2 * C)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun h =>
        ((hg.comp (continuous_id.add continuous_const)).sub hg).enorm.measurable
    · filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with h hh
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hh
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx]
        calc ‖g (x + h • u) - g x‖ₑ ≤ ‖g (x + h • u)‖ₑ + ‖g x‖ₑ := enorm_sub_le
          _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := by
              gcongr
              · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hC _)
              · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hC _)
          _ = ENNReal.ofReal (2 * C) := by rw [two_mul, ENNReal.ofReal_add hC0 hC0]
      · rw [indicator_of_notMem hx]
        have hx' : R + ‖u‖ < ‖x‖ := by
          rw [hB, Metric.mem_closedBall, dist_zero_right, not_le] at hx
          exact hx
        have hhu : ‖h • u‖ ≤ ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg u) hh
        have h1 : g x = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hm => ?_
          have := hR hm
          rw [Metric.mem_closedBall, dist_zero_right] at this
          linarith [norm_nonneg u]
        have h2 : g (x + h • u) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hm => ?_
          have := hR hm
          rw [Metric.mem_closedBall, dist_zero_right] at this
          have : ‖x‖ ≤ ‖x + h • u‖ + ‖h • u‖ := by
            simpa using norm_sub_le (x + h • u) (h • u)
          linarith
        simp [h1, h2]
    · rw [lintegral_indicator_const hBm]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun x => ?_
      have h1 : Tendsto (fun h : ℝ => x + h • u) (𝓝 0) (𝓝 (x + (0 : ℝ) • u)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      have h2 : Tendsto (fun h : ℝ => g (x + h • u) - g x) (𝓝 0)
          (𝓝 (g (x + (0 : ℝ) • u) - g x)) :=
        ((hg.tendsto _).comp h1).sub tendsto_const_nhds
      exact (continuous_enorm.tendsto _).comp h2
  simpa using key

/-- Continuity of translation in `L¹`. -/
theorem tendsto_lintegral_translate_sub [ProperSpace E] (u : E) (f : E → ℝ)
    (hf : Integrable f) :
    Tendsto (fun h : ℝ => ∫⁻ x, ‖f (x + h • u) - f x‖ₑ) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top
  obtain ⟨g, hgs, hfg, hgc, -⟩ :=
    hf.exists_hasCompactSupport_lintegral_sub_le (ε := ε / 3) hε3.ne'
  have hg := tendsto_lintegral_translate_sub_of_continuous u g hgc hgs
  rw [ENNReal.tendsto_nhds_zero] at hg
  filter_upwards [hg (ε / 3) hε3] with h hh
  have hfa : AEMeasurable f := hf.aemeasurable
  have hga : AEMeasurable g := hgc.measurable.aemeasurable
  have e1 : ∫⁻ x, ‖f (x + h • u) - g (x + h • u)‖ₑ = ∫⁻ x, ‖f x - g x‖ₑ :=
    lintegral_translate (fun x => ‖f x - g x‖ₑ) (h • u)
  have e2 : ∫⁻ x, ‖g x - f x‖ₑ = ∫⁻ x, ‖f x - g x‖ₑ :=
    lintegral_congr fun x => enorm_sub_rev _ _
  calc ∫⁻ x, ‖f (x + h • u) - f x‖ₑ
      ≤ (∫⁻ x, ‖f (x + h • u) - g (x + h • u)‖ₑ) + ∫⁻ x, ‖g (x + h • u) - f x‖ₑ :=
        lintegral_enorm_sub_le_add
          ((hfa.comp_quasiMeasurePreserving
              (measurePreserving_add_right volume (h • u)).quasiMeasurePreserving).sub
            (hga.comp_quasiMeasurePreserving
              (measurePreserving_add_right volume (h • u)).quasiMeasurePreserving)).enorm
    _ ≤ (∫⁻ x, ‖f (x + h • u) - g (x + h • u)‖ₑ) +
          ((∫⁻ x, ‖g (x + h • u) - g x‖ₑ) + ∫⁻ x, ‖g x - f x‖ₑ) :=
        add_le_add le_rfl (lintegral_enorm_sub_le_add (aemeasurable_enorm_translate_sub hga _))
    _ = (∫⁻ x, ‖f x - g x‖ₑ) + ((∫⁻ x, ‖g (x + h • u) - g x‖ₑ) + ∫⁻ x, ‖f x - g x‖ₑ) := by
        rw [e1, e2]
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := add_le_add hfg (add_le_add hh hfg)
    _ = ε := by rw [← add_assoc, ENNReal.add_thirds]

/-- Paper (3.1), second part: the difference quotients converge to `V_u f` as `h → 0⁺`
(including the value `+∞`).  Fekete's argument for the subadditive modulus. -/
theorem dirVar_tendsto [ProperSpace E] (u : E) (f : E → ℝ) (hf : Integrable f) :
    Tendsto (fun h : ℝ => (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) / ENNReal.ofReal h)
      (𝓝[>] 0) (𝓝 (dirVar u f)) := by
  set g : ℝ → ℝ≥0∞ := fun h => ∫⁻ x, ‖f (x + h • u) - f x‖ₑ with hg
  have hfa : AEMeasurable f := hf.aemeasurable
  have hcont : Tendsto g (𝓝 0) (𝓝 0) := tendsto_lintegral_translate_sub u f hf
  have hsub : ∀ a b : ℝ, g (a + b) ≤ g a + g b := fun a b =>
    lintegral_translate_sub_add_le' u f hfa a b
  have hnsmul : ∀ (n : ℕ) (a : ℝ), g ((n : ℝ) * a) ≤ n * g a := fun n a =>
    lintegral_translate_sub_nsmul_le u f hfa n a
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  -- upper bound: every difference quotient is at most the supremum
  have hsup : limsup (fun h => g h / ENNReal.ofReal h) (𝓝[>] 0) ≤ dirVar u f := by
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hpos] with h hh
    exact div_le_dirVar u f hh
  -- lower bound: Fekete
  have hinf : dirVar u f ≤ liminf (fun h => g h / ENNReal.ofReal h) (𝓝[>] 0) := by
    refine iSup₂_le fun h₀ hh₀ => ?_
    have hh0 : ENNReal.ofReal h₀ ≠ 0 := (ENNReal.ofReal_pos.2 hh₀).ne'
    -- the remainder `r h = h₀ - ⌊h₀ / h⌋₊ h ∈ [0, h)`
    obtain ⟨r, hr⟩ : ∃ r : ℝ → ℝ, r = fun h => h₀ - ⌊h₀ / h⌋₊ * h := ⟨_, rfl⟩
    have hr_nonneg : ∀ h : ℝ, 0 < h → 0 ≤ r h := by
      intro h hh
      have : (⌊h₀ / h⌋₊ : ℝ) * h ≤ h₀ := by
        calc (⌊h₀ / h⌋₊ : ℝ) * h ≤ h₀ / h * h := by
              gcongr; exact Nat.floor_le (div_nonneg hh₀.le hh.le)
          _ = h₀ := div_mul_cancel₀ h₀ hh.ne'
      rw [hr]; dsimp only; linarith
    have hr_lt : ∀ h : ℝ, 0 < h → r h < h := by
      intro h hh
      have : h₀ < (⌊h₀ / h⌋₊ : ℝ) * h + h := by
        calc h₀ = h₀ / h * h := (div_mul_cancel₀ h₀ hh.ne').symm
          _ < ((⌊h₀ / h⌋₊ : ℝ) + 1) * h := by gcongr; exact Nat.lt_floor_add_one _
          _ = (⌊h₀ / h⌋₊ : ℝ) * h + h := by ring
      rw [hr]; dsimp only; linarith
    have hr_tendsto : Tendsto r (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_id.mono_left nhdsWithin_le_nhds) ?_ ?_
      · filter_upwards [hpos] with h hh; exact hr_nonneg h hh
      · filter_upwards [hpos] with h hh; exact (hr_lt h hh).le
    have hv : Tendsto (fun h => g (r h) / ENNReal.ofReal h₀) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.div_const (hcont.comp hr_tendsto) (Or.inr hh0)
      simpa using this
    refine le_liminf_of_eventually_le_add hv ?_
    filter_upwards [hpos] with h hh
    -- `g h₀ ≤ n g h + g (r h)` with `n = ⌊h₀ / h⌋₊`
    have hsplit : g h₀ ≤ (⌊h₀ / h⌋₊ : ℝ≥0∞) * g h + g (r h) := by
      have e : (⌊h₀ / h⌋₊ : ℝ) * h + r h = h₀ := by rw [hr]; dsimp only; ring
      calc g h₀ = g ((⌊h₀ / h⌋₊ : ℝ) * h + r h) := by rw [e]
        _ ≤ g ((⌊h₀ / h⌋₊ : ℝ) * h) + g (r h) := hsub _ _
        _ ≤ (⌊h₀ / h⌋₊ : ℝ≥0∞) * g h + g (r h) := add_le_add (hnsmul _ _) le_rfl
    -- `n g h / h₀ ≤ g h / h`
    have hquot : (⌊h₀ / h⌋₊ : ℝ≥0∞) * g h / ENNReal.ofReal h₀ ≤ g h / ENNReal.ofReal h := by
      rw [ENNReal.div_le_iff hh0 ENNReal.ofReal_ne_top]
      calc (⌊h₀ / h⌋₊ : ℝ≥0∞) * g h ≤ ENNReal.ofReal (h₀ / h) * g h := by
            gcongr
            rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal (Nat.floor_le (div_nonneg hh₀.le hh.le))
        _ = g h / ENNReal.ofReal h * ENNReal.ofReal h₀ := by
            rw [ENNReal.ofReal_div_of_pos hh, div_eq_mul_inv, div_eq_mul_inv]; ring
    calc g h₀ / ENNReal.ofReal h₀
        ≤ ((⌊h₀ / h⌋₊ : ℝ≥0∞) * g h + g (r h)) / ENNReal.ofReal h₀ :=
          ENNReal.div_le_div_right hsplit _
      _ = (⌊h₀ / h⌋₊ : ℝ≥0∞) * g h / ENNReal.ofReal h₀ + g (r h) / ENNReal.ofReal h₀ :=
          ENNReal.add_div
      _ ≤ g h / ENNReal.ofReal h + g (r h) / ENNReal.ofReal h₀ := add_le_add hquot le_rfl
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup

/-! ### Homogeneity and subadditivity in the direction -/

/-- `V_{c u} f ≤ |c| V_u f`. -/
theorem dirVar_smul_le (c : ℝ) (u : E) (f : E → ℝ) (hf : Measurable f) :
    dirVar (c • u) f ≤ ENNReal.ofReal |c| * dirVar u f := by
  refine dirVar_le_of_forall _ _ fun h hh => ?_
  calc ∫⁻ x, ‖f (x + h • c • u) - f x‖ₑ = ∫⁻ x, ‖f (x + (h * c) • u) - f x‖ₑ := by
        simp_rw [mul_smul]
    _ ≤ ENNReal.ofReal |h * c| * dirVar u f := lintegral_translate_sub_le u f hf (h * c)
    _ = ENNReal.ofReal |c| * dirVar u f * ENNReal.ofReal h := by
        rw [abs_mul, abs_of_pos hh, ENNReal.ofReal_mul hh.le]; ring

/-- `V_{c u} f = |c| V_u f`. -/
theorem dirVar_smul (c : ℝ) (u : E) (f : E → ℝ) (hf : Measurable f) :
    dirVar (c • u) f = ENNReal.ofReal |c| * dirVar u f := by
  refine le_antisymm (dirVar_smul_le c u f hf) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ENNReal.ofReal |c| * dirVar u f = ENNReal.ofReal |c| * dirVar (c⁻¹ • c • u) f := by
        rw [inv_smul_smul₀ hc]
    _ ≤ ENNReal.ofReal |c| * (ENNReal.ofReal |c⁻¹| * dirVar (c • u) f) := by
        gcongr; exact dirVar_smul_le c⁻¹ (c • u) f hf
    _ = dirVar (c • u) f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, mul_inv_cancel₀
          (abs_ne_zero.2 hc), ENNReal.ofReal_one, one_mul]

/-- `V_{-u} f = V_u f`. -/
theorem dirVar_neg (u : E) (f : E → ℝ) (hf : Measurable f) : dirVar (-u) f = dirVar u f := by
  rw [← neg_one_smul ℝ u, dirVar_smul _ _ _ hf]
  simp

/-- `V_{u + w} f ≤ V_u f + V_w f`. -/
theorem dirVar_add_le (u w : E) (f : E → ℝ) (hf : Measurable f) :
    dirVar (u + w) f ≤ dirVar u f + dirVar w f := by
  refine dirVar_le_of_forall _ _ fun h hh => ?_
  calc ∫⁻ x, ‖f (x + h • (u + w)) - f x‖ₑ
      ≤ (∫⁻ x, ‖f (x + h • (u + w)) - f (x + h • u)‖ₑ) + ∫⁻ x, ‖f (x + h • u) - f x‖ₑ :=
        lintegral_enorm_sub_le_add (aemeasurable_enorm_sub_translate hf.aemeasurable _ _)
    _ = (∫⁻ x, ‖f (x + h • w) - f x‖ₑ) + ∫⁻ x, ‖f (x + h • u) - f x‖ₑ := by
        congr 1
        rw [← lintegral_translate (fun x => ‖f (x + h • w) - f x‖ₑ) (h • u)]
        refine lintegral_congr fun x => ?_
        rw [add_assoc, ← smul_add]
    _ ≤ ENNReal.ofReal h * dirVar w f + ENNReal.ofReal h * dirVar u f :=
        add_le_add (lintegral_translate_sub_le_of_pos w f hh)
          (lintegral_translate_sub_le_of_pos u f hh)
    _ = (dirVar u f + dirVar w f) * ENNReal.ofReal h := by ring

/-! ### Convexity and lower semicontinuity in the function -/

/-- `V_u` is subadditive in the function (half of convexity, paper Lemma 3.1).  Measurability
of `f` is used for the additivity of the lower integral, which fails for non-measurable
functions. -/
theorem dirVar_add_fun_le (u : E) (f g : E → ℝ) (hf : Measurable f) :
    dirVar u (f + g) ≤ dirVar u f + dirVar u g := by
  refine dirVar_le_of_forall _ _ fun h hh => ?_
  calc ∫⁻ x, ‖(f + g) (x + h • u) - (f + g) x‖ₑ
      ≤ ∫⁻ x, (‖f (x + h • u) - f x‖ₑ + ‖g (x + h • u) - g x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        simp only [Pi.add_apply]
        rw [show f (x + h • u) + g (x + h • u) - (f x + g x)
            = (f (x + h • u) - f x) + (g (x + h • u) - g x) by ring]
        exact enorm_add_le _ _
    _ = (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) + ∫⁻ x, ‖g (x + h • u) - g x‖ₑ :=
        lintegral_add_left (measurable_enorm_translate_sub hf _) _
    _ ≤ ENNReal.ofReal h * dirVar u f + ENNReal.ofReal h * dirVar u g :=
        add_le_add (lintegral_translate_sub_le_of_pos u f hh)
          (lintegral_translate_sub_le_of_pos u g hh)
    _ = (dirVar u f + dirVar u g) * ENNReal.ofReal h := by ring

/-- `V_u (c f) = |c| V_u f`. -/
theorem dirVar_const_smul_fun (u : E) (c : ℝ) (f : E → ℝ) :
    dirVar u (c • f) = ENNReal.ofReal |c| * dirVar u f := by
  unfold dirVar
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun h => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun _ => ?_
  rw [← mul_div_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_sub, enorm_mul, Real.enorm_eq_ofReal_abs]

/-- `V_u` is lower semicontinuous along `L¹`-convergent sequences (paper Lemma 3.1).
Measurability is needed for the triangle inequality of the lower integral. -/
theorem dirVar_le_liminf (u : E) (f : ℕ → E → ℝ) (g : E → ℝ) (hf : ∀ n, Measurable (f n))
    (hg : Measurable g)
    (hfg : Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ) atTop (𝓝 0)) :
    dirVar u g ≤ liminf (fun n => dirVar u (f n)) atTop := by
  refine iSup₂_le fun h hh => ?_
  have hh0 : ENNReal.ofReal h ≠ 0 := (ENNReal.ofReal_pos.2 hh).ne'
  have hv : Tendsto (fun n => 2 * (∫⁻ x, ‖f n x - g x‖ₑ) / ENNReal.ofReal h) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := 2) hfg (Or.inr ENNReal.ofNat_ne_top)
    have h2 := ENNReal.Tendsto.div_const h1 (Or.inr hh0)
    simpa using h2
  refine le_liminf_of_eventually_le_add hv (Eventually.of_forall fun n => ?_)
  rw [ENNReal.div_le_iff hh0 ENNReal.ofReal_ne_top, add_mul,
    ENNReal.div_mul_cancel hh0 ENNReal.ofReal_ne_top]
  have e1 : ∫⁻ x, ‖g (x + h • u) - f n (x + h • u)‖ₑ = ∫⁻ x, ‖f n x - g x‖ₑ := by
    rw [← lintegral_translate (fun x => ‖f n x - g x‖ₑ) (h • u)]
    exact lintegral_congr fun x => enorm_sub_rev _ _
  calc ∫⁻ x, ‖g (x + h • u) - g x‖ₑ
      ≤ (∫⁻ x, ‖g (x + h • u) - f n (x + h • u)‖ₑ) + ∫⁻ x, ‖f n (x + h • u) - g x‖ₑ :=
        lintegral_enorm_sub_le_add
          (((hg.comp (measurable_add_const _)).sub
            ((hf n).comp (measurable_add_const _))).enorm.aemeasurable)
    _ ≤ (∫⁻ x, ‖g (x + h • u) - f n (x + h • u)‖ₑ) +
          ((∫⁻ x, ‖f n (x + h • u) - f n x‖ₑ) + ∫⁻ x, ‖f n x - g x‖ₑ) :=
        add_le_add le_rfl
          (lintegral_enorm_sub_le_add (measurable_enorm_translate_sub (hf n) _).aemeasurable)
    _ ≤ (∫⁻ x, ‖f n x - g x‖ₑ) +
          (ENNReal.ofReal h * dirVar u (f n) + ∫⁻ x, ‖f n x - g x‖ₑ) := by
        rw [e1]
        gcongr
        exact lintegral_translate_sub_le_of_pos u (f n) hh
    _ = dirVar u (f n) * ENNReal.ofReal h + 2 * (∫⁻ x, ‖f n x - g x‖ₑ) := by ring

/-! ### The `W^{1,1}` bound -/

/-- Pointwise fundamental theorem of calculus along the direction `u`. -/
theorem sub_eq_integral_fderiv (u : E) (f : E → ℝ) (hf : ContDiff ℝ 1 f) (x : E) (h : ℝ) :
    f (x + h • u) - f x = ∫ s in (0 : ℝ)..h, fderiv ℝ f (x + s • u) u := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcont : Continuous fun y => fderiv ℝ f y u :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) h,
      HasDerivAt (fun s : ℝ => f (x + s • u)) (fderiv ℝ f (x + s • u) u) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => x + s • u) u s := by
      simpa using ((hasDerivAt_id s).smul_const u).const_add x
    have h2 : HasFDerivAt f (fderiv ℝ f (x + s • u)) (x + s • u) := (hfd _).hasFDerivAt
    simpa [Function.comp_def] using h2.comp_hasDerivAt s h1
  have hint : IntervalIntegrable (fun s : ℝ => fderiv ℝ f (x + s • u) u) volume 0 h :=
    (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable
      _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [zero_smul, add_zero] at hftc
  exact hftc.symm

/-- The `W^{1,1}` bound (paper, after (2.1)): for `C¹` compactly supported `f`,
`V_u f ≤ ∫ |∂_u f|`.  Proved by dominated convergence of the difference quotients (no Fubini,
so no local compactness of `E` is needed). -/
theorem dirVar_le_lintegral_fderiv (u : E) (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) :
    dirVar u f ≤ ∫⁻ x, ‖fderiv ℝ f x u‖ₑ := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  set g : ℝ → ℝ≥0∞ := fun h => ∫⁻ x, ‖f (x + h • u) - f x‖ₑ with hg
  -- a uniform bound on the directional derivative
  obtain ⟨C, hC⟩ := (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hsupp.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hCu : ∀ y, ‖fderiv ℝ f y u‖ ≤ C * ‖u‖ := fun y =>
    (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hC y)
  -- the compact set outside of which all difference quotients vanish
  set K : Set E := (fun p : E × ℝ => p.1 - p.2 • u) '' (tsupport f ×ˢ Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K :=
    (hsupp.prod isCompact_Icc).image (continuous_fst.sub (continuous_snd.smul continuous_const))
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKout : ∀ x, x ∉ K → ∀ s ∈ Icc (0 : ℝ) 1, f (x + s • u) = 0 := by
    intro x hx s hs
    refine image_eq_zero_of_notMem_tsupport fun hm => hx ?_
    exact ⟨(x + s • u, s), ⟨hm, hs⟩, by simp⟩
  -- the difference quotients converge to `‖∂_u f‖ₑ` and are dominated
  have hlim : Tendsto (fun h : ℝ => g h / ENNReal.ofReal h) (𝓝[>] 0)
      (𝓝 (∫⁻ x, ‖fderiv ℝ f x u‖ₑ)) := by
    have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
    have hle1 : ∀ᶠ h : ℝ in 𝓝[>] 0, h ≤ 1 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds one_pos)
    have hF : ∀ h : ℝ, 0 < h → g h / ENNReal.ofReal h
        = ∫⁻ x, ‖f (x + h • u) - f x‖ₑ / ENNReal.ofReal h := by
      intro h hh
      simp only [hg, div_eq_mul_inv]
      rw [← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hh).ne')]
    have key : Tendsto (fun h : ℝ => ∫⁻ x, ‖f (x + h • u) - f x‖ₑ / ENNReal.ofReal h) (𝓝[>] 0)
        (𝓝 (∫⁻ x, ‖fderiv ℝ f x u‖ₑ)) := by
      refine tendsto_lintegral_filter_of_dominated_convergence
        (K.indicator fun _ => ENNReal.ofReal (C * ‖u‖)) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun h =>
          ((hfc.comp (continuous_id.add continuous_const)).sub hfc).enorm.measurable.div_const _
      · filter_upwards [hpos, hle1] with h hh hh1
        refine Eventually.of_forall fun x => ?_
        by_cases hx : x ∈ K
        · rw [indicator_of_mem hx]
          rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hh).ne' ENNReal.ofReal_ne_top,
            ← ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.norm_eq_abs, sub_eq_integral_fderiv u f hf x h]
          calc ‖∫ s in (0 : ℝ)..h, fderiv ℝ f (x + s • u) u‖ ≤ C * ‖u‖ * |h - 0| :=
                intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hCu _
            _ = C * ‖u‖ * h := by rw [sub_zero, abs_of_pos hh]
        · have h0 := hKout x hx 0 ⟨le_rfl, zero_le_one⟩
          rw [zero_smul, add_zero] at h0
          rw [indicator_of_notMem hx, hKout x hx h ⟨hh.le, hh1⟩, h0]
          simp
      · rw [lintegral_indicator_const hKm]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKc.measure_lt_top.ne
      · refine Eventually.of_forall fun x => ?_
        have hd : HasDerivAt (fun s : ℝ => f (x + s • u)) (fderiv ℝ f (x + (0 : ℝ) • u) u) 0 := by
          have h1 : HasDerivAt (fun s : ℝ => x + s • u) u 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
          simpa [Function.comp_def] using (hfd _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
        have h2 := (continuous_enorm.tendsto _).comp hd.tendsto_slope_zero_right
        simp only [zero_smul, add_zero] at h2
        refine h2.congr' ?_
        filter_upwards [hpos] with h hh
        simp only [Function.comp_apply, zero_add]
        rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_inv, abs_of_pos hh,
          ENNReal.ofReal_inv_of_pos hh, div_eq_mul_inv, mul_comm]
    refine key.congr' ?_
    filter_upwards [hpos] with h hh
    exact (hF h hh).symm
  -- conclude: `g h / h ≤ g (h / n) / (h / n) → ∫ ‖∂_u f‖`
  refine iSup₂_le fun h hh => ?_
  have hfa : AEMeasurable f := hfc.measurable.aemeasurable
  have hseq : Tendsto (fun n : ℕ => h / (n + 1 : ℝ)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨?_, Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
    refine ((tendsto_const_div_atTop_nhds_zero_nat h).comp (tendsto_add_atTop_nat 1)).congr
      fun n => ?_
    simp
  refine le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim.comp hseq) fun n => ?_
  simp only [Function.comp_apply]
  have hn : (0 : ℝ) < h / (n + 1 : ℝ) := by positivity
  have hsub : g h ≤ (n + 1 : ℕ) * g (h / (n + 1 : ℝ)) := by
    have := lintegral_translate_sub_nsmul_le u f hfa (n + 1) (h / (n + 1 : ℝ))
    rwa [show ((n + 1 : ℕ) : ℝ) * (h / (n + 1 : ℝ)) = h by push_cast; field_simp] at this
  rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hh).ne' ENNReal.ofReal_ne_top]
  calc g h ≤ (n + 1 : ℕ) * g (h / (n + 1 : ℝ)) := hsub
    _ = g (h / (n + 1 : ℝ)) * ENNReal.ofReal (h / (h / (n + 1 : ℝ))) := by
        rw [show h / (h / (n + 1 : ℝ)) = (n + 1 : ℕ) by
              rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hh.ne']; push_cast; ring,
          ENNReal.ofReal_natCast, mul_comm]
    _ = g (h / (n + 1 : ℝ)) / ENNReal.ofReal (h / (n + 1 : ℝ)) * ENNReal.ofReal h := by
        rw [ENNReal.ofReal_div_of_pos hn, ← mul_div_assoc, ENNReal.mul_div_right_comm]

/-! ### Lipschitz functions -/

/-- A Lipschitz compactly supported function has finite directional variation:
`V_u f ≤ 2 L ‖u‖ |tsupport f|`. -/
theorem dirVar_le_of_lipschitz (u : E) (f : E → ℝ) {L : NNReal} (hf : LipschitzWith L f)
    (hsupp : HasCompactSupport f) :
    dirVar u f ≤ ENNReal.ofReal (2 * L * ‖u‖) * volume (tsupport f) := by
  refine dirVar_le_of_forall _ _ fun h hh => ?_
  set T := tsupport f with hT
  have hTm : MeasurableSet T := (isClosed_tsupport f).measurableSet
  set S := T ∪ (fun x => x + h • u) ⁻¹' T with hS
  have hSm : MeasurableSet S := hTm.union (hTm.preimage (measurable_add_const _))
  have hpt : ∀ x, ‖f (x + h • u) - f x‖ₑ ≤
      S.indicator (fun _ => (L : ℝ≥0∞) * ENNReal.ofReal (h * ‖u‖)) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      calc ‖f (x + h • u) - f x‖ₑ = edist (f (x + h • u)) (f x) := (edist_eq_enorm_sub _ _).symm
        _ ≤ L * edist (x + h • u) x := hf.edist_le_mul _ _
        _ = L * ENNReal.ofReal (h * ‖u‖) := by
            rw [edist_eq_enorm_sub, add_sub_cancel_left, enorm_smul, Real.enorm_eq_ofReal_abs,
              abs_of_pos hh, ← ofReal_norm, ← ENNReal.ofReal_mul hh.le]
    · rw [indicator_of_notMem hx]
      have hx1 : x ∉ T := fun h' => hx (Or.inl h')
      have hx2 : x + h • u ∉ T := fun h' => hx (Or.inr h')
      rw [image_eq_zero_of_notMem_tsupport hx1, image_eq_zero_of_notMem_tsupport hx2]
      simp
  calc ∫⁻ x, ‖f (x + h • u) - f x‖ₑ
      ≤ ∫⁻ x, S.indicator (fun _ => (L : ℝ≥0∞) * ENNReal.ofReal (h * ‖u‖)) x :=
        lintegral_mono hpt
    _ = (L : ℝ≥0∞) * ENNReal.ofReal (h * ‖u‖) * volume S := lintegral_indicator_const hSm _
    _ ≤ (L : ℝ≥0∞) * ENNReal.ofReal (h * ‖u‖) * (volume T + volume T) := by
        gcongr
        calc volume S ≤ volume T + volume ((fun x => x + h • u) ⁻¹' T) := measure_union_le _ _
          _ = volume T + volume T := by rw [measure_preimage_add_right]
    _ = ENNReal.ofReal (2 * L * ‖u‖) * volume T * ENNReal.ofReal h := by
        rw [ENNReal.ofReal_mul hh.le, ENNReal.ofReal_mul (p := 2 * (L : ℝ)) (by positivity),
          ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_ofNat]
        ring

end General

section Euclidean

variable {d : ℕ}

/-- Successive translations: `‖f(· + ∑ vᵢ) − f‖₁ ≤ ∑ ‖f(· + vᵢ) − f‖₁`. -/
theorem lintegral_translate_sub_sum_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
    [(volume : Measure E).IsAddHaarMeasure] (f : E → ℝ) (hf : Measurable f) {ι : Type*}
    (s : Finset ι) (v : ι → E) :
    ∫⁻ x, ‖f (x + ∑ i ∈ s, v i) - f x‖ₑ ≤ ∑ i ∈ s, ∫⁻ x, ‖f (x + v i) - f x‖ₑ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc ∫⁻ x, ‖f (x + (v a + ∑ i ∈ s, v i)) - f x‖ₑ
        ≤ (∫⁻ x, ‖f (x + (v a + ∑ i ∈ s, v i)) - f (x + ∑ i ∈ s, v i)‖ₑ)
            + ∫⁻ x, ‖f (x + ∑ i ∈ s, v i) - f x‖ₑ :=
          lintegral_enorm_sub_le_add (aemeasurable_enorm_sub_translate hf.aemeasurable _ _)
      _ = (∫⁻ x, ‖f (x + v a) - f x‖ₑ) + ∫⁻ x, ‖f (x + ∑ i ∈ s, v i) - f x‖ₑ := by
          congr 1
          rw [← lintegral_translate (fun x => ‖f (x + v a) - f x‖ₑ) (∑ i ∈ s, v i)]
          refine lintegral_congr fun x => ?_
          rw [add_assoc, add_comm (∑ i ∈ s, v i) (v a)]
      _ ≤ _ := add_le_add le_rfl ih

/-- Coordinate bound for a translation (paper Lemma 3.1):
`‖f(· + h) − f‖₁ ≤ ∑_i |h_i| V_{e_i} f`. -/
theorem lintegral_translate_sub_le_sum_coord (f : Euc d → ℝ) (hf : Measurable f) (h : Euc d) :
    ∫⁻ x, ‖f (x + h) - f x‖ₑ ≤
      ∑ i, ENNReal.ofReal |h i| * dirVar (EuclideanSpace.single i 1) f := by
  have hsum : h = ∑ i, h i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr h
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using this.symm
  calc ∫⁻ x, ‖f (x + h) - f x‖ₑ
      = ∫⁻ x, ‖f (x + ∑ i, h i • EuclideanSpace.single i (1 : ℝ)) - f x‖ₑ := by rw [← hsum]
    _ ≤ ∑ i, ∫⁻ x, ‖f (x + h i • EuclideanSpace.single i (1 : ℝ)) - f x‖ₑ :=
        lintegral_translate_sub_sum_le f hf _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => lintegral_translate_sub_le _ f hf (h i)

/-- Coordinate bound for the variation: `V_z f ≤ ∑_i |z_i| V_{e_i} f`. -/
theorem dirVar_le_sum_coord (f : Euc d → ℝ) (hf : Measurable f) (z : Euc d) :
    dirVar z f ≤ ∑ i, ENNReal.ofReal |z i| * dirVar (EuclideanSpace.single i 1) f := by
  refine dirVar_le_of_forall _ _ fun h hh => ?_
  calc ∫⁻ x, ‖f (x + h • z) - f x‖ₑ
      ≤ ∑ i, ENNReal.ofReal |(h • z) i| * dirVar (EuclideanSpace.single i 1) f :=
        lintegral_translate_sub_le_sum_coord f hf (h • z)
    _ = (∑ i, ENNReal.ofReal |z i| * dirVar (EuclideanSpace.single i 1) f) *
          ENNReal.ofReal h := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hh, ENNReal.ofReal_mul hh.le]
        ring

/-- Cauchy–Schwarz: `∑ |zᵢ| ≤ √d ‖z‖₂`. -/
theorem sum_abs_le_sqrt_card_mul_norm (z : Euc d) : ∑ i, |z i| ≤ Real.sqrt d * ‖z‖ := by
  have h1 : (∑ i, |z i|) ^ 2 ≤ (d : ℝ) * ∑ i, |z i| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun i => |z i|)
    simpa using this
  have h2 : ‖z‖ = Real.sqrt (∑ i, |z i| ^ 2) := by
    simp [EuclideanSpace.norm_eq]
  calc ∑ i, |z i| = Real.sqrt ((∑ i, |z i|) ^ 2) :=
        (Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)).symm
    _ ≤ Real.sqrt ((d : ℝ) * ∑ i, |z i| ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt d * ‖z‖ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), h2]

/-- The direction-perturbation estimate of paper Lemma 3.3:
`V_u f ≤ V_w f + √d ‖u − w‖ max_i V_{e_i} f`. -/
theorem dirVar_le_dirVar_add (f : Euc d → ℝ) (hf : Measurable f) (u w : Euc d) {M : ℝ≥0∞}
    (hM : ∀ i, dirVar (EuclideanSpace.single i 1) f ≤ M) :
    dirVar u f ≤ dirVar w f + ENNReal.ofReal (Real.sqrt d * ‖u - w‖) * M := by
  calc dirVar u f = dirVar (w + (u - w)) f := by rw [add_sub_cancel]
    _ ≤ dirVar w f + dirVar (u - w) f := dirVar_add_le w (u - w) f hf
    _ ≤ dirVar w f + ENNReal.ofReal (Real.sqrt d * ‖u - w‖) * M := by
        gcongr
        calc dirVar (u - w) f
            ≤ ∑ i, ENNReal.ofReal |(u - w) i| * dirVar (EuclideanSpace.single i 1) f :=
              dirVar_le_sum_coord f hf (u - w)
          _ ≤ ∑ i, ENNReal.ofReal |(u - w) i| * M :=
              Finset.sum_le_sum fun i _ => by gcongr; exact hM i
          _ = ENNReal.ofReal (∑ i, |(u - w) i|) * M := by
              rw [ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _, Finset.sum_mul]
          _ ≤ ENNReal.ofReal (Real.sqrt d * ‖u - w‖) * M := by
              gcongr
              exact sum_abs_le_sqrt_card_mul_norm (u - w)

/-- Every nonempty open set supports some `ρ ∈ 𝒫(K)` (a normalised Lipschitz bump). -/
theorem exists_memP_of_isOpen {K : Set (Euc d)} (hK : IsOpen K) (hne : K.Nonempty) :
    ∃ ρ, MemP K ρ := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK x₀ hx₀
  set r : ℝ := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : Metric.closedBall x₀ r ⊆ K :=
    (Metric.closedBall_subset_ball (by rw [hr]; linarith)).trans hball
  set g : Euc d → ℝ := fun x => max 0 (r - dist x x₀) with hg
  have hgl : LipschitzWith 1 g := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [hg, Real.dist_eq, NNReal.coe_one, one_mul]
    calc |max 0 (r - dist x x₀) - max 0 (r - dist y x₀)|
        ≤ |(r - dist x x₀) - (r - dist y x₀)| := by
          rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
      _ = |dist y x₀ - dist x x₀| := by congr 1; ring
      _ ≤ dist y x := abs_dist_sub_le _ _ _
      _ = dist x y := dist_comm _ _
  have hgc : Continuous g := hgl.continuous
  have hg0 : ∀ x, x ∉ Metric.closedBall x₀ r → g x = 0 := by
    intro x hx
    rw [Metric.mem_closedBall, not_le] at hx
    simp only [hg]
    exact max_eq_left (by linarith)
  have hgs : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_closedBall x₀ r) hg0
  have hgnn : ∀ x, 0 ≤ g x := fun x => le_max_left _ _
  have hI : 0 < ∫ x, g x :=
    hgc.integral_pos_of_hasCompactSupport_nonneg_nonzero hgs hgnn (x := x₀)
      (by simp only [hg, dist_self, sub_zero, max_eq_right hr0.le]; exact hr0.ne')
  have htsupp : tsupport g ⊆ Metric.closedBall x₀ r := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    by_contra hx'
    exact hx (hg0 x hx')
  set c : ℝ := (∫ x, g x)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 hI
  refine ⟨c • g, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (continuous_const.smul hgc).measurable
  · intro x
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hc0.le (hgnn x)
  · exact (hgc.integrable_of_hasCompactSupport hgs).smul c
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hc, inv_mul_cancel₀ hI.ne']
  · refine Eventually.of_forall fun x hx => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hg0 x (fun h' => hx (hcb h')), mul_zero]
  · intro u
    rw [dirVar_const_smul_fun]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ne_top_of_le_ne_top ?_ (dirVar_le_of_lipschitz u g hgl hgs)
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact ((measure_mono htsupp).trans_lt measure_closedBall_lt_top).ne

end Euclidean

end Komlos
