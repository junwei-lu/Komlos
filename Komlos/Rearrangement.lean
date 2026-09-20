import Komlos.Lift
import Komlos.Variation
import Komlos.RearrangementAux

/-!
# Fiber rearrangement (paper Lemma 4.2)

For nonnegative `R ∈ L¹(ℝ^d × ℝ)`, the fiberwise symmetric decreasing rearrangement
`R⋆` (`Komlos.symRearr`) is measurable, nonnegative, has the same mass, is supported in the
Steiner symmetral `B⋆` whenever `R` is supported in the lift `B`, and contracts horizontal
translations in `L¹` (hence `V_{(u,0)} R⋆ ≤ V_{(u,0)} R`).

Paper proof of the contraction: for nonnegative `f, g ∈ L¹(ℝ)`, layer cake and the maximal
intersection of centered intervals give `∫ min(f⋆, g⋆) ≥ ∫ min(f, g)`, hence
`‖f⋆ − g⋆‖₁ ≤ ‖f − g‖₁`; apply on the fibers at `y + h u` and `y` and integrate in `y`.
The one-dimensional theory is in `Komlos.RearrangementAux`; `symRearr R (y, s)` is
definitionally `symRearr1 (R (y, ·)) s`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-- The fiber distribution function `(y, t) ↦ μ(y, t)` is jointly measurable. -/
theorem measurable_fiberDist (R : Euc d × ℝ → ℝ) (hR : Measurable R) :
    Measurable fun q : Euc d × ℝ => fiberDist R q.1 q.2 := by
  have hS : MeasurableSet {q : (Euc d × ℝ) × ℝ | q.1.2 < R (q.1.1, q.2)} :=
    measurableSet_lt (measurable_snd.comp measurable_fst)
      (hR.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact measurable_measure_prodMk_left hS

/-- `R⋆` is jointly measurable. -/
theorem symRearr_measurable (R : Euc d × ℝ → ℝ) (hR : Measurable R) :
    Measurable (symRearr R) := by
  have hS : MeasurableSet
      {q : (Euc d × ℝ) × ℝ | ENNReal.ofReal (2 * |q.1.2|) < fiberDist R q.1.1 q.2} :=
    measurableSet_lt (measurable_ofReal_twoAbs.comp (measurable_snd.comp measurable_fst))
      ((measurable_fiberDist R hR).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have : symRearr R = fun p =>
      (∫⁻ t, {q : (Euc d × ℝ) × ℝ | ENNReal.ofReal (2 * |q.1.2|) < fiberDist R q.1.1 q.2}.indicator
        (fun _ => (1 : ℝ≥0∞)) (p, t) ∂(volume.restrict (Ioi 0))).toReal := by
    ext p
    unfold symRearr
    congr 1
  rw [this]
  exact (measurable_const.indicator hS).lintegral_prod_right'.ennreal_toReal

/-- `R⋆ ≥ 0`. -/
theorem symRearr_nonneg (R : Euc d × ℝ → ℝ) (p : Euc d × ℝ) : 0 ≤ symRearr R p :=
  ENNReal.toReal_nonneg

/-- For nonnegative integrable `R`, `∫⁻ ofReal R < ∞`. -/
theorem lintegral_ofReal_ne_top_of_integrable (R : Euc d × ℝ → ℝ) (h0 : ∀ p, 0 ≤ R p)
    (hint : Integrable R) : ∫⁻ p, ENNReal.ofReal (R p) ≠ ⊤ := by
  have h := hasFiniteIntegral_iff_enorm.mp hint.2
  rw [← lintegral_congr fun p => Real.enorm_eq_ofReal (h0 p)]
  exact h.ne

/-- Almost every fiber of a nonnegative integrable `R` is integrable. -/
theorem ae_lintegral_fiber_lt_top (R : Euc d × ℝ → ℝ) (hR : Measurable R) (h0 : ∀ p, 0 ≤ R p)
    (hint : Integrable R) : ∀ᵐ y : Euc d, ∫⁻ s, ENNReal.ofReal (R (y, s)) < ⊤ := by
  have hRm : Measurable fun p => ENNReal.ofReal (R p) := hR.ennreal_ofReal
  refine ae_lt_top hRm.lintegral_prod_right' ?_
  rw [← lintegral_prod _ hRm.aemeasurable, ← Measure.volume_eq_prod]
  exact lintegral_ofReal_ne_top_of_integrable R h0 hint

/-- `R⋆` has the same mass as `R` (paper Lemma 4.2, for `R ∈ L¹`).  Integrability is needed:
the convention `R⋆ = 0` on fibers where the rearrangement formula is infinite makes the
identity fail for, e.g., `R (y, s) = |s|`. -/
theorem lintegral_symRearr (R : Euc d × ℝ → ℝ) (hR : Measurable R) (h0 : ∀ p, 0 ≤ R p)
    (hint : Integrable R) :
    ∫⁻ p, ENNReal.ofReal (symRearr R p) = ∫⁻ p, ENNReal.ofReal (R p) := by
  have hRm : Measurable fun p => ENNReal.ofReal (R p) := hR.ennreal_ofReal
  rw [Measure.volume_eq_prod, lintegral_prod _ hRm.aemeasurable,
    lintegral_prod _ (symRearr_measurable R hR).ennreal_ofReal.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lintegral_fiber_lt_top R hR h0 hint] with y hy
  exact lintegral_symRearr1 (fun s => R (y, s)) (hR.comp measurable_prodMk_left)
    (fun s => h0 _) hy.ne

/-- If `R = 0` a.e. outside the lift `B`, then `R⋆ = 0` a.e. outside `B⋆`. -/
theorem symRearr_ae_zero_outside {K : Set (Euc d)} (hK : IsGoodConvex K) (v : Euc d)
    (R : Euc d × ℝ → ℝ) (hR : Measurable R) (h0 : ∀ p, 0 ≤ R p) (hint : Integrable R)
    (hsupp : ∀ᵐ p, p ∉ lift K v → R p = 0) :
    ∀ᵐ p, p ∉ steiner K v → symRearr R p = 0 := by
  -- Fubini on the support hypothesis.
  have h1 : ∀ᵐ y : Euc d, ∀ᵐ s : ℝ, (y, s) ∉ lift K v → R (y, s) = 0 := by
    rw [Measure.volume_eq_prod] at hsupp
    exact Measure.ae_ae_of_ae_prod hsupp
  -- On a good fiber, `μ(y, t) ≤ ℓ(y)` for `t > 0`, so the formula vanishes for `2|s| ≥ ℓ(y)`.
  have h2 : ∀ᵐ y : Euc d, ∀ s : ℝ, fiberLength K v y ≤ 2 * |s| → symRearr R (y, s) = 0 := by
    filter_upwards [h1] with y hy s hs
    obtain ⟨a, b, hab⟩ := exists_fiber_eq_Ioo hK v y
    have hJfin : volume {s : ℝ | (y, s) ∈ lift K v} ≠ ⊤ := by
      rw [hab, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hμ : ∀ t, 0 < t → fiberDist R y t ≤ volume {s : ℝ | (y, s) ∈ lift K v} := by
      intro t ht
      unfold fiberDist
      refine measure_mono_ae ?_
      filter_upwards [hy] with s hs' (hst : t < R (y, s))
      by_contra hne
      rw [hs' hne] at hst
      exact lt_irrefl _ (ht.trans hst)
    have hvol : volume {s : ℝ | (y, s) ∈ lift K v} = ENNReal.ofReal (fiberLength K v y) := by
      unfold fiberLength; rw [ENNReal.ofReal_toReal hJfin]
    have hempty : {t | ENNReal.ofReal (2 * |s|) < distFn (fun s => R (y, s)) t} ∩ Ioi 0 = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
      intro hlt ht
      have h3 : ENNReal.ofReal (2 * |s|) < ENNReal.ofReal (fiberLength K v y) :=
        hlt.trans_le ((hμ t ht).trans_eq hvol)
      exact (not_le.mpr h3) (ENNReal.ofReal_le_ofReal hs)
    show symRearr1 (fun s => R (y, s)) s = 0
    unfold symRearr1
    rw [rearrFormula_eq_volume, hempty, measure_empty, ENNReal.toReal_zero]
  rw [Measure.volume_eq_prod]
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d)))
    (ν := (volume : Measure ℝ))).ae h2] with p hp hpn
  have : fiberLength K v p.1 ≤ 2 * |p.2| := by
    simp only [steiner, mem_ofPred_eq, not_lt] at hpn
    linarith
  exact hp p.2 this

/-- Paper (4.4): horizontal translations contract under fiber rearrangement. -/
theorem lintegral_symRearr_translate_sub_le (R : Euc d × ℝ → ℝ) (hR : Measurable R)
    (h0 : ∀ p, 0 ≤ R p) (hint : Integrable R) (u : Euc d) (h : ℝ) :
    ∫⁻ p, ‖symRearr R (p + h • ((u, (0 : ℝ)) : Euc d × ℝ)) - symRearr R p‖ₑ ≤
      ∫⁻ p, ‖R (p + h • ((u, (0 : ℝ)) : Euc d × ℝ)) - R p‖ₑ := by
  have hadd : ∀ p : Euc d × ℝ, p + h • ((u, (0 : ℝ)) : Euc d × ℝ) = (p.1 + h • u, p.2) := by
    intro p; ext <;> simp
  simp_rw [hadd]
  have hae := ae_lintegral_fiber_lt_top R hR h0 hint
  have hae' : ∀ᵐ y : Euc d, ∫⁻ s, ENNReal.ofReal (R (y + h • u, s)) < ⊤ :=
    (measurePreserving_add_right volume (h • u)).quasiMeasurePreserving.ae hae
  have hshift : Measurable fun p : Euc d × ℝ => (p.1 + h • u, p.2) :=
    (measurable_fst.add_const _).prodMk measurable_snd
  have hRt : Measurable fun p : Euc d × ℝ => R (p.1 + h • u, p.2) := hR.comp hshift
  have hSt : Measurable fun p : Euc d × ℝ => symRearr R (p.1 + h • u, p.2) :=
    (symRearr_measurable R hR).comp hshift
  have hm1 : Measurable fun p : Euc d × ℝ =>
      ‖symRearr R (p.1 + h • u, p.2) - symRearr R p‖ₑ :=
    (hSt.sub (symRearr_measurable R hR)).enorm
  have hm2 : Measurable fun p : Euc d × ℝ => ‖R (p.1 + h • u, p.2) - R p‖ₑ :=
    (hRt.sub hR).enorm
  rw [Measure.volume_eq_prod, lintegral_prod _ hm1.aemeasurable, lintegral_prod _ hm2.aemeasurable]
  refine lintegral_mono_ae ?_
  filter_upwards [hae, hae'] with y hy hy'
  exact lintegral_enorm_symRearr1_sub_le (fun s => R (y + h • u, s)) (fun s => R (y, s))
    (hR.comp measurable_prodMk_left) (hR.comp measurable_prodMk_left) (fun s => h0 _)
    (fun s => h0 _) hy'.ne hy.ne

/-- Consequently `V_{(u,0)} R⋆ ≤ V_{(u,0)} R`. -/
theorem dirVar_symRearr_le (R : Euc d × ℝ → ℝ) (hR : Measurable R) (h0 : ∀ p, 0 ≤ R p)
    (hint : Integrable R) (u : Euc d) :
    dirVar ((u, (0 : ℝ)) : Euc d × ℝ) (symRearr R) ≤ dirVar ((u, (0 : ℝ)) : Euc d × ℝ) R := by
  unfold dirVar
  exact iSup₂_mono fun h _ =>
    ENNReal.div_le_div_right (lintegral_symRearr_translate_sub_le R hR h0 hint u h) _

end Komlos
