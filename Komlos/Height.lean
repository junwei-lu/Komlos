import Komlos.Rearrangement
import Komlos.HeightAux

/-!
# Rearranged height (paper Lemma 4.3)

For a probability density `ρ` on `ℝ^d` and `R(y,s) = (1/6) ρ(y + s v) 𝟙_{|s|<3}`,
`∫ |s| R⋆ = 3/2 − (1/24) ∫_0^6 (6 − h) ‖ρ − ρ(· + h v)‖₁ dh ≥ 3/2 − (3/2) V_v ρ`.

The proof follows the paper: with `μ(y,t) = |{s ∈ (−3,3) : ρ(y+sv) > 6t}|`, the superlevel
set of `R⋆(y,·)` at level `t` is the centred interval of length `μ(y,t)`, whose first absolute
moment is `μ(y,t)²/4`; layer cake gives `∫|s|R⋆ = (1/4)∫∫_0^∞ μ(y,t)² dt dy`, and
`∫_0^∞ μ(y,t)² dt = ∫∫_{(−3,3)²} min(R(y,s), R(y,r)) dr ds` (`lintegral_abs_mul_symRearr`).
Translation invariance turns the inner integral into the overlap `O(r − s)` (paper (4.6)),
and the double integral over the square of the even function `O` is `2∫_0^6 (6−h) O(h) dh`
(`lintegral_sq_eq_intervalIntegral`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-- The lifted density is measurable. -/
theorem liftedDensity_measurable {ρ : Euc d → ℝ} (hρ : Measurable ρ) (v : Euc d) :
    Measurable (liftedDensity ρ v) := by
  unfold liftedDensity
  exact Measurable.ite (measurableSet_lt measurable_snd.abs measurable_const)
    (measurable_const.mul (hρ.comp (measurable_fst.add (measurable_snd.smul_const v))))
    measurable_const

/-- The lifted density is nonnegative. -/
theorem liftedDensity_nonneg {ρ : Euc d → ℝ} (hρ : ∀ x, 0 ≤ ρ x) (v : Euc d) (p : Euc d × ℝ) :
    0 ≤ liftedDensity ρ v p := by
  unfold liftedDensity
  split_ifs
  · exact mul_nonneg (by norm_num) (hρ _)
  · exact le_rfl

/-- The lifted density has mass one. -/
theorem lintegral_liftedDensity {K : Set (Euc d)} {ρ : Euc d → ℝ} (hρ : IsProbDensityOn K ρ)
    (v : Euc d) : ∫⁻ p, ENNReal.ofReal (liftedDensity ρ v p) = 1 := by
  have hg : Measurable fun x => ENNReal.ofReal ((1 / 6 : ℝ) * ρ x) :=
    (measurable_const.mul hρ.measurable).ennreal_ofReal
  have : (fun p : Euc d × ℝ => ENNReal.ofReal (liftedDensity ρ v p)) =
      fun p => if |p.2| < 3 then (fun x => ENNReal.ofReal ((1 / 6 : ℝ) * ρ x)) (p.1 + p.2 • v)
        else 0 := by
    ext p
    unfold liftedDensity
    split_ifs <;> simp
  rw [this, lintegral_lift v hg]
  simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hρ.integrable (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_eq_one, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- The lifted density is a probability density on the lift, with
`V_{(u,0)} R ≤ V_u ρ` (paper, proof of Proposition 2.2). -/
theorem liftedDensity_isProbDensityOn {K : Set (Euc d)} {ρ : Euc d → ℝ}
    (hρ : IsProbDensityOn K ρ) (v : Euc d) :
    IsProbDensityOn (lift K v) (liftedDensity ρ v) where
  measurable := liftedDensity_measurable hρ.measurable v
  nonneg := liftedDensity_nonneg hρ.nonneg v
  integrable := by
    refine ⟨(liftedDensity_measurable hρ.measurable v).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal (liftedDensity_nonneg hρ.nonneg v _)]
    rw [lintegral_liftedDensity hρ v]
    exact ENNReal.one_lt_top
  integral_eq_one := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
      (liftedDensity_nonneg hρ.nonneg v))
      (liftedDensity_measurable hρ.measurable v).aestronglyMeasurable,
      lintegral_liftedDensity hρ v]
    simp
  ae_zero_outside := by
    filter_upwards [ae_lift v hρ.ae_zero_outside] with p hp hpK
    unfold liftedDensity
    split_ifs with h
    · rw [hp fun hmem => hpK ⟨h, hmem⟩, mul_zero]
    · rfl

theorem dirVar_liftedDensity_le {ρ : Euc d → ℝ} (hρ : Measurable ρ) (v u : Euc d) :
    dirVar ((u, (0 : ℝ)) : Euc d × ℝ) (liftedDensity ρ v) ≤ dirVar u ρ := by
  unfold dirVar
  refine iSup₂_mono fun h _ => ?_
  refine ENNReal.div_le_div_right ?_ _
  have hg : Measurable fun x : Euc d => ‖(1 / 6 : ℝ) * (ρ (x + h • u) - ρ x)‖ₑ :=
    (measurable_const.mul ((hρ.comp (measurable_id.add_const (h • u))).sub hρ)).enorm
  have : (fun p : Euc d × ℝ =>
      ‖liftedDensity ρ v (p + h • ((u, (0 : ℝ)) : Euc d × ℝ)) - liftedDensity ρ v p‖ₑ) =
      fun p => if |p.2| < 3 then
        (fun x : Euc d => ‖(1 / 6 : ℝ) * (ρ (x + h • u) - ρ x)‖ₑ) (p.1 + p.2 • v) else 0 := by
    ext p
    simp only [liftedDensity, Prod.smul_mk, smul_zero, Prod.fst_add, Prod.snd_add, add_zero]
    split_ifs with hp
    · congr 2
      rw [mul_sub]
      congr 3
      abel
    · simp
  rw [this, lintegral_lift v hg]
  simp_rw [enorm_mul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Superlevel sets of the fibers of the lifted density at positive levels lie in `(−3, 3)`. -/
theorem volume_lt_liftedDensity_ne_top (ρ : Euc d → ℝ) (v : Euc d) (y : Euc d) {t : ℝ}
    (ht : 0 < t) : volume {s : ℝ | t < liftedDensity ρ v (y, s)} ≠ ∞ := by
  have hsub : {s : ℝ | t < liftedDensity ρ v (y, s)} ⊆ Ioo (-3) 3 := by
    intro s hs
    change t < liftedDensity ρ v (y, s) at hs
    simp only [liftedDensity] at hs
    by_contra hcon
    rw [if_neg fun h => hcon (mem_Ioo.2 (abs_lt.1 h))] at hs
    exact absurd hs (not_lt.2 ht.le)
  have hfin : volume (Ioo (-3 : ℝ) 3) ≠ ∞ := by simp [Real.volume_Ioo]
  exact ne_top_of_le_ne_top hfin (measure_mono hsub)

/-- Pointwise form of `min(R(y,s), R(y,r))` for the lifted density. -/
theorem ofReal_min_liftedDensity (ρ : Euc d → ℝ) (v : Euc d) (y : Euc d) (s r : ℝ) :
    ENNReal.ofReal (min (liftedDensity ρ v (y, s)) (liftedDensity ρ v (y, r))) =
      if |s| < 3 ∧ |r| < 3 then
        ENNReal.ofReal (1 / 6) * ENNReal.ofReal (min (ρ (y + s • v)) (ρ (y + r • v))) else 0 := by
  simp only [liftedDensity]
  by_cases hs : |s| < 3 <;> by_cases hr : |r| < 3 <;> simp [hs, hr, mul_min_of_nonneg]

/-- Paper (4.5), the exact identity. -/
theorem integral_abs_mul_symRearr_liftedDensity {ρ : Euc d → ℝ}
    (hρ : IsProbDensityOn univ ρ) (v : Euc d) :
    ∫ p, |p.2| * symRearr (liftedDensity ρ v) p =
      3 / 2 - (1 / 24) * ∫ h in (0 : ℝ)..6, (6 - h) * ∫ x, |ρ x - ρ (x + h • v)| := by
  set R := liftedDensity ρ v with hRdef
  set O : ℝ → ℝ := fun h => ∫ x, min (ρ x) (ρ (x + h • v)) with hOdef
  set D : ℝ → ℝ := fun h => ∫ x, |ρ x - ρ (x + h • v)| with hDdef
  have hRm : Measurable R := liftedDensity_measurable hρ.measurable v
  have hR0 : ∀ p, 0 ≤ R p := liftedDensity_nonneg hρ.nonneg v
  have hRi : Integrable R := (liftedDensity_isProbDensityOn hρ v).integrable
  have hOm : Measurable O := measurable_integral_min_translate hρ v
  have hO0 : ∀ h, 0 ≤ O h := integral_min_translate_nonneg hρ v
  have hO1 : ∀ h, O h ≤ 1 := integral_min_translate_le_one hρ v
  have hOe : ∀ h, O (-h) = O h := integral_min_translate_neg ρ v
  -- Step 1: the Lebesgue-integral identity
  have key : ∫⁻ p, ENNReal.ofReal (|p.2| * symRearr R p) =
      ENNReal.ofReal (1 / 24) * ENNReal.ofReal (2 * ∫ h in (0 : ℝ)..6, (6 - h) * O h) := by
    rw [lintegral_abs_mul_symRearr R hRm hR0 hRi fun y t ht => volume_lt_liftedDensity_ne_top ρ v y ht]
    simp_rw [hRdef, ofReal_min_liftedDensity ρ v]
    have hF : Measurable fun z : Euc d × ℝ × ℝ => (if |z.2.1| < 3 ∧ |z.2.2| < 3 then
        ENNReal.ofReal (1 / 6) *
          ENNReal.ofReal (min (ρ (z.1 + z.2.1 • v)) (ρ (z.1 + z.2.2 • v))) else 0) := by
      have hm2 : Measurable fun z : Euc d × ℝ × ℝ => ENNReal.ofReal (1 / 6) *
          ENNReal.ofReal (min (ρ (z.1 + z.2.1 • v)) (ρ (z.1 + z.2.2 • v))) :=
        measurable_const.mul (Measurable.ennreal_ofReal
          ((hρ.measurable.comp (measurable_fst.add (measurable_snd.fst.smul_const v))).min
            (hρ.measurable.comp (measurable_fst.add (measurable_snd.snd.smul_const v)))))
      exact Measurable.ite ((measurableSet_lt measurable_snd.fst.abs measurable_const).inter
        (measurableSet_lt measurable_snd.snd.abs measurable_const)) hm2 measurable_const
    rw [lintegral_lintegral_lintegral_comm hF]
    have inner : ∀ s r : ℝ, ∫⁻ y, (if |s| < 3 ∧ |r| < 3 then ENNReal.ofReal (1 / 6) *
        ENNReal.ofReal (min (ρ (y + s • v)) (ρ (y + r • v))) else 0) =
        if |s| < 3 ∧ |r| < 3 then ENNReal.ofReal (1 / 6) * ENNReal.ofReal (O (r - s)) else 0 := by
      intro s r
      by_cases hsr : |s| < 3 ∧ |r| < 3
      · simp only [if_pos hsr]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        have hmin : Integrable fun y => min (ρ (y + s • v)) (ρ (y + r • v)) :=
          (hρ.integrable.comp_add_right (s • v)).inf (hρ.integrable.comp_add_right (r • v))
        rw [← ofReal_integral_eq_lintegral_ofReal hmin
          (Filter.Eventually.of_forall fun y => le_min (hρ.nonneg _) (hρ.nonneg _))]
        congr 1
        have htr := integral_add_right_eq_self (μ := volume)
          (fun y => min (ρ y) (ρ (y + (r - s) • v))) (s • v)
        refine Eq.trans ?_ htr
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show min (ρ (y + s • v)) (ρ (y + r • v)) =
          min (ρ (y + s • v)) (ρ (y + s • v + (r - s) • v))
        rw [show y + s • v + (r - s) • v = y + r • v by module]
      · simp only [if_neg hsr, lintegral_const, zero_mul]
    simp_rw [inner]
    have outer : ∀ s : ℝ, ∫⁻ r, (if |s| < 3 ∧ |r| < 3 then
        ENNReal.ofReal (1 / 6) * ENNReal.ofReal (O (r - s)) else 0) =
        (Ioo (-3 : ℝ) 3).indicator
          (fun s => ∫⁻ r in Ioo (-3 : ℝ) 3, ENNReal.ofReal (1 / 6) * ENNReal.ofReal (O (r - s))) s := by
      intro s
      by_cases hs : |s| < 3
      · rw [indicator_of_mem (mem_Ioo.2 (abs_lt.1 hs)), ← lintegral_indicator measurableSet_Ioo]
        refine lintegral_congr fun r => ?_
        by_cases hr : |r| < 3
        · rw [if_pos ⟨hs, hr⟩, indicator_of_mem (mem_Ioo.2 (abs_lt.1 hr))]
        · rw [if_neg fun h => hr h.2, indicator_of_notMem fun h => hr (abs_lt.2 (mem_Ioo.1 h))]
      · rw [indicator_of_notMem fun h => hs (abs_lt.2 (mem_Ioo.1 h))]
        simp [hs]
    simp_rw [outer]
    rw [lintegral_indicator measurableSet_Ioo]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_sq_eq_intervalIntegral O hOm hO0 hO1 hOe,
      show (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp,
      ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  -- Step 2: integrability of `|s| R⋆`
  have hnn : ∀ p : Euc d × ℝ, 0 ≤ |p.2| * symRearr R p := fun p =>
    mul_nonneg (abs_nonneg _) (symRearr_nonneg R p)
  have hint : Integrable fun p : Euc d × ℝ => |p.2| * symRearr R p := by
    refine ⟨(measurable_snd.abs.mul (symRearr_measurable R hRm)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal (hnn _)]
    rw [key]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- Step 3: back to a Bochner integral
  have hOi : IntervalIntegrable (fun h => (6 - h) * O h) volume 0 6 :=
    (intervalIntegrable_of_bounded hOm (C := 1)
      (fun h => by rw [abs_of_nonneg (hO0 h)]; exact hO1 h) 0 6).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  have hOnn : 0 ≤ ∫ h in (0 : ℝ)..6, (6 - h) * O h :=
    intervalIntegral.integral_nonneg (by norm_num) fun h hh =>
      mul_nonneg (by linarith [hh.2]) (hO0 h)
  have h1 : ∫ p, |p.2| * symRearr R p = (1 / 24) * (2 * ∫ h in (0 : ℝ)..6, (6 - h) * O h) := by
    have := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)
    rw [key, ← ENNReal.ofReal_mul (by norm_num)] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hnn) (by positivity)).1 this
  rw [h1]
  -- Step 4: `O = 1 − D/2`
  have hOD : ∀ h, O h = 1 - (1 / 2) * D h := fun h => integral_min_translate hρ v h
  have hDi : IntervalIntegrable (fun h => (6 - h) * D h) volume 0 6 :=
    (intervalIntegrable_of_bounded (measurable_integral_abs_sub_translate hρ v) (C := 2)
      (fun h => by
        rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)]
        exact integral_abs_sub_translate_le_two hρ v h) 0 6).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  have hlin : IntervalIntegrable (fun h : ℝ => 6 - h) volume 0 6 :=
    (continuous_const.sub continuous_id).intervalIntegrable _ _
  have hsplit : ∫ h in (0 : ℝ)..6, (6 - h) * O h =
      (∫ h in (0 : ℝ)..6, (6 - h)) - (1 / 2) * ∫ h in (0 : ℝ)..6, (6 - h) * D h := by
    have := intervalIntegral.integral_sub hlin (hDi.const_mul (1 / 2))
    rw [intervalIntegral.integral_const_mul] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun h _ => ?_
    simp only [hOD]
    ring
  have h18 : ∫ h in (0 : ℝ)..6, (6 - h) = 18 := by
    have hc : IntervalIntegrable (fun _ : ℝ => (6 : ℝ)) volume 0 6 :=
      continuous_const.intervalIntegrable _ _
    have hid : IntervalIntegrable (fun h : ℝ => h) volume 0 6 :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hc hid, intervalIntegral.integral_const, integral_id]
    norm_num
  rw [hsplit, h18]
  ring

/-- Paper (4.5), the inequality: `∫ |s| R⋆ ≥ 3/2 − (3/2) V_v ρ`. -/
theorem integral_abs_mul_symRearr_liftedDensity_ge {ρ : Euc d → ℝ}
    (hρ : IsProbDensityOn univ ρ) (v : Euc d) (hfin : dirVar v ρ ≠ ⊤) :
    3 / 2 - (3 / 2) * (dirVar v ρ).toReal ≤ ∫ p, |p.2| * symRearr (liftedDensity ρ v) p := by
  rw [integral_abs_mul_symRearr_liftedDensity hρ v]
  set V := (dirVar v ρ).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hDi : IntervalIntegrable (fun h => (6 - h) * ∫ x, |ρ x - ρ (x + h • v)|) volume 0 6 :=
    (intervalIntegrable_of_bounded (measurable_integral_abs_sub_translate hρ v) (C := 2)
      (fun h => by
        rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)]
        exact integral_abs_sub_translate_le_two hρ v h) 0 6).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  have hle : ∫ h in (0 : ℝ)..6, (6 - h) * ∫ x, |ρ x - ρ (x + h • v)| ≤
      ∫ h in (0 : ℝ)..6, (6 - h) * (h * V) := by
    have hc : IntervalIntegrable (fun h : ℝ => (6 - h) * (h * V)) volume 0 6 :=
      ((continuous_const.sub continuous_id).mul (continuous_id.mul continuous_const))
        |>.intervalIntegrable _ _
    refine intervalIntegral.integral_mono_on (by norm_num) hDi hc fun h hh => ?_
    exact mul_le_mul_of_nonneg_left (integral_abs_sub_translate_le hρ v hfin hh.1)
      (by linarith [hh.2])
  have h36 : ∫ h in (0 : ℝ)..6, (6 - h) * (h * V) = 36 * V := by
    have : (fun h : ℝ => (6 - h) * (h * V)) = fun h => V * (6 * h - h ^ 2) := by
      ext h; ring
    have hc : IntervalIntegrable (fun h : ℝ => 6 * h) volume 0 6 :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hsq : IntervalIntegrable (fun h : ℝ => h ^ 2) volume 0 6 :=
      (continuous_id.pow 2).intervalIntegrable _ _
    rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hc hsq,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
    ring
  linarith

end Komlos
