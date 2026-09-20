import Komlos.Literature.Regularized.InteriorHarmonicAux
import Komlos.Literature.PLaplacian.DiffQuotEstimate

/-!
# Difference quotients along segments (lane `L3h`)

Lane `L3h` (`reg/c2h`) proves the interior Hölder estimate for a `Ψ`-harmonic gradient field
(`exists_regHarmonic_holder_field` of `InteriorHarmonic.lean`).  Every quantitative input of that
proof rests on one elementary identity: for a Sobolev function `v` with weak gradient `G`, the
difference quotient is the *average of the gradient along the segment*,

`Δ_s^e v (x) = ∫₀¹ ⟪G (x + (t s) e), e⟫ dt`   (a.e. `x`).

Both consequences the lane needs are immediate from it and are proved here:

* `setLIntegral_sq_diffQuot_le` — the **local** `L²` bound
  `∫_A |Δ_s^e v|² ≤ ∫_S ‖G‖²` whenever `A` translated by `[0,s] e` stays inside `S`.
  This is *not* `Komlos.Literature.integral_norm_diffQuot_rpow_le`, which is global and therefore
  pays for the cut-off error; here the bound is local and sharp, which is what makes the constant
  in the Hölder estimate depend on the excess of `H` on the *data* ball only.
* `tendsto_lintegral_sq_diffQuot_sub` — `Δ_s^e v → ⟪G, e⟫` in `L²` as `s → 0`, by continuity of
  translation in `L²` (`tendsto_eLpNorm_translate_sub`, proved here from Mathlib's density of
  compactly supported continuous functions).

The identity itself is proved distributionally: both sides are locally integrable, and testing
against `ψ ∈ C_c^∞` turns the difference quotient onto `ψ` (summation by parts,
`Komlos.Literature.integral_diffQuot_mul_eq_neg`), writes `Δ_{-s}^e ψ` as a segment average by the
fundamental theorem of calculus, and applies the weak-gradient identity to each translate of `ψ`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### The segment average -/

/-- `segAvg s e G x = ∫₀¹ ⟪G (x + (t s) e), e⟫ dt`, the average of the `e`-component of `G` along
the segment from `x` to `x + s e`. -/
noncomputable def segAvg (s : ℝ) (e : Euc d) (G : Euc d → Euc d) (x : Euc d) : ℝ :=
  ∫ t in (0 : ℝ)..1, ⟪G (x + (t * s) • e), e⟫

/-- The integrand of `segAvg`, as a function on `Euc d × ℝ`. -/
theorem measurable_segAvg_uncurry {G : Euc d → Euc d} (hG : Measurable G) (s : ℝ) (e : Euc d) :
    Measurable (fun p : Euc d × ℝ => ⟪G (p.1 + (p.2 * s) • e), e⟫) := by
  have hc : Continuous fun p : Euc d × ℝ => p.1 + (p.2 * s) • e :=
    continuous_fst.add (((continuous_snd.mul continuous_const)).smul continuous_const)
  exact (hG.comp hc.measurable).inner measurable_const

/-- The segment average of a measurable field is strongly measurable (parametric integral). -/
theorem stronglyMeasurable_segAvg {G : Euc d → Euc d} (hG : Measurable G) (s : ℝ) (e : Euc d) :
    StronglyMeasurable (segAvg s e G) := by
  have hrw : segAvg s e G =
      fun x => ∫ t in Ioc (0 : ℝ) 1, ⟪G (x + (t * s) • e), e⟫ := by
    funext x
    rw [segAvg, intervalIntegral.integral_of_le zero_le_one]
  rw [hrw]
  exact (measurable_segAvg_uncurry hG s e).stronglyMeasurable.integral_prod_right'

/-- The segment average of a measurable field is a.e. strongly measurable. -/
theorem aestronglyMeasurable_segAvg {G : Euc d → Euc d} (hG : Measurable G) (s : ℝ) (e : Euc d) :
    AEStronglyMeasurable (segAvg s e G) volume :=
  (stronglyMeasurable_segAvg hG s e).aestronglyMeasurable

/-! ### Continuity of translation in `L²` -/

/-- Triangle inequality for a three-term pointwise decomposition, stated on an abstract measure
space: on `Euc d` the `Pi`-form of `eLpNorm_add_le` makes unification unfold the `PiLp`
instances and blow the heartbeat budget. -/
theorem eLpNorm_two_le_add_three {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] {f f₁ f₂ f₃ : α → E}
    (h : ∀ x, f x = f₁ x + f₂ x + f₃ x) (h1 : AEStronglyMeasurable f₁ μ)
    (h2 : AEStronglyMeasurable f₂ μ) (h3 : AEStronglyMeasurable f₃ μ) :
    eLpNorm f 2 μ ≤ eLpNorm f₁ 2 μ + eLpNorm f₂ 2 μ + eLpNorm f₃ 2 μ := by
  have hone : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have he : f = f₁ + f₂ + f₃ := funext h
  rw [he]
  exact (eLpNorm_add_le (h1.add h2) h3 hone).trans
    (add_le_add_left (eLpNorm_add_le h1 h2 hone) _)

section Translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous function vanishing outside a compact set is bounded. -/
theorem exists_bound_of_hasCompactSupport {g : Euc d → E} (hg : Continuous g)
    (hgs : HasCompactSupport g) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖g x‖ ≤ M := by
  have hts : IsCompact (tsupport g) := hgs
  obtain ⟨M, hM⟩ := hts.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact (hM x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

/-- **Continuity of translation in `L²` for continuous compactly supported functions.** -/
theorem tendsto_lintegral_translate_sub_of_continuous {g : Euc d → E} (hg : Continuous g)
    (hgs : HasCompactSupport g) {w : ℕ → Euc d} (hw : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖g (x + w n) - g x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ n, ‖w n‖ ≤ R₀ := by
    obtain ⟨R₀, hR₀⟩ := (hw.norm).bddAbove_range
    exact ⟨R₀, fun n => hR₀ ⟨n, rfl⟩⟩
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRn : ∀ n, ‖w n‖ ≤ R := fun n => (hR₀ n).trans (le_max_left _ _)
  have hts : IsCompact (tsupport g) := hgs
  set K : Set (Euc d) := Metric.cthickening R (tsupport g) with hKdef
  have hK : IsCompact K := hts.cthickening
  have hgK : tsupport g ⊆ K := Metric.self_subset_cthickening _
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_hasCompactSupport hg hgs
  have hbound : ∀ n, ∀ x, ‖g (x + w n) - g x‖ₑ ^ (2 : ℝ) ≤
      K.indicator (fun _ => (ENNReal.ofReal (2 * M)) ^ (2 : ℝ)) x := by
    intro n x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖g (x + w n) - g x‖ ≤ ‖g (x + w n)‖ + ‖g x‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM _) (hM _)
        _ = 2 * M := by ring
    · rw [Set.indicator_of_notMem hx]
      have h1 : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hgK h)
      have h2 : g (x + w n) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun h => hx ?_
        refine Metric.mem_cthickening_of_dist_le x (x + w n) R _ h ?_
        rw [dist_eq_norm]
        simpa using hRn n
      rw [h1, h2, sub_zero, enorm_zero]
      exact le_of_eq (ENNReal.zero_rpow_of_pos (by norm_num))
  have hfin : ∫⁻ x, K.indicator (fun _ => (ENNReal.ofReal (2 * M)) ^ (2 : ℝ)) x ≠ ⊤ := by
    rw [lintegral_indicator hK.measurableSet, setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hK.measure_lt_top.ne
  have hmeas : ∀ n, Measurable (fun x : Euc d => ‖g (x + w n) - g x‖ₑ ^ (2 : ℝ)) := fun n =>
    (ENNReal.continuous_rpow_const.comp (continuous_enorm.comp
      ((hg.comp (continuous_id.add continuous_const)).sub hg))).measurable
  have hlim : ∀ x : Euc d,
      Tendsto (fun n => ‖g (x + w n) - g x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    intro x
    have h0 : Tendsto (fun n => x + w n) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add hw
    have h1 : Tendsto (fun n => g (x + w n) - g x) atTop (𝓝 0) := by
      simpa using (hg.tendsto x).comp h0 |>.sub (tendsto_const_nhds (x := g x))
    have h2 : Tendsto (fun n => ‖g (x + w n) - g x‖ₑ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto (0 : E)).comp h1
    have h3 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto (0 : ℝ≥0∞) |>.comp h2
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (show (0:ℝ) < 2 by norm_num)]
      using h3
  have hDCT := tendsto_lintegral_of_dominated_convergence
    (F := fun n (x : Euc d) => ‖g (x + w n) - g x‖ₑ ^ (2 : ℝ)) (f := fun _ : Euc d => (0 : ℝ≥0∞))
    _ hmeas (fun n => Eventually.of_forall (hbound n)) hfin
    (Eventually.of_forall hlim)
  simpa using hDCT

/-- `‖f‖_{L²} = (∫⁻ ‖f‖ₑ²)^{1/2}`. -/
theorem eLpNorm_two_eq_rpow (f : Euc d → E) :
    eLpNorm f 2 volume = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp)]
  norm_num

/-- Convergence to `0` of the `L²` norms and of the `L²` energies is the same thing. -/
theorem tendsto_lintegral_two_iff_eLpNorm {F : ℕ → Euc d → E} :
    Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun n => eLpNorm (F n) 2 volume) atTop (𝓝 0) := by
  constructor
  · intro h
    have h2 := (ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto (0 : ℝ≥0∞) |>.comp h
    simp only [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)] at h2
    simpa only [eLpNorm_two_eq_rpow] using h2
  · intro h
    have h2 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto (0 : ℝ≥0∞) |>.comp h
    simp only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
    refine h2.congr fun n => ?_
    rw [eLpNorm_two_eq_rpow, ← ENNReal.rpow_mul]
    norm_num

/-- **Continuity of translation in `L²`.**  Approximate by a continuous compactly supported
function (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`) and use
`tendsto_lintegral_translate_sub_of_continuous` for the approximant. -/
theorem tendsto_lintegral_translate_sub {G : Euc d → E} (hG : MemLp G 2 volume)
    {w : ℕ → Euc d} (hw : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖G (x + w n) - G x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_lintegral_two_iff_eLpNorm]
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  set η : ℝ≥0∞ := ε / 4 with hηdef
  have hη0 : η ≠ 0 := by
    simp only [hηdef, ne_eq, ENNReal.div_eq_zero_iff]
    push Not
    exact ⟨hε.ne', by norm_num⟩
  have hεη : ε = 4 * η := (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
  obtain ⟨g, hgs, hgapp, hgc, hgmem⟩ :=
    hG.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by simp) hη0
  have hmid : Tendsto (fun n => eLpNorm (fun x => g (x + w n) - g x) 2 volume) atTop (𝓝 0) :=
    tendsto_lintegral_two_iff_eLpNorm.1 (tendsto_lintegral_translate_sub_of_continuous hgc hgs hw)
  have h2η : (0 : ℝ≥0∞) < 2 * η := pos_iff_ne_zero.2 (by simp [hη0])
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hmid (2 * η) h2η] with n hn
  have hsplit : ∀ x : Euc d, G (x + w n) - G x =
      (G - g) (x + w n) + (g (x + w n) - g x) + (g - G) x := by
    intro x
    simp only [Pi.sub_apply]
    abel
  have hm1 : AEStronglyMeasurable (fun x => (G - g) (x + w n)) volume :=
    (hG.1.sub hgmem.1).comp_measurePreserving (measurePreserving_add_right volume (w n))
  have hm2 : AEStronglyMeasurable (fun x => g (x + w n) - g x) volume :=
    ((hgc.comp (continuous_id.add continuous_const)).sub hgc).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (g - G) volume := hgmem.1.sub hG.1
  have htr : eLpNorm (fun x => (G - g) (x + w n)) 2 volume = eLpNorm (G - g) 2 volume :=
    eLpNorm_comp_measurePreserving (hG.1.sub hgmem.1) (measurePreserving_add_right volume (w n))
  have hsym : eLpNorm (g - G) 2 volume = eLpNorm (G - g) 2 volume := eLpNorm_sub_comm g G 2 volume
  calc eLpNorm (fun x => G (x + w n) - G x) 2 volume
      ≤ eLpNorm (fun x => (G - g) (x + w n)) 2 volume +
          eLpNorm (fun x => g (x + w n) - g x) 2 volume + eLpNorm (g - G) 2 volume :=
        eLpNorm_two_le_add_three hsplit hm1 hm2 hm3
    _ ≤ η + 2 * η + η := by
        rw [htr, hsym]
        exact add_le_add (add_le_add hgapp hn) hgapp
    _ = ε := by rw [hεη]; ring

end Translation

/-! ### The segment average: elementary properties -/

section SegAvgBasic

variable {s : ℝ} {e : Euc d}

/-- The segment average of a constant field. -/
theorem segAvg_const (s : ℝ) (e c : Euc d) : segAvg s e (fun _ => c) = fun _ => ⟪c, e⟫ := by
  funext x
  simp [segAvg]

/-- **The segment representation for `C¹` functions** (fundamental theorem of calculus). -/
theorem diffQuot_eq_segAvg_of_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hs : s ≠ 0)
    (e : Euc d) (x : Euc d) : diffQuot s e f x = segAvg s e (gradient f) x := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + (t * s) • e))
      (s * ⟪gradient f (x + (t * s) • e), e⟫) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + (t * s) • e) (s • e) t := by
      have h0 : HasDerivAt (fun t : ℝ => (t * s) • e) (s • e) t := by
        simpa using ((hasDerivAt_id t).mul_const s).smul_const e
      simpa using h0.const_add x
    have h2 := (hf.differentiable one_ne_zero (x + (t * s) • e)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : fderiv ℝ f (x + (t * s) • e) (s • e) = s * ⟪gradient f (x + (t * s) • e), e⟫ := by
      rw [map_smul, smul_eq_mul, fderiv_apply_eq_inner_gradient]
    rwa [h3] at h2
  have hcont : Continuous fun t : ℝ => s * ⟪gradient f (x + (t * s) • e), e⟫ :=
    continuous_const.mul (((continuous_gradient hf).comp
      (continuous_const.add ((continuous_id.mul continuous_const).smul
        continuous_const))).inner continuous_const)
  have hftc : ∫ t in (0 : ℝ)..1, s * ⟪gradient f (x + (t * s) • e), e⟫ =
      f (x + ((1 : ℝ) * s) • e) - f (x + ((0 : ℝ) * s) • e) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hftc
  simp only [one_mul, zero_mul, zero_smul, add_zero] at hftc
  rw [diffQuot_real, segAvg, div_eq_iff hs, ← hftc]
  ring

end SegAvgBasic

/-! ### The basic `L²` inequality for segment averages -/

section SegAvgEstimate

variable {s : ℝ} {e : Euc d} {G G₁ G₂ : Euc d → Euc d}

/-- `segAvg` of a measurable field, against a measurable field: the pointwise `L²` Jensen
inequality along the segment.  Junk values are harmless: if the right-hand side is finite then
both line integrals converge. -/
theorem enorm_segAvg_sub_sq_le (hG₁ : Measurable G₁) (hG₂ : Measurable G₂) (s : ℝ)
    (he : ‖e‖ = 1) (x : Euc d) :
    ‖segAvg s e G₁ x - segAvg s e G₂ x‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ ^ (2 : ℝ) := by
  set g₁ : ℝ → ℝ := fun t => ⟪G₁ (x + (t * s) • e), e⟫ with hg₁
  set g₂ : ℝ → ℝ := fun t => ⟪G₂ (x + (t * s) • e), e⟫ with hg₂
  have hcont : Continuous fun t : ℝ => x + (t * s) • e :=
    continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  have hm₁ : Measurable g₁ := (hG₁.comp hcont.measurable).inner measurable_const
  have hm₂ : Measurable g₂ := (hG₂.comp hcont.measurable).inner measurable_const
  by_cases htop : (∫⁻ t in Ioc (0 : ℝ) 1,
      ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ ^ (2 : ℝ)) = ⊤
  · rw [htop]; exact le_top
  -- the difference is square integrable on the segment, hence integrable
  have hdm : Measurable fun t : ℝ => G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e) :=
    (hG₁.comp hcont.measurable).sub (hG₂.comp hcont.measurable)
  have hdint : IntegrableOn (fun t : ℝ => G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e))
      (Ioc (0 : ℝ) 1) := by
    refine ⟨hdm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hj := lintegral_Ioc_rpow_le 1 (p := 2) one_lt_two
      (h := fun t => ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ)
      hdm.enorm.aemeasurable
    rw [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] at hj
    have hne : (∫⁻ t in Ioc (0 : ℝ) 1,
        ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ) ^ (2 : ℝ) ≠ ⊤ :=
      ne_top_of_le_ne_top htop hj
    exact lt_top_iff_ne_top.2 fun hc => hne (by rw [hc]; exact ENNReal.top_rpow_of_pos (by norm_num))
  have hdiff : IntegrableOn (fun t => g₁ t - g₂ t) (Ioc (0 : ℝ) 1) := by
    have h0 : IntegrableOn
        (fun t : ℝ => ⟪G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e), e⟫) (Ioc (0 : ℝ) 1) :=
      hdint.inner_const (𝕜 := ℝ) e
    refine h0.congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only [hg₁, hg₂, inner_sub_left]
  -- the pointwise bound for the difference of the two segment averages
  have hbdd : ∀ t : ℝ, ‖g₁ t - g₂ t‖ₑ ≤ ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ := by
    intro t
    have h1 : g₁ t - g₂ t = ⟪G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e), e⟫ := by
      simp only [hg₁, hg₂, inner_sub_left]
    rw [h1]
    refine (enorm_real_inner_le _ _).trans_eq ?_
    rw [← ofReal_norm e, he]
    simp
  have hkey : ‖segAvg s e G₁ x - segAvg s e G₂ x‖ₑ ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ := by
    by_cases h1 : IntegrableOn g₁ (Ioc (0 : ℝ) 1)
    · have h2 : IntegrableOn g₂ (Ioc (0 : ℝ) 1) := by
        have h0 : IntegrableOn (g₁ - fun t => g₁ t - g₂ t) (Ioc (0 : ℝ) 1) := h1.sub hdiff
        refine h0.congr_fun (fun t _ => ?_) measurableSet_Ioc
        simp only [Pi.sub_apply]
        ring
      have hsplit : segAvg s e G₁ x - segAvg s e G₂ x = ∫ t in Ioc (0 : ℝ) 1, (g₁ t - g₂ t) := by
        rw [segAvg, segAvg, intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_of_le zero_le_one, ← integral_sub h1 h2]
      rw [hsplit]
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t => hbdd t)
    · have h2 : ¬ IntegrableOn g₂ (Ioc (0 : ℝ) 1) := by
        intro h2
        have h0 : IntegrableOn (g₂ + fun t => g₁ t - g₂ t) (Ioc (0 : ℝ) 1) := h2.add hdiff
        refine h1 (h0.congr_fun (fun t _ => ?_) measurableSet_Ioc)
        simp only [Pi.add_apply]
        ring
      have e1 : segAvg s e G₁ x = 0 := by
        rw [segAvg, intervalIntegral.integral_of_le zero_le_one,
          integral_undef (fun hc => h1 hc)]
      have e2 : segAvg s e G₂ x = 0 := by
        rw [segAvg, intervalIntegral.integral_of_le zero_le_one,
          integral_undef (fun hc => h2 hc)]
      rw [e1, e2, sub_zero, enorm_zero]
      exact zero_le
  refine (ENNReal.rpow_le_rpow hkey (by norm_num)).trans ?_
  have hj := lintegral_Ioc_rpow_le 1 (p := 2) one_lt_two
    (h := fun t => ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ) hdm.enorm.aemeasurable
  rwa [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] at hj

end SegAvgEstimate

/-! ### The integrated `L²` bounds -/

section SegAvgIntegral

variable {s : ℝ} {e : Euc d} {G G₁ G₂ : Euc d → Euc d}

/-- Joint measurability of the segment integrand. -/
theorem measurable_seg_pair (hG₁ : Measurable G₁) (hG₂ : Measurable G₂) (s : ℝ) (e : Euc d) :
    Measurable (fun p : Euc d × ℝ =>
      ‖G₁ (p.1 + (p.2 * s) • e) - G₂ (p.1 + (p.2 * s) • e)‖ₑ ^ (2 : ℝ)) := by
  have hc : Continuous fun p : Euc d × ℝ => p.1 + (p.2 * s) • e :=
    continuous_fst.add ((continuous_snd.mul continuous_const).smul continuous_const)
  exact (ENNReal.continuous_rpow_const.measurable).comp
    (((hG₁.comp hc.measurable).sub (hG₂.comp hc.measurable)).enorm)

/-- **The global `L²` contraction of the segment average.** -/
theorem lintegral_segAvg_sub_sq_le (hG₁ : Measurable G₁) (hG₂ : Measurable G₂) (s : ℝ)
    (he : ‖e‖ = 1) :
    (∫⁻ x, ‖segAvg s e G₁ x - segAvg s e G₂ x‖ₑ ^ (2 : ℝ)) ≤
      ∫⁻ y, ‖G₁ y - G₂ y‖ₑ ^ (2 : ℝ) := by
  calc (∫⁻ x, ‖segAvg s e G₁ x - segAvg s e G₂ x‖ₑ ^ (2 : ℝ))
      ≤ ∫⁻ x, ∫⁻ t in Ioc (0 : ℝ) 1,
          ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ ^ (2 : ℝ) :=
        lintegral_mono fun x => enorm_segAvg_sub_sq_le hG₁ hG₂ s he x
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x,
          ‖G₁ (x + (t * s) • e) - G₂ (x + (t * s) • e)‖ₑ ^ (2 : ℝ) :=
        lintegral_lintegral_swap (measurable_seg_pair hG₁ hG₂ s e).aemeasurable
    _ = ∫⁻ _t in Ioc (0 : ℝ) 1, ∫⁻ y, ‖G₁ y - G₂ y‖ₑ ^ (2 : ℝ) := by
        refine lintegral_congr fun t => ?_
        exact lintegral_add_right_eq_self
          (fun y => ‖G₁ y - G₂ y‖ₑ ^ (2 : ℝ)) ((t * s) • e)
    _ = ∫⁻ y, ‖G₁ y - G₂ y‖ₑ ^ (2 : ℝ) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **The local `L²` bound for the segment average.**  If every segment `[x, x + s e]` with
`x ∈ A` stays inside `S`, then the `L²` energy of `segAvg s e G - ⟪c, e⟫` on `A` is at most the
`L²` energy of `G - c` on `S`. -/
theorem setLIntegral_segAvg_sub_sq_le (hG : Measurable G) (s : ℝ) (he : ‖e‖ = 1)
    {A S : Set (Euc d)} (hA : MeasurableSet A) (hS : MeasurableSet S) (c : Euc d)
    (hAS : ∀ x ∈ A, ∀ t ∈ Ioc (0 : ℝ) 1, x + (t * s) • e ∈ S) :
    (∫⁻ x in A, ‖segAvg s e G x - ⟪c, e⟫‖ₑ ^ (2 : ℝ)) ≤ ∫⁻ y in S, ‖G y - c‖ₑ ^ (2 : ℝ) := by
  set g : Euc d → ℝ≥0∞ := S.indicator (fun y => ‖G y - c‖ₑ ^ (2 : ℝ)) with hgdef
  have hconst : segAvg s e (fun _ => c) = fun _ => ⟪c, e⟫ := segAvg_const s e c
  have hstep : ∀ x ∈ A, ‖segAvg s e G x - ⟪c, e⟫‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, g (x + (t * s) • e) := by
    intro x hx
    have h0 := enorm_segAvg_sub_sq_le hG (measurable_const (a := c)) s he x
    rw [hconst] at h0
    refine h0.trans (lintegral_mono_ae ?_)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    rw [hgdef, Set.indicator_of_mem (hAS x hx t ht)]
  calc (∫⁻ x in A, ‖segAvg s e G x - ⟪c, e⟫‖ₑ ^ (2 : ℝ))
      ≤ ∫⁻ x in A, ∫⁻ t in Ioc (0 : ℝ) 1, g (x + (t * s) • e) :=
        lintegral_mono_ae (by
          filter_upwards [self_mem_ae_restrict hA] with x hx using hstep x hx)
    _ ≤ ∫⁻ x, ∫⁻ t in Ioc (0 : ℝ) 1, g (x + (t * s) • e) :=
        lintegral_mono_set (Set.subset_univ _) |>.trans_eq (by rw [Measure.restrict_univ])
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x, g (x + (t * s) • e) := by
        refine lintegral_lintegral_swap ?_
        have hc : Continuous fun p : Euc d × ℝ => p.1 + (p.2 * s) • e :=
          continuous_fst.add ((continuous_snd.mul continuous_const).smul continuous_const)
        have hgm : Measurable g := by
          refine Measurable.indicator ?_ hS
          exact (ENNReal.continuous_rpow_const.measurable).comp ((hG.sub measurable_const).enorm)
        exact (hgm.comp hc.measurable).aemeasurable
    _ = ∫⁻ _t in Ioc (0 : ℝ) 1, ∫⁻ y, g y := by
        refine lintegral_congr fun t => lintegral_add_right_eq_self g ((t * s) • e)
    _ = ∫⁻ y, g y := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
    _ = ∫⁻ y in S, ‖G y - c‖ₑ ^ (2 : ℝ) := by rw [hgdef, lintegral_indicator hS]

end SegAvgIntegral

/-! ### The segment representation of a Sobolev difference quotient -/

section Representation

/-- Triangle inequality for a pointwise difference, on an abstract measure space. -/
theorem eLpNorm_two_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] {f f₁ f₂ : α → E} (h : ∀ x, f x = f₁ x - f₂ x)
    (h1 : AEStronglyMeasurable f₁ μ) (h2 : AEStronglyMeasurable f₂ μ) :
    eLpNorm f 2 μ ≤ eLpNorm f₁ 2 μ + eLpNorm f₂ 2 μ := by
  have he : f = f₁ - f₂ := funext h
  rw [he]
  exact eLpNorm_sub_le h1 h2 (by norm_num)

/-- Triangle inequality for a pointwise sum, on an abstract measure space. -/
theorem eLpNorm_two_le_add_two {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] {f f₁ f₂ : α → E} (h : ∀ x, f x = f₁ x + f₂ x)
    (h1 : AEStronglyMeasurable f₁ μ) (h2 : AEStronglyMeasurable f₂ μ) :
    eLpNorm f 2 μ ≤ eLpNorm f₁ 2 μ + eLpNorm f₂ 2 μ := by
  have he : f = f₁ + f₂ := funext h
  rw [he]
  exact eLpNorm_add_le h1 h2 (by norm_num)

/-- `L²` norm of a constant multiple, on an abstract measure space. -/
theorem eLpNorm_two_const_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → E} (c : ℝ) (h : ∀ x, f x = c • g x) :
    eLpNorm f 2 μ = ‖c‖ₑ * eLpNorm g 2 μ := by
  have he : f = c • g := funext h
  rw [he, eLpNorm_const_smul]

/-- Monotonicity of the `L²` norm in the `L²` energy. -/
theorem eLpNorm_two_le_of_lintegral_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euc d → E} {g : Euc d → F}
    (h : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ≤ ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ)) :
    eLpNorm f 2 volume ≤ eLpNorm g 2 volume := by
  rw [eLpNorm_two_eq_rpow, eLpNorm_two_eq_rpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- Pi-form and lambda-form of a difference, for `eLpNorm` (abstract domain: on `Euc d` the
defeq check unfolds the `PiLp` instances). -/
theorem eLpNorm_lambda_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] (f g : α → E) (p : ℝ≥0∞) :
    eLpNorm (fun x => f x - g x) p μ = eLpNorm (f - g) p μ := rfl

/-- Translation invariance of `eLpNorm`, with the translate written as a lambda. -/
theorem eLpNorm_comp_add_right {E : Type*} [NormedAddCommGroup E] {f : Euc d → E}
    (hf : AEStronglyMeasurable f volume) (w : Euc d) (p : ℝ≥0∞) :
    eLpNorm (fun x => f (x + w)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right volume w)

/-- Measurability of a translate, written as a lambda. -/
theorem aestronglyMeasurable_comp_add_right {E : Type*} [NormedAddCommGroup E] {f : Euc d → E}
    (hf : AEStronglyMeasurable f volume) (w : Euc d) :
    AEStronglyMeasurable (fun x => f (x + w)) volume :=
  hf.comp_measurePreserving (measurePreserving_add_right volume w)

/-- A difference quotient of an a.e. strongly measurable function is a.e. strongly
measurable. -/
theorem aestronglyMeasurable_diffQuot {f : Euc d → ℝ} (hf : AEStronglyMeasurable f volume)
    (s : ℝ) (e : Euc d) : AEStronglyMeasurable (fun x => diffQuot s e f x) volume := by
  have h1 : AEStronglyMeasurable (fun x => f (x + s • e)) volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume (s • e))
  have h2 : AEStronglyMeasurable (fun x => f (x + s • e) - f x) volume := h1.sub hf
  have h3 : AEStronglyMeasurable ((s⁻¹ : ℝ) • fun x => f (x + s • e) - f x) volume :=
    h2.const_smul _
  exact h3.congr (Eventually.of_forall fun x => rfl)

set_option maxHeartbeats 1000000 in
/-- **Difference quotients are bounded on `L²` at a fixed step**:
`‖Δ_s^e f - Δ_s^e g‖_{L²} ≤ 2 |s|⁻¹ ‖f - g‖_{L²}`. -/
theorem eLpNorm_diffQuot_sub_le {f g : Euc d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (s : ℝ) (e : Euc d) :
    eLpNorm (fun x => diffQuot s e f x - diffQuot s e g x) 2 volume ≤
      ‖(s⁻¹ : ℝ)‖ₑ * (eLpNorm (fun x => f x - g x) 2 volume +
        eLpNorm (fun x => f x - g x) 2 volume) := by
  set w : Euc d → ℝ := fun x => f x - g x with hwdef
  have hwm : AEStronglyMeasurable w volume := hf.sub hg
  have hwm' : AEStronglyMeasurable (fun x => w (x + s • e)) volume :=
    aestronglyMeasurable_comp_add_right hwm (s • e)
  have heq : eLpNorm (fun x => diffQuot s e f x - diffQuot s e g x) 2 volume =
      ‖(s⁻¹ : ℝ)‖ₑ * eLpNorm (fun x => w (x + s • e) - w x) 2 volume := by
    refine eLpNorm_two_const_smul (s⁻¹) fun x => ?_
    simp only [hwdef, diffQuot_apply, smul_eq_mul]
    ring
  have htr : eLpNorm (fun x => w (x + s • e)) 2 volume = eLpNorm w 2 volume :=
    eLpNorm_comp_add_right hwm (s • e) 2
  rw [heq]
  refine mul_le_mul' le_rfl ?_
  refine (eLpNorm_two_sub_le (fun _ => rfl) hwm' hwm).trans ?_
  rw [htr]

/-- **The segment representation of a difference quotient**: for `v ∈ L²` with weak gradient
`G ∈ L²`, `Δ_s^e v (x) = ∫₀¹ ⟪G (x + t s e), e⟫ dt` for a.e. `x`.

Proof by mollification: for the smooth mollifications the identity is the fundamental theorem of
calculus (`diffQuot_eq_segAvg_of_contDiff`), and both sides converge in `L²` — the left one
because difference quotients are bounded operators on `L²` at fixed step, the right one by the
`L²` contraction `lintegral_segAvg_sub_sq_le` of the segment average. -/
theorem diffQuot_ae_eq_segAvg {v : Euc d → ℝ} {G : Euc d → Euc d} (hG : Measurable G)
    (hvG : HasWeakGradient v G) (hv2 : MemLp v 2 volume) (hG2 : MemLp G 2 volume)
    {s : ℝ} (hs : s ≠ 0) {e : Euc d} (he : ‖e‖ = 1) :
    diffQuot s e v =ᵐ[volume] segAvg s e G := by
  have h2e : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  have hv2' : MemLp v (ENNReal.ofReal (2 : ℝ)) volume := by rwa [h2e]
  have hG2' : MemLp G (ENNReal.ofReal (2 : ℝ)) volume := by rwa [h2e]
  set φ : ℕ → ContDiffBump (0 : Euc d) := fun n => mollifierBump n with hφ_def
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set u : ℕ → Euc d → ℝ := fun n => mollifyWith ((φ n).normed volume) v with hu_def
  set Gm : ℕ → Euc d → Euc d := fun n => mollifyWith ((φ n).normed volume) G with hGm_def
  have hu_smooth : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    contDiff_mollifyWith (φ n).contDiff_normed (φ n).hasCompactSupport_normed
      hvG.locallyIntegrable
  have hgrad : ∀ n, gradient (u n) = Gm n := fun n =>
    gradient_mollifyWith hvG (φ n).contDiff_normed (φ n).hasCompactSupport_normed
  have hGm_meas : ∀ n, Measurable (Gm n) := fun n =>
    (continuous_mollifyWith (φ n).continuous_normed (φ n).hasCompactSupport_normed
      hvG.locallyIntegrable_grad).measurable
  have hid : ∀ n x, diffQuot s e (u n) x = segAvg s e (Gm n) x := fun n x => by
    rw [diffQuot_eq_segAvg_of_contDiff (hu_smooth n) hs e x, hgrad n]
  -- the two `L²` convergences
  set cv : ℕ → ℝ≥0∞ := fun n => eLpNorm (fun x => u n x - v x) 2 volume with hcv_def
  set cG : ℕ → ℝ≥0∞ := fun n => eLpNorm (fun x => Gm n x - G x) 2 volume with hcG_def
  have hcv : Tendsto cv atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_mollifyWith_sub hφ (p := (2 : ℝ)) one_lt_two hv2'
    rw [h2e] at h
    simp only [← eLpNorm_lambda_sub] at h
    exact h
  have hcG : Tendsto cG atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_mollifyWith_sub hφ (p := (2 : ℝ)) one_lt_two hG2'
    rw [h2e] at h
    simp only [← eLpNorm_lambda_sub] at h
    exact h
  have hvm : AEStronglyMeasurable v volume := hv2.aestronglyMeasurable
  have hA : ∀ n, eLpNorm (fun x => diffQuot s e v x - diffQuot s e (u n) x) 2 volume ≤
      ‖(s⁻¹ : ℝ)‖ₑ * (cv n + cv n) := by
    intro n
    have hun : AEStronglyMeasurable (u n) volume :=
      (hu_smooth n).continuous.aestronglyMeasurable
    have hsym : eLpNorm (fun x => v x - u n x) 2 volume = cv n := by
      rw [hcv_def]
      simp only [eLpNorm_lambda_sub]
      exact eLpNorm_sub_comm v (u n) 2 volume
    have h0 := eLpNorm_diffQuot_sub_le hvm hun s e
    rwa [hsym] at h0
  -- the segment average is an `L²` contraction
  have hB : ∀ n, eLpNorm (fun x => segAvg s e (Gm n) x - segAvg s e G x) 2 volume ≤ cG n := by
    intro n
    have h0 : eLpNorm (fun x => segAvg s e (Gm n) x - segAvg s e G x) 2 volume ≤
        eLpNorm (fun x => Gm n x - G x) 2 volume :=
      eLpNorm_two_le_of_lintegral_le (f := fun x => segAvg s e (Gm n) x - segAvg s e G x)
        (g := fun x => Gm n x - G x) (lintegral_segAvg_sub_sq_le (hGm_meas n) hG s he)
    exact h0
  -- combine
  have hfm1 : ∀ n, AEStronglyMeasurable
      (fun x => diffQuot s e v x - diffQuot s e (u n) x) volume := fun n =>
    (aestronglyMeasurable_diffQuot hvm s e).sub
      (aestronglyMeasurable_diffQuot (hu_smooth n).continuous.aestronglyMeasurable s e)
  have hfm2 : ∀ n, AEStronglyMeasurable
      (fun x => segAvg s e (Gm n) x - segAvg s e G x) volume := fun n =>
    (aestronglyMeasurable_segAvg (hGm_meas n) s e).sub (aestronglyMeasurable_segAvg hG s e)
  have hfinal : ∀ n, eLpNorm (fun x => diffQuot s e v x - segAvg s e G x) 2 volume ≤
      ‖(s⁻¹ : ℝ)‖ₑ * (cv n + cv n) + cG n := by
    intro n
    refine (eLpNorm_two_le_add_two (f := fun x => diffQuot s e v x - segAvg s e G x)
      (f₁ := fun x => diffQuot s e v x - diffQuot s e (u n) x)
      (f₂ := fun x => segAvg s e (Gm n) x - segAvg s e G x)
      (fun x => by rw [hid n x]; ring) (hfm1 n) (hfm2 n)).trans ?_
    exact add_le_add (hA n) (hB n)
  have hlim : Tendsto (fun n => ‖(s⁻¹ : ℝ)‖ₑ * (cv n + cv n) + cG n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => cv n + cv n) atTop (𝓝 0) := by simpa using hcv.add hcv
    have h1 : Tendsto (fun n => ‖(s⁻¹ : ℝ)‖ₑ * (cv n + cv n)) atTop (𝓝 0) := by
      have h2 := ENNReal.Tendsto.const_mul (a := ‖(s⁻¹ : ℝ)‖ₑ) h0 (Or.inr enorm_ne_top)
      simpa using h2
    simpa using h1.add hcG
  have hzero : eLpNorm (fun x => diffQuot s e v x - segAvg s e G x) 2 volume = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hfinal)) zero_le
  have hfm : AEStronglyMeasurable (fun x => diffQuot s e v x - segAvg s e G x) volume :=
    (aestronglyMeasurable_diffQuot hvm s e).sub (aestronglyMeasurable_segAvg hG s e)
  have hae := (eLpNorm_eq_zero_iff hfm (by norm_num)).1 hzero
  filter_upwards [hae] with x hx
  have h0 : diffQuot s e v x - segAvg s e G x = 0 := hx
  linarith

end Representation

/-! ### The two consequences used by the Hölder estimate -/

section Consequences

variable {v : Euc d → ℝ} {G : Euc d → Euc d} {s : ℝ} {e : Euc d}

/-- `∫⁻ ‖f‖ₑ² = (‖f‖_{L²})²`. -/
theorem lintegral_enorm_rpow_two_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Euc d → E) : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) = eLpNorm f 2 volume ^ (2 : ℝ) := by
  rw [eLpNorm_two_eq_rpow, ← ENNReal.rpow_mul]
  norm_num

/-- A real set integral of a square is bounded by any `ENNReal` bound for the corresponding
lower integral. -/
theorem setIntegral_sq_le_of_lintegral_le {f : Euc d → ℝ} {A : Set (Euc d)} {M : ℝ} (hM : 0 ≤ M)
    (h : (∫⁻ x in A, ‖f x‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal M) : (∫ x in A, f x ^ 2) ≤ M := by
  by_cases hint : IntegrableOn (fun x => f x ^ 2) A
  · have hnn : 0 ≤ᵐ[volume.restrict A] fun x => f x ^ 2 :=
      Eventually.of_forall fun x => sq_nonneg _
    have hrw : (∫ x in A, f x ^ 2) = (∫⁻ x in A, ENNReal.ofReal (f x ^ 2)).toReal :=
      integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable
    have hcongr : (∫⁻ x in A, ENNReal.ofReal (f x ^ 2)) = ∫⁻ x in A, ‖f x‖ₑ ^ (2 : ℝ) :=
      lintegral_congr fun x => (enorm_rpow_two_real (f x)).symm
    rw [hrw, hcongr]
    calc (∫⁻ x in A, ‖f x‖ₑ ^ (2 : ℝ)).toReal ≤ (ENNReal.ofReal M).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = M := ENNReal.toReal_ofReal hM
  · rw [integral_undef hint]
    exact hM

/-- **The local `L²` bound for a difference quotient.**  If every segment `[x, x + s e]` with
`x ∈ A` stays inside `S`, then
`∫_A |Δ_s^e v - ⟪c, e⟫|² ≤ ∫_S ‖G - c‖²`, with **no** cut-off error. -/
theorem setIntegral_sq_diffQuot_sub_le (hG : Measurable G) (hvG : HasWeakGradient v G)
    (hv2 : MemLp v 2 volume) (hG2 : MemLp G 2 volume) (hs : s ≠ 0) (he : ‖e‖ = 1)
    {A S : Set (Euc d)} (hA : MeasurableSet A) (hS : MeasurableSet S) (c : Euc d)
    (hAS : ∀ x ∈ A, ∀ t ∈ Ioc (0 : ℝ) 1, x + (t * s) • e ∈ S)
    (hint : IntegrableOn (fun y => ‖G y - c‖ ^ 2) S) :
    (∫ x in A, (diffQuot s e v x - ⟪c, e⟫) ^ 2) ≤ ∫ y in S, ‖G y - c‖ ^ 2 := by
  have hnn : 0 ≤ ∫ y in S, ‖G y - c‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine setIntegral_sq_le_of_lintegral_le hnn ?_
  have hae : diffQuot s e v =ᵐ[volume] segAvg s e G :=
    diffQuot_ae_eq_segAvg hG hvG hv2 hG2 hs he
  have hcongr : (∫⁻ x in A, ‖diffQuot s e v x - ⟪c, e⟫‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x in A, ‖segAvg s e G x - ⟪c, e⟫‖ₑ ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with x hx
    rw [hx]
  rw [hcongr]
  refine (setLIntegral_segAvg_sub_sq_le hG s he hA hS c hAS).trans (le_of_eq ?_)
  have hnn' : 0 ≤ᵐ[volume.restrict S] fun y => ‖G y - c‖ ^ 2 :=
    Eventually.of_forall fun y => sq_nonneg _
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn']
  exact lintegral_congr fun y => enorm_rpow_two (G y - c)

set_option maxHeartbeats 1000000 in
/-- **The `L²` energy of a translate is uniformly bounded**: `∫ ‖G(·+w) - G‖² ≤ (2‖G‖_{L²})²`. -/
theorem lintegral_translate_sub_le (hG2 : MemLp G 2 volume) (w : Euc d) :
    (∫⁻ x, ‖G (x + w) - G x‖ₑ ^ (2 : ℝ)) ≤
      (eLpNorm G 2 volume + eLpNorm G 2 volume) ^ (2 : ℝ) := by
  have h1 : eLpNorm (fun x => G (x + w) - G x) 2 volume ≤
      eLpNorm G 2 volume + eLpNorm G 2 volume := by
    have h0 := eLpNorm_two_sub_le (f := fun x => G (x + w) - G x)
      (f₁ := fun x => G (x + w)) (f₂ := G) (fun _ => rfl)
      (aestronglyMeasurable_comp_add_right hG2.1 w) hG2.1
    rwa [eLpNorm_comp_add_right hG2.1 w 2] at h0
  rw [lintegral_enorm_rpow_two_eq]
  exact ENNReal.rpow_le_rpow h1 (by norm_num)

set_option maxHeartbeats 1000000 in
/-- **`Δ_s^e v → ⟪G, e⟫` in `L²` as the step tends to `0`.** -/
theorem tendsto_lintegral_diffQuot_sub (hG : Measurable G) (hvG : HasWeakGradient v G)
    (hv2 : MemLp v 2 volume) (hG2 : MemLp G 2 volume) (he : ‖e‖ = 1)
    {sn : ℕ → ℝ} (hsn : ∀ n, sn n ≠ 0) (h0 : Tendsto sn atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖diffQuot (sn n) e v x - ⟪G x, e⟫‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
  set Θ : Euc d → ℝ≥0∞ := fun w => ∫⁻ x, ‖G (x + w) - G x‖ₑ ^ (2 : ℝ) with hΘdef
  -- the pointwise Jensen bound
  have hpt : ∀ (s : ℝ) (x : Euc d), ‖segAvg s e G x - ⟪G x, e⟫‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ‖G (x + (t * s) • e) - G x‖ₑ ^ (2 : ℝ) := by
    intro s x
    have h := enorm_segAvg_sub_sq_le hG (measurable_const (a := G x)) s he x
    rwa [segAvg_const] at h
  -- the integrated bound
  have hbound : ∀ s : ℝ, (∫⁻ x, ‖segAvg s e G x - ⟪G x, e⟫‖ₑ ^ (2 : ℝ)) ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, Θ ((t * s) • e) := by
    intro s
    have hjm : Measurable (fun p : Euc d × ℝ =>
        ‖G (p.1 + (p.2 * s) • e) - G p.1‖ₑ ^ (2 : ℝ)) := by
      have hc : Continuous fun p : Euc d × ℝ => p.1 + (p.2 * s) • e :=
        continuous_fst.add ((continuous_snd.mul continuous_const).smul continuous_const)
      exact (ENNReal.continuous_rpow_const.measurable).comp
        (((hG.comp hc.measurable).sub (hG.comp measurable_fst)).enorm)
    calc (∫⁻ x, ‖segAvg s e G x - ⟪G x, e⟫‖ₑ ^ (2 : ℝ))
        ≤ ∫⁻ x, ∫⁻ t in Ioc (0 : ℝ) 1, ‖G (x + (t * s) • e) - G x‖ₑ ^ (2 : ℝ) :=
          lintegral_mono fun x => hpt s x
      _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x, ‖G (x + (t * s) • e) - G x‖ₑ ^ (2 : ℝ) :=
          lintegral_lintegral_swap hjm.aemeasurable
      _ = ∫⁻ t in Ioc (0 : ℝ) 1, Θ ((t * s) • e) := rfl
  -- the sequence of bounds tends to zero
  have hmeas : ∀ n, Measurable (fun t : ℝ => Θ ((t * sn n) • e)) := by
    intro n
    have hc : Continuous fun p : ℝ × Euc d => p.2 + (p.1 * sn n) • e :=
      continuous_snd.add ((continuous_fst.mul continuous_const).smul continuous_const)
    have hjm : Measurable (fun p : ℝ × Euc d =>
        ‖G (p.2 + (p.1 * sn n) • e) - G p.2‖ₑ ^ (2 : ℝ)) :=
      (ENNReal.continuous_rpow_const.measurable).comp
        (((hG.comp hc.measurable).sub (hG.comp measurable_snd)).enorm)
    exact hjm.lintegral_prod_right'
  have hdom : ∀ n, ∀ t : ℝ, Θ ((t * sn n) • e) ≤
      (eLpNorm G 2 volume + eLpNorm G 2 volume) ^ (2 : ℝ) := fun n t =>
    lintegral_translate_sub_le hG2 _
  have hfin : (∫⁻ _t in Ioc (0 : ℝ) 1,
      (eLpNorm G 2 volume + eLpNorm G 2 volume) ^ (2 : ℝ)) ≠ ⊤ := by
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.add_ne_top.2 ⟨hG2.eLpNorm_ne_top, hG2.eLpNorm_ne_top⟩)
  have hlimt : ∀ t : ℝ, Tendsto (fun n => Θ ((t * sn n) • e)) atTop (𝓝 0) := by
    intro t
    have hw : Tendsto (fun n => (t * sn n) • e) atTop (𝓝 0) := by
      have : Tendsto (fun n => t * sn n) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := t)).mul h0
      simpa using this.smul_const e
    exact tendsto_lintegral_translate_sub hG2 hw
  have hB : Tendsto (fun n => ∫⁻ t in Ioc (0 : ℝ) 1, Θ ((t * sn n) • e)) atTop (𝓝 0) := by
    have hDCT := tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (F := fun n (t : ℝ) => Θ ((t * sn n) • e)) (f := fun _ : ℝ => (0 : ℝ≥0∞))
      _ (fun n => hmeas n) (fun n => Eventually.of_forall (hdom n)) hfin
      (Eventually.of_forall hlimt)
    simpa using hDCT
  -- transfer to the difference quotients
  have hcongr : ∀ n, (∫⁻ x, ‖diffQuot (sn n) e v x - ⟪G x, e⟫‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x, ‖segAvg (sn n) e G x - ⟪G x, e⟫‖ₑ ^ (2 : ℝ) := by
    intro n
    refine lintegral_congr_ae ?_
    filter_upwards [diffQuot_ae_eq_segAvg hG hvG hv2 hG2 (hsn n) he] with x hx
    rw [hx]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
    (fun n => zero_le) (fun n => ?_)
  rw [hcongr n]
  exact hbound (sn n)

end Consequences

end Komlos.Literature.Regularized
