import Komlos.Literature.Regularized.InteriorHarmonicHolderLin

/-!
# The interior Campanato decay of a `Ψ`-harmonic gradient field (lane `L3h`)

This file carries the quantitative core of lane `L3h`: the scale-invariant decay of the `L²`
excess of a `Ψ`-harmonic gradient field,

`sqExcess H x₀ ρ ≤ Cdec (2ρ/r)^{d+2β} sqExcess H x₀ (r/2)`,  `0 < ρ ≤ r/2`,

for `H` a weak gradient with `div ∇Ψ(H) = 0` on `ball x₀ r`.  Together with Campanato's
criterion (`Komlos.Literature.exists_holder_of_campanato`, applied in
`InteriorHarmonicHolder.lean`) it gives the conclusion of link 2 of the interior regularity
chain, `exists_regHarmonic_campanato_field`.

## The route (uniformly in the difference-quotient step)

Fix a unit vector `e`, put `q = (H)_{B_{r/2}}` and localize: with a cut-off `ζ ≡ 1` on
`closedBall x₀ (0.46 r)` and supported in `ball x₀ (0.48 r)`, the function
`v = ζ · (h - ⟪q, ·⟫ - a)` is a global `W^{1,2}` function whose weak gradient `Gv` equals
`H - q` on `ball x₀ (0.46 r)`.

1. For `0 < s ≤ r/100`, `u_s = Δ_s^e v` is a weak solution of the **linear** equation
   `div (A_s ∇u_s) = 0` on `ball x₀ (0.45 r)`, where
   `A_s x = ∫₀¹ D(∇Ψ)(H x + t (H (x + s e) - H x)) dt` is bounded, measurable and uniformly
   elliptic with the ellipticity constants of `Ψ` (`InteriorHarmonicHolderLin.lean`).
2. `∫_{B} |u_s|² ≤ ∫_{B_{r/2}} ‖H - q‖²` **uniformly in `s`**, with no cut-off error: this is
   the local difference-quotient bound `setIntegral_sq_diffQuot_sub_le` of
   `InteriorHarmonicHolderSeg.lean`, which rests on the segment representation
   `Δ_s^e v = ∫₀¹ ⟪Gv (· + t s e), e⟫ dt`.
3. De Giorgi–Nash (`exists_essSup_bound`, `exists_osc_decay`) turns 1 and 2 into an
   oscillation decay for `u_s` that is uniform in `s`.
4. `u_s → ⟪H - q, e⟫` in `L²` as `s → 0` (`tendsto_lintegral_diffQuot_sub`), and the `L²`
   excess is continuous along that convergence; summing over an orthonormal basis gives the
   decay for `H`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

set_option linter.unusedSectionVars false

variable {d : ℕ} {Ψ : Euc d → ℝ}

/-- `h` is locally square integrable on `U`: square integrable on every closed ball inside `U`.

**DEVIATION.**  `IsRegHarmonicField Ψ U h H` does *not* imply that the potential `h` is locally
integrable on `U`: the field `HasWeakGradientOn.integral_eq` is stated with Lean integrals, which
take the junk value `0` when the integrand fails to be integrable, so the hypothesis "`H` is a
weak gradient of `h`" carries no information for such an `h` — and without it the conclusion is
false (for `Ψ = ‖·‖²/2` the equation alone says `div H = 0`, satisfied by any divergence-free
`L²` field).  The lane therefore carries this hypothesis explicitly.  It is available in the only
application, `IsWeakLogSol.exists_psi_harmonic_replacement`, where `h = v - z` with `v` continuous
on `U` and `z ∈ W₀^{1,2}`. -/
def IsLocSqIntegrableOn (U : Set (Euc d)) (h : Euc d → ℝ) : Prop :=
  ∀ (y : Euc d) (t : ℝ), Metric.closedBall y t ⊆ U →
    IntegrableOn (fun z => h z ^ 2) (Metric.closedBall y t) volume



/-- A function continuous on `U` is locally square integrable there. -/
theorem isLocSqIntegrableOn_of_continuousOn {U : Set (Euc d)} {h : Euc d → ℝ}
    (hh : ContinuousOn h U) : IsLocSqIntegrableOn U h := by
  intro y t ht
  exact ((hh.mono ht).pow 2).integrableOn_compact (isCompact_closedBall y t)

/-- Subtracting a global `L²` function preserves local square integrability. -/
theorem isLocSqIntegrableOn_sub_memLp {U : Set (Euc d)} {v z : Euc d → ℝ}
    (hv : IsLocSqIntegrableOn U v) (hvm : AEStronglyMeasurable v volume)
    (hz2 : MemLp z 2 volume) : IsLocSqIntegrableOn U (fun y => v y - z y) := by
  intro y t ht
  have hz : IntegrableOn (fun x => z x ^ 2) (Metric.closedBall y t) volume := by
    have h0 : Integrable (fun x => ‖z x‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hz2.aestronglyMeasurable).1 hz2
    refine h0.integrableOn.congr_fun (fun x _ => ?_) measurableSet_closedBall
    show ‖z x‖ ^ 2 = z x ^ 2
    rw [Real.norm_eq_abs, sq_abs]
  have hbound : IntegrableOn (fun x => 2 * v x ^ 2 + 2 * z x ^ 2)
      (Metric.closedBall y t) volume := ((hv y t ht).const_mul 2).add (hz.const_mul 2)
  refine Integrable.mono' hbound
    (((hvm.sub hz2.aestronglyMeasurable).restrict).pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (v x + z x), sq_nonneg (v x - z x)]

/-! ### The mean minimizes the `L²` deviation (measurable version) -/

/-- **The mean minimizes the `L²` deviation**, for a merely square integrable field.  (The
project's `Komlos.Literature.integral_norm_sub_setAverage_sq_le_const` assumes continuity.) -/
theorem integral_norm_sub_setAverage_sq_le_const' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : Euc d → E} {A : Set (Euc d)}
    (hA : MeasurableSet A) (hfin : volume A ≠ ⊤) (hf : IntegrableOn f A volume)
    (hsq : IntegrableOn (fun y => ‖f y‖ ^ 2) A volume) (c : E) :
    (∫ y in A, ‖f y - ⨍ z in A, f z‖ ^ 2) ≤ ∫ y in A, ‖f y - c‖ ^ 2 := by
  set m : E := ⨍ z in A, f z with hmdef
  have hV : volume.real A = (volume A).toReal := rfl
  have hint0 : (∫ y in A, (f y - m)) = 0 := by
    rw [integral_sub hf (integrableOn_const hfin), setIntegral_const, hmdef, setAverage_eq,
      smul_smul]
    by_cases h0 : volume.real A = 0
    · have hA0 : volume A = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (volume A)).1 h0 with h | h
        · exact h
        · exact absurd h hfin
      rw [setIntegral_measure_zero _ (by simp [hA0])]
      simp [h0]
    · rw [mul_inv_cancel₀ h0, one_smul, sub_self]
  have hfm : IntegrableOn (fun y => f y - m) A volume := hf.sub (integrableOn_const hfin)
  have hsqm : IntegrableOn (fun y => ‖f y - m‖ ^ 2) A volume := by
    have h1 := (hsq.const_mul 2).add (integrableOn_const (C := 2 * ‖m‖ ^ 2) hfin)
    refine Integrable.mono h1 (hfm.aestronglyMeasurable.norm.pow 2) ?_
    filter_upwards with y
    simp only [Pi.add_apply]
    have hb : ‖f y - m‖ ≤ ‖f y‖ + ‖m‖ := norm_sub_le _ _
    have h2 : |‖f y - m‖ ^ 2| = ‖f y - m‖ ^ 2 := abs_of_nonneg (by positivity)
    have h3 : (0 : ℝ) ≤ 2 * ‖f y‖ ^ 2 + 2 * ‖m‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h2, abs_of_nonneg h3]
    nlinarith [norm_nonneg (f y), norm_nonneg m, sq_nonneg (‖f y‖ - ‖m‖), norm_nonneg (f y - m)]
  have hcross : IntegrableOn (fun y => (2 : ℝ) * ⟪f y - m, m - c⟫) A volume :=
    (hfm.inner_const (𝕜 := ℝ) (m - c)).const_mul (2 : ℝ)
  have hexp : ∀ y, ‖f y - c‖ ^ 2 = ‖f y - m‖ ^ 2 + 2 * ⟪f y - m, m - c⟫ + ‖m - c‖ ^ 2 := by
    intro y
    have he : f y - c = (f y - m) + (m - c) := by abel
    rw [he, norm_add_sq_real]
  have i1 : IntegrableOn
      (fun y => ‖f y - m‖ ^ 2 + (2 : ℝ) * ⟪f y - m, m - c⟫) A volume := hsqm.add hcross
  have i2 : IntegrableOn (fun _ : Euc d => ‖m - c‖ ^ 2) A volume := integrableOn_const hfin
  have e1 : (∫ y in A, ‖f y - c‖ ^ 2) =
      ∫ y in A, (‖f y - m‖ ^ 2 + (2 : ℝ) * ⟪f y - m, m - c⟫ + ‖m - c‖ ^ 2) :=
    setIntegral_congr_fun hA (fun y _ => hexp y)
  have hzero : (∫ y in A, (2 : ℝ) * ⟪f y - m, m - c⟫) = 0 := by
    have hflip : ∀ y : Euc d, ⟪f y - m, m - c⟫ = ⟪m - c, f y - m⟫ := fun y =>
      real_inner_comm (m - c) (f y - m)
    rw [integral_const_mul, setIntegral_congr_fun hA (fun y _ => hflip y), integral_inner hfm,
      hint0, inner_zero_right, mul_zero]
  rw [e1, integral_add i1 i2, integral_add hsqm hcross, hzero, setIntegral_const, smul_eq_mul,
    add_zero]
  have hnn : 0 ≤ volume.real A * ‖m - c‖ ^ 2 :=
    mul_nonneg measureReal_nonneg (sq_nonneg _)
  linarith



/-! ### The localized potential -/

/-- A function vanishing outside a set on which its square is integrable is in `L²`. -/
theorem memLp_two_of_integrableOn_sq {E : Type*} [NormedAddCommGroup E] {g : Euc d → E}
    (hgm : AEStronglyMeasurable g volume) {K : Set (Euc d)} (h0 : ∀ x, x ∉ K → g x = 0)
    (hg : IntegrableOn (fun x => ‖g x‖ ^ 2) K volume) : MemLp g 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm hgm).2 ?_
  have hsupp : Function.support (fun x => ‖g x‖ ^ 2) ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (by simp [h0 x hxK])
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact hg

/-- A `Ψ`-harmonic gradient field is integrable on every closed ball inside its domain. -/
theorem IsRegHarmonicField.integrableOn' {U : Set (Euc d)} {h : Euc d → ℝ} {H : Euc d → Euc d}
    (hH : IsRegHarmonicField Ψ U h H) {y : Euc d} {t : ℝ} (ht : Metric.closedBall y t ⊆ U) :
    IntegrableOn H (Metric.closedBall y t) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall y t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have h2 : MemLp H 2 (volume.restrict (Metric.closedBall y t)) :=
    (memLp_two_iff_integrable_sq_norm hH.measurable_grad.aestronglyMeasurable).2
      (hH.integrableOn_sq y t ht)
  exact h2.integrable (by norm_num)

/-- A locally square integrable potential is integrable on closed balls inside the domain. -/
theorem IsLocSqIntegrableOn.integrableOn {U : Set (Euc d)} {h : Euc d → ℝ}
    (hL2 : IsLocSqIntegrableOn U h) (hm : Measurable h) {y : Euc d} {t : ℝ}
    (ht : Metric.closedBall y t ⊆ U) : IntegrableOn h (Metric.closedBall y t) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall y t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have hsq : IntegrableOn (fun x => ‖h x‖ ^ 2) (Metric.closedBall y t) volume := by
    refine (hL2 y t ht).congr_fun (fun x _ => ?_) measurableSet_closedBall
    rw [Real.norm_eq_abs, sq_abs]
  have h2 : MemLp h 2 (volume.restrict (Metric.closedBall y t)) :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 hsq
  exact h2.integrable (by norm_num)


set_option maxHeartbeats 1000000 in
/-- **The localized potential.**  Cutting `h` off by a smooth `η` that is `1` on
`closedBall x₀ (3r/5)` and supported in `closedBall x₀ (4r/5)` produces a global `W^{1,2}`
function whose weak gradient coincides with `H` on `ball x₀ (3r/5)`. -/
theorem exists_localized_potential (hΨ : IsRegProfile Ψ) {x₀ : Euc d} {r : ℝ} (hr : 0 < r)
    {h : Euc d → ℝ} {H : Euc d → Euc d} (hH : IsRegHarmonicField Ψ (Metric.ball x₀ r) h H)
    (hL2 : IsLocSqIntegrableOn (Metric.ball x₀ r) h) :
    ∃ (v : Euc d → ℝ) (Gv : Euc d → Euc d), Measurable v ∧ Measurable Gv ∧
      HasWeakGradient v Gv ∧ MemLp v 2 volume ∧ MemLp Gv 2 volume ∧
      ∀ x ∈ Metric.ball x₀ (3 * r / 5), Gv x = H x := by
  obtain ⟨Ccut, hCcut, hcut⟩ := exists_cutoff_const d
  obtain ⟨η, hηC, hηcs, hηsupp, hη0, hη1, hηone, hηgrad⟩ :=
    hcut x₀ (3 * r / 5) (4 * r / 5) (by positivity) (by linarith)
  have hBig : Metric.closedBall x₀ (4 * r / 5) ⊆ Metric.ball x₀ r :=
    Metric.closedBall_subset_ball (by linarith)
  have htsupp : tsupport η ⊆ Metric.ball x₀ r := hηsupp.trans hBig
  have hhint : IntegrableOn h (tsupport η) volume :=
    (hL2.integrableOn hH.measurable hBig).mono_set hηsupp
  have hHint : IntegrableOn H (tsupport η) volume := (hH.integrableOn' hBig).mono_set hηsupp
  have hhsq : IntegrableOn (fun x => h x ^ 2) (tsupport η) volume :=
    (hL2 x₀ (4 * r / 5) hBig).mono_set hηsupp
  have hHsq : IntegrableOn (fun x => ‖H x‖ ^ 2) (tsupport η) volume :=
    (hH.integrableOn_sq x₀ (4 * r / 5) hBig).mono_set hηsupp
  have hB : ∀ x, ‖gradient η x‖ ≤ Ccut / (4 * r / 5 - 3 * r / 5) := hηgrad
  set B : ℝ := Ccut / (4 * r / 5 - 3 * r / 5) with hBdef
  have hB0 : 0 ≤ B := by
    refine div_nonneg hCcut.le (by linarith)
  refine ⟨fun y => η y * h y, fun y => η y • H y + h y • gradient η y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hηC.continuous.measurable.mul hH.measurable
  · exact (hηC.continuous.measurable.smul hH.measurable_grad).add
      (hH.measurable.smul (continuous_gradient' hηC).measurable)
  · exact hH.hasWeakGradientOn.hasWeakGradient_mul_cutoff
      hH.measurable.aestronglyMeasurable hH.measurable_grad.aestronglyMeasurable hηC hηcs
      htsupp hhint hHint
  · refine memLp_two_of_integrableOn_sq
      (hηC.continuous.aestronglyMeasurable.mul hH.measurable.aestronglyMeasurable)
      (K := tsupport η) (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]) ?_
    refine Integrable.mono' hhsq
      ((hηC.continuous.aestronglyMeasurable.mul
        hH.measurable.aestronglyMeasurable).norm.pow 2).restrict ?_
    filter_upwards with x
    have h1 : |η x| ≤ 1 := abs_le.2 ⟨by linarith [hη0 x], hη1 x⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖η x * h x‖ ^ 2 = (|η x| * |h x|) ^ 2 := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (1 * |h x|) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = h x ^ 2 := by rw [one_mul, sq_abs]
  · refine memLp_two_of_integrableOn_sq
      (((hηC.continuous.aestronglyMeasurable.smul hH.measurable_grad.aestronglyMeasurable).add
        (hH.measurable.aestronglyMeasurable.smul
          (continuous_gradient' hηC).aestronglyMeasurable)))
      (K := tsupport η) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx, gradient_eq_zero_of_notMem_tsupport hx]
        simp) ?_
    refine Integrable.mono' ((hHsq.const_mul 2).add ((hhsq.const_mul (2 * B ^ 2))))
      ((((hηC.continuous.aestronglyMeasurable.smul
        hH.measurable_grad.aestronglyMeasurable).add
        (hH.measurable.aestronglyMeasurable.smul
          (continuous_gradient' hηC).aestronglyMeasurable)).norm.pow 2)).restrict ?_
    filter_upwards with x
    have h1 : |η x| ≤ 1 := abs_le.2 ⟨by linarith [hη0 x], hη1 x⟩
    have hnb : ‖η x • H x + h x • gradient η x‖ ≤ ‖H x‖ + B * |h x| := by
      calc ‖η x • H x + h x • gradient η x‖ ≤ ‖η x • H x‖ + ‖h x • gradient η x‖ :=
            norm_add_le _ _
        _ = |η x| * ‖H x‖ + |h x| * ‖gradient η x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ‖H x‖ + |h x| * B :=
            add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _))
        _ = ‖H x‖ + B * |h x| := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
    have h2 : (0 : ℝ) ≤ ‖η x • H x + h x • gradient η x‖ := norm_nonneg _
    nlinarith [norm_nonneg (H x), abs_nonneg (h x), sq_abs (h x),
      sq_nonneg (‖H x‖ - B * |h x|)]
  · intro x hx
    have hη1x : η x = 1 := hηone x (Metric.ball_subset_closedBall hx)
    have hgrad0 : gradient η x = 0 := by
      have hnb : η =ᶠ[𝓝 x] (fun _ : Euc d => (1 : ℝ)) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
        exact hηone y (Metric.ball_subset_closedBall hy)
      have hfd : fderiv ℝ η x = fderiv ℝ (fun _ : Euc d => (1 : ℝ)) x := hnb.fderiv_eq
      simp [gradient, hfd]
    show η x • H x + h x • gradient η x = H x
    rw [hη1x, hgrad0, one_smul, smul_zero, add_zero]

/-! ### Passing an `L²` oscillation bound to the limit -/

/-- `∫⁻ ‖f‖ₑ² = (‖f‖_{L²(μ)})²`, for an arbitrary measure. -/
theorem lintegral_enorm_rpow_two_eq' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] (f : α → E) :
    (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) = eLpNorm f 2 μ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp), ← ENNReal.rpow_mul]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **Passing a uniform `L²` oscillation bound to an `L²` limit.**  If `z n` is within `M` of a
constant `k n` a.e. on `A`, and `z n → w` in `L²`, then the `L²` oscillation of `w` about its
mean on `A` is at most `M² |A|`.  The constants `k n` are allowed to depend on `n`: only the
*mean* of `w` appears in the conclusion, and the mean minimises the `L²` deviation. -/
theorem setIntegral_sq_sub_setAverage_le_of_tendsto {A : Set (Euc d)} (hA : MeasurableSet A)
    (hAfin : volume A ≠ ⊤) {w : Euc d → ℝ} (hw2 : MemLp w 2 volume)
    {z : ℕ → Euc d → ℝ} (hz : ∀ n, AEStronglyMeasurable (z n) volume) {k : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hbd : ∀ n, ∀ᵐ x ∂(volume.restrict A), |z n x - k n| ≤ M)
    (hconv : Tendsto (fun n => ∫⁻ x, ‖z n x - w x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0)) :
    (∫ x in A, (w x - ⨍ y in A, w y) ^ 2) ≤ M ^ 2 * volume.real A := by
  set μ : Measure (Euc d) := volume.restrict A with hμdef
  have hfin : IsFiniteMeasure μ := by
    constructor
    rw [hμdef, Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hAfin
  have hμuniv : μ Set.univ = volume A := by rw [hμdef, Measure.restrict_apply_univ]
  have hwm : AEStronglyMeasurable w μ := hw2.aestronglyMeasurable.restrict
  have hwA2' : IntegrableOn (fun x => ‖w x‖ ^ 2) A volume :=
    ((memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).1 hw2).integrableOn
  have hwA2 : IntegrableOn (fun x => w x ^ 2) A volume := by
    refine hwA2'.congr_fun (fun x _ => ?_) hA
    show ‖w x‖ ^ 2 = w x ^ 2
    rw [Real.norm_eq_abs, sq_abs]
  have hwA : IntegrableOn w A volume := by
    have h2 : MemLp w 2 μ := hw2.restrict A
    exact h2.integrable (by norm_num)
  set m : ℝ := ⨍ y in A, w y with hmdef
  -- the mean minimises the `L²` deviation, in `eLpNorm` form
  have hmin : ∀ cst : ℝ, eLpNorm (fun x => w x - m) 2 μ ≤ eLpNorm (fun x => w x - cst) 2 μ := by
    intro cst
    have hsq : ∀ cst' : ℝ, IntegrableOn (fun x => (w x - cst') ^ 2) A volume := by
      intro cst'
      have h1 : IntegrableOn (fun x => w x ^ 2 - 2 * cst' * w x + cst' ^ 2) A volume :=
        ((hwA2.sub ((hwA.const_mul (2 * cst')))).add (integrableOn_const hAfin))
      refine h1.congr_fun (fun x _ => ?_) hA
      ring
    have hreal : (∫ x in A, (w x - m) ^ 2) ≤ ∫ x in A, (w x - cst) ^ 2 := by
      have h0 := integral_norm_sub_setAverage_sq_le_const' (f := w) hA hAfin hwA hwA2' cst
      have e1 : ∀ y : ℝ, ‖y‖ ^ 2 = y ^ 2 := fun y => by rw [Real.norm_eq_abs, sq_abs]
      simpa only [e1, hmdef] using h0
    have hcv : (∫⁻ x, ‖w x - m‖ₑ ^ (2 : ℝ) ∂μ) ≤ ∫⁻ x, ‖w x - cst‖ₑ ^ (2 : ℝ) ∂μ := by
      have e2 : ∀ (cst' : ℝ), (∫⁻ x, ‖w x - cst'‖ₑ ^ (2 : ℝ) ∂μ) =
          ENNReal.ofReal (∫ x in A, (w x - cst') ^ 2) := by
        intro cst'
        rw [hμdef, ofReal_integral_eq_lintegral_ofReal (hsq cst')
          (Eventually.of_forall fun x => sq_nonneg _)]
        exact lintegral_congr fun x => enorm_rpow_two_real _
      rw [e2, e2]
      exact ENNReal.ofReal_le_ofReal hreal
    rw [lintegral_enorm_rpow_two_eq', lintegral_enorm_rpow_two_eq'] at hcv
    have h3 := ENNReal.rpow_le_rpow hcv (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h3
    norm_num [ENNReal.rpow_one] at h3
    exact h3
  set Λ : ℝ≥0∞ := (volume A) ^ ((2 : ℝ)⁻¹) * ENNReal.ofReal M with hΛdef
  -- the uniform bound coming from the pointwise estimate
  have hN3 : ∀ n, eLpNorm (fun x => z n x - k n) 2 μ ≤ Λ := by
    intro n
    have h0 : ∀ᵐ x ∂μ, ‖z n x - k n‖ ≤ M := by
      filter_upwards [hbd n] with x hx
      rwa [Real.norm_eq_abs]
    have h1 := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) h0
    rw [hμuniv] at h1
    simpa only [hΛdef, ENNReal.toReal_ofNat] using h1
  -- the `L²` distance to the approximations
  set δ : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ‖z n x - w x‖ₑ ^ (2 : ℝ) with hδdef
  have hN4 : ∀ n, eLpNorm (fun x => w x - z n x) 2 μ ≤ (δ n) ^ ((2 : ℝ)⁻¹) := by
    intro n
    have h0 : (∫⁻ x, ‖w x - z n x‖ₑ ^ (2 : ℝ) ∂μ) ≤ δ n := by
      refine le_trans (lintegral_mono_set (Set.subset_univ A)) ?_
      rw [Measure.restrict_univ]
      refine le_of_eq (lintegral_congr fun x => ?_)
      rw [show w x - z n x = -(z n x - w x) by ring, enorm_neg]
    rw [lintegral_enorm_rpow_two_eq'] at h0
    have h3 := ENNReal.rpow_le_rpow h0 (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (2 : ℝ)⁻¹ = 1 by norm_num, ENNReal.rpow_one] at h3
    exact h3
  -- the triangle inequality
  have hchain : ∀ n, eLpNorm (fun x => w x - m) 2 μ ≤ (δ n) ^ ((2 : ℝ)⁻¹) + Λ := by
    intro n
    refine (hmin (k n)).trans ?_
    refine (eLpNorm_two_le_add_two (f := fun x => w x - k n)
      (f₁ := fun x => w x - z n x) (f₂ := fun x => z n x - k n) (fun x => by ring)
      (hwm.sub (hz n).restrict) (((hz n).restrict).sub aestronglyMeasurable_const)).trans ?_
    exact add_le_add (hN4 n) (hN3 n)
  -- pass to the limit
  have hlim : Tendsto (fun n => (δ n) ^ ((2 : ℝ)⁻¹) + Λ) atTop (𝓝 Λ) := by
    have h0 : Tendsto (fun n => (δ n) ^ ((2 : ℝ)⁻¹)) atTop (𝓝 0) := by
      have h1 := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto (0 : ℝ≥0∞) |>.comp
        hconv
      simp only [Function.comp_def,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)] at h1
      exact h1
    simpa using h0.add tendsto_const_nhds
  have hN : eLpNorm (fun x => w x - m) 2 μ ≤ Λ :=
    ge_of_tendsto hlim (Eventually.of_forall hchain)
  -- conclude
  have hΛ2 : Λ ^ (2 : ℝ) = ENNReal.ofReal (M ^ 2 * volume.real A) := by
    have e1 : ((volume A) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = volume A := by
      rw [← ENNReal.rpow_mul]
      norm_num
    have hMr : (M : ℝ) ^ (2 : ℝ) = M ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast M 2]
      norm_num
    have e2 : (ENNReal.ofReal M) ^ (2 : ℝ) = ENNReal.ofReal (M ^ 2) := by
      rw [← hMr, ENNReal.ofReal_rpow_of_nonneg hM (by norm_num)]
    rw [hΛdef, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e1, e2,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ M ^ 2),
      show volume.real A = (volume A).toReal from rfl, ENNReal.ofReal_toReal hAfin, mul_comm]
  have hfinal : (∫⁻ x in A, ‖w x - m‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (M ^ 2 * volume.real A) := by
    rw [← hΛ2, ← hμdef, lintegral_enorm_rpow_two_eq']
    exact ENNReal.rpow_le_rpow hN (by norm_num)
  exact setIntegral_sq_le_of_lintegral_le (by positivity) hfinal



/-! ### The component excess bound -/

set_option maxHeartbeats 2000000 in
/-- **The `L²` excess of one component of `H` decays at the rate `(ρ/r)^{d+2β}`.**

Route: on `ball x₀ (r/2)` the difference quotient `Δ_s^e v` of the localized potential solves a
linear uniformly elliptic equation with no right-hand side (`isLinearSol_diffQuot`), its `L²`
norm on `ball x₀ (2r/5)` is at most the excess `E` *uniformly in `s`*
(`setIntegral_sq_diffQuot_sub_le`), so De Giorgi–Nash bounds it in `L^∞` on `ball x₀ (r/5)` and
makes its oscillation on `ball x₀ ρ` decay like `(20ρ/r)^α`, again uniformly in `s`.  Letting
`s → 0` (`tendsto_lintegral_diffQuot_sub`) transfers the bound to `⟪H, e⟫`. -/
theorem exists_reg_component_excess (hd : 0 < d) (hΨ : IsRegProfile Ψ) :
    ∃ Kc β : ℝ, 0 ≤ Kc ∧ 0 < β ∧ β < 1 ∧
      ∀ (x₀ : Euc d) (r : ℝ), 0 < r → ∀ (h : Euc d → ℝ) (H : Euc d → Euc d),
        IsRegHarmonicField Ψ (Metric.ball x₀ r) h H → IsLocSqIntegrableOn (Metric.ball x₀ r) h →
        ∀ e : Euc d, ‖e‖ = 1 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 20 →
          (∫ x in Metric.closedBall x₀ ρ,
              (⟪H x, e⟫ - ⨍ y in Metric.closedBall x₀ ρ, ⟪H y, e⟫) ^ 2) ≤
            Kc * (ρ / r) ^ ((d : ℝ) + 2 * β) * Komlos.Literature.sqExcess H x₀ (r / 2) := by
  obtain ⟨c, C, hP⟩ := hΨ.exists_isRegProfileWith
  obtain ⟨C₁, hC₁, hsup⟩ := exists_essSup_bound hd hP.c_pos hP.C_nonneg
  obtain ⟨α, hα, C₀, hC₀, hosc⟩ := exists_osc_decay hd hP.c_pos hP.C_nonneg
  set β : ℝ := min α (1 / 2) with hβdef
  have hβ0 : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hβα : 2 * β ≤ 2 * α := by
    have := min_le_left α (1 / 2 : ℝ)
    linarith
  refine ⟨C₀ ^ 2 * C₁ ^ 2 * (20 : ℝ) ^ (2 * α) * (5 / 2 : ℝ) ^ d, β, by positivity, hβ0, hβ1, ?_⟩
  intro x₀ r hr h H hH hL2 e he ρ hρ hρr
  obtain ⟨v, Gv, hvm, hGvm, hvG, hv2, hGv2, hGvH⟩ := exists_localized_potential hΨ hr hH hL2
  set q : Euc d := ⨍ y in Metric.closedBall x₀ (r / 2), H y with hqdef
  set E : ℝ := Komlos.Literature.sqExcess H x₀ (r / 2) with hEdef
  have hE0 : 0 ≤ E := Komlos.Literature.sqExcess_nonneg _ _ _
  set kk : ℝ := ⟪q, e⟫ with hkkdef
  set vol1 : ℝ := volume.real (Metric.closedBall (0 : Euc d) 1) with hvol1def
  have hvol1 : 0 < vol1 := Komlos.Literature.volume_real_closedBall_pos
  -- the geometry
  have hsub35 : Metric.closedBall x₀ (r / 2) ⊆ Metric.ball x₀ (3 * r / 5) :=
    Metric.closedBall_subset_ball (by linarith)
  have hsubρ35 : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ (3 * r / 5) :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hsub35
  have hV2 : volume.real (Metric.ball x₀ (2 * r / 5)) = (2 * r / 5) ^ d * vol1 := by
    have h0 : volume.real (Metric.ball x₀ (2 * r / 5)) =
        volume.real (Metric.closedBall x₀ (2 * r / 5)) := by
      unfold Measure.real
      rw [measure_congr (ball_ae_eq_closedBall x₀ (by positivity))]
    rw [h0, hvol1def]
    exact Komlos.Literature.volume_real_closedBall x₀ (by positivity)
  set V₂ : ℝ := volume.real (Metric.ball x₀ (2 * r / 5)) with hV2def
  have hV2pos : 0 < V₂ := by rw [hV2]; positivity
  set Sb : ℝ := Real.sqrt (E / V₂) with hSbdef
  have hSb0 : 0 ≤ Sb := Real.sqrt_nonneg _
  have hSbsq : Sb ^ 2 = E / V₂ := Real.sq_sqrt (by positivity)
  set Lc : ℝ := C₀ * (ρ / (r / 20)) ^ α * (2 * C₁ * Sb) with hLcdef
  have hLc0 : 0 ≤ Lc := by
    refine mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg (by positivity) _)) ?_
    positivity
  -- the step sequence and the difference quotients
  set sn : ℕ → ℝ := fun n => (r / 100) * (1 / ((n : ℝ) + 1)) with hsndef
  have hsn0 : ∀ n, 0 < sn n := fun n => by rw [hsndef]; positivity
  have hsnle : ∀ n, sn n ≤ r / 100 := by
    intro n
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h2 : (0 : ℝ) < r / 100 := by positivity
    calc sn n = (r / 100) * (1 / ((n : ℝ) + 1)) := rfl
      _ ≤ (r / 100) * 1 := mul_le_mul_of_nonneg_left h1 h2.le
      _ = r / 100 := by ring
  have hsntend : Tendsto sn atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => (r / 100) * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 ((r / 100) * 0)) := h0.const_mul (r / 100)
    simpa [hsndef] using h1
  set z : ℕ → Euc d → ℝ := fun n => diffQuot (sn n) e v with hzdef
  set w : Euc d → ℝ := fun x => ⟪Gv x, e⟫ with hwdef
  have hw2 : MemLp w 2 volume := by
    refine hGv2.mono (hGv2.aestronglyMeasurable.inner aestronglyMeasurable_const) ?_
    filter_upwards with x
    calc ‖w x‖ = |⟪Gv x, e⟫| := Real.norm_eq_abs _
      _ ≤ ‖Gv x‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = ‖Gv x‖ := by rw [he, mul_one]
  have hzm : ∀ n, AEStronglyMeasurable (z n) volume := fun n =>
    (measurable_diffQuot hvm (sn n) e).aestronglyMeasurable
  have hconv : Tendsto (fun n => ∫⁻ x, ‖z n x - w x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) :=
    tendsto_lintegral_diffQuot_sub hGvm hvG hv2 hGv2 he (fun n => (hsn0 n).ne') hsntend
  -- the linear equation, uniformly in the step
  have hsol : ∀ n, IsLinearSol c C 0 0
      (regDQCoeffLoc Ψ H (sn n) e (Metric.ball x₀ (r / 2 + sn n))) 0 0
      (Metric.ball x₀ (r / 2)) (z n) (diffQuot (sn n) e Gv) := by
    intro n
    refine isLinearSol_diffQuot (ρ := r / 2) (ρ₀ := 3 * r / 5) hP hH hvm hGvm hvG hv2 hGv2
      (hsn0 n) he 0 (by positivity) ?_ (by linarith) ?_
    · have := hsnle n
      linarith
    · intro x hx
      rw [hGvH x hx, sub_zero]
  -- the uniform `L²` bound
  have hL2bd : ∀ n, (∫ x in Metric.ball x₀ (2 * r / 5), (z n x - kk) ^ 2) ≤ E := by
    intro n
    have hAS : ∀ x ∈ Metric.ball x₀ (2 * r / 5), ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        x + (t * sn n) • e ∈ Metric.closedBall x₀ (r / 2) := by
      intro x hx t ht
      have hdx : dist x x₀ < 2 * r / 5 := Metric.mem_ball.1 hx
      have ht0 : (0 : ℝ) < t := ht.1
      have hs0 : (0 : ℝ) < sn n := hsn0 n
      have hd : dist (x + (t * sn n) • e) x ≤ sn n := by
        rw [dist_eq_norm]
        simp only [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        nlinarith [ht.2]
      have htri := dist_triangle (x + (t * sn n) • e) x x₀
      have hs100 := hsnle n
      exact Metric.mem_closedBall.2 (by linarith)
    have hfin : IsFiniteMeasure (volume.restrict (Metric.closedBall x₀ (r / 2))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
    have h2 : MemLp (fun y => Gv y - q) 2 (volume.restrict (Metric.closedBall x₀ (r / 2))) :=
      (hGv2.restrict _).sub (memLp_const q)
    have hint : IntegrableOn (fun y => ‖Gv y - q‖ ^ 2) (Metric.closedBall x₀ (r / 2)) volume :=
      (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).1 h2
    have h0 := setIntegral_sq_diffQuot_sub_le hGvm hvG hv2 hGv2 (hsn0 n).ne' he
      measurableSet_ball measurableSet_closedBall q hAS hint
    refine h0.trans (le_of_eq ?_)
    rw [hEdef, Komlos.Literature.sqExcess_eq]
    refine setIntegral_congr_fun measurableSet_closedBall fun y hy => ?_
    rw [hGvH y (hsub35 hy)]
  -- the De Giorgi sup bound, uniformly in the step
  have hmaxsq : ∀ a : ℝ, max a 0 ^ 2 ≤ a ^ 2 := by
    intro a
    rcases le_total 0 a with ha | ha
    · rw [max_eq_left ha]
    · rw [max_eq_right ha]
      simpa using sq_nonneg a
  have hball25 : Metric.closedBall x₀ (2 * r / 5) ⊆ Metric.ball x₀ (r / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hR25 : (0 : ℝ) < 2 * r / 5 := by positivity
  have hsupbd : ∀ n, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (r / 5))),
      |z n x - kk| ≤ C₁ * Sb := by
    intro n
    have hfin : IsFiniteMeasure (volume.restrict (Metric.ball x₀ (2 * r / 5))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have h2 : MemLp (fun y => z n y - kk) 2 (volume.restrict (Metric.ball x₀ (2 * r / 5))) :=
      (((memLp_diffQuot hv2 (sn n) e)).restrict _).sub (memLp_const kk)
    have hsq : IntegrableOn (fun y => (z n y - kk) ^ 2) (Metric.ball x₀ (2 * r / 5)) volume := by
      have h3 : IntegrableOn (fun x => ‖z n x - kk‖ ^ 2) (Metric.ball x₀ (2 * r / 5)) volume :=
        (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).1 h2
      refine h3.congr_fun (fun y _ => ?_) measurableSet_ball
      show ‖z n y - kk‖ ^ 2 = (z n y - kk) ^ 2
      rw [Real.norm_eq_abs, sq_abs]
    have havg : ∀ g : Euc d → ℝ,
        AEStronglyMeasurable g (volume.restrict (Metric.ball x₀ (2 * r / 5))) →
        (∀ y, g y ^ 2 ≤ (z n y - kk) ^ 2) →
        Real.sqrt (⨍ y in Metric.ball x₀ (2 * r / 5), g y ^ 2) ≤ Sb := by
      intro g hgm hgle
      refine Real.sqrt_le_sqrt ?_
      have hgsq : IntegrableOn (fun y => g y ^ 2) (Metric.ball x₀ (2 * r / 5)) volume := by
        refine Integrable.mono' hsq (hgm.pow 2) ?_
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hgle y
      have hmono : (∫ y in Metric.ball x₀ (2 * r / 5), g y ^ 2) ≤
          ∫ y in Metric.ball x₀ (2 * r / 5), (z n y - kk) ^ 2 :=
        setIntegral_mono_on hgsq hsq measurableSet_ball fun y _ => hgle y
      rw [setAverage_eq, smul_eq_mul, ← hV2def]
      calc V₂⁻¹ * (∫ y in Metric.ball x₀ (2 * r / 5), g y ^ 2)
          ≤ V₂⁻¹ * E :=
            mul_le_mul_of_nonneg_left (hmono.trans (hL2bd n)) (inv_nonneg.2 hV2pos.le)
        _ = E / V₂ := by rw [inv_mul_eq_div]
    have hrr : 2 * r / 5 / 2 = r / 5 := by ring
    have h1 := hsup 0 0 (regDQCoeffLoc Ψ H (sn n) e (Metric.ball x₀ (r / 2 + sn n)))
      0 0 (Metric.ball x₀ (r / 2)) (z n) (diffQuot (sn n) e Gv) le_rfl le_rfl
      (hsol n).isLinearSubsol x₀ (2 * r / 5) hR25 hball25 kk
    rw [hrr] at h1
    have hneg := hsup 0 0 (regDQCoeffLoc Ψ H (sn n) e (Metric.ball x₀ (r / 2 + sn n)))
      (fun x => -(0 : Euc d → Euc d) x) (fun x => -(0 : Euc d → ℝ) x)
      (Metric.ball x₀ (r / 2)) (fun x => -(z n x)) (fun x => -(diffQuot (sn n) e Gv x))
      le_rfl le_rfl (hsol n).neg.isLinearSubsol x₀ (2 * r / 5) hR25 hball25 (-kk)
    rw [hrr] at hneg
    have hzM : Measurable (z n) := measurable_diffQuot hvm (sn n) e
    have hg1 : Real.sqrt (⨍ y in Metric.ball x₀ (2 * r / 5), max (z n y - kk) 0 ^ 2) ≤ Sb := by
      refine havg _ (((hzM.sub measurable_const).max
        measurable_const).aestronglyMeasurable.restrict) fun y => hmaxsq _
    have hg2 : Real.sqrt
        (⨍ y in Metric.ball x₀ (2 * r / 5), max ((fun x => -(z n x)) y - -kk) 0 ^ 2) ≤ Sb := by
      refine havg _ ((((hzM.neg).sub measurable_const).max
        measurable_const).aestronglyMeasurable.restrict) fun y => ?_
      have h0 : ((fun x => -(z n x)) y - -kk) = -(z n y - kk) := by ring
      rw [h0]
      calc max (-(z n y - kk)) 0 ^ 2 ≤ (-(z n y - kk)) ^ 2 := hmaxsq _
        _ = (z n y - kk) ^ 2 := by ring
    filter_upwards [h1, hneg] with x hx hxn
    have e1 : z n x - kk ≤ C₁ * Sb := by
      have := hx
      simp only [zero_mul, add_zero] at this
      nlinarith [hC₁, hg1, Real.sqrt_nonneg
        (⨍ y in Metric.ball x₀ (2 * r / 5), max (z n y - kk) 0 ^ 2)]
    have e2 : -(z n x - kk) ≤ C₁ * Sb := by
      have := hxn
      simp only [zero_mul, add_zero] at this
      nlinarith [hC₁, hg2, Real.sqrt_nonneg
        (⨍ y in Metric.ball x₀ (2 * r / 5), max ((fun x => -(z n x)) y - -kk) 0 ^ 2)]
    exact abs_le.2 ⟨by linarith, e1⟩
  -- the De Giorgi–Nash oscillation decay, uniformly in the step
  have hball3 : Metric.closedBall x₀ (3 * (r / 20)) ⊆ Metric.ball x₀ (r / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hR20 : (0 : ℝ) < r / 20 := by positivity
  have hstep : ∀ n : ℕ, ∃ kn : ℝ,
      ∀ᵐ x ∂(volume.restrict (Metric.closedBall x₀ ρ)), |z n x - kn| ≤ Lc / 2 := by
    intro n
    have hIcc : ∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * (r / 20)) →
        z n x ∈ Set.Icc (kk - C₁ * Sb) ((kk - C₁ * Sb) + 2 * (C₁ * Sb)) := by
      have h0 := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).1 (hsupbd n)
      filter_upwards [h0] with x hx hxb
      have hxb' : x ∈ Metric.ball x₀ (r / 5) := by
        refine Metric.mem_ball.2 ?_
        have := Metric.mem_closedBall.1 hxb
        linarith
      have h1 := hx hxb'
      rw [abs_le] at h1
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    obtain ⟨m', hm'⟩ := hosc 0 0 (regDQCoeffLoc Ψ H (sn n) e (Metric.ball x₀ (r / 2 + sn n)))
      0 0 (Metric.ball x₀ (r / 2)) (z n) (diffQuot (sn n) e Gv) le_rfl le_rfl (hsol n)
      x₀ (r / 20) hR20 hball3 (kk - C₁ * Sb) (2 * (C₁ * Sb)) (by positivity) hIcc ρ hρ hρr
    refine ⟨m' + Lc / 2, ?_⟩
    have hset : volume.restrict (Metric.closedBall x₀ ρ) = volume.restrict (Metric.ball x₀ ρ) :=
      (Measure.restrict_congr_set (ball_ae_eq_closedBall x₀ hρ.ne')).symm
    rw [hset, ae_restrict_iff' Metric.isOpen_ball.measurableSet]
    filter_upwards [hm'] with x hx hxb
    have h1 := hx hxb
    have hupper : z n x ≤ m' + Lc := by
      refine le_trans h1.2 ?_
      have : C₀ * (ρ / (r / 20)) ^ α *
          (2 * (C₁ * Sb) + (0 * (r / 20) + 0 * (3 * (r / 20)) * (r / 20))) = Lc := by
        rw [hLcdef]; ring
      rw [this]
    have hlower : m' ≤ z n x := h1.1
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  choose kn hkn using hstep
  -- pass to the limit
  have hlim := setIntegral_sq_sub_setAverage_le_of_tendsto measurableSet_closedBall
    measure_closedBall_lt_top.ne hw2 hzm (M := Lc / 2) (by positivity) hkn hconv
  have hwH : ∀ x ∈ Metric.closedBall x₀ ρ, w x = ⟪H x, e⟫ := by
    intro x hx
    show ⟪Gv x, e⟫ = ⟪H x, e⟫
    rw [hGvH x (hsubρ35 hx)]
  have havgH : (⨍ y in Metric.closedBall x₀ ρ, ⟪H y, e⟫) = ⨍ y in Metric.closedBall x₀ ρ, w y :=
    setAverage_congr_fun measurableSet_closedBall
      (Eventually.of_forall fun y hy => (hwH y hy).symm)
  have he1 : (∫ x in Metric.closedBall x₀ ρ,
        (⟪H x, e⟫ - ⨍ y in Metric.closedBall x₀ ρ, ⟪H y, e⟫) ^ 2) =
      ∫ x in Metric.closedBall x₀ ρ, (w x - ⨍ y in Metric.closedBall x₀ ρ, w y) ^ 2 := by
    rw [havgH]
    exact setIntegral_congr_fun measurableSet_closedBall fun x hx => by rw [hwH x hx]
  rw [he1]
  refine hlim.trans ?_
  -- the arithmetic
  have hX : (0 : ℝ) < ρ / r := by positivity
  have hX1 : ρ / r ≤ 1 := by
    rw [div_le_one hr]
    linarith
  have hvolρ : volume.real (Metric.closedBall x₀ ρ) = ρ ^ d * vol1 :=
    Komlos.Literature.volume_real_closedBall x₀ hρ.le
  have hLchalf : Lc / 2 = C₀ * (20 * (ρ / r)) ^ α * (C₁ * Sb) := by
    rw [hLcdef]
    have h20 : ρ / (r / 20) = 20 * (ρ / r) := by
      field_simp
    rw [h20]
    ring
  have hpow2 : ∀ y : ℝ, 0 ≤ y → (y ^ α) ^ 2 = y ^ (2 * α) := by
    intro y hy
    rw [← Real.rpow_natCast (y ^ α) 2, ← Real.rpow_mul hy]
    congr 1
    push_cast
    ring
  have hsq : (Lc / 2) ^ 2 =
      C₀ ^ 2 * C₁ ^ 2 * ((20 : ℝ) ^ (2 * α) * (ρ / r) ^ (2 * α)) * Sb ^ 2 := by
    rw [hLchalf, Real.mul_rpow (by norm_num) hX.le]
    have hexp : (C₀ * ((20 : ℝ) ^ α * (ρ / r) ^ α) * (C₁ * Sb)) ^ 2 =
        C₀ ^ 2 * C₁ ^ 2 * (((20 : ℝ) ^ α) ^ 2 * ((ρ / r) ^ α) ^ 2) * Sb ^ 2 := by ring
    rw [hexp, hpow2 20 (by norm_num), hpow2 (ρ / r) hX.le]
  have hfrac : Sb ^ 2 * (ρ ^ d * vol1) = E * ((5 / 2 : ℝ) ^ d * (ρ / r) ^ d) := by
    rw [hSbsq, hV2]
    have h1 : ((5 : ℝ) / 2) ^ d * (ρ / r) ^ d = ρ ^ d / (2 * r / 5) ^ d := by
      rw [← mul_pow, ← div_pow]
      congr 1
      field_simp
      try ring
    rw [h1]
    field_simp
  rw [hvolρ, hsq]
  have hmono2 : (ρ / r) ^ (2 * α) ≤ (ρ / r) ^ (2 * β) :=
    Real.rpow_le_rpow_of_exponent_ge hX hX1 hβα
  have hnn : (0 : ℝ) ≤ C₀ ^ 2 * C₁ ^ 2 * (20 : ℝ) ^ (2 * α) := by positivity
  have hcomb : (ρ / r) ^ (2 * β) * (ρ / r) ^ d = (ρ / r) ^ ((d : ℝ) + 2 * β) := by
    rw [← Real.rpow_natCast (ρ / r) d, ← Real.rpow_add hX]
    congr 1
    ring
  calc C₀ ^ 2 * C₁ ^ 2 * ((20 : ℝ) ^ (2 * α) * (ρ / r) ^ (2 * α)) * Sb ^ 2 * (ρ ^ d * vol1)
      = C₀ ^ 2 * C₁ ^ 2 * (20 : ℝ) ^ (2 * α) * (ρ / r) ^ (2 * α) *
          (Sb ^ 2 * (ρ ^ d * vol1)) := by ring
    _ = C₀ ^ 2 * C₁ ^ 2 * (20 : ℝ) ^ (2 * α) * (ρ / r) ^ (2 * α) *
          (E * ((5 / 2 : ℝ) ^ d * (ρ / r) ^ d)) := by rw [hfrac]
    _ ≤ C₀ ^ 2 * C₁ ^ 2 * (20 : ℝ) ^ (2 * α) * (ρ / r) ^ (2 * β) *
          (E * ((5 / 2 : ℝ) ^ d * (ρ / r) ^ d)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono2 hnn) ?_
        positivity
    _ = C₀ ^ 2 * C₁ ^ 2 * (20 : ℝ) ^ (2 * α) * (5 / 2 : ℝ) ^ d *
          ((ρ / r) ^ (2 * β) * (ρ / r) ^ d) * E := by ring
    _ = C₀ ^ 2 * C₁ ^ 2 * (20 : ℝ) ^ (2 * α) * (5 / 2 : ℝ) ^ d *
          (ρ / r) ^ ((d : ℝ) + 2 * β) * E := by rw [hcomb]

/-- **The interior Campanato decay of a `Ψ`-harmonic gradient field.**  See the module
docstring for the route. -/
-- TODO(reg/c2h): steps 1–4 of the module docstring (difference-quotient linearization,
-- uniform-in-`s` De Giorgi–Nash oscillation decay, `L²` passage to the limit `s → 0`).
theorem exists_reg_excess_decay (hΨ : IsRegProfile Ψ) :
    ∃ Cdec β : ℝ, 0 ≤ Cdec ∧ 0 < β ∧ β < 1 ∧
      ∀ (x₀ : Euc d) (r : ℝ), 0 < r → ∀ (h : Euc d → ℝ) (H : Euc d → Euc d),
        IsRegHarmonicField Ψ (Metric.ball x₀ r) h H →
        IsLocSqIntegrableOn (Metric.ball x₀ r) h →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 2 →
          Komlos.Literature.sqExcess H x₀ ρ ≤
            Cdec * (2 * ρ / r) ^ ((d : ℝ) + 2 * β) * Komlos.Literature.sqExcess H x₀ (r / 2) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- the zero-dimensional case: every field is a.e. constant, so the excess vanishes
    subst hd0
    refine ⟨1, 1 / 2, zero_le_one, by norm_num, by norm_num, ?_⟩
    intro x₀ r hr h H hH hL2 ρ hρ hρr
    have hsubρ : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r :=
      Metric.closedBall_subset_ball (by linarith)
    have h1 := integral_norm_sub_setAverage_sq_le_const' (f := H) measurableSet_closedBall
      measure_closedBall_lt_top.ne (hH.integrableOn' hsubρ) (hH.integrableOn_sq x₀ ρ hsubρ)
      (H x₀)
    have h2 : (∫ y in Metric.closedBall x₀ ρ, ‖H y - H x₀‖ ^ 2) = 0 := by
      have hz : ∀ y : Euc 0, ‖H y - H x₀‖ ^ 2 = 0 := by
        intro y
        rw [Subsingleton.elim y x₀]
        simp
      simp [hz]
    have h3 : Komlos.Literature.sqExcess H x₀ ρ ≤ 0 := by
      rw [Komlos.Literature.sqExcess_eq]
      exact h1.trans (le_of_eq h2)
    have h4 : (0 : ℝ) ≤ 1 * (2 * ρ / r) ^ ((0 : ℕ) + 2 * (1 / 2 : ℝ)) *
        Komlos.Literature.sqExcess H x₀ (r / 2) := by
      have : (0 : ℝ) ≤ (2 * ρ / r) ^ (((0 : ℕ) : ℝ) + 2 * (1 / 2 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have h5 := Komlos.Literature.sqExcess_nonneg H x₀ (r / 2)
      positivity
    exact h3.trans h4
  obtain ⟨Kc, β, hKc, hβ0, hβ1, hcomp⟩ := exists_reg_component_excess hd hΨ
  refine ⟨max ((d : ℝ) * Kc) ((10 : ℝ) ^ ((d : ℝ) + 2)), β, ?_, hβ0, hβ1, ?_⟩
  · exact le_trans (by positivity) (le_max_right _ _)
  intro x₀ r hr h H hH hL2 ρ hρ hρr
  set E : ℝ := Komlos.Literature.sqExcess H x₀ (r / 2) with hEdef
  have hE0 : 0 ≤ E := Komlos.Literature.sqExcess_nonneg _ _ _
  have hsubρ : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r :=
    Metric.closedBall_subset_ball (by linarith)
  have hsub2 : Metric.closedBall x₀ (r / 2) ⊆ Metric.ball x₀ r :=
    Metric.closedBall_subset_ball (by linarith)
  have hexp0 : (0 : ℝ) ≤ (d : ℝ) + 2 * β := by positivity
  by_cases hsmall : ρ ≤ r / 20
  · -- the main range: sum the component bounds over an orthonormal basis
    set b : OrthonormalBasis (Fin d) ℝ (Euc d) := EuclideanSpace.basisFun (Fin d) ℝ with hbdef
    set m : Euc d := ⨍ y in Metric.closedBall x₀ ρ, H y with hmdef
    have hHint : IntegrableOn H (Metric.closedBall x₀ ρ) volume := hH.integrableOn' hsubρ
    have havg : ∀ e : Euc d, (⨍ y in Metric.closedBall x₀ ρ, ⟪H y, e⟫) = ⟪m, e⟫ := by
      intro e
      rw [hmdef, setAverage_eq, setAverage_eq, smul_eq_mul, real_inner_smul_left]
      congr 1
      rw [real_inner_comm, ← integral_inner hHint]
      exact integral_congr_ae (Eventually.of_forall fun y => real_inner_comm _ _)
    have hparseval : ∀ x : Euc d, ‖x - m‖ ^ 2 = ∑ i : Fin d, (⟪x, b i⟫ - ⟪m, b i⟫) ^ 2 := by
      intro x
      have h0 := b.sum_inner_mul_inner (x - m) (x - m)
      rw [real_inner_self_eq_norm_sq] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_sub_left, real_inner_comm (x - m) (b i), inner_sub_left, sq]
    have hintcomp : ∀ i : Fin d,
        IntegrableOn (fun x => (⟪H x, b i⟫ - ⟪m, b i⟫) ^ 2) (Metric.closedBall x₀ ρ) volume := by
      intro i
      have hfin : IsFiniteMeasure (volume.restrict (Metric.closedBall x₀ ρ)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
      have h2 : MemLp (fun x => ⟪H x, b i⟫ - ⟪m, b i⟫) 2
          (volume.restrict (Metric.closedBall x₀ ρ)) := by
        refine MemLp.sub ?_ (memLp_const _)
        have hH2 : MemLp H 2 (volume.restrict (Metric.closedBall x₀ ρ)) :=
          (memLp_two_iff_integrable_sq_norm hH.measurable_grad.aestronglyMeasurable).2
            (hH.integrableOn_sq x₀ ρ hsubρ)
        refine hH2.mono (hH2.aestronglyMeasurable.inner aestronglyMeasurable_const) ?_
        filter_upwards with x
        calc ‖⟪H x, b i⟫‖ ≤ ‖H x‖ * ‖b i‖ := abs_real_inner_le_norm _ _
          _ = ‖H x‖ := by rw [b.orthonormal.1 i, mul_one]
      have h3 : IntegrableOn (fun x => ‖⟪H x, b i⟫ - ⟪m, b i⟫‖ ^ 2)
          (Metric.closedBall x₀ ρ) volume :=
        (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).1 h2
      refine h3.congr_fun (fun x _ => ?_) measurableSet_closedBall
      show ‖⟪H x, b i⟫ - ⟪m, b i⟫‖ ^ 2 = (⟪H x, b i⟫ - ⟪m, b i⟫) ^ 2
      rw [Real.norm_eq_abs, sq_abs]
    have hsplit : Komlos.Literature.sqExcess H x₀ ρ =
        ∑ i : Fin d, ∫ x in Metric.closedBall x₀ ρ, (⟪H x, b i⟫ - ⟪m, b i⟫) ^ 2 := by
      rw [Komlos.Literature.sqExcess_eq, ← hmdef,
        setIntegral_congr_fun measurableSet_closedBall (fun x _ => hparseval (H x))]
      exact integral_finsetSum _ (fun i _ => hintcomp i)
    have hbound : ∀ i : Fin d,
        (∫ x in Metric.closedBall x₀ ρ, (⟪H x, b i⟫ - ⟪m, b i⟫) ^ 2) ≤
          Kc * (ρ / r) ^ ((d : ℝ) + 2 * β) * E := by
      intro i
      have hbi : ‖b i‖ = 1 := b.orthonormal.1 i
      have h0 := hcomp x₀ r hr h H hH hL2 (b i) hbi ρ hρ hsmall
      rw [havg (b i)] at h0
      exact h0
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbound i)
    rw [hsplit]
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmono : (ρ / r) ^ ((d : ℝ) + 2 * β) ≤ (2 * ρ / r) ^ ((d : ℝ) + 2 * β) := by
      refine Real.rpow_le_rpow (by positivity) ?_ hexp0
      rw [div_le_div_iff_of_pos_right hr]
      linarith
    have hnn : (0 : ℝ) ≤ (d : ℝ) * Kc := by positivity
    calc (d : ℝ) * (Kc * (ρ / r) ^ ((d : ℝ) + 2 * β) * E)
        = (d : ℝ) * Kc * (ρ / r) ^ ((d : ℝ) + 2 * β) * E := by ring
      _ ≤ (d : ℝ) * Kc * (2 * ρ / r) ^ ((d : ℝ) + 2 * β) * E := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hnn) hE0
      _ ≤ max ((d : ℝ) * Kc) ((10 : ℝ) ^ ((d : ℝ) + 2)) *
            (2 * ρ / r) ^ ((d : ℝ) + 2 * β) * E := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_) hE0
          exact Real.rpow_nonneg (by positivity) _
  · -- the trivial range
    push Not at hsmall
    have hmonoE : Komlos.Literature.sqExcess H x₀ ρ ≤ E := by
      have h1 := integral_norm_sub_setAverage_sq_le_const' (f := H) measurableSet_closedBall
        measure_closedBall_lt_top.ne (hH.integrableOn' hsubρ) (hH.integrableOn_sq x₀ ρ hsubρ)
        (⨍ y in Metric.closedBall x₀ (r / 2), H y)
      rw [Komlos.Literature.sqExcess_eq]
      refine h1.trans ?_
      have hfin : IsFiniteMeasure (volume.restrict (Metric.closedBall x₀ (r / 2))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
      have h2 : MemLp (fun y => H y - ⨍ y in Metric.closedBall x₀ (r / 2), H y) 2
          (volume.restrict (Metric.closedBall x₀ (r / 2))) :=
        ((memLp_two_iff_integrable_sq_norm hH.measurable_grad.aestronglyMeasurable).2
          (hH.integrableOn_sq x₀ (r / 2) hsub2)).sub (memLp_const _)
      have hint2 : IntegrableOn
          (fun y => ‖H y - ⨍ y in Metric.closedBall x₀ (r / 2), H y‖ ^ 2)
          (Metric.closedBall x₀ (r / 2)) volume :=
        (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).1 h2
      exact setIntegral_mono_set hint2 (Eventually.of_forall fun y => sq_nonneg _)
        (Eventually.of_forall (Metric.closedBall_subset_closedBall hρr))
    refine hmonoE.trans ?_
    have hfac : (1 : ℝ) ≤ max ((d : ℝ) * Kc) ((10 : ℝ) ^ ((d : ℝ) + 2)) *
        (2 * ρ / r) ^ ((d : ℝ) + 2 * β) := by
      have h1 : ((10 : ℝ))⁻¹ ≤ 2 * ρ / r := by
        rw [le_div_iff₀ hr]
        linarith
      have h2 : ((10 : ℝ))⁻¹ ^ ((d : ℝ) + 2) ≤ ((10 : ℝ))⁻¹ ^ ((d : ℝ) + 2 * β) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      have h3 : ((10 : ℝ))⁻¹ ^ ((d : ℝ) + 2 * β) ≤ (2 * ρ / r) ^ ((d : ℝ) + 2 * β) :=
        Real.rpow_le_rpow (by norm_num) h1 hexp0
      have h4 : (10 : ℝ) ^ ((d : ℝ) + 2) * ((10 : ℝ))⁻¹ ^ ((d : ℝ) + 2) = 1 := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)]
        norm_num
      calc (1 : ℝ) = (10 : ℝ) ^ ((d : ℝ) + 2) * ((10 : ℝ))⁻¹ ^ ((d : ℝ) + 2) := h4.symm
        _ ≤ (10 : ℝ) ^ ((d : ℝ) + 2) * (2 * ρ / r) ^ ((d : ℝ) + 2 * β) := by
            refine mul_le_mul_of_nonneg_left (h2.trans h3) ?_
            exact Real.rpow_nonneg (by norm_num) _
        _ ≤ max ((d : ℝ) * Kc) ((10 : ℝ) ^ ((d : ℝ) + 2)) *
              (2 * ρ / r) ^ ((d : ℝ) + 2 * β) := by
            refine mul_le_mul_of_nonneg_right (le_max_right _ _) ?_
            exact Real.rpow_nonneg (by positivity) _
    nlinarith [hE0, hfac]

end Komlos.Literature.Regularized
