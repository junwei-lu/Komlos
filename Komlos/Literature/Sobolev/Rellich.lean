import Komlos.Literature.Sobolev.Defs

/-!
# Rellich–Kondrachov compactness for `W₀^{1,p}(K)`

A sequence in `W₀^{1,p}(K)`, `K` bounded, that is bounded in the graph norm has a subsequence
converging in `L^p` (`rellich`). This is the compactness input of the direct method giving a first
eigenfunction of the anisotropic `p`-Laplacian (paper Appendix A: "The direct method gives a
nonnegative, nonzero first eigenfunction `u_i ∈ W_0^{1,p}(K_i)`"). The proof is the
Fréchet–Kolmogorov argument:

* `lintegral_enorm_sub_translate_rpow_le` — for `C¹` `f`, `∫ |f(x − t) − f(x)|^p ≤ ‖t‖^p ∫ ‖∇f‖^p`
  (fundamental theorem of calculus on segments, Hölder on `[0, 1]`, Tonelli);
* `eLpNorm_sub_translate_le` — the same bound `‖u(· − t) − u‖_p ≤ ‖t‖ ‖g‖_p` for `u ∈ L^p` with
  weak gradient `g ∈ L^p`, by mollification;
* `eLpNorm_mollifyWith_sub_le` — **the Fréchet–Kolmogorov bound** `‖ρ ⋆ u − u‖_p ≤ ε ‖g‖_p` for a
  continuous probability density `ρ` supported in `closedBall 0 ε` (Jensen, Tonelli and the
  translation estimate);
* `enorm_mollifyWith_le`, `enorm_mollifyWith_sub_le` — mollifications of an `L¹`-bounded family are
  uniformly bounded and uniformly Lipschitz;
* `totallyBounded_range_toLp` — such a family, supported in a fixed ball, is totally bounded in
  `L^p`: mollify at a small scale (error `ε C`), apply Arzelà–Ascoli
  (`BoundedContinuousFunction.arzela_ascoli`) to the mollified family on a compact ball, and turn
  uniform closeness on the ball into `L^p` closeness;
* `rellich` — total boundedness in the complete space `Lp` yields a convergent subsequence.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal NNReal Pointwise ContDiff Convolution BoundedContinuousFunction

namespace Komlos.Literature

variable {d : ℕ} {p : ℝ}

/-! ### `L^p` bookkeeping -/

/-- `∫ ‖f‖^p = ‖f‖_{L^p}^p` at the level of lower integrals (`p > 0`). -/
theorem lintegral_enorm_rpow_eq_eLpNorm_rpow {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (hp0 : 0 < p) (f : α → E) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
    ENNReal.rpow_one]

/-- An `L^q` bound from a sup bound, for a function supported in a set `S`. -/
theorem eLpNorm_le_of_support_subset_of_norm_le {f : Euc d → ℝ} {S : Set (Euc d)}
    (hf : Function.support f ⊆ S) {θ : ℝ} (hθ : ∀ x, ‖f x‖ ≤ θ) (q : ℝ≥0∞) :
    eLpNorm f q ≤ volume S ^ q.toReal⁻¹ * ENNReal.ofReal θ := by
  rw [← eLpNorm_restrict_eq_of_support_subset hf]
  simpa only [Measure.restrict_apply_univ] using
    eLpNorm_le_of_ae_bound (μ := volume.restrict S) (p := q) (Eventually.of_forall hθ)

/-- A uniform `L¹` bound on a set from an `L^p` bound (Hölder). -/
theorem lintegral_enorm_le_of_support_subset (hp : 1 < p) {f : Euc d → ℝ}
    (hf : AEStronglyMeasurable f volume) {S : Set (Euc d)} (hS : MeasurableSet S)
    (hfS : ∀ x, x ∉ S → f x = 0) :
    ∫⁻ x, ‖f x‖ₑ ≤ eLpNorm f (ENNReal.ofReal p) *
      eLpNorm (S.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal (Real.conjExponent p)) := by
  refine le_trans (le_of_eq (lintegral_congr fun x => ?_))
    (lintegral_enorm_mul_enorm_le hp hf (aestronglyMeasurable_const.indicator hS))
  by_cases hx : x ∈ S
  · simp [Set.indicator_of_mem hx]
  · simp [hfS x hx]

/-! ### The translation estimate -/

/-- Fundamental theorem of calculus on a segment: for `C¹` `f`,
`|f (x - t) - f x| ≤ ∫₀¹ ‖∇f (x - s t)‖ ‖t‖ ds`. -/
theorem enorm_sub_translate_le_lintegral {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (x t : Euc d) :
    ‖f (x - t) - f x‖ₑ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ‖gradient f (x - s • t)‖ₑ * ‖t‖ₑ := by
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => f (x - s • t)) (fderiv ℝ f (x - s • t) (-t)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x - s • t) (-t) s := by
      simpa using ((hasDerivAt_id s).smul_const t).const_sub x
    exact (hf.differentiable one_ne_zero (x - s • t)).hasFDerivAt.comp_hasDerivAt s h1
  have hcont : Continuous fun s : ℝ => fderiv ℝ f (x - s • t) (-t) :=
    ((hf.continuous_fderiv one_ne_zero).comp
      (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hftc : ∫ s in (0 : ℝ)..1, fderiv ℝ f (x - s • t) (-t) =
      f (x - (1 : ℝ) • t) - f (x - (0 : ℝ) • t) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hcont.intervalIntegrable 0 1)
  have heq : f (x - t) - f x = ∫ s in Ioc (0 : ℝ) 1, fderiv ℝ f (x - s • t) (-t) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, hftc, one_smul, zero_smul, sub_zero]
  rw [heq]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun s => ?_)
  rw [fderiv_apply_eq_inner_gradient]
  exact (enorm_real_inner_le _ _).trans_eq (by rw [enorm_neg])

/-- Pointwise translation estimate for `C¹` `f`:
`|f (x - t) - f x|^p ≤ ‖t‖^p ∫₀¹ ‖∇f (x - s t)‖^p ds`. -/
theorem enorm_sub_translate_rpow_le {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hp : 1 < p)
    (x t : Euc d) :
    ‖f (x - t) - f x‖ₑ ^ p ≤ ‖t‖ₑ ^ p * ∫⁻ s in Ioc (0 : ℝ) 1, ‖gradient f (x - s • t)‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hm : AEMeasurable (fun s : ℝ => ‖gradient f (x - s • t)‖ₑ) (volume.restrict (Ioc 0 1)) :=
    (continuous_enorm.comp ((continuous_gradient hf).comp
      (continuous_const.sub (continuous_id.smul continuous_const)))).measurable.aemeasurable
  have h1 := enorm_sub_translate_le_lintegral hf x t
  rw [lintegral_mul_const' _ _ enorm_ne_top] at h1
  have h2 := lintegral_Ioc_rpow_le 1 hp hm
  rw [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] at h2
  refine (ENNReal.rpow_le_rpow h1 hp0.le).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, mul_comm]
  exact mul_le_mul' le_rfl h2

/-- **Translation estimate for `C¹` functions**: `∫ |f (x - t) - f x|^p ≤ ‖t‖^p ∫ ‖∇f‖^p`. -/
theorem lintegral_enorm_sub_translate_rpow_le {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hp : 1 < p)
    (t : Euc d) :
    ∫⁻ x, ‖f (x - t) - f x‖ₑ ^ p ≤ ‖t‖ₑ ^ p * ∫⁻ x, ‖gradient f x‖ₑ ^ p := by
  have hG : Measurable fun q : Euc d × ℝ => ‖gradient f (q.1 - q.2 • t)‖ₑ ^ p :=
    (ENNReal.continuous_rpow_const.comp (continuous_enorm.comp ((continuous_gradient hf).comp
      (continuous_fst.sub (continuous_snd.smul continuous_const))))).measurable
  calc ∫⁻ x, ‖f (x - t) - f x‖ₑ ^ p
      ≤ ∫⁻ x, ‖t‖ₑ ^ p * ∫⁻ s in Ioc (0 : ℝ) 1, ‖gradient f (x - s • t)‖ₑ ^ p :=
        lintegral_mono fun x => enorm_sub_translate_rpow_le hf hp x t
    _ = ‖t‖ₑ ^ p * ∫⁻ x, ∫⁻ s in Ioc (0 : ℝ) 1, ‖gradient f (x - s • t)‖ₑ ^ p :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) enorm_ne_top)
    _ = ‖t‖ₑ ^ p * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x, ‖gradient f (x - s • t)‖ₑ ^ p := by
        rw [lintegral_lintegral_swap hG.aemeasurable]
    _ = ‖t‖ₑ ^ p * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x, ‖gradient f x‖ₑ ^ p := by
        congr 1
        exact lintegral_congr fun s =>
          lintegral_sub_right_eq_self (fun x => ‖gradient f x‖ₑ ^ p) (s • t)
    _ = ‖t‖ₑ ^ p * ∫⁻ x, ‖gradient f x‖ₑ ^ p := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **Translation estimate on `W^{1,p}`**: if `u ∈ L^p` has weak gradient `g ∈ L^p` (`1 < p`),
then `‖u (· - t) - u‖_{L^p} ≤ ‖t‖ ‖g‖_{L^p}`. -/
theorem eLpNorm_sub_translate_le (hp : 1 < p) {u : Euc d → ℝ} {g : Euc d → Euc d}
    (hug : HasWeakGradient u g) (hu : MemLp u (ENNReal.ofReal p))
    (hg : MemLp g (ENNReal.ofReal p)) (t : Euc d) :
    eLpNorm (fun x => u (x - t) - u x) (ENNReal.ofReal p) ≤
      ‖t‖ₑ * eLpNorm g (ENNReal.ofReal p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  set φ : ℕ → ContDiffBump (0 : Euc d) := fun n => mollifierBump n with hφ_def
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set v : ℕ → Euc d → ℝ := fun n => mollifyWith ((φ n).normed volume) u with hv_def
  have hv_smooth : ∀ n, ContDiff ℝ 1 (v n) := fun n =>
    contDiff_mollifyWith (φ n).contDiff_normed (φ n).hasCompactSupport_normed hug.locallyIntegrable
  have hvp : ∀ n, MemLp (v n) (ENNReal.ofReal p) := fun n => memLp_mollifyWith_normed hp hu (φ n)
  have hGp : ∀ n, eLpNorm (gradient (v n)) (ENNReal.ofReal p) ≤ eLpNorm g (ENNReal.ofReal p) :=
    fun n => by
      rw [gradient_mollifyWith hug (φ n).contDiff_normed (φ n).hasCompactSupport_normed]
      exact eLpNorm_mollifyWith_le hg.1 (φ n).continuous_normed (φ n).nonneg_normed
        (φ n).integrable_normed (φ n).integral_normed hp
  have hsmooth : ∀ n, eLpNorm (fun x => v n (x - t) - v n x) (ENNReal.ofReal p) ≤
      ‖t‖ₑ * eLpNorm g (ENNReal.ofReal p) := fun n =>
    (eLpNorm_le_of_lintegral_rpow_le' hp0
      (lintegral_enorm_sub_translate_rpow_le (hv_smooth n) hp t)).trans
      (mul_le_mul' le_rfl (hGp n))
  have hlim : Tendsto (fun n => eLpNorm (v n - u) (ENNReal.ofReal p)) atTop (𝓝 0) :=
    tendsto_eLpNorm_mollifyWith_sub hφ hp hu
  have htri : ∀ n, eLpNorm (fun x => u (x - t) - u x) (ENNReal.ofReal p) ≤
      eLpNorm (v n - u) (ENNReal.ofReal p) +
        (‖t‖ₑ * eLpNorm g (ENNReal.ofReal p) + eLpNorm (v n - u) (ENNReal.ofReal p)) := by
    intro n
    have e : (fun x => u (x - t) - u x) =
        (fun x => (u - v n) (x - t)) + ((fun x => v n (x - t) - v n x) + (v n - u)) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have hm1 : AEStronglyMeasurable (fun x => (u - v n) (x - t)) volume :=
      (hu.1.sub (hvp n).1).comp_measurePreserving (measurePreserving_sub_right volume t)
    have hm2 : AEStronglyMeasurable (fun x => v n (x - t) - v n x) volume :=
      (((hv_smooth n).continuous.comp (continuous_id.sub continuous_const)).sub
        (hv_smooth n).continuous).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (v n - u) volume := (hvp n).1.sub hu.1
    have htrans : eLpNorm (fun x => (u - v n) (x - t)) (ENNReal.ofReal p) =
        eLpNorm (v n - u) (ENNReal.ofReal p) := by
      rw [eLpNorm_sub_comm (v n) u]
      exact eLpNorm_comp_measurePreserving (hu.1.sub (hvp n).1)
        (measurePreserving_sub_right volume t)
    rw [e]
    refine (eLpNorm_add_le hm1 (hm2.add hm3) hp1).trans ?_
    rw [htrans]
    exact add_le_add le_rfl ((eLpNorm_add_le hm2 hm3 hp1).trans (add_le_add (hsmooth n) le_rfl))
  have hlim2 : Tendsto (fun n => eLpNorm (v n - u) (ENNReal.ofReal p) +
      (‖t‖ₑ * eLpNorm g (ENNReal.ofReal p) + eLpNorm (v n - u) (ENNReal.ofReal p))) atTop
      (𝓝 (‖t‖ₑ * eLpNorm g (ENNReal.ofReal p))) := by
    simpa only [zero_add, add_zero] using hlim.add (tendsto_const_nhds.add hlim)
  exact ge_of_tendsto' hlim2 htri

/-! ### The Fréchet–Kolmogorov mollification bound -/

/-- **The Fréchet–Kolmogorov mollification bound**: for `u ∈ L^p` with weak gradient `g ∈ L^p`
(`1 < p`) and a continuous probability density `ρ` supported in `closedBall 0 ε`,
`‖ρ ⋆ u − u‖_{L^p} ≤ ε ‖g‖_{L^p}`. -/
theorem eLpNorm_mollifyWith_sub_le (hp : 1 < p) {u : Euc d → ℝ} {g : Euc d → Euc d}
    (hug : HasWeakGradient u g) (hu : MemLp u (ENNReal.ofReal p))
    (hg : MemLp g (ENNReal.ofReal p)) {ρ : Euc d → ℝ} (hρ : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1) {ε : ℝ}
    (hρε : Function.support ρ ⊆ Metric.closedBall 0 ε) :
    eLpNorm (mollifyWith ρ u - u) (ENNReal.ofReal p) ≤
      ENNReal.ofReal ε * eLpNorm g (ENNReal.ofReal p) := by
  have hp0 : 0 < p := by linarith
  have hρi : Integrable ρ := hρ.integrable_of_hasCompactSupport hρs
  have hul : LocallyIntegrable u := hug.locallyIntegrable
  have hρint : ∫⁻ s, ENNReal.ofReal (ρ s) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1,
      ENNReal.ofReal_one]
  -- the pointwise identity `ρ ⋆ u (x) - u x = ∫ ρ s (u (x - s) - u x) ds`
  have hpt : ∀ x, mollifyWith ρ u x - u x = ∫ s, ρ s • (u (x - s) - u x) := by
    intro x
    have h1 : mollifyWith ρ u x = ∫ s, ρ s • u (x - s) := by
      rw [mollifyWith_eq_convolution, convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply]
    have hi1 : Integrable fun s => ρ s • u (x - s) := by
      simpa only [sub_sub_cancel] using
        (integrable_mollifyWith_integrand hρ hρs hul x).comp_sub_left x
    have hi2 : Integrable fun s => ρ s • u x := hρi.smul_const (u x)
    rw [h1]
    simp_rw [smul_sub]
    rw [integral_sub hi1 hi2, integral_smul_const, hρ1, one_smul]
  -- Jensen
  have hjensen : ∀ x, ‖mollifyWith ρ u x - u x‖ₑ ^ p ≤
      ∫⁻ s, ENNReal.ofReal (ρ s) * ‖u (x - s) - u x‖ₑ ^ p := by
    intro x
    rw [hpt x]
    exact enorm_integral_smul_rpow_le_of_prob
      ((hu.1.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).sub
        aestronglyMeasurable_const) hρ.aemeasurable hρ0 hρint hp
  -- joint measurability
  have hmeas : AEMeasurable (Function.uncurry fun x s : Euc d =>
      ENNReal.ofReal (ρ s) * ‖u (x - s) - u x‖ₑ ^ p) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : Euc d × Euc d => u (q.1 - q.2)) (volume.prod volume) :=
      hu.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant
        volume volume)
    have h2 : AEStronglyMeasurable (fun q : Euc d × Euc d => u q.1) (volume.prod volume) :=
      hu.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    exact (ENNReal.measurable_ofReal.comp (hρ.measurable.comp measurable_snd)).aemeasurable.mul
      ((h1.sub h2).enorm.pow_const p)
  -- the translation estimate, inside the support of `ρ`
  have hbound : ∀ s, ENNReal.ofReal (ρ s) * ∫⁻ x, ‖u (x - s) - u x‖ₑ ^ p ≤
      ENNReal.ofReal (ρ s) * (ENNReal.ofReal ε ^ p * ∫⁻ x, ‖g x‖ₑ ^ p) := by
    intro s
    by_cases hs : ρ s = 0
    · simp [hs]
    · have hs' : ‖s‖ ≤ ε := by simpa using hρε hs
      refine mul_le_mul' le_rfl ?_
      rw [lintegral_enorm_rpow_eq_eLpNorm_rpow hp0 (fun x => u (x - s) - u x),
        lintegral_enorm_rpow_eq_eLpNorm_rpow hp0 g, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      refine ENNReal.rpow_le_rpow ((eLpNorm_sub_translate_le hp hug hu hg s).trans
        (mul_le_mul' ?_ le_rfl)) hp0.le
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hs'
  have hmain : ∫⁻ x, ‖(mollifyWith ρ u - u) x‖ₑ ^ p ≤
      ENNReal.ofReal ε ^ p * ∫⁻ x, ‖g x‖ₑ ^ p := by
    calc ∫⁻ x, ‖(mollifyWith ρ u - u) x‖ₑ ^ p
        ≤ ∫⁻ x, ∫⁻ s, ENNReal.ofReal (ρ s) * ‖u (x - s) - u x‖ₑ ^ p :=
          lintegral_mono fun x => hjensen x
      _ = ∫⁻ s, ∫⁻ x, ENNReal.ofReal (ρ s) * ‖u (x - s) - u x‖ₑ ^ p :=
          lintegral_lintegral_swap hmeas
      _ = ∫⁻ s, ENNReal.ofReal (ρ s) * ∫⁻ x, ‖u (x - s) - u x‖ₑ ^ p :=
          lintegral_congr fun s => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ s, ENNReal.ofReal (ρ s) * (ENNReal.ofReal ε ^ p * ∫⁻ x, ‖g x‖ₑ ^ p) :=
          lintegral_mono hbound
      _ = (∫⁻ s, ENNReal.ofReal (ρ s)) * (ENNReal.ofReal ε ^ p * ∫⁻ x, ‖g x‖ₑ ^ p) :=
          lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hρ.measurable)
      _ = ENNReal.ofReal ε ^ p * ∫⁻ x, ‖g x‖ₑ ^ p := by rw [hρint, one_mul]
  exact eLpNorm_le_of_lintegral_rpow_le' hp0 hmain

/-! ### Pointwise bounds for mollifications -/

/-- `‖ρ ⋆ w (x)‖ ≤ sup |ρ| · ∫ |w|`. -/
theorem enorm_mollifyWith_le {ρ : Euc d → ℝ} {M : ℝ} (hM : ∀ y, ‖ρ y‖ ≤ M) (w : Euc d → ℝ)
    (x : Euc d) : ‖mollifyWith ρ w x‖ₑ ≤ ENNReal.ofReal M * ∫⁻ t, ‖w t‖ₑ := by
  show ‖∫ t, ρ (x - t) • w t‖ₑ ≤ _
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun t => ?_
  rw [enorm_smul]
  exact mul_le_mul' (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM _)) le_rfl

/-- `‖ρ ⋆ w (y) - ρ ⋆ w (z)‖ ≤ Lip(ρ) ‖y - z‖ ∫ |w|`. -/
theorem enorm_mollifyWith_sub_le {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hρs : HasCompactSupport ρ)
    {L : ℝ≥0} (hL : LipschitzWith L ρ) {w : Euc d → ℝ} (hw : LocallyIntegrable w) (y z : Euc d) :
    ‖mollifyWith ρ w y - mollifyWith ρ w z‖ₑ ≤
      ENNReal.ofReal (L * dist y z) * ∫⁻ t, ‖w t‖ₑ := by
  have e : mollifyWith ρ w y - mollifyWith ρ w z = ∫ t, (ρ (y - t) - ρ (z - t)) • w t := by
    simp only [mollifyWith, sub_smul]
    exact (integral_sub (integrable_mollifyWith_integrand hρ hρs hw y)
      (integrable_mollifyWith_integrand hρ hρs hw z)).symm
  rw [e]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun t => ?_
  rw [enorm_smul]
  refine mul_le_mul' ?_ le_rfl
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hL.dist_le_mul (y - t) (z - t)
  rwa [dist_sub_right, Real.dist_eq, ← Real.norm_eq_abs] at h

/-! ### Total boundedness in `L^p` -/

/-- **Fréchet–Kolmogorov total boundedness**: a sequence `u n ∈ L^p` (`1 < p`) with weak gradients
`g n`, all supported in a fixed ball and bounded in `L^p` together with their weak gradients, is
totally bounded in `L^p`. -/
theorem totallyBounded_range_toLp (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] {R : ℝ}
    {u : ℕ → Euc d → ℝ} (hu : ∀ n, MemLp (u n) (ENNReal.ofReal p)) {g : ℕ → Euc d → Euc d}
    (hug : ∀ n, HasWeakGradient (u n) (g n)) (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p))
    (hsupp : ∀ n x, x ∉ Metric.closedBall (0 : Euc d) R → u n x = 0) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ n, eLpNorm (u n) (ENNReal.ofReal p) ≤ C ∧ eLpNorm (g n) (ENNReal.ofReal p) ≤ C) :
    TotallyBounded (Set.range fun n => (hu n).toLp (u n)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  obtain ⟨c, hc0, hCc⟩ : ∃ c : ℝ, 0 ≤ c ∧ C = ENNReal.ofReal c :=
    ⟨C.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hC).symm⟩
  -- a uniform `L¹` bound
  obtain ⟨M, hM0, hL1⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ∫⁻ x, ‖u n x‖ₑ ≤ ENNReal.ofReal M := by
    have hItop : eLpNorm ((Metric.closedBall (0 : Euc d) R).indicator fun _ => (1 : ℝ))
        (ENNReal.ofReal (Real.conjExponent p)) ≠ ⊤ :=
      (memLp_indicator_const _ measurableSet_closedBall (1 : ℝ)
        (Or.inr measure_closedBall_lt_top.ne)).eLpNorm_ne_top
    refine ⟨(C * eLpNorm ((Metric.closedBall (0 : Euc d) R).indicator fun _ => (1 : ℝ))
      (ENNReal.ofReal (Real.conjExponent p))).toReal, ENNReal.toReal_nonneg, fun n => ?_⟩
    rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top hC hItop)]
    exact (lintegral_enorm_le_of_support_subset hp (hu n).1 measurableSet_closedBall
      (hsupp n)).trans (mul_le_mul' (hbound n).1 le_rfl)
  rw [Metric.totallyBounded_iff]
  intro η hη
  -- the mollification scale
  obtain ⟨ε, hε0, hεc⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * c ≤ η / 4 := by
    have hc1 : c + 1 ≠ 0 := (by linarith : (0 : ℝ) < c + 1).ne'
    refine ⟨η / (4 * (c + 1)), div_pos hη (by linarith), ?_⟩
    calc η / (4 * (c + 1)) * c ≤ η / (4 * (c + 1)) * (c + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_pos hη (by linarith)).le
      _ = η / 4 := by field_simp
  let φb : ContDiffBump (0 : Euc d) := ⟨ε / 2, ε, half_pos hε0, by linarith⟩
  have hρc : Continuous (φb.normed volume) := φb.continuous_normed
  have hρs : HasCompactSupport (φb.normed volume) := φb.hasCompactSupport_normed
  obtain ⟨Lρ, hLρ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hρs
    (φb.contDiff_normed (n := ⊤)) (by simp)
  obtain ⟨Mρ, hMρ⟩ := hρc.bounded_above_of_compact_support hρs
  have hMρ0 : 0 ≤ Mρ := (norm_nonneg _).trans (hMρ 0)
  set v : ℕ → Euc d → ℝ := fun n => mollifyWith (φb.normed volume) (u n) with hv
  have hvc : ∀ n, Continuous (v n) := fun n =>
    continuous_mollifyWith hρc hρs ((hu n).locallyIntegrable hp1)
  -- (1) the mollification error
  have hmoll : ∀ n, eLpNorm (v n - u n) (ENNReal.ofReal p) ≤ ENNReal.ofReal (ε * c) := by
    intro n
    refine (eLpNorm_mollifyWith_sub_le (ε := ε) hp (hug n) (hu n) (hg n) hρc hρs φb.nonneg_normed
      φb.integral_normed ?_).trans ?_
    · rw [φb.support_normed_eq]
      exact Metric.ball_subset_closedBall
    · rw [ENNReal.ofReal_mul hε0.le, ← hCc]
      exact mul_le_mul' le_rfl (hbound n).2
  -- (2) the mollified functions live on a fixed ball
  have hvsupp : ∀ n, Function.support (v n) ⊆ Metric.closedBall 0 (R + ε) := by
    intro n x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := support_mollifyWith_subset _ _ hx
    rw [φb.support_normed_eq] at ha
    have ha' : ‖a‖ < ε := by simpa using ha
    have hb' : ‖b‖ ≤ R := by
      by_contra h
      exact hb (hsupp n b (by simpa using h))
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le _ _).trans (by linarith)
  -- (3) uniform bounds and a uniform Lipschitz constant
  have hvbd : ∀ n x, ‖v n x‖ ≤ Mρ * M := by
    intro n x
    have h := (enorm_mollifyWith_le hMρ (u n) x).trans (mul_le_mul' le_rfl (hL1 n))
    rw [← ENNReal.ofReal_mul hMρ0, ← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hMρ0 hM0)).1 h
  have hvlip : ∀ n (y z : Euc d), dist (v n y) (v n z) ≤ (Lρ * M) * dist y z := by
    intro n y z
    have h := (enorm_mollifyWith_sub_le hρc hρs hLρ ((hu n).locallyIntegrable hp1) y z).trans
      (mul_le_mul' le_rfl (hL1 n))
    rw [← ofReal_norm] at h
    have h2 : ENNReal.ofReal ‖v n y - v n z‖ ≤ ENNReal.ofReal (Lρ * dist y z * M) :=
      h.trans (le_of_eq (ENNReal.ofReal_mul (mul_nonneg Lρ.2 dist_nonneg)).symm)
    rw [dist_eq_norm, mul_right_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg Lρ.2 dist_nonneg) hM0)).1 h2
  -- (4) Arzelà–Ascoli on the compact ball
  have : CompactSpace (Metric.closedBall (0 : Euc d) (R + ε)) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall 0 (R + ε))
  let w : ℕ → (Metric.closedBall (0 : Euc d) (R + ε) →ᵇ ℝ) := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => v n x, (hvc n).comp continuous_subtype_val⟩
  have hw : ∀ n x, w n x = v n x := fun n x => rfl
  have hA : IsCompact (closure (Set.range w)) := by
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) (Mρ * M))
      (isCompact_closedBall _ _) _ ?_ ?_
    · rintro _ x ⟨n, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, hw]
      exact hvbd n x
    · refine (LipschitzWith.uniformEquicontinuous _ ⟨Lρ * M, mul_nonneg Lρ.2 hM0⟩
        ?_).equicontinuous
      rintro ⟨_, n, rfl⟩
      exact LipschitzWith.of_dist_le_mul fun y z => hvlip n y z
  -- (5) a finite net
  obtain ⟨V, hV0, hVeq⟩ : ∃ V : ℝ, 0 ≤ V ∧ volume (Metric.closedBall (0 : Euc d) (R + ε)) ^
      (ENNReal.ofReal p).toReal⁻¹ = ENNReal.ofReal V :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg
      (inv_nonneg.2 ENNReal.toReal_nonneg) measure_closedBall_lt_top.ne)).symm⟩
  obtain ⟨θ, hθ0, hθV⟩ : ∃ θ : ℝ, 0 < θ ∧ V * θ ≤ η / 4 := by
    have hV1 : V + 1 ≠ 0 := (by linarith : (0 : ℝ) < V + 1).ne'
    refine ⟨η / (4 * (V + 1)), div_pos hη (by linarith), ?_⟩
    calc V * (η / (4 * (V + 1))) ≤ (V + 1) * (η / (4 * (V + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_pos hη (by linarith)).le
      _ = η / 4 := by field_simp
  obtain ⟨t, htA, htfin, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded (hA.totallyBounded.subset subset_closure) θ hθ0
  have hidx : ∀ y ∈ t, ∃ n, w n = y := fun y hy => htA hy
  choose! idx hidx using hidx
  refine ⟨(fun y => (hu (idx y)).toLp (u (idx y))) '' t, htfin.image _, ?_⟩
  rintro _ ⟨m, rfl⟩
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (hcover ⟨m, rfl⟩)
  refine Set.mem_iUnion₂.2 ⟨_, ⟨y, hyt, rfl⟩, ?_⟩
  have hwy : dist (w m) (w (idx y)) < θ := by
    rw [hidx y hyt]
    exact Metric.mem_ball.1 hy
  have hclose : ∀ x, ‖v m x - v (idx y) x‖ ≤ θ := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Euc d) (R + ε)
    · have h1 := BoundedContinuousFunction.dist_coe_le_dist (f := w m) (g := w (idx y)) ⟨x, hx⟩
      rw [hw, hw, dist_eq_norm] at h1
      exact h1.trans hwy.le
    · rw [Function.notMem_support.1 fun h => hx (hvsupp m h),
        Function.notMem_support.1 fun h => hx (hvsupp (idx y) h), sub_zero, norm_zero]
      exact hθ0.le
  have hvv : eLpNorm (v m - v (idx y)) (ENNReal.ofReal p) ≤ ENNReal.ofReal (V * θ) := by
    refine (eLpNorm_le_of_support_subset_of_norm_le
      ((Function.support_sub _ _).trans (union_subset (hvsupp m) (hvsupp (idx y)))) hclose
      _).trans (le_of_eq ?_)
    rw [hVeq, ← ENNReal.ofReal_mul hV0]
  have hvm : ∀ n, AEStronglyMeasurable (v n) volume := fun n => (hvc n).aestronglyMeasurable
  have htri : eLpNorm (u m - u (idx y)) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (ε * c) + (ENNReal.ofReal (V * θ) + ENNReal.ofReal (ε * c)) := by
    have e : u m - u (idx y) = (u m - v m) + ((v m - v (idx y)) + (v (idx y) - u (idx y))) := by
      abel
    rw [e]
    refine (eLpNorm_add_le ((hu m).1.sub (hvm m))
      (((hvm m).sub (hvm (idx y))).add ((hvm (idx y)).sub (hu (idx y)).1)) hp1).trans
      (add_le_add ?_ ((eLpNorm_add_le ((hvm m).sub (hvm (idx y)))
        ((hvm (idx y)).sub (hu (idx y)).1) hp1).trans (add_le_add hvv (hmoll (idx y)))))
    rw [eLpNorm_sub_comm]
    exact hmoll m
  have hεc0 : 0 ≤ ε * c := mul_nonneg hε0.le hc0
  have hVθ0 : 0 ≤ V * θ := mul_nonneg hV0 hθ0.le
  rw [Metric.mem_ball, dist_edist, Lp.edist_toLp_toLp]
  refine (ENNReal.toReal_le_of_le_ofReal (add_nonneg hεc0 (add_nonneg hVθ0 hεc0))
    (htri.trans (le_of_eq ?_))).trans_lt (by linarith)
  rw [ENNReal.ofReal_add hεc0 (add_nonneg hVθ0 hεc0), ENNReal.ofReal_add hVθ0 hεc0]

/-! ### Rellich–Kondrachov -/

/-- **Rellich–Kondrachov**: a sequence in `W₀^{1,p}(K)`, `K` bounded, bounded in the graph norm,
has a subsequence converging in `L^p` (the compactness step of the direct method, paper
Appendix A: "The direct method gives a nonnegative, nonzero first eigenfunction"). -/
theorem rellich (hp : 1 < p) {K : Set (Euc d)} (hK : Bornology.IsBounded K)
    (u : ℕ → Euc d → ℝ) (hu : ∀ n, MemW0 p K (u n)) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ n, eLpNorm (u n) (ENNReal.ofReal p) ≤ C ∧ gradLpNorm p (u n) ≤ C) :
    ∃ f : Euc d → ℝ, MemLp f (ENNReal.ofReal p) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => eLpNorm (u (φ k) - f) (ENNReal.ofReal p)) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨hp1⟩
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : Euc d)
  -- representatives vanishing everywhere outside the ball
  set u' : ℕ → Euc d → ℝ := fun n => (Metric.closedBall (0 : Euc d) R).indicator (u n)
    with hu'_def
  have hae : ∀ n, u n =ᵐ[volume] u' n := fun n => by
    filter_upwards [(hu n).ae_eq_zero] with x hx
    by_cases hxR : x ∈ Metric.closedBall (0 : Euc d) R
    · exact (Set.indicator_of_mem hxR (u n)).symm
    · rw [show u' n x = 0 from Set.indicator_of_notMem hxR (u n)]
      exact hx fun hxK => hxR (hR hxK)
  have hu'p : ∀ n, MemLp (u' n) (ENNReal.ofReal p) := fun n => (hu n).memLp.ae_eq (hae n)
  have hu'g : ∀ n, HasWeakGradient (u' n) (weakGrad (u n)) := fun n =>
    (hu n).hasWeakGradient.congr_left (hae n)
  have hsupp : ∀ n x, x ∉ Metric.closedBall (0 : Euc d) R → u' n x = 0 := fun n x hx =>
    Set.indicator_of_notMem hx (u n)
  have hbound' : ∀ n, eLpNorm (u' n) (ENNReal.ofReal p) ≤ C ∧
      eLpNorm (weakGrad (u n)) (ENNReal.ofReal p) ≤ C := fun n =>
    ⟨(eLpNorm_congr_ae (hae n)).symm.le.trans (hbound n).1, (hbound n).2⟩
  have htb := totallyBounded_range_toLp hp hu'p hu'g (fun n => (hu n).memLp_weakGrad) hsupp hC
    hbound'
  obtain ⟨F, -, φ, hφ, hlim⟩ := (htb.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨F, Lp.memLp F, φ, hφ, ?_⟩
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun k => (hu'p (φ k)).toLp (u' (φ k))) F).1 hlim
  refine h.congr fun k => eLpNorm_congr_ae ?_
  filter_upwards [(hu'p (φ k)).coeFn_toLp, hae (φ k)] with x hx hx'
  simp only [Pi.sub_apply, hx, hx']

end Komlos.Literature
