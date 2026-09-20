import Komlos.Literature.Regularized.InteriorHarmonicHolderSeg

/-!
# The linearized difference-quotient equation (lane `L3h`)

For a `Ψ`-harmonic gradient field `H` (`div ∇Ψ(H) = 0` weakly), the difference quotient
`Δ_s^e H` satisfies a *linear* divergence-form equation, because

`∇Ψ(H (x + s e)) - ∇Ψ(H x) = A_s(x) (H (x + s e) - H x)`,
`A_s(x) = ∫₀¹ D(∇Ψ)(H x + t (H (x + s e) - H x)) dt`

(the secant of `∇Ψ`, `regSecant`).  The coefficients `A_s` are bounded and uniformly elliptic
with the ellipticity constants of `Ψ` (`isUnifElliptic_regDQCoeff`), *uniformly in `s`*, which is
exactly the input the De Giorgi–Nash lane consumes.

This file proves the secant identities and, in `regHarmonic_weakEq_diffQuot`, the weak form of
the differentiated equation against smooth test functions.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

set_option linter.unusedSectionVars false

variable {d : ℕ} {Ψ : Euc d → ℝ} {c C : ℝ}

/-! ### The secant of `∇Ψ` -/

/-- `regSecant Ψ a b = ∫₀¹ D(∇Ψ)(a + t (b - a)) dt`, the secant operator of `∇Ψ` between `a`
and `b`: it satisfies `∇Ψ b - ∇Ψ a = regSecant Ψ a b (b - a)` and inherits the ellipticity
bounds of `D(∇Ψ)`. -/
noncomputable def regSecant (Ψ : Euc d → ℝ) (a b : Euc d) : Euc d →L[ℝ] Euc d :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (a + t • (b - a))

section Secant

variable (hΨ : IsRegProfile Ψ)

/-- The integrand of `regSecant` is continuous. -/
theorem continuous_fderiv_gradient_line (hΨ : IsRegProfile Ψ) (a b : Euc d) :
    Continuous fun t : ℝ => fderiv ℝ (gradient Ψ) (a + t • (b - a)) :=
  (hΨ.contDiff_gradient.continuous_fderiv (by simp)).comp
    (continuous_const.add (continuous_id.smul continuous_const))

/-- `regSecant` applied to a vector is the integral of the applied derivatives. -/
theorem regSecant_apply (hΨ : IsRegProfile Ψ) (a b ξ : Euc d) :
    regSecant Ψ a b ξ = ∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (a + t • (b - a)) ξ :=
  ContinuousLinearMap.intervalIntegral_apply
    ((continuous_fderiv_gradient_line hΨ a b).intervalIntegrable 0 1) ξ

/-- **The secant identity**: `∇Ψ b - ∇Ψ a = regSecant Ψ a b (b - a)`. -/
theorem regSecant_apply_sub (hΨ : IsRegProfile Ψ) (a b : Euc d) :
    regSecant Ψ a b (b - a) = gradient Ψ b - gradient Ψ a := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => gradient Ψ (a + t • (b - a)))
      (fderiv ℝ (gradient Ψ) (a + t • (b - a)) (b - a)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => a + t • (b - a)) (b - a) t := by
      have h0 : HasDerivAt (fun t : ℝ => t • (b - a)) (b - a) t := by
        simpa using (hasDerivAt_id t).smul_const (b - a)
      simpa using h0.const_add a
    exact (hΨ.differentiable_gradient (a + t • (b - a))).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous fun t : ℝ => fderiv ℝ (gradient Ψ) (a + t • (b - a)) (b - a) :=
    (continuous_fderiv_gradient_line hΨ a b).clm_apply continuous_const
  have hftc : ∫ t in (0 : ℝ)..1, fderiv ℝ (gradient Ψ) (a + t • (b - a)) (b - a) =
      gradient Ψ (a + (1 : ℝ) • (b - a)) - gradient Ψ (a + (0 : ℝ) • (b - a)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 1)
  rw [regSecant_apply hΨ, hftc]
  simp

/-- The quadratic form of `regSecant` is the integral of the quadratic forms. -/
theorem inner_regSecant (hΨ : IsRegProfile Ψ) (a b ξ : Euc d) :
    ⟪regSecant Ψ a b ξ, ξ⟫ =
      ∫ t in (0 : ℝ)..1, ⟪fderiv ℝ (gradient Ψ) (a + t • (b - a)) ξ, ξ⟫ := by
  rw [regSecant_apply hΨ, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  have hint : IntegrableOn (fun t : ℝ => fderiv ℝ (gradient Ψ) (a + t • (b - a)) ξ)
      (Ioc (0 : ℝ) 1) volume :=
    (((continuous_fderiv_gradient_line hΨ a b).clm_apply
      continuous_const).intervalIntegrable 0 1).1
  rw [real_inner_comm, ← integral_inner hint]
  exact integral_congr_ae (Eventually.of_forall fun t => real_inner_comm _ _)

/-- **Ellipticity of the secant**: `c ‖ξ‖² ≤ ⟪regSecant Ψ a b ξ, ξ⟫`. -/
theorem regSecant_elliptic (hP : IsRegProfileWith Ψ c C) (a b ξ : Euc d) :
    c * ‖ξ‖ ^ 2 ≤ ⟪regSecant Ψ a b ξ, ξ⟫ := by
  rw [inner_regSecant hP.toIsRegProfile, intervalIntegral.integral_of_le zero_le_one]
  have hint : IntegrableOn
      (fun t : ℝ => ⟪fderiv ℝ (gradient Ψ) (a + t • (b - a)) ξ, ξ⟫) (Ioc (0 : ℝ) 1) volume := by
    refine (Continuous.integrableOn_Ioc ?_)
    exact ((continuous_fderiv_gradient_line hP.toIsRegProfile a b).clm_apply
      continuous_const).inner continuous_const
  have hmono := setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne) hint
    measurableSet_Ioc (fun t _ => hP.lower (a + t • (b - a)) ξ)
  rw [setIntegral_const, smul_eq_mul] at hmono
  have hv : volume.real (Ioc (0 : ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Ioc]
  rwa [hv, one_mul] at hmono

/-- **The secant is bounded by the upper ellipticity constant**: `‖regSecant Ψ a b‖ ≤ C`. -/
theorem norm_regSecant_le (hP : IsRegProfileWith Ψ c C) (a b : Euc d) :
    ‖regSecant Ψ a b‖ ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C)
    (f := fun t : ℝ => fderiv ℝ (gradient Ψ) (a + t • (b - a)))
    (fun t _ => hP.norm_fderiv_gradient_le (a + t • (b - a)))
  simpa [regSecant] using h

end Secant

/-! ### The coefficients of the difference-quotient equation -/

/-- `regDQCoeff Ψ H s e x = regSecant Ψ (H x) (H (x + s e))`, the coefficient field of the
equation satisfied by `Δ_s^e H`. -/
noncomputable def regDQCoeff (Ψ : Euc d → ℝ) (H : Euc d → Euc d) (s : ℝ) (e : Euc d)
    (x : Euc d) : Euc d →L[ℝ] Euc d :=
  regSecant Ψ (H x) (H (x + s • e))

/-- **The coefficients of the difference-quotient equation are uniformly elliptic**, with the
ellipticity constants of the profile — uniformly in the step `s`. -/
theorem isUnifElliptic_regDQCoeff (hP : IsRegProfileWith Ψ c C) (H : Euc d → Euc d) (s : ℝ)
    (e : Euc d) (Ω : Set (Euc d)) : IsUnifElliptic c C Ω (regDQCoeff Ψ H s e) where
  elliptic := Eventually.of_forall fun x _ ξ => regSecant_elliptic hP _ _ ξ
  bddCoeff := Eventually.of_forall fun x _ => norm_regSecant_le hP _ _

/-- The coefficients turn the difference quotient of `H` into the difference quotient of the
flux `∇Ψ ∘ H`. -/
theorem regDQCoeff_apply_diffQuot (hΨ : IsRegProfile Ψ) (H : Euc d → Euc d) {s : ℝ} (hs : s ≠ 0)
    (e : Euc d) (x : Euc d) :
    regDQCoeff Ψ H s e x (diffQuot s e H x) = diffQuot s e (fun y => gradient Ψ (H y)) x := by
  rw [regDQCoeff, diffQuot_apply, diffQuot_apply, map_smul, regSecant_apply_sub hΨ]

/-! ### The weak form of the differentiated equation -/

section WeakEq

/-- The gradient of a smooth compactly supported function has compact support. -/
theorem hasCompactSupport_gradient' {ψ : Euc d → ℝ} (hψs : HasCompactSupport ψ) :
    HasCompactSupport (gradient ψ) :=
  HasCompactSupport.intro hψs (fun x hx => gradient_eq_zero_of_notMem_tsupport hx)

/-- The gradient of a smooth function is continuous. -/
theorem continuous_gradient' {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) : Continuous (gradient ψ) := by
  have h1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
    (h1.continuous_fderiv one_ne_zero)

/-- `⟪Φ, ∇ψ⟫` is integrable when `Φ` is integrable on a compact set containing the support of
`ψ` and vanishing is enforced outside it by `∇ψ`. -/
theorem integrable_inner_gradient {Φ : Euc d → Euc d} (hΦm : AEStronglyMeasurable Φ volume)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    {K : Set (Euc d)} (hK : MeasurableSet K) (hKs : tsupport ψ ⊆ K)
    (hΦ : IntegrableOn Φ K volume) :
    Integrable (fun x => ⟪Φ x, gradient ψ x⟫) volume := by
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_of_hasCompactSupport (continuous_gradient' hψ) (hasCompactSupport_gradient' hψs)
  have hzero : ∀ x, x ∉ K → ⟪Φ x, gradient ψ x⟫ = 0 := by
    intro x hx
    rw [gradient_eq_zero_of_notMem_tsupport (fun hc => hx (hKs hc)), inner_zero_right]
  have hsupp : Function.support (fun x => ⟪Φ x, gradient ψ x⟫) ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (hzero x hxK)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  refine Integrable.mono' (hΦ.norm.const_mul M) ?_ ?_
  · exact (hΦm.inner (continuous_gradient' hψ).aestronglyMeasurable).restrict
  · filter_upwards with x
    refine (Real.norm_eq_abs _).le.trans ?_
    calc |⟪Φ x, gradient ψ x⟫| ≤ ‖Φ x‖ * ‖gradient ψ x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖Φ x‖ * M := mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
      _ = M * ‖Φ x‖ := by ring

/-- The flux `∇Ψ ∘ H` is integrable on every closed ball inside the domain. -/
theorem IsRegHarmonicField.integrableOn_flux (hP : IsRegProfileWith Ψ c C) {U : Set (Euc d)}
    {h : Euc d → ℝ} {H : Euc d → Euc d} (hH : IsRegHarmonicField Ψ U h H) {y : Euc d} {t : ℝ}
    (ht : Metric.closedBall y t ⊆ U) :
    IntegrableOn (fun x => gradient Ψ (H x)) (Metric.closedBall y t) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall y t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have h2 : MemLp H 2 (volume.restrict (Metric.closedBall y t)) :=
    (memLp_two_iff_integrable_sq_norm hH.measurable_grad.aestronglyMeasurable).2
      (hH.integrableOn_sq y t ht)
  have hHint : IntegrableOn H (Metric.closedBall y t) volume := h2.integrable (by norm_num)
  refine Integrable.mono' (hHint.norm.const_mul C) ?_ ?_
  · exact ((hP.toIsRegProfile.contDiff_gradient.continuous.comp_aestronglyMeasurable
      hH.measurable_grad.aestronglyMeasurable)).restrict
  · filter_upwards with x
    exact (hP.norm_gradient_le (H x)).trans (le_of_eq (by ring))

set_option maxHeartbeats 1000000 in
/-- **The differentiated equation in weak form.**  If `H` is a `Ψ`-harmonic gradient field on `U`
and both `closedBall y₀ t₀` (containing the support of `ψ`) and its `s e`-translate lie in `U`,
then

`∫ ⟪Δ_s^e (∇Ψ ∘ H), ∇ψ⟫ = 0`.

Together with `regDQCoeff_apply_diffQuot` this is the weak equation for `Δ_s^e H` with the
uniformly elliptic coefficients `regDQCoeff Ψ H s e`. -/
theorem regHarmonic_weakEq_diffQuot (hP : IsRegProfileWith Ψ c C) {U : Set (Euc d)}
    {h : Euc d → ℝ} {H : Euc d → Euc d} (hH : IsRegHarmonicField Ψ U h H) (s : ℝ) (e : Euc d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    {y₀ : Euc d} {t₀ : ℝ} (hBU : Metric.closedBall y₀ t₀ ⊆ U)
    (hBU' : Metric.closedBall (y₀ + s • e) t₀ ⊆ U)
    (hψB : tsupport ψ ⊆ Metric.closedBall y₀ t₀) :
    (∫ x, ⟪diffQuot s e (fun y => gradient Ψ (H y)) x, gradient ψ x⟫) = 0 := by
  set F : Euc d → Euc d := fun y => gradient Ψ (H y) with hFdef
  have hFm : AEStronglyMeasurable F volume :=
    hP.toIsRegProfile.contDiff_gradient.continuous.comp_aestronglyMeasurable
      hH.measurable_grad.aestronglyMeasurable
  set w : Euc d := s • e with hwdef
  -- the translated test function
  set ψ' : Euc d → ℝ := fun y => ψ (y - w) with hψ'def
  have hψ'C : ContDiff ℝ ∞ ψ' := hψ.comp (contDiff_id.sub contDiff_const)
  have hψ's : HasCompactSupport ψ' := hψs.comp_homeomorph (Homeomorph.subRight w)
  have hψ'supp : tsupport ψ' ⊆ (fun y => y - w) ⁻¹' (tsupport ψ) := by
    refine closure_minimal ?_ (IsClosed.preimage (continuous_id.sub continuous_const)
      (isClosed_tsupport ψ))
    intro y hy
    exact subset_tsupport ψ hy
  have hψ'B : tsupport ψ' ⊆ Metric.closedBall (y₀ + w) t₀ := by
    intro y hy
    have hy' : y - w ∈ Metric.closedBall y₀ t₀ := hψB (hψ'supp hy)
    have hd : dist y (y₀ + w) = dist (y - w) y₀ := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    exact Metric.mem_closedBall.2 (by rw [hd]; exact Metric.mem_closedBall.1 hy')
  have hψ'grad : ∀ y, gradient ψ' y = gradient ψ (y - w) := fun y =>
    Komlos.Literature.gradient_comp_sub_const (hψ.differentiable (by simp)) w y
  -- the two integrals vanish
  have hI₁ : (∫ x, ⟪F x, gradient ψ x⟫) = 0 := hH.weakEq ψ hψ hψs (hψB.trans hBU)
  have hI₂ : (∫ x, ⟪F x, gradient ψ' x⟫) = 0 := hH.weakEq ψ' hψ'C hψ's (hψ'B.trans hBU')
  -- integrability
  have hint₁ : Integrable (fun x => ⟪F x, gradient ψ x⟫) volume :=
    integrable_inner_gradient hFm hψ hψs measurableSet_closedBall hψB
      (hH.integrableOn_flux hP hBU)
  have hint₂' : Integrable (fun y => ⟪F y, gradient ψ' y⟫) volume :=
    integrable_inner_gradient hFm hψ'C hψ's measurableSet_closedBall hψ'B
      (hH.integrableOn_flux hP hBU')
  have hcongr : ∀ x : Euc d, ⟪F (x + w), gradient ψ x⟫ =
      (fun y => ⟪F y, gradient ψ' y⟫) (x + w) := by
    intro x
    simp only [hψ'grad]
    congr 2
    abel
  have hint₂ : Integrable (fun x => ⟪F (x + w), gradient ψ x⟫) volume := by
    refine (hint₂'.comp_add_right w).congr (Eventually.of_forall fun x => ?_)
    exact (hcongr x).symm
  have htrans : (∫ x, ⟪F (x + w), gradient ψ x⟫) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hcongr),
      integral_add_right_eq_self (fun y => ⟪F y, gradient ψ' y⟫) w]
    exact hI₂
  -- put it together
  have hpt : ∀ x : Euc d, ⟪diffQuot s e F x, gradient ψ x⟫ =
      s⁻¹ * (⟪F (x + w), gradient ψ x⟫ - ⟪F x, gradient ψ x⟫) := by
    intro x
    rw [diffQuot_apply, real_inner_smul_left, inner_sub_left]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_sub hint₂ hint₁, htrans, hI₁]
  simp

end WeakEq

/-! ### The difference quotient as a linear solution -/

section LinearSol

open Classical in
/-- The coefficient field of the difference-quotient equation, cut off outside a set `S` so that
the flux `A (Δ_s^e G)` is globally measurable.  `IsUnifElliptic` only constrains `A` on the
domain of the equation, which will be a subset of `S`. -/
noncomputable def regDQCoeffLoc (Ψ : Euc d → ℝ) (H : Euc d → Euc d) (s : ℝ) (e : Euc d)
    (S : Set (Euc d)) (x : Euc d) : Euc d →L[ℝ] Euc d :=
  if x ∈ S then regSecant Ψ (H x) (H (x + s • e)) else ContinuousLinearMap.id ℝ (Euc d)

/-- A difference quotient of a measurable function is measurable. -/
theorem measurable_diffQuot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {f : Euc d → E} (hf : Measurable f) (s : ℝ) (e : Euc d) :
    Measurable (diffQuot s e f) := by
  have h1 : Measurable fun x : Euc d => f (x + s • e) :=
    hf.comp (measurable_id.add_const (s • e))
  exact (h1.sub hf).const_smul _

set_option maxHeartbeats 1000000 in
/-- **The difference quotient of a `Ψ`-harmonic potential is a weak solution of a linear
uniformly elliptic equation**, with the ellipticity constants of `Ψ` and *no* right-hand side —
uniformly in the step `s`.  This is the input the De Giorgi–Nash lane consumes. -/
theorem isLinearSol_diffQuot (hP : IsRegProfileWith Ψ c C) {x₀ : Euc d} {r : ℝ}
    {h : Euc d → ℝ} {H : Euc d → Euc d} (hH : IsRegHarmonicField Ψ (Metric.ball x₀ r) h H)
    {v : Euc d → ℝ} {Gv : Euc d → Euc d} (hvm : Measurable v) (hGvm : Measurable Gv)
    (hvG : HasWeakGradient v Gv) (hv2 : MemLp v 2 volume) (hGv2 : MemLp Gv 2 volume)
    {s : ℝ} (hs : 0 < s) {e : Euc d} (he : ‖e‖ = 1) (q : Euc d) {ρ ρ₀ : ℝ} (hρ : 0 < ρ)
    (hρ0 : ρ + 2 * s ≤ ρ₀) (hρr : ρ₀ ≤ r)
    (hGveq : ∀ x ∈ Metric.ball x₀ ρ₀, Gv x = H x - q) :
    IsLinearSol c C 0 0 (regDQCoeffLoc Ψ H s e (Metric.ball x₀ (ρ + s))) 0 0
      (Metric.ball x₀ ρ) (diffQuot s e v) (diffQuot s e Gv) := by
  classical
  set S : Set (Euc d) := Metric.ball x₀ (ρ + s) with hSdef
  set A : Euc d → (Euc d →L[ℝ] Euc d) := regDQCoeffLoc Ψ H s e S with hAdef
  set Gu : Euc d → Euc d := diffQuot s e Gv with hGudef
  set F : Euc d → Euc d := fun y => gradient Ψ (H y) with hFdef
  have hΩS : Metric.ball x₀ ρ ⊆ S := Metric.ball_subset_ball (by linarith)
  have hSr : S ⊆ Metric.ball x₀ ρ₀ := Metric.ball_subset_ball (by linarith)
  have hSU : S ⊆ Metric.ball x₀ r := hSr.trans (Metric.ball_subset_ball hρr)
  -- on `S` the coefficients are the secant, and the flux is the difference quotient of `∇Ψ ∘ H`
  have hAS : ∀ x ∈ S, A x = regSecant Ψ (H x) (H (x + s • e)) := fun x hx => by
    simp only [hAdef, regDQCoeffLoc, if_pos hx]
  have hGuS : ∀ x ∈ S, Gu x = diffQuot s e H x := by
    intro x hx
    have h1 : Gv x = H x - q := hGveq x (hSr hx)
    have h2 : Gv (x + s • e) = H (x + s • e) - q := by
      refine hGveq _ (Metric.mem_ball.2 ?_)
      have hd : dist (x + s • e) x₀ ≤ dist x x₀ + s := by
        have : dist (x + s • e) x = s := by
          rw [dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
            abs_of_pos hs]
        calc dist (x + s • e) x₀ ≤ dist (x + s • e) x + dist x x₀ := dist_triangle _ _ _
          _ = s + dist x x₀ := by rw [this]
          _ = dist x x₀ + s := by ring
      have hx' : dist x x₀ < ρ + s := Metric.mem_ball.1 hx
      linarith
    simp only [hGudef, diffQuot_apply, h1, h2]
    congr 1
    abel
  have hfluxeq : ∀ x, A x (Gu x) = if x ∈ S then diffQuot s e F x else Gu x := by
    intro x
    by_cases hx : x ∈ S
    · rw [if_pos hx, hAS x hx, hGuS x hx]
      exact regDQCoeff_apply_diffQuot hP.toIsRegProfile H (ne_of_gt hs) e x
    · simp only [hAdef, regDQCoeffLoc, if_neg hx]
      rfl
  have hFm : Measurable F :=
    hP.toIsRegProfile.contDiff_gradient.continuous.measurable.comp hH.measurable_grad
  have hGum : Measurable Gu := measurable_diffQuot hGvm s e
  have hflux_meas : Measurable fun x => A x (Gu x) := by
    have h0 : (fun x => A x (Gu x)) = fun x => if x ∈ S then diffQuot s e F x else Gu x :=
      funext hfluxeq
    rw [h0]
    exact Measurable.ite Metric.isOpen_ball.measurableSet (measurable_diffQuot hFm s e) hGum
  -- `L²` bounds
  have hGu2 : MemLp Gu 2 volume := memLp_diffQuot hGv2 s e
  have hu2 : MemLp (diffQuot s e v) 2 volume := memLp_diffQuot hv2 s e
  have hAnorm : ∀ x, ‖A x‖ ≤ max C 1 := by
    intro x
    by_cases hx : x ∈ S
    · exact (hAS x hx ▸ norm_regSecant_le hP _ _).trans (le_max_left _ _)
    · simp only [hAdef, regDQCoeffLoc, if_neg hx]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)
  have hflux2 : MemLp (fun x => A x (Gu x)) 2 volume := by
    refine (hGu2.const_smul (max C 1)).mono hflux_meas.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    calc ‖A x (Gu x)‖ ≤ ‖A x‖ * ‖Gu x‖ := (A x).le_opNorm _
      _ ≤ max C 1 * ‖Gu x‖ := mul_le_mul_of_nonneg_right (hAnorm x) (norm_nonneg _)
      _ = ‖(max C 1) • Gu x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
  have hρr' : ρ < r := by linarith
  have hBU : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r := Metric.closedBall_subset_ball hρr'
  have hBU' : Metric.closedBall (x₀ + s • e) ρ ⊆ Metric.ball x₀ r := by
    intro y hy
    have hd : dist y (x₀ + s • e) ≤ ρ := Metric.mem_closedBall.1 hy
    have he' : dist (x₀ + s • e) x₀ = s := by
      rw [dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hs]
    have : dist y x₀ ≤ ρ + s := by
      calc dist y x₀ ≤ dist y (x₀ + s • e) + dist (x₀ + s • e) x₀ := dist_triangle _ _ _
        _ ≤ ρ + s := by rw [he']; linarith
    exact Metric.mem_ball.2 (by linarith)
  -- the weak equation against smooth test functions
  have hweak : ∀ χ : Euc d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.ball x₀ ρ →
      (∫ x, ⟪A x (Gu x), gradient χ x⟫) = ∫ x, (0 : ℝ) * χ x := by
    intro χ hχ hχs hχΩ
    have hcongr : ∀ x : Euc d, ⟪A x (Gu x), gradient χ x⟫ = ⟪diffQuot s e F x, gradient χ x⟫ := by
      intro x
      by_cases hx : x ∈ S
      · rw [hfluxeq x, if_pos hx]
      · have hxΩ : x ∉ tsupport χ := fun hc => hx (hΩS (hχΩ hc))
        rw [gradient_eq_zero_of_notMem_tsupport hxΩ, inner_zero_right, inner_zero_right]
    rw [integral_congr_ae (Eventually.of_forall hcongr)]
    have hz := regHarmonic_weakEq_diffQuot hP hH s e hχ hχs hBU hBU'
      (hχΩ.trans Metric.ball_subset_closedBall)
    rw [← hFdef] at hz
    rw [hz]
    simp
  refine { coeff := ?_, hasWeakGradient := hvG.diffQuot s e
           measurable := measurable_diffQuot hvm s e, measurable_grad := hGum
           aesm_flux := hflux_meas.aestronglyMeasurable
           aesm_f := aestronglyMeasurable_const, aesm_g := aestronglyMeasurable_const
           integrableOn := ?_, bound_f := ?_, bound_g := ?_, weakEq := ?_ }
  · refine ⟨Eventually.of_forall fun x hx ξ => ?_, Eventually.of_forall fun x hx => ?_⟩
    · rw [hAS x (hΩS hx)]
      exact regSecant_elliptic hP _ _ ξ
    · rw [hAS x (hΩS hx)]
      exact norm_regSecant_le hP _ _
  · intro y t _
    refine ⟨?_, ?_⟩
    · have h1 : Integrable (fun x => ‖diffQuot s e v x‖ ^ 2) volume :=
        (memLp_two_iff_integrable_sq_norm hu2.aestronglyMeasurable).1 hu2
      refine h1.integrableOn.congr_fun (fun x _ => ?_) measurableSet_closedBall
      show ‖diffQuot s e v x‖ ^ 2 = diffQuot s e v x ^ 2
      rw [Real.norm_eq_abs, sq_abs]
    · have h2 : Integrable (fun x => ‖Gu x‖ ^ 2) volume :=
        (memLp_two_iff_integrable_sq_norm hGu2.aestronglyMeasurable).1 hGu2
      exact h2.integrableOn
  · exact Eventually.of_forall fun x _ => by simp
  · exact Eventually.of_forall fun x _ => by simp
  · intro T ψ hψT
    have hΦ : MemLp ((Metric.ball x₀ ρ).indicator fun x => A x (Gu x)) 2 volume :=
      hflux2.indicator Metric.isOpen_ball.measurableSet
    have hg0 : MemLp ((Metric.ball x₀ ρ).indicator fun _ : Euc d => (0 : ℝ)) 2 volume := by
      simp
    have key := Komlos.Literature.integral_inner_weakGrad_eq_of_memW0_two Metric.isOpen_ball
      hΦ hg0 hweak hψT.isCompact hψT.subset hψT.memW0 hψT.grad_eq_zero
    simp only [zero_mul, integral_zero] at key
    rw [key]
    simp

end LinearSol

/-! ### Localizing a local weak gradient by a cut-off -/

section Cutoff

/-- A locally integrable factor times a bounded continuous factor supported in a set on which the
first is integrable, is integrable. -/
theorem integrable_mul_of_integrableOn {K : Set (Euc d)} (hK : MeasurableSet K)
    {f : Euc d → ℝ} (hfm : AEStronglyMeasurable f volume) (hf : IntegrableOn f K volume)
    {g : Euc d → ℝ} (hgm : AEStronglyMeasurable g volume) (hgK : ∀ x, x ∉ K → g x = 0)
    {M : ℝ} (hM : ∀ x, |g x| ≤ M) : Integrable (fun y => f y * g y) volume := by
  have hsupp : Function.support (fun y => f y * g y) ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (by simp [hgK x hxK])
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  refine Integrable.mono' (hf.norm.const_mul M) ((hfm.mul hgm).restrict) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  calc |f x| * |g x| ≤ |f x| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
    _ = M * ‖f x‖ := by rw [Real.norm_eq_abs]; ring

set_option maxHeartbeats 1000000 in
/-- **Localization of a local weak gradient.**  If `F` is a weak gradient of `f` on the open set
`U` and `η` is a smooth cut-off compactly supported in `U`, then `η f` has the product-rule weak
gradient *globally*.  Only integrability of `f` and `F` on `tsupport η` is needed. -/
theorem HasWeakGradientOn.hasWeakGradient_mul_cutoff {U : Set (Euc d)} {f : Euc d → ℝ}
    {F : Euc d → Euc d} (hfF : HasWeakGradientOn U f F) (hfm : AEStronglyMeasurable f volume)
    (hFm : AEStronglyMeasurable F volume) {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηs : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (hfint : IntegrableOn f (tsupport η) volume) (hFint : IntegrableOn F (tsupport η) volume) :
    HasWeakGradient (fun y => η y * f y) (fun y => η y • F y + f y • gradient η y) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hηd : Differentiable ℝ η := hη1.differentiable one_ne_zero
  have hDηc : Continuous (gradient η) := continuous_gradient' hη
  have hK : MeasurableSet (tsupport η) := (isClosed_tsupport η).measurableSet
  obtain ⟨A, hA0, hA⟩ := exists_bound_of_hasCompactSupport hη.continuous hηs
  obtain ⟨B, hB0, hB⟩ := exists_bound_of_hasCompactSupport hDηc (hasCompactSupport_gradient' hηs)
  have hDηzero : ∀ x, x ∉ tsupport η → gradient η x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport hx
  -- integrability of the localized potential and field
  have hvint : Integrable (fun y => η y * f y) volume := by
    have h0 := integrable_mul_of_integrableOn hK hfm hfint hη.continuous.aestronglyMeasurable
      (fun x hx => image_eq_zero_of_notMem_tsupport hx) (fun x => (Real.norm_eq_abs (η x)) ▸ hA x)
    exact h0.congr (Eventually.of_forall fun x => by ring)
  have hGint : Integrable (fun y => η y • F y + f y • gradient η y) volume := by
    have h1 : Integrable (fun y => η y • F y) volume := by
      have hsupp : Function.support (fun y => η y • F y) ⊆ tsupport η := by
        intro x hx
        by_contra hxK
        exact hx (by simp [image_eq_zero_of_notMem_tsupport hxK])
      rw [← integrableOn_iff_integrable_of_support_subset hsupp]
      refine Integrable.mono' (hFint.norm.const_mul A)
        ((hη.continuous.aestronglyMeasurable.smul hFm).restrict) ?_
      filter_upwards with x
      rw [norm_smul, Real.norm_eq_abs]
      calc |η x| * ‖F x‖ ≤ A * ‖F x‖ := mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)
        _ = A * ‖F x‖ := rfl
    have h2 : Integrable (fun y => f y • gradient η y) volume := by
      have hsupp : Function.support (fun y => f y • gradient η y) ⊆ tsupport η := by
        intro x hx
        by_contra hxK
        exact hx (by simp [hDηzero x hxK])
      rw [← integrableOn_iff_integrable_of_support_subset hsupp]
      refine Integrable.mono' (hfint.norm.const_mul B)
        ((hfm.smul hDηc.aestronglyMeasurable).restrict) ?_
      filter_upwards with x
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
    exact h1.add h2
  refine ⟨hvint.locallyIntegrable, hGint.locallyIntegrable, ?_⟩
  intro ψ hψ hψs w
  set χ : Euc d → ℝ := fun y => η y * ψ y with hχdef
  have hχ : ContDiff ℝ ∞ χ := hη.mul hψ
  have hχs : HasCompactSupport χ := hηs.mul_right
  have hχU : tsupport χ ⊆ U := (tsupport_mul_subset_left).trans hηU
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hψd : Differentiable ℝ ψ := hψ1.differentiable one_ne_zero
  have hprod : ∀ y, fderiv ℝ χ y w = η y * fderiv ℝ ψ y w + ψ y * fderiv ℝ η y w := by
    intro y
    have hd : HasFDerivAt χ (η y • fderiv ℝ ψ y + ψ y • fderiv ℝ η y) y :=
      (hηd y).hasFDerivAt.mul (hψd y).hasFDerivAt
    rw [hd.fderiv]
    simp [smul_eq_mul]
  -- the local weak equation for the product test function
  have key := hfF.integral_eq χ hχ hχs hχU w
  -- integrability of the three pieces
  obtain ⟨Mχ, hMχ0, hMχ⟩ := exists_bound_of_hasCompactSupport hχ.continuous hχs
  have hdχc : Continuous fun y => fderiv ℝ χ y w :=
    ((hχ.of_le (by simp) : ContDiff ℝ 1 χ).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  obtain ⟨Mdχ, hMdχ0, hMdχ⟩ := exists_bound_of_hasCompactSupport hdχc
    ((hχs.fderiv ℝ).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L w) (by simp))
  have hχzero : ∀ x, x ∉ tsupport η → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx (tsupport_mul_subset_left hc))
  have hdχzero : ∀ x, x ∉ tsupport η → fderiv ℝ χ x w = 0 := by
    intro x hx
    have hxχ : x ∉ tsupport χ := fun hc => hx (tsupport_mul_subset_left hc)
    have h0 : fderiv ℝ χ x = 0 := by
      by_contra hc
      exact hxχ (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 hc))
    rw [h0]
    simp
  have hi1 : Integrable (fun y => f y * fderiv ℝ χ y w) volume :=
    integrable_mul_of_integrableOn hK hfm hfint hdχc.aestronglyMeasurable hdχzero
      (fun x => by simpa [Real.norm_eq_abs] using hMdχ x)
  have hdηc : Continuous fun y => ψ y * fderiv ℝ η y w := by
    refine hψ.continuous.mul (((hη1.continuous_fderiv one_ne_zero).clm_apply continuous_const))
  obtain ⟨Mη, hMη0, hMη⟩ := exists_bound_of_hasCompactSupport hdηc
    (((hηs.fderiv ℝ).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L w) (by simp)).mul_left)
  have hdηzero : ∀ x, x ∉ tsupport η → ψ x * fderiv ℝ η x w = 0 := by
    intro x hx
    have h0 : fderiv ℝ η x = 0 := by
      by_contra hc
      exact hx (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 hc))
    rw [h0]
    simp
  have hi2 : Integrable (fun y => f y * (ψ y * fderiv ℝ η y w)) volume :=
    integrable_mul_of_integrableOn hK hfm hfint hdηc.aestronglyMeasurable hdηzero
      (fun x => by simpa [Real.norm_eq_abs] using hMη x)
  have hFwint : IntegrableOn (fun y => ⟪F y, w⟫) (tsupport η) volume :=
    hFint.inner_const (𝕜 := ℝ) w
  have hi3 : Integrable (fun y => ⟪F y, w⟫ * χ y) volume :=
    integrable_mul_of_integrableOn hK (hFm.inner aestronglyMeasurable_const) hFwint
      hχ.continuous.aestronglyMeasurable hχzero
      (fun x => by simpa [Real.norm_eq_abs] using hMχ x)
  -- rewrite both sides
  have hgoal : ∀ y : Euc d, (η y * f y) * fderiv ℝ ψ y w =
      f y * fderiv ℝ χ y w - f y * (ψ y * fderiv ℝ η y w) := by
    intro y
    rw [hprod]
    ring
  have hinner : ∀ y : Euc d, ⟪gradient η y, w⟫ = fderiv ℝ η y w := fun y =>
    (fderiv_apply_eq_inner_gradient (f := η) (x := y) (v := w)).symm
  have hrhs : ∀ y : Euc d, ⟪η y • F y + f y • gradient η y, w⟫ * ψ y =
      ⟪F y, w⟫ * χ y + f y * (ψ y * fderiv ℝ η y w) := by
    intro y
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hinner y, hχdef]
    ring
  rw [integral_congr_ae (Eventually.of_forall hgoal), integral_sub hi1 hi2, key,
    integral_congr_ae (Eventually.of_forall hrhs), integral_add hi3 hi2]
  ring

end Cutoff

end Komlos.Literature.Regularized
