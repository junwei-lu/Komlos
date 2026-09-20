import Komlos.Literature.Regularized.VariationalZeroSet

/-!
# Well-posedness of the regularized energy

Lane `L1` (`reg/variational`), Revision 2 of `REGULARIZED_ROUTE.md`.  This file establishes
everything about `regEnergy 2 κ Ψ` that does not involve a limit of competitors:

* the two parts `kineticEnergy Ψ u = ∫ u² Ψ(∇u/u)` and `entropyEnergy κ u = (κ/2) ∫ u² log u`
  are well-defined (both integrands are integrable for an admissible `u`);
* the two-sided kinetic bound `Ψ 0 + (c/2) ∫‖∇u‖² ≤ kineticEnergy Ψ u ≤ Ψ 0 + (C/2) ∫‖∇u‖²`,
  using `∫ u² = 1` and `∇u = 0` a.e. on `{u = 0}` (`weakGrad_eq_zero_of_eq_zero`);
* the entropy lower bound `entropyEnergy κ u ≥ -(κ/8) |K|`, from `s² log s ≥ -1/4`;
* hence **coercivity** `∫‖∇u‖² ≤ (2/c)(regEnergy 2 κ Ψ u - Ψ 0 + (κ/8)|K|)` and the
  `bddBelow` field of `IsRegMinimizer`;
* the admissible class is nonempty (`exists_isRegAdmissible`), so `regMin` is a genuine
  infimum: `regMin_le_regEnergy` and `le_regMin`.

The integrability of the entropy uses the Sobolev inequality
(`Komlos.Literature.sobolev_inequality`) to gain an exponent: `u ∈ L^{2+δ}` and
`s² log s ≤ s^{2+δ}/δ`.  This is the only place where `0 < d` is needed.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### Elementary facts about the body `K` -/

theorem _root_.Komlos.IsGoodConvex.measurableSet' {K : Set (Euc d)} (hK : IsGoodConvex K) :
    MeasurableSet K := hK.isOpen.measurableSet

theorem _root_.Komlos.IsGoodConvex.volume_ne_top {K : Set (Euc d)} (hK : IsGoodConvex K) :
    volume K ≠ ⊤ := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  exact ((measure_mono hR).trans_lt (isCompact_closedBall (0 : Euc d) R).measure_lt_top).ne

theorem _root_.Komlos.IsGoodConvex.integrable_indicator {K : Set (Euc d)} (hK : IsGoodConvex K) :
    Integrable (K.indicator fun _ => (1 : ℝ)) volume :=
  (integrable_indicator_iff hK.measurableSet').2 (integrableOn_const hK.volume_ne_top)

theorem _root_.Komlos.IsGoodConvex.integral_indicator {K : Set (Euc d)} (hK : IsGoodConvex K) :
    ∫ x, K.indicator (fun _ => (1 : ℝ)) x = (volume K).toReal := by
  rw [integral_indicator_const (1 : ℝ) hK.measurableSet']
  simp [Measure.real]

/-! ### The two parts of the energy -/

/-- The kinetic part `∫ u² Ψ(∇u/u)` of the regularized energy at `p = 2`. -/
noncomputable def kineticEnergy (Ψ : Euc d → ℝ) (u : Euc d → ℝ) : ℝ :=
  ∫ x, Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)

/-- The entropy part `(κ/2) ∫ u² log u` of the regularized energy at `p = 2`. -/
noncomputable def entropyEnergy (κ : ℝ) (u : Euc d → ℝ) : ℝ :=
  ∫ x, Korevaar.entropyPotential 2 κ (u x)

theorem regEnergy_two_eq (κ : ℝ) (Ψ : Euc d → ℝ) (u : Euc d → ℝ) :
    regEnergy 2 κ Ψ u = kineticEnergy Ψ u + entropyEnergy κ u := rfl

/-! ### Integrability -/

namespace IsRegAdmissible

theorem aestronglyMeasurable (hu : IsRegAdmissible 2 K u) : AEStronglyMeasurable u volume :=
  hu.memW0.memLp.aestronglyMeasurable

theorem aestronglyMeasurable_weakGrad (hu : IsRegAdmissible 2 K u) :
    AEStronglyMeasurable (weakGrad u) volume :=
  hu.memW0.memLp_weakGrad.aestronglyMeasurable

theorem integrable_sq (hu : IsRegAdmissible 2 K u) : Integrable (fun x => u x ^ 2) volume := by
  have h := hu.memW0.memLp.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
  refine h.congr (Eventually.of_forall fun x => ?_)
  show ‖u x‖ ^ (ENNReal.ofReal 2).toReal = u x ^ 2
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), Real.norm_eq_abs, rpow_two_eq, sq_abs]

theorem integrable_normSq_weakGrad (hu : IsRegAdmissible 2 K u) :
    Integrable (fun x => ‖weakGrad u x‖ ^ 2) volume := by
  have h := hu.memW0.memLp_weakGrad.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
  refine h.congr (Eventually.of_forall fun x => ?_)
  show ‖weakGrad u x‖ ^ (ENNReal.ofReal 2).toReal = ‖weakGrad u x‖ ^ 2
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), rpow_two_eq]

theorem integral_normSq_weakGrad_nonneg (u : Euc d → ℝ) :
    0 ≤ ∫ x, ‖weakGrad u x‖ ^ 2 :=
  integral_nonneg fun _ => sq_nonneg _

/-- The weak gradient vanishes a.e. on the zero set of an admissible competitor. -/
theorem ae_weakGrad_eq_zero (hK : IsGoodConvex K) (hu : IsRegAdmissible 2 K u) :
    ∀ᵐ x, u x = 0 → weakGrad u x = 0 :=
  weakGrad_eq_zero_of_eq_zero hK.measurableSet' hK.volume_ne_top hu.memW0 hu.nonneg

/-- The pointwise two-sided bound for the kinetic density, valid a.e. -/
theorem ae_kinetic_bounds (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    ∀ᵐ x, Ψ 0 * u x ^ 2 + c / 2 * ‖weakGrad u x‖ ^ 2 ≤
        Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x) ∧
      Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x) ≤
        Ψ 0 * u x ^ 2 + C / 2 * ‖weakGrad u x‖ ^ 2 := by
  filter_upwards [hu.ae_weakGrad_eq_zero hK] with x hx
  exact ⟨h.homogeneousDensity_two_lower (hu.nonneg x) hx,
    h.homogeneousDensity_two_upper (hu.nonneg x) hx⟩

theorem aestronglyMeasurable_kinetic (hΨ : Continuous Ψ) (hu : IsRegAdmissible 2 K u) :
    AEStronglyMeasurable
      (fun x => Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)) volume := by
  simp only [homogeneousDensity_two]
  exact ((hu.aestronglyMeasurable.aemeasurable.pow_const 2).mul
    (hΨ.measurable.comp_aemeasurable ((hu.aestronglyMeasurable.aemeasurable.inv).smul
      hu.aestronglyMeasurable_weakGrad.aemeasurable))).aestronglyMeasurable

theorem integrable_kinetic (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)) volume := by
  refine Integrable.mono' (g := fun x => |Ψ 0| * u x ^ 2 + C / 2 * ‖weakGrad u x‖ ^ 2)
    ((hu.integrable_sq.const_mul _).add (hu.integrable_normSq_weakGrad.const_mul _))
    (hu.aestronglyMeasurable_kinetic h.toIsRegProfile.contDiff.continuous) ?_
  filter_upwards [hu.ae_kinetic_bounds h hK] with x hx
  have hc : 0 ≤ c / 2 * ‖weakGrad u x‖ ^ 2 :=
    mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
  have h1 : -(|Ψ 0| * u x ^ 2) ≤ Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x) := by
    have := hx.1
    nlinarith [neg_abs_le (Ψ 0), sq_nonneg (u x)]
  have h2 : Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x) ≤
      |Ψ 0| * u x ^ 2 + C / 2 * ‖weakGrad u x‖ ^ 2 := by
    have := hx.2
    nlinarith [le_abs_self (Ψ 0), sq_nonneg (u x)]
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · nlinarith
  · exact h2

/-! ### The entropy: integrability via the Sobolev gain -/

theorem entropy_eq (hu : IsRegAdmissible 2 K u) (x : Euc d) :
    Korevaar.entropyPotential 2 κ (u x) = κ / 2 * (u x ^ 2 * Real.log (u x)) :=
  entropyPotential_two κ (hu.nonneg x)

theorem aestronglyMeasurable_entropy (hu : IsRegAdmissible 2 K u) :
    AEStronglyMeasurable (fun x => Korevaar.entropyPotential 2 κ (u x)) volume := by
  refine AEStronglyMeasurable.congr (f := fun x => κ / 2 * (u x ^ 2 * Real.log (u x))) ?_
    (Eventually.of_forall fun x => (hu.entropy_eq x).symm)
  exact (((hu.aestronglyMeasurable.aemeasurable.pow_const 2).mul
    (Real.measurable_log.comp_aemeasurable hu.aestronglyMeasurable.aemeasurable)).const_mul
      (κ / 2)).aestronglyMeasurable

/-- The entropy density is bounded below by `-(κ/8)` on `K` and vanishes a.e. off `K`. -/
theorem ae_entropy_lower (hκ : 0 ≤ κ) (hu : IsRegAdmissible 2 K u) :
    ∀ᵐ x, -(κ / 8) * K.indicator (fun _ => (1 : ℝ)) x ≤
      Korevaar.entropyPotential 2 κ (u x) := by
  filter_upwards [hu.memW0.ae_eq_zero] with x hx
  rw [hu.entropy_eq x]
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK, mul_one]
    have h1 := neg_quarter_le_sq_mul_log (hu.nonneg x)
    nlinarith
  · rw [Set.indicator_of_notMem hxK, hx hxK]
    simp

/-- `u ∈ L^{2+δ}` gives integrability of the entropy density. -/
theorem integrable_entropy_of_memLp {δ : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) (hmem : MemLp u (ENNReal.ofReal (2 + δ)) volume) :
    Integrable (fun x => Korevaar.entropyPotential 2 κ (u x)) volume := by
  have hpow : Integrable (fun x => u x ^ (2 + δ)) volume := by
    refine (integrable_norm_rpow_of_memLp (by linarith) hmem).congr
      (Eventually.of_forall fun x => ?_)
    show ‖u x‖ ^ (2 + δ) = u x ^ (2 + δ)
    rw [Real.norm_eq_abs, abs_of_nonneg (hu.nonneg x)]
  refine Integrable.mono' (g := fun x => κ / 2 *
      (1 / 4 * K.indicator (fun _ => (1 : ℝ)) x + u x ^ (2 + δ) / δ))
    (((hK.integrable_indicator.const_mul (1 / 4)).add (hpow.div_const δ)).const_mul (κ / 2))
    hu.aestronglyMeasurable_entropy ?_
  filter_upwards [hu.memW0.ae_eq_zero] with x hx
  rw [hu.entropy_eq x, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ κ / 2)]
  have hup : (0 : ℝ) ≤ u x ^ (2 + δ) / δ :=
    div_nonneg (Real.rpow_nonneg (hu.nonneg x) _) hδ.le
  have hkey : |u x ^ 2 * Real.log (u x)| ≤ 1 / 4 + u x ^ (2 + δ) / δ :=
    abs_sq_mul_log_le (hu.nonneg x) hδ
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK]
    have : (1 : ℝ) / 4 * 1 + u x ^ (2 + δ) / δ = 1 / 4 + u x ^ (2 + δ) / δ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hkey (by linarith)
  · rw [Set.indicator_of_notMem hxK, hx hxK]
    have hz : (0 : ℝ) ^ (2 + δ) = 0 := Real.zero_rpow (by positivity)
    simp [hz]

end IsRegAdmissible

/-- **The Sobolev gain**: for a bounded body there is `δ > 0` with `W₀^{1,2}(K) ⊆ L^{2+δ}`. -/
theorem exists_memLp_of_memW0 (hK : IsGoodConvex K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Euc d → ℝ, MemW0 2 K v → MemLp v (ENNReal.ofReal (2 + δ)) volume := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- in dimension `0` every function is constant, and the measure is finite
    subst hd0
    refine ⟨1, one_pos, fun v _ => ?_⟩
    have heq : v = fun _ => v 0 := by
      funext x
      congr 1
      exact Subsingleton.elim _ _
    rw [heq]
    exact memLp_const _
  · obtain ⟨κS, hκS, CS, hCS, hsob⟩ := sobolev_inequality hd one_lt_two hK.isBounded
    refine ⟨κS * 2 - 2, by linarith, fun v hv => ?_⟩
    have heq : 2 + (κS * 2 - 2) = κS * 2 := by ring
    rw [heq]
    refine ⟨hv.memLp.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (hsob v hv)
      (ENNReal.mul_lt_top hCS.lt_top hv.memLp_weakGrad.eLpNorm_lt_top)

theorem IsRegAdmissible.integrable_entropy (hκ : 0 ≤ κ) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    Integrable (fun x => Korevaar.entropyPotential 2 κ (u x)) volume := by
  obtain ⟨δ, hδ, hmem⟩ := exists_memLp_of_memW0 hK
  exact hu.integrable_entropy_of_memLp hδ hκ hK (hmem u hu.memW0)

/-! ### The energy bounds -/

namespace IsRegAdmissible

theorem kineticEnergy_ge (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    Ψ 0 + c / 2 * (∫ x, ‖weakGrad u x‖ ^ 2) ≤ kineticEnergy Ψ u := by
  have hint : Integrable (fun x => Ψ 0 * u x ^ 2 + c / 2 * ‖weakGrad u x‖ ^ 2) volume :=
    (hu.integrable_sq.const_mul _).add (hu.integrable_normSq_weakGrad.const_mul _)
  have hle := integral_mono_ae hint (hu.integrable_kinetic h hK)
    ((hu.ae_kinetic_bounds h hK).mono fun x hx => hx.1)
  rw [integral_add (hu.integrable_sq.const_mul _) (hu.integrable_normSq_weakGrad.const_mul _),
    integral_const_mul, integral_const_mul, hu.integral_sq, mul_one] at hle
  exact hle

theorem kineticEnergy_le (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    kineticEnergy Ψ u ≤ Ψ 0 + C / 2 * (∫ x, ‖weakGrad u x‖ ^ 2) := by
  have hint : Integrable (fun x => Ψ 0 * u x ^ 2 + C / 2 * ‖weakGrad u x‖ ^ 2) volume :=
    (hu.integrable_sq.const_mul _).add (hu.integrable_normSq_weakGrad.const_mul _)
  have hle := integral_mono_ae (hu.integrable_kinetic h hK) hint
    ((hu.ae_kinetic_bounds h hK).mono fun x hx => hx.2)
  rw [integral_add (hu.integrable_sq.const_mul _) (hu.integrable_normSq_weakGrad.const_mul _),
    integral_const_mul, integral_const_mul, hu.integral_sq, mul_one] at hle
  exact hle

theorem entropyEnergy_ge (hκ : 0 ≤ κ) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    -(κ / 8) * (volume K).toReal ≤ entropyEnergy κ u := by
  have hle := integral_mono_ae (hK.integrable_indicator.const_mul (-(κ / 8)))
    (hu.integrable_entropy hκ hK) (hu.ae_entropy_lower hκ)
  rwa [integral_const_mul, hK.integral_indicator] at hle

/-- **The energy bounds the Dirichlet integral** (coercivity). -/
theorem regEnergy_ge (h : IsRegProfileWith Ψ c C) (hκ : 0 ≤ κ)
    (hK : IsGoodConvex K) (hu : IsRegAdmissible 2 K u) :
    Ψ 0 + c / 2 * (∫ x, ‖weakGrad u x‖ ^ 2) - κ / 8 * (volume K).toReal ≤
      regEnergy 2 κ Ψ u := by
  rw [regEnergy_two_eq]
  have h1 := hu.kineticEnergy_ge h hK
  have h2 := hu.entropyEnergy_ge hκ hK
  linarith

theorem le_regEnergy (h : IsRegProfileWith Ψ c C) (hκ : 0 ≤ κ)
    (hK : IsGoodConvex K) (hu : IsRegAdmissible 2 K u) :
    Ψ 0 - κ / 8 * (volume K).toReal ≤ regEnergy 2 κ Ψ u := by
  have h1 := hu.regEnergy_ge h hκ hK
  have h2 : 0 ≤ c / 2 * (∫ x, ‖weakGrad u x‖ ^ 2) :=
    mul_nonneg (by linarith [h.c_pos]) (integral_normSq_weakGrad_nonneg u)
  linarith

theorem integral_normSq_weakGrad_le (h : IsRegProfileWith Ψ c C) (hκ : 0 ≤ κ)
    (hK : IsGoodConvex K) (hu : IsRegAdmissible 2 K u) :
    ∫ x, ‖weakGrad u x‖ ^ 2 ≤
      2 / c * (regEnergy 2 κ Ψ u - Ψ 0 + κ / 8 * (volume K).toReal) := by
  have h1 := hu.regEnergy_ge h hκ hK
  have hc := h.c_pos
  have hkey : c / 2 * (∫ x, ‖weakGrad u x‖ ^ 2) ≤
      regEnergy 2 κ Ψ u - Ψ 0 + κ / 8 * (volume K).toReal := by linarith
  have h2 : 2 / c * (c / 2 * (∫ x, ‖weakGrad u x‖ ^ 2)) ≤
      2 / c * (regEnergy 2 κ Ψ u - Ψ 0 + κ / 8 * (volume K).toReal) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have h3 : 2 / c * (c / 2 * (∫ x, ‖weakGrad u x‖ ^ 2)) = ∫ x, ‖weakGrad u x‖ ^ 2 := by
    field_simp
  rw [h3] at h2
  exact h2

end IsRegAdmissible

/-! ### The admissible class is nonempty -/

/-- A nonnegative normalized competitor exists: square a test function and normalize. -/
theorem exists_isRegAdmissible (hK : IsGoodConvex K) : ∃ u : Euc d → ℝ, IsRegAdmissible 2 K u := by
  obtain ⟨⟨f, hf⟩⟩ := hK.nonempty_testFn
  set g : Euc d → ℝ := fun x => f x ^ 2 with hg_def
  have hsupp : Function.support g ⊆ Function.support f := by
    intro x hx
    simp only [hg_def, Function.mem_support] at hx ⊢
    exact fun h => hx (by rw [h]; ring)
  have htsupp : tsupport g ⊆ tsupport f := closure_mono hsupp
  have hgtest : IsTestFn K g :=
    { contDiff := hf.contDiff.pow 2
      hasCompactSupport := hf.hasCompactSupport.mono hsupp
      supp_subset := htsupp.trans hf.supp_subset
      ne_zero := by
        intro h0
        refine hf.ne_zero (funext fun x => ?_)
        have : g x = 0 := by rw [h0]; rfl
        simpa [hg_def, pow_eq_zero_iff] using this }
  -- the normalization constant
  have hApos : 0 < ∫ x, g x ^ 2 := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    have hmem : MemLp f (ENNReal.ofReal 4) volume :=
      hf.contDiff.continuous.memLp_of_hasCompactSupport hf.hasCompactSupport
    have hpos := integral_abs_rpow_pos h4 hmem hf.not_ae_eq_zero
    refine lt_of_lt_of_le hpos (le_of_eq (integral_congr_ae (Eventually.of_forall fun x => ?_)))
    show |f x| ^ (4 : ℝ) = g x ^ 2
    rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ f x ^ 4)]
    simp only [hg_def]
    ring
  set A : ℝ := ∫ x, g x ^ 2 with hA_def
  set t : ℝ := (Real.sqrt A)⁻¹ with ht_def
  have hsq : Real.sqrt A > 0 := Real.sqrt_pos.2 hApos
  refine ⟨t • g, ?_, ?_, ?_, ?_⟩
  · exact (hgtest.memW0 2).smul t
  · intro x
    exact mul_nonneg (le_of_lt (inv_pos.2 hsq)) (by positivity)
  · intro x hx
    have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hgtest.supp_subset h)
    simp [this]
  · have hconv : ∀ x : Euc d, (t • g) x ^ (2 : ℝ) = t ^ 2 * g x ^ 2 := by
      intro x
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [integral_congr_ae (Eventually.of_forall hconv), integral_const_mul, ← hA_def, ht_def]
    rw [inv_pow, Real.sq_sqrt hApos.le]
    field_simp

/-! ### `regMin` -/

theorem nonempty_isRegAdmissible (hK : IsGoodConvex K) :
    Nonempty {v : Euc d → ℝ // IsRegAdmissible 2 K v} :=
  (exists_isRegAdmissible hK).elim fun u hu => ⟨⟨u, hu⟩⟩

/-- The `bddBelow` field of `IsRegMinimizer`: competitor energies are bounded below by
`Ψ 0 - (κ/8)|K|`. -/
theorem bddBelow_range_regEnergy (h : IsRegProfileWith Ψ c C) (hκ : 0 ≤ κ)
    (hK : IsGoodConvex K) :
    BddBelow (Set.range fun v : {v : Euc d → ℝ // IsRegAdmissible 2 K v} =>
      regEnergy 2 κ Ψ v.1) := by
  refine ⟨Ψ 0 - κ / 8 * (volume K).toReal, ?_⟩
  rintro y ⟨v, rfl⟩
  exact v.2.le_regEnergy h hκ hK

theorem regMin_le_regEnergy (h : IsRegProfileWith Ψ c C) (hκ : 0 ≤ κ)
    (hK : IsGoodConvex K) (hu : IsRegAdmissible 2 K u) :
    regMin 2 κ Ψ K ≤ regEnergy 2 κ Ψ u :=
  ciInf_le (bddBelow_range_regEnergy h hκ hK) (⟨u, hu⟩ : {v : Euc d → ℝ // IsRegAdmissible 2 K v})

theorem le_regMin (h : IsRegProfileWith Ψ c C) (hκ : 0 ≤ κ) (hK : IsGoodConvex K) :
    Ψ 0 - κ / 8 * (volume K).toReal ≤ regMin 2 κ Ψ K := by
  have := nonempty_isRegAdmissible hK
  exact le_ciInf fun v => v.2.le_regEnergy h hκ hK

end Komlos.Literature.Regularized
