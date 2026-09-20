import Komlos.CompactnessAux

/-!
# `L¹`-compactness of densities with bounded coordinate variations (paper Lemma 3.1)

Probability densities supported in a fixed bounded set with uniformly bounded coordinate
variations have an `L¹`-convergent subsequence; the limit is again a probability density
supported in the same set.

Paper proof: the coordinate bounds give a uniform translation modulus
(`lintegral_translate_sub_le_sum_coord`); averaging on cubes of a fixed small mesh
approximates every member uniformly in `L¹` by an element of a bounded subset of a
finite-dimensional space; a diagonal argument (equivalently: total boundedness in the
complete space `L¹`) gives an `L¹`-Cauchy subsequence.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-- Nonnegativity, mass one and the support condition pass to `L¹` limits
(paper Lemma 3.3: "nonnegativity and mass one pass to the limit, and the support condition
follows from `∫_{K^c} |ρ| ≤ ‖ρ − ρ_j‖₁ → 0`"). -/
theorem isProbDensityOn_of_tendsto {K : Set (Euc d)} (ρ : ℕ → Euc d → ℝ)
    (hρ : ∀ n, IsProbDensityOn K (ρ n)) (ρ' : Euc d → ℝ) (hmeas : Measurable ρ')
    (hnn : ∀ x, 0 ≤ ρ' x)
    (hlim : Tendsto (fun n => ∫⁻ x, ‖ρ n x - ρ' x‖ₑ) atTop (𝓝 0)) :
    IsProbDensityOn K ρ' := by
  -- integrability: `ρ' = ρ n − (ρ n − ρ')` for any `n` with `‖ρ n − ρ'‖₁ < ∞`
  have hint : Integrable ρ' := by
    obtain ⟨n, hn⟩ : ∃ n, ∫⁻ x, ‖ρ n x - ρ' x‖ₑ < ⊤ :=
      (hlim.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
    have hsub : Integrable (fun x => ρ n x - ρ' x) :=
      ⟨((hρ n).measurable.sub hmeas).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 hn⟩
    refine ((hρ n).integrable.sub hsub).congr (Eventually.of_forall fun x => ?_)
    simp
  refine ⟨hmeas, hnn, hint, ?_, ?_⟩
  · -- mass one passes to the limit
    have h := tendsto_integral_of_L1 ρ' hint.aestronglyMeasurable
      (Eventually.of_forall fun n => (hρ n).integrable) hlim
    have hone : (fun n => ∫ x, ρ n x) = fun _ => (1 : ℝ) := funext fun n => (hρ n).integral_eq_one
    rw [hone] at h
    exact (tendsto_const_nhds_iff.1 h).symm
  · -- support: an a.e.-convergent subsequence vanishes outside `K`
    have hm : TendstoInMeasure volume ρ atTop ρ' :=
      tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
        (fun n => (hρ n).measurable.aestronglyMeasurable) hmeas.aestronglyMeasurable
        (by simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hlim)
    obtain ⟨ns, -, hae⟩ := hm.exists_seq_tendsto_ae
    filter_upwards [hae, ae_all_iff.2 fun n => (hρ n).ae_zero_outside] with x hx hK hxK
    have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (ρ' x)) :=
      hx.congr fun i => hK (ns i) hxK
    exact (tendsto_const_nhds_iff.1 h0).symm

/-- Paper Lemma 3.1 (compactness): densities supported in a bounded set `K` with coordinate
variations bounded by `M < ∞` have a subsequence converging in `L¹` to a probability density
supported in `K`. -/
theorem exists_subseq_tendsto_L1 {K : Set (Euc d)} (hK : Bornology.IsBounded K)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (ρ : ℕ → Euc d → ℝ) (hρ : ∀ n, IsProbDensityOn K (ρ n))
    (hvar : ∀ n i, dirVar (EuclideanSpace.single i 1) (ρ n) ≤ M) :
    ∃ (φ : ℕ → ℕ) (ρ' : Euc d → ℝ), StrictMono φ ∧ IsProbDensityOn K ρ' ∧
      Tendsto (fun k => ∫⁻ x, ‖ρ (φ k) x - ρ' x‖ₑ) atTop (𝓝 0) := by
  -- the `L¹` classes of the `ρ n`
  set F : ℕ → Lp ℝ 1 (volume : Measure (Euc d)) :=
    fun n => (memLp_one_iff_integrable.2 (hρ n).integrable).toLp (ρ n) with hF
  have hTB : TotallyBounded (Set.range F) := totallyBounded_range_toLp hK hM ρ hρ hvar
  have hcpt : IsCompact (closure (Set.range F)) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨hTB.closure, isClosed_closure.isComplete⟩
  obtain ⟨g, -, φ, hφ, hlim⟩ :=
    hcpt.tendsto_subseq fun n => subset_closure (Set.mem_range_self (f := F) n)
  -- a measurable representative of the limit, truncated to be nonnegative
  set g' : Euc d → ℝ := (Lp.aestronglyMeasurable g).mk g with hg'
  have hg'm : Measurable g' := (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.measurable
  have hgg' : ⇑g =ᵐ[volume] g' := (Lp.aestronglyMeasurable g).ae_eq_mk
  -- `L¹` convergence to `g`, written with the lower integral
  have h2 : ∀ k, eLpNorm (⇑(F (φ k) - g)) 1 volume = ∫⁻ x, ‖ρ (φ k) x - g x‖ₑ := by
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm]
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_sub (F (φ k)) g,
      MemLp.coeFn_toLp (memLp_one_iff_integrable.2 (hρ (φ k)).integrable)] with x hx hx'
    rw [hx, Pi.sub_apply, hx']
  have hconv : Tendsto (fun k => ∫⁻ x, ‖ρ (φ k) x - g x‖ₑ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ‖F (φ k) - g‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hlim
    have h1' : Tendsto (fun k => (∫⁻ x, ‖ρ (φ k) x - g x‖ₑ).toReal) atTop (𝓝 0) := by
      refine h1.congr fun k => ?_
      rw [Lp.norm_def, h2 k]
    have hne : ∀ k, ∫⁻ x, ‖ρ (φ k) x - g x‖ₑ ≠ ⊤ := fun k => (h2 k) ▸ Lp.eLpNorm_ne_top _
    exact (ENNReal.tendsto_toReal_iff hne ENNReal.zero_ne_top).1
      (by rw [ENNReal.toReal_zero]; exact h1')
  -- truncation does not increase the `L¹` distance to a nonnegative function
  have hconv' : Tendsto (fun k => ∫⁻ x, ‖ρ (φ k) x - max (g' x) 0‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => zero_le) fun k => ?_
    refine lintegral_mono_ae ?_
    filter_upwards [hgg'] with x hx
    rw [← hx, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |ρ (φ k) x - max (g x) 0| = |max (ρ (φ k) x) 0 - max (g x) 0| := by
          rw [max_eq_left ((hρ _).nonneg x)]
      _ ≤ |ρ (φ k) x - g x| := abs_max_sub_max_le_abs _ _ _
  exact ⟨φ, fun x => max (g' x) 0, hφ,
    isProbDensityOn_of_tendsto (fun k => ρ (φ k)) (fun k => hρ (φ k)) _
      (hg'm.max measurable_const) (fun x => le_max_right _ _) hconv', hconv'⟩

end Komlos
