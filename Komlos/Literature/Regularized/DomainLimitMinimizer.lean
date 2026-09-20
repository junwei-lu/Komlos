import Komlos.Literature.Regularized.DomainLimitEnergy
import Komlos.Literature.Regularized.DomainLimitScalar
import Komlos.Literature.Regularized.VariationalUnique
import Komlos.Literature.Sobolev.Rellich

/-!
# Convergence of the inner-domain minimizers

Step 5 of the `L4` lane of `REGULARIZED_ROUTE.md`: the minimizers `φ_n` of the regularized
energy on the inner domains `K_n = x₀ + s_n (K − x₀)` converge, along a subsequence and almost
everywhere, to the minimizer `φ` on `K`.

The argument is: the energies `regEnergy 2 κ Ψ φ_n = regMin 2 κ Ψ K_n` are bounded (they
decrease to `regMin 2 κ Ψ K` by `DomainLimitScalar`/`DomainLimitEnergy`), the quadratic lower
bound `Ψ 0 + (c/2)‖q‖² ≤ Ψ q` of `ProfileBasic` together with the Jensen bound
`∫ w² log w ≥ −(1/8) |K|` turns this into a bound for `‖φ_n‖_{W^{1,2}}`
(`IsRegAdmissible.integral_normSq_weakGrad_le`), Rellich (`Komlos.Literature.rellich`)
extracts an `L²`-convergent subsequence, the limit is admissible for `K`, lower semicontinuity
of `regEnergy` (`regEnergy_lsc`, proved here out of lane `L1`'s ingredients) plus the scalar
convergence make it a minimizer, and `IsRegMinimizer.ae_eq` identifies it with `φ`; `L²`
convergence finally gives a further a.e. convergent subsequence.

## What lane `L1` supplies

`regEnergy_lsc` is *not* a frozen statement of the interface; it is proved here by replaying
the second half of the direct method of `Komlos/Literature/Regularized/VariationalExistence.lean`
with the limit function given rather than constructed:

* the energies converge, hence are bounded above (`Filter.Tendsto.bddAbove_range`), and
  coercivity (`IsRegAdmissible.integral_normSq_weakGrad_le`) turns this into a uniform bound
  for `∫‖∇u_n‖²`;
* `exists_weakGrad_of_bounded` (sequential Banach–Alaoglu) produces a subsequence along which
  the gradients converge weakly in `L²` to a weak gradient of the limit, necessarily a.e. equal
  to `weakGrad f`;
* `le_of_tendsto_integral_kineticDensityNorm` is the lower semicontinuity of the kinetic part
  (the perspective function and its supporting hyperplanes), and
  `integral_le_of_tendsto_integral` is Fatou for the entropy part, applied to the nonnegative
  shift `(κ/2) w² log w + (κ/8) 1_K`.

Both results of this file are now `sorry`-free.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)}

/-! ### Lower semicontinuity of the regularized energy -/

/-- **Lower semicontinuity of the regularized energy along `L²`-convergent sequences of
admissible competitors.**  This is the input lane `L4` needs from lane `L1`
(`reg/variational`): it is the same convexity/Fatou argument that makes the direct method of
`exists_isRegMinimizer` work, namely that in the variable `ρ̃ = w²` the kinetic density
`ρ̃ Ψ(∇ρ̃/(2ρ̃))` is a perspective function, hence jointly convex in `(ρ̃, ∇ρ̃)`, so the kinetic
part of `regEnergy` is weakly lower semicontinuous, while the entropy part is lower
semicontinuous by Fatou along an a.e. convergent subsequence. -/
theorem regEnergy_lsc (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K)
    {u : ℕ → Euc d → ℝ} {f : Euc d → ℝ} (hu : ∀ n, IsRegAdmissible 2 K (u n))
    (hf : IsRegAdmissible 2 K f)
    (hL2 : Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal 2)) atTop (𝓝 0))
    {L : ℝ} (hlim : Tendsto (fun n => regEnergy 2 κ Ψ (u n)) atTop (𝓝 L)) :
    regEnergy 2 κ Ψ f ≤ L := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  have hL2' : Tendsto (fun n => eLpNorm (u n - f) 2 volume) atTop (𝓝 0) := by
    simpa only [ofReal_two] using hL2
  -- the energies of a convergent sequence are bounded above
  obtain ⟨E₀, hE₀r⟩ := hlim.bddAbove_range
  have hE₀ : ∀ n, regEnergy 2 κ Ψ (u n) ≤ E₀ := fun n => hE₀r ⟨n, rfl⟩
  -- coercivity: a uniform Dirichlet bound
  set Db : ℝ := 2 / c * (E₀ - Ψ 0 + κ / 8 * (volume K).toReal) with hDb_def
  have hDbb : ∀ n, ∫ x, ‖weakGrad (u n) x‖ ^ 2 ≤ Db := by
    intro n
    refine le_trans ((hu n).integral_normSq_weakGrad_le h hκ.le hK) ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hE₀ n]) (by have := h.c_pos; positivity)
  have hD0 : 0 ≤ Db := le_trans (integral_nonneg fun _ => sq_nonneg _) (hDbb 0)
  set B : ℝ := Real.sqrt Db with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBb : ∀ n, (eLpNorm (weakGrad (u n)) 2 volume).toReal ≤ B := fun n =>
    toReal_eLpNorm_le_of_sq_le' (hu n).memLp2_weakGrad hB0
      (by rw [hBdef, Real.sq_sqrt hD0]; exact hDbb n)
  -- weak convergence of the gradients along a subsequence
  obtain ⟨g, φ₂, hgmem, hφ₂, hgM, hwg, hweak⟩ :=
    exists_weakGrad_of_bounded (u := u) (G := fun n => weakGrad (u n))
      (fun n => (hu n).memW0.hasWeakGradient) (fun n => (hu n).memLp2_weakGrad)
      (fun n => (hu n).memLp2) hf.memLp2 hL2' hB0
      (fun n => eLpNorm_le_ofReal (hu n).memLp2_weakGrad (hBb n))
  have hgf : weakGrad f =ᵐ[volume] g := hwg.weakGrad_ae_eq
  -- a further subsequence along which the kinetic integrals converge
  have hIcc : ∀ k : ℕ, (∫ x, kineticDensityNorm Ψ (u (φ₂ k) x) (weakGrad (u (φ₂ k)) x))
      ∈ Set.Icc (0 : ℝ) (C / 2 * Db) := by
    intro k
    refine ⟨integral_nonneg_of_ae ?_, ?_⟩
    · filter_upwards [(hu (φ₂ k)).ae_kineticNorm_nonneg h hK] with x hx
      exact le_trans (mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)) hx
    · refine le_trans (integral_mono_ae ((hu (φ₂ k)).integrable_kineticNorm h hK)
        ((hu (φ₂ k)).integrable_normSq_weakGrad.const_mul (C / 2))
        ((hu (φ₂ k)).ae_kineticNorm_le h hK)) ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hDbb (φ₂ k)) (by linarith [h.C_nonneg])
  obtain ⟨α, -, φ₃, hφ₃, hα⟩ := isCompact_Icc.tendsto_subseq hIcc
  -- and a further subsequence converging a.e.
  obtain ⟨φ₄, hφ₄, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := volume)
    (p := 2) (by simp) (fun k => (hu (φ₂ (φ₃ k))).memLp2.aestronglyMeasurable)
    hf.memLp2.aestronglyMeasurable
    (((hL2'.comp hφ₂.tendsto_atTop).comp hφ₃.tendsto_atTop).congr
      fun k => rfl)).exists_seq_tendsto_ae
  set ψ : ℕ → ℕ := fun k => φ₂ (φ₃ (φ₄ k)) with hψ
  have hψmono : StrictMono ψ := (hφ₂.comp hφ₃).comp hφ₄
  set W : ℕ → Euc d → ℝ := fun k => u (ψ k) with hW
  have hWadm : ∀ k, IsRegAdmissible 2 K (W k) := fun k => hu (ψ k)
  -- the three limits along the final subsequence
  have hstrong : Tendsto (fun k => (eLpNorm (fun x => W k x - f x) 2 volume).toReal) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k => eLpNorm (u (ψ k) - f) 2 volume) atTop (𝓝 0) :=
      ((hL2'.comp hφ₂.tendsto_atTop).comp hφ₃.tendsto_atTop).comp hφ₄.tendsto_atTop
    have h2 : ∀ k, eLpNorm (fun x => W k x - f x) 2 volume = eLpNorm (u (ψ k) - f) 2 volume :=
      fun k => eLpNorm_congr_ae (Eventually.of_forall fun x => rfl)
    simp only [h2]
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using h3
  have hweakW : ∀ φ : Euc d → Euc d, MemLp φ 2 volume →
      Tendsto (fun k => ∫ x, ⟪weakGrad (W k) x, φ x⟫) atTop
        (𝓝 (∫ x, ⟪weakGrad f x, φ x⟫)) := by
    intro φ hφ
    have h1 := (hweak φ hφ).comp (hφ₃.tendsto_atTop.comp hφ₄.tendsto_atTop)
    have h2 : (∫ x, ⟪g x, φ x⟫) = ∫ x, ⟪weakGrad f x, φ x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [hgf] with x hx
      rw [hx]
    rw [← h2]
    simpa [Function.comp_def, hW, hψ] using h1
  have hαW : Tendsto (fun k => ∫ x, kineticDensityNorm Ψ (W k x) (weakGrad (W k) x)) atTop
      (𝓝 α) := by
    have h1 := hα.comp hφ₄.tendsto_atTop
    simpa [Function.comp_def, hW, hψ] using h1
  -- lower semicontinuity of the kinetic part
  have hkin : (∫ x, kineticDensityNorm Ψ (f x) (weakGrad f x)) ≤ α :=
    le_of_tendsto_integral_kineticDensityNorm h hK hWadm hf
      (fun k => hBb (ψ k)) hstrong hweakW hαW
  -- the entropy part, by Fatou
  set ind : Euc d → ℝ := K.indicator (fun _ => (1 : ℝ)) with hind
  set F : ℕ → Euc d → ℝ := fun k x =>
    Korevaar.entropyPotential 2 κ (W k x) + κ / 8 * ind x with hF
  set Fl : Euc d → ℝ := fun x => Korevaar.entropyPotential 2 κ (f x) + κ / 8 * ind x with hFl
  have hFi : ∀ k, Integrable (F k) volume := fun k =>
    ((hWadm k).integrable_entropy hκ.le hK).add (hK.integrable_indicator.const_mul _)
  have hFli : Integrable Fl volume :=
    (hf.integrable_entropy hκ.le hK).add (hK.integrable_indicator.const_mul _)
  have hF0 : ∀ k, 0 ≤ᵐ[volume] F k := by
    intro k
    filter_upwards [(hWadm k).ae_entropy_lower hκ.le] with x hx
    show (0 : ℝ) ≤ Korevaar.entropyPotential 2 κ (W k x) + κ / 8 * ind x
    have hle : -(κ / 8) * ind x ≤ Korevaar.entropyPotential 2 κ (W k x) := hx
    linarith
  have hFlim : ∀ᵐ x, Tendsto (fun k => F k x) atTop (𝓝 (Fl x)) := by
    filter_upwards [hae] with x hx
    have hcont : Tendsto (fun k => Korevaar.entropyPotential 2 κ (W k x)) atTop
        (𝓝 (Korevaar.entropyPotential 2 κ (f x))) := by
      have hW0 : ∀ k, Korevaar.entropyPotential 2 κ (W k x)
          = κ / 2 * ((W k x) ^ 2 * Real.log (W k x)) := fun k =>
        entropyPotential_two κ ((hWadm k).nonneg x)
      have hu0 : Korevaar.entropyPotential 2 κ (f x) = κ / 2 * ((f x) ^ 2 * Real.log (f x)) :=
        entropyPotential_two κ (hf.nonneg x)
      simp only [hW0, hu0]
      exact ((continuous_entropyPotential_two κ).tendsto _).comp hx
    simpa [hF, hFl] using hcont.add_const (κ / 8 * ind x)
  have hβ : Tendsto (fun k => ∫ x, F k x) atTop
      (𝓝 (L - Ψ 0 - α + κ / 8 * (volume K).toReal)) := by
    have hsplit : ∀ k, (∫ x, F k x)
        = (regEnergy 2 κ Ψ (W k)
            - ((∫ x, kineticDensityNorm Ψ (W k x) (weakGrad (W k) x)) + Ψ 0))
          + κ / 8 * (volume K).toReal := by
      intro k
      rw [hF, integral_add ((hWadm k).integrable_entropy hκ.le hK)
        (hK.integrable_indicator.const_mul _), integral_const_mul, hK.integral_indicator]
      have he : regEnergy 2 κ Ψ (W k)
          = ((∫ x, kineticDensityNorm Ψ (W k x) (weakGrad (W k) x)) + Ψ 0)
            + entropyEnergy κ (W k) := by
        rw [regEnergy_two_eq, (hWadm k).kineticEnergy_eq_add h hK]
      rw [entropyEnergy] at he
      linarith [he]
    simp only [hsplit]
    have h1 := hlim.comp hψmono.tendsto_atTop
    have h2 : Tendsto (fun k => regEnergy 2 κ Ψ (W k)) atTop (𝓝 L) := by
      simpa [Function.comp_def, hW] using h1
    have h3 := (h2.sub (hαW.add_const (Ψ 0))).add_const (κ / 8 * (volume K).toReal)
    have heq2 : L - (α + Ψ 0) + κ / 8 * (volume K).toReal
        = L - Ψ 0 - α + κ / 8 * (volume K).toReal := by ring
    rw [heq2] at h3
    exact h3
  have hent : entropyEnergy κ f ≤ L - Ψ 0 - α := by
    have hle := integral_le_of_tendsto_integral hFi hF0 hFli hFlim hβ
    rw [hFl, integral_add (hf.integrable_entropy hκ.le hK)
      (hK.integrable_indicator.const_mul _), integral_const_mul,
      hK.integral_indicator] at hle
    rw [entropyEnergy]
    linarith
  rw [regEnergy_two_eq, hf.kineticEnergy_eq_add h hK]
  linarith

/-! ### The `L²` limit of the inner-domain minimizers -/

/-- **The inner-domain minimizers converge in `L²` to the minimizer on `K`** (`L4`, step 5).
Along a subsequence, `φ_n → f` in `L²` with `f =ᵐ D.φ`: the energies
`regEnergy 2 κ Ψ φ_n = regMin 2 κ Ψ K_n` converge to `regMin 2 κ Ψ K`
(`tendsto_regMin_innerDomain`), hence are bounded, so Rellich extracts an `L²`-convergent
subsequence; `regEnergy_lsc` makes its limit a minimizer on `K`, and `IsRegMinimizer.ae_eq`
identifies it with `D.φ`. -/
theorem exists_subseq_tendsto_eLpNorm_innerDomain (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) (D : RegEigenData 2 κ Ψ K)
    (Dn : ∀ n, RegEigenData 2 κ Ψ (innerDomain x₀ K n)) :
    ∃ (σ : ℕ → ℕ) (f : Euc d → ℝ), StrictMono σ ∧ f =ᵐ[volume] D.φ ∧
      MemLp f 2 (volume : Measure (Euc d)) ∧
      Tendsto (fun k => eLpNorm (fun x => (Dn (σ k)).φ x - f x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  have hadm : ∀ n, IsRegAdmissible 2 K ((Dn n).φ) := fun n =>
    ((Dn n).isRegMinimizer.toIsRegAdmissible).mono (innerDomain_subset hK hx₀ n)
  -- the energies converge to `regMin 2 κ Ψ K`
  have hE : Tendsto (fun n => regEnergy 2 κ Ψ ((Dn n).φ)) atTop (𝓝 (regMin 2 κ Ψ K)) :=
    (tendsto_regMin_innerDomain hκ hΨ hK hx₀ D Dn).congr fun n =>
      ((Dn n).isRegMinimizer.energy_eq).symm
  obtain ⟨E₀, hE₀r⟩ := hE.bddAbove_range
  have hE₀ : ∀ n, regEnergy 2 κ Ψ ((Dn n).φ) ≤ E₀ := fun n => hE₀r ⟨n, rfl⟩
  -- the uniform `W^{1,2}` bound
  set Db : ℝ := 2 / c * (E₀ - Ψ 0 + κ / 8 * (volume K).toReal) with hDb_def
  have hDbb : ∀ n, ∫ x, ‖weakGrad ((Dn n).φ) x‖ ^ 2 ≤ Db := by
    intro n
    refine le_trans ((hadm n).integral_normSq_weakGrad_le h hκ.le hK) ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hE₀ n]) (by have := h.c_pos; positivity)
  have hD0 : 0 ≤ Db := le_trans (integral_nonneg fun _ => sq_nonneg _) (hDbb 0)
  set B : ℝ := Real.sqrt Db with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBb : ∀ n, (eLpNorm (weakGrad ((Dn n).φ)) 2 volume).toReal ≤ B := fun n =>
    toReal_eLpNorm_le_of_sq_le' (hadm n).memLp2_weakGrad hB0
      (by rw [hBdef, Real.sq_sqrt hD0]; exact hDbb n)
  -- Rellich
  set Cb : ℝ≥0∞ := max 1 (ENNReal.ofReal B) with hCb
  have hCbtop : Cb ≠ ⊤ := by
    rw [hCb]
    exact (max_lt ENNReal.one_lt_top ENNReal.ofReal_lt_top).ne
  have hbound : ∀ n, eLpNorm ((Dn n).φ) (ENNReal.ofReal 2) ≤ Cb ∧ gradLpNorm 2 ((Dn n).φ) ≤ Cb := by
    intro n
    constructor
    · rw [ofReal_two]
      refine le_trans ?_ (le_max_left _ _)
      have h1 : eLpNorm ((Dn n).φ) 2 volume ≤ ENNReal.ofReal 1 :=
        eLpNorm_le_ofReal (hadm n).memLp2 (by rw [(hadm n).toReal_eLpNorm_eq_one])
      simpa using h1
    · rw [gradLpNorm, ofReal_two]
      exact le_trans (eLpNorm_le_ofReal (hadm n).memLp2_weakGrad (hBb n)) (le_max_right _ _)
  obtain ⟨f, hfmem, φ₁, hφ₁, hlim₁⟩ :=
    rellich one_lt_two hK.isBounded (fun n => (Dn n).φ) (fun n => (hadm n).memW0) hCbtop hbound
  rw [ofReal_two] at hfmem
  have hlim₁' : Tendsto (fun k => eLpNorm ((Dn (φ₁ k)).φ - f) 2 volume) atTop (𝓝 0) :=
    hlim₁.congr fun k => by rw [ofReal_two]
  -- a weak gradient for the limit
  obtain ⟨g, φ₂, hgmem, hφ₂, hgM, hwg, -⟩ :=
    exists_weakGrad_of_bounded (u := fun k => (Dn (φ₁ k)).φ)
      (G := fun k => weakGrad ((Dn (φ₁ k)).φ))
      (fun k => (hadm (φ₁ k)).memW0.hasWeakGradient)
      (fun k => (hadm (φ₁ k)).memLp2_weakGrad) (fun k => (hadm (φ₁ k)).memLp2) hfmem
      hlim₁' hB0 (fun k => eLpNorm_le_ofReal (hadm (φ₁ k)).memLp2_weakGrad (hBb (φ₁ k)))
  -- an a.e. convergent subsequence, used to see that the limit is nonnegative and vanishes
  -- off `K`
  obtain ⟨φ₅, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := volume)
    (p := 2) (by simp) (fun k => (hadm (φ₁ k)).memLp2.aestronglyMeasurable)
    hfmem.aestronglyMeasurable hlim₁').exists_seq_tendsto_ae
  have hfvanish : ∀ᵐ x, x ∉ K → f x = 0 := by
    filter_upwards [hae, ae_all_iff.2 fun n => (hadm n).memW0.ae_eq_zero] with x hx hzero hxK
    exact tendsto_nhds_unique (hx.congr fun i => hzero _ hxK) tendsto_const_nhds
  have hfnonneg : ∀ᵐ x, 0 ≤ f x := by
    filter_upwards [hae] with x hx
    exact ge_of_tendsto' hx fun i => (hadm _).nonneg x
  -- the admissible representative of the limit
  set v : Euc d → ℝ := K.indicator (fun x => max (f x) 0) with hv_def
  have hae_v : f =ᵐ[volume] v := by
    filter_upwards [hfvanish, hfnonneg] with x hx hx0
    by_cases hxK : x ∈ K
    · rw [hv_def, Set.indicator_of_mem hxK, max_eq_left hx0]
    · rw [hv_def, Set.indicator_of_notMem hxK, hx hxK]
  have hnorm1 : eLpNorm f 2 volume = 1 := by
    have hlim := tendsto_eLpNorm_of_tendsto_eLpNorm_sub (p := 2) one_le_two
      (fun k => (hadm (φ₁ k)).memLp2.aestronglyMeasurable) hfmem hlim₁'
    have heq : ∀ k, eLpNorm ((Dn (φ₁ k)).φ) 2 volume = 1 := by
      intro k
      have h1 := (hadm (φ₁ k)).toReal_eLpNorm_eq_one
      have h2 := (hadm (φ₁ k)).memLp2.eLpNorm_ne_top
      rw [← ENNReal.ofReal_toReal h2, h1, ENNReal.ofReal_one]
    simp only [heq] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  have hfsq : ∫ x, f x ^ 2 = 1 := by
    have h1 := toReal_eLpNorm_sq hfmem
    rw [hnorm1] at h1
    simpa using h1.symm
  have hvadm : IsRegAdmissible 2 K v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (MemW0.mk (by rw [ofReal_two]; exact hfmem) hfvanish
        ⟨g, hwg, by rw [ofReal_two]; exact hgmem⟩).congr hae_v
    · exact fun x => Set.indicator_nonneg (fun y _ => le_max_right _ _) x
    · exact fun x hx => Set.indicator_of_notMem hx _
    · rw [← hfsq]
      refine integral_congr_ae ?_
      filter_upwards [hae_v] with x hx
      show v x ^ (2 : ℝ) = f x ^ 2
      rw [rpow_two_eq, hx]
  -- `v` is a minimizer on `K`
  have hlimv : Tendsto (fun k => eLpNorm ((Dn (φ₁ k)).φ - v) (ENNReal.ofReal 2)) atTop (𝓝 0) := by
    rw [ofReal_two]
    refine hlim₁'.congr fun k => eLpNorm_congr_ae ?_
    filter_upwards [hae_v] with x hx
    show (Dn (φ₁ k)).φ x - f x = (Dn (φ₁ k)).φ x - v x
    rw [hx]
  have hEv : regEnergy 2 κ Ψ v ≤ regMin 2 κ Ψ K :=
    regEnergy_lsc hκ hΨ hK (fun k => hadm (φ₁ k)) hvadm hlimv
      (by simpa [Function.comp_def] using hE.comp hφ₁.tendsto_atTop)
  have hvmin : IsRegMinimizer 2 κ Ψ K v :=
    { hvadm with
      energy_eq := le_antisymm hEv (regMin_le_regEnergy h hκ.le hK hvadm)
      bddBelow := bddBelow_range_regEnergy h hκ.le hK }
  have hvD : v =ᵐ[volume] D.φ :=
    IsRegMinimizer.ae_eq hκ hΨ hK hvmin D.isRegMinimizer
  refine ⟨φ₁, f, hφ₁, hae_v.trans hvD, hfmem, ?_⟩
  refine hlim₁'.congr fun k => eLpNorm_congr_ae (Eventually.of_forall fun x => rfl)

/-- **Convergence of the inner-domain minimizers** (`REGULARIZED_ROUTE.md`, `L4`, step 5): along
a subsequence, the positive continuous representatives `φ_n` of the minimizers on the inner
domains converge almost everywhere to the representative `φ` on `K`. -/
theorem exists_subseq_ae_tendsto_innerDomain (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) (D : RegEigenData 2 κ Ψ K)
    (Dn : ∀ n, RegEigenData 2 κ Ψ (innerDomain x₀ K n)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ z, Tendsto (fun k => (Dn (σ k)).φ z) atTop (𝓝 (D.φ z)) := by
  obtain ⟨σ, f, hσ, hfD, hfmem, hlim⟩ :=
    exists_subseq_tendsto_eLpNorm_innerDomain hκ hΨ hK hx₀ D Dn
  have hadm : ∀ n, IsRegAdmissible 2 K ((Dn n).φ) := fun n =>
    ((Dn n).isRegMinimizer.toIsRegAdmissible).mono (innerDomain_subset hK hx₀ n)
  have hmeas : TendstoInMeasure volume (fun k => (Dn (σ k)).φ) atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (μ := volume) (p := 2) (by simp)
      (fun k => (hadm (σ k)).memLp2.aestronglyMeasurable) hfmem.aestronglyMeasurable
      (hlim.congr fun k => eLpNorm_congr_ae (Eventually.of_forall fun x => rfl))
  obtain ⟨τ, hτ, hae⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨fun k => σ (τ k), hσ.comp hτ, ?_⟩
  filter_upwards [hae, hfD] with z hz hzD
  rw [← hzD]
  exact hz

end Komlos.Literature.Regularized
