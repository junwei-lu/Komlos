import Komlos.Literature.Regularized.VariationalFatou

/-!
# Existence of a minimizer of the regularized energy

Lane `L1` (`reg/variational`): `exists_isRegMinimizer`, the existence half of the frozen lane
statements of `REGULARIZED_ROUTE.md` (Revision 2).  The statement used to be a named `sorry` in
`Komlos/Literature/Regularized/Interface.lean`; lane `L7` deleted it there in favour of this
proof.

## The direct method

1. A minimizing sequence `w n` of admissible competitors with `E(w n) < m + 1/(n+1)`
   (`exists_lt_of_ciInf_lt`, using `bddBelow_range_regEnergy` and the nonemptiness of the
   admissible class).
2. **Coercivity** (`IsRegAdmissible.integral_normSq_weakGrad_le`): `∫‖∇w n‖² ≤ D`.
3. **Rellich–Kondrachov** (`Komlos.Literature.rellich`): a subsequence converging in `L²` to
   some `f`.
4. **Weak compactness of the gradients** (`exists_weakGrad_of_bounded`, via the sequential
   Banach–Alaoglu theorem): a further subsequence whose gradients converge weakly in `L²` to a
   weak gradient `g` of `f`.
5. Two more subsequences: one making the kinetic integrals converge (Bolzano–Weierstrass), one
   making the functions converge a.e. (for Fatou).
6. **Lower semicontinuity**: `le_of_tendsto_integral_kineticDensityNorm` for the kinetic part
   and `integral_le_of_tendsto_integral` (Fatou) for the entropy part.

The representative `u = 1_K · max (f, 0)` is nonnegative everywhere and vanishes off `K`, as
`IsRegAdmissible` requires.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-- An `ℝ≥0∞` bound from a `toReal` bound. -/
theorem eLpNorm_le_ofReal {H : Type*} [NormedAddCommGroup H] {f : Euc d → H}
    (hf : MemLp f 2 (volume : Measure (Euc d))) {B : ℝ}
    (hB : (eLpNorm f 2 volume).toReal ≤ B) : eLpNorm f 2 volume ≤ ENNReal.ofReal B := by
  rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hB

/-- The upper bound for the normalized kinetic density. -/
theorem IsRegAdmissible.ae_kineticNorm_le (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    ∀ᵐ x, kineticDensityNorm Ψ (u x) (weakGrad u x) ≤ C / 2 * ‖weakGrad u x‖ ^ 2 := by
  filter_upwards [hu.ae_kinetic_bounds h hK] with x hx
  rw [homogeneousDensity_two_eq_add] at hx
  linarith [hx.2]

/-- The entropy density is a continuous function of the value. -/
theorem continuous_entropyPotential_two (κ : ℝ) :
    Continuous fun s : ℝ => κ / 2 * (s ^ 2 * Real.log s) := by
  have h : Continuous fun s : ℝ => s * (s * Real.log s) :=
    continuous_id.mul Real.continuous_mul_log
  refine (h.const_mul (κ / 2)).congr fun s => ?_
  ring

/-- **(L1, `reg/variational`)** Existence of a minimizer of the regularized energy: the direct
method for the perspective-plus-entropy functional of `REGULARIZED_ROUTE.md` (Revision 2).
This is exactly the frozen statement `exists_isRegMinimizer` of the interface. -/
theorem exists_isRegMinimizer (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) : ∃ u, IsRegMinimizer 2 κ Ψ K u := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  have hne := nonempty_isRegAdmissible (K := K) hK
  have hbdd : BddBelow (Set.range fun v : {v : Euc d → ℝ // IsRegAdmissible 2 K v} =>
      regEnergy 2 κ Ψ v.1) := bddBelow_range_regEnergy h hκ.le hK
  set m : ℝ := regMin 2 κ Ψ K with hm
  -- a minimizing sequence
  have hseq : ∀ n : ℕ, ∃ v : Euc d → ℝ, IsRegAdmissible 2 K v ∧
      regEnergy 2 κ Ψ v < m + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : (⨅ v : {v : Euc d → ℝ // IsRegAdmissible 2 K v}, regEnergy 2 κ Ψ v.1)
        < m + 1 / ((n : ℝ) + 1) := by
      have heq : (⨅ v : {v : Euc d → ℝ // IsRegAdmissible 2 K v}, regEnergy 2 κ Ψ v.1) = m :=
        hm.symm
      rw [heq]
      linarith
    obtain ⟨v, hv⟩ := exists_lt_of_ciInf_lt hlt
    exact ⟨v.1, v.2, hv⟩
  choose w hwadm hwlt using hseq
  have hlow : ∀ n, m ≤ regEnergy 2 κ Ψ (w n) := fun n =>
    regMin_le_regEnergy h hκ.le hK (hwadm n)
  have hE : Tendsto (fun n => regEnergy 2 κ Ψ (w n)) atTop (𝓝 m) := by
    have hup : Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) atTop (𝓝 m) := by
      have := (tendsto_const_nhds (x := m) (f := (atTop : Filter ℕ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlow
      fun n => (hwlt n).le
  -- the Dirichlet bound
  set D : ℝ := 2 / c * (m + 1 - Ψ 0 + κ / 8 * (volume K).toReal) with hD
  have hDb : ∀ n, ∫ x, ‖weakGrad (w n) x‖ ^ 2 ≤ D := by
    intro n
    refine le_trans ((hwadm n).integral_normSq_weakGrad_le h hκ.le hK) ?_
    have h1 : regEnergy 2 κ Ψ (w n) ≤ m + 1 := by
      have h2 := hwlt n
      have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    exact mul_le_mul_of_nonneg_left (by linarith) (by have := h.c_pos; positivity)
  have hD0 : 0 ≤ D := le_trans (integral_nonneg fun _ => sq_nonneg _) (hDb 0)
  set B : ℝ := Real.sqrt D with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBb : ∀ n, (eLpNorm (weakGrad (w n)) 2 volume).toReal ≤ B := fun n =>
    toReal_eLpNorm_le_of_sq_le' (hwadm n).memLp2_weakGrad hB0
      (by rw [hBdef, Real.sq_sqrt hD0]; exact hDb n)
  -- Rellich
  set Cb : ℝ≥0∞ := max 1 (ENNReal.ofReal B) with hCb
  have hCbtop : Cb ≠ ⊤ := by
    rw [hCb]
    exact (max_lt ENNReal.one_lt_top ENNReal.ofReal_lt_top).ne
  have hbound : ∀ n, eLpNorm (w n) (ENNReal.ofReal 2) ≤ Cb ∧ gradLpNorm 2 (w n) ≤ Cb := by
    intro n
    constructor
    · rw [ofReal_two]
      refine le_trans ?_ (le_max_left _ _)
      have h1 : eLpNorm (w n) 2 volume ≤ ENNReal.ofReal 1 :=
        eLpNorm_le_ofReal (hwadm n).memLp2 (by rw [(hwadm n).toReal_eLpNorm_eq_one])
      simpa using h1
    · rw [gradLpNorm, ofReal_two]
      exact le_trans (eLpNorm_le_ofReal (hwadm n).memLp2_weakGrad (hBb n)) (le_max_right _ _)
  obtain ⟨f, hfmem, φ₁, hφ₁, hlim₁⟩ :=
    rellich one_lt_two hK.isBounded w (fun n => (hwadm n).memW0) hCbtop hbound
  rw [ofReal_two] at hfmem
  have hlim₁' : Tendsto (fun k => eLpNorm (w (φ₁ k) - f) 2 volume) atTop (𝓝 0) :=
    hlim₁.congr fun k => by rw [ofReal_two]
  -- weak limit of the gradients
  obtain ⟨g, φ₂, hgmem, hφ₂, hgM, hwg, hweak⟩ :=
    exists_weakGrad_of_bounded (u := fun k => w (φ₁ k)) (G := fun k => weakGrad (w (φ₁ k)))
      (fun k => (hwadm (φ₁ k)).memW0.hasWeakGradient)
      (fun k => (hwadm (φ₁ k)).memLp2_weakGrad) (fun k => (hwadm (φ₁ k)).memLp2) hfmem
      hlim₁' hB0 (fun k => eLpNorm_le_ofReal (hwadm (φ₁ k)).memLp2_weakGrad (hBb (φ₁ k)))
  -- a convergent subsequence of the kinetic integrals
  have hIcc : ∀ k : ℕ, (∫ x, kineticDensityNorm Ψ (w (φ₁ (φ₂ k)) x)
      (weakGrad (w (φ₁ (φ₂ k))) x)) ∈ Set.Icc (0 : ℝ) (C / 2 * D) := by
    intro k
    set n := φ₁ (φ₂ k) with hn
    refine ⟨integral_nonneg_of_ae ?_, ?_⟩
    · filter_upwards [(hwadm n).ae_kineticNorm_nonneg h hK] with x hx
      exact le_trans (mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)) hx
    · refine le_trans (integral_mono_ae ((hwadm n).integrable_kineticNorm h hK)
        ((hwadm n).integrable_normSq_weakGrad.const_mul (C / 2))
        ((hwadm n).ae_kineticNorm_le h hK)) ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hDb n) (by linarith [h.C_nonneg])
  obtain ⟨α, -, φ₃, hφ₃, hα⟩ := isCompact_Icc.tendsto_subseq hIcc
  -- an a.e. convergent subsequence
  obtain ⟨φ₄, hφ₄, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := volume)
    (p := 2) (by simp) (fun k => (hwadm (φ₁ (φ₂ (φ₃ k)))).memLp2.aestronglyMeasurable)
    hfmem.aestronglyMeasurable
    (((hlim₁'.comp hφ₂.tendsto_atTop).comp hφ₃.tendsto_atTop).congr
      fun k => rfl)).exists_seq_tendsto_ae
  -- the final sequence
  set ψ : ℕ → ℕ := fun k => φ₁ (φ₂ (φ₃ (φ₄ k))) with hψ
  have hψmono : StrictMono ψ := ((hφ₁.comp hφ₂).comp hφ₃).comp hφ₄
  set W : ℕ → Euc d → ℝ := fun k => w (ψ k) with hW
  have hWadm : ∀ k, IsRegAdmissible 2 K (W k) := fun k => hwadm (ψ k)
  -- the limit function and its representative
  have hfvanish : ∀ᵐ x, x ∉ K → f x = 0 := by
    filter_upwards [hae, ae_all_iff.2 fun n => (hwadm n).memW0.ae_eq_zero] with x hx hzero hxK
    exact tendsto_nhds_unique (hx.congr fun i => hzero _ hxK) tendsto_const_nhds
  have hfnonneg : ∀ᵐ x, 0 ≤ f x := by
    filter_upwards [hae] with x hx
    exact ge_of_tendsto' hx fun i => (hwadm _).nonneg x
  set u : Euc d → ℝ := K.indicator (fun x => max (f x) 0) with hu_def
  have hae_u : f =ᵐ[volume] u := by
    filter_upwards [hfvanish, hfnonneg] with x hx hx0
    by_cases hxK : x ∈ K
    · rw [hu_def, Set.indicator_of_mem hxK, max_eq_left hx0]
    · rw [hu_def, Set.indicator_of_notMem hxK, hx hxK]
  have hwgu : HasWeakGradient u g := hwg.congr_left hae_u
  have hgu : weakGrad u =ᵐ[volume] g := hwgu.weakGrad_ae_eq
  -- `∫ f² = 1`
  have hnorm1 : eLpNorm f 2 volume = 1 := by
    have hlim := tendsto_eLpNorm_of_tendsto_eLpNorm_sub (p := 2) one_le_two
      (fun k => (hwadm (φ₁ k)).memLp2.aestronglyMeasurable) hfmem hlim₁'
    have heq : ∀ k, eLpNorm (w (φ₁ k)) 2 volume = 1 := by
      intro k
      have h1 := (hwadm (φ₁ k)).toReal_eLpNorm_eq_one
      have h2 := (hwadm (φ₁ k)).memLp2.eLpNorm_ne_top
      rw [← ENNReal.ofReal_toReal h2, h1, ENNReal.ofReal_one]
    simp only [heq] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  have hfsq : ∫ x, f x ^ 2 = 1 := by
    have h1 := toReal_eLpNorm_sq hfmem
    rw [hnorm1] at h1
    simpa using h1.symm
  have huadm : IsRegAdmissible 2 K u := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (MemW0.mk (by rw [ofReal_two]; exact hfmem) hfvanish
        ⟨g, hwg, by rw [ofReal_two]; exact hgmem⟩).congr hae_u
    · exact fun x => Set.indicator_nonneg (fun y _ => le_max_right _ _) x
    · exact fun x hx => Set.indicator_of_notMem hx _
    · rw [← hfsq]
      refine integral_congr_ae ?_
      filter_upwards [hae_u] with x hx
      show u x ^ (2 : ℝ) = f x ^ 2
      rw [rpow_two_eq, hx]
  -- transport the limits to `W` and `u`
  have hstrong : Tendsto (fun k => (eLpNorm (fun x => W k x - u x) 2 volume).toReal) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k => eLpNorm (w (ψ k) - f) 2 volume) atTop (𝓝 0) :=
      ((hlim₁'.comp hφ₂.tendsto_atTop).comp hφ₃.tendsto_atTop).comp hφ₄.tendsto_atTop
    have h2 : ∀ k, eLpNorm (fun x => W k x - u x) 2 volume = eLpNorm (w (ψ k) - f) 2 volume := by
      intro k
      refine eLpNorm_congr_ae ?_
      filter_upwards [hae_u] with x hx
      simp [hW, hx]
    simp only [h2]
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using h3
  have hweakW : ∀ φ : Euc d → Euc d, MemLp φ 2 volume →
      Tendsto (fun k => ∫ x, ⟪weakGrad (W k) x, φ x⟫) atTop
        (𝓝 (∫ x, ⟪weakGrad u x, φ x⟫)) := by
    intro φ hφ
    have h1 := (hweak φ hφ).comp (hφ₃.tendsto_atTop.comp hφ₄.tendsto_atTop)
    have h2 : (∫ x, ⟪g x, φ x⟫) = ∫ x, ⟪weakGrad u x, φ x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [hgu] with x hx
      rw [hx]
    rw [← h2]
    simpa [Function.comp_def, hW, hψ] using h1
  have hαW : Tendsto (fun k => ∫ x, kineticDensityNorm Ψ (W k x) (weakGrad (W k) x)) atTop
      (𝓝 α) := by
    have h1 := hα.comp hφ₄.tendsto_atTop
    simpa [Function.comp_def, hW, hψ] using h1
  -- lower semicontinuity of the kinetic part
  have hkin : (∫ x, kineticDensityNorm Ψ (u x) (weakGrad u x)) ≤ α :=
    le_of_tendsto_integral_kineticDensityNorm h hK hWadm huadm
      (fun k => hBb (ψ k)) hstrong hweakW hαW
  -- the entropy part, by Fatou
  set ind : Euc d → ℝ := K.indicator (fun _ => (1 : ℝ)) with hind
  set F : ℕ → Euc d → ℝ := fun k x =>
    Korevaar.entropyPotential 2 κ (W k x) + κ / 8 * ind x with hF
  set Fl : Euc d → ℝ := fun x => Korevaar.entropyPotential 2 κ (u x) + κ / 8 * ind x with hFl
  have hFi : ∀ k, Integrable (F k) volume := fun k =>
    ((hWadm k).integrable_entropy hκ.le hK).add (hK.integrable_indicator.const_mul _)
  have hFli : Integrable Fl volume :=
    (huadm.integrable_entropy hκ.le hK).add (hK.integrable_indicator.const_mul _)
  have hF0 : ∀ k, 0 ≤ᵐ[volume] F k := by
    intro k
    filter_upwards [(hWadm k).ae_entropy_lower hκ.le] with x hx
    show (0 : ℝ) ≤ Korevaar.entropyPotential 2 κ (W k x) + κ / 8 * ind x
    have hle : -(κ / 8) * ind x ≤ Korevaar.entropyPotential 2 κ (W k x) := hx
    linarith
  have hFlim : ∀ᵐ x, Tendsto (fun k => F k x) atTop (𝓝 (Fl x)) := by
    filter_upwards [hae, hae_u] with x hx hxu
    have hcont : Tendsto (fun k => Korevaar.entropyPotential 2 κ (W k x)) atTop
        (𝓝 (Korevaar.entropyPotential 2 κ (u x))) := by
      have hW0 : ∀ k, Korevaar.entropyPotential 2 κ (W k x)
          = κ / 2 * ((W k x) ^ 2 * Real.log (W k x)) := fun k =>
        entropyPotential_two κ ((hWadm k).nonneg x)
      have hu0 : Korevaar.entropyPotential 2 κ (u x) = κ / 2 * ((u x) ^ 2 * Real.log (u x)) :=
        entropyPotential_two κ (huadm.nonneg x)
      simp only [hW0, hu0]
      have hxu' : Tendsto (fun k => W k x) atTop (𝓝 (u x)) := by
        rw [← hxu]
        exact hx
      exact ((continuous_entropyPotential_two κ).tendsto _).comp hxu'
    simpa [hF, hFl] using hcont.add_const (κ / 8 * ind x)
  have hβ : Tendsto (fun k => ∫ x, F k x) atTop
      (𝓝 (m - Ψ 0 - α + κ / 8 * (volume K).toReal)) := by
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
    have h1 := hE.comp hψmono.tendsto_atTop
    have h2 : Tendsto (fun k => regEnergy 2 κ Ψ (W k)) atTop (𝓝 m) := by
      simpa [Function.comp_def, hW] using h1
    have h3 := (h2.sub (hαW.add_const (Ψ 0))).add_const (κ / 8 * (volume K).toReal)
    have heq2 : m - (α + Ψ 0) + κ / 8 * (volume K).toReal
        = m - Ψ 0 - α + κ / 8 * (volume K).toReal := by ring
    rw [heq2] at h3
    exact h3
  have hent : entropyEnergy κ u ≤ m - Ψ 0 - α := by
    have hle := integral_le_of_tendsto_integral hFi hF0 hFli hFlim hβ
    rw [hFl, integral_add (huadm.integrable_entropy hκ.le hK)
      (hK.integrable_indicator.const_mul _), integral_const_mul,
      hK.integral_indicator] at hle
    rw [entropyEnergy]
    linarith
  -- conclude
  have hEu : regEnergy 2 κ Ψ u ≤ m := by
    rw [regEnergy_two_eq, huadm.kineticEnergy_eq_add h hK]
    linarith
  refine ⟨u, { huadm with
    energy_eq := le_antisymm hEu (regMin_le_regEnergy h hκ.le hK huadm)
    bddBelow := hbdd }⟩

end Komlos.Literature.Regularized
