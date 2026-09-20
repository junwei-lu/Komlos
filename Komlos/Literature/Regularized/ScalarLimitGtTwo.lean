import Komlos.Literature.Regularized.ScalarLimitGtTwoChain
import Komlos.Literature.Regularized.VariationalLsc
import Komlos.Literature.Sobolev.Rellich

/-!
# The lower scalar limit for `p > 2`

`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*, lower half, the case `2 < p`.

For `p > 2` the truncated power satisfies `h_R ≤ s^p/p`, so `Ψ_n ≤ F^p/p` and the pointwise
argument of `le_integral_kinetic_regProfile` (valid only for `p ≤ 2`) is unavailable.  The
truncation level therefore has to be sent to infinity *along a minimizing sequence*, which
forces a compactness argument.

## The argument

Suppose `regMin 2 κ_n Ψ_n K < E` for every `n` (this is the negation of the statement, after
extracting a subsequence).  Pick admissible `w n` with `regEnergy 2 κ_n Ψ_n (w n) < E`.

1. **Uniform `W^{1,2}` bound.**  `Ψ_n ≥ Θ_1` (`truncDensity_le_regProfile`, using `R_n ≥ 1` and
   the monotonicity of `h_R` in `R` for `p ≥ 2`), and `Θ_1` has quadratic coercivity
   (`quad_le_homogeneousDensity_truncDensity`); together with the entropy bound this gives
   `∫ ‖∇w n‖² ≤ D`.
2. **Compactness.**  Rellich–Kondrachov gives an `L²`-convergent subsequence; sequential
   Banach–Alaoglu in `L²` gives weakly convergent gradients (`exists_weakGrad_of_bounded`), and
   the limit `v` is again admissible.
3. **Lower semicontinuity at a fixed truncation level.**  For each `R₀` and each `η > 0` pick a
   mollifier of small radius `ε₀`; then `Ψ₀ = regProfile p F R₀ ρ₀` is a genuine `IsRegProfile`
   with `Ψ₀ ≤ Ψ_n + A ε₀ (1 + ‖q‖)` (`exists_regProfile_comparison`, using `R₀ ≤ R_n`), and the
   affine error integrates to at most `A ε₀ (1 + (1+D)/2)`.  Lane `L1`'s lower semicontinuity
   (`le_of_tendsto_integral_kineticDensityNorm`) applies verbatim to `Ψ₀` and yields
   `∫ D_{Ψ₀}(v, ∇v) ≤ E + η`; by Jensen `Θ_{R₀} ≤ Ψ₀`, so `∫ D_{Θ_{R₀}}(v, ∇v) ≤ E`.
4. **`R₀ → ∞` and the chain rule** (`lambdaGen_div_le_of_truncDensity_le`) give
   `λ_{p,F}(K)/p ≤ E`, contradicting `E = λ_{p,F}(K)/p - δ`.

## Main result

* `le_regMin_of_gt_two'`: the frozen statement `le_regMin_of_gt_two` of
  `Komlos/Literature/Regularized/ScalarLimitLower.lean`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-- An `ℝ≥0∞` bound from a `toReal` bound (the local copy of `VariationalExistence`'s
`eLpNorm_le_ofReal`). -/
theorem eLpNorm_le_ofReal' {H : Type*} [NormedAddCommGroup H] {f : Euc d → H}
    (hf : MemLp f 2 (volume : Measure (Euc d))) {B : ℝ}
    (hB : (eLpNorm f 2 volume).toReal ≤ B) : eLpNorm f 2 volume ≤ ENNReal.ofReal B := by
  rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hB

/-! ### Lower semicontinuity with an eventual bound -/

section Lsc

variable {Ψ : Euc d → ℝ} {c C : ℝ} {K : Set (Euc d)}

/-- **Lane `L1`'s lower semicontinuity, with an eventual bound.**  The kinetic integrals lie in a
compact interval, so a subsequence converges; `le_of_tendsto_integral_kineticDensityNorm` applies
to it. -/
theorem integral_kineticNorm_le_of_eventually (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    {w : ℕ → Euc d → ℝ} {v : Euc d → ℝ}
    (hw : ∀ n, IsRegAdmissible 2 K (w n)) (hv : IsRegAdmissible 2 K v)
    {B : ℝ} (hB : ∀ n, (eLpNorm (weakGrad (w n)) 2 volume).toReal ≤ B)
    (hstrong : Tendsto (fun n => (eLpNorm (fun x => w n x - v x) 2 volume).toReal) atTop (𝓝 0))
    (hweak : ∀ φ : Euc d → Euc d, MemLp φ 2 volume →
      Tendsto (fun n => ∫ x, ⟪weakGrad (w n) x, φ x⟫) atTop (𝓝 (∫ x, ⟪weakGrad v x, φ x⟫)))
    {b : ℝ}
    (hb : ∀ᶠ n in atTop, (∫ x, kineticDensityNorm Ψ (w n x) (weakGrad (w n) x)) ≤ b) :
    (∫ x, kineticDensityNorm Ψ (v x) (weakGrad v x)) ≤ b := by
  have hX : ∀ n, (∫ x, ‖weakGrad (w n) x‖ ^ 2) ≤ B ^ 2 := by
    intro n
    rw [← toReal_eLpNorm_sq' (hw n).memLp2_weakGrad]
    have h0 : (0 : ℝ) ≤ (eLpNorm (weakGrad (w n)) 2 volume).toReal := ENNReal.toReal_nonneg
    nlinarith [hB n, h0]
  have hIcc : ∀ n, (∫ x, kineticDensityNorm Ψ (w n x) (weakGrad (w n) x)) ∈
      Set.Icc (0 : ℝ) (C / 2 * B ^ 2) := by
    intro n
    refine ⟨integral_nonneg_of_ae ?_, ?_⟩
    · filter_upwards [(hw n).ae_kineticNorm_nonneg h hK] with x hx
      exact le_trans (mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)) hx
    · have h1 := (hw n).kineticEnergy_le h hK
      have h2 := (hw n).kineticEnergy_eq_add h hK
      have h3 : C / 2 * (∫ x, ‖weakGrad (w n) x‖ ^ 2) ≤ C / 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left (hX n) (by linarith [h.C_nonneg])
      linarith [h1, h2, h3]
  obtain ⟨α, -, φ, hφ, hα⟩ := isCompact_Icc.tendsto_subseq hIcc
  have hαb : α ≤ b := le_of_tendsto hα (hφ.tendsto_atTop.eventually hb)
  refine le_trans ?_ hαb
  have hstrong' : Tendsto
      (fun k => (eLpNorm (fun x => w (φ k) x - v x) 2 volume).toReal) atTop (𝓝 0) :=
    hstrong.comp hφ.tendsto_atTop
  have hweak' : ∀ ψ : Euc d → Euc d, MemLp ψ 2 volume →
      Tendsto (fun k => ∫ x, ⟪weakGrad (w (φ k)) x, ψ x⟫) atTop
        (𝓝 (∫ x, ⟪weakGrad v x, ψ x⟫)) := fun ψ hψ => (hweak ψ hψ).comp hφ.tendsto_atTop
  exact le_of_tendsto_integral_kineticDensityNorm h hK (fun k => hw (φ k)) hv
    (fun k => hB (φ k)) hstrong' hweak' hα

end Lsc

/-! ### The integral form of the profile comparison -/

section Comparison

variable {K : Set (Euc d)}

/-- **The profile comparison at the level of kinetic integrals.**  An error that is affine in the
profile argument integrates, against a normalized `w` with `∫ ‖∇w‖² ≤ X`, to at most
`a (1 + (1+X)/2)`. -/
theorem integral_kinetic_le_of_profile_le {Ψ Φ : Euc d → ℝ} {c C c' C' : ℝ}
    (hΨ : IsRegProfileWith Ψ c C) (hΦ : IsRegProfileWith Φ c' C') (hK : IsGoodConvex K)
    {w : Euc d → ℝ} (hw : IsRegAdmissible 2 K w) {a : ℝ} (ha : 0 ≤ a)
    (hle : ∀ q, Ψ q ≤ Φ q + a * (1 + ‖q‖)) {X : ℝ} (hX : (∫ x, ‖weakGrad w x‖ ^ 2) ≤ X) :
    (∫ x, Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x)) ≤
      (∫ x, Korevaar.homogeneousDensity 2 Φ (w x) (weakGrad w x)) + a * (1 + (1 + X) / 2) := by
  have hi1 := integrable_kinetic hΨ hw.memW0 hw.nonneg
  have hi2 := integrable_kinetic hΦ hw.memW0 hw.nonneg
  have hmul : Integrable (fun x => w x * ‖weakGrad w x‖) volume :=
    integrable_mul_of_memLp hw.memLp2 hw.memLp2_weakGrad.norm
  have hi3 : Integrable (fun x => a * (w x ^ 2 + w x * ‖weakGrad w x‖)) volume :=
    (hw.integrable_sq.add hmul).const_mul a
  have hptw : ∀ x, Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) ≤
      Korevaar.homogeneousDensity 2 Φ (w x) (weakGrad w x) +
        a * (w x ^ 2 + w x * ‖weakGrad w x‖) := fun x =>
    homogeneousDensity_two_le_add hle (hw.nonneg x) (weakGrad w x)
  have hi23 : Integrable (fun x => Korevaar.homogeneousDensity 2 Φ (w x) (weakGrad w x)
      + a * (w x ^ 2 + w x * ‖weakGrad w x‖)) volume :=
    (hi2.add hi3).congr (Eventually.of_forall fun x => rfl)
  have hmono := integral_mono hi1 hi23 hptw
  rw [integral_add hi2 hi3, integral_const_mul,
    integral_add hw.integrable_sq hmul, hw.integral_sq] at hmono
  have hcs : (∫ x, w x * ‖weakGrad w x‖) ≤ (1 + X) / 2 := by
    have hy : ∀ x, w x * ‖weakGrad w x‖ ≤ (w x ^ 2 + ‖weakGrad w x‖ ^ 2) / 2 := fun x => by
      nlinarith [sq_nonneg (w x - ‖weakGrad w x‖)]
    have hsum : Integrable (fun x => w x ^ 2 + ‖weakGrad w x‖ ^ 2) volume :=
      (hw.integrable_sq.add hw.integrable_normSq_weakGrad).congr
        (Eventually.of_forall fun x => rfl)
    have hcalc := integral_mono hmul (hsum.div_const 2) hy
    rw [integral_div, integral_add hw.integrable_sq hw.integrable_normSq_weakGrad,
      hw.integral_sq] at hcalc
    linarith [hcalc, hX]
  have hstep := mul_le_mul_of_nonneg_left hcs ha
  linarith [hmono, hstep]

end Comparison

/-! ### The core compactness argument -/

/-- **The core of the lower scalar limit for `p > 2`.**  If every `regMin 2 κ_n Ψ_n K` is below
`E`, then `λ_{p,F}(K)/p ≤ E`. -/
theorem lambdaGen_div_le_of_regMin_lt {p : ℝ} (hp2 : 2 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {E : ℝ}
    {Rs εs κs : ℕ → ℝ} {ρs : ℕ → Euc d → ℝ}
    (hR1 : ∀ n, 1 ≤ Rs n) (hRlim : Tendsto Rs atTop atTop)
    (hρ : ∀ n, IsMollifier (ρs n) (εs n))
    (hκpos : ∀ n, 0 < κs n) (hκlim : Tendsto κs atTop (𝓝 0))
    (hlt : ∀ n, regMin 2 (κs n) (regProfile p F (Rs n) (ρs n)) K < E) :
    lambdaGen p F K / p ≤ E := by
  have hp : 1 < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨cF, hcF0, hcF⟩ := exists_pos_mul_norm_le' hF
  have hRpos : ∀ n, 0 < Rs n := fun n => lt_of_lt_of_le one_pos (hR1 n)
  have hΨreg : ∀ n, IsRegProfile (regProfile p F (Rs n) (ρs n)) := fun n =>
    isRegProfile_regProfile hp (hRpos n) hF (hρ n)
  have hΨW : ∀ n, ∃ c C : ℝ, IsRegProfileWith (regProfile p F (Rs n) (ρs n)) c C := fun n =>
    (hΨreg n).exists_isRegProfileWith
  -- an almost-minimizing competitor at each level
  have hex : ∀ n, ∃ u : Euc d → ℝ, IsRegAdmissible 2 K u ∧
      regEnergy 2 (κs n) (regProfile p F (Rs n) (ρs n)) u < E := by
    intro n
    have := nonempty_isRegAdmissible (K := K) hK
    have h : (⨅ u : {u : Euc d → ℝ // IsRegAdmissible 2 K u},
        regEnergy 2 (κs n) (regProfile p F (Rs n) (ρs n)) u.1) < E := hlt n
    obtain ⟨u, hu⟩ := exists_lt_of_ciInf_lt h
    exact ⟨u.1, u.2, hu⟩
  choose w hwadm hwlt using hex
  have hwint : ∀ n, Integrable (fun x =>
      Korevaar.homogeneousDensity 2 (regProfile p F (Rs n) (ρs n)) (w n x)
        (weakGrad (w n) x)) volume := by
    intro n
    obtain ⟨c, C, hW⟩ := hΨW n
    exact integrable_kinetic hW (hwadm n).memW0 (hwadm n).nonneg
  -- the kinetic bound
  have hkin : ∀ n, (∫ x, Korevaar.homogeneousDensity 2 (regProfile p F (Rs n) (ρs n)) (w n x)
      (weakGrad (w n) x)) ≤ E + κs n / 2 * |(1 / 2) * Real.log (volume K).toReal| := by
    intro n
    have h1 := entropy_integral_ge (hκpos n) hK (hwadm n)
    have h2 := hwlt n
    rw [regEnergy] at h2
    linarith
  have hEslim : Tendsto
      (fun n => E + κs n / 2 * |(1 / 2) * Real.log (volume K).toReal|) atTop (𝓝 E) := by
    have h0 : Tendsto (fun n => κs n / 2 * |(1 / 2) * Real.log (volume K).toReal|) atTop (𝓝 0) := by
      simpa using (hκlim.div_const 2).mul_const |(1 / 2) * Real.log (volume K).toReal|
    simpa using tendsto_const_nhds.add h0
  obtain ⟨S, hSmem⟩ := hEslim.bddAbove_range
  have hS : ∀ n, E + κs n / 2 * |(1 / 2) * Real.log (volume K).toReal| ≤ S := fun n =>
    hSmem ⟨n, rfl⟩
  -- the uniform Dirichlet bound
  obtain ⟨A₁, hA₁pos, hA₁le⟩ : ∃ A₁ : ℝ, 0 < A₁ ∧ ∀ t : ℝ, 0 ≤ t → ∀ ξ : Euc d, (t = 0 → ξ = 0) →
      A₁ * ‖ξ‖ ^ 2 - (p - 1) / 2 * t ^ 2 ≤
        Korevaar.homogeneousDensity 2 (truncDensity p F 1) t ξ := by
    refine ⟨(p - 1) / 4 * (2 / p) ^ 2 * cF ^ 2, by positivity, fun t ht ξ hξ => ?_⟩
    have h := quad_le_homogeneousDensity_truncDensity hp hF hcF0 hcF ht hξ
    linarith [h]
  have hXb : ∀ n, (∫ x, ‖weakGrad (w n) x‖ ^ 2) ≤ (S + (p - 1) / 2) / A₁ := by
    intro n
    have hptw : ∀ᵐ x, A₁ * ‖weakGrad (w n) x‖ ^ 2 - (p - 1) / 2 * (w n x) ^ 2 ≤
        Korevaar.homogeneousDensity 2 (regProfile p F (Rs n) (ρs n)) (w n x)
          (weakGrad (w n) x) := by
      filter_upwards [(hwadm n).ae_weakGrad_eq_zero hK] with x hx
      refine le_trans (hA₁le (w n x) ((hwadm n).nonneg x) (weakGrad (w n) x) hx) ?_
      exact homogeneousDensity_two_mono
        (fun q => truncDensity_le_regProfile hp hp2.le hF one_pos (hR1 n) (hρ n) q) _ _
    have hi1 : Integrable (fun x =>
        A₁ * ‖weakGrad (w n) x‖ ^ 2 - (p - 1) / 2 * (w n x) ^ 2) volume :=
      ((hwadm n).integrable_normSq_weakGrad.const_mul _).sub
        ((hwadm n).integrable_sq.const_mul _)
    have hmono := integral_mono_ae hi1 (hwint n) hptw
    rw [integral_sub ((hwadm n).integrable_normSq_weakGrad.const_mul _)
      ((hwadm n).integrable_sq.const_mul _), integral_const_mul, integral_const_mul,
      (hwadm n).integral_sq, mul_one] at hmono
    rw [le_div_iff₀ hA₁pos]
    linarith [hmono, hkin n, hS n]
  set D : ℝ := (S + (p - 1) / 2) / A₁ with hDdef
  have hD0 : 0 ≤ D := le_trans (integral_nonneg fun _ => sq_nonneg _) (hXb 0)
  set B : ℝ := Real.sqrt D with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBb : ∀ n, (eLpNorm (weakGrad (w n)) 2 volume).toReal ≤ B := fun n =>
    toReal_eLpNorm_le_of_sq_le' (hwadm n).memLp2_weakGrad hB0
      (by rw [hBdef, Real.sq_sqrt hD0]; exact hXb n)
  -- Rellich
  have hCbtop : (max 1 (ENNReal.ofReal B) : ℝ≥0∞) ≠ ⊤ :=
    (max_lt ENNReal.one_lt_top ENNReal.ofReal_lt_top).ne
  have hbound : ∀ n, eLpNorm (w n) (ENNReal.ofReal 2) ≤ max 1 (ENNReal.ofReal B) ∧
      gradLpNorm 2 (w n) ≤ max 1 (ENNReal.ofReal B) := by
    intro n
    refine ⟨?_, ?_⟩
    · rw [ofReal_two]
      refine le_trans ?_ (le_max_left _ _)
      have h1 : eLpNorm (w n) 2 volume ≤ ENNReal.ofReal 1 :=
        eLpNorm_le_ofReal' (hwadm n).memLp2 (by rw [(hwadm n).toReal_eLpNorm_eq_one])
      simpa using h1
    · rw [gradLpNorm, ofReal_two]
      exact le_trans (eLpNorm_le_ofReal' (hwadm n).memLp2_weakGrad (hBb n)) (le_max_right _ _)
  obtain ⟨f, hfmem, φ₁, hφ₁, hlim₁⟩ :=
    rellich one_lt_two hK.isBounded w (fun n => (hwadm n).memW0) hCbtop hbound
  rw [ofReal_two] at hfmem
  have hlim₁' : Tendsto (fun k => eLpNorm (w (φ₁ k) - f) 2 volume) atTop (𝓝 0) :=
    hlim₁.congr fun k => by rw [ofReal_two]
  -- the weak limit of the gradients
  obtain ⟨g, φ₂, hgmem, hφ₂, hgM, hwg, hweak⟩ :=
    exists_weakGrad_of_bounded (u := fun k => w (φ₁ k)) (G := fun k => weakGrad (w (φ₁ k)))
      (fun k => (hwadm (φ₁ k)).memW0.hasWeakGradient)
      (fun k => (hwadm (φ₁ k)).memLp2_weakGrad) (fun k => (hwadm (φ₁ k)).memLp2) hfmem
      hlim₁' hB0 (fun k => eLpNorm_le_ofReal' (hwadm (φ₁ k)).memLp2_weakGrad (hBb (φ₁ k)))
  -- an a.e.-convergent subsequence
  obtain ⟨φ₃, hφ₃, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := volume)
    (p := 2) (by simp) (fun k => (hwadm (φ₁ (φ₂ k))).memLp2.aestronglyMeasurable)
    hfmem.aestronglyMeasurable
    ((hlim₁'.comp hφ₂.tendsto_atTop).congr fun k => rfl)).exists_seq_tendsto_ae
  set ψ : ℕ → ℕ := fun k => φ₁ (φ₂ (φ₃ k)) with hψdef
  have hψmono : StrictMono ψ := (hφ₁.comp hφ₂).comp hφ₃
  set W : ℕ → Euc d → ℝ := fun k => w (ψ k) with hWdef
  have hWadm : ∀ k, IsRegAdmissible 2 K (W k) := fun k => hwadm (ψ k)
  -- the admissible representative of the limit
  have hfvanish : ∀ᵐ x, x ∉ K → f x = 0 := by
    filter_upwards [hae, ae_all_iff.2 fun n => (hwadm n).memW0.ae_eq_zero] with x hx hzero hxK
    exact tendsto_nhds_unique (hx.congr fun i => hzero _ hxK) tendsto_const_nhds
  have hfnonneg : ∀ᵐ x, 0 ≤ f x := by
    filter_upwards [hae] with x hx
    exact ge_of_tendsto' hx fun i => (hwadm _).nonneg x
  set v : Euc d → ℝ := K.indicator (fun x => max (f x) 0) with hvdef
  have hae_v : f =ᵐ[volume] v := by
    filter_upwards [hfvanish, hfnonneg] with x hx hx0
    by_cases hxK : x ∈ K
    · rw [hvdef, Set.indicator_of_mem hxK, max_eq_left hx0]
    · rw [hvdef, Set.indicator_of_notMem hxK, hx hxK]
  have hwgv : HasWeakGradient v g := hwg.congr_left hae_v
  have hgv : weakGrad v =ᵐ[volume] g := hwgv.weakGrad_ae_eq
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
  -- transport the convergences to `W` and `v`
  have hstrong : Tendsto (fun k => (eLpNorm (fun x => W k x - v x) 2 volume).toReal) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k => eLpNorm (w (ψ k) - f) 2 volume) atTop (𝓝 0) :=
      (hlim₁'.comp hφ₂.tendsto_atTop).comp hφ₃.tendsto_atTop
    have h2 : ∀ k, eLpNorm (fun x => W k x - v x) 2 volume = eLpNorm (w (ψ k) - f) 2 volume := by
      intro k
      refine eLpNorm_congr_ae ?_
      filter_upwards [hae_v] with x hx
      simp [hWdef, hx]
    simp only [h2]
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using h3
  have hweakW : ∀ φ : Euc d → Euc d, MemLp φ 2 volume →
      Tendsto (fun k => ∫ x, ⟪weakGrad (W k) x, φ x⟫) atTop
        (𝓝 (∫ x, ⟪weakGrad v x, φ x⟫)) := by
    intro φ hφ
    have h1 := (hweak φ hφ).comp (hφ₃.tendsto_atTop)
    have h2 : (∫ x, ⟪g x, φ x⟫) = ∫ x, ⟪weakGrad v x, φ x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [hgv] with x hx
      rw [hx]
    rw [← h2]
    simpa [Function.comp_def, hWdef, hψdef] using h1
  have hBW : ∀ k, (eLpNorm (weakGrad (W k)) 2 volume).toReal ≤ B := fun k => hBb (ψ k)
  have hRψ : Tendsto (fun k => Rs (ψ k)) atTop atTop := hRlim.comp hψmono.tendsto_atTop
  have hEsψ : Tendsto
      (fun k => E + κs (ψ k) / 2 * |(1 / 2) * Real.log (volume K).toReal|) atTop (𝓝 E) :=
    hEslim.comp hψmono.tendsto_atTop
  -- the truncated kinetic bounds for `v`
  have hstep : ∀ R₀ : ℝ, 0 < R₀ →
      (∫ x, Korevaar.homogeneousDensity 2 (truncDensity p F R₀) (v x) (weakGrad v x)) ≤ E := by
    intro R₀ hR₀
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨A, hA0, hAle⟩ := exists_regProfile_comparison hp hp2.le hF hR₀
    -- choose the mollification radius
    have hT0 : (0 : ℝ) < 1 + (1 + D) / 2 := by linarith
    have hAT : (0 : ℝ) ≤ A * (1 + (1 + D) / 2) := mul_nonneg hA0 hT0.le
    have hden : (0 : ℝ) < 4 * (A * (1 + (1 + D) / 2) + 1) := by linarith
    set ε₀ : ℝ := min 1 (η / (4 * (A * (1 + (1 + D) / 2) + 1))) with hε₀def
    have hε₀0 : 0 < ε₀ := lt_min one_pos (by positivity)
    have hε₀1 : ε₀ ≤ 1 := min_le_left _ _
    have hεA : A * ε₀ * (1 + (1 + D) / 2) < η / 2 := by
      have h1 : ε₀ ≤ η / (4 * (A * (1 + (1 + D) / 2) + 1)) := min_le_right _ _
      have h2 : A * ε₀ * (1 + (1 + D) / 2) = (A * (1 + (1 + D) / 2)) * ε₀ := by ring
      have h3 : (A * (1 + (1 + D) / 2)) * ε₀ ≤
          (A * (1 + (1 + D) / 2)) * (η / (4 * (A * (1 + (1 + D) / 2) + 1))) :=
        mul_le_mul_of_nonneg_left h1 hAT
      have h4 : (A * (1 + (1 + D) / 2)) * (η / (4 * (A * (1 + (1 + D) / 2) + 1))) ≤ η / 4 := by
        have heq : (A * (1 + (1 + D) / 2)) * (η / (4 * (A * (1 + (1 + D) / 2) + 1)))
            = (A * (1 + (1 + D) / 2)) * η / (4 * (A * (1 + (1 + D) / 2) + 1)) := by ring
        rw [heq, div_le_iff₀ hden]
        nlinarith [hη, hAT]
      linarith [h2, h3, h4, hη]
    obtain ⟨ρ₀, hρ₀⟩ := exists_isMollifier (d := d) hε₀0
    have hΨ₀reg : IsRegProfile (regProfile p F R₀ ρ₀) := isRegProfile_regProfile hp hR₀ hF hρ₀
    obtain ⟨c₀, C₀, hW₀⟩ := hΨ₀reg.exists_isRegProfileWith
    -- the eventual bound on the normalized kinetic integrals
    have hcomp : ∀ᶠ k in atTop,
        (∫ x, kineticDensityNorm (regProfile p F R₀ ρ₀) (W k x) (weakGrad (W k) x)) ≤
          E + η - regProfile p F R₀ ρ₀ 0 := by
      filter_upwards [hRψ.eventually_ge_atTop R₀,
        hEsψ.eventually (eventually_lt_nhds (by linarith : E < E + η / 2))] with k hk hEk
      obtain ⟨cn, Cn, hWn⟩ := hΨW (ψ k)
      have hcompare := integral_kinetic_le_of_profile_le hW₀ hWn hK (hWadm k)
        (a := A * ε₀) (mul_nonneg hA0 hε₀0.le)
        (fun q => hAle ε₀ ρ₀ hρ₀ hε₀1 (Rs (ψ k)) hk (εs (ψ k)) (ρs (ψ k)) (hρ (ψ k)) q)
        (hXb (ψ k))
      have hk2 := hkin (ψ k)
      have heq := (hWadm k).kineticEnergy_eq_add hW₀ hK
      rw [kineticEnergy] at heq
      have hWeq : ∀ x, W k x = w (ψ k) x := fun x => rfl
      simp only [hWdef] at heq hcompare ⊢
      linarith [hcompare, hk2, hEk, heq, hεA]
    have hlsc := integral_kineticNorm_le_of_eventually hW₀ hK hWadm hvadm hBW hstrong hweakW hcomp
    -- back to the kinetic density
    have heqv := hvadm.kineticEnergy_eq_add hW₀ hK
    rw [kineticEnergy] at heqv
    have hΨ₀int : Integrable (fun x =>
        Korevaar.homogeneousDensity 2 (regProfile p F R₀ ρ₀) (v x) (weakGrad v x)) volume :=
      integrable_kinetic hW₀ hvadm.memW0 hvadm.nonneg
    have hΘle : ∀ x, Korevaar.homogeneousDensity 2 (truncDensity p F R₀) (v x) (weakGrad v x) ≤
        Korevaar.homogeneousDensity 2 (regProfile p F R₀ ρ₀) (v x) (weakGrad v x) := fun x =>
      homogeneousDensity_two_mono
        (fun q => truncDensity_le_regProfile hp hp2.le hF hR₀ le_rfl hρ₀ q) _ _
    have hΘint : Integrable (fun x =>
        Korevaar.homogeneousDensity 2 (truncDensity p F R₀) (v x) (weakGrad v x)) volume := by
      refine Integrable.mono' hΨ₀int
        (aestronglyMeasurable_kinetic (continuous_truncDensity hp hF)
          hvadm.aestronglyMeasurable hvadm.aestronglyMeasurable_weakGrad)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (homogeneousDensity_two_nonneg
        (fun q => truncDensity_nonneg hp hR₀.le hF q) _ _)]
      exact hΘle x
    have hmono := integral_mono hΘint hΨ₀int hΘle
    linarith [hmono, hlsc, heqv]
  exact lambdaGen_div_le_of_truncDensity_le hp2 hF hK hvadm hstep

/-! ### The frozen statement -/

/-- **(L6, `reg/limits`)** The lower scalar limit for `p > 2`; this is the frozen statement
`le_regMin_of_gt_two` of `Komlos/Literature/Regularized/ScalarLimitLower.lean`. -/
theorem le_regMin_of_gt_two' {p : ℝ} (hp2 : 2 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ)
    {Rs εs κs : ℕ → ℝ} {ρs : ℕ → Euc d → ℝ}
    (hRpos : ∀ n, 0 < Rs n) (hRlim : Tendsto Rs atTop atTop)
    (hρ : ∀ n, IsMollifier (ρs n) (εs n)) (hεlim : Tendsto εs atTop (𝓝 0))
    (hκpos : ∀ n, 0 < κs n) (hκlim : Tendsto κs atTop (𝓝 0)) :
    ∀ᶠ n in atTop, lambdaGen p F K / p - δ ≤
      regMin 2 (κs n) (regProfile p F (Rs n) (ρs n)) K := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨σ, hσ, hσlt⟩ := Filter.extraction_of_frequently_atTop hcon
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hRlim.eventually_ge_atTop (1 : ℝ))
  set τ : ℕ → ℕ := fun k => σ (k + N) with hτdef
  have hτmono : StrictMono τ := fun a b hab => hσ (Nat.add_lt_add_right hab N)
  have hτge : ∀ k, N ≤ τ k := fun k =>
    le_trans (Nat.le_add_left N k) hσ.le_apply
  have hR1 : ∀ k, 1 ≤ Rs (τ k) := fun k => hN _ (hτge k)
  have hlt : ∀ k, regMin 2 (κs (τ k)) (regProfile p F (Rs (τ k)) (ρs (τ k))) K
      < lambdaGen p F K / p - δ := fun k => not_le.1 (hσlt (k + N))
  have hRτ : Tendsto (fun k => Rs (τ k)) atTop atTop := hRlim.comp hτmono.tendsto_atTop
  have hκτ : Tendsto (fun k => κs (τ k)) atTop (𝓝 0) := hκlim.comp hτmono.tendsto_atTop
  have hmain := lambdaGen_div_le_of_regMin_lt (p := p) hp2 hF hK
    (Rs := fun k => Rs (τ k)) (εs := fun k => εs (τ k)) (κs := fun k => κs (τ k))
    (ρs := fun k => ρs (τ k)) hR1 hRτ
    (fun k => hρ (τ k)) (fun k => hκpos (τ k)) hκτ hlt
  linarith [hmain]

end Komlos.Literature.Regularized
