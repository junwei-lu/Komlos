import Komlos.Eigenvalue
import Komlos.EigenvalueConvex

/-!
# The `p ↓ 1` limit and Minkowski convexity of the Cheeger value (paper Lemma 3.2)

`lambdaMix_tendsto_cheeger` (paper (3.9)) is the `p ↓ 1` limit `λ_{p,H}(K) → h_H(K)`, proved
from the smooth-density bridges and a Hölder / dominated-convergence sandwich.
`cheeger_minkowski` (paper Lemma 3.2) then follows by passing to the limit in
`eigenvalue_convexity`. Modulo the single input `eigenvalue_convexity`, this closes Lemma 3.2.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ} {N : ℕ} {α : Fin N → ℝ} {u : Fin N → Euc d}

/-! ### Elementary facts about `mixtureGrad`, `rayleighMix` and `lambdaMix`
(`mixtureGrad_nonneg` and `rayleighMix_nonneg` live in `Komlos/Eigenvalue.lean`.) -/

/-- `H(∇f)` is continuous for `C¹` `f`. -/
theorem continuous_mixtureGrad {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (mixtureGrad α u f) := by
  unfold mixtureGrad
  refine continuous_finsetSum _ fun l _ => continuous_const.mul ?_
  exact ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).abs

/-- `H(∇f)` has compact support when `f` does. -/
theorem hasCompactSupport_mixtureGrad {f : Euc d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (mixtureGrad α u f) :=
  (hf.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => ∑ l, α l * |L (u l)|) (by simp)

/-- `λ_{p,H}(K) ≤ rayleighMix p f` for every test function `f`. -/
theorem lambdaMix_le_rayleighMix (hmix : IsMixture α u) (p : ℝ) {K : Set (Euc d)}
    {f : Euc d → ℝ} (hf : IsTestFn K f) : lambdaMix p α u K ≤ rayleighMix p α u f := by
  have hbdd : BddBelow (Set.range fun f : {f : Euc d → ℝ // IsTestFn K f} =>
      rayleighMix p α u f.1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨g, rfl⟩
    exact rayleighMix_nonneg hmix p g.1
  exact ciInf_le hbdd ⟨f, hf⟩

/-- For a `C¹` compactly supported `g`, `E_H(g) ≤ ∫ H(∇g)` (the inequality half of
`mixtureEnergy_eq_ofReal_integral_mixtureGrad`, from `dirVar_le_lintegral_fderiv`). -/
theorem mixtureEnergy_le_ofReal_integral_mixtureGrad (hmix : IsMixture α u) {g : Euc d → ℝ}
    (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) :
    mixtureEnergy α u g ≤ ENNReal.ofReal (∫ x, mixtureGrad α u g x) := by
  have hint : ∀ l, Integrable (fun x => |fderiv ℝ g x (u l)|) := fun l =>
    (((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).abs).integrable_of_hasCompactSupport
      (hsupp.fderiv_apply ℝ (u l)).abs
  calc mixtureEnergy α u g
      = ∑ l, ENNReal.ofReal (α l) * dirVar (u l) g := rfl
    _ ≤ ∑ l, ENNReal.ofReal (α l) * ∫⁻ x, ‖fderiv ℝ g x (u l)‖ₑ := by
        gcongr with l
        exact dirVar_le_lintegral_fderiv (u l) g hg hsupp
    _ = ∑ l, ENNReal.ofReal (α l * ∫ x, |fderiv ℝ g x (u l)|) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [ENNReal.ofReal_mul (hmix.nonneg l), ofReal_integral_eq_lintegral_ofReal (hint l)
          (Eventually.of_forall fun x => abs_nonneg _)]
        congr 1
        refine lintegral_congr fun x => ?_
        rw [← ofReal_norm, Real.norm_eq_abs]
    _ = ENNReal.ofReal (∑ l, α l * ∫ x, |fderiv ℝ g x (u l)|) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro l _
        exact mul_nonneg (hmix.nonneg l) (integral_nonneg fun x => abs_nonneg _)
    _ = ENNReal.ofReal (∫ x, mixtureGrad α u g x) := by
        congr 1
        unfold mixtureGrad
        rw [integral_finsetSum _ fun l _ => (hint l).const_mul _]
        simp_rw [integral_const_mul]

/-! ### The chain rule for `|f|^p` -/

/-- The directional derivative of `|f|^p` for `p > 1`: `∂_v(|f|^p) = p |f|^{p-2} f ∂_v f`. -/
theorem fderiv_abs_rpow_apply {f : Euc d → ℝ} (hf : Differentiable ℝ f) {p : ℝ} (hp : 1 < p)
    (x v : Euc d) :
    fderiv ℝ (fun x => |f x| ^ p) x v = p * |f x| ^ (p - 2) * f x * fderiv ℝ f x v := by
  have h : (fun x => |f x| ^ p) = fun x => ‖f x‖ ^ p := by
    funext x; rw [Real.norm_eq_abs]
  rw [h, hf.fderiv_norm_rpow hp]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    smul_eq_mul, Real.norm_eq_abs, RCLike.inner_apply, conj_trivial]
  ring

/-- `|∂_v(|f|^p)| = p |f|^{p-1} |∂_v f|` for `p > 1`. -/
theorem abs_fderiv_abs_rpow_apply {f : Euc d → ℝ} (hf : Differentiable ℝ f) {p : ℝ}
    (hp : 1 < p) (x v : Euc d) :
    |fderiv ℝ (fun x => |f x| ^ p) x v| = p * |f x| ^ (p - 1) * |fderiv ℝ f x v| := by
  rw [fderiv_abs_rpow_apply hf hp]
  have h1 : |f x| ^ (p - 1) = |f x| ^ (p - 2) * |f x| := by
    rw [show p - 1 = p - 2 + 1 by ring,
      Real.rpow_add_one' (abs_nonneg _) (by linarith : (0 : ℝ) < p - 2 + 1).ne']
  rw [h1, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  ring

/-! ### The Hölder lower bound -/

/-- Hölder lower bound (paper (3.9) proof): `h_H(K) ≤ p · rayleighMix(f)^{1/p}` for every smooth
test `f`, obtained by testing the Cheeger infimum with `ρ = |f|^p/∫|f|^p`. Hence
`lambdaMix p α u K ≥ (h_H(K)/p)^p`. -/
theorem cheeger_toReal_le_of_rayleigh (hmix : IsMixture α u) {K : Set (Euc d)}
    (hK : IsGoodConvex K) {p : ℝ} (hp : 1 < p) {f : Euc d → ℝ} (hf : IsTestFn K f) :
    (cheeger α u K).toReal ≤ p * rayleighMix p α u f ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hfc : Continuous f := hf.contDiff.continuous
  have hf1 : ContDiff ℝ 1 f := hf.contDiff.of_le (by exact_mod_cast le_top)
  have hfd : Differentiable ℝ f := hf1.differentiable one_ne_zero
  -- the function `|f|^p`
  have hFc : Continuous (fun x => |f x| ^ p) := hfc.abs.rpow_const fun _ => Or.inr hp0.le
  have hFsupp : HasCompactSupport (fun x => |f x| ^ p) :=
    hf.hasCompactSupport.comp_left (g := fun t : ℝ => |t| ^ p) (by simp [hp0.ne'])
  have hF0 : ∀ x, 0 ≤ |f x| ^ p := fun x => Real.rpow_nonneg (abs_nonneg _) p
  have hFint : Integrable (fun x => |f x| ^ p) := hFc.integrable_of_hasCompactSupport hFsupp
  have hF1 : ContDiff ℝ 1 (fun x => |f x| ^ p) := by
    have : (fun x => |f x| ^ p) = fun x => ‖f x‖ ^ p := by
      funext x; rw [Real.norm_eq_abs]
    rw [this]; exact hf1.norm_rpow hp
  -- `c = ∫ |f|^p > 0`
  set c : ℝ := ∫ x, |f x| ^ p with hc
  have hcpos : 0 < c := by
    obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hf.ne_zero (funext h)
    exact integral_pos_of_integrable_nonneg_nonzero hFc hFint hF0
      (x := x₀) (Real.rpow_pos_of_pos (abs_pos.2 hx₀) p).ne'
  -- the test density `g = c⁻¹ |f|^p ∈ 𝒫(K)`
  set g : Euc d → ℝ := fun x => c⁻¹ * |f x| ^ p with hg
  have hg1 : ContDiff ℝ 1 g := contDiff_const.mul hF1
  have hgsupp : HasCompactSupport g := hFsupp.mul_left
  have hgmem : MemP K g :=
    { measurable := hg1.continuous.measurable
      nonneg := fun x => mul_nonneg (inv_nonneg.2 hcpos.le) (hF0 x)
      integrable := hFint.const_mul _
      integral_eq_one := by
        show ∫ x, c⁻¹ * |f x| ^ p = 1
        rw [integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']
      ae_zero_outside := Eventually.of_forall fun x hx => by
        have hx' : x ∉ tsupport f := fun h => hx (hf.supp_subset h)
        simp [hg, image_eq_zero_of_notMem_tsupport hx', hp0.ne']
      dirVar_ne_top := fun v => by
        refine ne_top_of_le_ne_top ?_ (dirVar_le_lintegral_fderiv v g hg1 hgsupp)
        have : Integrable (fun x => fderiv ℝ g x v) :=
          ((hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
            (hgsupp.fderiv_apply ℝ v)
        exact (hasFiniteIntegral_iff_enorm.1 this.hasFiniteIntegral).ne }
  -- `h_H(K) ≤ ∫ H(∇g)`
  have h1 : (cheeger α u K).toReal ≤ ∫ x, mixtureGrad α u g x := by
    refine ENNReal.toReal_le_of_le_ofReal
      (integral_nonneg fun x => mixtureGrad_nonneg hmix g x) ?_
    exact (cheeger_le_mixtureEnergy hgmem).trans
      (mixtureEnergy_le_ofReal_integral_mixtureGrad hmix hg1 hgsupp)
  -- chain rule: `H(∇g) = (p/c) |f|^{p-1} H(∇f)`
  have h2 : ∀ x, mixtureGrad α u g x = p / c * (|f x| ^ (p - 1) * mixtureGrad α u f x) := by
    intro x
    unfold mixtureGrad
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hdg : fderiv ℝ g x = c⁻¹ • fderiv ℝ (fun x => |f x| ^ p) x := by
      rw [hg]
      exact fderiv_const_mul (hF1.differentiable one_ne_zero x) c⁻¹
    rw [hdg, smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.2 hcpos.le), abs_fderiv_abs_rpow_apply hfd hp]
    ring
  -- Hölder with conjugate exponents `q = p/(p-1)` and `p`
  set q : ℝ := Real.conjExponent p with hq
  have hpq : q.HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  have hGc : Continuous (mixtureGrad α u f) := continuous_mixtureGrad hf1
  have hGsupp : HasCompactSupport (mixtureGrad α u f) :=
    hasCompactSupport_mixtureGrad hf.hasCompactSupport
  have hG0 : ∀ x, 0 ≤ mixtureGrad α u f x := mixtureGrad_nonneg hmix f
  have hFq : Continuous (fun x => |f x| ^ (p - 1)) :=
    hfc.abs.rpow_const fun _ => Or.inr (by linarith)
  have hFqsupp : HasCompactSupport (fun x => |f x| ^ (p - 1)) :=
    hf.hasCompactSupport.comp_left (g := fun t : ℝ => |t| ^ (p - 1))
      (by simp [(sub_pos.2 hp).ne'])
  have hHolder : ∫ x, |f x| ^ (p - 1) * mixtureGrad α u f x ≤
      (∫ x, (|f x| ^ (p - 1)) ^ q) ^ (1 / q) * (∫ x, mixtureGrad α u f x ^ p) ^ (1 / p) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
      (Eventually.of_forall hG0) (hFq.memLp_of_hasCompactSupport hFqsupp)
      (hGc.memLp_of_hasCompactSupport hGsupp)
  have hFqq : ∀ x, (|f x| ^ (p - 1)) ^ q = |f x| ^ p := fun x => by
    rw [← Real.rpow_mul (abs_nonneg _), hpq.symm.sub_one_mul_conj]
  have hX0 : 0 ≤ ∫ x, mixtureGrad α u f x ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (hG0 x) p
  have hcq : c ^ (1 / q) = c / c ^ (1 / p) := by
    rw [one_div, one_div, ← hpq.symm.one_sub_inv, Real.rpow_sub hcpos, Real.rpow_one]
  have hcp : c ^ (1 / p) ≠ 0 := (Real.rpow_pos_of_pos hcpos _).ne'
  calc (cheeger α u K).toReal ≤ ∫ x, mixtureGrad α u g x := h1
    _ = p / c * ∫ x, |f x| ^ (p - 1) * mixtureGrad α u f x := by
        simp_rw [h2]; rw [integral_const_mul]
    _ ≤ p / c * ((∫ x, (|f x| ^ (p - 1)) ^ q) ^ (1 / q) *
          (∫ x, mixtureGrad α u f x ^ p) ^ (1 / p)) := by
        gcongr
    _ = p * rayleighMix p α u f ^ (1 / p) := by
        simp_rw [hFqq]
        rw [← hc, hcq]
        show _ = p * ((∫ x, mixtureGrad α u f x ^ p) / c) ^ (1 / p)
        rw [Real.div_rpow hX0 hcpos.le]
        field_simp

/-! ### The `p ↓ 1` limit -/

/-- Near-minimizers of the Cheeger value among smooth test densities (from
`cheegerSmooth_eq_cheeger`): for every `δ > 0` there is a smooth test density `f` with
`∫ H(∇f) < h_H(K) + δ`. -/
theorem exists_testFn_integral_mixtureGrad_lt (hmix : IsMixture α u) {K : Set (Euc d)}
    (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : Euc d → ℝ, IsTestFn K f ∧ 0 ≤ f ∧ ∫ x, f x = 1 ∧
      ∫ x, mixtureGrad α u f x < (cheeger α u K).toReal + δ := by
  have hlt : cheeger α u K < ⊤ := cheeger_lt_top hmix hK.isOpen hK.nonempty
  have h : cheegerSmooth α u K < cheeger α u K + ENNReal.ofReal δ := by
    rw [cheegerSmooth_eq_cheeger hmix hK]
    exact ENNReal.lt_add_right hlt.ne (ENNReal.ofReal_pos.2 hδ).ne'
  simp only [cheegerSmooth, iInf_lt_iff, exists_prop] at h
  obtain ⟨f, hf, hf0, hf1, hlt'⟩ := h
  refine ⟨f, hf, hf0, hf1, ?_⟩
  rw [mixtureEnergy_eq_ofReal_integral_mixtureGrad hmix hf, ← ENNReal.ofReal_toReal hlt.ne,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hδ.le] at hlt'
  exact (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hδ)).1 hlt'

/-- Dominated convergence: `∫ G^p → ∫ G` as `p ↓ 1` for continuous compactly supported
`G ≥ 0`. -/
theorem tendsto_integral_rpow_nhdsWithin_one {G : Euc d → ℝ} (hGc : Continuous G)
    (hGsupp : HasCompactSupport G) (hG0 : ∀ x, 0 ≤ G x) :
    Tendsto (fun p : ℝ => ∫ x, G x ^ p) (𝓝[>] 1) (𝓝 (∫ x, G x)) := by
  obtain ⟨M, hM⟩ := hGc.bounded_above_of_compact_support hGsupp
  have hGM : ∀ x, G x ≤ M := fun x => by
    have := hM x
    rwa [Real.norm_eq_abs, abs_of_nonneg (hG0 x)] at this
  have hM0 : 0 ≤ M := (hG0 0).trans (hGM 0)
  have hev : ∀ᶠ p in 𝓝[>] (1 : ℝ), 1 < p ∧ p ≤ 2 :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (eventually_le_nhds one_lt_two))
  have key : Tendsto (fun p : ℝ => ∫ x, G x ^ p) (𝓝[>] 1) (𝓝 (∫ x, G x ^ (1 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((tsupport G).indicator fun _ => (1 + M) ^ 2) ?_ ?_ ?_ ?_
    · filter_upwards [hev] with p hp
      exact (hGc.rpow_const fun x => Or.inr (by linarith [hp.1])).aestronglyMeasurable
    · filter_upwards [hev] with p hp
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hG0 x) p)]
      by_cases hx : x ∈ tsupport G
      · rw [indicator_of_mem hx]
        calc G x ^ p ≤ (1 + M) ^ p :=
              Real.rpow_le_rpow (hG0 x) (by linarith [hGM x]) (by linarith [hp.1])
          _ ≤ (1 + M) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hp.2
          _ = (1 + M) ^ 2 := Real.rpow_two _
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
          Real.zero_rpow (by linarith [hp.1])]
    · exact (integrableOn_const hGsupp.isCompact.measure_lt_top.ne).integrable_indicator
        (isClosed_tsupport G).measurableSet
    · exact Eventually.of_forall fun x =>
        (Real.continuousAt_const_rpow' one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
  simpa only [Real.rpow_one] using key

/-- **The `p ↓ 1` limit** (paper (3.9)): `λ_{p,H}(K) → h_H(K)` as `p ↓ 1`. -/
theorem lambdaMix_tendsto_cheeger (hmix : IsMixture α u) {K : Set (Euc d)} (hK : IsGoodConvex K) :
    Tendsto (fun p => lambdaMix p α u K) (𝓝[>] 1) (𝓝 (cheeger α u K).toReal) := by
  set L := (cheeger α u K).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  -- test functions exist
  obtain ⟨f₀, hf₀, -, -, -⟩ := exists_testFn_integral_mixtureGrad_lt hmix hK one_pos
  have : Nonempty {f : Euc d → ℝ // IsTestFn K f} := ⟨⟨f₀, hf₀⟩⟩
  have hev : ∀ᶠ p in 𝓝[>] (1 : ℝ), 1 < p := eventually_mem_nhdsWithin
  rw [tendsto_order]
  constructor
  · -- lower bound: `(L/p)^p ≤ λ_p` and `(L/p)^p → L`
    intro a ha
    have hlow : ∀ᶠ p in 𝓝[>] (1 : ℝ), (L / p) ^ p ≤ lambdaMix p α u K := by
      filter_upwards [hev] with p hp
      have hp0 : 0 < p := by linarith
      unfold lambdaMix
      refine le_ciInf fun f => ?_
      have h := cheeger_toReal_le_of_rayleigh hmix hK hp f.2
      have hr : 0 ≤ rayleighMix p α u f.1 := rayleighMix_nonneg hmix p f.1
      calc (L / p) ^ p ≤ (rayleighMix p α u f.1 ^ (1 / p)) ^ p :=
            Real.rpow_le_rpow (div_nonneg hL0 hp0.le)
              ((div_le_iff₀ hp0).2 (by rw [mul_comm]; exact h)) hp0.le
        _ = rayleighMix p α u f.1 := by
            rw [← Real.rpow_mul hr, one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    have hlim : Tendsto (fun p : ℝ => (L / p) ^ p) (𝓝[>] 1) (𝓝 L) := by
      have hc : ContinuousAt (fun p : ℝ => (L / p) ^ p) 1 :=
        (continuousAt_const.div continuousAt_id one_ne_zero).rpow continuousAt_id (Or.inr one_pos)
      have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (1 : ℝ)) hc.tendsto
      simpa using this
    filter_upwards [hlow, hlim.eventually (eventually_gt_nhds ha)] with p h1 h2
    exact h2.trans_le h1
  · -- upper bound: `λ_p ≤ rayleighMix p f_δ → ∫ H(∇f_δ) < L + δ`
    intro b hb
    obtain ⟨f, hf, hf0, hf1, hlt⟩ :=
      exists_testFn_integral_mixtureGrad_lt hmix hK (half_pos (sub_pos.2 hb))
    have hup : ∀ p, lambdaMix p α u K ≤ rayleighMix p α u f := fun p =>
      lambdaMix_le_rayleighMix hmix p hf
    have hlim : Tendsto (fun p => rayleighMix p α u f) (𝓝[>] 1)
        (𝓝 (∫ x, mixtureGrad α u f x)) := by
      have hf1' : ContDiff ℝ 1 f := hf.contDiff.of_le (by exact_mod_cast le_top)
      have hnum := tendsto_integral_rpow_nhdsWithin_one (continuous_mixtureGrad hf1')
        (hasCompactSupport_mixtureGrad hf.hasCompactSupport) (mixtureGrad_nonneg hmix f)
      have hden := tendsto_integral_rpow_nhdsWithin_one (G := fun x => |f x|)
        hf1'.continuous.abs (hf.hasCompactSupport.comp_left abs_zero) (fun x => abs_nonneg _)
      have h1 : ∫ x, |f x| = 1 := by
        rw [← hf1]
        exact integral_congr_ae (Eventually.of_forall fun x => abs_of_nonneg (hf0 x))
      rw [h1] at hden
      have := hnum.div hden one_ne_zero
      rw [div_one] at this
      exact this
    have hb' : ∫ x, mixtureGrad α u f x < b := by linarith
    filter_upwards [hlim.eventually (eventually_lt_nhds hb')] with p hp
    exact (hup p).trans_lt hp

/-! ### Minkowski convexity -/

/-- **Minkowski convexity of the Cheeger value** (paper Lemma 3.2). Proved from
`lambdaMix_tendsto_cheeger` and `eigenvalue_convexity` by passing to the limit `p ↓ 1`; the
boundary cases `t ∈ {0,1}` are immediate. -/
theorem cheeger_minkowski (hmix : IsMixture α u) {K₀ K₁ : Set (Euc d)}
    (hK₀ : IsGoodConvex K₀) (hK₁ : IsGoodConvex K₁) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    cheeger α u ((1 - t) • K₀ + t • K₁) ≤
      ENNReal.ofReal (1 - t) * cheeger α u K₀ + ENNReal.ofReal t * cheeger α u K₁ := by
  rcases ht₀.eq_or_lt with rfl | ht₀'
  · simp [zero_smul_set hK₁.nonempty]
  rcases ht₁.eq_or_lt with rfl | ht₁'
  · simp [zero_smul_set hK₀.nonempty]
  -- interior case: pass to the limit `p ↓ 1` in `eigenvalue_convexity`
  have hKt := isGoodConvex_convexCombo hK₀ hK₁ ht₀' ht₁'
  have h0 := lambdaMix_tendsto_cheeger hmix hK₀
  have h1 := lambdaMix_tendsto_cheeger hmix hK₁
  have ht := lambdaMix_tendsto_cheeger hmix hKt
  have hreal : (cheeger α u ((1 - t) • K₀ + t • K₁)).toReal ≤
      (1 - t) * (cheeger α u K₀).toReal + t * (cheeger α u K₁).toReal := by
    refine le_of_tendsto_of_tendsto ht ((h0.const_mul (1 - t)).add (h1.const_mul t)) ?_
    filter_upwards [eventually_mem_nhdsWithin] with p hp
    exact eigenvalue_convexity hmix hp hK₀ hK₁ ht₀ ht₁
  have hlt₀ := cheeger_lt_top hmix hK₀.isOpen hK₀.nonempty
  have hlt₁ := cheeger_lt_top hmix hK₁.isOpen hK₁.nonempty
  have hltt := cheeger_lt_top hmix hKt.isOpen hKt.nonempty
  rw [← ENNReal.ofReal_toReal hltt.ne, ← ENNReal.ofReal_toReal hlt₀.ne,
    ← ENNReal.ofReal_toReal hlt₁.ne, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul ht₀,
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
      (mul_nonneg ht₀ ENNReal.toReal_nonneg)]
  exact ENNReal.ofReal_le_ofReal hreal

end Komlos
