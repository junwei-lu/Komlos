import Komlos.Literature.PLaplacian.Eigenfunction

/-!
# The chain rule in `W₀^{1,p}`

The chain rule for weak gradients (Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Lemma 7.5): for `G ∈ C¹(ℝ)` with bounded derivative and `G(0) = 0`, and
`f ∈ W₀^{1,p}(K)`, the composition `G ∘ f` lies in `W₀^{1,p}(K)` with weak gradient `G'(f) ∇f`.
It feeds the Moser iteration of `Komlos.Literature.PLaplacian.RegularityInterior` (global
boundedness of the first eigenfunction, towards Mosconi–Riey–Squassina 2024, Proposition 4.5; paper
Appendix A, *Eigenfunction inputs*).

## Main results

* `hasWeakGradient_gradient_of_contDiff` — a `C¹` function (without compact support) has its
  classical gradient as weak gradient.
* `gradient_comp_apply` — the classical chain rule `∇(G ∘ v) = G'(v) ∇v`.
* `tendsto_eLpNorm_smul_of_tendsto_ae`, `tendsto_eLpNorm_smul_sub_smul` — dominated convergence in
  `L^p` for bounded multipliers converging almost everywhere.
* `memW0_comp` — **the chain rule in `W₀^{1,p}(K)`**. Proof: mollify `f`
  (`tendsto_eLpNorm_mollifyWith_sub`, `gradient_mollifyWith`), pass to an a.e.-convergent
  subsequence, apply the classical chain rule to the smooth approximants and conclude with
  `HasWeakGradient.of_tendsto`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-- A `C¹` function on `ℝ^d` (not necessarily compactly supported) has its classical gradient as
weak gradient (integration by parts against the compactly supported test function). -/
theorem hasWeakGradient_gradient_of_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakGradient f (gradient f) where
  locallyIntegrable := hf.continuous.locallyIntegrable
  locallyIntegrable_grad := (continuous_gradient hf).locallyIntegrable
  integral_mul_fderiv ψ hψ hψs v := by
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hfv : Continuous fun x => fderiv ℝ f x v :=
      (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hψv : Continuous fun x => fderiv ℝ ψ x v :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hsψv : HasCompactSupport fun x => fderiv ℝ ψ x v :=
      (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v)
      (f := f) (g := ψ)
      ((hfv.mul hψ.continuous).integrable_of_hasCompactSupport hψs.mul_left)
      ((hf.continuous.mul hψv).integrable_of_hasCompactSupport hsψv.mul_left)
      ((hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψs.mul_left)
      (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hψ1.differentiable one_ne_zero x)
    rw [h]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only [fderiv_apply_eq_inner_gradient])

/-- The classical chain rule for gradients: `∇(G ∘ v)(x) = G'(v(x)) ∇v(x)`. -/
theorem gradient_comp_apply {G : ℝ → ℝ} (hG : Differentiable ℝ G) {v : Euc d → ℝ} {x : Euc d}
    (hv : DifferentiableAt ℝ v x) :
    gradient (fun y => G (v y)) x = deriv G (v x) • gradient v x :=
  gradient_eq_smul_of_hasFDerivAt ((hG (v x)).hasDerivAt.comp_hasFDerivAt x hv.hasFDerivAt)

/-! ### Dominated convergence in `L^p` -/

/-- **Dominated convergence in `L^p` for bounded multipliers**: if `|h_n| ≤ L`, `h_n → 0` a.e. and
`g ∈ L^p`, then `‖h_n g‖_{L^p} → 0`. -/
theorem tendsto_eLpNorm_smul_of_tendsto_ae {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ} (hp0 : 0 < p) {h : ℕ → α → ℝ} {g : α → E}
    (hg : MemLp g (ENNReal.ofReal p) μ) {L : ℝ} (hh : ∀ n x, |h n x| ≤ L)
    (hhm : ∀ n, AEStronglyMeasurable (h n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => h n x • g x) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hLtop : ENNReal.ofReal (max L 0) ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have hfin : ∫⁻ x, ENNReal.ofReal (max L 0) ^ p * ‖g x‖ₑ ^ p ∂μ ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ hLtop, lintegral_enorm_rpow_eq_eLpNorm_rpow hp0]
    exact ENNReal.mul_ne_top hLtop (ENNReal.rpow_ne_top_of_nonneg hp0.le hg.eLpNorm_ne_top)
  have hint : Tendsto (fun n => ∫⁻ x, ‖h n x • g x‖ₑ ^ p ∂μ) atTop (𝓝 0) := by
    have h0 := tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0)
      (fun x => ENNReal.ofReal (max L 0) ^ p * ‖g x‖ₑ ^ p)
      (fun n => (((hhm n).smul hg.1).enorm.pow_const p)) (fun n => Eventually.of_forall fun x => ?_)
      hfin ?_
    · simpa using h0
    · show ‖h n x • g x‖ₑ ^ p ≤ ENNReal.ofReal (max L 0) ^ p * ‖g x‖ₑ ^ p
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      rw [enorm_smul]
      gcongr
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal ((hh n x).trans (le_max_left _ _))
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun n => h n x • g x) atTop (𝓝 0) := by
        simpa using hx.smul_const (g x)
      have h2 : Tendsto (fun n => ‖h n x • g x‖ₑ) atTop (𝓝 0) := by
        have h := (continuous_enorm.tendsto (0 : E)).comp h1
        rw [enorm_zero] at h
        exact h
      have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp0] using h3
  have h1 : Tendsto (fun n => (∫⁻ x, ‖h n x • g x‖ₑ ^ p ∂μ) ^ (1 / p)) atTop (𝓝 0) := by
    have h2 := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0 |>.comp hint
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h2
  refine h1.congr fun n => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]

/-- **Convergence of products in `L^p`**: if `a_n → a` a.e. with `|a_n|, |a| ≤ L`, and `b_n → b`
in `L^p`, then `a_n b_n → a b` in `L^p`. -/
theorem tendsto_eLpNorm_smul_sub_smul {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ} (hp : 1 < p) {a : ℕ → α → ℝ} {al : α → ℝ}
    {b : ℕ → α → E} {bl : α → E} (hbl : MemLp bl (ENNReal.ofReal p) μ) {L : ℝ}
    (ha : ∀ n x, |a n x| ≤ L) (hal : ∀ x, |al x| ≤ L) (ham : ∀ n, AEStronglyMeasurable (a n) μ)
    (halm : AEStronglyMeasurable al μ) (hbm : ∀ n, AEStronglyMeasurable (b n) μ)
    (hlima : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (al x)))
    (hlimb : Tendsto (fun n => eLpNorm (b n - bl) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((fun x => a n x • b n x) - fun x => al x • bl x)
      (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hsplit : ∀ n, ((fun x => a n x • b n x) - fun x => al x • bl x) =
      (fun x => a n x • (b n x - bl x)) + fun x => (a n x - al x) • bl x := by
    intro n
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, smul_sub, sub_smul]
    abel
  have h1 : Tendsto (fun n => eLpNorm (fun x => a n x • (b n x - bl x)) (ENNReal.ofReal p) μ)
      atTop (𝓝 0) := by
    have hle : ∀ n, eLpNorm (fun x => a n x • (b n x - bl x)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max L 0) * eLpNorm (b n - bl) (ENNReal.ofReal p) μ := fun n =>
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => by
        show ‖a n x • (b n x - bl x)‖ ≤ max L 0 * ‖(b n - bl) x‖
        rw [norm_smul, Real.norm_eq_abs, Pi.sub_apply]
        exact mul_le_mul_of_nonneg_right ((ha n x).trans (le_max_left _ _)) (norm_nonneg _)) _
    have hlim := ENNReal.Tendsto.const_mul hlimb (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (max L 0))
    rw [mul_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      hle
  have h2 : Tendsto (fun n => eLpNorm (fun x => (a n x - al x) • bl x) (ENNReal.ofReal p) μ)
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_smul_of_tendsto_ae hp0 hbl (L := 2 * max L 0) (fun n x => ?_)
      (fun n => (ham n).sub halm) (hlima.mono fun x hx => by simpa using hx.sub_const (al x))
    calc |a n x - al x| ≤ |a n x| + |al x| := abs_sub _ _
      _ ≤ max L 0 + max L 0 :=
          add_le_add ((ha n x).trans (le_max_left _ _)) ((hal x).trans (le_max_left _ _))
      _ = 2 * max L 0 := by ring
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
    fun n => ?_
  rw [hsplit n]
  exact eLpNorm_add_le ((ham n).smul ((hbm n).sub hbl.1)) (((ham n).sub halm).smul hbl.1) hp1

/-! ### The chain rule -/

/-- **Chain rule in `W₀^{1,p}(K)`** (Gilbarg–Trudinger, *Elliptic Partial Differential Equations
of Second Order*, Lemma 7.5; Ziemer, *Weakly Differentiable Functions*, Theorem 2.1.11): if
`G ∈ C¹(ℝ)` has bounded derivative and `G(0) = 0`, and `f ∈ W₀^{1,p}(K)`, then
`G ∘ f ∈ W₀^{1,p}(K)` with weak gradient `G'(f) ∇f`. Used with truncated powers `G` in the Moser
iteration (`IsWeakEigensolution.exists_ae_le`).

Proof: the mollifications `v_n = ρ_n ⋆ f` are smooth, `v_n → f` and `∇v_n = ρ_n ⋆ ∇f → ∇f` in `L^p`;
along an a.e.-convergent subsequence, `G(v_n) → G(f)` in `L^p` (`G` is Lipschitz) and
`G'(v_n) ∇v_n → G'(f) ∇f` in `L^p` (`tendsto_eLpNorm_smul_sub_smul`), and `G'(v_n) ∇v_n` is the
classical, hence weak, gradient of `G(v_n)`; `HasWeakGradient.of_tendsto` concludes. -/
theorem memW0_comp {p : ℝ} (hp : 1 < p) {K : Set (Euc d)} {f : Euc d → ℝ} (hf : MemW0 p K f)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) {L : ℝ} (hGL : ∀ t, |deriv G t| ≤ L) :
    MemW0 p K (fun x => G (f x)) ∧
      weakGrad (fun x => G (f x)) =ᵐ[volume] fun x => deriv G (f x) • weakGrad f x := by
  have hp0 : 0 < p := by linarith
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hdG : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hLip : ∀ s t : ℝ, |G s - G t| ≤ L * |s - t| := fun s t => by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := G) (fun x _ => hGd x)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hGL x) (mem_univ t) (mem_univ s)
    simpa only [Real.norm_eq_abs] using h
  have hg : HasWeakGradient f (weakGrad f) := hf.hasWeakGradient
  have hgp : MemLp (weakGrad f) (ENNReal.ofReal p) := hf.memLp_weakGrad
  have hGfm : MemLp (fun x => G (f x)) (ENNReal.ofReal p) :=
    hf.memLp.of_le_mul (c := L) (hG.continuous.comp_aestronglyMeasurable hf.memLp.1)
      (Eventually.of_forall fun x => by
        have h := hLip (f x) 0
        rw [hG0, sub_zero, sub_zero] at h
        simpa only [Real.norm_eq_abs] using h)
  have hgl : MemLp (fun x => deriv G (f x) • weakGrad f x) (ENNReal.ofReal p) :=
    hgp.of_le_mul (c := L) ((hdG.comp_aestronglyMeasurable hf.memLp.1).smul hgp.1)
      (Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hGL _) (norm_nonneg _))
  -- the mollified sequence
  have hrOut : Tendsto (fun n => (mollifierBump (d := d) n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hvc : ∀ n, ContDiff ℝ 1 (mollifyWith ((mollifierBump n).normed volume) f) := fun n =>
    (contDiff_mollifyWith (n := ⊤) (ContDiffBump.contDiff_normed _)
      (mollifierBump n).hasCompactSupport_normed hg.locallyIntegrable).of_le
      (by exact_mod_cast le_top)
  have hvf : Tendsto (fun n => eLpNorm (mollifyWith ((mollifierBump n).normed volume) f - f)
      (ENNReal.ofReal p)) atTop (𝓝 0) :=
    tendsto_eLpNorm_mollifyWith_sub hrOut hp hf.memLp
  have hgg : Tendsto (fun n => eLpNorm (gradient (mollifyWith ((mollifierBump n).normed volume) f) -
      weakGrad f) (ENNReal.ofReal p)) atTop (𝓝 0) := by
    simp only [gradient_mollifyWith hg (ContDiffBump.contDiff_normed _)
      (ContDiffBump.hasCompactSupport_normed _)]
    exact tendsto_eLpNorm_mollifyWith_sub hrOut hp hgp
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp'
    (fun n => (hvc n).continuous.aestronglyMeasurable) hf.memLp.aestronglyMeasurable
    hvf).exists_seq_tendsto_ae
  have hwg : HasWeakGradient (fun x => G (f x)) (fun x => deriv G (f x) • weakGrad f x) := by
    refine HasWeakGradient.of_tendsto hp
      (u := fun i x => G (mollifyWith ((mollifierBump (ns i)).normed volume) f x))
      (G := fun i x => deriv G (mollifyWith ((mollifierBump (ns i)).normed volume) f x) •
        gradient (mollifyWith ((mollifierBump (ns i)).normed volume) f) x)
      (fun i => ?_) hGfm hgl ?_ ?_
    · have hc : ContDiff ℝ 1 fun x => G (mollifyWith ((mollifierBump (ns i)).normed volume) f x) :=
        hG.comp (hvc (ns i))
      refine (hasWeakGradient_gradient_of_contDiff hc).congr_right
        (Eventually.of_forall fun x => ?_)
      exact gradient_comp_apply hGd ((hvc (ns i)).differentiable one_ne_zero x)
    · have hlim : Tendsto (fun i => ENNReal.ofReal L *
          eLpNorm (mollifyWith ((mollifierBump (ns i)).normed volume) f - f) (ENNReal.ofReal p))
          atTop (𝓝 0) := by
        have h := ENNReal.Tendsto.const_mul (hvf.comp hns.tendsto_atTop)
          (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal L)
        rw [mul_zero] at h
        exact h
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
        fun i => ?_
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) _
      show ‖G (mollifyWith ((mollifierBump (ns i)).normed volume) f x) - G (f x)‖ ≤
        L * ‖mollifyWith ((mollifierBump (ns i)).normed volume) f x - f x‖
      simpa only [Real.norm_eq_abs] using hLip _ (f x)
    · exact tendsto_eLpNorm_smul_sub_smul hp hgp (L := L)
        (a := fun n x => deriv G (mollifyWith ((mollifierBump (ns n)).normed volume) f x))
        (b := fun n => gradient (mollifyWith ((mollifierBump (ns n)).normed volume) f))
        (al := fun x => deriv G (f x)) (bl := weakGrad f)
        (fun n x => hGL _) (fun x => hGL _)
        (fun n => hdG.comp_aestronglyMeasurable (hvc (ns n)).continuous.aestronglyMeasurable)
        (hdG.comp_aestronglyMeasurable hf.memLp.1)
        (fun n => (continuous_gradient (hvc (ns n))).aestronglyMeasurable)
        (hae.mono fun x hx => (hdG.tendsto (f x)).comp hx)
        (hgg.comp hns.tendsto_atTop)
  refine ⟨⟨hGfm, ?_, _, hwg, hgl⟩, hwg.weakGrad_ae_eq⟩
  filter_upwards [hf.ae_eq_zero] with x hx hxK
  simp only [hx hxK, hG0]

end Komlos.Literature
