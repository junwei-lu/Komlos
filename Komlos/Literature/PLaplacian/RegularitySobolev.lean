import Komlos.Literature.PLaplacian.Eigenfunction

/-!
# The Sobolev inequality on `W₀^{1,p}(K)`

For a bounded set `K ⊆ ℝ^d` (`d ≥ 1`) and `p > 1` there are `κ > 1` and `C < ∞` with
`‖w‖_{L^{κp}} ≤ C ‖∇w‖_{L^p}` for all `w ∈ W₀^{1,p}(K)` (`sobolev_inequality`; Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Theorem 7.10). It is the integrability
gain behind the Moser iteration of `Komlos.Literature.PLaplacian.RegularityInterior` (global
boundedness of the first eigenfunction, towards Mosconi–Riey–Squassina 2024, Proposition 4.5; paper
Appendix A, *Eigenfunction inputs*).

## Proof

* `d ≥ 2`: Mathlib's Gagliardo–Nirenberg–Sobolev inequality for `C¹` functions with bounded
  support (`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`) at an exponent `1 ≤ p₀ ≤ p`, `p₀ < d`
  (`exists_sobolev_exponents`), followed by Hölder on the ball (`exists_sobolev_smooth_of_two_le`).
* `d = 1`: the smooth case is `exists_sobolev_smooth_one`.
* Passage to `W₀^{1,p}(K)` by mollification and Fatou, as for the Poincaré inequality
  `MemW0.eLpNorm_le_eLpNorm_weakGrad` (`MemW0.eLpNorm_le_of_smooth`).
-/

open MeasureTheory Set Filter Topology Module
open scoped ENNReal NNReal Convolution

namespace Komlos.Literature

variable {d : ℕ}

/-- The Fréchet derivative and the gradient have the same pointwise norms, hence the same `L^q`
norms. -/
theorem eLpNorm_fderiv_eq_eLpNorm_gradient (w : Euc d → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fderiv ℝ w) q volume = eLpNorm (gradient w) q volume :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
    rw [gradient, LinearIsometryEquiv.norm_map])

/-- Admissible exponents for the Gagliardo–Nirenberg–Sobolev inequality: for `d ≥ 2` and `p > 1`
there are `1 ≤ p₀ ≤ p` with `p₀ < d` and `κ > 1` with `1/p₀ - 1/d ≤ 1/(κp)` (`p₀ = p`,
`κ = d/(d-p)` if `p < d`; `p₀ = 2pd/(2p+d)`, `κ = 2` otherwise). -/
theorem exists_sobolev_exponents (hd : 2 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ p₀ κ : ℝ, 1 ≤ p₀ ∧ p₀ ≤ p ∧ p₀ < d ∧ 1 < κ ∧ p₀⁻¹ - (d : ℝ)⁻¹ ≤ (κ * p)⁻¹ := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  rcases lt_or_ge p d with hpd | hpd
  · have hdp : 0 < (d : ℝ) - p := by linarith
    refine ⟨p, d / (d - p), hp.le, le_rfl, hpd, ?_, le_of_eq ?_⟩
    · rw [lt_div_iff₀ hdp]
      linarith
    · field_simp
  · have hs : (0 : ℝ) < 2 * p + d := by linarith
    refine ⟨2 * p * d / (2 * p + d), 2, ?_, ?_, ?_, by norm_num, le_of_eq ?_⟩
    · rw [le_div_iff₀ hs]
      nlinarith [mul_nonneg (sub_nonneg.2 hp.le) (sub_nonneg.2 hd')]
    · rw [div_le_iff₀ hs]
      nlinarith
    · rw [div_lt_iff₀ hs]
      nlinarith
    · field_simp
      ring

/-- **Sobolev inequality for smooth functions, `d ≥ 2`**: for `p > 1` and `R` there are `κ > 1`
and `C < ∞` with `‖w‖_{L^{κp}} ≤ C ‖∇w‖_{L^p}` for every `C¹` function `w` supported in the ball
`closedBall 0 R` (Gagliardo–Nirenberg–Sobolev at the exponent of `exists_sobolev_exponents`, then
Hölder on the ball). -/
theorem exists_sobolev_smooth_of_two_le (hd : 2 ≤ d) {p : ℝ} (hp : 1 < p) (R : ℝ) :
    ∃ κ : ℝ, 1 < κ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : Euc d → ℝ, ContDiff ℝ 1 w →
      tsupport w ⊆ Metric.closedBall 0 R →
      eLpNorm w (ENNReal.ofReal (κ * p)) ≤ C * eLpNorm (gradient w) (ENNReal.ofReal p) := by
  obtain ⟨p₀, κ, hp₀1, hp₀p, hp₀d, hκ, hexp⟩ := exists_sobolev_exponents hd hp
  have hp0 : 0 < p := by linarith
  have hp₀0 : 0 < p₀ := by linarith
  have hκp : 0 < κ * p := mul_pos (by linarith) hp0
  have hfin : finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  have hBb : Bornology.IsBounded (Metric.closedBall (0 : Euc d) R) := Metric.isBounded_closedBall
  have hBfin : volume (Metric.closedBall (0 : Euc d) R) ≠ ⊤ := measure_closedBall_lt_top.ne
  have he0 : 0 ≤ 1 / p₀ - 1 / p := sub_nonneg.2 (one_div_le_one_div_of_le hp₀0 hp₀p)
  refine ⟨κ, hκ, (eLpNormLESNormFDerivOfLeConst ℝ volume (Metric.closedBall (0 : Euc d) R)
    p₀.toNNReal (κ * p).toNNReal : ℝ≥0∞) *
      volume (Metric.closedBall (0 : Euc d) R) ^ (1 / p₀ - 1 / p),
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.rpow_ne_top_of_nonneg he0 hBfin),
    fun w hw hwB => ?_⟩
  have hsupp : Function.support w ⊆ Metric.closedBall 0 R := (subset_tsupport w).trans hwB
  have h1 : (1 : ℝ≥0) ≤ p₀.toNNReal := by simpa using Real.toNNReal_le_toNNReal hp₀1
  have h2 : p₀.toNNReal < (finrank ℝ (Euc d) : ℝ≥0) := by
    rw [hfin, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hp₀0.le]
    exact_mod_cast hp₀d
  have h3 : ((p₀.toNNReal)⁻¹ : ℝ≥0) - ((finrank ℝ (Euc d) : ℕ) : ℝ)⁻¹ ≤
      (((κ * p).toNNReal : ℝ≥0) : ℝ)⁻¹ := by
    rw [hfin, NNReal.coe_inv, Real.coe_toNNReal _ hp₀0.le, Real.coe_toNNReal _ hκp.le]
    exact hexp
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_le (F := ℝ) volume hw hsupp h1 h2 h3 hBb
  -- Hölder on the ball for the gradient
  have hgsupp : Function.support (gradient w) ⊆ Metric.closedBall 0 R := fun x hx => by
    by_contra h
    exact hx (gradient_eq_zero_of_notMem_tsupport fun h' => h (hwB h'))
  have hgm : AEStronglyMeasurable (gradient w) (volume.restrict (Metric.closedBall 0 R)) :=
    (continuous_gradient hw).aestronglyMeasurable
  have hle : ENNReal.ofReal p₀ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp₀p
  have hholder : eLpNorm (gradient w) (ENNReal.ofReal p₀) volume ≤
      eLpNorm (gradient w) (ENNReal.ofReal p) volume *
        volume (Metric.closedBall (0 : Euc d) R) ^ (1 / p₀ - 1 / p) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hle hgm
    rw [eLpNorm_restrict_eq_of_support_subset hgsupp, eLpNorm_restrict_eq_of_support_subset hgsupp,
      Measure.restrict_apply_univ, ENNReal.toReal_ofReal hp₀0.le,
      ENNReal.toReal_ofReal hp0.le] at h
    exact h
  have hfd : eLpNorm (fderiv ℝ w) ((p₀.toNNReal : ℝ≥0) : ℝ≥0∞) volume =
      eLpNorm (gradient w) (ENNReal.ofReal p₀) volume :=
    eLpNorm_fderiv_eq_eLpNorm_gradient w _
  refine hgns.trans ?_
  rw [hfd, mul_assoc]
  exact mul_le_mul_right (hholder.trans (le_of_eq (mul_comm _ _))) _

/-- The unit vector `e₁ = (1)` of `ℝ¹` has norm `1`. -/
theorem norm_toLp_one_fin_one : ‖(WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : Euc 1)‖ = 1 := by
  simp [EuclideanSpace.norm_eq]

/-- **Integration along the line in dimension one**: `∫ g(x + t e₁) dt = ∫ g` on `ℝ¹` (the map
`t ↦ t e₁` is volume preserving, `PiLp.volume_preserving_toLp`, and Lebesgue measure is translation
invariant). -/
theorem lintegral_line_eq_lintegral_one {g : Euc 1 → ℝ≥0∞} (hg : Measurable g) (x : Euc 1) :
    ∫⁻ t : ℝ, g (x + t • (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : Euc 1)) = ∫⁻ y, g y := by
  have hψ : MeasurePreserving (fun t : ℝ =>
      (WithLp.toLp 2 ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm t) : Euc 1)) volume volume :=
    (PiLp.volume_preserving_toLp (Fin 1)).comp ((volume_preserving_funUnique (Fin 1) ℝ).symm _)
  have hψe : ∀ t : ℝ, (WithLp.toLp 2 ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm t) : Euc 1) =
      t • (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : Euc 1) := by
    intro t
    refine PiLp.ext fun i => ?_
    have hi : i = default := Subsingleton.elim _ _
    subst hi
    simp
  calc ∫⁻ t : ℝ, g (x + t • (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : Euc 1))
      = ∫⁻ t : ℝ,
          g (x + (WithLp.toLp 2 ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm t) : Euc 1)) := by
        simp only [hψe]
    _ = ∫⁻ y, g (x + y) :=
        hψ.lintegral_comp (f := fun y => g (x + y)) (hg.comp (measurable_const_add x))
    _ = ∫⁻ y, g y := lintegral_add_left_eq_self g x

/-- `∫ f^{2p} ≤ S^p ∫ f^p` when `f ≤ S` (`p > 0`). -/
theorem lintegral_rpow_two_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {S : ℝ≥0∞} (hS : S ≠ ⊤) {p : ℝ} (hp0 : 0 < p) (hf : ∀ x, f x ≤ S) :
    ∫⁻ x, f x ^ (2 * p) ∂μ ≤ S ^ p * ∫⁻ x, f x ^ p ∂μ := by
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le hS)]
  refine lintegral_mono fun x => ?_
  rw [two_mul, ENNReal.rpow_add_of_nonneg _ _ hp0.le hp0.le]
  exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hf x) hp0.le) zero_le

/-- `X^{2p} ≤ A^p N^{2p}` implies `X ≤ A^{1/2} N` in `ℝ≥0∞` (`p > 0`). -/
theorem le_rpow_half_mul_of_rpow_two_mul_le {X N A : ℝ≥0∞} {p : ℝ} (hp0 : 0 < p)
    (h : X ^ (2 * p) ≤ A ^ p * N ^ (2 * p)) : X ≤ A ^ (1 / 2 : ℝ) * N := by
  have hp2 : 0 < 2 * p := by linarith
  rw [← ENNReal.rpow_le_rpow_iff hp2, ENNReal.mul_rpow_of_nonneg _ _ hp2.le, ← ENNReal.rpow_mul]
  have he : (1 / 2 : ℝ) * (2 * p) = p := by ring
  rw [he]
  exact h

/-- **The sup bound in dimension one**: `|w(x)| ≤ ‖w'‖_{L^p} |B|^{1-1/p}` for a `C¹` function `w`
supported in the ball `B = closedBall 0 R` (the fundamental theorem of calculus along the line,
`enorm_le_lintegral_gradient_line`, `lintegral_line_eq_lintegral_one`, and Hölder on `B`). -/
theorem enorm_le_eLpNorm_gradient_one {p : ℝ} (hp : 1 < p) {R : ℝ} {w : Euc 1 → ℝ}
    (hw : ContDiff ℝ 1 w) (hwB : tsupport w ⊆ Metric.closedBall 0 R) (x : Euc 1) :
    ‖w x‖ₑ ≤ eLpNorm (gradient w) (ENNReal.ofReal p) *
      volume (Metric.closedBall (0 : Euc 1) R) ^ (1 - 1 / p) := by
  have hp0 : 0 < p := by linarith
  have hgsupp : Function.support (gradient w) ⊆ Metric.closedBall 0 R := fun y hy => by
    by_contra h
    exact hy (gradient_eq_zero_of_notMem_tsupport fun h' => h (hwB h'))
  have hL1 : ∫⁻ y, ‖gradient w y‖ₑ ≤ eLpNorm (gradient w) (ENNReal.ofReal p) *
      volume (Metric.closedBall (0 : Euc 1) R) ^ (1 - 1 / p) := by
    have hgm : AEStronglyMeasurable (gradient w)
        (volume.restrict (Metric.closedBall (0 : Euc 1) R)) :=
      (continuous_gradient hw).aestronglyMeasurable
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := ENNReal.ofReal p)
      (ENNReal.one_le_ofReal.2 hp.le) hgm
    rw [eLpNorm_restrict_eq_of_support_subset hgsupp, eLpNorm_restrict_eq_of_support_subset hgsupp,
      Measure.restrict_apply_univ, eLpNorm_one_eq_lintegral_enorm, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hp0.le, div_one] at h
    exact h
  have h1 := enorm_le_lintegral_gradient_line hw hwB norm_toLp_one_fin_one
    (show 2 * R < 2 * R + 1 by linarith) x
  exact h1.trans ((setLIntegral_le_lintegral _ _).trans
    ((lintegral_line_eq_lintegral_one
      (continuous_enorm.comp (continuous_gradient hw)).measurable x).le.trans hL1))

/-- **Sobolev inequality for smooth functions, `d = 1`**: `‖w‖_{L^{2p}} ≤ C ‖w'‖_{L^p}` for `C¹`
functions `w` supported in `closedBall 0 R`. Proof: the sup bound `enorm_le_eLpNorm_gradient_one`
gives `∫ |w|^{2p} ≤ sup |w|^p ∫ |w|^p`, and the Poincaré inequality bounds `∫ |w|^p`. -/
theorem exists_sobolev_smooth_one {p : ℝ} (hp : 1 < p) (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : Euc 1 → ℝ, ContDiff ℝ 1 w →
      tsupport w ⊆ Metric.closedBall 0 R →
      eLpNorm w (ENNReal.ofReal (2 * p)) ≤ C * eLpNorm (gradient w) (ENNReal.ofReal p) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < 2 * p := by linarith
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = volume (Metric.closedBall (0 : Euc 1) |R|) := ⟨_, rfl⟩
  have hVfin : V ≠ ⊤ := by
    rw [hV]
    exact measure_closedBall_lt_top.ne
  have hep : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]
    exact hp.le
  refine ⟨(V ^ (1 - 1 / p) * ENNReal.ofReal (2 * |R| + 1)) ^ (1 / 2 : ℝ),
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hep hVfin) ENNReal.ofReal_ne_top),
    fun w hw hwB => ?_⟩
  have hwB' : tsupport w ⊆ Metric.closedBall 0 |R| :=
    hwB.trans (Metric.closedBall_subset_closedBall (le_abs_self R))
  have hws : HasCompactSupport w :=
    (isCompact_closedBall 0 |R|).of_isClosed_subset (isClosed_tsupport w) hwB'
  obtain ⟨N, hN⟩ : ∃ N : ℝ≥0∞, N = eLpNorm (gradient w) (ENNReal.ofReal p) := ⟨_, rfl⟩
  have hNfin : N ≠ ⊤ := by
    rw [hN]
    exact ((continuous_gradient hw).memLp_of_hasCompactSupport
      (hasCompactSupport_gradient hws)).eLpNorm_ne_top
  have hsup : ∀ x, ‖w x‖ₑ ≤ N * V ^ (1 - 1 / p) := fun x => by
    rw [hN, hV]
    exact enorm_le_eLpNorm_gradient_one hp hw hwB' x
  have hpoin : ∫⁻ x, ‖w x‖ₑ ^ p ≤ ENNReal.ofReal (2 * |R| + 1) ^ p * N ^ p := by
    rw [hN, ← lintegral_enorm_rpow_eq_eLpNorm_rpow hp0]
    exact lintegral_rpow_le_lintegral_rpow_gradient one_pos (abs_nonneg R) hw hwB' hp
      (by linarith)
  have h1 := lintegral_rpow_two_mul_le (μ := volume)
    (ENNReal.mul_ne_top hNfin (ENNReal.rpow_ne_top_of_nonneg hep hVfin)) hp0 hsup
  have hN2 : N ^ (2 * p) = N ^ p * N ^ p := by
    rw [two_mul, ENNReal.rpow_add_of_nonneg _ _ hp0.le hp0.le]
  have h2 : ∫⁻ x, ‖w x‖ₑ ^ (2 * p) ≤
      (V ^ (1 - 1 / p) * ENNReal.ofReal (2 * |R| + 1)) ^ p * N ^ (2 * p) := by
    refine h1.trans ((mul_le_mul_of_nonneg_left hpoin zero_le).trans (le_of_eq ?_))
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hN2]
    ring
  rw [← hN]
  refine le_rpow_half_mul_of_rpow_two_mul_le hp0 ?_
  rw [← lintegral_enorm_rpow_eq_eLpNorm_rpow hp2]
  exact h2

/-- **Sobolev inequality for smooth functions** (`d ≥ 1`). -/
theorem exists_sobolev_smooth (hd : 0 < d) {p : ℝ} (hp : 1 < p) (R : ℝ) :
    ∃ κ : ℝ, 1 < κ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : Euc d → ℝ, ContDiff ℝ 1 w →
      tsupport w ⊆ Metric.closedBall 0 R →
      eLpNorm w (ENNReal.ofReal (κ * p)) ≤ C * eLpNorm (gradient w) (ENNReal.ofReal p) := by
  obtain rfl | hd2 : d = 1 ∨ 2 ≤ d := by omega
  · obtain ⟨C, hC, h⟩ := exists_sobolev_smooth_one hp R
    exact ⟨2, by norm_num, C, hC, h⟩
  · exact exists_sobolev_smooth_of_two_le hd2 hp R

/-- **Passage from smooth functions to `W₀^{1,p}(K)`** (mollification and Fatou, as in
`MemW0.eLpNorm_le_eLpNorm_weakGrad`): a Sobolev inequality for `C¹` functions supported in
`closedBall 0 (R + 1)` holds for all `f ∈ W₀^{1,p}(K)` when `K ⊆ closedBall 0 R`. -/
theorem MemW0.eLpNorm_le_of_smooth {p : ℝ} (hp : 1 < p) {K : Set (Euc d)} {R : ℝ} (hR : 0 ≤ R)
    (hK : K ⊆ Metric.closedBall 0 R) {q : ℝ≥0∞} {C : ℝ≥0∞}
    (hsmooth : ∀ w : Euc d → ℝ, ContDiff ℝ 1 w → tsupport w ⊆ Metric.closedBall 0 (R + 1) →
      eLpNorm w q ≤ C * eLpNorm (gradient w) (ENNReal.ofReal p))
    {f : Euc d → ℝ} (hf : MemW0 p K f) :
    eLpNorm f q ≤ C * eLpNorm (weakGrad f) (ENNReal.ofReal p) := by
  set g := weakGrad f with hg_def
  have hg : HasWeakGradient f g := hf.hasWeakGradient
  have hgp : MemLp g (ENNReal.ofReal p) := hf.memLp_weakGrad
  -- a representative supported in the ball
  set f' := (Metric.closedBall (0 : Euc d) R).indicator f with hf'_def
  have hff' : f =ᵐ[volume] f' := by
    filter_upwards [hf.ae_eq_zero] with x hx
    by_cases hxR : x ∈ Metric.closedBall (0 : Euc d) R
    · simp [hf'_def, Set.indicator_of_mem hxR]
    · simp [hf'_def, Set.indicator_of_notMem hxR, hx fun hxK => hxR (hK hxK)]
  have hg' : HasWeakGradient f' g := hg.congr_left hff'
  have hsupp' : Function.support f' ⊆ Metric.closedBall 0 R := fun x hx => by
    by_contra h
    exact hx (Set.indicator_of_notMem h f)
  -- the mollified sequence
  set ρ : ℕ → Euc d → ℝ := fun n => (mollifierBump n).normed volume with hρ_def
  set u : ℕ → Euc d → ℝ := fun n => f' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ n with hu_def
  have hu_smooth : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    (mollifierBump n).hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hg'.locallyIntegrable (ContDiffBump.contDiff_normed _)
  have hu_supp : ∀ n, tsupport (u n) ⊆ Metric.closedBall 0 (R + 1) := fun n => by
    have h1 : tsupport (u n) ⊆ Metric.closedBall 0 (R + 1 / ((n : ℝ) + 1)) :=
      tsupport_convolution_subset_closedBall hR (by positivity) hsupp'
        (by rw [ContDiffBump.support_normed_eq]; exact Metric.ball_subset_closedBall)
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact h1.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hu_grad : ∀ n, gradient (u n) = mollifyWith (ρ n) g := fun n => funext fun x =>
    gradient_convolution_eq hg' (ContDiffBump.contDiff_normed _)
      (mollifierBump n).hasCompactSupport_normed x
  have hG_le : ∀ n, eLpNorm (gradient (u n)) (ENNReal.ofReal p) ≤ eLpNorm g (ENNReal.ofReal p) :=
    fun n => by
      rw [hu_grad n]
      exact eLpNorm_mollifyWith_le hgp.aestronglyMeasurable (ContDiffBump.continuous_normed _)
        (ContDiffBump.nonneg_normed _) (ContDiffBump.integrable_normed _)
        (ContDiffBump.integral_normed _) hp
  have hbound : ∀ n, eLpNorm (u n) q ≤ C * eLpNorm g (ENNReal.ofReal p) := fun n =>
    (hsmooth _ (hu_smooth n) (hu_supp n)).trans (mul_le_mul_right (hG_le n) C)
  -- Fatou
  have hae := ae_tendsto_convolution_stdBump hg'.locallyIntegrable
  have hfatou : eLpNorm f' q ≤ liminf (fun n => eLpNorm (u n) q) atTop :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hu_smooth n).continuous.aestronglyMeasurable) f'
      hae
  rw [eLpNorm_congr_ae hff']
  exact hfatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))

/-- **Sobolev inequality on `W₀^{1,p}(K)`** for bounded `K` (Gagliardo–Nirenberg–Sobolev; Gilbarg–
Trudinger, Theorem 7.10): there are `κ > 1` and `C < ∞` with `‖w‖_{L^{κp}} ≤ C ‖∇w‖_{L^p}` for all
`w ∈ W₀^{1,p}(K)` (`κ = d/(d-p)` if `p < d`). Proof: `exists_sobolev_smooth` on the ball of radius
`R + 1` and `MemW0.eLpNorm_le_of_smooth`. -/
theorem sobolev_inequality (hd : 0 < d) {p : ℝ} (hp : 1 < p) {K : Set (Euc d)}
    (hK : Bornology.IsBounded K) :
    ∃ κ : ℝ, 1 < κ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : Euc d → ℝ, MemW0 p K w →
      eLpNorm w (ENNReal.ofReal (κ * p)) ≤ C * eLpNorm (weakGrad w) (ENNReal.ofReal p) := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : Euc d)
  have hR' : K ⊆ Metric.closedBall 0 |R| :=
    hR.trans (Metric.closedBall_subset_closedBall (le_abs_self R))
  obtain ⟨κ, hκ, C, hC, hsmooth⟩ := exists_sobolev_smooth hd hp (|R| + 1)
  exact ⟨κ, hκ, C, hC, fun w hw => hw.eLpNorm_le_of_smooth hp (abs_nonneg R) hR' hsmooth⟩

end Komlos.Literature
