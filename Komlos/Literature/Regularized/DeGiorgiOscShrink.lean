import Komlos.Literature.Regularized.DeGiorgiOscAux

/-!
# De Giorgi's measure-shrinking lemma

De Giorgi's *second* lemma for the class `DG⁺` of
`Komlos/Literature/Regularized/DeGiorgiClass.lean`: if `z ∈ DG⁺(Ω, γ, χ)` satisfies
`z ≤ M` on `B_{3ρ/2}` and is below the midpoint `M - om/2` on at least half of `B_ρ`, then the
level sets `{z > k_j}` with the geometric ladder `k_j = M - 2^{-j} om/2` have measures tending to
`0` at a rate depending only on `d` and `γ` — provided the lower-order datum satisfies
`χ ρ ≤ 2^{-s} om` at the last level used.

The mechanism (Ladyzhenskaya–Ural'tseva, Ch. II, Lemma 3.9 and §6; Giusti, *Direct Methods*,
Lemma 7.2 and Theorem 7.3) is the isoperimetric inequality of
`Komlos/Literature/Regularized/DeGiorgiOscAux.lean` at the exponent `p = 3/2`, combined with
Hölder (`lintegral_rpow_le_rpow_lintegral_sq`) and the `(DG)` energy inequality at the level
`k_j`: the factor `2^{-j}` of the level gap is exactly cancelled by the factor `2^{-j}` coming
from `(∫_{ {z>k_j} } ‖∇z‖²)^{3/4}`, so that

`|A_{j+1}|⁴ ≤ C |B_ρ|³ |A_j ∖ A_{j+1}|`   (`dg_shrink_step`)

with a `j`-independent `C`.  The sets `A_j ∖ A_{j+1}` are disjoint, so summing `s` of these gives
`s |A_s|⁴ ≤ C |B_ρ|⁴` (`dg_shrink_sum`), which is the measure-shrinking statement.

## Main results

* `dg_shrink_step` — one step of the ladder.
* `exists_dg_measure_shrink` — `s |A_s|⁴ ≤ C |B_ρ|⁴` with `C = C(d, γ)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Real-power bookkeeping -/

/-- `(x^a)^n = x^m` when `a n = m`. -/
theorem rpow_natCast_pow {x a : ℝ} (hx : 0 ≤ x) {n m : ℕ} (h : a * n = m) :
    (x ^ a) ^ n = x ^ m := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx, h, Real.rpow_natCast]

/-- The square of the norm of a field, as a lower Lebesgue integral. -/
theorem dgosc_lintegral_enorm_rpow_two_eq {A : Set (Euc d)} {G : Euc d → Euc d}
    (h : IntegrableOn (fun x => ‖G x‖ ^ 2) A volume) :
    ∫⁻ x in A, ‖G x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∫ x in A, ‖G x‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm (G x),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ### One step of the ladder -/

/-- **One step of De Giorgi's measure-shrinking lemma.**  For `z ∈ DG⁺(Ω, γ, χ)` bounded above by
`M` on `B_{3ρ/2}`, with `χ ρ ≤ τ` and `|B_ρ ∩ {z ≤ M - τ/2}| ≥ |B_ρ|/2`,

`|B_ρ ∩ {z > M - τ/4}|⁴ ≤ 2^{25} (2^d)⁴ γ³ ((3/2)^d)³ |B_ρ|³ |B_ρ ∩ {M - τ/2 < z ≤ M - τ/4}|`.

The right-hand side does not involve `τ`: the level gap `τ/4` and the energy of `z` above the
level `M - τ/2`, which the `(DG)` inequality bounds by `C τ² |B_ρ|/ρ²`, carry matching powers of
`τ`.  This is what makes the ladder `τ_j = 2^{-j} om` summable. -/
theorem dg_shrink_step {γ χ R₀ : ℝ} (hγ : 0 ≤ γ) (hχ : 0 ≤ χ) {Ω : Set (Euc d)} {z : Euc d → ℝ}
    {G : Euc d → Euc d} (hz : IsDGSub γ χ R₀ Ω z G) {x₀ : Euc d} {ρ : ℝ} (hρ : 0 < ρ)
    (hρR : 3 / 2 * ρ ≤ R₀) (hball : Metric.closedBall x₀ (3 / 2 * ρ) ⊆ Ω) (hd : 0 < d)
    {M τ : ℝ} (hτ : 0 < τ) (hχτ : χ * ρ ≤ τ)
    (hMbd : ∀ᵐ x, x ∈ Metric.closedBall x₀ (3 / 2 * ρ) → z x ≤ M)
    (hhalf : volume (Metric.ball x₀ ρ) ≤
      2 * volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ / 2})) :
    (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal ^ 4 ≤
      2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * γ ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 *
        (volume (Metric.ball x₀ ρ)).toReal ^ 3 *
        (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 2 < z x ∧ z x ≤ M - τ / 4})).toReal := by
  have hk : M - τ / 2 < M - τ / 4 := by linarith
  obtain ⟨hzint, hGint⟩ := hz.integrableOn x₀ (3 / 2 * ρ) hball
  -- volumes
  have hVB : volume (Metric.ball x₀ (3 / 2 * ρ)) =
      ENNReal.ofReal ((3 / 2 : ℝ) ^ d) * volume (Metric.ball x₀ ρ) :=
    volume_ball_mul_eq hd x₀ hρ.le (by norm_num)
  have hBtop : volume (Metric.ball x₀ ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hBpos : volume (Metric.ball x₀ ρ) ≠ 0 := (Metric.measure_ball_pos volume x₀ hρ).ne'
  set V : ℝ := (volume (Metric.ball x₀ ρ)).toReal with hVdef
  have hV0 : 0 < V := ENNReal.toReal_pos hBpos hBtop
  have hVs : (volume (Metric.ball x₀ (3 / 2 * ρ))).toReal = (3 / 2 : ℝ) ^ d * V := by
    rw [hVB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- the energy bound above the level `M - τ/2`
  set Q : ℝ := 2 * γ * (3 / 2 : ℝ) ^ d * V * τ ^ 2 / ρ ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    positivity
  have hEn : ∫ x in Metric.ball x₀ ρ ∩ {x | M - τ / 2 < z x}, ‖G x‖ ^ 2 ≤ Q := by
    have hDG := hz.energy x₀ ρ (3 / 2 * ρ) (M - τ / 2) hρ (by linarith) hρR hball
    have h1 : ∫ x in Metric.ball x₀ (3 / 2 * ρ), max (z x - (M - τ / 2)) 0 ^ 2 ≤
        (τ / 2) ^ 2 * ((3 / 2 : ℝ) ^ d * V) := by
      have hbd : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (3 / 2 * ρ))),
          max (z x - (M - τ / 2)) 0 ^ 2 ≤ (τ / 2) ^ 2 := by
        filter_upwards [ae_restrict_of_ae hMbd, ae_restrict_mem measurableSet_ball] with x hx hxb
        have hzM : z x ≤ M := hx (Metric.ball_subset_closedBall hxb)
        have h2 : max (z x - (M - τ / 2)) 0 ≤ τ / 2 := max_le (by linarith) (by linarith)
        have h3 : (0 : ℝ) ≤ max (z x - (M - τ / 2)) 0 := le_max_right _ _
        nlinarith
      have hmono := integral_mono_of_nonneg
        (Eventually.of_forall fun x => sq_nonneg (max (z x - (M - τ / 2)) 0))
        (integrableOn_const (C := (τ / 2) ^ 2) measure_ball_lt_top.ne) hbd
      rw [setIntegral_const, smul_eq_mul, Measure.real, hVs] at hmono
      calc ∫ x in Metric.ball x₀ (3 / 2 * ρ), max (z x - (M - τ / 2)) 0 ^ 2
          ≤ (3 / 2 : ℝ) ^ d * V * (τ / 2) ^ 2 := hmono
        _ = (τ / 2) ^ 2 * ((3 / 2 : ℝ) ^ d * V) := by ring
    have h2 : (volume (Metric.ball x₀ (3 / 2 * ρ) ∩
        {x | M - τ / 2 < z x})).toReal ≤ (3 / 2 : ℝ) ^ d * V := by
      rw [← hVs]
      exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono inter_subset_left)
    have hχ2 : χ ^ 2 ≤ τ ^ 2 / ρ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul hχτ hχτ (mul_nonneg hχ hρ.le) hτ.le]
    have hc : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ d * V := by positivity
    have hgap : 3 / 2 * ρ - ρ = ρ / 2 := by ring
    rw [hgap] at hDG
    have hfin : γ / (ρ / 2) ^ 2 * ((τ / 2) ^ 2 * ((3 / 2 : ℝ) ^ d * V)) +
        γ * χ ^ 2 * ((3 / 2 : ℝ) ^ d * V) ≤ Q := by
      rw [hQdef]
      have e1 : γ / (ρ / 2) ^ 2 * ((τ / 2) ^ 2 * ((3 / 2 : ℝ) ^ d * V)) =
          γ * (3 / 2 : ℝ) ^ d * V * τ ^ 2 / ρ ^ 2 := by
        field_simp
        try ring
      rw [e1]
      have e2 : γ * χ ^ 2 * ((3 / 2 : ℝ) ^ d * V) ≤ γ * (3 / 2 : ℝ) ^ d * V * τ ^ 2 / ρ ^ 2 := by
        have : γ * χ ^ 2 * ((3 / 2 : ℝ) ^ d * V) ≤ γ * (τ ^ 2 / ρ ^ 2) *
            ((3 / 2 : ℝ) ^ d * V) := by
          have := mul_le_mul_of_nonneg_left hχ2 hγ
          nlinarith
        calc γ * χ ^ 2 * ((3 / 2 : ℝ) ^ d * V)
            ≤ γ * (τ ^ 2 / ρ ^ 2) * ((3 / 2 : ℝ) ^ d * V) := this
          _ = γ * (3 / 2 : ℝ) ^ d * V * τ ^ 2 / ρ ^ 2 := by field_simp; try ring
      have e3 : 2 * γ * (3 / 2 : ℝ) ^ d * V * τ ^ 2 / ρ ^ 2 =
          γ * (3 / 2 : ℝ) ^ d * V * τ ^ 2 / ρ ^ 2 +
            γ * (3 / 2 : ℝ) ^ d * V * τ ^ 2 / ρ ^ 2 := by ring
      rw [e3]
      linarith
    refine hDG.trans (le_trans (add_le_add ?_ ?_) hfin)
    · exact mul_le_mul_of_nonneg_left h1 (by positivity)
    · exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- the isoperimetric inequality at exponent `3/2`
  have hgap2 : M - τ / 4 - (M - τ / 2) = τ / 4 := by ring
  have hiso := measure_mul_measure_le_lintegral_grad_rpow (p := 3 / 2) (by norm_num) (by norm_num)
    hz.hasWeakGradient hz.measurable hz.measurable_grad hρ hzint hGint hk
  rw [hgap2] at hiso
  set S : Set (Euc d) := Metric.ball x₀ ρ ∩ {y | M - τ / 2 < z y ∧ z y ≤ M - τ / 4} with hSdef
  set IS : ℝ≥0∞ := ∫⁻ x in S, ‖G x‖ₑ ^ (3 / 2 : ℝ) with hISdef
  have hSB : S ⊆ Metric.ball x₀ ρ := inter_subset_left
  have hStop : volume S ≠ ⊤ := ((measure_mono hSB).trans_lt measure_ball_lt_top).ne
  -- Hölder between the exponents `3/2` and `2`
  have hhold : IS ≤ ENNReal.ofReal (Q ^ (3 / 4 : ℝ)) * volume S ^ (1 / 4 : ℝ) := by
    have h1 := lintegral_rpow_le_rpow_lintegral_sq (μ := volume) S
      (hz.measurable_grad.enorm.aemeasurable) (p := 3 / 2) (by norm_num) (by norm_num)
    have ea : (3 / 2 : ℝ) / 2 = 3 / 4 := by norm_num
    have eb : (1 : ℝ) - 3 / 4 = 1 / 4 := by norm_num
    rw [ea, eb] at h1
    have hsub : S ⊆ Metric.ball x₀ ρ ∩ {x | M - τ / 2 < z x} :=
      fun y hy => ⟨hy.1, hy.2.1⟩
    have hGsub : IntegrableOn (fun x => ‖G x‖ ^ 2)
        (Metric.ball x₀ ρ ∩ {x | M - τ / 2 < z x}) volume :=
      hGint.mono_set (fun y hy =>
        Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hy.1))
    have h2 : ∫⁻ x in S, ‖G x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal Q := by
      calc ∫⁻ x in S, ‖G x‖ₑ ^ (2 : ℝ)
          ≤ ∫⁻ x in Metric.ball x₀ ρ ∩ {x | M - τ / 2 < z x}, ‖G x‖ₑ ^ (2 : ℝ) :=
            lintegral_mono_set hsub
        _ = ENNReal.ofReal (∫ x in Metric.ball x₀ ρ ∩ {x | M - τ / 2 < z x}, ‖G x‖ ^ 2) :=
            dgosc_lintegral_enorm_rpow_two_eq hGsub
        _ ≤ ENNReal.ofReal Q := ENNReal.ofReal_le_ofReal hEn
    refine h1.trans ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg hQ0 (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    gcongr
  have hIStop : IS ≠ ⊤ :=
    ((hhold.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hStop)))).ne
  -- pass to real numbers
  have hτ4 : (0 : ℝ) ≤ τ / 4 := by linarith
  have h2ρ : (0 : ℝ) ≤ 2 * ρ := by linarith
  have hRHStop : (2 : ℝ≥0∞) ^ d * ENNReal.ofReal (2 * ρ) ^ (3 / 2 : ℝ) *
      volume (Metric.ball x₀ ρ) * IS ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)) hBtop) hIStop
  have hisoR : (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 ≤ z x})).toReal *
        ((τ / 4) ^ (3 / 2 : ℝ) *
          (volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ / 2})).toReal) ≤
      (2 : ℝ) ^ d * (2 * ρ) ^ (3 / 2 : ℝ) * V * IS.toReal := by
    have h := ENNReal.toReal_mono hRHStop hiso
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hτ4, ENNReal.toReal_ofReal h2ρ, ENNReal.toReal_ofNat] at h
    rw [hVdef]
    exact h
  have hholdR : IS.toReal ≤ Q ^ (3 / 4 : ℝ) * (volume S).toReal ^ (1 / 4 : ℝ) := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hStop)) hhold
    simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hQ0 (3 / 4 : ℝ))] at h
    exact h
  have hhalfR : V ≤ 2 * (volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ / 2})).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
      (((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne)) hhalf
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h
    rw [hVdef]
    exact h
  have ha1e1 : (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal ≤
      (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 ≤ z x})).toReal :=
    ENNReal.toReal_mono (((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne)
      (measure_mono fun y hy => ⟨hy.1, by
        have hy2 := hy.2
        simp only [Set.mem_ofPred_eq] at hy2 ⊢
        linarith⟩)
  -- the constant
  set yy : ℝ := (2 : ℝ) ^ d * (2 * ρ) ^ (3 / 2 : ℝ) * 2 * Q ^ (3 / 4 : ℝ) with hyydef
  have hyy0 : 0 ≤ yy := by
    rw [hyydef]
    positivity
  have hxx0 : (0 : ℝ) < (τ / 4) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hm0 : (0 : ℝ) ≤ (volume S).toReal := ENNReal.toReal_nonneg
  have ha10 : (0 : ℝ) ≤ (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal :=
    ENNReal.toReal_nonneg
  have hd0 : (0 : ℝ) ≤ (volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ / 2})).toReal :=
    ENNReal.toReal_nonneg
  have his0 : (0 : ℝ) ≤ IS.toReal := ENNReal.toReal_nonneg
  have hcoef : (0 : ℝ) ≤ (2 : ℝ) ^ d * (2 * ρ) ^ (3 / 2 : ℝ) := by positivity
  -- cancel `V`
  have hstep : (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal *
      (τ / 4) ^ (3 / 2 : ℝ) ≤ yy * (volume S).toReal ^ (1 / 4 : ℝ) := by
    have hA : (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal *
        (τ / 4) ^ (3 / 2 : ℝ) * V ≤
        (yy * (volume S).toReal ^ (1 / 4 : ℝ)) * V := by
      have h1 : (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal *
          (τ / 4) ^ (3 / 2 : ℝ) * V ≤
          2 * ((volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 ≤ z x})).toReal *
            ((τ / 4) ^ (3 / 2 : ℝ) *
              (volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ / 2})).toReal)) := by
        have he1 : (0 : ℝ) ≤ (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 ≤ z x})).toReal :=
          ENNReal.toReal_nonneg
        calc (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal *
              (τ / 4) ^ (3 / 2 : ℝ) * V
            ≤ (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 ≤ z x})).toReal *
              (τ / 4) ^ (3 / 2 : ℝ) * V :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right ha1e1 hxx0.le) hV0.le
          _ ≤ (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 ≤ z x})).toReal *
              (τ / 4) ^ (3 / 2 : ℝ) *
              (2 * (volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ / 2})).toReal) :=
              mul_le_mul_of_nonneg_left hhalfR (mul_nonneg he1 hxx0.le)
          _ = 2 * ((volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 ≤ z x})).toReal *
              ((τ / 4) ^ (3 / 2 : ℝ) *
                (volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ / 2})).toReal)) := by ring
      have h2 : 2 * ((volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 ≤ z x})).toReal *
            ((τ / 4) ^ (3 / 2 : ℝ) *
              (volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ / 2})).toReal)) ≤
          2 * ((2 : ℝ) ^ d * (2 * ρ) ^ (3 / 2 : ℝ) * V * IS.toReal) := by linarith
      have h3 : 2 * ((2 : ℝ) ^ d * (2 * ρ) ^ (3 / 2 : ℝ) * V * IS.toReal) ≤
          (yy * (volume S).toReal ^ (1 / 4 : ℝ)) * V := by
        rw [hyydef]
        have := mul_le_mul_of_nonneg_left hholdR (by positivity : (0:ℝ) ≤
          2 * ((2 : ℝ) ^ d * (2 * ρ) ^ (3 / 2 : ℝ)) * V)
        nlinarith [this]
      linarith
    exact le_of_mul_le_mul_right hA hV0
  -- raise to the fourth power
  have h4 := pow_le_pow_left₀ (by positivity) hstep 4
  have eL : ((volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal *
      (τ / 4) ^ (3 / 2 : ℝ)) ^ 4 =
      (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal ^ 4 * (τ / 4) ^ 6 := by
    rw [mul_pow, rpow_natCast_pow hτ4 (by norm_num : (3 / 2 : ℝ) * (4 : ℕ) = (6 : ℕ))]
  have eR : (yy * (volume S).toReal ^ (1 / 4 : ℝ)) ^ 4 = yy ^ 4 * (volume S).toReal := by
    rw [mul_pow, rpow_natCast_pow hm0 (by norm_num : (1 / 4 : ℝ) * (4 : ℕ) = (1 : ℕ)), pow_one]
  rw [eL, eR] at h4
  have eyy : yy ^ 4 = 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * γ ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 *
      (τ / 4) ^ 6 := by
    rw [hyydef, mul_pow, mul_pow, mul_pow,
      rpow_natCast_pow h2ρ (by norm_num : (3 / 2 : ℝ) * (4 : ℕ) = (6 : ℕ)),
      rpow_natCast_pow hQ0 (by norm_num : (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ)), hQdef]
    field_simp
    ring
  rw [eyy] at h4
  have hpos6 : (0 : ℝ) < (τ / 4) ^ 6 := by positivity
  refine le_of_mul_le_mul_right ?_ hpos6
  calc (volume (Metric.ball x₀ ρ ∩ {x | M - τ / 4 < z x})).toReal ^ 4 * (τ / 4) ^ 6
      ≤ 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * γ ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 * (τ / 4) ^ 6 *
        (volume S).toReal := h4
    _ = 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * γ ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 *
        (volume S).toReal * (τ / 4) ^ 6 := by ring

/-! ### Summing the ladder -/

/-- **De Giorgi's measure-shrinking lemma** (Ladyzhenskaya–Ural'tseva, Ch. II, §6; Giusti,
*Direct Methods in the Calculus of Variations*, Theorem 7.3): with the geometric level ladder
`k_j = M - 2^{-j} om/2`, and provided `χ ρ ≤ 2^{-s} om`,

`s |B_ρ ∩ {z > k_s}|⁴ ≤ C |B_ρ|⁴`,   `C = C(d, γ)`.

The sets `{k_j < z ≤ k_{j+1}}`, `j < s`, are disjoint subsets of `B_ρ`, so their measures sum to
at most `|B_ρ|`; `dg_shrink_step` bounds `|{z > k_{j+1}}|⁴` by `C |B_ρ|³` times the measure of the
`j`-th of them, and `{z > k_s} ⊆ {z > k_{j+1}}`. -/
theorem exists_dg_measure_shrink {γ : ℝ} (hγ : 0 ≤ γ) (hd : 0 < d) :
    ∃ Cst : ℝ, 0 < Cst ∧
      ∀ (χ R₀ : ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
        0 ≤ χ → IsDGSub γ χ R₀ Ω z G →
      ∀ (x₀ : Euc d) (ρ : ℝ), 0 < ρ → 3 / 2 * ρ ≤ R₀ →
        Metric.closedBall x₀ (3 / 2 * ρ) ⊆ Ω →
      ∀ (M om : ℝ), 0 < om →
      (∀ᵐ x, x ∈ Metric.closedBall x₀ (3 / 2 * ρ) → z x ≤ M) →
      volume (Metric.ball x₀ ρ) ≤ 2 * volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - om / 2}) →
      ∀ s : ℕ, χ * ρ ≤ (1 / 2 : ℝ) ^ s * om →
      (s : ℝ) * (volume (Metric.ball x₀ ρ ∩
            {x | M - (1 / 2 : ℝ) ^ s * om / 2 < z x})).toReal ^ 4 ≤
          Cst * (volume (Metric.ball x₀ ρ)).toReal ^ 4 := by
  refine ⟨2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3, by positivity, ?_⟩
  intro χ R₀ Ω z G hχ hz x₀ ρ hρ hρR hball M om hom hMbd hhalf s hχs
  obtain ⟨τ, hτdef⟩ : ∃ f : ℕ → ℝ, f = fun j => (1 / 2 : ℝ) ^ j * om := ⟨_, rfl⟩
  have hτval : ∀ j, τ j = (1 / 2 : ℝ) ^ j * om := fun j => by rw [hτdef]
  have hτpos : ∀ j, 0 < τ j := fun j => by rw [hτval]; positivity
  have hτanti : ∀ i j : ℕ, i ≤ j → τ j ≤ τ i := by
    intro i j hij
    rw [hτval, hτval]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij) hom.le
  have hτsucc : ∀ j, τ (j + 1) = τ j / 2 := by
    intro j
    rw [hτval, hτval, pow_succ]
    ring
  have hτzero : τ 0 = om := by rw [hτval]; norm_num
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (Metric.ball x₀ ρ)).toReal := ⟨_, rfl⟩
  have hV0 : 0 < V := by
    rw [hVdef]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hρ).ne' measure_ball_lt_top.ne
  obtain ⟨A, hAdef⟩ : ∃ f : ℕ → Set (Euc d),
      f = fun j => Metric.ball x₀ ρ ∩ {x | M - τ j / 2 < z x} := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ f : ℕ → Set (Euc d),
      f = fun j => Metric.ball x₀ ρ ∩ {x | M - τ j / 2 < z x ∧ z x ≤ M - τ j / 4} := ⟨_, rfl⟩
  have hWm : ∀ j, MeasurableSet (W j) := by
    intro j
    rw [hWdef]
    exact measurableSet_ball.inter ((measurableSet_lt measurable_const hz.measurable).inter
      (measurableSet_le hz.measurable measurable_const))
  have hWB : ∀ j, W j ⊆ Metric.ball x₀ ρ := by
    intro j
    rw [hWdef]
    exact inter_subset_left
  have hWtop : ∀ j, volume (W j) ≠ ⊤ := fun j =>
    ((measure_mono (hWB j)).trans_lt measure_ball_lt_top).ne
  have hAtop : ∀ j, volume (A j) ≠ ⊤ := by
    intro j
    rw [hAdef]
    exact ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  -- one step of the ladder
  have hstep : ∀ j : ℕ, j ≤ s →
      (volume (A (j + 1))).toReal ^ 4 ≤
        2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 *
          (volume (W j)).toReal := by
    intro j hj
    have hχτ : χ * ρ ≤ τ j := by
      have h1 : τ s ≤ τ j := hτanti j s hj
      rw [hτval] at h1
      linarith [hχs]
    have hhalfj : volume (Metric.ball x₀ ρ) ≤
        2 * volume (Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ j / 2}) := by
      have h1 : τ j ≤ om := by
        have h2 := hτanti 0 j (Nat.zero_le j)
        rw [hτzero] at h2
        linarith
      have hsub : Metric.ball x₀ ρ ∩ {x | z x ≤ M - om / 2} ⊆
          Metric.ball x₀ ρ ∩ {x | z x ≤ M - τ j / 2} := by
        intro y hy
        refine ⟨hy.1, ?_⟩
        show z y ≤ M - τ j / 2
        have hy2 : z y ≤ M - om / 2 := hy.2
        linarith
      exact hhalf.trans (mul_le_mul_right (measure_mono hsub) 2)
    have hraw := dg_shrink_step hγ hχ hz hρ hρR hball hd (hτpos j) hχτ hMbd hhalfj
    have heq : M - τ (j + 1) / 2 = M - τ j / 4 := by rw [hτsucc]; ring
    rw [hAdef]
    simp only [heq]
    have hmono : 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * γ ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 ≤
        2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 := by
      have h1 : γ ^ 3 ≤ (γ + 1) ^ 3 := by nlinarith
      have h2 : (0 : ℝ) ≤ 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 := by positivity
      have h3 : (0 : ℝ) ≤ ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 := by positivity
      calc 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * γ ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3
          = 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * γ ^ 3 * (((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3) := by ring
        _ ≤ 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * (((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
        _ = 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 := by ring
    rw [hWdef, hVdef]
    refine hraw.trans ?_
    exact mul_le_mul_of_nonneg_right (by rw [← hVdef]; exact hmono) ENNReal.toReal_nonneg
  -- the sets `W j` are pairwise disjoint
  have hdisj_aux : ∀ i j : ℕ, i < j → Disjoint (W i) (W j) := by
    intro i j hij
    rw [Set.disjoint_left, hWdef]
    rintro x ⟨-, -, hxi⟩ ⟨-, hxj, -⟩
    have h1 : τ j ≤ τ i / 2 := by
      have h2 := hτanti (i + 1) j hij
      rw [hτsucc] at h2
      exact h2
    have hxi' : z x ≤ M - τ i / 4 := hxi
    have hxj' : M - τ j / 2 < z x := hxj
    linarith
  have hdisj : (↑(Finset.range s) : Set ℕ).PairwiseDisjoint W := by
    intro i _ j _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdisj_aux i j h
    · exact (hdisj_aux j i h).symm
  have hsumW : ∑ j ∈ Finset.range s, (volume (W j)).toReal ≤ V := by
    rw [← ENNReal.toReal_sum (fun j _ => hWtop j),
      ← measure_biUnion_finset hdisj (fun j _ => hWm j), hVdef]
    exact ENNReal.toReal_mono measure_ball_lt_top.ne
      (measure_mono (iUnion₂_subset fun j _ => hWB j))
  -- `A s ⊆ A (j+1)` for `j < s`
  have hAmono : ∀ j : ℕ, j < s → (volume (A s)).toReal ≤ (volume (A (j + 1))).toReal := by
    intro j hj
    refine ENNReal.toReal_mono (hAtop (j + 1)) (measure_mono ?_)
    rw [hAdef]
    intro y hy
    refine ⟨hy.1, ?_⟩
    show M - τ (j + 1) / 2 < z y
    have hy2 : M - τ s / 2 < z y := hy.2
    have h1 : τ s ≤ τ (j + 1) := hτanti (j + 1) s hj
    linarith
  -- sum the ladder
  have hkey : (s : ℝ) * (volume (A s)).toReal ^ 4 ≤
      2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 4 := by
    have e1 : (s : ℝ) * (volume (A s)).toReal ^ 4 =
        ∑ _j ∈ Finset.range s, (volume (A s)).toReal ^ 4 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e2 : ∑ _j ∈ Finset.range s, (volume (A s)).toReal ^ 4 ≤
        ∑ j ∈ Finset.range s, (volume (A (j + 1))).toReal ^ 4 :=
      Finset.sum_le_sum fun j hj =>
        pow_le_pow_left₀ ENNReal.toReal_nonneg (hAmono j (Finset.mem_range.1 hj)) 4
    have e3 : ∑ j ∈ Finset.range s, (volume (A (j + 1))).toReal ^ 4 ≤
        ∑ j ∈ Finset.range s,
          2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 *
            (volume (W j)).toReal :=
      Finset.sum_le_sum fun j hj => hstep j (le_of_lt (Finset.mem_range.1 hj))
    have e4 : ∑ j ∈ Finset.range s,
          2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 *
            (volume (W j)).toReal =
        2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 *
          ∑ j ∈ Finset.range s, (volume (W j)).toReal := by
      rw [Finset.mul_sum]
    have e5 : 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 *
          ∑ j ∈ Finset.range s, (volume (W j)).toReal ≤
        2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 * V :=
      mul_le_mul_of_nonneg_left hsumW (by positivity)
    have e6 : 2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 3 * V =
        2 ^ 25 * ((2 : ℝ) ^ d) ^ 4 * (γ + 1) ^ 3 * ((3 / 2 : ℝ) ^ d) ^ 3 * V ^ 4 := by ring
    rw [e1]
    calc ∑ _j ∈ Finset.range s, (volume (A s)).toReal ^ 4
        ≤ ∑ j ∈ Finset.range s, (volume (A (j + 1))).toReal ^ 4 := e2
      _ ≤ _ := e3
      _ = _ := e4
      _ ≤ _ := e5
      _ = _ := e6
  have hAs : A s = Metric.ball x₀ ρ ∩ {x | M - (1 / 2 : ℝ) ^ s * om / 2 < z x} := by
    rw [hAdef]
    simp only [hτval]
  rw [← hAs, hVdef] at *
  exact hkey

end Komlos.Literature.Regularized
