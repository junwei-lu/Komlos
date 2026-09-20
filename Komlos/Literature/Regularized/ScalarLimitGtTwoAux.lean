import Komlos.Literature.Regularized.ScalarLimitUpper

/-!
# Scalar and profile inequalities for the lower scalar limit at `p > 2`

`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*, lower half, the case `2 < p`.  For `p > 2`
the truncated power satisfies `h_R ≤ s^p/p`, so the profile lies *below* `F^p/p` and the
pointwise argument of `le_integral_kinetic_regProfile` is unavailable: the truncation level has
to be sent to infinity along a minimizing sequence.  This file collects the elementary
inequalities that the compactness argument
(`Komlos/Literature/Regularized/ScalarLimitGtTwo.lean`) needs.

## Contents

* `exists_pos_mul_norm_le'`: `c ‖ξ‖ ≤ F ξ` with `c > 0`, without the `Nonempty (Fin d)`
  hypothesis of `IsSmoothStrictNorm.exists_pos_mul_norm_le` (for `d = 0` take `c = 1`).
* `exists_isMollifier`: mollifiers of every positive radius exist (a normalized bump).
* `rpow_tangent_le`, `truncPowDeriv_mono_R`, `truncPow_mono_R`: for `2 ≤ p` the truncated power
  `h_R` is *nondecreasing in the truncation level* `R`.  This is what makes `Φ_{R₀}` a valid
  lower profile for every `Ψ_n` with `R_n ≥ R₀`.
* `truncPow_add_le`: the increment bound `h_R(s + a) - h_R(s) ≤ a h_R'(s+a)`, which converts the
  mollification error `M ε` into an error that is *affine* in `‖q‖` — hence controlled, after
  multiplication by `w²` and integration, by the `W^{1,2}` norm of `w`.
* `truncPow_quad_lower`: `θ s²/2 - θ R² ≤ h_R(s)` with `θ = (p-1)R^{p-2}/2`, the quadratic
  coercivity that yields the uniform `W^{1,2}` bound.
* `truncPow_le_regProfile`, `exists_regProfile_comparison`: the two profile comparisons in the
  form in which the compactness argument uses them.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Two auxiliary existence statements -/

/-- `F` is bounded below by a positive multiple of the Euclidean norm, with no hypothesis on the
dimension: for `d = 0` every vector is `0` and `c = 1` works. -/
theorem exists_pos_mul_norm_le' {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ, c * ‖ξ‖ ≤ F ξ := by
  rcases isEmpty_or_nonempty (Fin d) with _ | _
  · refine ⟨1, one_pos, fun ξ => ?_⟩
    have hξ : ξ = 0 := Subsingleton.elim _ _
    simp [hξ, hF.map_zero]
  · exact hF.exists_pos_mul_norm_le

/-- **Mollifiers of every positive radius exist**: the normalization of a `ContDiffBump`
centred at the origin. -/
theorem exists_isMollifier {ε : ℝ} (hε : 0 < ε) : ∃ ρ : Euc d → ℝ, IsMollifier ρ ε := by
  set φ : ContDiffBump (0 : Euc d) := ⟨ε / 2, ε, by positivity, by linarith⟩ with hφ
  refine ⟨φ.normed volume, ?_, ?_, ?_, ?_, ?_, hε⟩
  · exact φ.contDiff_normed (μ := (volume : Measure (Euc d))) (n := ⊤)
  · exact fun x => ContDiffBump.nonneg_normed _ x
  · intro x
    have h := φ.normed_sub (μ := volume) x
    simpa using h
  · exact ContDiffBump.integral_normed _
  · have hs : Function.support (φ.normed volume) = Metric.ball (0 : Euc d) ε := by
      rw [ContDiffBump.support_normed_eq]
    rw [tsupport, hs]
    exact Metric.closure_ball_subset_closedBall
  
/-! ### The tangent-line inequality for `x ↦ x^q`, `q ≥ 1` -/

/-- For `q ≥ 1` the tangent line of `x ↦ x^q` at `R > 0` lies below the graph, on `[R, ∞)`. -/
theorem rpow_tangent_le {q R u : ℝ} (hq : 1 ≤ q) (hR : 0 < R) (hu : R ≤ u) :
    R ^ q + q * R ^ (q - 1) * (u - R) ≤ u ^ q := by
  set g : ℝ → ℝ := fun x => x ^ q - R ^ q - q * R ^ (q - 1) * (x - R) with hg
  have hderiv : ∀ x : ℝ, x ≠ 0 → HasDerivAt g (q * x ^ (q - 1) - q * R ^ (q - 1)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => y ^ q) (q * x ^ (q - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx)
    have h2 : HasDerivAt (fun y : ℝ => q * R ^ (q - 1) * (y - R)) (q * R ^ (q - 1)) x := by
      simpa using ((hasDerivAt_id x).sub_const R).const_mul (q * R ^ (q - 1))
    exact (h1.sub_const (R ^ q)).sub h2
  have hcont : Continuous g := by
    have hrc : Continuous fun x : ℝ => x ^ q :=
      continuous_iff_continuousAt.2 fun x =>
        Real.continuousAt_rpow_const x q (Or.inr (by linarith))
    exact (hrc.sub continuous_const).sub
      (continuous_const.mul (continuous_id.sub continuous_const))
  have hmono : MonotoneOn g (Ici R) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici R) hcont.continuousOn
      (fun x hx => (hderiv x (by rw [interior_Ici] at hx; exact (hR.trans hx).ne')
        ).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hderiv x (hR.trans hx).ne').deriv]
    have hle : R ^ (q - 1) ≤ x ^ (q - 1) := Real.rpow_le_rpow hR.le hx.le (by linarith)
    nlinarith [hle]
  have h0 : g R = 0 := by simp [hg]
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hu) hu
  rw [h0] at this
  simp only [hg] at this
  linarith

/-! ### Monotonicity of `h_R` in the truncation level, for `2 ≤ p` -/

variable {p R R' : ℝ}

/-- For `2 ≤ p` the derivative `h_R'` is nondecreasing in the truncation level `R`. -/
theorem truncPowDeriv_mono_R (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R) (hRR' : R ≤ R') (t : ℝ) :
    truncPowDeriv p R t ≤ truncPowDeriv p R' t := by
  have hR' : 0 < R' := lt_of_lt_of_le hR hRR'
  have hq : (1 : ℝ) ≤ p - 1 := by linarith
  have hexp : p - 1 - 1 = p - 2 := by ring
  set u : ℝ := max t 0 with hu
  have hu0 : 0 ≤ u := le_max_right _ _
  have heqR : max (t - R) 0 = max (u - R) 0 := by
    rcases le_or_gt 0 t with ht | ht
    · rw [hu, max_eq_left ht]
    · rw [hu, max_eq_right ht.le, max_eq_right (by linarith), max_eq_right (by linarith)]
  have heqR' : max (t - R') 0 = max (u - R') 0 := by
    rcases le_or_gt 0 t with ht | ht
    · rw [hu, max_eq_left ht]
    · rw [hu, max_eq_right ht.le, max_eq_right (by linarith), max_eq_right (by linarith)]
  rw [truncPowDeriv, truncPowDeriv, ← hu, heqR, heqR']
  rcases le_or_gt u R with h1 | h1
  · rw [min_eq_left h1, min_eq_left (h1.trans hRR'), max_eq_right (by linarith),
      max_eq_right (by linarith)]
    simp
  · rcases le_or_gt u R' with h2 | h2
    · rw [min_eq_right h1.le, min_eq_left h2, max_eq_left (by linarith),
        max_eq_right (by linarith), mul_zero, add_zero]
      have := rpow_tangent_le hq hR h1.le
      rw [hexp] at this
      linarith
    · rw [min_eq_right h1.le, min_eq_right h2.le, max_eq_left (by linarith),
        max_eq_left (by linarith)]
      have htan := rpow_tangent_le hq hR hRR'
      rw [hexp] at htan
      have hw : R ^ (p - 2) ≤ R' ^ (p - 2) := Real.rpow_le_rpow hR.le hRR' (by linarith)
      have hRp : (0 : ℝ) ≤ R ^ (p - 2) := Real.rpow_nonneg hR.le _
      have hu' : (0 : ℝ) ≤ u - R' := by linarith
      have hstep : (p - 1) * R ^ (p - 2) * (u - R') ≤ (p - 1) * R' ^ (p - 2) * (u - R') := by
        have hcoef : (p - 1) * R ^ (p - 2) ≤ (p - 1) * R' ^ (p - 2) :=
          mul_le_mul_of_nonneg_left hw (by linarith)
        exact mul_le_mul_of_nonneg_right hcoef hu'
      have hsplit : (p - 1) * R ^ (p - 2) * (u - R) =
          (p - 1) * R ^ (p - 2) * (R' - R) + (p - 1) * R ^ (p - 2) * (u - R') := by ring
      linarith [htan, hstep, hsplit]

/-- For `2 ≤ p` the truncated power `h_R` is nondecreasing in the truncation level `R`. -/
theorem truncPow_mono_R (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R) (hRR' : R ≤ R') {s : ℝ}
    (hs : 0 ≤ s) : truncPow p R s ≤ truncPow p R' s := by
  rw [truncPow, truncPow]
  exact intervalIntegral.integral_mono_on hs (intervalIntegrable_truncPowDeriv hp 0 s)
    (intervalIntegrable_truncPowDeriv hp 0 s) fun x _ => truncPowDeriv_mono_R hp hp2 hR hRR' x

/-! ### The increment bound -/

/-- **The increment bound** `h_R(s + a) ≤ h_R(s) + a (R^{p-1} + (p-1)R^{p-2}(s+a))`: the
derivative is monotone, so the increment is at most `a h_R'(s+a)`, and `h_R'` is bounded by the
affine continuation. -/
theorem truncPow_add_le (hp : 1 < p) (hR : 0 < R) {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    truncPow p R (s + a) ≤
      truncPow p R s + a * (R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (s + a)) := by
  have hsplit : truncPow p R (s + a) =
      truncPow p R s + ∫ t in s..(s + a), truncPowDeriv p R t := by
    rw [truncPow, truncPow, intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_truncPowDeriv hp 0 s) (intervalIntegrable_truncPowDeriv hp s (s + a))]
  have hbound : (∫ t in s..(s + a), truncPowDeriv p R t) ≤
      a * (R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (s + a)) := by
    have hmono : ∀ t ∈ Set.Icc s (s + a),
        truncPowDeriv p R t ≤ R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (s + a) := by
      intro t ht
      have h1 : min (max t 0) R ^ (p - 1) ≤ R ^ (p - 1) :=
        Real.rpow_le_rpow (le_min (le_max_right _ _) hR.le) (min_le_right _ _) (by linarith)
      have h2 : max (t - R) 0 ≤ s + a := by
        refine max_le (by linarith [ht.2, hR.le]) (by linarith)
      have h3 : (0 : ℝ) ≤ (p - 1) * R ^ (p - 2) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hR.le _)
      have := mul_le_mul_of_nonneg_left h2 h3
      rw [truncPowDeriv]
      linarith
    have hcalc := intervalIntegral.integral_mono_on (by linarith : s ≤ s + a)
      (intervalIntegrable_truncPowDeriv hp s (s + a))
      ((continuous_const.intervalIntegrable s (s + a))) hmono
    rwa [intervalIntegral.integral_const, smul_eq_mul, show s + a - s = a by ring] at hcalc
  linarith [hsplit, hbound]

/-! ### Quadratic coercivity of `h_R` -/

/-- **Quadratic coercivity**: with `θ = (p-1)R^{p-2}/2` one has `θ s²/2 - θ R² ≤ h_R(s)` for all
`s ≥ 0`.  Past `R` the derivative is at least `(p-1)R^{p-2}(t-R)`, so `h_R(s) ≥ θ (s-R)²`, and
`(s-R)² ≥ s²/2 - R²`. -/
theorem truncPow_quad_lower (hp : 1 < p) (hR : 0 < R) {s : ℝ} (hs : 0 ≤ s) :
    (p - 1) * R ^ (p - 2) / 4 * s ^ 2 - (p - 1) * R ^ (p - 2) / 2 * R ^ 2 ≤ truncPow p R s := by
  have hRp : (0 : ℝ) ≤ R ^ (p - 2) := Real.rpow_nonneg hR.le _
  have hθ2 : (0 : ℝ) ≤ (p - 1) * R ^ (p - 2) / 2 :=
    div_nonneg (mul_nonneg (by linarith) hRp) (by norm_num)
  have hθ4 : (0 : ℝ) ≤ (p - 1) * R ^ (p - 2) / 4 :=
    div_nonneg (mul_nonneg (by linarith) hRp) (by norm_num)
  have h0 : 0 ≤ truncPow p R s := truncPow_nonneg hp hR.le hs
  rcases le_or_gt s R with hsR | hsR
  · have hss : s ^ 2 ≤ R ^ 2 := by nlinarith
    have h1 : (p - 1) * R ^ (p - 2) / 4 * s ^ 2 ≤ (p - 1) * R ^ (p - 2) / 4 * R ^ 2 :=
      mul_le_mul_of_nonneg_left hss hθ4
    have h2 : (0 : ℝ) ≤ (p - 1) * R ^ (p - 2) / 4 * R ^ 2 := mul_nonneg hθ4 (sq_nonneg R)
    have hid : (p - 1) * R ^ (p - 2) / 2 * R ^ 2
        = 2 * ((p - 1) * R ^ (p - 2) / 4 * R ^ 2) := by ring
    linarith [h0, h1, h2, hid]
  · -- past `R` the derivative dominates `(p-1)R^{p-2}(t-R)`
    have hsplit : truncPow p R s = truncPow p R R + ∫ t in R..s, truncPowDeriv p R t := by
      rw [truncPow, truncPow, intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_truncPowDeriv hp 0 R) (intervalIntegrable_truncPowDeriv hp R s)]
    have hlow : ∀ t ∈ Set.Icc R s, (p - 1) * R ^ (p - 2) * (t - R) ≤ truncPowDeriv p R t := by
      intro t ht
      rw [truncPowDeriv_of_ge hR.le ht.1]
      have : (0 : ℝ) ≤ R ^ (p - 1) := Real.rpow_nonneg hR.le _
      linarith
    have hint : IntervalIntegrable (fun t => (p - 1) * R ^ (p - 2) * (t - R)) volume R s :=
      (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable R s
    have hcalc := intervalIntegral.integral_mono_on hsR.le hint
      (intervalIntegrable_truncPowDeriv hp R s) hlow
    have heval : (∫ t in R..s, (p - 1) * R ^ (p - 2) * (t - R))
        = (p - 1) * R ^ (p - 2) / 2 * (s - R) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
      have hsub : (∫ t in R..s, (t - R)) = (s - R) ^ 2 / 2 := by
        rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
          intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [hsub]
      ring
    rw [heval] at hcalc
    have hR0 : 0 ≤ truncPow p R R := truncPow_nonneg hp hR.le hR.le
    have hkey : (p - 1) * R ^ (p - 2) / 2 * (s - R) ^ 2 ≤ truncPow p R s := by
      rw [hsplit]; linarith
    have hid : (p - 1) * R ^ (p - 2) / 2 * (s - R) ^ 2
        = ((p - 1) * R ^ (p - 2) / 4 * s ^ 2 - (p - 1) * R ^ (p - 2) / 2 * R ^ 2)
          + (p - 1) * R ^ (p - 2) / 4 * (s - 2 * R) ^ 2 := by ring
    have hy : (0 : ℝ) ≤ (p - 1) * R ^ (p - 2) / 4 * (s - 2 * R) ^ 2 :=
      mul_nonneg hθ4 (sq_nonneg _)
    linarith [hkey, hid, hy]

/-! ### The two profile comparisons -/

section Profiles

variable {F ρ : Euc d → ℝ} {ε : ℝ}

/-- `Ψ((p/2) q) = Ψ_p(q)` at the *un*dilated argument: `regProfile p F R ρ q = Ψ_p((2/p) q)`. -/
theorem regProfile_eq (p : ℝ) (F : Euc d → ℝ) (R : ℝ) (ρ : Euc d → ℝ) (q : Euc d) :
    regProfile p F R ρ q = truncSmoothedProfile p F R ρ ((2 / p) • q) := rfl

/-- `F ((2/p) • q) = (2/p) F q`. -/
theorem map_smul_two_div (hp : 1 < p) (hF : IsSmoothStrictNorm F) (q : Euc d) :
    F ((2 / p) • q) = 2 / p * F q := by
  have hpos : (0 : ℝ) < 2 / p := by
    have : (0 : ℝ) < p := by linarith
    positivity
  rw [hF.homog, abs_of_pos hpos]

/-- **The lower profile comparison for `2 ≤ p`**: for every truncation level `R₀ ≤ R` the
*unmollified* truncated profile at level `R₀` lies below `regProfile p F R ρ`.  Combine
monotonicity of `h_R` in `R` (`truncPow_mono_R`) with Jensen
(`truncProfile_le_truncSmoothedProfile`). -/
theorem truncPow_le_regProfile (hp : 1 < p) (hp2 : 2 ≤ p) (hF : IsSmoothStrictNorm F)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hR₀R : R₀ ≤ R) (hρ : IsMollifier ρ ε) (q : Euc d) :
    truncPow p R₀ (2 / p * F q) ≤ regProfile p F R ρ q := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le hR₀ hR₀R
  have hnn : 0 ≤ 2 / p * F q :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith)) (hF.nonneg q)
  calc truncPow p R₀ (2 / p * F q)
      ≤ truncPow p R (2 / p * F q) := truncPow_mono_R hp hp2 hR₀ hR₀R hnn
    _ = truncProfile p F R ((2 / p) • q) := by rw [truncProfile, map_smul_two_div hp hF]
    _ ≤ truncSmoothedProfile p F R ρ ((2 / p) • q) :=
        truncProfile_le_truncSmoothedProfile hp hR.le hF hρ _
    _ = regProfile p F R ρ q := rfl

/-- **The upper profile comparison** in the form the compactness argument uses: for a fixed
truncation level `R₀` and every mollifier `ρ₀` of radius `ε₀ ≤ 1`, the profile
`regProfile p F R₀ ρ₀` exceeds `regProfile p F R ρ` (`R₀ ≤ R`) by at most
`A ε₀ (1 + ‖q‖)`, with `A` depending only on `p`, `F` and `R₀`.

The mollification error `M ε₀` is converted by `truncPow_add_le` into an error that is affine
in `F q ≤ M_F ‖q‖`; affineness is exactly what makes the error integrable against `w²` with a
bound in terms of the `W^{1,2}` norm of `w`. -/
theorem exists_regProfile_comparison (hp : 1 < p) (hp2 : 2 ≤ p) (hF : IsSmoothStrictNorm F)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ε₀ : ℝ) (ρ₀ : Euc d → ℝ), IsMollifier ρ₀ ε₀ → ε₀ ≤ 1 →
      ∀ (R : ℝ), R₀ ≤ R → ∀ (ε : ℝ) (ρ : Euc d → ℝ), IsMollifier ρ ε → ∀ q : Euc d,
        regProfile p F R₀ ρ₀ q ≤ regProfile p F R ρ q + A * ε₀ * (1 + ‖q‖) := by
  obtain ⟨M, hM0, hM⟩ := exists_truncSmoothedProfile_le (p := p) (F := F) hp hF
  obtain ⟨MF₀, hMF₀⟩ := hF.exists_le_mul_norm
  set MF : ℝ := max MF₀ 0 with hMF
  have hMF0 : (0 : ℝ) ≤ MF := le_max_right _ _
  have hMFle : ∀ ξ : Euc d, F ξ ≤ MF * ‖ξ‖ := fun ξ =>
    (hMF₀ ξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg ξ))
  have hR₀p : (0 : ℝ) ≤ R₀ ^ (p - 1) := Real.rpow_nonneg hR₀.le _
  have hR₀q : (0 : ℝ) ≤ R₀ ^ (p - 2) := Real.rpow_nonneg hR₀.le _
  refine ⟨M * R₀ ^ (p - 1) + M * M * ((p - 1) * R₀ ^ (p - 2))
      + M * ((p - 1) * R₀ ^ (p - 2)) * (2 / p * MF), ?_, ?_⟩
  · have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
    have hc : (0 : ℝ) ≤ (p - 1) * R₀ ^ (p - 2) := mul_nonneg hp1 hR₀q
    have h2p : (0 : ℝ) ≤ 2 / p := div_nonneg (by norm_num) (by linarith)
    exact add_nonneg (add_nonneg (mul_nonneg hM0 hR₀p) (mul_nonneg (mul_nonneg hM0 hM0) hc))
      (mul_nonneg (mul_nonneg hM0 hc) (mul_nonneg h2p hMF0))
  intro ε₀ ρ₀ hρ₀ hε₀ R hR₀R ε ρ hρ q
  have hε₀0 : 0 < ε₀ := hρ₀.eps_pos
  set s : ℝ := 2 / p * F q with hs
  have hs0 : 0 ≤ s := mul_nonneg (div_nonneg (by norm_num) (by linarith)) (hF.nonneg q)
  have ha0 : 0 ≤ M * ε₀ := mul_nonneg hM0 hε₀0.le
  -- upper bound for the left-hand profile
  have hup : regProfile p F R₀ ρ₀ q ≤ truncPow p R₀ (s + M * ε₀) := by
    have h := hM R₀ hR₀.le ρ₀ ε₀ hρ₀ ((2 / p) • q)
    rwa [map_smul_two_div hp hF] at h
  -- lower bound for the right-hand profile
  have hlow : truncPow p R₀ s ≤ regProfile p F R ρ q :=
    truncPow_le_regProfile hp hp2 hF hR₀ hR₀R hρ q
  -- the increment
  have hincr := truncPow_add_le (p := p) (R := R₀) hp hR₀ hs0 ha0
  -- and the affine bound for the increment
  have hsq : s ≤ 2 / p * (MF * ‖q‖) :=
    mul_le_mul_of_nonneg_left (hMFle q) (by positivity)
  have hεsq : M * ε₀ * (M * ε₀) ≤ M * M * ε₀ := by nlinarith [ha0, hM0, hε₀0.le]
  have hkey : M * ε₀ * (R₀ ^ (p - 1) + (p - 1) * R₀ ^ (p - 2) * (s + M * ε₀)) ≤
      (M * R₀ ^ (p - 1) + M * M * ((p - 1) * R₀ ^ (p - 2))
        + M * ((p - 1) * R₀ ^ (p - 2)) * (2 / p * MF)) * ε₀ * (1 + ‖q‖) := by
    have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
    have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
    have hcoef : (0 : ℝ) ≤ (p - 1) * R₀ ^ (p - 2) := mul_nonneg hp1 hR₀q
    have h1 : M * ε₀ * ((p - 1) * R₀ ^ (p - 2) * s) ≤
        M * ((p - 1) * R₀ ^ (p - 2)) * (2 / p * MF) * ε₀ * ‖q‖ := by
      have := mul_le_mul_of_nonneg_left hsq (mul_nonneg ha0 hcoef)
      nlinarith [this]
    have h2 : M * ε₀ * ((p - 1) * R₀ ^ (p - 2) * (M * ε₀)) ≤
        M * M * ((p - 1) * R₀ ^ (p - 2)) * ε₀ := by nlinarith [hεsq, hcoef]
    have h3 : (0 : ℝ) ≤ M * R₀ ^ (p - 1) * ε₀ * ‖q‖ := by positivity
    have h4 : (0 : ℝ) ≤ M * M * ((p - 1) * R₀ ^ (p - 2)) * ε₀ * ‖q‖ := by positivity
    have h5 : (0 : ℝ) ≤ M * ((p - 1) * R₀ ^ (p - 2)) * (2 / p * MF) * ε₀ := by positivity
    nlinarith [h1, h2, h3, h4, h5]
  linarith [hup, hlow, hincr, hkey]

end Profiles

/-! ### The truncated and limiting exponent-`2` profiles -/

section Density

variable {F : Euc d → ℝ}

/-- The *unmollified* exponent-`2` profile at truncation level `R`: `Θ_R(q) = h_R((2/p) F q)`.
It is the profile against which the lower semicontinuity is run; `Ψ_n ≥ Θ_{R₀}` as soon as
`R_n ≥ R₀` (`truncDensity_le_regProfile`). -/
noncomputable def truncDensity (p : ℝ) (F : Euc d → ℝ) (R : ℝ) : Euc d → ℝ :=
  fun q => truncPow p R (2 / p * F q)

/-- Its `R → ∞` limit, `Λ(q) = ((2/p) F q)^p / p`.  The exponent-`2` kinetic density of `Λ` at
`(w, ∇w)` is `(1/p) F(∇u)^p` with `u = w^{2/p}`. -/
noncomputable def limitProfile (p : ℝ) (F : Euc d → ℝ) : Euc d → ℝ :=
  fun q => (2 / p * F q) ^ p / p

theorem truncDensity_nonneg (hp : 1 < p) (hR : 0 ≤ R) (hF : IsSmoothStrictNorm F) (q : Euc d) :
    0 ≤ truncDensity p F R q :=
  truncPow_nonneg hp hR (mul_nonneg (div_nonneg (by norm_num) (by linarith)) (hF.nonneg q))

theorem continuous_truncDensity (hp : 1 < p) (hF : IsSmoothStrictNorm F) :
    Continuous (truncDensity p F R) :=
  (differentiable_truncPow hp).continuous.comp (continuous_const.mul hF.continuous)

theorem limitProfile_nonneg (hp : 1 < p) (hF : IsSmoothStrictNorm F) (q : Euc d) :
    0 ≤ limitProfile p F q := by
  have h1 : (0 : ℝ) ≤ 2 / p * F q :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith)) (hF.nonneg q)
  exact div_nonneg (Real.rpow_nonneg h1 _) (by linarith)

/-- For `2 ≤ p` the truncated profile is nondecreasing in the truncation level. -/
theorem truncDensity_mono (hp : 1 < p) (hp2 : 2 ≤ p) (hF : IsSmoothStrictNorm F) (hR : 0 < R)
    (hRR' : R ≤ R') (q : Euc d) : truncDensity p F R q ≤ truncDensity p F R' q :=
  truncPow_mono_R hp hp2 hR hRR' (mul_nonneg (div_nonneg (by norm_num) (by linarith)) (hF.nonneg q))

/-- `Θ_{R₀} ≤ regProfile p F R ρ` for `R₀ ≤ R`. -/
theorem truncDensity_le_regProfile (hp : 1 < p) (hp2 : 2 ≤ p) (hF : IsSmoothStrictNorm F)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hR₀R : R₀ ≤ R) {ρ : Euc d → ℝ} {ε : ℝ} (hρ : IsMollifier ρ ε)
    (q : Euc d) : truncDensity p F R₀ q ≤ regProfile p F R ρ q :=
  truncPow_le_regProfile hp hp2 hF hR₀ hR₀R hρ q

/-- For a fixed `q` the truncated profile is eventually the limiting one. -/
theorem eventually_truncDensity_eq (hp : 1 < p) (hF : IsSmoothStrictNorm F) (q : Euc d) :
    ∀ᶠ R in atTop, truncDensity p F R q = limitProfile p F q :=
  eventually_truncPow_eq hp (mul_nonneg (div_nonneg (by norm_num) (by linarith)) (hF.nonneg q))

end Density

/-! ### Generic manipulations of the exponent-`2` kinetic density -/

section Kinetic

variable {Ψ Φ : Euc d → ℝ}

theorem homogeneousDensity_two_nonneg (hΨ : ∀ q, 0 ≤ Ψ q) (t : ℝ) (ξ : Euc d) :
    0 ≤ Korevaar.homogeneousDensity 2 Ψ t ξ := by
  rw [Korevaar.homogeneousDensity, rpow_two_eq_sq]
  exact mul_nonneg (sq_nonneg t) (hΨ _)

theorem homogeneousDensity_two_mono (h : ∀ q, Ψ q ≤ Φ q) (t : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ t ξ ≤ Korevaar.homogeneousDensity 2 Φ t ξ := by
  rw [Korevaar.homogeneousDensity, Korevaar.homogeneousDensity, rpow_two_eq_sq]
  exact mul_le_mul_of_nonneg_left (h _) (sq_nonneg t)

/-- An error that is *affine* in the profile argument becomes, at the level of the kinetic
density, an error controlled by `t²` and `t ‖ξ‖` — hence, after integration against a normalized
`w` with `∇w ∈ L²`, by the `W^{1,2}` norm. -/
theorem homogeneousDensity_two_le_add {a : ℝ}
    (h : ∀ q, Ψ q ≤ Φ q + a * (1 + ‖q‖)) {t : ℝ} (ht : 0 ≤ t) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ t ξ ≤
      Korevaar.homogeneousDensity 2 Φ t ξ + a * (t ^ 2 + t * ‖ξ‖) := by
  rcases ht.eq_or_lt with hz | hpos
  · rw [← hz]
    simp [Korevaar.homogeneousDensity, Real.zero_rpow (two_ne_zero)]
  · have hmul := mul_le_mul_of_nonneg_left (h (t⁻¹ • ξ)) (sq_nonneg t)
    have hnorm : ‖(t⁻¹ • ξ : Euc d)‖ = t⁻¹ * ‖ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
    rw [hnorm] at hmul
    have hexp : t ^ 2 * (a * (1 + t⁻¹ * ‖ξ‖)) = a * (t ^ 2 + t * ‖ξ‖) := by
      field_simp
      try ring
    rw [Korevaar.homogeneousDensity, Korevaar.homogeneousDensity, rpow_two_eq_sq]
    nlinarith [hmul, hexp]

/-- **Quadratic coercivity of the kinetic density of `Θ_1`.**  Since `h_1(σ) ≥ (p-1)σ²/4 -
(p-1)/2` and `c_F ‖ξ‖ ≤ F ξ`, the kinetic density of the truncated profile at level `1`
dominates `A₁ ‖ξ‖² - A₂ t²`.  This is the uniform `W^{1,2}` bound of the compactness argument;
the hypothesis `t = 0 → ξ = 0` holds a.e. for an admissible competitor
(`IsRegAdmissible.ae_weakGrad_eq_zero`). -/
theorem quad_le_homogeneousDensity_truncDensity (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {cF : ℝ} (hcF0 : 0 < cF) (hcF : ∀ ξ, cF * ‖ξ‖ ≤ F ξ)
    {t : ℝ} (ht : 0 ≤ t) {ξ : Euc d} (hξ : t = 0 → ξ = 0) :
    (p - 1) / 4 * (2 / p) ^ 2 * cF ^ 2 * ‖ξ‖ ^ 2 - (p - 1) / 2 * t ^ 2
      ≤ Korevaar.homogeneousDensity 2 (truncDensity p F 1) t ξ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  rcases ht.eq_or_lt with hz | htpos
  · rw [← hz, hξ hz.symm]
    simp [homogeneousDensity_two_zero]
  · have htne : t ≠ 0 := htpos.ne'
    have hFξ : 0 ≤ F ξ := hF.nonneg ξ
    set σ : ℝ := 2 / p * F (t⁻¹ • ξ) with hσ
    have hq : F (t⁻¹ • ξ) = t⁻¹ * F ξ := by
      rw [hF.homog, abs_of_pos (inv_pos.2 htpos)]
    have hσ' : σ = 2 / p * t⁻¹ * F ξ := by rw [hσ, hq]; ring
    have hσ0 : 0 ≤ σ := by
      rw [hσ']
      exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hp0.le)
        (inv_nonneg.2 htpos.le)) hFξ
    have hlow := truncPow_quad_lower (p := p) (R := 1) hp one_pos hσ0
    rw [Real.one_rpow] at hlow
    have hdens : Korevaar.homogeneousDensity 2 (truncDensity p F 1) t ξ
        = t ^ 2 * truncPow p 1 σ := by
      simp only [Korevaar.homogeneousDensity, truncDensity, rpow_two_eq_sq]
      rw [← hσ]
    have hsq : t ^ 2 * σ ^ 2 = (2 / p) ^ 2 * F ξ ^ 2 := by
      rw [hσ']
      field_simp
      try ring
    have hcs : cF ^ 2 * ‖ξ‖ ^ 2 ≤ F ξ ^ 2 := by
      have h := hcF ξ
      have h0 : (0 : ℝ) ≤ cF * ‖ξ‖ := mul_nonneg hcF0.le (norm_nonneg ξ)
      nlinarith [mul_self_le_mul_self h0 h]
    have hcoef : (0 : ℝ) ≤ (p - 1) / 4 * (2 / p) ^ 2 :=
      mul_nonneg (div_nonneg hp1 (by norm_num)) (sq_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hlow (sq_nonneg t)
    rw [← hdens] at hmul
    have hkey : (p - 1) / 4 * (2 / p) ^ 2 * cF ^ 2 * ‖ξ‖ ^ 2 - (p - 1) / 2 * t ^ 2
        ≤ t ^ 2 * ((p - 1) * 1 / 4 * σ ^ 2 - (p - 1) * 1 / 2 * 1 ^ 2) := by
      have h1 : t ^ 2 * ((p - 1) * 1 / 4 * σ ^ 2 - (p - 1) * 1 / 2 * 1 ^ 2)
          = (p - 1) / 4 * (t ^ 2 * σ ^ 2) - (p - 1) / 2 * t ^ 2 := by ring
      rw [h1, hsq]
      have h2 := mul_le_mul_of_nonneg_left hcs hcoef
      linarith [h2]
    linarith [hkey, hmul]

end Kinetic

end Komlos.Literature.Regularized
