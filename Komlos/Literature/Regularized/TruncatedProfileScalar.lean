import Komlos.Literature.Regularized.TruncatedProfile

/-!
# Scalar two-sided bounds for the derivative `h_R'` of the truncated power

`REGULARIZED_ROUTE.md`, Revision 2, needs the mollified truncated profile `Ψ_p = Φ_R ∗ ρ` to be
*globally* uniformly elliptic.  The whole estimate is reduced, in
`Komlos/Literature/Regularized/TruncatedProfileFlux.lean`, to two-sided comparisons of the scalar
`h_R' = truncPowDeriv p R` with the identity — the scalar of the flux of `F²/2`.  This file proves
those comparisons.

Writing `a = min σ R` (so that `h_R'(σ) = a^{p-1} + (p-1) R^{p-2} (σ - a)` for `σ ≥ 0`,
`truncPowDeriv_eq_add`) and `W(σ) = a^{p-2}` (`truncWeight`), the four regimes are:

| | `1 < p ≤ 2` | `2 ≤ p` |
| --- | --- | --- |
| lower | `(p-1)R^{p-2} σ ≤ h_R'(σ)` | `W(σ) σ ≤ h_R'(σ)` |
| upper | `h_R'(σ) ≤ W(σ) σ` | `h_R'(σ) ≤ (p-1)R^{p-2} σ` |

together with the corresponding *difference* inequalities (`le_truncPowDeriv_sub_const`,
`truncPowDeriv_sub_le_weight`, `weight_le_truncPowDeriv_sub`, `truncPowDeriv_sub_le_const`),
which are the ones that enter the monotonicity comparison.  The singular regimes are exactly the
two off-diagonal ones: for `p < 2` the weight `W` blows up at `0`, for `p > 2` it degenerates
there; both defects are repaired later by the mollification.

All four pointwise bounds and two of the four difference bounds are elementary consequences of
`x ↦ x^{p-2}` being monotone (in the appropriate direction).  The remaining two use the
monotonicity of `x ↦ x^{p-1} - (p-1)R^{p-2} x` (resp. its negative) on `[0, R]`, i.e. a mean
value argument on an interval on which `x^{p-1}` is differentiable.
-/

open Set

namespace Komlos.Literature.Regularized

variable {p R : ℝ}

/-! ### The weight `W(σ) = min(σ, R)^{p-2}` -/

/-- The weight `W(σ) = min(σ, R)^{p-2}` governing the ellipticity of `Φ_R = h_R ∘ F` at the
level `F = σ`. -/
noncomputable def truncWeight (p R σ : ℝ) : ℝ := min σ R ^ (p - 2)

theorem truncWeight_nonneg (hR : 0 ≤ R) {σ : ℝ} (hσ : 0 ≤ σ) : 0 ≤ truncWeight p R σ :=
  Real.rpow_nonneg (le_min hσ hR) _

/-- `min σ R ^ (p-2) * min σ R = min σ R ^ (p-1)`. -/
private theorem rpow_mul_self (hp : 1 < p) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (p - 2) * x = x ^ (p - 1) := by
  have h : x ^ (p - 2 + 1) = x ^ (p - 2) * x :=
    Real.rpow_add_one' hx (by intro h; apply absurd h; intro h'; linarith [h'])
  rw [← h]
  ring_nf

/-- The closed form of `h_R'` on `[0, ∞)`: `h_R'(σ) = a^{p-1} + (p-1) R^{p-2} (σ - a)` with
`a = min σ R`. -/
theorem truncPowDeriv_eq_add (_hR : 0 ≤ R) {σ : ℝ} (hσ : 0 ≤ σ) :
    truncPowDeriv p R σ = min σ R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (σ - min σ R) := by
  rw [truncPowDeriv, max_eq_left hσ]
  congr 2
  rcases le_total σ R with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]

theorem sub_min_nonneg {σ : ℝ} (_hσ : 0 ≤ σ) (_hR : 0 ≤ R) : 0 ≤ σ - min σ R := by
  rcases le_total σ R with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- `σ - min σ R = (σ - R)⁺` is monotone. -/
theorem sub_min_mono {τ σ : ℝ} (hτσ : τ ≤ σ) : τ - min τ R ≤ σ - min σ R := by
  rcases le_total σ R with h | h
  · rw [min_eq_left h, min_eq_left (hτσ.trans h)]
    linarith
  · rw [min_eq_right h]
    rcases le_total τ R with h' | h'
    · rw [min_eq_left h']; linarith
    · rw [min_eq_right h']; linarith

/-! ### Two mean value estimates on `[0, R]` -/

private theorem continuous_rpow_sub_one (hp : 1 < p) : Continuous fun x : ℝ => x ^ (p - 1) :=
  continuous_iff_continuousAt.2 fun x =>
    Real.continuousAt_rpow_const x (p - 1) (Or.inr (by linarith))

/-- For `1 < p ≤ 2`, `x ↦ x^{p-1} - (p-1)R^{p-2} x` is monotone on `[0, R]`. -/
private theorem rpow_sub_rpow_ge_const (hp : 1 < p) (hp2 : p ≤ 2) (_hR : 0 < R) {b a : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (haR : a ≤ R) :
    (p - 1) * R ^ (p - 2) * (a - b) ≤ a ^ (p - 1) - b ^ (p - 1) := by
  set G : ℝ → ℝ := fun x => x ^ (p - 1) - (p - 1) * R ^ (p - 2) * x with hG
  have hderiv : ∀ x : ℝ, x ≠ 0 →
      HasDerivAt G ((p - 1) * x ^ (p - 2) - (p - 1) * R ^ (p - 2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => y ^ (p - 1)) ((p - 1) * x ^ (p - 1 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx)
    have h2 : HasDerivAt (fun y : ℝ => (p - 1) * R ^ (p - 2) * y) ((p - 1) * R ^ (p - 2)) x := by
      simpa using (hasDerivAt_id x).const_mul ((p - 1) * R ^ (p - 2))
    have heq : p - 1 - 1 = p - 2 := by ring
    rw [heq] at h1
    exact h1.sub h2
  have hmono : MonotoneOn G (Icc 0 R) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 R)
      ((continuous_rpow_sub_one hp).sub (continuous_const.mul continuous_id)).continuousOn
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (hderiv x (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      rw [(hderiv x (ne_of_gt hx.1)).deriv]
      have : R ^ (p - 2) ≤ x ^ (p - 2) :=
        Real.rpow_le_rpow_of_nonpos hx.1 hx.2.le (by linarith)
      nlinarith
  have := hmono ⟨hb, hba.trans haR⟩ ⟨hb.trans hba, haR⟩ hba
  simp only [hG] at this
  linarith

/-- For `2 ≤ p`, `x ↦ (p-1)R^{p-2} x - x^{p-1}` is monotone on `[0, R]`. -/
private theorem rpow_sub_rpow_le_const (hp : 1 < p) (hp2 : 2 ≤ p) (_hR : 0 < R) {b a : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (haR : a ≤ R) :
    a ^ (p - 1) - b ^ (p - 1) ≤ (p - 1) * R ^ (p - 2) * (a - b) := by
  set G : ℝ → ℝ := fun x => (p - 1) * R ^ (p - 2) * x - x ^ (p - 1) with hG
  have hderiv : ∀ x : ℝ, x ≠ 0 →
      HasDerivAt G ((p - 1) * R ^ (p - 2) - (p - 1) * x ^ (p - 2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => y ^ (p - 1)) ((p - 1) * x ^ (p - 1 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx)
    have h2 : HasDerivAt (fun y : ℝ => (p - 1) * R ^ (p - 2) * y) ((p - 1) * R ^ (p - 2)) x := by
      simpa using (hasDerivAt_id x).const_mul ((p - 1) * R ^ (p - 2))
    have heq : p - 1 - 1 = p - 2 := by ring
    rw [heq] at h1
    exact h2.sub h1
  have hmono : MonotoneOn G (Icc 0 R) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 R)
      ((continuous_const.mul continuous_id).sub (continuous_rpow_sub_one hp)).continuousOn
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (hderiv x (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      rw [(hderiv x (ne_of_gt hx.1)).deriv]
      have : x ^ (p - 2) ≤ R ^ (p - 2) := Real.rpow_le_rpow hx.1.le hx.2.le (by linarith)
      nlinarith
  have := hmono ⟨hb, hba.trans haR⟩ ⟨hb.trans hba, haR⟩ hba
  simp only [hG] at this
  linarith

/-- The elementary upper estimate `a^{p-1} - b^{p-1} ≤ a^{p-2}(a-b)` for `p ≤ 2`: it reduces to
`a^{p-2} b ≤ b^{p-2} b`. -/
private theorem rpow_sub_rpow_le_weight (hp : 1 < p) (hp2 : p ≤ 2) {b a : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) : a ^ (p - 1) - b ^ (p - 1) ≤ a ^ (p - 2) * (a - b) := by
  have ha : 0 ≤ a := hb.trans hba
  have key : a ^ (p - 2) * b ≤ b ^ (p - 1) := by
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0, mul_zero, Real.zero_rpow (by intro hc; linarith : p - 1 ≠ 0)]
    · have h1 : a ^ (p - 2) ≤ b ^ (p - 2) := Real.rpow_le_rpow_of_nonpos hb0 hba (by linarith)
      calc a ^ (p - 2) * b ≤ b ^ (p - 2) * b := mul_le_mul_of_nonneg_right h1 hb
        _ = b ^ (p - 1) := rpow_mul_self hp hb
  have hself : a ^ (p - 2) * a = a ^ (p - 1) := rpow_mul_self hp ha
  calc a ^ (p - 1) - b ^ (p - 1) ≤ a ^ (p - 1) - a ^ (p - 2) * b := by linarith
    _ = a ^ (p - 2) * (a - b) := by rw [mul_sub, hself]

/-- The elementary lower estimate `b^{p-2}(a-b) ≤ a^{p-1} - b^{p-1}` for `2 ≤ p`. -/
private theorem rpow_sub_rpow_ge_weight (hp : 1 < p) (hp2 : 2 ≤ p) {b a : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) : b ^ (p - 2) * (a - b) ≤ a ^ (p - 1) - b ^ (p - 1) := by
  have ha : 0 ≤ a := hb.trans hba
  have key : b ^ (p - 2) * a ≤ a ^ (p - 1) := by
    have h1 : b ^ (p - 2) ≤ a ^ (p - 2) := Real.rpow_le_rpow hb hba (by linarith)
    calc b ^ (p - 2) * a ≤ a ^ (p - 2) * a := mul_le_mul_of_nonneg_right h1 ha
      _ = a ^ (p - 1) := rpow_mul_self hp ha
  have hself : b ^ (p - 2) * b = b ^ (p - 1) := rpow_mul_self hp hb
  calc b ^ (p - 2) * (a - b) = b ^ (p - 2) * a - b ^ (p - 1) := by rw [mul_sub, hself]
    _ ≤ a ^ (p - 1) - b ^ (p - 1) := by linarith

/-! ### The four pointwise bounds -/

theorem le_truncPowDeriv_const (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R) {σ : ℝ} (hσ : 0 ≤ σ) :
    (p - 1) * R ^ (p - 2) * σ ≤ truncPowDeriv p R σ := by
  set a := min σ R with ha
  have ha0 : 0 ≤ a := le_min hσ hR.le
  have haR : a ≤ R := min_le_right _ _
  have hkey : (p - 1) * R ^ (p - 2) * a ≤ a ^ (p - 1) := by
    have h2 : a ^ (p - 2) * a = a ^ (p - 1) := rpow_mul_self hp ha0
    have h4 : 0 ≤ a ^ (p - 1) := Real.rpow_nonneg ha0 _
    rcases eq_or_lt_of_le ha0 with h0 | h0
    · rw [← h0, mul_zero]
      exact Real.rpow_nonneg le_rfl _
    · have h1 : R ^ (p - 2) ≤ a ^ (p - 2) := Real.rpow_le_rpow_of_nonpos h0 haR (by linarith)
      have h3 : R ^ (p - 2) * a ≤ a ^ (p - 1) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_right h1 ha0
      have h5 : (p - 1) * (R ^ (p - 2) * a) ≤ (p - 1) * a ^ (p - 1) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      nlinarith [h5, h4]
  rw [truncPowDeriv_eq_add hR.le hσ, ← ha]
  linarith

theorem truncPowDeriv_le_weight (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R) {σ : ℝ} (hσ : 0 ≤ σ) :
    truncPowDeriv p R σ ≤ truncWeight p R σ * σ := by
  rcases eq_or_lt_of_le hσ with hσ0 | hσ0
  · rw [← hσ0, mul_zero, truncPowDeriv_of_mem hR.le le_rfl hR.le,
      Real.zero_rpow (by intro hc; linarith : p - 1 ≠ 0)]
  set a := min σ R with ha
  have ha0 : 0 < a := lt_min hσ0 hR
  have haR : a ≤ R := min_le_right _ _
  have hd : 0 ≤ σ - a := sub_min_nonneg hσ hR.le
  have hself : a ^ (p - 2) * a = a ^ (p - 1) := rpow_mul_self hp ha0.le
  have hkey : (p - 1) * R ^ (p - 2) ≤ a ^ (p - 2) := by
    have h1 : R ^ (p - 2) ≤ a ^ (p - 2) := Real.rpow_le_rpow_of_nonpos ha0 haR (by linarith)
    nlinarith [Real.rpow_nonneg hR.le (p - 2)]
  rw [truncPowDeriv_eq_add hR.le hσ, truncWeight, ← ha]
  nlinarith [mul_le_mul_of_nonneg_right hkey hd]

theorem weight_le_truncPowDeriv (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R) {σ : ℝ} (hσ : 0 ≤ σ) :
    truncWeight p R σ * σ ≤ truncPowDeriv p R σ := by
  set a := min σ R with ha
  have ha0 : 0 ≤ a := le_min hσ hR.le
  have haR : a ≤ R := min_le_right _ _
  have hd : 0 ≤ σ - a := sub_min_nonneg hσ hR.le
  have hself : a ^ (p - 2) * a = a ^ (p - 1) := rpow_mul_self hp ha0
  have hkey : a ^ (p - 2) ≤ (p - 1) * R ^ (p - 2) := by
    have h1 : a ^ (p - 2) ≤ R ^ (p - 2) := Real.rpow_le_rpow ha0 haR (by linarith)
    nlinarith [Real.rpow_nonneg hR.le (p - 2)]
  rw [truncPowDeriv_eq_add hR.le hσ, truncWeight, ← ha]
  nlinarith

theorem truncPowDeriv_le_const (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R) {σ : ℝ} (hσ : 0 ≤ σ) :
    truncPowDeriv p R σ ≤ (p - 1) * R ^ (p - 2) * σ := by
  set a := min σ R with ha
  have ha0 : 0 ≤ a := le_min hσ hR.le
  have haR : a ≤ R := min_le_right _ _
  have hself : a ^ (p - 2) * a = a ^ (p - 1) := rpow_mul_self hp ha0
  have hkey : a ^ (p - 1) ≤ (p - 1) * R ^ (p - 2) * a := by
    have h1 : a ^ (p - 2) ≤ R ^ (p - 2) := Real.rpow_le_rpow ha0 haR (by linarith)
    have h3 : a ^ (p - 1) ≤ R ^ (p - 2) * a := by
      rw [← hself]; exact mul_le_mul_of_nonneg_right h1 ha0
    have h4 : 0 ≤ R ^ (p - 2) * a := mul_nonneg (Real.rpow_nonneg hR.le _) ha0
    nlinarith [h3, h4]
  rw [truncPowDeriv_eq_add hR.le hσ, ← ha]
  linarith

/-! ### The four difference bounds (`0 ≤ τ ≤ σ`) -/

theorem le_truncPowDeriv_sub_const (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R) {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    (p - 1) * R ^ (p - 2) * (σ - τ) ≤ truncPowDeriv p R σ - truncPowDeriv p R τ := by
  have hσ : 0 ≤ σ := hτ.trans hτσ
  set a := min σ R with ha
  set b := min τ R with hb
  have hb0 : 0 ≤ b := le_min hτ hR.le
  have hba : b ≤ a := min_le_min hτσ le_rfl
  have haR : a ≤ R := min_le_right _ _
  have h1 := rpow_sub_rpow_ge_const hp hp2 hR hb0 hba haR
  rw [truncPowDeriv_eq_add hR.le hσ, truncPowDeriv_eq_add hR.le hτ, ← ha, ← hb]
  nlinarith

theorem truncPowDeriv_sub_le_weight (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R) {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    truncPowDeriv p R σ - truncPowDeriv p R τ ≤
      (truncWeight p R σ + truncWeight p R τ) * (σ - τ) := by
  have hσ : 0 ≤ σ := hτ.trans hτσ
  rcases eq_or_lt_of_le hσ with hσ0 | hσ0
  · have hτ0 : τ = 0 := le_antisymm (by linarith [hτσ, hσ0.symm]) hτ
    rw [hτ0, ← hσ0]
    simp
  set a := min σ R with ha
  set b := min τ R with hb
  have ha0 : 0 ≤ a := le_min hσ hR.le
  have hapos : 0 < a := lt_min hσ0 hR
  have hb0 : 0 ≤ b := le_min hτ hR.le
  have hba : b ≤ a := min_le_min hτσ le_rfl
  have haR : a ≤ R := min_le_right _ _
  have hdσ : 0 ≤ σ - a := sub_min_nonneg hσ hR.le
  have hdτ : 0 ≤ τ - b := sub_min_nonneg hτ hR.le
  have h1 := rpow_sub_rpow_le_weight hp hp2 hb0 hba
  have hbw : 0 ≤ b ^ (p - 2) := Real.rpow_nonneg hb0 _
  have haw : 0 ≤ a ^ (p - 2) := Real.rpow_nonneg ha0 _
  -- `(p-1) R^{p-2} ≤ a^{p-2}` whenever the affine part contributes
  have hD2 : 0 ≤ (σ - a) - (τ - b) := by
    have := sub_min_mono (R := R) hτσ
    rw [← ha, ← hb] at this
    linarith
  have hcmp : (p - 1) * R ^ (p - 2) ≤ a ^ (p - 2) := by
    have h2 : R ^ (p - 2) ≤ a ^ (p - 2) := Real.rpow_le_rpow_of_nonpos hapos haR (by linarith)
    nlinarith [Real.rpow_nonneg hR.le (p - 2)]
  have hkey : (p - 1) * R ^ (p - 2) * ((σ - a) - (τ - b)) ≤
      a ^ (p - 2) * ((σ - a) - (τ - b)) := mul_le_mul_of_nonneg_right hcmp hD2
  rw [truncPowDeriv_eq_add hR.le hσ, truncPowDeriv_eq_add hR.le hτ, truncWeight, truncWeight,
    ← ha, ← hb]
  have hsplit : σ - τ = (a - b) + ((σ - a) - (τ - b)) := by ring
  nlinarith

theorem weight_le_truncPowDeriv_sub (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R) {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    min (truncWeight p R σ) (truncWeight p R τ) * (σ - τ) ≤
      truncPowDeriv p R σ - truncPowDeriv p R τ := by
  have hσ : 0 ≤ σ := hτ.trans hτσ
  set a := min σ R with ha
  set b := min τ R with hb
  have ha0 : 0 ≤ a := le_min hσ hR.le
  have hb0 : 0 ≤ b := le_min hτ hR.le
  have hba : b ≤ a := min_le_min hτσ le_rfl
  have hbR : b ≤ R := min_le_right _ _
  have hdσ : 0 ≤ σ - a := sub_min_nonneg hσ hR.le
  have hdτ : 0 ≤ τ - b := sub_min_nonneg hτ hR.le
  have hmin : min (a ^ (p - 2)) (b ^ (p - 2)) = b ^ (p - 2) :=
    min_eq_right (Real.rpow_le_rpow hb0 hba (by linarith))
  have h1 := rpow_sub_rpow_ge_weight hp hp2 hb0 hba
  have hkey : b ^ (p - 2) * ((σ - a) - (τ - b)) ≤
      (p - 1) * R ^ (p - 2) * ((σ - a) - (τ - b)) := by
    have hD2 : 0 ≤ (σ - a) - (τ - b) := by
      have := sub_min_mono (R := R) hτσ
      rw [← ha, ← hb] at this
      linarith
    have hcmp : b ^ (p - 2) ≤ (p - 1) * R ^ (p - 2) := by
      have h2 : b ^ (p - 2) ≤ R ^ (p - 2) := Real.rpow_le_rpow hb0 hbR (by linarith)
      nlinarith [Real.rpow_nonneg hR.le (p - 2)]
    exact mul_le_mul_of_nonneg_right hcmp hD2
  rw [truncPowDeriv_eq_add hR.le hσ, truncPowDeriv_eq_add hR.le hτ, truncWeight, truncWeight,
    ← ha, ← hb, hmin]
  nlinarith

theorem truncPowDeriv_sub_le_const (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R) {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    truncPowDeriv p R σ - truncPowDeriv p R τ ≤ (p - 1) * R ^ (p - 2) * (σ - τ) := by
  have hσ : 0 ≤ σ := hτ.trans hτσ
  set a := min σ R with ha
  set b := min τ R with hb
  have hb0 : 0 ≤ b := le_min hτ hR.le
  have hba : b ≤ a := min_le_min hτσ le_rfl
  have haR : a ≤ R := min_le_right _ _
  have h1 := rpow_sub_rpow_le_const hp hp2 hR hb0 hba haR
  rw [truncPowDeriv_eq_add hR.le hσ, truncPowDeriv_eq_add hR.le hτ, ← ha, ← hb]
  nlinarith

end Komlos.Literature.Regularized
