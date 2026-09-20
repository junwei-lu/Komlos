import Komlos.Literature.Regularized.ProfileBasic
import Komlos.Literature.Regularized.Profile

/-!
# The truncated power `h_R` and the truncated profile `Φ_R = h_R ∘ F`

`REGULARIZED_ROUTE.md`, Revision 2, builds the profiles of the class `IsRegProfile` out of a
smooth strictly convex norm `F` and an exponent `p > 1` in three steps:

1. the **truncated power** `h_R : ℝ → ℝ`, equal to `s ↦ s^p/p` on `[0, R]` and continued past
   `R` with the *constant* second derivative `(p-1) R^{p-2}`:
   `h_R(s) = R^p/p + R^{p-1}(s-R) + (p-1) R^{p-2}(s-R)²/2` for `s > R`;
2. the **truncated profile** `Φ_R = h_R ∘ F`, convex and even;
3. its mollification `Ψ_p = Φ_R ∗ ρ_ε` and, finally, the exponent-`2` profile
   `Ψ(q) = Ψ_p((2/p) q)` (`Komlos/Literature/Regularized/TruncatedProfileElliptic.lean`).

This file does steps 1 and 2 and the elementary (non-elliptic) facts about `Ψ_p`.

## Implementation: `h_R` as a primitive

`h_R` is *defined* as the primitive `∫_0^s h_R'` of its (explicit, continuous, monotone,
nonnegative) derivative

`truncPowDeriv p R t = (min t⁺ R)^{p-1} + (p-1) R^{p-2} (t - R)⁺`.

This makes `h_R` differentiable everywhere *including at the junction `s = R`* for free (the
fundamental theorem of calculus for a continuous integrand), and convexity is monotonicity of
`truncPowDeriv`.  The two closed formulas are then recovered by computing the integral
(`truncPow_of_nonneg_of_le` on `[0, R]`).

## Main results

* `truncPow`, `truncPowDeriv`, `hasDerivAt_truncPow`, `convexOn_truncPow`,
  `monotone_truncPow`, `truncPow_nonneg`;
* `truncPow_of_nonneg_of_le : 0 ≤ s → s ≤ R → truncPow p R s = s^p/p`;
* `rpow_div_le_truncPow` (`p ≤ 2`) and `truncPow_le_rpow_div` (`2 ≤ p`): the two-sided
  comparison with `s^p/p`, obtained from the sign of
  `φ(s) = R^{p-1} + (p-1)R^{p-2}(s-R) - s^{p-1}` on `[R, ∞)`, itself the sign of
  `φ'(s) = (p-1)(R^{p-2} - s^{p-2})`;
* `truncProfile p F R = h_R ∘ F`: `convexOn_truncProfile`, `truncProfile_even`,
  `continuous_truncProfile`, `truncProfile_nonneg`, and the comparisons with `F^p/p`;
* `truncSmoothedProfile p F R ρ = Φ_R ∗ ρ`: smoothness, convexity, evenness, and
  `le_mollifyWith_of_convexOn` (Jensen for an even probability kernel), which gives
  `Φ_R ≤ Ψ_p`, together with the upper comparison `Ψ_p ≤ h_R(F + Mε)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The truncated power `h_R` -/

/-- The derivative of the truncated power: `t ↦ (min t⁺ R)^{p-1} + (p-1) R^{p-2} (t-R)⁺`.
It equals `t^{p-1}` on `[0, R]` and the affine function `R^{p-1} + (p-1)R^{p-2}(t-R)` on
`[R, ∞)`, and it vanishes on `(-∞, 0]`. -/
noncomputable def truncPowDeriv (p R t : ℝ) : ℝ :=
  min (max t 0) R ^ (p - 1) + (p - 1) * R ^ (p - 2) * max (t - R) 0

/-- **The truncated power** `h_R` of `REGULARIZED_ROUTE.md`, Revision 2: the primitive of
`truncPowDeriv` vanishing at `0`.  On `[0, R]` it is `s^p/p`; past `R` it is continued with the
constant second derivative `(p-1)R^{p-2}`. -/
noncomputable def truncPow (p R s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, truncPowDeriv p R t

section Deriv

variable {p R : ℝ}

theorem truncPowDeriv_of_mem (hR : 0 ≤ R) {t : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) :
    truncPowDeriv p R t = t ^ (p - 1) := by
  rw [truncPowDeriv, max_eq_left ht, min_eq_left htR, max_eq_right (by linarith), mul_zero,
    add_zero]

theorem truncPowDeriv_of_ge (hR : 0 ≤ R) {t : ℝ} (htR : R ≤ t) :
    truncPowDeriv p R t = R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (t - R) := by
  rw [truncPowDeriv, max_eq_left (hR.trans htR), min_eq_right htR,
    max_eq_left (by linarith : 0 ≤ t - R)]

/-- `truncPowDeriv` is continuous. -/
theorem continuous_truncPowDeriv (hp : 1 < p) : Continuous (truncPowDeriv p R) := by
  have hrc : Continuous fun x : ℝ => x ^ (p - 1) :=
    continuous_iff_continuousAt.2 fun x =>
      Real.continuousAt_rpow_const x (p - 1) (Or.inr (by linarith))
  exact (hrc.comp ((continuous_id.max continuous_const).min continuous_const)).add
    (continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const))

/-- `truncPowDeriv` is nonnegative. -/
theorem truncPowDeriv_nonneg (hp : 1 < p) (hR : 0 ≤ R) (t : ℝ) : 0 ≤ truncPowDeriv p R t := by
  refine add_nonneg (Real.rpow_nonneg (le_min (le_max_right _ _) hR) _) ?_
  exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hR _)) (le_max_right _ _)

/-- `truncPowDeriv` is monotone: both summands are. -/
theorem monotone_truncPowDeriv (hp : 1 < p) (hR : 0 ≤ R) : Monotone (truncPowDeriv p R) := by
  intro s t hst
  refine add_le_add ?_ ?_
  · exact Real.rpow_le_rpow (le_min (le_max_right _ _) hR)
      (min_le_min (max_le_max hst le_rfl) le_rfl) (by linarith)
  · exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl)
      (mul_nonneg (by linarith) (Real.rpow_nonneg hR _))

theorem intervalIntegrable_truncPowDeriv (hp : 1 < p) (a b : ℝ) :
    IntervalIntegrable (truncPowDeriv p R) volume a b :=
  (continuous_truncPowDeriv hp).intervalIntegrable a b

/-- The fundamental theorem of calculus: `h_R' = truncPowDeriv`, everywhere (in particular at
the junction `s = R`). -/
theorem hasDerivAt_truncPow (hp : 1 < p) (s : ℝ) :
    HasDerivAt (truncPow p R) (truncPowDeriv p R s) s := by
  have hc := continuous_truncPowDeriv (p := p) (R := R) hp
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_truncPowDeriv hp 0 s)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem differentiable_truncPow (hp : 1 < p) : Differentiable ℝ (truncPow p R) :=
  fun s => (hasDerivAt_truncPow hp s).differentiableAt

theorem deriv_truncPow (hp : 1 < p) : deriv (truncPow p R) = truncPowDeriv p R :=
  funext fun s => (hasDerivAt_truncPow hp s).deriv

@[simp] theorem truncPow_zero_arg : truncPow p R 0 = 0 := by simp [truncPow]

/-- `h_R` is monotone (its derivative is nonnegative). -/
theorem monotone_truncPow (hp : 1 < p) (hR : 0 ≤ R) : Monotone (truncPow p R) :=
  monotone_of_deriv_nonneg (differentiable_truncPow hp) fun s => by
    rw [deriv_truncPow hp]; exact truncPowDeriv_nonneg hp hR s

/-- `h_R` is convex (its derivative is monotone). -/
theorem convexOn_truncPow (hp : 1 < p) (hR : 0 ≤ R) : ConvexOn ℝ univ (truncPow p R) := by
  refine MonotoneOn.convexOn_of_deriv convex_univ
    (differentiable_truncPow hp).continuous.continuousOn
    (differentiable_truncPow hp).differentiableOn ?_
  rw [deriv_truncPow hp]
  exact (monotone_truncPowDeriv hp hR).monotoneOn _

theorem truncPow_nonneg (hp : 1 < p) (hR : 0 ≤ R) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ truncPow p R s := by
  simpa using monotone_truncPow hp hR hs

/-- **`h_R(s) = s^p/p` on `[0, R]`.** -/
theorem truncPow_of_nonneg_of_le (hp : 1 < p) (hR : 0 ≤ R) {s : ℝ} (hs : 0 ≤ s) (hsR : s ≤ R) :
    truncPow p R s = s ^ p / p := by
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) s, truncPowDeriv p R t = t ^ (p - 1) := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    exact truncPowDeriv_of_mem hR ht.1 (ht.2.trans hsR)
  rw [truncPow, intervalIntegral.integral_congr hcongr,
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < p - 1))]
  have hpe : p - 1 + 1 = p := by ring
  rw [hpe, Real.zero_rpow (by linarith)]
  ring

end Deriv

/-! ### Comparison of `h_R` with `s^p/p` -/

section Comparison

variable {p R : ℝ}

/-- The gap `φ(s) = R^{p-1} + (p-1)R^{p-2}(s-R) - s^{p-1}` between the continued derivative and
the true derivative, past `R`. -/
private noncomputable def gapDeriv (p R s : ℝ) : ℝ :=
  R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (s - R) - s ^ (p - 1)

private theorem hasDerivAt_gapDeriv (hp : 1 < p) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (gapDeriv p R) ((p - 1) * R ^ (p - 2) - (p - 1) * s ^ (p - 2)) s := by
  have h1 : HasDerivAt (fun x : ℝ => R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (x - R))
      ((p - 1) * R ^ (p - 2)) s := by
    simpa using
      ((((hasDerivAt_id s).sub_const R).const_mul ((p - 1) * R ^ (p - 2))).const_add
        (R ^ (p - 1)))
  have h2 : HasDerivAt (fun x : ℝ => x ^ (p - 1)) ((p - 1) * s ^ (p - 1 - 1)) s :=
    Real.hasDerivAt_rpow_const (Or.inl hs)
  have heq : p - 1 - 1 = p - 2 := by ring
  rw [heq] at h2
  exact h1.sub h2

private theorem continuousOn_gapDeriv (hp : 1 < p) : Continuous (gapDeriv p R) := by
  have hrc : Continuous fun x : ℝ => x ^ (p - 1) :=
    continuous_iff_continuousAt.2 fun x =>
      Real.continuousAt_rpow_const x (p - 1) (Or.inr (by linarith))
  exact ((continuous_const.mul (continuous_id.sub continuous_const)).const_add _).sub hrc

/-- For `p ≤ 2` the continued derivative dominates the true one past `R`. -/
private theorem gapDeriv_nonneg (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R) {s : ℝ} (hs : R ≤ s) :
    0 ≤ gapDeriv p R s := by
  have hmono : MonotoneOn (gapDeriv p R) (Ici R) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici R) (continuousOn_gapDeriv hp).continuousOn
      (fun x hx => (hasDerivAt_gapDeriv (R := R) hp
        (by rw [interior_Ici] at hx;
            exact (hR.trans hx).ne')).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_gapDeriv (R := R) hp (hR.trans hx).ne').deriv]
    have : x ^ (p - 2) ≤ R ^ (p - 2) :=
      Real.rpow_le_rpow_of_nonpos hR hx.le (by linarith)
    nlinarith
  have h0 : gapDeriv p R R = 0 := by simp [gapDeriv]
  have := hmono ((mem_Ici.2 le_rfl)) (mem_Ici.2 hs) hs
  linarith [h0 ▸ this]

/-- For `2 ≤ p` the true derivative dominates the continued one past `R`. -/
private theorem gapDeriv_nonpos (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R) {s : ℝ} (hs : R ≤ s) :
    gapDeriv p R s ≤ 0 := by
  have hanti : AntitoneOn (gapDeriv p R) (Ici R) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici R) (continuousOn_gapDeriv hp).continuousOn
      (fun x hx => (hasDerivAt_gapDeriv (R := R) hp
        (by rw [interior_Ici] at hx;
            exact (hR.trans hx).ne')).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_gapDeriv (R := R) hp (hR.trans hx).ne').deriv]
    have : R ^ (p - 2) ≤ x ^ (p - 2) :=
      Real.rpow_le_rpow hR.le hx.le (by linarith)
    nlinarith
  have h0 : gapDeriv p R R = 0 := by simp [gapDeriv]
  have := hanti ((mem_Ici.2 le_rfl)) (mem_Ici.2 hs) hs
  linarith [h0 ▸ this]

/-- The difference `h_R(s) - s^p/p`, used only inside this section. -/
private noncomputable def truncGap (p R s : ℝ) : ℝ := truncPow p R s - s ^ p / p

private theorem hasDerivAt_truncGap (hp : 1 < p) (hR : 0 ≤ R) {s : ℝ} (hs : R ≤ s) :
    HasDerivAt (truncGap p R) (gapDeriv p R s) s := by
  have h1 := hasDerivAt_truncPow (p := p) (R := R) hp s
  have h2 : HasDerivAt (fun x : ℝ => x ^ p / p) (s ^ (p - 1)) s := by
    have h := (Real.hasDerivAt_rpow_const (x := s) (p := p) (Or.inr hp.le)).div_const p
    have : p * s ^ (p - 1) / p = s ^ (p - 1) := by field_simp
    rwa [this] at h
  have := h1.sub h2
  rwa [truncPowDeriv_of_ge hR hs, show
    R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (s - R) - s ^ (p - 1) = gapDeriv p R s from rfl] at this

private theorem truncGap_eq_zero_at (hp : 1 < p) (hR : 0 < R) : truncGap p R R = 0 := by
  rw [truncGap, truncPow_of_nonneg_of_le hp hR.le hR.le le_rfl, sub_self]

private theorem continuous_truncGap (hp : 1 < p) : Continuous (truncGap p R) := by
  have hrc : Continuous fun x : ℝ => x ^ p :=
    continuous_iff_continuousAt.2 fun x =>
      Real.continuousAt_rpow_const x p (Or.inr (by linarith))
  exact (differentiable_truncPow (R := R) hp).continuous.sub (hrc.div_const p)

/-- **`s^p/p ≤ h_R(s)` for `1 < p ≤ 2`** (`REGULARIZED_ROUTE.md`, Revision 2: "For `p ≤ 2`:
`h_R ≥ s^p/p`, so the lower scalar bound is Jensen"). -/
theorem rpow_div_le_truncPow (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R) {s : ℝ} (hs : 0 ≤ s) :
    s ^ p / p ≤ truncPow p R s := by
  rcases le_or_gt s R with hsR | hsR
  · rw [truncPow_of_nonneg_of_le hp hR.le hs hsR]
  · have hmono : MonotoneOn (truncGap p R) (Ici R) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici R) (continuous_truncGap hp).continuousOn
        (fun x hx => (hasDerivAt_truncGap hp hR.le
          (by rw [interior_Ici] at hx;
              exact hx.le)).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_truncGap hp hR.le hx.le).deriv]
      exact gapDeriv_nonneg hp hp2 hR hx.le
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hsR.le) hsR.le
    rw [truncGap_eq_zero_at hp hR] at this
    simpa [truncGap, sub_nonneg] using this

/-- **`h_R(s) ≤ s^p/p` for `2 ≤ p`** (`REGULARIZED_ROUTE.md`, Revision 2: "For `p > 2`:
`Ψ_p ≤ (F+Mε)^p/p` gives the upper bound"). -/
theorem truncPow_le_rpow_div (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R) {s : ℝ} (hs : 0 ≤ s) :
    truncPow p R s ≤ s ^ p / p := by
  rcases le_or_gt s R with hsR | hsR
  · rw [truncPow_of_nonneg_of_le hp hR.le hs hsR]
  · have hanti : AntitoneOn (truncGap p R) (Ici R) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici R) (continuous_truncGap hp).continuousOn
        (fun x hx => (hasDerivAt_truncGap hp hR.le
          (by rw [interior_Ici] at hx;
              exact hx.le)).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_truncGap hp hR.le hx.le).deriv]
      exact gapDeriv_nonpos hp hp2 hR hx.le
    have := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hsR.le) hsR.le
    rw [truncGap_eq_zero_at hp hR] at this
    simpa [truncGap, sub_nonpos] using this

/-- For a fixed `s ≥ 0` the truncated power is eventually (in the truncation level) the
untruncated one.  This is the `R → ∞` half of the scalar limits. -/
theorem eventually_truncPow_eq {p : ℝ} (hp : 1 < p) {s : ℝ} (hs : 0 ≤ s) :
    ∀ᶠ r : ℝ in atTop, truncPow p r s = s ^ p / p := by
  filter_upwards [eventually_ge_atTop s, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  exact truncPow_of_nonneg_of_le hp hr0 hs hr

/-- The gap `s^p/p + θ s² - h_R(s)`, used only inside this section. -/
private noncomputable def quadGap (p R θ s : ℝ) : ℝ := s ^ p / p + θ * s ^ 2 - truncPow p R s

private theorem hasDerivAt_quadGap {p R θ : ℝ} (hp : 1 < p) (hR : 0 ≤ R) {s : ℝ} (hs : R ≤ s) :
    HasDerivAt (quadGap p R θ)
      (s ^ (p - 1) + θ * (2 * s) - (R ^ (p - 1) + (p - 1) * R ^ (p - 2) * (s - R))) s := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ p / p) (s ^ (p - 1)) s := by
    have h := (Real.hasDerivAt_rpow_const (x := s) (p := p) (Or.inr hp.le)).div_const p
    have he : p * s ^ (p - 1) / p = s ^ (p - 1) := by field_simp
    rwa [he] at h
  have h2 : HasDerivAt (fun x : ℝ => θ * x ^ 2) (θ * (2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_mul θ
  have h3 := hasDerivAt_truncPow (p := p) (R := R) hp s
  rw [truncPowDeriv_of_ge hR hs] at h3
  exact (h1.add h2).sub h3

private theorem continuous_quadGap {p R θ : ℝ} (hp : 1 < p) : Continuous (quadGap p R θ) := by
  have hrc : Continuous fun x : ℝ => x ^ p :=
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x p (Or.inr (by linarith))
  exact ((hrc.div_const p).add (continuous_const.mul (continuous_pow 2))).sub
    (differentiable_truncPow (R := R) hp).continuous

/-- **`h_R(s) ≤ s^p/p + (p-1) R^{p-2} s²/2`, for every `p > 1`.**  Past `R` the gap
`s^p/p + θ s² - h_R(s)` has derivative `s^{p-1} - R^{p-1} + (p-1) R^{p-1} ≥ 0`, and at `s = R`
it equals `θ R² ≥ 0`.  This is the bound that carries the truncation error of the upper scalar
limit for `p < 2`, where `R^{p-2} → 0`. -/
theorem truncPow_le_rpow_div_add_sq {p R : ℝ} (hp : 1 < p) (hR : 0 < R) {s : ℝ} (hs : 0 ≤ s) :
    truncPow p R s ≤ s ^ p / p + (p - 1) * R ^ (p - 2) / 2 * s ^ 2 := by
  set θ : ℝ := (p - 1) * R ^ (p - 2) / 2 with hθdef
  have hRp : (0 : ℝ) < R ^ (p - 2) := Real.rpow_pos_of_pos hR _
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  rcases le_or_gt s R with hsR | hsR
  · rw [truncPow_of_nonneg_of_le hp hR.le hs hsR]
    nlinarith [sq_nonneg s]
  · have hRpow : R ^ (p - 2) * R = R ^ (p - 1) := by
      have h := Real.rpow_add hR (p - 2) 1
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    have hmono : MonotoneOn (quadGap p R θ) (Ici R) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici R) (continuous_quadGap hp).continuousOn
        (fun x hx => (hasDerivAt_quadGap hp hR.le
          (by rw [interior_Ici] at hx; exact hx.le)).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_quadGap hp hR.le hx.le).deriv]
      have h1 : R ^ (p - 1) ≤ x ^ (p - 1) := Real.rpow_le_rpow hR.le hx.le (by linarith)
      have h2 : θ * (2 * x) = (p - 1) * R ^ (p - 2) * x := by rw [hθdef]; ring
      have h3 : (0 : ℝ) < R ^ (p - 1) := Real.rpow_pos_of_pos hR _
      rw [h2]
      nlinarith [h1, h3, hRpow]
    have hG0 : 0 ≤ quadGap p R θ R := by
      show 0 ≤ R ^ p / p + θ * R ^ 2 - truncPow p R R
      rw [truncPow_of_nonneg_of_le hp hR.le hR.le le_rfl]
      nlinarith [sq_nonneg R]
    have hle := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hsR.le) hsR.le
    have hq : quadGap p R θ s = s ^ p / p + θ * s ^ 2 - truncPow p R s := rfl
    rw [hq] at hle
    linarith [hG0, hle]

end Comparison

/-! ### The truncated profile `Φ_R = h_R ∘ F` -/

section Profile

variable {p R : ℝ} {F : Euc d → ℝ}

/-- **The truncated profile** `Φ_R(q) = h_R(F q)` (`REGULARIZED_ROUTE.md`, Revision 2). -/
noncomputable def truncProfile (p : ℝ) (F : Euc d → ℝ) (R : ℝ) : Euc d → ℝ :=
  fun q => truncPow p R (F q)

theorem continuous_truncProfile (hp : 1 < p) (hF : IsSmoothStrictNorm F) :
    Continuous (truncProfile p F R) :=
  (differentiable_truncPow (R := R) hp).continuous.comp hF.continuous

theorem truncProfile_nonneg (hp : 1 < p) (hR : 0 ≤ R) (hF : IsSmoothStrictNorm F) (q : Euc d) :
    0 ≤ truncProfile p F R q :=
  truncPow_nonneg hp hR (hF.nonneg q)

theorem truncProfile_even (hF : IsSmoothStrictNorm F) (q : Euc d) :
    truncProfile p F R (-q) = truncProfile p F R q := by
  simp [truncProfile, hF.even]

/-- `Φ_R` is convex: `h_R` is convex and monotone, `F` is convex. -/
theorem convexOn_truncProfile (hp : 1 < p) (hR : 0 ≤ R) (hF : IsSmoothStrictNorm F) :
    ConvexOn ℝ univ (truncProfile p F R) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hFc := hF.convexOn.2 (mem_univ x) (mem_univ y) ha hb hab
  have hconv := (convexOn_truncPow (R := R) hp hR).2 (mem_univ (F x)) (mem_univ (F y)) ha hb hab
  simp only [smul_eq_mul] at hFc hconv ⊢
  exact (monotone_truncPow (R := R) hp hR hFc).trans hconv

/-- On the set where `F ≤ R` the truncated profile is the untruncated one. -/
theorem truncProfile_of_le (hp : 1 < p) (hR : 0 ≤ R) (hF : IsSmoothStrictNorm F) {q : Euc d}
    (hq : F q ≤ R) : truncProfile p F R q = F q ^ p / p :=
  truncPow_of_nonneg_of_le hp hR (hF.nonneg q) hq

/-- `F^p/p ≤ Φ_R` for `1 < p ≤ 2`. -/
theorem rpow_div_le_truncProfile (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (q : Euc d) : F q ^ p / p ≤ truncProfile p F R q :=
  rpow_div_le_truncPow hp hp2 hR (hF.nonneg q)

/-- `Φ_R ≤ F^p/p` for `2 ≤ p`. -/
theorem truncProfile_le_rpow_div (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (q : Euc d) : truncProfile p F R q ≤ F q ^ p / p :=
  truncPow_le_rpow_div hp hp2 hR (hF.nonneg q)

end Profile

/-! ### Jensen's inequality for an even mollifier -/

/-- **Jensen's inequality for mollification by an even probability kernel**: a convex `Φ`
satisfies `Φ q ≤ (Φ ∗ ρ)(q)`.  The kernel is even, so the mollification at `q` is the average
of the midpoint averages `(Φ(q-y) + Φ(q+y))/2 ≥ Φ(q)`; no differentiability of `Φ` is used.
(This is `Komlos.Literature.Regularized.le_smoothedProfile` for a general convex `Φ`.) -/
theorem le_mollifyWith_of_convexOn {ρ Φ : Euc d → ℝ} {ε : ℝ} (hρ : IsMollifier ρ ε)
    (hΦc : Continuous Φ) (hΦ : ConvexOn ℝ univ Φ) (q : Euc d) : Φ q ≤ mollifyWith ρ Φ q := by
  have hi1 : Integrable fun y : Euc d => ρ y * Φ (q - y) :=
    (hρ.continuous.mul
      (hΦc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρ.hasCompactSupport.mul_right
  have hi2 : Integrable fun y : Euc d => ρ y * Φ (q + y) :=
    (hρ.continuous.mul
      (hΦc.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
      hρ.hasCompactSupport.mul_right
  have hi0 : Integrable fun y : Euc d => ρ y * (2 * Φ q) := hρ.integrable.mul_const _
  have hJI : (∫ y, ρ y * Φ (q + y)) = ∫ y, ρ y * Φ (q - y) := by
    calc (∫ y, ρ y * Φ (q + y))
        = ∫ y, ρ (-y) * Φ (q + -y) :=
          (integral_neg_eq_self (fun y : Euc d => ρ y * Φ (q + y)) volume).symm
      _ = ∫ y, ρ y * Φ (q - y) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          show ρ (-y) * Φ (q + -y) = ρ y * Φ (q - y)
          rw [hρ.even, ← sub_eq_add_neg]
  have hmid : ∀ y : Euc d, ρ y * (2 * Φ q) ≤ ρ y * Φ (q - y) + ρ y * Φ (q + y) := by
    intro y
    have hconv := hΦ.2 (mem_univ (q - y)) (mem_univ (q + y)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have heq : (1 / 2 : ℝ) • (q - y) + (1 / 2 : ℝ) • (q + y) = q := by module
    rw [heq] at hconv
    simp only [smul_eq_mul] at hconv
    have hfin : 2 * Φ q ≤ Φ (q - y) + Φ (q + y) := by linarith
    have := mul_le_mul_of_nonneg_left hfin (hρ.nonneg y)
    linarith
  have hstep : 2 * Φ q ≤ 2 * ∫ y, ρ y * Φ (q - y) := by
    calc 2 * Φ q = ∫ y, ρ y * (2 * Φ q) := by
          rw [integral_mul_const, hρ.integral_eq_one, one_mul]
      _ ≤ ∫ y, (ρ y * Φ (q - y) + ρ y * Φ (q + y)) := integral_mono hi0 (hi1.add hi2) hmid
      _ = (∫ y, ρ y * Φ (q - y)) + ∫ y, ρ y * Φ (q + y) := integral_add hi1 hi2
      _ = 2 * ∫ y, ρ y * Φ (q - y) := by rw [hJI]; ring
  rw [Korevaar.mollifyWith_eq_kernel_integral]
  linarith

/-! ### The mollified truncated profile `Ψ_p = Φ_R ∗ ρ` -/

section Smoothed

variable {p R ε : ℝ} {F ρ : Euc d → ℝ}

/-- **The mollified truncated profile** `Ψ_p = Φ_R ∗ ρ_ε` (`REGULARIZED_ROUTE.md`,
Revision 2).  It is the `p`-exponent profile; the exponent-`2` profile of the interface is
`Ψ(q) = Ψ_p((2/p) q)` (`Komlos/Literature/Regularized/TruncatedProfileElliptic.lean`). -/
noncomputable def truncSmoothedProfile (p : ℝ) (F : Euc d → ℝ) (R : ℝ) (ρ : Euc d → ℝ) :
    Euc d → ℝ := mollifyWith ρ (truncProfile p F R)

theorem contDiff_truncSmoothedProfile (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) : ContDiff ℝ ∞ (truncSmoothedProfile p F R ρ) :=
  contDiff_mollifyWith hρ.contDiff hρ.hasCompactSupport
    (continuous_truncProfile hp hF).locallyIntegrable

theorem convexOn_truncSmoothedProfile (hp : 1 < p) (hR : 0 ≤ R) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) : ConvexOn ℝ univ (truncSmoothedProfile p F R ρ) :=
  Korevaar.convexOn_mollifyWith hρ.continuous hρ.hasCompactSupport hρ.nonneg
    (continuous_truncProfile hp hF) (convexOn_truncProfile hp hR hF)

theorem truncSmoothedProfile_even (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε)
    (q : Euc d) : truncSmoothedProfile p F R ρ (-q) = truncSmoothedProfile p F R ρ q :=
  Korevaar.mollifyWith_even hρ.even (truncProfile_even hF) q

/-- `Φ_R ≤ Ψ_p` (Jensen). -/
theorem truncProfile_le_truncSmoothedProfile (hp : 1 < p) (hR : 0 ≤ R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) (q : Euc d) :
    truncProfile p F R q ≤ truncSmoothedProfile p F R ρ q :=
  le_mollifyWith_of_convexOn hρ (continuous_truncProfile hp hF) (convexOn_truncProfile hp hR hF) q

theorem truncSmoothedProfile_nonneg (hp : 1 < p) (hR : 0 ≤ R) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) (q : Euc d) : 0 ≤ truncSmoothedProfile p F R ρ q :=
  (truncProfile_nonneg hp hR hF q).trans (truncProfile_le_truncSmoothedProfile hp hR hF hρ q)

/-- **The upper comparison** `Ψ_p(q) ≤ h_R(F q + M ε)`, with `M ≥ 0` depending only on `F`:
on the support of `ρ` the triangle inequality gives `F(q - y) ≤ F q + M ε`, and `h_R` is
monotone. -/
theorem exists_truncSmoothedProfile_le (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 0 ≤ R → ∀ (ρ : Euc d → ℝ) (ε : ℝ), IsMollifier ρ ε →
      ∀ q : Euc d, truncSmoothedProfile p F R ρ q ≤ truncPow p R (F q + M * ε) := by
  obtain ⟨M₀, hM₀⟩ := hF.exists_le_mul_norm
  refine ⟨max M₀ 0, le_max_right _ _, fun R hR ρ ε hρ q => ?_⟩
  have hM0 : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have hi1 : Integrable fun y : Euc d => ρ y * truncProfile p F R (q - y) :=
    (hρ.continuous.mul ((continuous_truncProfile hp hF).comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρ.hasCompactSupport.mul_right
  have hi2 : Integrable fun y : Euc d => ρ y * truncPow p R (F q + max M₀ 0 * ε) :=
    hρ.integrable.mul_const _
  have hle : ∀ y : Euc d, ρ y * truncProfile p F R (q - y) ≤
      ρ y * truncPow p R (F q + max M₀ 0 * ε) := by
    intro y
    rcases eq_or_ne (ρ y) 0 with h0 | h0
    · simp [h0]
    · have hy : ‖y‖ ≤ ε := hρ.norm_le_of_ne_zero h0
      have htri := hF.map_add_le_add q (-y)
      have hadd : q + -y = q - y := by abel
      rw [hadd, hF.even y] at htri
      have h3 : F y ≤ M₀ * ‖y‖ := hM₀ y
      have h4 : M₀ * ‖y‖ ≤ max M₀ 0 * ‖y‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg y)
      have h5 : max M₀ 0 * ‖y‖ ≤ max M₀ 0 * ε := mul_le_mul_of_nonneg_left hy hM0
      have h1 : F (q - y) ≤ F q + max M₀ 0 * ε := by linarith
      exact mul_le_mul_of_nonneg_left (monotone_truncPow hp hR h1) (hρ.nonneg y)
  rw [truncSmoothedProfile, Korevaar.mollifyWith_eq_kernel_integral]
  calc (∫ y, ρ y * truncProfile p F R (q - y))
      ≤ ∫ y, ρ y * truncPow p R (F q + max M₀ 0 * ε) := integral_mono hi1 hi2 hle
    _ = truncPow p R (F q + max M₀ 0 * ε) := by
        rw [integral_mul_const, hρ.integral_eq_one, one_mul]

end Smoothed

end Komlos.Literature.Regularized
