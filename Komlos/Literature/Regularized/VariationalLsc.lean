import Komlos.Literature.Regularized.VariationalWeakLimit

/-!
# Lower semicontinuity of the kinetic energy

Lane `L1` (`reg/variational`).  This is the analytic core of the direct method: the kinetic
functional `w ↦ ∫ w² Ψ(∇w/w)` is sequentially lower semicontinuous along sequences that
converge **strongly in `L²`** with **weakly convergent gradients**.

## The mechanism

Write `Q̂(s, ξ) = s² (Ψ(ξ/s) - Ψ 0)` (`kineticDensityNorm`); by `IsRegProfileWith` it satisfies
`(c/2)‖ξ‖² ≤ Q̂(s,ξ) ≤ (C/2)‖ξ‖²`, so it is nonnegative, and
`∫ Q(u, ∇u) = ∫ Q̂(u, ∇u) + Ψ 0` for a normalized competitor.

`Q̂` is *not* jointly convex in `(s, ξ)`; it is the **perspective** of a convex function in the
variables `(ρ, ∇ρ) = (s², 2 s ξ)`, hence jointly convex there.  Its supporting hyperplane at a
point `(t, ζ)` with `t > 0`, written back in the `(s, ξ)` variables, is
`kineticDensityNorm_supporting`:

`Q̂(t,ζ) + A · (s² - t²) + ⟪∇Ψ(q₀), s • ξ - t • ζ⟫ ≤ Q̂(s,ξ)`,  `q₀ = ζ/t`,
`A = Ψ(q₀) - Ψ 0 - ⟪∇Ψ(q₀), q₀⟫`,

which is *affine in `(s², s ξ)`* — exactly the combination controlled by strong `L²`
convergence of `w n` and weak `L²` convergence of `∇w n`.

The coefficients `A` and `∇Ψ(q₀)` are unbounded near `{v = 0}`, so the inequality is multiplied
by a continuous cut-off `θ_k = cutLow k (v ·) · cutHigh k ‖∇v ·‖` which vanishes unless
`v > 1/(k+1)` and `‖∇v‖ < k+1`; on its support `‖q₀‖ < (k+1)²`, so `θ_k A` and `θ_k ∇Ψ(q₀)` are
bounded.  Letting `k → ∞` (dominated convergence, using `∇v = 0` a.e. on `{v = 0}`) finishes.

## Main result

* `le_of_tendsto_integral_kineticDensityNorm`: if `w n → v` strongly in `L²`, `∇w n ⇀ ∇v`
  weakly in `L²`, the Dirichlet integrals are bounded, and `∫ Q̂(w n, ∇w n) → α`, then
  `∫ Q̂(v, ∇v) ≤ α`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### The normalized kinetic density -/

/-- The kinetic density normalized to vanish at `ξ = 0`: `Q̂(s,ξ) = s² (Ψ(ξ/s) - Ψ 0)`. -/
noncomputable def kineticDensityNorm (Ψ : Euc d → ℝ) (s : ℝ) (ξ : Euc d) : ℝ :=
  s ^ 2 * (Ψ (s⁻¹ • ξ) - Ψ 0)

theorem homogeneousDensity_two_eq_add (Ψ : Euc d → ℝ) (s : ℝ) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ s ξ = kineticDensityNorm Ψ s ξ + Ψ 0 * s ^ 2 := by
  rw [homogeneousDensity_two, kineticDensityNorm]
  ring

@[simp] theorem kineticDensityNorm_zero (Ψ : Euc d → ℝ) (ξ : Euc d) :
    kineticDensityNorm Ψ 0 ξ = 0 := by
  simp [kineticDensityNorm]

/-! ### The supporting hyperplane of the perspective -/

/-- **The supporting-hyperplane inequality for the perspective.**  In the variables
`(ρ, m) = (s², 2 s ξ)` the density `Q̂` is the perspective of the convex function `Ψ - Ψ 0`,
hence jointly convex; this is its tangent-plane inequality at a base point `(t, ζ)` with
`t > 0`, rewritten in the `(s, ξ)` variables.  It holds for **all** `s ≥ 0` and all `ξ`. -/
theorem kineticDensityNorm_supporting (h : IsRegProfileWith Ψ c C) {t : ℝ} (ht : 0 < t)
    (ζ : Euc d) {s : ℝ} (hs : 0 ≤ s) (ξ : Euc d) :
    kineticDensityNorm Ψ t ζ
        + (Ψ (t⁻¹ • ζ) - Ψ 0 - ⟪gradient Ψ (t⁻¹ • ζ), t⁻¹ • ζ⟫) * (s ^ 2 - t ^ 2)
        + ⟪gradient Ψ (t⁻¹ • ζ), s • ξ - t • ζ⟫ ≤ kineticDensityNorm Ψ s ξ := by
  rcases hs.lt_or_eq with hpos | hzero
  · -- `s > 0`: the inequality is the convexity of `Ψ` at `q₀ = ζ/t`, scaled by `s²`
    have hconv : Ψ (t⁻¹ • ζ) + ⟪gradient Ψ (t⁻¹ • ζ), s⁻¹ • ξ - t⁻¹ • ζ⟫ ≤ Ψ (s⁻¹ • ξ) := by
      have hh := h.add_inner_add_half_le (t⁻¹ • ζ) (s⁻¹ • ξ - t⁻¹ • ζ)
      have h2 : t⁻¹ • ζ + (s⁻¹ • ξ - t⁻¹ • ζ) = s⁻¹ • ξ := by abel
      rw [h2] at hh
      have h3 : 0 ≤ c / 2 * ‖s⁻¹ • ξ - t⁻¹ • ζ‖ ^ 2 :=
        mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
      linarith
    rw [inner_sub_right] at hconv
    have h5 := mul_le_mul_of_nonneg_left hconv (sq_nonneg s)
    have e1 : ⟪gradient Ψ (t⁻¹ • ζ), s • ξ - t • ζ⟫
        = s ^ 2 * ⟪gradient Ψ (t⁻¹ • ζ), s⁻¹ • ξ⟫
          - t ^ 2 * ⟪gradient Ψ (t⁻¹ • ζ), t⁻¹ • ζ⟫ := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right]
      field_simp
      try ring
    rw [e1, kineticDensityNorm, kineticDensityNorm]
    linarith [h5]
  · -- `s = 0`: both sides vanish
    have e0 : ⟪gradient Ψ (t⁻¹ • ζ), (0 : ℝ) • ξ - t • ζ⟫
        = -(t ^ 2 * ⟪gradient Ψ (t⁻¹ • ζ), t⁻¹ • ζ⟫) := by
      rw [zero_smul, zero_sub, inner_neg_right, real_inner_smul_right, real_inner_smul_right]
      field_simp
      try ring
    rw [← hzero, e0, kineticDensityNorm_zero, kineticDensityNorm]
    linarith

/-! ### The continuous cut-offs -/

/-- Cut-off in the value variable: `0` for `t ≤ 1/(k+1)`, `1` for `t ≥ 2/(k+1)`. -/
noncomputable def cutLow (k : ℕ) (t : ℝ) : ℝ := min 1 (max 0 ((k + 1) * t - 1))

/-- Cut-off in the gradient variable: `1` for `r ≤ k`, `0` for `r ≥ k+1`. -/
noncomputable def cutHigh (k : ℕ) (r : ℝ) : ℝ := min 1 (max 0 ((k + 1) - r))

theorem cutLow_nonneg (k : ℕ) (t : ℝ) : 0 ≤ cutLow k t :=
  le_min zero_le_one (le_max_left _ _)

theorem cutLow_le_one (k : ℕ) (t : ℝ) : cutLow k t ≤ 1 := min_le_left _ _

theorem cutHigh_nonneg (k : ℕ) (r : ℝ) : 0 ≤ cutHigh k r :=
  le_min zero_le_one (le_max_left _ _)

theorem cutHigh_le_one (k : ℕ) (r : ℝ) : cutHigh k r ≤ 1 := min_le_left _ _

theorem continuous_cutLow (k : ℕ) : Continuous (cutLow k) :=
  continuous_const.min (continuous_const.max ((continuous_const.mul continuous_id).sub
    continuous_const))

theorem continuous_cutHigh (k : ℕ) : Continuous (cutHigh k) :=
  continuous_const.min (continuous_const.max (continuous_const.sub continuous_id))

/-- On the support of `cutLow k`, the value is bounded below. -/
theorem lt_of_cutLow_ne_zero {k : ℕ} {t : ℝ} (h : cutLow k t ≠ 0) :
    1 / ((k : ℝ) + 1) < t := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  by_contra hle
  push Not at hle
  have h1 : ((k : ℝ) + 1) * t - 1 ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hle hk.le
    rw [mul_one_div, div_self hk.ne'] at this
    linarith
  exact h (by simp [cutLow, max_eq_left h1])

/-- On the support of `cutHigh k`, the gradient norm is bounded above. -/
theorem lt_of_cutHigh_ne_zero {k : ℕ} {r : ℝ} (h : cutHigh k r ≠ 0) : r < (k : ℝ) + 1 := by
  by_contra hle
  push Not at hle
  have h1 : ((k : ℝ) + 1) - r ≤ 0 := by linarith
  exact h (by simp [cutHigh, max_eq_left h1])

theorem tendsto_cutLow {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => cutLow k t) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / t)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkN : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
  have h2 : 2 / t < (k : ℝ) + 1 := by linarith
  have h3 : 2 ≤ ((k : ℝ) + 1) * t := by
    rw [div_lt_iff₀ ht] at h2
    linarith
  have h4 : 1 ≤ ((k : ℝ) + 1) * t - 1 := by linarith
  simp [cutLow, max_eq_right (by linarith : (0:ℝ) ≤ ((k : ℝ) + 1) * t - 1), min_eq_left h4]

theorem tendsto_cutHigh (r : ℝ) : Tendsto (fun k : ℕ => cutHigh k r) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt r
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkN : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
  have h4 : 1 ≤ ((k : ℝ) + 1) - r := by linarith
  simp [cutHigh, max_eq_right (by linarith : (0:ℝ) ≤ ((k : ℝ) + 1) - r), min_eq_left h4]

/-! ### The normalized density for admissible competitors -/

namespace IsRegAdmissible

/-- An admissible competitor lies in `L²` (with the `ℝ≥0∞` exponent `2`). -/
theorem memLp2 (hu : IsRegAdmissible 2 K u) : MemLp u 2 (volume : Measure (Euc d)) := by
  have h := hu.memW0.memLp
  rwa [ofReal_two] at h

theorem memLp2_weakGrad (hu : IsRegAdmissible 2 K u) :
    MemLp (weakGrad u) 2 (volume : Measure (Euc d)) := by
  have h := hu.memW0.memLp_weakGrad
  rwa [ofReal_two] at h

/-- An admissible competitor is a unit vector of `L²`. -/
theorem toReal_eLpNorm_eq_one (hu : IsRegAdmissible 2 K u) :
    (eLpNorm u 2 (volume : Measure (Euc d))).toReal = 1 := by
  have h1 := toReal_eLpNorm_sq hu.memLp2
  rw [hu.integral_sq] at h1
  have h2 : (0 : ℝ) ≤ (eLpNorm u 2 (volume : Measure (Euc d))).toReal := ENNReal.toReal_nonneg
  nlinarith [h1]

theorem integrable_kineticNorm (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    Integrable (fun x => kineticDensityNorm Ψ (u x) (weakGrad u x)) volume := by
  have hk := hu.integrable_kinetic h hK
  simp only [homogeneousDensity_two_eq_add] at hk
  refine (hk.sub (hu.integrable_sq.const_mul (Ψ 0))).congr
    (Eventually.of_forall fun x => ?_)
  show kineticDensityNorm Ψ (u x) (weakGrad u x) + Ψ 0 * u x ^ 2 - Ψ 0 * u x ^ 2
    = kineticDensityNorm Ψ (u x) (weakGrad u x)
  ring

theorem ae_kineticNorm_nonneg (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    ∀ᵐ x, c / 2 * ‖weakGrad u x‖ ^ 2 ≤ kineticDensityNorm Ψ (u x) (weakGrad u x) := by
  filter_upwards [hu.ae_kinetic_bounds h hK] with x hx
  rw [homogeneousDensity_two_eq_add] at hx
  linarith [hx.1]

theorem kineticEnergy_eq_add (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegAdmissible 2 K u) :
    kineticEnergy Ψ u = (∫ x, kineticDensityNorm Ψ (u x) (weakGrad u x)) + Ψ 0 := by
  rw [kineticEnergy]
  simp only [homogeneousDensity_two_eq_add]
  rw [integral_add (hu.integrable_kineticNorm h hK) (hu.integrable_sq.const_mul (Ψ 0)),
    integral_const_mul, hu.integral_sq, mul_one]

end IsRegAdmissible

/-! ### The cut-off supporting-hyperplane step -/

/-- **The affine minorant passes to the limit.**  If `θ` is a bounded nonnegative weight and
`Acoef`, `Bcoef` are bounded coefficients for which the cut-off supporting inequality holds
pointwise, then `∫ θ Q̂(v, ∇v) ≤ α`.  The three terms of the minorant are, respectively,
constant in `n`, controlled by the *strong* `L²` convergence `w n → v`, and controlled by a
mixture of strong convergence and the *weak* convergence of the gradients. -/
theorem integral_cut_le_of_tendsto
    (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    {w : ℕ → Euc d → ℝ} {v : Euc d → ℝ}
    (hw : ∀ n, IsRegAdmissible 2 K (w n)) (hv : IsRegAdmissible 2 K v)
    {B : ℝ} (hB : ∀ n, (eLpNorm (weakGrad (w n)) 2 volume).toReal ≤ B)
    (hstrong : Tendsto (fun n => (eLpNorm (fun x => w n x - v x) 2 volume).toReal) atTop (𝓝 0))
    (hweak : ∀ φ : Euc d → Euc d, MemLp φ 2 volume →
      Tendsto (fun n => ∫ x, ⟪weakGrad (w n) x, φ x⟫) atTop (𝓝 (∫ x, ⟪weakGrad v x, φ x⟫)))
    {α : ℝ}
    (hα : Tendsto (fun n => ∫ x, kineticDensityNorm Ψ (w n x) (weakGrad (w n) x)) atTop (𝓝 α))
    {θ : Euc d → ℝ} {Acoef : Euc d → ℝ} {Bcoef : Euc d → Euc d} {cA cB : ℝ}
    (hθm : AEStronglyMeasurable θ volume) (hθ0 : ∀ x, 0 ≤ θ x) (hθ1 : ∀ x, θ x ≤ 1)
    (hAm : AEStronglyMeasurable Acoef volume) (hAb : ∀ x, |Acoef x| ≤ cA)
    (hBm : AEStronglyMeasurable Bcoef volume) (hBb : ∀ x, ‖Bcoef x‖ ≤ cB)
    (hsupport : ∀ n, ∀ᵐ x,
      θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)
        + Acoef x * (w n x ^ 2 - v x ^ 2)
        + (⟪(w n x) • Bcoef x, weakGrad (w n) x⟫ - ⟪(v x) • Bcoef x, weakGrad v x⟫)
      ≤ θ x * kineticDensityNorm Ψ (w n x) (weakGrad (w n) x)) :
    (∫ x, θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)) ≤ α := by
  have hcA : 0 ≤ cA := le_trans (abs_nonneg _) (hAb 0)
  have hcB : 0 ≤ cB := le_trans (norm_nonneg _) (hBb 0)
  have hB0 : 0 ≤ B := le_trans ENNReal.toReal_nonneg (hB 0)
  -- a uniform bound for `t • Bcoef`
  have hsm : ∀ (t : ℝ) (x : Euc d), ‖t • Bcoef x‖ ≤ cB * ‖t‖ := by
    intro t x
    calc ‖t • Bcoef x‖ = ‖Bcoef x‖ * ‖t‖ := by rw [norm_smul]; ring
      _ ≤ cB * ‖t‖ := mul_le_mul_of_nonneg_right (hBb x) (norm_nonneg _)
  -- `L²` membership of the auxiliary fields
  have hPn : ∀ n, MemLp (fun x => (w n x) • Bcoef x) 2 (volume : Measure (Euc d)) := fun n =>
    (hw n).memLp2.of_le_mul (c := cB) (((hw n).memLp2.aestronglyMeasurable).smul hBm)
      (Eventually.of_forall fun x => hsm _ x)
  have hPv : MemLp (fun x => (v x) • Bcoef x) 2 (volume : Measure (Euc d)) :=
    hv.memLp2.of_le_mul (c := cB) ((hv.memLp2.aestronglyMeasurable).smul hBm)
      (Eventually.of_forall fun x => hsm _ x)
  have hdiff : ∀ n, MemLp (fun x => w n x - v x) 2 (volume : Measure (Euc d)) := fun n =>
    ((hw n).memLp2.sub hv.memLp2).ae_eq (Eventually.of_forall fun _ => rfl)
  have hPdiff : ∀ n, MemLp (fun x => (w n x - v x) • Bcoef x) 2 (volume : Measure (Euc d)) :=
    fun n => (hdiff n).of_le_mul (c := cB) (((hdiff n).aestronglyMeasurable).smul hBm)
      (Eventually.of_forall fun x => hsm _ x)
  -- integrability of the pieces
  have hQv := hv.integrable_kineticNorm h hK
  have hQw : ∀ n, Integrable (fun x => kineticDensityNorm Ψ (w n x) (weakGrad (w n) x)) volume :=
    fun n => (hw n).integrable_kineticNorm h hK
  have hθQ : ∀ g : Euc d → ℝ, Integrable g volume → Integrable (fun x => θ x * g x) volume := by
    intro g hg
    refine Integrable.mono' (g := fun x => |g x|) hg.abs
      (hθm.mul hg.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hθ0 x)]
    exact mul_le_of_le_one_left (abs_nonneg _) (hθ1 x)
  have hAterm : ∀ n, Integrable (fun x => Acoef x * (w n x ^ 2 - v x ^ 2)) volume := by
    intro n
    refine Integrable.mono' (g := fun x => cA * ((w n x) ^ 2 + (v x) ^ 2))
      (((hw n).integrable_sq.add hv.integrable_sq).const_mul cA)
      (hAm.mul ((((hw n).memLp2.aestronglyMeasurable.aemeasurable.pow_const 2).sub
        (hv.memLp2.aestronglyMeasurable.aemeasurable.pow_const 2)).aestronglyMeasurable))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine le_trans (mul_le_mul (hAb x) (abs_sub _ _) (abs_nonneg _) hcA) ?_
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  have hIn : ∀ n, Integrable (fun x => ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫) volume :=
    fun n => integrable_inner_of_memLp (hPn n) (hw n).memLp2_weakGrad
  have hIv : Integrable (fun x => ⟪(v x) • Bcoef x, weakGrad v x⟫) volume :=
    integrable_inner_of_memLp hPv hv.memLp2_weakGrad
  -- the per-`n` inequality
  have hstep : ∀ n,
      (∫ x, θ x * kineticDensityNorm Ψ (v x) (weakGrad v x))
        + (∫ x, Acoef x * (w n x ^ 2 - v x ^ 2))
        + ((∫ x, ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫)
            - ∫ x, ⟪(v x) • Bcoef x, weakGrad v x⟫)
      ≤ ∫ x, kineticDensityNorm Ψ (w n x) (weakGrad (w n) x) := by
    intro n
    have hI1 : Integrable (fun x => θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)
        + Acoef x * (w n x ^ 2 - v x ^ 2)) volume :=
      ((hθQ _ hQv).add (hAterm n)).congr (Eventually.of_forall fun _ => rfl)
    have hI2 : Integrable (fun x => ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫
        - ⟪(v x) • Bcoef x, weakGrad v x⟫) volume :=
      ((hIn n).sub hIv).congr (Eventually.of_forall fun _ => rfl)
    have hIall : Integrable (fun x => (θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)
        + Acoef x * (w n x ^ 2 - v x ^ 2))
        + (⟪(w n x) • Bcoef x, weakGrad (w n) x⟫ - ⟪(v x) • Bcoef x, weakGrad v x⟫)) volume :=
      (hI1.add hI2).congr (Eventually.of_forall fun _ => rfl)
    have e3 : (∫ x, ((θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)
          + Acoef x * (w n x ^ 2 - v x ^ 2))
          + (⟪(w n x) • Bcoef x, weakGrad (w n) x⟫ - ⟪(v x) • Bcoef x, weakGrad v x⟫)))
        = (∫ x, (θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)
            + Acoef x * (w n x ^ 2 - v x ^ 2)))
          + ∫ x, (⟪(w n x) • Bcoef x, weakGrad (w n) x⟫
            - ⟪(v x) • Bcoef x, weakGrad v x⟫) := integral_add hI1 hI2
    have e1 : (∫ x, (θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)
          + Acoef x * (w n x ^ 2 - v x ^ 2)))
        = (∫ x, θ x * kineticDensityNorm Ψ (v x) (weakGrad v x))
          + ∫ x, Acoef x * (w n x ^ 2 - v x ^ 2) := integral_add (hθQ _ hQv) (hAterm n)
    have e2 : (∫ x, (⟪(w n x) • Bcoef x, weakGrad (w n) x⟫
          - ⟪(v x) • Bcoef x, weakGrad v x⟫))
        = (∫ x, ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫)
          - ∫ x, ⟪(v x) • Bcoef x, weakGrad v x⟫ := integral_sub (hIn n) hIv
    have hmono := integral_mono_ae hIall (hθQ _ (hQw n)) (hsupport n)
    rw [e3, e1, e2] at hmono
    refine hmono.trans ?_
    refine integral_mono_ae (hθQ _ (hQw n)) (hQw n) ?_
    filter_upwards [(hw n).ae_kineticNorm_nonneg h hK] with x hx
    have hQ0 : 0 ≤ kineticDensityNorm Ψ (w n x) (weakGrad (w n) x) :=
      le_trans (mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)) hx
    nlinarith [hθ1 x, hθ0 x, hQ0]
  -- the value term tends to `0`
  have hA0 : Tendsto (fun n => ∫ x, Acoef x * (w n x ^ 2 - v x ^ 2)) atTop (𝓝 0) := by
    have hf : ∀ n, MemLp (fun x => Acoef x * (w n x + v x)) 2 (volume : Measure (Euc d)) := by
      intro n
      refine ((hw n).memLp2.add hv.memLp2).of_le_mul (c := cA)
        (hAm.mul ((hw n).memLp2.aestronglyMeasurable.add hv.memLp2.aestronglyMeasurable))
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hAb x) (abs_nonneg _)
    refine squeeze_zero_norm
      (a := fun n => 2 * cA * (eLpNorm (fun x => w n x - v x) 2 volume).toReal)
      (fun n => ?_) (by simpa using hstrong.const_mul (2 * cA))
    have heq : (∫ x, Acoef x * (w n x ^ 2 - v x ^ 2))
        = ∫ x, (Acoef x * (w n x + v x)) * (w n x - v x) :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [Real.norm_eq_abs, heq]
    have hfb : (eLpNorm (fun x => Acoef x * (w n x + v x)) 2 volume).toReal ≤ 2 * cA := by
      refine toReal_eLpNorm_le_of_sq_le (hf n) (by positivity) ?_
      have hbig : (∫ x, (Acoef x * (w n x + v x)) ^ 2)
          ≤ ∫ x, cA ^ 2 * (2 * w n x ^ 2 + 2 * v x ^ 2) := by
        refine integral_mono (integrable_sq_of_memLp (hf n))
          ((((hw n).integrable_sq.const_mul 2).add
            (hv.integrable_sq.const_mul 2)).const_mul (cA ^ 2)) fun x => ?_
        have h1 : (Acoef x) ^ 2 ≤ cA ^ 2 := by
          have hx := hAb x
          nlinarith [abs_nonneg (Acoef x), sq_abs (Acoef x)]
        have h2 : (w n x + v x) ^ 2 ≤ 2 * w n x ^ 2 + 2 * v x ^ 2 := by
          nlinarith [sq_nonneg (w n x - v x)]
        have h3 : (0 : ℝ) ≤ (w n x + v x) ^ 2 := sq_nonneg _
        have h4 : (0 : ℝ) ≤ (Acoef x) ^ 2 := sq_nonneg _
        calc (Acoef x * (w n x + v x)) ^ 2 = (Acoef x) ^ 2 * (w n x + v x) ^ 2 := by ring
          _ ≤ cA ^ 2 * (2 * w n x ^ 2 + 2 * v x ^ 2) := by nlinarith
      refine hbig.trans (le_of_eq ?_)
      rw [integral_const_mul, integral_add ((hw n).integrable_sq.const_mul 2)
        (hv.integrable_sq.const_mul 2), integral_const_mul, integral_const_mul,
        (hw n).integral_sq, hv.integral_sq]
      ring
    calc |∫ x, (Acoef x * (w n x + v x)) * (w n x - v x)|
        ≤ (eLpNorm (fun x => Acoef x * (w n x + v x)) 2 volume).toReal *
            (eLpNorm (fun x => w n x - v x) 2 volume).toReal :=
          abs_integral_mul_le (hf n) (hdiff n)
      _ ≤ 2 * cA * (eLpNorm (fun x => w n x - v x) 2 volume).toReal :=
          mul_le_mul_of_nonneg_right hfb ENNReal.toReal_nonneg
  -- the gradient term converges
  have hBlim : Tendsto (fun n => ∫ x, ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫) atTop
      (𝓝 (∫ x, ⟪(v x) • Bcoef x, weakGrad v x⟫)) := by
    have hsplit : ∀ n, (∫ x, ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫)
        = (∫ x, ⟪(w n x - v x) • Bcoef x, weakGrad (w n) x⟫)
          + ∫ x, ⟪(v x) • Bcoef x, weakGrad (w n) x⟫ := by
      intro n
      rw [← integral_add (integrable_inner_of_memLp (hPdiff n) (hw n).memLp2_weakGrad)
        (integrable_inner_of_memLp hPv (hw n).memLp2_weakGrad)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫
        = ⟪(w n x - v x) • Bcoef x, weakGrad (w n) x⟫ + ⟪(v x) • Bcoef x, weakGrad (w n) x⟫
      have hadd : w n x - v x + v x = w n x := by ring
      rw [← inner_add_left, ← add_smul, hadd]
    simp only [hsplit]
    have h1 : Tendsto (fun n => ∫ x, ⟪(w n x - v x) • Bcoef x, weakGrad (w n) x⟫) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm
        (a := fun n => cB * B * (eLpNorm (fun x => w n x - v x) 2 volume).toReal)
        (fun n => ?_) (by simpa using hstrong.const_mul (cB * B))
      have hfb : (eLpNorm (fun x => (w n x - v x) • Bcoef x) 2 volume).toReal ≤
          cB * (eLpNorm (fun x => w n x - v x) 2 volume).toReal := by
        refine toReal_eLpNorm_le_of_sq_le' (hPdiff n)
          (mul_nonneg hcB ENNReal.toReal_nonneg) ?_
        have hsq := toReal_eLpNorm_sq (hdiff n)
        rw [mul_pow, hsq, ← integral_const_mul]
        refine integral_mono (integrable_normSq_of_memLp (hPdiff n))
          ((integrable_sq_of_memLp (hdiff n)).const_mul (cB ^ 2)) fun x => ?_
        have h1 : ‖(w n x - v x) • Bcoef x‖ ≤ cB * |w n x - v x| := by
          have := hsm (w n x - v x) x
          rwa [Real.norm_eq_abs] at this
        have h2 : (0 : ℝ) ≤ ‖(w n x - v x) • Bcoef x‖ := norm_nonneg _
        nlinarith [sq_abs (w n x - v x), mul_nonneg hcB (abs_nonneg (w n x - v x))]
      rw [Real.norm_eq_abs]
      calc |∫ x, ⟪(w n x - v x) • Bcoef x, weakGrad (w n) x⟫|
          ≤ (eLpNorm (fun x => (w n x - v x) • Bcoef x) 2 volume).toReal *
              (eLpNorm (weakGrad (w n)) 2 volume).toReal :=
            abs_integral_inner_le (hPdiff n) (hw n).memLp2_weakGrad
        _ ≤ (cB * (eLpNorm (fun x => w n x - v x) 2 volume).toReal) * B :=
            mul_le_mul hfb (hB n) ENNReal.toReal_nonneg
              (mul_nonneg hcB ENNReal.toReal_nonneg)
        _ = cB * B * (eLpNorm (fun x => w n x - v x) 2 volume).toReal := by ring
    have h2 : Tendsto (fun n => ∫ x, ⟪(v x) • Bcoef x, weakGrad (w n) x⟫) atTop
        (𝓝 (∫ x, ⟪(v x) • Bcoef x, weakGrad v x⟫)) := by
      have hcomm : ∀ G : Euc d → Euc d, (∫ x, ⟪(v x) • Bcoef x, G x⟫)
          = ∫ x, ⟪G x, (v x) • Bcoef x⟫ :=
        fun G => integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
      simp only [hcomm]
      exact hweak _ hPv
    simpa using h1.add h2
  -- pass to the limit
  have hLHS : Tendsto (fun n =>
      (∫ x, θ x * kineticDensityNorm Ψ (v x) (weakGrad v x))
        + (∫ x, Acoef x * (w n x ^ 2 - v x ^ 2))
        + ((∫ x, ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫)
            - ∫ x, ⟪(v x) • Bcoef x, weakGrad v x⟫)) atTop
      (𝓝 (∫ x, θ x * kineticDensityNorm Ψ (v x) (weakGrad v x))) := by
    have hc1 : Tendsto (fun _ : ℕ =>
        ∫ x, θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)) atTop
        (𝓝 (∫ x, θ x * kineticDensityNorm Ψ (v x) (weakGrad v x))) := tendsto_const_nhds
    have hc2 : Tendsto (fun _ : ℕ => ∫ x, ⟪(v x) • Bcoef x, weakGrad v x⟫) atTop
        (𝓝 (∫ x, ⟪(v x) • Bcoef x, weakGrad v x⟫)) := tendsto_const_nhds
    have hc := (hc1.add hA0).add (hBlim.sub hc2)
    simpa using hc
  exact le_of_tendsto_of_tendsto' hLHS hα hstep

/-! ### Lower semicontinuity -/

section Lsc

variable {w : ℕ → Euc d → ℝ} {v : Euc d → ℝ}

/-- The cut-off weight attached to `v` at level `k`. -/
noncomputable def cutWeight (k : ℕ) (v : Euc d → ℝ) (x : Euc d) : ℝ :=
  cutLow k (v x) * cutHigh k ‖weakGrad v x‖

theorem cutWeight_nonneg (k : ℕ) (v : Euc d → ℝ) (x : Euc d) : 0 ≤ cutWeight k v x :=
  mul_nonneg (cutLow_nonneg _ _) (cutHigh_nonneg _ _)

theorem cutWeight_le_one (k : ℕ) (v : Euc d → ℝ) (x : Euc d) : cutWeight k v x ≤ 1 :=
  mul_le_one₀ (cutLow_le_one _ _) (cutHigh_nonneg _ _) (cutHigh_le_one _ _)

/-- On the support of the cut-off, the value is positive and the scaled gradient is bounded. -/
theorem cutWeight_support {k : ℕ} {v : Euc d → ℝ} {x : Euc d} (hx : cutWeight k v x ≠ 0)
    (_hv0 : 0 ≤ v x) : 0 < v x ∧ ‖(v x)⁻¹ • weakGrad v x‖ ≤ ((k : ℝ) + 1) ^ 2 := by
  have h1 : cutLow k (v x) ≠ 0 := fun hz => hx (by simp [cutWeight, hz])
  have h2 : cutHigh k ‖weakGrad v x‖ ≠ 0 := fun hz => hx (by simp [cutWeight, hz])
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlow := lt_of_cutLow_ne_zero h1
  have hhigh := lt_of_cutHigh_ne_zero h2
  have hvpos : 0 < v x := lt_of_lt_of_le (by positivity) hlow.le
  refine ⟨hvpos, ?_⟩
  have hinv : (v x)⁻¹ ≤ (k : ℝ) + 1 := by
    rw [inv_le_comm₀ hvpos hk]
    rw [one_div] at hlow
    exact hlow.le
  calc ‖(v x)⁻¹ • weakGrad v x‖ = (v x)⁻¹ * ‖weakGrad v x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hvpos)]
    _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) :=
        mul_le_mul hinv hhigh.le (norm_nonneg _) (by positivity)
    _ = ((k : ℝ) + 1) ^ 2 := by ring

/-- **Lower semicontinuity of the normalized kinetic energy.**  If `w n → v` strongly in `L²`,
the gradients converge weakly in `L²` and are bounded, and the kinetic integrals converge to
`α`, then `∫ Q̂(v, ∇v) ≤ α`.

This is the direct-method lower semicontinuity of `REGULARIZED_ROUTE.md`: the integrand is the
perspective of a convex function, so its supporting hyperplane at the limit is affine in
`(w², w ∇w)`; multiplied by the cut-off `cutWeight k v` it has bounded coefficients, and
letting `k → ∞` recovers the full integral by dominated convergence (the weak gradient of `v`
vanishes a.e. on `{v = 0}`, where the density vanishes too). -/
theorem le_of_tendsto_integral_kineticDensityNorm
    (h : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hw : ∀ n, IsRegAdmissible 2 K (w n)) (hv : IsRegAdmissible 2 K v)
    {B : ℝ} (hB : ∀ n, (eLpNorm (weakGrad (w n)) 2 volume).toReal ≤ B)
    (hstrong : Tendsto (fun n => (eLpNorm (fun x => w n x - v x) 2 volume).toReal) atTop (𝓝 0))
    (hweak : ∀ φ : Euc d → Euc d, MemLp φ 2 volume →
      Tendsto (fun n => ∫ x, ⟪weakGrad (w n) x, φ x⟫) atTop (𝓝 (∫ x, ⟪weakGrad v x, φ x⟫)))
    {α : ℝ}
    (hα : Tendsto (fun n => ∫ x, kineticDensityNorm Ψ (w n x) (weakGrad (w n) x)) atTop (𝓝 α)) :
    (∫ x, kineticDensityNorm Ψ (v x) (weakGrad v x)) ≤ α := by
  have hQv := hv.integrable_kineticNorm h hK
  -- the scaled gradient of the limit
  set q₀ : Euc d → Euc d := fun x => (v x)⁻¹ • weakGrad v x with hq₀
  have hq₀m : AEStronglyMeasurable q₀ volume :=
    ((hv.aestronglyMeasurable.aemeasurable.inv).smul
      hv.aestronglyMeasurable_weakGrad.aemeasurable).aestronglyMeasurable
  have hGm : AEStronglyMeasurable (fun x => gradient Ψ (q₀ x)) volume :=
    (h.toIsRegProfile.contDiff_gradient.continuous).comp_aestronglyMeasurable hq₀m
  -- the cut-off step
  have hstep : ∀ k : ℕ,
      (∫ x, cutWeight k v x * kineticDensityNorm Ψ (v x) (weakGrad v x)) ≤ α := by
    intro k
    set Rk : ℝ := ((k : ℝ) + 1) ^ 2 with hRk
    have hRk0 : 0 ≤ Rk := by positivity
    set θ : Euc d → ℝ := cutWeight k v with hθ
    set Acoef : Euc d → ℝ :=
      fun x => θ x * (Ψ (q₀ x) - Ψ 0 - ⟪gradient Ψ (q₀ x), q₀ x⟫) with hAc
    set Bcoef : Euc d → Euc d := fun x => θ x • gradient Ψ (q₀ x) with hBc
    have hθm : AEStronglyMeasurable θ volume := by
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (continuous_cutLow k).comp_aestronglyMeasurable hv.aestronglyMeasurable
      · exact (continuous_cutHigh k).comp_aestronglyMeasurable
          (continuous_norm.comp_aestronglyMeasurable hv.aestronglyMeasurable_weakGrad)
    have hAm : AEStronglyMeasurable Acoef volume :=
      hθm.mul ((((h.toIsRegProfile.contDiff.continuous).comp_aestronglyMeasurable
        hq₀m).sub aestronglyMeasurable_const).sub (AEStronglyMeasurable.inner hGm hq₀m))
    have hBm : AEStronglyMeasurable Bcoef volume := hθm.smul hGm
    -- the bounds
    have hAb : ∀ x, |Acoef x| ≤ 3 * C / 2 * Rk ^ 2 := by
      intro x
      have hθ1x : θ x ≤ 1 := cutWeight_le_one k v x
      have hθ0x : 0 ≤ θ x := cutWeight_nonneg k v x
      by_cases hz : θ x = 0
      · rw [hAc]
        simp only [hz, zero_mul, abs_zero]
        exact mul_nonneg (by linarith [h.C_nonneg]) (by positivity)
      · obtain ⟨hvpos, hqb⟩ := cutWeight_support (v := v) hz (hv.nonneg x)
        have hq2 : ‖q₀ x‖ ^ 2 ≤ Rk ^ 2 := by
          have := norm_nonneg (q₀ x)
          nlinarith [hqb]
        have h1 : 0 ≤ Ψ (q₀ x) - Ψ 0 := by
          have := h.quadratic_lower (q₀ x)
          nlinarith [mul_nonneg (by linarith [h.c_pos] : (0:ℝ) ≤ c / 2)
            (sq_nonneg ‖q₀ x‖)]
        have h2 : Ψ (q₀ x) - Ψ 0 ≤ C / 2 * Rk ^ 2 := by
          have := h.quadratic_upper (q₀ x)
          nlinarith [h.C_nonneg]
        have h3 : |⟪gradient Ψ (q₀ x), q₀ x⟫| ≤ C * Rk ^ 2 := by
          refine le_trans (abs_real_inner_le_norm _ _) ?_
          calc ‖gradient Ψ (q₀ x)‖ * ‖q₀ x‖ ≤ (C * ‖q₀ x‖) * ‖q₀ x‖ :=
                mul_le_mul_of_nonneg_right (h.norm_gradient_le _) (norm_nonneg _)
            _ = C * ‖q₀ x‖ ^ 2 := by ring
            _ ≤ C * Rk ^ 2 := mul_le_mul_of_nonneg_left hq2 h.C_nonneg
        have hbracket : |Ψ (q₀ x) - Ψ 0 - ⟪gradient Ψ (q₀ x), q₀ x⟫| ≤ 3 * C / 2 * Rk ^ 2 := by
          rw [abs_le] at h3 ⊢
          constructor <;> linarith [h3.1, h3.2]
        have habs : |Acoef x| = θ x * |Ψ (q₀ x) - Ψ 0 - ⟪gradient Ψ (q₀ x), q₀ x⟫| := by
          rw [hAc, abs_mul, abs_of_nonneg hθ0x]
        rw [habs]
        nlinarith [abs_nonneg (Ψ (q₀ x) - Ψ 0 - ⟪gradient Ψ (q₀ x), q₀ x⟫),
          mul_nonneg (by linarith [h.C_nonneg] : (0:ℝ) ≤ 3 * C / 2) (sq_nonneg Rk)]
    have hBb : ∀ x, ‖Bcoef x‖ ≤ C * Rk := by
      intro x
      have hθ1x : θ x ≤ 1 := cutWeight_le_one k v x
      have hθ0x : 0 ≤ θ x := cutWeight_nonneg k v x
      by_cases hz : θ x = 0
      · rw [hBc]
        simp only [hz, zero_smul, norm_zero]
        exact mul_nonneg h.C_nonneg hRk0
      · obtain ⟨hvpos, hqb⟩ := cutWeight_support (v := v) hz (hv.nonneg x)
        have hgb : ‖gradient Ψ (q₀ x)‖ ≤ C * Rk :=
          le_trans (h.norm_gradient_le _) (mul_le_mul_of_nonneg_left hqb h.C_nonneg)
        have hnorm : ‖Bcoef x‖ = θ x * ‖gradient Ψ (q₀ x)‖ := by
          rw [hBc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0x]
        rw [hnorm]
        nlinarith [norm_nonneg (gradient Ψ (q₀ x)),
          mul_nonneg (by linarith : (0:ℝ) ≤ 1 - θ x) (norm_nonneg (gradient Ψ (q₀ x)))]
    -- the pointwise supporting inequality
    have hsupport : ∀ n, ∀ᵐ x,
        θ x * kineticDensityNorm Ψ (v x) (weakGrad v x)
          + Acoef x * (w n x ^ 2 - v x ^ 2)
          + (⟪(w n x) • Bcoef x, weakGrad (w n) x⟫ - ⟪(v x) • Bcoef x, weakGrad v x⟫)
        ≤ θ x * kineticDensityNorm Ψ (w n x) (weakGrad (w n) x) := by
      intro n
      refine Eventually.of_forall fun x => ?_
      by_cases hz : θ x = 0
      · simp [hAc, hBc, hz]
      · obtain ⟨hvpos, -⟩ := cutWeight_support (v := v) hz (hv.nonneg x)
        have hsup := kineticDensityNorm_supporting h hvpos (weakGrad v x)
          ((hw n).nonneg x) (weakGrad (w n) x)
        have hmul := mul_le_mul_of_nonneg_left hsup (cutWeight_nonneg k v x)
        have hinner : ⟪(w n x) • Bcoef x, weakGrad (w n) x⟫
            - ⟪(v x) • Bcoef x, weakGrad v x⟫
            = θ x * ⟪gradient Ψ (q₀ x),
                (w n x) • weakGrad (w n) x - (v x) • weakGrad v x⟫ := by
          rw [hBc, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
          simp only [real_inner_smul_left]
          ring
        rw [hinner, hAc]
        simp only [hθ] at hmul ⊢
        nlinarith [hmul]
    exact integral_cut_le_of_tendsto h hK hw hv hB hstrong hweak hα hθm
      (fun x => cutWeight_nonneg k v x) (fun x => cutWeight_le_one k v x)
      hAm hAb hBm hBb hsupport
  -- dominated convergence in `k`
  have hdom : Tendsto (fun k : ℕ =>
      ∫ x, cutWeight k v x * kineticDensityNorm Ψ (v x) (weakGrad v x)) atTop
      (𝓝 (∫ x, kineticDensityNorm Ψ (v x) (weakGrad v x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |kineticDensityNorm Ψ (v x) (weakGrad v x)|)
      (fun k => ?_) hQv.abs (fun k => Eventually.of_forall fun x => ?_) ?_
    · refine AEStronglyMeasurable.mul ?_ hQv.aestronglyMeasurable
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (continuous_cutLow k).comp_aestronglyMeasurable hv.aestronglyMeasurable
      · exact (continuous_cutHigh k).comp_aestronglyMeasurable
          (continuous_norm.comp_aestronglyMeasurable hv.aestronglyMeasurable_weakGrad)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutWeight_nonneg k v x)]
      exact mul_le_of_le_one_left (abs_nonneg _) (cutWeight_le_one k v x)
    · filter_upwards [hv.ae_weakGrad_eq_zero hK] with x hx
      rcases (hv.nonneg x).lt_or_eq with hpos | hzero
      · have h1 := tendsto_cutLow hpos
        have h2 := tendsto_cutHigh ‖weakGrad v x‖
        have h3 : Tendsto (fun k : ℕ => cutWeight k v x) atTop (𝓝 1) := by
          simpa [cutWeight] using h1.mul h2
        simpa using h3.mul_const (kineticDensityNorm Ψ (v x) (weakGrad v x))
      · have hg : weakGrad v x = 0 := hx hzero.symm
        have hQ : kineticDensityNorm Ψ (v x) (weakGrad v x) = 0 := by
          rw [← hzero, kineticDensityNorm_zero]
        rw [hQ]
        simp
  exact le_of_tendsto hdom (Eventually.of_forall hstep)

end Lsc

end Komlos.Literature.Regularized
