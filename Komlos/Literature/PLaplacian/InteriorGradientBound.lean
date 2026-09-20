import Komlos.Literature.PLaplacian.GradientBound
import Komlos.Literature.PLaplacian.SchauderBootstrap
import Komlos.Literature.PLaplacian.SchauderFreezing

/-!
# The uniform interior `L^∞` gradient bound (Gilbarg–Trudinger, Theorem 8.32)

For a `C¹` weak solution of `div(A ∇w) = g` on `B(x₀, 2R)` with `A` uniformly `μ`-elliptic,
`Λ`-bounded and `α`-Hölder, `|g| ≤ Λ`, `|w| ≤ Λ` and `∇w` `α`-Hölder, this file proves

`sup_{B̄(x₀, 3R/2)} ‖∇w‖ ≤ M(d, α, μ, Λ, R)`,

with `M` quantified **before** the data — it depends only on `d, α, μ, Λ, R`, never on
`x₀, A, g, w`. This supplies the uniform bound consumed by
`Komlos.Literature.exists_frozen_replacement_data` (`PLaplacian/SchauderHarmonic.lean`).

## Why this file exists

The bound is *not* obtainable from the two routes one first reaches for.

* `Komlos.Literature.schauder_interior_gradient_bound` (`PLaplacian/RegularitySchauder.lean`) is
  **circular** here: in this repository it is derived from `schauder_perturbed_energy_decay`,
  i.e. from `exists_frozen_comparison`, i.e. from `exists_frozen_replacement_data` itself — and
  also circular for Lean's import graph, since `RegularitySchauder` imports `SchauderHarmonic`.
* `Komlos.Literature.exists_linear_energy_bound` (`PLaplacian/GradientBound.lean`) is
  non-circular but is the *wrong estimate*: it is the single-ball `L²` Caccioppoli bound
  `∫_{B̄(x₀,3R/2)} ‖∇w‖² ≤ E`, whereas a pointwise gradient bound needs the **Morrey** bound
  `∫_{B(x,s)} ‖∇w‖² ≤ M² ω_d s^d` on *every* small ball; for merely bounded measurable `A` that
  is false (De Giorgi–Nash–Moser bounds `w`, not `∇w`).  The `L^∞` gradient bound is genuinely a
  Schauder statement.

The route taken here is the Gilbarg–Trudinger interpolation/absorption argument, which is
self-contained over a family of nested balls and therefore breaks the circle.

## Contents

* `sSup_le_div_one_sub_of_le_add_mul_sSup` — **the absorption principle**: if every element of a
  nonempty set `S ⊆ ℝ` is at most `A + θ · sSup S` with `θ < 1`, then `sSup S ≤ A / (1 - θ)`.
* `norm_gradient_le_of_nested_absorb` — **the nested-ball absorption**: the previous principle
  applied to the weighted family `(R - ρ) ‖∇w y‖`, `y ∈ B̄(x₀, ρ)`, `ρ < R`.  The finiteness of
  the supremum is free, because `∇w` is continuous on the compact `B̄(x₀, R)`.
* `mul_norm_gradient_le_of_oscillation` — **the interpolation inequality**
  `t ‖∇w x‖ ≤ 2 sup|w| + H t` where `H` bounds the oscillation of `∇w` on `B̄(x, t)`; with
  `H = [∇w]_α t^α` this is the classical `t ‖∇w x‖ ≤ 2 sup|w| + [∇w]_α t^{1+α}`.
* `mul_norm_gradient_le_of_holder` — the Hölder form of the same inequality.
* `exists_interior_gradient_holder_scaled` — the proved interior Hölder estimate for `∇w`,
  obtained from `SchauderFreezing` and `SchauderBootstrap`, with a *data-dependent* constant
  in the scale-invariant form
  `τ^α [∇w]_{α; B̄(x,τ)} ≤ C (1 + sup_{B̄(x, 3τ/2)} ‖∇w‖)`.
* `exists_uniform_interior_gradient_bound` — the theorem of the title, proved from the four
  items above.

## The absorption, in arithmetic

Write `Φ(ρ) = sup_{B̄(x₀,ρ)} ‖∇w‖` and `Θ = sup_{ρ < Rs} (Rs - ρ) Φ(ρ)` with `Rs = 7R/4`; the
number `Θ` is finite for free.  Fix `ρ < Rs`, put `τ = (Rs - ρ)/2` and `σ = Rs - τ/2`.  For
`x ∈ B̄(x₀, ρ)` one has `B̄(x, 3τ/2) ⊆ B̄(x₀, σ)`, so the scaled Hölder estimate applies with
`Mτ = 2Θ/τ ≥ Φ(σ)`, and on the ball `B̄(x, κτ)` it gives the oscillation bound
`‖∇w y - ∇w x‖ ≤ C κ^α (1 + Mτ)`.  Choosing `κ = (8C)^{-1/α}` makes `C κ^α = 1/8`, and the
interpolation inequality at radius `t = κτ` then yields

`(Rs - ρ) ‖∇w x‖ = 2τ ‖∇w x‖ ≤ 4 Λ⁺ / κ + τ/4 + Θ/2 ≤ A + Θ/2`,   `A = 4Λ⁺/κ + 7R/32`,

where `Λ⁺ = max Λ 0` (the statement quantifies `M` before the data, so `Λ ≥ 0` is not yet
available when `A` is chosen; for admissible data `Λ⁺ = Λ`).

The left-hand side is an arbitrary member of the family whose supremum is `Θ`, so `Θ ≤ A + Θ/2`
and hence `Θ ≤ 2A`.  Specialising to `ρ = 3R/2`, where `Rs - ρ = R/4`, gives `M = 8A/R`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff Convolution

namespace Komlos.Literature

variable {d : ℕ}

/-! ### The absorption principle -/

/-- **Absorption of a supremum into itself.**  If every element of a nonempty set `S ⊆ ℝ` is at
most `A + θ * sSup S` with `θ < 1`, then `sSup S ≤ A / (1 - θ)`.

No boundedness hypothesis is needed: the bound `habs` itself witnesses `BddAbove S`. -/
theorem sSup_le_div_one_sub_of_le_add_mul_sSup {S : Set ℝ} {A θ : ℝ} (hne : S.Nonempty)
    (hθ1 : θ < 1) (habs : ∀ c ∈ S, c ≤ A + θ * sSup S) : sSup S ≤ A / (1 - θ) := by
  have h1 : sSup S ≤ A + θ * sSup S := csSup_le hne habs
  have h2 : (0 : ℝ) < 1 - θ := by linarith
  rw [le_div_iff₀ h2]
  have h3 : sSup S * (1 - θ) = sSup S - θ * sSup S := by ring
  rw [h3]
  linarith

/-! ### The nested-ball absorption -/

/-- **The nested-ball absorption device of Gilbarg–Trudinger.**  Let `∇w` be bounded by `M₀` on
the compact ball `B̄(x₀, R)` — which is automatic when `w` is `C¹` near that ball — and suppose
that the *weighted* quantity `(R - ρ) ‖∇w x‖`, for `x ∈ B̄(x₀, ρ)` and `ρ < R`, obeys
`(R - ρ) ‖∇w x‖ ≤ A + θ Θ` whenever `Θ` dominates the whole weighted family and `θ < 1`.  Then
the family is bounded by `A / (1 - θ)`, i.e. `‖∇w‖ ≤ A / ((1 - θ)(R - ρ))` on `B̄(x₀, ρ)`.

This is where the near-maximiser argument lives: `Θ` is instantiated with the supremum of the
family itself, which is finite precisely because of `hM₀`. -/
theorem norm_gradient_le_of_nested_absorb {w : Euc d → ℝ} {x₀ : Euc d} {R A θ M₀ : ℝ}
    (hR : 0 < R) (hθ1 : θ < 1)
    (hM₀ : ∀ y ∈ Metric.closedBall x₀ R, ‖gradient w y‖ ≤ M₀)
    (habs : ∀ Θ : ℝ,
      (∀ σ, 0 ≤ σ → σ < R → ∀ y ∈ Metric.closedBall x₀ σ, (R - σ) * ‖gradient w y‖ ≤ Θ) →
      ∀ ρ, 0 ≤ ρ → ρ < R → ∀ x ∈ Metric.closedBall x₀ ρ,
        (R - ρ) * ‖gradient w x‖ ≤ A + θ * Θ) :
    ∀ ρ, 0 ≤ ρ → ρ < R → ∀ y ∈ Metric.closedBall x₀ ρ,
      (R - ρ) * ‖gradient w y‖ ≤ A / (1 - θ) := by
  obtain ⟨S, hSdef⟩ : ∃ S : Set ℝ, S = {c : ℝ | ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < R ∧
      ∃ y ∈ Metric.closedBall x₀ ρ, c = (R - ρ) * ‖gradient w y‖} := ⟨_, rfl⟩
  have hmem : ∀ ρ, 0 ≤ ρ → ρ < R → ∀ y ∈ Metric.closedBall x₀ ρ,
      (R - ρ) * ‖gradient w y‖ ∈ S := by
    intro ρ hρ0 hρR y hy
    rw [hSdef]
    exact ⟨ρ, hρ0, hρR, y, hy, rfl⟩
  have hne : S.Nonempty :=
    ⟨(R - 0) * ‖gradient w x₀‖, hmem 0 le_rfl hR x₀ (Metric.mem_closedBall_self le_rfl)⟩
  have hM₀0 : 0 ≤ M₀ :=
    le_trans (norm_nonneg _) (hM₀ x₀ (Metric.mem_closedBall_self hR.le))
  have hbdd : BddAbove S := by
    refine ⟨R * M₀, ?_⟩
    intro c hc
    rw [hSdef] at hc
    obtain ⟨ρ, hρ0, hρR, y, hy, rfl⟩ := hc
    have hyR : y ∈ Metric.closedBall x₀ R := Metric.closedBall_subset_closedBall hρR.le hy
    have h1 : (0 : ℝ) ≤ R - ρ := by linarith
    calc (R - ρ) * ‖gradient w y‖ ≤ (R - ρ) * M₀ :=
          mul_le_mul_of_nonneg_left (hM₀ y hyR) h1
      _ ≤ R * M₀ := mul_le_mul_of_nonneg_right (by linarith) hM₀0
  have hle : ∀ σ, 0 ≤ σ → σ < R → ∀ y ∈ Metric.closedBall x₀ σ,
      (R - σ) * ‖gradient w y‖ ≤ sSup S := fun σ hσ0 hσR y hy =>
    le_csSup hbdd (hmem σ hσ0 hσR y hy)
  have hkey : ∀ c ∈ S, c ≤ A + θ * sSup S := by
    intro c hc
    rw [hSdef] at hc
    obtain ⟨ρ, hρ0, hρR, y, hy, rfl⟩ := hc
    exact habs (sSup S) hle ρ hρ0 hρR y hy
  have hΘ := sSup_le_div_one_sub_of_le_add_mul_sSup hne hθ1 hkey
  intro ρ hρ0 hρR y hy
  exact le_trans (hle ρ hρ0 hρR y hy) hΘ

/-! ### The interpolation inequality -/

/-- **The interpolation inequality between `sup |w|` and the oscillation of `∇w`**
(Gilbarg–Trudinger, proof of Theorem 8.32).  If `|w| ≤ K` and `‖∇w - ∇w x‖ ≤ H` on the closed
ball `B̄(x, t)`, then `t ‖∇w x‖ ≤ 2 K + H t`.

The proof compares `w` with its first-order Taylor polynomial at `x` along the radius pointing in
the direction of `∇w x`: the mean value inequality applied to `z ↦ w z - ⟪∇w x, z⟫`, whose
derivative has norm `‖∇w z - ∇w x‖ ≤ H`, gives `|w p - w x - t ‖∇w x‖| ≤ H t` at the endpoint
`p = x + (t / ‖∇w x‖) ∇w x`. -/
theorem mul_norm_gradient_le_of_oscillation {V : Set (Euc d)} (hV : IsOpen V) {w : Euc d → ℝ}
    (hw : ContDiffOn ℝ 1 w V) {x : Euc d} {t K H : ℝ} (ht : 0 < t)
    (hsub : Metric.closedBall x t ⊆ V)
    (hK : ∀ y ∈ Metric.closedBall x t, |w y| ≤ K)
    (hH : ∀ y ∈ Metric.closedBall x t, ‖gradient w y - gradient w x‖ ≤ H) :
    t * ‖gradient w x‖ ≤ 2 * K + H * t := by
  have hxmem : x ∈ Metric.closedBall x t := Metric.mem_closedBall_self ht.le
  have hK0 : 0 ≤ K := le_trans (abs_nonneg (w x)) (hK x hxmem)
  have hH0 : 0 ≤ H := by
    have h := hH x hxmem
    rwa [sub_self, norm_zero] at h
  rcases eq_or_ne (gradient w x) 0 with hG0 | hGne
  · rw [hG0, norm_zero, mul_zero]
    have h1 : 0 ≤ H * t := mul_nonneg hH0 ht.le
    linarith
  have hGpos : 0 < ‖gradient w x‖ := norm_pos_iff.mpr hGne
  have hGne0 : ‖gradient w x‖ ≠ 0 := hGpos.ne'
  -- The endpoint `p` of the radius in the direction of `∇w x`.
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = t * ‖gradient w x‖⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]
    exact mul_pos ht (inv_pos.mpr hGpos)
  obtain ⟨p, hpdef⟩ : ∃ p : Euc d, p = x + c • gradient w x := ⟨_, rfl⟩
  have hpx : p - x = c • gradient w x := by rw [hpdef, add_sub_cancel_left]
  have hnormpx : ‖p - x‖ = t := by
    rw [hpx, norm_smul, Real.norm_eq_abs, abs_of_pos hc0, hcdef]
    exact inv_mul_cancel_right₀ hGne0 t
  have hpmem : p ∈ Metric.closedBall x t := by
    have h1 : dist p x = t := by
      rw [dist_eq_norm]
      exact hnormpx
    exact Metric.mem_closedBall.mpr h1.le
  have hinner : ⟪gradient w x, p - x⟫ = t * ‖gradient w x‖ := by
    rw [hpx, real_inner_smul_right, real_inner_self_eq_norm_mul_norm, hcdef, ← mul_assoc,
      inv_mul_cancel_right₀ hGne0]
  -- The affine correction `u z = w z - ⟪∇w x, z⟫` and its derivative.
  obtain ⟨L, hLdef⟩ : ∃ L : Euc d →L[ℝ] ℝ,
      L = InnerProductSpace.toDual ℝ (Euc d) (gradient w x) := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : Euc d → ℝ, u = fun z => w z - L z := ⟨_, rfl⟩
  have huapp : ∀ z : Euc d, u z = w z - L z := fun z => by simp only [hudef]
  have hdiffw : ∀ y ∈ Metric.closedBall x t, DifferentiableAt ℝ w y := fun y hy =>
    (hw.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds (hsub hy))
  have hfd : ∀ y ∈ Metric.closedBall x t,
      HasFDerivAt u (InnerProductSpace.toDual ℝ (Euc d) (gradient w y - gradient w x)) y := by
    intro y hy
    have h1 : HasFDerivAt w (fderiv ℝ w y) y := (hdiffw y hy).hasFDerivAt
    have h2 : HasFDerivAt (fun z : Euc d => L z) L y := L.hasFDerivAt
    have e1 : InnerProductSpace.toDual ℝ (Euc d) (gradient w y) = fderiv ℝ w y :=
      toDual_gradient
    have h3 : InnerProductSpace.toDual ℝ (Euc d) (gradient w y - gradient w x)
        = fderiv ℝ w y - L := by
      rw [LinearIsometryEquiv.map_sub, e1, hLdef]
    rw [hudef, h3]
    exact h1.sub h2
  have hdiffu : ∀ y ∈ Metric.closedBall x t, DifferentiableAt ℝ u y := fun y hy =>
    (hfd y hy).differentiableAt
  have hbd : ∀ y ∈ Metric.closedBall x t, ‖fderiv ℝ u y‖ ≤ H := by
    intro y hy
    rw [(hfd y hy).fderiv, LinearIsometryEquiv.norm_map]
    exact hH y hy
  -- The mean value inequality on the (convex) closed ball.
  have hmvt : ‖u p - u x‖ ≤ H * ‖p - x‖ :=
    (convex_closedBall x t).norm_image_sub_le_of_norm_fderiv_le hdiffu hbd hxmem hpmem
  have hLsub : L p - L x = t * ‖gradient w x‖ := by
    have h1 : L p - L x = L (p - x) := (map_sub L p x).symm
    rw [h1, hLdef]
    exact hinner
  have hupx : u p - u x = w p - w x - t * ‖gradient w x‖ := by
    rw [huapp p, huapp x, ← hLsub]
    ring
  rw [hupx, hnormpx, Real.norm_eq_abs] at hmvt
  obtain ⟨hA1, _hA2⟩ := abs_le.mp hmvt
  obtain ⟨_hB1, hB2⟩ := abs_le.mp (hK p hpmem)
  obtain ⟨hC1, _hC2⟩ := abs_le.mp (hK x hxmem)
  linarith

/-- **The interpolation inequality in Hölder form**: `t ‖∇w x‖ ≤ 2 sup|w| + [∇w]_α t^{1+α}`.
This is the form used in Gilbarg–Trudinger's absorption step, with `t` chosen so small that the
Hölder constant multiplied by `t^α` is at most `1/2`. -/
theorem mul_norm_gradient_le_of_holder {V : Set (Euc d)} (hV : IsOpen V) {w : Euc d → ℝ}
    (hw : ContDiffOn ℝ 1 w V) {x : Euc d} {t K Hc α : ℝ} (ht : 0 < t) (hα : 0 ≤ α)
    (hHc : 0 ≤ Hc) (hsub : Metric.closedBall x t ⊆ V)
    (hK : ∀ y ∈ Metric.closedBall x t, |w y| ≤ K)
    (hH : ∀ y ∈ Metric.closedBall x t, ‖gradient w y - gradient w x‖ ≤ Hc * dist y x ^ α) :
    t * ‖gradient w x‖ ≤ 2 * K + Hc * t ^ α * t := by
  refine mul_norm_gradient_le_of_oscillation hV hw ht hsub hK ?_
  intro y hy
  refine le_trans (hH y hy) ?_
  have h1 : dist y x ^ α ≤ t ^ α :=
    Real.rpow_le_rpow dist_nonneg (Metric.mem_closedBall.mp hy) hα
  exact mul_le_mul_of_nonneg_left h1 hHc

/-! ### The scaled interior Hölder estimate for the gradient -/

/-- **The interior Hölder estimate for `∇w`, with a data-dependent constant.**
The data-dependent frozen comparison is proved before the bootstrap, which recovers
uniform constants through the Campanato estimates and the absorption argument below.

For `div(A ∇w) = g` on `B(x₀, 2R)` with `A` uniformly `μ`-elliptic, `Λ`-bounded and `α`-Hölder,
`|g| ≤ Λ`, `|w| ≤ Λ` and `∇w` `α`-Hölder, and for any ball `B(x, 2τ) ⊆ B(x₀, 2R)` with
`0 < τ ≤ R`:

`τ^α ‖∇w y - ∇w z‖ ≤ C (1 + sup_{B̄(x, 3τ/2)} ‖∇w‖) dist y z ^ α`   for `y, z ∈ B̄(x, τ)`,

with `C` depending only on `d, α, μ, Λ, R`.  The `sup` on the right is what makes the constant
*data-dependent*, and it is exactly what makes the statement non-circular: for a fixed `w` that
supremum is finite for free, because `w` is `C¹` on the open ball `B(x₀, 2R)` and `B̄(x, 3τ/2)` is
a compact subset of it.  The uniformity in the data is then recovered by the interpolation and
absorption of `exists_uniform_interior_gradient_bound`, which is where `sup ‖∇w‖` is absorbed
into the left-hand side.

The statement is *scale-invariant*: under `w̃(z) = (w(x + τ z) - w(x)) / τ` on `B(0, 2)` one has
`∇w̃(z) = ∇w(x + τ z)` and `[∇w̃]_{α; B̄(0,1)} = τ^α [∇w]_{α; B̄(x,τ)}`, while
`Ã(z) = A(x + τ z)` is `μ`-elliptic, `Λ`-bounded and `Λ τ^α ≤ Λ R^α`-Hölder,
`g̃(z) = τ g(x + τ z)` satisfies `|g̃| ≤ R Λ`, and `|w̃| ≤ (3/2) sup_{B̄(x,3τ/2)} ‖∇w‖` on
`B̄(0, 3/2)` by the mean value inequality.  So the content is the *fixed-scale* interior estimate
on a pair of nested balls. The proof uses the radius-independent comparison constants
of `SchauderFreezing` and the quantitative iteration of `SchauderBootstrap`; it does
not invoke the downstream uniform estimate of `RegularitySchauder`. -/
theorem exists_interior_gradient_holder_scaled (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hμ : 0 < μ) (hR : 0 < R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ (x : Euc d) (τ Mτ : ℝ), 0 < τ → τ ≤ R →
        Metric.ball x (2 * τ) ⊆ Metric.ball x₀ (2 * R) →
        (∀ y ∈ Metric.closedBall x (3 * τ / 2), ‖gradient w y‖ ≤ Mτ) →
        ∀ y ∈ Metric.closedBall x τ, ∀ z ∈ Metric.closedBall x τ,
          τ ^ α * ‖gradient w y - gradient w z‖ ≤ C * (1 + Mτ) * dist y z ^ α := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, le_rfl, ?_⟩
    intro x₀ A g w _ _ _ _ _ _ _ _ _ x τ Mτ _ _ _ _ y _ z _
    have hyz : y = z := Subsingleton.elim _ _
    subst z
    simp [Real.zero_rpow hα.ne']
  obtain ⟨a, b, ha, hb, hdec⟩ :=
    exists_perturbed_sqExcess_decay_of_gradient_bound d hd (α := α) (μ := μ)
      (Λ := Λ) hα hα1 hμ
  obtain ⟨C, hC, hboot⟩ := exists_scaled_holder_of_perturbed_decay d
    (a := a) (b := b) (R := R) hα hα1 ha hb hR
  refine ⟨C, hC, ?_⟩
  intro x₀ A g w hell hAbd hAhol hgc hgbd hw _hwbd _hwlip hweak
    x τ Mτ hτ hτR hsub hMτ
  have hM0 : 0 ≤ Mτ := (norm_nonneg (gradient w x)).trans
    (hMτ x (Metric.mem_closedBall_self (by positivity)))
  have hGc : ContinuousOn (gradient w) (Metric.ball x (2 * τ)) :=
    (continuousOn_gradient Metric.isOpen_ball hw).mono hsub
  apply hboot x τ Mτ (gradient w) hτ hτR hM0 hGc hMτ
  intro v hv ρ r hρ hρr hr
  have hsmall : Metric.ball v (2 * (τ / 4)) ⊆ Metric.closedBall x (3 * τ / 2) := by
    intro t ht
    rw [Metric.mem_ball] at ht
    rw [Metric.mem_closedBall] at hv ⊢
    calc dist t x ≤ dist t v + dist v x := dist_triangle _ _ _
      _ ≤ 3 * τ / 2 := by linarith
  have hlocal : Metric.ball v (2 * (τ / 4)) ⊆ Metric.ball x₀ (2 * R) :=
    hsmall.trans ((Metric.closedBall_subset_ball (by linarith)).trans hsub)
  have hdecv := hdec (R := τ / 4) (M := Mτ) (by linarith) hM0 v A g w
    (fun t ht => hell t (hlocal ht))
    (fun t ht => hAbd t (hlocal ht))
    (fun t ht q hq => hAhol t (hlocal ht) q (hlocal hq))
    (hgc.mono hlocal) (fun t ht => hgbd t (hlocal ht)) (hw.mono hlocal)
    (fun t ht => hMτ t (hsmall ht))
    (fun ψ hψ hψs hψB => hweak ψ hψ hψs (hψB.trans hlocal))
    v (Metric.mem_ball_self (by linarith)) ρ r hρ hρr
  have hr' : r ≤ min ((τ / 4) / 4) (1 / 2) := by
    simpa only [show (τ / 4) / 4 = τ / 16 by ring] using hr
  exact hdecv hr'

/-! ### The uniform interior gradient bound -/

/-- **The uniform interior `L^∞` gradient bound** (Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Theorem 8.32).  For `μ > 0`, `Λ`, `R > 0` and
`0 < α < 1` there is a single constant `M = M(d, α, μ, Λ, R)` such that **every** `C¹` weak
solution of `div(A ∇w) = g` on `B(x₀, 2R)` with `A` uniformly `μ`-elliptic, `‖A‖ ≤ Λ` and
`α`-Hölder with constant `Λ`, `|g| ≤ Λ`, `|w| ≤ Λ` and `∇w` `α`-Hölder satisfies

`‖∇w‖ ≤ M` on `B̄(x₀, 3R/2)`.

The constant is quantified **before** the data: it does not depend on `x₀, A, g, w`, and in
particular not on the Hölder constant `Cw` of `∇w`, which is only assumed to be finite.  That is
exactly the uniformity that `exists_frozen_replacement_data` needs and that
`schauder_interior_gradient_bound` cannot supply without circularity.

The proof is the interpolation/absorption argument.  Only
`exists_interior_gradient_holder_scaled` — the interior Hölder estimate for `∇w` with a
*data-dependent* constant — is taken as input; everything else is the elementary interpolation
`mul_norm_gradient_le_of_oscillation` together with the nested-ball absorption
`norm_gradient_le_of_nested_absorb`. -/
theorem exists_uniform_interior_gradient_bound (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hμ : 0 < μ) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ y ∈ Metric.closedBall x₀ (3 * R / 2), ‖gradient w y‖ ≤ M := by
  obtain ⟨C, hC1, hSCH⟩ := exists_interior_gradient_holder_scaled d hα hα1 hμ hR
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hCne : C ≠ 0 := hC0.ne'
  have hαne : α ≠ 0 := hα.ne'
  -- The interpolation parameter `κ`, chosen so that `C κ^α = 1/8`.
  have h8C : (0 : ℝ) < 8 * C := by linarith
  obtain ⟨κ, hκdef⟩ : ∃ k : ℝ, k = (1 / (8 * C)) ^ (1 / α) := ⟨_, rfl⟩
  have hb0 : (0 : ℝ) < 1 / (8 * C) := div_pos one_pos h8C
  have hb1 : 1 / (8 * C) ≤ 1 := by
    rw [div_le_one h8C]
    linarith
  have hκpos : 0 < κ := by
    rw [hκdef]
    exact Real.rpow_pos_of_pos hb0 _
  have hκne : κ ≠ 0 := hκpos.ne'
  have hκ1 : κ ≤ 1 := by
    rw [hκdef]
    exact Real.rpow_le_one hb0.le hb1 (div_pos one_pos hα).le
  have hinv : 1 / α * α = 1 := one_div_mul_cancel hαne
  have hκα : κ ^ α = 1 / (8 * C) := by
    rw [hκdef, ← Real.rpow_mul hb0.le, hinv, Real.rpow_one]
  have hCκ : C * κ ^ α = 1 / 8 := by
    rw [hκα]
    field_simp <;> ring
  -- The constant.
  obtain ⟨Kmax, hKmaxdef⟩ : ∃ k : ℝ, k = max Λ 0 := ⟨_, rfl⟩
  have hKmax0 : 0 ≤ Kmax := by
    rw [hKmaxdef]
    exact le_max_right _ _
  obtain ⟨Ac, hAcdef⟩ : ∃ a : ℝ, a = 4 * Kmax / κ + 7 * R / 32 := ⟨_, rfl⟩
  have hAc0 : 0 ≤ Ac := by
    rw [hAcdef]
    have h1 : 0 ≤ 4 * Kmax / κ := div_nonneg (by linarith) hκpos.le
    linarith
  refine ⟨8 * Ac / R, div_nonneg (by linarith) hR.le, ?_⟩
  intro x₀ A g w hell hAbd hAhol hgc hgbd hw hwbd hwhol hweak
  -- The absorption radius `Rs = 7R/4`, strictly inside the ball carrying the equation.
  obtain ⟨Rs, hRsdef⟩ : ∃ s : ℝ, s = 7 * R / 4 := ⟨_, rfl⟩
  have hRs0 : 0 < Rs := by rw [hRsdef]; linarith
  have hRs2R : Rs < 2 * R := by rw [hRsdef]; linarith
  -- `∇w` is continuous on `B(x₀, 2R)`, hence bounded on the compact `B̄(x₀, Rs)`.
  have hgradw : ContinuousOn (gradient w) (Metric.ball x₀ (2 * R)) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hw.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
  have hsubRs : Metric.closedBall x₀ Rs ⊆ Metric.ball x₀ (2 * R) :=
    Metric.closedBall_subset_ball hRs2R
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall x₀ Rs).exists_bound_of_continuousOn
    (hgradw.mono hsubRs)
  -- The one-step estimate feeding the absorption.
  have habs : ∀ Θ : ℝ,
      (∀ σ, 0 ≤ σ → σ < Rs → ∀ y ∈ Metric.closedBall x₀ σ, (Rs - σ) * ‖gradient w y‖ ≤ Θ) →
      ∀ ρ, 0 ≤ ρ → ρ < Rs → ∀ x ∈ Metric.closedBall x₀ ρ,
        (Rs - ρ) * ‖gradient w x‖ ≤ Ac + 1 / 2 * Θ := by
    intro Θ hΘ ρ hρ0 hρRs x hx
    obtain ⟨τ, hτdef⟩ : ∃ s : ℝ, s = (Rs - ρ) / 2 := ⟨_, rfl⟩
    have hτpos : 0 < τ := by rw [hτdef]; linarith
    have hτne : τ ≠ 0 := hτpos.ne'
    have hδ : Rs - ρ = 2 * τ := by rw [hτdef]; ring
    have hτR : τ ≤ R := by rw [hτdef, hRsdef]; linarith
    have hτsmall : τ ≤ 7 * R / 8 := by rw [hτdef, hRsdef]; linarith
    obtain ⟨σ, hσdef⟩ : ∃ s : ℝ, s = Rs - τ / 2 := ⟨_, rfl⟩
    have hσ0 : 0 ≤ σ := by rw [hσdef, hτdef]; linarith
    have hσRs : σ < Rs := by rw [hσdef]; linarith
    have hRsσ : Rs - σ = τ / 2 := by rw [hσdef]; ring
    have hxρ : dist x x₀ ≤ ρ := Metric.mem_closedBall.mp hx
    -- Geometry of the three concentric balls `B̄(x, κτ) ⊆ B̄(x, τ) ⊆ B̄(x, 3τ/2) ⊆ B̄(x₀, σ)`.
    have hball2τ : Metric.ball x (2 * τ) ⊆ Metric.ball x₀ (2 * R) := by
      intro y hy
      have h1 : dist y x < 2 * τ := Metric.mem_ball.mp hy
      have h2 : dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      refine Metric.mem_ball.mpr ?_
      linarith
    have hcb3 : Metric.closedBall x (3 * τ / 2) ⊆ Metric.closedBall x₀ σ := by
      intro y hy
      have h1 : dist y x ≤ 3 * τ / 2 := Metric.mem_closedBall.mp hy
      have h2 : dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      refine Metric.mem_closedBall.mpr ?_
      rw [hσdef]
      linarith
    -- The weighted supremum controls `‖∇w‖` on `B̄(x, 3τ/2)`.
    have hΘ0 : 0 ≤ Θ := by
      have h1 := hΘ σ hσ0 hσRs x₀ (Metric.mem_closedBall_self hσ0)
      have h2 : (0 : ℝ) ≤ (Rs - σ) * ‖gradient w x₀‖ :=
        mul_nonneg (by rw [hRsσ]; linarith) (norm_nonneg _)
      linarith
    obtain ⟨Mτ, hMτdef⟩ : ∃ m : ℝ, m = 2 * Θ / τ := ⟨_, rfl⟩
    have hMτ0 : 0 ≤ Mτ := by
      rw [hMτdef]
      exact div_nonneg (by linarith) hτpos.le
    have hMτbd : ∀ y ∈ Metric.closedBall x (3 * τ / 2), ‖gradient w y‖ ≤ Mτ := by
      intro y hy
      have h1 : (Rs - σ) * ‖gradient w y‖ ≤ Θ := hΘ σ hσ0 hσRs y (hcb3 hy)
      rw [hRsσ] at h1
      rw [hMτdef, le_div_iff₀ hτpos]
      linarith
    -- The scaled Hölder estimate, and the oscillation of `∇w` on the small ball `B̄(x, κτ)`.
    have hSch := hSCH x₀ A g w hell hAbd hAhol hgc hgbd hw hwbd hwhol hweak x τ Mτ hτpos hτR
      hball2τ hMτbd
    have hκτle : κ * τ ≤ τ := by
      have h1 : κ * τ ≤ 1 * τ := mul_le_mul_of_nonneg_right hκ1 hτpos.le
      linarith
    have hκτpos : 0 < κ * τ := mul_pos hκpos hτpos
    have hosc : ∀ y ∈ Metric.closedBall x (κ * τ),
        ‖gradient w y - gradient w x‖ ≤ (1 + Mτ) / 8 := by
      intro y hy
      have hyτ : y ∈ Metric.closedBall x τ := Metric.closedBall_subset_closedBall hκτle hy
      have hxτ : x ∈ Metric.closedBall x τ := Metric.mem_closedBall_self hτpos.le
      have h1 := hSch y hyτ x hxτ
      have h2 : dist y x ^ α ≤ (κ * τ) ^ α :=
        Real.rpow_le_rpow dist_nonneg (Metric.mem_closedBall.mp hy) hα.le
      have h3 : C * (1 + Mτ) * dist y x ^ α ≤ C * (1 + Mτ) * (κ * τ) ^ α :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0.le (by linarith))
      have h4 : C * (1 + Mτ) * (κ * τ) ^ α = τ ^ α * ((1 + Mτ) / 8) := by
        rw [Real.mul_rpow hκpos.le hτpos.le]
        have h5 : C * (1 + Mτ) * (κ ^ α * τ ^ α) = C * κ ^ α * ((1 + Mτ) * τ ^ α) := by ring
        rw [h5, hCκ]
        ring
      have hτα : 0 < τ ^ α := Real.rpow_pos_of_pos hτpos α
      have h6 : τ ^ α * ‖gradient w y - gradient w x‖ ≤ τ ^ α * ((1 + Mτ) / 8) := by
        rw [← h4]
        linarith
      exact le_of_mul_le_mul_left h6 hτα
    -- The interpolation inequality at radius `κτ`.
    have hsubV : Metric.closedBall x (κ * τ) ⊆ Metric.ball x₀ (2 * R) :=
      (Metric.closedBall_subset_closedBall hκτle).trans
        ((Metric.closedBall_subset_ball (by linarith)).trans hball2τ)
    have hKbd : ∀ y ∈ Metric.closedBall x (κ * τ), |w y| ≤ Kmax := by
      intro y hy
      refine le_trans (hwbd y (hsubV hy)) ?_
      rw [hKmaxdef]
      exact le_max_left _ _
    have hinterp := mul_norm_gradient_le_of_oscillation Metric.isOpen_ball hw hκτpos hsubV
      hKbd hosc
    -- Absorption arithmetic: multiply by `2/κ` and use `τ Mτ = 2Θ`.
    have hτMτ : τ * Mτ = 2 * Θ := by
      rw [hMτdef, mul_comm τ (2 * Θ / τ), div_mul_cancel₀ _ hτne]
    have hstep : 2 / κ * (κ * τ * ‖gradient w x‖)
        ≤ 2 / κ * (2 * Kmax + (1 + Mτ) / 8 * (κ * τ)) :=
      mul_le_mul_of_nonneg_left hinterp (div_nonneg (by norm_num) hκpos.le)
    have he1 : 2 / κ * (κ * τ * ‖gradient w x‖) = 2 * τ * ‖gradient w x‖ := by
      field_simp <;> ring
    have he2 : 2 / κ * (2 * Kmax + (1 + Mτ) / 8 * (κ * τ))
        = 4 * Kmax / κ + (1 + Mτ) * τ / 4 := by
      field_simp <;> ring
    rw [he1, he2] at hstep
    have he3 : (1 + Mτ) * τ / 4 = τ / 4 + Θ / 2 := by linarith [hτMτ]
    rw [he3] at hstep
    rw [hδ, hAcdef]
    linarith
  -- The absorption, and the conclusion at `ρ = 3R/2`.
  have hmain := norm_gradient_le_of_nested_absorb (R := Rs) (A := Ac) (θ := (1 : ℝ) / 2)
    (M₀ := M₀) hRs0 (by norm_num) hM₀ habs
  intro y hy
  have h3R0 : (0 : ℝ) ≤ 3 * R / 2 := by linarith
  have h3RRs : 3 * R / 2 < Rs := by rw [hRsdef]; linarith
  have h1 := hmain (3 * R / 2) h3R0 h3RRs y hy
  have h2 : Rs - 3 * R / 2 = R / 4 := by rw [hRsdef]; ring
  rw [h2] at h1
  have h3 : Ac / (1 - (1 : ℝ) / 2) = 2 * Ac := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    ring
  rw [le_div_iff₀ hR]
  linarith [h1, h3]

end Komlos.Literature
