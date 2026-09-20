import Komlos.Literature.Regularized.InteriorSchauderScale

/-!
# Interior Schauder estimates with a first-order right-hand side (lane `L3c`)

The difference quotients of a quasilinear equation with *natural growth*,

`div ∇Ψ(∇v) = κ v + 2 m + B(∇v)`,   `∇B(q) = 2 D²Ψ(q) q`,

satisfy linear equations `div (A_s ∇w_s) = g_s` whose right-hand side is **not bounded
uniformly in `s`**: it has the form

`|g_s| ≤ a + b ‖∇w_s‖`,

with `a`, `b` uniform, because differentiating the natural-growth term produces a bounded *drift*
coefficient contracted with `∇w_s`.  `Komlos.Literature.schauder_C2` does not apply directly: its
hypothesis is `|g| ≤ Λ`.

This file supplies the estimate that does apply.  Its two ingredients are

* `exists_schauder_scaled` (`InteriorSchauderScale.lean`), which makes the contribution of `g` to
  the gradient bound carry a factor `r` — the smallness needed to absorb `b ‖∇w‖`;
* `Komlos.Literature.norm_gradient_le_of_nested_absorb`, the Gilbarg–Trudinger nested-ball
  absorption device, already available in the project.

The results are

* `exists_schauder_drift_gradient_bound` — `sup_{B̄(x₀, R/4)} ‖∇w‖ ≤ M(d, α, μ, Λ, a, b, W, R)`;
* `exists_schauder_drift_holder` — the full interior `C^{1,α}` bound on `B(x₀, R/8)`, obtained by
  feeding the gradient bound back into `schauder_C2`, whose right-hand side is now bounded.

Both constants are quantified **before** the data, and in particular do not depend on the (only
qualitatively assumed) Hölder constant of `∇w`.  That is exactly the uniformity the
difference-quotient argument needs.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

open Komlos.Literature

variable {d : ℕ}

/-- **Interior gradient bound for `div(A ∇w) = g` with `|g| ≤ a + b ‖∇w‖`.**

For `0 < α < 1`, `μ > 0`, `Λ, a, b ≥ 0` and a radius `R ∈ (0, 1]` there is a constant
`M = M(d, α, μ, Λ, a, b, W, R)` such that every `C^{1,α}` weak solution of `div(A ∇w) = g` on
`B(x₀, R)`, with `A` uniformly `μ`-elliptic, `Λ`-bounded and `Λ`-`α`-Hölder, `|w| ≤ W` and
`|g| ≤ a + b ‖∇w‖`, satisfies `‖∇w‖ ≤ M` on `B̄(x₀, R/4)`.

The proof is the nested-ball absorption: on the ball `B(x, η δ)` around a point `x` at distance
`ρ` from the centre (`δ = R/2 - ρ`, `η` a small fixed fraction), the scaled estimate gives
`‖∇w x‖ ≤ C (W/(ηδ) + ηδ (a + b Θ/((1-η)δ)))`, where `Θ` dominates the weighted family
`(R/2 - σ) sup_{B̄(x₀,σ)} ‖∇w‖`.  Multiplying by `δ`, the `Θ`-term has coefficient
`C η b δ/(1-η) ≤ 2 C η b R`, which is `≤ 1/2` once `η` is chosen small; the absorption principle
then bounds `Θ`. -/
theorem exists_schauder_drift_gradient_bound (d : ℕ) {α μ Λ a b W R : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hμ : 0 < μ) (hΛ : 0 ≤ Λ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hW : 0 ≤ W)
    (hR : 0 < R) (hR1 : R ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ z ∈ Metric.ball x₀ R, ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A z ζ, ζ⟫) →
      (∀ z ∈ Metric.ball x₀ R, ‖A z‖ ≤ Λ) →
      (∀ z ∈ Metric.ball x₀ R, ∀ z' ∈ Metric.ball x₀ R, ‖A z - A z'‖ ≤ Λ * dist z z' ^ α) →
      ContinuousOn g (Metric.ball x₀ R) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ R) →
      (∃ Cw : ℝ, ∀ z ∈ Metric.ball x₀ R, ∀ z' ∈ Metric.ball x₀ R,
        ‖gradient w z - gradient w z'‖ ≤ Cw * dist z z' ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball x₀ R →
        ∫ z, ⟪A z (gradient w z), gradient ψ z⟫ = ∫ z, g z * ψ z) →
      (∀ z ∈ Metric.ball x₀ R, |w z| ≤ W) →
      (∀ z ∈ Metric.ball x₀ R, |g z| ≤ a + b * ‖gradient w z‖) →
      ∀ z ∈ Metric.closedBall x₀ (R / 4), ‖gradient w z‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := exists_schauder_scaled d hα hα1 hμ hΛ
  -- the absorption fraction
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (1 / 2) (1 / (2 * (2 * C * b * R + 1))) := ⟨_, rfl⟩
  have hden : (0 : ℝ) < 2 * (2 * C * b * R + 1) := by positivity
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min (by norm_num) (by positivity)
  have hη2 : η ≤ 1 / 2 := by rw [hηdef]; exact min_le_left _ _
  have hηb : C * b * R * η ≤ 1 / 2 := by
    have h1 : η ≤ 1 / (2 * (2 * C * b * R + 1)) := by rw [hηdef]; exact min_le_right _ _
    have h2 : 0 ≤ C * b * R := by positivity
    have h1' : η * (2 * (2 * C * b * R + 1)) ≤ 1 := by
      rw [le_div_iff₀ hden] at h1
      exact h1
    nlinarith [h1', h2, hη0.le]
  obtain ⟨Ac, hAcdef⟩ : ∃ A' : ℝ, A' = C * W / η + C * η * R ^ 2 * a / 4 := ⟨_, rfl⟩
  have hAc0 : 0 ≤ Ac := by
    rw [hAcdef]
    have h1 : 0 ≤ C * W / η := by positivity
    have h2 : 0 ≤ C * η * R ^ 2 * a / 4 := by positivity
    linarith
  refine ⟨8 * Ac / R, by positivity, ?_⟩
  intro x₀ A g w hell hAbd hAhol hgc hw hwhol hweak hwbd hgbd
  -- the absorption radius
  obtain ⟨Rh, hRhdef⟩ : ∃ s : ℝ, s = R / 2 := ⟨_, rfl⟩
  have hRh0 : 0 < Rh := by rw [hRhdef]; linarith
  have hRhR : Rh < R := by rw [hRhdef]; linarith
  have hsubRh : Metric.closedBall x₀ Rh ⊆ Metric.ball x₀ R := Metric.closedBall_subset_ball hRhR
  have hgradw : ContinuousOn (gradient w) (Metric.ball x₀ R) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hw.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall x₀ Rh).exists_bound_of_continuousOn
    (hgradw.mono hsubRh)
  -- the one-step estimate
  have habs : ∀ Θ : ℝ,
      (∀ σ, 0 ≤ σ → σ < Rh → ∀ y ∈ Metric.closedBall x₀ σ, (Rh - σ) * ‖gradient w y‖ ≤ Θ) →
      ∀ ρ, 0 ≤ ρ → ρ < Rh → ∀ x ∈ Metric.closedBall x₀ ρ,
        (Rh - ρ) * ‖gradient w x‖ ≤ Ac + 1 / 2 * Θ := by
    intro Θ hΘ ρ hρ0 hρRh x hx
    obtain ⟨δ, hδdef⟩ : ∃ s : ℝ, s = Rh - ρ := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδdef]; linarith
    have hδR : δ ≤ Rh := by rw [hδdef]; linarith
    obtain ⟨rr, hrrdef⟩ : ∃ s : ℝ, s = η * δ := ⟨_, rfl⟩
    have hrr0 : 0 < rr := by rw [hrrdef]; positivity
    have hrr1 : rr ≤ 1 := by
      rw [hrrdef]
      have : η * δ ≤ (1 / 2) * Rh := by
        refine mul_le_mul hη2 hδR hδ0.le (by norm_num)
      rw [hRhdef] at this
      linarith
    obtain ⟨σ, hσdef⟩ : ∃ s : ℝ, s = ρ + η * δ := ⟨_, rfl⟩
    have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
    have hσRh : σ < Rh := by
      rw [hσdef, hδdef]
      nlinarith [hη2, hδ0]
    have hRhσ : Rh - σ = (1 - η) * δ := by rw [hσdef, hδdef]; ring
    have hη1 : (0 : ℝ) < 1 - η := by linarith
    -- the small ball around `x`
    have hballsub : Metric.ball x rr ⊆ Metric.closedBall x₀ σ := by
      intro y hy
      have h1 : dist y x < rr := Metric.mem_ball.1 hy
      have h2 : dist x x₀ ≤ ρ := Metric.mem_closedBall.1 hx
      have h3 := dist_triangle y x x₀
      rw [Metric.mem_closedBall, hσdef, ← hrrdef]
      linarith
    have hballR : Metric.ball x rr ⊆ Metric.ball x₀ R := by
      refine hballsub.trans ?_
      exact (Metric.closedBall_subset_closedBall hσRh.le).trans
        (Metric.closedBall_subset_ball hRhR)
    -- the local gradient bound coming from `Θ`
    have hlocal : ∀ y ∈ Metric.ball x rr, ‖gradient w y‖ ≤ Θ / ((1 - η) * δ) := by
      intro y hy
      have h := hΘ σ hσ0 hσRh y (hballsub hy)
      rw [hRhσ] at h
      rw [le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨G, hGdef⟩ : ∃ s : ℝ, s = a + b * (Θ / ((1 - η) * δ)) := ⟨_, rfl⟩
    have hgG : ∀ y ∈ Metric.ball x rr, |g y| ≤ G := by
      intro y hy
      refine (hgbd y (hballR hy)).trans ?_
      rw [hGdef]
      have := mul_le_mul_of_nonneg_left (hlocal y hy) hb
      linarith
    have hkey := hC rr hrr0 hrr1 x A g w W G
      (fun z hz ζ => hell z (hballR hz) ζ) (fun z hz => hAbd z (hballR hz))
      (fun z hz z' hz' => hAhol z (hballR hz) z' (hballR hz'))
      (hgc.mono hballR) (hw.mono hballR)
      (by
        obtain ⟨Cw, hCw⟩ := hwhol
        exact ⟨Cw, fun z hz z' hz' => hCw z (hballR hz) z' (hballR hz')⟩)
      (fun ψ hψ hψs hψb => hweak ψ hψ hψs (hψb.trans hballR))
      (fun z hz => hwbd z (hballR hz)) hgG x (Metric.mem_ball_self (by positivity))
    -- multiply by `δ` and absorb
    have hΘ0 : 0 ≤ Θ := by
      have := hΘ ρ hρ0 hρRh x hx
      have h2 : 0 ≤ (Rh - ρ) * ‖gradient w x‖ :=
        mul_nonneg (by linarith) (norm_nonneg _)
      linarith
    have hηne : η ≠ 0 := hη0.ne'
    have hδne : δ ≠ 0 := hδ0.ne'
    have hη1ne : (1 : ℝ) - η ≠ 0 := hη1.ne'
    have hexp : C * (W / rr + rr * G) * δ
        = C * W / η + C * η * δ ^ 2 * a + C * b * δ * η / (1 - η) * Θ := by
      rw [hrrdef, hGdef]
      field_simp
      ring
    have hmul : (Rh - ρ) * ‖gradient w x‖ ≤ C * (W / rr + rr * G) * δ := by
      rw [← hδdef]
      calc δ * ‖gradient w x‖ ≤ δ * (C * (W / rr + rr * G)) :=
            mul_le_mul_of_nonneg_left hkey hδ0.le
        _ = C * (W / rr + rr * G) * δ := by ring
    rw [hexp] at hmul
    have hδR' : δ ≤ R / 2 := by rw [hRhdef] at hδR; linarith
    have hd2 : δ ^ 2 ≤ R ^ 2 / 4 := by nlinarith [hδ0.le, hδR']
    have hpos : 0 ≤ C * η * a := by positivity
    have hterm2 : C * η * δ ^ 2 * a ≤ C * η * R ^ 2 * a / 4 :=
      calc C * η * δ ^ 2 * a = C * η * a * δ ^ 2 := by ring
        _ ≤ C * η * a * (R ^ 2 / 4) := mul_le_mul_of_nonneg_left hd2 hpos
        _ = C * η * R ^ 2 * a / 4 := by ring
    have hterm3 : C * b * δ * η / (1 - η) * Θ ≤ 1 / 2 * Θ := by
      have hprod : 0 ≤ C * b * η := by positivity
      have hstep : C * b * δ * η ≤ C * b * R * η / 2 :=
        calc C * b * δ * η = C * b * η * δ := by ring
          _ ≤ C * b * η * (R / 2) := mul_le_mul_of_nonneg_left hδR' hprod
          _ = C * b * R * η / 2 := by ring
      have hcoef : C * b * δ * η / (1 - η) ≤ 1 / 2 := by
        rw [div_le_iff₀ hη1]
        linarith
      exact mul_le_mul_of_nonneg_right hcoef hΘ0
    rw [hAcdef]
    linarith
  have hfinal := norm_gradient_le_of_nested_absorb hRh0 (by norm_num : (1:ℝ) / 2 < 1) hM₀ habs
  intro z hz
  have h := hfinal (R / 4) (by positivity) (by rw [hRhdef]; linarith) z hz
  have hcoef : Rh - R / 4 = R / 4 := by rw [hRhdef]; ring
  have hdiv : Ac / (1 - (1 : ℝ) / 2) = 2 * Ac := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    ring
  rw [hcoef, hdiv] at h
  rw [le_div_iff₀ hR]
  linarith

/-- **Interior `C^{1,α}` bound for `div(A ∇w) = g` with `|g| ≤ a + b ‖∇w‖`.**

Once `exists_schauder_drift_gradient_bound` has bounded `‖∇w‖` on `B̄(x₀, R/4)`, the right-hand
side is bounded there by `a + b M`, so `Komlos.Literature.schauder_C2` applies verbatim on
`B(x₀, 2 · (R/8))` and gives the interior gradient and Hölder bounds on `B(x₀, R/8)`, with a
constant depending only on `d, α, μ, Λ, a, b, W, R`. -/
theorem exists_schauder_drift_holder (d : ℕ) {α μ Λ a b W R : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hμ : 0 < μ) (hΛ : 0 ≤ Λ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hW : 0 ≤ W)
    (hR : 0 < R) (hR1 : R ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ z ∈ Metric.ball x₀ R, ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A z ζ, ζ⟫) →
      (∀ z ∈ Metric.ball x₀ R, ‖A z‖ ≤ Λ) →
      (∀ z ∈ Metric.ball x₀ R, ∀ z' ∈ Metric.ball x₀ R, ‖A z - A z'‖ ≤ Λ * dist z z' ^ α) →
      ContinuousOn g (Metric.ball x₀ R) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ R) →
      (∃ Cw : ℝ, ∀ z ∈ Metric.ball x₀ R, ∀ z' ∈ Metric.ball x₀ R,
        ‖gradient w z - gradient w z'‖ ≤ Cw * dist z z' ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball x₀ R →
        ∫ z, ⟪A z (gradient w z), gradient ψ z⟫ = ∫ z, g z * ψ z) →
      (∀ z ∈ Metric.ball x₀ R, |w z| ≤ W) →
      (∀ z ∈ Metric.ball x₀ R, |g z| ≤ a + b * ‖gradient w z‖) →
      ∀ z ∈ Metric.ball x₀ (R / 8), ‖gradient w z‖ ≤ M ∧
        ∀ z' ∈ Metric.ball x₀ (R / 8), ‖gradient w z - gradient w z'‖ ≤ M * dist z z' ^ α := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_schauder_drift_gradient_bound d hα hα1 hμ hΛ ha hb hW hR hR1
  obtain ⟨Λ₂, hΛ₂def⟩ : ∃ s : ℝ, s = max (max Λ (a + b * M₁)) W := ⟨_, rfl⟩
  have hΛΛ₂ : Λ ≤ Λ₂ := by rw [hΛ₂def]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hgΛ₂ : a + b * M₁ ≤ Λ₂ := by
    rw [hΛ₂def]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hWΛ₂ : W ≤ Λ₂ := by rw [hΛ₂def]; exact le_max_right _ _
  obtain ⟨C, hC⟩ := schauder_C2 d (Λ := Λ₂) hα hα1 hμ (by positivity : (0:ℝ) < R / 8)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x₀ A g w hell hAbd hAhol hgc hw hwhol hweak hwbd hgbd
  have hMbd := hM₁ x₀ A g w hell hAbd hAhol hgc hw hwhol hweak hwbd hgbd
  have hball4 : Metric.ball x₀ (2 * (R / 8)) ⊆ Metric.ball x₀ R :=
    Metric.ball_subset_ball (by linarith)
  have hball4' : Metric.ball x₀ (2 * (R / 8)) ⊆ Metric.closedBall x₀ (R / 4) := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    linarith
  have hgbd' : ∀ z ∈ Metric.ball x₀ (2 * (R / 8)), |g z| ≤ Λ₂ := by
    intro z hz
    refine (hgbd z (hball4 hz)).trans (le_trans ?_ hgΛ₂)
    have := hMbd z (hball4' hz)
    nlinarith [hb, this]
  have hconc := hC x₀ A g w (fun z hz ζ => hell z (hball4 hz) ζ)
    (fun z hz => (hAbd z (hball4 hz)).trans hΛΛ₂)
    (fun z hz z' hz' => (hAhol z (hball4 hz) z' (hball4 hz')).trans
      (mul_le_mul_of_nonneg_right hΛΛ₂ (Real.rpow_nonneg dist_nonneg _)))
    (hgc.mono hball4) hgbd' (hw.mono hball4)
    (fun z hz => (hwbd z (hball4 hz)).trans hWΛ₂)
    (by
      obtain ⟨Cw, hCw⟩ := hwhol
      exact ⟨Cw, fun z hz z' hz' => hCw z (hball4 hz) z' (hball4 hz')⟩)
    (fun ψ hψ hψs hψb => hweak ψ hψ hψs (hψb.trans hball4))
  intro z hz
  obtain ⟨h1, h2⟩ := hconc z hz
  refine ⟨h1.trans (le_max_left _ _), fun z' hz' => (h2 z' hz').trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)


end Komlos.Literature.Regularized
