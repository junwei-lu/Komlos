import Komlos.Literature.Regularized.InteriorRegularity

/-!
# The scaled interior Schauder estimate (lane `L3c`)

The interior Schauder estimate `Komlos.Literature.schauder_C2` is stated at a *fixed* radius `R`
with a constant that is quantified before the data but *after* `R`; the bounds on `w` and on the
right-hand side `g` enter it through the single constant `Λ`, so the estimate as stated carries
no information about how the constant scales when the ball shrinks.

This file extracts that information.  Both scalings are elementary:

* **the multiplicative one** — the equation `div(A ∇w) = g` is linear in `(w, g)`, so `(w, g)` may
  be replaced by `(λ w, λ g)`; choosing `λ` to normalize `sup|w| + r² sup|g|` to the value `Λ`
  turns the qualitative conclusion `‖∇w‖ ≤ C` into the *linear* bound
  `‖∇w‖ ≤ C λ⁻¹`;
* **the spatial one** — `wS(y) = w(x + r y)`, `AS(y) = A(x + r y)`, `gS(y) = r² g(x + r y)` solves
  the same kind of equation on the unit ball, with the same ellipticity constant `μ`, with
  `‖AS‖ ≤ Λ`, and with the Hölder seminorm of `AS` *decreased* by the factor `r^α ≤ 1`.

Together they give `exists_schauder_scaled`:

`sup_{B(x, r/2)} ‖∇w‖ ≤ C (sup_{B(x,r)}|w| / r + r · sup_{B(x,r)}|g|)`,

with `C` depending only on `d, α, μ, Λ` — in particular **not on `r`**.  The factor `r` in front
of `sup |g|` is the smallness that the absorption argument of
`Komlos/Literature/Regularized/InteriorSchauderDrift.lean` needs in order to treat a right-hand
side of the form `|g| ≤ a + b ‖∇w‖`, which is what the difference quotients of a quasilinear
equation with natural growth produce.

The change of variables in the weak formulation is the same computation as in
`Komlos.Literature.weak_rescale` (`PLaplacian/ScaledGradient.lean`); it is redone here rather
than imported because that file lies in the degenerate `p`-Laplacian chain.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

open Komlos.Literature

variable {d : ℕ}

/-! ### The affine change of variables `y ↦ x + r y` -/

/-- The dilation Jacobian, in the form used below: `∫ f = r^d ∫ f(x + r ·)` for `r > 0`.
(Identical to `Komlos.Literature.integral_eq_pow_mul_comp_add_smul`, reproved here to avoid the
degenerate chain.) -/
theorem integral_eq_pow_mul_comp_add_smul' (f : Euc d → ℝ) (x : Euc d) {r : ℝ} (hr : 0 < r) :
    ∫ z, f z = r ^ d * ∫ y, f (x + r • y) := by
  have hrd : (0 : ℝ) < r ^ d := pow_pos hr d
  have h := integral_comp_add_smul f x r
  rw [abs_of_nonneg (inv_nonneg.2 hrd.le)] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hrd.ne', one_mul]

/-- **Chain rule for the gradient under the affine map `y ↦ x + r y`.** -/
theorem gradient_comp_add_smul' {ψ : Euc d → ℝ} {x : Euc d} {r : ℝ} {y : Euc d}
    (hψ : DifferentiableAt ℝ ψ (x + r • y)) :
    gradient (fun z : Euc d => ψ (x + r • z)) y = r • gradient ψ (x + r • y) := by
  have hT : HasFDerivAt (fun z : Euc d => x + r • z)
      (r • ContinuousLinearMap.id ℝ (Euc d)) y :=
    ((hasFDerivAt_id y).const_smul r).const_add x
  have hcomp : HasFDerivAt (fun z : Euc d => ψ (x + r • z))
      ((fderiv ℝ ψ (x + r • y)).comp (r • ContinuousLinearMap.id ℝ (Euc d))) y :=
    hψ.hasFDerivAt.comp y hT
  refine eq_of_forall_inner_eq fun v => ?_
  have h1 := fderiv_apply_eq_inner_gradient (fun z : Euc d => ψ (x + r • z)) y v
  rw [hcomp.fderiv] at h1
  have h2 : ((fderiv ℝ ψ (x + r • y)).comp (r • ContinuousLinearMap.id ℝ (Euc d))) v =
      ⟪r • gradient ψ (x + r • y), v⟫ := by
    have h3 : ((fderiv ℝ ψ (x + r • y)).comp (r • ContinuousLinearMap.id ℝ (Euc d))) v
        = fderiv ℝ ψ (x + r • y) (r • v) := by simp
    rw [h3, fderiv_apply_eq_inner_gradient, real_inner_smul_right, real_inner_smul_left]
  rw [h2] at h1
  exact h1.symm

/-- **The gradient of the unscaled test function** `Ψ(z) = ψ(r⁻¹ (z - x))`. -/
theorem gradient_comp_inv_smul_sub' {ψ : Euc d → ℝ} (hψ : Differentiable ℝ ψ) (x : Euc d) (r : ℝ)
    (z : Euc d) :
    gradient (fun w : Euc d => ψ (r⁻¹ • (w - x))) z = r⁻¹ • gradient ψ (r⁻¹ • (z - x)) := by
  have hrw : ∀ w : Euc d, r⁻¹ • (w - x) = -(r⁻¹ • x) + r⁻¹ • w := fun w => by module
  simp only [hrw]
  exact gradient_comp_add_smul' (hψ _)

/-- The dilation `y ↦ x + r y` maps `B(0, t)` into `B(x, t r)`. -/
theorem mem_ball_of_mem_ball' {x : Euc d} {r t : ℝ} (hr : 0 < r) {y : Euc d}
    (hy : y ∈ Metric.ball (0 : Euc d) t) : x + r • y ∈ Metric.ball x (t * r) := by
  rw [mem_ball_zero_iff] at hy
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hr.le]
  calc r * ‖y‖ < r * t := mul_lt_mul_of_pos_left hy hr
    _ = t * r := by ring

/-! ### The scaled estimate -/

/-- **The interior Schauder gradient bound, in scaled linear form.**

For `0 < α < 1`, `μ > 0` and `Λ ≥ 0` there is a constant `C = C(d, α, μ, Λ)` such that for every
radius `r ∈ (0, 1]`, every ball `B(x, r)`, every uniformly `μ`-elliptic, `Λ`-bounded and
`Λ`-`α`-Hölder coefficient field `A` on it, and every `C^{1,α}` weak solution `w` of
`div(A ∇w) = g` there,

`‖∇w‖ ≤ C (W / r + r G)` on `B(x, r/2)`,

where `W` bounds `|w|` and `G` bounds `|g|` on `B(x, r)`.  The constant does **not** depend on
`r`, on the ball, on the data, or on the Hölder constant of `∇w` (which is only assumed finite).

This is `Komlos.Literature.schauder_C2` at `R = 1/2` transported by the two scalings described in
the module docstring. -/
theorem exists_schauder_scaled (d : ℕ) {α μ Λ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hμ : 0 < μ)
    (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → r ≤ 1 →
      ∀ (x : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ) (W G : ℝ),
      (∀ z ∈ Metric.ball x r, ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A z ζ, ζ⟫) →
      (∀ z ∈ Metric.ball x r, ‖A z‖ ≤ Λ) →
      (∀ z ∈ Metric.ball x r, ∀ z' ∈ Metric.ball x r, ‖A z - A z'‖ ≤ Λ * dist z z' ^ α) →
      ContinuousOn g (Metric.ball x r) →
      ContDiffOn ℝ 1 w (Metric.ball x r) →
      (∃ Cw : ℝ, ∀ z ∈ Metric.ball x r, ∀ z' ∈ Metric.ball x r,
        ‖gradient w z - gradient w z'‖ ≤ Cw * dist z z' ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball x r →
        ∫ z, ⟪A z (gradient w z), gradient ψ z⟫ = ∫ z, g z * ψ z) →
      (∀ z ∈ Metric.ball x r, |w z| ≤ W) → (∀ z ∈ Metric.ball x r, |g z| ≤ G) →
      ∀ z ∈ Metric.ball x (r / 2), ‖gradient w z‖ ≤ C * (W / r + r * G) := by
  obtain ⟨C₀, hC₀⟩ := schauder_C2 d (Λ := max Λ 1) hα hα1 hμ (by norm_num : (0:ℝ) < 1 / 2)
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro r hr hr1 x A g w W G hell hAbd hAhol hgc hw hwhol hweak hW hG z hz
  set Λ' : ℝ := max Λ 1 with hΛ'def
  have hΛ'1 : (1 : ℝ) ≤ Λ' := le_max_right _ _
  have hΛ'0 : (0 : ℝ) < Λ' := lt_of_lt_of_le one_pos hΛ'1
  have hΛΛ' : Λ ≤ Λ' := le_max_left _ _
  have hrne : r ≠ 0 := hr.ne'
  have hxmem : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW x hxmem)
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hG x hxmem)
  -- the target quantity
  set N : ℝ := W + r ^ 2 * G with hNdef
  have hN0 : 0 ≤ N := by positivity
  have hNle : N ≤ r * (W / r + r * G) := by
    rw [hNdef]
    field_simp
    ring_nf
    nlinarith [hW0, hG0, sq_nonneg r]
  -- the degenerate case `N = 0`: `w` vanishes identically on the ball
  rcases eq_or_lt_of_le hN0 with hNzero | hNpos
  · have hWz : W = 0 := by
      have h1 : 0 ≤ r ^ 2 * G := by positivity
      rw [hNdef] at hNzero
      linarith
    have hw0 : ∀ y ∈ Metric.ball x r, w y = 0 := fun y hy => by
      have := hW y hy
      rw [hWz] at this
      exact abs_nonpos_iff.1 this
    have hzr : z ∈ Metric.ball x r := Metric.ball_subset_ball (by linarith) hz
    have hev : w =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzr] with y hy using hw0 y hy
    have : gradient w z = 0 := by
      unfold gradient
      rw [hev.fderiv_eq]
      simp
    rw [this, norm_zero]
    have h2 : 0 ≤ W / r + r * G := by positivity
    positivity
  -- the normalizing factor
  set lam : ℝ := Λ' / N with hlamdef
  have hlam0 : 0 < lam := div_pos hΛ'0 hNpos
  have hlamN : lam * N = Λ' := by
    rw [hlamdef]
    field_simp
  -- the rescaled data
  set T : Euc d → Euc d := fun y => x + r • y with hTdef
  set AS : Euc d → Euc d →L[ℝ] Euc d := fun y => A (T y) with hASdef
  set wS : Euc d → ℝ := fun y => lam * w (T y) with hwSdef
  set gS : Euc d → ℝ := fun y => lam * r ^ 2 * g (T y) with hgSdef
  have hmaps : ∀ y ∈ Metric.ball (0 : Euc d) 1, T y ∈ Metric.ball x r := by
    intro y hy
    have h := mem_ball_of_mem_ball' (x := x) (r := r) (t := 1) hr hy
    rw [one_mul] at h
    exact h
  have hmaps2 : ∀ y ∈ Metric.ball (0 : Euc d) (1 / 2), T y ∈ Metric.ball x (r / 2) := by
    intro y hy
    have h := mem_ball_of_mem_ball' (x := x) (r := r) (t := 1 / 2) hr hy
    rw [show (1 : ℝ) / 2 * r = r / 2 by ring] at h
    exact h
  have hballeq : Metric.ball (0 : Euc d) (2 * (1 / 2)) = Metric.ball (0 : Euc d) 1 := by
    norm_num
  have hdistT : ∀ y y' : Euc d, dist (T y) (T y') = r * dist y y' := by
    intro y y'
    rw [hTdef]
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.le]
  -- `wS` is `C¹` on the unit ball, with the expected gradient
  have hTcd : ContDiff ℝ 1 T := by
    rw [hTdef]; fun_prop
  have hwS1 : ContDiffOn ℝ 1 wS (Metric.ball (0 : Euc d) 1) := by
    rw [hwSdef]
    exact contDiffOn_const.mul (hw.comp hTcd.contDiffOn hmaps)
  have hgradwS : ∀ y ∈ Metric.ball (0 : Euc d) 1,
      gradient wS y = (lam * r) • gradient w (T y) := by
    intro y hy
    have hdiff : DifferentiableAt ℝ w (T y) :=
      (hw.differentiableOn one_ne_zero).differentiableAt
        (Metric.isOpen_ball.mem_nhds (hmaps y hy))
    have h1 : gradient wS y = lam • gradient (fun z : Euc d => w (T z)) y := by
      rw [hwSdef]
      refine gradient_eq_smul_of_hasFDerivAt ?_
      have hcomp : HasFDerivAt (fun z : Euc d => w (T z))
          (fderiv ℝ (fun z : Euc d => w (T z)) y) y := by
        have hT : HasFDerivAt T (r • ContinuousLinearMap.id ℝ (Euc d)) y := by
          rw [hTdef]
          exact ((hasFDerivAt_id y).const_smul r).const_add x
        exact (hdiff.hasFDerivAt.comp y hT).differentiableAt.hasFDerivAt
      exact hcomp.const_mul lam
    rw [h1, gradient_comp_add_smul' hdiff, smul_smul]
  -- the weak equation for the rescaled data
  have hweakS : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Euc d) 1 →
      ∫ y, ⟪AS y (gradient wS y), gradient ψ y⟫ = ∫ y, gS y * ψ y := by
    intro ψ hψ hψs hψb
    have hψd : Differentiable ℝ ψ := (hψ.of_le (by simp)).differentiable one_ne_zero
    obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Euc d → ℝ, Φ = fun z : Euc d => ψ (r⁻¹ • (z - x)) := ⟨_, rfl⟩
    have hTinv : ContDiff ℝ ∞ (fun z : Euc d => r⁻¹ • (z - x)) :=
      (contDiff_id.sub contDiff_const).const_smul r⁻¹
    have hΦc : ContDiff ℝ ∞ Φ := by rw [hΦdef]; exact hψ.comp hTinv
    have hmem : ∀ z : Euc d, r⁻¹ • (z - x) ∈ tsupport ψ → z ∈ Metric.ball x r := by
      intro z hz
      have h1 : ‖r⁻¹ • (z - x)‖ < 1 := mem_ball_zero_iff.1 (hψb hz)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hr.le)] at h1
      have h4 : r⁻¹ * ‖z - x‖ * r < 1 * r := mul_lt_mul_of_pos_right h1 hr
      have h5 : r⁻¹ * ‖z - x‖ * r = ‖z - x‖ := by
        rw [mul_comm r⁻¹ ‖z - x‖, mul_assoc, inv_mul_cancel₀ hrne, mul_one]
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have hΦb : tsupport Φ ⊆ Metric.ball x r := by
      have hcl : IsClosed ((fun z : Euc d => r⁻¹ • (z - x)) ⁻¹' tsupport ψ) :=
        (isClosed_tsupport ψ).preimage hTinv.continuous
      have hsupp : Function.support Φ ⊆ (fun z : Euc d => r⁻¹ • (z - x)) ⁻¹' tsupport ψ := by
        intro z hz
        have hz0 : Φ z ≠ 0 := hz
        simp only [hΦdef] at hz0
        exact subset_tsupport ψ hz0
      exact fun z hz => hmem z (closure_minimal hsupp hcl hz)
    have hΦs : HasCompactSupport Φ := by
      refine HasCompactSupport.intro (isCompact_closedBall x r) fun z hz => ?_
      exact image_eq_zero_of_notMem_tsupport fun h =>
        hz (Metric.ball_subset_closedBall (hΦb h))
    have hpteq : ∀ y : Euc d, r⁻¹ • (T y - x) = y := by
      intro y
      rw [hTdef]
      simp only [add_sub_cancel_left]
      rw [smul_smul, inv_mul_cancel₀ hrne, one_smul]
    have hgradΦ : ∀ y : Euc d, gradient Φ (T y) = r⁻¹ • gradient ψ y := by
      intro y
      rw [hΦdef, gradient_comp_inv_smul_sub' hψd x r (T y), hpteq]
    have hΦy : ∀ y : Euc d, Φ (T y) = ψ y := by
      intro y
      simp only [hΦdef]
      rw [hpteq]
    obtain ⟨Gf, hGfdef⟩ : ∃ Gf : Euc d → ℝ,
      Gf = fun z : Euc d => ⟪A z (gradient w z), gradient Φ z⟫ := ⟨_, rfl⟩
    obtain ⟨Hf, hHfdef⟩ : ∃ Hf : Euc d → ℝ, Hf = fun z : Euc d => g z * Φ z := ⟨_, rfl⟩
    have hkey : (∫ z, Gf z) = ∫ z, Hf z := by
      rw [hGfdef, hHfdef]
      exact hweak Φ hΦc hΦs hΦb
    have hGpt : ∀ y : Euc d,
        Gf (T y) = (lam * r ^ 2)⁻¹ * ⟪AS y (gradient wS y), gradient ψ y⟫ := by
      intro y
      simp only [hGfdef]
      rw [hgradΦ y, real_inner_smul_right]
      by_cases hy : y ∈ Metric.ball (0 : Euc d) 1
      · have hgw : gradient w (T y) = (lam * r)⁻¹ • gradient wS y := by
          rw [hgradwS y hy, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
        rw [hgw]
        show r⁻¹ * ⟪A (T y) ((lam * r)⁻¹ • gradient wS y), gradient ψ y⟫ = _
        rw [map_smul, real_inner_smul_left]
        have hAt : A (T y) = AS y := rfl
        rw [hAt]
        have : r⁻¹ * ((lam * r)⁻¹ * ⟪AS y (gradient wS y), gradient ψ y⟫)
            = (lam * r ^ 2)⁻¹ * ⟪AS y (gradient wS y), gradient ψ y⟫ := by
          rw [← mul_assoc]
          congr 1
          field_simp
          try ring
        exact this
      · have h0 : gradient ψ y = 0 :=
          gradient_eq_zero_of_notMem_tsupport fun h => hy (hψb h)
        simp [h0]
    have hHpt : ∀ y : Euc d, Hf (T y) = (lam * r ^ 2)⁻¹ * (gS y * ψ y) := by
      intro y
      simp only [hHfdef, hgSdef]
      rw [hΦy y]
      field_simp
      try ring
    have hGint := integral_eq_pow_mul_comp_add_smul' Gf x hr
    have hHint := integral_eq_pow_mul_comp_add_smul' Hf x hr
    rw [funext hGpt, integral_const_mul] at hGint
    rw [funext hHpt, integral_const_mul] at hHint
    rw [hGint, hHint] at hkey
    have hfac : (0 : ℝ) < r ^ d * (lam * r ^ 2)⁻¹ := by positivity
    have := mul_left_cancel₀ hfac.ne' (by
      calc r ^ d * (lam * r ^ 2)⁻¹ * ∫ y, ⟪AS y (gradient wS y), gradient ψ y⟫
          = r ^ d * ((lam * r ^ 2)⁻¹ * ∫ y, ⟪AS y (gradient wS y), gradient ψ y⟫) := by ring
        _ = r ^ d * ((lam * r ^ 2)⁻¹ * ∫ y, gS y * ψ y) := hkey
        _ = r ^ d * (lam * r ^ 2)⁻¹ * ∫ y, gS y * ψ y := by ring)
    exact this
  -- the hypotheses of the fixed-scale Schauder estimate on the unit ball
  have hrα : r ^ α ≤ 1 := Real.rpow_le_one hr.le hr1 hα.le
  have hell' : ∀ y ∈ Metric.ball (0 : Euc d) (2 * (1 / 2)), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪AS y ζ, ζ⟫ := by
    rw [hballeq]
    exact fun y hy ζ => hell (T y) (hmaps y hy) ζ
  have hAbd' : ∀ y ∈ Metric.ball (0 : Euc d) (2 * (1 / 2)), ‖AS y‖ ≤ Λ' := by
    rw [hballeq]
    exact fun y hy => (hAbd (T y) (hmaps y hy)).trans hΛΛ'
  have hAhol' : ∀ y ∈ Metric.ball (0 : Euc d) (2 * (1 / 2)),
      ∀ y' ∈ Metric.ball (0 : Euc d) (2 * (1 / 2)), ‖AS y - AS y'‖ ≤ Λ' * dist y y' ^ α := by
    rw [hballeq]
    intro y hy y' hy'
    have h := hAhol (T y) (hmaps y hy) (T y') (hmaps y' hy')
    rw [hdistT y y'] at h
    refine h.trans ?_
    rw [Real.mul_rpow hr.le dist_nonneg]
    calc Λ * (r ^ α * dist y y' ^ α) ≤ Λ * (1 * dist y y' ^ α) := by
          refine mul_le_mul_of_nonneg_left ?_ hΛ
          exact mul_le_mul_of_nonneg_right hrα (Real.rpow_nonneg dist_nonneg _)
      _ = Λ * dist y y' ^ α := by ring
      _ ≤ Λ' * dist y y' ^ α :=
          mul_le_mul_of_nonneg_right hΛΛ' (Real.rpow_nonneg dist_nonneg _)
  have hgc' : ContinuousOn gS (Metric.ball (0 : Euc d) (2 * (1 / 2))) := by
    rw [hballeq, hgSdef]
    exact continuousOn_const.mul ((hgc.comp hTcd.continuous.continuousOn hmaps))
  have hgbd' : ∀ y ∈ Metric.ball (0 : Euc d) (2 * (1 / 2)), |gS y| ≤ Λ' := by
    rw [hballeq]
    intro y hy
    have h := hG (T y) (hmaps y hy)
    rw [hgSdef]
    show |lam * r ^ 2 * g (T y)| ≤ Λ'
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam * r ^ 2)]
    have h2 : lam * r ^ 2 * |g (T y)| ≤ lam * r ^ 2 * G :=
      mul_le_mul_of_nonneg_left h (by positivity)
    refine h2.trans ?_
    rw [← hlamN, hNdef]
    nlinarith [mul_nonneg hlam0.le hW0]
  have hw' : ContDiffOn ℝ 1 wS (Metric.ball (0 : Euc d) (2 * (1 / 2))) := by
    rw [hballeq]; exact hwS1
  have hwbd' : ∀ y ∈ Metric.ball (0 : Euc d) (2 * (1 / 2)), |wS y| ≤ Λ' := by
    rw [hballeq]
    intro y hy
    have h := hW (T y) (hmaps y hy)
    rw [hwSdef]
    show |lam * w (T y)| ≤ Λ'
    rw [abs_mul, abs_of_nonneg hlam0.le]
    have h2 : lam * |w (T y)| ≤ lam * W := mul_le_mul_of_nonneg_left h hlam0.le
    refine h2.trans ?_
    rw [← hlamN, hNdef]
    nlinarith [mul_nonneg hlam0.le (mul_nonneg (sq_nonneg r) hG0)]
  have hwhol' : ∃ Cw : ℝ, ∀ y ∈ Metric.ball (0 : Euc d) (2 * (1 / 2)),
      ∀ y' ∈ Metric.ball (0 : Euc d) (2 * (1 / 2)),
      ‖gradient wS y - gradient wS y'‖ ≤ Cw * dist y y' ^ α := by
    obtain ⟨Cw, hCw⟩ := hwhol
    refine ⟨lam * r * (max Cw 0) * r ^ α, ?_⟩
    rw [hballeq]
    intro y hy y' hy'
    rw [hgradwS y hy, hgradwS y' hy', ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ lam * r)]
    have h := hCw (T y) (hmaps y hy) (T y') (hmaps y' hy')
    rw [hdistT y y'] at h
    have h2 : ‖gradient w (T y) - gradient w (T y')‖ ≤ max Cw 0 * (r * dist y y') ^ α :=
      h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
    calc lam * r * ‖gradient w (T y) - gradient w (T y')‖
        ≤ lam * r * (max Cw 0 * (r * dist y y') ^ α) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = lam * r * (max Cw 0) * r ^ α * dist y y' ^ α := by
          rw [Real.mul_rpow hr.le dist_nonneg]; ring
  have hweak' : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball (0 : Euc d) (2 * (1 / 2)) →
      ∫ y, ⟪AS y (gradient wS y), gradient ψ y⟫ = ∫ y, gS y * ψ y := by
    rw [hballeq]
    exact hweakS
  -- apply the fixed-scale estimate and undo the scaling
  obtain ⟨y, hy, hyz⟩ : ∃ y : Euc d, y ∈ Metric.ball (0 : Euc d) (1 / 2) ∧ T y = z := by
    refine ⟨r⁻¹ • (z - x), ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hr.le)]
      have hzx : ‖z - x‖ < r / 2 := by
        have := Metric.mem_ball.1 hz
        rwa [dist_eq_norm] at this
      calc r⁻¹ * ‖z - x‖ < r⁻¹ * (r / 2) := by
            exact mul_lt_mul_of_pos_left hzx (by positivity)
        _ = 1 / 2 := by field_simp
    · rw [hTdef]
      simp only [smul_smul, mul_inv_cancel₀ hrne, one_smul]
      abel
  have hy1 : y ∈ Metric.ball (0 : Euc d) 1 := Metric.ball_subset_ball (by norm_num) hy
  have hconc := (hC₀ (0 : Euc d) AS gS wS hell' hAbd' hAhol' hgc' hgbd' hw' hwbd' hwhol'
    hweak' y hy).1
  have hgz : gradient wS y = (lam * r) • gradient w z := by rw [hgradwS y hy1, hyz]
  rw [hgz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam * r)] at hconc
  have hC₀0 : 0 ≤ C₀ :=
    le_trans (mul_nonneg (mul_nonneg hlam0.le hr.le) (norm_nonneg _)) hconc
  have hlr : (0 : ℝ) < lam * r := by positivity
  have hstep : ‖gradient w z‖ ≤ C₀ / (lam * r) := by
    rw [le_div_iff₀ hlr]
    calc ‖gradient w z‖ * (lam * r) = lam * r * ‖gradient w z‖ := by ring
      _ ≤ C₀ := hconc
  refine hstep.trans ?_
  have hNne : N ≠ 0 := hNpos.ne'
  have hΛ'ne : Λ' ≠ 0 := hΛ'0.ne'
  have hlamr : C₀ / (lam * r) = C₀ * (N / r) / Λ' := by
    rw [hlamdef]
    field_simp
    try ring
  rw [hlamr]
  have hX0 : 0 ≤ C₀ * (N / r) := mul_nonneg hC₀0 (div_nonneg hN0 hr.le)
  refine (div_le_self hX0 hΛ'1).trans ?_
  have hNr : N / r = W / r + r * G := by
    rw [hNdef]
    field_simp
    try ring
  rw [hNr]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (add_nonneg (div_nonneg hW0 hr.le) (mul_nonneg hr.le hG0))

end Komlos.Literature.Regularized
