import Komlos.Literature.PLaplacian.FrozenComparison

/-!
# The mean value property in `ℝ^d` for a constant-coefficient elliptic equation

Mathlib's harmonic-function theory is two dimensional: `InnerProductSpace.HarmonicOnNhd` is
defined on any real inner product space, but the only mean value property available
(`InnerProductSpace.HarmonicOnNhd.circleAverage_eq`) goes through complex analysis and lives on
`ℂ`, and `MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable` — the divergence
theorem — is stated for boxes, so it cannot produce the classical `∫_{∂B} ∂_ν h = ∫_B Δh = 0`.
This file builds the `ℝ^d` theory that the interior derivative estimate of the Campanato/Schauder
method (Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Theorem 8.32) needs, **without** any divergence theorem, by the following device.

## The device

Let `A` be a constant symmetric positive definite matrix and `S = A⁻¹`.  Put
`Q(w) = ⟪S w, w⟫`, a positive definite quadratic form, and let `θ : ℝ → ℝ` be a smooth profile
which is `1` near `0` and vanishes for `t ≥ 2` (`mvpProfile`).  Then
`W = θ ∘ Q` is a smooth compactly supported function with

`∇W(w) = χ(w) • S w`,   `χ(w) = 2 θ'(Q w)`,

because `∇Q(w) = 2 S w`.  Since `S` is the inverse of `A`, `⟪A ζ, S w⟫ = ⟪ζ, w⟫`, so testing the
weak equation `∫ ⟪A ∇h, ∇ψ⟫ = 0` against the rescaled bump `ψ(y) = W((y - x)/s)` gives exactly

`∫ χ((y - x)/s) ⟪∇h y, y - x⟫ dy = 0`,

which says that `s ↦ ∫ χ(w) h(x + s w) dw` has vanishing derivative.  Letting `s → 0` yields the
**mean value property in the mollified form**

`(∫ χ) · h x = ∫ χ(w) h (x + s • w) dw`.

The profile `θ` is taken *antitone*, so `χ ≤ 0`, and `∫ χ < 0` is then elementary — no polar
coordinates and no surface measure are needed anywhere.

## Main results

* `exists_integral_mvpKernel_le_neg`: `∫ χ ≤ -κ` with `κ > 0` depending only on `d`, `μ`, `Λ`
  — the normalisation that makes the mean value property usable.
* `integral_mvpKernel_mul_comp_eq`: **the mean value property** `(∫ χ) h x = ∫ χ(w) h (x + s w) dw`
  for a `C¹` weak solution of `div (A ∇h) = 0`, `A` constant and symmetric.
* `integral_mvpKernel_mul_inner_gradient_eq`: the mean value property for the gradient, obtained by
  differentiating the previous identity in `x`.
* `abs_integral_mvpKernel_mul_norm_gradient_sub_le` and
  `exists_constCoeff_gradient_lipschitz_aux`: **the interior derivative estimate.**  Comparing the mean
  value property at two nearby points, the difference of the two kernels is `O(|x₁ - x₂|/s)` and
  supported in a set of measure `O(s^d)`; Cauchy–Schwarz then bounds `‖∇h x₁ - ∇h x₂‖` by
  `C s^{-d/2-1} ‖∇h - c‖_{L²} ‖x₁ - x₂‖`, which is the scale-invariant Lipschitz estimate needed
  by `Komlos.Literature.sqExcess_decay_of_lipschitz`.
* `integral_inner_antisymm_gradient_eq_zero`: the **antisymmetric part of a constant matrix
  drops out of the weak equation** already for `C¹` solutions — the integration by parts
  `∫ (∂_e h)(∂_f ψ) = ∫ (∂_f h)(∂_e ψ)` needs only `h ∈ C¹` and the symmetry of the second
  derivative of the smooth test function `ψ`.  This removes the need for Weyl's lemma in the
  reduction to a symmetric coefficient matrix.
-/

open MeasureTheory Set Filter Topology InnerProductSpace

open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### An antitone smooth profile -/

/-- The radial profile `θ(t) = smoothTransition (2 - t)`: smooth, `θ = 1` for `t ≤ 1`, `θ = 0`
for `t ≥ 2`, and antitone. -/
noncomputable def mvpProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem contDiff_mvpProfile : ContDiff ℝ ∞ mvpProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem contDiff_one_mvpProfile : ContDiff ℝ 1 mvpProfile :=
  contDiff_mvpProfile.of_le (by simp)

theorem differentiable_mvpProfile : Differentiable ℝ mvpProfile :=
  contDiff_one_mvpProfile.differentiable one_ne_zero

theorem mvpProfile_of_le_one {t : ℝ} (ht : t ≤ 1) : mvpProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem mvpProfile_of_two_le {t : ℝ} (ht : 2 ≤ t) : mvpProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem antitone_mvpProfile : Antitone mvpProfile := by
  intro a b hab
  exact Real.smoothTransition.monotone (by linarith)

/-- The derivative of the profile. -/
noncomputable def mvpProfile' : ℝ → ℝ := deriv mvpProfile

theorem contDiff_mvpProfile' : ContDiff ℝ ∞ mvpProfile' :=
  (contDiff_infty_iff_deriv.1 contDiff_mvpProfile).2

theorem continuous_mvpProfile' : Continuous mvpProfile' :=
  contDiff_mvpProfile'.continuous

theorem hasDerivAt_mvpProfile (t : ℝ) : HasDerivAt mvpProfile (mvpProfile' t) t :=
  (differentiable_mvpProfile t).hasDerivAt

/-- A differentiable antitone real function has nonpositive derivative. -/
theorem deriv_nonpos_of_antitone {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hmono : Antitone f)
    (t : ℝ) : deriv f t ≤ 0 := by
  have hd : HasDerivAt f (deriv f t) t := (hf t).hasDerivAt
  have hslope : Tendsto (slope f t) (𝓝[≠] t) (𝓝 (deriv f t)) :=
    hasDerivAt_iff_tendsto_slope.1 hd
  have hsub : (𝓝[>] t) ≤ (𝓝[≠] t) :=
    nhdsWithin_mono t fun y (hy : t < y) => Set.mem_compl_singleton_iff.2 (ne_of_gt hy)
  have hslope' : Tendsto (slope f t) (𝓝[>] t) (𝓝 (deriv f t)) := hslope.mono_left hsub
  refine le_of_tendsto hslope' ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : t < y)
  have h1 : f y - f t ≤ 0 := by
    have := hmono hy.le
    linarith
  have h2 : (0 : ℝ) < y - t := by linarith
  have h3 : slope f t y = (f y - f t) / (y - t) := slope_def_field f t y
  rw [h3]
  exact div_nonpos_of_nonpos_of_nonneg h1 h2.le

theorem mvpProfile'_nonpos (t : ℝ) : mvpProfile' t ≤ 0 :=
  deriv_nonpos_of_antitone differentiable_mvpProfile antitone_mvpProfile t

/-- The profile drops by `1` between `1` and `2`, so its derivative equals `-1` somewhere. -/
theorem exists_mvpProfile'_eq_neg_one : ∃ t₀ ∈ Set.Ioo (1 : ℝ) 2, mvpProfile' t₀ = -1 := by
  obtain ⟨t₀, ht₀, hd⟩ := exists_deriv_eq_slope mvpProfile (by norm_num : (1 : ℝ) < 2)
    (contDiff_mvpProfile.continuous.continuousOn) (differentiable_mvpProfile.differentiableOn)
  refine ⟨t₀, ht₀, ?_⟩
  rw [mvpProfile', hd, mvpProfile_of_two_le le_rfl, mvpProfile_of_le_one le_rfl]
  norm_num

theorem mvpProfile'_of_two_lt {t : ℝ} (ht : 2 < t) : mvpProfile' t = 0 := by
  have he : mvpProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_Ioi (a := (2 : ℝ))).mem_nhds (Set.mem_Ioi.2 ht)] with y hy
    exact mvpProfile_of_two_le (le_of_lt hy)
  rw [mvpProfile', he.deriv_eq, deriv_const]

/-! ### The quadratic form of the inverse coefficient matrix -/

/-- `Q_S(w) = ⟪S w, w⟫`.  For `S = A⁻¹` with `A` symmetric positive definite this is the
positive definite quadratic form whose level sets are the ellipsoids adapted to `A`. -/
noncomputable def ellQuad (S : Euc d →L[ℝ] Euc d) (w : Euc d) : ℝ := ⟪S w, w⟫

theorem ellQuad_apply (S : Euc d →L[ℝ] Euc d) (w : Euc d) : ellQuad S w = ⟪S w, w⟫ := rfl

theorem contDiff_ellQuad (S : Euc d →L[ℝ] Euc d) : ContDiff ℝ ∞ (ellQuad S) :=
  ContDiff.inner ℝ (S.contDiff) contDiff_id

theorem continuous_ellQuad (S : Euc d →L[ℝ] Euc d) : Continuous (ellQuad S) :=
  (contDiff_ellQuad S).continuous

/-- `Q_S (c • w) = c² Q_S w`. -/
theorem ellQuad_smul (S : Euc d →L[ℝ] Euc d) (c : ℝ) (w : Euc d) :
    ellQuad S (c • w) = c ^ 2 * ellQuad S w := by
  show ⟪S (c • w), c • w⟫ = c ^ 2 * ⟪S w, w⟫
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The polarisation identity for a symmetric `S`. -/
theorem ellQuad_add {S : Euc d →L[ℝ] Euc d} (hS : ∀ u v : Euc d, ⟪S u, v⟫ = ⟪u, S v⟫)
    (w v : Euc d) : ellQuad S (w + v) = ellQuad S w + 2 * ⟪S w, v⟫ + ellQuad S v := by
  have hsym : ⟪S v, w⟫ = ⟪S w, v⟫ := (hS v w).trans (real_inner_comm (S w) v)
  show ⟪S (w + v), w + v⟫ = ⟪S w, w⟫ + 2 * ⟪S w, v⟫ + ⟪S v, v⟫
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym]
  ring

/-- `|Q_S w| ≤ ‖S‖ ‖w‖²`. -/
theorem abs_ellQuad_le (S : Euc d →L[ℝ] Euc d) (w : Euc d) :
    |ellQuad S w| ≤ ‖S‖ * ‖w‖ * ‖w‖ :=
  (abs_real_inner_le_norm (S w) w).trans
    (mul_le_mul_of_nonneg_right (S.le_opNorm w) (norm_nonneg w))

/-- The differential of `Q_S` at `w` is `v ↦ 2 ⟪S w, v⟫`. -/
theorem hasFDerivAt_ellQuad {S : Euc d →L[ℝ] Euc d} (hS : ∀ u v : Euc d, ⟪S u, v⟫ = ⟪u, S v⟫)
    (w : Euc d) : HasFDerivAt (ellQuad S) ((2 : ℝ) • innerSL ℝ (S w)) w := by
  have happ : ∀ z : Euc d, ((2 : ℝ) • innerSL ℝ (S w)) z = 2 * ⟪S w, z⟫ := by
    intro z
    rw [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hkey : ∀ z : Euc d,
      ellQuad S z - ellQuad S w - ((2 : ℝ) • innerSL ℝ (S w)) (z - w) = ellQuad S (z - w) := by
    intro z
    have h1 : ellQuad S (w + (z - w)) = ellQuad S w + 2 * ⟪S w, z - w⟫ + ellQuad S (z - w) :=
      ellQuad_add hS w (z - w)
    have h2 : w + (z - w) = z := by abel
    rw [h2] at h1
    rw [happ (z - w), h1]
    ring
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hS1 : (0 : ℝ) < ‖S‖ + 1 := by positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = c / (‖S‖ + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact div_pos hc hS1
  have hδc : (‖S‖ + 1) * δ = c := by
    rw [hδdef, mul_div_cancel₀ c hS1.ne']
  filter_upwards [Metric.ball_mem_nhds w hδ0] with z hz
  have hzw : ‖z - w‖ < δ := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.1 hz
  rw [hkey z]
  have h3 : ‖ellQuad S (z - w)‖ ≤ ‖S‖ * ‖z - w‖ * ‖z - w‖ := by
    rw [Real.norm_eq_abs]
    exact abs_ellQuad_le S (z - w)
  have h4 : ‖S‖ * ‖z - w‖ ≤ c := by
    have ha : ‖S‖ * ‖z - w‖ ≤ ‖S‖ * δ := mul_le_mul_of_nonneg_left hzw.le (norm_nonneg S)
    have hb : ‖S‖ * δ ≤ (‖S‖ + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  calc ‖ellQuad S (z - w)‖ ≤ ‖S‖ * ‖z - w‖ * ‖z - w‖ := h3
    _ ≤ c * ‖z - w‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)

theorem gradient_ellQuad {S : Euc d →L[ℝ] Euc d} (hS : ∀ u v : Euc d, ⟪S u, v⟫ = ⟪u, S v⟫)
    (w : Euc d) : gradient (ellQuad S) w = (2 : ℝ) • S w := by
  refine ext_inner_right ℝ fun v => ?_
  rw [← fderiv_apply_eq_inner_gradient, (hasFDerivAt_ellQuad hS w).fderiv,
    _root_.smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_smul_left]

/-! ### The elliptic bump and its kernel -/

/-- `W_S = θ ∘ Q_S`: a smooth compactly supported bump whose level sets are the ellipsoids of
`S`. -/
noncomputable def mvpBump (S : Euc d →L[ℝ] Euc d) (w : Euc d) : ℝ := mvpProfile (ellQuad S w)

/-- `χ_S(w) = 2 θ'(Q_S w)`, the kernel appearing in `∇W_S w = χ_S w • S w`. -/
noncomputable def mvpKernel (S : Euc d →L[ℝ] Euc d) (w : Euc d) : ℝ :=
  2 * mvpProfile' (ellQuad S w)

theorem contDiff_mvpBump (S : Euc d →L[ℝ] Euc d) : ContDiff ℝ ∞ (mvpBump S) := by
  have h : ContDiff ℝ ∞ (mvpProfile ∘ ellQuad S) :=
    contDiff_mvpProfile.comp (contDiff_ellQuad S)
  exact h

theorem contDiff_mvpKernel (S : Euc d →L[ℝ] Euc d) : ContDiff ℝ ∞ (mvpKernel S) := by
  have h : ContDiff ℝ ∞ (mvpProfile' ∘ ellQuad S) :=
    contDiff_mvpProfile'.comp (contDiff_ellQuad S)
  exact contDiff_const.mul h

theorem continuous_mvpBump (S : Euc d →L[ℝ] Euc d) : Continuous (mvpBump S) :=
  (contDiff_mvpBump S).continuous

theorem continuous_mvpKernel (S : Euc d →L[ℝ] Euc d) : Continuous (mvpKernel S) :=
  (contDiff_mvpKernel S).continuous

theorem mvpKernel_nonpos (S : Euc d →L[ℝ] Euc d) (w : Euc d) : mvpKernel S w ≤ 0 := by
  have h := mvpProfile'_nonpos (ellQuad S w)
  have : mvpKernel S w = 2 * mvpProfile' (ellQuad S w) := rfl
  rw [this]
  linarith

/-- `∇W_S w = χ_S w • S w`: the whole point of the construction. -/
theorem gradient_mvpBump {S : Euc d →L[ℝ] Euc d} (hS : ∀ u v : Euc d, ⟪S u, v⟫ = ⟪u, S v⟫)
    (w : Euc d) : gradient (mvpBump S) w = mvpKernel S w • S w := by
  have hcomp : HasFDerivAt (mvpProfile ∘ ellQuad S)
      (mvpProfile' (ellQuad S w) • ((2 : ℝ) • innerSL ℝ (S w))) w :=
    HasDerivAt.comp_hasFDerivAt w (hasDerivAt_mvpProfile (ellQuad S w))
      (hasFDerivAt_ellQuad hS w)
  have hbump : HasFDerivAt (mvpBump S)
      (mvpProfile' (ellQuad S w) • ((2 : ℝ) • innerSL ℝ (S w))) w := hcomp
  refine ext_inner_right ℝ fun v => ?_
  rw [← fderiv_apply_eq_inner_gradient, hbump.fderiv]
  rw [_root_.smul_apply, _root_.smul_apply, innerSL_apply_apply,
    smul_eq_mul, smul_eq_mul, real_inner_smul_left]
  have : mvpKernel S w = 2 * mvpProfile' (ellQuad S w) := rfl
  rw [this]
  ring

/-! ### The support of the bump -/

/-- The radius of the ellipsoid `{Q_S ≤ 2}` when `α ‖·‖² ≤ Q_S`. -/
noncomputable def mvpRadius (α : ℝ) : ℝ := Real.sqrt (2 / α)

theorem mvpRadius_pos {α : ℝ} (hα : 0 < α) : 0 < mvpRadius α :=
  Real.sqrt_pos.2 (div_pos two_pos hα)

theorem norm_le_mvpRadius {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) {w : Euc d} (hw : ellQuad S w ≤ 2) :
    ‖w‖ ≤ mvpRadius α := by
  have h1 : α * ‖w‖ ^ 2 ≤ 2 := le_trans (hQ w) hw
  have h2 : ‖w‖ ^ 2 ≤ 2 / α := by
    rw [le_div_iff₀ hα, mul_comm]
    exact h1
  have h3 : ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
  rw [h3, mvpRadius]
  exact Real.sqrt_le_sqrt h2

theorem support_mvpBump_subset {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) :
    Function.support (mvpBump S) ⊆ Metric.closedBall (0 : Euc d) (mvpRadius α) := by
  intro w hw
  have h1 : mvpProfile (ellQuad S w) ≠ 0 := hw
  have h2 : ellQuad S w ≤ 2 := by
    by_contra h
    exact h1 (mvpProfile_of_two_le (le_of_lt (not_le.1 h)))
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_mvpRadius hα hQ h2

theorem support_mvpKernel_subset {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) :
    Function.support (mvpKernel S) ⊆ Metric.closedBall (0 : Euc d) (mvpRadius α) := by
  intro w hw
  have h1 : 2 * mvpProfile' (ellQuad S w) ≠ 0 := hw
  have h2 : ellQuad S w ≤ 2 := by
    by_contra h
    rw [mvpProfile'_of_two_lt (not_le.1 h)] at h1
    exact h1 (by ring)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_mvpRadius hα hQ h2

theorem hasCompactSupport_mvpBump {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) : HasCompactSupport (mvpBump S) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (mvpRadius α)) fun x hx => by
    by_contra hne
    exact hx (support_mvpBump_subset hα hQ hne)

theorem hasCompactSupport_mvpKernel {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) : HasCompactSupport (mvpKernel S) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (mvpRadius α)) fun x hx => by
    by_contra hne
    exact hx (support_mvpKernel_subset hα hQ hne)

theorem tsupport_mvpBump_subset {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) :
    tsupport (mvpBump S) ⊆ Metric.closedBall (0 : Euc d) (mvpRadius α) :=
  closure_minimal (support_mvpBump_subset hα hQ) Metric.isClosed_closedBall

theorem integrable_mvpKernel {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) : Integrable (mvpKernel S) :=
  (continuous_mvpKernel S).integrable_of_hasCompactSupport (hasCompactSupport_mvpKernel hα hQ)

/-! ### The rescaled test function -/

/-- The rescaled bump `ψ_{x,s}(y) = W_S ((y - x)/s)`, the test function of the mean value
property. -/
noncomputable def mvpTest (S : Euc d →L[ℝ] Euc d) (x : Euc d) (s : ℝ) (y : Euc d) : ℝ :=
  mvpBump S (s⁻¹ • (y - x))

theorem contDiff_mvpTest (S : Euc d →L[ℝ] Euc d) (x : Euc d) (s : ℝ) :
    ContDiff ℝ ∞ (mvpTest S x s) := by
  have haff : ContDiff ℝ ∞ fun y : Euc d => s⁻¹ • (y - x) :=
    (contDiff_id.sub contDiff_const).const_smul s⁻¹
  have h : ContDiff ℝ ∞ (mvpBump S ∘ fun y : Euc d => s⁻¹ • (y - x)) :=
    (contDiff_mvpBump S).comp haff
  exact h

theorem gradient_mvpTest (S : Euc d →L[ℝ] Euc d) (x : Euc d) (s : ℝ) (y : Euc d) :
    gradient (mvpTest S x s) y = s⁻¹ • gradient (mvpBump S) (s⁻¹ • (y - x)) := by
  have hW1 : ContDiff ℝ 1 (mvpBump S) := (contDiff_mvpBump S).of_le (by simp)
  have hWdiff : Differentiable ℝ (mvpBump S) := hW1.differentiable one_ne_zero
  have hT : HasFDerivAt (fun z : Euc d => s⁻¹ • (z - x))
      (s⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) y :=
    ((hasFDerivAt_id y).sub_const x).const_smul s⁻¹
  have hW : HasFDerivAt (mvpBump S) (fderiv ℝ (mvpBump S) (s⁻¹ • (y - x))) (s⁻¹ • (y - x)) :=
    (hWdiff (s⁻¹ • (y - x))).hasFDerivAt
  have hcomp : HasFDerivAt (mvpTest S x s)
      ((fderiv ℝ (mvpBump S) (s⁻¹ • (y - x))).comp
        (s⁻¹ • ContinuousLinearMap.id ℝ (Euc d))) y := hW.comp y hT
  refine ext_inner_right ℝ fun v => ?_
  rw [← fderiv_apply_eq_inner_gradient, hcomp.fderiv, real_inner_smul_left,
    ← fderiv_apply_eq_inner_gradient]
  show fderiv ℝ (mvpBump S) (s⁻¹ • (y - x)) ((s⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) v) =
    s⁻¹ * fderiv ℝ (mvpBump S) (s⁻¹ • (y - x)) v
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

theorem support_mvpTest_subset {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) (x : Euc d) {s : ℝ} (hs : 0 < s) :
    Function.support (mvpTest S x s) ⊆ Metric.closedBall x (s * mvpRadius α) := by
  intro y hy
  have h1 : s⁻¹ • (y - x) ∈ Function.support (mvpBump S) := hy
  have h2 : ‖s⁻¹ • (y - x)‖ ≤ mvpRadius α := by
    have := support_mvpBump_subset hα hQ h1
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)] at h2
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h3 : ‖y - x‖ = s * (s⁻¹ * ‖y - x‖) := by
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [h3]
  exact mul_le_mul_of_nonneg_left h2 hs.le

theorem hasCompactSupport_mvpTest {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) (x : Euc d) {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (mvpTest S x s) :=
  HasCompactSupport.intro (isCompact_closedBall x (s * mvpRadius α)) fun y hy => by
    by_contra hne
    exact hy (support_mvpTest_subset hα hQ x hs hne)

theorem tsupport_mvpTest_subset {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) (x : Euc d) {s : ℝ} (hs : 0 < s) :
    tsupport (mvpTest S x s) ⊆ Metric.closedBall x (s * mvpRadius α) :=
  closure_minimal (support_mvpTest_subset hα hQ x hs) Metric.isClosed_closedBall

/-! ### Change of variables -/

/-- `∫ f (x + s • w) dw = |s^d|⁻¹ ∫ f` on `ℝ^d`. -/
theorem integral_comp_add_smul (f : Euc d → ℝ) (x : Euc d) (s : ℝ) :
    ∫ w, f (x + s • w) = |(s ^ d)⁻¹| * ∫ y, f y := by
  have h2 := Measure.integral_comp_smul (volume : Measure (Euc d))
    (fun z : Euc d => f (x + z)) s
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at h2
  rw [integral_add_left_eq_self f x] at h2
  exact h2

/-- The inverse form of the change of variables. -/
theorem integral_comp_inv_smul_sub (g : Euc d → ℝ) (x : Euc d) {s : ℝ} (hs : 0 < s) :
    ∫ w, g w = |(s ^ d)⁻¹| * ∫ y, g (s⁻¹ • (y - x)) := by
  have h := integral_comp_add_smul (fun y : Euc d => g (s⁻¹ • (y - x))) x s
  have he : ∀ w : Euc d, s⁻¹ • ((x + s • w) - x) = w := by
    intro w
    rw [add_sub_cancel_left, inv_smul_smul₀ hs.ne']
  simp only [he] at h
  exact h

/-! ### The mean value property -/

/-- **The key vanishing identity.**  Testing the weak equation against the rescaled elliptic
bump `ψ(y) = W_S((y - x)/s)` and using `S A = 1` gives
`∫ χ_S(w) ⟪∇u (x + s w), w⟫ dw = 0`, which is exactly the statement that the spherical-type mean
`s ↦ ∫ χ_S(w) u(x + s w) dw` has vanishing derivative. -/
theorem integral_mvpKernel_mul_inner_eq_zero
    {A S : Euc d →L[ℝ] Euc d} (hSsymm : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫)
    (hSA : ∀ v : Euc d, S (A v) = v)
    {α : ℝ} (hα : 0 < α) (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w)
    {V : Set (Euc d)} {u : Euc d → ℝ}
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∫ y, ⟪A (gradient u y), gradient ψ y⟫ = 0)
    {x : Euc d} {s : ℝ} (hs : 0 < s)
    (hball : Metric.closedBall x (s * mvpRadius α) ⊆ V) :
    ∫ w, mvpKernel S w * ⟪gradient u (x + s • w), w⟫ = 0 := by
  have hzero : ∫ y, ⟪A (gradient u y), gradient (mvpTest S x s) y⟫ = 0 :=
    hsol (mvpTest S x s) (contDiff_mvpTest S x s) (hasCompactSupport_mvpTest hα hQ x hs)
      ((tsupport_mvpTest_subset hα hQ x hs).trans hball)
  have hpt : ∀ y : Euc d,
      ⟪A (gradient u y), gradient (mvpTest S x s) y⟫ =
        s⁻¹ * (mvpKernel S (s⁻¹ • (y - x)) *
          ⟪gradient u (x + s • (s⁻¹ • (y - x))), s⁻¹ • (y - x)⟫) := by
    intro y
    have hy : x + s • (s⁻¹ • (y - x)) = y := by
      rw [smul_inv_smul₀ hs.ne']
      abel
    rw [gradient_mvpTest S x s y,
      real_inner_smul_right (A (gradient u y)) (gradient (mvpBump S) (s⁻¹ • (y - x))) s⁻¹,
      gradient_mvpBump hSsymm (s⁻¹ • (y - x)),
      real_inner_smul_right (A (gradient u y)) (S (s⁻¹ • (y - x)))
        (mvpKernel S (s⁻¹ • (y - x))),
      hy, ← hSsymm (A (gradient u y)) (s⁻¹ • (y - x)), hSA]
  have hstep : ∫ y, mvpKernel S (s⁻¹ • (y - x)) *
      ⟪gradient u (x + s • (s⁻¹ • (y - x))), s⁻¹ • (y - x)⟫ = 0 := by
    have h1 : ∫ y, ⟪A (gradient u y), gradient (mvpTest S x s) y⟫ =
        ∫ y, s⁻¹ * (mvpKernel S (s⁻¹ • (y - x)) *
          ⟪gradient u (x + s • (s⁻¹ • (y - x))), s⁻¹ • (y - x)⟫) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [h1, integral_const_mul] at hzero
    exact (mul_eq_zero.1 hzero).resolve_left (inv_ne_zero hs.ne')
  have hfin : ∫ w, mvpKernel S w * ⟪gradient u (x + s • w), w⟫ =
      |((s : ℝ) ^ d)⁻¹| * ∫ y, mvpKernel S (s⁻¹ • (y - x)) *
        ⟪gradient u (x + s • (s⁻¹ • (y - x))), s⁻¹ • (y - x)⟫ :=
    integral_comp_inv_smul_sub
      (fun w : Euc d => mvpKernel S w * ⟪gradient u (x + s • w), w⟫) x hs
  rw [hstep, mul_zero] at hfin
  exact hfin

/-- The integrand of the mollified mean is integrable: it is continuous and supported in the
ellipsoid `{Q_S ≤ 2}`. -/
theorem integrable_mvpKernel_mul {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) {g : Euc d → ℝ} (hg : Continuous g) :
    Integrable fun w : Euc d => mvpKernel S w * g w := by
  refine Continuous.integrable_of_hasCompactSupport ((continuous_mvpKernel S).mul hg) ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (mvpRadius α)) ?_
  intro w hw
  have h0 : mvpKernel S w = 0 := by
    by_contra hne
    exact hw (support_mvpKernel_subset hα hQ hne)
  rw [h0, zero_mul]

/-- **Differentiation under the integral sign for the mollified mean.**  The integrand is
`χ_S(w) u (q w + τ c w)`; only the parameter `τ` moves, the domain of integration is the fixed
compact support of `χ_S`, and `‖∇u‖` is globally bounded because `u` is `C¹` with compact
support. -/
theorem hasDerivAt_integral_mvpKernel {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u)
    (hus : HasCompactSupport u) {q c : Euc d → Euc d} (hq : Continuous q) (hc : Continuous c)
    {N : ℝ} (hN0 : 0 ≤ N) (hcN : ∀ w : Euc d, mvpKernel S w ≠ 0 → ‖c w‖ ≤ N) (σ : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ w, mvpKernel S w * u (q w + τ • c w))
      (∫ w, mvpKernel S w * ⟪gradient u (q w + σ • c w), c w⟫) σ := by
  have hgc : IsCompact (tsupport (gradient u)) := hasCompactSupport_gradient hus
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Euc d, ‖gradient u y‖ ≤ M :=
    exists_bound_of_zero_outside' hgc (continuous_gradient hu).continuousOn
      fun y hy => image_eq_zero_of_notMem_tsupport hy
  have haff : ∀ τ : ℝ, Continuous fun w : Euc d => q w + τ • c w := fun τ =>
    hq.add (hc.const_smul τ)
  have hcont : ∀ τ : ℝ, Continuous fun w : Euc d => mvpKernel S w * u (q w + τ • c w) :=
    fun τ => (continuous_mvpKernel S).mul (hu.continuous.comp (haff τ))
  have hcont' : ∀ τ : ℝ,
      Continuous fun w : Euc d => mvpKernel S w * ⟪gradient u (q w + τ • c w), c w⟫ := fun τ =>
    (continuous_mvpKernel S).mul (((continuous_gradient hu).comp (haff τ)).inner hc)
  have hbdint : Integrable fun w : Euc d => |mvpKernel S w| * (M * N) :=
    (integrable_mvpKernel hα hQ).abs.mul_const _
  have hbd : ∀ᵐ w : Euc d, ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) →
      ‖mvpKernel S w * ⟪gradient u (q w + τ • c w), c w⟫‖ ≤ |mvpKernel S w| * (M * N) := by
    refine Filter.Eventually.of_forall fun w => fun τ _ => ?_
    rcases eq_or_ne (mvpKernel S w) 0 with h0 | h0
    · rw [h0]
      simp
    · have h1 : |⟪gradient u (q w + τ • c w), c w⟫| ≤ M * ‖c w‖ :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hMb _) (norm_nonneg _))
      have h2 : M * ‖c w‖ ≤ M * N := mul_le_mul_of_nonneg_left (hcN w h0) hM0
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
  have hdiff : ∀ᵐ w : Euc d, ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) →
      HasDerivAt (fun τ : ℝ => mvpKernel S w * u (q w + τ • c w))
        (mvpKernel S w * ⟪gradient u (q w + τ • c w), c w⟫) τ := by
    refine Filter.Eventually.of_forall fun w => fun τ _ => ?_
    have h2 : HasDerivAt (fun τ : ℝ => τ • c w) (c w) τ := by
      simpa using (hasDerivAt_id τ).smul_const (c w)
    have h1 : HasDerivAt (fun τ : ℝ => q w + τ • c w) (c w) τ := by
      simpa using h2.const_add (q w)
    have h4 : HasFDerivAt u (fderiv ℝ u (q w + τ • c w)) (q w + τ • c w) :=
      ((hu.differentiable one_ne_zero) (q w + τ • c w)).hasFDerivAt
    have h3 : HasDerivAt (fun τ : ℝ => u (q w + τ • c w))
        (fderiv ℝ u (q w + τ • c w) (c w)) τ := h4.comp_hasDerivAt τ h1
    have h5 := h3.const_mul (mvpKernel S w)
    rwa [fderiv_apply_eq_inner_gradient u (q w + τ • c w) (c w)] at h5
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Euc d)))
    (F := fun τ : ℝ => fun w : Euc d => mvpKernel S w * u (q w + τ • c w))
    (F' := fun τ : ℝ => fun w : Euc d => mvpKernel S w * ⟪gradient u (q w + τ • c w), c w⟫)
    (x₀ := σ) (s := (Set.univ : Set ℝ))
    (bound := fun w : Euc d => |mvpKernel S w| * (M * N))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
    (integrable_mvpKernel_mul hα hQ (hu.continuous.comp (haff σ)))
    (hcont' σ).aestronglyMeasurable hbd hbdint hdiff
  exact key.2

/-- The special case `q w = x`, `c w = w` (differentiation in the scale). -/
theorem hasDerivAt_integral_mvpKernel_scale {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u)
    (hus : HasCompactSupport u) (x : Euc d) (σ : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ w, mvpKernel S w * u (x + τ • w))
      (∫ w, mvpKernel S w * ⟪gradient u (x + σ • w), w⟫) σ :=
  hasDerivAt_integral_mvpKernel (q := fun _ : Euc d => x) (c := fun w : Euc d => w) hα hQ hu hus
    continuous_const continuous_id' (mvpRadius_pos hα).le
    (fun w hw => by
      have hmem := support_mvpKernel_subset hα hQ (show w ∈ Function.support (mvpKernel S) from hw)
      rwa [Metric.mem_closedBall, dist_zero_right] at hmem) σ

/-- **The mean value property in `ℝ^d` for a constant symmetric elliptic operator.**  If `u` is a
`C¹` weak solution of `div (A ∇u) = 0` on `V` and the ellipsoid `x + s {Q_S ≤ 2}` is contained in
`V`, then the `χ_S`-mean of `u` over that ellipsoid equals `(∫ χ_S) u x`.

The proof is exactly the classical one for the sphere mean, but with the divergence theorem
replaced by the algebraic identity `∇W_S = χ_S • S (·)`: the scale derivative of the mean is a
multiple of `∫ ⟪A ∇u, ∇ψ⟫` for the rescaled bump `ψ`, hence zero, and the mean tends to
`(∫ χ_S) u x` as the scale tends to `0`. -/
theorem integral_mvpKernel_mul_comp_eq
    {A S : Euc d →L[ℝ] Euc d} (hSsymm : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫)
    (hSA : ∀ v : Euc d, S (A v) = v)
    {α : ℝ} (hα : 0 < α) (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w)
    {V : Set (Euc d)} {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) (hus : HasCompactSupport u)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∫ y, ⟪A (gradient u y), gradient ψ y⟫ = 0)
    {x : Euc d} {s : ℝ} (hs : 0 < s)
    (hball : Metric.closedBall x (s * mvpRadius α) ⊆ V) :
    ∫ w, mvpKernel S w * u (x + s • w) = (∫ w, mvpKernel S w) * u x := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, F = fun τ => ∫ w, mvpKernel S w * u (x + τ • w) := ⟨_, rfl⟩
  have hFderiv : ∀ τ : ℝ,
      HasDerivAt F (∫ w, mvpKernel S w * ⟪gradient u (x + τ • w), w⟫) τ := by
    intro τ
    rw [hFdef]
    exact hasDerivAt_integral_mvpKernel_scale hα hQ hu hus x τ
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.2 fun τ => (hFderiv τ).continuousAt
  have hzeroderiv : ∀ τ : ℝ, 0 < τ → τ ≤ s → HasDerivAt F 0 τ := by
    intro τ hτ0 hτs
    have hsub : Metric.closedBall x (τ * mvpRadius α) ⊆ V :=
      subset_trans (Metric.closedBall_subset_closedBall
        (mul_le_mul_of_nonneg_right hτs (mvpRadius_pos hα).le)) hball
    have hvan := integral_mvpKernel_mul_inner_eq_zero hSsymm hSA hα hQ hsol hτ0 hsub
    have h2 := hFderiv τ
    rwa [hvan] at h2
  have hconst : ∀ a : ℝ, 0 < a → a ≤ s → F s = F a := by
    intro a ha0 has
    have hderiv : ∀ τ ∈ Set.Ico a s, HasDerivWithinAt F 0 (Set.Ici τ) τ := by
      intro τ hτ
      exact (hzeroderiv τ (lt_of_lt_of_le ha0 hτ.1) (le_of_lt hτ.2)).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero (a := a) (b := s) hFcont.continuousOn hderiv s
      ⟨has, le_rfl⟩
  have hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
    hFcont.continuousAt.mono_left nhdsWithin_le_nhds
  have heq : ∀ᶠ a in 𝓝[>] (0 : ℝ), F s = F a := by
    filter_upwards [Ioo_mem_nhdsGT hs] with a ha
    exact hconst a ha.1 (le_of_lt ha.2)
  have hlim2 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F s)) := tendsto_const_nhds.congr' heq
  have h0 : F 0 = F s := tendsto_nhds_unique hlim hlim2
  have hF0 : F 0 = (∫ w, mvpKernel S w) * u x := by
    simp only [hFdef, zero_smul, add_zero]
    exact integral_mul_const (u x) (mvpKernel S)
  have hgoal : F s = (∫ w, mvpKernel S w) * u x := h0.symm.trans hF0
  simpa only [hFdef] using hgoal

/-- **The mean value property for the gradient.**  Differentiating the mean value property in the
base point `x` along a direction `e`. -/
theorem integral_mvpKernel_mul_inner_gradient_eq
    {A S : Euc d →L[ℝ] Euc d} (hSsymm : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫)
    (hSA : ∀ v : Euc d, S (A v) = v)
    {α : ℝ} (hα : 0 < α) (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w)
    {V : Set (Euc d)} {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) (hus : HasCompactSupport u)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∫ y, ⟪A (gradient u y), gradient ψ y⟫ = 0)
    {x : Euc d} {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hball : Metric.closedBall x (s * mvpRadius α + δ) ⊆ V) (e : Euc d) :
    ∫ w, mvpKernel S w * ⟪gradient u (x + s • w), e⟫ =
      (∫ w, mvpKernel S w) * ⟪gradient u x, e⟫ := by
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ,
      g = fun t : ℝ => ∫ w, mvpKernel S w * u (x + s • w + t • e) := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ → ℝ, p = fun t : ℝ => (∫ w, mvpKernel S w) * u (x + t • e) :=
    ⟨_, rfl⟩
  -- the derivative of `g` at `0`
  have hgd : HasDerivAt g (∫ w, mvpKernel S w * ⟪gradient u (x + s • w), e⟫) 0 := by
    have hraw := hasDerivAt_integral_mvpKernel (q := fun w : Euc d => x + s • w)
      (c := fun _ : Euc d => e) hα hQ hu hus
      (continuous_const.add (continuous_id'.const_smul s)) continuous_const (norm_nonneg e)
      (fun w _ => le_rfl) 0
    simp only [zero_smul, add_zero] at hraw
    rw [hgdef]
    exact hraw
  -- the derivative of `p` at `0`
  have hpd : HasDerivAt p ((∫ w, mvpKernel S w) * ⟪gradient u x, e⟫) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => t • e) e 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const e
    have h1 : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
      simpa using h2.const_add x
    have h4 : HasFDerivAt u (fderiv ℝ u x) x :=
      ((hu.differentiable one_ne_zero) x).hasFDerivAt
    have h3 : HasDerivAt (fun t : ℝ => u (x + t • e)) (fderiv ℝ u x e) 0 :=
      h4.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    rw [hpdef]
    have h6 := h3.const_mul (∫ w, mvpKernel S w)
    rwa [fderiv_apply_eq_inner_gradient u x e] at h6
  -- the two functions agree near `0`
  have heq : g =ᶠ[𝓝 (0 : ℝ)] p := by
    have hball0 : (0 : ℝ) < δ / (‖e‖ + 1) := div_pos hδ (by positivity)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hball0] with t ht
    have htabs : |t| < δ / (‖e‖ + 1) := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht
    have hte : |t| * ‖e‖ ≤ δ := by
      have h1 : |t| * (‖e‖ + 1) ≤ δ := by
        rw [← le_div_iff₀ (by positivity)]
        exact htabs.le
      nlinarith [abs_nonneg t, norm_nonneg e]
    have hsub : Metric.closedBall (x + t • e) (s * mvpRadius α) ⊆ V := by
      refine subset_trans (fun z hz => ?_) hball
      rw [Metric.mem_closedBall] at hz ⊢
      have h1 : dist z x ≤ dist z (x + t • e) + dist (x + t • e) x := dist_triangle _ _ _
      have h2 : dist (x + t • e) x = |t| * ‖e‖ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      rw [h2] at h1
      linarith
    have hmvp := integral_mvpKernel_mul_comp_eq hSsymm hSA hα hQ hu hus hsol (x := x + t • e)
      hs hsub
    have hshift : ∀ w : Euc d, x + t • e + s • w = x + s • w + t • e := by
      intro w
      abel
    simp only [hgdef, hpdef]
    rw [← hmvp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show mvpKernel S w * u (x + s • w + t • e) = mvpKernel S w * u (x + t • e + s • w)
    rw [hshift w]
  have hgd2 : HasDerivAt p (∫ w, mvpKernel S w * ⟪gradient u (x + s • w), e⟫) 0 :=
    hgd.congr_of_eventuallyEq heq.symm
  exact hgd2.unique hpd

/-! ### The rescaled kernel as a function of the base point -/

theorem support_mvpKernel_comp_subset {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) (z : Euc d) {s : ℝ} (hs : 0 < s) :
    (Function.support fun y : Euc d => mvpKernel S (s⁻¹ • (y - z))) ⊆
      Metric.closedBall z (s * mvpRadius α) := by
  intro y hy
  have h1 : s⁻¹ • (y - z) ∈ Function.support (mvpKernel S) := hy
  have h2 : ‖s⁻¹ • (y - z)‖ ≤ mvpRadius α := by
    have hmem := support_mvpKernel_subset hα hQ h1
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)] at h2
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h3 : ‖y - z‖ = s * (s⁻¹ * ‖y - z‖) := by
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [h3]
  exact mul_le_mul_of_nonneg_left h2 hs.le

theorem continuous_mvpKernel_comp (S : Euc d →L[ℝ] Euc d) (z : Euc d) (s : ℝ) :
    Continuous fun y : Euc d => mvpKernel S (s⁻¹ • (y - z)) :=
  (continuous_mvpKernel S).comp ((continuous_id.sub continuous_const).const_smul s⁻¹)

/-- The total mass of the rescaled kernel. -/
theorem integral_mvpKernel_comp (S : Euc d →L[ℝ] Euc d) (z : Euc d) {s : ℝ} (hs : 0 < s) :
    ∫ y, mvpKernel S (s⁻¹ • (y - z)) = s ^ d * ∫ w, mvpKernel S w := by
  have h := integral_comp_inv_smul_sub (mvpKernel S) z hs
  have habs : |((s : ℝ) ^ d)⁻¹| = ((s : ℝ) ^ d)⁻¹ :=
    abs_of_pos (inv_pos.2 (pow_pos hs d))
  rw [habs] at h
  have hsd : ((s : ℝ) ^ d) ≠ 0 := (pow_pos hs d).ne'
  rw [h, ← mul_assoc, mul_inv_cancel₀ hsd, one_mul]

/-- **The mean value property for the gradient, written as an integral over the base ball.** -/
theorem integral_mvpKernel_comp_mul_inner_eq
    {A S : Euc d →L[ℝ] Euc d} (hSsymm : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫)
    (hSA : ∀ v : Euc d, S (A v) = v)
    {α : ℝ} (hα : 0 < α) (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w)
    {V : Set (Euc d)} {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) (hus : HasCompactSupport u)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∫ y, ⟪A (gradient u y), gradient ψ y⟫ = 0)
    {z : Euc d} {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hball : Metric.closedBall z (s * mvpRadius α + δ) ⊆ V) (e : Euc d) :
    (s ^ d * ((∫ w, mvpKernel S w) * ⟪gradient u z, e⟫)) =
      ∫ y, mvpKernel S (s⁻¹ • (y - z)) * ⟪gradient u y, e⟫ := by
  have hmvp := integral_mvpKernel_mul_inner_gradient_eq hSsymm hSA hα hQ hu hus hsol hs hδ
    hball e
  have hcov : ∫ w, mvpKernel S w * ⟪gradient u (z + s • w), e⟫ =
      |((s : ℝ) ^ d)⁻¹| * ∫ y, mvpKernel S (s⁻¹ • (y - z)) *
        ⟪gradient u (z + s • (s⁻¹ • (y - z))), e⟫ :=
    integral_comp_inv_smul_sub
      (fun w : Euc d => mvpKernel S w * ⟪gradient u (z + s • w), e⟫) z hs
  have hpt : ∀ y : Euc d,
      mvpKernel S (s⁻¹ • (y - z)) * ⟪gradient u (z + s • (s⁻¹ • (y - z))), e⟫ =
        mvpKernel S (s⁻¹ • (y - z)) * ⟪gradient u y, e⟫ := by
    intro y
    have hy : z + s • (s⁻¹ • (y - z)) = y := by
      rw [smul_inv_smul₀ hs.ne']
      abel
    rw [hy]
  simp only [hpt] at hcov
  rw [hmvp] at hcov
  have habs : |((s : ℝ) ^ d)⁻¹| = ((s : ℝ) ^ d)⁻¹ :=
    abs_of_pos (inv_pos.2 (pow_pos hs d))
  rw [habs] at hcov
  have hsd : ((s : ℝ) ^ d) ≠ 0 := (pow_pos hs d).ne'
  rw [hcov, ← mul_assoc, mul_inv_cancel₀ hsd, one_mul]

theorem integrable_mvpKernel_comp_mul {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) (z : Euc d) {s : ℝ} (hs : 0 < s)
    {g : Euc d → ℝ} (hg : Continuous g) :
    Integrable fun y : Euc d => mvpKernel S (s⁻¹ • (y - z)) * g y := by
  refine Continuous.integrable_of_hasCompactSupport
    ((continuous_mvpKernel_comp S z s).mul hg) ?_
  refine HasCompactSupport.intro (isCompact_closedBall z (s * mvpRadius α)) ?_
  intro y hy
  have h0 : mvpKernel S (s⁻¹ • (y - z)) = 0 := by
    by_contra hne
    exact hy (support_mvpKernel_comp_subset hα hQ z hs hne)
  rw [h0, zero_mul]

theorem integrable_mvpKernel_comp {S : Euc d →L[ℝ] Euc d} {α : ℝ} (hα : 0 < α)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) (z : Euc d) {s : ℝ} (hs : 0 < s) :
    Integrable fun y : Euc d => mvpKernel S (s⁻¹ • (y - z)) := by
  have h := integrable_mvpKernel_comp_mul hα hQ z hs (g := fun _ : Euc d => (1 : ℝ))
    continuous_const
  simpa using h


/-! ### The interior derivative estimate -/

/-- Two kernels with the same total mass may be tested against `G - m` for any constant `m`. -/
theorem integral_kernel_diff_mul (K₁ K₂ G : Euc d → ℝ) (m : ℝ)
    (h1 : Integrable fun y => K₁ y * G y) (h2 : Integrable fun y => K₂ y * G y)
    (hk1 : Integrable K₁) (hk2 : Integrable K₂) (hmass : (∫ y, K₁ y) = ∫ y, K₂ y) :
    ∫ y, (K₁ y - K₂ y) * (G y - m) = (∫ y, K₁ y * G y) - ∫ y, K₂ y * G y := by
  have hexp : ∀ y : Euc d, (K₁ y - K₂ y) * (G y - m) =
      K₁ y * G y - K₂ y * G y - (m * K₁ y - m * K₂ y) := by
    intro y
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_sub (h1.sub' h2) ((hk1.const_mul m).sub' (hk2.const_mul m)),
    integral_sub h1 h2, integral_sub (hk1.const_mul m) (hk2.const_mul m),
    integral_const_mul, integral_const_mul, hmass]
  ring

/-- **The interior derivative estimate for a constant symmetric elliptic operator.**  Comparing
the mean value property for the gradient at two base points `x₁, x₂`: the two kernels differ by
`O(‖x₁ - x₂‖ / s)` pointwise, both are supported in `B̄(x₀, r)`, and they have the same total
mass, so any constant `v₀` may be subtracted from `∇u`.  This is the `ℝ^d` substitute for the
classical derivative estimate obtained from the Poisson kernel. -/
theorem abs_integral_mvpKernel_mul_norm_gradient_sub_le
    {A S : Euc d →L[ℝ] Euc d} (hSsymm : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫)
    (hSA : ∀ v : Euc d, S (A v) = v)
    {α : ℝ} (hα : 0 < α) (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w)
    {V : Set (Euc d)} {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) (hus : HasCompactSupport u)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∫ y, ⟪A (gradient u y), gradient ψ y⟫ = 0)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ a b : Euc d, |mvpKernel S a - mvpKernel S b| ≤ L * ‖a - b‖)
    {x₀ : Euc d} {r s δ : ℝ} (hr : 0 < r) (hs : 0 < s) (hδ : 0 < δ)
    (hsr : s * mvpRadius α ≤ r / 2)
    (hcover : ∀ z ∈ Metric.closedBall x₀ (r / 2),
      Metric.closedBall z (s * mvpRadius α + δ) ⊆ V)
    (v₀ : Euc d) {x₁ x₂ : Euc d}
    (hx₁ : x₁ ∈ Metric.closedBall x₀ (r / 2)) (hx₂ : x₂ ∈ Metric.closedBall x₀ (r / 2)) :
    |∫ w, mvpKernel S w| * ‖gradient u x₁ - gradient u x₂‖ ≤
      L / s ^ (d + 1) * (∫ y in Metric.closedBall x₀ r, ‖gradient u y - v₀‖) * ‖x₁ - x₂‖ := by
  obtain ⟨e, hedef⟩ : ∃ e : Euc d, e = gradient u x₁ - gradient u x₂ := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ∫ w, mvpKernel S w := ⟨_, rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ, J = ∫ y in Metric.closedBall x₀ r, ‖gradient u y - v₀‖ :=
    ⟨_, rfl⟩
  have hcpt : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  have hJ0 : 0 ≤ J := by
    rw [hJdef]
    exact setIntegral_nonneg measurableSet_closedBall fun y _ => norm_nonneg _
  have hsd : (0 : ℝ) < s ^ d := pow_pos hs d
  have hsd1 : (0 : ℝ) < s ^ (d + 1) := pow_pos hs (d + 1)
  have hGc' : Continuous fun y : Euc d => ⟪gradient u y, e⟫ :=
    (continuous_gradient hu).inner continuous_const
  -- the two mean value identities for the gradient
  have hA1 : s ^ d * (c * ⟪gradient u x₁, e⟫) =
      ∫ y, mvpKernel S (s⁻¹ • (y - x₁)) * ⟪gradient u y, e⟫ := by
    rw [hcdef]
    exact integral_mvpKernel_comp_mul_inner_eq hSsymm hSA hα hQ hu hus hsol hs hδ
      (hcover x₁ hx₁) e
  have hA2 : s ^ d * (c * ⟪gradient u x₂, e⟫) =
      ∫ y, mvpKernel S (s⁻¹ • (y - x₂)) * ⟪gradient u y, e⟫ := by
    rw [hcdef]
    exact integral_mvpKernel_comp_mul_inner_eq hSsymm hSA hα hQ hu hus hsol hs hδ
      (hcover x₂ hx₂) e
  have hi1 : Integrable fun y : Euc d =>
      mvpKernel S (s⁻¹ • (y - x₁)) * ⟪gradient u y, e⟫ :=
    integrable_mvpKernel_comp_mul hα hQ x₁ hs hGc'
  have hi2 : Integrable fun y : Euc d =>
      mvpKernel S (s⁻¹ • (y - x₂)) * ⟪gradient u y, e⟫ :=
    integrable_mvpKernel_comp_mul hα hQ x₂ hs hGc'
  have hk1 : Integrable fun y : Euc d => mvpKernel S (s⁻¹ • (y - x₁)) :=
    integrable_mvpKernel_comp hα hQ x₁ hs
  have hk2 : Integrable fun y : Euc d => mvpKernel S (s⁻¹ • (y - x₂)) :=
    integrable_mvpKernel_comp hα hQ x₂ hs
  have hmass : (∫ y, mvpKernel S (s⁻¹ • (y - x₁))) = ∫ y, mvpKernel S (s⁻¹ • (y - x₂)) := by
    rw [integral_mvpKernel_comp S x₁ hs, integral_mvpKernel_comp S x₂ hs]
  have hid : ∫ y, (mvpKernel S (s⁻¹ • (y - x₁)) - mvpKernel S (s⁻¹ • (y - x₂))) *
      (⟪gradient u y, e⟫ - ⟪v₀, e⟫) =
      (∫ y, mvpKernel S (s⁻¹ • (y - x₁)) * ⟪gradient u y, e⟫) -
        ∫ y, mvpKernel S (s⁻¹ • (y - x₂)) * ⟪gradient u y, e⟫ :=
    integral_kernel_diff_mul (fun y : Euc d => mvpKernel S (s⁻¹ • (y - x₁)))
      (fun y : Euc d => mvpKernel S (s⁻¹ • (y - x₂))) (fun y : Euc d => ⟪gradient u y, e⟫)
      ⟪v₀, e⟫ hi1 hi2 hk1 hk2 hmass
  have hnorm : ⟪gradient u x₁, e⟫ - ⟪gradient u x₂, e⟫ = ‖e‖ ^ 2 := by
    rw [← inner_sub_left, ← hedef, real_inner_self_eq_norm_sq]
  have hrhs : (∫ y, mvpKernel S (s⁻¹ • (y - x₁)) * ⟪gradient u y, e⟫) -
      ∫ y, mvpKernel S (s⁻¹ • (y - x₂)) * ⟪gradient u y, e⟫ = s ^ d * (c * ‖e‖ ^ 2) := by
    rw [← hA1, ← hA2]
    linear_combination (s ^ d * c) * hnorm
  rw [hrhs] at hid
  -- the kernels are close and are supported in the ball
  have hincl : ∀ z ∈ Metric.closedBall x₀ (r / 2),
      Metric.closedBall z (s * mvpRadius α) ⊆ Metric.closedBall x₀ r := by
    intro z hz y hy
    rw [Metric.mem_closedBall] at hz hy ⊢
    have h1 : dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
    linarith
  have hΔbound : ∀ y : Euc d,
      |mvpKernel S (s⁻¹ • (y - x₁)) - mvpKernel S (s⁻¹ • (y - x₂))| ≤ L / s * ‖x₁ - x₂‖ := by
    intro y
    have h1 := hLip (s⁻¹ • (y - x₁)) (s⁻¹ • (y - x₂))
    have h2 : s⁻¹ • (y - x₁) - s⁻¹ • (y - x₂) = s⁻¹ • (x₂ - x₁) := by
      rw [← smul_sub]
      congr 1
      abel
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs), norm_sub_rev] at h1
    refine h1.trans_eq ?_
    ring
  have hΔsupp : ∀ y : Euc d, y ∉ Metric.closedBall x₀ r →
      (mvpKernel S (s⁻¹ • (y - x₁)) - mvpKernel S (s⁻¹ • (y - x₂))) *
        (⟪gradient u y, e⟫ - ⟪v₀, e⟫) = 0 := by
    intro y hy
    have hz1 : mvpKernel S (s⁻¹ • (y - x₁)) = 0 := by
      by_contra hne
      exact hy (hincl x₁ hx₁ (support_mvpKernel_comp_subset hα hQ x₁ hs hne))
    have hz2 : mvpKernel S (s⁻¹ • (y - x₂)) = 0 := by
      by_contra hne
      exact hy (hincl x₂ hx₂ (support_mvpKernel_comp_subset hα hQ x₂ hs hne))
    rw [hz1, hz2, sub_self, zero_mul]
  -- the estimate for the tested integral
  have habs : |∫ y, (mvpKernel S (s⁻¹ • (y - x₁)) - mvpKernel S (s⁻¹ • (y - x₂))) *
      (⟪gradient u y, e⟫ - ⟪v₀, e⟫)| ≤ L / s * ‖x₁ - x₂‖ * ‖e‖ * J := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hΔsupp]
    refine le_trans abs_integral_le_integral_abs ?_
    have hc1 : Continuous fun y : Euc d =>
        |(mvpKernel S (s⁻¹ • (y - x₁)) - mvpKernel S (s⁻¹ • (y - x₂))) *
          (⟪gradient u y, e⟫ - ⟪v₀, e⟫)| :=
      (((continuous_mvpKernel_comp S x₁ s).sub (continuous_mvpKernel_comp S x₂ s)).mul
        (hGc'.sub continuous_const)).abs
    have hc2 : Continuous fun y : Euc d =>
        L / s * ‖x₁ - x₂‖ * ‖e‖ * ‖gradient u y - v₀‖ :=
      continuous_const.mul ((continuous_gradient hu).sub continuous_const).norm
    have hmono : (∫ y in Metric.closedBall x₀ r,
        |(mvpKernel S (s⁻¹ • (y - x₁)) - mvpKernel S (s⁻¹ • (y - x₂))) *
          (⟪gradient u y, e⟫ - ⟪v₀, e⟫)|) ≤
        ∫ y in Metric.closedBall x₀ r, L / s * ‖x₁ - x₂‖ * ‖e‖ * ‖gradient u y - v₀‖ := by
      refine setIntegral_mono_on (hc1.continuousOn.integrableOn_compact hcpt)
        (hc2.continuousOn.integrableOn_compact hcpt) measurableSet_closedBall ?_
      intro y _
      have hg : |⟪gradient u y, e⟫ - ⟪v₀, e⟫| ≤ ‖gradient u y - v₀‖ * ‖e‖ := by
        rw [← inner_sub_left]
        exact abs_real_inner_le_norm _ _
      have hLs : (0 : ℝ) ≤ L / s * ‖x₁ - x₂‖ :=
        mul_nonneg (div_nonneg hL0 hs.le) (norm_nonneg _)
      rw [abs_mul]
      calc |mvpKernel S (s⁻¹ • (y - x₁)) - mvpKernel S (s⁻¹ • (y - x₂))| *
            |⟪gradient u y, e⟫ - ⟪v₀, e⟫|
          ≤ (L / s * ‖x₁ - x₂‖) * (‖gradient u y - v₀‖ * ‖e‖) :=
            mul_le_mul (hΔbound y) hg (abs_nonneg _) hLs
        _ = L / s * ‖x₁ - x₂‖ * ‖e‖ * ‖gradient u y - v₀‖ := by ring
    rw [integral_const_mul, ← hJdef] at hmono
    exact hmono
  rw [hid] at habs
  have hLHS : |s ^ d * (c * ‖e‖ ^ 2)| = s ^ d * (|c| * ‖e‖ ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_pos hsd, abs_of_nonneg (sq_nonneg ‖e‖)]
  rw [hLHS] at habs
  -- conclude
  rw [← hcdef, ← hJdef, ← hedef]
  rcases eq_or_lt_of_le (norm_nonneg e) with he0 | hepos
  · rw [← he0, mul_zero]
    have : (0 : ℝ) ≤ L / s ^ (d + 1) * J * ‖x₁ - x₂‖ :=
      mul_nonneg (mul_nonneg (div_nonneg hL0 hsd1.le) hJ0) (norm_nonneg _)
    exact this
  · have h1 : s * (s ^ d * (|c| * ‖e‖ ^ 2)) ≤ s * (L / s * ‖x₁ - x₂‖ * ‖e‖ * J) :=
      mul_le_mul_of_nonneg_left habs hs.le
    have hsne : s ≠ 0 := hs.ne'
    have h2 : s * (L / s * ‖x₁ - x₂‖ * ‖e‖ * J) = L * ‖x₁ - x₂‖ * ‖e‖ * J := by
      field_simp
      try ring
    have h3 : s * (s ^ d * (|c| * ‖e‖ ^ 2)) = s ^ (d + 1) * (|c| * ‖e‖ ^ 2) := by
      rw [pow_succ]
      ring
    rw [h2, h3] at h1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hsd1]
    have e1 : |c| * ‖e‖ * s ^ (d + 1) * ‖e‖ = s ^ (d + 1) * (|c| * ‖e‖ ^ 2) := by ring
    have e2 : L * J * ‖x₁ - x₂‖ * ‖e‖ = L * ‖x₁ - x₂‖ * ‖e‖ * J := by ring
    have h4 : |c| * ‖e‖ * s ^ (d + 1) * ‖e‖ ≤ L * J * ‖x₁ - x₂‖ * ‖e‖ := by
      rw [e1, e2]
      exact h1
    exact le_of_mul_le_mul_right h4 hepos

/-! ### Uniform bounds on the kernel

For the constant of the interior derivative estimate to depend only on `d`, `μ` and `Λ` the
Lipschitz constant of `χ_S` must be bounded above and `|∫ χ_S|` bounded below uniformly over the
admissible `S = A⁻¹`.  Both follow from `α ‖w‖² ≤ Q_S w` and `‖S‖ ≤ β`. -/

noncomputable def mvpProfile'' : ℝ → ℝ := deriv mvpProfile'

theorem contDiff_mvpProfile'' : ContDiff ℝ ∞ mvpProfile'' :=
  (contDiff_infty_iff_deriv.1 contDiff_mvpProfile').2

theorem continuous_mvpProfile'' : Continuous mvpProfile'' := contDiff_mvpProfile''.continuous

theorem hasDerivAt_mvpProfile' (t : ℝ) : HasDerivAt mvpProfile' (mvpProfile'' t) t :=
  ((contDiff_infty_iff_deriv.1 contDiff_mvpProfile').1 t).hasDerivAt

theorem mvpProfile'_of_lt_one {t : ℝ} (ht : t < 1) : mvpProfile' t = 0 := by
  have he : mvpProfile =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_Iio (a := (1 : ℝ))).mem_nhds (Set.mem_Iio.2 ht)] with y hy
    exact mvpProfile_of_le_one (le_of_lt hy)
  rw [mvpProfile', he.deriv_eq, deriv_const]

theorem support_mvpProfile'_subset : Function.support mvpProfile' ⊆ Set.Icc 1 2 := by
  intro t ht
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact ht (mvpProfile'_of_lt_one (not_le.1 h))
  · by_contra h
    exact ht (mvpProfile'_of_two_lt (not_le.1 h))

theorem support_mvpProfile''_subset : Function.support mvpProfile'' ⊆ Set.Icc 1 2 :=
  (support_deriv_subset).trans (closure_minimal support_mvpProfile'_subset isClosed_Icc)

theorem exists_bound_mvpProfile'' : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |mvpProfile'' t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    continuous_mvpProfile''.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (1 : ℝ) 2
  · have h1 : |mvpProfile'' t| ≤ M := by
      have := hM t ht
      rwa [Real.norm_eq_abs] at this
    exact h1.trans (le_max_left _ _)
  · have h0 : mvpProfile'' t = 0 := by
      by_contra hne
      exact ht (support_mvpProfile''_subset hne)
    rw [h0, abs_zero]
    exact le_max_right _ _

/-- `∇χ_S w = 4 θ''(Q_S w) • S w`. -/
theorem gradient_mvpKernel {S : Euc d →L[ℝ] Euc d} (hS : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫)
    (w : Euc d) : gradient (mvpKernel S) w = (4 * mvpProfile'' (ellQuad S w)) • S w := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * mvpProfile' t) (2 * mvpProfile'' (ellQuad S w))
      (ellQuad S w) := (hasDerivAt_mvpProfile' (ellQuad S w)).const_mul 2
  have hcomp : HasFDerivAt ((fun t : ℝ => 2 * mvpProfile' t) ∘ ellQuad S)
      ((2 * mvpProfile'' (ellQuad S w)) • ((2 : ℝ) • innerSL ℝ (S w))) w :=
    HasDerivAt.comp_hasFDerivAt w h1 (hasFDerivAt_ellQuad hS w)
  have hk : HasFDerivAt (mvpKernel S)
      ((2 * mvpProfile'' (ellQuad S w)) • ((2 : ℝ) • innerSL ℝ (S w))) w := hcomp
  refine ext_inner_right ℝ fun v => ?_
  rw [← fderiv_apply_eq_inner_gradient, hk.fderiv, _root_.smul_apply,
    _root_.smul_apply, innerSL_apply_apply, smul_eq_mul, smul_eq_mul,
    real_inner_smul_left]
  ring

/-- **A uniform Lipschitz bound for the kernel.** -/
theorem abs_mvpKernel_sub_le {S : Euc d →L[ℝ] Euc d} {α β M : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hM0 : 0 ≤ M) (hS : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫)
    (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) (hSn : ‖S‖ ≤ β)
    (hM : ∀ t : ℝ, |mvpProfile'' t| ≤ M) (a b : Euc d) :
    |mvpKernel S a - mvpKernel S b| ≤ 4 * M * β * mvpRadius α * ‖a - b‖ := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 4 * M * β * mvpRadius α := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hβ) (mvpRadius_pos hα).le
  have hgrad : ∀ w : Euc d, ‖gradient (mvpKernel S) w‖ ≤ L := by
    intro w
    rw [gradient_mvpKernel hS, norm_smul, Real.norm_eq_abs, hLdef]
    rcases eq_or_ne (mvpProfile'' (ellQuad S w)) 0 with h0 | h0
    · rw [h0, mul_zero, abs_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hβ) (mvpRadius_pos hα).le
    · have hmem : ellQuad S w ≤ 2 := (Set.mem_Icc.1 (support_mvpProfile''_subset h0)).2
      have hwn : ‖w‖ ≤ mvpRadius α := norm_le_mvpRadius hα hQ hmem
      have hSw : ‖S w‖ ≤ β * mvpRadius α :=
        (S.le_opNorm w).trans (mul_le_mul hSn hwn (norm_nonneg _) hβ)
      have habs : |4 * mvpProfile'' (ellQuad S w)| ≤ 4 * M := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        exact mul_le_mul_of_nonneg_left (hM _) (by norm_num)
      calc |4 * mvpProfile'' (ellQuad S w)| * ‖S w‖
          ≤ (4 * M) * (β * mvpRadius α) :=
            mul_le_mul habs hSw (norm_nonneg _) (by linarith)
        _ = 4 * M * β * mvpRadius α := by ring
  have hfd : ∀ x : Euc d, ‖fderiv ℝ (mvpKernel S) x‖ ≤ L := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ hL0 fun v => ?_
    rw [Real.norm_eq_abs, fderiv_apply_eq_inner_gradient]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hgrad x) (norm_nonneg _))
  have hk1 : ContDiff ℝ 1 (mvpKernel S) := (contDiff_mvpKernel S).of_le (by simp)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := mvpKernel S)
    (fun x _ => (hk1.differentiable one_ne_zero) x) (fun x _ => hfd x) convex_univ
    (Set.mem_univ b) (Set.mem_univ a)
  rw [Real.norm_eq_abs] at h
  rw [← hLdef]
  exact h

/-- **A uniform negative upper bound for `∫ χ_S`.**  The profile has `θ' = -1` at some
`t₀ ∈ (1, 2)`, hence `θ' < -1/2` on a fixed interval around `t₀`; the level set `{Q_S = t₀}` is
nonempty and lies in the ball of radius `√(t₀/α)`, and `Q_S` has gradient bounded by `2 β √(t₀/α)`
there, so the shell `{|Q_S - t₀| < γ}` contains a ball of a radius depending only on `α`, `β` and
the profile. -/
theorem exists_integral_mvpKernel_le_neg (d : ℕ) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {e : Euc d} (he : e ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ S : Euc d →L[ℝ] Euc d, (∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫) →
      (∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w) → ‖S‖ ≤ β →
      ∫ w, mvpKernel S w ≤ -κ := by
  obtain ⟨t₀, ht₀, hdt₀⟩ := exists_mvpProfile'_eq_neg_one
  have ht₀1 : (1 : ℝ) < t₀ := ht₀.1
  have hopen : IsOpen {t : ℝ | mvpProfile' t < -(1 / 2)} :=
    isOpen_lt continuous_mvpProfile' continuous_const
  have hmemt : t₀ ∈ {t : ℝ | mvpProfile' t < -(1 / 2)} := by
    show mvpProfile' t₀ < -(1 / 2)
    rw [hdt₀]; norm_num
  obtain ⟨γ, hγ0, hγ⟩ := Metric.isOpen_iff.1 hopen t₀ hmemt
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = Real.sqrt (t₀ / α) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min 1 (γ / (2 * β * R + β + 1)) := ⟨_, rfl⟩
  have hden : (0 : ℝ) < 2 * β * R + β + 1 := by nlinarith [mul_nonneg hβ.le hR0, hβ]
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    exact lt_min one_pos (div_pos hγ0 hden)
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact min_le_left _ _
  have hρ2 : ρ * (2 * β * R + β) < γ := by
    have h1 : ρ ≤ γ / (2 * β * R + β + 1) := by rw [hρdef]; exact min_le_right _ _
    have h2 : ρ * (2 * β * R + β + 1) ≤ γ := by
      rw [← le_div_iff₀ hden]
      exact h1
    nlinarith [hρ0, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hβ.le) hR0]
  refine ⟨ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1),
    mul_pos (pow_pos hρ0 d) volume_real_closedBall_pos, ?_⟩
  intro S hS hQ hSn
  -- a point on the level set `{Q_S = t₀}`
  have hene : (0 : ℝ) < ‖e‖ := norm_pos_iff.2 he
  have hQe : 0 < ellQuad S e := lt_of_lt_of_le (mul_pos hα (pow_pos hene 2)) (hQ e)
  obtain ⟨wstar, hwstar⟩ : ∃ w : Euc d, ellQuad S w = t₀ := by
    refine ⟨Real.sqrt (t₀ / ellQuad S e) • e, ?_⟩
    have hne : ellQuad S e ≠ 0 := hQe.ne'
    rw [ellQuad_smul, Real.sq_sqrt (div_nonneg (by linarith) hQe.le)]
    field_simp
  have hwn : ‖wstar‖ ≤ R := by
    have h1 : α * ‖wstar‖ ^ 2 ≤ t₀ := by
      have := hQ wstar
      rw [hwstar] at this
      exact this
    have h2 : ‖wstar‖ ^ 2 ≤ t₀ / α := by
      rw [le_div_iff₀ hα, mul_comm]
      exact h1
    have h3 : ‖wstar‖ = Real.sqrt (‖wstar‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [hRdef, h3]
    exact Real.sqrt_le_sqrt h2
  -- the kernel is at most `-1` on a ball around `wstar`
  have hker : ∀ w ∈ Metric.closedBall wstar ρ, mvpKernel S w ≤ -1 := by
    intro w hw
    have hdw : ‖w - wstar‖ ≤ ρ := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.1 hw
    have hexp : ellQuad S w = t₀ + 2 * ⟪S wstar, w - wstar⟫ + ellQuad S (w - wstar) := by
      have h := ellQuad_add hS wstar (w - wstar)
      rw [show wstar + (w - wstar) = w from by abel, hwstar] at h
      exact h
    have hb1 : |2 * ⟪S wstar, w - wstar⟫| ≤ 2 * β * R * ρ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h1 : |⟪S wstar, w - wstar⟫| ≤ ‖S wstar‖ * ‖w - wstar‖ :=
        abs_real_inner_le_norm _ _
      have h2 : ‖S wstar‖ ≤ β * R :=
        (S.le_opNorm wstar).trans (mul_le_mul hSn hwn (norm_nonneg _) hβ.le)
      have h3 : ‖S wstar‖ * ‖w - wstar‖ ≤ (β * R) * ρ :=
        mul_le_mul h2 hdw (norm_nonneg _) (mul_nonneg hβ.le hR0)
      calc 2 * |⟪S wstar, w - wstar⟫| ≤ 2 * ((β * R) * ρ) := by linarith
        _ = 2 * β * R * ρ := by ring
    have hb2 : |ellQuad S (w - wstar)| ≤ β * ρ := by
      have h1 : |ellQuad S (w - wstar)| ≤ ‖S‖ * ‖w - wstar‖ * ‖w - wstar‖ :=
        abs_ellQuad_le S _
      have h2 : ‖S‖ * ‖w - wstar‖ * ‖w - wstar‖ ≤ β * ρ * 1 := by
        have hn0 : (0 : ℝ) ≤ ‖w - wstar‖ := norm_nonneg _
        have h3 : ‖w - wstar‖ ≤ 1 := hdw.trans hρ1
        have h4 : ‖S‖ * ‖w - wstar‖ ≤ β * ρ :=
          mul_le_mul hSn hdw hn0 hβ.le
        exact mul_le_mul h4 h3 hn0 (mul_nonneg hβ.le hρ0.le)
      rw [mul_one] at h2
      exact h1.trans h2
    have hclose : |ellQuad S w - t₀| < γ := by
      have hsub : ellQuad S w - t₀ = 2 * ⟪S wstar, w - wstar⟫ + ellQuad S (w - wstar) := by
        rw [hexp]; ring
      rw [hsub]
      calc |2 * ⟪S wstar, w - wstar⟫ + ellQuad S (w - wstar)|
          ≤ |2 * ⟪S wstar, w - wstar⟫| + |ellQuad S (w - wstar)| := abs_add_le _ _
        _ ≤ 2 * β * R * ρ + β * ρ := add_le_add hb1 hb2
        _ = ρ * (2 * β * R + β) := by ring
        _ < γ := hρ2
    have hmem : ellQuad S w ∈ Metric.ball t₀ γ := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact hclose
    have h5 : mvpProfile' (ellQuad S w) < -(1 / 2) := hγ hmem
    show 2 * mvpProfile' (ellQuad S w) ≤ -1
    linarith
  -- integrate
  have hintS : Integrable (mvpKernel S) := integrable_mvpKernel hα hQ
  have hBfin : volume (Metric.closedBall wstar ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hsetle : ∫ w in Metric.closedBall wstar ρ, mvpKernel S w ≤
      -volume.real (Metric.closedBall wstar ρ) := by
    have h1 : ∫ w in Metric.closedBall wstar ρ, mvpKernel S w ≤
        ∫ _w in Metric.closedBall wstar ρ, (-1 : ℝ) :=
      setIntegral_mono_on hintS.integrableOn (integrableOn_const hBfin)
        measurableSet_closedBall hker
    rwa [setIntegral_const, smul_eq_mul, mul_neg_one] at h1
  have hnegint : Integrable fun w : Euc d => -(mvpKernel S w) := hintS.neg
  have hle : ∫ w, mvpKernel S w ≤ ∫ w in Metric.closedBall wstar ρ, mvpKernel S w := by
    have h1 : ∫ w in Metric.closedBall wstar ρ, -(mvpKernel S w) ≤ ∫ w, -(mvpKernel S w) :=
      setIntegral_le_integral hnegint
        (Filter.Eventually.of_forall fun w => neg_nonneg.2 (mvpKernel_nonpos S w))
    rw [integral_neg, integral_neg] at h1
    linarith
  have hvol : volume.real (Metric.closedBall wstar ρ) =
      ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) :=
    volume_real_closedBall wstar hρ0.le
  rw [hvol] at hsetle
  linarith

/-! ### The inverse of a symmetric elliptic coefficient matrix -/

/-- A symmetric `μ`-elliptic `A` is invertible, its inverse `S` is symmetric, `‖S‖ ≤ 1/μ`, and
`Q_S w = ⟪S w, w⟫ ≥ μ (‖A‖ + 1)^{-2} ‖w‖²`. -/
theorem exists_inverse_of_symmetric_elliptic {μ : ℝ} (hμ : 0 < μ) (A : Euc d →L[ℝ] Euc d)
    (hsymm : ∀ p q : Euc d, ⟪A p, q⟫ = ⟪p, A q⟫)
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A ζ, ζ⟫) :
    ∃ S : Euc d →L[ℝ] Euc d, (∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫) ∧ (∀ v : Euc d, S (A v) = v) ∧
      ‖S‖ ≤ 1 / μ ∧ ∀ w : Euc d, μ / (‖A‖ + 1) ^ 2 * ‖w‖ ^ 2 ≤ ellQuad S w := by
  classical
  have hinj : Function.Injective ((A : Euc d →ₗ[ℝ] Euc d)) := by
    intro p q hpq
    have hEq : A p = A q := hpq
    have h1 : A (p - q) = 0 := by rw [map_sub, hEq, sub_self]
    have h2 : μ * ‖p - q‖ ^ 2 ≤ ⟪A (p - q), p - q⟫ := hell _
    rw [h1, inner_zero_left] at h2
    have h3 : ‖p - q‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 h3))
  have hsurj : Function.Surjective ((A : Euc d →ₗ[ℝ] Euc d)) :=
    LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨Ae, hAe⟩ : ∃ Ae : Euc d ≃L[ℝ] Euc d, ∀ w : Euc d, Ae w = A w :=
    ⟨(LinearEquiv.ofBijective (A : Euc d →ₗ[ℝ] Euc d) ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      fun _ => rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Euc d →L[ℝ] Euc d, S = (Ae.symm : Euc d →L[ℝ] Euc d) := ⟨_, rfl⟩
  have hSA : ∀ v : Euc d, S (A v) = v := by
    intro v
    have h : S (A v) = Ae.symm (A v) := by rw [hSdef]; rfl
    rw [h, ← hAe v, ContinuousLinearEquiv.symm_apply_apply]
  have hAS : ∀ w : Euc d, A (S w) = w := by
    intro w
    have h : S w = Ae.symm w := by rw [hSdef]; rfl
    rw [h, ← hAe (Ae.symm w), ContinuousLinearEquiv.apply_symm_apply]
  have hSsymm : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫ := by
    intro p q
    calc ⟪S p, q⟫ = ⟪S p, A (S q)⟫ := by rw [hAS]
      _ = ⟪A (S p), S q⟫ := (hsymm (S p) (S q)).symm
      _ = ⟪p, S q⟫ := by rw [hAS]
  have hmul : ∀ w : Euc d, μ * ‖S w‖ ≤ ‖w‖ := by
    intro w
    have h1 : μ * ‖S w‖ ^ 2 ≤ ⟪A (S w), S w⟫ := hell _
    rw [hAS] at h1
    have h2 : ⟪w, S w⟫ ≤ ‖w‖ * ‖S w‖ :=
      (le_abs_self _).trans (abs_real_inner_le_norm w (S w))
    rcases eq_or_lt_of_le (norm_nonneg (S w)) with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg w
    · nlinarith
  have hSn : ‖S‖ ≤ 1 / μ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (one_div_nonneg.2 hμ.le) fun w => ?_
    have h := hmul w
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hμ, mul_comm]
    exact h
  refine ⟨S, hSsymm, hSA, hSn, fun w => ?_⟩
  have hA1 : (0 : ℝ) < ‖A‖ + 1 := by positivity
  have hA1ne : (‖A‖ + 1) ≠ 0 := hA1.ne'
  have heq : ellQuad S w = ⟪A (S w), S w⟫ := by
    rw [hAS]
    show ⟪S w, w⟫ = ⟪w, S w⟫
    exact (real_inner_comm (S w) w).symm
  have h1 : μ * ‖S w‖ ^ 2 ≤ ellQuad S w := by
    rw [heq]
    exact hell (S w)
  have h3 : ‖A (S w)‖ ≤ ‖A‖ * ‖S w‖ := A.le_opNorm _
  rw [hAS] at h3
  have h4 : ‖w‖ ^ 2 ≤ (‖A‖ + 1) ^ 2 * ‖S w‖ ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg (S w), norm_nonneg A]
  calc μ / (‖A‖ + 1) ^ 2 * ‖w‖ ^ 2
      ≤ μ / (‖A‖ + 1) ^ 2 * ((‖A‖ + 1) ^ 2 * ‖S w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (div_nonneg hμ.le (sq_nonneg _))
    _ = μ * ‖S w‖ ^ 2 := by field_simp
    _ ≤ ellQuad S w := h1

/-! ### The `L¹`–`L²` bound on a ball -/

/-- `(∫_s g)² ≤ |s| ∫_s g²` — Cauchy–Schwarz against the constant `1`, obtained from Young's
inequality `2 t g ≤ g² + t²` with the optimal `t`. -/
theorem sq_setIntegral_le_mul {s : Set (Euc d)} {g : Euc d → ℝ} (hgi : IntegrableOn g s)
    (hg2 : IntegrableOn (fun y => g y ^ 2) s) (hsfin : volume s ≠ ⊤)
    (hspos : 0 < volume.real s) :
    (∫ y in s, g y) ^ 2 ≤ volume.real s * ∫ y in s, g y ^ 2 := by
  obtain ⟨Jv, hJv⟩ : ∃ J : ℝ, J = ∫ y in s, g y := ⟨_, rfl⟩
  obtain ⟨Iv, hIv⟩ : ∃ I : ℝ, I = ∫ y in s, g y ^ 2 := ⟨_, rfl⟩
  obtain ⟨Vv, hVv⟩ : ∃ V : ℝ, V = volume.real s := ⟨_, rfl⟩
  have hVpos : 0 < Vv := by rw [hVv]; exact hspos
  have hVne : Vv ≠ 0 := hVpos.ne'
  have h := two_mul_setIntegral_le_setIntegral_sq_add hgi hg2 hsfin (t := Jv / Vv)
  rw [← hJv, ← hIv, ← hVv] at h
  have hexp : (Jv / Vv) ^ 2 * Vv = Jv ^ 2 / Vv := by
    field_simp
    try ring
  have h2 : 2 * (Jv / Vv) * Jv = 2 * (Jv ^ 2 / Vv) := by
    field_simp
    try ring
  rw [hexp, h2] at h
  have h3 : Jv ^ 2 / Vv ≤ Iv := by linarith
  rw [div_le_iff₀ hVpos] at h3
  rw [← hJv, ← hIv, ← hVv]
  linarith [h3, mul_comm Iv Vv]

/-! ### The antisymmetric part of a constant matrix -/

/-- Differentiating the scalar field `z ↦ ∂_w ψ z` in the direction `v` gives the second
derivative `D²ψ(y)(v, w)`: this is `fderiv_clm_apply` with a *constant* second factor. -/
theorem fderiv_fderiv_apply_const {ψ : Euc d → ℝ} (hψ : Differentiable ℝ (fderiv ℝ ψ))
    (w v y : Euc d) :
    fderiv ℝ (fun z : Euc d => fderiv ℝ ψ z w) y v = fderiv ℝ (fderiv ℝ ψ) y v w := by
  have hcd : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) y) y := (hψ y).hasFDerivAt
  have happ : HasFDerivAt (fun z : Euc d => fderiv ℝ ψ z w)
      ((fderiv ℝ ψ y).comp (0 : Euc d →L[ℝ] Euc d) +
        (fderiv ℝ (fderiv ℝ ψ) y).flip w) y := hcd.clm_apply (hasFDerivAt_const w y)
  rw [happ.fderiv]
  simp

/-- **Symmetry of the mixed integrals** `∫ (∂_v u)(∂_w ψ) = ∫ (∂_w u)(∂_v ψ)` for `u ∈ C¹` and
`ψ` smooth with compact support.  One integration by parts
(`integral_mul_fderiv_eq_neg_of_contDiffOn`, against the test function `z ↦ ∂_w ψ z`) turns the
left side into `-∫ u D²ψ(·)(v, w)`, and the right side into `-∫ u D²ψ(·)(w, v)`; the two agree by
the symmetry of the second derivative of the smooth function `ψ`
(`second_derivative_symmetric`).  Only `ψ` is differentiated twice, so `u ∈ C¹` suffices. -/
theorem integral_fderiv_mul_fderiv_comm {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (e f : Euc d) :
    ∫ y, fderiv ℝ u y e * fderiv ℝ ψ y f = ∫ y, fderiv ℝ u y f * fderiv ℝ ψ y e := by
  have hψd : Differentiable ℝ ψ := (contDiff_infty_iff_fderiv.1 hψ).1
  have hψD : ContDiff ℝ ∞ (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψ).2
  have hψDd : Differentiable ℝ (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψD).1
  have key : ∀ v w : Euc d, ∫ y, fderiv ℝ u y v * fderiv ℝ ψ y w
      = -∫ y, u y * fderiv ℝ (fderiv ℝ ψ) y v w := by
    intro v w
    have hc : ContDiff ℝ 1 fun z : Euc d => fderiv ℝ ψ z w :=
      (hψD.clm_apply (contDiff_const (c := w))).of_le (by simp)
    have hcs : HasCompactSupport fun z : Euc d => fderiv ℝ ψ z w := hψs.fderiv_apply ℝ w
    have h : ∫ y, u y * fderiv ℝ (fun z : Euc d => fderiv ℝ ψ z w) y v
        = -∫ y, fderiv ℝ u y v * fderiv ℝ ψ y w :=
      integral_mul_fderiv_eq_neg_of_contDiffOn (U := (Set.univ : Set (Euc d))) isOpen_univ
        hu.contDiffOn hc hcs (subset_univ _) v
    have h2 : ∫ y, u y * fderiv ℝ (fun z : Euc d => fderiv ℝ ψ z w) y v
        = ∫ y, u y * fderiv ℝ (fderiv ℝ ψ) y v w := by
      simp only [fderiv_fderiv_apply_const hψDd w v]
    rw [← h2]
    linarith [h]
  have hsymm : ∀ y : Euc d,
      fderiv ℝ (fderiv ℝ ψ) y e f = fderiv ℝ (fderiv ℝ ψ) y f e := fun y =>
    second_derivative_symmetric (fun z => (hψd z).hasFDerivAt) (hψDd y).hasFDerivAt e f
  rw [key e f, key f e]
  simp only [hsymm]

/-- **The antisymmetric part of a constant coefficient matrix does not contribute to the weak
divergence-form equation**, already for `C¹` functions `u`.

The classical proof is two integrations by parts: for `e, f : ℝ^d`,
`∫ (∂_e u)(∂_f ψ) = -∫ u (∂_e ∂_f ψ) = -∫ u (∂_f ∂_e ψ) = ∫ (∂_f u)(∂_e ψ)`, where only the
*smooth* test function `ψ` is differentiated twice, so that the symmetry of its second derivative
(`ContDiffAt.isSymmSndFDerivAt`) applies and `u ∈ C¹` suffices.  Expanding
`⟪N g, h⟫ = ∑_{i,j} ⟪N b_j, b_i⟫ ⟪g, b_j⟫ ⟪h, b_i⟫` in the standard orthonormal basis and using
`⟪N b_j, b_i⟫ = -⟪N b_i, b_j⟫` then gives `∫ ⟪N ∇u, ∇ψ⟫ = -∫ ⟪N ∇u, ∇ψ⟫`. -/
theorem integral_inner_antisymm_gradient_eq_zero {N : Euc d →L[ℝ] Euc d}
    (hN : ∀ p q : Euc d, ⟪N p, q⟫ = -⟪p, N q⟫) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) :
    ∫ y, ⟪N (gradient u y), gradient ψ y⟫ = 0 := by
  obtain ⟨b, -⟩ : ∃ b : OrthonormalBasis (Fin d) ℝ (Euc d), True :=
    ⟨EuclideanSpace.basisFun (Fin d) ℝ, trivial⟩
  have hψDc : Continuous (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψ).2.continuous
  -- every product of a directional derivative of `u` with one of `ψ` is integrable
  have hint : ∀ v w : Euc d,
      Integrable (fun y : Euc d => fderiv ℝ u y v * fderiv ℝ ψ y w) volume := by
    intro v w
    refine Continuous.integrable_of_hasCompactSupport ?_ (hψs.fderiv_apply ℝ w).mul_left
    exact ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      (hψDc.clm_apply continuous_const)
  -- expand `⟪N ∇u, ∇ψ⟫` in the orthonormal basis, moving `N` onto the basis vector
  have hexp1 : ∀ y : Euc d, -⟪N (gradient u y), gradient ψ y⟫
      = ∑ i : Fin d, fderiv ℝ u y (N (b i)) * fderiv ℝ ψ y (b i) := by
    intro y
    rw [← b.sum_inner_mul_inner (N (gradient u y)) (gradient ψ y), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hN (gradient u y) (b i), real_inner_comm (gradient ψ y) (b i),
      fderiv_apply_eq_inner_gradient u y (N (b i)), fderiv_apply_eq_inner_gradient ψ y (b i)]
    ring
  -- the same expansion after moving `N` onto `∇ψ` instead: the two signs differ
  have hexp2 : ∀ y : Euc d, ⟪N (gradient u y), gradient ψ y⟫
      = ∑ i : Fin d, fderiv ℝ u y (b i) * fderiv ℝ ψ y (N (b i)) := by
    intro y
    have hswap : ⟪N (gradient u y), gradient ψ y⟫ = -⟪N (gradient ψ y), gradient u y⟫ := by
      rw [hN (gradient ψ y) (gradient u y), neg_neg]
      exact real_inner_comm (gradient ψ y) (N (gradient u y))
    rw [hswap, ← b.sum_inner_mul_inner (N (gradient ψ y)) (gradient u y),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hN (gradient ψ y) (b i), real_inner_comm (gradient u y) (b i),
      fderiv_apply_eq_inner_gradient u y (b i), fderiv_apply_eq_inner_gradient ψ y (N (b i))]
    ring
  have hJ1 : (∫ y, ⟪N (gradient u y), gradient ψ y⟫)
      = ∑ i : Fin d, ∫ y, fderiv ℝ u y (b i) * fderiv ℝ ψ y (N (b i)) := by
    simp only [hexp2]
    exact integral_finsetSum Finset.univ fun i _ => hint (b i) (N (b i))
  have hJ2 : -(∫ y, ⟪N (gradient u y), gradient ψ y⟫)
      = ∑ i : Fin d, ∫ y, fderiv ℝ u y (N (b i)) * fderiv ℝ ψ y (b i) := by
    have hneg : -(∫ y, ⟪N (gradient u y), gradient ψ y⟫)
        = ∫ y, -⟪N (gradient u y), gradient ψ y⟫ :=
      (integral_neg fun y : Euc d => ⟪N (gradient u y), gradient ψ y⟫).symm
    rw [hneg]
    simp only [hexp1]
    exact integral_finsetSum Finset.univ fun i _ => hint (N (b i)) (b i)
  -- the two sums agree term by term, by the symmetry of the mixed integrals
  have hsum : ∑ i : Fin d, ∫ y, fderiv ℝ u y (N (b i)) * fderiv ℝ ψ y (b i)
      = ∑ i : Fin d, ∫ y, fderiv ℝ u y (b i) * fderiv ℝ ψ y (N (b i)) :=
    Finset.sum_congr rfl fun i _ =>
      integral_fderiv_mul_fderiv_comm hu hψ hψs (N (b i)) (b i)
  linarith [hJ1, hJ2, hsum]

/-! ### Reduction to a symmetric coefficient matrix -/

/-- The symmetric part `(A + Aᵀ)/2` of a constant coefficient matrix. -/
noncomputable def symPart (A : Euc d →L[ℝ] Euc d) : Euc d →L[ℝ] Euc d :=
  (1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A)

/-- The antisymmetric part `(A - Aᵀ)/2` of a constant coefficient matrix. -/
noncomputable def antisymPart (A : Euc d →L[ℝ] Euc d) : Euc d →L[ℝ] Euc d :=
  (1 / 2 : ℝ) • (A - ContinuousLinearMap.adjoint A)

theorem half_add_half_sub (a b : Euc d) :
    (1 / 2 : ℝ) • (a + b) + (1 / 2 : ℝ) • (a - b) = a := by
  rw [smul_add, smul_sub,
    show (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b + ((1 / 2 : ℝ) • a - (1 / 2 : ℝ) • b) =
      (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • a from by abel, ← add_smul]
  norm_num

theorem symPart_add_antisymPart (A : Euc d →L[ℝ] Euc d) (v : Euc d) :
    symPart A v + antisymPart A v = A v := by
  show (1 / 2 : ℝ) • (A v + (ContinuousLinearMap.adjoint A) v) +
    (1 / 2 : ℝ) • (A v - (ContinuousLinearMap.adjoint A) v) = A v
  exact half_add_half_sub (A v) ((ContinuousLinearMap.adjoint A) v)

theorem symPart_symm (A : Euc d →L[ℝ] Euc d) (p q : Euc d) :
    ⟪symPart A p, q⟫ = ⟪p, symPart A q⟫ := by
  show ⟪(1 / 2 : ℝ) • (A p + (ContinuousLinearMap.adjoint A) p), q⟫ =
    ⟪p, (1 / 2 : ℝ) • (A q + (ContinuousLinearMap.adjoint A) q)⟫
  rw [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    ContinuousLinearMap.adjoint_inner_left A q p, ContinuousLinearMap.adjoint_inner_right A p q]
  ring

theorem antisymPart_antisymm (A : Euc d →L[ℝ] Euc d) (p q : Euc d) :
    ⟪antisymPart A p, q⟫ = -⟪p, antisymPart A q⟫ := by
  show ⟪(1 / 2 : ℝ) • (A p - (ContinuousLinearMap.adjoint A) p), q⟫ =
    -⟪p, (1 / 2 : ℝ) • (A q - (ContinuousLinearMap.adjoint A) q)⟫
  rw [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_left A q p, ContinuousLinearMap.adjoint_inner_right A p q]
  ring

theorem symPart_inner_self (A : Euc d →L[ℝ] Euc d) (ζ : Euc d) :
    ⟪symPart A ζ, ζ⟫ = ⟪A ζ, ζ⟫ := by
  show ⟪(1 / 2 : ℝ) • (A ζ + (ContinuousLinearMap.adjoint A) ζ), ζ⟫ = ⟪A ζ, ζ⟫
  rw [real_inner_smul_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left A ζ ζ,
    real_inner_comm (A ζ) ζ]
  ring

theorem norm_adjoint_apply_le (A : Euc d →L[ℝ] Euc d) (w : Euc d) :
    ‖(ContinuousLinearMap.adjoint A) w‖ ≤ ‖A‖ * ‖w‖ := by
  obtain ⟨v, hv⟩ : ∃ v : Euc d, v = (ContinuousLinearMap.adjoint A) w := ⟨_, rfl⟩
  have h1 : ‖v‖ ^ 2 = ⟪w, A v⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hv]
    exact ContinuousLinearMap.adjoint_inner_left A v w
  have h2 : ⟪w, A v⟫ ≤ ‖w‖ * ‖A v‖ := (le_abs_self _).trans (abs_real_inner_le_norm w (A v))
  have h3 : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  have h4 : ‖v‖ ^ 2 ≤ ‖w‖ * (‖A‖ * ‖v‖) := by
    refine h1.le.trans (h2.trans ?_)
    exact mul_le_mul_of_nonneg_left h3 (norm_nonneg w)
  rw [← hv]
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

theorem norm_symPart_le (A : Euc d →L[ℝ] Euc d) : ‖symPart A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun w => ?_
  have hval : symPart A w = (1 / 2 : ℝ) • (A w + (ContinuousLinearMap.adjoint A) w) := rfl
  rw [hval, norm_smul, Real.norm_eq_abs]
  have h1 : ‖A w + (ContinuousLinearMap.adjoint A) w‖ ≤ ‖A‖ * ‖w‖ + ‖A‖ * ‖w‖ :=
    (norm_add_le _ _).trans (add_le_add (A.le_opNorm w) (norm_adjoint_apply_le A w))
  have h2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [h2]
  linarith

theorem integrable_inner_clm_gradient (T : Euc d →L[ℝ] Euc d) {u : Euc d → ℝ}
    (hu : ContDiff ℝ 1 u) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ) :
    Integrable fun y : Euc d => ⟪T (gradient u y), gradient ψ y⟫ := by
  refine Continuous.integrable_of_hasCompactSupport
    ((T.continuous.comp (continuous_gradient hu)).inner (continuous_gradient hψ)) ?_
  refine HasCompactSupport.intro (hasCompactSupport_gradient hψs) fun y hy => ?_
  rw [image_eq_zero_of_notMem_tsupport hy, inner_zero_right]

/-- **The weak equation only sees the symmetric part of a constant coefficient matrix.** -/
theorem integral_inner_symPart_eq (A : Euc d →L[ℝ] Euc d) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) :
    ∫ y, ⟪symPart A (gradient u y), gradient ψ y⟫ =
      ∫ y, ⟪A (gradient u y), gradient ψ y⟫ := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hsplit : ∀ y : Euc d, ⟪A (gradient u y), gradient ψ y⟫ =
      ⟪symPart A (gradient u y), gradient ψ y⟫ +
        ⟪antisymPart A (gradient u y), gradient ψ y⟫ := by
    intro y
    rw [← inner_add_left, symPart_add_antisymPart]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add (integrable_inner_clm_gradient (symPart A) hu hψ1 hψs)
      (integrable_inner_clm_gradient (antisymPart A) hu hψ1 hψs),
    integral_inner_antisymm_gradient_eq_zero (antisymPart_antisymm A) hu hψ hψs, add_zero]

/-! ### The interior derivative estimate, assembled -/

/-- **The `ℝ^d` interior derivative estimate for a constant elliptic operator**, in the form used
by the Campanato/Schauder iteration: `∇h` is Lipschitz on the half ball with a constant `K`
obeying the scale-invariant bound `K² r^{d+2} ≤ C ∫_{B(x,r)} ‖∇h - (∇h)_r‖²`, with
`C = C(d, μ, Λ)`.

The proof: replace `A₀` by its symmetric part (`integral_inner_symPart_eq`), invert it
(`exists_inverse_of_symmetric_elliptic`), cut `h` off to a globally `C¹` compactly supported `u`,
and apply `abs_integral_mvpKernel_mul_norm_gradient_sub_le` at the scale `s = r/(2 ρ₀)`; the
resulting `L¹` quantity is converted to the `L²` excess by `sq_setIntegral_le_mul`. -/
theorem exists_constCoeff_gradient_lipschitz_aux (d : ℕ) {μ Λ : ℝ} (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A₀ : Euc d →L[ℝ] Euc d) (h : Euc d → ℝ) (x : Euc d) (r : ℝ), 0 < r →
        (∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) → ‖A₀‖ ≤ Λ →
        ContDiffOn ℝ 1 h (Metric.ball x (2 * r)) →
        (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ Metric.ball x (2 * r) → ∫ y, ⟪A₀ (gradient h y), gradient ψ y⟫ = 0) →
        ∃ K : ℝ, 0 ≤ K ∧
          K ^ 2 * (r ^ d * r ^ 2) ≤ C *
            ∫ y in Metric.closedBall x r,
              ‖gradient h y - ⨍ z in Metric.closedBall x r, gradient h z‖ ^ 2 ∧
          ∀ y ∈ Metric.closedBall x (r / 2), ∀ z ∈ Metric.closedBall x (r / 2),
            ‖gradient h y - gradient h z‖ ≤ K * dist y z := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hnorm0 : ∀ v : Euc 0, ‖v‖ = 0 := by
      intro v
      rw [EuclideanSpace.norm_eq]
      simp
    refine ⟨0, le_rfl, ?_⟩
    intro A₀ h x r _ _ _ _ _
    refine ⟨0, le_rfl, by simp, fun y _ z _ => ?_⟩
    rw [hnorm0 (gradient h y - gradient h z), zero_mul]
  -- the constants
  obtain ⟨Λ', hΛ'def⟩ : ∃ Λ' : ℝ, Λ' = max Λ 1 := ⟨_, rfl⟩
  have hΛ'1 : (1 : ℝ) ≤ Λ' := by rw [hΛ'def]; exact le_max_right _ _
  have hΛ'0 : (0 : ℝ) < Λ' := lt_of_lt_of_le one_pos hΛ'1
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = μ / (Λ' + 1) ^ 2 := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; exact div_pos hμ (pow_pos (by linarith) 2)
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 1 / μ := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; exact one_div_pos.2 hμ
  have hρ0 : 0 < mvpRadius α := mvpRadius_pos hα
  obtain ⟨e, hedef⟩ : ∃ w : Euc d, w = EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) := ⟨_, rfl⟩
  have he : e ≠ 0 := by
    rw [hedef]
    intro hcon
    have h1 : (1 : ℝ) = 0 := EuclideanSpace.single_eq_zero_iff.1 hcon
    norm_num at h1
  obtain ⟨κ, hκ0, hκ⟩ := exists_integral_mvpKernel_le_neg d hα hβ he
  obtain ⟨M, hM0, hM⟩ := exists_bound_mvpProfile''
  obtain ⟨Lc, hLcdef⟩ : ∃ L : ℝ, L = 4 * M * β * mvpRadius α := ⟨_, rfl⟩
  have hLc0 : 0 ≤ Lc := by
    rw [hLcdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hβ.le) hρ0.le
  obtain ⟨Dc, hDcdef⟩ : ∃ D : ℝ, D = Lc * (2 * mvpRadius α) ^ (d + 1) / κ := ⟨_, rfl⟩
  have hDc0 : 0 ≤ Dc := by
    rw [hDcdef]
    exact div_nonneg (mul_nonneg hLc0 (pow_nonneg (mul_pos two_pos hρ0).le _)) hκ0.le
  refine ⟨Dc ^ 2 * volume.real (Metric.closedBall (0 : Euc d) 1),
    mul_nonneg (sq_nonneg _) volume_real_closedBall_pos.le, ?_⟩
  intro A₀ h x r hr hell hbdd hh hsol
  have hrne : r ≠ 0 := hr.ne'
  -- the symmetric part of `A₀` and its inverse
  obtain ⟨A, hAdef⟩ : ∃ T : Euc d →L[ℝ] Euc d, T = symPart A₀ := ⟨_, rfl⟩
  have hAsymm : ∀ p q : Euc d, ⟪A p, q⟫ = ⟪p, A q⟫ := by
    rw [hAdef]; exact symPart_symm A₀
  have hAell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A ζ, ζ⟫ := by
    intro ζ
    rw [hAdef, symPart_inner_self]
    exact hell ζ
  have hAnorm : ‖A‖ ≤ Λ' := by
    rw [hAdef]
    refine (norm_symPart_le A₀).trans ?_
    rw [hΛ'def]
    exact hbdd.trans (le_max_left _ _)
  obtain ⟨S, hSsymm, hSA, hSn, hQ0⟩ := exists_inverse_of_symmetric_elliptic hμ A hAsymm hAell
  have hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w := by
    intro w
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) (hQ0 w)
    rw [hαdef, div_le_div_iff₀ (pow_pos (by linarith) 2) (by positivity)]
    have hA0 : (0 : ℝ) ≤ ‖A‖ + 1 := by positivity
    have hAle : ‖A‖ + 1 ≤ Λ' + 1 := by linarith
    have hsq : (‖A‖ + 1) ^ 2 ≤ (Λ' + 1) ^ 2 := pow_le_pow_left₀ hA0 hAle 2
    exact mul_le_mul_of_nonneg_left hsq hμ.le
  have hSn' : ‖S‖ ≤ β := by rw [hβdef]; exact hSn
  -- the cutoff and the globally `C¹` function `u`
  obtain ⟨Cη, hCη0, hcut⟩ := exists_uniform_cutoff (d := d) (a := 7 * r / 4) (b := 15 * r / 8)
    (by linarith) (by linarith)
  obtain ⟨η, hηsmooth, hηnn, hηle, hηone, hηsupp, hηgrad⟩ := hcut x
  obtain ⟨u, hudef⟩ : ∃ f : Euc d → ℝ, f = fun y => η y * h y := ⟨_, rfl⟩
  have hsub1 : Metric.closedBall x (15 * r / 8) ⊆ Metric.ball x (2 * r) := by
    intro y hy
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    linarith
  have husupp : tsupport u ⊆ Metric.closedBall x (15 * r / 8) := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro y hy
    have hy' : η y * h y ≠ 0 := by rw [hudef] at hy; exact hy
    have hy2 : η y ≠ 0 := fun hc => hy' (by rw [hc, zero_mul])
    exact hηsupp (subset_tsupport η hy2)
  have hucd : ContDiffOn ℝ 1 u (Metric.ball x (2 * r)) := by
    rw [hudef]
    exact ((hηsmooth.of_le (by simp)).contDiffOn).mul hh
  have hu : ContDiff ℝ 1 u :=
    contDiff_one_of_contDiffOn Metric.isOpen_ball Metric.isClosed_closedBall hsub1 hucd husupp
  have hus : HasCompactSupport u :=
    HasCompactSupport.intro (isCompact_closedBall x (15 * r / 8)) fun y hy => by
      by_contra hne
      exact hy (husupp (subset_tsupport u hne))
  have hgrad_eq : ∀ y ∈ Metric.ball x (7 * r / 4), gradient u y = gradient h y := by
    intro y hy
    have heq : u =ᶠ[𝓝 y] h := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
      have h1 : η z = 1 :=
        hηone z (Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hz)))
      rw [hudef]
      show η z * h z = h z
      rw [h1, one_mul]
    have hfd : fderiv ℝ u y = fderiv ℝ h y := heq.fderiv_eq
    refine ext_inner_right ℝ fun v => ?_
    rw [← fderiv_apply_eq_inner_gradient, ← fderiv_apply_eq_inner_gradient, hfd]
  -- the weak equation for `u` with the symmetric matrix `A`
  have hsolu : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball x (7 * r / 4) →
      ∫ y, ⟪A (gradient u y), gradient ψ y⟫ = 0 := by
    intro ψ hψ hψs hψV
    have hsub2 : Metric.ball x (7 * r / 4) ⊆ Metric.ball x (2 * r) :=
      Metric.ball_subset_ball (by linarith)
    have h1 : ∫ y, ⟪A (gradient u y), gradient ψ y⟫ =
        ∫ y, ⟪A₀ (gradient u y), gradient ψ y⟫ := by
      rw [hAdef]
      exact integral_inner_symPart_eq A₀ hu hψ hψs
    have hpt : ∀ y : Euc d, ⟪A₀ (gradient u y), gradient ψ y⟫ =
        ⟪A₀ (gradient h y), gradient ψ y⟫ := by
      intro y
      by_cases hy : y ∈ Metric.ball x (7 * r / 4)
      · rw [hgrad_eq y hy]
      · have hyψ : y ∉ tsupport ψ := fun hc => hy (hψV hc)
        rw [gradient_eq_zero_of_notMem_tsupport hyψ, inner_zero_right, inner_zero_right]
    rw [h1, integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact hsol ψ hψ hψs (hψV.trans hsub2)
  -- the scale
  obtain ⟨s, hsdef⟩ : ∃ t : ℝ, t = r / (2 * mvpRadius α) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; exact div_pos hr (mul_pos two_pos hρ0)
  have hsr : s * mvpRadius α = r / 2 := by
    have h2ρ : (0 : ℝ) < 2 * mvpRadius α := mul_pos two_pos hρ0
    rw [hsdef, div_mul_eq_mul_div, div_eq_div_iff h2ρ.ne' (two_ne_zero)]
    ring
  have hcover : ∀ z ∈ Metric.closedBall x (r / 2),
      Metric.closedBall z (s * mvpRadius α + r / 2) ⊆ Metric.ball x (7 * r / 4) := by
    intro z hz y hy
    rw [Metric.mem_closedBall] at hz hy
    rw [hsr] at hy
    rw [Metric.mem_ball]
    have htri := dist_triangle y z x
    linarith
  have hLip : ∀ a b : Euc d, |mvpKernel S a - mvpKernel S b| ≤ Lc * ‖a - b‖ := by
    intro a b
    rw [hLcdef]
    exact abs_mvpKernel_sub_le hα hβ.le hM0 hSsymm hQ hSn' hM a b
  -- the excess quantities
  obtain ⟨v₀, hv₀def⟩ : ∃ v : Euc d, v = ⨍ z in Metric.closedBall x r, gradient h z := ⟨_, rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ t : ℝ, t = ∫ y in Metric.closedBall x r, ‖gradient h y - v₀‖ :=
    ⟨_, rfl⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ t : ℝ, t = ∫ y in Metric.closedBall x r, ‖gradient h y - v₀‖ ^ 2 :=
    ⟨_, rfl⟩
  have hJ0 : 0 ≤ J := by
    rw [hJdef]
    exact setIntegral_nonneg measurableSet_closedBall fun y _ => norm_nonneg _
  have hJu : (∫ y in Metric.closedBall x r, ‖gradient u y - v₀‖) = J := by
    rw [hJdef]
    refine setIntegral_congr_fun measurableSet_closedBall fun y hy => ?_
    have hy' : y ∈ Metric.ball x (7 * r / 4) := by
      rw [Metric.mem_ball]
      have h1 := Metric.mem_closedBall.1 hy
      linarith
    rw [hgrad_eq y hy']
  have hGc : ContinuousOn (fun y : Euc d => ‖gradient h y - v₀‖) (Metric.closedBall x r) := by
    -- `ContinuousOn.congr` constrains only `g`, so the `v₀` inside `continuous_const` is
    -- otherwise undetermined; pin the whole term with an explicit type ascription.
    have hcont : Continuous (fun y : Euc d => ‖gradient u y - v₀‖) :=
      ((continuous_gradient hu).sub continuous_const).norm
    refine ContinuousOn.congr hcont.continuousOn fun y hy => ?_
    have hy' : y ∈ Metric.ball x (7 * r / 4) := by
      rw [Metric.mem_ball]
      have h1 := Metric.mem_closedBall.1 hy
      linarith
    rw [hgrad_eq y hy']
  have hcpt : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  have hgi : IntegrableOn (fun y : Euc d => ‖gradient h y - v₀‖) (Metric.closedBall x r) :=
    hGc.integrableOn_compact hcpt
  have hg2 : IntegrableOn (fun y : Euc d => ‖gradient h y - v₀‖ ^ 2) (Metric.closedBall x r) :=
    (hGc.pow 2).integrableOn_compact hcpt
  have hvolpos : 0 < volume.real (Metric.closedBall x r) := volume_real_closedBall_pos' x hr
  have hJsq : J ^ 2 ≤ volume.real (Metric.closedBall (0 : Euc d) 1) * r ^ d * Φ := by
    have h1 := sq_setIntegral_le_mul hgi hg2 measure_closedBall_lt_top.ne hvolpos
    rw [← hJdef, ← hΦdef, volume_real_closedBall x hr.le] at h1
    calc J ^ 2 ≤ r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) * Φ := h1
      _ = volume.real (Metric.closedBall (0 : Euc d) 1) * r ^ d * Φ := by ring
  have hmain : ∀ y ∈ Metric.closedBall x (r / 2), ∀ z ∈ Metric.closedBall x (r / 2),
      |∫ w, mvpKernel S w| * ‖gradient u y - gradient u z‖ ≤
        Lc / s ^ (d + 1) * J * ‖y - z‖ := by
    intro y hy z hz
    have h1 := abs_integral_mvpKernel_mul_norm_gradient_sub_le hSsymm hSA hα hQ hu hus hsolu
      hLc0 hLip hr hs (by linarith : (0 : ℝ) < r / 2) (le_of_eq hsr) hcover v₀ hy hz
    rwa [hJu] at h1
  have hcneg : ∫ w, mvpKernel S w ≤ -κ := hκ S hSsymm hQ hSn'
  have hcle0 : ∫ w, mvpKernel S w ≤ 0 := by linarith
  have hcabs : κ ≤ |∫ w, mvpKernel S w| := by
    rw [abs_of_nonpos hcle0]
    linarith
  have hκne : κ ≠ 0 := hκ0.ne'
  have hρne : mvpRadius α ≠ 0 := hρ0.ne'
  refine ⟨Dc * J / r ^ (d + 1), div_nonneg (mul_nonneg hDc0 hJ0) (pow_nonneg hr.le _), ?_, ?_⟩
  · have hkey : (Dc * J / r ^ (d + 1)) ^ 2 * (r ^ d * r ^ 2) = Dc ^ 2 * J ^ 2 / r ^ d := by
      field_simp
      ring
    rw [hkey, ← hv₀def, ← hΦdef, div_le_iff₀ (pow_pos hr d)]
    calc Dc ^ 2 * J ^ 2
        ≤ Dc ^ 2 * (volume.real (Metric.closedBall (0 : Euc d) 1) * r ^ d * Φ) :=
          mul_le_mul_of_nonneg_left hJsq (sq_nonneg Dc)
      _ = Dc ^ 2 * volume.real (Metric.closedBall (0 : Euc d) 1) * Φ * r ^ d := by ring
  · intro y hy z hz
    have hy' : y ∈ Metric.ball x (7 * r / 4) := by
      rw [Metric.mem_ball]
      have h1 := Metric.mem_closedBall.1 hy
      linarith
    have hz' : z ∈ Metric.ball x (7 * r / 4) := by
      rw [Metric.mem_ball]
      have h1 := Metric.mem_closedBall.1 hz
      linarith
    have h1 := hmain y hy z hz
    rw [hgrad_eq y hy', hgrad_eq z hz'] at h1
    have h2 : κ * ‖gradient h y - gradient h z‖ ≤ Lc / s ^ (d + 1) * J * ‖y - z‖ :=
      le_trans (mul_le_mul_of_nonneg_right hcabs (norm_nonneg _)) h1
    have h2ρne : ((2 : ℝ) * mvpRadius α) ≠ 0 := (mul_pos two_pos hρ0).ne'
    have hLs : Lc / s ^ (d + 1) = Dc * κ / r ^ (d + 1) := by
      rw [hDcdef, hsdef, div_pow]
      field_simp
      try ring
    rw [hLs] at h2
    rw [dist_eq_norm]
    have h3 : κ * ‖gradient h y - gradient h z‖ ≤ κ * (Dc * J / r ^ (d + 1) * ‖y - z‖) := by
      refine h2.trans_eq ?_
      ring
    exact le_of_mul_le_mul_left h3 hκ0

end Komlos.Literature
