import Komlos.Literature.Regularized.Interface

/-!
# The smoothed profile `Ψ = (F^p/p) ∗ ρ`

The regularized route of `REGULARIZED_ROUTE.md` replaces the degenerate kinetic profile
`F^p/p` by its mollification `Ψ = Korevaar.smoothedProfile p F ρ`.  This file collects the
facts about `Ψ` that the other lanes use.  Everything is stated for a mollifier
`IsMollifier ρ ε` and a smooth strictly convex norm `F` (`IsSmoothStrictNorm`).

## Main results

* `le_smoothedProfile`: `F(q)^p/p ≤ Ψ(q)`.  This is Jensen's inequality for the even
  probability kernel `ρ`, proved here in the symmetric form
  `Ψ(q) = ½ ∫ ρ(y) (Φ(q-y) + Φ(q+y)) dy ≥ ∫ ρ(y) Φ(q) dy = Φ(q)`,
  which needs only midpoint convexity of `Φ = F^p/p` and no differentiability at `0`.
* `exists_smoothedProfile_le`: `Ψ(q) ≤ (F(q) + M ε)^p/p` with `M` depending only on `F`
  (triangle inequality for `F` plus `F ≤ M ‖·‖` on the support of `ρ`).
* `contDiff_smoothedProfile'`, `convexOn_smoothedProfile'`, `smoothedProfile_even'`,
  `differentiable_smoothedProfile`, `hasGradientAt_smoothedProfile`,
  `gradient_smoothedProfile_neg`: smoothness, convexity, evenness, and oddness of
  `gradient Ψ` (wrappers around `Komlos/Literature/PLaplacian/KorevaarSmoothedProfile.lean`).
* `exists_norm_gradient_smoothedProfile_le`: `‖∇Ψ(q)‖ ≤ C (‖q‖ + ε)^{p-1}`.  The proof is
  purely convex-analytic — `norm_gradient_le_of_convexOn` bounds the gradient of a
  nonnegative convex function by its sup on a ball — so it never differentiates under the
  convolution integral.
* `exists_local_ellipticity_upper`: the local upper bound for `D²Ψ`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Elementary consequences of `IsMollifier` -/

namespace IsMollifier

variable {ρ : Euc d → ℝ} {ε : ℝ}

protected theorem continuous (hρ : IsMollifier ρ ε) : Continuous ρ := hρ.contDiff.continuous

protected theorem hasCompactSupport (hρ : IsMollifier ρ ε) : HasCompactSupport ρ :=
  (isCompact_closedBall (0 : Euc d) ε).of_isClosed_subset (isClosed_tsupport ρ)
    hρ.tsupport_subset

protected theorem integrable (hρ : IsMollifier ρ ε) : Integrable ρ :=
  hρ.continuous.integrable_of_hasCompactSupport hρ.hasCompactSupport

/-- The kernel vanishes outside the ball of radius `ε`. -/
theorem norm_le_of_ne_zero (hρ : IsMollifier ρ ε) {y : Euc d} (hy : ρ y ≠ 0) : ‖y‖ ≤ ε := by
  have hmem : y ∈ tsupport ρ := subset_tsupport ρ (Function.mem_support.2 hy)
  simpa [mem_closedBall_zero_iff] using hρ.tsupport_subset hmem

end IsMollifier

/-! ### Smoothness, convexity, evenness -/

section Wrappers

variable {p ε : ℝ} {F ρ : Euc d → ℝ}

/-- The mollified profile is `C^∞` everywhere, including at the origin. -/
theorem contDiff_smoothedProfile' (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) : ContDiff ℝ ∞ (Korevaar.smoothedProfile p F ρ) :=
  Korevaar.contDiff_smoothedProfile (by linarith) hF hρ.contDiff hρ.hasCompactSupport

/-- The mollified profile is convex. -/
theorem convexOn_smoothedProfile' (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) : ConvexOn ℝ univ (Korevaar.smoothedProfile p F ρ) :=
  Korevaar.convexOn_smoothedProfile hp hF hρ.continuous hρ.hasCompactSupport hρ.nonneg

/-- The mollified profile is even (the kernel is even and `F` is even). -/
theorem smoothedProfile_even' (p : ℝ) (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε)
    (q : Euc d) :
    Korevaar.smoothedProfile p F ρ (-q) = Korevaar.smoothedProfile p F ρ q :=
  Korevaar.smoothedProfile_even p hF hρ.even q

/-- The mollified profile is differentiable. -/
theorem differentiable_smoothedProfile (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) : Differentiable ℝ (Korevaar.smoothedProfile p F ρ) :=
  (contDiff_smoothedProfile' hp hF hρ).differentiable (by simp)

/-- The gradient of the mollified profile is its actual gradient. -/
theorem hasGradientAt_smoothedProfile (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) (q : Euc d) :
    HasGradientAt (Korevaar.smoothedProfile p F ρ)
      (gradient (Korevaar.smoothedProfile p F ρ) q) q :=
  (differentiable_smoothedProfile hp hF hρ q).hasGradientAt

/-- The gradient of the mollified profile is odd. -/
theorem gradient_smoothedProfile_neg (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) (q : Euc d) :
    gradient (Korevaar.smoothedProfile p F ρ) (-q) =
      -gradient (Korevaar.smoothedProfile p F ρ) q :=
  Korevaar.gradient_odd_of_even (differentiable_smoothedProfile hp hF hρ)
    (smoothedProfile_even' p hF hρ) q

/-- The convolution written with the kernel at the integration variable. -/
theorem smoothedProfile_eq_integral (p : ℝ) (F ρ : Euc d → ℝ) (q : Euc d) :
    Korevaar.smoothedProfile p F ρ q = ∫ y, ρ y * (F (q - y) ^ p / p) :=
  Korevaar.mollifyWith_eq_kernel_integral ρ (fun z => F z ^ p / p) q

end Wrappers

/-! ### The two-sided comparison `F^p/p ≤ Ψ ≤ (F + Mε)^p/p` -/

section Comparison

variable {p ε : ℝ} {F ρ : Euc d → ℝ}

/-- **Jensen's inequality for the smoothed profile**: `F(q)^p/p ≤ Ψ(q)`.

The kernel is an even probability density, so the mollification of a convex `Φ` at `q` is the
average of the midpoint averages `(Φ(q-y) + Φ(q+y))/2 ≥ Φ(q)`.  This form of Jensen needs no
differentiability of `Φ` (in particular none at the origin). -/
theorem le_smoothedProfile (hp : 1 < p) (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε)
    (q : Euc d) : F q ^ p / p ≤ Korevaar.smoothedProfile p F ρ q := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hΦc : Continuous fun z : Euc d => F z ^ p / p := (hF.continuous_rpow hp0.le).div_const p
  have hi1 : Integrable fun y : Euc d => ρ y * (F (q - y) ^ p / p) :=
    (hρ.continuous.mul
      (hΦc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρ.hasCompactSupport.mul_right
  have hi2 : Integrable fun y : Euc d => ρ y * (F (q + y) ^ p / p) :=
    (hρ.continuous.mul
      (hΦc.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
      hρ.hasCompactSupport.mul_right
  have hi0 : Integrable fun y : Euc d => ρ y * (2 * (F q ^ p / p)) := hρ.integrable.mul_const _
  -- The reflected and the direct half-integral agree, because `ρ` is even.
  have hJI : (∫ y, ρ y * (F (q + y) ^ p / p)) = ∫ y, ρ y * (F (q - y) ^ p / p) := by
    calc (∫ y, ρ y * (F (q + y) ^ p / p))
        = ∫ y, ρ (-y) * (F (q + -y) ^ p / p) :=
          (integral_neg_eq_self (fun y : Euc d => ρ y * (F (q + y) ^ p / p)) volume).symm
      _ = ∫ y, ρ y * (F (q - y) ^ p / p) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          show ρ (-y) * (F (q + -y) ^ p / p) = ρ y * (F (q - y) ^ p / p)
          rw [hρ.even, ← sub_eq_add_neg]
  -- Midpoint convexity of `F^p/p`, weighted by the kernel.
  have hmid : ∀ y : Euc d, ρ y * (2 * (F q ^ p / p)) ≤
      ρ y * (F (q - y) ^ p / p) + ρ y * (F (q + y) ^ p / p) := by
    intro y
    have hconv := (convexOn_rpow_of_isSmoothStrictNorm hF hp.le).2 (mem_univ (q - y))
      (mem_univ (q + y)) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have heq : (1 / 2 : ℝ) • (q - y) + (1 / 2 : ℝ) • (q + y) = q := by module
    rw [heq] at hconv
    simp only [smul_eq_mul] at hconv
    have hkey := mul_le_mul_of_nonneg_left hconv (le_of_lt (inv_pos.2 hp0))
    have hfin : 2 * (F q ^ p / p) ≤ F (q - y) ^ p / p + F (q + y) ^ p / p := by
      simp only [div_eq_inv_mul]
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hfin (hρ.nonneg y)
    linarith
  have hstep : 2 * (F q ^ p / p) ≤ 2 * ∫ y, ρ y * (F (q - y) ^ p / p) := by
    calc 2 * (F q ^ p / p) = ∫ y, ρ y * (2 * (F q ^ p / p)) := by
          rw [integral_mul_const, hρ.integral_eq_one, one_mul]
      _ ≤ ∫ y, (ρ y * (F (q - y) ^ p / p) + ρ y * (F (q + y) ^ p / p)) :=
          integral_mono hi0 (hi1.add hi2) hmid
      _ = (∫ y, ρ y * (F (q - y) ^ p / p)) + ∫ y, ρ y * (F (q + y) ^ p / p) :=
          integral_add hi1 hi2
      _ = 2 * ∫ y, ρ y * (F (q - y) ^ p / p) := by rw [hJI]; ring
  rw [smoothedProfile_eq_integral]
  linarith

/-- The smoothed profile is nonnegative. -/
theorem smoothedProfile_nonneg (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) (q : Euc d) : 0 ≤ Korevaar.smoothedProfile p F ρ q :=
  le_trans (div_nonneg (Real.rpow_nonneg (hF.nonneg q) p) (by linarith))
    (le_smoothedProfile hp hF hρ q)

/-- **The upper comparison** `Ψ(q) ≤ (F(q) + M ε)^p/p`, with `M ≥ 0` depending only on `F`
(and not on the kernel or its radius): on the support of `ρ` the triangle inequality for `F`
gives `F(q - y) ≤ F(q) + F(y) ≤ F(q) + M ‖y‖ ≤ F(q) + M ε`. -/
theorem exists_smoothedProfile_le {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ρ : Euc d → ℝ) (ε : ℝ), IsMollifier ρ ε →
      ∀ q : Euc d, Korevaar.smoothedProfile p F ρ q ≤ (F q + M * ε) ^ p / p := by
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨M₀, hM₀⟩ := hF.exists_le_mul_norm
  refine ⟨max M₀ 0, le_max_right _ _, fun ρ ε hρ q => ?_⟩
  have hM0 : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have hΦc : Continuous fun z : Euc d => F z ^ p / p := (hF.continuous_rpow hp0.le).div_const p
  have hi1 : Integrable fun y : Euc d => ρ y * (F (q - y) ^ p / p) :=
    (hρ.continuous.mul
      (hΦc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρ.hasCompactSupport.mul_right
  have hi2 : Integrable fun y : Euc d => ρ y * ((F q + max M₀ 0 * ε) ^ p / p) :=
    hρ.integrable.mul_const _
  have hle : ∀ y : Euc d,
      ρ y * (F (q - y) ^ p / p) ≤ ρ y * ((F q + max M₀ 0 * ε) ^ p / p) := by
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
      have h7 : F (q - y) ^ p ≤ (F q + max M₀ 0 * ε) ^ p :=
        Real.rpow_le_rpow (hF.nonneg _) h1 hp0.le
      have h8 : F (q - y) ^ p / p ≤ (F q + max M₀ 0 * ε) ^ p / p := by
        simp only [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left h7 (inv_nonneg.2 hp0.le)
      exact mul_le_mul_of_nonneg_left h8 (hρ.nonneg y)
  rw [smoothedProfile_eq_integral]
  calc (∫ y, ρ y * (F (q - y) ^ p / p))
      ≤ ∫ y, ρ y * ((F q + max M₀ 0 * ε) ^ p / p) := integral_mono hi1 hi2 hle
    _ = (F q + max M₀ 0 * ε) ^ p / p := by
        rw [integral_mul_const, hρ.integral_eq_one, one_mul]

end Comparison

/-! ### Gradient growth -/

section GradientGrowth

/-- **A differentiable convex function lies above its tangent plane.**  Mean value theorem
plus monotonicity of the derivative along the segment. -/
theorem inner_gradient_le_sub_of_convexOn {Ψ : Euc d → ℝ} (hd : Differentiable ℝ Ψ)
    (hconv : ConvexOn ℝ univ Ψ) (q ξ : Euc d) :
    ⟪gradient Ψ q, ξ⟫ ≤ Ψ (q + ξ) - Ψ q := by
  have hf : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Ψ (q + t • ξ))
      (⟪gradient Ψ (q + t • ξ), ξ⟫) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => q + s • ξ) ξ t := by
      simpa using ((hasDerivAt_id t).smul_const ξ).const_add q
    have h := (hasGradientAt_iff_hasFDerivAt.1
      (hd (q + t • ξ)).hasGradientAt).comp_hasDerivAt t hline
    rwa [InnerProductSpace.toDual_apply_apply] at h
  have hfc : ConvexOn ℝ univ fun t : ℝ => Ψ (q + t • ξ) := by
    refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
    have h := hconv.2 (mem_univ (q + s • ξ)) (mem_univ (q + t • ξ)) ha hb hab
    have heq : a • (q + s • ξ) + b • (q + t • ξ) = q + (a * s + b * t) • ξ := by
      have hq : a • q + b • q = q := by rw [← add_smul, hab, one_smul]
      calc a • (q + s • ξ) + b • (q + t • ξ) =
          (a • q + b • q) + (a * s + b * t) • ξ := by module
        _ = q + (a * s + b * t) • ξ := by rw [hq]
    simpa only [smul_eq_mul, heq] using h
  have hderiv : deriv (fun t : ℝ => Ψ (q + t • ξ)) =
      fun t : ℝ => ⟪gradient Ψ (q + t • ξ), ξ⟫ := funext fun t => (hf t).deriv
  have hm := hfc.monotoneOn_deriv fun t _ => (hf t).differentiableAt
  rw [hderiv] at hm
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => Ψ (q + t • ξ))
    (fun t : ℝ => ⟪gradient Ψ (q + t • ξ), ξ⟫) zero_lt_one
    (fun t _ => (hf t).continuousAt.continuousWithinAt) fun t _ => hf t
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hceq
  have h0 := hm (mem_univ (0 : ℝ)) (mem_univ c) hc.1.le
  simp only [zero_smul, add_zero] at h0
  rw [hceq] at h0
  exact h0

/-- **A gradient bound for nonnegative convex functions.**  If `Ψ ≥ 0` is convex and
differentiable and `Ψ ≤ A` on the ball of radius `‖q‖ + r`, then `‖∇Ψ(q)‖ ≤ A / r`: move from
`q` a distance `r` in the direction of the gradient and use the tangent-plane inequality. -/
theorem norm_gradient_le_of_convexOn {Ψ : Euc d → ℝ} (hd : Differentiable ℝ Ψ)
    (hconv : ConvexOn ℝ univ Ψ) (hnn : ∀ z, 0 ≤ Ψ z) {q : Euc d} {r A : ℝ} (hr : 0 < r)
    (hub : ∀ z : Euc d, ‖z‖ ≤ ‖q‖ + r → Ψ z ≤ A) : ‖gradient Ψ q‖ ≤ A / r := by
  have hA : 0 ≤ A := le_trans (hnn q) (hub q (by linarith))
  rcases eq_or_ne (gradient Ψ q) 0 with h0 | h0
  · rw [h0, norm_zero]
    exact div_nonneg hA hr.le
  · have hgn : 0 < ‖gradient Ψ q‖ := norm_pos_iff.2 h0
    have hne : ‖gradient Ψ q‖ ≠ 0 := hgn.ne'
    have hen : ‖(‖gradient Ψ q‖⁻¹ • gradient Ψ q : Euc d)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    have hinner :
        ⟪gradient Ψ q, r • (‖gradient Ψ q‖⁻¹ • gradient Ψ q)⟫ = r * ‖gradient Ψ q‖ := by
      rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
      field_simp
    have htan := inner_gradient_le_sub_of_convexOn hd hconv q
      (r • (‖gradient Ψ q‖⁻¹ • gradient Ψ q))
    rw [hinner] at htan
    have hz : ‖q + r • (‖gradient Ψ q‖⁻¹ • gradient Ψ q)‖ ≤ ‖q‖ + r := by
      calc ‖q + r • (‖gradient Ψ q‖⁻¹ • gradient Ψ q)‖
          ≤ ‖q‖ + ‖r • (‖gradient Ψ q‖⁻¹ • gradient Ψ q)‖ := norm_add_le _ _
        _ = ‖q‖ + r := by rw [norm_smul, hen, mul_one, Real.norm_of_nonneg hr.le]
    have hub' := hub _ hz
    have hq0 := hnn q
    have hfin : r * ‖gradient Ψ q‖ ≤ A := by linarith
    rw [le_div_iff₀ hr]
    linarith

/-- **Gradient growth of the smoothed profile**: `‖∇Ψ(q)‖ ≤ C (‖q‖ + ε)^{p-1}` with `C`
depending only on `p` and `F`.  Apply `norm_gradient_le_of_convexOn` at radius
`r = ‖q‖ + ε`, on which `Ψ ≤ ((2M + M') r)^p/p` by `exists_smoothedProfile_le` and the
linear growth of `F`. -/
theorem exists_norm_gradient_smoothedProfile_le {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Euc d → ℝ) (ε : ℝ), IsMollifier ρ ε → ∀ q : Euc d,
      ‖gradient (Korevaar.smoothedProfile p F ρ) q‖ ≤ C * (‖q‖ + ε) ^ (p - 1) := by
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨M, hM0, hMle⟩ := exists_smoothedProfile_le hp hF
  obtain ⟨M₀, hM₀⟩ := hF.exists_le_mul_norm
  have hN0 : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have hNle : ∀ z : Euc d, F z ≤ max M₀ 0 * ‖z‖ := fun z =>
    (hM₀ z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  have hbase : (0 : ℝ) ≤ 2 * max M₀ 0 + M := by linarith
  refine ⟨(2 * max M₀ 0 + M) ^ p / p,
    div_nonneg (Real.rpow_nonneg hbase p) hp0.le, fun ρ ε hρ q => ?_⟩
  have hrpos : 0 < ‖q‖ + ε := by
    have := hρ.eps_pos
    have := norm_nonneg q
    linarith
  -- the sup of `Ψ` on the relevant ball
  have hub : ∀ z : Euc d, ‖z‖ ≤ ‖q‖ + (‖q‖ + ε) →
      Korevaar.smoothedProfile p F ρ z ≤
        (2 * max M₀ 0 + M) ^ p * (‖q‖ + ε) ^ p / p := by
    intro z hz
    have hz2 : ‖z‖ ≤ 2 * (‖q‖ + ε) := by
      have := hρ.eps_pos
      linarith
    have hFz : F z ≤ max M₀ 0 * (2 * (‖q‖ + ε)) :=
      (hNle z).trans (mul_le_mul_of_nonneg_left hz2 hN0)
    have hεr : ε ≤ ‖q‖ + ε := by linarith [norm_nonneg q]
    have hMε : M * ε ≤ M * (‖q‖ + ε) := mul_le_mul_of_nonneg_left hεr hM0
    have h2 : F z + M * ε ≤ (2 * max M₀ 0 + M) * (‖q‖ + ε) := by nlinarith
    have hnn2 : (0 : ℝ) ≤ F z + M * ε :=
      add_nonneg (hF.nonneg z) (mul_nonneg hM0 hρ.eps_pos.le)
    have h4 : (F z + M * ε) ^ p ≤ ((2 * max M₀ 0 + M) * (‖q‖ + ε)) ^ p :=
      Real.rpow_le_rpow hnn2 h2 hp0.le
    have h5 : ((2 * max M₀ 0 + M) * (‖q‖ + ε)) ^ p =
        (2 * max M₀ 0 + M) ^ p * (‖q‖ + ε) ^ p := Real.mul_rpow hbase hrpos.le
    calc Korevaar.smoothedProfile p F ρ z ≤ (F z + M * ε) ^ p / p := hMle ρ ε hρ z
      _ ≤ ((2 * max M₀ 0 + M) * (‖q‖ + ε)) ^ p / p := by
          simp only [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left h4 (inv_nonneg.2 hp0.le)
      _ = (2 * max M₀ 0 + M) ^ p * (‖q‖ + ε) ^ p / p := by rw [h5]
  have hmain := norm_gradient_le_of_convexOn (differentiable_smoothedProfile hp hF hρ)
    (convexOn_smoothedProfile' hp hF hρ) (smoothedProfile_nonneg hp hF hρ) hrpos hub
  -- rewrite `r^p / r` as `r^(p-1)`
  have hrp : (‖q‖ + ε) ^ p = (‖q‖ + ε) * (‖q‖ + ε) ^ (p - 1) := by
    rw [Real.rpow_sub hrpos, Real.rpow_one]
    field_simp
  refine hmain.trans_eq ?_
  rw [hrp]
  field_simp
  try ring

end GradientGrowth

/-! ### Local upper bound for `D²Ψ`

Revision 2 of `REGULARIZED_ROUTE.md` replaced `Korevaar.smoothedProfile` by the abstract
class `IsRegProfile` and builds the profiles it needs in `TruncatedProfile*.lean`, so the
*lower* ellipticity bound for `smoothedProfile` is no longer part of the route; only the
elementary upper bound below is kept. -/

section Ellipticity

variable {p ε : ℝ} {F ρ : Euc d → ℝ}

/-- `∇Ψ` is `C^∞`, because `Ψ` is. -/
theorem contDiff_gradient_smoothedProfile (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) :
    ContDiff ℝ ∞ (gradient (Korevaar.smoothedProfile p F ρ)) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ (Korevaar.smoothedProfile p F ρ)) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_smoothedProfile' hp hF hρ)).2
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp hfd

/-- **The matching local upper bound for `D²Ψ`**: on every ball `‖q‖ ≤ R` there is `Λ ≥ 0`
with `⟪D²Ψ(q) ξ, ξ⟫ ≤ Λ ‖ξ‖²`.

`D²Ψ` is continuous (`contDiff_gradient_smoothedProfile`), hence bounded in operator norm on
the compact ball `closedBall 0 R`, and `⟪Aξ, ξ⟫ ≤ ‖A‖ ‖ξ‖²`. -/
theorem exists_local_ellipticity_upper (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) {R : ℝ} (hR : 0 < R) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ q : Euc d, ‖q‖ ≤ R → ∀ ξ : Euc d,
      ⟪fderiv ℝ (gradient (Korevaar.smoothedProfile p F ρ)) q ξ, ξ⟫ ≤ Λ * ‖ξ‖ ^ 2 := by
  have hc : Continuous (fderiv ℝ (gradient (Korevaar.smoothedProfile p F ρ))) :=
    (contDiff_gradient_smoothedProfile hp hF hρ).continuous_fderiv (by simp)
  obtain ⟨Λ₀, hΛ₀⟩ := (isCompact_closedBall (0 : Euc d) R).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max Λ₀ 0, le_max_right _ _, fun q hq ξ => ?_⟩
  have h1 : ‖fderiv ℝ (gradient (Korevaar.smoothedProfile p F ρ)) q‖ ≤ Λ₀ :=
    hΛ₀ q (mem_closedBall_zero_iff.2 hq)
  have h2 : ‖fderiv ℝ (gradient (Korevaar.smoothedProfile p F ρ)) q ξ‖ ≤ Λ₀ * ‖ξ‖ :=
    (fderiv ℝ (gradient (Korevaar.smoothedProfile p F ρ)) q).le_of_opNorm_le h1 ξ
  calc ⟪fderiv ℝ (gradient (Korevaar.smoothedProfile p F ρ)) q ξ, ξ⟫
      ≤ ‖fderiv ℝ (gradient (Korevaar.smoothedProfile p F ρ)) q ξ‖ * ‖ξ‖ :=
        real_inner_le_norm _ _
    _ ≤ Λ₀ * ‖ξ‖ * ‖ξ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg ξ)
    _ ≤ max Λ₀ 0 * ‖ξ‖ * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left Λ₀ 0) (norm_nonneg ξ)) (norm_nonneg ξ)
    _ = max Λ₀ 0 * ‖ξ‖ ^ 2 := by ring

end Ellipticity

end Komlos.Literature.Regularized
