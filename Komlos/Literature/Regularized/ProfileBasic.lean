import Komlos.Literature.Regularized.Interface

/-!
# Elementary consequences of `IsRegProfile`

`REGULARIZED_ROUTE.md`, Revision 2, replaces the mollified profile
`Korevaar.smoothedProfile p F ρ` by the abstract class `IsRegProfile`: a `C^∞`, even, convex
`Ψ : Euc d → ℝ` whose second derivative satisfies the *global* two-sided bound
`c ‖ξ‖² ≤ ⟪D(∇Ψ)(q) ξ, ξ⟫ ≤ C ‖ξ‖²` with `c > 0`.  This file proves, with no `sorry`, all
the consequences the downstream lanes need.

## Main results

* `IsRegProfileWith`: the same class with the two ellipticity constants exposed (and `C`
  normalized to be nonnegative).  `IsRegProfile.exists_isRegProfileWith` produces it.
* `IsRegProfile.gradient_neg`, `IsRegProfile.gradient_zero`: `∇Ψ` is odd, `∇Ψ(0) = 0`.
* `IsRegProfile.exists_elliptic_fderiv_gradient`: the symmetric positive semidefinite
  derivative package, i.e. exactly the `elliptic` field of
  `Korevaar.IsSmoothAffineReactionSolution`.
* `IsRegProfileWith.norm_fderiv_gradient_apply_le`, `IsRegProfileWith.norm_fderiv_gradient_le`:
  `‖D(∇Ψ)(q)‖ ≤ C`.  The two-sided bound on the quadratic form controls the *operator* norm
  because `D(∇Ψ)(q)` is symmetric and positive semidefinite: polarization gives
  `4 ⟪Aξ, η⟫ ≤ C ‖ξ + η‖²`, and `η = (‖ξ‖/‖Aξ‖) • Aξ` turns this into `‖Aξ‖ ≤ C ‖ξ‖`.
* `IsRegProfileWith.lipschitz_gradient`, `IsRegProfileWith.norm_gradient_le`: `∇Ψ` is
  `C`-Lipschitz and `‖∇Ψ q‖ ≤ C ‖q‖`.
* `IsRegProfileWith.inner_gradient_sub`: strong monotonicity
  `c ‖q - q'‖² ≤ ⟪∇Ψ q - ∇Ψ q', q - q'⟫`.
* `IsRegProfileWith.add_inner_add_half_le`, `IsRegProfileWith.le_add_inner_add_half`: the
  two-sided Taylor bound `Ψ q + ⟪∇Ψ q, ξ⟫ + (c/2)‖ξ‖² ≤ Ψ (q+ξ) ≤ Ψ q + ⟪∇Ψ q, ξ⟫ +
  (C/2)‖ξ‖²`, whence the quadratic growth `Ψ 0 + (c/2)‖q‖² ≤ Ψ q ≤ Ψ 0 + (C/2)‖q‖²`
  (`quadratic_lower`, `quadratic_upper`) and the convexity inequality
  `0 ≤ ⟪∇Ψ q, q⟫ - Ψ q + Ψ 0` (`IsRegProfile.zero_le_inner_gradient_sub`).

Every quantitative statement also has an `IsRegProfile`-level version with the constants
existentially quantified (`IsRegProfile.exists_*`).

All the one-dimensional work goes through `le_of_deriv_nonneg_unitInterval`: a function of
`t ∈ [0,1]` with nonnegative derivative there satisfies `f 0 ≤ f 1`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {Ψ : Euc d → ℝ} {c C : ℝ}

/-! ### A one-dimensional comparison helper -/

/-- If `f : ℝ → ℝ` is differentiable and `f' ≥ 0` on `[0,1]`, then `f 0 ≤ f 1`. -/
theorem le_of_deriv_nonneg_unitInterval {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ deriv f t) : f 0 ≤ f 1 := by
  have hmono : MonotoneOn f (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hf.continuous.continuousOn
      hf.differentiableOn fun t ht => h t (interior_subset ht)
  exact hmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one

/-! ### Smoothness, oddness of the gradient -/

namespace IsRegProfile

/-- A regularized profile is differentiable. -/
protected theorem differentiable (hΨ : IsRegProfile Ψ) : Differentiable ℝ Ψ :=
  hΨ.contDiff.differentiable (by simp)

/-- The gradient of a regularized profile is `C^∞`. -/
theorem contDiff_gradient (hΨ : IsRegProfile Ψ) : ContDiff ℝ ∞ (gradient Ψ) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ Ψ) := (contDiff_infty_iff_fderiv.1 hΨ.contDiff).2
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp hfd

/-- The gradient of a regularized profile is differentiable. -/
theorem differentiable_gradient (hΨ : IsRegProfile Ψ) : Differentiable ℝ (gradient Ψ) :=
  hΨ.contDiff_gradient.differentiable (by simp)

/-- `∇Ψ` has `fderiv ℝ (gradient Ψ) q` as its derivative at every point. -/
theorem hasFDerivAt_gradient (hΨ : IsRegProfile Ψ) (q : Euc d) :
    HasFDerivAt (gradient Ψ) (fderiv ℝ (gradient Ψ) q) q :=
  (hΨ.differentiable_gradient q).hasFDerivAt

/-- The gradient of an even profile is odd. -/
theorem gradient_neg (hΨ : IsRegProfile Ψ) (q : Euc d) :
    gradient Ψ (-q) = -gradient Ψ q :=
  Korevaar.gradient_odd_of_even hΨ.differentiable hΨ.even q

/-- The gradient of an even profile vanishes at the origin. -/
theorem gradient_zero (hΨ : IsRegProfile Ψ) : gradient Ψ (0 : Euc d) = 0 := by
  have h : gradient Ψ (-(0 : Euc d)) = -gradient Ψ (0 : Euc d) := hΨ.gradient_neg 0
  rw [neg_zero] at h
  have h2 : (2 : ℝ) • gradient Ψ (0 : Euc d) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    abel
  simpa using h2

/-! ### Derivative along a line -/

/-- The derivative of `t ↦ Ψ (a + t • e)`. -/
theorem hasDerivAt_line (hΨ : IsRegProfile Ψ) (a e : Euc d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ψ (a + s • e)) (⟪gradient Ψ (a + t • e), e⟫) t := by
  have hline : HasDerivAt (fun s : ℝ => a + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add a
  have hg := (hasGradientAt_iff_hasFDerivAt.1
    (hΨ.differentiable (a + t • e)).hasGradientAt).comp_hasDerivAt t hline
  rwa [InnerProductSpace.toDual_apply_apply] at hg

/-- The derivative of `t ↦ ⟪∇Ψ (a + t • e), z⟫`. -/
theorem hasDerivAt_inner_gradient_line (hΨ : IsRegProfile Ψ) (a e z : Euc d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪gradient Ψ (a + s • e), z⟫)
      (⟪fderiv ℝ (gradient Ψ) (a + t • e) e, z⟫) t := by
  have hline : HasDerivAt (fun s : ℝ => a + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add a
  have hcomp := (hΨ.hasFDerivAt_gradient (a + t • e)).comp_hasDerivAt t hline
  have hg : HasDerivAt (fun s : ℝ => gradient Ψ (a + s • e))
      (fderiv ℝ (gradient Ψ) (a + t • e) e) t := by
    simpa only [Function.comp_def] using hcomp
  simpa using hg.inner ℝ (hasDerivAt_const t z)

/-! ### The symmetric positive semidefinite derivative package -/

/-- Symmetry of `D(∇Ψ)(q)`. -/
theorem inner_fderiv_gradient_comm (hΨ : IsRegProfile Ψ) (q ξ η : Euc d) :
    ⟪fderiv ℝ (gradient Ψ) q ξ, η⟫ = ⟪ξ, fderiv ℝ (gradient Ψ) q η⟫ :=
  Korevaar.inner_fderiv_gradient_comm (Eventually.of_forall fun y => hΨ.differentiable y)
    (hΨ.hasFDerivAt_gradient q) ξ η

/-- The exact interface required by the `elliptic` field of
`Korevaar.IsSmoothAffineReactionSolution`: at every gradient value the flux `∇Ψ` has a
symmetric positive semidefinite derivative. -/
theorem exists_elliptic_fderiv_gradient (hΨ : IsRegProfile Ψ) (q : Euc d) :
    ∃ A : Euc d →L[ℝ] Euc d, HasFDerivAt (gradient Ψ) A q ∧
      (∀ ξ η : Euc d, ⟪A ξ, η⟫ = ⟪ξ, A η⟫) ∧ (∀ ξ : Euc d, 0 ≤ ⟪A ξ, ξ⟫) :=
  Korevaar.exists_elliptic_fderiv_gradient_of_contDiff_convex
    (hΨ.contDiff.of_le (by norm_cast)) hΨ.convexOn q

end IsRegProfile

/-! ### The ellipticity constants made explicit -/

/-- A regularized profile together with explicit ellipticity constants `c ≤ D²Ψ ≤ C`.  The
upper constant is normalized to be nonnegative, which costs nothing and avoids a
degenerate-dimension case distinction in the operator-norm bound. -/
structure IsRegProfileWith (Ψ : Euc d → ℝ) (c C : ℝ) : Prop extends IsRegProfile Ψ where
  /-- The lower ellipticity constant is positive. -/
  c_pos : 0 < c
  /-- The upper ellipticity constant is nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- The lower bound for `D²Ψ`. -/
  lower : ∀ q ξ : Euc d, c * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫
  /-- The upper bound for `D²Ψ`. -/
  upper : ∀ q ξ : Euc d, ⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫ ≤ C * ‖ξ‖ ^ 2

/-- Every regularized profile carries explicit ellipticity constants. -/
theorem IsRegProfile.exists_isRegProfileWith (hΨ : IsRegProfile Ψ) :
    ∃ c C : ℝ, IsRegProfileWith Ψ c C := by
  obtain ⟨c, C, hc, hell⟩ := hΨ.elliptic
  refine ⟨c, max C 0, { hΨ with
    c_pos := hc
    C_nonneg := le_max_right _ _
    lower := fun q ξ => (hell q ξ).1
    upper := fun q ξ => ?_ }⟩
  exact (hell q ξ).2.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

namespace IsRegProfileWith

/-! ### The operator norm of `D²Ψ` -/

/-- **The upper ellipticity bound controls the operator norm.**  `A = D(∇Ψ)(q)` is symmetric
and positive semidefinite, so polarization gives `4 ⟪A ξ, η⟫ ≤ C ‖ξ + η‖²`; taking
`η = (‖ξ‖/‖A ξ‖) • A ξ` yields `4 ‖ξ‖ ‖A ξ‖ ≤ 4 C ‖ξ‖²`. -/
theorem norm_fderiv_gradient_apply_le (h : IsRegProfileWith Ψ c C) (q ξ : Euc d) :
    ‖fderiv ℝ (gradient Ψ) q ξ‖ ≤ C * ‖ξ‖ := by
  have hsymm : ∀ a b : Euc d, ⟪fderiv ℝ (gradient Ψ) q a, b⟫ =
      ⟪a, fderiv ℝ (gradient Ψ) q b⟫ := h.toIsRegProfile.inner_fderiv_gradient_comm q
  have hswap : ∀ a b : Euc d, ⟪fderiv ℝ (gradient Ψ) q b, a⟫ =
      ⟪fderiv ℝ (gradient Ψ) q a, b⟫ := fun a b =>
    (hsymm b a).trans (real_inner_comm (fderiv ℝ (gradient Ψ) q a) b)
  have hnn : ∀ a : Euc d, 0 ≤ ⟪fderiv ℝ (gradient Ψ) q a, a⟫ := fun a =>
    le_trans (mul_nonneg h.c_pos.le (sq_nonneg _)) (h.lower q a)
  -- polarization
  have hpol : ∀ a b : Euc d, 4 * ⟪fderiv ℝ (gradient Ψ) q a, b⟫ ≤ C * ‖a + b‖ ^ 2 := by
    intro a b
    have e1 : ⟪fderiv ℝ (gradient Ψ) q (a + b), a + b⟫ =
        ⟪fderiv ℝ (gradient Ψ) q a, a⟫ + 2 * ⟪fderiv ℝ (gradient Ψ) q a, b⟫ +
          ⟪fderiv ℝ (gradient Ψ) q b, b⟫ := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, hswap a b]
      ring
    have e2 : ⟪fderiv ℝ (gradient Ψ) q (a - b), a - b⟫ =
        ⟪fderiv ℝ (gradient Ψ) q a, a⟫ - 2 * ⟪fderiv ℝ (gradient Ψ) q a, b⟫ +
          ⟪fderiv ℝ (gradient Ψ) q b, b⟫ := by
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hswap a b]
      ring
    have h1 := h.upper q (a + b)
    have h2 := hnn (a - b)
    rw [e1] at h1
    rw [e2] at h2
    linarith
  rcases eq_or_ne ξ 0 with hξ | hξ
  · simp [hξ]
  rcases eq_or_ne (fderiv ℝ (gradient Ψ) q ξ) 0 with hA0 | hA0
  · rw [hA0, norm_zero]
    exact mul_nonneg h.C_nonneg (norm_nonneg ξ)
  · have hξpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hApos : 0 < ‖fderiv ℝ (gradient Ψ) q ξ‖ := norm_pos_iff.2 hA0
    set η : Euc d := (‖ξ‖ / ‖fderiv ℝ (gradient Ψ) q ξ‖) • fderiv ℝ (gradient Ψ) q ξ with hη
    have hnorm : ‖η‖ = ‖ξ‖ := by
      rw [hη, norm_smul, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hinner : ⟪fderiv ℝ (gradient Ψ) q ξ, η⟫ =
        ‖ξ‖ * ‖fderiv ℝ (gradient Ψ) q ξ‖ := by
      rw [hη, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
      field_simp
      try ring
    have hsum : ‖ξ + η‖ ≤ 2 * ‖ξ‖ := by
      calc ‖ξ + η‖ ≤ ‖ξ‖ + ‖η‖ := norm_add_le _ _
        _ = 2 * ‖ξ‖ := by rw [hnorm]; ring
    have hsq : ‖ξ + η‖ ^ 2 ≤ (2 * ‖ξ‖) ^ 2 := by nlinarith [norm_nonneg (ξ + η)]
    have hmain := hpol ξ η
    rw [hinner] at hmain
    have h3 : C * ‖ξ + η‖ ^ 2 ≤ C * (2 * ‖ξ‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq h.C_nonneg
    have key : ‖ξ‖ * ‖fderiv ℝ (gradient Ψ) q ξ‖ ≤ ‖ξ‖ * (C * ‖ξ‖) := by nlinarith
    exact le_of_mul_le_mul_left key hξpos

/-- The operator norm of `D²Ψ` is bounded by the upper ellipticity constant. -/
theorem norm_fderiv_gradient_le (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    ‖fderiv ℝ (gradient Ψ) q‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ h.C_nonneg (h.norm_fderiv_gradient_apply_le q)

/-! ### Lipschitz continuity and growth of `∇Ψ` -/

/-- **`∇Ψ` is globally `C`-Lipschitz.** -/
theorem lipschitz_gradient (h : IsRegProfileWith Ψ c C) (q q' : Euc d) :
    ‖gradient Ψ q - gradient Ψ q'‖ ≤ C * ‖q - q'‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => h.toIsRegProfile.differentiable_gradient x)
    (fun x _ => h.norm_fderiv_gradient_le x) (mem_univ q') (mem_univ q)

/-- **Linear growth of `∇Ψ`**: `‖∇Ψ q‖ ≤ C ‖q‖`. -/
theorem norm_gradient_le (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    ‖gradient Ψ q‖ ≤ C * ‖q‖ := by
  have hlip := h.lipschitz_gradient q 0
  rwa [h.toIsRegProfile.gradient_zero, sub_zero, sub_zero] at hlip

/-! ### Strong monotonicity -/

/-- **Strong monotonicity of `∇Ψ`**: `c ‖q - q'‖² ≤ ⟪∇Ψ q - ∇Ψ q', q - q'⟫`.  Integrate the
lower ellipticity bound along the segment from `q'` to `q`. -/
theorem inner_gradient_sub (h : IsRegProfileWith Ψ c C) (q q' : Euc d) :
    c * ‖q - q'‖ ^ 2 ≤ ⟪gradient Ψ q - gradient Ψ q', q - q'⟫ := by
  set e : Euc d := q - q' with he
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => ⟪gradient Ψ (q' + s • e), e⟫ - c * s * ‖e‖ ^ 2)
        (⟪fderiv ℝ (gradient Ψ) (q' + t • e) e, e⟫ - c * ‖e‖ ^ 2) t := by
    intro t
    have h1 := h.toIsRegProfile.hasDerivAt_inner_gradient_line q' e e t
    have h2 : HasDerivAt (fun s : ℝ => c * s * ‖e‖ ^ 2) (c * ‖e‖ ^ 2) t := by
      simpa using (((hasDerivAt_id t).const_mul c).mul_const (‖e‖ ^ 2))
    exact h1.sub h2
  have hkey := le_of_deriv_nonneg_unitInterval
    (f := fun s : ℝ => ⟪gradient Ψ (q' + s • e), e⟫ - c * s * ‖e‖ ^ 2)
    (fun t => (hderiv t).differentiableAt) (fun t _ => by
      rw [(hderiv t).deriv]
      exact sub_nonneg.2 (h.lower _ e))
  simp only [zero_smul, one_smul, add_zero, mul_zero, zero_mul, sub_zero, mul_one] at hkey
  have hqe : q' + e = q := by rw [he]; abel
  rw [hqe] at hkey
  rw [inner_sub_left]
  linarith

/-! ### The two-sided Taylor bound -/

/-- **Strong convexity**: `Ψ q + ⟪∇Ψ q, ξ⟫ + (c/2) ‖ξ‖² ≤ Ψ (q + ξ)`. -/
theorem add_inner_add_half_le (h : IsRegProfileWith Ψ c C) (q ξ : Euc d) :
    Ψ q + ⟪gradient Ψ q, ξ⟫ + c / 2 * ‖ξ‖ ^ 2 ≤ Ψ (q + ξ) := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt
        (fun s : ℝ => Ψ (q + s • ξ) - Ψ q - s * ⟪gradient Ψ q, ξ⟫ - c / 2 * s ^ 2 * ‖ξ‖ ^ 2)
        (⟪gradient Ψ (q + t • ξ), ξ⟫ - ⟪gradient Ψ q, ξ⟫ - c * t * ‖ξ‖ ^ 2) t := by
    intro t
    have h1 := h.toIsRegProfile.hasDerivAt_line q ξ t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient Ψ q, ξ⟫) (⟪gradient Ψ q, ξ⟫) t := by
      simpa using (hasDerivAt_id t).mul_const (⟪gradient Ψ q, ξ⟫)
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h3 : HasDerivAt (fun s : ℝ => c / 2 * s ^ 2 * ‖ξ‖ ^ 2) (c * t * ‖ξ‖ ^ 2) t := by
      have h4 : HasDerivAt (fun s : ℝ => c / 2 * s ^ 2 * ‖ξ‖ ^ 2)
          (c / 2 * (2 * t) * ‖ξ‖ ^ 2) t := (hsq.const_mul (c / 2)).mul_const (‖ξ‖ ^ 2)
      have heq : c / 2 * (2 * t) * ‖ξ‖ ^ 2 = c * t * ‖ξ‖ ^ 2 := by ring
      rwa [heq] at h4
    exact ((h1.sub_const (Ψ q)).sub h2).sub h3
  have hnn : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ ⟪gradient Ψ (q + t • ξ), ξ⟫ - ⟪gradient Ψ q, ξ⟫ - c * t * ‖ξ‖ ^ 2 := by
    intro t ht
    have hmono := h.inner_gradient_sub (q + t • ξ) q
    have hsub : q + t • ξ - q = t • ξ := by abel
    rw [hsub] at hmono
    -- `⟪∇Ψ(q+tξ) - ∇Ψ q, t ξ⟫ = t ⟪∇Ψ(q+tξ) - ∇Ψ q, ξ⟫` and `‖tξ‖² = t²‖ξ‖²`
    rw [real_inner_smul_right, norm_smul, mul_pow, Real.norm_of_nonneg ht.1] at hmono
    rw [inner_sub_left] at hmono
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · simp [← h0]
    · have hle : c * t * ‖ξ‖ ^ 2 ≤ ⟪gradient Ψ (q + t • ξ), ξ⟫ - ⟪gradient Ψ q, ξ⟫ := by
        have := hmono
        nlinarith [this]
      linarith
  have hkey := le_of_deriv_nonneg_unitInterval
    (f := fun s : ℝ => Ψ (q + s • ξ) - Ψ q - s * ⟪gradient Ψ q, ξ⟫ - c / 2 * s ^ 2 * ‖ξ‖ ^ 2)
    (fun t => (hderiv t).differentiableAt) (fun t ht => by
      rw [(hderiv t).deriv]; exact hnn t ht)
  simp only [zero_smul, one_smul, add_zero, zero_mul, mul_zero, sub_zero, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hkey
  linarith

/-- **Quadratic upper Taylor bound**: `Ψ (q + ξ) ≤ Ψ q + ⟪∇Ψ q, ξ⟫ + (C/2) ‖ξ‖²`. -/
theorem le_add_inner_add_half (h : IsRegProfileWith Ψ c C) (q ξ : Euc d) :
    Ψ (q + ξ) ≤ Ψ q + ⟪gradient Ψ q, ξ⟫ + C / 2 * ‖ξ‖ ^ 2 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt
        (fun s : ℝ => Ψ q + s * ⟪gradient Ψ q, ξ⟫ + C / 2 * s ^ 2 * ‖ξ‖ ^ 2 - Ψ (q + s • ξ))
        (⟪gradient Ψ q, ξ⟫ + C * t * ‖ξ‖ ^ 2 - ⟪gradient Ψ (q + t • ξ), ξ⟫) t := by
    intro t
    have h1 := h.toIsRegProfile.hasDerivAt_line q ξ t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient Ψ q, ξ⟫) (⟪gradient Ψ q, ξ⟫) t := by
      simpa using (hasDerivAt_id t).mul_const (⟪gradient Ψ q, ξ⟫)
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h3 : HasDerivAt (fun s : ℝ => C / 2 * s ^ 2 * ‖ξ‖ ^ 2) (C * t * ‖ξ‖ ^ 2) t := by
      have h4 : HasDerivAt (fun s : ℝ => C / 2 * s ^ 2 * ‖ξ‖ ^ 2)
          (C / 2 * (2 * t) * ‖ξ‖ ^ 2) t := (hsq.const_mul (C / 2)).mul_const (‖ξ‖ ^ 2)
      have heq : C / 2 * (2 * t) * ‖ξ‖ ^ 2 = C * t * ‖ξ‖ ^ 2 := by ring
      rwa [heq] at h4
    exact (((h2.const_add (Ψ q)).add h3).sub h1)
  have hnn : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ ⟪gradient Ψ q, ξ⟫ + C * t * ‖ξ‖ ^ 2 - ⟪gradient Ψ (q + t • ξ), ξ⟫ := by
    intro t ht
    have hlip := h.lipschitz_gradient (q + t • ξ) q
    have hsub : q + t • ξ - q = t • ξ := by abel
    rw [hsub, norm_smul, Real.norm_of_nonneg ht.1] at hlip
    have hcs : ⟪gradient Ψ (q + t • ξ) - gradient Ψ q, ξ⟫ ≤
        ‖gradient Ψ (q + t • ξ) - gradient Ψ q‖ * ‖ξ‖ := real_inner_le_norm _ _
    rw [inner_sub_left] at hcs
    nlinarith [norm_nonneg ξ]
  have hkey := le_of_deriv_nonneg_unitInterval
    (f := fun s : ℝ => Ψ q + s * ⟪gradient Ψ q, ξ⟫ + C / 2 * s ^ 2 * ‖ξ‖ ^ 2 - Ψ (q + s • ξ))
    (fun t => (hderiv t).differentiableAt) (fun t ht => by
      rw [(hderiv t).deriv]; exact hnn t ht)
  simp only [zero_smul, one_smul, add_zero, zero_mul, mul_zero, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hkey
  linarith

/-! ### Quadratic growth and the convexity inequality -/

/-- **Quadratic lower bound**: `Ψ 0 + (c/2) ‖q‖² ≤ Ψ q`. -/
theorem quadratic_lower (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    Ψ 0 + c / 2 * ‖q‖ ^ 2 ≤ Ψ q := by
  have hmain := h.add_inner_add_half_le 0 q
  rw [h.toIsRegProfile.gradient_zero, inner_zero_left, zero_add] at hmain
  simpa using hmain

/-- **Quadratic upper bound**: `Ψ q ≤ Ψ 0 + (C/2) ‖q‖²`. -/
theorem quadratic_upper (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    Ψ q ≤ Ψ 0 + C / 2 * ‖q‖ ^ 2 := by
  have hmain := h.le_add_inner_add_half 0 q
  rw [h.toIsRegProfile.gradient_zero, inner_zero_left, zero_add] at hmain
  simpa using hmain

/-- **The convexity inequality** `0 ≤ ⟪∇Ψ q, q⟫ - Ψ q + Ψ 0`: the tangent plane of `Ψ` at `q`
lies below `Ψ`, evaluated at the origin. -/
theorem zero_le_inner_gradient_sub (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    0 ≤ ⟪gradient Ψ q, q⟫ - Ψ q + Ψ 0 := by
  have hmain := h.add_inner_add_half_le q (-q)
  rw [add_neg_cancel, inner_neg_right] at hmain
  have hpos : 0 ≤ c / 2 * ‖(-q : Euc d)‖ ^ 2 :=
    mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
  linarith

end IsRegProfileWith

/-! ### Existentially quantified versions -/

namespace IsRegProfile

/-- `∇Ψ` is globally Lipschitz, with linear growth. -/
theorem exists_lipschitz_gradient (hΨ : IsRegProfile Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ q q' : Euc d, ‖gradient Ψ q - gradient Ψ q'‖ ≤ C * ‖q - q'‖) ∧
      ∀ q : Euc d, ‖gradient Ψ q‖ ≤ C * ‖q‖ := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  exact ⟨C, h.C_nonneg, h.lipschitz_gradient, h.norm_gradient_le⟩

/-- `∇Ψ` is strongly monotone. -/
theorem exists_strongly_monotone_gradient (hΨ : IsRegProfile Ψ) :
    ∃ c : ℝ, 0 < c ∧ ∀ q q' : Euc d,
      c * ‖q - q'‖ ^ 2 ≤ ⟪gradient Ψ q - gradient Ψ q', q - q'⟫ := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  exact ⟨c, h.c_pos, h.inner_gradient_sub⟩

/-- Two-sided quadratic growth of `Ψ` around its minimum at the origin. -/
theorem exists_quadratic_bounds (hΨ : IsRegProfile Ψ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ (∀ q : Euc d, Ψ 0 + c / 2 * ‖q‖ ^ 2 ≤ Ψ q) ∧
      ∀ q : Euc d, Ψ q ≤ Ψ 0 + C / 2 * ‖q‖ ^ 2 := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  exact ⟨c, C, h.c_pos, h.C_nonneg, h.quadratic_lower, h.quadratic_upper⟩

/-- The convexity inequality `0 ≤ ⟪∇Ψ q, q⟫ - Ψ q + Ψ 0`. -/
theorem zero_le_inner_gradient_sub (hΨ : IsRegProfile Ψ) (q : Euc d) :
    0 ≤ ⟪gradient Ψ q, q⟫ - Ψ q + Ψ 0 := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  exact h.zero_le_inner_gradient_sub q

end IsRegProfile

end Komlos.Literature.Regularized
