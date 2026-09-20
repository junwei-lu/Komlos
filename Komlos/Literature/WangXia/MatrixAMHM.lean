import Mathlib

/-!
# The arithmetic–harmonic inequality for positive matrices

This file proves the operator (Loewner-order) arithmetic–harmonic mean inequality used in
paper Appendix A (the proof of Wang–Xia's Theorem 1.2, cf. paper Proposition A.1): for
symmetric positive-definite matrices `B₀, B₁` and `0 ≤ t ≤ 1`,
```
((1 - t) • B₀⁻¹ + t • B₁⁻¹)⁻¹ ≤ (1 - t) • B₀ + t • B₁ .
```
The paper uses it to bound the Hessian of the perturbed infimal convolution,
`D²w_η = ((1-t)B₀⁻¹ + tB₁⁻¹)⁻¹ ≤ (1-t)B₀ + tB₁`.

## Strategy

The inequality is exactly operator convexity of `X ↦ X⁻¹` on positive-definite matrices,
applied to `B₀⁻¹, B₁⁻¹`.  We prove operator convexity of the inverse in the generality of a
unital ring with a real continuous functional calculus (so it applies to real *and* complex
matrices, and to self-adjoint operators):

1. `harm_le_arith`: the scalar inequality `((1-t)/a + t/b)⁻¹ ≤ (1-t)a + tb` for `a, b > 0`.
2. `ringInverse_algebraMap_add_smul_le`: for a strictly positive `x`, the one-variable
   operator inequality `((1-t)·1 + t x)⁻¹ ≤ (1-t)·1 + t x⁻¹`, obtained from (1) with `a = 1`
   through the continuous functional calculus (`cfc_mono`).
3. `ringInverse_smul_add_smul_le` (operator convexity of the inverse): the joint congruence
   by `c = a^{-1/2}` reduces the general case to (2), since `c a c = 1` and `x = c b c` is
   strictly positive; congruence by a self-adjoint element preserves the Loewner order.
4. `ringInverse_amhm`: (3) applied to `a⁻¹, b⁻¹`.
5. `matrix_amhm` and friends: the specialisation to `Matrix n n ℝ` with `Matrix.PosDef`
   (inverses are `Matrix.inv`, the order is the Loewner order `Matrix.instPartialOrder`,
   scoped in `MatrixOrder`), together with the `PosSemidef` and quadratic-form restatements.
-/

namespace Komlos.Literature

open scoped NNReal

/-! ### The scalar inequality -/

/-- Scalar arithmetic–harmonic mean inequality: for `a, b > 0` and `0 ≤ t ≤ 1`,
`((1 - t) / a + t / b)⁻¹ ≤ (1 - t) * a + t * b` (the weighted harmonic mean is at most the
weighted arithmetic mean; convexity of `x ↦ 1 / x`). -/
theorem harm_le_arith {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) / a + t / b)⁻¹ ≤ (1 - t) * a + t * b := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
  have hden : 0 < (1 - t) / a + t / b := by
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · simpa using hb
    · have : 0 < 1 - t := sub_pos.2 ht1'
      positivity
  rw [inv_eq_one_div, div_le_iff₀ hden]
  have key : ((1 - t) * a + t * b) * ((1 - t) / a + t / b)
      = 1 + t * (1 - t) * (a - b) ^ 2 / (a * b) := by
    field_simp
    ring
  have hnn : 0 ≤ t * (1 - t) * (a - b) ^ 2 / (a * b) :=
    div_nonneg (mul_nonneg (mul_nonneg ht0 h1t) (sq_nonneg _)) (mul_pos ha hb).le
  rw [key]
  linarith

/-- The affine function `s ↦ (1 - t) + t * s` is positive on `(0, ∞)` for `0 ≤ t ≤ 1`. -/
theorem affine_pos {s t : ℝ} (hs : 0 < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (1 - t) + t * s := by
  rcases le_or_gt s 1 with h | h <;> nlinarith

/-- One-variable form of `harm_le_arith`, with `a = 1` and `b = s⁻¹`:
`((1 - t) + t * s)⁻¹ ≤ (1 - t) + t * s⁻¹` for `s > 0`. -/
theorem inv_affine_le {s t : ℝ} (hs : 0 < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) + t * s)⁻¹ ≤ (1 - t) + t * s⁻¹ := by
  have := harm_le_arith one_pos (inv_pos.2 hs) ht0 ht1
  rwa [div_one, div_inv_eq_mul, mul_one] at this

/-! ### Inverses of conjugates -/

/-- If `c` is a two-sided inverse of `d` and `y` is a unit, then the `Ring.inverse` of
`d * y * d` is `c * y⁻¹ * c`.  Stated with an arbitrary `z = d * y * d` for convenient
rewriting. -/
theorem ringInverse_conj {A : Type*} [Ring A] {c d y z : A} (hcd : c * d = 1) (hdc : d * c = 1)
    (hy : IsUnit y) (hz : d * y * d = z) :
    Ring.inverse z = c * Ring.inverse y * c := by
  subst hz
  have hd : IsUnit d := ⟨⟨d, c, hdc, hcd⟩, rfl⟩
  have hu : IsUnit (d * y * d) := (hd.mul hy).mul hd
  have hz : c * Ring.inverse y * c * (d * y * d) = 1 := by
    calc c * Ring.inverse y * c * (d * y * d)
        = c * Ring.inverse y * (c * d) * y * d := by simp only [mul_assoc]
      _ = c * (Ring.inverse y * y) * d := by rw [hcd, mul_one, mul_assoc c]
      _ = 1 := by rw [Ring.inverse_mul_cancel y hy, mul_one, hcd]
  calc Ring.inverse (d * y * d)
      = (c * Ring.inverse y * c * (d * y * d)) * Ring.inverse (d * y * d) := by
        rw [hz, one_mul]
    _ = c * Ring.inverse y * c * ((d * y * d) * Ring.inverse (d * y * d)) := by
        rw [mul_assoc]
    _ = c * Ring.inverse y * c := by rw [Ring.mul_inverse_cancel _ hu, mul_one]

/-! ### Operator convexity of the inverse via the continuous functional calculus -/

section General

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

omit [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] in
/-- The continuous functional calculus of an affine function. -/
theorem cfc_affine {x : A} (hx : IsSelfAdjoint x) (r t : ℝ) :
    cfc (fun s : ℝ => r + t * s) x = algebraMap ℝ A r + t • x := by
  rw [cfc_const_add _ _ _ (by fun_prop) hx, cfc_const_mul_id _ _ hx]

/-- For strictly positive `x` and `0 ≤ t ≤ 1`, the element `(1 - t) • 1 + t • x` is strictly
positive (in particular a unit). -/
theorem isStrictlyPositive_algebraMap_add_smul {x : A} (hx : IsStrictlyPositive x) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsStrictlyPositive (algebraMap ℝ A (1 - t) + t • x) := by
  rw [← cfc_affine hx.isSelfAdjoint]
  exact (cfc_isStrictlyPositive_iff _ _ (by fun_prop) hx.isSelfAdjoint).mpr
    fun s hs => affine_pos (hx.spectrum_pos hs) ht0 ht1

/-- The inverse of a strictly positive element is strictly positive. -/
theorem isStrictlyPositive_ringInverse {x : A} (hx : IsStrictlyPositive x) :
    IsStrictlyPositive (Ring.inverse x) := by
  rw [← cfc_ringInverse_id (R := ℝ) x hx.isUnit hx.isSelfAdjoint]
  refine (cfc_isStrictlyPositive_iff _ _ ?_ hx.isSelfAdjoint).mpr
    fun s hs => inv_pos.2 (hx.spectrum_pos hs)
  exact ContinuousOn.inv₀ continuousOn_id fun s hs => (hx.spectrum_pos hs).ne'

/-- One-variable operator arithmetic–harmonic inequality: for strictly positive `x` and
`0 ≤ t ≤ 1`, `((1 - t) • 1 + t • x)⁻¹ ≤ (1 - t) • 1 + t • x⁻¹` (inverses as `Ring.inverse`). -/
theorem ringInverse_algebraMap_add_smul_le {x : A} (hx : IsStrictlyPositive x) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ring.inverse (algebraMap ℝ A (1 - t) + t • x)
      ≤ algebraMap ℝ A (1 - t) + t • Ring.inverse x := by
  have hsa : IsSelfAdjoint x := hx.isSelfAdjoint
  have hspec : ∀ s ∈ spectrum ℝ x, 0 < s := fun s hs => hx.spectrum_pos hs
  have hpos : ∀ s ∈ spectrum ℝ x, 0 < (1 - t) + t * s :=
    fun s hs => affine_pos (hspec s hs) ht0 ht1
  have hcont₁ : ContinuousOn (fun s : ℝ => ((1 - t) + t * s)⁻¹) (spectrum ℝ x) :=
    ContinuousOn.inv₀ (by fun_prop) fun s hs => (hpos s hs).ne'
  have hcont₂ : ContinuousOn (fun s : ℝ => s⁻¹) (spectrum ℝ x) :=
    ContinuousOn.inv₀ continuousOn_id fun s hs => (hspec s hs).ne'
  have hcont₃ : ContinuousOn (fun s : ℝ => (1 - t) + t * s⁻¹) (spectrum ℝ x) :=
    continuousOn_const.add (continuousOn_const.mul hcont₂)
  have e₁ : cfc (fun s : ℝ => ((1 - t) + t * s)⁻¹) x
      = Ring.inverse (algebraMap ℝ A (1 - t) + t • x) := by
    rw [← cfc_affine hsa]
    exact cfc_inv _ x (fun s hs => (hpos s hs).ne') (by fun_prop) hsa
  have e₂ : cfc (fun s : ℝ => (1 - t) + t * s⁻¹) x
      = algebraMap ℝ A (1 - t) + t • Ring.inverse x := by
    rw [cfc_const_add (1 - t) (fun s : ℝ => t * s⁻¹) x (continuousOn_const.mul hcont₂) hsa,
      cfc_const_mul t (fun s : ℝ => s⁻¹) x hcont₂, cfc_ringInverse_id (R := ℝ) x hx.isUnit hsa]
  rw [← e₁, ← e₂]
  exact cfc_mono (fun s hs => inv_affine_le (hspec s hs) ht0 ht1) hcont₁ hcont₃

/-- **Operator convexity of the inverse.**  For strictly positive `a, b` and `0 ≤ t ≤ 1`,
`((1 - t) • a + t • b)⁻¹ ≤ (1 - t) • a⁻¹ + t • b⁻¹` (inverses as `Ring.inverse`).
Proof by simultaneous congruence with `c = a ^ (-1/2)`. -/
theorem ringInverse_smul_add_smul_le {a b : A} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ring.inverse ((1 - t) • a + t • b) ≤ (1 - t) • Ring.inverse a + t • Ring.inverse b := by
  -- `c = a^{-1/2}`, `d = a^{1/2}`: two-sided inverses, `d * d = a`, `c ≥ 0`.
  obtain ⟨c, d, hcd, hdc, hdd, hc0⟩ :
      ∃ c d : A, c * d = 1 ∧ d * c = 1 ∧ d * d = a ∧ 0 ≤ c := by
    refine ⟨a ^ (-(1 / 2 : ℝ)), a ^ (1 / 2 : ℝ), CFC.rpow_neg_mul_rpow _ ha,
      CFC.rpow_mul_rpow_neg _ ha, ?_, CFC.rpow_nonneg⟩
    rw [← CFC.rpow_add ha.isUnit]
    norm_num
    exact CFC.rpow_one a ha.nonneg
  have hc_sa : IsSelfAdjoint c := IsSelfAdjoint.of_nonneg hc0
  have hc_unit : IsUnit c := ⟨⟨c, d, hcd, hdc⟩, rfl⟩
  -- `x = c * b * c` is strictly positive and `b = d * x * d`.
  have hx : IsStrictlyPositive (c * b * c) :=
    IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint b c hc_unit hc_sa hb
  have hb' : d * (c * b * c) * d = b := by
    calc d * (c * b * c) * d = (d * c) * b * (c * d) := by simp only [mul_assoc]
      _ = b := by rw [hdc, hcd, one_mul, mul_one]
  -- the convex combination is the congruence of `(1 - t) • 1 + t • x` by `d`.
  have hm : d * (algebraMap ℝ A (1 - t) + t • (c * b * c)) * d = (1 - t) • a + t • b := by
    rw [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      hdd, mul_smul_comm, smul_mul_assoc, hb']
  have hy : IsUnit (algebraMap ℝ A (1 - t) + t • (c * b * c)) :=
    (isStrictlyPositive_algebraMap_add_smul hx ht0 ht1).isUnit
  have hinv_a : Ring.inverse a = c * c := by
    have := ringInverse_conj hcd hdc isUnit_one (by rw [mul_one, hdd])
    rwa [Ring.inverse_one, mul_one] at this
  have hinv_b : Ring.inverse b = c * Ring.inverse (c * b * c) * c :=
    ringInverse_conj hcd hdc hx.isUnit hb'
  calc Ring.inverse ((1 - t) • a + t • b)
      = c * Ring.inverse (algebraMap ℝ A (1 - t) + t • (c * b * c)) * c :=
        ringInverse_conj hcd hdc hy hm
    _ ≤ c * (algebraMap ℝ A (1 - t) + t • Ring.inverse (c * b * c)) * c :=
        hc_sa.conjugate_le_conjugate (ringInverse_algebraMap_add_smul_le hx ht0 ht1)
    _ = (1 - t) • Ring.inverse a + t • Ring.inverse b := by
        rw [hinv_a, hinv_b, Algebra.algebraMap_eq_smul_one, mul_add, add_mul, mul_smul_comm,
          smul_mul_assoc, mul_one, mul_smul_comm, smul_mul_assoc]

/-- **Arithmetic–harmonic inequality** for strictly positive elements (inverses as
`Ring.inverse`): for `0 ≤ t ≤ 1`,
`((1 - t) • a⁻¹ + t • b⁻¹)⁻¹ ≤ (1 - t) • a + t • b`.  This is
`ringInverse_smul_add_smul_le` applied to `a⁻¹, b⁻¹`. -/
theorem ringInverse_amhm {a b : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ring.inverse ((1 - t) • Ring.inverse a + t • Ring.inverse b) ≤ (1 - t) • a + t • b := by
  have := ringInverse_smul_add_smul_le (isStrictlyPositive_ringInverse ha)
    (isStrictlyPositive_ringInverse hb) ht0 ht1
  rwa [Ring.inverse_inverse ha.isUnit, Ring.inverse_inverse hb.isUnit] at this

end General

/-! ### Matrices -/

section Matrix

open Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Arithmetic–harmonic matrix inequality** (paper Appendix A, used for
`D²w_η = ((1-t)B₀⁻¹ + tB₁⁻¹)⁻¹ ≤ (1-t)B₀ + tB₁`): for real symmetric positive-definite
matrices `B₀, B₁` and `0 ≤ t ≤ 1`, in the Loewner order,
`((1 - t) • B₀⁻¹ + t • B₁⁻¹)⁻¹ ≤ (1 - t) • B₀ + t • B₁`. -/
theorem matrix_amhm {B₀ B₁ : Matrix n n ℝ} (h₀ : B₀.PosDef) (h₁ : B₁.PosDef) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • B₀⁻¹ + t • B₁⁻¹)⁻¹ ≤ (1 - t) • B₀ + t • B₁ := by
  simp only [nonsing_inv_eq_ringInverse]
  exact ringInverse_amhm h₀.isStrictlyPositive h₁.isStrictlyPositive ht0 ht1

/-- `matrix_amhm`, phrased as positive semidefiniteness of the difference
(`Matrix.le_iff` unfolds the Loewner order to exactly this). -/
theorem matrix_amhm_posSemidef {B₀ B₁ : Matrix n n ℝ} (h₀ : B₀.PosDef) (h₁ : B₁.PosDef) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • B₀ + t • B₁ - ((1 - t) • B₀⁻¹ + t • B₁⁻¹)⁻¹).PosSemidef :=
  matrix_amhm h₀ h₁ ht0 ht1

/-- `matrix_amhm` as an inequality of quadratic forms: for every `x`,
`x ⬝ᵥ (((1 - t) • B₀⁻¹ + t • B₁⁻¹)⁻¹ *ᵥ x) ≤ x ⬝ᵥ (((1 - t) • B₀ + t • B₁) *ᵥ x)`. -/
theorem matrix_amhm_dotProduct {B₀ B₁ : Matrix n n ℝ} (h₀ : B₀.PosDef) (h₁ : B₁.PosDef) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : n → ℝ) :
    x ⬝ᵥ (((1 - t) • B₀⁻¹ + t • B₁⁻¹)⁻¹ *ᵥ x) ≤ x ⬝ᵥ (((1 - t) • B₀ + t • B₁) *ᵥ x) := by
  have h := (matrix_amhm_posSemidef h₀ h₁ ht0 ht1).dotProduct_mulVec_nonneg x
  rw [sub_mulVec, dotProduct_sub] at h
  simpa using h

/-- The positive-definite matrix `(1 - t) • B₀⁻¹ + t • B₁⁻¹` (the "harmonic" side) is
invertible and positive definite. -/
theorem posDef_smul_inv_add_smul_inv {B₀ B₁ : Matrix n n ℝ} (h₀ : B₀.PosDef) (h₁ : B₁.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ((1 - t) • B₀⁻¹ + t • B₁⁻¹).PosDef := by
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · simpa using h₁.inv
  · rcases eq_or_lt_of_le ht0 with rfl | ht0'
    · simpa using h₀.inv
    · exact (h₀.inv.smul (sub_pos.2 ht1')).add (h₁.inv.smul ht0')

/-- `matrix_amhm` for `Fin d` (as in the paper: `d × d` matrices). -/
theorem matrix_amhm_fin {d : ℕ} {B₀ B₁ : Matrix (Fin d) (Fin d) ℝ} (h₀ : B₀.PosDef)
    (h₁ : B₁.PosDef) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • B₀⁻¹ + t • B₁⁻¹)⁻¹ ≤ (1 - t) • B₀ + t • B₁ :=
  matrix_amhm h₀ h₁ ht0 ht1

end Matrix

end Komlos.Literature
