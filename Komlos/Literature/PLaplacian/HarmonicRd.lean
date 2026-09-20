import Komlos.Literature.PLaplacian.SchauderHarmonic
import Komlos.Literature.PLaplacian.FrozenDirichlet

-- `FrozenDirichlet` is not used below; it is imported here only so that the module is
-- part of the library's import graph (`HarmonicRd` is the leaf of the Schauder chain).
-- Its intended final home is an import in `SchauderHarmonic.lean`, so that the `L²` frozen
-- Dirichlet replacement proved there can be consumed by `exists_frozen_replacement_data`.
-- That is NOT yet the case: `FrozenDirichlet` is not in `SchauderHarmonic`'s import closure
-- (both it and `HarmonicMVP` import `FrozenComparison`, and this file imports both), and the
-- missing step is Weyl regularity — nothing in the repository upgrades the minimizer's `L²`
-- field to the gradient of a `C¹` function.

/-!
# The square root of a constant symmetric elliptic coefficient matrix

`Komlos.Literature.PLaplacian.SchauderHarmonic` reduces the constant-coefficient equation
`div (A₀ ∇w) = 0` to the Laplace equation through the linear change of variables `y = A₀^{1/2} x`
(`isWeaklyHarmonicOn_comp_of_isWeakConstSolutionOn`): all that is needed is a **self-adjoint
linear isomorphism `L` with `L ∘ L = A₀`**.  This file constructs `L` for a symmetric
`μ`-elliptic `A₀`, so that the reduction step of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Theorem 8.32 is available in full.

Mathlib has no continuous functional calculus for real operator algebras
(`ContinuousFunctionalCalculus ℝ A IsSelfAdjoint` is built from a *complex* C\*-algebra
structure), but it does have one for **real matrices**,
`Matrix.IsHermitian.instContinuousFunctionalCalculus`.  The construction therefore transports
`A₀` to `Matrix (Fin d) (Fin d) ℝ` along the star algebra equivalence `Matrix.toEuclideanCLM`,
takes `CFC.sqrt` there, and transports back.  This is the same route as
`Komlos.Literature.matrix_amhm` in `Komlos/Literature/WangXia/MatrixAMHM.lean`.

## Main results

* `exists_sqrt_of_symmetric_elliptic`: a symmetric `μ`-elliptic `A₀ : Euc d →L[ℝ] Euc d` has a
  self-adjoint square root `L : Euc d ≃L[ℝ] Euc d`, `L ∘ L = A₀`.
* `norm_sq_apply_of_sq_eq`, `sqrt_mul_norm_le_norm_apply`: `‖L v‖² = ⟪A₀ v, v⟫`, hence
  `√μ ‖v‖ ≤ ‖L v‖`; this is the quantitative control on the distortion of balls under the change
  of variables.
* `exists_comp_isWeaklyHarmonicOn_of_isWeakConstSolutionOn`: the resulting **complete reduction**
  of a symmetric constant-coefficient weak solution to a weakly harmonic function.
-/

open MeasureTheory Set Filter Topology InnerProductSpace

open scoped RealInnerProductSpace MatrixOrder

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Positivity of a symmetric elliptic coefficient matrix -/

/-- A symmetric `μ`-elliptic constant coefficient operator is a positive operator in the sense of
`LinearMap.IsPositive`. -/
theorem isPositive_of_symmetric_elliptic {μ : ℝ} (hμ : 0 < μ) (A₀ : Euc d →L[ℝ] Euc d)
    (hsymm : ∀ u v : Euc d, ⟪A₀ u, v⟫ = ⟪u, A₀ v⟫)
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) :
    (A₀ : Euc d →ₗ[ℝ] Euc d).IsPositive := by
  refine ⟨fun u v => hsymm u v, fun v => ?_⟩
  have h1 : (0 : ℝ) ≤ μ * ‖v‖ ^ 2 := mul_nonneg hμ.le (sq_nonneg _)
  have h2 : (0 : ℝ) ≤ ⟪A₀ v, v⟫ := h1.trans (hell v)
  simpa using h2

/-! ### The square root -/

/-- **The square root of a constant symmetric positive-definite coefficient matrix**
(Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 8.32,
step 1).  A symmetric `μ`-elliptic `A₀ : Euc d →L[ℝ] Euc d` factors as `A₀ = L ∘ L` with `L` a
self-adjoint linear isomorphism of `Euc d`.

The construction transports `A₀` to a real matrix along the star algebra equivalence
`Matrix.toEuclideanCLM`, where Mathlib's continuous functional calculus for Hermitian matrices
supplies `CFC.sqrt`; invertibility of the resulting `L` comes from `‖L v‖² = ⟪A₀ v, v⟫ ≥ μ‖v‖²`
and the finite-dimensional equivalence of injectivity and surjectivity. -/
theorem exists_sqrt_of_symmetric_elliptic {μ : ℝ} (hμ : 0 < μ) (A₀ : Euc d →L[ℝ] Euc d)
    (hsymm : ∀ u v : Euc d, ⟪A₀ u, v⟫ = ⟪u, A₀ v⟫)
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) :
    ∃ L : Euc d ≃L[ℝ] Euc d, (∀ u v : Euc d, ⟪L u, v⟫ = ⟪u, L v⟫) ∧
      ∀ v : Euc d, L (L v) = A₀ v := by
  classical
  -- the matrix of `A₀` in the standard orthonormal basis of `Euc d`
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) ℝ, Matrix.toEuclideanCLM (𝕜 := ℝ) M = A₀ :=
    ⟨(Matrix.toEuclideanCLM (𝕜 := ℝ)).symm A₀,
      (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply A₀⟩
  have hlin : Matrix.toEuclideanLin M = (A₀ : Euc d →ₗ[ℝ] Euc d) := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, hM]
  have hMpsd : M.PosSemidef := by
    refine Matrix.isPositive_toEuclideanLin_iff.1 ?_
    rw [hlin]
    exact isPositive_of_symmetric_elliptic hμ A₀ hsymm hell
  -- its (matrix) square root, via the continuous functional calculus for Hermitian matrices
  obtain ⟨S, hS0, hSS⟩ : ∃ S : Matrix (Fin d) (Fin d) ℝ, 0 ≤ S ∧ S * S = M :=
    ⟨CFC.sqrt M, CFC.sqrt_nonneg M, CFC.sqrt_mul_sqrt_self M hMpsd.nonneg⟩
  obtain ⟨L, hL⟩ : ∃ L : Euc d →L[ℝ] Euc d, Matrix.toEuclideanCLM (𝕜 := ℝ) S = L := ⟨_, rfl⟩
  -- `L ∘ L = A₀`
  have hmul : L * L = A₀ := by
    rw [← hL, ← map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ)) S S, hSS]
    exact hM
  have hLL : ∀ v : Euc d, L (L v) = A₀ v := by
    intro v
    calc L (L v) = (L * L) v := rfl
      _ = A₀ v := by rw [hmul]
  -- `L` is self-adjoint
  have hLsa : IsSelfAdjoint L := by
    rw [← hL]
    exact (IsSelfAdjoint.of_nonneg hS0).map (Matrix.toEuclideanCLM (𝕜 := ℝ))
  have hLsymm : ∀ u v : Euc d, ⟪L u, v⟫ = ⟪u, L v⟫ := fun u v =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hLsa u v
  -- `L` is injective, hence (finite dimensions) a linear isomorphism
  have hinj : Function.Injective ((L : Euc d →ₗ[ℝ] Euc d)) := by
    intro u v huv
    have huv' : L u = L v := huv
    have hw : L (u - v) = 0 := by rw [map_sub, huv', sub_self]
    have e1 : ⟪A₀ (u - v), u - v⟫ = ⟪L (u - v), L (u - v)⟫ := by
      rw [← hLL (u - v), hLsymm]
    have h1 : ⟪A₀ (u - v), u - v⟫ = (0 : ℝ) := by
      rw [e1, hw, inner_zero_left]
    have h2 : μ * ‖u - v‖ ^ 2 ≤ 0 := by
      have h := hell (u - v)
      rw [h1] at h
      exact h
    have h3 : ‖u - v‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 h3))
  have hsurj : Function.Surjective ((L : Euc d →ₗ[ℝ] Euc d)) :=
    LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨Le, hLe⟩ : ∃ Le : Euc d ≃L[ℝ] Euc d, ∀ w : Euc d, Le w = L w :=
    ⟨(LinearEquiv.ofBijective (L : Euc d →ₗ[ℝ] Euc d) ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      fun _ => rfl⟩
  refine ⟨Le, fun u v => ?_, fun v => ?_⟩
  · rw [hLe u, hLe v]
    exact hLsymm u v
  · rw [hLe v, hLe (L v)]
    exact hLL v

/-! ### Distortion of balls under the change of variables -/

/-- If `L` is self-adjoint with `L ∘ L = A₀`, then `‖L v‖² = ⟪A₀ v, v⟫`. -/
theorem norm_sq_apply_of_sq_eq {A₀ : Euc d →L[ℝ] Euc d} {L : Euc d ≃L[ℝ] Euc d}
    (hL : ∀ u v : Euc d, ⟪L u, v⟫ = ⟪u, L v⟫) (hLL : ∀ v : Euc d, L (L v) = A₀ v) (v : Euc d) :
    ‖L v‖ ^ 2 = ⟪A₀ v, v⟫ := by
  rw [← hLL v, hL, real_inner_self_eq_norm_sq]

/-- **The square root of a `μ`-elliptic matrix is bounded below by `√μ`**: `√μ ‖v‖ ≤ ‖L v‖`.
This is the quantitative statement that `L⁻¹` maps a ball of radius `s` into the ball of radius
`s / √μ`, i.e. the control on the distortion of balls in the change of variables
`isWeaklyHarmonicOn_comp_of_isWeakConstSolutionOn`. -/
theorem sqrt_mul_norm_le_norm_apply {μ : ℝ} (hμ : 0 < μ) {A₀ : Euc d →L[ℝ] Euc d}
    {L : Euc d ≃L[ℝ] Euc d} (hL : ∀ u v : Euc d, ⟪L u, v⟫ = ⟪u, L v⟫)
    (hLL : ∀ v : Euc d, L (L v) = A₀ v)
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) (v : Euc d) :
    Real.sqrt μ * ‖v‖ ≤ ‖L v‖ := by
  have hnn : (0 : ℝ) ≤ Real.sqrt μ * ‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h1 : μ * ‖v‖ ^ 2 ≤ ‖L v‖ ^ 2 := by
    rw [norm_sq_apply_of_sq_eq hL hLL v]
    exact hell v
  have h2 : (Real.sqrt μ * ‖v‖) ^ 2 ≤ ‖L v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hμ.le]
    exact h1
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq (norm_nonneg (L v))] at h3

/-! ### The complete reduction to the Laplace equation -/

/-- **Reduction of a symmetric constant-coefficient equation to the Laplace equation**
(Gilbarg–Trudinger, Theorem 8.32, step 1), with the square root supplied by
`exists_sqrt_of_symmetric_elliptic`: if `A₀` is symmetric and `μ`-elliptic and `w` solves
`div (A₀ ∇w) = 0` weakly on the open set `U`, then there is a self-adjoint linear isomorphism `L`
with `L ∘ L = A₀` such that `w ∘ L` is weakly harmonic on `L⁻¹(U)`. -/
theorem exists_comp_isWeaklyHarmonicOn_of_isWeakConstSolutionOn {μ : ℝ} (hμ : 0 < μ)
    (A₀ : Euc d →L[ℝ] Euc d) (hsymm : ∀ u v : Euc d, ⟪A₀ u, v⟫ = ⟪u, A₀ v⟫)
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) {U : Set (Euc d)} (hU : IsOpen U)
    {w : Euc d → ℝ} (hwd : ContDiffOn ℝ 1 w U) (hw : IsWeakConstSolutionOn A₀ U w) :
    ∃ L : Euc d ≃L[ℝ] Euc d, (∀ u v : Euc d, ⟪L u, v⟫ = ⟪u, L v⟫) ∧
      (∀ v : Euc d, L (L v) = A₀ v) ∧
      IsWeaklyHarmonicOn ((L : Euc d → Euc d) ⁻¹' U) (fun z => w (L z)) := by
  obtain ⟨L, hLsymm, hLL⟩ := exists_sqrt_of_symmetric_elliptic hμ A₀ hsymm hell
  exact ⟨L, hLsymm, hLL,
    isWeaklyHarmonicOn_comp_of_isWeakConstSolutionOn hLsymm hLL hU hwd hw⟩

end Komlos.Literature
