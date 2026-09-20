import Komlos.Literature.Regularized.ScalarLimit
import Komlos.Literature.Regularized.Assembly

/-!
# Eigenvalue convexity via the regularized route

This is the endpoint of the regularized route of `REGULARIZED_ROUTE.md` (Revision 2), lane
`L6`: **paper Proposition A.1** (Wang–Xia 2011, Theorem 1.2) in the form

`λ_{p,F}((1-t)K₀ + tK₁) ≤ (1-t) λ_{p,F}(K₀) + t λ_{p,F}(K₁)`,

proved *without* the degenerate `p`-Laplacian eigenfunction theory.  It rests on exactly two
inputs:

* `exists_regMin_convexity_const` (lane `L5`, `Komlos/Literature/Regularized/Interface.lean`):
  the almost-convexity `m(K_t) ≤ (1-t) m(K₀) + t m(K₁) + C κ` of the regularized minima, with
  an absolute constant `C`;
* `tendsto_regMin` (`Komlos/Literature/Regularized/ScalarLimit.lean`): the scalar limit
  `m_n(K) → λ_{p,F}(K)/p` along the canonical parameter sequence `R = n+1`, `ε = κ = 1/(n+1)`.

The proof is then three lines of limit passage: the almost-convexity holds for every `n` with
the *same* profile `regProfileSeq p F n` for the three bodies, its error term `C κ_n` tends to
`0`, and the three sides converge to `λ/p`; multiplying by `p > 0` removes the `1/p`.

`eigenvalue_convexity_gen_reg` has the statement of
`Komlos.Literature.eigenvalue_convexity_gen`
(`Komlos/Literature/WangXia/EigenvalueConvexAssembly.lean`), whose proof the coordinator
replaces by a one-line call to this theorem; nothing here imports
`EigenfunctionData.lean`, `LogConcave.lean`, `PLaplacian/Regularity.lean`, `KorevaarSMP.lean`
or `DiffQuotCaccioppoli.lean` results (see the report of lane `L6a`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-- **Paper Proposition A.1 via the regularized route.**  Convexity of `K ↦ λ_{p,F}(K)` along
Minkowski combinations of good convex bodies, for a smooth strictly convex norm `F` and
`p > 1`.

The proof passes to the limit in the almost-convexity of the regularized minima
`exists_regMin_convexity_const` along the canonical parameter sequence of
`Komlos/Literature/Regularized/ScalarLimit.lean`. -/
theorem eigenvalue_convexity_gen_reg {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K₀ K₁ : Set (Euc d)} (hK₀ : IsGoodConvex K₀)
    (hK₁ : IsGoodConvex K₁) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    lambdaGen p F ((1 - t) • K₀ + t • K₁) ≤
      (1 - t) * lambdaGen p F K₀ + t * lambdaGen p F K₁ := by
  rcases ht₀.eq_or_lt with rfl | ht₀'
  · simp [zero_smul_set hK₁.nonempty]
  rcases ht₁.eq_or_lt with rfl | ht₁'
  · simp [zero_smul_set hK₀.nonempty]
  have hp0 : (0 : ℝ) < p := by linarith
  have hKt : IsGoodConvex ((1 - t) • K₀ + t • K₁) := isGoodConvex_convexCombo hK₀ hK₁ ht₀' ht₁'
  obtain ⟨C, hC⟩ := exists_regMin_convexity_const (d := d)
  -- the almost-convexity inequality along the canonical sequence
  have hineq : ∀ n : ℕ,
      regMin 2 (regKappa n) (regProfileSeq p F n) ((1 - t) • K₀ + t • K₁) ≤
        (1 - t) * regMin 2 (regKappa n) (regProfileSeq p F n) K₀ +
          t * regMin 2 (regKappa n) (regProfileSeq p F n) K₁ + C * regKappa n :=
    fun n => hC (regKappa n) (regProfileSeq p F n) K₀ K₁ t (regKappa_pos n)
      (isRegProfile_regProfileSeq hp hF n) hK₀ hK₁ ht₀' ht₁'
  -- pass to the limit
  have hlim : lambdaGen p F ((1 - t) • K₀ + t • K₁) / p ≤
      (1 - t) * (lambdaGen p F K₀ / p) + t * (lambdaGen p F K₁ / p) + C * 0 :=
    le_of_tendsto_of_tendsto (tendsto_regMin hp hF hKt)
      ((((tendsto_regMin hp hF hK₀).const_mul (1 - t)).add
        ((tendsto_regMin hp hF hK₁).const_mul t)).add (tendsto_regKappa.const_mul C))
      (Eventually.of_forall hineq)
  rw [mul_zero, add_zero] at hlim
  -- remove the factor `1/p`
  have hdiv : ∀ a b : ℝ, a / p ≤ b / p → a ≤ b := by
    intro a b h
    have h2 := mul_le_mul_of_nonneg_right h hp0.le
    have e1 : a / p * p = a := by field_simp
    have e2 : b / p * p = b := by field_simp
    rwa [e1, e2] at h2
  refine hdiv _ _ ?_
  rw [add_div, mul_div_assoc, mul_div_assoc]
  exact hlim

end Komlos.Literature.Regularized
