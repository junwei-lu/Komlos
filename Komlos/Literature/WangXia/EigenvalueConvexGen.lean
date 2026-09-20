import Komlos.Literature.Regularized.EigenvalueConvexityReg

/-!
# Paper Proposition A.1: eigenvalue convexity for smooth strictly convex norms

This module holds `Komlos.Literature.eigenvalue_convexity_gen`, the statement the paper's
Appendix A needs and the only Wang–Xia result the main theorem consumes
(`Komlos/EigenvalueConvex.lean`).

**DEVIATION from paper Appendix A (regularized route, `REGULARIZED_ROUTE.md` Revision 2).**
The paper proves this proposition by running Wang–Xia's infimal-convolution argument on the
*degenerate* `p`-Laplacian eigenfunctions, which needs their `C^{1,α}` regularity and
Korevaar's concavity maximum principle (`mrs_regularity`, `mrs_logConcave`).  Here the proof
is `Komlos.Literature.Regularized.eigenvalue_convexity_gen_reg`: the same two arguments are
run on a *smooth, uniformly elliptic* regularization `Ψ` of `F^p/p` at exponent `2`, where
the regularity theory is classical, and only the scalar minima `m(K) = regMin 2 κ Ψ K` are
passed to the limit `ε, κ → 0`.  The statement is unchanged.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-- **Eigenvalue convexity for smooth strictly convex norms** (paper Proposition A.1 = Wang–Xia
2011, Theorem 1.2): for `1 < p`, a norm `F` smooth away from `0` with `D²(F²) ≻ 0` there, and
nonempty bounded open convex `K₀, K₁`,
`λ_{p,F}((1-t)K₀ + tK₁) ≤ (1-t) λ_{p,F}(K₀) + t λ_{p,F}(K₁)` for `0 ≤ t ≤ 1`. -/
theorem eigenvalue_convexity_gen {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K₀ K₁ : Set (Euc d)} (hK₀ : IsGoodConvex K₀)
    (hK₁ : IsGoodConvex K₁) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    lambdaGen p F ((1 - t) • K₀ + t • K₁) ≤ (1 - t) * lambdaGen p F K₀ + t * lambdaGen p F K₁ :=
  Regularized.eigenvalue_convexity_gen_reg hp hF hK₀ hK₁ ht₀ ht₁

end Komlos.Literature
