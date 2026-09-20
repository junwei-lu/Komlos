import Komlos.Eigenvalue
import Komlos.Literature.WangXia.EigenvalueConvexGen
import Komlos.Literature.PLaplacian.MixtureNorm

/-!
# Eigenvalue convexity (Wang–Xia 2011, Theorem 1.2)

`eigenvalue_convexity` is paper (3.8) / Proposition A.1. It is deduced from the general-integrand
statement `Komlos.Literature.eigenvalue_convexity_gen` (paper Proposition A.1 for a smooth
strictly convex norm, assembled in `Komlos/Literature/WangXia/EigenvalueConvexAssembly.lean`
from the eigenfunction data of Mosconi–Riey–Squassina 2024) applied to the regularized mixture
integrands `H_ε` (paper Lemma 3.2, last paragraph), followed by the limit `ε ↓ 0`
(`lambdaMix_convex_of_Heps`). See `SORRIES.md` for the remaining open inputs of Phase B.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ} {N : ℕ} {α : Fin N → ℝ} {u : Fin N → Euc d}

/-- **Eigenvalue convexity** (paper (3.8), Proposition A.1 = Wang–Xia 2011, Theorem 1.2): the
anisotropic `p`-eigenvalue is convex along Minkowski combinations of convex bodies.

Proof: for every `ε > 0` the regularized integrand `H_ε` is a smooth strictly convex norm
(`Heps_isSmoothStrictNorm`), so `eigenvalue_convexity_gen` gives the inequality for
`lambdaGen p (Heps ε α u)`; the limit `ε ↓ 0` is `lambdaMix_convex_of_Heps`. -/
theorem eigenvalue_convexity (hmix : IsMixture α u) {p : ℝ} (hp : 1 < p) {K₀ K₁ : Set (Euc d)}
    (hK₀ : IsGoodConvex K₀) (hK₁ : IsGoodConvex K₁) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    lambdaMix p α u ((1 - t) • K₀ + t • K₁) ≤
      (1 - t) * lambdaMix p α u K₀ + t * lambdaMix p α u K₁ :=
  lambdaMix_convex_of_Heps hmix hp <| by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Literature.eigenvalue_convexity_gen hp (Literature.Heps_isSmoothStrictNorm hmix hε)
      hK₀ hK₁ ht₀ ht₁

end Komlos
