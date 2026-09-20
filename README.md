# The Komlós Conjecture — a Lean 4 formalization

A complete, machine-checked proof of the main results of the paper "Vector Balancing via
Directional Total Variation" by Shengtao Guo, Ethan X. Fang, Junwei Lu,
[https://arxiv.org/abs/2609.11189](https://arxiv.org/abs/2609.11189), formalized in Lean 4 over
[Mathlib](https://github.com/leanprover-community/mathlib4). This proves the
[Komlós conjecture](https://en.wikipedia.org/wiki/Discrepancy_of_hypergraphs)
with the explicit constant $3\sqrt{2\pi}$, and the square-root dependence in the Beck–Fiala
conjecture. The library compiles with **zero `sorry`** and the headline theorems depend only on
Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## The Komlós Conjecture

For a real $m \times n$ matrix $A$ with columns $v_1, \dots, v_n$, the discrepancy is
$\mathrm{disc}(A) = \min_{\varepsilon \in \{-1,1\}^n} \| \sum_j \varepsilon_j v_j \|_\infty$.
Komlós conjectured that $\mathrm{disc}(A)$ is bounded by a universal constant whenever every
column has Euclidean norm at most one — with no restriction on the dimension $m$ or on the number
of vectors $n$. The theorem proved here: for all positive integers $m, n$ and all
$v_1, \dots, v_n \in \mathbb{R}^m$ with $\|v_j\|_2 \le 1$ there are signs
$\varepsilon_1, \dots, \varepsilon_n \in \{-1, 1\}$ with

$$\Big\| \sum_{j=1}^n \varepsilon_j v_j \Big\|_\infty < 3\sqrt{2\pi}.$$

As a consequence (Beck–Fiala), if $A \in \{0,1\}^{m \times n}$ has at most $t$ nonzero entries in
each column, then $\mathrm{disc}(A) < 3\sqrt{2\pi t}$.

The formalization follows the proof of

- S. Guo, E. X. Fang, J. Lu, *Vector Balancing via Directional Total Variation* (paper item
  numbers are cited in the docstrings, e.g. `(paper Lemma 3.4)`),

whose Appendix A (convexity of the anisotropic $p$-Laplace eigenvalue along Minkowski
combinations, Proposition A.1) builds on

- G. Wang, C. Xia, *A Brunn–Minkowski inequality for a Finsler-Laplacian*, 2011 (the
  infimal-convolution method), and
- N. Korevaar, *Convex solutions to nonlinear elliptic and parabolic boundary value problems*,
  1983 (the concavity maximum principle).


## Where the main theorem is

The headline statements are in [`Komlos/Main.lean`](Komlos/Main.lean):

```lean
theorem komlos (m n : ℕ) (v : Fin n → Fin m → ℝ) (hv : ∀ j, ∑ i, v j i ^ 2 ≤ 1) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |∑ j, ε j * v j i| < 3 * Real.sqrt (2 * Real.pi)

theorem beck_fiala (m n t : ℕ) (ht : 0 < t) (A : Fin m → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hcol : ∀ j, (Finset.univ.filter fun i => A i j ≠ 0).card ≤ t) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |∑ j, A i j * ε j| < 3 * Real.sqrt (2 * Real.pi * t)
```

together with the equivalent forms `komlos_euclidean` (vectors in `EuclideanSpace`) and
`komlos_supNorm` (the sup norm of `Fin m → ℝ`). The statement of `komlos` is deliberately
elementary — finite sums of real numbers, no measure theory, no project-specific definitions —
so it can be audited without trusting any of the proof machinery. The primitive definitions used
by the intermediate results (the open-set Banaszczyk transform, directional variation, the
class of convex bodies) live in [`Komlos/Defs.lean`](Komlos/Defs.lean).

Rough module map (paper tags in docstrings):
`Defs`, `Variation`, `Transform` (directional total variation and the Banaszczyk transform) →
`CubeDensity` (the cube density, paper Lemma 2.4) → `Compactness`, `Cheeger`, `Eigenvalue`,
`EigenvalueLimit`, `EigenvalueConvex` (anisotropic Cheeger constants as $p \downarrow 1$ limits of
$p$-Laplace eigenvalues; Minkowski convexity, paper Lemma 3.2) → `CommonDensity`, `Section`
(prescribed sections, paper Lemmas 3.3–3.4) → `Lift`, `Rearrangement`, `Height`, `Stability`
(the geometric lift and finite-step stability, paper Section 4) → `Signing` → `Main`
(paper Theorem 1.1 and Corollary 1.2).
The analytic substrate of Proposition A.1 is under `Literature/`: `Sobolev/*` (weak gradients,
density, mollification, Rellich), `PLaplacian/*` (Rayleigh quotients, linear regularity: Weyl's
lemma, Campanato, Schauder), `WangXia/*` (infimal convolution, matrix AM–HM), and
`Regularized/*` (the regularized route: `Variational*`, `DeGiorgi*`, `Positivity*`, `Interior*`,
`Korevaar2`, `DomainLimit*`, `LogConcave`, `PrekopaLeindler`, `Assembly*`, `TruncatedProfile*`,
`ScalarLimit*`, `EigenvalueConvexityReg`).

## How to certify the proof

Prerequisites: [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager). The
pinned toolchain (`lean-toolchain`, Lean `v4.33.0`, Mathlib `v4.33.0`) is installed automatically
on first build.

```bash
git clone https://github.com/junwei-lu/Komlos.git
cd Komlos
lake exe cache get    # download the prebuilt Mathlib cache (avoids compiling Mathlib)
lake build            # compile the whole library (~80k lines of Lean; allow about an hour)
```

`lake build` must finish with no errors **and no `declaration uses 'sorry'` warnings** — the
library contains none (`grep -rnE "^\s*sorry\s*$|:= sorry|by sorry" Komlos/` returns nothing;
the word appears only in comments). As a hard gate, the module `Komlos/AxiomCheck.lean` *fails to
compile* if `sorryAx` is reachable from any headline theorem:

```bash
lake build Komlos.AxiomCheck
```

Then check the axiom footprint of the main results:

```bash
lake env lean AxiomsCheck.lean
```

Expected output — every listed theorem, including the headline, reports exactly Lean's three
standard axioms:

```
'Komlos.komlos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Komlos.komlos_euclidean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Komlos.komlos_supNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Komlos.beck_fiala' depends on axioms: [propext, Classical.choice, Quot.sound]
'Komlos.eigenvalue_convexity' depends on axioms: [propext, Classical.choice, Quot.sound]
...
```

No `axiom` or `admit` appears anywhere in the repository, so this output certifies that the
theorem is proved unconditionally within Lean's standard foundations.
