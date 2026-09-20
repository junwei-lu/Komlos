/-
Copyright (c) 2026 Komlos formalization contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Komlos

/-!
# Axiom audit — the zero-`sorry` gate

This module is the acceptance gate for the formalization of Guo–Fang–Lu,
*Vector Balancing via Directional Total Variation* (arXiv:2609.11189): it asserts
that the paper's main results depend on **no** `sorryAx`. Whether it currently passes is
recorded in `SORRIES.md`.

`assert_no_sorry` (`Mathlib/Util/AssertNoSorry.lean`) traverses the full transitive
axiom cone of a declaration and **throws an elaboration error** if `sorryAx` occurs.
So `lake build Komlos.AxiomCheck` *fails* while any `sorry` remains reachable from
the main theorem — the "no sorry" claim is enforced by the build, not asserted by hand.

The `#print axioms` lines are informative; the expected output for each is
`[propext, Classical.choice, Quot.sound]` — the three standard Lean axioms — and
notably **not** `sorryAx`.

This file is deliberately **not** imported by `Komlos.lean`: it is the final
verification target, built explicitly on the cluster:

```
lake build Komlos.AxiomCheck
```

## Endpoints audited

* `Komlos.komlos` — paper Theorem 1.1 (coordinate form), the headline Komlós bound.
* `Komlos.komlos_euclidean` — paper Theorem 1.1 (Euclidean-space form).
* `Komlos.komlos_supNorm` — paper Theorem 1.1 (sup-norm form).
* `Komlos.beck_fiala` — paper Corollary 1.2.
* `Komlos.eigenvalue_convexity` — paper (3.8) / Proposition A.1 = Wang–Xia 2011, Theorem 1.2;
  this was the last reduction target of Phase A and the root of the whole literature tree.
* `Komlos.Literature.exists_interior_gradient_holder_scaled` — the formerly admitted
  auxiliary scaled Schauder estimate. The uniform freezing proof now uses it;
  it is also audited explicitly to preserve coverage of this former independent gap.
* `Komlos.Literature.eigenvalue_convexity_gen` — paper Proposition A.1 for a smooth strictly
  convex norm (`WangXia/EigenvalueConvexGen.lean`), the single Appendix A input of
  `Komlos.eigenvalue_convexity`.
* `Komlos.Literature.Regularized.eigenvalue_convexity_gen_reg` — its proof along the
  regularized route of `REGULARIZED_ROUTE.md` (Revision 2); see the **DEVIATION** recorded
  in `Komlos/Literature/Regularized/NOTES_integrate.md`.
* `Komlos.Literature.Regularized.exists_regMin_convexity_const` (lane `L5`) and
  `Komlos.Literature.Regularized.tendsto_regMin` (lane `L6`) — the two inputs of the
  regularized endpoint, audited separately so that a failure is localized.
-/

-- Informative: exactly which sorried declarations the main results still depend on.
-- (`#print sorries` walks the transitive cone; it never fails, so it stays useful while the
-- gate below is red.)
#print sorries Komlos.komlos
#print sorries Komlos.eigenvalue_convexity
#print sorries Komlos.Literature.exists_interior_gradient_holder_scaled
#print sorries Komlos.Literature.Regularized.eigenvalue_convexity_gen_reg
#print sorries Komlos.Literature.Regularized.exists_regMin_convexity_const
#print sorries Komlos.Literature.Regularized.tendsto_regMin

-- Informative: the full axiom cone of each endpoint.
#print axioms Komlos.komlos
#print axioms Komlos.komlos_euclidean
#print axioms Komlos.komlos_supNorm
#print axioms Komlos.beck_fiala
#print axioms Komlos.eigenvalue_convexity
#print axioms Komlos.Literature.exists_interior_gradient_holder_scaled
#print axioms Komlos.Literature.eigenvalue_convexity_gen
#print axioms Komlos.Literature.Regularized.eigenvalue_convexity_gen_reg

-- The hard gate: each of these fails to elaborate if `sorryAx` is reachable.
assert_no_sorry Komlos.komlos
assert_no_sorry Komlos.komlos_euclidean
assert_no_sorry Komlos.komlos_supNorm
assert_no_sorry Komlos.beck_fiala
assert_no_sorry Komlos.eigenvalue_convexity
assert_no_sorry Komlos.Literature.exists_interior_gradient_holder_scaled
assert_no_sorry Komlos.Literature.eigenvalue_convexity_gen
assert_no_sorry Komlos.Literature.Regularized.eigenvalue_convexity_gen_reg
assert_no_sorry Komlos.Literature.Regularized.exists_regMin_convexity_const
assert_no_sorry Komlos.Literature.Regularized.tendsto_regMin
