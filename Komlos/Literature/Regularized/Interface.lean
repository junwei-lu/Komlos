import Komlos.Literature.PLaplacian.KorevaarSmoothedProfile
import Komlos.Literature.PLaplacian.KorevaarEntropy
import Komlos.Literature.PLaplacian.Rayleigh
import Komlos.Literature.Sobolev.Defs

/-!
# The regularized closure route: definitions

This is the interface file of the regularized route described in `REGULARIZED_ROUTE.md`
(lane `L0`), in the formulation of **Revision 2** of that document.  It fixes, once and for
all, the objects the other lanes (`L1`–`L5`) produce and consume.

Until the integration pass (lane `L7`) this file also carried the eight *frozen lane
statements* as named `sorry`s.  They are now all proved, each in the file that owns it
(`VariationalExistence`, `VariationalUnique`, `VariationalBound`, `VariationalEuler`,
`Positivity`, `Interior`, `LogConcave`, `Assembly`), and the placeholders were deleted;
this module contains **definitions only**.

## Revision 2: exponent `2` and an abstract uniformly elliptic profile

Revision 2 substitutes `w = u^{p/2}` and thereby runs the whole variational, regularity,
Korevaar and Wang–Xia machinery at the **single exponent `p = 2`**, with a profile that is
*globally* uniformly elliptic rather than merely locally so.  Concretely:

* the profile is no longer `Korevaar.smoothedProfile p F ρ` but an abstract `Ψ` satisfying
  `IsRegProfile Ψ`: `C^∞`, even, convex, and with `c ‖ξ‖² ≤ ⟪D(∇Ψ)(q) ξ, ξ⟫ ≤ C ‖ξ‖²` for
  constants `0 < c` and `C` that do not depend on `q`.  Lane `L6` constructs such profiles
  from `F` and `p` (`Φ_R(q) = h_R(F q)` mollified, with `h_R` continued past `R` with
  constant second derivative); the exponent `p` and the norm `F` therefore appear only in
  `L6`.  Elementary consequences of `IsRegProfile` are proved in
  `Komlos/Literature/Regularized/ProfileBasic.lean`.
* every lane statement takes `(hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K)`
  in place of the former `hp`/`hF`/`hρ`;
* the definitions `regEnergy`, `IsRegAdmissible`, `regMin`, `IsRegMinimizer` and
  `RegEigenData` keep their real exponent parameter `p` (it costs nothing and keeps them
  reusable), but **every theorem is stated at `p = (2 : ℝ)`**.

## Objects

* `IsMollifier ρ ε`: a smooth, nonnegative, even probability kernel supported in
  `closedBall 0 ε`.  It is no longer used by the lane statements; lane `L6` uses it to
  build profiles, and `Komlos/Literature/Regularized/Profile.lean` collects the facts about
  `Korevaar.smoothedProfile p F ρ`.
* `IsRegProfile Ψ`: the profile class of Revision 2 (see above).
* `regEnergy p κ Ψ u = ∫ u^p Ψ(∇u/u) + (κ/p) ∫ u^p log u`, with the *weak* gradient of
  `Komlos/Literature/Sobolev/Defs.lean`.  The densities are `Korevaar.homogeneousDensity`
  and `Korevaar.entropyPotential`; their junk value at `u = 0` is `0`, which is a.e.
  correct because a weak gradient vanishes a.e. on `{u = 0}`.  At `p = 2` this is
  `E(w) = ∫ w² Ψ(∇w/w) + (κ/2) ∫ w² log w`.
* `IsRegAdmissible p K u`: `u ∈ W₀^{1,p}(K)`, `u ≥ 0`, `u = 0` off `K`, `∫ u^p = 1`.  The
  normalization is written with `Real.rpow`; at `p = 2` the natural-number-power form
  `∫ u^2 = 1` is `IsRegAdmissible.integral_sq`, which consumers should prefer.
* `regMin p κ Ψ K`: the infimum of `regEnergy` over admissible competitors, written with the
  *subtype* index (as `lambdaGen`, so that an empty competitor class gives the value `0`
  rather than a `Prop`-bounded `⨅` collapsing to `0` on every non-competitor).
* `IsRegMinimizer`, `RegEigenData`: a minimizer, and the classical data extracted from it.

## The constant in `RegEigenData.equation`

`Korevaar.log_equation_of_entropy_euler_lagrange` produces, for `v = -log u`,
`div ∇Ψ(∇v) = κ v + (Λ - κ/p) + p (⟪∇Ψ(∇v), ∇v⟫ - Ψ(∇v))`,
where `Λ` is the Lagrange multiplier normalized so that the weak Euler–Lagrange equation
reads `DE(u)[ψ] = Λ ∫ u^{p-1} ψ` (the constraint `∫ u^p = 1` has derivative
`p ∫ u^{p-1} ψ`, so `Λ` is `p` times the naive multiplier).  Testing that equation with
`ψ = u` identifies `Λ`; the computation, done by hand, is:

* the kinetic density `D(u, ξ) = u^p Ψ(ξ/u)` is jointly `p`-homogeneous, so Euler's
  relation gives `u D_u(u,∇u) + ⟪D_ξ(u,∇u), ∇u⟫ = p D(u,∇u)`; integrating,
  `∫ ⟪D_ξ, ∇u⟫ + ∫ D_u · u = p ∫ D(u, ∇u)`, i.e. `p` times the kinetic part of the energy;
* `P(u) = (κ/p) u^p log u` has `P'(u) = u^{p-1} (κ log u + κ/p)`
  (`Korevaar.hasDerivAt_entropyPotential`), so `P'(u) · u = κ u^p log u + (κ/p) u^p
  = p P(u) + (κ/p) u^p`; integrating and using `∫ u^p = 1`, this is `p` times the entropy
  part of the energy plus `κ/p`;
* the right-hand side is `Λ ∫ u^{p-1} · u = Λ ∫ u^p = Λ`.

Hence `Λ = p · regEnergy p κ Ψ u + κ/p = p · regMin p κ Ψ K + κ/p`, and the constant
appearing in the transformed equation is `Λ - κ/p = p · regMin p κ Ψ K`.

**At `p = 2` this was re-verified by hand**: the kinetic density `D(u, ξ) = u² Ψ(ξ/u)` is
jointly `2`-homogeneous, `P(u) = (κ/2) u² log u` has `P'(u) · u = 2 P(u) + (κ/2) u²`, and
the constraint derivative is `2 ∫ u ψ`.  So

`Λ = 2 · regMin 2 κ Ψ K + κ/2`,

and the transformed equation reads
`div ∇Ψ(∇v) = κ v + 2 m(K) + 2 (⟪∇Ψ(∇v), ∇v⟫ - Ψ(∇v))`,
which is exactly `RegEigenData.equation` instantiated at `p = 2`.  In
`IsRegMinimizer.weak_euler_lagrange` the right-hand side `Λ ∫ u^{p-1} ψ` is written at
`p = 2` as `Λ ∫ u ψ` (`Real.rpow_one`).

-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Mollifiers -/

/-- Mollifier of radius `ε`: a smooth, nonnegative, even probability density supported in
`closedBall 0 ε`. -/
structure IsMollifier (ρ : Euc d → ℝ) (ε : ℝ) : Prop where
  /-- `ρ` is `C^∞`. -/
  contDiff : ContDiff ℝ ∞ ρ
  /-- `ρ` is nonnegative. -/
  nonneg : ∀ x, 0 ≤ ρ x
  /-- `ρ` is even. -/
  even : ∀ x, ρ (-x) = ρ x
  /-- `ρ` has unit mass. -/
  integral_eq_one : ∫ x, ρ x = 1
  /-- `ρ` is supported in the closed ball of radius `ε`. -/
  tsupport_subset : tsupport ρ ⊆ Metric.closedBall 0 ε
  /-- The radius is positive. -/
  eps_pos : 0 < ε

/-! ### The profile class of Revision 2 -/

/-- **The regularized profile class** (`REGULARIZED_ROUTE.md`, Revision 2): a smooth, even,
convex kinetic profile whose second derivative is *globally* two-sidedly bounded,
`c ‖ξ‖² ≤ ⟪D(∇Ψ)(q) ξ, ξ⟫ ≤ C ‖ξ‖²` with `c > 0`.

This replaces `Korevaar.smoothedProfile p F ρ` in the interface: it is exactly what makes
the `w`-equation uniformly elliptic with standard quadratic growth, so that no local
Lipschitz bound for the minimizer is needed before the interior `C²` theory.  Lane `L6`
constructs profiles of this class out of a smooth strictly convex norm `F` and an exponent
`p > 1`.  Consequences of the definition are collected in
`Komlos/Literature/Regularized/ProfileBasic.lean`. -/
structure IsRegProfile (Ψ : Euc d → ℝ) : Prop where
  /-- `Ψ` is `C^∞`. -/
  contDiff : ContDiff ℝ ∞ Ψ
  /-- `Ψ` is even. -/
  even : ∀ q, Ψ (-q) = Ψ q
  /-- `Ψ` is convex. -/
  convexOn : ConvexOn ℝ Set.univ Ψ
  /-- `D²Ψ` is globally two-sidedly bounded, with a positive lower constant. -/
  elliptic : ∃ c C : ℝ, 0 < c ∧ ∀ q ξ : Euc d,
    c * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫ ∧ ⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫ ≤ C * ‖ξ‖ ^ 2

/-! ### The regularized energy -/

/-- The regularized energy `E(u) = ∫ u^p Ψ(∇u/u) + (κ/p) ∫ u^p log u`, written with the weak
gradient `weakGrad u`.  Both densities take the junk value `0` at `u = 0`, which is a.e.
correct because a weak gradient vanishes a.e. on `{u = 0}`.  Revision 2 uses it at `p = 2`
only. -/
noncomputable def regEnergy (p κ : ℝ) (Ψ : Euc d → ℝ) (u : Euc d → ℝ) : ℝ :=
  (∫ x, Korevaar.homogeneousDensity p Ψ (u x) (weakGrad u x)) +
    ∫ x, Korevaar.entropyPotential p κ (u x)

/-- Admissible competitors for `regEnergy`: nonnegative elements of `W₀^{1,p}(K)` vanishing
off `K` and normalized by `∫ u^p = 1`. -/
structure IsRegAdmissible (p : ℝ) (K : Set (Euc d)) (u : Euc d → ℝ) : Prop where
  /-- `u ∈ W₀^{1,p}(K)`. -/
  memW0 : MemW0 p K u
  /-- `u` is nonnegative. -/
  nonneg : ∀ x, 0 ≤ u x
  /-- `u` vanishes off `K`. -/
  eq_zero_of_notMem : ∀ x, x ∉ K → u x = 0
  /-- `u` is normalized in `L^p`. -/
  integral_rpow : ∫ x, u x ^ p = 1

/-- At `p = 2`, the normalization written with the natural-number power.  This is the form
consumers should use; `IsRegAdmissible.integral_rpow` carries the `Real.rpow` version. -/
theorem IsRegAdmissible.integral_sq {K : Set (Euc d)} {u : Euc d → ℝ}
    (hu : IsRegAdmissible 2 K u) : ∫ x, u x ^ 2 = 1 := by
  rw [← hu.integral_rpow]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show u x ^ 2 = u x ^ (2 : ℝ)
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The regularized minimum `m(K)`, over the subtype of admissible competitors (as
`Komlos.lambdaGen`; the value is `0` when there is no competitor). -/
noncomputable def regMin (p κ : ℝ) (Ψ : Euc d → ℝ) (K : Set (Euc d)) : ℝ :=
  ⨅ u : {u : Euc d → ℝ // IsRegAdmissible p K u}, regEnergy p κ Ψ u.1

/-- A minimizer of `regEnergy` in the admissible class.  The `bddBelow` field records that the
infimum is attained rather than being the junk value of an unbounded `⨅`. -/
structure IsRegMinimizer (p κ : ℝ) (Ψ : Euc d → ℝ) (K : Set (Euc d)) (u : Euc d → ℝ) : Prop
    extends IsRegAdmissible p K u where
  /-- `u` attains the infimum. -/
  energy_eq : regEnergy p κ Ψ u = regMin p κ Ψ K
  /-- The competitor energies are bounded below. -/
  bddBelow :
    BddBelow (Set.range fun w : {w : Euc d → ℝ // IsRegAdmissible p K w} => regEnergy p κ Ψ w.1)

/-- The classical data every consumer of the regularized route uses: a positive continuous
representative of the minimizer whose negative logarithm is `C²` on `K` and solves the
transformed (logarithmic) equation pointwise.

The constant `p * regMin p κ Ψ K` in `equation` is `Λ - κ/p` with `Λ` the multiplier of
`IsRegMinimizer.weak_euler_lagrange`; see the module docstring for the by-hand computation
identifying `Λ = p * regMin p κ Ψ K + κ / p`, which was verified by testing the weak
Euler–Lagrange equation with `ψ = u` and Euler's relation for the `p`-homogeneous kinetic
density (paper Appendix A; `Korevaar.log_equation_of_entropy_euler_lagrange`).  At `p = 2`,
the only instance Revision 2 uses, `equation` reads
`div ∇Ψ(∇v) = κ v + 2 m(K) + 2 (⟪∇Ψ(∇v), ∇v⟫ - Ψ(∇v))`. -/
structure RegEigenData (p κ : ℝ) (Ψ : Euc d → ℝ) (K : Set (Euc d)) where
  /-- The continuous representative. -/
  φ : Euc d → ℝ
  /-- It is continuous. -/
  continuous : Continuous φ
  /-- It vanishes off `K`. -/
  eq_zero_of_notMem : ∀ x, x ∉ K → φ x = 0
  /-- It is positive on `K`. -/
  pos : ∀ x ∈ K, 0 < φ x
  /-- It minimizes the regularized energy. -/
  isRegMinimizer : IsRegMinimizer p κ Ψ K φ
  /-- `v = -log φ` is `C²` on `K`. -/
  contDiffOn_two : ContDiffOn ℝ 2 (fun x => -Real.log (φ x)) K
  /-- `v = -log φ` solves `div ∇Ψ(∇v) = κ v + p m(K) + p (⟪∇Ψ(∇v), ∇v⟫ - Ψ(∇v))` on `K`. -/
  equation : ∀ x ∈ K,
    Korevaar.divergence (fun y => gradient Ψ (gradient (fun z => -Real.log (φ z)) y)) x =
      κ * (-Real.log (φ x)) + p * regMin p κ Ψ K +
        p * (⟪gradient Ψ (gradient (fun z => -Real.log (φ z)) x),
              gradient (fun z => -Real.log (φ z)) x⟫ -
            Ψ (gradient (fun z => -Real.log (φ z)) x))

end Komlos.Literature.Regularized
