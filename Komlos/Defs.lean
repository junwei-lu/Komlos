import Mathlib

/-!
# Komlós vector balancing — basic definitions

Formalization of S. Guo, E. X. Fang, J. Lu, *Vector Balancing via Directional Total
Variation* (arXiv:2609.11189; source in `ref/komlos-variation.tex`).

This file collects the objects of the paper's Sections 2–4:

* `Komlos.IsGoodConvex` — "nonempty, bounded, open, convex";
* `Komlos.transform` — the open-set Banaszczyk transform `𝒯_v K` (paper (2.9));
* `Komlos.dirVar` — the directional variation `V_u f` (paper (2.1), via the
  translation characterisation (3.1));
* `Komlos.IsProbDensityOn`, `Komlos.MemP` — the class `𝒫(K)` of paper §2;
* `Komlos.VarBounded` — the cap `V_u ρ ≤ κ‖u‖₂` (paper (2.8));
* `Komlos.IsMixture`, `Komlos.mixtureEnergy`, `Komlos.cheeger` — the mixture
  integrands (3.6), the energy `E_H` and the Cheeger value `h_H(K)` (paper (3.2));
* `Komlos.lift`, `Komlos.fiberLength`, `Komlos.steiner` — the geometric lift and its
  Steiner symmetral (paper Lemma 4.1);
* `Komlos.liftedDensity`, `Komlos.fiberDist`, `Komlos.symRearr` — the lifted density
  (4.2) and the fiberwise symmetric decreasing rearrangement (4.1).

## Design note on `dirVar`

The paper defines `V_u f` by duality against `C_c^1` test functions (paper (2.1)) and
proves in Lemma 3.1 that, for `f ∈ L¹`,
`V_u f = lim_{h→0} ‖f(·+hu) − f‖₁ / |h|` and `‖f(·+hu) − f‖₁ ≤ |h| V_u f`.
Since `h ↦ ‖f(·+hu) − f‖₁` is subadditive and even, this limit equals
`sup_{h>0} ‖f(·+hu) − f‖₁ / h`.  We *define* `dirVar u f` as that supremum (valued in
`ℝ≥0∞`), which is equivalent to the paper's definition for integrable `f` and makes
every use of `V_u` in the paper (Lemma 3.1, (3.4), Lemma 4.2, Lemma 4.3) a direct
consequence of the definition.  Only the limit statement `Komlos.dirVar_tendsto`
(a Fekete-type argument) needs an extra proof.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

/-- Euclidean space `ℝ^d` with its Euclidean norm and Lebesgue measure. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standing geometric hypothesis of the paper: `K` is nonempty, bounded, open and
convex. -/
structure IsGoodConvex (K : Set E) : Prop where
  nonempty : K.Nonempty
  isBounded : Bornology.IsBounded K
  isOpen : IsOpen K
  convex : Convex ℝ K

/-- The open-set Banaszczyk transform (paper (2.9)):
`𝒯_v K = ((K − v) ∩ (K + v)) + {t v : −2 < t < 2}`. -/
def transform (v : E) (K : Set E) : Set E :=
  ((fun x => x - v) '' K ∩ (fun x => x + v) '' K) + ((fun t : ℝ => t • v) '' Ioo (-2 : ℝ) 2)

end Geometry

section Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]

/-- Directional variation `V_u f` (paper (2.1)), in its translation form (paper (3.1)):
`V_u f = sup_{h > 0} ‖f(· + h u) − f‖₁ / h ∈ [0, ∞]`. -/
noncomputable def dirVar (u : E) (f : E → ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : 0 < h), (∫⁻ x, ‖f (x + h • u) - f x‖ₑ) / ENNReal.ofReal h

/-- A probability density supported (almost everywhere) in `K`: measurable, nonnegative,
integrable, of mass one, vanishing a.e. outside `K`.  This is the paper's `𝒫(K)` without
the `BV` requirement (used for the lifted density `R` of Lemma 3.4). -/
structure IsProbDensityOn (K : Set E) (ρ : E → ℝ) : Prop where
  measurable : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  integrable : Integrable ρ
  integral_eq_one : ∫ x, ρ x = 1
  ae_zero_outside : ∀ᵐ x, x ∉ K → ρ x = 0

/-- The class `𝒫(K)` of the paper (§2): a probability density supported in `K` whose
directional variations are all finite (`ρ ∈ BV(ℝ^d)`). -/
structure MemP (K : Set E) (ρ : E → ℝ) : Prop extends IsProbDensityOn K ρ where
  dirVar_ne_top : ∀ u, dirVar u ρ ≠ ⊤

/-- The variation cap (paper (2.8)): `V_u ρ ≤ κ ‖u‖₂` for every direction `u`. -/
def VarBounded (κ : ℝ) (ρ : E → ℝ) : Prop :=
  ∀ u, dirVar u ρ ≤ ENNReal.ofReal (κ * ‖u‖)

/-- The invariant of the paper (§2): `K` supports some `ρ ∈ 𝒫(K)` satisfying (2.8). -/
def HasAdmissible (K : Set E) (κ : ℝ) : Prop :=
  ∃ ρ, MemP K ρ ∧ VarBounded κ ρ

/-- Mixture data (paper (3.6)): nonnegative weights summing to one and unit directions. -/
structure IsMixture {N : ℕ} (α : Fin N → ℝ) (u : Fin N → E) : Prop where
  nonneg : ∀ l, 0 ≤ α l
  sum_eq_one : ∑ l, α l = 1
  norm_eq_one : ∀ l, ‖u l‖ = 1

/-- The energy `E_H(ρ) = ∑ α_ℓ V_{u_ℓ}(ρ)` of a mixture integrand (paper, after (3.6)). -/
noncomputable def mixtureEnergy {N : ℕ} (α : Fin N → ℝ) (u : Fin N → E) (ρ : E → ℝ) :
    ℝ≥0∞ :=
  ∑ l, ENNReal.ofReal (α l) * dirVar (u l) ρ

/-- The (anisotropic) Cheeger value `h_H(K) = inf_{ρ ∈ 𝒫(K)} E_H(ρ)` (paper (3.2)). -/
noncomputable def cheeger {N : ℕ} (α : Fin N → ℝ) (u : Fin N → E) (K : Set E) : ℝ≥0∞ :=
  ⨅ (ρ : E → ℝ) (_ : MemP K ρ), mixtureEnergy α u ρ

end Variation

section Lift

variable {d : ℕ}

/-- Lebesgue measure on `ℝ^d × ℝ` is a Haar measure.  Instance search does not unfold
`volume` on a product type to `Measure.prod`, so this is recorded explicitly (as Mathlib does
for `NumberField.mixedSpace`); it lets the general lemmas of `Komlos.Variation` be applied to
functions on `Euc d × ℝ`. -/
instance isAddHaarMeasure_volume_prod : (volume : Measure (Euc d × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- The horizontal section `D_t = {y : (y, t) ∈ B}` of a set `B ⊆ ℝ^d × ℝ` (paper Lemma 3.4). -/
def sectionAt (B : Set (Euc d × ℝ)) (t : ℝ) : Set (Euc d) :=
  {y | (y, t) ∈ B}

/-- The geometric lift `B = {(y, s) : |s| < 3, y + s v ∈ K}` (paper Lemma 4.1). -/
def lift (K : Set (Euc d)) (v : Euc d) : Set (Euc d × ℝ) :=
  {p | |p.2| < 3 ∧ p.1 + p.2 • v ∈ K}

/-- The length `ℓ(y)` of the vertical fiber of the lift over `y` (zero for an empty fiber). -/
noncomputable def fiberLength (K : Set (Euc d)) (v : Euc d) (y : Euc d) : ℝ :=
  (volume {s : ℝ | (y, s) ∈ lift K v}).toReal

/-- The Steiner symmetral `B⋆ = {(y, s) : |s| < ℓ(y)/2}` of the lift (paper Lemma 4.1). -/
def steiner (K : Set (Euc d)) (v : Euc d) : Set (Euc d × ℝ) :=
  {p | |p.2| < fiberLength K v p.1 / 2}

/-- The lifted density `R(y, s) = (1/6) ρ(y + s v) 𝟙_{|s| < 3}` (paper (4.2)). -/
noncomputable def liftedDensity (ρ : Euc d → ℝ) (v : Euc d) : Euc d × ℝ → ℝ :=
  fun p => if |p.2| < 3 then (1 / 6 : ℝ) * ρ (p.1 + p.2 • v) else 0

/-- The fiber distribution function `μ(y, t) = |{s : R(y, s) > t}|` (paper (4.1)). -/
noncomputable def fiberDist (R : Euc d × ℝ → ℝ) (y : Euc d) (t : ℝ) : ℝ≥0∞ :=
  volume {s : ℝ | t < R (y, s)}

/-- The fiberwise symmetric decreasing rearrangement (paper (4.1)):
`R⋆(y, s) = ∫_0^∞ 𝟙{2|s| < μ(y, t)} dt`, with the value `0` wherever the integral is
infinite (the paper's convention on exceptional fibers). -/
noncomputable def symRearr (R : Euc d × ℝ → ℝ) : Euc d × ℝ → ℝ :=
  fun p =>
    (∫⁻ t in Ioi (0 : ℝ),
      {t | ENNReal.ofReal (2 * |p.2|) < fiberDist R p.1 t}.indicator (fun _ => (1 : ℝ≥0∞)) t).toReal

end Lift

end Komlos
