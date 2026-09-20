import Komlos.Literature.Regularized.InteriorDefs
import Komlos.Literature.Regularized.VariationalUnique
import Komlos.Literature.Regularized.Positivity

/-!
# The positive continuous minimizer (lane `L3`)

The first link of lane `L3` (`reg/c2`) of `REGULARIZED_ROUTE.md`, Revision 2: the continuous
positive representative produced by lane `L2`
(`IsRegMinimizer.exists_pos_continuous_rep`) is *again* a minimizer of the regularized energy.

The point is that `regEnergy` is a function of the a.e.-class of `u` only: its two densities are
evaluated at `u x` and at the **chosen** weak gradient `weakGrad u x`, and a weak gradient of `u`
is a weak gradient of every `φ =ᵐ u` (`HasWeakGradient.congr_left`), so
`weakGrad φ =ᵐ weakGrad u`.  The only fields of `IsRegAdmissible` that are *not* a.e. statements
are `nonneg` and `eq_zero_of_notMem`, and lane `L2` supplies both for `φ` directly.

## Main results

* `regEnergy_congr` — `regEnergy` only depends on the a.e.-class.
* `IsRegAdmissible.congr'`, `IsRegMinimizer.congr'` — transfer along `=ᵐ`.
* `exists_pos_continuous_minimizer` — the packaged statement consumed by the rest of the lane:
  a **continuous** minimizer, positive on `K` and vanishing off `K`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {p κ : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u φ : Euc d → ℝ}

/-- **Two a.e.-equal functions have a.e.-equal chosen weak gradients**, provided one of them has
a weak gradient at all. -/
theorem weakGrad_congr (h : φ =ᵐ[volume] u) (hu : ∃ g, HasWeakGradient u g) :
    weakGrad φ =ᵐ[volume] weakGrad u := by
  obtain ⟨g, hg⟩ := hu
  exact (hg.congr_left h.symm).weakGrad_ae_eq.trans hg.weakGrad_ae_eq.symm

/-- **`regEnergy` only depends on the a.e.-class of its argument.** -/
theorem regEnergy_congr (p κ : ℝ) (Ψ : Euc d → ℝ) (h : φ =ᵐ[volume] u)
    (hu : ∃ g, HasWeakGradient u g) : regEnergy p κ Ψ φ = regEnergy p κ Ψ u := by
  unfold regEnergy
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [h, weakGrad_congr h hu] with x hx hgx
    rw [hx, hgx]
  · exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- Admissibility transfers along `=ᵐ`, given the two pointwise conditions. -/
theorem IsRegAdmissible.congr' (hu : IsRegAdmissible p K u) (h : φ =ᵐ[volume] u)
    (hnn : ∀ x, 0 ≤ φ x) (hzero : ∀ x, x ∉ K → φ x = 0) : IsRegAdmissible p K φ where
  memW0 := hu.memW0.congr h.symm
  nonneg := hnn
  eq_zero_of_notMem := hzero
  integral_rpow := by
    rw [← hu.integral_rpow]
    exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- Being a minimizer transfers along `=ᵐ`, given the two pointwise conditions. -/
theorem IsRegMinimizer.congr' (hu : IsRegMinimizer p κ Ψ K u) (h : φ =ᵐ[volume] u)
    (hnn : ∀ x, 0 ≤ φ x) (hzero : ∀ x, x ∉ K → φ x = 0) : IsRegMinimizer p κ Ψ K φ where
  toIsRegAdmissible := hu.toIsRegAdmissible.congr' h hnn hzero
  energy_eq := by
    rw [regEnergy_congr p κ Ψ h (hu.memW0.exists_weakGradient.imp fun _ hg => hg.1)]
    exact hu.energy_eq
  bddBelow := hu.bddBelow

/-- **A continuous, positive minimizer.**  Lane `L1` produces a minimizer, lane `L2` its
continuous positive representative, and `IsRegMinimizer.congr'` transports minimality.

This is the input of every later link of lane `L3`. -/
theorem exists_pos_continuous_minimizer {κ : ℝ} (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) :
    ∃ φ : Euc d → ℝ, Continuous φ ∧ (∀ x, x ∉ K → φ x = 0) ∧ (∀ x ∈ K, 0 < φ x) ∧
      IsRegMinimizer 2 κ Ψ K φ := by
  obtain ⟨u, hu⟩ := exists_isRegMinimizer hκ hΨ hK
  obtain ⟨φ, hφc, hφu, hφ0, hφpos⟩ := hu.exists_pos_continuous_rep hκ hΨ hK
  have hnn : ∀ x, 0 ≤ φ x := fun x => by
    by_cases hx : x ∈ K
    · exact (hφpos x hx).le
    · rw [hφ0 x hx]
  exact ⟨φ, hφc, hφ0, hφpos, hu.congr' hφu hnn hφ0⟩

/-! ### The logarithmic transform -/

/-- `v = -log φ` is continuous on `K` when `φ` is continuous and positive there. -/
theorem continuousOn_neg_log (hφc : Continuous φ) (hφpos : ∀ x ∈ K, 0 < φ x) :
    ContinuousOn (fun x => -Real.log (φ x)) K := fun x hx =>
  ((Real.continuousAt_log (hφpos x hx).ne').comp hφc.continuousAt).neg.continuousWithinAt

/-- `v = -log φ` is globally measurable when `φ` is continuous. -/
theorem measurable_neg_log (hφc : Continuous φ) : Measurable fun x => -Real.log (φ x) :=
  (Real.measurable_log.comp hφc.measurable).neg

/-- `φ = exp (-v)` on the positivity set. -/
theorem exp_neg_log (hφpos : ∀ x ∈ K, 0 < φ x) {x : Euc d} (hx : x ∈ K) :
    Real.exp (-(-Real.log (φ x))) = φ x := by
  rw [neg_neg, Real.exp_log (hφpos x hx)]

end Komlos.Literature.Regularized
