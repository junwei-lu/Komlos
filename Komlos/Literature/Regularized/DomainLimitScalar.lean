import Komlos.Literature.Regularized.DomainLimitDomain

/-!
# Monotonicity of `regMin` in the domain

Elementary half of step 4 of the `L4` lane of `REGULARIZED_ROUTE.md`: enlarging the domain
enlarges the admissible class, hence lowers the infimum.  Because `regMin` is written as a
`⨅` over a subtype, the statement needs the two `BddBelow`/attainment facts that
`IsRegMinimizer` carries, so it is phrased with a minimizer on the smaller domain.

The hard half (`regMin` of the inner domains converges *down* to `regMin K`, by dilating a
minimizer of `K` into the inner domain) is `Komlos/Literature/Regularized/DomainLimitEnergy.lean`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {p κ : ℝ} {Ψ : Euc d → ℝ} {K K' : Set (Euc d)} {u u' : Euc d → ℝ}

/-- Admissibility is monotone in the domain (zero extension). -/
theorem IsRegAdmissible.mono (hu : IsRegAdmissible p K u) (hKK' : K ⊆ K') :
    IsRegAdmissible p K' u where
  memW0 := hu.memW0.mono hKK'
  nonneg := hu.nonneg
  eq_zero_of_notMem x hx := hu.eq_zero_of_notMem x fun hxK => hx (hKK' hxK)
  integral_rpow := hu.integral_rpow

/-- The regularized minimum is a lower bound for the energy of every admissible competitor,
provided the competitor energies are bounded below (as recorded by `IsRegMinimizer.bddBelow`). -/
theorem regMin_le_regEnergy_of_bddBelow
    (hbdd : BddBelow
      (Set.range fun w : {w : Euc d → ℝ // IsRegAdmissible p K w} => regEnergy p κ Ψ w.1))
    (hu : IsRegAdmissible p K u) : regMin p κ Ψ K ≤ regEnergy p κ Ψ u :=
  ciInf_le hbdd (⟨u, hu⟩ : {w : Euc d → ℝ // IsRegAdmissible p K w})

/-- **Monotonicity of `regMin` in the domain.**  If `K' ⊆ K` and the energy on `K'` is attained
at `u'`, then `regMin K ≤ regMin K'`: the zero extension of `u'` competes on `K`. -/
theorem regMin_le_regMin_of_subset (hKK' : K' ⊆ K)
    (hbdd : BddBelow
      (Set.range fun w : {w : Euc d → ℝ // IsRegAdmissible p K w} => regEnergy p κ Ψ w.1))
    (hu' : IsRegMinimizer p κ Ψ K' u') : regMin p κ Ψ K ≤ regMin p κ Ψ K' := by
  rw [← hu'.energy_eq]
  exact regMin_le_regEnergy_of_bddBelow hbdd (hu'.toIsRegAdmissible.mono hKK')

end Komlos.Literature.Regularized
