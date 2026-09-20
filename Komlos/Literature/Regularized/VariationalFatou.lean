import Komlos.Literature.Regularized.VariationalLsc

/-!
# Fatou's lemma for the Bochner integral

Lane `L1` (`reg/variational`).  Mathlib has Fatou's lemma only for the lower Lebesgue integral
(`MeasureTheory.lintegral_liminf_le'`).  The entropy part of the regularized energy is lower
semicontinuous by Fatou applied to the nonnegative shifted densities
`(κ/2) w² log w + (κ/8) 1_K ≥ 0`, so we record the Bochner version we need: if `F n ≥ 0`
converges a.e. to `f` and `∫ F n` converges to `β`, then `∫ f ≤ β`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-- **Fatou's lemma for the Bochner integral** (the version used for the entropy): for
nonnegative integrable `F n` converging a.e. to an integrable `f`, with `∫ F n → β`, one has
`∫ f ≤ β`. -/
theorem integral_le_of_tendsto_integral {F : ℕ → Euc d → ℝ} {f : Euc d → ℝ} {β : ℝ}
    (hFi : ∀ n, Integrable (F n) (volume : Measure (Euc d)))
    (hF0 : ∀ n, 0 ≤ᵐ[volume] F n) (hfi : Integrable f volume)
    (hlim : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun n => ∫ x, F n x) atTop (𝓝 β)) :
    (∫ x, f x) ≤ β := by
  -- `f ≥ 0` a.e. and `β ≥ 0`
  have hf0 : 0 ≤ᵐ[volume] f := by
    filter_upwards [hlim, ae_all_iff.2 hF0] with x hx hF
    exact ge_of_tendsto' hx fun n => hF n
  have hβ0 : 0 ≤ β :=
    ge_of_tendsto' hint fun n => integral_nonneg_of_ae (hF0 n)
  -- the lower Lebesgue integrals
  have hFm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (F n x)) volume := fun n =>
    (hFi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hlin : ∀ n, (∫⁻ x, ENNReal.ofReal (F n x)) = ENNReal.ofReal (∫ x, F n x) := by
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae (hF0 n) (hFi n).aestronglyMeasurable,
      ENNReal.ofReal_toReal]
    have := (hFi n).2
    rw [hasFiniteIntegral_iff_ofReal (hF0 n)] at this
    exact this.ne
  have hliminf : (∫⁻ x, ENNReal.ofReal (f x)) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x)) atTop := by
    refine le_trans (le_of_eq ?_) (lintegral_liminf_le' hFm)
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with x hx
    have h1 : Tendsto (fun n => ENNReal.ofReal (F n x)) atTop (𝓝 (ENNReal.ofReal (f x))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hx
    exact h1.liminf_eq.symm
  have hlimit : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (F n x)) atTop
      (𝓝 (ENNReal.ofReal β)) := by
    simp only [hlin]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hint
  rw [hlimit.liminf_eq] at hliminf
  -- conclude
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hfi.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hβ0 hliminf

end Komlos.Literature.Regularized
