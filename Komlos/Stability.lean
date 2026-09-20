import Komlos.Section
import Komlos.Height

/-!
# Finite-step stability (paper Proposition 2.2)

If `ρ ∈ 𝒫(K)` satisfies the cap (2.8) and `κ ‖v‖₂ ≤ 1/3`, then `𝒯_v K` is nonempty and
admits an admissible density with the same `κ`.

Paper proof: lift `ρ` to `R` (mass one, supported in the lift `B`, horizontal variations
`≤ κ‖u‖`), rearrange to `R⋆` (supported in `B⋆`, horizontal variations still `≤ κ‖u‖`), and
observe `∫ |s| R⋆ ≥ 3/2 − (3/2) κ ‖v‖ ≥ 1`; apply `prescribed_section` at height one, whose
section is `𝒯_v K` by `sectionAt_steiner_one`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-- The fiberwise rearrangement `R⋆` of a probability density `R` on the lift `B` is a
probability density on the Steiner symmetral `B⋆` (paper Lemma 4.2, packaged). -/
theorem symRearr_isProbDensityOn {K : Set (Euc d)} (hK : IsGoodConvex K) (v : Euc d)
    {R : Euc d × ℝ → ℝ} (hR : IsProbDensityOn (lift K v) R) :
    IsProbDensityOn (steiner K v) (symRearr R) := by
  have hmeas : Measurable (symRearr R) := symRearr_measurable R hR.measurable
  have hnn : ∀ p, 0 ≤ symRearr R p := symRearr_nonneg R
  have hlint : ∫⁻ p, ENNReal.ofReal (symRearr R p) = ∫⁻ p, ENNReal.ofReal (R p) :=
    lintegral_symRearr R hR.measurable hR.nonneg hR.integrable
  have hR_lint : ∫⁻ p, ENNReal.ofReal (R p) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hR.integrable (ae_of_all _ hR.nonneg),
      hR.integral_eq_one, ENNReal.ofReal_one]
  have hint : Integrable (symRearr R) :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).2
      (by rw [hlint, hR_lint]; exact ENNReal.one_lt_top)⟩
  refine ⟨hmeas, hnn, hint, ?_, ?_⟩
  · have := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)
    rw [hlint, hR_lint] at this
    have h0 : 0 ≤ ∫ p, symRearr R p := integral_nonneg hnn
    rw [← ENNReal.toReal_ofReal h0, this, ENNReal.toReal_one]
  · exact symRearr_ae_zero_outside hK v R hR.measurable hR.nonneg hR.integrable
      hR.ae_zero_outside

/-- **Paper Proposition 2.2 (finite-step stability).** -/
theorem finite_step_stability {K : Set (Euc d)} (hK : IsGoodConvex K) {κ : ℝ} (hκ : 0 ≤ κ)
    {v : Euc d} {ρ : Euc d → ℝ} (hρ : MemP K ρ) (hcap : VarBounded κ ρ)
    (hstep : κ * ‖v‖ ≤ 1 / 3) :
    (transform v K).Nonempty ∧ HasAdmissible (transform v K) κ := by
  -- the lifted density `R` (paper (4.2)) and its rearrangement `R⋆` (paper (4.1))
  have hR : IsProbDensityOn (lift K v) (liftedDensity ρ v) :=
    liftedDensity_isProbDensityOn hρ.toIsProbDensityOn v
  have hRs : IsProbDensityOn (steiner K v) (symRearr (liftedDensity ρ v)) :=
    symRearr_isProbDensityOn hK v hR
  -- horizontal variations (paper (4.6)): `V_{(u,0)} R⋆ ≤ V_{(u,0)} R ≤ V_u ρ ≤ κ ‖u‖`
  have hvar : ∀ u : Euc d, ‖u‖ = 1 →
      dirVar ((u, (0 : ℝ)) : Euc d × ℝ) (symRearr (liftedDensity ρ v)) ≤ ENNReal.ofReal κ := by
    intro u hu
    calc dirVar ((u, (0 : ℝ)) : Euc d × ℝ) (symRearr (liftedDensity ρ v))
        ≤ dirVar ((u, (0 : ℝ)) : Euc d × ℝ) (liftedDensity ρ v) :=
          dirVar_symRearr_le _ hR.measurable hR.nonneg hR.integrable u
      _ ≤ dirVar u ρ := dirVar_liftedDensity_le hρ.measurable v u
      _ ≤ ENNReal.ofReal (κ * ‖u‖) := hcap u
      _ = ENNReal.ofReal κ := by rw [hu, mul_one]
  -- height (paper (4.5) and (2.10)): `∫ |s| R⋆ ≥ 3/2 − (3/2) V_v ρ ≥ 1`
  have hρ_univ : IsProbDensityOn univ ρ :=
    ⟨hρ.measurable, hρ.nonneg, hρ.integrable, hρ.integral_eq_one,
      ae_of_all _ fun x hx => (hx (mem_univ x)).elim⟩
  have hV : (dirVar v ρ).toReal ≤ 1 / 3 := by
    have h2 : (dirVar v ρ).toReal ≤ (ENNReal.ofReal (κ * ‖v‖)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap v)
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    linarith
  have hheight : (1 : ℝ) ≤ ∫ p, |p.2| * symRearr (liftedDensity ρ v) p := by
    have := integral_abs_mul_symRearr_liftedDensity_ge hρ_univ v (hρ.dirVar_ne_top v)
    linarith
  -- apply paper Lemma 3.4 to `B⋆, R⋆` at height one; the section is `𝒯_v K` (paper (4.3))
  have := prescribed_section (isGoodConvex_steiner hK v) (fun p hp => steiner_symm v p hp) hκ
    hRs hvar zero_le_one hheight
  rwa [sectionAt_steiner_one hK v] at this

end Komlos
