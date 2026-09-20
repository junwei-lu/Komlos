import Komlos.Literature.Regularized.InteriorHarmonicAux
import Komlos.Literature.Regularized.InteriorHarmonicHolder
import Komlos.Literature.Regularized.InteriorRegularity

/-!
# The `Ψ`-harmonic comparison problem: link 2 of lane `L3` (lane `L3b`)

Link 2 of the interior regularity chain of
`Komlos/Literature/Regularized/InteriorRegularity.lean`
(`exists_regHarmonic_campanato`): a weak solution of the *homogeneous* equation
`div ∇Ψ(∇h) = 0` on a ball is regular there, and the `L²` oscillation of its gradient decays at
a Morrey rate.

## The route (Giaquinta–Martinazzi, Theorem 8.1; Gilbarg–Trudinger, Theorem 8.32)

1. **`W^{2,2}_loc` by difference quotients.**  `∇Ψ` is globally Lipschitz and strongly monotone
   (`IsRegProfileWith.lipschitz_gradient`, `IsRegProfileWith.inner_gradient_sub`), so testing the
   weak equation with `η² Δ_s^e h` and using
   `Komlos.Literature.integral_inner_diffQuot_flux`-style summation by parts
   (`PLaplacian/DiffQuotBasic.lean`, `DiffQuotLocalization.lean`, `DiffQuotEstimate.lean`) gives a
   Caccioppoli bound for `Δ_s^e ∇h` that is uniform in `s`; hence `∇h ∈ W^{1,2}_loc`.
2. **The differentiated equation is linear and uniformly elliptic.**  Each directional derivative
   `z = ∂_e h` is a weak solution of `div (A ∇z) = 0` with `A = regLinCoeff Ψ ∇h = D²Ψ(∇h)`, a
   *bounded measurable* uniformly elliptic coefficient field: this is
   `isUnifElliptic_regLinCoeff` (**proved**, in `InteriorHarmonicAux.lean`), which is exactly the
   hypothesis `IsUnifElliptic` consumed by the De Giorgi–Nash lane.
3. **De Giorgi–Nash.**  `IsLinearSol.exists_osc_decay` and `exists_essSup_bound`
   (`DeGiorgiNash.lean`, lane `DGN`) give, for such a `z`, the interior oscillation decay
   `osc_{B_ρ} z ≤ C (2ρ/r)^β osc_{B_{r/2}} z` together with the local bound
   `osc_{B_{r/2}} z ≤ C (⨍_{B_r} |z - (z)_r|²)^{1/2}`.  Summing over an orthonormal basis turns
   this into the *scale-invariant* Hölder estimate `exists_regHarmonic_holder_gradient` below.
4. **The Campanato decay** then follows from the Hölder estimate by the elementary computation
   `excess_decay_of_holder` (**proved**, in `InteriorHarmonicAux.lean`).

Steps (1)–(4) are **proved** by lane `reg/c2h` in `InteriorHarmonicHolder*.lean`; this file
records the statement of link 2 and derives its frozen shape.  The scale-invariant *Hölder*
estimate that step (4) was originally meant to consume — `exists_regHarmonic_holder_field` —
turned out to be **false** (it bounds the oscillation of `W` on `B_{r/2}` by the `L²` excess on
the *same* ball; see the counterexample in `NOTES_L3h.md`), so lane `reg/c2h` proves the
Campanato *decay* directly and that lemma was deleted.

## DEVIATION from the frozen statement of link 2

`exists_regHarmonic_campanato` as stated in `InteriorRegularity.lean` asserts

* `ContDiffOn ℝ 2 h (Metric.ball x₀ r)` and
* the decay exponent `d + 2`.

Both are *stronger than link 6 needs*, and both require an extra Schauder step (the
`C^{0,α}` ⇒ `C^{1,α}` bootstrap `Komlos.Literature.schauder_C2` applied to the differentiated
equation, i.e. a second linear regularity theory on top of De Giorgi–Nash).  Following the lane
brief ("prefer the weakest statement that makes link 6 and the final assembly work"), this file
proves the weaker

* `ContDiffOn ℝ 1 h (Metric.ball x₀ r)` and
* the decay exponent `d + 2β` for **some** `β ∈ (0,1)`,

and it does so through a **third** weakening: the hypothesis `IsRegHarmonic` — which carries the
continuity of the potential `h` — is replaced by `IsRegHarmonicField`, and the conclusion is
stated for a continuous representative `W` of the gradient *field* rather than for `gradient h`
(`exists_regHarmonic_campanato_field`).  Continuity of `h` plays no role in the interior
regularity theory, and it is what the `Ψ`-harmonic replacement of link 6 cannot supply without a
separate De Giorgi–Nash argument for the *potential*.  The frozen-shape statement
`exists_regHarmonic_campanato` is nevertheless recovered from the field version, using the
continuity of `h` carried by `IsRegHarmonic`,

which is what the Campanato iteration of link 6 consumes: the iteration only needs the good
exponent of the homogeneous problem to exceed the data exponent produced by the comparison
estimate, and `d + 2β` does (see `InteriorCampanato.lean`).  `exists_regHarmonic_campanato` is
used nowhere else in the chain (link 6 is its only consumer, and the final assembly
`exists_regEigenData` goes through link 8, which uses links 6 and 7), so the deviation is
confined to lane `L3b`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {Ψ : Euc d → ℝ}

/-! ### `Ψ`-harmonic functions give `Ψ`-harmonic gradient fields -/

/-- Forgetting the continuity of the potential turns a `Ψ`-harmonic function into a `Ψ`-harmonic
gradient field. -/
theorem IsRegHarmonic.toIsRegHarmonicField {U : Set (Euc d)} {h : Euc d → ℝ} {H : Euc d → Euc d}
    (hh : IsRegHarmonic Ψ U h H) : IsRegHarmonicField Ψ U h H where
  isOpen := hh.isOpen
  measurable := hh.measurable
  measurable_grad := hh.measurable_grad
  hasWeakGradientOn := hh.hasWeakGradientOn
  integrableOn_sq := hh.integrableOn_sq
  weakEq := hh.weakEq

/-! ### Link 2 for gradient fields: the Campanato decay -/

/-- **(link 2, field form) The Campanato decay of a `Ψ`-harmonic gradient field.**  The continuous
representative `W` of `H` satisfies

`sqExcess W x₀ ρ ≤ Cdec (2ρ/r)^{d+2β} sqExcess W x₀ (r/2)`,  `0 < ρ ≤ r/2`.

This is the form link 6 consumes.  It is proved by lane `reg/c2h` as
`exists_regHarmonic_campanato_field'` (`InteriorHarmonicHolder.lean`); this file only records
the statement.

**DEVIATION (lane `reg/c2h`)**: the extra hypothesis `IsLocSqIntegrableOn (ball x₀ r) h`.
`HasWeakGradientOn.integral_eq` is stated with Lean integrals, which take the junk value `0`
when the integrand is not integrable, so `IsRegHarmonicField` alone does not say that `H` is a
weak gradient of anything; without local square integrability of the potential the conclusion
is false (for `Ψ = ‖·‖²/2` the equation only says `div H = 0`, which any divergence-free `L²`
field satisfies).  In the application `h = v - z` with `v` continuous and `z ∈ W₀^{1,2}`, so
the hypothesis is supplied by `isLocSqIntegrableOn_sub_memLp`. -/
theorem exists_regHarmonic_campanato_field (hΨ : IsRegProfile Ψ) :
    ∃ Cdec β : ℝ, 0 ≤ Cdec ∧ 0 < β ∧ β < 1 ∧
      ∀ (x₀ : Euc d) (r : ℝ), 0 < r → ∀ (h : Euc d → ℝ) (H : Euc d → Euc d),
        IsRegHarmonicField Ψ (Metric.ball x₀ r) h H →
        IsLocSqIntegrableOn (Metric.ball x₀ r) h →
        ∃ W : Euc d → Euc d, ContinuousOn W (Metric.ball x₀ r) ∧
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), H x = W x) ∧
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 2 →
            Komlos.Literature.sqExcess W x₀ ρ ≤
              Cdec * (2 * ρ / r) ^ ((d : ℝ) + 2 * β) *
                Komlos.Literature.sqExcess W x₀ (r / 2) :=
  exists_regHarmonic_campanato_field' hΨ

/-! ### Link 2 in the shape of the frozen statement -/

/-- **(link 2, `reg/c2b`) Interior regularity and Campanato decay for `Ψ`-harmonic functions**, in
the weakened form described in the module docstring (**DEVIATION**: `C¹` instead of `C²`, and the
decay exponent `d + 2β` instead of `d + 2`).

Proof: `exists_regHarmonic_campanato_field` applied to the underlying gradient field gives the
continuous representative `W` of `H` and the decay; since `h` is continuous on the ball and `W` is
a continuous weak gradient of `h` there, `HasWeakGradientOn.contDiffOn_one` makes `h` a `C¹`
function with `∇h = W`, and the decay transfers to `∇h`. -/
theorem exists_regHarmonic_campanato (hΨ : IsRegProfile Ψ) :
    ∃ Cdec β : ℝ, 0 ≤ Cdec ∧ 0 < β ∧ β < 1 ∧
      ∀ (x₀ : Euc d) (r : ℝ), 0 < r → ∀ (h : Euc d → ℝ) (H : Euc d → Euc d),
        IsRegHarmonic Ψ (Metric.ball x₀ r) h H →
        ContDiffOn ℝ 1 h (Metric.ball x₀ r) ∧
        (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), H x = gradient h x) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 2 →
          (∫ y in Metric.ball x₀ ρ, ‖gradient h y - ⨍ z in Metric.ball x₀ ρ, gradient h z‖ ^ 2) ≤
            Cdec * (2 * ρ / r) ^ ((d : ℝ) + 2 * β) *
              ∫ y in Metric.ball x₀ (r / 2),
                ‖gradient h y - ⨍ z in Metric.ball x₀ (r / 2), gradient h z‖ ^ 2 := by
  obtain ⟨Cdec, β, hCdec, hβ, hβ1, hmain⟩ := exists_regHarmonic_campanato_field hΨ
  refine ⟨Cdec, β, hCdec, hβ, hβ1, fun x₀ r hr h H hh => ?_⟩
  obtain ⟨W, hWc, hWae, hdec⟩ := hmain x₀ r hr h H hh.toIsRegHarmonicField
    (isLocSqIntegrableOn_of_continuousOn hh.continuousOn)
  have hWae' : ∀ᵐ x, x ∈ Metric.ball x₀ r → H x = W x :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).1 hWae
  -- `W` is a continuous weak gradient of `h` on the ball
  have hweak : HasWeakGradientOn (Metric.ball x₀ r) h W := by
    refine ⟨fun ψ hψ hψs hψU e => ?_⟩
    rw [hh.hasWeakGradientOn.integral_eq ψ hψ hψs hψU e]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hWae'] with x hx
    show ⟪H x, e⟫ * ψ x = ⟪W x, e⟫ * ψ x
    by_cases hxs : x ∈ tsupport ψ
    · rw [hx (hψU hxs)]
    · rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero, mul_zero]
  obtain ⟨hC1, hgradeq⟩ :=
    hweak.contDiffOn_one Metric.isOpen_ball (hh.continuousOn) hWc
  refine ⟨hC1, ?_, fun ρ hρ hρr => ?_⟩
  · filter_upwards [hWae, self_mem_ae_restrict Metric.isOpen_ball.measurableSet] with x hx hxb
    rw [hx, hgradeq x hxb]
  · have hr2 : (0 : ℝ) < r / 2 := by linarith
    have hsub2 : Metric.closedBall x₀ (r / 2) ⊆ Metric.ball x₀ r :=
      Metric.closedBall_subset_ball (by linarith)
    have hsubρ : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r :=
      (Metric.closedBall_subset_closedBall hρr).trans hsub2
    have e1 := sqExcess_congr_of_eqOn (W := gradient h) (W' := W) (x₀ := x₀) (ρ := ρ)
      (fun x hx => hgradeq x (hsubρ hx))
    have e2 := sqExcess_congr_of_eqOn (W := gradient h) (W' := W) (x₀ := x₀) (ρ := r / 2)
      (fun x hx => hgradeq x (hsub2 hx))
    rw [Komlos.Literature.sqExcess_eq (gradient h) x₀ ρ] at e1
    rw [Komlos.Literature.sqExcess_eq (gradient h) x₀ (r / 2)] at e2
    rw [excess_ball_eq_closedBall (gradient h) x₀ hρ.ne',
      excess_ball_eq_closedBall (gradient h) x₀ hr2.ne', e1, e2]
    exact hdec ρ hρ hρr

end Komlos.Literature.Regularized
