import Komlos.Literature.Regularized.InteriorCampanatoAux

/-!
# Link 6: `C^{1,β}` regularity of the logarithmic solution (lane `L3b`)

Link 6 of the interior regularity chain of
`Komlos/Literature/Regularized/InteriorRegularity.lean`
(`IsWeakLogSol.exists_holder_gradient`): a weak solution of

`div ∇Ψ(∇v) = κ v + 2 m + B(∇v)`

on an open set `U`, continuous there, is `C¹` on `U`, its weak gradient field `G` is the classical
one, and `∇v` is Hölder continuous on every compact subset of `U`.

## Structure of the proof

1. `IsWeakLogSol.exists_harmonic_comparison` (`InteriorCampanatoAux.lean`, the one `sorry` of
   link 6): the comparison with the `Ψ`-harmonic replacement.  Its *existence* half
   (`IsWeakLogSol.exists_psi_harmonic_replacement`, `InteriorReplacement.lean`) and its
   *monotonicity* half (`IsWeakLogSol.replacement_comparison_le`) are proved; what is missing is
   the maximum principle for the replacement and the bootstrap of the Morrey exponent.
   `IsWeakLogSol.exists_perturbed_excess_decay` combines it with the Campanato decay of link 2
   (`exists_regHarmonic_campanato_field`) into a *perturbed* decay for the `L²` excess of `G`.
2. `IsWeakLogSol.exists_campanato_L1` (**proved**): the Campanato iteration
   (`Komlos.Literature.campanato_iteration_constants`) plus the `L² → L¹` conversion.
3. `IsWeakLogSol.exists_contDiffOn_one_of_closure_subset` (**proved**, this file): Campanato's
   criterion `Komlos.Literature.exists_holder_of_campanato` on a *relatively compact* open
   `V ⊆ U`, followed by `HasWeakGradientOn.contDiffOn_one`.  The relative compactness is what makes
   `V.indicator G` globally locally integrable, which is the hypothesis of the criterion; `G`
   itself is only locally integrable *on* `U`.
4. `IsWeakLogSol.exists_holder_gradient` (**proved**, this file): the three conclusions are local,
   so they follow from (3) by `exists_compact_between` (a relatively compact open neighbourhood of
   a compact subset of `U`), `contDiffOn_of_locally_contDiffOn`, and
   `MeasureTheory.measure_null_of_locally_null`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ mc : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-! ### The local statement on a relatively compact open subset -/

/-- **`C¹` regularity on a relatively compact open subset of `U`.**

Campanato's criterion is applied to `V.indicator G`, which is globally locally integrable because
`closure V` is a compact subset of `U` (`IsWeakLogSol.locallyIntegrable_indicator`); on balls
contained in `V` it agrees with `G`, so the Campanato bounds of
`IsWeakLogSol.exists_campanato_L1` apply.  The resulting continuous representative `G'` of `G` is
a continuous weak gradient of `v` on `V`, so `HasWeakGradientOn.contDiffOn_one`
(`Komlos.Literature.contDiffOn_of_weakGradient`) makes `v` a `C¹` function with `∇v = G'`. -/
theorem IsWeakLogSol.exists_contDiffOn_one_of_closure_subset (hd : 0 < d)
    (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ mc Ψ U v G) {V : Set (Euc d)} (hV : IsOpen V) (hVU : closure V ⊆ U) :
    ContDiffOn ℝ 1 v V ∧ (∀ᵐ x ∂(volume.restrict V), G x = gradient v x) ∧
      ∀ T : Set (Euc d), IsCompact T → T ⊆ V →
        ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r (gradient v) T := by
  have hVsubU : V ⊆ U := subset_closure.trans hVU
  have hloc : LocallyIntegrable (V.indicator G) volume :=
    hsol.locallyIntegrable_indicator hV.measurableSet hVU
  -- the Campanato hypothesis for `V.indicator G`
  have hcamp : ∀ T : Set (Euc d), IsCompact T → T ⊆ V → ∃ α C R₀ : ℝ, 0 < α ∧ 0 < R₀ ∧
      ∀ x ∈ T, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ a : Euc d, (∫ y in Metric.closedBall x r, ‖V.indicator G y - a‖) ≤
          C * r ^ ((d : ℝ) + α) := by
    intro T hT hTV
    obtain ⟨δ, hδ, hδsub⟩ := hT.exists_cthickening_subset_open hV hTV
    obtain ⟨α, C, R₀, hα, hR₀, hballU, hmain⟩ :=
      hsol.exists_campanato_L1 hd hΨ hT (hTV.trans hVsubU)
    refine ⟨α, C, min R₀ δ, hα, lt_min hR₀ hδ, fun x hx r hr hrR => ?_⟩
    obtain ⟨a, hbound⟩ := hmain x hx r hr (hrR.trans (min_le_left _ _))
    refine ⟨a, ?_⟩
    have hsubV : Metric.closedBall x r ⊆ V :=
      ((Metric.closedBall_subset_closedBall (hrR.trans (min_le_right _ _))).trans
        (Metric.closedBall_subset_cthickening hx δ)).trans hδsub
    have heq : (∫ y in Metric.closedBall x r, ‖V.indicator G y - a‖) =
        ∫ y in Metric.closedBall x r, ‖G y - a‖ := by
      refine setIntegral_congr_fun measurableSet_closedBall fun y hy => ?_
      rw [Set.indicator_of_mem (hsubV hy)]
    rw [heq]
    exact hbound
  obtain ⟨G', hG'ae, hG'c, hG'H⟩ := Komlos.Literature.exists_holder_of_campanato hV hloc hcamp
  have hG'G : ∀ᵐ x ∂(volume.restrict V), G' x = G x := by
    filter_upwards [hG'ae, self_mem_ae_restrict hV.measurableSet] with x h1 h2
    rw [h1, Set.indicator_of_mem h2]
  have hG'G' : ∀ᵐ x, x ∈ V → G' x = G x := (ae_restrict_iff' hV.measurableSet).1 hG'G
  -- `G'` is a continuous weak gradient of `v` on `V`
  have hweak : HasWeakGradientOn V v G' := by
    refine ⟨fun ψ hψ hψs hψV e => ?_⟩
    rw [hsol.hasWeakGradientOn.integral_eq ψ hψ hψs (hψV.trans hVsubU) e]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hG'G'] with x hx
    show ⟪G x, e⟫ * ψ x = ⟪G' x, e⟫ * ψ x
    by_cases hxs : x ∈ tsupport ψ
    · rw [hx (hψV hxs)]
    · rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero, mul_zero]
  obtain ⟨hC1, hgradeq⟩ :=
    hweak.contDiffOn_one hV (hsol.continuousOn.mono hVsubU) hG'c
  refine ⟨hC1, ?_, ?_⟩
  · filter_upwards [hG'G, self_mem_ae_restrict hV.measurableSet] with x h1 h2
    rw [hgradeq x h2, h1]
  · intro T hT hTV
    obtain ⟨Cn, rn, hrn, hH⟩ := hG'H T hT hTV
    refine ⟨Cn, rn, hrn, fun y hy z hz => ?_⟩
    rw [hgradeq y (hTV hy), hgradeq z (hTV hz)]
    exact hH y hy z hz

/-! ### Link 6 -/

/-- **(link 6, `reg/c2b`) `v ∈ C^{1,β}_loc(U)`**, with `∇v = G` a.e.  This is the frozen statement
`Komlos.Literature.Regularized.IsWeakLogSol.exists_holder_gradient` of `InteriorRegularity.lean`,
verbatim.

All three conclusions are local, so they follow from
`IsWeakLogSol.exists_contDiffOn_one_of_closure_subset` once every compact subset of `U` has a
relatively compact open neighbourhood inside `U` (`exists_compact_between`):
`contDiffOn_of_locally_contDiffOn` for the `C¹` statement,
`MeasureTheory.measure_null_of_locally_null` for the a.e. identification of the gradient, and a
direct application for the Hölder bound on a compact set. -/
theorem IsWeakLogSol.exists_holder_gradient_pos (hd : 0 < d) (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ mc Ψ U v G) :
    ContDiffOn ℝ 1 v U ∧ (∀ᵐ x ∂(volume.restrict U), G x = gradient v x) ∧
      ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
        ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r (gradient v) S := by
  have hU : IsOpen U := hsol.isOpen
  -- every compact subset of `U` has a relatively compact open neighbourhood inside `U`
  have hnbhd : ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
      ∃ V : Set (Euc d), IsOpen V ∧ S ⊆ V ∧ closure V ⊆ U := by
    intro S hS hSU
    obtain ⟨L, hL, hSL, hLU⟩ := exists_compact_between hS hU hSU
    exact ⟨interior L, isOpen_interior, hSL,
      (closure_minimal interior_subset hL.isClosed).trans hLU⟩
  refine ⟨?_, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    obtain ⟨V, hV, hxV, hVU⟩ := hnbhd {x} isCompact_singleton (singleton_subset_iff.2 hx)
    obtain ⟨hC1, -, -⟩ := hsol.exists_contDiffOn_one_of_closure_subset hd hΨ hV hVU
    exact ⟨V, hV, hxV rfl, hC1.mono inter_subset_right⟩
  · refine (ae_restrict_iff' hU.measurableSet).2 (ae_iff.2 ?_)
    refine measure_null_of_locally_null _ fun x hx => ?_
    have hxU : x ∈ U := by
      by_contra hxU
      exact hx fun h => absurd h hxU
    obtain ⟨V, hV, hxV, hVU⟩ := hnbhd {x} isCompact_singleton (singleton_subset_iff.2 hxU)
    obtain ⟨-, hae, -⟩ := hsol.exists_contDiffOn_one_of_closure_subset hd hΨ hV hVU
    refine ⟨_, inter_mem_nhdsWithin _ (hV.mem_nhds (hxV rfl)), ?_⟩
    refine measure_mono_null (fun y hy => ?_)
      (ae_iff.1 ((ae_restrict_iff' hV.measurableSet).1 hae))
    show ¬ (y ∈ V → G y = gradient v y)
    intro hcon
    exact hy.1 fun _ => hcon hy.2
  · intro S hS hSU
    obtain ⟨V, hV, hSV, hVU⟩ := hnbhd S hS hSU
    obtain ⟨-, -, hH⟩ := hsol.exists_contDiffOn_one_of_closure_subset hd hΨ hV hVU
    exact hH S hS hSV

/-- **(link 6, `reg/c2b`) `v ∈ C^{1,β}_loc(U)`**, with `∇v = G` a.e.  This is the frozen statement
`Komlos.Literature.Regularized.IsWeakLogSol.exists_holder_gradient` of `InteriorRegularity.lean`,
verbatim.

For `d ≥ 1` this is `IsWeakLogSol.exists_holder_gradient_pos`; for `d = 0` the space `Euc 0` is a
single point, every function on it is smooth and every gradient vanishes, so all three
conclusions are trivial. -/
theorem IsWeakLogSol.exists_holder_gradient (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ mc Ψ U v G) :
    ContDiffOn ℝ 1 v U ∧ (∀ᵐ x ∂(volume.restrict U), G x = gradient v x) ∧
      ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
        ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r (gradient v) S := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    have hzero : ∀ y : Euc 0, y = 0 := Komlos.Literature.eq_zero_of_dim_zero
    have hC1 : ContDiffOn ℝ 1 v U :=
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : Euc 0 => v 0) U).congr
        (fun y _ => by rw [hzero y])
    refine ⟨hC1, ?_, ?_⟩
    · filter_upwards with y
      rw [hzero (G y), hzero (gradient v y)]
    · intro S hS hSU
      refine ⟨0, 1, one_pos, fun y hy z hz => ?_⟩
      rw [hzero (gradient v y), hzero (gradient v z)]
      simp
  · exact hsol.exists_holder_gradient_pos hd hΨ

end Komlos.Literature.Regularized
