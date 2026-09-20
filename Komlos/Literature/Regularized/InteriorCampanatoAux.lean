import Komlos.Literature.Regularized.InteriorEnergyDecay
import Komlos.Literature.Regularized.InteriorHarmonic
import Komlos.Literature.Regularized.InteriorMorrey
import Komlos.Literature.Regularized.InteriorReplacement

/-!
# The comparison step and the Campanato iteration: auxiliary material (lane `L3b`)

This file prepares link 6 of the interior regularity chain
(`IsWeakLogSol.exists_holder_gradient`, proved in
`Komlos/Literature/Regularized/InteriorCampanato.lean`).  It contains

* the local integrability of the gradient field `G` of a weak solution (`IsWeakLogSol`), and the
  local integrability of its restriction to a relatively compact open subset — the hypothesis of
  Campanato's criterion `Komlos.Literature.exists_holder_of_campanato`;
* `setIntegral_norm_sub_setAverage_le_of_sq'`, the `L² → L¹` conversion of
  `Komlos.Literature.setIntegral_norm_sub_setAverage_le_of_sq` with the continuity hypothesis
  replaced by integrability — `G` is a priori only square integrable;
* `IsWeakLogSol.exists_perturbed_excess_decay`, the **analytic core** of link 6: the comparison
  of `v` with its `Ψ`-harmonic replacement, which turns the Campanato decay of link 2 into a
  *perturbed* decay for the excess of `G`;
* `exists_regHarmonic_energy_decay`, the `L²` energy decay of the `Ψ`-harmonic replacement field
  (lane `L8`, `reg/energy-decay`), proved from the Campanato decay of link 2 by the means
  telescope of `Komlos/Literature/Regularized/InteriorEnergyDecay.lean`;
* `IsWeakLogSol.exists_campanato_L1`, the conclusion of the Campanato iteration in the form
  required by Campanato's criterion.  This is **proved** from the previous item by
  `Komlos.Literature.campanato_iteration_constants`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ mc : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-! ### Local integrability of the gradient field -/

/-- On a closed ball inside `U` the field `G` is square integrable, hence integrable. -/
theorem IsWeakLogSol.integrableOn_closedBall (hsol : IsWeakLogSol κ mc Ψ U v G) {x : Euc d}
    {r : ℝ} (hr : Metric.closedBall x r ⊆ U) : IntegrableOn G (Metric.closedBall x r) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall x r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have h2 : MemLp G 2 (volume.restrict (Metric.closedBall x r)) :=
    (memLp_two_iff_integrable_sq_norm hsol.measurable_grad.aestronglyMeasurable).2
      (hsol.integrableOn_sq x r hr)
  exact h2.integrable (by norm_num)

/-- On a closed ball inside `U` the translate `G - a` is square integrable and integrable. -/
theorem IsWeakLogSol.integrableOn_norm_sub (hsol : IsWeakLogSol κ mc Ψ U v G) {x : Euc d}
    {r : ℝ} (hr : Metric.closedBall x r ⊆ U) (a : Euc d) :
    IntegrableOn (fun y => ‖G y - a‖) (Metric.closedBall x r) volume ∧
      IntegrableOn (fun y => ‖G y - a‖ ^ 2) (Metric.closedBall x r) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall x r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have h2 : MemLp G 2 (volume.restrict (Metric.closedBall x r)) :=
    (memLp_two_iff_integrable_sq_norm hsol.measurable_grad.aestronglyMeasurable).2
      (hsol.integrableOn_sq x r hr)
  have hc : MemLp (fun _ : Euc d => a) 2 (volume.restrict (Metric.closedBall x r)) :=
    memLp_const a
  have hsub : MemLp (fun y => G y - a) 2 (volume.restrict (Metric.closedBall x r)) := h2.sub hc
  refine ⟨?_, ?_⟩
  · exact (hsub.integrable (by norm_num)).norm
  · exact (memLp_two_iff_integrable_sq_norm hsub.aestronglyMeasurable).1 hsub

/-- The restriction of `G` to a relatively compact open subset of `U` is globally locally
integrable: inside `U` this is `IsWeakLogSol.integrableOn_closedBall`, and away from the closure
the function vanishes.  This is the hypothesis of Campanato's criterion
`Komlos.Literature.exists_holder_of_campanato`. -/
theorem IsWeakLogSol.locallyIntegrable_indicator (hsol : IsWeakLogSol κ mc Ψ U v G)
    {V : Set (Euc d)} (hV : MeasurableSet V) (hVU : closure V ⊆ U) :
    LocallyIntegrable (V.indicator G) volume := by
  intro x
  by_cases hx : x ∈ closure V
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hsol.isOpen x (hVU hx)
    refine ⟨Metric.closedBall x (r / 2), Metric.closedBall_mem_nhds x (by linarith), ?_⟩
    have hsub : Metric.closedBall x (r / 2) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    exact (hsol.integrableOn_closedBall hsub).indicator hV
  · refine ⟨(closure V)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hx, ?_⟩
    refine (integrableOn_zero (μ := volume) (s := (closure V)ᶜ)).congr_fun
      (fun y hy => ?_) isClosed_closure.isOpen_compl.measurableSet
    exact (Set.indicator_of_notMem (fun h => hy (subset_closure h)) G).symm

/-! ### The `L² → L¹` conversion without continuity -/

/-- **`L¹` Campanato bound out of an `L²` (Morrey) bound on a ball**, the integrability version of
`Komlos.Literature.setIntegral_norm_sub_setAverage_le_of_sq`: the gradient field of a weak
solution is a priori only square integrable, never continuous, so the continuity hypothesis of
the original has to be replaced by integrability of `‖W - a‖` and `‖W - a‖²`. -/
theorem setIntegral_norm_sub_le_of_sq' {W : Euc d → Euc d} {x : Euc d} {ρ C₃ α : ℝ}
    (hρ : 0 < ρ) {a : Euc d}
    (hgi : IntegrableOn (fun y => ‖W y - a‖) (Metric.closedBall x ρ) volume)
    (hg2 : IntegrableOn (fun y => ‖W y - a‖ ^ 2) (Metric.closedBall x ρ) volume)
    (hsq : (∫ y in Metric.closedBall x ρ, ‖W y - a‖ ^ 2) ≤ C₃ * ρ ^ ((d : ℝ) + 2 * α)) :
    (∫ y in Metric.closedBall x ρ, ‖W y - a‖) ≤
      (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * ρ ^ ((d : ℝ) + α) := by
  have hfin : volume (Metric.closedBall x ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hvol : volume.real (Metric.closedBall x ρ) =
      ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) :=
    Komlos.Literature.volume_real_closedBall x hρ.le
  have hρα : (0 : ℝ) < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have hpow1 : (ρ ^ α) ^ 2 = ρ ^ (2 * α) := by rw [pow_two, ← Real.rpow_add hρ, two_mul]
  have hpow2 : ρ ^ (2 * α) * ρ ^ d = ρ ^ ((d : ℝ) + 2 * α) := by
    rw [← Real.rpow_natCast ρ d, ← Real.rpow_add hρ]; congr 1; ring
  have hpow3 : ρ ^ ((d : ℝ) + α) * ρ ^ α = ρ ^ ((d : ℝ) + 2 * α) := by
    rw [← Real.rpow_add hρ]; congr 1; ring
  have hkey := Komlos.Literature.two_mul_setIntegral_le_setIntegral_sq_add hgi hg2 hfin
    (t := ρ ^ α)
  have hbig : 2 * ρ ^ α * (∫ y in Metric.closedBall x ρ, ‖W y - a‖) ≤
      (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) * ρ ^ ((d : ℝ) + 2 * α) := by
    refine le_trans hkey ?_
    rw [hvol, hpow1]
    calc (∫ y in Metric.closedBall x ρ, ‖W y - a‖ ^ 2) +
          ρ ^ (2 * α) * (ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))
        ≤ C₃ * ρ ^ ((d : ℝ) + 2 * α) +
            ρ ^ (2 * α) * (ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) := by
          linarith [hsq]
      _ = C₃ * ρ ^ ((d : ℝ) + 2 * α) +
            volume.real (Metric.closedBall (0 : Euc d) 1) * (ρ ^ (2 * α) * ρ ^ d) := by ring
      _ = (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) * ρ ^ ((d : ℝ) + 2 * α) := by
          rw [hpow2]; ring
  have hne : (2 : ℝ) * ρ ^ α ≠ 0 := ne_of_gt (by linarith)
  have hstep : 2 * ρ ^ α * (∫ y in Metric.closedBall x ρ, ‖W y - a‖) ≤
      2 * ρ ^ α *
        ((C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * ρ ^ ((d : ℝ) + α)) := by
    refine hbig.trans (le_of_eq ?_)
    rw [← hpow3]; ring
  calc (∫ y in Metric.closedBall x ρ, ‖W y - a‖)
      = (2 * ρ ^ α)⁻¹ * (2 * ρ ^ α * ∫ y in Metric.closedBall x ρ, ‖W y - a‖) :=
        (inv_mul_cancel_left₀ hne _).symm
    _ ≤ (2 * ρ ^ α)⁻¹ * (2 * ρ ^ α *
          ((C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * ρ ^ ((d : ℝ) + α))) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 (by linarith))
    _ = (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * ρ ^ ((d : ℝ) + α) :=
        inv_mul_cancel_left₀ hne _


/-! ### Excess bounds for a merely square-integrable field -/

/-- `‖W - e‖` and `‖W - e‖²` are integrable on a set of finite measure on which `W` is square
integrable.  (The project's excess toolbox assumes continuity of the field; the gradient field of
a weak solution is only square integrable.) -/
theorem integrableOn_norm_sub_sq {W : Euc d → Euc d} {s : Set (Euc d)} (hs : volume s ≠ ⊤)
    (hm : AEStronglyMeasurable W (volume.restrict s))
    (hWsq : IntegrableOn (fun y => ‖W y‖ ^ 2) s volume) (e : Euc d) :
    IntegrableOn (fun y => ‖W y - e‖) s volume ∧
      IntegrableOn (fun y => ‖W y - e‖ ^ 2) s volume := by
  have hfm : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hs⟩
  have h2 : MemLp W 2 (volume.restrict s) := (memLp_two_iff_integrable_sq_norm hm).2 hWsq
  have hsub : MemLp (fun y => W y - e) 2 (volume.restrict s) := h2.sub (memLp_const e)
  exact ⟨(hsub.integrable (by norm_num)).norm,
    (memLp_two_iff_integrable_sq_norm hsub.aestronglyMeasurable).1 hsub⟩

/-- **The mean minimizes the `L²` deviation**, for a merely integrable field: the integrability
version of `Komlos.Literature.integral_norm_sub_setAverage_sq_le_const`. -/
theorem sqExcess_le_const' {W : Euc d → Euc d} {x : Euc d} {ρ : ℝ} (hρ : 0 < ρ)
    (hW : IntegrableOn W (Metric.closedBall x ρ) volume)
    (hWs : ∀ e : Euc d, IntegrableOn (fun y => ‖W y - e‖ ^ 2) (Metric.closedBall x ρ) volume)
    (a : Euc d) :
    Komlos.Literature.sqExcess W x ρ ≤ ∫ y in Metric.closedBall x ρ, ‖W y - a‖ ^ 2 := by
  have hfin : volume (Metric.closedBall x ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hreal : (0 : ℝ) < volume.real (Metric.closedBall x ρ) :=
    Komlos.Literature.volume_real_closedBall_pos' x hρ
  set mm : Euc d := ⨍ z in Metric.closedBall x ρ, W z with hmm
  have hfmi : IntegrableOn (fun y => W y - mm) (Metric.closedBall x ρ) volume :=
    hW.sub (integrableOn_const hfin)
  have hinner : IntegrableOn (fun y => (2 : ℝ) * ⟪mm - a, W y - mm⟫)
      (Metric.closedBall x ρ) volume := (hfmi.const_inner (mm - a)).const_mul 2
  have hzero : ∫ y in Metric.closedBall x ρ, (W y - mm) = 0 := by
    rw [integral_sub hW (integrableOn_const hfin), setIntegral_const, hmm, setAverage_eq,
      smul_smul, mul_inv_cancel₀ hreal.ne', one_smul, sub_self]
  have hI : ∫ y in Metric.closedBall x ρ, (2 : ℝ) * ⟪mm - a, W y - mm⟫ = 0 := by
    rw [integral_const_mul, integral_inner hfmi, hzero, inner_zero_right, mul_zero]
  rw [Komlos.Literature.sqExcess_eq, ← hmm, ← sub_nonneg, ← integral_sub (hWs a) (hWs mm)]
  have hpt : ∀ y : Euc d, ‖W y - a‖ ^ 2 - ‖W y - mm‖ ^ 2 =
      (2 : ℝ) * ⟪mm - a, W y - mm⟫ + ‖mm - a‖ ^ 2 := by
    intro y
    rw [show W y - a = (mm - a) + (W y - mm) by abel, norm_add_sq_real]
    ring
  simp only [hpt]
  rw [integral_add hinner (integrableOn_const hfin), hI, setIntegral_const, smul_eq_mul, zero_add]
  exact mul_nonneg hreal.le (sq_nonneg _)

/-- Monotonicity of the `L²` excess in the radius, for a merely integrable field. -/
theorem sqExcess_mono' {W : Euc d → Euc d} {x : Euc d} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hW : IntegrableOn W (Metric.closedBall x r) volume)
    (hWs : ∀ e : Euc d, IntegrableOn (fun y => ‖W y - e‖ ^ 2) (Metric.closedBall x r) volume) :
    Komlos.Literature.sqExcess W x ρ ≤ Komlos.Literature.sqExcess W x r := by
  have hsub : Metric.closedBall x ρ ⊆ Metric.closedBall x r :=
    Metric.closedBall_subset_closedBall hρr
  refine le_trans (sqExcess_le_const' hρ (hW.mono_set hsub) (fun e => (hWs e).mono_set hsub)
    (⨍ z in Metric.closedBall x r, W z)) ?_
  exact setIntegral_mono_set (hWs _) (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE

/-- `‖G‖²` is locally integrable on `U`. -/
theorem IsWeakLogSol.locallyIntegrableOn_sq (hsol : IsWeakLogSol κ mc Ψ U v G) :
    LocallyIntegrableOn (fun y => ‖G y‖ ^ 2) U volume := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hsol.isOpen x hx
  refine ⟨Metric.closedBall x (r / 2),
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x (by linarith)), ?_⟩
  exact hsol.integrableOn_sq x (r / 2)
    ((Metric.closedBall_subset_ball (by linarith)).trans hball)

/-- A radius and an energy bound that are **uniform on a compact subset** of `U`: on
`Metric.cthickening R₀ S`, a compact subset of `U`, the field `G` has finite energy, which dominates the
energy on every ball `B(x, R₀)` with `x ∈ S`. -/
theorem IsWeakLogSol.exists_uniform_sq_bound (hsol : IsWeakLogSol κ mc Ψ U v G)
    {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ R₀ M : ℝ, 0 < R₀ ∧ 0 ≤ M ∧ (∀ x ∈ S, Metric.closedBall x R₀ ⊆ U) ∧
      ∀ x ∈ S, (∫ y in Metric.closedBall x R₀, ‖G y‖ ^ 2) ≤ M := by
  obtain ⟨δ, hδ, hδsub⟩ := hS.exists_cthickening_subset_open hsol.isOpen hSU
  have hKc : IsCompact (Metric.cthickening (δ / 2) S) := hS.cthickening
  have hKU : Metric.cthickening (δ / 2) S ⊆ U :=
    (Metric.cthickening_mono (by linarith) S).trans hδsub
  have hKint : IntegrableOn (fun y => ‖G y‖ ^ 2) (Metric.cthickening (δ / 2) S) volume :=
    hsol.locallyIntegrableOn_sq.integrableOn_compact_subset hKU hKc
  refine ⟨δ / 2, ∫ y in Metric.cthickening (δ / 2) S, ‖G y‖ ^ 2, by linarith,
    integral_nonneg fun _ => sq_nonneg _, ?_, ?_⟩
  · exact fun x hx => (Metric.closedBall_subset_cthickening hx (δ / 2)).trans hKU
  · exact fun x hx => setIntegral_mono_set hKint (Eventually.of_forall fun _ => sq_nonneg _)
      (Metric.closedBall_subset_cthickening hx (δ / 2)).eventuallyLE


/-! ### Uniform Hölder and Morrey bounds on a compact subset -/

/-- **Links 4 and 5, made uniform on a compact subset of `U`.**  `IsWeakLogSol.exists_local_holder`
and `IsWeakLogSol.exists_morrey` are stated at a single point of `U`, with radii and constants
depending on that point; a finite subcover turns them into one statement with constants uniform
on a compact `S ⊆ U`, at the price of replacing the two exponents by their minimum. -/
theorem IsWeakLogSol.exists_uniform_holder_morrey (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ mc Ψ U v G) {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ Cu α R : ℝ, 0 ≤ Cu ∧ 0 < α ∧ α < 1 ∧ 0 < R ∧ R ≤ 1 / 2 ∧
      (∀ x ∈ S, Metric.closedBall x R ⊆ U) ∧
      (∀ x ∈ S, ∀ y ∈ Metric.closedBall x R, ∀ y' ∈ Metric.closedBall x R,
        |v y - v y'| ≤ Cu * dist y y' ^ α) ∧
      (∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ R →
        (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ Cu * t ^ ((d : ℝ) - 2 + 2 * α)) := by
  classical
  by_cases hSne : S.Nonempty
  case neg =>
    refine ⟨0, 1 / 2, 1 / 2, le_rfl, by norm_num, by norm_num, by norm_num, le_rfl, ?_, ?_, ?_⟩ <;>
      · intro x hx
        exact absurd ⟨x, hx⟩ hSne
  -- the local data, made total
  have hloc : ∀ x₀ : Euc d, ∃ r Cl α : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ 0 < α ∧ α < 1 ∧
      (x₀ ∈ S → (Metric.closedBall x₀ (2 * r) ⊆ U ∧
        (∀ y ∈ Metric.closedBall x₀ (2 * r), ∀ y' ∈ Metric.closedBall x₀ (2 * r),
          |v y - v y'| ≤ Cl * dist y y' ^ α) ∧
        (∀ y ∈ Metric.ball x₀ r, ∀ t : ℝ, 0 < t → t ≤ r →
          (∫ z in Metric.closedBall y t, ‖G z‖ ^ 2) ≤ Cl * t ^ ((d : ℝ) - 2 + 2 * α)))) := by
    intro x₀
    by_cases hx : x₀ ∈ S
    · obtain ⟨r4, Ch, α4, hr4, hα4, hα41, hb4, hhol⟩ := hsol.exists_local_holder hΨ (hSU hx)
      obtain ⟨r5, Cm, α5, hr5, hα5, hα51, hb5, hmor⟩ := hsol.exists_morrey hΨ (hSU hx)
      refine ⟨min (min (r4 / 2) (r5 / 2)) (1 / 4), max (max Ch Cm) 0, min α4 α5, ?_, ?_, ?_, ?_, ?_⟩
      · exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      · exact le_trans (min_le_right _ _) (by norm_num)
      · exact lt_min hα4 hα5
      · exact lt_of_le_of_lt (min_le_left _ _) hα41
      · intro _
        have hle4 : 2 * min (min (r4 / 2) (r5 / 2)) (1 / 4) ≤ r4 := by
          have := (min_le_left (min (r4 / 2) (r5 / 2)) (1 / 4)).trans (min_le_left (r4/2) (r5/2))
          linarith
        have hle5 : min (min (r4 / 2) (r5 / 2)) (1 / 4) ≤ r5 / 2 :=
          (min_le_left _ _).trans (min_le_right _ _)
        refine ⟨(Metric.closedBall_subset_closedBall hle4).trans hb4, ?_, ?_⟩
        · intro y hy y' hy'
          have hy2 : y ∈ Metric.closedBall x₀ r4 := Metric.closedBall_subset_closedBall hle4 hy
          have hy'2 : y' ∈ Metric.closedBall x₀ r4 := Metric.closedBall_subset_closedBall hle4 hy'
          refine (hhol y hy2 y' hy'2).trans ?_
          have hdle : dist y y' ≤ 1 := by
            have h1 : dist y y' ≤ dist y x₀ + dist x₀ y' := dist_triangle _ _ _
            have h2 : dist y x₀ ≤ 2 * min (min (r4 / 2) (r5 / 2)) (1 / 4) :=
              Metric.mem_closedBall.1 hy
            have h3 : dist x₀ y' ≤ 2 * min (min (r4 / 2) (r5 / 2)) (1 / 4) := by
              rw [dist_comm]; exact Metric.mem_closedBall.1 hy'
            have h4 : min (min (r4 / 2) (r5 / 2)) (1 / 4) ≤ 1 / 4 := min_le_right _ _
            linarith
          rcases eq_or_lt_of_le (dist_nonneg : (0:ℝ) ≤ dist y y') with h0 | h0
          · rw [← h0, Real.zero_rpow hα4.ne', Real.zero_rpow (lt_min hα4 hα5).ne']
            simp
          · exact mul_le_mul (le_max_of_le_left (le_max_left _ _))
              (Real.rpow_le_rpow_of_exponent_ge h0 hdle (min_le_left _ _))
              (Real.rpow_nonneg dist_nonneg _) (le_max_right _ _)
        · intro y hy t ht htr
          have hy5 : y ∈ Metric.ball x₀ (r5 / 2) :=
            Metric.ball_subset_ball hle5 hy
          have ht5 : t ≤ r5 / 2 := htr.trans hle5
          have hkey := hmor y hy5 t ht ht5
          rw [setIntegral_ball_eq_closedBall (fun z => ‖G z‖ ^ 2) y ht.ne'] at hkey
          refine hkey.trans ?_
          have ht1 : t ≤ 1 := by
            have h14 : min (min (r4 / 2) (r5 / 2)) (1 / 4) ≤ 1 / 4 := min_le_right _ _
            linarith [htr]
          exact mul_le_mul (le_max_of_le_left (le_max_right _ _))
            (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by
              have : min α4 α5 ≤ α5 := min_le_right _ _
              linarith)) (Real.rpow_nonneg ht.le _) (le_max_right _ _)
    · exact ⟨1 / 2, 0, 1 / 2, by norm_num, le_rfl, by norm_num, by norm_num, fun h => absurd h hx⟩
  choose r Cl al hr hr12 hal hal1 hmain using hloc
  -- the finite subcover
  have hcov : S ⊆ ⋃ x₀ ∈ S, Metric.ball x₀ (r x₀) := fun y hy =>
    Set.mem_biUnion hy (Metric.mem_ball_self (hr y))
  obtain ⟨T, hTS, hTfin, hTcov⟩ :=
    hS.elim_finite_subcover_image (fun i _ => Metric.isOpen_ball) hcov
  set F : Finset (Euc d) := hTfin.toFinset with hF
  have hFmem : ∀ i, i ∈ F ↔ i ∈ T := by intro i; rw [hF]; exact hTfin.mem_toFinset
  have hFne : F.Nonempty := by
    obtain ⟨y, hy⟩ := hSne
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (hTcov hy)
    exact ⟨i, (hFmem i).2 hi⟩
  set R : ℝ := F.inf' hFne r with hR
  set α : ℝ := F.inf' hFne al with hα
  set Cu : ℝ := max (F.sup' hFne Cl) 0 with hCu
  have hRpos : 0 < R := (Finset.lt_inf'_iff hFne).2 fun i _ => hr i
  have hR12 : R ≤ 1 / 2 := by
    obtain ⟨i, hi⟩ := hFne
    exact (Finset.inf'_le _ hi).trans (hr12 i)
  have hαpos : 0 < α := (Finset.lt_inf'_iff hFne).2 fun i _ => hal i
  have hα1 : α < 1 := by
    obtain ⟨i, hi⟩ := hFne
    exact lt_of_le_of_lt (Finset.inf'_le _ hi) (hal1 i)
  -- the point-to-cover dictionary
  have hpick : ∀ x ∈ S, ∃ i ∈ F, x ∈ Metric.ball i (r i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hTcov hx)
    exact ⟨i, (hFmem i).2 hi, hxi⟩
  have hsub : ∀ x ∈ S, ∀ i ∈ F, x ∈ Metric.ball i (r i) →
      Metric.closedBall x R ⊆ Metric.closedBall i (2 * r i) := by
    intro x hx i hi hxi y hy
    have h1 : dist y x ≤ R := Metric.mem_closedBall.1 hy
    have h2 : dist x i ≤ r i := (Metric.mem_ball.1 hxi).le
    have h3 : R ≤ r i := Finset.inf'_le _ hi
    have : dist y i ≤ dist y x + dist x i := dist_triangle _ _ _
    exact Metric.mem_closedBall.2 (by linarith)
  refine ⟨Cu, α, R, le_max_right _ _, hαpos, hα1, hRpos, hR12, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := hpick x hx
    exact (hsub x hx i hi hxi).trans (hmain i (hTS ((hFmem i).1 hi))).1
  · intro x hx y hy y' hy'
    obtain ⟨i, hi, hxi⟩ := hpick x hx
    obtain ⟨-, hhol, -⟩ := hmain i (hTS ((hFmem i).1 hi))
    refine (hhol y (hsub x hx i hi hxi hy) y' (hsub x hx i hi hxi hy')).trans ?_
    have hdle : dist y y' ≤ 1 := by
      have h1 : dist y y' ≤ dist y x + dist x y' := dist_triangle _ _ _
      have h2 : dist y x ≤ R := Metric.mem_closedBall.1 hy
      have h3 : dist x y' ≤ R := by rw [dist_comm]; exact Metric.mem_closedBall.1 hy'
      linarith
    have hαi : α ≤ al i := Finset.inf'_le _ hi
    have hCi : Cl i ≤ Cu := le_trans (Finset.le_sup' _ hi) (le_max_left _ _)
    rcases eq_or_lt_of_le (dist_nonneg : (0:ℝ) ≤ dist y y') with h0 | h0
    · rw [← h0, Real.zero_rpow (hal i).ne', Real.zero_rpow hαpos.ne']
      simp
    · exact mul_le_mul hCi (Real.rpow_le_rpow_of_exponent_ge h0 hdle hαi)
        (Real.rpow_nonneg dist_nonneg _) (le_max_right _ _)
  · intro x hx t ht htR
    obtain ⟨i, hi, hxi⟩ := hpick x hx
    obtain ⟨-, -, hmor⟩ := hmain i (hTS ((hFmem i).1 hi))
    have hRi : R ≤ r i := Finset.inf'_le _ hi
    refine (hmor x hxi t ht (htR.trans hRi)).trans ?_
    have ht1 : t ≤ 1 := by linarith [htR.trans hR12]
    have hαi : α ≤ al i := Finset.inf'_le _ hi
    have hCi : Cl i ≤ Cu := le_trans (Finset.le_sup' _ hi) (le_max_left _ _)
    exact mul_le_mul hCi
      (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith))
      (Real.rpow_nonneg ht.le _) (le_max_right _ _)


/-! ### The energy decay of a `Ψ`-harmonic gradient field -/

/-- **The local sup bound and the `L²` energy decay for a `Ψ`-harmonic gradient field.**

`∫_{B_ρ} ‖W‖² ≤ Cs (2ρ/r)^d ∫_{B_{r/2}} ‖W‖²`  for `0 < ρ ≤ r/2`.

This is the "good exponent `d`" that the Morrey bootstrap of
`IsWeakLogSol.exists_harmonic_comparison` iterates.

**History.**  The original proof read it off a *sup* bound `‖W y‖² ≤ C ⨍_{B_{r/2}} ‖W‖²` for
`y ∈ B_{r/2}`, coming from the scale-invariant Hölder estimate
`exists_regHarmonic_holder_field`.  Lane `reg/c2h` showed that estimate — and the sup bound on
the *same* ball that it implies — to be **false**: for `Ψ = ‖·‖²/2` and
`H_n = ∇Re(z^{n+1}/((n+1)2^{-n}))` on `B_1 ⊆ ℝ²` one has `⨍_{B_{1/2}}‖H_n‖² = 1/(n+1) → 0`
while `‖H_n(±1/2)‖ = 1` (`NOTES_L3h.md`, DEVIATION 1).  The statement below is nevertheless
true, and is the standard consequence of the Campanato decay
`exists_regHarmonic_campanato_field` (lane `reg/c2h`) that the *interior* sup bound gives.

**Proof** (lane `L8`, `reg/energy-decay`; details in `NOTES_energy-decay.md`).  Write `R = r/2`,
`A_t = sqExcess W x₀ t`, `E = ∫_{B_R}‖W‖²`.  Pythagoras
(`setIntegral_norm_sq_eq_sqExcess_add`) splits `∫_{B_ρ}‖W‖² = A_ρ + |B_ρ| ‖(W)_ρ‖²`.  The
excess term is `≤ Cdec (ρ/R)^d E` because `(ρ/R)^{2β} ≤ 1` and `A_R ≤ E`.  For the mean term,
`|B_ρ| ‖(W)_ρ - (W)_t‖² ≤ A_t` (`volume_real_mul_norm_setAverage_sub_sq_le`) together with the
decay and the volume ratio `|B_ρ| ≥ 2^{-d}(t/R)^d|B_R|` give
`‖(W)_ρ - (W)_t‖ ≤ √(2^d Cdec) (t/R)^β √(A_R/|B_R|)` for comparable radii `ρ ≤ t ≤ 2ρ`, and the
geometric series over the halvings of `R` (`exists_norm_setAverage_sub_setAverage_bound`) turns
that into `‖(W)_ρ - (W)_R‖ ≤ K √(A_R/|B_R|)` for *every* `ρ ∈ (0, R]` — so no separate
non-dyadic case is needed.  Since `A_R ≤ E` and `‖(W)_R‖² ≤ E/|B_R|` (Jensen), this bounds
`|B_ρ| ‖(W)_ρ‖²` by `(K+1)² (ρ/R)^d E`, and `Cs = Cdec + (K+1)²` works.  `d = 0` needs no
special case. -/
theorem exists_regHarmonic_energy_decay (hΨ : IsRegProfile Ψ) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧
      ∀ (x₀ : Euc d) (r : ℝ), 0 < r → ∀ (hf : Euc d → ℝ) (H : Euc d → Euc d),
        IsRegHarmonicField Ψ (Metric.ball x₀ r) hf H →
        IsLocSqIntegrableOn (Metric.ball x₀ r) hf →
        ∃ W : Euc d → Euc d, ContinuousOn W (Metric.ball x₀ r) ∧
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), H x = W x) ∧
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 2 →
            (∫ y in Metric.closedBall x₀ ρ, ‖W y‖ ^ 2) ≤
              Cs * (2 * ρ / r) ^ ((d : ℝ)) *
                ∫ y in Metric.closedBall x₀ (r / 2), ‖W y‖ ^ 2 := by
  obtain ⟨Cdec, β, hCdec, hβ, hβ1, hcamp⟩ := exists_regHarmonic_campanato_field hΨ
  obtain ⟨K, hK0, htel⟩ := exists_norm_setAverage_sub_setAverage_bound (d := d) hCdec hβ
  refine ⟨Cdec + (K + 1) ^ 2, add_nonneg hCdec (sq_nonneg _), ?_⟩
  intro x₀ r hr hfun H hfield hL2
  obtain ⟨W, hWc, hWae, hdecW⟩ := hcamp x₀ r hr hfun H hfield hL2
  refine ⟨W, hWc, hWae, ?_⟩
  intro ρ hρ hρr
  set R : ℝ := r / 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  have hWR : ContinuousOn W (Metric.closedBall x₀ R) :=
    hWc.mono (Metric.closedBall_subset_ball (by rw [hRdef]; linarith))
  -- the Campanato decay, written with the ratio `t / R` instead of `2 t / r`
  have hratio : ∀ t : ℝ, 2 * t / r = t / R := by
    intro t
    rw [hRdef, div_div_eq_mul_div]
    ring
  have hdec' : ∀ t : ℝ, 0 < t → t ≤ R →
      Komlos.Literature.sqExcess W x₀ t ≤
        Cdec * (t / R) ^ ((d : ℝ) + 2 * β) * Komlos.Literature.sqExcess W x₀ R := by
    intro t ht htR
    have h := hdecW t ht htR
    rwa [hratio t] at h
  -- abbreviations
  set E : ℝ := ∫ y in Metric.closedBall x₀ R, ‖W y‖ ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; exact integral_nonneg fun _ => sq_nonneg _
  have hvR : (0 : ℝ) < volume.real (Metric.closedBall x₀ R) :=
    Komlos.Literature.volume_real_closedBall_pos' x₀ hR
  have hA0 : 0 ≤ Komlos.Literature.sqExcess W x₀ R := Komlos.Literature.sqExcess_nonneg _ _ _
  have hAE : Komlos.Literature.sqExcess W x₀ R ≤ E := by
    have h := setIntegral_norm_sq_eq_sqExcess_add hR hWR
    have h2 : (0 : ℝ) ≤ volume.real (Metric.closedBall x₀ R) *
        ‖⨍ z in Metric.closedBall x₀ R, W z‖ ^ 2 := by positivity
    rw [← hE] at h
    linarith
  -- the two means are both bounded by `√(E / |B_R|)`
  set S : ℝ := Real.sqrt (E / volume.real (Metric.closedBall x₀ R)) with hS
  have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  have hS2 : S ^ 2 = E / volume.real (Metric.closedBall x₀ R) := by
    rw [hS]; exact Real.sq_sqrt (by positivity)
  have hmR : ‖⨍ z in Metric.closedBall x₀ R, W z‖ ≤ S := by
    refine edec_le_of_sq_le_sq ?_ hS0
    rw [hS2, le_div_iff₀ hvR]
    have h := volume_real_mul_norm_setAverage_sq_le hR hWR
    rw [← hE] at h
    linarith
  have hDS : Real.sqrt (Komlos.Literature.sqExcess W x₀ R /
      volume.real (Metric.closedBall x₀ R)) ≤ S := by
    rw [hS]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hAE hvR.le)
  have hmρ : ‖⨍ z in Metric.closedBall x₀ ρ, W z‖ ≤ (K + 1) * S := by
    have h1 : ‖⨍ z in Metric.closedBall x₀ ρ, W z‖ ≤
        ‖(⨍ z in Metric.closedBall x₀ ρ, W z) - ⨍ z in Metric.closedBall x₀ R, W z‖ +
          ‖⨍ z in Metric.closedBall x₀ R, W z‖ := by
      calc ‖⨍ z in Metric.closedBall x₀ ρ, W z‖
          = ‖((⨍ z in Metric.closedBall x₀ ρ, W z) - ⨍ z in Metric.closedBall x₀ R, W z) +
              ⨍ z in Metric.closedBall x₀ R, W z‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖(⨍ z in Metric.closedBall x₀ ρ, W z) - ⨍ z in Metric.closedBall x₀ R, W z‖ ≤
        K * S :=
      (htel W x₀ R hR hWR hdec' ρ hρ hρr).trans (mul_le_mul_of_nonneg_left hDS hK0)
    have h3 : (K + 1) * S = K * S + S := by ring
    linarith
  -- the contribution of the mean
  have hvolρ : volume.real (Metric.closedBall x₀ ρ) =
      (ρ / R) ^ d * volume.real (Metric.closedBall x₀ R) :=
    volume_real_closedBall_eq_ratio x₀ hρ.le hR
  have hd0 : (0 : ℝ) ≤ (ρ / R) ^ d := by positivity
  have hmean : volume.real (Metric.closedBall x₀ ρ) *
      ‖⨍ z in Metric.closedBall x₀ ρ, W z‖ ^ 2 ≤ (K + 1) ^ 2 * ((ρ / R) ^ d * E) := by
    have h1 : ‖⨍ z in Metric.closedBall x₀ ρ, W z‖ ^ 2 ≤ ((K + 1) * S) ^ 2 := by
      have h0 := norm_nonneg (⨍ z in Metric.closedBall x₀ ρ, W z)
      nlinarith [hmρ]
    have h2 : (0 : ℝ) ≤ volume.real (Metric.closedBall x₀ ρ) := measureReal_nonneg
    calc volume.real (Metric.closedBall x₀ ρ) * ‖⨍ z in Metric.closedBall x₀ ρ, W z‖ ^ 2
        ≤ volume.real (Metric.closedBall x₀ ρ) * ((K + 1) * S) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = (K + 1) ^ 2 * ((ρ / R) ^ d * E) := by
          rw [hvolρ, mul_pow, hS2]
          field_simp
          try ring
  -- the contribution of the excess
  have hexc : Komlos.Literature.sqExcess W x₀ ρ ≤ Cdec * ((ρ / R) ^ d * E) := by
    have h1 := hdec' ρ hρ hρr
    have hq : (0 : ℝ) < ρ / R := div_pos hρ hR
    have hsplit : (ρ / R) ^ ((d : ℝ) + 2 * β) = (ρ / R) ^ d * (ρ / R) ^ (2 * β) := by
      rw [Real.rpow_add hq, Real.rpow_natCast]
    have hle1 : (ρ / R) ^ (2 * β) ≤ 1 :=
      Real.rpow_le_one hq.le (by rw [div_le_one hR]; exact hρr) (by linarith)
    have hP0 : (0 : ℝ) ≤ (ρ / R) ^ (2 * β) := Real.rpow_nonneg hq.le _
    have hc0 : (0 : ℝ) ≤ Cdec * ((ρ / R) ^ d * (ρ / R) ^ (2 * β)) :=
      mul_nonneg hCdec (mul_nonneg hd0 hP0)
    have hcE : (0 : ℝ) ≤ Cdec * ((ρ / R) ^ d * E) := mul_nonneg hCdec (mul_nonneg hd0 hE0)
    rw [hsplit] at h1
    calc Komlos.Literature.sqExcess W x₀ ρ
        ≤ Cdec * ((ρ / R) ^ d * (ρ / R) ^ (2 * β)) * Komlos.Literature.sqExcess W x₀ R := h1
      _ ≤ Cdec * ((ρ / R) ^ d * (ρ / R) ^ (2 * β)) * E := mul_le_mul_of_nonneg_left hAE hc0
      _ = Cdec * ((ρ / R) ^ d * E) * (ρ / R) ^ (2 * β) := by ring
      _ ≤ Cdec * ((ρ / R) ^ d * E) * 1 := mul_le_mul_of_nonneg_left hle1 hcE
      _ = Cdec * ((ρ / R) ^ d * E) := by ring
  -- assemble
  have hpow : (2 * ρ / r) ^ ((d : ℝ)) = (ρ / R) ^ d := by
    rw [hratio ρ, Real.rpow_natCast]
  have hPyth := setIntegral_norm_sq_eq_sqExcess_add hρ
    (hWR.mono (Metric.closedBall_subset_closedBall hρr))
  rw [hpow, hPyth]
  have hid : (Cdec + (K + 1) ^ 2) * (ρ / R) ^ d * E =
      Cdec * ((ρ / R) ^ d * E) + (K + 1) ^ 2 * ((ρ / R) ^ d * E) := by ring
  rw [hid]
  linarith


/-! ### The comparison estimate for the `Ψ`-harmonic replacement -/

/-- **The comparison estimate.**  If `z ∈ W₀^{1,2}(B̄)` is *essentially bounded by `M`* and
`H = 1_{B̄} G - ∇z` is the `Ψ`-harmonic replacement field (so that the Euler–Lagrange equation
`∫ ⟪∇Ψ H, ∇z⟫ = 0` holds), then strong monotonicity of `∇Ψ` gives

`c ∫ ‖∇z‖² ≤ ∫ |f z|`,  `f = regLogRhs κ m Ψ v G`.

The two inputs are `comparison_energy_le` (**proved**, `InteriorRegularity.lean`) and the
Sobolev-test form of the equation for `v`, `IsWeakLogSol.weakEq_memW0` (link 3), which is exactly
where the essential boundedness of the test function `z` — i.e. the maximum principle for the
replacement — is needed: the right-hand side `f` has natural growth and is only `L¹`. -/
theorem IsWeakLogSol.replacement_comparison_le {c C : ℝ} (hΨ : IsRegProfile Ψ)
    (hP : IsRegProfileWith Ψ c C)
    (hsol : IsWeakLogSol κ mc Ψ U v G) {x : Euc d} {s s' : ℝ} (hss' : s < s')
    (hsub' : Metric.closedBall x s' ⊆ U) {z : Euc d → ℝ} {Z H : Euc d → Euc d}
    (hz : MemW0 2 (Metric.closedBall x s) z) (hZz : weakGrad z =ᵐ[volume] Z)
    (hHdef : ∀ y, H y = (Metric.closedBall x s).indicator G y - Z y)
    (hHmem : MemLp H (ENNReal.ofReal 2))
    (hEL : (∫ y, ⟪gradient Ψ (H y), weakGrad z y⟫) = 0)
    {M : ℝ} (hM : ∀ y, |z y| ≤ M) :
    c * (∫ y, ‖weakGrad z y‖ ^ 2) ≤ ∫ y, |regLogRhs κ mc Ψ v G y * z y| := by
  have h2e : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  set B : Set (Euc d) := Metric.closedBall x s with hB
  set GB : Euc d → Euc d := B.indicator G with hGB
  have hsubU : B ⊆ U := (Metric.closedBall_subset_closedBall hss'.le).trans hsub'
  have hGBm : MemLp GB (ENNReal.ofReal 2) := by
    rw [hGB, h2e]
    refine (memLp_indicator_iff_restrict measurableSet_closedBall).2 ?_
    exact (memLp_two_iff_integrable_sq_norm hsol.measurable_grad.aestronglyMeasurable).2
      (hsol.integrableOn_sq x s hsubU)
  have hz0 : ∀ᵐ y, y ∉ B → weakGrad z y = 0 := hz.weakGrad_eq_zero_of_isClosed Metric.isClosed_closedBall
  -- `GB - H = ∇z` almost everywhere
  have hGH : ∀ᵐ y, GB y - H y = weakGrad z y := by
    filter_upwards [hZz] with y hy
    rw [hHdef y, hy]
    abel
  -- the homogeneous equation tested with `z`
  have heq2 : (∫ y, ⟪gradient Ψ (H y), GB y - H y⟫) = 0 := by
    rw [← hEL]
    exact integral_congr_ae (by filter_upwards [hGH] with y hy; rw [hy])
  -- the inhomogeneous equation tested with `z`
  have heq1 : (∫ y, ⟪gradient Ψ (GB y), GB y - H y⟫) =
      -∫ y, regLogRhs κ mc Ψ v G y * z y := by
    have hlink3 := hsol.weakEq_memW0 hΨ hsub' (isCompact_closedBall x s)
      (Metric.closedBall_subset_ball hss') hz hz0 hM
    rw [← hlink3]
    refine integral_congr_ae ?_
    filter_upwards [hGH, hz0] with y hy hy0
    show ⟪gradient Ψ (GB y), GB y - H y⟫ = ⟪gradient Ψ (G y), weakGrad z y⟫
    rw [hy]
    by_cases hyB : y ∈ B
    · rw [hGB, Set.indicator_of_mem hyB]
    · rw [hy0 hyB, inner_zero_right, inner_zero_right]
  have hkey := comparison_energy_le hP hGBm hHmem heq1 heq2
  have hsq : (∫ y, ‖GB y - H y‖ ^ 2) = ∫ y, ‖weakGrad z y‖ ^ 2 :=
    integral_congr_ae (by filter_upwards [hGH] with y hy; rw [hy])
  rwa [hsq] at hkey

/-! ### The size of the right-hand side -/

/-- The right-hand side `f = κ v + 2 m + B(∇v)` of the equation for `v` has natural growth,
`|f| ≤ M₁ + 2C‖∇v‖²`, so on a ball where `v` is bounded and the Morrey bound holds its `L¹` norm
is `O(t^{d-2+2α})`. -/
theorem IsWeakLogSol.integral_abs_rhs_le (hΨ : IsRegProfile Ψ) {c C : ℝ}
    (hP : IsRegProfileWith Ψ c C) (hsol : IsWeakLogSol κ mc Ψ U v G)
    {x : Euc d} {t Mv Cu α : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 < α) (hα1 : α < 1)
    (hCu : 0 ≤ Cu) (hbU : Metric.closedBall x t ⊆ U)
    (hvbd : ∀ y ∈ Metric.closedBall x t, |v y| ≤ Mv)
    (hGmor : (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ Cu * t ^ ((d : ℝ) - 2 + 2 * α)) :
    IntegrableOn (fun y => |regLogRhs κ mc Ψ v G y|) (Metric.closedBall x t) volume ∧
      (∫ y in Metric.closedBall x t, |regLogRhs κ mc Ψ v G y|) ≤
        ((|κ| * Mv + 2 * |mc| + 2 * |Ψ 0|) *
          volume.real (Metric.closedBall (0 : Euc d) 1) + 2 * C * Cu) *
          t ^ ((d : ℝ) - 2 + 2 * α) := by
  have hC0 : (0 : ℝ) ≤ C := hP.C_nonneg
  have hMv0 : 0 ≤ Mv := le_trans (abs_nonneg _) (hvbd x (Metric.mem_closedBall_self ht.le))
  set V : ℝ := volume.real (Metric.closedBall (0 : Euc d) 1) with hV
  have hVpos : 0 < V := Komlos.Literature.volume_real_closedBall_pos
  set M1 : ℝ := |κ| * Mv + 2 * |mc| + 2 * |Ψ 0| with hM1
  have hM10 : 0 ≤ M1 := by positivity
  have hfmeas : Measurable fun y => regLogRhs κ mc Ψ v G y := by
    show Measurable fun y => κ * v y + 2 * mc + regNatGrowth Ψ (G y)
    exact ((measurable_const.mul hsol.measurable).add measurable_const).add
      ((continuous_regNatGrowth hΨ).measurable.comp hsol.measurable_grad)
  have hfbd : ∀ y ∈ Metric.closedBall x t, |regLogRhs κ mc Ψ v G y| ≤
      M1 + 2 * C * ‖G y‖ ^ 2 := by
    intro y hy
    have hnat := abs_regNatGrowth_le hP (G y)
    have h1 : |κ * v y + 2 * mc + regNatGrowth Ψ (G y)| ≤
        |κ * v y + 2 * mc| + |regNatGrowth Ψ (G y)| := abs_add_le _ _
    have h2 : |κ * v y + 2 * mc| ≤ |κ * v y| + |2 * mc| := abs_add_le _ _
    have h3 : |κ * v y| = |κ| * |v y| := abs_mul _ _
    have h4 : |κ| * |v y| ≤ |κ| * Mv := mul_le_mul_of_nonneg_left (hvbd y hy) (abs_nonneg _)
    have h5 : |2 * mc| = 2 * |mc| := by rw [abs_mul]; simp
    show |κ * v y + 2 * mc + regNatGrowth Ψ (G y)| ≤ M1 + 2 * C * ‖G y‖ ^ 2
    rw [hM1]
    linarith
  have hGB : IntegrableOn (fun y => ‖G y‖ ^ 2) (Metric.closedBall x t) volume :=
    hsol.integrableOn_sq x t hbU
  have hconst : IntegrableOn (fun _ : Euc d => M1) (Metric.closedBall x t) volume :=
    integrableOn_const measure_closedBall_lt_top.ne
  have hdom : IntegrableOn (fun y => M1 + 2 * C * ‖G y‖ ^ 2) (Metric.closedBall x t) volume :=
    hconst.add (hGB.const_mul _)
  have hfint : IntegrableOn (fun y => |regLogRhs κ mc Ψ v G y|) (Metric.closedBall x t) volume := by
    refine Integrable.mono' hdom hfmeas.abs.aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_closedBall] with y hy
    rw [Real.norm_eq_abs, abs_abs]
    exact hfbd y hy
  refine ⟨hfint, ?_⟩
  have h1 := setIntegral_mono_on hfint hdom measurableSet_closedBall hfbd
  have h2 : (∫ y in Metric.closedBall x t, (M1 + 2 * C * ‖G y‖ ^ 2)) =
      M1 * volume.real (Metric.closedBall x t) +
        2 * C * ∫ y in Metric.closedBall x t, ‖G y‖ ^ 2 := by
    rw [integral_add hconst (hGB.const_mul _), setIntegral_const, integral_const_mul, smul_eq_mul]
    ring
  rw [h2, Komlos.Literature.volume_real_closedBall x ht.le] at h1
  have hpowle : (t ^ d : ℝ) ≤ t ^ ((d : ℝ) - 2 + 2 * α) := by
    rw [← Real.rpow_natCast t d]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have h3 : M1 * (t ^ d * V) ≤ M1 * V * t ^ ((d : ℝ) - 2 + 2 * α) := by
    calc M1 * (t ^ d * V) = M1 * V * t ^ d := by ring
      _ ≤ M1 * V * t ^ ((d : ℝ) - 2 + 2 * α) :=
        mul_le_mul_of_nonneg_left hpowle (mul_nonneg hM10 hVpos.le)
  have h4 : 2 * C * (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤
      2 * C * Cu * t ^ ((d : ℝ) - 2 + 2 * α) := by
    have := mul_le_mul_of_nonneg_left hGmor (by linarith : (0:ℝ) ≤ 2 * C)
    linarith [this]
  linarith

/-! ### The comparison bound with the exponent `d - 2 + 3α` -/

/-- **The comparison bound.**  Assembling the `Ψ`-harmonic replacement
(`IsWeakLogSol.exists_psi_harmonic_replacement`), the two-sided maximum principle
(`regDirEnergy_min_abs_le`), the comparison estimate
(`IsWeakLogSol.replacement_comparison_le`) and the uniform Hölder/Morrey data gives

`∫_{B_r} ‖G - H‖² ≤ Cb r^{d-2+3α}`

for the replacement field `H` on `B_{2r}`.  Indeed `G - H = ∇z` on the ball, the comparison gives
`c ∫ ‖∇z‖² ≤ ∫ |f z| ≤ ‖z‖_∞ ∫_{B_{2r}} |f|`, the maximum principle bounds `‖z‖_∞` by the
oscillation `2 Cu (2r)^α`, and `IsWeakLogSol.integral_abs_rhs_le` bounds `∫_{B_{2r}} |f|` by
`M₂ (2r)^{d-2+2α}`. -/
theorem IsWeakLogSol.exists_replacement_bound (hd : 0 < d) (hΨ : IsRegProfile Ψ)
    {c C : ℝ} (hP : IsRegProfileWith Ψ c C) (hsol : IsWeakLogSol κ mc Ψ U v G)
    {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U)
    {Cu Cm αh αm R : ℝ} (hCu : 0 ≤ Cu) (hCm : 0 ≤ Cm) (hαh : 0 < αh) (hαm : 0 < αm)
    (hαm1 : αm < 1) (hR : 0 < R) (hR12 : R ≤ 1 / 2)
    (hSball : ∀ x ∈ S, Metric.closedBall x R ⊆ U)
    (hhol : ∀ x ∈ S, ∀ y ∈ Metric.closedBall x R, ∀ y' ∈ Metric.closedBall x R,
      |v y - v y'| ≤ Cu * dist y y' ^ αh)
    (hmor : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ R →
      (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ Cm * t ^ ((d : ℝ) - 2 + 2 * αm)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ x ∈ S, ∀ r : ℝ, 0 < r → 3 * r ≤ R →
      ∃ (hfun : Euc d → ℝ) (H : Euc d → Euc d),
        IsRegHarmonicField Ψ (Metric.ball x (2 * r)) hfun H ∧
        IsLocSqIntegrableOn (Metric.ball x (2 * r)) hfun ∧
        IntegrableOn (fun y => ‖G y - H y‖ ^ 2) (Metric.closedBall x r) volume ∧
        (∫ y in Metric.closedBall x r, ‖G y - H y‖ ^ 2) ≤ Cb * r ^ ((d : ℝ) - 2 + 2 * αm + αh) := by
  classical
  obtain ⟨Mv0, hMv0⟩ := hS.exists_bound_of_continuousOn (hsol.continuousOn.mono hSU)
  set Mv : ℝ := max Mv0 0 with hMvdef
  have hMvS : ∀ y ∈ S, |v y| ≤ Mv := fun y hy => by
    have h := hMv0 y hy
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  set V : ℝ := volume.real (Metric.closedBall (0 : Euc d) 1) with hV
  have hVpos : 0 < V := Komlos.Literature.volume_real_closedBall_pos
  have hC0 : (0 : ℝ) ≤ C := hP.C_nonneg
  have hc0 : (0 : ℝ) < c := hP.c_pos
  set M2 : ℝ := (|κ| * (Mv + Cu) + 2 * |mc| + 2 * |Ψ 0|) * V + 2 * C * Cm with hM2
  have hMv0' : (0 : ℝ) ≤ Mv := le_max_right _ _
  have hM20 : 0 ≤ M2 := by positivity
  refine ⟨2 * Cu * M2 / c * (2 : ℝ) ^ ((d : ℝ) - 2 + 2 * αm + αh), by positivity, ?_⟩
  intro x hx r hr h3r
  have h2rR : 2 * r ≤ R := by linarith
  have h2r1 : 2 * r ≤ 1 := by linarith
  have h2rpos : (0 : ℝ) < 2 * r := by linarith
  have hb3U : Metric.closedBall x (3 * r) ⊆ U :=
    (Metric.closedBall_subset_closedBall h3r).trans (hSball x hx)
  have hb2U : Metric.closedBall x (2 * r) ⊆ U :=
    (Metric.closedBall_subset_closedBall h2rR).trans (hSball x hx)
  obtain ⟨z, Z, H, hz, hzm, hZm, hZz, hHmem, hHdef, hGH, hEL, hfield, hmin⟩ :=
    hsol.exists_psi_harmonic_replacement hd hP h2rpos hb2U
  -- the oscillation of `v` on the ball
  have hrα1 : (2 * r) ^ αh ≤ 1 := Real.rpow_le_one (by positivity) h2r1 hαh.le
  have hrα0 : (0 : ℝ) ≤ (2 * r) ^ αh := Real.rpow_nonneg (by positivity) _
  have hosc0 : (0 : ℝ) ≤ 2 * Cu * (2 * r) ^ αh := by positivity
  have hoscbd : ∀ y ∈ Metric.closedBall x (2 * r), |v y - v x| ≤ Cu * (2 * r) ^ αh := by
    intro y hy
    have hyR : y ∈ Metric.closedBall x R := Metric.closedBall_subset_closedBall h2rR hy
    have hxR : x ∈ Metric.closedBall x R := Metric.mem_closedBall_self hR.le
    refine (hhol x hx y hyR x hxR).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (Metric.mem_closedBall.1 hy) hαh.le) hCu
  have hK : ∀ y ∈ Metric.closedBall x (2 * r), v y ≤ v x + Cu * (2 * r) ^ αh := by
    intro y hy
    have h := hoscbd y hy
    have h2 : v y - v x ≤ |v y - v x| := le_abs_self _
    linarith
  have hk : ∀ y ∈ Metric.closedBall x (2 * r), v x - Cu * (2 * r) ^ αh ≤ v y := by
    intro y hy
    have h := hoscbd y hy
    have h2 : -(v y - v x) ≤ |v y - v x| := neg_le_abs _
    linarith
  have hvbd2 : ∀ y ∈ Metric.closedBall x (2 * r), |v y| ≤ Mv + Cu := by
    intro y hy
    have h1 := hoscbd y hy
    have h2 : |v x| ≤ Mv := hMvS x hx
    have h3 : |v y| ≤ |v x| + |v y - v x| := by
      calc |v y| = |v x + (v y - v x)| := by ring_nf
        _ ≤ |v x| + |v y - v x| := abs_add_le _ _
    have h4 : Cu * (2 * r) ^ αh ≤ Cu := by nlinarith
    linarith
  -- the maximum principle
  have hGsq3 : IntegrableOn (fun y => ‖G y‖ ^ 2) (Metric.closedBall x (3 * r)) volume :=
    hsol.integrableOn_sq x (3 * r) hb3U
  have habs := regDirEnergy_min_abs_le hd hP hsol.isOpen hsol.hasWeakGradientOn
    hsol.continuousOn hsol.locallyIntegrableOn_grad
    hsol.measurable_grad.aestronglyMeasurable h2rpos (by linarith : 2 * r < 5 * r / 2)
    (by linarith : 5 * r / 2 < 3 * r) hb3U hGsq3 hz hmin hk hK
  have habs' : ∀ᵐ y, |z y| ≤ 2 * Cu * (2 * r) ^ αh := by
    filter_upwards [habs] with y hy
    calc |z y| ≤ v x + Cu * (2 * r) ^ αh - (v x - Cu * (2 * r) ^ αh) := hy
      _ = 2 * Cu * (2 * r) ^ αh := by ring
  -- truncate `z` to get a *pointwise* bound
  set z' : Euc d → ℝ := fun y => if |z y| ≤ 2 * Cu * (2 * r) ^ αh then z y else 0 with hz'def
  have hz'ae : z =ᵐ[volume] z' := by
    filter_upwards [habs'] with y hy
    show z y = if |z y| ≤ 2 * Cu * (2 * r) ^ αh then z y else 0
    rw [if_pos hy]
  have hz'M : ∀ y, |z' y| ≤ 2 * Cu * (2 * r) ^ αh := by
    intro y
    show |if |z y| ≤ 2 * Cu * (2 * r) ^ αh then z y else 0| ≤ 2 * Cu * (2 * r) ^ αh
    by_cases hcase : |z y| ≤ 2 * Cu * (2 * r) ^ αh
    · rw [if_pos hcase]; exact hcase
    · rw [if_neg hcase, abs_zero]; exact hosc0
  have hz'meas : Measurable z' :=
    Measurable.ite (measurableSet_le hzm.abs measurable_const) hzm measurable_const
  have hz'W : MemW0 2 (Metric.closedBall x (2 * r)) z' := hz.congr hz'ae
  have hz'g : weakGrad z' =ᵐ[volume] weakGrad z :=
    (hz.hasWeakGradient.congr_left hz'ae).weakGrad_ae_eq
  have hZz' : weakGrad z' =ᵐ[volume] Z := hz'g.trans hZz
  have hEL' : (∫ y, ⟪gradient Ψ (H y), weakGrad z' y⟫) = 0 := by
    rw [← hEL]
    exact integral_congr_ae (by filter_upwards [hz'g] with y hy; rw [hy])
  have hcomp := hsol.replacement_comparison_le hΨ hP (by linarith : 2 * r < 3 * r) hb3U
    hz'W hZz' hHdef hHmem hEL' hz'M
  -- the size of the right-hand side
  obtain ⟨hfint, hfB⟩ := hsol.integral_abs_rhs_le hΨ hP h2rpos h2r1 hαm hαm1 hCm hb2U hvbd2
    (hmor x hx (2 * r) h2rpos h2rR)
  have hfmeas : Measurable fun y => regLogRhs κ mc Ψ v G y := by
    show Measurable fun y => κ * v y + 2 * mc + regNatGrowth Ψ (G y)
    exact ((measurable_const.mul hsol.measurable).add measurable_const).add
      ((continuous_regNatGrowth hΨ).measurable.comp hsol.measurable_grad)
  have hfz'int : IntegrableOn (fun y => |regLogRhs κ mc Ψ v G y * z' y|)
      (Metric.closedBall x (2 * r)) volume := by
    refine Integrable.mono' (hfint.const_mul (2 * Cu * (2 * r) ^ αh))
      (hfmeas.mul hz'meas).abs.aestronglyMeasurable.restrict ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_abs, abs_mul]
    calc |regLogRhs κ mc Ψ v G y| * |z' y|
        ≤ |regLogRhs κ mc Ψ v G y| * (2 * Cu * (2 * r) ^ αh) :=
          mul_le_mul_of_nonneg_left (hz'M y) (abs_nonneg _)
      _ = 2 * Cu * (2 * r) ^ αh * |regLogRhs κ mc Ψ v G y| := by ring
  have hz'0 : ∀ᵐ y, y ∉ Metric.closedBall x (2 * r) →
      |regLogRhs κ mc Ψ v G y * z' y| = 0 := by
    filter_upwards [hz'W.ae_eq_zero] with y hy hyB
    rw [hy hyB, mul_zero, abs_zero]
  have hsplit : (∫ y, |regLogRhs κ mc Ψ v G y * z' y|) ≤
      2 * Cu * (2 * r) ^ αh * ∫ y in Metric.closedBall x (2 * r), |regLogRhs κ mc Ψ v G y| := by
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hz'0, ← integral_const_mul]
    refine setIntegral_mono_on hfz'int (hfint.const_mul _) measurableSet_closedBall
      fun y _ => ?_
    rw [abs_mul]
    calc |regLogRhs κ mc Ψ v G y| * |z' y|
        ≤ |regLogRhs κ mc Ψ v G y| * (2 * Cu * (2 * r) ^ αh) :=
          mul_le_mul_of_nonneg_left (hz'M y) (abs_nonneg _)
      _ = 2 * Cu * (2 * r) ^ αh * |regLogRhs κ mc Ψ v G y| := by ring
  -- assemble
  have hrpow : (2 * r) ^ αh * (2 * r) ^ ((d : ℝ) - 2 + 2 * αm) =
      (2 : ℝ) ^ ((d : ℝ) - 2 + 2 * αm + αh) * r ^ ((d : ℝ) - 2 + 2 * αm + αh) := by
    rw [← Real.rpow_add h2rpos, ← Real.mul_rpow (by norm_num) hr.le]
    congr 1
    ring
  have hfinal : (∫ y, ‖weakGrad z' y‖ ^ 2) ≤
      2 * Cu * M2 / c * (2 : ℝ) ^ ((d : ℝ) - 2 + 2 * αm + αh) * r ^ ((d : ℝ) - 2 + 2 * αm + αh) := by
    have hstep : c * (∫ y, ‖weakGrad z' y‖ ^ 2) ≤
        2 * Cu * (2 * r) ^ αh * (M2 * (2 * r) ^ ((d : ℝ) - 2 + 2 * αm)) :=
      hcomp.trans (hsplit.trans (mul_le_mul_of_nonneg_left hfB hosc0))
    have hid : 2 * Cu * (2 * r) ^ αh * (M2 * (2 * r) ^ ((d : ℝ) - 2 + 2 * αm)) =
        2 * Cu * M2 * ((2 : ℝ) ^ ((d : ℝ) - 2 + 2 * αm + αh) * r ^ ((d : ℝ) - 2 + 2 * αm + αh)) := by
      rw [← hrpow]; ring
    rw [hid] at hstep
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc0]
    nlinarith [hstep]
  -- transfer to `G - H` on the small ball
  have hsubr : Metric.closedBall x r ⊆ Metric.closedBall x (2 * r) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hGHae : ∀ᵐ y ∂(volume.restrict (Metric.closedBall x r)),
      ‖G y - H y‖ ^ 2 = ‖weakGrad z' y‖ ^ 2 := by
    filter_upwards [ae_restrict_of_ae hZz', self_mem_ae_restrict measurableSet_closedBall]
      with y hy hyB
    rw [hGH y (hsubr hyB), hy]
  have hzsq : Integrable (fun y => ‖weakGrad z' y‖ ^ 2) :=
    Komlos.Literature.FrozenDirichlet.integrable_norm_sq hz'W.memLp_weakGrad
  refine ⟨fun y => v y - z y, H, hfield, ?_, ?_, ?_⟩
  · -- the potential `v - z` is locally square integrable on the ball (`reg/c2h`, DEVIATION 2)
    refine isLocSqIntegrableOn_sub_memLp
      (isLocSqIntegrableOn_of_continuousOn
        (hsol.continuousOn.mono (Metric.ball_subset_closedBall.trans hb2U)))
      hsol.measurable.aestronglyMeasurable ?_
    have h2e : ENNReal.ofReal (2 : ℝ) = 2 := by simp
    have hml : MemLp z (ENNReal.ofReal (2 : ℝ)) volume := hz.memLp
    rwa [h2e] at hml
  · exact (hzsq.integrableOn).congr (hGHae.mono fun y hy => hy.symm)
  · calc (∫ y in Metric.closedBall x r, ‖G y - H y‖ ^ 2)
        = ∫ y in Metric.closedBall x r, ‖weakGrad z' y‖ ^ 2 := integral_congr_ae hGHae
      _ ≤ ∫ y, ‖weakGrad z' y‖ ^ 2 := by
          refine setIntegral_le_integral hzsq ?_
          filter_upwards with y using sq_nonneg _
      _ ≤ _ := hfinal





/-- The elementary splitting `‖A‖² ≤ 2‖A - B‖² + 2‖B‖²`, integrated. -/
theorem integral_norm_sq_le_split {A B : Euc d → Euc d} {T : Set (Euc d)} (hT : MeasurableSet T)
    (hA : IntegrableOn (fun y => ‖A y‖ ^ 2) T volume)
    (hD : IntegrableOn (fun y => ‖A y - B y‖ ^ 2) T volume)
    (hB : IntegrableOn (fun y => ‖B y‖ ^ 2) T volume) :
    (∫ y in T, ‖A y‖ ^ 2) ≤ 2 * (∫ y in T, ‖A y - B y‖ ^ 2) + 2 * ∫ y in T, ‖B y‖ ^ 2 := by
  have hi1 : IntegrableOn (fun y => 2 * ‖A y - B y‖ ^ 2) T volume := hD.const_mul 2
  have hi2 : IntegrableOn (fun y => 2 * ‖B y‖ ^ 2) T volume := hB.const_mul 2
  have hisum : IntegrableOn (fun y => 2 * ‖A y - B y‖ ^ 2 + 2 * ‖B y‖ ^ 2) T volume := hi1.add hi2
  have hpt : ∀ y ∈ T, ‖A y‖ ^ 2 ≤ 2 * ‖A y - B y‖ ^ 2 + 2 * ‖B y‖ ^ 2 := by
    intro y _
    have htri : ‖A y‖ ≤ ‖A y - B y‖ + ‖B y‖ := by
      calc ‖A y‖ = ‖(A y - B y) + B y‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    nlinarith [norm_nonneg (A y), norm_nonneg (A y - B y), norm_nonneg (B y),
      sq_nonneg (‖A y - B y‖ - ‖B y‖)]
  have h1 := setIntegral_mono_on hA hisum hT hpt
  rwa [integral_add hi1 hi2, integral_const_mul, integral_const_mul] at h1

/-! ### The perturbed decay of the energy -/

set_option maxHeartbeats 1000000 in
/-- **The perturbed decay of `Φ(t) = ∫_{B_t} ‖G‖²`**, with the *trivial* good exponent `d` coming
from the energy decay of the `Ψ`-harmonic replacement and the data exponent
`β = d - 2 + 2αm + αh` coming from the comparison bound. -/
theorem IsWeakLogSol.exists_energy_perturbed_decay (hd : 0 < d) (hΨ : IsRegProfile Ψ) {c C : ℝ}
    (hP : IsRegProfileWith Ψ c C) (hsol : IsWeakLogSol κ mc Ψ U v G)
    {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U)
    {Cu Cm αh αm Rm : ℝ} (hCu : 0 ≤ Cu) (hCm : 0 ≤ Cm) (hαh : 0 < αh) (hαm : 0 < αm)
    (hαm1 : αm < 1) (hRm : 0 < Rm) (hRm12 : Rm ≤ 1 / 2)
    (hSball : ∀ x ∈ S, Metric.closedBall x Rm ⊆ U)
    (hhol : ∀ x ∈ S, ∀ y ∈ Metric.closedBall x Rm, ∀ y' ∈ Metric.closedBall x Rm,
      |v y - v y'| ≤ Cu * dist y y' ^ αh)
    (hmor : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ Rm →
      (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ Cm * t ^ ((d : ℝ) - 2 + 2 * αm)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ x ∈ S, ∀ ρ s : ℝ, 0 < ρ → ρ ≤ s → s ≤ Rm / 2 →
        (∫ y in Metric.closedBall x ρ, ‖G y‖ ^ 2) ≤
          a * (ρ / s) ^ ((d : ℝ)) * (∫ y in Metric.closedBall x s, ‖G y‖ ^ 2) +
            b * s ^ ((d : ℝ) - 2 + 2 * αm + αh) := by
  classical
  set β : ℝ := (d : ℝ) - 2 + 2 * αm + αh with hβdef
  obtain ⟨Cb, hCb, hrep⟩ := hsol.exists_replacement_bound hd hΨ hP hS hSU hCu hCm hαh hαm hαm1
    hRm hRm12 hSball hhol hmor
  obtain ⟨Cs, hCs, hdec⟩ := exists_regHarmonic_energy_decay (Ψ := Ψ) hΨ
  have h2d0 : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h2β0 : (0 : ℝ) < (2 : ℝ) ^ (-β) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨4 * Cs * (2 : ℝ) ^ ((d : ℝ)) + (2 : ℝ) ^ ((d : ℝ)),
    (2 + 4 * Cs) * Cb * (2 : ℝ) ^ (-β), by positivity, by positivity, ?_⟩
  intro x hx ρ s hρ hρs hsR
  set a : ℝ := 4 * Cs * (2 : ℝ) ^ ((d : ℝ)) + (2 : ℝ) ^ ((d : ℝ)) with ha
  set b : ℝ := (2 + 4 * Cs) * Cb * (2 : ℝ) ^ (-β) with hb
  have hs0 : 0 < s := lt_of_lt_of_le hρ hρs
  have hsRm : s ≤ Rm := by linarith
  have hGint : ∀ u : ℝ, u ≤ Rm → IntegrableOn (fun y => ‖G y‖ ^ 2)
      (Metric.closedBall x u) volume := fun u hu =>
    hsol.integrableOn_sq x u ((Metric.closedBall_subset_closedBall hu).trans (hSball x hx))
  set Φ : ℝ → ℝ := fun u => ∫ y in Metric.closedBall x u, ‖G y‖ ^ 2 with hΦdef
  have hΦ0 : ∀ u : ℝ, 0 ≤ Φ u := fun u => integral_nonneg fun _ => sq_nonneg _
  set q : ℝ := (ρ / s) ^ ((d : ℝ)) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  by_cases hcase : ρ ≤ s / 2
  · -- the genuine comparison step
    obtain ⟨hfun, H, hfield, hfL2, hGHint, hGHbd⟩ :=
      hrep x hx (s / 2) (by linarith) (by linarith)
    have hball : (2 : ℝ) * (s / 2) = s := by ring
    rw [hball] at hfield hfL2
    obtain ⟨W, hWc, hWae, hWdec⟩ := hdec x s hs0 hfun H hfield hfL2
    have hsub2 : Metric.closedBall x (s / 2) ⊆ Metric.ball x s :=
      Metric.closedBall_subset_ball (by linarith)
    have hsubρ : Metric.closedBall x ρ ⊆ Metric.closedBall x (s / 2) :=
      Metric.closedBall_subset_closedBall hcase
    set E : ℝ := ∫ y in Metric.closedBall x (s / 2), ‖G y - H y‖ ^ 2 with hEdef
    have hE0 : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
    have hWH : ∀ u : ℝ, Metric.closedBall x u ⊆ Metric.ball x s →
        (∫ y in Metric.closedBall x u, ‖H y‖ ^ 2) =
          ∫ y in Metric.closedBall x u, ‖W y‖ ^ 2 := by
      intro u hu
      refine integral_congr_ae ?_
      filter_upwards [ae_mono (Measure.restrict_mono hu le_rfl) hWae] with y hy
      rw [hy]
    have hsplitG : ∀ u : ℝ, Metric.closedBall x u ⊆ Metric.closedBall x (s / 2) →
        Φ u ≤ 2 * E + 2 * ∫ y in Metric.closedBall x u, ‖H y‖ ^ 2 := by
      intro u hu
      have hGu : IntegrableOn (fun y => ‖G y‖ ^ 2) (Metric.closedBall x u) volume :=
        (hGint (s / 2) (by linarith)).mono_set hu
      have hGHu : IntegrableOn (fun y => ‖G y - H y‖ ^ 2) (Metric.closedBall x u) volume :=
        hGHint.mono_set hu
      have hHu : IntegrableOn (fun y => ‖H y‖ ^ 2) (Metric.closedBall x u) volume :=
        hfield.integrableOn_sq x u (hu.trans hsub2)
      have h1 := integral_norm_sq_le_split (A := G) (B := H) measurableSet_closedBall hGu hGHu hHu
      have h2 : (∫ y in Metric.closedBall x u, ‖G y - H y‖ ^ 2) ≤ E :=
        setIntegral_mono_set hGHint (Eventually.of_forall fun _ => sq_nonneg _) hu.eventuallyLE
      have h3 : Φ u = ∫ y in Metric.closedBall x u, ‖G y‖ ^ 2 := rfl
      rw [h3]
      linarith
    have hsplitH : (∫ y in Metric.closedBall x (s / 2), ‖H y‖ ^ 2) ≤ 2 * E + 2 * Φ s := by
      have hGu : IntegrableOn (fun y => ‖G y‖ ^ 2) (Metric.closedBall x (s / 2)) volume :=
        hGint (s / 2) (by linarith)
      have hHu : IntegrableOn (fun y => ‖H y‖ ^ 2) (Metric.closedBall x (s / 2)) volume :=
        hfield.integrableOn_sq x (s / 2) hsub2
      have hHGu : IntegrableOn (fun y => ‖H y - G y‖ ^ 2) (Metric.closedBall x (s / 2)) volume := by
        refine hGHint.congr_fun (fun y _ => ?_) measurableSet_closedBall
        show ‖G y - H y‖ ^ 2 = ‖H y - G y‖ ^ 2
        rw [← norm_neg (G y - H y)]
        congr 2
        abel
      have h1 := integral_norm_sq_le_split (A := H) (B := G) measurableSet_closedBall hHu hHGu hGu
      have h2 : (∫ y in Metric.closedBall x (s / 2), ‖H y - G y‖ ^ 2) = E := by
        refine setIntegral_congr_fun measurableSet_closedBall fun y _ => ?_
        rw [← norm_neg (H y - G y)]
        congr 2
        abel
      have h3 : Φ (s / 2) ≤ Φ s :=
        setIntegral_mono_set (hGint s hsRm) (Eventually.of_forall fun _ => sq_nonneg _)
          (Metric.closedBall_subset_closedBall (by linarith)).eventuallyLE
      have h4 : Φ (s / 2) = ∫ y in Metric.closedBall x (s / 2), ‖G y‖ ^ 2 := rfl
      rw [h2] at h1
      rw [h4] at h3
      linarith
    -- the decay of the harmonic part
    have hWd := hWdec ρ hρ hcase
    have hfrac : (2 : ℝ) * ρ / s = 2 * (ρ / s) := by ring
    have hQdef : ((2 : ℝ) * ρ / s) ^ ((d : ℝ)) = (2 : ℝ) ^ ((d : ℝ)) * q := by
      rw [hfrac, hq]
      exact Real.mul_rpow (by norm_num) (by positivity)
    rw [hQdef] at hWd
    rw [← hWH ρ (hsubρ.trans hsub2), ← hWH (s / 2) hsub2] at hWd
    have hQ1 : (2 : ℝ) ^ ((d : ℝ)) * q ≤ 1 := by
      rw [← hQdef]
      refine Real.rpow_le_one (by positivity) ?_ (by positivity)
      rw [div_le_one hs0]
      linarith
    have hQ0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ)) * q := by positivity
    have hEb : E ≤ Cb * ((2 : ℝ) ^ (-β) * s ^ β) := by
      refine hGHbd.trans (le_of_eq ?_)
      congr 1
      rw [Real.div_rpow hs0.le (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      ring
    -- the algebra
    have c1 : Φ ρ ≤ 2 * E + 2 * (Cs * ((2 : ℝ) ^ ((d : ℝ)) * q) *
        ∫ y in Metric.closedBall x (s / 2), ‖H y‖ ^ 2) := by
      have := hsplitG ρ hsubρ
      linarith [hWd]
    have c2 : Cs * ((2 : ℝ) ^ ((d : ℝ)) * q) *
        (∫ y in Metric.closedBall x (s / 2), ‖H y‖ ^ 2) ≤
        Cs * ((2 : ℝ) ^ ((d : ℝ)) * q) * (2 * E + 2 * Φ s) :=
      mul_le_mul_of_nonneg_left hsplitH (by positivity)
    have c3 : Cs * ((2 : ℝ) ^ ((d : ℝ)) * q) * E ≤ Cs * E := by
      nlinarith [mul_nonneg hCs hE0, hQ1, hQ0]
    have c5 : 4 * (Cs * ((2 : ℝ) ^ ((d : ℝ)) * q) * Φ s) ≤ a * q * Φ s := by
      rw [ha]
      nlinarith [mul_nonneg (mul_nonneg h2d0.le hq0) (hΦ0 s)]
    have c6 : (2 + 4 * Cs) * E ≤ b * s ^ β := by
      rw [hb]
      nlinarith [mul_le_mul_of_nonneg_left hEb (show (0:ℝ) ≤ 2 + 4 * Cs by linarith)]
    linarith [c1, c2, c3, c5, c6]
  · -- the trivial range `s/2 < ρ ≤ s`
    push Not at hcase
    have hbs : 0 ≤ b * s ^ β := by positivity
    have hqlb : (1 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ)) * q := by
      have h1 : (2 : ℝ)⁻¹ ≤ ρ / s := by
        rw [le_div_iff₀ hs0]
        linarith
      have h2 : ((2 : ℝ)⁻¹) ^ ((d : ℝ)) ≤ q :=
        Real.rpow_le_rpow (by norm_num) h1 (by positivity)
      have h3 : ((2 : ℝ)⁻¹) ^ ((d : ℝ)) = ((2 : ℝ) ^ ((d : ℝ)))⁻¹ :=
        Real.inv_rpow (by norm_num) _
      rw [h3] at h2
      have h4 := mul_le_mul_of_nonneg_left h2 h2d0.le
      rwa [mul_inv_cancel₀ h2d0.ne'] at h4
    have hmono : Φ ρ ≤ Φ s :=
      setIntegral_mono_set (hGint s hsRm) (Eventually.of_forall fun _ => sq_nonneg _)
        (Metric.closedBall_subset_closedBall hρs).eventuallyLE
    have hstep : Φ s ≤ a * q * Φ s := by
      have hge : (1 : ℝ) ≤ a * q := by
        rw [ha]
        nlinarith [hqlb, hCs, hq0, h2d0, mul_nonneg (mul_nonneg hCs h2d0.le) hq0]
      nlinarith [hΦ0 s, hge]
    linarith


/-! ### One bootstrap step for the Morrey exponent -/

/-- **One step of the Morrey bootstrap**: a Morrey bound with exponent `αm` yields one with
exponent `αm + αh/2` (on half the radius), by the Campanato iteration applied to the perturbed
decay of `IsWeakLogSol.exists_energy_perturbed_decay`. -/
theorem IsWeakLogSol.morrey_step (hd : 0 < d) (hΨ : IsRegProfile Ψ) {c C : ℝ}
    (hP : IsRegProfileWith Ψ c C) (hsol : IsWeakLogSol κ mc Ψ U v G)
    {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U)
    {Cu Cm αh αm Rm : ℝ} (hCu : 0 ≤ Cu) (hCm : 0 ≤ Cm) (hαh : 0 < αh) (hαm : 0 < αm)
    (hαm1 : αm < 1) (hRm : 0 < Rm) (hRm12 : Rm ≤ 1 / 2)
    (hβ0 : 0 ≤ (d : ℝ) - 2 + 2 * αm + αh) (hβd : (d : ℝ) - 2 + 2 * αm + αh < (d : ℝ))
    (hSball : ∀ x ∈ S, Metric.closedBall x Rm ⊆ U)
    (hhol : ∀ x ∈ S, ∀ y ∈ Metric.closedBall x Rm, ∀ y' ∈ Metric.closedBall x Rm,
      |v y - v y'| ≤ Cu * dist y y' ^ αh)
    (hmor : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ Rm →
      (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ Cm * t ^ ((d : ℝ) - 2 + 2 * αm)) :
    ∃ Cm' : ℝ, 0 ≤ Cm' ∧
      ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ Rm / 2 →
        (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤
          Cm' * t ^ ((d : ℝ) - 2 + 2 * (αm + αh / 2)) := by
  classical
  set β : ℝ := (d : ℝ) - 2 + 2 * αm + αh with hβdef
  have hexp : (d : ℝ) - 2 + 2 * (αm + αh / 2) = β := by rw [hβdef]; ring
  obtain ⟨a, b, ha0, hb0, hdecay⟩ := hsol.exists_energy_perturbed_decay hd hΨ hP hS hSU hCu hCm
    hαh hαm hαm1 hRm hRm12 hSball hhol hmor
  obtain ⟨cit, hcit0, hcit⟩ :=
    Komlos.Literature.campanato_iteration_constants (a := a) (β := β) (γ := (d : ℝ))
      ha0 hβ0 hβd
  set R₀ : ℝ := Rm / 2 with hR₀def
  have hR₀pos : 0 < R₀ := by rw [hR₀def]; linarith
  have hR₀β : (0 : ℝ) < R₀ ^ β := Real.rpow_pos_of_pos hR₀pos _
  refine ⟨cit * (Cm * R₀ ^ ((d : ℝ) - 2 + 2 * αm) + b * R₀ ^ β) / R₀ ^ β, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Cm * R₀ ^ ((d : ℝ) - 2 + 2 * αm) :=
      mul_nonneg hCm (Real.rpow_nonneg hR₀pos.le _)
    have h2 : (0 : ℝ) ≤ b * R₀ ^ β := mul_nonneg hb0 hR₀β.le
    have h3 : (0 : ℝ) ≤ cit * (Cm * R₀ ^ ((d : ℝ) - 2 + 2 * αm) + b * R₀ ^ β) :=
      mul_nonneg hcit0 (by linarith)
    exact div_nonneg h3 hR₀β.le
  intro x hx t ht htR
  set Φ : ℝ → ℝ := fun u => ∫ y in Metric.closedBall x u, ‖G y‖ ^ 2 with hΦdef
  have hΦ0 : ∀ u : ℝ, 0 ≤ Φ u := fun u => integral_nonneg fun _ => sq_nonneg _
  have hGint : ∀ u : ℝ, u ≤ Rm → IntegrableOn (fun y => ‖G y‖ ^ 2)
      (Metric.closedBall x u) volume := fun u hu =>
    hsol.integrableOn_sq x u ((Metric.closedBall_subset_closedBall hu).trans (hSball x hx))
  have hΦmono : ∀ ρ u : ℝ, 0 < ρ → ρ ≤ u → u ≤ R₀ → Φ ρ ≤ Φ u := by
    intro ρ u hρ hρu huR
    exact setIntegral_mono_set (hGint u (by rw [hR₀def] at huR; linarith))
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Metric.closedBall_subset_closedBall hρu).eventuallyLE
  have hkey := hcit b R₀ hb0 hR₀pos Φ hΦ0 hΦmono (hdecay x hx) t ht htR
  have hΦR : Φ R₀ ≤ Cm * R₀ ^ ((d : ℝ) - 2 + 2 * αm) :=
    hmor x hx R₀ hR₀pos (by rw [hR₀def]; linarith)
  have hqeq : (t / R₀) ^ β = t ^ β / R₀ ^ β := Real.div_rpow ht.le hR₀pos.le _
  rw [hexp]
  calc Φ t ≤ cit * (Φ R₀ + b * R₀ ^ β) * (t / R₀) ^ β := hkey
    _ ≤ cit * (Cm * R₀ ^ ((d : ℝ) - 2 + 2 * αm) + b * R₀ ^ β) * (t / R₀) ^ β := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hcit0) ?_
        exact Real.rpow_nonneg (by positivity) _
    _ = cit * (Cm * R₀ ^ ((d : ℝ) - 2 + 2 * αm) + b * R₀ ^ β) / R₀ ^ β * t ^ β := by
        rw [hqeq]; field_simp


/-! ### Iterating the bootstrap -/

/-- **The Morrey bootstrap, iterated `n` times.**  Each step adds `αh/2` to the Morrey exponent
and halves the radius; the iteration stops once the exponent has passed `1 - αh/2`, which is
exactly the threshold beyond which `IsWeakLogSol.morrey_step` no longer applies (its data exponent
would exceed the good exponent `d`). -/
theorem IsWeakLogSol.morrey_iterate (hd : 0 < d) (hΨ : IsRegProfile Ψ) {c C : ℝ}
    (hP : IsRegProfileWith Ψ c C) (hsol : IsWeakLogSol κ mc Ψ U v G)
    {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U)
    {Cu αh R : ℝ} (hCu : 0 ≤ Cu) (hαh : 0 < αh) (hR : 0 < R) (hR12 : R ≤ 1 / 2)
    (hSball : ∀ x ∈ S, Metric.closedBall x R ⊆ U)
    (hhol : ∀ x ∈ S, ∀ y ∈ Metric.closedBall x R, ∀ y' ∈ Metric.closedBall x R,
      |v y - v y'| ≤ Cu * dist y y' ^ αh)
    {Cm₀ αm₀ : ℝ} (hCm₀ : 0 ≤ Cm₀) (hαm₀ : 0 < αm₀) (hαm₀1 : αm₀ < 1)
    (hβ₀ : 0 ≤ (d : ℝ) - 2 + 2 * αm₀ + αh)
    (hmor₀ : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ R →
      (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ Cm₀ * t ^ ((d : ℝ) - 2 + 2 * αm₀)) (n : ℕ) :
    ∃ Cm αm Rm : ℝ, 0 ≤ Cm ∧ 0 < αm ∧ αm < 1 ∧ 0 < Rm ∧ Rm ≤ R ∧
      0 ≤ (d : ℝ) - 2 + 2 * αm + αh ∧ min (αm₀ + n * (αh / 2)) (1 - αh / 2) ≤ αm ∧
      (∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ Rm →
        (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ Cm * t ^ ((d : ℝ) - 2 + 2 * αm)) := by
  induction n with
  | zero =>
    refine ⟨Cm₀, αm₀, R, hCm₀, hαm₀, hαm₀1, hR, le_rfl, hβ₀, ?_, hmor₀⟩
    simpa using min_le_left αm₀ (1 - αh / 2)
  | succ n ih =>
    obtain ⟨Cm, αm, Rm, hCm, hαm, hαm1, hRm, hRmR, hβ, hmin, hmor⟩ := ih
    by_cases hstop : 1 - αh / 2 ≤ αm
    · exact ⟨Cm, αm, Rm, hCm, hαm, hαm1, hRm, hRmR, hβ,
        le_trans (min_le_right _ _) hstop, hmor⟩
    · push Not at hstop
      have hβd : (d : ℝ) - 2 + 2 * αm + αh < (d : ℝ) := by linarith
      have hSballm : ∀ x ∈ S, Metric.closedBall x Rm ⊆ U := fun x hx =>
        (Metric.closedBall_subset_closedBall hRmR).trans (hSball x hx)
      have hholm : ∀ x ∈ S, ∀ y ∈ Metric.closedBall x Rm, ∀ y' ∈ Metric.closedBall x Rm,
          |v y - v y'| ≤ Cu * dist y y' ^ αh := fun x hx y hy y' hy' =>
        hhol x hx y (Metric.closedBall_subset_closedBall hRmR hy) y'
          (Metric.closedBall_subset_closedBall hRmR hy')
      obtain ⟨Cm', hCm', hmor'⟩ := hsol.morrey_step hd hΨ hP hS hSU hCu hCm hαh hαm hαm1
        hRm (le_trans hRmR hR12) hβ hβd hSballm hholm hmor
      refine ⟨Cm', αm + αh / 2, Rm / 2, hCm', by linarith, by linarith, by linarith,
        by linarith, by linarith, ?_, hmor'⟩
      have hcase : αm₀ + n * (αh / 2) ≤ αm := by
        rcases min_cases (αm₀ + n * (αh / 2)) (1 - αh / 2) with ⟨he, -⟩ | ⟨he, -⟩
        · rw [he] at hmin; exact hmin
        · rw [he] at hmin; linarith
      refine le_trans (min_le_left _ _) ?_
      push_cast
      linarith

/-! ### The analytic core: comparison with the `Ψ`-harmonic replacement -/

/-- The Morrey exponent improves by the factor `3/2` at every comparison step, so any threshold
is passed after finitely many steps.  This is the arithmetic of the bootstrap described in
`IsWeakLogSol.exists_harmonic_comparison`. -/
theorem exists_pow_three_halves_ge {α₀ T : ℝ} (hα₀ : 0 < α₀) :
    ∃ n : ℕ, T ≤ (3 / 2 : ℝ) ^ n * α₀ := by
  obtain ⟨n, hn⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3 / 2)).eventually_ge_atTop
      (T / α₀)).exists
  refine ⟨n, ?_⟩
  rw [div_le_iff₀ hα₀] at hn
  linarith

/-- **The comparison with the `Ψ`-harmonic replacement** — the analytic core of link 6
(`REGULARIZED_ROUTE.md`, Revision 2 (v); Giaquinta, *Multiple Integrals in the Calculus of
Variations*, Ch. VI).

For every compact `S ⊆ U` and every *target* exponent `γ > d` there are `β ∈ (d, γ)` and `b ≥ 0`
such that, on every ball `B_r(x) ⋐ U` with `x ∈ S` and `r ≤ R₁`, the solution `v` admits a
`Ψ`-harmonic replacement field `H` on `B_{2r}(x)` with

`∫_{B_r(x)} ‖∇v - H‖² ≤ b r^β`.

Proof.  Write `B = B̄_{2r}(x)`, `GB = 1_B G`, and let `z ∈ W₀^{1,2}(B)` minimise the `Ψ`-Dirichlet
energy `∫ (Ψ(GB - ∇·) - Ψ 0)`; then `H = GB - ∇z` is the replacement field and `G - H = ∇z` on
`B` (`IsWeakLogSol.exists_psi_harmonic_replacement`).  The four ingredients are:

* the **direct method** and the **Euler–Lagrange equation** for the `Ψ`-Dirichlet energy
  (`exists_regDirEnergy_min`, `euler_lagrange_regDirEnergy_min`);
* the **maximum principle** `‖z‖_∞ ≤ osc_B v` (`regDirEnergy_min_abs_le`), which is what makes
  `z` an admissible test function for the natural-growth right-hand side;
* the **comparison estimate** `c ∫ ‖∇z‖² ≤ ∫ |f z|` (`IsWeakLogSol.replacement_comparison_le`,
  from `comparison_energy_le` and link 3), together with
  `∫_{B} |f| ≤ M₂ (2r)^{d-2+2αm}` (`IsWeakLogSol.integral_abs_rhs_le`, from the Morrey bound) and
  `osc_B v ≤ 2 Cu (2r)^{αh}` (from link 4); this is `IsWeakLogSol.exists_replacement_bound`, with
  exponent `d - 2 + 2αm + αh`;
* the **Morrey bootstrap**: `d - 2 + 2αm + αh > d` requires `2αm + αh > 2`, which link 5 does not
  provide.  Iterating the *same* comparison on `Φ(t) = ∫_{B_t}‖G‖²`, whose good exponent is the
  trivial one `d` (`IsWeakLogSol.exists_energy_perturbed_decay`, using the energy decay
  `exists_regHarmonic_energy_decay` of the harmonic part), improves the Morrey exponent by
  `αh/2` at each step (`IsWeakLogSol.morrey_step`, `morrey_iterate`) until it passes
  `1 - αh/4`, which gives `β ≥ d + αh/2 > d`; running the iteration with the *halved* Hölder
  exponent and capping `αh ≤ γ - d` keeps `β < d + αh ≤ γ`. -/
theorem IsWeakLogSol.exists_harmonic_comparison (hd : 0 < d) (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ mc Ψ U v G) {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U)
    {γ : ℝ} (hγ : (d : ℝ) < γ) :
    ∃ b β R₁ : ℝ, 0 ≤ b ∧ (d : ℝ) < β ∧ β < γ ∧ 0 < R₁ ∧
      (∀ x ∈ S, Metric.closedBall x (2 * R₁) ⊆ U) ∧
      ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₁ →
        ∃ (hfun : Euc d → ℝ) (H : Euc d → Euc d),
          IsRegHarmonicField Ψ (Metric.ball x (2 * r)) hfun H ∧
          IsLocSqIntegrableOn (Metric.ball x (2 * r)) hfun ∧
          IntegrableOn (fun y => ‖G y - H y‖ ^ 2) (Metric.closedBall x r) volume ∧
          (∫ y in Metric.closedBall x r, ‖G y - H y‖ ^ 2) ≤ b * r ^ β := by
  classical
  obtain ⟨c, C, hP⟩ := hΨ.exists_isRegProfileWith
  obtain ⟨Cu, α, R, hCu, hα, hα1, hR, hR12, hSball, hhol, hmor⟩ :=
    hsol.exists_uniform_holder_morrey hΨ hS hSU
  obtain ⟨Rz, M, hRz, hM0, hSballz, hMbd⟩ := hsol.exists_uniform_sq_bound hS hSU
  -- the working radius and the two Hölder exponents
  set R' : ℝ := min R Rz with hR'def
  have hR'pos : 0 < R' := lt_min hR hRz
  have hR'R : R' ≤ R := min_le_left _ _
  have hR'12 : R' ≤ 1 / 2 := le_trans hR'R hR12
  set αh : ℝ := min α (γ - (d : ℝ)) with hαhdef
  have hαh : 0 < αh := lt_min hα (by linarith)
  have hαhα : αh ≤ α := min_le_left _ _
  have hαhγ : αh ≤ γ - (d : ℝ) := min_le_right _ _
  have hαh1 : αh < 1 := lt_of_le_of_lt hαhα hα1
  set αh2 : ℝ := αh / 2 with hαh2def
  have hαh2 : 0 < αh2 := by rw [hαh2def]; linarith
  -- the Hölder bound holds with any smaller exponent
  have hhol' : ∀ θ : ℝ, 0 < θ → θ ≤ α → ∀ x ∈ S, ∀ y ∈ Metric.closedBall x R',
      ∀ y' ∈ Metric.closedBall x R', |v y - v y'| ≤ Cu * dist y y' ^ θ := by
    intro θ hθ hθα x hx y hy y' hy'
    have hyR : y ∈ Metric.closedBall x R := Metric.closedBall_subset_closedBall hR'R hy
    have hy'R : y' ∈ Metric.closedBall x R := Metric.closedBall_subset_closedBall hR'R hy'
    refine (hhol x hx y hyR y' hy'R).trans ?_
    have hdle : dist y y' ≤ 1 := by
      have h1 : dist y y' ≤ dist y x + dist x y' := dist_triangle _ _ _
      have h2 : dist y x ≤ R' := Metric.mem_closedBall.1 hy
      have h3 : dist x y' ≤ R' := by rw [dist_comm]; exact Metric.mem_closedBall.1 hy'
      linarith
    rcases eq_or_lt_of_le (dist_nonneg : (0:ℝ) ≤ dist y y') with h0 | h0
    · rw [← h0, Real.zero_rpow hα.ne', Real.zero_rpow hθ.ne']
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge h0 hdle hθα) hCu
  have hSball' : ∀ x ∈ S, Metric.closedBall x R' ⊆ U := fun x hx =>
    (Metric.closedBall_subset_closedBall hR'R).trans (hSball x hx)
  -- the initial Morrey exponent
  set αm₀ : ℝ := max α ((2 - (d : ℝ)) / 2) with hαm₀def
  have hαm₀ : 0 < αm₀ := lt_of_lt_of_le hα (le_max_left _ _)
  have hαm₀1 : αm₀ < 1 := by
    refine max_lt hα1 ?_
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hαm₀ge : (2 - (d : ℝ)) / 2 ≤ αm₀ := le_max_right _ _
  have hβ₀ : 0 ≤ (d : ℝ) - 2 + 2 * αm₀ + αh2 := by linarith
  have hmor₀ : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ R' →
      (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ (Cu + M) * t ^ ((d : ℝ) - 2 + 2 * αm₀) := by
    intro x hx t ht htR
    have ht1 : t ≤ 1 := by linarith
    rcases max_cases α ((2 - (d : ℝ)) / 2) with ⟨he, hle⟩ | ⟨he, hlt⟩
    · rw [hαm₀def, he]
      have h1 := hmor x hx t ht (htR.trans hR'R)
      have h2 : (0:ℝ) ≤ t ^ ((d : ℝ) - 2 + 2 * α) := Real.rpow_nonneg ht.le _
      nlinarith [h1, hM0, h2]
    · rw [hαm₀def, he]
      have hzero : (d : ℝ) - 2 + 2 * ((2 - (d : ℝ)) / 2) = 0 := by ring
      rw [hzero]
      have h1 : (∫ y in Metric.closedBall x t, ‖G y‖ ^ 2) ≤ M := by
        refine le_trans ?_ (hMbd x hx)
        exact setIntegral_mono_set (hsol.integrableOn_sq x Rz (hSballz x hx))
          (Eventually.of_forall fun _ => sq_nonneg _)
          (Metric.closedBall_subset_closedBall (htR.trans (min_le_right _ _))).eventuallyLE
      rw [Real.rpow_zero, mul_one]
      linarith [h1, hCu]
  -- run the bootstrap
  obtain ⟨n, hn⟩ := exists_nat_ge ((1 - αh2 / 2 - αm₀) / (αh2 / 2))
  obtain ⟨Cm, αm, Rm, hCm, hαm, hαm1, hRm, hRmR, hβm, hminα, hmorm⟩ :=
    hsol.morrey_iterate hd hΨ hP hS hSU hCu hαh2 hR'pos hR'12 hSball'
      (hhol' αh2 hαh2 (by rw [hαh2def]; linarith)) (by linarith : (0:ℝ) ≤ Cu + M) hαm₀ hαm₀1
      hβ₀ hmor₀ n
  have hαmlb : 1 - αh2 / 2 ≤ αm := by
    refine le_trans ?_ hminα
    refine le_min ?_ le_rfl
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  -- the final comparison bound
  have hRm12 : Rm ≤ 1 / 2 := le_trans hRmR hR'12
  have hSballm : ∀ x ∈ S, Metric.closedBall x Rm ⊆ U := fun x hx =>
    (Metric.closedBall_subset_closedBall hRmR).trans (hSball' x hx)
  have hholm : ∀ x ∈ S, ∀ y ∈ Metric.closedBall x Rm, ∀ y' ∈ Metric.closedBall x Rm,
      |v y - v y'| ≤ Cu * dist y y' ^ αh := fun x hx y hy y' hy' =>
    hhol' αh hαh hαhα x hx y (Metric.closedBall_subset_closedBall hRmR hy) y'
      (Metric.closedBall_subset_closedBall hRmR hy')
  obtain ⟨Cb, hCb, hrep⟩ := hsol.exists_replacement_bound hd hΨ hP hS hSU hCu hCm hαh hαm hαm1
    hRm hRm12 hSballm hholm hmorm
  refine ⟨Cb, (d : ℝ) - 2 + 2 * αm + αh, Rm / 3, hCb, ?_, ?_, by linarith, ?_, ?_⟩
  · -- `β > d`
    rw [hαh2def] at hαmlb
    linarith
  · -- `β < γ`
    linarith
  · intro x hx
    exact (Metric.closedBall_subset_closedBall (by linarith)).trans (hSballm x hx)
  · intro x hx r hr hrR
    exact hrep x hx r hr (by linarith)

/-! ### The perturbed decay: link 2 combined with the comparison -/

/-- **The perturbed Campanato decay of the excess of `∇v`.**  This is the hypothesis of the
Campanato iteration, and it is **proved** here from link 2
(`exists_regHarmonic_campanato`, with its good exponent `γ = d + 2β'`) and the comparison
`IsWeakLogSol.exists_harmonic_comparison`.

The computation is the classical "add and subtract the harmonic replacement":
with `E = ∫_{B_r} ‖∇v - ∇h‖²`, `Φ_v(ρ) = ∫_{B_ρ}‖∇v - (∇v)_ρ‖²` and
`Φ_h(ρ) = ∫_{B_ρ}‖∇h - (∇h)_ρ‖²`,

`Φ_v(ρ) ≤ 2E + 2 Φ_h(ρ) ≤ 2E + 2 Cdec (ρ/r)^γ Φ_h(r) ≤ 2E + 2 Cdec (ρ/r)^γ (2E + 2 Φ_v(r))`,

and `(ρ/r)^γ ≤ 1` turns this into
`Φ_v(ρ) ≤ 4 Cdec (ρ/r)^γ Φ_v(r) + (2 + 4 Cdec) b r^β`.

Note that this is where the **DEVIATION** in link 2 is used and where it is seen to be harmless:
only `γ > β` is needed, and the weakened exponent `γ = d + 2β'` of
`exists_regHarmonic_campanato` is fed back into the comparison as its target exponent. -/
theorem IsWeakLogSol.exists_perturbed_excess_decay (hd : 0 < d) (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ mc Ψ U v G) {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ a b β γ R₀ M : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ (d : ℝ) < β ∧ β < γ ∧ 0 < R₀ ∧ 0 ≤ M ∧
      (∀ x ∈ S, Metric.closedBall x R₀ ⊆ U) ∧
      (∀ x ∈ S, Komlos.Literature.sqExcess G x R₀ ≤ M) ∧
      (∀ x ∈ S, ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ →
        Komlos.Literature.sqExcess G x ρ ≤ Komlos.Literature.sqExcess G x r) ∧
      (∀ x ∈ S, ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ →
        Komlos.Literature.sqExcess G x ρ ≤
          a * (ρ / r) ^ γ * Komlos.Literature.sqExcess G x r + b * r ^ β) := by
  obtain ⟨Cdec, β', hCdec, hβ'0, hβ'1, hlink2⟩ := exists_regHarmonic_campanato_field hΨ
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hγd : (d : ℝ) < (d : ℝ) + 2 * β' := by linarith
  obtain ⟨b₀, β, R₁, hb₀, hdβ, hβγ, hR₁, hball2, hcomp⟩ :=
    hsol.exists_harmonic_comparison hd hΨ hS hSU hγd
  obtain ⟨R₂, M₀, hR₂, hM₀, hball2', hMbd⟩ := hsol.exists_uniform_sq_bound hS hSU
  have hR₀ : (0 : ℝ) < min R₁ R₂ := lt_min hR₁ hR₂
  have hγ0 : (0 : ℝ) ≤ (d : ℝ) + 2 * β' := by linarith
  -- the balls of radius ≤ `min R₁ R₂` centred in `S` lie in `U`
  have hsubU : ∀ x ∈ S, ∀ r : ℝ, r ≤ min R₁ R₂ → Metric.closedBall x r ⊆ U := by
    intro x hx r hr
    exact (Metric.closedBall_subset_closedBall (hr.trans (min_le_right _ _))).trans (hball2' x hx)
  -- integrability of `G` and of its translates on those balls
  have hGi : ∀ x ∈ S, ∀ r : ℝ, r ≤ min R₁ R₂ →
      IntegrableOn G (Metric.closedBall x r) volume := fun x hx r hr =>
    hsol.integrableOn_closedBall (hsubU x hx r hr)
  have hGs : ∀ x ∈ S, ∀ r : ℝ, r ≤ min R₁ R₂ → ∀ e : Euc d,
      IntegrableOn (fun y => ‖G y - e‖ ^ 2) (Metric.closedBall x r) volume := fun x hx r hr e =>
    (hsol.integrableOn_norm_sub (hsubU x hx r hr) e).2
  refine ⟨4 * Cdec, (2 + 4 * Cdec) * b₀, β, (d : ℝ) + 2 * β', min R₁ R₂, M₀, by linarith,
    by positivity, hdβ, hβγ, hR₀, hM₀, fun x hx => hsubU x hx _ le_rfl, ?_, ?_, ?_⟩
  · -- the uniform bound at the scale `R₀`
    intro x hx
    have h1 := sqExcess_le_const' hR₀ (hGi x hx _ le_rfl) (hGs x hx _ le_rfl) 0
    simp only [sub_zero] at h1
    refine h1.trans ((setIntegral_mono_set (hsol.integrableOn_sq x R₂ (hball2' x hx))
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Metric.closedBall_subset_closedBall (min_le_right _ _)).eventuallyLE).trans (hMbd x hx))
  · -- monotonicity of the excess
    intro x hx ρ r hρ hρr hrR
    exact sqExcess_mono' hρ hρr (hGi x hx r hrR) (hGs x hx r hrR)
  · -- the perturbed decay
    intro x hx ρ r hρ hρr hrR
    have hrpos : 0 < r := lt_of_lt_of_le hρ hρr
    obtain ⟨h, H, hharm, hhL2, hEint0, hEbd0⟩ :=
      hcomp x hx r hrpos (hrR.trans (min_le_left _ _))
    obtain ⟨W, hWc, hWae, hdec⟩ := hlink2 x (2 * r) (by linarith) h H hharm hhL2
    have hsubball : Metric.closedBall x r ⊆ Metric.ball x (2 * r) :=
      Metric.closedBall_subset_ball (by linarith)
    have hghc : ContinuousOn W (Metric.closedBall x r) := hWc.mono hsubball
    have hsubρr : Metric.closedBall x ρ ⊆ Metric.closedBall x r :=
      Metric.closedBall_subset_closedBall hρr
    -- transfer the comparison bound from `H` to its continuous representative `W`
    have hWr : ∀ᵐ y ∂(volume.restrict (Metric.closedBall x r)), H y = W y :=
      ae_mono (Measure.restrict_mono hsubball le_rfl) hWae
    have hEq : (∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2) =
        ∫ y in Metric.closedBall x r, ‖G y - H y‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hWr] with y hy
      rw [hy]
    have hEint : IntegrableOn (fun y => ‖G y - W y‖ ^ 2) (Metric.closedBall x r) volume := by
      refine hEint0.congr ?_
      filter_upwards [hWr] with y hy
      rw [hy]
    have hEbd : (∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2) ≤ b₀ * r ^ β := hEq ▸ hEbd0
    -- link 2 at the scale `2 r`
    have hdecρ := hdec ρ hρ (by linarith)
    have hfrac : (2 : ℝ) * ρ / (2 * r) = ρ / r := by
      rw [mul_div_mul_left _ _ (two_ne_zero)]
    have h2r : (2 : ℝ) * r / 2 = r := by ring
    rw [hfrac, h2r] at hdecρ
    have hd2 : Komlos.Literature.sqExcess W x ρ ≤
        Cdec * (ρ / r) ^ ((d : ℝ) + 2 * β') * Komlos.Literature.sqExcess W x r := hdecρ
    -- the two elementary "add and subtract" steps
    have hcont2 : ∀ e : Euc d,
        IntegrableOn (fun y => ‖W y - e‖ ^ 2) (Metric.closedBall x r) volume := fun e =>
      (((hghc.sub continuousOn_const).norm.pow 2)).integrableOn_compact (isCompact_closedBall x r)
    have hstep1 : Komlos.Literature.sqExcess G x ρ ≤
        2 * (∫ y in Metric.closedBall x ρ, ‖G y - W y‖ ^ 2) +
          2 * Komlos.Literature.sqExcess W x ρ := by
      set cc : Euc d := ⨍ z in Metric.closedBall x ρ, W z with hcc
      have h1 := sqExcess_le_const' hρ ((hGi x hx r hrR).mono_set hsubρr)
        (fun e => (hGs x hx r hrR e).mono_set hsubρr) cc
      have hpt : ∀ y : Euc d, ‖G y - cc‖ ^ 2 ≤
          2 * ‖G y - W y‖ ^ 2 + 2 * ‖W y - cc‖ ^ 2 := by
        intro y
        have htri : ‖G y - cc‖ ≤ ‖G y - W y‖ + ‖W y - cc‖ := by
          calc ‖G y - cc‖ = ‖(G y - W y) + (W y - cc)‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        nlinarith [norm_nonneg (G y - cc), norm_nonneg (G y - W y),
          norm_nonneg (W y - cc), sq_nonneg (‖G y - W y‖ - ‖W y - cc‖)]
      have hi1 : IntegrableOn (fun y => 2 * ‖G y - W y‖ ^ 2)
          (Metric.closedBall x ρ) volume := (hEint.mono_set hsubρr).const_mul 2
      have hi2 : IntegrableOn (fun y => 2 * ‖W y - cc‖ ^ 2)
          (Metric.closedBall x ρ) volume := ((hcont2 cc).mono_set hsubρr).const_mul 2
      have h2 : (∫ y in Metric.closedBall x ρ, ‖G y - cc‖ ^ 2) ≤
          ∫ y in Metric.closedBall x ρ, (2 * ‖G y - W y‖ ^ 2 + 2 * ‖W y - cc‖ ^ 2) :=
        setIntegral_mono ((hGs x hx r hrR cc).mono_set hsubρr) (hi1.add hi2) (fun y => hpt y)
      rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul] at h2
      exact h1.trans h2
    have hstep2 : Komlos.Literature.sqExcess W x r ≤
        2 * (∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2) +
          2 * Komlos.Literature.sqExcess G x r := by
      set cc : Euc d := ⨍ z in Metric.closedBall x r, G z with hcc
      have h1 := Komlos.Literature.sqExcess_le_const hrpos hghc cc
      have hpt : ∀ y : Euc d, ‖W y - cc‖ ^ 2 ≤
          2 * ‖G y - W y‖ ^ 2 + 2 * ‖G y - cc‖ ^ 2 := by
        intro y
        have htri : ‖W y - cc‖ ≤ ‖G y - W y‖ + ‖G y - cc‖ := by
          calc ‖W y - cc‖ = ‖-(G y - W y) + (G y - cc)‖ := by congr 1; abel
            _ ≤ ‖-(G y - W y)‖ + ‖G y - cc‖ := norm_add_le _ _
            _ = ‖G y - W y‖ + ‖G y - cc‖ := by rw [norm_neg]
        nlinarith [norm_nonneg (W y - cc), norm_nonneg (G y - W y),
          norm_nonneg (G y - cc), sq_nonneg (‖G y - W y‖ - ‖G y - cc‖)]
      have hi1 : IntegrableOn (fun y => 2 * ‖G y - W y‖ ^ 2)
          (Metric.closedBall x r) volume := hEint.const_mul 2
      have hi2 : IntegrableOn (fun y => 2 * ‖G y - cc‖ ^ 2)
          (Metric.closedBall x r) volume := (hGs x hx r hrR cc).const_mul 2
      have h2 : (∫ y in Metric.closedBall x r, ‖W y - cc‖ ^ 2) ≤
          ∫ y in Metric.closedBall x r, (2 * ‖G y - W y‖ ^ 2 + 2 * ‖G y - cc‖ ^ 2) :=
        setIntegral_mono (hcont2 cc) (hi1.add hi2) (fun y => hpt y)
      rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul] at h2
      exact h1.trans h2
    -- the arithmetic
    have hq0 : (0 : ℝ) ≤ (ρ / r) ^ ((d : ℝ) + 2 * β') :=
      Real.rpow_nonneg (by positivity) _
    have hq1 : (ρ / r) ^ ((d : ℝ) + 2 * β') ≤ 1 :=
      Real.rpow_le_one (by positivity) ((div_le_one hrpos).2 hρr) hγ0
    have hE0 : (0 : ℝ) ≤ ∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hEρ : (∫ y in Metric.closedBall x ρ, ‖G y - W y‖ ^ 2) ≤
        ∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2 :=
      setIntegral_mono_set hEint (Eventually.of_forall fun _ => sq_nonneg _) hsubρr.eventuallyLE
    have hSG0 : (0 : ℝ) ≤ Komlos.Literature.sqExcess G x r :=
      Komlos.Literature.sqExcess_nonneg _ _ _
    have hB : Cdec * (ρ / r) ^ ((d : ℝ) + 2 * β') * Komlos.Literature.sqExcess W x r ≤
        2 * (Cdec * (ρ / r) ^ ((d : ℝ) + 2 * β') *
            ∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2) +
          2 * (Cdec * (ρ / r) ^ ((d : ℝ) + 2 * β') * Komlos.Literature.sqExcess G x r) := by
      have hh := mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCdec hq0)
      linarith [hh]
    have hPE : Cdec * (ρ / r) ^ ((d : ℝ) + 2 * β') *
        (∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2) ≤
        Cdec * ∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hq1 (mul_nonneg hCdec hE0)
      linarith [hh]
    have hfin : (2 + 4 * Cdec) * (∫ y in Metric.closedBall x r, ‖G y - W y‖ ^ 2) ≤
        (2 + 4 * Cdec) * (b₀ * r ^ β) :=
      mul_le_mul_of_nonneg_left hEbd (by linarith)
    linarith [hstep1, hd2, hB, hPE, hfin, hEρ]


/-! ### The Campanato iteration -/

/-- **The `L¹` Campanato bound for `G` on a compact subset of `U`.**  This is exactly the
hypothesis `hcamp` of Campanato's criterion `Komlos.Literature.exists_holder_of_campanato`.

Proof: `Komlos.Literature.campanato_iteration_constants` turns the perturbed decay of
`IsWeakLogSol.exists_perturbed_excess_decay` into `Φ(x, ρ) ≤ C₃ ρ^β` with `β = d + 2α`,
`α = (β - d)/2 > 0`; `setIntegral_norm_sub_le_of_sq'` converts that `L²` bound into the `L¹`
bound `∫_{B_ρ} ‖G - (G)_{B_ρ}‖ ≤ C ρ^{d+α}`. -/
theorem IsWeakLogSol.exists_campanato_L1 (hd : 0 < d) (hΨ : IsRegProfile Ψ)
    (hsol : IsWeakLogSol κ mc Ψ U v G) {S : Set (Euc d)} (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ α C R₀ : ℝ, 0 < α ∧ 0 < R₀ ∧ (∀ x ∈ S, Metric.closedBall x R₀ ⊆ U) ∧
      ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ a : Euc d, (∫ y in Metric.closedBall x r, ‖G y - a‖) ≤ C * r ^ ((d : ℝ) + α) := by
  obtain ⟨a, b, β, γ, R₀, M, ha, hb, hdβ, hβγ, hR₀, hM, hballU, hMbd, hmono, hdec⟩ :=
    hsol.exists_perturbed_excess_decay hd hΨ hS hSU
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hβ0 : (0 : ℝ) ≤ β := le_of_lt (lt_of_le_of_lt hd0 hdβ)
  obtain ⟨c, hc0, hiter⟩ := Komlos.Literature.campanato_iteration_constants ha hβ0 hβγ
  set α : ℝ := (β - (d : ℝ)) / 2 with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith
  have hR₀β : (0 : ℝ) < R₀ ^ β := Real.rpow_pos_of_pos hR₀ β
  set C₃ : ℝ := c * (M + b * R₀ ^ β) / R₀ ^ β with hC₃def
  have hC₃0 : 0 ≤ C₃ :=
    div_nonneg (mul_nonneg hc0 (add_nonneg hM (mul_nonneg hb hR₀β.le))) hR₀β.le
  refine ⟨α, (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2, R₀, hα, hR₀, hballU, ?_⟩
  intro x hx r hr hrR₀
  refine ⟨⨍ z in Metric.closedBall x r, G z, ?_⟩
  have hsub : Metric.closedBall x r ⊆ U :=
    (Metric.closedBall_subset_closedBall hrR₀).trans (hballU x hx)
  obtain ⟨hgi, hg2⟩ := hsol.integrableOn_norm_sub hsub (⨍ z in Metric.closedBall x r, G z)
  refine setIntegral_norm_sub_le_of_sq' hr hgi hg2 ?_
  have hit := hiter b R₀ hb hR₀ (fun s => Komlos.Literature.sqExcess G x s)
    (fun s => Komlos.Literature.sqExcess_nonneg G x s) (hmono x hx) (hdec x hx) r hr hrR₀
  have h1 : Komlos.Literature.sqExcess G x r ≤ c * (M + b * R₀ ^ β) * (r / R₀) ^ β := by
    refine hit.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _))
    exact mul_le_mul_of_nonneg_left (by linarith [hMbd x hx]) hc0
  have hexp : ((d : ℝ) + 2 * α) = β := by rw [hαdef]; ring
  have h2 : c * (M + b * R₀ ^ β) * (r / R₀) ^ β = C₃ * r ^ ((d : ℝ) + 2 * α) := by
    rw [hexp, Real.div_rpow hr.le hR₀.le, hC₃def]
    ring
  calc (∫ y in Metric.closedBall x r, ‖G y - ⨍ z in Metric.closedBall x r, G z‖ ^ 2)
      = Komlos.Literature.sqExcess G x r := rfl
    _ ≤ c * (M + b * R₀ ^ β) * (r / R₀) ^ β := h1
    _ = C₃ * r ^ ((d : ℝ) + 2 * α) := h2

end Komlos.Literature.Regularized
