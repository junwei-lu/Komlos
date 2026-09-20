import Komlos.Literature.Regularized.InteriorRep

/-!
# Interior regularity of the logarithmic solution (lane `L3`)

The analytic chain of lane `L3` (`reg/c2`) of `REGULARIZED_ROUTE.md`, Revision 2 (v): a weak
solution `v` of

`div ∇Ψ(∇v) = κ v + 2 m + B(∇v)`,   `B(q) = 2 (⟪∇Ψ q, q⟫ - Ψ q)`,   `|B(q)| ≤ C ‖q‖²`,

on an open set `U`, continuous there, is `C²` on `U`.  The profile `Ψ` is smooth and *globally*
uniformly elliptic (`IsRegProfile`), so the principal part has standard quadratic growth and no
local Lipschitz bound for `v` is needed first; the only difficulty is the quadratic ("natural")
growth of the right-hand side in `∇v`.

## The chain

The six links below were originally stated here as named `sorry`s.  They are now all proved,
each in its own file, and the placeholders were deleted by lane `L7`; the list is kept as the
road map of the lane, with the file that owns each link:

1. `IsWeakLogSol.exists_local_holder` — `InteriorMorreyHolder.lean`;
2. `IsWeakLogSol.exists_morrey` — `InteriorMorrey.lean`;
3. `exists_regHarmonic_campanato` — `InteriorHarmonic.lean` (with the deviations of
   `NOTES_c2b.md`; its analytic core `exists_regHarmonic_holder_field` is the one open
   `sorry` of the lane, owned by `reg/c2h`);
4. `IsWeakLogSol.exists_holder_gradient` — `InteriorCampanato.lean`;
5. the divergence-form Schauder estimate turned out to be **unnecessary** (lane `reg/c2c`
   proved link 6 by scaled Schauder plus drift absorption, `InteriorSchauder*.lean`) and was
   deleted;
6. `IsWeakLogSol.contDiffOn_two` — `InteriorC2.lean`;
   and `IsWeakLogSol.weakEq_memW0` — `InteriorWeakEq.lean`.

What this file still provides is the structure `IsRegHarmonic`, the homogeneous Sobolev-test
equation `IsRegHarmonic.weakEq_memW0` and the monotonicity core `comparison_energy_le`, all
proved here.

The original description of the chain follows.

1. `IsWeakLogSol.exists_local_holder` — **`v` is locally Hölder**.  `v` is a quasi-minimum of a
   functional with standard quadratic growth, hence lies in a De Giorgi class; the interior
   Hölder estimate is `Komlos.Literature.Regularized.IsDG.exists_holder_representative`
   (lane `DGN`).
2. `IsWeakLogSol.exists_morrey` — **the Morrey/Caccioppoli bound**
   `∫_{B_s} ‖∇v‖² ≤ C s^{d-2+2α}`.  Test the equation with `η² (v - v̄)`; the quadratic term
   `∫ η² |B(∇v)| |v - v̄| ≤ C osc(v) ∫ η² ‖∇v‖²` is absorbed because, by (1), the oscillation of
   `v` on a small ball is small.
3. `exists_regHarmonic_campanato` — **the homogeneous comparison problem**: a weak solution of
   `div ∇Ψ(∇h) = 0` on a ball is `C²` there and its gradient satisfies the Campanato decay
   `∫_{B_ρ} ‖∇h - (∇h)_ρ‖² ≤ C (ρ/r)^{d+2} ∫_{B_r} ‖∇h - (∇h)_r‖²`.  (Difference quotients give
   `h ∈ W^{2,2}_loc`; each `∂_k h` solves the *linear* equation `div (D²Ψ(∇h) ∇z) = 0` with
   bounded measurable uniformly elliptic coefficients, so De Giorgi–Nash gives `∇h ∈ C^{0,α}`,
   and then `schauder_C2` — whose right-hand side is `0` — gives `∇h ∈ C^{1,α}`.)
4. `IsWeakLogSol.exists_holder_gradient` — **`v ∈ C^{1,β}_loc`**.  Strong monotonicity of `∇Ψ`
   gives `c ∫_{B_r} ‖∇v - ∇h‖² ≤ ∫_{B_r} |f| |v - h|` with `f = κ v + 2 m + B(∇v)`; the Morrey
   bound of (2) makes the right-hand side `o(r^{d+2β})`, and the Campanato iteration
   (`Komlos.Literature.campanato_iteration_constants`) combines it with (3).
5. `exists_schauder_divergence_estimate` — the **linear** input still missing from the project:
   the interior Schauder estimate for `div (A ∇w) = div F` with `A`, `F` of class `C^{0,α}`.
   `Komlos.Literature.schauder_C2` is the case `F = 0` with a bounded zeroth-order right-hand
   side; the divergence-form right-hand side is what the difference-quotient argument of (6)
   produces, because `∫ (Δ_s f) ψ = ∫ f ∂_e ψ + O(s) = ∫ ⟪f e, ∇ψ⟫ + O(s)` and `f` is only
   Hölder, never Lipschitz.
6. `IsWeakLogSol.contDiffOn_two` — **`v ∈ C²`**.  With `v ∈ C^{1,β}` from (4), the coefficients
   `D²Ψ(∇v)` and the right-hand side `f` are `C^{0,β}`; the difference quotients `Δ_s v` solve
   `div (A_s ∇ Δ_s v) = div (f e) + O(s)` with uniformly `C^{0,β}` data, so (5) bounds `∇Δ_s v`
   in `C^{0,β}` uniformly in `s`, and `Komlos.Literature.contDiffOn_of_holder_difference`
   upgrades that to `∇v ∈ C¹`.

Steps (1), (2) and (4) all test the weak equations with functions that are not smooth, so they
need a `W₀^{1,2}` version of the weak equations.  For the homogeneous equation this is
`IsRegHarmonic.weakEq_memW0`, **proved** here from the project's density theorem
`Komlos.Literature.integral_inner_weakGrad_eq_of_memW0_two`; for the equation of `v` the
right-hand side is only `L¹` (natural growth), so the test functions must also be bounded, and
`IsWeakLogSol.weakEq_memW0` is a separate statement (`InteriorWeakEq.lean`).  The monotonicity
core of step (4), `comparison_energy_le`, is **proved** here.

The two ends of the lane are `exists_pos_continuous_minimizer` (`InteriorRep.lean`) and the
passage from (6) to the pointwise equation and to `RegEigenData` (`Interior.lean`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ m c C : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-! ### `Ψ`-harmonic functions -/

/-- **`h` is `Ψ`-harmonic on `U`**: `div ∇Ψ(∇h) = 0` weakly.  This is the comparison problem of
step (3): the homogeneous equation with the *same* principal part as the equation for `v`. -/
structure IsRegHarmonic (Ψ : Euc d → ℝ) (U : Set (Euc d)) (h : Euc d → ℝ)
    (H : Euc d → Euc d) : Prop where
  /-- `U` is open. -/
  isOpen : IsOpen U
  /-- `h` is continuous on `U`. -/
  continuousOn : ContinuousOn h U
  /-- `h` is globally measurable. -/
  measurable : Measurable h
  /-- `H` is globally measurable. -/
  measurable_grad : Measurable H
  /-- `H` is a weak gradient of `h` on `U`. -/
  hasWeakGradientOn : HasWeakGradientOn U h H
  /-- `H` is square integrable on every closed ball inside `U`. -/
  integrableOn_sq : ∀ (x₀ : Euc d) (r : ℝ), Metric.closedBall x₀ r ⊆ U →
    IntegrableOn (fun x => ‖H x‖ ^ 2) (Metric.closedBall x₀ r) volume
  /-- The homogeneous weak equation. -/
  weakEq : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    (∫ x, ⟪gradient Ψ (H x), gradient ψ x⟫) = 0

/-! ### Sobolev test functions and the comparison estimate

Both the Caccioppoli step (2) and the comparison step (4) test the weak equations with functions
that are *not* smooth — `η² (v - v̄)` and `v - h` — so they need the weak equations against
`W₀^{1,2}` test functions.  For the homogeneous equation this is exactly the project's density
theorem `Komlos.Literature.integral_inner_weakGrad_eq_of_memW0_two` and is **proved** below; for
the equation of `v` it is not, because the right-hand side `κ v + 2 m + B(∇v)` is only `L¹`
(`B` has quadratic growth in `∇v`), so the test functions must additionally be bounded. -/

/-- `∇Ψ ∘ G` inherits every `L^p` bound of `G`, because `‖∇Ψ q‖ ≤ C ‖q‖`. -/
theorem memLp_gradient_comp (h : IsRegProfileWith Ψ c C) {p : ℝ≥0∞} {G : Euc d → Euc d}
    (hG : MemLp G p) : MemLp (fun x => gradient Ψ (G x)) p := by
  refine (hG.const_smul C).mono ?_ (Eventually.of_forall fun x => ?_)
  · exact h.toIsRegProfile.contDiff_gradient.continuous.comp_aestronglyMeasurable
      hG.aestronglyMeasurable
  · show ‖gradient Ψ (G x)‖ ≤ ‖(C • G) x‖
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h.C_nonneg]
    exact h.norm_gradient_le (G x)

/-- The `L²` field `G` restricted to a ball inside `U`, as a global `L²` function. -/
theorem IsWeakLogSol.memLp_indicator (hsol : IsWeakLogSol κ m Ψ U v G) {y : Euc d} {s : ℝ}
    (hs : Metric.closedBall y s ⊆ U) :
    MemLp ((Metric.ball y s).indicator G) 2 := by
  refine (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet).2 ?_
  refine (memLp_two_iff_integrable_sq_norm hsol.measurable_grad.aestronglyMeasurable).2 ?_
  exact (hsol.integrableOn_sq y s hs).mono_set Metric.ball_subset_closedBall

/-- The `L²` field `H` restricted to a ball inside `U`, as a global `L²` function. -/
theorem IsRegHarmonic.memLp_indicator {h : Euc d → ℝ} {H : Euc d → Euc d}
    (hh : IsRegHarmonic Ψ U h H) {y : Euc d} {s : ℝ} (hs : Metric.closedBall y s ⊆ U) :
    MemLp ((Metric.ball y s).indicator H) 2 := by
  refine (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet).2 ?_
  refine (memLp_two_iff_integrable_sq_norm hh.measurable_grad.aestronglyMeasurable).2 ?_
  exact (hh.integrableOn_sq y s hs).mono_set Metric.ball_subset_closedBall

/-- `∇Ψ` commutes with restriction to a set, because `∇Ψ 0 = 0`. -/
theorem indicator_gradient_comp (hΨ : IsRegProfile Ψ) (S : Set (Euc d)) (G : Euc d → Euc d) :
    S.indicator (fun x => gradient Ψ (G x)) = fun x => gradient Ψ (S.indicator G x) := by
  funext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, hΨ.gradient_zero]

/-- **The homogeneous weak equation against `W₀^{1,2}` test functions.**  Proved from the
project's density theorem `Komlos.Literature.integral_inner_weakGrad_eq_of_memW0_two`: the
right-hand side is `0`, hence trivially `L²`, and the flux `∇Ψ ∘ H` is `L²` on any ball whose
closure lies in `U`. -/
theorem IsRegHarmonic.weakEq_memW0 (hΨ : IsRegProfile Ψ) {h : Euc d → ℝ} {H : Euc d → Euc d}
    (hh : IsRegHarmonic Ψ U h H) {y : Euc d} {s : ℝ} (hs : Metric.closedBall y s ⊆ U)
    {T : Set (Euc d)} (hT : IsCompact T) (hTs : T ⊆ Metric.ball y s) {ψ : Euc d → ℝ}
    (hψ : MemW0 2 T ψ) (hψg : ∀ᵐ x, x ∉ T → weakGrad ψ x = 0) :
    (∫ x, ⟪gradient Ψ (H x), weakGrad ψ x⟫) = 0 := by
  obtain ⟨c, C, hC⟩ := hΨ.exists_isRegProfileWith
  have hball : Metric.ball y s ⊆ U := Metric.ball_subset_closedBall.trans hs
  have hΦ : MemLp ((Metric.ball y s).indicator fun x => gradient Ψ (H x)) 2 := by
    rw [indicator_gradient_comp hΨ]
    exact memLp_gradient_comp hC (hh.memLp_indicator hs)
  have hg : MemLp ((Metric.ball y s).indicator fun _ : Euc d => (0 : ℝ)) 2 := by
    simp
  have hweak : ∀ χ : Euc d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.ball y s →
      (∫ x, ⟪gradient Ψ (H x), gradient χ x⟫) = ∫ x, (0 : ℝ) * χ x := by
    intro χ h1 h2 h3
    rw [hh.weakEq χ h1 h2 (h3.trans hball)]
    simp
  have key := Komlos.Literature.integral_inner_weakGrad_eq_of_memW0_two Metric.isOpen_ball hΦ hg
    hweak hT hTs hψ hψg
  simpa using key

/-- **The comparison estimate**, the monotonicity half of step (4).  If `G` and `H` are `L²`
fields whose fluxes are tested against `G - H` by the two weak equations — the inhomogeneous one
with right-hand side `f`, tested against `w`, and the homogeneous one — then strong monotonicity
of `∇Ψ` (`IsRegProfileWith.inner_gradient_sub`) gives

`c ∫ ‖G - H‖² ≤ ∫ |f w|`.

In the application `G = ∇v`, `H = ∇h` (both restricted to a ball `B`), `w = v - h` and
`f = κ v + 2 m + B(∇v)`; the right-hand side is then estimated by Poincaré and the Morrey
bound (2). -/
theorem comparison_energy_le (h : IsRegProfileWith Ψ c C) {f w : Euc d → ℝ}
    {G H : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal 2)) (hH : MemLp H (ENNReal.ofReal 2))
    (heq1 : (∫ x, ⟪gradient Ψ (G x), G x - H x⟫) = -∫ x, f x * w x)
    (heq2 : (∫ x, ⟪gradient Ψ (H x), G x - H x⟫) = 0) :
    c * ∫ x, ‖G x - H x‖ ^ 2 ≤ ∫ x, |f x * w x| := by
  have hGΨ := memLp_gradient_comp h hG
  have hHΨ := memLp_gradient_comp h hH
  have hsub : MemLp (fun x => G x - H x) (ENNReal.ofReal 2) := hG.sub hH
  have hid : ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hi1 : Integrable fun x => ⟪gradient Ψ (G x), G x - H x⟫ := by
    simpa using Komlos.Literature.FrozenDirichlet.integrable_inner_apply hid hGΨ hsub
  have hi2 : Integrable fun x => ⟪gradient Ψ (H x), G x - H x⟫ := by
    simpa using Komlos.Literature.FrozenDirichlet.integrable_inner_apply hid hHΨ hsub
  have hsq : Integrable fun x => ‖G x - H x‖ ^ 2 := Komlos.Literature.FrozenDirichlet.integrable_norm_sq hsub
  have hmono : ∀ x, c * ‖G x - H x‖ ^ 2 ≤
      ⟪gradient Ψ (G x), G x - H x⟫ - ⟪gradient Ψ (H x), G x - H x⟫ := fun x => by
    have hx := h.inner_gradient_sub (G x) (H x)
    rwa [inner_sub_left] at hx
  have habs : -∫ x, f x * w x ≤ ∫ x, |f x * w x| := by
    have h1 : -∫ x, f x * w x ≤ |∫ x, f x * w x| := neg_le_abs _
    have h2 : |∫ x, f x * w x| ≤ ∫ x, |f x * w x| := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm fun x => f x * w x
    exact h1.trans h2
  calc c * ∫ x, ‖G x - H x‖ ^ 2 = ∫ x, c * ‖G x - H x‖ ^ 2 := (integral_const_mul c _).symm
    _ ≤ ∫ x, (⟪gradient Ψ (G x), G x - H x⟫ - ⟪gradient Ψ (H x), G x - H x⟫) :=
        integral_mono (hsq.const_mul c) (hi1.sub hi2) hmono
    _ = -∫ x, f x * w x := by rw [integral_sub hi1 hi2, heq1, heq2, sub_zero]
    _ ≤ ∫ x, |f x * w x| := habs

end Komlos.Literature.Regularized
