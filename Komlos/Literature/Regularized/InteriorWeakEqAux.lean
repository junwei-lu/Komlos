import Komlos.Literature.Regularized.InteriorDefs

/-!
# Toolkit for the `W₀^{1,2}` test-function upgrade (lane `L3a`, links 1 and 3)

Auxiliary material for `Komlos/Literature/Regularized/InteriorWeakEq.lean`, which proves link 3
of lane `L3` (`IsWeakLogSol.weakEq_memW0`): the weak equation of `v` against *bounded*
`W₀^{1,2}` test functions.

The right-hand side `f = κ v + 2 m + B(∇v)` of the equation for `v` has quadratic growth in
`∇v`, hence is only `L¹` on a ball; the `L²`–`L²` duality behind
`Komlos.Literature.integral_inner_weakGrad_eq_of_memW0_two` is therefore unavailable, and the
approximation argument has to be run by hand, with dominated convergence on the right-hand
side.  Two ingredients are missing from the repository and are supplied here.

## Main results

* `exists_contDiff_tendsto_eLpNorm_bounded`, `MemW0.exists_contDiff_tendsto_eLpNorm_bounded` —
  the smooth-approximation theorem of `Komlos/Literature/Sobolev/Density.lean` with the extra
  conclusion that the approximants obey the **same sup bound** as the approximated function.
  This is automatic for the mollifications used in the proof
  (`Komlos.Literature.norm_mollifyWith_le_of_norm_le`), but the repository's statement does not
  record it, and it is exactly what makes the dominated convergence of the right-hand side work.
* `IsWeakLogSol.measurable_rhs`, `IsWeakLogSol.integrableOn_rhs` — the right-hand side is
  measurable and `L¹` on every closed ball inside `U`: `v` is continuous there, and
  `|B(q)| ≤ 2 C ‖q‖² + 2 |Ψ 0|` (`abs_regNatGrowth_le`) together with `∇v ∈ L²_loc`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ m c C : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ}
  {G : Euc d → Euc d}

/-! ### Bounded smooth approximation in `W^{1,p}` -/

/-- **Smooth approximation preserving a sup bound.**  This is
`Komlos.Literature.exists_contDiff_tendsto_eLpNorm_of_hasWeakGradient` with the extra conclusion
`|u n| ≤ M`: the approximants are mollifications of `f`, and the mollification of a function
bounded by `M` is bounded by `M` (`Komlos.Literature.norm_mollifyWith_le_of_norm_le`). -/
theorem exists_contDiff_tendsto_eLpNorm_bounded {p : ℝ} (hp : 1 < p) {Ω : Set (Euc d)}
    (hΩ : IsOpen Ω) {L : Set (Euc d)} (hL : IsCompact L) (hLΩ : L ⊆ Ω) {f : Euc d → ℝ}
    {Gf : Euc d → Euc d} (hfG : HasWeakGradient f Gf) (hf : MemLp f (ENNReal.ofReal p))
    (hG : MemLp Gf (ENNReal.ofReal p)) (hfL : ∀ x, x ∉ L → f x = 0) {M : ℝ}
    (hfM : ∀ x, |f x| ≤ M) :
    ∃ u : ℕ → Euc d → ℝ, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, tsupport (u n) ⊆ Ω) ∧ (∀ n x, |u n x| ≤ M) ∧
      Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (gradient (u n) - Gf) (ENNReal.ofReal p)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hLδ⟩ := hL.exists_cthickening_subset_open hΩ hLΩ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  set φ : ℕ → ContDiffBump (0 : Euc d) := fun n => Komlos.Literature.mollifierBump (max n N)
    with hφ_def
  have hrOut : ∀ n, (φ n).rOut < δ := by
    intro n
    have hle : ((N : ℝ) + 1) ≤ ((max n N : ℕ) : ℝ) + 1 := by
      have h1 : (N : ℝ) ≤ ((max n N : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
      linarith
    have h2 : 1 / (((max n N : ℕ) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hle
    simp only [hφ_def]
    show 1 / (((max n N : ℕ) : ℝ) + 1) < δ
    exact lt_of_le_of_lt h2 hN
  have hφlim : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [hφ_def]
    have hmax : max n N = n := by omega
    show (1 : ℝ) / ((n : ℝ) + 1) = 1 / (((max n N : ℕ) : ℝ) + 1)
    rw [hmax]
  set u : ℕ → Euc d → ℝ := fun n => Komlos.Literature.mollifyWith ((φ n).normed volume) f
    with hu_def
  have hsupp : ∀ n, Function.support (u n) ⊆ Metric.cthickening δ L := by
    intro n x hx
    simp only [hu_def] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Komlos.Literature.support_mollifyWith_subset ((φ n).normed volume) f hx
    rw [ContDiffBump.support_normed_eq] at ha
    have ha' : ‖a‖ < (φ n).rOut := by simpa using ha
    have hbL : b ∈ L := by
      by_contra h
      exact hb (hfL b h)
    refine Metric.mem_cthickening_of_dist_le _ b δ L hbL ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    linarith [hrOut n]
  have hcpt : IsCompact (Metric.cthickening δ L) := hL.cthickening
  have hgrad : ∀ n, gradient (u n) = Komlos.Literature.mollifyWith ((φ n).normed volume) Gf :=
    fun n => Komlos.Literature.gradient_mollifyWith hfG (φ n).contDiff_normed
      (φ n).hasCompactSupport_normed
  have hM0 : ∀ t, ‖f t‖ ≤ M := fun t => by rw [Real.norm_eq_abs]; exact hfM t
  refine ⟨u, fun n => Komlos.Literature.contDiff_mollifyWith (φ n).contDiff_normed
      (φ n).hasCompactSupport_normed hfG.locallyIntegrable,
    fun n => HasCompactSupport.of_support_subset_isCompact hcpt (hsupp n),
    fun n => (closure_minimal (hsupp n) Metric.isClosed_cthickening).trans hLδ, ?_, ?_, ?_⟩
  · intro n x
    have h := Komlos.Literature.norm_mollifyWith_le_of_norm_le (φ n).nonneg_normed
      (φ n).integrable_normed (φ n).integral_normed hM0 x
    rwa [Real.norm_eq_abs] at h
  · simp only [hu_def]
    exact Komlos.Literature.tendsto_eLpNorm_mollifyWith_sub hφlim hp hf
  · simp only [hgrad]
    exact Komlos.Literature.tendsto_eLpNorm_mollifyWith_sub hφlim hp hG

/-- The `W₀^{1,p}` form of `exists_contDiff_tendsto_eLpNorm_bounded`: a *bounded* element of
`W₀^{1,p}(K)`, `K` compact inside the open set `Ω`, is approximated in the graph norm by smooth
functions compactly supported in `Ω` and obeying the same bound. -/
theorem _root_.Komlos.Literature.MemW0.exists_contDiff_tendsto_eLpNorm_bounded {p : ℝ} (hp : 1 < p) {Ω : Set (Euc d)}
    (hΩ : IsOpen Ω) {K : Set (Euc d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) {f : Euc d → ℝ}
    (hf : MemW0 p K f) {M : ℝ} (hfM : ∀ x, |f x| ≤ M) :
    ∃ u : ℕ → Euc d → ℝ, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, tsupport (u n) ⊆ Ω) ∧ (∀ n x, |u n x| ≤ M) ∧
      Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (gradient (u n) - weakGrad f) (ENNReal.ofReal p)) atTop
        (𝓝 0) := by
  set f' := K.indicator f with hf'_def
  have hff' : f =ᵐ[volume] f' := by
    filter_upwards [hf.ae_eq_zero] with x hx
    by_cases hxK : x ∈ K
    · rw [hf'_def, Set.indicator_of_mem hxK]
    · rw [hf'_def, Set.indicator_of_notMem hxK, hx hxK]
  have hf'K : ∀ x, x ∉ K → f' x = 0 := fun x hx => Set.indicator_of_notMem hx f
  have hf'M : ∀ x, |f' x| ≤ M := by
    intro x
    by_cases hxK : x ∈ K
    · rw [hf'_def, Set.indicator_of_mem hxK]; exact hfM x
    · rw [hf'_def, Set.indicator_of_notMem hxK, abs_zero]
      exact (abs_nonneg (f x)).trans (hfM x)
  obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ :=
    _root_.Komlos.Literature.Regularized.exists_contDiff_tendsto_eLpNorm_bounded hp hΩ hK hKΩ
      (hf.hasWeakGradient.congr_left hff') (hf.memLp.ae_eq hff') hf.memLp_weakGrad hf'K hf'M
  refine ⟨u, h1, h2, h3, h4, h5.congr fun n => eLpNorm_congr_ae ?_, h6⟩
  filter_upwards [hff'] with x hx
  simp only [Pi.sub_apply, hx]

/-! ### The right-hand side of the equation for `v` -/

/-- The right-hand side `κ v + 2 m + B(G)` is measurable. -/
theorem IsWeakLogSol.measurable_rhs (hΨ : IsRegProfile Ψ) (hsol : IsWeakLogSol κ m Ψ U v G) :
    Measurable (regLogRhs κ m Ψ v G) := by
  unfold regLogRhs
  exact ((measurable_const.mul hsol.measurable).add measurable_const).add
    ((continuous_regNatGrowth hΨ).measurable.comp hsol.measurable_grad)

/-- The right-hand side `κ v + 2 m + B(G)` is integrable on every closed ball inside `U`: `v` is
continuous on the (compact) ball, and `|B(G)| ≤ 2 C ‖G‖² + 2 |Ψ 0|` with `‖G‖² ∈ L¹` there.

This is the precise sense in which the right-hand side of the equation for `v` is only `L¹`: the
natural growth `|B(q)| ≤ C ‖q‖²` is borderline for a gradient in `L²`. -/
theorem IsWeakLogSol.integrableOn_rhs (hΨ : IsRegProfile Ψ) (hsol : IsWeakLogSol κ m Ψ U v G)
    {y : Euc d} {s : ℝ} (hs : Metric.closedBall y s ⊆ U) :
    IntegrableOn (regLogRhs κ m Ψ v G) (Metric.closedBall y s) volume := by
  obtain ⟨c, C, hC⟩ := hΨ.exists_isRegProfileWith
  have hcpt : IsCompact (Metric.closedBall y s) := isCompact_closedBall y s
  have hfin : volume (Metric.closedBall y s) < ⊤ := hcpt.measure_lt_top
  -- the linear part
  have hv : IntegrableOn v (Metric.closedBall y s) volume :=
    (hsol.continuousOn.mono hs).integrableOn_compact hcpt
  have h1 : IntegrableOn (fun x => κ * v x + 2 * m) (Metric.closedBall y s) volume :=
    (hv.const_mul κ).add (integrableOn_const hfin.ne)
  -- the natural growth part
  have hsq : IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall y s) volume :=
    hsol.integrableOn_sq y s hs
  have hdom : IntegrableOn (fun x => 2 * C * ‖G x‖ ^ 2 + 2 * |Ψ 0|)
      (Metric.closedBall y s) volume :=
    (hsq.const_mul (2 * C)).add (integrableOn_const hfin.ne)
  have hmeas : AEStronglyMeasurable (fun x => regNatGrowth Ψ (G x))
      (volume.restrict (Metric.closedBall y s)) :=
    (((continuous_regNatGrowth hΨ).measurable.comp
      hsol.measurable_grad).aestronglyMeasurable).restrict
  have h2 : IntegrableOn (fun x => regNatGrowth Ψ (G x)) (Metric.closedBall y s) volume := by
    refine Integrable.mono' hdom hmeas (Eventually.of_forall fun x => ?_)
    have h := abs_regNatGrowth_le hC (G x)
    rwa [Real.norm_eq_abs]
  have hsum : IntegrableOn (fun x => (κ * v x + 2 * m) + regNatGrowth Ψ (G x))
      (Metric.closedBall y s) volume := by
    refine (h1.add h2).congr_fun (fun x _ => rfl) measurableSet_closedBall
  exact hsum

/-! ### Integrability from a bound on a set -/

/-- A function vanishing outside a measurable set `S` and dominated there by an integrable
function is integrable. -/
theorem integrable_of_bound_on_set {E : Type*} [NormedAddCommGroup E] {g : Euc d → E}
    {S : Set (Euc d)} (hS : MeasurableSet S) (hm : AEStronglyMeasurable g volume)
    {b : Euc d → ℝ} (hb : IntegrableOn b S volume) (hbound : ∀ x ∈ S, ‖g x‖ ≤ b x)
    (hzero : ∀ x, x ∉ S → g x = 0) : Integrable g volume := by
  have hb' : Integrable (S.indicator b) volume := (integrable_indicator_iff hS).2 hb
  refine Integrable.mono' hb' hm (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]; exact hbound x hx
  · rw [Set.indicator_of_notMem hx, hzero x hx, norm_zero]

/-! ### `L²` bounds for the flux

These three lemmas duplicate `memLp_gradient_comp`, `IsWeakLogSol.memLp_indicator` and
`indicator_gradient_comp` of `Komlos/Literature/Regularized/InteriorRegularity.lean`.  They are
reproved here (under primed names) because the files of this lane must **not** import
`InteriorRegularity.lean`: they prove statements whose `sorry` placeholders live in it, and the
coordinator discharges those placeholders by a call to the primed versions, which would be a
module cycle if the dependency ran the other way. -/

/-- `∇Ψ ∘ G` inherits every `L^p` bound of `G`, because `‖∇Ψ q‖ ≤ C ‖q‖`. -/
theorem memLp_gradient_comp' (h : IsRegProfileWith Ψ c C) {q : ℝ≥0∞} {Gf : Euc d → Euc d}
    (hG : MemLp Gf q) : MemLp (fun x => gradient Ψ (Gf x)) q := by
  refine (hG.const_smul C).mono ?_ (Eventually.of_forall fun x => ?_)
  · exact h.toIsRegProfile.contDiff_gradient.continuous.comp_aestronglyMeasurable
      hG.aestronglyMeasurable
  · show ‖gradient Ψ (Gf x)‖ ≤ ‖(C • Gf) x‖
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h.C_nonneg]
    exact h.norm_gradient_le (Gf x)

/-- The `L²` field `G` restricted to a ball inside `U`, as a global `L²` function. -/
theorem IsWeakLogSol.memLp_indicator' (hsol : IsWeakLogSol κ m Ψ U v G) {y : Euc d} {s : ℝ}
    (hs : Metric.closedBall y s ⊆ U) :
    MemLp ((Metric.ball y s).indicator G) 2 := by
  refine (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet).2 ?_
  refine (memLp_two_iff_integrable_sq_norm hsol.measurable_grad.aestronglyMeasurable).2 ?_
  exact (hsol.integrableOn_sq y s hs).mono_set Metric.ball_subset_closedBall

/-- `∇Ψ` commutes with restriction to a set, because `∇Ψ 0 = 0`. -/
theorem indicator_gradient_comp' (hΨ : IsRegProfile Ψ) (S : Set (Euc d)) (Gf : Euc d → Euc d) :
    S.indicator (fun x => gradient Ψ (Gf x)) = fun x => gradient Ψ (S.indicator Gf x) := by
  funext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, hΨ.gradient_zero]

/-- `ENNReal.ofReal 2 = 2`. -/
theorem ofReal_two' : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num

/-- The conjugate exponent of `2` is `2`, as an `ℝ≥0∞` exponent. -/
theorem ofReal_conjExponent_two : ENNReal.ofReal (Real.conjExponent (2 : ℝ)) = 2 := by
  rw [Real.HolderConjugate.conjExponent_eq Real.HolderConjugate.two_two]
  norm_num

end Komlos.Literature.Regularized
