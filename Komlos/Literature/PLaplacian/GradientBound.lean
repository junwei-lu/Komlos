import Komlos.Literature.PLaplacian.SchauderAux

/-!
# The interior energy (Caccioppoli) bound for linear divergence-form equations

This file supplies the missing analytic input of the **interior gradient bound**
`schauder_interior_gradient_bound` (Gilbarg–Trudinger, *Elliptic Partial Differential Equations
of Second Order*, Theorem 8.32; paper Appendix A, *Eigenfunction inputs*): the uniform
**Caccioppoli energy estimate**

`∫_{B(x₀, 3R/2)} ‖∇w‖² ≤ E(d, μ, Λ, R)`

for a `C¹` weak solution of `div(A ∇w) = g` on `B(x₀, 2R)` with `A` uniformly elliptic
(constant `μ`) and bounded, `|g| ≤ Λ` and `|w| ≤ Λ`; the constant `E` depends only on
`d, μ, Λ, R` and *not* on `x₀, A, g, w`.  That uniformity is exactly what the Campanato
iteration of `RegularitySchauder.lean` needs in order to start.

## Contents

* `gradient_mul_apply`, `gradient_comp_sub_const` — two elementary gradient rules.
* `continuous_of_continuousOn_zero_outside`, `exists_bound_of_zero_outside'` — gluing a function
  continuous on an open set with the zero function outside a closed subset.
* `integral_inner_eq_of_contDiff_one` — **the weak formulation extends from `C^∞` to `C¹`
  compactly supported test functions** (mollification: `mollifyWith`, `gradient_mollifyWith`,
  `norm_mollifyWith_sub_le`).  This is what makes the Caccioppoli test function `η² w`
  admissible, since `w` is only `C¹`.
* `exists_uniform_cutoff` — a translation-invariant smooth cutoff with a gradient bound
  depending only on the radii and the dimension.
* `exists_linear_energy_bound` — the Caccioppoli energy estimate itself.

The test function is `ψ = η² w` with `η` a cutoff that is `1` on `B(x₀, 3R/2)`: testing the
equation with it and using `⟪A ∇w, ∇w⟫ ≥ μ ‖∇w‖²` together with Young's inequality
`2ab ≤ (μ/2) a² + (2/μ) b²` absorbs the cross term.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff Convolution

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Elementary gradient rules -/

/-- **The product rule for gradients.** -/
theorem gradient_mul_apply {f h : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) :
    gradient (fun y => f y * h y) x = f x • gradient h x + h x • gradient f x := by
  have hd : HasFDerivAt (fun y => f y * h y) (f x • fderiv ℝ h x + h x • fderiv ℝ f x) x :=
    hf.hasFDerivAt.mul hh.hasFDerivAt
  refine ext_inner_right ℝ fun v => ?_
  rw [← fderiv_apply_eq_inner_gradient, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, inner_add_left, real_inner_smul_left, fderiv_apply_eq_inner_gradient]

/-- **The gradient of a translate.** -/
theorem gradient_comp_sub_const {f : Euc d → ℝ} (hf : Differentiable ℝ f) (a x : Euc d) :
    gradient (fun y => f (y - a)) x = gradient f (x - a) := by
  have h : HasFDerivAt (fun y : Euc d => f (y - a))
      ((fderiv ℝ f (x - a)).comp (ContinuousLinearMap.id ℝ (Euc d))) x :=
    (hf (x - a)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  have h' : HasFDerivAt (fun y : Euc d => f (y - a)) (fderiv ℝ f (x - a)) x := by
    simpa using h
  refine ext_inner_right ℝ fun v => ?_
  rw [← fderiv_apply_eq_inner_gradient, h'.fderiv, fderiv_apply_eq_inner_gradient]

/-! ### Gluing with zero outside a compact set -/

/-- A function that is continuous on an open set `V` and vanishes outside a closed `S ⊆ V` is
continuous on all of `Euc d`. -/
theorem continuous_of_continuousOn_zero_outside {E : Type*} [TopologicalSpace E] [Zero E]
    {V S : Set (Euc d)} (hV : IsOpen V) (hS : IsClosed S) (hSV : S ⊆ V) {f : Euc d → E}
    (hf : ContinuousOn f V) (h0 : ∀ x, x ∉ S → f x = 0) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ V
  · exact hf.continuousAt (hV.mem_nhds hx)
  · have hxS : x ∉ S := fun h => hx (hSV h)
    have he : (fun _ : Euc d => (0 : E)) =ᶠ[𝓝 x] f := by
      filter_upwards [hS.isOpen_compl.mem_nhds hxS] with y hy
      exact (h0 y hy).symm
    exact continuousAt_const.congr he

/-- A function continuous on a compact set `S` and vanishing outside `S` is globally bounded.
(Copied from `Komlos.Literature.exists_bound_of_zero_outside` of `WangXia`, which is not
importable here.) -/
theorem exists_bound_of_zero_outside' {E : Type*} [NormedAddCommGroup E] {S : Set (Euc d)}
    (hS : IsCompact S) {f : Euc d → E} (hf : ContinuousOn f S) (h0 : ∀ x, x ∉ S → f x = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hf
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ S
  · exact (hB x hx).trans (le_max_left _ _)
  · rw [h0 x hx, norm_zero]
    exact le_max_right _ _

/-- A function that is `C¹` on an open `V` and supported in a closed `S ⊆ V` is globally `C¹`. -/
theorem contDiff_one_of_contDiffOn {V S : Set (Euc d)} (hV : IsOpen V) (hS : IsClosed S)
    (hSV : S ⊆ V) {f : Euc d → ℝ} (hf : ContDiffOn ℝ 1 f V) (hfS : tsupport f ⊆ S) :
    ContDiff ℝ 1 f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact hf.contDiffAt (hV.mem_nhds hx)
  · have hxS : x ∉ tsupport f := fun h => hx (hSV (hfS h))
    have he : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxS] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- A real function continuous on an open `V` and vanishing outside a compact `S ⊆ V` is
integrable. -/
theorem integrable_of_continuousOn_zero_outside {V S : Set (Euc d)} (hV : IsOpen V)
    (hS : IsCompact S) (hSV : S ⊆ V) {u : Euc d → ℝ} (hu : ContinuousOn u V)
    (h0 : ∀ x, x ∉ S → u x = 0) : Integrable u :=
  (continuous_of_continuousOn_zero_outside hV hS.isClosed hSV hu
    h0).integrable_of_hasCompactSupport (HasCompactSupport.intro hS h0)

/-! ### From `C^∞` to `C¹` test functions -/

/-- **The weak formulation extends to `C¹` compactly supported test functions.**  If the
divergence-form identity `∫ ⟪W, ∇ψ⟫ = ∫ g ψ` holds for every `ψ ∈ C_c^∞(B(x₀, r))`, and `W`, `g`
are continuous on `B(x₀, r)`, then it holds for every `C¹` compactly supported `ψ` whose support
lies in the strictly smaller ball `B̄(x₀, s)`, `s < r`.

Proof: mollify, `ψ_δ = ρ_δ ⋆ ψ`.  Then `ψ_δ` is `C^∞` with support in `B̄(x₀, s + δ) ⊆ B(x₀, r)`
(`support_mollifyWith_subset`), `∇ψ_δ = ρ_δ ⋆ ∇ψ` (`gradient_mollifyWith`), and both `ψ_δ → ψ`
and `∇ψ_δ → ∇ψ` *uniformly* (`norm_mollifyWith_sub_le` plus the uniform continuity of the
compactly supported continuous functions `ψ` and `∇ψ`).  All integrands live on the fixed compact
`B̄(x₀, t)`, where `‖W‖` and `|g|` are bounded, so both sides pass to the limit. -/
theorem integral_inner_eq_of_contDiff_one {x₀ : Euc d} {r s : ℝ} (hs : 0 ≤ s) (hsr : s < r)
    {W : Euc d → Euc d} {g : Euc d → ℝ}
    (hW : ContinuousOn W (Metric.ball x₀ r)) (hg : ContinuousOn g (Metric.ball x₀ r))
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball x₀ r → ∫ x, ⟪W x, gradient ψ x⟫ = ∫ x, g x * ψ x)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ)
    (hψb : tsupport ψ ⊆ Metric.closedBall x₀ s) :
    ∫ x, ⟪W x, gradient ψ x⟫ = ∫ x, g x * ψ x := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (s + r) / 2 := ⟨_, rfl⟩
  have hst : s < t := by rw [ht]; linarith
  have htr : t < r := by rw [ht]; linarith
  have ht0 : 0 ≤ t := le_trans hs hst.le
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Euc d), S = Metric.closedBall x₀ t := ⟨_, rfl⟩
  have hScpt : IsCompact S := by rw [hSdef]; exact isCompact_closedBall x₀ t
  have hSclosed : IsClosed S := by rw [hSdef]; exact Metric.isClosed_closedBall
  have hSball : S ⊆ Metric.ball x₀ r := by
    rw [hSdef]; exact Metric.closedBall_subset_ball htr
  have hSfin : volume S < ⊤ := by rw [hSdef]; exact measure_closedBall_lt_top
  have hSvol : (0 : ℝ) ≤ volume.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_nonneg
  have hsS : Metric.closedBall x₀ s ⊆ S := by
    rw [hSdef]; exact Metric.closedBall_subset_closedBall hst.le
  -- Bounds for the data on the fixed compact `S`.
  obtain ⟨CW, hCW0, hCW⟩ : ∃ CW : ℝ, 0 ≤ CW ∧ ∀ x ∈ S, ‖W x‖ ≤ CW := by
    obtain ⟨B, hB⟩ := hScpt.exists_bound_of_continuousOn (hW.mono hSball)
    exact ⟨max B 0, le_max_right _ _, fun x hx => (hB x hx).trans (le_max_left _ _)⟩
  obtain ⟨Cg, hCg0, hCg⟩ : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x ∈ S, ‖g x‖ ≤ Cg := by
    obtain ⟨B, hB⟩ := hScpt.exists_bound_of_continuousOn (hg.mono hSball)
    exact ⟨max B 0, le_max_right _ _, fun x hx => (hB x hx).trans (le_max_left _ _)⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (CW + Cg) * volume.real S + 1 := ⟨_, rfl⟩
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ CW + Cg) hSvol]
  have hK0 : (0 : ℝ) < K := by linarith
  -- Integrability of any continuous integrand supported in `S`.
  have hint : ∀ u : Euc d → ℝ, ContinuousOn u (Metric.ball x₀ r) → (∀ x, x ∉ S → u x = 0) →
      Integrable u := by
    intro u hu h0
    exact (continuous_of_continuousOn_zero_outside Metric.isOpen_ball hSclosed hSball hu
      h0).integrable_of_hasCompactSupport (HasCompactSupport.intro hScpt h0)
  -- The key `ε`-estimate.
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ x, ⟪W x, gradient ψ x⟫) - ∫ x, g x * ψ x‖ ≤ ε := by
    intro ε hε
    obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = ε / K := ⟨_, rfl⟩
    have he0 : 0 < e := by rw [hedef]; exact div_pos hε hK0
    -- the moduli of continuity of `ψ` and `∇ψ`
    have hψuc : UniformContinuous ψ := hψs.uniformContinuous_of_continuous hψ.continuous
    have hgψuc : UniformContinuous (gradient ψ) :=
      (hasCompactSupport_gradient hψs).uniformContinuous_of_continuous (continuous_gradient hψ)
    obtain ⟨δ₁, hδ₁, hmod₁⟩ := Metric.uniformContinuous_iff.1 hψuc e he0
    obtain ⟨δ₂, hδ₂, hmod₂⟩ := Metric.uniformContinuous_iff.1 hgψuc e he0
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min δ₁ δ₂) (t - s) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by
      rw [hδdef]
      exact lt_min (lt_min hδ₁ hδ₂) (by linarith)
    have hδ1 : δ ≤ δ₁ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ2 : δ ≤ δ₂ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hδt : δ ≤ t - s := by rw [hδdef]; exact min_le_right _ _
    -- the mollifier
    obtain ⟨φ, hφdef⟩ : ∃ φ : ContDiffBump (0 : Euc d),
        φ = ⟨δ / 2, δ, by positivity, by linarith⟩ := ⟨_, rfl⟩
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : Euc d → ℝ, ρ = φ.normed volume := ⟨_, rfl⟩
    have hρc : Continuous ρ := by rw [hρdef]; exact φ.continuous_normed
    have hρinf : ContDiff ℝ ∞ ρ := by rw [hρdef]; exact φ.contDiff_normed
    have hρs : HasCompactSupport ρ := by rw [hρdef]; exact φ.hasCompactSupport_normed
    have hρ0 : ∀ y, 0 ≤ ρ y := by
      intro y
      rw [hρdef]
      exact φ.nonneg_normed y
    have hρ1 : ∫ y, ρ y = 1 := by rw [hρdef]; exact φ.integral_normed
    have hφout : φ.rOut = δ := by rw [hφdef]
    have hρδ : Function.support ρ ⊆ Metric.ball (0 : Euc d) δ := by
      rw [hρdef, φ.support_normed_eq, hφout]
    -- the mollified test function
    obtain ⟨u, hudef⟩ : ∃ u : Euc d → ℝ, u = mollifyWith ρ ψ := ⟨_, rfl⟩
    have huinf : ContDiff ℝ ∞ u := by
      rw [hudef]
      exact contDiff_mollifyWith hρinf hρs hψ.continuous.locallyIntegrable
    have hgradu : gradient u = mollifyWith ρ (gradient ψ) := by
      rw [hudef]
      exact gradient_mollifyWith (hasWeakGradient_gradient hψ hψs) hρinf hρs
    have husupp : tsupport u ⊆ S := by
      refine closure_minimal ?_ hSclosed
      rw [hudef]
      refine (support_mollifyWith_subset ρ ψ).trans ?_
      have h1 : Function.support ρ ⊆ Metric.closedBall (0 : Euc d) δ :=
        hρδ.trans Metric.ball_subset_closedBall
      have h2 : Function.support ψ ⊆ Metric.closedBall x₀ s := subset_closure.trans hψb
      calc Function.support ρ + Function.support ψ
          ⊆ Metric.closedBall (0 : Euc d) δ + Metric.closedBall x₀ s := Set.add_subset_add h1 h2
        _ = Metric.closedBall x₀ (δ + s) := by
            rw [closedBall_add_closedBall hδ0.le hs, zero_add]
        _ ⊆ S := by
            rw [hSdef]
            exact Metric.closedBall_subset_closedBall (by linarith)
    have hucs : HasCompactSupport u :=
      HasCompactSupport.intro hScpt fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => hx (husupp h)
    -- uniform closeness
    have hclose1 : ∀ x, ‖u x - ψ x‖ ≤ e := by
      intro x
      rw [hudef]
      refine norm_mollifyWith_sub_le hρc hρs hρ0 hρ1 hρδ hψ.continuous.locallyIntegrable ?_
      filter_upwards with y hy
      have hd : dist y x < δ₁ := lt_of_lt_of_le (Metric.mem_ball.1 hy) hδ1
      have h1 : dist (ψ y) (ψ x) < e := hmod₁ hd
      rw [dist_eq_norm] at h1
      exact h1.le
    have hclose2 : ∀ x, ‖gradient u x - gradient ψ x‖ ≤ e := by
      intro x
      rw [hgradu]
      refine norm_mollifyWith_sub_le hρc hρs hρ0 hρ1 hρδ
        (continuous_gradient hψ).locallyIntegrable ?_
      filter_upwards with y hy
      have hd : dist y x < δ₂ := lt_of_lt_of_le (Metric.mem_ball.1 hy) hδ2
      have h1 : dist (gradient ψ y) (gradient ψ x) < e := hmod₂ hd
      rw [dist_eq_norm] at h1
      exact h1.le
    -- the weak identity for the smooth test function
    have heq : ∫ x, ⟪W x, gradient u x⟫ = ∫ x, g x * u x :=
      hweak u huinf hucs (husupp.trans hSball)
    -- vanishing outside `S`
    have hz1 : ∀ x, x ∉ S → ⟪W x, gradient ψ x⟫ = 0 := fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport fun h => hx (hsS (hψb h)), inner_zero_right]
    have hz2 : ∀ x, x ∉ S → ⟪W x, gradient u x⟫ = 0 := fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport fun h => hx (husupp h), inner_zero_right]
    have hz3 : ∀ x, x ∉ S → g x * ψ x = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsS (hψb h)), mul_zero]
    have hz4 : ∀ x, x ∉ S → g x * u x = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (husupp h), mul_zero]
    have hz5 : ∀ x, x ∉ S → ⟪W x, gradient ψ x⟫ - ⟪W x, gradient u x⟫ = 0 := fun x hx => by
      rw [hz1 x hx, hz2 x hx, sub_zero]
    have hz6 : ∀ x, x ∉ S → g x * ψ x - g x * u x = 0 := fun x hx => by
      rw [hz3 x hx, hz4 x hx, sub_zero]
    -- continuity on the ball
    have hgψc : ContinuousOn (gradient ψ) (Metric.ball x₀ r) :=
      (continuous_gradient hψ).continuousOn
    have hguc : ContinuousOn (gradient u) (Metric.ball x₀ r) :=
      (continuous_gradient (huinf.of_le (by simp))).continuousOn
    have hc1 : ContinuousOn (fun x => ⟪W x, gradient ψ x⟫) (Metric.ball x₀ r) := hW.inner hgψc
    have hc2 : ContinuousOn (fun x => ⟪W x, gradient u x⟫) (Metric.ball x₀ r) := hW.inner hguc
    have hc3 : ContinuousOn (fun x => g x * ψ x) (Metric.ball x₀ r) :=
      hg.mul hψ.continuous.continuousOn
    have hc4 : ContinuousOn (fun x => g x * u x) (Metric.ball x₀ r) :=
      hg.mul huinf.continuous.continuousOn
    have hi1 := hint _ hc1 hz1
    have hi2 := hint _ hc2 hz2
    have hi3 := hint _ hc3 hz3
    have hi4 := hint _ hc4 hz4
    -- the two error terms
    have hA : ‖(∫ x, ⟪W x, gradient ψ x⟫) - ∫ x, ⟪W x, gradient u x⟫‖ ≤
        CW * e * volume.real S := by
      rw [← integral_sub hi1 hi2, ← setIntegral_eq_integral_of_forall_compl_eq_zero hz5]
      refine norm_setIntegral_le_of_norm_le_const hSfin fun x hx => ?_
      have hbd : ⟪W x, gradient ψ x⟫ - ⟪W x, gradient u x⟫ =
          ⟪W x, gradient ψ x - gradient u x⟫ := by rw [inner_sub_right]
      rw [hbd, Real.norm_eq_abs]
      calc |⟪W x, gradient ψ x - gradient u x⟫|
          ≤ ‖W x‖ * ‖gradient ψ x - gradient u x‖ := abs_real_inner_le_norm _ _
        _ ≤ CW * e := by
            refine mul_le_mul (hCW x hx) ?_ (norm_nonneg _) hCW0
            rw [norm_sub_rev]
            exact hclose2 x
    have hB : ‖(∫ x, g x * ψ x) - ∫ x, g x * u x‖ ≤ Cg * e * volume.real S := by
      rw [← integral_sub hi3 hi4, ← setIntegral_eq_integral_of_forall_compl_eq_zero hz6]
      refine norm_setIntegral_le_of_norm_le_const hSfin fun x hx => ?_
      have hbd : g x * ψ x - g x * u x = g x * (ψ x - u x) := by ring
      rw [hbd, norm_mul]
      refine mul_le_mul (hCg x hx) ?_ (norm_nonneg _) hCg0
      rw [norm_sub_rev]
      exact hclose1 x
    -- conclusion
    have hsplit : (∫ x, ⟪W x, gradient ψ x⟫) - ∫ x, g x * ψ x =
        ((∫ x, ⟪W x, gradient ψ x⟫) - ∫ x, ⟪W x, gradient u x⟫) -
          ((∫ x, g x * ψ x) - ∫ x, g x * u x) := by
      rw [heq]; ring
    rw [hsplit]
    have htri := norm_sub_le ((∫ x, ⟪W x, gradient ψ x⟫) - ∫ x, ⟪W x, gradient u x⟫)
      ((∫ x, g x * ψ x) - ∫ x, g x * u x)
    have hKne : K ≠ 0 := hK0.ne'
    have hKe : K * e = ε := by
      rw [hedef]
      field_simp <;> ring
    have hexp : CW * e * volume.real S + Cg * e * volume.real S + e = ε := by
      rw [← hKe, hKdef]; ring
    linarith
  -- `‖X - Y‖ ≤ ε` for every `ε > 0` forces `X = Y`.
  have hzero : (∫ x, ⟪W x, gradient ψ x⟫) - ∫ x, g x * ψ x = 0 := by
    by_contra hne
    have hpos : 0 < ‖(∫ x, ⟪W x, gradient ψ x⟫) - ∫ x, g x * ψ x‖ := norm_pos_iff.2 hne
    have hhalf := key _ (half_pos hpos)
    linarith
  exact sub_eq_zero.mp hzero

/-! ### A translation-invariant smooth cutoff -/

/-- **A smooth cutoff with a centre-independent gradient bound.**  For `0 < a < b` there is a
constant `Cη = Cη(a, b, d)` such that every centre `x₀` carries a smooth cutoff `η` with
`0 ≤ η ≤ 1`, `η ≡ 1` on `B̄(x₀, a)`, `tsupport η ⊆ B̄(x₀, b)` and `‖∇η‖ ≤ Cη`.  The point is the
uniformity in `x₀`, obtained by translating one fixed `ContDiffBump`. -/
theorem exists_uniform_cutoff {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x₀ : Euc d, ∃ η : Euc d → ℝ, ContDiff ℝ ∞ η ∧
      (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧ (∀ x ∈ Metric.closedBall x₀ a, η x = 1) ∧
      tsupport η ⊆ Metric.closedBall x₀ b ∧ ∀ x, ‖gradient η x‖ ≤ Cη := by
  obtain ⟨φ, hφdef⟩ : ∃ φ : ContDiffBump (0 : Euc d), φ = ⟨a, b, ha, hab⟩ := ⟨_, rfl⟩
  have hφIn : φ.rIn = a := by rw [hφdef]
  have hφOut : φ.rOut = b := by rw [hφdef]
  have hφinf : ContDiff ℝ ∞ (φ : Euc d → ℝ) := φ.contDiff
  have hφ1 : ContDiff ℝ 1 (φ : Euc d → ℝ) := hφinf.of_le (by simp)
  have hsupp0 : tsupport (φ : Euc d → ℝ) ⊆ Metric.closedBall (0 : Euc d) b := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    rw [φ.support_eq, hφOut]
    exact Metric.ball_subset_closedBall
  obtain ⟨Cη, hCη0, hCη⟩ := exists_bound_of_zero_outside'
    (isCompact_closedBall (0 : Euc d) b) (f := gradient (φ : Euc d → ℝ))
    (continuous_gradient hφ1).continuousOn
    (fun x hx => gradient_eq_zero_of_notMem_tsupport fun h => hx (hsupp0 h))
  refine ⟨Cη, hCη0, fun x₀ => ⟨fun x => φ (x - x₀), ?_, fun x => φ.nonneg, fun x => φ.le_one,
    ?_, ?_, ?_⟩⟩
  · have hsub : ContDiff ℝ ∞ fun x : Euc d => x - x₀ := contDiff_id.sub contDiff_const
    exact hφinf.comp hsub
  · intro x hx
    show (φ : Euc d → ℝ) (x - x₀) = 1
    refine φ.one_of_mem_closedBall ?_
    rw [hφIn, Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact Metric.mem_closedBall.1 hx
  · refine closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    have hx0 : (φ : Euc d → ℝ) (x - x₀) ≠ 0 := hx
    have hmem : x - x₀ ∈ Function.support (φ : Euc d → ℝ) := hx0
    rw [φ.support_eq, hφOut, Metric.mem_ball, dist_zero_right] at hmem
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hmem.le
  · intro x
    rw [gradient_comp_sub_const (hφ1.differentiable one_ne_zero) x₀ x]
    exact hCη _


/-! ### The Caccioppoli energy estimate -/

/-- **Young's inequality** in the form used to absorb the Caccioppoli cross term:
`2 a b ≤ (μ/2) a² + (2/μ) b²`. -/
theorem two_mul_mul_le_of_pos {μ : ℝ} (hμ : 0 < μ) (a b : ℝ) :
    2 * a * b ≤ μ / 2 * a ^ 2 + 2 / μ * b ^ 2 := by
  have hμne : μ ≠ 0 := hμ.ne'
  have hkey : 0 ≤ μ / 2 * (a - 2 / μ * b) ^ 2 := by positivity
  have hexp : μ / 2 * (a - 2 / μ * b) ^ 2 = μ / 2 * a ^ 2 - 2 * a * b + 2 / μ * b ^ 2 := by
    field_simp <;> ring
  rw [hexp] at hkey
  linarith

/-- **The interior Caccioppoli energy estimate for `div(A ∇w) = g`, uniform over the data**
(Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 8.32,
step (a); the missing classical input of `schauder_interior_gradient_bound`).  For `μ > 0`, `Λ`
and `R > 0` there is a single constant `E` such that every `C¹` weak solution of `div(A ∇w) = g`
on `B(x₀, 2R)` with `A` continuous and uniformly elliptic (constant `μ`), `‖A‖ ≤ Λ`, `|g| ≤ Λ`
and `|w| ≤ Λ` satisfies `∫_{B̄(x₀, 3R/2)} ‖∇w‖² ≤ E`.

Proof: test the equation with `ψ = η² w`, where `η` is the cutoff of `exists_uniform_cutoff`
(`η ≡ 1` on `B̄(x₀, 3R/2)`, supported in `B̄(x₀, 7R/4)`, `‖∇η‖ ≤ Cη` with `Cη` *independent of
`x₀`*).  Since `w` is only `C¹`, admissibility of `ψ` is exactly the mollification lemma
`integral_inner_eq_of_contDiff_one`.  Expanding,
`⟪A ∇w, ∇ψ⟫ = η² ⟪A ∇w, ∇w⟫ + 2 η w ⟪A ∇w, ∇η⟫`; ellipticity bounds the first term below by
`μ η² ‖∇w‖²`, and Young's inequality (`two_mul_mul_le_of_pos`) with `a = η ‖∇w‖`, `b = Λ² Cη`
absorbs the second into it. -/
theorem exists_linear_energy_bound (d : ℕ) {μ Λ R : ℝ} (hμ : 0 < μ) (hR : 0 < R) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      ContinuousOn A (Metric.ball x₀ (2 * R)) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      (∫ x in Metric.closedBall x₀ (3 * R / 2), ‖gradient w x‖ ^ 2) ≤ E := by
  have hμne : μ ≠ 0 := hμ.ne'
  obtain ⟨Cη, hCη0, hcut⟩ := exists_uniform_cutoff (d := d) (a := 3 * R / 2) (b := 7 * R / 4)
    (by linarith) (by linarith)
  obtain ⟨V₀, hV₀def⟩ : ∃ V₀ : ℝ,
      V₀ = (7 * R / 4) ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀def]
    exact mul_nonneg (pow_nonneg (by linarith) d) volume_real_closedBall_pos.le
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 2 / μ * (max Λ 0 * max Λ 0 * Cη) ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    have h1 : (0 : ℝ) ≤ 2 / μ := by positivity
    exact mul_nonneg h1 (sq_nonneg _)
  refine ⟨2 / μ * ((max Λ 0 ^ 2 + c) * V₀), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 / μ := by positivity
    exact mul_nonneg h1 (mul_nonneg (by positivity) hV₀0)
  intro x₀ A g w hAc hell hAbd hgc hgbd hw hwbd hweak
  -- Geometry of the two balls.
  have hTV : Metric.closedBall x₀ (7 * R / 4) ⊆ Metric.ball x₀ (2 * R) :=
    Metric.closedBall_subset_ball (by linarith)
  have hTcpt : IsCompact (Metric.closedBall x₀ (7 * R / 4)) := isCompact_closedBall _ _
  have hTfin : volume (Metric.closedBall x₀ (7 * R / 4)) < ⊤ := measure_closedBall_lt_top
  have hTvol : volume.real (Metric.closedBall x₀ (7 * R / 4)) = V₀ := by
    rw [hV₀def, volume_real_closedBall x₀ (by linarith : (0 : ℝ) ≤ 7 * R / 4)]
  have hx₀V : x₀ ∈ Metric.ball x₀ (2 * R) := Metric.mem_ball_self (by linarith)
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg (g x₀)) (hgbd x₀ hx₀V)
  have hΛmax : max Λ 0 = Λ := max_eq_left hΛ0
  -- The cutoff.
  obtain ⟨η, hηinf, hη0, hη1, hηone, hηT, hηgrad⟩ := hcut x₀
  have hη1' : ContDiff ℝ 1 η := hηinf.of_le (by simp)
  have hηzero : ∀ x, x ∉ Metric.closedBall x₀ (7 * R / 4) → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hηT h)
  -- Continuity of the data.
  have hgradw : ContinuousOn (gradient w) (Metric.ball x₀ (2 * R)) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hw.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
  have hW : ContinuousOn (fun x => A x (gradient w x)) (Metric.ball x₀ (2 * R)) :=
    hAc.clm_apply hgradw
  have hwdiff : ∀ x ∈ Metric.ball x₀ (2 * R), DifferentiableAt ℝ w x := fun x hx =>
    (hw.differentiableOn one_ne_zero).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  have hηdiff : ∀ x : Euc d, DifferentiableAt ℝ η x := fun x => (hη1'.differentiable one_ne_zero) x
  -- The test function `Ψ = η² w`.
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Euc d → ℝ, Ψ = fun x => η x * (η x * w x) := ⟨_, rfl⟩
  have hΨsupp : tsupport Ψ ⊆ Metric.closedBall x₀ (7 * R / 4) := by
    refine le_trans (closure_mono ?_) hηT
    intro x hx
    have hx' : Ψ x ≠ 0 := hx
    intro h0
    refine hx' ?_
    rw [hΨdef]
    simp [h0]
  have hΨ1 : ContDiff ℝ 1 Ψ := by
    refine contDiff_one_of_contDiffOn Metric.isOpen_ball Metric.isClosed_closedBall hTV ?_ hΨsupp
    rw [hΨdef]
    exact hη1'.contDiffOn.mul (hη1'.contDiffOn.mul hw)
  have hΨcs : HasCompactSupport Ψ :=
    HasCompactSupport.intro hTcpt fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hΨsupp h)
  have hgradΨ : ∀ x ∈ Metric.ball x₀ (2 * R), gradient Ψ x =
      (η x * η x) • gradient w x + (2 * (η x * w x)) • gradient η x := by
    intro x hx
    have h1 : gradient (fun y => η y * w y) x = η x • gradient w x + w x • gradient η x :=
      gradient_mul_apply (hηdiff x) (hwdiff x hx)
    have h2 : DifferentiableAt ℝ (fun y => η y * w y) x := (hηdiff x).mul (hwdiff x hx)
    have h3 : gradient (fun y => η y * (η y * w y)) x =
        η x • gradient (fun y => η y * w y) x + (η x * w x) • gradient η x :=
      gradient_mul_apply (hηdiff x) h2
    rw [hΨdef, h3, h1]
    module
  -- The three integrands.
  obtain ⟨Q, hQdef⟩ : ∃ Q : Euc d → ℝ,
      Q = fun x => (η x * η x) * ⟪A x (gradient w x), gradient w x⟫ := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Euc d → ℝ,
      P = fun x => 2 * (η x * w x) * ⟪A x (gradient w x), gradient η x⟫ := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ∫ x, (η x * η x) * ‖gradient w x‖ ^ 2 := ⟨_, rfl⟩
  have hQ0 : ∀ x, x ∉ Metric.closedBall x₀ (7 * R / 4) → Q x = 0 := fun x hx => by
    simp [hQdef, hηzero x hx]
  have hP0 : ∀ x, x ∉ Metric.closedBall x₀ (7 * R / 4) → P x = 0 := fun x hx => by
    simp [hPdef, hηzero x hx]
  have hG0 : ∀ x, x ∉ Metric.closedBall x₀ (7 * R / 4) → g x * Ψ x = 0 := fun x hx => by
    simp [hΨdef, hηzero x hx]
  have hE0 : ∀ x, x ∉ Metric.closedBall x₀ (7 * R / 4) →
      (η x * η x) * ‖gradient w x‖ ^ 2 = 0 := fun x hx => by
    simp [hηzero x hx]
  -- The pointwise expansion of the weak integrand.
  have hpt : ∀ x, ⟪A x (gradient w x), gradient Ψ x⟫ = Q x + P x := by
    intro x
    by_cases hx : x ∈ Metric.ball x₀ (2 * R)
    · rw [hgradΨ x hx, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      simp only [hQdef, hPdef]
    · have hxT : x ∉ Metric.closedBall x₀ (7 * R / 4) := fun h => hx (hTV h)
      have hΨ0 : gradient Ψ x = 0 :=
        gradient_eq_zero_of_notMem_tsupport fun h => hxT (hΨsupp h)
      rw [hΨ0, inner_zero_right, hQ0 x hxT, hP0 x hxT, add_zero]
  -- Integrability of the three integrands.
  have hQc : ContinuousOn Q (Metric.ball x₀ (2 * R)) := by
    rw [hQdef]
    exact (hη1'.continuous.continuousOn.mul hη1'.continuous.continuousOn).mul (hW.inner hgradw)
  have hPc : ContinuousOn P (Metric.ball x₀ (2 * R)) := by
    rw [hPdef]
    refine ContinuousOn.mul ?_ (hW.inner (continuous_gradient hη1').continuousOn)
    exact continuousOn_const.mul (hη1'.continuous.continuousOn.mul hw.continuousOn)
  have hGc : ContinuousOn (fun x => g x * Ψ x) (Metric.ball x₀ (2 * R)) :=
    hgc.mul hΨ1.continuous.continuousOn
  have hEc : ContinuousOn (fun x => (η x * η x) * ‖gradient w x‖ ^ 2)
      (Metric.ball x₀ (2 * R)) :=
    (hη1'.continuous.continuousOn.mul hη1'.continuous.continuousOn).mul (hgradw.norm.pow 2)
  have hQi : Integrable Q :=
    integrable_of_continuousOn_zero_outside Metric.isOpen_ball hTcpt hTV hQc hQ0
  have hPi : Integrable P :=
    integrable_of_continuousOn_zero_outside Metric.isOpen_ball hTcpt hTV hPc hP0
  have hGi : Integrable fun x => g x * Ψ x :=
    integrable_of_continuousOn_zero_outside Metric.isOpen_ball hTcpt hTV hGc hG0
  have hEi : Integrable fun x => (η x * η x) * ‖gradient w x‖ ^ 2 :=
    integrable_of_continuousOn_zero_outside Metric.isOpen_ball hTcpt hTV hEc hE0
  -- The weak identity for the `C¹` test function `Ψ`.
  have hweakΨ : ∫ x, ⟪A x (gradient w x), gradient Ψ x⟫ = ∫ x, g x * Ψ x :=
    integral_inner_eq_of_contDiff_one (x₀ := x₀) (r := 2 * R) (s := 7 * R / 4)
      (by linarith) (by linarith) hW hgc hweak hΨ1 hΨcs hΨsupp
  have hsum : (∫ x, Q x) + ∫ x, P x = ∫ x, g x * Ψ x := by
    rw [← integral_add hQi hPi, ← hweakΨ]
    exact integral_congr_ae (Eventually.of_forall fun x => (hpt x).symm)
  -- Ellipticity: a lower bound for `∫ Q`.
  have hQlow : μ * N ≤ ∫ x, Q x := by
    rw [hNdef, ← integral_const_mul]
    refine integral_mono (hEi.const_mul μ) hQi fun x => ?_
    by_cases hx : x ∈ Metric.ball x₀ (2 * R)
    · have h1 : μ * ‖gradient w x‖ ^ 2 ≤ ⟪A x (gradient w x), gradient w x⟫ :=
        hell x hx _
      have h2 : 0 ≤ η x * η x := mul_nonneg (hη0 x) (hη0 x)
      simp only [hQdef]
      calc μ * ((η x * η x) * ‖gradient w x‖ ^ 2)
          = (η x * η x) * (μ * ‖gradient w x‖ ^ 2) := by ring
        _ ≤ (η x * η x) * ⟪A x (gradient w x), gradient w x⟫ :=
            mul_le_mul_of_nonneg_left h1 h2
    · have hxT : x ∉ Metric.closedBall x₀ (7 * R / 4) := fun h => hx (hTV h)
      rw [hQ0 x hxT, hηzero x hxT]
      simp
  -- The zeroth-order term.
  have hGbd : ∫ x, g x * Ψ x ≤ Λ ^ 2 * V₀ := by
    have hnorm : ‖∫ x, g x * Ψ x‖ ≤ Λ ^ 2 * V₀ := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hG0, ← hTvol]
      refine norm_setIntegral_le_of_norm_le_const hTfin fun x hx => ?_
      have hxV : x ∈ Metric.ball x₀ (2 * R) := hTV hx
      have h1 : |g x| ≤ Λ := hgbd x hxV
      have h2 : |w x| ≤ Λ := hwbd x hxV
      have h3 : |η x| ≤ 1 := abs_le.2 ⟨by linarith [hη0 x], hη1 x⟩
      have h4 : (0 : ℝ) ≤ |η x| := abs_nonneg _
      have h5 : (0 : ℝ) ≤ |w x| := abs_nonneg _
      have h6 : (0 : ℝ) ≤ |g x| := abs_nonneg _
      simp only [hΨdef]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      have ha : |η x| * |w x| ≤ 1 * Λ := mul_le_mul h3 h2 h5 zero_le_one
      have hb1 : |η x| * (|η x| * |w x|) ≤ 1 * (1 * Λ) :=
        mul_le_mul h3 ha (mul_nonneg h4 h5) zero_le_one
      have hb2 : |g x| * (|η x| * (|η x| * |w x|)) ≤ Λ * (1 * (1 * Λ)) :=
        mul_le_mul h1 hb1 (mul_nonneg h4 (mul_nonneg h4 h5)) hΛ0
      calc |g x| * (|η x| * (|η x| * |w x|)) ≤ Λ * (1 * (1 * Λ)) := hb2
        _ = Λ ^ 2 := by ring
    rw [Real.norm_eq_abs] at hnorm
    exact le_trans (le_abs_self _) hnorm
  -- The cross term, absorbed by Young's inequality.
  have hPbd : ∀ x, |P x| ≤ μ / 2 * ((η x * η x) * ‖gradient w x‖ ^ 2) +
      (Metric.closedBall x₀ (7 * R / 4)).indicator (fun _ => c) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall x₀ (7 * R / 4)
    · have hxV : x ∈ Metric.ball x₀ (2 * R) := hTV hx
      have hA1 : ‖A x‖ ≤ Λ := hAbd x hxV
      have h2 : |w x| ≤ Λ := hwbd x hxV
      have hAw : ‖A x (gradient w x)‖ ≤ Λ * ‖gradient w x‖ :=
        le_trans ((A x).le_opNorm _) (mul_le_mul_of_nonneg_right hA1 (norm_nonneg _))
      have hAw0 : (0 : ℝ) ≤ Λ * ‖gradient w x‖ := le_trans (norm_nonneg _) hAw
      have hinner : |⟪A x (gradient w x), gradient η x⟫| ≤ Λ * ‖gradient w x‖ * Cη :=
        le_trans (abs_real_inner_le_norm _ _)
          (mul_le_mul hAw (hηgrad x) (norm_nonneg _) hAw0)
      have hstep : |P x| ≤ 2 * (η x * ‖gradient w x‖) * (Λ * Λ * Cη) := by
        have hexp : |2 * (η x * w x) * ⟪A x (gradient w x), gradient η x⟫| =
            2 * (η x * |w x|) * |⟪A x (gradient w x), gradient η x⟫| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hη0 x),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [hPdef]
        rw [hexp]
        have hfac : (0 : ℝ) ≤ 2 * (η x * Λ) :=
          mul_nonneg (by norm_num) (mul_nonneg (hη0 x) hΛ0)
        have hle1 : 2 * (η x * |w x|) ≤ 2 * (η x * Λ) := by
          have := mul_le_mul_of_nonneg_left h2 (hη0 x)
          linarith
        calc 2 * (η x * |w x|) * |⟪A x (gradient w x), gradient η x⟫|
            ≤ 2 * (η x * Λ) * (Λ * ‖gradient w x‖ * Cη) :=
              mul_le_mul hle1 hinner (abs_nonneg _) hfac
          _ = 2 * (η x * ‖gradient w x‖) * (Λ * Λ * Cη) := by ring
      have hy := two_mul_mul_le_of_pos hμ (η x * ‖gradient w x‖) (Λ * Λ * Cη)
      have hsq : (η x * ‖gradient w x‖) ^ 2 = (η x * η x) * ‖gradient w x‖ ^ 2 := by ring
      have hcv : 2 / μ * (Λ * Λ * Cη) ^ 2 = c := by rw [hcdef, hΛmax]
      rw [hsq, hcv] at hy
      rw [indicator_of_mem hx]
      linarith
    · rw [hP0 x hx, indicator_of_notMem hx, hηzero x hx]
      simp
  have hPint : ∫ x, |P x| ≤ μ / 2 * N + c * V₀ := by
    have hind : Integrable ((Metric.closedBall x₀ (7 * R / 4)).indicator fun _ : Euc d => c) :=
      (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hTfin.ne)
    have hmono : ∫ x, |P x| ≤ ∫ x, (μ / 2 * ((η x * η x) * ‖gradient w x‖ ^ 2) +
        (Metric.closedBall x₀ (7 * R / 4)).indicator (fun _ => c) x) :=
      integral_mono hPi.abs ((hEi.const_mul (μ / 2)).add hind) hPbd
    rw [integral_add (hEi.const_mul (μ / 2)) hind, integral_const_mul,
      integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, hTvol,
      ← hNdef] at hmono
    linarith
  have hPneg : -(∫ x, P x) ≤ μ / 2 * N + c * V₀ := by
    have h1 : ‖∫ x, P x‖ ≤ ∫ x, ‖P x‖ := norm_integral_le_integral_norm P
    have h2 : (∫ x, ‖P x‖) = ∫ x, |P x| :=
      integral_congr_ae (Eventually.of_forall fun x => Real.norm_eq_abs (P x))
    have h3 : -(∫ x, P x) ≤ |∫ x, P x| := by
      rw [← abs_neg]
      exact le_abs_self _
    rw [h2, Real.norm_eq_abs] at h1
    linarith
  -- Combining the three estimates.
  have hkey : μ / 2 * N ≤ (Λ ^ 2 + c) * V₀ := by
    have hexp : (Λ ^ 2 + c) * V₀ = Λ ^ 2 * V₀ + c * V₀ := by ring
    rw [hexp]
    linarith [hQlow, hsum, hGbd, hPneg]
  have hNle : N ≤ 2 / μ * ((max Λ 0 ^ 2 + c) * V₀) := by
    rw [hΛmax]
    have h2 : (0 : ℝ) ≤ 2 / μ := by positivity
    calc N = 2 / μ * (μ / 2 * N) := by field_simp <;> ring
      _ ≤ 2 / μ * ((Λ ^ 2 + c) * V₀) := mul_le_mul_of_nonneg_left hkey h2
  -- Restricting to the smaller ball, where `η = 1`.
  refine le_trans ?_ hNle
  have hrestrict : (∫ x in Metric.closedBall x₀ (3 * R / 2), ‖gradient w x‖ ^ 2) =
      ∫ x in Metric.closedBall x₀ (3 * R / 2), (η x * η x) * ‖gradient w x‖ ^ 2 := by
    refine setIntegral_congr_fun measurableSet_closedBall fun x hx => ?_
    rw [hηone x hx]
    ring
  rw [hrestrict, hNdef, ← integral_indicator measurableSet_closedBall]
  refine integral_mono ((integrable_indicator_iff measurableSet_closedBall).2
    hEi.integrableOn) hEi fun x => ?_
  by_cases hx : x ∈ Metric.closedBall x₀ (3 * R / 2)
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    exact mul_nonneg (mul_nonneg (hη0 x) (hη0 x)) (sq_nonneg _)

end Komlos.Literature
