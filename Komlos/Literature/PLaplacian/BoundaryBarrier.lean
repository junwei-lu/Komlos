import Komlos.Literature.PLaplacian.HolderExcessAux

/-!
# The weak comparison principle and the linear boundary barrier

The boundary half of Mosconi–Riey–Squassina 2024, Proposition 4.5 (paper Appendix A,
*Eigenfunction inputs*: "`u_i` has bounded gradient and zero boundary value"), for the degenerate
anisotropic `p`-Laplacian `-div a(∇u) = λ u^{p-1}` with `a = flux p F` on a **bounded open convex**
set `K`.

Everything here is proved. The consumer in `Komlos.Literature.PLaplacian.Regularity` is
`boundary_holder_barrier` — the barrier bound `φ ≤ C (ℓ x₀ − ℓ x)^γ` near a boundary point, with
the *linear* exponent `γ = 1` (Lieberman's convex-domain barrier).

## The route

1. **Strict monotonicity of the flux** (`IsSmoothStrictNorm.inner_flux_sub_pos`):
   `⟪a(ξ) − a(ζ), ξ − ζ⟫ > 0` for `ξ ≠ ζ`. Away from the origin this is the mean value formula
   `a(ξ) − a(ζ) = (∫₀¹ Da(ζ + t(ξ−ζ)) dt)(ξ − ζ)` (`flux_sub_eq_integral_fderiv`) together with the
   uniform ellipticity of `Da` on the (compact convex) segment (`exists_fderiv_flux_bounds`,
   ultimately `hessian_sq_pos`); the degenerate configurations (`ζ = 0`, `ξ = 0`, or `0` interior
   to the segment, i.e. `ζ = −μ ξ`) are handled by Euler's identity `⟪a(ξ), ξ⟫ = F(ξ)^p` and the
   homogeneity `a(s ξ) = s^{p−1} a(ξ)`, `a(−ξ) = −a(ξ)`.
2. **The positive part in `W₀^{1,p}`** (`memW0_posPart`): `f ↦ f⁺` maps `W₀^{1,p}(K)` to itself with
   `∇(f⁺) = 1_{f > 0} ∇f`. Proof: the `C¹` primitives `G_ε(t) = ∫₀ᵗ (s/ε ∧ 1)⁺ ds` of the truncated
   ramps satisfy the hypotheses of the chain rule `memW0_comp`, and `G_ε(f) → f⁺`,
   `G_ε'(f) ∇f → 1_{f>0} ∇f` in `L^p` (dominated convergence), so `HasWeakGradient.of_tendsto`
   applies.
3. **The weak comparison principle** (`ae_le_of_comparison`, with the test function supplied by
   `exists_posPart_test`): testing the difference of the two weak equations with
   `ψ = (u − Ψ)⁺ ∈ W₀^{1,p}(K)` and using (1) forces `∇ψ = 0` a.e., hence `ψ = 0` a.e. by the
   Dirichlet–Poincaré inequality (`exists_poincare_const`), i.e. `u ≤ Ψ` a.e.
4. **The linear barrier** (`exists_barrier_data`, `exists_linear_barrier`): on the supporting
   half-space `{ℓ < ℓ x₀} ⊇ K` the smooth function `Φ(x) = A (1 − e^{ℓ x − ℓ x₀})` has
   `a(∇Φ) = c(x) • a(−n)` with `c(x) = A^{p−1} e^{(p−1)(ℓ x − ℓ x₀)}` (`n` the Riesz vector of
   `ℓ`), so `−div a(∇Φ) = (p−1) F(n)^p c > 0`, which for `A` large dominates `λ ‖u‖_∞^{p−1}` on the
   bounded set `K`. Its positive part, cut off far from `K`, is the supersolution `Ψ` of (3), and
   the comparison gives `u ≤ Φ ≤ A (ℓ x₀ − ℓ ·)` a.e. on `K`. The integration by parts against
   `ψ ∈ W₀^{1,p}(K)` is `integral_inner_weakGrad_mul_smooth`, which tests the weak-gradient identity
   of `ψ` with the compactly supported smooth function `θ c`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Homogeneity of the flux -/

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- **Homogeneity of `DF`**: `c · DF(c ξ)[v] = |c| · DF(ξ)[v]` for `c ≠ 0` and `ξ ≠ 0`. Along the
line `t ↦ c ξ + t v = c (ξ + (t/c) v)` the `1`-homogeneity `F(c y) = |c| F(y)` turns the derivative
of `F` at `c ξ` into `|c|/c` times the derivative at `ξ`. -/
theorem mul_fderiv_smul_apply {c : ℝ} (hc : c ≠ 0) {ξ : Euc d} (hξ : ξ ≠ 0) (v : Euc d) :
    c * fderiv ℝ F (c • ξ) v = |c| * fderiv ℝ F ξ v := by
  have hcξ : c • ξ ≠ 0 := smul_ne_zero hc hξ
  have hF2cξ : ContDiffAt ℝ 2 F (c • ξ) := (hF.contDiffAt hcξ).of_le (WithTop.coe_le_coe.2 le_top)
  have hFd : HasFDerivAt F (fderiv ℝ F ξ) ξ :=
    ((hF.contDiffAt hξ).differentiableAt (by simp)).hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => F (c • ξ + t • v)) (fderiv ℝ F (c • ξ) v) 0 := by
    simpa using (eventually_hasDerivAt_line hF2cξ v).self_of_nhds
  have hline : HasDerivAt (fun t : ℝ => ξ + (t / c) • v) ((1 / c) • v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t / c) • v) ((1 / c) • v) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).div_const c).smul_const v
    simpa using h1.const_add ξ
  have h0 : HasDerivAt (fun t : ℝ => F (ξ + (t / c) • v)) (fderiv ℝ F ξ ((1 / c) • v)) 0 :=
    hFd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hcomp : HasDerivAt (fun t : ℝ => |c| * F (ξ + (t / c) • v))
      (|c| * fderiv ℝ F ξ ((1 / c) • v)) 0 := h0.const_mul _
  have heq : (fun t : ℝ => F (c • ξ + t • v)) = fun t : ℝ => |c| * F (ξ + (t / c) • v) := by
    funext t
    have hct : c * (t / c) = t := by field_simp
    rw [← hF.homog c (ξ + (t / c) • v), smul_add, smul_smul, hct]
  rw [heq] at hg
  have hkey := hg.unique hcomp
  have hsm : fderiv ℝ F ξ ((1 / c) • v) = (1 / c) * fderiv ℝ F ξ v := by
    rw [map_smul, smul_eq_mul]
  rw [hkey, hsm]
  have hc1 : c * (1 / c) = 1 := by field_simp
  calc c * (|c| * (1 / c * fderiv ℝ F ξ v))
      = |c| * fderiv ℝ F ξ v * (c * (1 / c)) := by ring
    _ = |c| * fderiv ℝ F ξ v := by rw [hc1, mul_one]

/-- **`∇F` is `0`-homogeneous**: `∇F(c ξ) = ∇F(ξ)` for `c > 0`. -/
theorem gradient_smul_of_pos {c : ℝ} (hc : 0 < c) {ξ : Euc d} (hξ : ξ ≠ 0) :
    gradient F (c • ξ) = gradient F ξ := by
  refine ext_inner_right ℝ fun v => ?_
  have h := hF.mul_fderiv_smul_apply hc.ne' hξ v
  rw [abs_of_pos hc] at h
  simp only [inner_gradient_left]
  exact mul_left_cancel₀ hc.ne' h

/-- **`∇F` is odd**: `∇F(−ξ) = −∇F(ξ)` for `ξ ≠ 0` (from `F(−y) = F(y)`). -/
theorem gradient_neg {ξ : Euc d} (hξ : ξ ≠ 0) : gradient F (-ξ) = -gradient F ξ := by
  refine ext_inner_right ℝ fun v => ?_
  have h := hF.mul_fderiv_smul_apply (c := -1) (by norm_num) hξ v
  rw [neg_one_smul, abs_neg, abs_one, one_mul] at h
  simp only [inner_neg_left, inner_gradient_left]
  linarith

/-- **Positive homogeneity of the flux**: `a(s ξ) = s^{p−1} a(ξ)` for `s > 0`. -/
theorem flux_smul_of_pos {p : ℝ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) (ξ : Euc d) :
    flux p F (s • ξ) = s ^ (p - 1) • flux p F ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [flux, hF.map_zero, Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
  rw [flux, flux, hF.gradient_smul_of_pos hs hξ, hF.homog, abs_of_pos hs,
    Real.mul_rpow hs.le (hF.nonneg ξ), ← smul_smul]

/-- **The flux is odd**: `a(−ξ) = −a(ξ)`. -/
theorem flux_neg {p : ℝ} (hp : 1 < p) (ξ : Euc d) : flux p F (-ξ) = -flux p F ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [flux_zero hp hF]
  rw [flux, flux, hF.even, hF.gradient_neg hξ, smul_neg]

/-! ### Strict monotonicity of the flux -/

/-- **Strict monotonicity of the flux** (paper (A.ellipticity)): `⟪a(ξ) − a(ζ), ξ − ζ⟫ > 0` for
`ξ ≠ ζ`. If the segment `[ζ, ξ]` avoids the origin this is the mean value formula
`flux_sub_eq_integral_fderiv` plus the uniform ellipticity `exists_fderiv_flux_bounds` of
`A = Da` on that (compact, convex) segment. Otherwise either an endpoint is `0`, and Euler's
identity `⟪a(ξ), ξ⟫ = F(ξ)^p > 0` applies, or the two vectors point in opposite directions,
`ζ = −μ ξ` with `μ > 0`, and `⟪a(ξ) − a(ζ), ξ − ζ⟫ = (1 + μ^{p−1})(1 + μ) F(ξ)^p > 0` by the
homogeneity `flux_smul_of_pos` and oddness `flux_neg` of `a`. -/
theorem inner_flux_sub_pos {p : ℝ} (hp : 1 < p) {ξ ζ : Euc d} (hne : ξ ≠ ζ) :
    0 < ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ := by
  have hself : ∀ η : Euc d, η ≠ 0 → 0 < ⟪flux p F η, η⟫ := fun η hη => by
    rw [hF.inner_flux_self_eq_rpow hp]
    exact Real.rpow_pos_of_pos (hF.pos η hη) p
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · have hξ0 : ξ ≠ 0 := hne
    simpa [flux_zero hp hF] using hself ξ hξ0
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · have h := hself ζ hζ0
    have e : ⟪flux p F 0 - flux p F ζ, (0 : Euc d) - ζ⟫ = ⟪flux p F ζ, ζ⟫ := by
      rw [flux_zero hp hF, zero_sub, zero_sub, inner_neg_neg]
    rw [e]
    exact h
  by_cases h0 : (0 : Euc d) ∈ segment ℝ ζ ξ
  · -- the origin lies on the segment: `ζ = −m ξ` with `m > 0`
    obtain ⟨a, b, ha, hb, hab, hzero⟩ := h0
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hzero
      rw [zero_add] at hab
      rw [hab, one_smul] at hzero
      exact hξ0 hzero
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_smul, add_zero] at hzero
      rw [add_zero] at hab
      rw [hab, one_smul] at hzero
      exact hζ0 hzero
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = b / a := ⟨_, rfl⟩
    have hmpos : 0 < m := by rw [hm_def]; exact div_pos hbpos hapos
    have hinvm : a⁻¹ * b = m := by rw [hm_def, div_eq_inv_mul]
    have hζm : ζ = -(m • ξ) := by
      have h1 : a • ζ = -(b • ξ) := eq_neg_of_add_eq_zero_left hzero
      have h2 : ζ = a⁻¹ • (a • ζ) := by
        rw [smul_smul, inv_mul_cancel₀ hapos.ne', one_smul]
      rw [h2, h1, smul_neg, smul_smul, hinvm]
    have hflux : flux p F ζ = -(m ^ (p - 1) • flux p F ξ) := by
      rw [hζm, hF.flux_neg hp, hF.flux_smul_of_pos hp hmpos]
    have hsub : ξ - ζ = (1 + m) • ξ := by
      rw [hζm]
      module
    have hfsub : flux p F ξ - flux p F ζ = (1 + m ^ (p - 1)) • flux p F ξ := by
      rw [hflux, sub_neg_eq_add, add_smul, one_smul]
    rw [hsub, hfsub, real_inner_smul_left, real_inner_smul_right]
    have hpow : 0 < m ^ (p - 1) := Real.rpow_pos_of_pos hmpos _
    have hss := hself ξ hξ0
    exact mul_pos (by linarith) (mul_pos (by linarith) hss)
  · -- the segment avoids the origin: mean value formula plus uniform ellipticity
    have hNcv : Convex ℝ (segment ℝ ζ ξ) := convex_segment ζ ξ
    have hNc : IsCompact (segment ℝ ζ ξ) := by
      rw [← convexHull_pair]
      exact ((Set.finite_singleton ξ).insert ζ).isCompact_convexHull (𝕜 := ℝ)
    have hζN : ζ ∈ segment ℝ ζ ξ := left_mem_segment ℝ ζ ξ
    have hξN : ξ ∈ segment ℝ ζ ξ := right_mem_segment ℝ ζ ξ
    obtain ⟨μ, Λ, L, hμ0, hΛ0, hL0, hμ, hΛ, hL⟩ :=
      hF.exists_fderiv_flux_bounds hp hNc hNcv h0
    obtain ⟨hell, -, -⟩ :=
      hF.integral_fderiv_flux_bounds p hNcv h0 hμ hΛ hL hL0 hζN hξN hζN hξN
    have hmv := hF.flux_sub_eq_integral_fderiv p hNcv h0 hζN hξN
    have hpos : 0 < ‖ξ - ζ‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hne
    rw [hmv]
    exact lt_of_lt_of_le (mul_pos hμ0 (pow_pos hpos 2)) (hell (ξ - ζ))

/-- **Monotonicity of the flux**: `⟪a(ξ) − a(ζ), ξ − ζ⟫ ≥ 0`. -/
theorem inner_flux_sub_nonneg {p : ℝ} (hp : 1 < p) (ξ ζ : Euc d) :
    0 ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ := by
  rcases eq_or_ne ξ ζ with rfl | hne
  · simp
  · exact (hF.inner_flux_sub_pos hp hne).le

/-- The strict monotonicity in contrapositive form: a vanishing monotonicity pairing forces
equality of the two arguments. -/
theorem eq_of_inner_flux_sub_eq_zero {p : ℝ} (hp : 1 < p) {ξ ζ : Euc d}
    (h : ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ = 0) : ξ = ζ := by
  by_contra hne
  exact absurd h (hF.inner_flux_sub_pos hp hne).ne'

end IsSmoothStrictNorm

/-! ### From almost-everywhere to pointwise on an open set -/

/-- If `φ` and `g` are continuous on the open set `U` and `φ ≤ g` almost everywhere on `U`, then
`φ ≤ g` everywhere on `U` (a point with `φ > g` would give a ball of positive measure on which
`φ > g`). -/
theorem le_of_ae_le_on_open {U : Set (Euc d)} (hU : IsOpen U) {φ g : Euc d → ℝ}
    (hφc : ContinuousOn φ U) (hgc : ContinuousOn g U)
    (h : ∀ᵐ x ∂(volume.restrict U), φ x ≤ g x) : ∀ x ∈ U, φ x ≤ g x := by
  intro x₀ hx₀
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hUx : U ∈ 𝓝 x₀ := hU.mem_nhds hx₀
  have hc : ContinuousAt (fun y => g y - φ y) x₀ :=
    (hgc.continuousAt hUx).sub (hφc.continuousAt hUx)
  have h0 : g x₀ - φ x₀ < 0 := by linarith
  have hev : ∀ᶠ y in 𝓝 x₀, g y < φ y := by
    filter_upwards [hc.eventually (gt_mem_nhds h0)] with y hy
    linarith [hy]
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have h2 : ∀ᵐ y : Euc d, y ∈ U → φ y ≤ g y := (ae_restrict_iff' hU.measurableSet).1 h
  have hρ : 0 < min δ r := lt_min hδ hr
  have hnull : volume (Metric.ball x₀ (min δ r)) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [h2] with y hy2 hy
    have hyδ : y ∈ Metric.ball x₀ δ := Metric.ball_subset_ball (min_le_left δ r) hy
    have hyU : y ∈ U := hball (Metric.ball_subset_ball (min_le_right δ r) hy)
    exact absurd (hy2 hyU) (not_le.2 (hδball y hyδ))
  exact (Metric.measure_ball_pos volume x₀ hρ).ne' hnull

/-! ### Integrability of the flux pairing -/

/-- `⟪a(A), B⟫ ∈ L¹` for `A, B ∈ L^p` (`‖a(ξ)‖ ≤ C ‖ξ‖^{p−1}` and Young's inequality). -/
theorem integrable_inner_flux {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {A B : Euc d → Euc d} (hA : MemLp A (ENNReal.ofReal p) volume)
    (hB : MemLp B (ENNReal.ofReal p) volume) :
    Integrable fun x => ⟪flux p F (A x), B x⟫ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Ca, hCa0, hCa⟩ := hF.exists_norm_flux_le hp
  have hdom : Integrable fun x => Ca * (‖A x‖ ^ p + ‖B x‖ ^ p) :=
    ((integrable_norm_rpow_of_memLp hp0 hA).add
      (integrable_norm_rpow_of_memLp hp0 hB)).const_mul Ca
  refine hdom.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((hF.continuous_flux' hp).comp_aestronglyMeasurable hA.aestronglyMeasurable).inner
      hB.aestronglyMeasurable
  · have h1 : ‖⟪flux p F (A x), B x⟫‖ ≤ Ca * ‖A x‖ ^ (p - 1) * ‖B x‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hCa (A x)) (norm_nonneg _))
    have h2 := rpow_sub_one_mul_le_add hp.le (norm_nonneg (A x)) (norm_nonneg (B x))
    calc ‖⟪flux p F (A x), B x⟫‖ ≤ Ca * (‖A x‖ ^ (p - 1) * ‖B x‖) := by
          rw [← mul_assoc]; exact h1
      _ ≤ Ca * (‖A x‖ ^ p + ‖B x‖ ^ p) := mul_le_mul_of_nonneg_left h2 hCa0

/-! ### A `C¹` approximation of the positive part -/

/-- The truncated ramp `s ↦ (s/ε ∧ 1) ∨ 0`, the derivative of `posPartApprox ε`. -/
noncomputable def rampDeriv (ε s : ℝ) : ℝ := max 0 (min (s / ε) 1)

/-- The `C¹` approximation `G_ε(t) = ∫₀ᵗ (s/ε ∧ 1) ∨ 0 ds` of the positive part `t ↦ t ∨ 0`. -/
noncomputable def posPartApprox (ε t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, rampDeriv ε s

theorem continuous_rampDeriv (ε : ℝ) : Continuous (rampDeriv ε) := by
  have h : Continuous fun s : ℝ => s / ε := continuous_id.div_const ε
  exact continuous_const.max (h.min continuous_const)

theorem rampDeriv_nonneg (ε s : ℝ) : 0 ≤ rampDeriv ε s := le_max_left _ _

theorem rampDeriv_le_one (ε s : ℝ) : rampDeriv ε s ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem abs_rampDeriv_le_one (ε s : ℝ) : |rampDeriv ε s| ≤ 1 := by
  rw [abs_of_nonneg (rampDeriv_nonneg ε s)]
  exact rampDeriv_le_one ε s

theorem rampDeriv_of_nonpos {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ 0) : rampDeriv ε s = 0 := by
  have hinv : 0 < ε⁻¹ := inv_pos.2 hε
  have h1 : s / ε ≤ 0 := by rw [div_eq_mul_inv]; nlinarith
  exact max_eq_left (le_trans (min_le_left _ _) h1)

theorem rampDeriv_of_le {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ s) : rampDeriv ε s = 1 := by
  have h1 : 1 ≤ s / ε := (one_le_div hε).2 hs
  rw [rampDeriv, min_eq_right h1, max_eq_right zero_le_one]

theorem hasDerivAt_posPartApprox (ε t : ℝ) : HasDerivAt (posPartApprox ε) (rampDeriv ε t) t := by
  have hc := continuous_rampDeriv ε
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem deriv_posPartApprox (ε : ℝ) : deriv (posPartApprox ε) = rampDeriv ε :=
  funext fun t => (hasDerivAt_posPartApprox ε t).deriv

theorem contDiff_posPartApprox (ε : ℝ) : ContDiff ℝ 1 (posPartApprox ε) :=
  contDiff_one_iff_deriv.2
    ⟨fun t => (hasDerivAt_posPartApprox ε t).differentiableAt, by
      rw [deriv_posPartApprox]; exact continuous_rampDeriv ε⟩

theorem posPartApprox_zero (ε : ℝ) : posPartApprox ε 0 = 0 := intervalIntegral.integral_same

theorem posPartApprox_of_nonpos {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ≤ 0) :
    posPartApprox ε t = 0 := by
  have h0 : ∀ s ∈ Set.Ioc t (0 : ℝ), rampDeriv ε s = 0 := fun s hs =>
    rampDeriv_of_nonpos hε hs.2
  rw [posPartApprox, intervalIntegral.integral_of_ge ht,
    setIntegral_eq_zero_of_forall_eq_zero h0, neg_zero]

theorem posPartApprox_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ posPartApprox ε t := by
  rcases le_or_gt 0 t with ht | ht
  · exact intervalIntegral.integral_nonneg ht fun s _ => rampDeriv_nonneg ε s
  · rw [posPartApprox_of_nonpos hε ht.le]

theorem posPartApprox_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : posPartApprox ε t ≤ max t 0 := by
  rcases le_or_gt 0 t with ht | ht
  · have h1 : ∫ s in (0 : ℝ)..t, rampDeriv ε s ≤ ∫ _s in (0 : ℝ)..t, (1 : ℝ) :=
      intervalIntegral.integral_mono_on ht
        ((continuous_rampDeriv ε).intervalIntegrable _ _) intervalIntegrable_const
        fun s _ => rampDeriv_le_one ε s
    have h2 : ∫ _s in (0 : ℝ)..t, (1 : ℝ) = t := by simp
    rw [max_eq_left ht, posPartApprox]
    linarith
  · rw [posPartApprox_of_nonpos hε ht.le, max_eq_right ht.le]

theorem sub_le_posPartApprox {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) :
    t - ε ≤ posPartApprox ε t := by
  rcases le_or_gt t ε with h | h
  · have h0 := posPartApprox_nonneg hε t
    linarith
  · have hεt : ε ≤ t := h.le
    have hsplit : posPartApprox ε ε + ∫ s in ε..t, rampDeriv ε s = posPartApprox ε t := by
      rw [posPartApprox, posPartApprox]
      exact intervalIntegral.integral_add_adjacent_intervals
        ((continuous_rampDeriv ε).intervalIntegrable _ _)
        ((continuous_rampDeriv ε).intervalIntegrable _ _)
    have hcong : ∫ s in ε..t, rampDeriv ε s = ∫ _s in ε..t, (1 : ℝ) :=
      intervalIntegral.integral_congr fun s hs => by
        rw [Set.uIcc_of_le hεt] at hs
        exact rampDeriv_of_le hε hs.1
    have h1 : ∫ _s in ε..t, (1 : ℝ) = t - ε := by simp
    have h2 := posPartApprox_nonneg hε ε
    linarith [hsplit, hcong, h1]

theorem abs_posPartApprox_sub_le_abs {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |posPartApprox ε t - max t 0| ≤ |t| := by
  have h1 := posPartApprox_nonneg hε t
  have h2 := posPartApprox_le hε t
  have h3 : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
  have h4 : (0 : ℝ) ≤ |t| := abs_nonneg t
  rw [abs_le]
  constructor <;> linarith

theorem abs_posPartApprox_sub_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |posPartApprox ε t - max t 0| ≤ ε := by
  rcases le_or_gt 0 t with ht | ht
  · have h1 := sub_le_posPartApprox hε ht
    have h2 := posPartApprox_le hε t
    rw [max_eq_left ht] at h2 ⊢
    rw [abs_le]
    constructor <;> linarith
  · rw [posPartApprox_of_nonpos hε ht.le, max_eq_right ht.le]
    simpa using hε.le

/-- The truncated ramps converge pointwise to the indicator of `{t > 0}`. -/
theorem tendsto_rampDeriv (t : ℝ) :
    Tendsto (fun n : ℕ => rampDeriv (1 / ((n : ℝ) + 1)) t) atTop
      (𝓝 (if 0 < t then (1 : ℝ) else 0)) := by
  rcases le_or_gt t 0 with ht | ht
  · rw [if_neg (not_lt.2 ht)]
    exact tendsto_const_nhds.congr fun n =>
      (rampDeriv_of_nonpos (by positivity) ht).symm
  · rw [if_pos ht]
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < t :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds ht)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    exact (rampDeriv_of_le (by positivity) hn.le).symm

/-- The approximations converge pointwise to the positive part. -/
theorem tendsto_posPartApprox (t : ℝ) :
    Tendsto (fun n : ℕ => posPartApprox (1 / ((n : ℝ) + 1)) t) atTop (𝓝 (max t 0)) := by
  have hbound : ∀ n : ℕ, |posPartApprox (1 / ((n : ℝ) + 1)) t - max t 0| ≤ 1 / ((n : ℝ) + 1) :=
    fun n => abs_posPartApprox_sub_le (by positivity) t
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hzero
  rw [Real.dist_eq]
  exact hbound n

/-! ### Dominated convergence in `L^p` -/

/-- **Dominated convergence in `L^p`**: if `‖h n‖ ≤ ‖g‖` a.e. with `g ∈ L^p` and `h n → 0` a.e.,
then `‖h n‖_{L^p} → 0`. -/
theorem tendsto_eLpNorm_of_dominated {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ} (hp0 : 0 < p) {h : ℕ → α → E} {g : α → E}
    (hg : MemLp g (ENNReal.ofReal p) μ) (hhm : ∀ n, AEStronglyMeasurable (h n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ ≤ ‖g x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (h n) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hfin : ∫⁻ x, ‖g x‖ₑ ^ p ∂μ ≠ ⊤ := by
    rw [lintegral_enorm_rpow_eq_eLpNorm_rpow hp0]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le hg.eLpNorm_ne_top
  have hint : Tendsto (fun n => ∫⁻ x, ‖h n x‖ₑ ^ p ∂μ) atTop (𝓝 0) := by
    have h0 := tendsto_lintegral_of_dominated_convergence' (f := fun _ => (0 : ℝ≥0∞))
      (fun x => ‖g x‖ₑ ^ p) (fun n => ((hhm n).enorm.pow_const p)) (fun n => ?_) hfin ?_
    · simpa using h0
    · filter_upwards [hbound n] with x hx
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx
    · filter_upwards [hlim] with x hx
      have h2 : Tendsto (fun n => ‖h n x‖ₑ) atTop (𝓝 0) := by
        have hc := (continuous_enorm.tendsto (0 : E)).comp hx
        rwa [enorm_zero] at hc
      have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp0] using h3
  have h1 : Tendsto (fun n => (∫⁻ x, ‖h n x‖ₑ ^ p ∂μ) ^ (1 / p)) atTop (𝓝 0) := by
    have h2 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hint
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h2
  refine h1.congr fun n => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]

/-- The form of `tendsto_eLpNorm_of_dominated` used for `HasWeakGradient.of_tendsto`. -/
theorem tendsto_eLpNorm_sub_of_dominated {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ} (hp0 : 0 < p) {w : ℕ → α → E} {wl g : α → E}
    (hg : MemLp g (ENNReal.ofReal p) μ) (hwm : ∀ n, AEStronglyMeasurable (w n) μ)
    (hwlm : AEStronglyMeasurable wl μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖w n x - wl x‖ ≤ ‖g x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (wl x))) :
    Tendsto (fun n => eLpNorm (w n - wl) (ENNReal.ofReal p) μ) atTop (𝓝 0) :=
  tendsto_eLpNorm_of_dominated hp0 hg (fun n => (hwm n).sub hwlm)
    (fun n => (hbound n).mono fun x hx => hx)
    (hlim.mono fun x hx => by simpa using hx.sub_const (wl x))

/-! ### The positive part in `W₀^{1,p}` -/

/-- **The positive part in `W₀^{1,p}(K)`** (Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Lemma 7.6): `f ↦ f ∨ 0` maps `W₀^{1,p}(K)` to itself, with weak
gradient `1_{f > 0} ∇f`.

Proof: the `C¹` primitives `posPartApprox ε` of the truncated ramps satisfy the hypotheses of the
chain rule `memW0_comp`, giving `HasWeakGradient (G_ε ∘ f) (G_ε'(f) ∇f)`; as `ε = 1/(n+1) ↓ 0` one
has `G_ε(f) → f ∨ 0` and `G_ε'(f) ∇f → 1_{f>0} ∇f` in `L^p` (dominated convergence), so
`HasWeakGradient.of_tendsto` transfers the weak gradient to the limit. -/
theorem memW0_posPart {p : ℝ} (hp : 1 < p) {K : Set (Euc d)} {f : Euc d → ℝ}
    (hf : MemW0 p K f) :
    MemW0 p K (fun x => max (f x) 0) ∧
      weakGrad (fun x => max (f x) 0) =ᵐ[volume]
        fun x => if 0 < f x then weakGrad f x else 0 := by
  have hp0 : 0 < p := by linarith
  have hεpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hgp : MemLp (weakGrad f) (ENNReal.ofReal p) volume := hf.memLp_weakGrad
  have hfm : AEStronglyMeasurable f volume := hf.memLp.aestronglyMeasurable
  have hmaxc : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
  have hflm : AEStronglyMeasurable (fun x => max (f x) 0) volume :=
    hmaxc.comp_aestronglyMeasurable hfm
  have hflp : MemLp (fun x => max (f x) 0) (ENNReal.ofReal p) volume := by
    refine hf.memLp.of_le_mul (c := 1) hflm (Eventually.of_forall fun x => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (f x) (0 : ℝ))]
    exact max_le (le_abs_self _) (abs_nonneg _)
  -- the `C¹` approximants and their weak gradients
  have happ : ∀ n : ℕ, MemW0 p K (fun x => posPartApprox (1 / ((n : ℝ) + 1)) (f x)) ∧
      weakGrad (fun x => posPartApprox (1 / ((n : ℝ) + 1)) (f x)) =ᵐ[volume]
        fun x => deriv (posPartApprox (1 / ((n : ℝ) + 1))) (f x) • weakGrad f x := fun n =>
    memW0_comp hp hf (contDiff_posPartApprox _) (posPartApprox_zero _)
      (fun t => by rw [deriv_posPartApprox]; exact abs_rampDeriv_le_one _ t)
  have hwgn : ∀ n : ℕ, HasWeakGradient (fun x => posPartApprox (1 / ((n : ℝ) + 1)) (f x))
      (fun x => rampDeriv (1 / ((n : ℝ) + 1)) (f x) • weakGrad f x) := by
    intro n
    refine ((happ n).1.hasWeakGradient).congr_right
      ((happ n).2.trans (Eventually.of_forall fun x => ?_))
    rw [deriv_posPartApprox]
  -- measurability and `L^p` membership of the limit gradient
  have hram : ∀ n : ℕ, AEStronglyMeasurable
      (fun x => rampDeriv (1 / ((n : ℝ) + 1)) (f x)) volume := fun n =>
    (continuous_rampDeriv _).comp_aestronglyMeasurable hfm
  have hlima : ∀ᵐ x : Euc d,
      Tendsto (fun n : ℕ => rampDeriv (1 / ((n : ℝ) + 1)) (f x)) atTop
        (𝓝 (if 0 < f x then (1 : ℝ) else 0)) :=
    Eventually.of_forall fun x => tendsto_rampDeriv (f x)
  have hglm : AEStronglyMeasurable (fun x => if 0 < f x then weakGrad f x else 0) volume := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun (n : ℕ) x => rampDeriv (1 / ((n : ℝ) + 1)) (f x) • weakGrad f x)
      (fun n => (hram n).smul hgp.aestronglyMeasurable) ?_
    filter_upwards [hlima] with x hx
    have hs := hx.smul_const (weakGrad f x)
    by_cases hfx : 0 < f x
    · simpa [hfx] using hs
    · simpa [hfx] using hs
  have hglp : MemLp (fun x => if 0 < f x then weakGrad f x else 0)
      (ENNReal.ofReal p) volume := by
    refine hgp.of_le_mul (c := 1) hglm (Eventually.of_forall fun x => ?_)
    by_cases hfx : 0 < f x
    · simp [hfx]
    · simp [hfx]
  -- `L^p` convergence of the values
  have hconv1 : Tendsto (fun n : ℕ =>
      eLpNorm ((fun x => posPartApprox (1 / ((n : ℝ) + 1)) (f x)) - fun x => max (f x) 0)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_dominated hp0 hf.memLp
      (fun n => ((contDiff_posPartApprox _).continuous).comp_aestronglyMeasurable hfm)
      hflm (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => tendsto_posPartApprox (f x))
    simpa only [Real.norm_eq_abs] using abs_posPartApprox_sub_le_abs (hεpos n) (f x)
  -- `L^p` convergence of the gradients
  have hconv2 : Tendsto (fun n : ℕ =>
      eLpNorm ((fun x => rampDeriv (1 / ((n : ℝ) + 1)) (f x) • weakGrad f x) -
        fun x => if 0 < f x then weakGrad f x else 0) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_dominated hp0 (g := weakGrad f) hgp
      (fun n => (hram n).smul hgp.aestronglyMeasurable) hglm
      (fun n => Eventually.of_forall fun x => ?_) ?_
    · by_cases hfx : 0 < f x
      · have hrw : rampDeriv (1 / ((n : ℝ) + 1)) (f x) • weakGrad f x -
            (if 0 < f x then weakGrad f x else 0) =
            (rampDeriv (1 / ((n : ℝ) + 1)) (f x) - 1) • weakGrad f x := by
          rw [if_pos hfx, sub_smul, one_smul]
        rw [hrw, norm_smul, Real.norm_eq_abs]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        have h1 := rampDeriv_nonneg (1 / ((n : ℝ) + 1)) (f x)
        have h2 := rampDeriv_le_one (1 / ((n : ℝ) + 1)) (f x)
        rw [abs_le]
        constructor <;> linarith
      · rw [if_neg hfx, sub_zero, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (abs_rampDeriv_le_one _ _)
    · filter_upwards [hlima] with x hx
      have hs := hx.smul_const (weakGrad f x)
      by_cases hfx : 0 < f x
      · simpa [hfx] using hs
      · simpa [hfx] using hs
  have hwg : HasWeakGradient (fun x => max (f x) 0)
      (fun x => if 0 < f x then weakGrad f x else 0) :=
    HasWeakGradient.of_tendsto hp hwgn hflp hglp hconv1 hconv2
  refine ⟨⟨hflp, ?_, ⟨_, hwg, hglp⟩⟩, hwg.weakGrad_ae_eq⟩
  filter_upwards [hf.ae_eq_zero] with x hx hxK
  simp [hx hxK]

/-! ### The comparison test function -/

/-- The test function `ψ = (u − Ψ)⁺` of the comparison principle: if `u ∈ W₀^{1,p}(K)`,
`Ψ ∈ W^{1,p}(ℝ^d)` and `u ≤ Ψ` a.e. outside `K`, then `ψ ∈ W₀^{1,p}(K)` with weak gradient
`1_{u > Ψ}(∇u − ∇Ψ)`. -/
theorem exists_posPart_test {p : ℝ} (hp : 1 < p) {K : Set (Euc d)} {u Ψ : Euc d → ℝ}
    (hu : MemW0 p K u) (hΨ : MemW0 p Set.univ Ψ)
    (hvK : ∀ᵐ x : Euc d, x ∉ K → u x - Ψ x ≤ 0) :
    ∃ ψ : Euc d → ℝ, MemW0 p K ψ ∧ (∀ x, ψ x = max (u x - Ψ x) 0) ∧
      weakGrad ψ =ᵐ[volume]
        fun x => if 0 < u x - Ψ x then weakGrad u x - weakGrad Ψ x else 0 := by
  have hu' : MemW0 p Set.univ u := hu.mono (Set.subset_univ K)
  have hadd : MemW0 p Set.univ (u + (-1 : ℝ) • Ψ) := hu'.add (hΨ.smul (-1))
  have hfe : (u + (-1 : ℝ) • Ψ) = fun x => u x - Ψ x := by
    funext x
    simp [sub_eq_add_neg]
  have hv : MemW0 p Set.univ (fun x => u x - Ψ x) := hfe ▸ hadd
  have hwv : HasWeakGradient (fun x => u x - Ψ x) (fun x => weakGrad u x - weakGrad Ψ x) := by
    have h1 : HasWeakGradient (u + (-1 : ℝ) • Ψ) (weakGrad u + (-1 : ℝ) • weakGrad Ψ) :=
      hu.hasWeakGradient.add (hΨ.hasWeakGradient.smul (-1))
    refine (h1.congr_left (Eventually.of_forall fun x => ?_)).congr_right
      (Eventually.of_forall fun x => ?_)
    · simp [sub_eq_add_neg]
    · simp [sub_eq_add_neg]
  have hvg : weakGrad (fun x => u x - Ψ x) =ᵐ[volume] fun x => weakGrad u x - weakGrad Ψ x :=
    hwv.weakGrad_ae_eq
  obtain ⟨hpos, hposg⟩ := memW0_posPart hp hv
  refine ⟨fun x => max (u x - Ψ x) 0, ⟨hpos.memLp, ?_, hpos.exists_weakGradient⟩,
    fun x => rfl, ?_⟩
  · filter_upwards [hvK] with x hx hxK
    exact max_eq_right (hx hxK)
  · refine hposg.trans ?_
    filter_upwards [hvg] with x hx
    by_cases hxv : 0 < u x - Ψ x
    · rw [if_pos hxv, if_pos hxv, hx]
    · rw [if_neg hxv, if_neg hxv]

/-! ### The weak comparison principle -/

/-- **Weak comparison principle for the degenerate anisotropic `p`-Laplacian.** Let `u` be a
nonnegative weak eigensolution of `−div a(∇u) = λ u^{p−1}` on the bounded open set `K` and let
`Ψ` have a weak gradient in `L^p`. If the test function `ψ = (u − Ψ)⁺` lies in `W₀^{1,p}(K)` with
weak gradient `1_{u > Ψ}(∇u − ∇Ψ)` (`exists_posPart_test`) and `Ψ` is a supersolution against it,
`λ ∫ u^{p−1} ψ ≤ ∫ ⟪a(∇Ψ), ∇ψ⟫`, then `u ≤ Ψ` almost everywhere.

Proof: subtracting the two relations, `∫ ⟪a(∇u) − a(∇Ψ), ∇ψ⟫ ≤ 0`, while the integrand equals
`1_{u > Ψ} ⟪a(∇u) − a(∇Ψ), ∇u − ∇Ψ⟫ ≥ 0` by the monotonicity of the flux; hence it vanishes a.e.,
so `∇u = ∇Ψ` a.e. on `{u > Ψ}` by strict monotonicity (`eq_of_inner_flux_sub_eq_zero`), i.e.
`∇ψ = 0` a.e.  The Dirichlet–Poincaré inequality then forces `ψ = 0` a.e. -/
theorem ae_le_of_comparison {p : ℝ} (hp : 1 < p) (hd : 0 < d) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hKb : Bornology.IsBounded K)
    {lam : ℝ} {u Ψ : Euc d → ℝ} (hu : IsWeakEigensolution p F K lam u)
    (hΨp : MemLp (weakGrad Ψ) (ENNReal.ofReal p) volume) {ψ : Euc d → ℝ}
    (hψK : MemW0 p K ψ) (hψval : ∀ x, ψ x = max (u x - Ψ x) 0)
    (hψgrad : weakGrad ψ =ᵐ[volume]
      fun x => if 0 < u x - Ψ x then weakGrad u x - weakGrad Ψ x else 0)
    (hsuper : lam * ∫ x, u x ^ (p - 1) * ψ x ≤
      ∫ x, ⟪flux p F (weakGrad Ψ x), weakGrad ψ x⟫) :
    ∀ᵐ x : Euc d, u x ≤ Ψ x := by
  have hp0 : 0 < p := by linarith
  have heq1 : ∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ = lam * ∫ x, u x ^ (p - 1) * ψ x :=
    hu.weakEq ψ hψK
  have hi1 : Integrable fun x => ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ :=
    integrable_inner_flux hp hF hu.memW0.memLp_weakGrad hψK.memLp_weakGrad
  have hi2 : Integrable fun x => ⟪flux p F (weakGrad Ψ x), weakGrad ψ x⟫ :=
    integrable_inner_flux hp hF hΨp hψK.memLp_weakGrad
  have hsplit : (fun x => ⟪flux p F (weakGrad u x) - flux p F (weakGrad Ψ x), weakGrad ψ x⟫) =
      fun x => ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ -
        ⟪flux p F (weakGrad Ψ x), weakGrad ψ x⟫ := by
    funext x
    rw [inner_sub_left]
  have hi3 : Integrable fun x =>
      ⟪flux p F (weakGrad u x) - flux p F (weakGrad Ψ x), weakGrad ψ x⟫ := by
    rw [hsplit]
    exact hi1.sub hi2
  have hnn : 0 ≤ᵐ[volume]
      fun x => ⟪flux p F (weakGrad u x) - flux p F (weakGrad Ψ x), weakGrad ψ x⟫ := by
    filter_upwards [hψgrad] with x hx
    show (0 : ℝ) ≤ ⟪flux p F (weakGrad u x) - flux p F (weakGrad Ψ x), weakGrad ψ x⟫
    rw [hx]
    by_cases hxv : 0 < u x - Ψ x
    · rw [if_pos hxv]
      exact hF.inner_flux_sub_nonneg hp _ _
    · simp [hxv]
  have hle : ∫ x, ⟪flux p F (weakGrad u x) - flux p F (weakGrad Ψ x), weakGrad ψ x⟫ ≤ 0 := by
    rw [hsplit, integral_sub hi1 hi2, heq1]
    linarith
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn hi3).1
    (le_antisymm hle (integral_nonneg_of_ae hnn))
  have hgrad0 : weakGrad ψ =ᵐ[volume] 0 := by
    filter_upwards [hzero, hψgrad] with x h1 h2
    have h1' : ⟪flux p F (weakGrad u x) - flux p F (weakGrad Ψ x), weakGrad ψ x⟫ = 0 := h1
    show weakGrad ψ x = 0
    by_cases hxv : 0 < u x - Ψ x
    · rw [h2, if_pos hxv] at h1' ⊢
      have heq := hF.eq_of_inner_flux_sub_eq_zero hp h1'
      simp [heq]
    · rw [h2, if_neg hxv]
  obtain ⟨C, hCtop, hC⟩ := exists_poincare_const hd hp hKb
  have hnorm : eLpNorm ψ (ENNReal.ofReal p) volume = 0 := by
    have h1 := hC ψ hψK
    have h2 : gradLpNorm p ψ = 0 := by
      rw [gradLpNorm, eLpNorm_congr_ae hgrad0, eLpNorm_zero]
    rw [h2, mul_zero] at h1
    exact le_antisymm h1 zero_le
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hψ0 : ψ =ᵐ[volume] 0 :=
    (eLpNorm_eq_zero_iff hψK.memLp.aestronglyMeasurable hp').1 hnorm
  filter_upwards [hψ0] with x hx
  have hmax : max (u x - Ψ x) 0 = 0 := by rw [← hψval x]; exact hx
  by_contra hcon
  push_neg at hcon
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ u x - Ψ x)] at hmax
  linarith

/-! ### Integration by parts against a `W₀^{1,p}(K)` function -/

/-- **Integration by parts for a smooth scalar against `W₀^{1,p}(K)`**: if `ψ ∈ W₀^{1,p}(K)`
vanishes a.e. off `K` together with its weak gradient, `c` is smooth and `θ` is a smooth compactly
supported cutoff with `θ = 1` and `∇θ = 0` on `K`, then `∫ ⟪∇ψ, w⟫ c = −∫ ψ ⟪∇c, w⟫`. (Testing
the weak-gradient identity of `ψ` with the compactly supported test function `θ c`.) -/
theorem integral_inner_weakGrad_mul_smooth {p : ℝ} {K : Set (Euc d)} {ψ : Euc d → ℝ}
    (hψ : MemW0 p K ψ) (hψg : ∀ᵐ x : Euc d, x ∉ K → weakGrad ψ x = 0)
    {c θ : Euc d → ℝ} (hc : ContDiff ℝ ∞ c) (hθ : ContDiff ℝ ∞ θ)
    (hθs : HasCompactSupport θ) (hθ1 : ∀ x ∈ K, θ x = 1)
    (hθg : ∀ x ∈ K, gradient θ x = 0) (w : Euc d) :
    Integrable (fun x => ψ x * ⟪gradient c x, w⟫) ∧
      ∫ x, ⟪weakGrad ψ x, w⟫ * c x = -∫ x, ψ x * ⟪gradient c x, w⟫ := by
  have hχ : ContDiff ℝ ∞ fun x => θ x * c x := hθ.mul hc
  have hχs : HasCompactSupport fun x => θ x * c x := hθs.mul_right
  have hkey : ∫ x, ψ x * fderiv ℝ (fun y => θ y * c y) x w =
      -∫ x, ⟪weakGrad ψ x, w⟫ * (θ x * c x) :=
    hψ.hasWeakGradient.integral_mul_fderiv _ hχ hχs w
  have hgradχ : ∀ x : Euc d, fderiv ℝ (fun y => θ y * c y) x w =
      θ x * ⟪gradient c x, w⟫ + c x * ⟪gradient θ x, w⟫ := by
    intro x
    have hθ1' : ContDiff ℝ 1 θ := hθ.of_le (by simp)
    have hc1' : ContDiff ℝ 1 c := hc.of_le (by simp)
    have h : HasFDerivAt (fun y => θ y * c y) (θ x • fderiv ℝ c x + c x • fderiv ℝ θ x) x :=
      (hθ1'.differentiable one_ne_zero x).hasFDerivAt.mul
        (hc1'.differentiable one_ne_zero x).hasFDerivAt
    rw [h.fderiv]
    simp
  have e1 : ∀ᵐ x : Euc d,
      ψ x * fderiv ℝ (fun y => θ y * c y) x w = ψ x * ⟪gradient c x, w⟫ := by
    filter_upwards [hψ.ae_eq_zero] with x hx
    by_cases hxK : x ∈ K
    · rw [hgradχ x, hθ1 x hxK, hθg x hxK, one_mul, inner_zero_left, mul_zero, add_zero]
    · rw [hx hxK, zero_mul, zero_mul]
  have e2 : ∀ᵐ x : Euc d,
      ⟪weakGrad ψ x, w⟫ * (θ x * c x) = ⟪weakGrad ψ x, w⟫ * c x := by
    filter_upwards [hψg] with x hx
    by_cases hxK : x ∈ K
    · rw [hθ1 x hxK, one_mul]
    · rw [hx hxK, inner_zero_left, zero_mul, zero_mul]
  have hA : ∫ x, ψ x * fderiv ℝ (fun y => θ y * c y) x w = ∫ x, ψ x * ⟪gradient c x, w⟫ :=
    integral_congr_ae e1
  have hB : ∫ x, ⟪weakGrad ψ x, w⟫ * (θ x * c x) = ∫ x, ⟪weakGrad ψ x, w⟫ * c x :=
    integral_congr_ae e2
  have hDc : Continuous fun x => fderiv ℝ (fun y => θ y * c y) x w :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDcs : HasCompactSupport fun x => fderiv ℝ (fun y => θ y * c y) x w :=
    (hχs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L w) (by simp)
  have hint : Integrable fun x => ψ x * fderiv ℝ (fun y => θ y * c y) x w := by
    simpa only [smul_eq_mul, mul_comm] using
      hψ.hasWeakGradient.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hDc hDcs
  exact ⟨hint.congr e1, by linarith [hkey, hA, hB]⟩

/-! ### The smooth half-space barrier -/

/-- Euler's identity at the Riesz vector: `⟪n, a(−n)⟫ = −F(n)^p`. -/
theorem inner_riesz_flux_neg {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    (n : Euc d) : ⟪n, flux p F (-n)⟫ = -(F n ^ p) := by
  have h1 : ⟪flux p F (-n), -n⟫ = F (-n) ^ p := hF.inner_flux_self_eq_rpow hp (-n)
  rw [inner_neg_right, hF.even] at h1
  rw [real_inner_comm]
  linarith

/-- **The exponential half-space barrier.** With `n` the Riesz vector of `ℓ` and `A > 0`, the
smooth functions `Φ = A (1 − e^{ℓ · − ℓ x₀})` and `c = A^{p−1} e^{(p−1)(ℓ · − ℓ x₀)}` satisfy
`a(∇Φ) = c • a(−n)` and `⟪∇c, a(−n)⟫ = −(p−1) F(n)^p c`, i.e. `−div a(∇Φ) = (p−1) F(n)^p c > 0`. -/
theorem exists_barrier_data {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {n : Euc d} (ℓ : Euc d →L[ℝ] ℝ) (hn : ∀ v : Euc d, ⟪n, v⟫ = ℓ v) (x₀ : Euc d) {A : ℝ}
    (hA0 : 0 < A) :
    ∃ Φ cc : Euc d → ℝ, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ cc ∧
      (∀ x, Φ x = A * (1 - Real.exp (ℓ x - ℓ x₀))) ∧
      (∀ x, cc x = A ^ (p - 1) * Real.exp ((p - 1) * (ℓ x - ℓ x₀))) ∧
      (∀ x, 0 < cc x) ∧
      (∀ x, flux p F (gradient Φ x) = cc x • flux p F (-n)) ∧
      (∀ x, ⟪gradient cc x, flux p F (-n)⟫ = -((p - 1) * F n ^ p * cc x)) := by
  have hp1 : 0 < p - 1 := by linarith
  have hS : ∀ x : Euc d, HasFDerivAt (fun y : Euc d => ℓ y - ℓ x₀) (ℓ : Euc d →L[ℝ] ℝ) x :=
    fun x => (ℓ.hasFDerivAt (x := x)).sub_const (ℓ x₀)
  have hgradS : ∀ x : Euc d, gradient (fun y : Euc d => ℓ y - ℓ x₀) x = n := by
    intro x
    refine ext_inner_right ℝ fun v => ?_
    rw [inner_gradient_left, (hS x).fderiv, hn v]
  have hGd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => A * (1 - Real.exp s)) (-(A * Real.exp t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => 1 - Real.exp s) (-Real.exp t) t :=
      (Real.hasDerivAt_exp t).const_sub 1
    have h2 := h1.const_mul A
    rw [mul_neg] at h2
    exact h2
  have hG2d : ∀ t : ℝ, HasDerivAt (fun s : ℝ => A ^ (p - 1) * Real.exp ((p - 1) * s))
      ((p - 1) * (A ^ (p - 1) * Real.exp ((p - 1) * t))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (p - 1) * s) (p - 1) t := by
      simpa using (hasDerivAt_id t).const_mul (p - 1)
    have h2 : HasDerivAt (fun s : ℝ => Real.exp ((p - 1) * s))
        (Real.exp ((p - 1) * t) * (p - 1)) t := (Real.hasDerivAt_exp ((p - 1) * t)).comp t h1
    have h3 := h2.const_mul (A ^ (p - 1))
    have he : A ^ (p - 1) * (Real.exp ((p - 1) * t) * (p - 1))
        = (p - 1) * (A ^ (p - 1) * Real.exp ((p - 1) * t)) := by ring
    rw [he] at h3
    exact h3
  refine ⟨fun x => A * (1 - Real.exp (ℓ x - ℓ x₀)),
    fun x => A ^ (p - 1) * Real.exp ((p - 1) * (ℓ x - ℓ x₀)), ?_, ?_, fun x => rfl, fun x => rfl,
    fun x => mul_pos (Real.rpow_pos_of_pos hA0 _) (Real.exp_pos _), ?_, ?_⟩
  · exact contDiff_const.mul (contDiff_const.sub (ℓ.contDiff.sub contDiff_const).exp)
  · exact contDiff_const.mul (contDiff_const.mul (ℓ.contDiff.sub contDiff_const)).exp
  · intro x
    have hgradΦ : gradient (fun y : Euc d => A * (1 - Real.exp (ℓ y - ℓ x₀))) x =
        (A * Real.exp (ℓ x - ℓ x₀)) • (-n) := by
      rw [gradient_comp_apply (fun t => (hGd t).differentiableAt) (hS x).differentiableAt,
        (hGd (ℓ x - ℓ x₀)).deriv, hgradS x]
      module
    show flux p F (gradient (fun y : Euc d => A * (1 - Real.exp (ℓ y - ℓ x₀))) x) =
      (A ^ (p - 1) * Real.exp ((p - 1) * (ℓ x - ℓ x₀))) • flux p F (-n)
    rw [hgradΦ, hF.flux_smul_of_pos hp (mul_pos hA0 (Real.exp_pos _)) (-n)]
    congr 1
    rw [Real.mul_rpow hA0.le (Real.exp_pos _).le, ← Real.exp_mul,
      mul_comm (ℓ x - ℓ x₀) (p - 1)]
  · intro x
    have hgradcc :
        gradient (fun y : Euc d => A ^ (p - 1) * Real.exp ((p - 1) * (ℓ y - ℓ x₀))) x =
          ((p - 1) * (A ^ (p - 1) * Real.exp ((p - 1) * (ℓ x - ℓ x₀)))) • n := by
      rw [gradient_comp_apply (fun t => (hG2d t).differentiableAt) (hS x).differentiableAt,
        (hG2d (ℓ x - ℓ x₀)).deriv, hgradS x]
    show ⟪gradient (fun y : Euc d => A ^ (p - 1) * Real.exp ((p - 1) * (ℓ y - ℓ x₀))) x,
        flux p F (-n)⟫ =
      -((p - 1) * F n ^ p * (A ^ (p - 1) * Real.exp ((p - 1) * (ℓ x - ℓ x₀))))
    rw [hgradcc, real_inner_smul_left, inner_riesz_flux_neg hp hF n]
    ring

/-! ### The linear barrier bound -/

/-- **The linear boundary barrier with an explicit constant** (the analytic core of
`exists_linear_barrier`).  If `A > 0` is large enough that

`max lam 0 * M^{p-1} + 1 ≤ (p-1) F(n)^p A^{p-1} e^{-(p-1)D}`,

where `n` is the Riesz vector of the supporting functional `ℓ` and `D` bounds `ℓ x₀ - ℓ ·` on `K`,
then the comparison function `Φ = A (1 - e^{ℓ · - ℓ x₀})` dominates `u` on `K`.  Splitting the
largeness requirement off as a hypothesis is what makes `A` choosable *uniformly* over the
supporting functionals of `K` (`exists_uniform_linear_barrier`), which is what the boundary
gradient estimate needs. -/
theorem ae_le_linear_barrier {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} (hK : IsGoodConvex K) {lam : ℝ} {u : Euc d → ℝ}
    (hu : IsWeakEigensolution p F K lam u) {M : ℝ} (hM : ∀ᵐ x : Euc d, u x ≤ M)
    {x₀ : Euc d} (ℓ : Euc d →L[ℝ] ℝ) {n : Euc d} (hn : ∀ v : Euc d, ⟪n, v⟫ = ℓ v) (hn0 : n ≠ 0)
    (hℓ : ∀ x ∈ K, ℓ x < ℓ x₀) {A D : ℝ} (hA0 : 0 < A) (hD : ∀ x ∈ K, ℓ x₀ - ℓ x ≤ D)
    (hAbig : max lam 0 * M ^ (p - 1) + 1 ≤
      (p - 1) * F n ^ p * (A ^ (p - 1) * Real.exp (-((p - 1) * D)))) :
    ∀ᵐ x : Euc d, x ∈ K → u x ≤ A * (ℓ x₀ - ℓ x) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  obtain ⟨z, hz⟩ := hK.nonempty
  have hdpos : 0 < d := by
    rcases isEmpty_or_nonempty (Fin d) with hd | hd
    · exact absurd (Subsingleton.elim n 0) hn0
    · exact Fin.pos_iff_nonempty.2 hd
  have hFnp : 0 < F n ^ p := Real.rpow_pos_of_pos (hF.pos n hn0) p
  have hEpos : 0 < (p - 1) * F n ^ p := mul_pos hp1 hFnp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) (mem_closedBall_zero_iff.1 (hR hz))
  -- the smooth barrier data
  obtain ⟨Φ, cc, hΦs, hccs, hΦval, hccval, hccpos, hflux, hdivc⟩ :=
    exists_barrier_data hp hF (n := n) ℓ hn x₀ hA0
  have hΦpos : ∀ x ∈ K, 0 < Φ x := by
    intro x hx
    rw [hΦval x]
    have h1 : Real.exp (ℓ x - ℓ x₀) < 1 := by
      have h2 := hℓ x hx
      calc Real.exp (ℓ x - ℓ x₀) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
        _ = 1 := Real.exp_zero
    exact mul_pos hA0 (by linarith)
  have hΦle : ∀ x : Euc d, Φ x ≤ A * (ℓ x₀ - ℓ x) := by
    intro x
    rw [hΦval x]
    have h1 : (ℓ x - ℓ x₀) + 1 ≤ Real.exp (ℓ x - ℓ x₀) := Real.add_one_le_exp _
    have h2 : 0 ≤ A * (Real.exp (ℓ x - ℓ x₀) - ((ℓ x - ℓ x₀) + 1)) :=
      mul_nonneg hA0.le (by linarith)
    nlinarith
  have hcclow : ∀ x ∈ K, A ^ (p - 1) * Real.exp (-((p - 1) * D)) ≤ cc x := by
    intro x hx
    rw [hccval x]
    have h1 : -((p - 1) * D) ≤ (p - 1) * (ℓ x - ℓ x₀) := by
      have h2 := hD x hx
      have h3 : 0 ≤ (p - 1) * (D - (ℓ x₀ - ℓ x)) := mul_nonneg hp1.le (by linarith)
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) (Real.rpow_pos_of_pos hA0 _).le
  -- the cutoff
  obtain ⟨θb, hθbIn⟩ : ∃ θb : ContDiffBump (0 : Euc d), θb.rIn = R + 1 :=
    ⟨⟨R + 1, R + 2, by linarith, by linarith⟩, rfl⟩
  have hKball : ∀ x ∈ K, x ∈ Metric.ball (0 : Euc d) (R + 1) := fun x hx => by
    rw [mem_ball_zero_iff]
    have h2 := mem_closedBall_zero_iff.1 (hR hx)
    linarith
  have hθ1 : ∀ x ∈ Metric.ball (0 : Euc d) (R + 1), (θb : Euc d → ℝ) x = 1 := by
    intro x hx
    refine θb.one_of_mem_closedBall ?_
    rw [hθbIn]
    exact Metric.ball_subset_closedBall hx
  have hθg : ∀ x ∈ Metric.ball (0 : Euc d) (R + 1),
      gradient (θb : Euc d → ℝ) x = 0 := by
    intro x hx
    have heq : (θb : Euc d → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      exact hθ1 y hy
    unfold gradient
    rw [heq.fderiv_eq]
    simp
  -- the comparison function `Ψ = (θ Φ)⁺`
  have hΨ0s : ContDiff ℝ ∞ fun x => (θb : Euc d → ℝ) x * Φ x := θb.contDiff.mul hΦs
  have hΨ0c : HasCompactSupport fun x => (θb : Euc d → ℝ) x * Φ x :=
    θb.hasCompactSupport.mul_right
  have hΨ0w : MemW0 p Set.univ fun x => (θb : Euc d → ℝ) x * Φ x :=
    memW0_of_contDiff (hΨ0s.of_le (by simp)) hΨ0c (Set.subset_univ _) p
  obtain ⟨hΨw, hΨgr⟩ := memW0_posPart hp hΨ0w
  have hΨ0grad : weakGrad (fun x => (θb : Euc d → ℝ) x * Φ x) =ᵐ[volume]
      gradient (fun x => (θb : Euc d → ℝ) x * Φ x) :=
    weakGrad_ae_eq_gradient (hΨ0s.of_le (by simp)) hΨ0c
  have hgradeq : ∀ x ∈ Metric.ball (0 : Euc d) (R + 1),
      gradient (fun y : Euc d => (θb : Euc d → ℝ) y * Φ y) x = gradient Φ x := by
    intro x hx
    have heq : (fun y : Euc d => (θb : Euc d → ℝ) y * Φ y) =ᶠ[𝓝 x] Φ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      rw [hθ1 y hy, one_mul]
    unfold gradient
    rw [heq.fderiv_eq]
  have hΨKval : ∀ x ∈ K, max ((θb : Euc d → ℝ) x * Φ x) 0 = Φ x := by
    intro x hx
    rw [hθ1 x (hKball x hx), one_mul, max_eq_left (hΦpos x hx).le]
  have hΨnn : ∀ x : Euc d, 0 ≤ max ((θb : Euc d → ℝ) x * Φ x) 0 := fun x => le_max_right _ _
  have hΨgradK : ∀ᵐ x : Euc d, x ∈ K →
      weakGrad (fun y => max ((θb : Euc d → ℝ) y * Φ y) 0) x = gradient Φ x := by
    filter_upwards [hΨgr, hΨ0grad] with x h1 h2 hxK
    have hposx : 0 < (θb : Euc d → ℝ) x * Φ x := by
      rw [hθ1 x (hKball x hxK), one_mul]
      exact hΦpos x hxK
    rw [h1, if_pos hposx, h2, hgradeq x (hKball x hxK)]
  -- the test function `ψ = (u − Ψ)⁺`
  have hvK : ∀ᵐ x : Euc d, x ∉ K → u x - max ((θb : Euc d → ℝ) x * Φ x) 0 ≤ 0 := by
    filter_upwards [hu.memW0.ae_eq_zero] with x hx hxK
    rw [hx hxK]
    linarith [hΨnn x]
  obtain ⟨ψ, hψK, hψval, hψgrad⟩ := exists_posPart_test hp hu.memW0 hΨw hvK
  have hψnn : ∀ x : Euc d, 0 ≤ ψ x := fun x => by rw [hψval x]; exact le_max_right _ _
  have hψ0K : ∀ᵐ x : Euc d, x ∉ K → ψ x = 0 := hψK.ae_eq_zero
  have hψgrad0 : ∀ᵐ x : Euc d, x ∉ K → weakGrad ψ x = 0 := by
    filter_upwards [hψgrad, hvK] with x h1 h2 hxK
    rw [h1, if_neg (not_lt.2 (h2 hxK))]
  -- integration by parts
  obtain ⟨hintc, hIBP⟩ := integral_inner_weakGrad_mul_smooth hψK hψgrad0 hccs θb.contDiff
    θb.hasCompactSupport (fun x hx => hθ1 x (hKball x hx))
    (fun x hx => hθg x (hKball x hx)) (flux p F (-n))
  have hstep2 : (fun x => ψ x * ⟪gradient cc x, flux p F (-n)⟫) =
      fun x => -((p - 1) * F n ^ p * (ψ x * cc x)) := by
    funext x
    rw [hdivc x]
    ring
  have hintRHS : Integrable fun x => (p - 1) * F n ^ p * (ψ x * cc x) := by
    refine hintc.neg.congr (Eventually.of_forall fun x => ?_)
    show -(ψ x * ⟪gradient cc x, flux p F (-n)⟫) = (p - 1) * F n ^ p * (ψ x * cc x)
    rw [hdivc x]
    ring
  have hfluxint : ∫ x, ⟪flux p F (weakGrad (fun y => max ((θb : Euc d → ℝ) y * Φ y) 0) x),
      weakGrad ψ x⟫ = ∫ x, (p - 1) * F n ^ p * (ψ x * cc x) := by
    have step1 : ∫ x, ⟪flux p F (weakGrad (fun y => max ((θb : Euc d → ℝ) y * Φ y) 0) x),
        weakGrad ψ x⟫ = ∫ x, ⟪weakGrad ψ x, flux p F (-n)⟫ * cc x := by
      refine integral_congr_ae ?_
      filter_upwards [hΨgradK, hψgrad0] with x h1 h2
      by_cases hxK : x ∈ K
      · rw [h1 hxK, hflux x, real_inner_smul_left, real_inner_comm, mul_comm]
      · rw [h2 hxK, inner_zero_right, inner_zero_left, zero_mul]
    rw [step1, hIBP, hstep2, integral_neg, neg_neg]
  -- the supersolution inequality
  have hsuper : lam * ∫ x, u x ^ (p - 1) * ψ x ≤
      ∫ x, ⟪flux p F (weakGrad (fun y => max ((θb : Euc d → ℝ) y * Φ y) 0) x),
        weakGrad ψ x⟫ := by
    rw [hfluxint]
    have hRHSnn : 0 ≤ ∫ x, (p - 1) * F n ^ p * (ψ x * cc x) :=
      integral_nonneg fun x =>
        mul_nonneg hEpos.le (mul_nonneg (hψnn x) (hccpos x).le)
    have hLHSnn : 0 ≤ ∫ x, u x ^ (p - 1) * ψ x :=
      integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (hu.nonneg x) _) (hψnn x)
    rcases le_or_gt lam 0 with hlam | hlam
    · nlinarith
    · have hpt : ∀ᵐ x : Euc d,
          lam * (u x ^ (p - 1) * ψ x) ≤ (p - 1) * F n ^ p * (ψ x * cc x) := by
        filter_upwards [hM, hψ0K] with x hxM hx0
        by_cases hxK : x ∈ K
        · have h1 : u x ^ (p - 1) ≤ M ^ (p - 1) :=
            Real.rpow_le_rpow (hu.nonneg x) hxM hp1.le
          have h2 : A ^ (p - 1) * Real.exp (-((p - 1) * D)) ≤ cc x := hcclow x hxK
          have h3 : 0 ≤ ψ x := hψnn x
          have h4 : max lam 0 = lam := max_eq_left hlam.le
          calc lam * (u x ^ (p - 1) * ψ x)
              ≤ lam * (M ^ (p - 1) * ψ x) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h3) hlam.le
            _ = lam * M ^ (p - 1) * ψ x := by ring
            _ ≤ (max lam 0 * M ^ (p - 1) + 1) * ψ x := by rw [h4]; nlinarith
            _ ≤ (p - 1) * F n ^ p * (A ^ (p - 1) * Real.exp (-((p - 1) * D))) * ψ x :=
                mul_le_mul_of_nonneg_right hAbig h3
            _ ≤ (p - 1) * F n ^ p * cc x * ψ x :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hEpos.le) h3
            _ = (p - 1) * F n ^ p * (ψ x * cc x) := by ring
        · rw [hx0 hxK]
          simp
      have hmono := integral_mono_of_nonneg
        (Eventually.of_forall fun x => mul_nonneg hlam.le
          (mul_nonneg (Real.rpow_nonneg (hu.nonneg x) _) (hψnn x)))
        hintRHS hpt
      rwa [integral_const_mul] at hmono
  -- the comparison principle
  have hcomp := ae_le_of_comparison hp hdpos hF hK.isBounded hu hΨw.memLp_weakGrad hψK hψval
    hψgrad hsuper
  filter_upwards [hcomp] with x hx hxK
  rw [hΨKval x hxK] at hx
  exact le_trans hx (hΦle x)

/-- **The linear boundary barrier on a convex domain** (Lieberman 1988, *Boundary regularity for
solutions of degenerate elliptic equations*, Nonlinear Anal. 12, Theorem 1; MRS24, Proposition 4.5):
for a weak eigensolution `u` on a good convex `K` bounded above by `M` and a supporting functional
`ℓ` at a boundary point (`ℓ < ℓ x₀` on `K`), there is `A > 0` with `u ≤ A (ℓ x₀ − ℓ ·)` a.e. on `K`.

The comparison function is `Ψ = (θ Φ)⁺` with `Φ = A (1 − e^{ℓ · − ℓ x₀})` (positive on `K`,
`≤ A (ℓ x₀ − ℓ ·)` everywhere) and `θ` a cutoff equal to `1` on a neighbourhood of `K`; by
`exists_barrier_data`, `−div a(∇Φ) = (p−1) F(n)^p c` on `K`, which for `A` large exceeds
`λ M^{p−1}`, so `Ψ` is a supersolution and the comparison principle `ae_le_of_comparison` gives
`u ≤ Ψ = Φ` on `K`. -/
theorem exists_linear_barrier {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} (hK : IsGoodConvex K) {lam : ℝ} {u : Euc d → ℝ}
    (hu : IsWeakEigensolution p F K lam u) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x : Euc d, u x ≤ M)
    {x₀ : Euc d} (ℓ : Euc d →L[ℝ] ℝ) (hℓ : ∀ x ∈ K, ℓ x < ℓ x₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ᵐ x : Euc d, x ∈ K → u x ≤ A * (ℓ x₀ - ℓ x) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  obtain ⟨z, hz⟩ := hK.nonempty
  obtain ⟨n, hn⟩ : ∃ n : Euc d, ∀ v : Euc d, ⟪n, v⟫ = ℓ v :=
    ⟨(InnerProductSpace.toDual ℝ (Euc d)).symm ℓ, fun v => InnerProductSpace.toDual_symm_apply⟩
  have hℓne : ℓ ≠ 0 := by
    intro h
    have hlt := hℓ z hz
    rw [h] at hlt
    simp at hlt
  have hn0 : n ≠ 0 := by
    intro h
    refine hℓne (ContinuousLinearMap.ext fun v => ?_)
    have hv := hn v
    rw [h, inner_zero_left] at hv
    simp [← hv]
  have hdpos : 0 < d := by
    rcases isEmpty_or_nonempty (Fin d) with hd | hd
    · exact absurd (Subsingleton.elim n 0) hn0
    · exact Fin.pos_iff_nonempty.2 hd
  have hFnp : 0 < F n ^ p := Real.rpow_pos_of_pos (hF.pos n hn0) p
  have hEpos : 0 < (p - 1) * F n ^ p := mul_pos hp1 hFnp
  -- a bound for the linear functional on `K`
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) (mem_closedBall_zero_iff.1 (hR hz))
  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 < D ∧ ∀ x ∈ K, ℓ x₀ - ℓ x ≤ D := by
    have hmul : 0 ≤ ‖ℓ‖ * R := mul_nonneg (norm_nonneg ℓ) hR0
    refine ⟨|ℓ x₀| + ‖ℓ‖ * R + 1, by linarith [abs_nonneg (ℓ x₀)], fun x hx => ?_⟩
    have h1 : |ℓ x| ≤ ‖ℓ‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using ℓ.le_opNorm x
    have h2 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    have h3 : ℓ x₀ ≤ |ℓ x₀| := le_abs_self _
    have h4 : -|ℓ x| ≤ ℓ x := neg_abs_le _
    have h5 : ‖ℓ‖ * ‖x‖ ≤ ‖ℓ‖ * R := mul_le_mul_of_nonneg_left h2 (norm_nonneg ℓ)
    linarith
  -- the size of the barrier
  have hden : (p - 1) * F n ^ p ≠ 0 := ne_of_gt hEpos
  obtain ⟨B, hB0, hBeq⟩ : ∃ B : ℝ, 0 < B ∧
      (p - 1) * F n ^ p * B * Real.exp (-((p - 1) * D)) = max lam 0 * M ^ (p - 1) + 1 := by
    have hnum : 0 < max lam 0 * M ^ (p - 1) + 1 := by
      have h1 : 0 ≤ max lam 0 := le_max_right _ _
      have h2 : 0 ≤ M ^ (p - 1) := Real.rpow_nonneg hM0 _
      have h3 : 0 ≤ max lam 0 * M ^ (p - 1) := mul_nonneg h1 h2
      linarith
    refine ⟨(max lam 0 * M ^ (p - 1) + 1) * Real.exp ((p - 1) * D) * ((p - 1) * F n ^ p)⁻¹,
      mul_pos (mul_pos hnum (Real.exp_pos _)) (inv_pos.2 hEpos), ?_⟩
    have hinv : (p - 1) * F n ^ p * ((p - 1) * F n ^ p)⁻¹ = 1 := mul_inv_cancel₀ hden
    have hexp : Real.exp ((p - 1) * D) * Real.exp (-((p - 1) * D)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (p - 1) * F n ^ p * ((max lam 0 * M ^ (p - 1) + 1) * Real.exp ((p - 1) * D) *
          ((p - 1) * F n ^ p)⁻¹) * Real.exp (-((p - 1) * D))
        = (max lam 0 * M ^ (p - 1) + 1) * ((p - 1) * F n ^ p * ((p - 1) * F n ^ p)⁻¹) *
            (Real.exp ((p - 1) * D) * Real.exp (-((p - 1) * D))) := by ring
      _ = max lam 0 * M ^ (p - 1) + 1 := by rw [hinv, hexp]; ring
  obtain ⟨A, hA0, hApow⟩ : ∃ A : ℝ, 0 < A ∧ A ^ (p - 1) = B := by
    refine ⟨B ^ (1 / (p - 1)), Real.rpow_pos_of_pos hB0 _, ?_⟩
    rw [← Real.rpow_mul hB0.le, one_div, inv_mul_cancel₀ (ne_of_gt hp1), Real.rpow_one]
  refine ⟨A, hA0, ae_le_linear_barrier hp hF hK hu hM ℓ hn hn0 hℓ hA0 hD (le_of_eq ?_)⟩
  rw [hApow, ← hBeq]
  ring

/-- **A linear boundary barrier with a constant uniform over the supporting functionals**
(Lieberman 1988, Theorem 1, the form needed for the boundary gradient estimate): for a bounded
weak eigensolution `u` on a good convex `K` there is a *single* `A > 0` such that
`u ≤ A (ℓ x₀ - ℓ ·)` a.e. on `K` for **every** norm-one functional `ℓ` supporting `K` at a point
`x₀` of `closure K`.

Uniformity has two ingredients. The Riesz vector `n` of `ℓ` has `‖n‖ = 1`, so `F n ≥ c` with `c`
the ellipticity constant of `F` (`IsSmoothStrictNorm.exists_pos_mul_norm_le`); and
`ℓ x₀ - ℓ x ≤ 2R` on `K` whenever `K ∪ {x₀} ⊆ B̄(0, R)`. Both bounds are independent of `ℓ`, so
a single `A` satisfies the largeness hypothesis of `ae_le_linear_barrier` for all of them. -/
theorem exists_uniform_linear_barrier {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {lam : ℝ} {u : Euc d → ℝ}
    (hu : IsWeakEigensolution p F K lam u) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x : Euc d, u x ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ (x₀ : Euc d) (ℓ : Euc d →L[ℝ] ℝ), ‖ℓ‖ = 1 → x₀ ∈ closure K →
      (∀ x ∈ K, ℓ x < ℓ x₀) → ∀ᵐ x : Euc d, x ∈ K → u x ≤ A * (ℓ x₀ - ℓ x) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  obtain ⟨z, hz⟩ := hK.nonempty
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) (mem_closedBall_zero_iff.1 (hR hz))
  have hRcl : closure K ⊆ Metric.closedBall (0 : Euc d) R :=
    closure_minimal hR Metric.isClosed_closedBall
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · -- In dimension `0` there is no functional of norm one, so the statement is vacuous.
    refine ⟨1, one_pos, fun x₀ ℓ hℓ1 _ _ => ?_⟩
    exfalso
    have hz0 : ℓ = 0 := by
      refine ContinuousLinearMap.ext fun v => ?_
      have hv : v = 0 := Subsingleton.elim v 0
      simp [hv]
    rw [hz0, norm_zero] at hℓ1
    exact zero_ne_one hℓ1
  · haveI : Nonempty (Fin d) := hd
    obtain ⟨cc, hcc0, hcc⟩ := hF.exists_pos_mul_norm_le
    have hccp : 0 < cc ^ p := Real.rpow_pos_of_pos hcc0 p
    have hEpos : 0 < (p - 1) * cc ^ p := mul_pos hp1 hccp
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 2 * R + 1 := ⟨_, rfl⟩
    have hnum : 0 < max lam 0 * M ^ (p - 1) + 1 := by
      have h1 : (0 : ℝ) ≤ max lam 0 := le_max_right _ _
      have h2 : (0 : ℝ) ≤ M ^ (p - 1) := Real.rpow_nonneg hM0 _
      have h3 : (0 : ℝ) ≤ max lam 0 * M ^ (p - 1) := mul_nonneg h1 h2
      linarith
    obtain ⟨B, hB0, hBeq⟩ : ∃ B : ℝ, 0 < B ∧
        (p - 1) * cc ^ p * B * Real.exp (-((p - 1) * D)) = max lam 0 * M ^ (p - 1) + 1 := by
      refine ⟨(max lam 0 * M ^ (p - 1) + 1) * Real.exp ((p - 1) * D) * ((p - 1) * cc ^ p)⁻¹,
        mul_pos (mul_pos hnum (Real.exp_pos _)) (inv_pos.2 hEpos), ?_⟩
      have hinv : (p - 1) * cc ^ p * ((p - 1) * cc ^ p)⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
      have hexp : Real.exp ((p - 1) * D) * Real.exp (-((p - 1) * D)) = 1 := by
        rw [← Real.exp_add]
        simp
      calc (p - 1) * cc ^ p * ((max lam 0 * M ^ (p - 1) + 1) * Real.exp ((p - 1) * D) *
            ((p - 1) * cc ^ p)⁻¹) * Real.exp (-((p - 1) * D))
          = (max lam 0 * M ^ (p - 1) + 1) * ((p - 1) * cc ^ p * ((p - 1) * cc ^ p)⁻¹) *
              (Real.exp ((p - 1) * D) * Real.exp (-((p - 1) * D))) := by ring
        _ = max lam 0 * M ^ (p - 1) + 1 := by rw [hinv, hexp]; ring
    obtain ⟨A, hA0, hApow⟩ : ∃ A : ℝ, 0 < A ∧ A ^ (p - 1) = B := by
      refine ⟨B ^ (1 / (p - 1)), Real.rpow_pos_of_pos hB0 _, ?_⟩
      rw [← Real.rpow_mul hB0.le, one_div, inv_mul_cancel₀ (ne_of_gt hp1), Real.rpow_one]
    refine ⟨A, hA0, fun x₀ ℓ hℓ1 hx₀ hℓ => ?_⟩
    obtain ⟨n, hndef⟩ : ∃ n : Euc d, n = (InnerProductSpace.toDual ℝ (Euc d)).symm ℓ := ⟨_, rfl⟩
    have hn : ∀ v : Euc d, ⟪n, v⟫ = ℓ v := by
      intro v
      rw [hndef]
      exact InnerProductSpace.toDual_symm_apply
    have hnle : ‖n‖ ≤ 1 := by
      have h1 : ‖n‖ * ‖n‖ = ℓ n := by rw [← hn n, real_inner_self_eq_norm_mul_norm]
      have h2 : ℓ n ≤ ‖ℓ‖ * ‖n‖ := by
        have h := ℓ.le_opNorm n
        rw [Real.norm_eq_abs] at h
        exact le_trans (le_abs_self _) h
      rw [hℓ1, one_mul] at h2
      nlinarith [norm_nonneg n]
    have hnge : (1 : ℝ) ≤ ‖n‖ := by
      rw [← hℓ1]
      refine ℓ.opNorm_le_bound (norm_nonneg n) fun v => ?_
      rw [← hn v, Real.norm_eq_abs]
      exact abs_real_inner_le_norm n v
    have hnnorm : ‖n‖ = 1 := le_antisymm hnle hnge
    have hn0 : n ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnnorm
      exact zero_ne_one hnnorm
    have hFn : cc ≤ F n := by
      have h := hcc n
      rwa [hnnorm, mul_one] at h
    have hFnp : cc ^ p ≤ F n ^ p := Real.rpow_le_rpow hcc0.le hFn hp0.le
    have hD : ∀ x ∈ K, ℓ x₀ - ℓ x ≤ D := by
      intro x hx
      have h1 : |ℓ x₀| ≤ ‖ℓ‖ * ‖x₀‖ := by simpa [Real.norm_eq_abs] using ℓ.le_opNorm x₀
      have h2 : |ℓ x| ≤ ‖ℓ‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using ℓ.le_opNorm x
      have h3 : ‖x₀‖ ≤ R := mem_closedBall_zero_iff.1 (hRcl hx₀)
      have h4 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
      rw [hℓ1, one_mul] at h1 h2
      have h5 : ℓ x₀ ≤ |ℓ x₀| := le_abs_self _
      have h6 : -|ℓ x| ≤ ℓ x := neg_abs_le _
      rw [hDdef]
      linarith
    refine ae_le_linear_barrier hp hF hK hu hM ℓ hn hn0 hℓ hA0 hD ?_
    have hnn : (0 : ℝ) ≤ A ^ (p - 1) * Real.exp (-((p - 1) * D)) :=
      mul_nonneg (Real.rpow_nonneg hA0.le _) (Real.exp_pos _).le
    have hstep : (p - 1) * cc ^ p * (A ^ (p - 1) * Real.exp (-((p - 1) * D))) ≤
        (p - 1) * F n ^ p * (A ^ (p - 1) * Real.exp (-((p - 1) * D))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFnp hp1.le) hnn
    have heq : (p - 1) * cc ^ p * (A ^ (p - 1) * Real.exp (-((p - 1) * D))) =
        max lam 0 * M ^ (p - 1) + 1 := by
      rw [hApow, ← hBeq]
      ring
    linarith

end Komlos.Literature
