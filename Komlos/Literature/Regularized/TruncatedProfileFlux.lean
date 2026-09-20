import Komlos.Literature.Regularized.TruncatedProfileScalar

/-!
# The flux of the truncated profile `Φ_R = h_R ∘ F`

This file provides the first-order calculus of the truncated profile
`truncProfile p F R = h_R ∘ F` of `Komlos/Literature/Regularized/TruncatedProfile.lean`, and the
two-sided monotonicity estimates for its gradient, in the form needed for the global ellipticity
of the mollification `Ψ_p = Φ_R ∗ ρ`
(`Komlos/Literature/Regularized/TruncatedProfileElliptic.lean`, `REGULARIZED_ROUTE.md`,
Revision 2).

## The scalar-flux identity

For any scalar `g : ℝ → ℝ` the radial field `A_g(ξ) = g(F ξ) ∇F(ξ)` satisfies, for all `u, v`,

`⟪A_g u - A_g v, u - v⟫ = (g s - g t)(s - t) + g s · X + g t · Y`   (`inner_scalarFlux_sub`)

with `s = F u`, `t = F v`, `X = F v - ⟪∇F u, v⟫ ≥ 0` and `Y = F u - ⟪∇F v, u⟫ ≥ 0`.  The identity
uses only Euler's identity `⟪∇F ξ, ξ⟫ = F ξ`; the sign of `X` and `Y` is the subgradient
inequality `⟪∇F u, v⟫ ≤ F v` (`inner_gradient_le`).

Two instances matter: `g = id` gives `flux 2 F = ∇(F²/2)`, whose strong monotonicity and
Lipschitz bound are *unweighted* (they are the `p = 2` instances of
`IsSmoothStrictNorm.exists_pos_weighted_normSq_le_inner_flux_sub` and
`IsSmoothStrictNorm.exists_norm_flux_sub_le`, whose weight `(‖ξ‖+‖ζ‖)^{p-2}` is then `1`), and
`g = truncPowDeriv p R`, which gives `truncFlux p F R = ∇Φ_R`.  Comparing the two term by term
(`monotone_comparison_ge`, `monotone_comparison_le`) reduces every monotonicity estimate for
`∇Φ_R` to the *scalar* inequalities of
`Komlos/Literature/Regularized/TruncatedProfileScalar.lean`.

## Main results

* `truncFlux`, `hasGradientAt_truncProfile`, `continuous_truncFlux`,
  `hasWeakGradient_truncProfile`;
* the four two-sided bounds `inner_truncFlux_sub_ge_const` (`p ≤ 2`),
  `inner_truncFlux_sub_le_weight` (`p ≤ 2`), `inner_truncFlux_sub_ge_weight` (`2 ≤ p`),
  `inner_truncFlux_sub_le_const` (`2 ≤ p`), all in terms of
  `⟪flux 2 F u - flux 2 F v, u - v⟫`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The subgradient inequality -/

/-- **The subgradient inequality for a norm**: `⟪∇F u, v⟫ ≤ F v` at every point `u ≠ 0` where
`F` is differentiable.  The slope of `t ↦ F (u + t v)` at `0⁺` is at most `F v` by the triangle
inequality and `1`-homogeneity. -/
theorem inner_gradient_le {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {u : Euc d} (hu : u ≠ 0)
    (v : Euc d) : ⟪gradient F u, v⟫ ≤ F v := by
  have hF2 : ContDiffAt ℝ 2 F u := (hF.contDiffAt hu).of_le (WithTop.coe_le_coe.2 le_top)
  have hderiv0 := (eventually_hasDerivAt_line hF2 v).self_of_nhds
  have hzero : u + (0 : ℝ) • v = u := by module
  rw [hzero, fderiv_apply_eq_inner_gradient] at hderiv0
  have hderiv : HasDerivAt (fun s : ℝ => F (u + s • v)) (⟪gradient F u, v⟫) 0 := hderiv0
  set f : ℝ → ℝ := fun s => F (u + s • v) with hf
  have hslope : Tendsto (slope f 0) (𝓝[≠] (0 : ℝ)) (𝓝 (⟪gradient F u, v⟫)) :=
    hasDerivAt_iff_tendsto_slope.1 hderiv
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  refine le_of_tendsto (hslope.mono_left hsub) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : (0 : ℝ) < t := ht
  have htri : F (u + t • v) ≤ F u + t * F v := by
    have h := hF.map_add_le_add u (t • v)
    rwa [hF.homog t v, abs_of_pos htpos] at h
  have hslope_eq : slope f 0 t = (f t - f 0) / t := by rw [slope_def_field, sub_zero]
  have hf0 : f 0 = F u := by simp [hf]
  have hft : f t = F (u + t • v) := rfl
  rw [hslope_eq, div_le_iff₀ htpos, hf0, hft]
  linarith

/-! ### The scalar-flux identity and the comparison principle -/

/-- **The two-point expansion of a radial field** `A_g(ξ) = g(F ξ) ∇F ξ`. -/
theorem inner_scalarFlux_sub {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) (g : ℝ → ℝ)
    (u v : Euc d) :
    ⟪g (F u) • gradient F u - g (F v) • gradient F v, u - v⟫ =
      (g (F u) - g (F v)) * (F u - F v) + g (F u) * (F v - ⟪gradient F u, v⟫) +
        g (F v) * (F u - ⟪gradient F v, u⟫) := by
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, inner_sub_right,
    inner_sub_right, hF.euler_inner_gradient u, hF.euler_inner_gradient v]
  ring

/-- `flux 2 F` is the radial field of `g = id`. -/
theorem flux_two_eq {F : Euc d → ℝ} (ξ : Euc d) : flux 2 F ξ = F ξ • gradient F ξ := by
  rw [flux]
  norm_num

/-- The `p = 2` expansion `⟪∇(F²/2) u - ∇(F²/2) v, u - v⟫ = (s-t)² + s X + t Y`. -/
theorem inner_flux_two_sub {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) (u v : Euc d) :
    ⟪flux 2 F u - flux 2 F v, u - v⟫ =
      (F u - F v) * (F u - F v) + F u * (F v - ⟪gradient F u, v⟫) +
        F v * (F u - ⟪gradient F v, u⟫) := by
  simp only [flux_two_eq]
  exact inner_scalarFlux_sub hF (fun x => x) u v

/-- **Comparison of two radial fields, lower bound.** -/
theorem monotone_comparison_ge {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {g : ℝ → ℝ} {lam : ℝ}
    (hg0 : g 0 = 0) (u v : Euc d)
    (h1 : lam * (F u - F v) ^ 2 ≤ (g (F u) - g (F v)) * (F u - F v))
    (h2 : lam * F u ≤ g (F u)) (h3 : lam * F v ≤ g (F v)) :
    lam * ⟪flux 2 F u - flux 2 F v, u - v⟫ ≤
      ⟪g (F u) • gradient F u - g (F v) • gradient F v, u - v⟫ := by
  have e2 : lam * F u * (F v - ⟪gradient F u, v⟫) ≤ g (F u) * (F v - ⟪gradient F u, v⟫) := by
    rcases eq_or_ne u 0 with rfl | hu
    · rw [hF.map_zero, hg0]; simp
    · exact mul_le_mul_of_nonneg_right h2 (by linarith [inner_gradient_le hF hu v])
  have e3 : lam * F v * (F u - ⟪gradient F v, u⟫) ≤ g (F v) * (F u - ⟪gradient F v, u⟫) := by
    rcases eq_or_ne v 0 with rfl | hv
    · rw [hF.map_zero, hg0]; simp
    · exact mul_le_mul_of_nonneg_right h3 (by linarith [inner_gradient_le hF hv u])
  rw [inner_flux_two_sub hF u v, inner_scalarFlux_sub hF g u v]
  nlinarith [h1, e2, e3]

/-- **Comparison of two radial fields, upper bound.** -/
theorem monotone_comparison_le {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {g : ℝ → ℝ} {lam : ℝ}
    (hg0 : g 0 = 0) (u v : Euc d)
    (h1 : (g (F u) - g (F v)) * (F u - F v) ≤ lam * (F u - F v) ^ 2)
    (h2 : g (F u) ≤ lam * F u) (h3 : g (F v) ≤ lam * F v) :
    ⟪g (F u) • gradient F u - g (F v) • gradient F v, u - v⟫ ≤
      lam * ⟪flux 2 F u - flux 2 F v, u - v⟫ := by
  have e2 : g (F u) * (F v - ⟪gradient F u, v⟫) ≤ lam * F u * (F v - ⟪gradient F u, v⟫) := by
    rcases eq_or_ne u 0 with rfl | hu
    · rw [hF.map_zero, hg0]; simp
    · exact mul_le_mul_of_nonneg_right h2 (by linarith [inner_gradient_le hF hu v])
  have e3 : g (F v) * (F u - ⟪gradient F v, u⟫) ≤ lam * F v * (F u - ⟪gradient F v, u⟫) := by
    rcases eq_or_ne v 0 with rfl | hv
    · rw [hF.map_zero, hg0]; simp
    · exact mul_le_mul_of_nonneg_right h3 (by linarith [inner_gradient_le hF hv u])
  rw [inner_flux_two_sub hF u v, inner_scalarFlux_sub hF g u v]
  nlinarith [h1, e2, e3]

/-! ### Symmetrization of the scalar difference bounds -/

private theorem mul_sub_sq_of_diff_ge {g : ℝ → ℝ} {Λ : ℝ → ℝ → ℝ} (hsymm : ∀ x y, Λ x y = Λ y x)
    (h : ∀ τ σ : ℝ, 0 ≤ τ → τ ≤ σ → Λ σ τ * (σ - τ) ≤ g σ - g τ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : Λ s t * (s - t) ^ 2 ≤ (g s - g t) * (s - t) := by
  rcases le_total t s with hts | hst
  · have h1 := h t s ht hts
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s - t)]
  · have h1 := h s t hs hst
    rw [hsymm t s] at h1
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ t - s)]

private theorem mul_sub_sq_of_diff_le {g : ℝ → ℝ} {Λ : ℝ → ℝ → ℝ} (hsymm : ∀ x y, Λ x y = Λ y x)
    (h : ∀ τ σ : ℝ, 0 ≤ τ → τ ≤ σ → g σ - g τ ≤ Λ σ τ * (σ - τ))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : (g s - g t) * (s - t) ≤ Λ s t * (s - t) ^ 2 := by
  rcases le_total t s with hts | hst
  · have h1 := h t s ht hts
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s - t)]
  · have h1 := h s t hs hst
    rw [hsymm t s] at h1
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ t - s)]

/-! ### The flux of the truncated profile -/

section Flux

variable {p R : ℝ} {F : Euc d → ℝ}

/-- **The flux of the truncated profile**: `∇Φ_R(ξ) = h_R'(F ξ) ∇F(ξ)` (the value at `ξ = 0`
is `0`, since `h_R'(0) = 0`). -/
noncomputable def truncFlux (p : ℝ) (F : Euc d → ℝ) (R : ℝ) : Euc d → Euc d :=
  fun ξ => truncPowDeriv p R (F ξ) • gradient F ξ

theorem truncPowDeriv_zero (hp : 1 < p) (hR : 0 ≤ R) : truncPowDeriv p R 0 = 0 := by
  rw [truncPowDeriv_of_mem hR le_rfl hR, Real.zero_rpow (by intro hc; linarith : p - 1 ≠ 0)]

/-- Below the truncation level the flux of `Φ_R` is the flux of `F^p/p`. -/
theorem truncFlux_eq_flux (_hp : 1 < p) (hR : 0 ≤ R) (hF : IsSmoothStrictNorm F) {ξ : Euc d}
    (hξ : F ξ ≤ R) : truncFlux p F R ξ = flux p F ξ := by
  rw [truncFlux, flux, truncPowDeriv_of_mem hR (hF.nonneg ξ) hξ]

theorem truncFlux_zero (hp : 1 < p) (hR : 0 ≤ R) (hF : IsSmoothStrictNorm F) :
    truncFlux p F R (0 : Euc d) = 0 := by
  rw [truncFlux, hF.map_zero, truncPowDeriv_zero hp hR, zero_smul]

/-- The open set `{F < R}`, a neighbourhood of the origin. -/
private theorem isOpen_F_lt (hF : IsSmoothStrictNorm F) : IsOpen {x : Euc d | F x < R} :=
  isOpen_lt hF.continuous continuous_const

private theorem zero_mem_F_lt (hR : 0 < R) (hF : IsSmoothStrictNorm F) :
    (0 : Euc d) ∈ {x : Euc d | F x < R} := by
  simpa [hF.map_zero] using hR

/-- **`Φ_R` is differentiable everywhere, with gradient `truncFlux p F R`.**  Away from the
origin this is the chain rule; at the origin `Φ_R` agrees with `F^p/p` on a neighbourhood, and
the latter is differentiable there with vanishing gradient (paper Appendix A: `F^p ∈ C¹`). -/
theorem hasGradientAt_truncProfile (hp : 1 < p) (hR : 0 < R) (hF : IsSmoothStrictNorm F)
    (ξ : Euc d) : HasGradientAt (truncProfile p F R) (truncFlux p F R ξ) ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [truncFlux_zero hp hR.le hF]
    have heq : truncProfile p F R =ᶠ[𝓝 (0 : Euc d)] fun x => F x ^ p / p := by
      filter_upwards [(isOpen_F_lt (R := R) hF).mem_nhds (zero_mem_F_lt hR hF)] with x hx
      exact truncProfile_of_le hp hR.le hF (le_of_lt hx)
    have h0 : (p • innerSL ℝ (flux p F (0 : Euc d))) = 0 := by
      rw [flux_zero hp hF]
      ext w
      simp
    have h := hF.hasFDerivAt_rpow hp (0 : Euc d)
    rw [h0] at h
    have h2 : HasFDerivAt (fun x : Euc d => F x ^ p / p) (0 : Euc d →L[ℝ] ℝ) (0 : Euc d) := by
      have hd : HasDerivAt (fun s : ℝ => s / p) (1 / p) (F (0 : Euc d) ^ p) := by
        simpa using (hasDerivAt_id (F (0 : Euc d) ^ p)).div_const p
      have h2' := hd.comp_hasFDerivAt (0 : Euc d) h
      rwa [smul_zero] at h2' 
    rw [hasGradientAt_iff_hasFDerivAt]
    refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
    simpa using h2
  · have hg : HasGradientAt F (gradient F ξ) ξ :=
      ((hF.contDiffAt hξ).differentiableAt (by simp)).hasGradientAt
    have h := (hasDerivAt_truncPow (R := R) hp (F ξ)).comp_hasFDerivAt ξ
      (hasGradientAt_iff_hasFDerivAt.1 hg)
    rw [hasGradientAt_iff_hasFDerivAt, truncFlux, map_smul]
    exact h

theorem continuous_truncFlux (hp : 1 < p) (hR : 0 < R) (hF : IsSmoothStrictNorm F) :
    Continuous (truncFlux p F R) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have heq : truncFlux p F R =ᶠ[𝓝 (0 : Euc d)] flux p F := by
      filter_upwards [(isOpen_F_lt (R := R) hF).mem_nhds (zero_mem_F_lt hR hF)] with x hx
      exact truncFlux_eq_flux hp hR.le hF (le_of_lt hx)
    exact ((hF.continuous_flux' hp).continuousAt).congr heq.symm
  · have hF1 : ContDiffAt ℝ 1 F ξ := (hF.contDiffAt hξ).of_le (by exact_mod_cast le_top)
    have hfd : ContinuousAt (fderiv ℝ F) ξ :=
      (hF1.fderiv_right (m := 0) (by norm_num)).continuousAt
    have hgrad : ContinuousAt (gradient F) ξ :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.continuousAt.comp hfd
    exact (((continuous_truncPowDeriv hp).comp hF.continuous).continuousAt).smul hgrad

/-- A `C¹` function (with no support assumption) has its classical gradient as weak gradient. -/
theorem hasWeakGradient_of_hasGradientAt {f : Euc d → ℝ} {g : Euc d → Euc d}
    (hfc : Continuous f) (hgc : Continuous g) (hfg : ∀ x, HasGradientAt f (g x) x) :
    HasWeakGradient f g where
  locallyIntegrable := hfc.locallyIntegrable
  locallyIntegrable_grad := hgc.locallyIntegrable
  integral_mul_fderiv ψ hψ hψs v := by
    have hfd : ∀ x, fderiv ℝ f x v = inner ℝ (g x) v := fun x => by
      rw [fderiv_apply_eq_inner_gradient, (hfg x).gradient]
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hfv : Continuous fun x => fderiv ℝ f x v := by
      simp only [hfd]
      exact hgc.inner continuous_const
    have hψv : Continuous fun x => fderiv ℝ ψ x v :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hsuppψ : HasCompactSupport fun x => fderiv ℝ ψ x v := by
      refine (hψs.fderiv (𝕜 := ℝ)).mono ?_
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx ⊢
      intro hc
      exact hx (by rw [hc]; simp)
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v)
      (f := f) (g := ψ)
      ((hfv.mul hψ.continuous).integrable_of_hasCompactSupport hψs.mul_left)
      ((hfc.mul hψv).integrable_of_hasCompactSupport hsuppψ.mul_left)
      ((hfc.mul hψ.continuous).integrable_of_hasCompactSupport hψs.mul_left)
      (fun x _ => (hfg x).differentiableAt) (fun x _ => hψ1.differentiable one_ne_zero x)
    rw [h]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hfd])

theorem hasWeakGradient_truncProfile (hp : 1 < p) (hR : 0 < R) (hF : IsSmoothStrictNorm F) :
    HasWeakGradient (truncProfile p F R) (truncFlux p F R) :=
  hasWeakGradient_of_hasGradientAt (continuous_truncProfile hp hF)
    (continuous_truncFlux hp hR hF) (hasGradientAt_truncProfile hp hR hF)

end Flux

/-! ### The four pointwise monotonicity bounds -/

section Bounds

variable {p R : ℝ} {F : Euc d → ℝ}

/-- `1 < p ≤ 2`: `Φ_R` is uniformly convex, with the constant of `(p-1)R^{p-2} · F²/2`. -/
theorem inner_truncFlux_sub_ge_const (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (u v : Euc d) :
    (p - 1) * R ^ (p - 2) * ⟪flux 2 F u - flux 2 F v, u - v⟫ ≤
      ⟪truncFlux p F R u - truncFlux p F R v, u - v⟫ := by
  refine monotone_comparison_ge hF (truncPowDeriv_zero hp hR.le) u v ?_
    (le_truncPowDeriv_const hp hp2 hR (hF.nonneg u))
    (le_truncPowDeriv_const hp hp2 hR (hF.nonneg v))
  exact mul_sub_sq_of_diff_ge (Λ := fun _ _ => (p - 1) * R ^ (p - 2)) (fun _ _ => rfl)
    (fun τ σ hτ hτσ => le_truncPowDeriv_sub_const hp hp2 hR hτ hτσ) (hF.nonneg u) (hF.nonneg v)

/-- `2 ≤ p`: the Lipschitz bound for `∇Φ_R`, with the constant of `(p-1)R^{p-2} · F²/2`. -/
theorem inner_truncFlux_sub_le_const (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (u v : Euc d) :
    ⟪truncFlux p F R u - truncFlux p F R v, u - v⟫ ≤
      (p - 1) * R ^ (p - 2) * ⟪flux 2 F u - flux 2 F v, u - v⟫ := by
  refine monotone_comparison_le hF (truncPowDeriv_zero hp hR.le) u v ?_
    (truncPowDeriv_le_const hp hp2 hR (hF.nonneg u))
    (truncPowDeriv_le_const hp hp2 hR (hF.nonneg v))
  exact mul_sub_sq_of_diff_le (Λ := fun _ _ => (p - 1) * R ^ (p - 2)) (fun _ _ => rfl)
    (fun τ σ hτ hτσ => truncPowDeriv_sub_le_const hp hp2 hR hτ hτσ) (hF.nonneg u) (hF.nonneg v)

/-- `2 ≤ p`: the degenerate lower bound, with the weight `min(W(F u), W(F v))`,
`W(σ) = min(σ, R)^{p-2}`. -/
theorem inner_truncFlux_sub_ge_weight (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (u v : Euc d) :
    min (truncWeight p R (F u)) (truncWeight p R (F v)) *
        ⟪flux 2 F u - flux 2 F v, u - v⟫ ≤
      ⟪truncFlux p F R u - truncFlux p F R v, u - v⟫ := by
  have hmu : min (truncWeight p R (F u)) (truncWeight p R (F v)) * F u ≤
      truncPowDeriv p R (F u) :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (hF.nonneg u)).trans
      (weight_le_truncPowDeriv hp hp2 hR (hF.nonneg u))
  have hmv : min (truncWeight p R (F u)) (truncWeight p R (F v)) * F v ≤
      truncPowDeriv p R (F v) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (hF.nonneg v)).trans
      (weight_le_truncPowDeriv hp hp2 hR (hF.nonneg v))
  refine monotone_comparison_ge hF (truncPowDeriv_zero hp hR.le) u v ?_ hmu hmv
  exact mul_sub_sq_of_diff_ge
    (Λ := fun x y => min (truncWeight p R x) (truncWeight p R y)) (fun x y => min_comm _ _)
    (fun τ σ hτ hτσ => weight_le_truncPowDeriv_sub hp hp2 hR hτ hτσ) (hF.nonneg u) (hF.nonneg v)

/-- `1 < p ≤ 2`: the singular upper bound, with the weight `W(F u) + W(F v)`. -/
theorem inner_truncFlux_sub_le_weight (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (u v : Euc d) :
    ⟪truncFlux p F R u - truncFlux p F R v, u - v⟫ ≤
      (truncWeight p R (F u) + truncWeight p R (F v)) *
        ⟪flux 2 F u - flux 2 F v, u - v⟫ := by
  have hwu : 0 ≤ truncWeight p R (F u) := truncWeight_nonneg hR.le (hF.nonneg u)
  have hwv : 0 ≤ truncWeight p R (F v) := truncWeight_nonneg hR.le (hF.nonneg v)
  have hmu : truncPowDeriv p R (F u) ≤
      (truncWeight p R (F u) + truncWeight p R (F v)) * F u := by
    refine (truncPowDeriv_le_weight hp hp2 hR (hF.nonneg u)).trans ?_
    have := mul_le_mul_of_nonneg_right (by linarith : truncWeight p R (F u) ≤
      truncWeight p R (F u) + truncWeight p R (F v)) (hF.nonneg u)
    linarith
  have hmv : truncPowDeriv p R (F v) ≤
      (truncWeight p R (F u) + truncWeight p R (F v)) * F v := by
    refine (truncPowDeriv_le_weight hp hp2 hR (hF.nonneg v)).trans ?_
    have := mul_le_mul_of_nonneg_right (by linarith : truncWeight p R (F v) ≤
      truncWeight p R (F u) + truncWeight p R (F v)) (hF.nonneg v)
    linarith
  refine monotone_comparison_le hF (truncPowDeriv_zero hp hR.le) u v ?_ hmu hmv
  exact mul_sub_sq_of_diff_le
    (Λ := fun x y => truncWeight p R x + truncWeight p R y) (fun x y => add_comm _ _)
    (fun τ σ hτ hτσ => truncPowDeriv_sub_le_weight hp hp2 hR hτ hτσ) (hF.nonneg u) (hF.nonneg v)

end Bounds

end Komlos.Literature.Regularized
