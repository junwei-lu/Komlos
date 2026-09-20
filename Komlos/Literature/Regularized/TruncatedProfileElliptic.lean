import Komlos.Literature.Regularized.TruncatedProfileMollify

/-!
# Global ellipticity of the mollified truncated profile, and `IsRegProfile`

This file completes step 3 of the profile construction of `REGULARIZED_ROUTE.md`,
Revision 2: from the mollified truncated profile `Ψ_p = Φ_R ∗ ρ_ε`
(`truncSmoothedProfile`, `Komlos/Literature/Regularized/TruncatedProfile.lean`) it builds the
exponent-`2` profile

`Ψ(q) = Ψ_p((2/p) q)`  (`regProfile`)

and proves `IsRegProfile Ψ`.

## The route to the ellipticity of `D²Ψ`

`D²Φ_R = h_R''(F) ∇F ⊗ ∇F + h_R'(F) D²F` is *not* two-sidedly bounded: for `p < 2` it blows up
like `|q|^{p-2}` at the origin and for `p > 2` it degenerates there.  Both defects are repaired
by the mollification, but differentiating under the convolution integral at the singularity is
not legitimate.  Following `REGULARIZED_ROUTE.md` we therefore work with *difference*
inequalities for `∇Ψ_p`, which pass through the convolution by integration against `ρ`, and only
then pass to the derivative:

* `inner_fderiv_gradient_lower_of_monotone`: strong monotonicity
  `c ‖q - q'‖² ≤ ⟪∇Ψ q - ∇Ψ q', q - q'⟫` implies `c ‖ξ‖² ≤ ⟪D(∇Ψ)(q) ξ, ξ⟫`;
* `inner_fderiv_gradient_upper_of_monotone`: `⟪∇Ψ q - ∇Ψ q', q - q'⟫ ≤ C ‖q - q'‖²` implies
  `⟪D(∇Ψ)(q) ξ, ξ⟫ ≤ C ‖ξ‖²` (and `inner_fderiv_gradient_upper_of_lipschitz` is the variant
  taking the *norm* Lipschitz bound).

All are proved here (the slope of `t ↦ ⟪∇Ψ(q + tξ), ξ⟫` at `t = 0`), and the two difference
inequalities for `Ψ_p` themselves are proved in
`Komlos/Literature/Regularized/TruncatedProfileScalar.lean` (scalar bounds for `h_R'`),
`Komlos/Literature/Regularized/TruncatedProfileFlux.lean` (two-sided monotonicity of
`∇Φ_R` against `∇(F²/2)`) and `Komlos/Literature/Regularized/TruncatedProfileMollify.lean`
(integration against the kernel `ρ`, which repairs the degeneracy at the origin for `p > 2`
and the singularity there for `p < 2`).

## Transfer to the dilated profile

`IsRegProfile` is stable under `q ↦ Ψ(c q)` (`isRegProfile_comp_smul`).  The gradient chain rule
`∇(Ψ ∘ (c •))(q) = c ∇Ψ(c q)` (`gradient_comp_smul`) turns both difference inequalities into
difference inequalities with the constants multiplied by `c²`, so no second-order chain rule is
needed.

## Main results

* `isRegProfile_of_gradient_bounds`, `isRegProfile_of_gradient_inner_bounds`: the two
  constructors of `IsRegProfile` from smoothness, evenness, convexity and the two difference
  inequalities (in norm resp. inner-product form);
* `exists_strongly_monotone_gradient_truncSmoothedProfile`,
  `exists_upper_monotone_gradient_truncSmoothedProfile`,
  `exists_lipschitz_gradient_truncSmoothedProfile`: the two-sided ellipticity of `∇Ψ_p`;
* `isRegProfile_truncSmoothedProfile : IsRegProfile (truncSmoothedProfile p F R ρ)`;
* `regProfile p F R ρ = fun q => Ψ_p ((2/p) q)` and
  `isRegProfile_regProfile : IsRegProfile (regProfile p F R ρ)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Smoothness of the gradient -/

/-- The gradient of a `C^∞` function is `C^∞` (the `IsRegProfile`-free version of
`IsRegProfile.contDiff_gradient`). -/
theorem contDiff_gradient_of_contDiff {Ψ : Euc d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (gradient Ψ) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ Ψ) := (contDiff_infty_iff_fderiv.1 hΨ).2
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp hfd

/-- The derivative of `t ↦ ⟪∇Ψ (a + t • e), z⟫` (the `IsRegProfile`-free version of
`IsRegProfile.hasDerivAt_inner_gradient_line`). -/
theorem hasDerivAt_inner_gradient_line' {Ψ : Euc d → ℝ}
    (hg : Differentiable ℝ (gradient Ψ)) (a e z : Euc d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪gradient Ψ (a + s • e), z⟫)
      (⟪fderiv ℝ (gradient Ψ) (a + t • e) e, z⟫) t := by
  have hline : HasDerivAt (fun s : ℝ => a + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add a
  have hcomp := (hg (a + t • e)).hasFDerivAt.comp_hasDerivAt t hline
  have hgd : HasDerivAt (fun s : ℝ => gradient Ψ (a + s • e))
      (fderiv ℝ (gradient Ψ) (a + t • e) e) t := by
    simpa only [Function.comp_def] using hcomp
  simpa using hgd.inner ℝ (hasDerivAt_const t z)

/-! ### From difference inequalities to the quadratic form of `D(∇Ψ)` -/

/-- **Strong monotonicity of `∇Ψ` gives the lower ellipticity bound.**  For `t > 0` the
monotonicity inequality at the pair `(q + tξ, q)` says that the slope at `0` of
`f(t) = ⟪∇Ψ(q + tξ), ξ⟫` is at least `c ‖ξ‖²`; letting `t ↓ 0` gives `f'(0)`, which is
`⟪D(∇Ψ)(q) ξ, ξ⟫`. -/
theorem inner_fderiv_gradient_lower_of_monotone {Ψ : Euc d → ℝ}
    (hg : Differentiable ℝ (gradient Ψ)) {c : ℝ}
    (hmono : ∀ q q' : Euc d, c * ‖q - q'‖ ^ 2 ≤ ⟪gradient Ψ q - gradient Ψ q', q - q'⟫)
    (q ξ : Euc d) : c * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫ := by
  set f : ℝ → ℝ := fun s => ⟪gradient Ψ (q + s • ξ), ξ⟫ with hf
  have hderiv : HasDerivAt f (⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫) 0 := by
    have h := hasDerivAt_inner_gradient_line' hg q ξ ξ 0
    simp only [zero_smul, add_zero] at h
    exact h
  have hslope : Tendsto (slope f 0) (𝓝[≠] (0 : ℝ)) (𝓝 (⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫)) :=
    hasDerivAt_iff_tendsto_slope.1 hderiv
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  refine ge_of_tendsto (hslope.mono_left hsub) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : (0 : ℝ) < t := ht
  have hkey := hmono (q + t • ξ) q
  have hsubq : q + t • ξ - q = t • ξ := by abel
  rw [hsubq, norm_smul, mul_pow, Real.norm_of_nonneg htpos.le, real_inner_smul_right,
    inner_sub_left] at hkey
  have hf0 : f 0 = ⟪gradient Ψ q, ξ⟫ := by simp [hf]
  have hft : f t = ⟪gradient Ψ (q + t • ξ), ξ⟫ := rfl
  have hslope_eq : slope f 0 t = (f t - f 0) / t := by
    rw [slope_def_field, sub_zero]
  rw [hslope_eq, hf0, hft, le_div_iff₀ htpos]
  nlinarith [hkey]

/-- **A Lipschitz gradient gives the upper ellipticity bound.** -/
theorem inner_fderiv_gradient_upper_of_lipschitz {Ψ : Euc d → ℝ}
    (hg : Differentiable ℝ (gradient Ψ)) {C : ℝ}
    (hlip : ∀ q q' : Euc d, ‖gradient Ψ q - gradient Ψ q'‖ ≤ C * ‖q - q'‖)
    (q ξ : Euc d) : ⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫ ≤ C * ‖ξ‖ ^ 2 := by
  set f : ℝ → ℝ := fun s => ⟪gradient Ψ (q + s • ξ), ξ⟫ with hf
  have hderiv : HasDerivAt f (⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫) 0 := by
    have h := hasDerivAt_inner_gradient_line' hg q ξ ξ 0
    simp only [zero_smul, add_zero] at h
    exact h
  have hslope : Tendsto (slope f 0) (𝓝[≠] (0 : ℝ)) (𝓝 (⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫)) :=
    hasDerivAt_iff_tendsto_slope.1 hderiv
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  refine le_of_tendsto (hslope.mono_left hsub) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : (0 : ℝ) < t := ht
  have hkey := hlip (q + t • ξ) q
  have hsubq : q + t • ξ - q = t • ξ := by abel
  rw [hsubq, norm_smul, Real.norm_of_nonneg htpos.le] at hkey
  have hcs : ⟪gradient Ψ (q + t • ξ) - gradient Ψ q, ξ⟫ ≤
      ‖gradient Ψ (q + t • ξ) - gradient Ψ q‖ * ‖ξ‖ := real_inner_le_norm _ _
  rw [inner_sub_left] at hcs
  have hf0 : f 0 = ⟪gradient Ψ q, ξ⟫ := by simp [hf]
  have hft : f t = ⟪gradient Ψ (q + t • ξ), ξ⟫ := rfl
  have hslope_eq : slope f 0 t = (f t - f 0) / t := by
    rw [slope_def_field, sub_zero]
  rw [hslope_eq, hf0, hft, div_le_iff₀ htpos]
  nlinarith [norm_nonneg ξ, norm_nonneg (gradient Ψ (q + t • ξ) - gradient Ψ q)]

/-- **An upper monotonicity bound gives the upper ellipticity bound.**  This is the mirror
image of `inner_fderiv_gradient_lower_of_monotone`: the slope at `0` of
`f(t) = ⟪∇Ψ(q + tξ), ξ⟫` is at most `C ‖ξ‖²`.  Unlike
`inner_fderiv_gradient_upper_of_lipschitz` it needs only the *inner-product* form of the
difference inequality, which is what the mollification of `Φ_R` produces directly. -/
theorem inner_fderiv_gradient_upper_of_monotone {Ψ : Euc d → ℝ}
    (hg : Differentiable ℝ (gradient Ψ)) {C : ℝ}
    (hmono : ∀ q q' : Euc d, ⟪gradient Ψ q - gradient Ψ q', q - q'⟫ ≤ C * ‖q - q'‖ ^ 2)
    (q ξ : Euc d) : ⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫ ≤ C * ‖ξ‖ ^ 2 := by
  set f : ℝ → ℝ := fun s => ⟪gradient Ψ (q + s • ξ), ξ⟫ with hf
  have hderiv : HasDerivAt f (⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫) 0 := by
    have h := hasDerivAt_inner_gradient_line' hg q ξ ξ 0
    simp only [zero_smul, add_zero] at h
    exact h
  have hslope : Tendsto (slope f 0) (𝓝[≠] (0 : ℝ)) (𝓝 (⟪fderiv ℝ (gradient Ψ) q ξ, ξ⟫)) :=
    hasDerivAt_iff_tendsto_slope.1 hderiv
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  refine le_of_tendsto (hslope.mono_left hsub) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : (0 : ℝ) < t := ht
  have hkey := hmono (q + t • ξ) q
  have hsubq : q + t • ξ - q = t • ξ := by abel
  rw [hsubq, norm_smul, mul_pow, Real.norm_of_nonneg htpos.le, real_inner_smul_right,
    inner_sub_left] at hkey
  have hf0 : f 0 = ⟪gradient Ψ q, ξ⟫ := by simp [hf]
  have hft : f t = ⟪gradient Ψ (q + t • ξ), ξ⟫ := rfl
  have hslope_eq : slope f 0 t = (f t - f 0) / t := by
    rw [slope_def_field, sub_zero]
  rw [hslope_eq, hf0, hft, div_le_iff₀ htpos]
  nlinarith [hkey]

/-- **The constructor of `IsRegProfile` from two-sided monotonicity inequalities.**  Both
bounds are in inner-product form; this is what the mollification of `Φ_R` produces (the
*norm* Lipschitz bound is then recovered from `IsRegProfileWith.lipschitz_gradient`). -/
theorem isRegProfile_of_gradient_inner_bounds {Ψ : Euc d → ℝ} (hsmooth : ContDiff ℝ ∞ Ψ)
    (heven : ∀ q, Ψ (-q) = Ψ q) (hconv : ConvexOn ℝ univ Ψ)
    (hmono : ∃ c : ℝ, 0 < c ∧ ∀ q q' : Euc d,
      c * ‖q - q'‖ ^ 2 ≤ ⟪gradient Ψ q - gradient Ψ q', q - q'⟫)
    (hupper : ∃ C : ℝ, ∀ q q' : Euc d,
      ⟪gradient Ψ q - gradient Ψ q', q - q'⟫ ≤ C * ‖q - q'‖ ^ 2) :
    IsRegProfile Ψ := by
  obtain ⟨c, hc, hmono⟩ := hmono
  obtain ⟨C, hupper⟩ := hupper
  have hgd : Differentiable ℝ (gradient Ψ) :=
    (contDiff_gradient_of_contDiff hsmooth).differentiable (by simp)
  exact
    { contDiff := hsmooth
      even := heven
      convexOn := hconv
      elliptic := ⟨c, C, hc, fun q ξ =>
        ⟨inner_fderiv_gradient_lower_of_monotone hgd hmono q ξ,
          inner_fderiv_gradient_upper_of_monotone hgd hupper q ξ⟩⟩ }

/-- **The constructor of `IsRegProfile` from difference inequalities.** -/
theorem isRegProfile_of_gradient_bounds {Ψ : Euc d → ℝ} (hsmooth : ContDiff ℝ ∞ Ψ)
    (heven : ∀ q, Ψ (-q) = Ψ q) (hconv : ConvexOn ℝ univ Ψ)
    (hmono : ∃ c : ℝ, 0 < c ∧ ∀ q q' : Euc d,
      c * ‖q - q'‖ ^ 2 ≤ ⟪gradient Ψ q - gradient Ψ q', q - q'⟫)
    (hlip : ∃ C : ℝ, ∀ q q' : Euc d, ‖gradient Ψ q - gradient Ψ q'‖ ≤ C * ‖q - q'‖) :
    IsRegProfile Ψ := by
  obtain ⟨c, hc, hmono⟩ := hmono
  obtain ⟨C, hlip⟩ := hlip
  have hgd : Differentiable ℝ (gradient Ψ) :=
    (contDiff_gradient_of_contDiff hsmooth).differentiable (by simp)
  exact
    { contDiff := hsmooth
      even := heven
      convexOn := hconv
      elliptic := ⟨c, C, hc, fun q ξ =>
        ⟨inner_fderiv_gradient_lower_of_monotone hgd hmono q ξ,
          inner_fderiv_gradient_upper_of_lipschitz hgd hlip q ξ⟩⟩ }

/-! ### The two ellipticity inputs for `Ψ_p = Φ_R ∗ ρ_ε` -/

section Ellipticity

variable {p R ε : ℝ} {F ρ : Euc d → ℝ}

/-- **Strong monotonicity of `∇Ψ_p`** (`REGULARIZED_ROUTE.md`, Revision 2, *global two-sided
ellipticity*, lower half).

The flux `a = ∇Φ_R` satisfies a two-sided weighted monotonicity estimate against the flux of
`F²/2` (`Komlos/Literature/Regularized/TruncatedProfileFlux.lean`), whose own monotonicity is
unweighted.  For `1 < p ≤ 2` the weight is bounded below by `(p-1)R^{p-2}`, so `Φ_R` is already
uniformly convex and the mollification changes nothing
(`exists_strongly_monotone_le_two`).  For `2 ≤ p` the weight `min(W(F u), W(F v))` degenerates
at the origin; there the kernel mass of a small `F`-ball around `q` (and around `q'`) is small,
uniformly in `q`, which supplies a positive constant (`exists_strongly_monotone_two_le`).
The inequality is proved throughout as a *difference* inequality, integrated against `ρ` —
never by differentiating `Φ_R` twice. -/
theorem exists_strongly_monotone_gradient_truncSmoothedProfile (hp : 1 < p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ q q' : Euc d,
      c * ‖q - q'‖ ^ 2 ≤
        ⟪gradient (truncSmoothedProfile p F R ρ) q -
          gradient (truncSmoothedProfile p F R ρ) q', q - q'⟫ := by
  rcases isEmpty_or_nonempty (Fin d) with hemp | hne
  · refine ⟨1, one_pos, fun q q' => ?_⟩
    have hqq : q = q' := Subsingleton.elim q q'
    subst hqq
    simp
  · have hd : 0 < d := Fin.pos_iff_nonempty.2 hne
    rcases le_total p 2 with h2 | h2
    · exact exists_strongly_monotone_le_two hp h2 hR hF hρ
    · exact exists_strongly_monotone_two_le hd hp h2 hR hF hρ

/-- **The upper ellipticity bound for `∇Ψ_p`, in inner-product form.**  For `2 ≤ p` the flux
`∇Φ_R` is already globally Lipschitz with constant `(p-1)R^{p-2}` times that of `∇(F²/2)`
(`exists_lipschitz_two_le`).  For `p < 2` the weight `W(F u) + W(F v)` is singular at the
origin, but `W ∘ F ≲ ‖·‖^{p-2}` is locally integrable (`p - 2 > -1 ≥ -d`), so its mollification
is bounded uniformly (`exists_lipschitz_lt_two`). -/
theorem exists_upper_monotone_gradient_truncSmoothedProfile (hp : 1 < p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q q' : Euc d,
      ⟪gradient (truncSmoothedProfile p F R ρ) q -
          gradient (truncSmoothedProfile p F R ρ) q', q - q'⟫ ≤ C * ‖q - q'‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin d) with hemp | hne
  · refine ⟨0, le_rfl, fun q q' => ?_⟩
    have hqq : q = q' := Subsingleton.elim q q'
    subst hqq
    simp
  · have hd : 0 < d := Fin.pos_iff_nonempty.2 hne
    by_cases h2 : 2 ≤ p
    · exact exists_lipschitz_two_le hp h2 hR hF hρ
    · exact exists_lipschitz_lt_two hd hp (not_le.1 h2) hR hF hρ

/-- **`Ψ_p = Φ_R ∗ ρ_ε` is a regularized profile.** -/
theorem isRegProfile_truncSmoothedProfile (hp : 1 < p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    IsRegProfile (truncSmoothedProfile p F R ρ) := by
  obtain ⟨C, -, hupper⟩ := exists_upper_monotone_gradient_truncSmoothedProfile hp hR hF hρ
  exact isRegProfile_of_gradient_inner_bounds (contDiff_truncSmoothedProfile hp hF hρ)
    (truncSmoothedProfile_even hF hρ) (convexOn_truncSmoothedProfile hp hR.le hF hρ)
    (exists_strongly_monotone_gradient_truncSmoothedProfile hp hR hF hρ) ⟨C, hupper⟩

/-- **Lipschitz continuity of `∇Ψ_p`** (`REGULARIZED_ROUTE.md`, Revision 2, *global two-sided
ellipticity*, upper half).  The *norm* form follows from the inner-product form
(`exists_upper_monotone_gradient_truncSmoothedProfile`) once `Ψ_p` is known to be a regularized
profile, because the symmetric positive semidefinite `D(∇Ψ_p)` has its operator norm controlled
by its quadratic form (`IsRegProfileWith.lipschitz_gradient`). -/
theorem exists_lipschitz_gradient_truncSmoothedProfile (hp : 1 < p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q q' : Euc d,
      ‖gradient (truncSmoothedProfile p F R ρ) q -
        gradient (truncSmoothedProfile p F R ρ) q'‖ ≤ C * ‖q - q'‖ := by
  obtain ⟨C, hC0, hlip, -⟩ :=
    (isRegProfile_truncSmoothedProfile hp hR hF hρ).exists_lipschitz_gradient
  exact ⟨C, hC0, hlip⟩

end Ellipticity

/-! ### Dilation -/

/-- The gradient chain rule for a dilation: `∇(Ψ ∘ (c •))(q) = c ∇Ψ(c q)`. -/
theorem hasGradientAt_comp_smul {Ψ : Euc d → ℝ} (hΨ : Differentiable ℝ Ψ) (c : ℝ) (q : Euc d) :
    HasGradientAt (fun x => Ψ (c • x)) (c • gradient Ψ (c • q)) q := by
  have hL : HasFDerivAt (fun x : Euc d => c • x) (c • ContinuousLinearMap.id ℝ (Euc d)) q :=
    (hasFDerivAt_id q).const_smul c
  have hΨd : HasFDerivAt Ψ ((InnerProductSpace.toDual ℝ (Euc d)) (gradient Ψ (c • q))) (c • q) :=
    hasGradientAt_iff_hasFDerivAt.1 (hΨ (c • q)).hasGradientAt
  have hcomp := hΨd.comp q hL
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hcomp.congr_fderiv ?_
  ext ξ
  simp

theorem gradient_comp_smul {Ψ : Euc d → ℝ} (hΨ : Differentiable ℝ Ψ) (c : ℝ) (q : Euc d) :
    gradient (fun x => Ψ (c • x)) q = c • gradient Ψ (c • q) :=
  (hasGradientAt_comp_smul hΨ c q).gradient

/-- **`IsRegProfile` is stable under dilations** `q ↦ Ψ(c q)` with `c > 0`.  The two difference
inequalities transfer with their constants multiplied by `c²`; no second-order chain rule is
needed. -/
theorem isRegProfile_comp_smul {Ψ : Euc d → ℝ} (hΨ : IsRegProfile Ψ) {c : ℝ} (hc : 0 < c) :
    IsRegProfile fun q => Ψ (c • q) := by
  obtain ⟨c₀, C₀, hpk⟩ := hΨ.exists_isRegProfileWith
  have hd : Differentiable ℝ Ψ := hΨ.differentiable
  have hgrad : ∀ q : Euc d, gradient (fun x => Ψ (c • x)) q = c • gradient Ψ (c • q) :=
    fun q => gradient_comp_smul hd c q
  refine isRegProfile_of_gradient_bounds ?_ ?_ ?_
    ⟨c₀ * c ^ 2, mul_pos hpk.c_pos (by positivity), ?_⟩ ⟨C₀ * c ^ 2, ?_⟩
  · exact hΨ.contDiff.comp ((contDiff_id (E := Euc d) (n := ∞)).const_smul c)
  · intro q
    rw [smul_neg, hΨ.even]
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hmain := hΨ.convexOn.2 (mem_univ (c • x)) (mem_univ (c • y)) ha hb hab
    have heq : a • (c • x) + b • (c • y) = c • (a • x + b • y) := by module
    rwa [heq] at hmain
  · intro q q'
    have hkey := hpk.inner_gradient_sub (c • q) (c • q')
    have hs : c • q - c • q' = c • (q - q') := by module
    rw [hs, norm_smul, mul_pow, Real.norm_of_nonneg hc.le, real_inner_smul_right] at hkey
    rw [hgrad, hgrad, ← smul_sub, real_inner_smul_left]
    have hrw : c₀ * c ^ 2 * ‖q - q'‖ ^ 2 = c₀ * (c ^ 2 * ‖q - q'‖ ^ 2) := by ring
    rw [hrw]
    exact hkey
  · intro q q'
    have hkey := hpk.lipschitz_gradient (c • q) (c • q')
    have hs : c • q - c • q' = c • (q - q') := by module
    rw [hs, norm_smul, Real.norm_of_nonneg hc.le] at hkey
    rw [hgrad, hgrad, ← smul_sub, norm_smul, Real.norm_of_nonneg hc.le]
    have hmul := mul_le_mul_of_nonneg_left hkey hc.le
    nlinarith [hmul]

/-! ### The exponent-`2` profile -/

/-- **The exponent-`2` regularized profile** of `REGULARIZED_ROUTE.md`, Revision 2:
`Ψ(q) = Ψ_p((2/p) q)`.

The dilation is dictated by the substitution `w = u^{p/2}`: with `u = w^{2/p}` one has
`∇u/u = (2/p) ∇w/w`, hence `u^p Ψ_p(∇u/u) = w² Ψ(∇w/w)`, and the entropy transforms as
`(κ'/p) u^p log u = (2κ'/p²) w² log w`.  So a `p`-energy with entropy weight `κ'` becomes the
exponent-`2` energy `regEnergy 2 κ Ψ` with `κ = 4κ'/p²`, i.e. `κ' = p² κ / 4`
(see `Komlos/Literature/Regularized/ScalarLimit.lean`). -/
noncomputable def regProfile (p : ℝ) (F : Euc d → ℝ) (R : ℝ) (ρ : Euc d → ℝ) : Euc d → ℝ :=
  fun q => truncSmoothedProfile p F R ρ ((2 / p) • q)

/-- `Ψ((p/2) q) = Ψ_p(q)`: the dilation in `regProfile` is inverted by the dilation `p/2`
coming from `∇w/w = (p/2) ∇u/u`. -/
theorem regProfile_smul {p : ℝ} (hp : p ≠ 0) (F : Euc d → ℝ) (R : ℝ) (ρ : Euc d → ℝ)
    (q : Euc d) : regProfile p F R ρ ((p / 2) • q) = truncSmoothedProfile p F R ρ q := by
  have h : (2 / p) * (p / 2) = 1 := by field_simp
  simp only [regProfile, smul_smul, h, one_smul]

/-- **The lower profile comparison at the dilated argument, `1 < p ≤ 2`**:
`F(q)^p/p ≤ Ψ((p/2) q)`.  Combined with `u^p F(∇u/u)^p/p = F(∇u)^p/p` this is the inequality
behind the lower scalar limit for `p ≤ 2`. -/
theorem rpow_div_le_regProfile {p R ε : ℝ} {F ρ : Euc d → ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hR : 0 < R) (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) (q : Euc d) :
    F q ^ p / p ≤ regProfile p F R ρ ((p / 2) • q) := by
  rw [regProfile_smul (by linarith : p ≠ 0)]
  exact (rpow_div_le_truncProfile hp hp2 hR hF q).trans
    (truncProfile_le_truncSmoothedProfile hp hR.le hF hρ q)

/-- **The upper profile comparison at the dilated argument, `2 ≤ p`**:
`Ψ((p/2) q) ≤ (F q + M ε)^p/p` with `M ≥ 0` depending only on `F`.  This is the inequality
behind the upper scalar limit for `p ≥ 2`. -/
theorem exists_regProfile_le {p : ℝ} {F : Euc d → ℝ} (hp : 1 < p) (hp2 : 2 ≤ p)
    (hF : IsSmoothStrictNorm F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 0 < R → ∀ (ρ : Euc d → ℝ) (ε : ℝ), IsMollifier ρ ε →
      ∀ q : Euc d, regProfile p F R ρ ((p / 2) • q) ≤ (F q + M * ε) ^ p / p := by
  obtain ⟨M, hM0, hM⟩ := exists_truncSmoothedProfile_le (p := p) hp hF
  refine ⟨M, hM0, fun R hR ρ ε hρ q => ?_⟩
  rw [regProfile_smul (by linarith : p ≠ 0)]
  refine (hM R hR.le ρ ε hρ q).trans (truncPow_le_rpow_div hp hp2 hR ?_)
  exact add_nonneg (hF.nonneg q) (mul_nonneg hM0 hρ.eps_pos.le)

/-- **The exponent-`2` profile built from `F`, `p`, `R`, `ρ` is a regularized profile.** -/
theorem isRegProfile_regProfile {p R ε : ℝ} {F ρ : Euc d → ℝ} (hp : 1 < p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    IsRegProfile (regProfile p F R ρ) :=
  isRegProfile_comp_smul (isRegProfile_truncSmoothedProfile hp hR hF hρ)
    (by positivity : (0 : ℝ) < 2 / p)

end Komlos.Literature.Regularized
