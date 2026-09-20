import Komlos.Literature.PLaplacian.Regularity

/-!
# Korevaar's concavity maximum principle: the interior second-order step

This file carries the **second-order half** of Korevaar's *concavity maximum principle*, the
method behind Mosconi–Riey–Squassina 2024, Theorem 1.1 (log-concavity of the first anisotropic
`p`-Laplacian eigenfunction).  `LogConcaveAux.lean` imports it and supplies the zeroth- and
first-order half (blow-up of `v = -log φ` at `∂K`, vanishing of the concavity function on the
diagonal, the passage from midpoint convexity to convexity).

Write `v` for the log-transform `-log φ` of the eigenfunction and

  `C(x, y) = v (midpoint x y) - (v x + v y) / 2`   (`concavityFn`)

for Korevaar's concavity function, so that `v` is midpoint convex exactly when `C ≤ 0`.

## Main results

* `concavityFn`, `concavityFn_self`, `concavityFn_comm`,
  `gradient_eq_of_isLocalMax_concavityFn` — the concavity function, its vanishing on the
  diagonal, its symmetry, and the **first-order conditions** at an interior maximum in one
  variable (`∇v (midpoint x y) = ∇v x`).  These were moved here from `LogConcaveAux.lean` so
  that the second-order material below can be stated.
* `Korevaar.isLocalMax_left`, `Korevaar.isLocalMax_right`,
  `Korevaar.gradient_eq_of_isLocalMax_pair` — at an interior local maximum of `C` on the *pair*
  `(x, y)` the three gradients `∇v x`, `∇v y`, `∇v (midpoint x y)` coincide, so the reaction term
  `λ + (p-1) F(∇v)^p` of the transformed equation takes the same value at all three points.
* `Korevaar.inner_hessian_midpoint_le_of_isLocalMax` — the **second-order conditions** at such a
  maximum, i.e. Korevaar's Loewner inequality
  `D²v(m)[ζ, ζ] ≤ (D²v(x)[ζ, ζ] + D²v(y)[ζ, ζ]) / 2`.  Proof: the pair moves along the diagonal
  `s ↦ (x + sζ, y + sζ)`, whose midpoint is `m + sζ` (`Korevaar.midpoint_add_smul`), so the
  scalar defect `s ↦ -C(x + sζ, y + sζ)` has a local minimum at `s = 0`, and the one-dimensional
  second-order necessary condition `Korevaar.nonneg_of_isLocalMin_of_hasDerivAt_deriv` applies.
* `Korevaar.sum_inner_single_nonneg`, `Korevaar.trace_midpoint_le` — the **trace step**:
  `tr(A N) ≥ 0` for a symmetric positive semidefinite `A` and an `N` with nonnegative quadratic
  form (spectral theorem for `A`), hence `tr(A D²v(m)) ≤ (tr(A D²v(x)) + tr(A D²v(y)))/2` under
  the Loewner inequality.
* `Korevaar.divergence`, `Korevaar.divergence_comp`,
  `Korevaar.divergence_flux_gradient_midpoint_le` — the trace step in its divergence form
  (`div a(∇v) = tr(A(∇v) D²v)` by the chain rule):
  `div a(∇v)(m) ≤ (div a(∇v)(x) + div a(∇v)(y))/2` at an interior maximum of `C` whose common
  gradient does not vanish.
* `Korevaar.inner_hessian_midpoint_eq_of_divergence_eq` — the **degenerate case**: if the three
  divergences agree (which they do, by the transformed equation, because the three gradients
  agree), then the Loewner inequality is an *equality*,
  `D²v(m)[ζ, ζ] = (D²v(x)[ζ, ζ] + D²v(y)[ζ, ζ])/2` for **every** `ζ`.  This is where Korevaar's
  argument needs the strong maximum principle for the linearized operator.
* `Korevaar.divergence_flux_gradient_neg_log` — the **transformed equation**
  `div a(∇v) = λ + (p-1) F(∇v)^p` for `v = -log φ`, re-proved here from the pointwise
  ("strong") form `div a(∇φ) + λ φ^{p-1} = 0` of the eigenvalue equation by the chain rule and
  the homogeneity of the flux.  (The same computation is `EigenfunctionData
  .divergence_flux_gradient_neg_log` in `WangXia.EigenvalueConvexOffCritical`, which cannot be
  imported here: `EigenvalueConvexOffCritical → … → EigenfunctionData → LogConcave`.)

Several of the auxiliary declarations below duplicate material of
`WangXia.EigenvalueConvexHessian` and `WangXia.EigenvalueConvexAssemblyAux` for exactly that
reason; they are placed in the namespace `Komlos.Literature.Korevaar` so that no name clashes
with the downstream copies.
-/

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Korevaar's concavity function -/

/-- **Korevaar's concavity function** of `v` (the object of the concavity maximum principle used
in MRS24, Theorem 1.1): `C(x, y) = v (midpoint x y) - (v x + v y) / 2`. A continuous `v` is convex
on a convex set exactly when `C ≤ 0` there (`convexOn_of_concavityFn_nonpos`). -/
noncomputable def concavityFn (v : Euc d → ℝ) (x y : Euc d) : ℝ :=
  v (midpoint ℝ x y) - (v x + v y) / 2

/-- **The concavity function vanishes on the diagonal**: `C(x, x) = 0`. Together with the boundary
behaviour (`tendsto_concavityFn_atBot_of_mem_frontier`) this is the reason a *positive* maximum of
`C` must be attained at an interior, off-diagonal point, where the second-order conditions apply. -/
theorem concavityFn_self (v : Euc d → ℝ) (x : Euc d) : concavityFn v x x = 0 := by
  simp only [concavityFn, midpoint_self]
  ring

/-- The concavity function is symmetric. -/
theorem concavityFn_comm (v : Euc d → ℝ) (x y : Euc d) :
    concavityFn v x y = concavityFn v y x := by
  simp only [concavityFn]
  rw [midpoint_comm]
  ring

/-- **First-order conditions at an interior maximum of the concavity function** (step (ii) of
Korevaar's argument; MRS24, Theorem 1.1): if `z ↦ C(z, y)` has a local maximum at `x`, and `v` has
gradient `gx` at `x` and `gm` at the midpoint of `x` and `y`, then `gm = gx`.

By symmetry (`concavityFn_comm`) the same applies in the second variable, so at an interior
maximum of `C` the three gradients `∇v(x)`, `∇v(y)` and `∇v(midpoint x y)` coincide
(`Korevaar.gradient_eq_of_isLocalMax_pair`). Hence the reaction term `λ + (p - 1) F(∇v)^p` of the
transformed equation `div a(∇v) = λ + (p-1) F(∇v)^p` takes the *same* value at the three points —
this, together with the second-order conditions and the ellipticity `A(ξ) = Da(ξ) ⪰ 0`, is what
makes an interior positive maximum impossible.

Proof: for each direction `w`, the function `t ↦ C(x + t w, y)` has a local maximum at `t = 0`
(`IsLocalMax.comp_continuous`) and derivative `⟪gm, w/2⟫ - ⟪gx, w⟫/2` there, because the midpoint
of `x + t w` and `y` is `midpoint x y + (t/2) w`. Fermat's theorem
(`IsLocalMax.hasDerivAt_eq_zero`) gives `⟪gm - gx, w⟫ = 0` for every `w`; take `w = gm - gx`. -/
theorem gradient_eq_of_isLocalMax_concavityFn {v : Euc d → ℝ} {x y gx gm : Euc d}
    (hvx : HasGradientAt v gx x) (hvm : HasGradientAt v gm (midpoint ℝ x y))
    (hmax : IsLocalMax (fun z => concavityFn v z y) x) : gm = gx := by
  have key : ∀ w : Euc d, ⟪gm - gx, w⟫ = 0 := by
    intro w
    -- The line `t ↦ x + t w` and the induced motion of the midpoint.
    have hline : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hcontline : Continuous fun t : ℝ => x + t • w := by fun_prop
    -- the midpoint of `x + t w` and `y` moves along the line `midpoint x y + (t/2) w`
    have hmidfun : (fun t : ℝ => midpoint ℝ (x + t • w) y)
        = fun t : ℝ => midpoint ℝ x y + ((2 : ℝ)⁻¹ * t) • w := by
      funext t
      simp only [midpoint_eq_smul_add, invOf_eq_inv]
      module
    have hmidline : HasDerivAt (fun t : ℝ => midpoint ℝ (x + t • w) y) ((2 : ℝ)⁻¹ • w) 0 := by
      rw [hmidfun]
      have hmul : HasDerivAt (fun t : ℝ => (2 : ℝ)⁻¹ * t) ((2 : ℝ)⁻¹) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul ((2 : ℝ)⁻¹)
      exact (hmul.smul_const w).const_add (midpoint ℝ x y)
    -- Derivatives of the two terms of the concavity function along the line.
    have hd1 : HasDerivAt (fun t : ℝ => v (midpoint ℝ (x + t • w) y)) ⟪gm, (2 : ℝ)⁻¹ • w⟫ 0 := by
      have h := (hasGradientAt_iff_hasFDerivAt.1 hvm).comp_hasDerivAt_of_eq (0 : ℝ) hmidline
        (by simp)
      rw [InnerProductSpace.toDual_apply_apply] at h
      exact h
    have hd2 : HasDerivAt (fun t : ℝ => v (x + t • w)) ⟪gx, w⟫ 0 := by
      have h := (hasGradientAt_iff_hasFDerivAt.1 hvx).comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
      rw [InnerProductSpace.toDual_apply_apply] at h
      exact h
    have hdC : HasDerivAt (fun t : ℝ => concavityFn v (x + t • w) y)
        (⟪gm, (2 : ℝ)⁻¹ • w⟫ - ⟪gx, w⟫ / 2) 0 := by
      simp only [concavityFn]
      exact hd1.sub ((hd2.add_const (v y)).div_const 2)
    -- Fermat's theorem at the local maximum `t = 0`.
    have hmaxline : IsLocalMax (fun t : ℝ => concavityFn v (x + t • w) y) 0 := by
      have hmax' : IsLocalMax (fun z => concavityFn v z y) ((fun t : ℝ => x + t • w) 0) := by
        simpa using hmax
      -- name the inner map: unification would otherwise split the beta-reduced base point
      -- `x + 0 • w` as `HAdd.hAdd x` applied to `0 • w`
      exact hmax'.comp_continuous (g := fun t : ℝ => x + t • w) (b := 0) hcontline.continuousAt
    have hzero := hmaxline.hasDerivAt_eq_zero hdC
    rw [real_inner_smul_right] at hzero
    rw [inner_sub_left]
    linarith
  -- Test against `w = gm - gx`.
  have h := key (gm - gx)
  rw [real_inner_self_eq_norm_sq] at h
  have hn : ‖gm - gx‖ = 0 := by nlinarith [norm_nonneg (gm - gx)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hn)

namespace Korevaar

/-! ### Moving an interior maximizing pair -/

/-- **Translating both points of a pair translates their midpoint**:
`midpoint (x + sζ) (y + sζ) = midpoint x y + sζ`. This is what makes the *diagonal* direction
`(ζ, ζ)` the useful test direction in Korevaar's second-order argument: along it the concavity
function becomes the one-dimensional defect
`s ↦ v(m + sζ) - (v(x + sζ) + v(y + sζ))/2`. -/
theorem midpoint_add_smul (x y ζ : Euc d) (s : ℝ) :
    midpoint ℝ (x + s • ζ) (y + s • ζ) = midpoint ℝ x y + s • ζ := by
  simp only [midpoint_eq_smul_add, invOf_eq_inv]
  module

/-- A local maximum of `C` on the pair restricts to a local maximum in the first variable. -/
theorem isLocalMax_left {v : Euc d → ℝ} {x y : Euc d}
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y)) :
    IsLocalMax (fun z : Euc d => concavityFn v z y) x := by
  have hcont : Continuous fun z : Euc d => ((z, y) : Euc d × Euc d) := by fun_prop
  have hten : Tendsto (fun z : Euc d => ((z, y) : Euc d × Euc d)) (𝓝 x) (𝓝 (x, y)) := by
    simpa using hcont.tendsto x
  have h : ∀ᶠ z : Euc d in 𝓝 x, concavityFn v z y ≤ concavityFn v x y := hten.eventually hmax
  exact h

/-- A local maximum of `C` on the pair restricts to a local maximum in the second variable;
stated in the first-variable form of `gradient_eq_of_isLocalMax_concavityFn` via
`concavityFn_comm`. -/
theorem isLocalMax_right {v : Euc d → ℝ} {x y : Euc d}
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y)) :
    IsLocalMax (fun z : Euc d => concavityFn v z x) y := by
  have hcont : Continuous fun z : Euc d => ((x, z) : Euc d × Euc d) := by fun_prop
  have hten : Tendsto (fun z : Euc d => ((x, z) : Euc d × Euc d)) (𝓝 y) (𝓝 (x, y)) := by
    simpa using hcont.tendsto y
  have h : ∀ᶠ z : Euc d in 𝓝 y, concavityFn v x z ≤ concavityFn v x y := hten.eventually hmax
  have h' : ∀ᶠ z : Euc d in 𝓝 y, concavityFn v z x ≤ concavityFn v y x := by
    filter_upwards [h] with z hz
    rwa [concavityFn_comm v z x, concavityFn_comm v y x]
  exact h'

/-- **The first-order conditions at an interior maximum of the concavity function on the pair**
(Korevaar's step (ii); MRS24, Theorem 1.1): the three gradients coincide,
`∇v (midpoint x y) = ∇v x = ∇v y`. Consequently the reaction term `λ + (p-1) F(∇v)^p` of the
transformed equation `div a(∇v) = λ + (p-1) F(∇v)^p` takes the same value at `x`, `y` and the
midpoint, so the three flux divergences agree. -/
theorem gradient_eq_of_isLocalMax_pair {v : Euc d → ℝ} {x y gx gy gm : Euc d}
    (hvx : HasGradientAt v gx x) (hvy : HasGradientAt v gy y)
    (hvm : HasGradientAt v gm (midpoint ℝ x y))
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y)) :
    gm = gx ∧ gy = gx := by
  have h1 : gm = gx := gradient_eq_of_isLocalMax_concavityFn hvx hvm (isLocalMax_left hmax)
  have hvm' : HasGradientAt v gm (midpoint ℝ y x) := by rwa [midpoint_comm]
  have h2 : gm = gy := gradient_eq_of_isLocalMax_concavityFn hvy hvm' (isLocalMax_right hmax)
  exact ⟨h1, by rw [← h2, h1]⟩

/-- **The diagonal defect has a local minimum**: if `C` has a local maximum at the pair `(x, y)`
then, for every direction `ζ`, the scalar function
`s ↦ -v(m + sζ) + (v(x + sζ) + v(y + sζ))/2` (with `m = midpoint x y`) has a local minimum at
`s = 0`. This is the one-dimensional reduction behind the second-order conditions. -/
theorem isLocalMin_line_of_isLocalMax {v : Euc d → ℝ} {x y : Euc d}
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y)) (ζ : Euc d) :
    IsLocalMin (fun s : ℝ => -v (midpoint ℝ x y + s • ζ)
      + (v (x + s • ζ) + v (y + s • ζ)) / 2) 0 := by
  have hcont : Continuous fun s : ℝ => ((x + s • ζ, y + s • ζ) : Euc d × Euc d) := by fun_prop
  have hten : Tendsto (fun s : ℝ => ((x + s • ζ, y + s • ζ) : Euc d × Euc d)) (𝓝 0)
      (𝓝 (x, y)) := by
    simpa using hcont.tendsto 0
  have h : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
      concavityFn v (x + s • ζ) (y + s • ζ) ≤ concavityFn v x y := hten.eventually hmax
  have hgoal : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
      -v (midpoint ℝ x y + (0 : ℝ) • ζ)
          + (v (x + (0 : ℝ) • ζ) + v (y + (0 : ℝ) • ζ)) / 2
        ≤ -v (midpoint ℝ x y + s • ζ) + (v (x + s • ζ) + v (y + s • ζ)) / 2 := by
    filter_upwards [h] with s hs
    simp only [concavityFn, midpoint_add_smul] at hs
    simp only [zero_smul, add_zero]
    linarith
  exact hgoal

/-! ### Second-order necessary conditions -/

/-- **Second-order necessary condition** (one variable): at a local minimum `x₀` of `f`, if `f` is
differentiable near `x₀` and `deriv f` has derivative `f''` at `x₀`, then `0 ≤ f''`.

(The same statement is `nonneg_of_isLocalMin_of_hasDerivAt_deriv` in
`WangXia.EigenvalueConvexHessian`, which is not importable here.) -/
theorem nonneg_of_isLocalMin_of_hasDerivAt_deriv {f : ℝ → ℝ} {x₀ f'' : ℝ}
    (hmin : IsLocalMin f x₀) (hd : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ f x)
    (hd2 : HasDerivAt (deriv f) f'' x₀) : 0 ≤ f'' := by
  by_contra hlt
  replace hlt : f'' < 0 := not_le.1 hlt
  have h0 : deriv f x₀ = 0 := hmin.deriv_eq_zero
  have hsign : ∀ᶠ x in 𝓝 x₀, SignType.sign (deriv f x) = SignType.sign (x₀ - x) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg (by rw [hd2.deriv]; exact hlt) h0
  have hneg : ∀ᶠ b in 𝓝[>] x₀, deriv f b < 0 :=
    deriv_neg_right_of_sign_deriv (nhdsWithin_le_nhds hsign)
  obtain ⟨u, hu, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hneg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hd.and hmin)
  set δ : ℝ := min (u - x₀) r / 2 with hδ
  have hδpos : 0 < δ := by
    have : 0 < min (u - x₀) r := lt_min (sub_pos.2 (mem_Ioi.1 hu)) hr
    positivity
  have hδu : δ < u - x₀ := by
    have : min (u - x₀) r ≤ u - x₀ := min_le_left _ _
    linarith
  have hδr : δ < r := by
    have : min (u - x₀) r ≤ r := min_le_right _ _
    linarith
  have hmem : ∀ x ∈ Icc x₀ (x₀ + δ), x ∈ Metric.ball x₀ r := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hx.1, hx.2]
  have hanti : StrictAntiOn f (Icc x₀ (x₀ + δ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · exact fun x hx => ((hball (hmem x hx)).1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hIoo ⟨hx.1, by linarith [hx.2]⟩
  have h1 : f (x₀ + δ) < f x₀ :=
    hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have h2 : f x₀ ≤ f (x₀ + δ) := (hball (hmem _ ⟨by linarith, le_rfl⟩)).2
  linarith

/-- **Derivatives along a line through `a`**: if `v` is differentiable near `a` and `∇v` has
derivative `H` at `a`, then `s ↦ v (a + sζ)` has derivative `⟪∇v(a + sζ), ζ⟫` for `s` near `0`,
and that derivative has derivative `⟪Hζ, ζ⟫` at `s = 0`. -/
theorem hasDerivAt_inner_gradient_line {v : Euc d → ℝ} {a : Euc d} {H : Euc d →L[ℝ] Euc d}
    (hd : ∀ᶠ z in 𝓝 a, DifferentiableAt ℝ v z) (hH : HasFDerivAt (gradient v) H a) (ζ : Euc d) :
    (∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
        HasDerivAt (fun s : ℝ => v (a + s • ζ)) ⟪gradient v (a + s • ζ), ζ⟫ s) ∧
      HasDerivAt (fun s : ℝ => ⟪gradient v (a + s • ζ), ζ⟫) ⟪H ζ, ζ⟫ 0 := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => a + s • ζ) ζ s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const ζ).const_add a
  have hcont : Continuous fun s : ℝ => a + s • ζ := by fun_prop
  have hlim : Tendsto (fun s : ℝ => a + s • ζ) (𝓝 0) (𝓝 a) := by
    simpa using hcont.tendsto 0
  refine ⟨?_, ?_⟩
  · filter_upwards [hlim.eventually hd] with s hs
    have h1 := (hasGradientAt_iff_hasFDerivAt.1 hs.hasGradientAt).comp_hasDerivAt s (hline s)
    rw [InnerProductSpace.toDual_apply_apply] at h1
    exact h1
  · have h3 : HasDerivAt (fun s : ℝ => gradient v (a + s • ζ)) (H ζ) 0 :=
      hH.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) (by simp)
    have h4 := h3.inner ℝ (hasDerivAt_const (0 : ℝ) ζ)
    simpa using h4

/-- **The second-order conditions of Korevaar's concavity maximum principle** (MRS24,
Theorem 1.1): at a local maximum of the concavity function `C` on the pair `(x, y)`, the Hessian
of `v` at the midpoint is dominated, in the Loewner order, by the average of the Hessians at `x`
and `y`:

  `D²v(m)[ζ, ζ] ≤ (D²v(x)[ζ, ζ] + D²v(y)[ζ, ζ]) / 2`   for every `ζ`.

Proof: moving the pair along the diagonal, `s ↦ (x + sζ, y + sζ)`, the midpoint moves along
`m + sζ` (`midpoint_add_smul`), so the scalar defect
`ψ(s) = -v(m + sζ) + (v(x + sζ) + v(y + sζ))/2` has a local minimum at `s = 0`
(`isLocalMin_line_of_isLocalMax`); its first derivative is
`-⟪∇v(m + sζ), ζ⟫ + (⟪∇v(x + sζ), ζ⟫ + ⟪∇v(y + sζ), ζ⟫)/2`
(`hasDerivAt_inner_gradient_line`), whose derivative at `s = 0` is
`-⟪D²v(m)ζ, ζ⟫ + (⟪D²v(x)ζ, ζ⟫ + ⟪D²v(y)ζ, ζ⟫)/2`; this is `≥ 0` by the one-dimensional
second-order necessary condition `nonneg_of_isLocalMin_of_hasDerivAt_deriv`. -/
theorem inner_hessian_midpoint_le_of_isLocalMax {v : Euc d → ℝ} {x y : Euc d}
    {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v) Hx x) (hHy : HasFDerivAt (gradient v) Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y))
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y)) (ζ : Euc d) :
    ⟪Hm ζ, ζ⟫ ≤ (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2 := by
  obtain ⟨hx1, hx2⟩ := hasDerivAt_inner_gradient_line hdx hHx ζ
  obtain ⟨hy1, hy2⟩ := hasDerivAt_inner_gradient_line hdy hHy ζ
  obtain ⟨hm1, hm2⟩ := hasDerivAt_inner_gradient_line hdm hHm ζ
  -- the diagonal defect and its first derivative
  have hψd : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), HasDerivAt
      (fun s : ℝ => -v (midpoint ℝ x y + s • ζ) + (v (x + s • ζ) + v (y + s • ζ)) / 2)
      (-⟪gradient v (midpoint ℝ x y + s • ζ), ζ⟫
        + (⟪gradient v (x + s • ζ), ζ⟫ + ⟪gradient v (y + s • ζ), ζ⟫) / 2) s := by
    filter_upwards [hx1, hy1, hm1] with s hsx hsy hsm
    exact hsm.neg.add ((hsx.add hsy).div_const 2)
  have hderiv : deriv (fun s : ℝ =>
        -v (midpoint ℝ x y + s • ζ) + (v (x + s • ζ) + v (y + s • ζ)) / 2) =ᶠ[𝓝 (0 : ℝ)]
      fun s : ℝ => -⟪gradient v (midpoint ℝ x y + s • ζ), ζ⟫
        + (⟪gradient v (x + s • ζ), ζ⟫ + ⟪gradient v (y + s • ζ), ζ⟫) / 2 := by
    filter_upwards [hψd] with s hs
    exact hs.deriv
  have h2 : HasDerivAt (fun s : ℝ => -⟪gradient v (midpoint ℝ x y + s • ζ), ζ⟫
        + (⟪gradient v (x + s • ζ), ζ⟫ + ⟪gradient v (y + s • ζ), ζ⟫) / 2)
      (-⟪Hm ζ, ζ⟫ + (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2) 0 :=
    hm2.neg.add ((hx2.add hy2).div_const 2)
  have hd2 : HasDerivAt (deriv fun s : ℝ =>
      -v (midpoint ℝ x y + s • ζ) + (v (x + s • ζ) + v (y + s • ζ)) / 2)
      (-⟪Hm ζ, ζ⟫ + (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2) 0 := h2.congr_of_eventuallyEq hderiv
  have hkey := nonneg_of_isLocalMin_of_hasDerivAt_deriv
    (isLocalMin_line_of_isLocalMax hmax ζ) (hψd.mono fun s hs => hs.differentiableAt) hd2
  linarith

/-! ### The trace step -/

/-- **The trace of `A N` in an eigenbasis of `A`**: for a symmetric `A` with eigenbasis `b` and
eigenvalues `μ`, `tr(A N) = ∑ⱼ μⱼ ⟪bⱼ, N bⱼ⟫`. (Here `tr(A N) = ∑ᵢ ⟪eᵢ, A (N eᵢ)⟫` is computed in
the standard basis; the trace is basis independent.) -/
theorem sum_inner_single_eq_sum_eigen {A N : Euc d →L[ℝ] Euc d}
    (hAsym : (A : Euc d →ₗ[ℝ] Euc d).IsSymmetric) :
    ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (N (EuclideanSpace.single i (1 : ℝ)))⟫ =
      ∑ j, hAsym.eigenvalues finrank_euclideanSpace_fin j *
        ⟪hAsym.eigenvectorBasis finrank_euclideanSpace_fin j,
          N (hAsym.eigenvectorBasis finrank_euclideanSpace_fin j)⟫ := by
  set b := hAsym.eigenvectorBasis finrank_euclideanSpace_fin with hb
  have h1 : ∑ i, ⟪EuclideanSpace.single i (1 : ℝ),
      A (N (EuclideanSpace.single i (1 : ℝ)))⟫ =
      LinearMap.trace ℝ (Euc d) ((A : Euc d →ₗ[ℝ] Euc d) * (N : Euc d →ₗ[ℝ] Euc d)) := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp [EuclideanSpace.basisFun_apply]
  rw [h1, LinearMap.trace_mul_comm, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hev : (A : Euc d →ₗ[ℝ] Euc d) (b j) =
      hAsym.eigenvalues finrank_euclideanSpace_fin j • b j := by
    have h := hAsym.apply_eigenvectorBasis finrank_euclideanSpace_fin j
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h
  rw [Module.End.mul_apply, hev, map_smul]
  simp only [real_inner_smul_right, ContinuousLinearMap.coe_coe]

/-- The eigenvalues of a symmetric positive semidefinite `A` are nonnegative. -/
theorem eigenvalues_nonneg {A : Euc d →L[ℝ] Euc d}
    (hAsym : (A : Euc d →ₗ[ℝ] Euc d).IsSymmetric) (hA : ∀ ζ : Euc d, 0 ≤ ⟪A ζ, ζ⟫) (j : Fin d) :
    0 ≤ hAsym.eigenvalues finrank_euclideanSpace_fin j := by
  set b := hAsym.eigenvectorBasis finrank_euclideanSpace_fin with hb
  have hev : (A : Euc d →ₗ[ℝ] Euc d) (b j) =
      hAsym.eigenvalues finrank_euclideanSpace_fin j • b j := by
    have h := hAsym.apply_eigenvectorBasis finrank_euclideanSpace_fin j
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h
  have hnorm : ‖b j‖ = 1 := b.orthonormal.1 j
  have h := hA (b j)
  rw [← ContinuousLinearMap.coe_coe A, hev, real_inner_smul_left, real_inner_self_eq_norm_sq,
    hnorm] at h
  simpa using h

/-- The eigenvalues of a symmetric positive definite `A` are positive. -/
theorem eigenvalues_pos {A : Euc d →L[ℝ] Euc d}
    (hAsym : (A : Euc d →ₗ[ℝ] Euc d).IsSymmetric) (hA : ∀ ζ : Euc d, ζ ≠ 0 → 0 < ⟪A ζ, ζ⟫)
    (j : Fin d) : 0 < hAsym.eigenvalues finrank_euclideanSpace_fin j := by
  set b := hAsym.eigenvectorBasis finrank_euclideanSpace_fin with hb
  have hev : (A : Euc d →ₗ[ℝ] Euc d) (b j) =
      hAsym.eigenvalues finrank_euclideanSpace_fin j • b j := by
    have h := hAsym.apply_eigenvectorBasis finrank_euclideanSpace_fin j
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h
  have hnorm : ‖b j‖ = 1 := b.orthonormal.1 j
  have hbne : b j ≠ 0 := fun hj => by
    rw [hj, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have h := hA (b j) hbne
  rw [← ContinuousLinearMap.coe_coe A, hev, real_inner_smul_left, real_inner_self_eq_norm_sq,
    hnorm] at h
  simpa using h

/-- **Trace positivity**: for a symmetric positive semidefinite `A` and any `N` with nonnegative
quadratic form, `tr(A N) ≥ 0`. This is the algebraic heart of Korevaar's "take the trace against
`A(q) ⪰ 0`" step: by the spectral theorem `tr(A N) = ∑ⱼ μⱼ ⟪bⱼ, N bⱼ⟫` with `μⱼ ≥ 0`.

(The same statement, in the two-sided form, is `sum_inner_single_apply_le` in
`WangXia.EigenvalueConvexHessian`, which is not importable here.) -/
theorem sum_inner_single_nonneg {A N : Euc d →L[ℝ] Euc d}
    (hAs : ∀ ζ ζ' : Euc d, ⟪A ζ, ζ'⟫ = ⟪ζ, A ζ'⟫) (hA : ∀ ζ : Euc d, 0 ≤ ⟪A ζ, ζ⟫)
    (hN0 : ∀ ζ : Euc d, 0 ≤ ⟪N ζ, ζ⟫) :
    0 ≤ ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (N (EuclideanSpace.single i (1 : ℝ)))⟫ := by
  have hAsym : (A : Euc d →ₗ[ℝ] Euc d).IsSymmetric := fun ζ ζ' => hAs ζ ζ'
  rw [sum_inner_single_eq_sum_eigen hAsym]
  refine Finset.sum_nonneg fun j _ => ?_
  exact mul_nonneg (eigenvalues_nonneg hAsym hA j) (by rw [real_inner_comm]; exact hN0 _)

/-- The quadratic form of the "second-order defect" `N = Hx + Hy - 2 Hm` is nonnegative exactly
when the Loewner inequality `Hm ⪯ (Hx + Hy)/2` holds. -/
theorem inner_defect_nonneg {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hle : ∀ ζ : Euc d, ⟪Hm ζ, ζ⟫ ≤ (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2) (ζ : Euc d) :
    0 ≤ ⟪(Hx + Hy - Hm - Hm) ζ, ζ⟫ := by
  have h := hle ζ
  simp only [_root_.sub_apply, _root_.add_apply, inner_sub_left, inner_add_left]
  linarith

/-- Additivity of `tr(A ·)` on the defect `N = Hx + Hy - 2 Hm`:
`tr(A N) + 2 tr(A Hm) = tr(A Hx) + tr(A Hy)`. -/
theorem sum_inner_single_defect (A Hx Hy Hm : Euc d →L[ℝ] Euc d) :
    (∑ i, ⟪EuclideanSpace.single i (1 : ℝ),
        A ((Hx + Hy - Hm - Hm) (EuclideanSpace.single i (1 : ℝ)))⟫) +
      ((∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hm (EuclideanSpace.single i (1 : ℝ)))⟫) +
        ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hm (EuclideanSpace.single i (1 : ℝ)))⟫) =
      (∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hx (EuclideanSpace.single i (1 : ℝ)))⟫) +
        ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hy (EuclideanSpace.single i (1 : ℝ)))⟫ := by
  have hsplit : ∀ i : Fin d,
      ⟪EuclideanSpace.single i (1 : ℝ),
          A ((Hx + Hy - Hm - Hm) (EuclideanSpace.single i (1 : ℝ)))⟫ +
        (⟪EuclideanSpace.single i (1 : ℝ), A (Hm (EuclideanSpace.single i (1 : ℝ)))⟫ +
          ⟪EuclideanSpace.single i (1 : ℝ), A (Hm (EuclideanSpace.single i (1 : ℝ)))⟫) =
      ⟪EuclideanSpace.single i (1 : ℝ), A (Hx (EuclideanSpace.single i (1 : ℝ)))⟫ +
        ⟪EuclideanSpace.single i (1 : ℝ), A (Hy (EuclideanSpace.single i (1 : ℝ)))⟫ := by
    intro i
    simp only [_root_.sub_apply, _root_.add_apply, map_sub, map_add, inner_sub_right,
      inner_add_right]
    ring
  have hsum := Finset.sum_congr rfl fun (i : Fin d) (_ : i ∈ Finset.univ) => hsplit i
  simp only [Finset.sum_add_distrib] at hsum
  exact hsum

/-- **The trace step of Korevaar's argument**: tracing the Loewner inequality
`Hm ⪯ (Hx + Hy)/2` against a symmetric positive semidefinite `A` gives
`tr(A Hm) ≤ (tr(A Hx) + tr(A Hy))/2`. -/
theorem trace_midpoint_le {A Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hAs : ∀ ζ ζ' : Euc d, ⟪A ζ, ζ'⟫ = ⟪ζ, A ζ'⟫) (hA : ∀ ζ : Euc d, 0 ≤ ⟪A ζ, ζ⟫)
    (hle : ∀ ζ : Euc d, ⟪Hm ζ, ζ⟫ ≤ (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2) :
    ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hm (EuclideanSpace.single i (1 : ℝ)))⟫ ≤
      ((∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hx (EuclideanSpace.single i (1 : ℝ)))⟫) +
        ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hy (EuclideanSpace.single i (1 : ℝ)))⟫) / 2 := by
  have hkey := sum_inner_single_nonneg hAs hA (inner_defect_nonneg hle)
  have hsum := sum_inner_single_defect A Hx Hy Hm
  linarith

/-- A real quadratic `t ↦ t S + t² C` with `C ≥ 0` which is nonnegative for every `t` has
`S = 0` (Cauchy–Schwarz for a positive semidefinite quadratic form). -/
theorem eq_zero_of_quadratic_nonneg {S C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ t * S + t ^ 2 * C) : S = 0 := by
  by_contra hS
  have hS2 : 0 < S ^ 2 := by
    rcases lt_trichotomy S 0 with h' | h' | h'
    · nlinarith
    · exact absurd h' hS
    · nlinarith
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  have hu0 : (0 : ℝ) < (C + 1)⁻¹ := inv_pos.2 hCpos
  have huC : (C + 1)⁻¹ * C - 1 < 0 := by
    have h1 : (C + 1)⁻¹ * C < 1 := by
      rw [inv_mul_eq_div, div_lt_one hCpos]
      linarith
    linarith
  have hkey := h (-((C + 1)⁻¹ * S))
  have hexp : -((C + 1)⁻¹ * S) * S + (-((C + 1)⁻¹ * S)) ^ 2 * C =
      S ^ 2 * ((C + 1)⁻¹ * ((C + 1)⁻¹ * C - 1)) := by ring
  rw [hexp] at hkey
  have hneg : S ^ 2 * ((C + 1)⁻¹ * ((C + 1)⁻¹ * C - 1)) < 0 :=
    mul_neg_of_pos_of_neg hS2 (mul_neg_of_pos_of_neg hu0 huC)
  linarith

/-- **The degenerate case of the trace step**: if `A` is symmetric positive *definite*, the
quadratic form of `N` is nonnegative and `tr(A N) = 0`, then the quadratic form of `N` vanishes
identically.

Proof: by the spectral theorem `tr(A N) = ∑ⱼ μⱼ ⟪bⱼ, N bⱼ⟫` with `μⱼ > 0` and each
`⟪bⱼ, N bⱼ⟫ ≥ 0`, so `⟪N bⱼ, bⱼ⟫ = 0` for every member of the orthonormal eigenbasis `b` of `A`.
A nonnegative quadratic form vanishing at a vector has vanishing bilinear form against every
other vector (`eq_zero_of_quadratic_nonneg`), and expanding an arbitrary `ζ` in the basis `b`
gives `⟪N ζ, ζ⟫ = -⟪N ζ, ζ⟫`. -/
theorem quadratic_eq_zero_of_sum_inner_single_eq_zero {A N : Euc d →L[ℝ] Euc d}
    (hAs : ∀ ζ ζ' : Euc d, ⟪A ζ, ζ'⟫ = ⟪ζ, A ζ'⟫)
    (hApos : ∀ ζ : Euc d, ζ ≠ 0 → 0 < ⟪A ζ, ζ⟫) (hN0 : ∀ ζ : Euc d, 0 ≤ ⟪N ζ, ζ⟫)
    (htr : ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (N (EuclideanSpace.single i (1 : ℝ)))⟫ = 0)
    (ζ : Euc d) : ⟪N ζ, ζ⟫ = 0 := by
  have hAsym : (A : Euc d →ₗ[ℝ] Euc d).IsSymmetric := fun a c => hAs a c
  -- (i) the quadratic form of `N` vanishes on the eigenbasis of `A`
  have hsum : ∑ j, hAsym.eigenvalues finrank_euclideanSpace_fin j *
      ⟪hAsym.eigenvectorBasis finrank_euclideanSpace_fin j,
        N (hAsym.eigenvectorBasis finrank_euclideanSpace_fin j)⟫ = 0 := by
    rw [← sum_inner_single_eq_sum_eigen hAsym]
    exact htr
  set b := hAsym.eigenvectorBasis finrank_euclideanSpace_fin with hb
  set μ := hAsym.eigenvalues finrank_euclideanSpace_fin with hμ
  have hμpos : ∀ j, 0 < μ j := fun j => eigenvalues_pos hAsym hApos j
  have hterm : ∀ j : Fin d, 0 ≤ μ j * ⟪b j, N (b j)⟫ := fun j =>
    mul_nonneg (hμpos j).le (by rw [real_inner_comm]; exact hN0 _)
  have hzero : ∀ j, ⟪N (b j), b j⟫ = 0 := by
    intro j
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).1 hsum j (Finset.mem_univ j)
    rw [real_inner_comm]
    exact (mul_eq_zero.1 h).resolve_left (hμpos j).ne'
  -- (ii) polarization at each eigenvector
  have hpol : ∀ (j : Fin d) (w : Euc d), ⟪N (b j), w⟫ + ⟪N w, b j⟫ = 0 := by
    intro j w
    refine eq_zero_of_quadratic_nonneg (hN0 w) fun t => ?_
    have h := hN0 (b j + t • w)
    have he : ⟪N (b j + t • w), b j + t • w⟫ =
        ⟪N (b j), b j⟫ + (t * (⟪N (b j), w⟫ + ⟪N w, b j⟫) + t ^ 2 * ⟪N w, w⟫) := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      ring
    rw [he, hzero j] at h
    linarith
  -- (iii) expand `ζ` in the eigenbasis
  have hNζ : N ζ = ∑ j, ⟪b j, ζ⟫ • N (b j) := by
    conv_lhs => rw [← b.sum_repr' ζ]
    rw [map_sum]
    simp only [map_smul]
  have hexp : ⟪N ζ, ζ⟫ = ∑ j, ⟪b j, ζ⟫ * ⟪N (b j), ζ⟫ := by
    rw [hNζ, sum_inner]
    exact Finset.sum_congr rfl fun j _ => real_inner_smul_left _ _ _
  have hcancel : (∑ j, ⟪b j, ζ⟫ * ⟪N (b j), ζ⟫) + ∑ j, ⟪N ζ, b j⟫ * ⟪b j, ζ⟫ = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hr : ⟪b j, ζ⟫ * ⟪N (b j), ζ⟫ + ⟪N ζ, b j⟫ * ⟪b j, ζ⟫ =
        ⟪b j, ζ⟫ * (⟪N (b j), ζ⟫ + ⟪N ζ, b j⟫) := by ring
    rw [hr, hpol j ζ, mul_zero]
  have hpars : ∑ j, ⟪N ζ, b j⟫ * ⟪b j, ζ⟫ = ⟪N ζ, ζ⟫ := b.sum_inner_mul_inner (N ζ) ζ
  rw [hpars] at hcancel
  linarith

/-- **The degenerate case of the trace step, at the level of quadratic forms**: if in addition
`A` is positive *definite* and the traced inequality is an equality, then the Loewner inequality
is an equality.

This is exactly the situation Korevaar's argument reaches at an interior positive maximum of the
concavity function: the three flux divergences agree (because the three gradients do, and the
transformed equation `div a(∇v) = λ + (p-1) F(∇v)^p` has the same right-hand side at all three
points), so the trace inequality `trace_midpoint_le` is saturated and the second-order conditions
hold with equality. -/
theorem inner_hessian_eq_of_trace_eq {A Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hAs : ∀ ζ ζ' : Euc d, ⟪A ζ, ζ'⟫ = ⟪ζ, A ζ'⟫) (hA : ∀ ζ : Euc d, ζ ≠ 0 → 0 < ⟪A ζ, ζ⟫)
    (hle : ∀ ζ : Euc d, ⟪Hm ζ, ζ⟫ ≤ (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2)
    (htr : ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hm (EuclideanSpace.single i (1 : ℝ)))⟫ =
      ((∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hx (EuclideanSpace.single i (1 : ℝ)))⟫) +
        ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (Hy (EuclideanSpace.single i (1 : ℝ)))⟫) / 2)
    (ζ : Euc d) : ⟪Hm ζ, ζ⟫ = (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2 := by
  have hsum := sum_inner_single_defect A Hx Hy Hm
  have hzero : ∑ i, ⟪EuclideanSpace.single i (1 : ℝ),
      A ((Hx + Hy - Hm - Hm) (EuclideanSpace.single i (1 : ℝ)))⟫ = 0 := by linarith
  have h := quadratic_eq_zero_of_sum_inner_single_eq_zero hAs hA (inner_defect_nonneg hle) hzero ζ
  simp only [_root_.sub_apply, _root_.add_apply, inner_sub_left, inner_add_left] at h
  linarith

/-! ### The divergence of a vector field -/

/-- The divergence `div W (x) = ∑ i ⟪e_i, DW(x) e_i⟫` of a vector field on `ℝ^d`.

(This repeats `Komlos.Literature.divergence` of `WangXia.EigenvalueConvexAssemblyAux`, which
imports `EigenfunctionData` and hence `LogConcave`, and so cannot be imported here.) -/
noncomputable def divergence (W : Euc d → Euc d) (x : Euc d) : ℝ :=
  ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), fderiv ℝ W x (EuclideanSpace.single i (1 : ℝ))⟫

/-- The divergence only depends on the germ of the vector field. -/
theorem divergence_congr {W₁ W₂ : Euc d → Euc d} {x : Euc d} (h : W₁ =ᶠ[𝓝 x] W₂) :
    divergence W₁ x = divergence W₂ x := by
  simp only [divergence, h.fderiv_eq]

/-- The divergence of a composition `a ∘ G`, by the chain rule. -/
theorem divergence_comp {a G : Euc d → Euc d} {x : Euc d} {a' G' : Euc d →L[ℝ] Euc d}
    (ha : HasFDerivAt a a' (G x)) (hG : HasFDerivAt G G' x) :
    divergence (fun y => a (G y)) x =
      ∑ i, ⟪EuclideanSpace.single i (1 : ℝ),
        a' (G' (EuclideanSpace.single i (1 : ℝ)))⟫ := by
  have h : HasFDerivAt (fun y => a (G y)) (a'.comp G') x := ha.comp x hG
  simp only [divergence, h.fderiv, ContinuousLinearMap.comp_apply]

/-- The product rule for the divergence: `div (c W) = ⟪∇c, W⟫ + c div W`. -/
theorem divergence_smul {c : Euc d → ℝ} {W : Euc d → Euc d} {x : Euc d} {g : Euc d}
    {W' : Euc d →L[ℝ] Euc d} (hc : HasGradientAt c g x) (hW : HasFDerivAt W W' x) :
    divergence (fun y => c y • W y) x = ⟪g, W x⟫ + c x * divergence W x := by
  have hc' : HasFDerivAt c (InnerProductSpace.toDual ℝ (Euc d) g) x :=
    hasGradientAt_iff_hasFDerivAt.1 hc
  have h : HasFDerivAt (fun y => c y • W y)
      (c x • W' + (InnerProductSpace.toDual ℝ (Euc d) g).smulRight (W x)) x := hc'.smul hW
  simp only [divergence, h.fderiv, hW.fderiv, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply, inner_add_right,
    inner_smul_right, Finset.sum_add_distrib, InnerProductSpace.toDual_apply_apply]
  rw [Finset.mul_sum, ← (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner g (W x)]
  simp only [EuclideanSpace.basisFun_apply]
  ring

/-! ### Symmetry of the ellipticity matrix `A(q) = Da(q)` -/

/-- **Symmetry of the Hessian**: if `f` is differentiable near `x` and `∇f` is differentiable at
`x` with derivative `H`, then `H` is symmetric.

(The same statement is `inner_fderiv_gradient_comm` in `WangXia.EigenvalueConvexHessian`.) -/
theorem inner_fderiv_gradient_comm {f : Euc d → ℝ} {x : Euc d} {H : Euc d →L[ℝ] Euc d}
    (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hH : HasFDerivAt (gradient f) H x)
    (ζ ζ' : Euc d) : ⟪H ζ, ζ'⟫ = ⟪ζ, H ζ'⟫ := by
  set T : Euc d →L[ℝ] Euc d →L[ℝ] ℝ :=
    (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := Euc d)).toContinuousLinearMap with hT
  have hTapp : ∀ a b : Euc d, T a b = ⟪a, b⟫ := fun a b =>
    (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := Euc d)).toContinuousLinearMap_apply a b
  have hf' : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y := hd.mono fun y hy => hy.hasFDerivAt
  have hf'' : HasFDerivAt (fderiv ℝ f) (T.comp H) x := by
    have heq : fderiv ℝ f = fun y => T (gradient f y) := by
      funext y
      ext ζ
      rw [hTapp, inner_gradient_left]
    rw [heq]
    exact T.hasFDerivAt.comp x hH
  have h := second_derivative_symmetric_of_eventually_of_real hf' hf'' ζ ζ'
  simp only [ContinuousLinearMap.comp_apply, hTapp] at h
  rw [h, real_inner_comm]

/-- The potential `G = F^p / p` of the flux: `a = ∇G` away from the origin.

(The same statement is `IsSmoothStrictNorm.hasGradientAt_flux_potential` in
`WangXia.EigenvalueConvexHessian`.) -/
theorem hasGradientAt_flux_potential {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {p : ℝ}
    (hp : 1 < p) {ξ : Euc d} (hξ : ξ ≠ 0) :
    HasGradientAt (fun x => F x ^ p / p) (flux p F ξ) ξ := by
  have hFξ : 0 < F ξ := hF.pos ξ hξ
  have hd : HasDerivAt (fun s : ℝ => s ^ p / p) (F ξ ^ (p - 1)) (F ξ) := by
    have h := (Real.hasDerivAt_rpow_const (x := F ξ) (p := p) (Or.inl hFξ.ne')).div_const p
    have hp0 : p ≠ 0 := by linarith
    exact h.congr_deriv (mul_div_cancel_left₀ _ hp0)
  have hg : HasGradientAt F (gradient F ξ) ξ :=
    ((hF.contDiffAt hξ).differentiableAt (by simp)).hasGradientAt
  have h := hd.comp_hasFDerivAt ξ (hasGradientAt_iff_hasFDerivAt.1 hg)
  rw [hasGradientAt_iff_hasFDerivAt, flux, map_smul]
  exact h

/-- **Symmetry of `A(q) = Da(q)`** for `q ≠ 0`: the flux is the gradient of the potential
`F^p / p`, and Hessians are symmetric.

(The same statement is `IsSmoothStrictNorm.inner_fderiv_flux_comm` in
`WangXia.EigenvalueConvexHessian`.) -/
theorem inner_fderiv_flux_comm {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {p : ℝ} (hp : 1 < p)
    {q : Euc d} (hq : q ≠ 0) (ζ ζ' : Euc d) :
    ⟪fderiv ℝ (flux p F) q ζ, ζ'⟫ = ⟪ζ, fderiv ℝ (flux p F) q ζ'⟫ := by
  have hev : ∀ᶠ ξ in 𝓝 q, ξ ≠ 0 := isOpen_compl_singleton.mem_nhds hq
  have hd : ∀ᶠ ξ in 𝓝 q, DifferentiableAt ℝ (fun x => F x ^ p / p) ξ := by
    filter_upwards [hev] with ξ hξ
    exact (hasGradientAt_flux_potential hF hp hξ).differentiableAt
  have hgrad : flux p F =ᶠ[𝓝 q] gradient fun x => F x ^ p / p := by
    filter_upwards [hev] with ξ hξ
    exact (hasGradientAt_flux_potential hF hp hξ).gradient.symm
  have hH : HasFDerivAt (gradient fun x => F x ^ p / p) (fderiv ℝ (flux p F) q) q :=
    (hF.hasFDerivAt_flux' p hq).congr_of_eventuallyEq hgrad.symm
  exact inner_fderiv_gradient_comm hd hH ζ ζ'

/-- **Positive semidefiniteness of `A(q) = Da(q)`** for `q ≠ 0`, from the pointwise ellipticity
`IsSmoothStrictNorm.inner_fderiv_flux_pos` (paper (A.ellipticity)). -/
theorem inner_fderiv_flux_nonneg {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {p : ℝ} (hp : 1 < p)
    {q : Euc d} (hq : q ≠ 0) (ζ : Euc d) : 0 ≤ ⟪fderiv ℝ (flux p F) q ζ, ζ⟫ := by
  rcases eq_or_ne ζ 0 with rfl | hζ
  · simp
  · exact (hF.inner_fderiv_flux_pos hp hq hζ).le

/-! ### The trace step in divergence form -/

/-- **The flux divergence as a trace** (the chain rule): at a point where `∇v ≠ 0` and `∇v` is
differentiable, `div a(∇v) = tr(A(∇v) D²v)` with `A(ξ) = Da(ξ)`. -/
theorem divergence_flux_gradient_eq {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) (p : ℝ)
    {v : Euc d → ℝ} {x : Euc d} {H : Euc d →L[ℝ] Euc d} (hq : gradient v x ≠ 0)
    (hH : HasFDerivAt (gradient v) H x) :
    divergence (fun z => flux p F (gradient v z)) x =
      ∑ i, ⟪EuclideanSpace.single i (1 : ℝ),
        fderiv ℝ (flux p F) (gradient v x) (H (EuclideanSpace.single i (1 : ℝ)))⟫ :=
  divergence_comp (a := flux p F) (G := gradient v) (hF.hasFDerivAt_flux' p hq) hH

/-- **Korevaar's interior second-order step** (MRS24, Theorem 1.1; the trace step): at an
interior local maximum `(x, y)` of the concavity function of `v`, at which the three gradients
coincide (`gradient_eq_of_isLocalMax_pair`) and do not vanish, the flux divergence of `∇v` at the
midpoint is dominated by the average of its values at `x` and `y`,

  `div a(∇v)(m) ≤ (div a(∇v)(x) + div a(∇v)(y)) / 2`.

Proof: the second-order conditions (`inner_hessian_midpoint_le_of_isLocalMax`) give the Loewner
inequality `D²v(m) ⪯ (D²v(x) + D²v(y))/2`; the common gradient `q` makes the ellipticity matrix
`A(q) = Da(q)` the *same* at the three points, and it is symmetric (`inner_fderiv_flux_comm`) and
positive semidefinite (`inner_fderiv_flux_nonneg`), so the trace against it is monotone
(`trace_midpoint_le`). -/
theorem divergence_flux_gradient_midpoint_le {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {v : Euc d → ℝ} {x y : Euc d} {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v) Hx x) (hHy : HasFDerivAt (gradient v) Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y)) (hq : gradient v x ≠ 0)
    (hqy : gradient v y = gradient v x)
    (hqm : gradient v (midpoint ℝ x y) = gradient v x)
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y)) :
    divergence (fun z => flux p F (gradient v z)) (midpoint ℝ x y) ≤
      (divergence (fun z => flux p F (gradient v z)) x +
        divergence (fun z => flux p F (gradient v z)) y) / 2 := by
  have hqy' : gradient v y ≠ 0 := by rw [hqy]; exact hq
  have hqm' : gradient v (midpoint ℝ x y) ≠ 0 := by rw [hqm]; exact hq
  rw [divergence_flux_gradient_eq hF p hqm' hHm, divergence_flux_gradient_eq hF p hq hHx,
    divergence_flux_gradient_eq hF p hqy' hHy, hqy, hqm]
  exact trace_midpoint_le (inner_fderiv_flux_comm hF hp hq) (inner_fderiv_flux_nonneg hF hp hq)
    (inner_hessian_midpoint_le_of_isLocalMax hdx hdy hdm hHx hHy hHm hmax)

/-- **The degenerate case of Korevaar's interior step**: if in addition the three flux
divergences satisfy the trace inequality with *equality* — which is what the transformed equation
`div a(∇v) = λ + (p-1) F(∇v)^p` forces, since the three gradients agree — then the second-order
conditions hold with equality as well:

  `D²v(m)[ζ, ζ] = (D²v(x)[ζ, ζ] + D²v(y)[ζ, ζ]) / 2`   for **every** `ζ`.

This is the point at which Korevaar's argument invokes the strong maximum principle for the
linearized operator: the concavity function then has to be constant, contradicting `C = 0` on
the diagonal and `C > 0` at the maximum. -/
theorem inner_hessian_midpoint_eq_of_divergence_eq {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {v : Euc d → ℝ} {x y : Euc d} {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v) Hx x) (hHy : HasFDerivAt (gradient v) Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y)) (hq : gradient v x ≠ 0)
    (hqy : gradient v y = gradient v x)
    (hqm : gradient v (midpoint ℝ x y) = gradient v x)
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y))
    (heq : divergence (fun z => flux p F (gradient v z)) (midpoint ℝ x y) =
      (divergence (fun z => flux p F (gradient v z)) x +
        divergence (fun z => flux p F (gradient v z)) y) / 2) (ζ : Euc d) :
    ⟪Hm ζ, ζ⟫ = (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2 := by
  have hqy' : gradient v y ≠ 0 := by rw [hqy]; exact hq
  have hqm' : gradient v (midpoint ℝ x y) ≠ 0 := by rw [hqm]; exact hq
  rw [divergence_flux_gradient_eq hF p hqm' hHm, divergence_flux_gradient_eq hF p hq hHx,
    divergence_flux_gradient_eq hF p hqy' hHy, hqy, hqm] at heq
  exact inner_hessian_eq_of_trace_eq (inner_fderiv_flux_comm hF hp hq)
    (fun ξ hξ => hF.inner_fderiv_flux_pos hp hq hξ)
    (inner_hessian_midpoint_le_of_isLocalMax hdx hdy hdm hHx hHy hHm hmax) heq ζ

/-- **Korevaar's degenerate case, with the transformed equation inserted.** If `v` solves
`div a(∇v) = λ + (p-1) F(∇v)^p` at `x`, at `y` and at their midpoint — the transformed equation
of MRS24, Theorem 1.1 — then at an interior local maximum of the concavity function the three
right-hand sides agree (the three gradients do, by `gradient_eq_of_isLocalMax_pair`), so the
trace inequality of `divergence_flux_gradient_midpoint_le` is saturated and the second-order
conditions hold with *equality* in every direction.

This is precisely the configuration in which Korevaar's argument concludes by the strong maximum
principle for the linearized operator. -/
theorem inner_hessian_midpoint_eq_of_equation {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {v : Euc d → ℝ} {x y : Euc d} {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    {lam : ℝ}
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v) Hx x) (hHy : HasFDerivAt (gradient v) Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y)) (hq : gradient v x ≠ 0)
    (hqy : gradient v y = gradient v x)
    (hqm : gradient v (midpoint ℝ x y) = gradient v x)
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn v z.1 z.2) (x, y))
    (hEx : divergence (fun z => flux p F (gradient v z)) x = lam + (p - 1) * F (gradient v x) ^ p)
    (hEy : divergence (fun z => flux p F (gradient v z)) y = lam + (p - 1) * F (gradient v y) ^ p)
    (hEm : divergence (fun z => flux p F (gradient v z)) (midpoint ℝ x y) =
      lam + (p - 1) * F (gradient v (midpoint ℝ x y)) ^ p) (ζ : Euc d) :
    ⟪Hm ζ, ζ⟫ = (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2 := by
  have heq : divergence (fun z => flux p F (gradient v z)) (midpoint ℝ x y) =
      (divergence (fun z => flux p F (gradient v z)) x +
        divergence (fun z => flux p F (gradient v z)) y) / 2 := by
    rw [hEm, hEx, hEy, hqm, hqy]
    ring
  exact inner_hessian_midpoint_eq_of_divergence_eq hp hF hdx hdy hdm hHx hHy hHm hq hqy hqm hmax
    heq ζ

/-! ### The transformed equation for `v = -log φ` -/

/-- `∇F(cξ) = -∇F(ξ)` for `c < 0` and `ξ ≠ 0` (`F` is even and `1`-homogeneous).

(The same statement is `IsSmoothStrictNorm.gradient_smul_of_neg` in
`WangXia.EigenvalueConvexHessian`.) -/
theorem gradient_smul_of_neg {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {c : ℝ} (hc : c < 0)
    {ξ : Euc d} (hξ : ξ ≠ 0) : gradient F (c • ξ) = -gradient F ξ := by
  have hcξ : c • ξ ≠ 0 := smul_ne_zero hc.ne hξ
  have h1 : HasFDerivAt F (fderiv ℝ F (c • ξ)) (c • ξ) :=
    ((hF.contDiffAt hcξ).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fun y => F (c • y))
      ((fderiv ℝ F (c • ξ)).comp (c • ContinuousLinearMap.id ℝ (Euc d))) ξ :=
    h1.comp ξ ((hasFDerivAt_id ξ).const_smul c)
  have h3 : HasFDerivAt (fun y => F (c • y)) (|c| • fderiv ℝ F ξ) ξ := by
    have heq : (fun y => F (c • y)) = fun y => |c| * F y := funext fun y => hF.homog c y
    rw [heq]
    exact ((hF.contDiffAt hξ).differentiableAt (by simp)).hasFDerivAt.const_mul |c|
  have h4 := h2.unique h3
  refine ext_inner_right ℝ fun h => ?_
  have h5 := congrArg (fun L : Euc d →L[ℝ] ℝ => L h) h4
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, ← inner_gradient_left,
    abs_of_neg hc] at h5
  rw [inner_neg_left]
  refine mul_left_cancel₀ hc.ne ?_
  linear_combination h5

/-- Homogeneity of the flux: `a(cξ) = -|c|^{p-1} a(ξ)` for `c < 0`. -/
theorem flux_smul_of_neg {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {p : ℝ} (hp : 1 < p)
    {c : ℝ} (hc : c < 0) (ξ : Euc d) :
    flux p F (c • ξ) = -(|c| ^ (p - 1) • flux p F ξ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [flux_zero hp hF]
  rw [flux, flux, hF.homog, gradient_smul_of_neg hF hc hξ,
    Real.mul_rpow (abs_nonneg c) (hF.nonneg ξ), smul_neg, smul_smul]

/-- The gradient of `y ↦ exp (-(a v y))`. -/
theorem hasGradientAt_exp_neg_mul {v : Euc d → ℝ} {x g : Euc d} (hv : HasGradientAt v g x)
    (a : ℝ) :
    HasGradientAt (fun y => Real.exp (-(a * v y))) (-(a * Real.exp (-(a * v x))) • g) x := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(a * s))) (-(a * Real.exp (-(a * v x))))
      (v x) := by
    have h := ((hasDerivAt_id (v x)).const_mul a).neg.exp
    simpa [mul_comm] using h
  have h := hexp.comp_hasFDerivAt x (hasGradientAt_iff_hasFDerivAt.1 hv)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h.congr_fderiv ?_
  rw [map_smul]

/-- The gradient of `-f`. -/
theorem hasGradientAt_neg' {f : Euc d → ℝ} {f' x : Euc d} (hf : HasGradientAt f f' x) :
    HasGradientAt (fun y => -f y) (-f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  rw [map_neg]
  exact hf.neg

/-- **The flux-divergence of `e^{-v}`** (paper Appendix A: "Evenness and homogeneity give, at
noncritical points, `div a(∇e^{-v}) = e^{-(p-1)v}((p-1)F(∇v)^p - div a(∇v))`"): for `v`
differentiable near `x` with `∇v` differentiable at `x` and `∇v(x) ≠ 0`.

(The same statement is `divergence_flux_gradient_exp_neg` in
`WangXia.EigenvalueConvexHessian`.) -/
theorem divergence_flux_gradient_exp_neg {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {v : Euc d → ℝ} {x : Euc d}
    (hv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y) (hv' : DifferentiableAt ℝ (gradient v) x)
    (hx : gradient v x ≠ 0) :
    divergence (fun y => flux p F (gradient (fun y => Real.exp (-v y)) y)) x =
      Real.exp (-((p - 1) * v x)) *
        ((p - 1) * F (gradient v x) ^ p - divergence (fun y => flux p F (gradient v y)) x) := by
  -- the gradient of `e^{-v}` near `x`
  have hgrad : ∀ᶠ y in 𝓝 x,
      gradient (fun y => Real.exp (-v y)) y = (-Real.exp (-v y)) • gradient v y := by
    filter_upwards [hv] with y hy
    have h := hasGradientAt_exp_neg_mul hy.hasGradientAt 1
    simp only [one_mul] at h
    exact h.gradient
  -- the flux field of `e^{-v}` is `-e^{-(p-1)v} a(∇v)`
  have hflux : (fun y => flux p F (gradient (fun y => Real.exp (-v y)) y)) =ᶠ[𝓝 x]
      fun y => (-Real.exp (-((p - 1) * v y))) • flux p F (gradient v y) := by
    filter_upwards [hgrad] with y hy
    rw [hy, flux_smul_of_neg hF hp (neg_neg_of_pos (Real.exp_pos _)), abs_neg,
      abs_of_pos (Real.exp_pos _), ← Real.exp_mul, neg_smul]
    congr 3
    ring
  rw [divergence_congr hflux]
  -- product rule
  have hm : HasGradientAt (fun y => -Real.exp (-((p - 1) * v y)))
      (((p - 1) * Real.exp (-((p - 1) * v x))) • gradient v x) x := by
    have h := hasGradientAt_neg' (hasGradientAt_exp_neg_mul hv.self_of_nhds.hasGradientAt (p - 1))
    rwa [neg_smul, neg_neg] at h
  have hW : HasFDerivAt (fun y => flux p F (gradient v y))
      ((fderiv ℝ (flux p F) (gradient v x)).comp (fderiv ℝ (gradient v) x)) x :=
    (hF.hasFDerivAt_flux' p hx).comp x hv'.hasFDerivAt
  rw [divergence_smul hm hW, real_inner_smul_left, real_inner_comm,
    hF.inner_flux_self_eq_rpow hp]
  ring

/-- **The log-eigenfunction equation** (paper (A.log-eigenfunction)): if `φ > 0` near `x`, is
differentiable there, and satisfies the *pointwise* ("strong") eigenvalue equation
`div a(∇φ) + λ φ^{p-1} = 0` at `x`, then the transform `v = -log φ` satisfies

  `div a(∇v) = λ + (p-1) F(∇v)^p`   at `x`,

provided `∇v(x) ≠ 0` and `∇v` is differentiable at `x`.

This is the equation Korevaar's concavity maximum principle is applied to: its right-hand side
is a **convex** function of `∇v` (`convexOn_rpow_of_isSmoothStrictNorm`), which is the
concavity-preserving structure condition, and at an interior maximum of the concavity function
the three gradients agree (`gradient_eq_of_isLocalMax_pair`), so the right-hand side takes the
same value at `x`, `y` and their midpoint.

(The same statement, for an `EigenfunctionData`, is
`EigenfunctionData.divergence_flux_gradient_neg_log` in `WangXia.EigenvalueConvexOffCritical`;
it is reproved here because that file imports `EigenfunctionData`, which imports
`LogConcave`.) -/
theorem divergence_flux_gradient_neg_log {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {φ : Euc d → ℝ} {x : Euc d} {lam : ℝ}
    (hpos : ∀ᶠ y in 𝓝 x, 0 < φ y)
    (hv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => -Real.log (φ y)) y)
    (hv' : DifferentiableAt ℝ (gradient fun y => -Real.log (φ y)) x)
    (hx' : gradient (fun y => -Real.log (φ y)) x ≠ 0)
    (hstrong : divergence (fun y => flux p F (gradient φ y)) x + lam * φ x ^ (p - 1) = 0) :
    divergence (fun y => flux p F (gradient (fun y => -Real.log (φ y)) y)) x =
      lam + (p - 1) * F (gradient (fun y => -Real.log (φ y)) x) ^ p := by
  have hφx : 0 < φ x := hpos.self_of_nhds
  -- `e^{-v} = φ` near `x`
  have heq : (fun y => Real.exp (-(-Real.log (φ y)))) =ᶠ[𝓝 x] φ := by
    filter_upwards [hpos] with y hy
    rw [neg_neg, Real.exp_log hy]
  have hflux : (fun y => flux p F (gradient (fun y => Real.exp (-(-Real.log (φ y)))) y)) =ᶠ[𝓝 x]
      fun y => flux p F (gradient φ y) := by
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    rw [hy.gradient_eq]
  have hexp : divergence (fun y => flux p F (gradient φ y)) x =
      Real.exp (-((p - 1) * -Real.log (φ x))) *
        ((p - 1) * F (gradient (fun y => -Real.log (φ y)) x) ^ p -
          divergence (fun y => flux p F (gradient (fun y => -Real.log (φ y)) y)) x) := by
    rw [← divergence_congr hflux]
    exact divergence_flux_gradient_exp_neg hp hF hv hv' hx'
  have hφpow : φ x ^ (p - 1) = Real.exp (-((p - 1) * -Real.log (φ x))) := by
    rw [Real.rpow_def_of_pos hφx]
    congr 1
    ring
  rw [hφpow, hexp] at hstrong
  have h0 : Real.exp (-((p - 1) * -Real.log (φ x))) *
      ((p - 1) * F (gradient (fun y => -Real.log (φ y)) x) ^ p -
        divergence (fun y => flux p F (gradient (fun y => -Real.log (φ y)) y)) x + lam) = 0 := by
    linear_combination hstrong
  have h1 := (mul_eq_zero.1 h0).resolve_left (Real.exp_pos _).ne'
  linarith

end Korevaar

end Komlos.Literature
