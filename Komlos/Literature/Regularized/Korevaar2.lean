import Komlos.Literature.PLaplacian.KorevaarApproximation

/-!
# Korevaar's concavity maximum principle for two solutions

This file generalizes the one-function Korevaar material of
`Komlos/Literature/PLaplacian/KorevaarNonlinearMaximum.lean` and
`Komlos/Literature/PLaplacian/KorevaarApproximation.lean` to *two* solutions of the *same*
quasilinear operator with *different* constants, which is the form needed by the regularized
closure route (`REGULARIZED_ROUTE.md`, "Korevaar with two functions"): on a large open convex
domain `Ω` a solution `v` of

  `div (fluxA (∇v)) = κ v + c + reaction (∇v)`

is compared with a solution `v'` of the same equation with constant `c'` on an inner domain
`Ω' ⊆ Ω`.  The comparison object is the *two-function concavity function*

  `Φ (x, y) = v (midpoint x y) - (v' x + v' y) / 2`   (`concavityFn₂`).

Both equations are packaged by the existing structure
`Komlos.Literature.Korevaar.IsSmoothAffineReactionSolution`, whose `reaction` slot absorbs the
constant (`fun q => c + reaction q`); in particular the `elliptic` field supplies a symmetric
positive semidefinite `A = D fluxA` at the relevant gradients.

## Main results

* `concavityFn₂_le_of_isLocalMax` — **the pointwise two-point lemma**: at an interior local
  maximum of `Φ` the three gradients `∇v (m)`, `∇v' x`, `∇v' y` coincide (so the *same* matrix
  `A = D fluxA(q)` and the *same* value `reaction q` occur at all three points), the pair second
  variation gives `D²v(m) ⪯ (D²v'(x) + D²v'(y))/2`, and tracing against `A ⪰ 0` leaves
  `κ Φ (x, y) ≤ c' - c`.
* `concavityFn₂_le_max` — **the global lemma**: if `Ω'` is bounded with `closure Ω' ⊆ Ω`, `v` is
  continuous on `Ω`, and `v'` is continuous, bounded below, and has compact sublevel sets in `Ω'`
  (the `IsInputData.isCompact_sublevel` form of "`v' → +∞` at `∂Ω'`"), then a positive supremum of
  `Φ` is attained at an interior pair, and hence
  `Φ (x, y) ≤ max 0 ((c' - c) / κ)` for all `x, y ∈ Ω'`.
* `mul_le_exp_mul_sq_of_affine_reaction` — the same statement for `v = -log φ`, `v' = -log φ'`:
  `φ' x * φ' y ≤ exp (2 max 0 ((c' - c)/κ)) * φ (midpoint x y) ^ 2`.
* `convexOn_neg_log_of_tendsto_midpoint` — **the limit lemma** (pure real analysis): an almost
  everywhere limit of functions satisfying the midpoint inequality with errors `δ n → 0` on an
  exhausting sequence of open subsets has convex negative logarithm.

Nothing here constructs solutions; existence, regularity and the convergence of the inner
domains belong to the other lanes of the regularized route.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

noncomputable section

namespace Komlos.Literature.Regularized

open Korevaar

variable {d : ℕ}

/-! ### The two-function concavity function -/

/-- **The two-function concavity function** `Φ (x, y) = v (midpoint x y) - (v' x + v' y) / 2`.
For `v' = v` this is `Komlos.Literature.concavityFn`. -/
def concavityFn₂ (v v' : Euc d → ℝ) (x y : Euc d) : ℝ :=
  v (midpoint ℝ x y) - (v' x + v' y) / 2

theorem concavityFn₂_self (v : Euc d → ℝ) (x y : Euc d) :
    concavityFn₂ v v x y = concavityFn v x y := rfl

/-- `Φ` is symmetric, because the midpoint is. -/
theorem concavityFn₂_comm (v v' : Euc d → ℝ) (x y : Euc d) :
    concavityFn₂ v v' x y = concavityFn₂ v v' y x := by
  simp only [concavityFn₂]
  rw [midpoint_comm]
  ring

/-- A local maximum of `Φ` on the pair restricts to a local maximum in the first variable. -/
theorem isLocalMax_left₂ {v v' : Euc d → ℝ} {x y : Euc d}
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn₂ v v' z.1 z.2) (x, y)) :
    IsLocalMax (fun z : Euc d => concavityFn₂ v v' z y) x := by
  have hcont : Continuous fun z : Euc d => ((z, y) : Euc d × Euc d) := by fun_prop
  have hten : Tendsto (fun z : Euc d => ((z, y) : Euc d × Euc d)) (𝓝 x) (𝓝 (x, y)) := by
    simpa using hcont.tendsto x
  exact hten.eventually hmax

/-- A local maximum of `Φ` on the pair restricts to a local maximum in the second variable,
stated in the first-variable form via `concavityFn₂_comm`. -/
theorem isLocalMax_right₂ {v v' : Euc d → ℝ} {x y : Euc d}
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn₂ v v' z.1 z.2) (x, y)) :
    IsLocalMax (fun z : Euc d => concavityFn₂ v v' z x) y := by
  have hcont : Continuous fun z : Euc d => ((x, z) : Euc d × Euc d) := by fun_prop
  have hten : Tendsto (fun z : Euc d => ((x, z) : Euc d × Euc d)) (𝓝 y) (𝓝 (x, y)) := by
    simpa using hcont.tendsto y
  have h : ∀ᶠ z : Euc d in 𝓝 y, concavityFn₂ v v' x z ≤ concavityFn₂ v v' x y :=
    hten.eventually hmax
  filter_upwards [h] with z hz
  rwa [concavityFn₂_comm v v' z x, concavityFn₂_comm v v' y x]

/-! ### First-order conditions -/

/-- **First-order condition in the first variable** (the two-function form of
`gradient_eq_of_isLocalMax_concavityFn`): if `z ↦ Φ (z, y)` has a local maximum at `x`, then
`∇v (midpoint x y) = ∇v' x`. -/
theorem gradient_eq_of_isLocalMax_left₂ {v v' : Euc d → ℝ} {x y gx gm : Euc d}
    (hvx : HasGradientAt v' gx x) (hvm : HasGradientAt v gm (midpoint ℝ x y))
    (hmax : IsLocalMax (fun z => concavityFn₂ v v' z y) x) : gm = gx := by
  have key : ∀ w : Euc d, ⟪gm - gx, w⟫ = 0 := by
    intro w
    have hline : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hcontline : Continuous fun t : ℝ => x + t • w := by fun_prop
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
    have hd1 : HasDerivAt (fun t : ℝ => v (midpoint ℝ (x + t • w) y)) ⟪gm, (2 : ℝ)⁻¹ • w⟫ 0 := by
      have h := (hasGradientAt_iff_hasFDerivAt.1 hvm).comp_hasDerivAt_of_eq (0 : ℝ) hmidline
        (by simp)
      rw [InnerProductSpace.toDual_apply_apply] at h
      exact h
    have hd2 : HasDerivAt (fun t : ℝ => v' (x + t • w)) ⟪gx, w⟫ 0 := by
      have h := (hasGradientAt_iff_hasFDerivAt.1 hvx).comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
      rw [InnerProductSpace.toDual_apply_apply] at h
      exact h
    have hdC : HasDerivAt (fun t : ℝ => concavityFn₂ v v' (x + t • w) y)
        (⟪gm, (2 : ℝ)⁻¹ • w⟫ - ⟪gx, w⟫ / 2) 0 := by
      simp only [concavityFn₂]
      exact hd1.sub ((hd2.add_const (v' y)).div_const 2)
    have hmaxline : IsLocalMax (fun t : ℝ => concavityFn₂ v v' (x + t • w) y) 0 := by
      have hmax' : IsLocalMax (fun z => concavityFn₂ v v' z y) ((fun t : ℝ => x + t • w) 0) := by
        simpa using hmax
      exact hmax'.comp_continuous (g := fun t : ℝ => x + t • w) (b := 0) hcontline.continuousAt
    have hzero := hmaxline.hasDerivAt_eq_zero hdC
    rw [real_inner_smul_right] at hzero
    rw [inner_sub_left]
    linarith
  have h := key (gm - gx)
  rw [real_inner_self_eq_norm_sq] at h
  have hn : ‖gm - gx‖ = 0 := by nlinarith [norm_nonneg (gm - gx)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hn)

/-- **The first-order conditions at an interior maximum of `Φ`**: the three gradients coincide,
`∇v (midpoint x y) = ∇v' x = ∇v' y`.  Consequently the reaction `reaction (∇·)` takes the same
value at the three points, and the *same* ellipticity matrix `A = D fluxA(q)` occurs there. -/
theorem gradient_eq_of_isLocalMax_pair₂ {v v' : Euc d → ℝ} {x y gx gy gm : Euc d}
    (hvx : HasGradientAt v' gx x) (hvy : HasGradientAt v' gy y)
    (hvm : HasGradientAt v gm (midpoint ℝ x y))
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn₂ v v' z.1 z.2) (x, y)) :
    gm = gx ∧ gm = gy := by
  refine ⟨gradient_eq_of_isLocalMax_left₂ hvx hvm (isLocalMax_left₂ hmax), ?_⟩
  have hvm' : HasGradientAt v gm (midpoint ℝ y x) := by rwa [midpoint_comm]
  exact gradient_eq_of_isLocalMax_left₂ hvy hvm' (isLocalMax_right₂ hmax)

/-! ### Second-order conditions -/

/-- **The diagonal defect has a local minimum**: moving the pair along `(ζ, ζ)` moves the
midpoint along `ζ`, so `s ↦ -v (m + sζ) + (v' (x + sζ) + v' (y + sζ))/2` has a local minimum
at `s = 0`. -/
theorem isLocalMin_line_of_isLocalMax₂ {v v' : Euc d → ℝ} {x y : Euc d}
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn₂ v v' z.1 z.2) (x, y)) (ζ : Euc d) :
    IsLocalMin (fun s : ℝ => -v (midpoint ℝ x y + s • ζ)
      + (v' (x + s • ζ) + v' (y + s • ζ)) / 2) 0 := by
  have hcont : Continuous fun s : ℝ => ((x + s • ζ, y + s • ζ) : Euc d × Euc d) := by fun_prop
  have hten : Tendsto (fun s : ℝ => ((x + s • ζ, y + s • ζ) : Euc d × Euc d)) (𝓝 0)
      (𝓝 (x, y)) := by
    simpa using hcont.tendsto 0
  have h : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
      concavityFn₂ v v' (x + s • ζ) (y + s • ζ) ≤ concavityFn₂ v v' x y := hten.eventually hmax
  filter_upwards [h] with s hs
  simp only [concavityFn₂, midpoint_add_smul] at hs
  simp only [zero_smul, add_zero]
  linarith

/-- **The second-order conditions for the two-function concavity function**: at a local maximum
of `Φ` the Hessian of `v` at the midpoint is dominated, in the Loewner order, by the average of
the Hessians of `v'` at the endpoints,

  `D²v(m)[ζ, ζ] ≤ (D²v'(x)[ζ, ζ] + D²v'(y)[ζ, ζ]) / 2`. -/
theorem inner_hessian_midpoint_le_of_isLocalMax₂ {v v' : Euc d → ℝ} {x y : Euc d}
    {Hx Hy Hm : Euc d →L[ℝ] Euc d}
    (hdx : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ v' z)
    (hdy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ v' z)
    (hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z)
    (hHx : HasFDerivAt (gradient v') Hx x) (hHy : HasFDerivAt (gradient v') Hy y)
    (hHm : HasFDerivAt (gradient v) Hm (midpoint ℝ x y))
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn₂ v v' z.1 z.2) (x, y)) (ζ : Euc d) :
    ⟪Hm ζ, ζ⟫ ≤ (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2 := by
  obtain ⟨hx1, hx2⟩ := hasDerivAt_inner_gradient_line hdx hHx ζ
  obtain ⟨hy1, hy2⟩ := hasDerivAt_inner_gradient_line hdy hHy ζ
  obtain ⟨hm1, hm2⟩ := hasDerivAt_inner_gradient_line hdm hHm ζ
  have hψd : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), HasDerivAt
      (fun s : ℝ => -v (midpoint ℝ x y + s • ζ) + (v' (x + s • ζ) + v' (y + s • ζ)) / 2)
      (-⟪gradient v (midpoint ℝ x y + s • ζ), ζ⟫
        + (⟪gradient v' (x + s • ζ), ζ⟫ + ⟪gradient v' (y + s • ζ), ζ⟫) / 2) s := by
    filter_upwards [hx1, hy1, hm1] with s hsx hsy hsm
    exact hsm.neg.add ((hsx.add hsy).div_const 2)
  have hderiv : deriv (fun s : ℝ =>
        -v (midpoint ℝ x y + s • ζ) + (v' (x + s • ζ) + v' (y + s • ζ)) / 2) =ᶠ[𝓝 (0 : ℝ)]
      fun s : ℝ => -⟪gradient v (midpoint ℝ x y + s • ζ), ζ⟫
        + (⟪gradient v' (x + s • ζ), ζ⟫ + ⟪gradient v' (y + s • ζ), ζ⟫) / 2 := by
    filter_upwards [hψd] with s hs
    exact hs.deriv
  have h2 : HasDerivAt (fun s : ℝ => -⟪gradient v (midpoint ℝ x y + s • ζ), ζ⟫
        + (⟪gradient v' (x + s • ζ), ζ⟫ + ⟪gradient v' (y + s • ζ), ζ⟫) / 2)
      (-⟪Hm ζ, ζ⟫ + (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2) 0 :=
    hm2.neg.add ((hx2.add hy2).div_const 2)
  have hd2 : HasDerivAt (deriv fun s : ℝ =>
      -v (midpoint ℝ x y + s • ζ) + (v' (x + s • ζ) + v' (y + s • ζ)) / 2)
      (-⟪Hm ζ, ζ⟫ + (⟪Hx ζ, ζ⟫ + ⟪Hy ζ, ζ⟫) / 2) 0 := h2.congr_of_eventuallyEq hderiv
  have hkey := nonneg_of_isLocalMin_of_hasDerivAt_deriv
    (isLocalMin_line_of_isLocalMax₂ hmax ζ) (hψd.mono fun s hs => hs.differentiableAt) hd2
  linarith

/-! ### The pointwise two-point lemma -/

/-- **The two-function two-point maximum lemma.**  Let `v` solve
`div (fluxA (∇v)) = κ v + c + reaction (∇v)` on the open set `Ω`, and let `v'` solve the same
equation with constant `c'` on the open convex `Ω' ⊆ Ω`.  If

  `Φ (x, y) = v (midpoint x y) - (v' x + v' y)/2`

has a local maximum at a pair `(x, y) ∈ Ω' ×ˢ Ω'`, then `κ Φ (x, y) ≤ c' - c`.

Proof: the first-order conditions (`gradient_eq_of_isLocalMax_pair₂`) give a common gradient
`q = ∇v (m) = ∇v' x = ∇v' y`, so the *same* symmetric positive semidefinite
`A = D fluxA (q)` (the `elliptic` field of `IsSmoothAffineReactionSolution` at the midpoint) and
the *same* value `reaction q` appear at all three points.  The second-order conditions
(`inner_hessian_midpoint_le_of_isLocalMax₂`) give `D²v(m) ⪯ (D²v'(x) + D²v'(y))/2`, and tracing
against `A ⪰ 0` (`trace_midpoint_le`, via `divergence_comp`) turns this into
`κ v(m) + c ≤ κ (v' x + v' y)/2 + c'`. -/
theorem concavityFn₂_le_of_isLocalMax
    {Ω Ω' : Set (Euc d)} {fluxA : Euc d → Euc d} {reaction v v' : Euc d → ℝ} {κ c c' : ℝ}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hconv' : Convex ℝ Ω') (hsub : Ω' ⊆ Ω)
    (hsol : IsSmoothAffineReactionSolution Ω fluxA (fun q => c + reaction q) v κ)
    (hsol' : IsSmoothAffineReactionSolution Ω' fluxA (fun q => c' + reaction q) v' κ)
    {x y : Euc d} (hx : x ∈ Ω') (hy : y ∈ Ω')
    (hmax : IsLocalMax (fun z : Euc d × Euc d => concavityFn₂ v v' z.1 z.2) (x, y)) :
    κ * concavityFn₂ v v' x y ≤ c' - c := by
  have hm' : midpoint ℝ x y ∈ Ω' := hconv'.midpoint_mem hx hy
  have hm : midpoint ℝ x y ∈ Ω := hsub hm'
  have hd' : ∀ a ∈ Ω', ∀ᶠ z in 𝓝 a, DifferentiableAt ℝ v' z := by
    intro a ha
    filter_upwards [hΩ'.mem_nhds ha] with z hz
    exact hsol'.differentiable.differentiableAt (hΩ'.mem_nhds hz)
  have hdm : ∀ᶠ z in 𝓝 (midpoint ℝ x y), DifferentiableAt ℝ v z := by
    filter_upwards [hΩ.mem_nhds hm] with z hz
    exact hsol.differentiable.differentiableAt (hΩ.mem_nhds hz)
  have hH' : ∀ a ∈ Ω', HasFDerivAt (gradient v') (fderiv ℝ (gradient v') a) a :=
    fun a ha => (hsol'.gradient_differentiable.differentiableAt (hΩ'.mem_nhds ha)).hasFDerivAt
  have hHm : HasFDerivAt (gradient v) (fderiv ℝ (gradient v) (midpoint ℝ x y))
      (midpoint ℝ x y) :=
    (hsol.gradient_differentiable.differentiableAt (hΩ.mem_nhds hm)).hasFDerivAt
  -- first-order conditions: a common gradient at the three points
  obtain ⟨hqx, hqy⟩ := gradient_eq_of_isLocalMax_pair₂
    (hd' x hx).self_of_nhds.hasGradientAt (hd' y hy).self_of_nhds.hasGradientAt
    hdm.self_of_nhds.hasGradientAt hmax
  have hxy : gradient v' y = gradient v' x := hqy.symm.trans hqx
  -- the same ellipticity matrix at all three points
  obtain ⟨A, hA, hAs, hA0⟩ := hsol.elliptic _ hm
  have hAx : HasFDerivAt fluxA A (gradient v' x) := by rw [← hqx]; exact hA
  have hAy : HasFDerivAt fluxA A (gradient v' y) := by rw [← hqy]; exact hA
  -- the three flux divergences as traces
  have htm := divergence_comp (a := fluxA) (G := gradient v) hA hHm
  have htx := divergence_comp (a := fluxA) (G := gradient v') hAx (hH' x hx)
  have hty := divergence_comp (a := fluxA) (G := gradient v') hAy (hH' y hy)
  -- the traced Loewner inequality
  have htrace := trace_midpoint_le hAs hA0
    (inner_hessian_midpoint_le_of_isLocalMax₂ (hd' x hx) (hd' y hy) hdm
      (hH' x hx) (hH' y hy) hHm hmax)
  -- the equations, with the common gradient inserted in the reaction
  have hEm := hsol.equation _ hm
  have hEx := hsol'.equation x hx
  have hEy := hsol'.equation y hy
  rw [hqx] at hEm
  rw [hxy] at hEy
  rw [← htm, ← htx, ← hty, hEm, hEx, hEy] at htrace
  simp only [concavityFn₂]
  linarith

/-! ### The global lemma -/

/-- **The global two-function maximum principle.**  Assume, in addition to the hypotheses of
`concavityFn₂_le_of_isLocalMax`, that `Ω'` is bounded with `closure Ω' ⊆ Ω`, that `v` is
continuous on `Ω`, and that `v'` is continuous on `Ω'`, bounded below there, and has compact
sublevel sets `{z ∈ Ω' | v' z ≤ M}` (the `IsInputData.isCompact_sublevel` formulation of
"`v' → +∞` at the frontier of `Ω'`").  Then

  `v (midpoint x y) - (v' x + v' y)/2 ≤ max 0 ((c' - c) / κ)`   for all `x, y ∈ Ω'`.

Proof: if some pair violated the bound, the level `a = Φ (x, y) > 0` would confine both entries
of every pair with `Φ ≥ a` to the compact sublevel set `S = {v' ≤ 2 (sup_{closure Ω'} v - a) - b}`
(`v` is bounded above on the compact `closure Ω' ⊆ Ω`, and `v' ≥ b`), so the maximum of `Φ` over
the compact `S ×ˢ S` is a maximum over all of `Ω' ×ˢ Ω'`, in particular an interior local
maximum; the pointwise lemma then bounds it by `(c' - c)/κ ≤ max 0 ((c' - c)/κ) < a`. -/
theorem concavityFn₂_le_max
    {Ω Ω' : Set (Euc d)} {fluxA : Euc d → Euc d} {reaction v v' : Euc d → ℝ} {κ c c' : ℝ}
    (hκ : 0 < κ) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hconv' : Convex ℝ Ω')
    (hbdd : Bornology.IsBounded Ω') (hcl : closure Ω' ⊆ Ω)
    (hvc : ContinuousOn v Ω) (hv'c : ContinuousOn v' Ω')
    (hlb : ∃ b : ℝ, ∀ z ∈ Ω', b ≤ v' z)
    (hsublevel : ∀ M : ℝ, IsCompact {z ∈ Ω' | v' z ≤ M})
    (hsol : IsSmoothAffineReactionSolution Ω fluxA (fun q => c + reaction q) v κ)
    (hsol' : IsSmoothAffineReactionSolution Ω' fluxA (fun q => c' + reaction q) v' κ)
    {x y : Euc d} (hx : x ∈ Ω') (hy : y ∈ Ω') :
    concavityFn₂ v v' x y ≤ max 0 ((c' - c) / κ) := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨b, hb⟩ := hlb
  have hΩ'Ω : Ω' ⊆ Ω := subset_closure.trans hcl
  -- `v` is bounded above on the compact `closure Ω'`
  obtain ⟨z₀, -, hz₀⟩ := hbdd.isCompact_closure.exists_isMaxOn
    ⟨x, subset_closure hx⟩ (hvc.mono hcl)
  have hvB : ∀ z ∈ closure Ω', v z ≤ v z₀ := fun z hz => isMaxOn_iff.1 hz₀ z hz
  -- pairs at level `≥ Φ (x, y)` have both entries in a fixed sublevel set of `v'`
  have hkey : ∀ p ∈ Ω', ∀ q ∈ Ω', concavityFn₂ v v' x y ≤ concavityFn₂ v v' p q →
      v' p ≤ 2 * (v z₀ - concavityFn₂ v v' x y) - b ∧
        v' q ≤ 2 * (v z₀ - concavityFn₂ v v' x y) - b := by
    intro p hp q hq hpq
    have h1 : v (midpoint ℝ p q) ≤ v z₀ :=
      hvB _ (subset_closure (hconv'.midpoint_mem hp hq))
    have h2 : b ≤ v' p := hb p hp
    have h3 : b ≤ v' q := hb q hq
    simp only [concavityFn₂] at hpq ⊢
    constructor <;> linarith
  have hxS : x ∈ {z ∈ Ω' | v' z ≤ 2 * (v z₀ - concavityFn₂ v v' x y) - b} :=
    ⟨hx, (hkey x hx y hy le_rfl).1⟩
  have hyS : y ∈ {z ∈ Ω' | v' z ≤ 2 * (v z₀ - concavityFn₂ v v' x y) - b} :=
    ⟨hy, (hkey x hx y hy le_rfl).2⟩
  -- `Φ` is continuous on `Ω' ×ˢ Ω'`
  have hmidcont : Continuous fun z : Euc d × Euc d => midpoint ℝ z.1 z.2 := by
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    fun_prop
  have hΦcont : ContinuousOn (fun z : Euc d × Euc d => concavityFn₂ v v' z.1 z.2)
      (Ω' ×ˢ Ω') := by
    have hmaps : Set.MapsTo (fun z : Euc d × Euc d => midpoint ℝ z.1 z.2) (Ω' ×ˢ Ω') Ω :=
      fun z hz => hΩ'Ω (hconv'.midpoint_mem hz.1 hz.2)
    have hmfst : Set.MapsTo (Prod.fst : Euc d × Euc d → Euc d) (Ω' ×ˢ Ω') Ω' :=
      fun z hz => hz.1
    have hmsnd : Set.MapsTo (Prod.snd : Euc d × Euc d → Euc d) (Ω' ×ˢ Ω') Ω' :=
      fun z hz => hz.2
    have h1 : ContinuousOn (fun z : Euc d × Euc d => v (midpoint ℝ z.1 z.2)) (Ω' ×ˢ Ω') := by
      have h := hvc.comp hmidcont.continuousOn hmaps
      simpa only [Function.comp_def] using h
    have h2 : ContinuousOn (fun z : Euc d × Euc d => v' z.1) (Ω' ×ˢ Ω') := by
      have h := hv'c.comp continuous_fst.continuousOn hmfst
      simpa only [Function.comp_def] using h
    have h3 : ContinuousOn (fun z : Euc d × Euc d => v' z.2) (Ω' ×ˢ Ω') := by
      have h := hv'c.comp continuous_snd.continuousOn hmsnd
      simpa only [Function.comp_def] using h
    have h4 : ContinuousOn (fun z : Euc d × Euc d =>
        v (midpoint ℝ z.1 z.2) - (v' z.1 + v' z.2) / 2) (Ω' ×ˢ Ω') :=
      h1.sub ((h2.add h3).div_const 2)
    simp only [concavityFn₂]
    exact h4
  -- the maximum over the compact `S ×ˢ S`
  obtain ⟨⟨p, q⟩, hpq, hpqmax⟩ :=
    ((hsublevel (2 * (v z₀ - concavityFn₂ v v' x y) - b)).prod
      (hsublevel (2 * (v z₀ - concavityFn₂ v v' x y) - b))).exists_isMaxOn
      ⟨(x, y), hxS, hyS⟩ (hΦcont.mono (fun z hz => ⟨hz.1.1, hz.2.1⟩))
  have hage : concavityFn₂ v v' x y ≤ concavityFn₂ v v' p q :=
    isMaxOn_iff.1 hpqmax (x, y) ⟨hxS, hyS⟩
  -- it is a maximum over all of `Ω' ×ˢ Ω'`, hence a local maximum
  have hglob : ∀ z ∈ Ω' ×ˢ Ω', concavityFn₂ v v' z.1 z.2 ≤ concavityFn₂ v v' p q := by
    intro z hz
    by_cases hz' : concavityFn₂ v v' x y ≤ concavityFn₂ v v' z.1 z.2
    · obtain ⟨h1, h2⟩ := hkey z.1 hz.1 z.2 hz.2 hz'
      exact isMaxOn_iff.1 hpqmax z ⟨⟨hz.1, h1⟩, ⟨hz.2, h2⟩⟩
    · exact (not_le.1 hz').le.trans hage
  have hloc : IsLocalMax (fun z : Euc d × Euc d => concavityFn₂ v v' z.1 z.2) (p, q) := by
    filter_upwards [(hΩ'.prod hΩ').mem_nhds
      (show ((p, q) : Euc d × Euc d) ∈ Ω' ×ˢ Ω' from ⟨hpq.1.1, hpq.2.1⟩)] with z hz
    exact hglob z hz
  have hpt := concavityFn₂_le_of_isLocalMax hΩ hΩ' hconv' hΩ'Ω hsol hsol'
    hpq.1.1 hpq.2.1 hloc
  have hle : concavityFn₂ v v' p q ≤ (c' - c) / κ := (le_div_iff₀ hκ).2 (by linarith)
  exact absurd (hage.trans (hle.trans (le_max_right _ _))) (not_le.2 hcon)

/-! ### The logarithmic form -/

/-- **The logarithmic form of the global lemma.**  With `v = -log φ` and `v' = -log φ'`, the
conclusion of `concavityFn₂_le_max` reads

  `φ' x * φ' y ≤ exp (2 max 0 ((c' - c)/κ)) * φ (midpoint x y) ^ 2`.

The hypotheses are the natural ones for a consumer: `φ` is continuous and positive on `Ω`, `φ'`
is continuous, positive and bounded above on `Ω'`, and the superlevel sets `{φ' ≥ ε}` of `φ'` are
compact subsets of `Ω'` (which is what "`φ'` extends continuously by `0` to `∂Ω'`" gives). -/
theorem mul_le_exp_mul_sq_of_affine_reaction
    {Ω Ω' : Set (Euc d)} {fluxA : Euc d → Euc d} {reaction φ φ' : Euc d → ℝ} {κ c c' : ℝ}
    (hκ : 0 < κ) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hconv' : Convex ℝ Ω')
    (hbdd : Bornology.IsBounded Ω') (hcl : closure Ω' ⊆ Ω)
    (hφ : ContinuousOn φ Ω) (hφpos : ∀ z ∈ Ω, 0 < φ z)
    (hφ' : ContinuousOn φ' Ω') (hφ'pos : ∀ z ∈ Ω', 0 < φ' z)
    (hub : ∃ B : ℝ, ∀ z ∈ Ω', φ' z ≤ B)
    (hcompact : ∀ ε : ℝ, 0 < ε → IsCompact {z ∈ Ω' | ε ≤ φ' z})
    (hsol : IsSmoothAffineReactionSolution Ω fluxA (fun q => c + reaction q)
      (fun z => -Real.log (φ z)) κ)
    (hsol' : IsSmoothAffineReactionSolution Ω' fluxA (fun q => c' + reaction q)
      (fun z => -Real.log (φ' z)) κ)
    {x y : Euc d} (hx : x ∈ Ω') (hy : y ∈ Ω') :
    φ' x * φ' y ≤ Real.exp (2 * max 0 ((c' - c) / κ)) * φ (midpoint ℝ x y) ^ 2 := by
  have hΩ'Ω : Ω' ⊆ Ω := subset_closure.trans hcl
  have hmΩ : midpoint ℝ x y ∈ Ω := hΩ'Ω (hconv'.midpoint_mem hx hy)
  -- continuity of the logarithmic potentials
  have hvc : ContinuousOn (fun z => -Real.log (φ z)) Ω :=
    (hφ.log fun z hz => (hφpos z hz).ne').neg
  have hv'c : ContinuousOn (fun z => -Real.log (φ' z)) Ω' :=
    (hφ'.log fun z hz => (hφ'pos z hz).ne').neg
  -- `-log φ'` is bounded below because `φ'` is bounded above
  have hlb : ∃ b : ℝ, ∀ z ∈ Ω', b ≤ -Real.log (φ' z) := by
    obtain ⟨B, hB⟩ := hub
    exact ⟨-Real.log B, fun z hz => neg_le_neg (Real.log_le_log (hφ'pos z hz) (hB z hz))⟩
  -- compact sublevel sets of `-log φ'` are compact superlevel sets of `φ'`
  have hsublevel : ∀ M : ℝ, IsCompact {z ∈ Ω' | -Real.log (φ' z) ≤ M} := by
    intro M
    have hset : {z ∈ Ω' | -Real.log (φ' z) ≤ M} = {z ∈ Ω' | Real.exp (-M) ≤ φ' z} := by
      ext z
      constructor
      · rintro ⟨hz, hzM⟩
        exact ⟨hz, (Real.le_log_iff_exp_le (hφ'pos z hz)).1 (by linarith)⟩
      · rintro ⟨hz, hzM⟩
        exact ⟨hz, by linarith [(Real.le_log_iff_exp_le (hφ'pos z hz)).2 hzM]⟩
    rw [hset]
    exact hcompact _ (Real.exp_pos _)
  have hglob := concavityFn₂_le_max hκ hΩ hΩ' hconv' hbdd hcl hvc hv'c hlb hsublevel
    hsol hsol' hx hy
  simp only [concavityFn₂] at hglob
  -- exponentiate
  have hx0 : 0 < φ' x := hφ'pos x hx
  have hy0 : 0 < φ' y := hφ'pos y hy
  have hm0 : 0 < φ (midpoint ℝ x y) := hφpos _ hmΩ
  have e1 : φ' x * φ' y = Real.exp (Real.log (φ' x) + Real.log (φ' y)) := by
    rw [Real.exp_add, Real.exp_log hx0, Real.exp_log hy0]
  have e2 : Real.exp (2 * max 0 ((c' - c) / κ)) * φ (midpoint ℝ x y) ^ 2
      = Real.exp (2 * max 0 ((c' - c) / κ) + 2 * Real.log (φ (midpoint ℝ x y))) := by
    rw [Real.exp_add, two_mul (Real.log (φ (midpoint ℝ x y))), Real.exp_add,
      Real.exp_log hm0]
    ring
  rw [e1, e2]
  exact Real.exp_le_exp.2 (by linarith)

/-! ### The limit lemma -/

/-- **Passing the midpoint inequality to an almost everywhere limit** (pure real analysis, no
PDE).  If `φ` is continuous and positive on the open convex `K`, the sets `K n` increase with
union `K`, `δ n → 0`, the approximants satisfy

  `φ n x * φ n y ≤ exp (δ n) * φ (midpoint x y) ^ 2`   for `x, y ∈ K n`,

and `φ n → φ` almost everywhere, then `-log φ` is convex on `K`.

Proof: on the full-measure set where the convergence holds, the inequality passes to the limit
as `φ x * φ y ≤ φ (midpoint x y) ^ 2`; the complement of a null set is dense in the open `K`, so
continuity of `φ` extends the inequality to all pairs; this is midpoint convexity of `-log φ`
(`concavityFn ≤ 0`), which together with continuity gives convexity
(`convexOn_of_concavityFn_nonpos`). -/
theorem convexOn_neg_log_of_tendsto_midpoint {K : Set (Euc d)} (hK : IsOpen K)
    (hconv : Convex ℝ K) {φ : Euc d → ℝ} (hφ : ContinuousOn φ K) (hpos : ∀ z ∈ K, 0 < φ z)
    {φn : ℕ → Euc d → ℝ} {δ : ℕ → ℝ} {Kn : ℕ → Set (Euc d)}
    (hδ : Tendsto δ atTop (𝓝 0)) (hmono : Monotone Kn) (hunion : ⋃ n, Kn n = K)
    (hineq : ∀ n, ∀ x ∈ Kn n, ∀ y ∈ Kn n,
      φn n x * φn n y ≤ Real.exp (δ n) * φ (midpoint ℝ x y) ^ 2)
    (hae : ∀ᵐ z, Tendsto (fun n => φn n z) atTop (𝓝 (φ z))) :
    ConvexOn ℝ K (fun z => -Real.log (φ z)) := by
  have hnull : volume {z : Euc d | ¬ Tendsto (fun n => φn n z) atTop (𝓝 (φ z))} = 0 :=
    ae_iff.1 hae
  -- the inequality on the full-measure set
  have hlim : ∀ x ∈ K, Tendsto (fun n => φn n x) atTop (𝓝 (φ x)) →
      ∀ y ∈ K, Tendsto (fun n => φn n y) atTop (𝓝 (φ y)) →
      φ x * φ y ≤ φ (midpoint ℝ x y) ^ 2 := by
    intro x hxK hxG y hyK hyG
    obtain ⟨n₁, hn₁⟩ : ∃ n, x ∈ Kn n := by
      have h : x ∈ ⋃ n, Kn n := by rw [hunion]; exact hxK
      simpa using h
    obtain ⟨n₂, hn₂⟩ : ∃ n, y ∈ Kn n := by
      have h : y ∈ ⋃ n, Kn n := by rw [hunion]; exact hyK
      simpa using h
    have hev : ∀ᶠ n in atTop,
        φn n x * φn n y ≤ Real.exp (δ n) * φ (midpoint ℝ x y) ^ 2 := by
      filter_upwards [eventually_ge_atTop (max n₁ n₂)] with n hn
      exact hineq n x (hmono ((le_max_left n₁ n₂).trans hn) hn₁)
        y (hmono ((le_max_right n₁ n₂).trans hn) hn₂)
    have hexp : Tendsto (fun n => Real.exp (δ n)) atTop (𝓝 1) := by
      have h := (Real.continuous_exp.tendsto 0).comp hδ
      simpa only [Function.comp_def, Real.exp_zero] using h
    have hR : Tendsto (fun n => Real.exp (δ n) * φ (midpoint ℝ x y) ^ 2) atTop
        (𝓝 (φ (midpoint ℝ x y) ^ 2)) := by
      simpa using hexp.mul_const (φ (midpoint ℝ x y) ^ 2)
    exact le_of_tendsto_of_tendsto (hxG.mul hyG) hR hev
  -- the full-measure set is dense in the open set `K`
  have hdense : ∀ z ∈ K, ∀ k : ℕ, ∃ w, w ∈ K ∧
      Tendsto (fun n => φn n w) atTop (𝓝 (φ w)) ∧ dist w z < 1 / (k + 1 : ℝ) := by
    intro z hz k
    have hε : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    have hUopen : IsOpen (Metric.ball z (1 / (k + 1 : ℝ)) ∩ K) :=
      Metric.isOpen_ball.inter hK
    have hUpos : 0 < volume (Metric.ball z (1 / (k + 1 : ℝ)) ∩ K) :=
      hUopen.measure_pos volume ⟨z, Metric.mem_ball_self hε, hz⟩
    have hnsub : ¬ (Metric.ball z (1 / (k + 1 : ℝ)) ∩ K ⊆
        {w : Euc d | ¬ Tendsto (fun n => φn n w) atTop (𝓝 (φ w))}) := fun h =>
      absurd (measure_mono_null h hnull) hUpos.ne'
    rw [Set.not_subset] at hnsub
    obtain ⟨w, hwU, hwG⟩ := hnsub
    exact ⟨w, hwU.2, by simpa using hwG, by simpa using hwU.1⟩
  -- extend the inequality to all pairs by continuity
  have hall : ∀ x ∈ K, ∀ y ∈ K, φ x * φ y ≤ φ (midpoint ℝ x y) ^ 2 := by
    intro x hx y hy
    choose xs hxsK hxsG hxsd using hdense x hx
    choose ys hysK hysG hysd using hdense y hy
    have hone : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have htx : Tendsto xs atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun k => dist_nonneg) (fun k => (hxsd k).le) hone
    have hty : Tendsto ys atTop (𝓝 y) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun k => dist_nonneg) (fun k => (hysd k).le) hone
    have htm : Tendsto (fun k => midpoint ℝ (xs k) (ys k)) atTop (𝓝 (midpoint ℝ x y)) := by
      simp only [midpoint_eq_smul_add, invOf_eq_inv]
      exact (htx.add hty).const_smul _
    have hcx : Tendsto (fun k => φ (xs k)) atTop (𝓝 (φ x)) := by
      have h := (hφ.continuousAt (hK.mem_nhds hx)).tendsto.comp htx
      simpa only [Function.comp_def] using h
    have hcy : Tendsto (fun k => φ (ys k)) atTop (𝓝 (φ y)) := by
      have h := (hφ.continuousAt (hK.mem_nhds hy)).tendsto.comp hty
      simpa only [Function.comp_def] using h
    have hcm : Tendsto (fun k => φ (midpoint ℝ (xs k) (ys k))) atTop
        (𝓝 (φ (midpoint ℝ x y))) := by
      have h := (hφ.continuousAt (hK.mem_nhds (hconv.midpoint_mem hx hy))).tendsto.comp htm
      simpa only [Function.comp_def] using h
    exact le_of_tendsto_of_tendsto (hcx.mul hcy) (hcm.pow 2)
      (Eventually.of_forall fun k =>
        hlim _ (hxsK k) (hxsG k) _ (hysK k) (hysG k))
  -- midpoint convexity of `-log φ`, then convexity
  refine convexOn_of_concavityFn_nonpos hconv ((hφ.log fun z hz => (hpos z hz).ne').neg) ?_
  intro x hx y hy
  have h := hall x hx y hy
  have hlog := Real.log_le_log (mul_pos (hpos x hx) (hpos y hy)) h
  rw [Real.log_mul (hpos x hx).ne' (hpos y hy).ne', Real.log_pow] at hlog
  push_cast at hlog
  simp only [concavityFn]
  linarith

end Komlos.Literature.Regularized

end
