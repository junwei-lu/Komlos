import Komlos.Literature.PLaplacian.KorevaarAux

/-!
# Inputs for the concavity maximum principle (Mosconi–Riey–Squassina 2024, Theorem 1.1)

This file collects the parts of Korevaar's *concavity maximum principle* — the proof of MRS24,
Theorem 1.1, i.e. of the log-concavity of the first anisotropic `p`-Laplacian eigenfunction — that
are provable without elliptic-PDE substrate, and isolates the one analytic step that is not.

Write `v = -log φ` for the transform of the (positive, `C¹`, `C²`-off-the-critical-set)
representative `φ` of the eigenfunction. Korevaar's *concavity function* is

  `C(x, y) = v (midpoint x y) - (v x + v y) / 2`,

so `v` is midpoint convex — equivalently, since `v` is continuous, convex — exactly when `C ≤ 0`.

## Main results

* `convexOn_rpow_of_isSmoothStrictNorm` — `ξ ↦ F ξ ^ p` is convex for `1 ≤ p`. This is the
  structural ("concavity-preserving", in Korevaar's sense) property of the right-hand side of the
  transformed equation `div a(∇v) = λ + (p - 1) F(∇v)^p`. **Proved.**
* `le_zero_of_midpoint_le_of_continuousOn`, `convexOn_of_midpoint_le` — the classical passage from
  midpoint convexity to convexity for continuous functions, in the sharp form needed here: a
  continuous midpoint-convex function on a convex subset of `ℝ^d` is convex. **Proved** (via the
  extreme value theorem: a positive interior maximum of the defect `v ∘ lineMap - affine`
  propagates to an endpoint, where the defect vanishes).
* `convexOn_of_concavityFn_nonpos` — the reduction of convexity to `C ≤ 0`. **Proved.** (The
  concavity function `concavityFn` itself, its vanishing on the diagonal `concavityFn_self` and
  its symmetry `concavityFn_comm` are in `KorevaarAux.lean`, which this file imports.)
* `midpoint_mem_interior`, `tendsto_neg_log_atTop_of_mem_frontier`,
  `tendsto_concavityFn_atBot_of_mem_frontier` — the boundary behaviour: `v = -log φ → +∞` at every
  boundary point (because `φ` is continuous, positive inside and zero outside `K`), hence
  `C(·, y) → -∞` there for each fixed interior `y` (the midpoint of a boundary point and an
  interior point stays interior, so `v (midpoint · y)` stays bounded). This is step (i) of
  Korevaar's argument: the maximum of `C` cannot escape to `∂K`. **Proved.**
* Step (ii) of Korevaar's argument — the interior first- and second-order conditions at a maximum
  of `C`, the trace step against the ellipticity matrix `A(ξ) = Da(ξ)`, and the transformed
  equation `div a(∇v) = λ + (p-1) F(∇v)^p` — is proved in `KorevaarAux.lean`
  (`gradient_eq_of_isLocalMax_concavityFn`, `Korevaar.gradient_eq_of_isLocalMax_pair`,
  `Korevaar.inner_hessian_midpoint_le_of_isLocalMax`,
  `Korevaar.divergence_flux_gradient_midpoint_le`,
  `Korevaar.inner_hessian_midpoint_eq_of_equation`,
  `Korevaar.divergence_flux_gradient_neg_log`). **Proved.**
* The concavity maximum principle `neg_log_concavityFn_nonpos` itself — `C ≤ 0` — is **not** in
  this file: it lives in `KorevaarSMP.lean`, because its proof needs the attainment step and the
  interior second-order step of `KorevaarMaxPrinciple.lean`, which imports this file.  This file
  has no proof placeholders. Its remaining concavity input is
  `Korevaar.boundary_nonpos_and_smp` (`KorevaarSMP.lean`): a boundary-pair estimate and
  propagation of a positive interior maximum for the nonlinear two-point equation.
  That file proves the constant-coefficient weak-subsolution maximum principle and a conditional
  Hopf-ratio limit calculation. Applying them still requires boundary Hopf estimates,
  treatment of the degenerate operator in the pair variables, and a justification at critical
  points; the second-order identity at a noncritical maximum alone does not provide these.
-/

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Convexity of `F^p`: the concavity-preserving structure of the reaction term -/

/-- **Convexity of `ξ ↦ F(ξ)^p`** for a smooth strictly convex norm `F` and `1 ≤ p`: `F` is convex
and nonnegative and `t ↦ t^p` is convex and monotone on `[0, ∞)`.

This is the structural input of Korevaar's concavity maximum principle (MRS24, Theorem 1.1): the
right-hand side of the transformed eigenvalue equation `div a(∇v) = λ + (p - 1) F(∇v)^p` for
`v = -log φ` is a convex function of `∇v`, which is exactly the condition under which the equation
preserves concavity.

(The same computation appears downstream as `IsSmoothStrictNorm.convexOn_flux_potential` in
`WangXia.EigenvalueConvexHessian`; it is reproved here because that file imports
`EigenfunctionData`, which imports `LogConcave`.) -/
theorem convexOn_rpow_of_isSmoothStrictNorm {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {p : ℝ}
    (hp : 1 ≤ p) : ConvexOn ℝ (univ : Set (Euc d)) fun ξ => F ξ ^ p := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hc := hF.convexOn.2 (mem_univ x) (mem_univ y) ha hb hab
  have h2 := (convexOn_rpow hp).2 (mem_Ici.2 (hF.nonneg x)) (mem_Ici.2 (hF.nonneg y)) ha hb hab
  simp only [smul_eq_mul] at hc h2 ⊢
  calc F (a • x + b • y) ^ p ≤ (a * F x + b * F y) ^ p :=
        Real.rpow_le_rpow (hF.nonneg _) hc (by linarith)
    _ ≤ a * F x ^ p + b * F y ^ p := h2

/-! ### From midpoint convexity to convexity -/

/-- The midpoint of two reals is their average. -/
theorem midpoint_real (s t : ℝ) : midpoint ℝ s t = (s + t) / 2 := by
  rw [midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul]
  ring

/-- **A continuous midpoint-subadditive function with nonpositive endpoint values is
nonpositive**: if `h` is continuous on `[0, 1]`, satisfies `h((s+t)/2) ≤ (h s + h t)/2`, and has
`h 0 ≤ 0` and `h 1 ≤ 0`, then `h ≤ 0` on `[0, 1]`.

This is the one-dimensional maximum principle behind "midpoint convex + continuous ⇒ convex", in
the form used by the concavity maximum principle. Proof: if `h` were positive somewhere, the
extreme value theorem would give a maximum point `t₀ ∈ [0, 1]` with `M = h t₀ > 0`. If
`t₀ ≤ 1 - t₀` then `2t₀ ∈ [0, 1]` and `t₀` is the midpoint of `0` and `2t₀`, so
`M ≤ (h 0 + h (2t₀))/2 ≤ (0 + M)/2`, forcing `M ≤ 0`; symmetrically, if `1 - t₀ ≤ t₀` then `t₀` is
the midpoint of `2t₀ - 1` and `1` and `M ≤ (M + 0)/2`. Either way `M ≤ 0`, a contradiction. -/
theorem le_zero_of_midpoint_le_of_continuousOn {h : ℝ → ℝ}
    (hc : ContinuousOn h (Icc (0 : ℝ) 1))
    (hmid : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, h ((s + t) / 2) ≤ (h s + h t) / 2)
    (h0 : h 0 ≤ 0) (h1 : h 1 ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, h t ≤ 0 := by
  intro t ht
  by_contra hcon
  push_neg at hcon
  -- The extreme value theorem: `h` attains a maximum `M = h t₀` on `[0, 1]`, and `M > 0`.
  obtain ⟨t₀, ht₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 zero_le_one) hc
  have hM : 0 < h t₀ := lt_of_lt_of_le hcon (hmax ht)
  rw [mem_Icc] at ht₀
  obtain ⟨ht₀0, ht₀1⟩ := ht₀
  rcases le_total t₀ (1 - t₀) with hcase | hcase
  · -- `t₀` is the midpoint of `0` and `2t₀ ∈ [0, 1]`.
    have hmem : (2 * t₀) ∈ Icc (0 : ℝ) 1 := mem_Icc.2 ⟨by linarith, by linarith⟩
    have key := hmid 0 (mem_Icc.2 ⟨le_rfl, zero_le_one⟩) (2 * t₀) hmem
    rw [show (0 + 2 * t₀) / 2 = t₀ by ring] at key
    -- `hmax hmem` is the membership `2t₀ ∈ {s | h s ≤ h t₀}`; restate it for `linarith`
    have hle : h (2 * t₀) ≤ h t₀ := hmax hmem
    linarith
  · -- `t₀` is the midpoint of `2t₀ - 1 ∈ [0, 1]` and `1`.
    have hmem : (2 * t₀ - 1) ∈ Icc (0 : ℝ) 1 := mem_Icc.2 ⟨by linarith, by linarith⟩
    have key := hmid (2 * t₀ - 1) hmem 1 (mem_Icc.2 ⟨zero_le_one, le_rfl⟩)
    rw [show (2 * t₀ - 1 + 1) / 2 = t₀ by ring] at key
    have hle : h (2 * t₀ - 1) ≤ h t₀ := hmax hmem
    linarith


/-- **Midpoint convexity plus continuity implies convexity** on a convex subset of `ℝ^d`: if `v`
is continuous on the convex set `s` and `v (midpoint x y) ≤ (v x + v y) / 2` for all `x, y ∈ s`,
then `v` is convex on `s`.

This is the classical (Jensen) passage from midpoint convexity to convexity, and it is the form in
which the concavity maximum principle delivers convexity of `v = -log φ`: Korevaar's argument
produces exactly the midpoint inequality `C(x, y) = v (midpoint x y) - (v x + v y)/2 ≤ 0`.

Proof: fix `x, y ∈ s` and let `h t = v (lineMap x y t) - ((1-t) v x + t v y)` be the defect of `v`
against the affine interpolant along `[x, y]`. Then `h` is continuous on `[0, 1]` (the segment
lies in `s`), vanishes at `t = 0, 1`, and inherits the midpoint inequality because the subtracted
term is affine and `lineMap x y` maps midpoints to midpoints (`AffineMap.map_midpoint`). By
`le_zero_of_midpoint_le_of_continuousOn`, `h ≤ 0` on `[0, 1]`; evaluating at `t = b` (where
`lineMap x y b = a • x + b • y` since `a = 1 - b`) is the convexity inequality. -/
theorem convexOn_of_midpoint_le {s : Set (Euc d)} (hs : Convex ℝ s) {v : Euc d → ℝ}
    (hv : ContinuousOn v s)
    (hmid : ∀ x ∈ s, ∀ y ∈ s, v (midpoint ℝ x y) ≤ (v x + v y) / 2) :
    ConvexOn ℝ s v := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  have hmaps : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) s := hs.mapsTo_lineMap hx hy
  have hline : Continuous fun t : ℝ => AffineMap.lineMap x y t := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  -- The defect of `v` against the affine interpolant along the segment `[x, y]`.
  set h : ℝ → ℝ := fun t => v (AffineMap.lineMap x y t) - ((1 - t) * v x + t * v y) with hh
  have hcomp : ContinuousOn (fun t : ℝ => v (AffineMap.lineMap x y t)) (Icc (0 : ℝ) 1) :=
    hv.comp hline.continuousOn hmaps
  have haff : ContinuousOn (fun t : ℝ => (1 - t) * v x + t * v y) (Icc (0 : ℝ) 1) :=
    (by fun_prop : Continuous fun t : ℝ => (1 - t) * v x + t * v y).continuousOn
  have hcont : ContinuousOn h (Icc (0 : ℝ) 1) := by
    rw [hh]
    exact hcomp.sub haff
  have hzero : h 0 ≤ 0 := by simp [hh, AffineMap.lineMap_apply_zero]
  have hone : h 1 ≤ 0 := by simp [hh, AffineMap.lineMap_apply_one]
  have hmid' : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ τ ∈ Icc (0 : ℝ) 1, h ((σ + τ) / 2) ≤ (h σ + h τ) / 2 := by
    intro σ hσ τ hτ
    have hmidline : AffineMap.lineMap x y ((σ + τ) / 2)
        = midpoint ℝ (AffineMap.lineMap x y σ) (AffineMap.lineMap x y τ) := by
      rw [← AffineMap.map_midpoint, midpoint_real]
    have hkey := hmid _ (hmaps hσ) _ (hmaps hτ)
    rw [← hmidline] at hkey
    -- the subtracted interpolant is affine, so it splits exactly at the midpoint
    have haffine : (1 - (σ + τ) / 2) * v x + (σ + τ) / 2 * v y
        = ((1 - σ) * v x + σ * v y + ((1 - τ) * v x + τ * v y)) / 2 := by ring
    simp only [hh]
    linarith [hkey, haffine]
  -- The defect is nonpositive on `[0, 1]`; evaluate at `t = b`.
  have hb1 : b ∈ Icc (0 : ℝ) 1 := mem_Icc.2 ⟨hb, by linarith⟩
  have hfin := le_zero_of_midpoint_le_of_continuousOn hcont hmid' hzero hone b hb1
  have hxy : AffineMap.lineMap x y b = a • x + b • y := by
    rw [AffineMap.lineMap_apply_module, show (1 : ℝ) - b = a from by linarith]
  simp only [hh, hxy, show (1 : ℝ) - b = a from by linarith] at hfin
  simp only [smul_eq_mul]
  linarith


/-! ### Korevaar's concavity function

The concavity function `C(x, y) = v (midpoint x y) - (v x + v y) / 2` itself (`concavityFn`),
its vanishing on the diagonal (`concavityFn_self`) and its symmetry (`concavityFn_comm`) live in
`KorevaarAux.lean`, together with the second-order material that needs them. -/

/-- **`C ≤ 0` gives convexity**: a continuous function whose concavity function is nonpositive on
a convex set is convex there. This is the last step of Korevaar's argument. -/
theorem convexOn_of_concavityFn_nonpos {s : Set (Euc d)} (hs : Convex ℝ s) {v : Euc d → ℝ}
    (hv : ContinuousOn v s) (hC : ∀ x ∈ s, ∀ y ∈ s, concavityFn v x y ≤ 0) :
    ConvexOn ℝ s v := by
  refine convexOn_of_midpoint_le hs hv fun x hx y hy => ?_
  have h := hC x hx y hy
  simp only [concavityFn] at h
  linarith


/-! ### Boundary behaviour: `v = -log φ` blows up at `∂K` -/

/-- **The midpoint of a closure point and an interior point is interior** (for a convex set).
In Korevaar's argument this is what keeps `v (midpoint x y)` bounded while `v x → +∞` as `x`
approaches the boundary. -/
theorem midpoint_mem_interior {s : Set (Euc d)} (hs : Convex ℝ s) {x y : Euc d}
    (hx : x ∈ closure s) (hy : y ∈ interior s) : midpoint ℝ x y ∈ interior s := by
  have h : (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y ∈ interior s :=
    hs.combo_closure_interior_mem_interior hx hy (by norm_num) (by norm_num) (by norm_num)
  rwa [midpoint_eq_smul_add, invOf_eq_inv, smul_add]

/-- **The log-transform blows up at the boundary** (MRS24, Proposition 4.5 supplies the zero
boundary values): if `φ` is continuous, positive on `interior K` and zero outside the open convex
set `K`, then `v = -log φ` tends to `+∞` along `interior K` at every boundary point.

This is step (i) of Korevaar's concavity maximum principle: the concavity function cannot attain a
positive maximum at the boundary, because `v` is proper on `interior K`.

Proof: `φ x₀ = 0` since `x₀ ∉ K` (an open set is disjoint from its frontier), so `φ → 0` along
`𝓝[interior K] x₀`; given `b`, eventually `φ x < e^{-b}`, and then `log (φ x) ≤ -b` by monotonicity
of `log` on the positives, i.e. `-log (φ x) ≥ b`. -/
theorem tendsto_neg_log_atTop_of_mem_frontier {K : Set (Euc d)} (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hzero : ∀ x, x ∉ K → φ x = 0)
    (hpos : ∀ x ∈ interior K, 0 < φ x) {x₀ : Euc d} (hx₀ : x₀ ∈ frontier K) :
    Tendsto (fun x => -Real.log (φ x)) (𝓝[interior K] x₀) atTop := by
  -- `x₀` lies outside the open set `K`, so `φ x₀ = 0`.
  have hx₀K : x₀ ∉ K := by
    intro hmem
    have hcontra : x₀ ∈ K ∩ frontier K := ⟨hmem, hx₀⟩
    rw [hK.isOpen.inter_frontier_eq] at hcontra
    simp at hcontra
  have h1 : Tendsto φ (𝓝[interior K] x₀) (𝓝 (φ x₀)) :=
    (hφc.tendsto x₀).mono_left nhdsWithin_le_nhds
  rw [hzero x₀ hx₀K] at h1
  refine tendsto_atTop.2 fun b => ?_
  have hexp : (0 : ℝ) < Real.exp (-b) := Real.exp_pos _
  have hlt : ∀ᶠ z : ℝ in 𝓝 (0 : ℝ), z < Real.exp (-b) := Iio_mem_nhds hexp
  filter_upwards [h1.eventually hlt, self_mem_nhdsWithin] with x hx hxK
  have hxpos : 0 < φ x := hpos x hxK
  have hlog : Real.log (φ x) ≤ -b := by
    have hle := Real.log_le_log hxpos hx.le
    rwa [Real.log_exp] at hle
  linarith

/-- **The concavity function tends to `-∞` at the boundary**: for a fixed interior point `y`, the
concavity function `C(x, y) = v (midpoint x y) - (v x + v y)/2` of `v = -log φ` tends to `-∞` as
`x` approaches any boundary point of `K` from inside, because `v (midpoint x y)` stays bounded
(the midpoint of a boundary point and an interior point is interior, `midpoint_mem_interior`)
while `v x → +∞` (`tendsto_neg_log_atTop_of_mem_frontier`).

Combined with `concavityFn_self` (`C = 0` on the diagonal) this is exactly step (i) of Korevaar's
argument: a positive maximum of `C` over `K̄ × K̄` is attained at an interior, off-diagonal pair. -/
theorem tendsto_concavityFn_atBot_of_mem_frontier {K : Set (Euc d)} (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hzero : ∀ x, x ∉ K → φ x = 0)
    (hpos : ∀ x ∈ interior K, 0 < φ x) {x₀ y : Euc d} (hx₀ : x₀ ∈ frontier K)
    (hy : y ∈ interior K) :
    Tendsto (fun x => concavityFn (fun z => -Real.log (φ z)) x y) (𝓝[interior K] x₀) atBot := by
  -- `v x → +∞`, hence `-(v x / 2) → -∞`.
  have hv := tendsto_neg_log_atTop_of_mem_frontier hK hφc hzero hpos hx₀
  have hhalf : Tendsto (fun x => -Real.log (φ x) / 2) (𝓝[interior K] x₀) atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) hv
  have hneg : Tendsto (fun x => -(-Real.log (φ x) / 2)) (𝓝[interior K] x₀) atBot :=
    Filter.tendsto_neg_atBot_iff.2 hhalf
  -- `v (midpoint x y)` stays bounded: the midpoint is an interior point, where `φ > 0`.
  have hmidmem : midpoint ℝ x₀ y ∈ interior K :=
    midpoint_mem_interior hK.convex (frontier_subset_closure hx₀) hy
  have hmidcont : Continuous fun x : Euc d => midpoint ℝ x y := by
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    fun_prop
  have hcomp : ContinuousAt (fun x : Euc d => φ (midpoint ℝ x y)) x₀ :=
    (hφc.comp hmidcont).continuousAt
  have hcA : Tendsto (fun x : Euc d => -Real.log (φ (midpoint ℝ x y))) (𝓝 x₀)
      (𝓝 (-Real.log (φ (midpoint ℝ x₀ y)))) := (hcomp.log (hpos _ hmidmem).ne').neg
  have hA : Tendsto (fun x : Euc d => -Real.log (φ (midpoint ℝ x y)) - -Real.log (φ y) / 2)
      (𝓝[interior K] x₀) (𝓝 (-Real.log (φ (midpoint ℝ x₀ y)) - -Real.log (φ y) / 2)) :=
    (hcA.mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds
  refine (hA.add_atBot hneg).congr fun x => ?_
  simp only [concavityFn]
  ring


/-! ### The residual analytic core

The **concavity maximum principle** itself — `neg_log_concavityFn_nonpos`, i.e. `C ≤ 0` for
`v = -log φ` — is proved in `KorevaarSMP.lean`, which is downstream of this file: its proof needs
the attainment step and the interior second-order step of `KorevaarMaxPrinciple.lean` (which
imports this file). What remains open there is `Korevaar.boundary_nonpos_and_smp`: the
boundary-pair estimate and nonlinear interior propagation, including the case of a critical
maximum. The scalar weak-subsolution maximum principle and the conditional Hopf-ratio limit
calculation are proved there, but their hypotheses still need to be established for the
concavity function. The convexity of `ξ ↦ F(ξ)^p`, midpoint convexity criterion, and boundary
blow-up facts proved here supply other parts of that reduction. -/


end Komlos.Literature
