import Komlos.Literature.PLaplacian.LogConcaveAux

/-!
# Korevaar's concavity maximum principle: attainment and the pointwise eigenvalue equation

This file closes two of the four analytic gaps that `neg_log_concavityFn_nonpos`
(`LogConcaveAux.lean`) listed for Korevaar's *concavity maximum principle*
(Mosconi–Riey–Squassina 2024, Theorem 1.1, log-concavity of the first anisotropic `p`-Laplacian
eigenfunction): the pointwise ("strong") eigenvalue equation **completely**, and the attainment of
an interior maximum of the concavity function **up to its last boundary case** (pairs with both
entries on `∂K`).  The second-order half of Korevaar's argument is in `KorevaarAux.lean`, the
zeroth- and first-order half in `LogConcaveAux.lean`; everything here lives in the namespace
`Komlos.Literature.Korevaar`, so nothing clashes with the downstream `WangXia` copies of the
integration-by-parts material.

Auxiliary declarations proved along the way: `Korevaar.continuousOn_concavityFn_pair`,
`Korevaar.hasCompactSupport_of_zero_outside`, `Korevaar.continuous_mul_of_continuousOn`,
`Korevaar.isOpen_noncritical`, `Korevaar.contDiffOn_flux_gradient`,
`Korevaar.hasGradientAt_neg_log`, `Korevaar.gradient_neg_log_ne_zero_iff`,
`Korevaar.eventually_differentiableAt_neg_log`, `Korevaar.differentiableAt_gradient_neg_log`.

## Main results

### The attainment step (Korevaar's step (i))

* `Korevaar.exists_isMaxOn_of_eventually_lt` — **a relatively compact set on which a continuous
  function is eventually smaller at the boundary than at one interior point carries a maximum**:
  if `closure Ω` is compact, `g` is continuous on `Ω`, `a ∈ Ω`, and for every
  `z ∈ closure Ω \ Ω` one has `g < g a` eventually along `𝓝[Ω] z`, then `g` attains a maximum
  on `Ω`.  (Proof: the superlevel set `E = {w ∈ Ω | g a ≤ g w}` has `closure E ⊆ Ω`, so
  `closure E` is a compact subset of `Ω` and the extreme value theorem applies there.)
  **Proved.**
* `Korevaar.exists_isMaxOn_of_tendsto_atBot` — the same with `g → -∞` at the boundary.
  **Proved.**
* `Korevaar.tendsto_concavityFn_pair_atBot_left`, `Korevaar.tendsto_concavityFn_pair_atBot_right`
  — the **joint** (two-variable) form of `tendsto_concavityFn_atBot_of_mem_frontier`: the
  concavity function of `v = -log φ` tends to `-∞` along `𝓝[K × K] (x₀, y₀)` whenever *one* of
  `x₀`, `y₀` lies on `∂K` and the other in `K`.  **Proved.**
* `Korevaar.exists_isMaxOn_concavityFn` — **attainment of the maximum of the concavity function
  at an interior pair**, granted the one remaining boundary case, namely pairs with *both*
  entries on `∂K` (the hypothesis `hdiag`; this is the case Korevaar handles by first working on
  smooth strongly convex domains and then approximating).  **Proved** modulo `hdiag`.

### The pointwise ("strong") eigenvalue equation

* `Korevaar.integral_inner_gradient_eq_neg_integral_divergence` (integration by parts on `ℝ^d`)
  and `Korevaar.eq_zero_of_integral_mul_testFn_eq_zero` (the fundamental lemma of the calculus of
  variations).  **Proved** (re-proved here from `WangXia.EigenvalueConvexAssemblyAux`, which
  cannot be imported: `EigenvalueConvexAssemblyAux → EigenfunctionData → LogConcave`).
* `Korevaar.divergence_flux_gradient_add_eq_zero` — **the strong form
  `div a(∇φ) + λ φ^{p-1} = 0`** of the eigenvalue equation at every non-critical interior point,
  for the continuous representative `φ` of a weak first eigenfunction.  **Proved.**  This closes
  the last of the four gaps listed in `neg_log_concavityFn_nonpos` that was purely an
  import-cycle artefact.
* `Korevaar.divergence_flux_gradient_neg_log_of_eigenfunction` — the **transformed equation**
  `div a(∇v) = λ + (p-1) F(∇v)^p` for `v = -log φ`, assembled from the strong form and
  `Korevaar.divergence_flux_gradient_neg_log`.  **Proved.**
* `Korevaar.inner_hessian_midpoint_eq_of_isLocalMax` — the **capstone of the interior step**: at
  an interior local maximum of the concavity function of `v = -log φ` whose three points are
  non-critical, the Hessian of `v` at the midpoint equals the average of the Hessians at the two
  points, `D²v(m)[ζ, ζ] = (D²v(x)[ζ, ζ] + D²v(y)[ζ, ζ])/2`, for **every** `ζ`.  **Proved**, from
  `Korevaar.inner_hessian_midpoint_eq_of_equation` and the transformed equation above.

### The critical set

* `Korevaar.concavityFn_nonpos_of_mem_closure` — the "continuity plus density" half of the
  critical-set step: `C ≤ 0` on a subset `S` of `interior K × interior K` forces `C ≤ 0` at every
  point of `closure S`, because `C` is continuous on all of `interior K × interior K`
  (`continuousOn_concavityFn_pair`), also across `{∇φ = 0}`.  **Proved.**  (What is *not*
  available is the density of the non-critical set `{∇φ ≠ 0}` itself.)

What remains for `neg_log_concavityFn_nonpos` after this file is Korevaar's degenerate case — the
**strong maximum principle** for the operator linearized at the common gradient, which turns the
equality above into "`C` is constant" — plus the two-boundary case `hdiag` of the attainment step
and the density of the non-critical set.  See the TODO there.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

namespace Korevaar

/-! ### Attainment of a maximum on a relatively compact set -/

/-- **Attainment of a maximum on a relatively compact set.** If `closure Ω` is compact, `g` is
continuous on `Ω`, `a ∈ Ω`, and at every boundary point `z ∈ closure Ω \ Ω` one has `g w < g a`
for `w` near `z` inside `Ω`, then `g` attains a maximum on `Ω`.

This is step (i) of Korevaar's concavity maximum principle in abstract form: a positive maximum
of the concavity function cannot escape to `∂K`, because the concavity function tends to `-∞`
there.

Proof: the superlevel set `E = {w ∈ Ω | g a ≤ g w}` satisfies `closure E ⊆ Ω` — a point
`z ∈ closure E \ Ω` would be a boundary point of `Ω`, so `g < g a` eventually along the nontrivial
filter `𝓝[E] z ≤ 𝓝[Ω] z`, while `g a ≤ g` everywhere on `E`.  Hence `closure E` is a compact
subset of `Ω` containing `a`, and the extreme value theorem produces a maximum point `z` of `g`
on `closure E`; it is a maximum on all of `Ω`, since points of `Ω \ E` have `g w < g a ≤ g z`. -/
theorem exists_isMaxOn_of_eventually_lt {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (hcl : IsCompact (closure Ω)) {g : X → ℝ} (hg : ContinuousOn g Ω) {a : X} (ha : a ∈ Ω)
    (hbd : ∀ z ∈ closure Ω \ Ω, ∀ᶠ w in 𝓝[Ω] z, g w < g a) :
    ∃ z ∈ Ω, IsMaxOn g Ω z := by
  set E : Set X := {w | w ∈ Ω ∧ g a ≤ g w}
  have haE : a ∈ E := ⟨ha, le_rfl⟩
  have hEΩ : E ⊆ Ω := fun w hw => hw.1
  have hsub : closure E ⊆ Ω := by
    intro z hz
    by_contra hzΩ
    haveI : (𝓝[E] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
    have hlt : ∀ᶠ w in 𝓝[E] z, g w < g a :=
      (hbd z ⟨closure_mono hEΩ hz, hzΩ⟩).filter_mono (nhdsWithin_mono z hEΩ)
    have hge : ∀ᶠ w in 𝓝[E] z, g a ≤ g w := by
      filter_upwards [self_mem_nhdsWithin] with w hw using hw.2
    obtain ⟨w, hw1, hw2⟩ := (hlt.and hge).exists
    linarith
  have hEcl : IsCompact (closure E) :=
    hcl.of_isClosed_subset isClosed_closure (closure_mono hEΩ)
  obtain ⟨z, hz, hmax⟩ := hEcl.exists_isMaxOn ⟨a, subset_closure haE⟩ (hg.mono hsub)
  refine ⟨z, hsub hz, isMaxOn_iff.2 fun w hw => ?_⟩
  rcases le_or_gt (g a) (g w) with h | h
  · exact hmax (subset_closure (show w ∈ E from ⟨hw, h⟩))
  · exact le_trans h.le (hmax (subset_closure haE))

/-- **Attainment of a maximum on a relatively compact set**, in the form used here: `g` tends to
`-∞` at every boundary point of `Ω`. -/
theorem exists_isMaxOn_of_tendsto_atBot {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (hcl : IsCompact (closure Ω)) {g : X → ℝ} (hg : ContinuousOn g Ω) {a : X} (ha : a ∈ Ω)
    (hbd : ∀ z ∈ closure Ω \ Ω, Tendsto g (𝓝[Ω] z) atBot) :
    ∃ z ∈ Ω, IsMaxOn g Ω z :=
  exists_isMaxOn_of_eventually_lt hcl hg ha fun z hz =>
    (hbd z hz).eventually (eventually_lt_atBot (g a))

/-! ### The concavity function at a pair with one entry on the boundary -/

/-- **The concavity function tends to `-∞` at a pair whose *first* entry lies on `∂K`** (the
joint, two-variable form of `tendsto_concavityFn_atBot_of_mem_frontier`): for `x₀ ∈ ∂K` and
`y₀ ∈ interior K`, the concavity function
`C(x, y) = v (midpoint x y) - (v x + v y)/2` of `v = -log φ` tends to `-∞` along
`𝓝[interior K × interior K] (x₀, y₀)`, because `v (midpoint x y)` and `v y` stay bounded near
`(x₀, y₀)` (the midpoint of a closure point and an interior point is interior,
`midpoint_mem_interior`) while `v x → +∞` (`tendsto_neg_log_atTop_of_mem_frontier`).

The *joint* form is what the attainment step `exists_isMaxOn_of_tendsto_atBot` needs: the boundary
of `interior K × interior K` is approached in both variables at once. -/
theorem tendsto_concavityFn_pair_atBot_left {K : Set (Euc d)} (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hzero : ∀ x, x ∉ K → φ x = 0)
    (hpos : ∀ x ∈ interior K, 0 < φ x) {x₀ y₀ : Euc d} (hx₀ : x₀ ∈ frontier K)
    (hy₀ : y₀ ∈ interior K) :
    Tendsto (fun q : Euc d × Euc d => concavityFn (fun z => -Real.log (φ z)) q.1 q.2)
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d)) atBot := by
  -- the first coordinate converges to `x₀` inside `interior K`
  have hfst : Tendsto (Prod.fst : Euc d × Euc d → Euc d)
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d)) (𝓝[interior K] x₀) := by
    rw [nhdsWithin_prod_eq]
    exact tendsto_fst
  -- `-v x / 2 → -∞` in the first coordinate
  have hv : Tendsto (fun x => -Real.log (φ x)) (𝓝[interior K] x₀) atTop :=
    tendsto_neg_log_atTop_of_mem_frontier hK hφc hzero hpos hx₀
  have hhalf0 : Tendsto (fun x => -Real.log (φ x) / 2) (𝓝[interior K] x₀) atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) hv
  have hhalf : Tendsto (fun q : Euc d × Euc d => -Real.log (φ q.1) / 2)
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d)) atTop := hhalf0.comp hfst
  have hB : Tendsto (fun q : Euc d × Euc d => -(-Real.log (φ q.1) / 2))
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d)) atBot :=
    Filter.tendsto_neg_atBot_iff.2 hhalf
  -- the midpoint of `x₀` and the interior point `y₀` is interior, so `v ∘ midpoint` is bounded
  have hmidmem : midpoint ℝ x₀ y₀ ∈ interior K :=
    midpoint_mem_interior hK.convex (frontier_subset_closure hx₀) hy₀
  have hmidcont : Continuous fun q : Euc d × Euc d => midpoint ℝ q.1 q.2 := by
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    fun_prop
  have hmidφ : ContinuousAt (fun q : Euc d × Euc d => φ (midpoint ℝ q.1 q.2))
      ((x₀, y₀) : Euc d × Euc d) := (hφc.comp hmidcont).continuousAt
  have hsndφ : ContinuousAt (fun q : Euc d × Euc d => φ q.2) ((x₀, y₀) : Euc d × Euc d) :=
    (hφc.comp continuous_snd).continuousAt
  have hA1 : ContinuousAt (fun q : Euc d × Euc d => -Real.log (φ (midpoint ℝ q.1 q.2)))
      ((x₀, y₀) : Euc d × Euc d) := (hmidφ.log (hpos _ hmidmem).ne').neg
  have hA2 : ContinuousAt (fun q : Euc d × Euc d => -Real.log (φ q.2) / 2)
      ((x₀, y₀) : Euc d × Euc d) := ((hsndφ.log (hpos _ hy₀).ne').neg).div_const 2
  have hA0 : Tendsto (fun q : Euc d × Euc d =>
      -Real.log (φ (midpoint ℝ q.1 q.2)) - -Real.log (φ q.2) / 2)
      (𝓝 ((x₀, y₀) : Euc d × Euc d))
      (𝓝 (-Real.log (φ (midpoint ℝ x₀ y₀)) - -Real.log (φ y₀) / 2)) := hA1.sub hA2
  have hA : Tendsto (fun q : Euc d × Euc d =>
      -Real.log (φ (midpoint ℝ q.1 q.2)) - -Real.log (φ q.2) / 2)
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d))
      (𝓝 (-Real.log (φ (midpoint ℝ x₀ y₀)) - -Real.log (φ y₀) / 2)) :=
    hA0.mono_left nhdsWithin_le_nhds
  refine (hA.add_atBot hB).congr fun q => ?_
  simp only [concavityFn]
  ring

/-- **The concavity function tends to `-∞` at a pair whose *second* entry lies on `∂K`**; the
mirror image of `tendsto_concavityFn_pair_atBot_left`.  (The concavity function is symmetric,
`concavityFn_comm`, but the two limits are taken along *different* filters, so the computation is
repeated with the roles of the two coordinates exchanged.) -/
theorem tendsto_concavityFn_pair_atBot_right {K : Set (Euc d)} (hK : IsGoodConvex K)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hzero : ∀ x, x ∉ K → φ x = 0)
    (hpos : ∀ x ∈ interior K, 0 < φ x) {x₀ y₀ : Euc d} (hx₀ : x₀ ∈ interior K)
    (hy₀ : y₀ ∈ frontier K) :
    Tendsto (fun q : Euc d × Euc d => concavityFn (fun z => -Real.log (φ z)) q.1 q.2)
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d)) atBot := by
  have hsnd : Tendsto (Prod.snd : Euc d × Euc d → Euc d)
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d)) (𝓝[interior K] y₀) := by
    rw [nhdsWithin_prod_eq]
    exact tendsto_snd
  have hv : Tendsto (fun y => -Real.log (φ y)) (𝓝[interior K] y₀) atTop :=
    tendsto_neg_log_atTop_of_mem_frontier hK hφc hzero hpos hy₀
  have hhalf0 : Tendsto (fun y => -Real.log (φ y) / 2) (𝓝[interior K] y₀) atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) hv
  have hhalf : Tendsto (fun q : Euc d × Euc d => -Real.log (φ q.2) / 2)
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d)) atTop := hhalf0.comp hsnd
  have hB : Tendsto (fun q : Euc d × Euc d => -(-Real.log (φ q.2) / 2))
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d)) atBot :=
    Filter.tendsto_neg_atBot_iff.2 hhalf
  have hmidmem : midpoint ℝ x₀ y₀ ∈ interior K := by
    have h : midpoint ℝ y₀ x₀ ∈ interior K :=
      midpoint_mem_interior hK.convex (frontier_subset_closure hy₀) hx₀
    rwa [midpoint_comm] at h
  have hmidcont : Continuous fun q : Euc d × Euc d => midpoint ℝ q.1 q.2 := by
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    fun_prop
  have hmidφ : ContinuousAt (fun q : Euc d × Euc d => φ (midpoint ℝ q.1 q.2))
      ((x₀, y₀) : Euc d × Euc d) := (hφc.comp hmidcont).continuousAt
  have hfstφ : ContinuousAt (fun q : Euc d × Euc d => φ q.1) ((x₀, y₀) : Euc d × Euc d) :=
    (hφc.comp continuous_fst).continuousAt
  have hA1 : ContinuousAt (fun q : Euc d × Euc d => -Real.log (φ (midpoint ℝ q.1 q.2)))
      ((x₀, y₀) : Euc d × Euc d) := (hmidφ.log (hpos _ hmidmem).ne').neg
  have hA2 : ContinuousAt (fun q : Euc d × Euc d => -Real.log (φ q.1) / 2)
      ((x₀, y₀) : Euc d × Euc d) := ((hfstφ.log (hpos _ hx₀).ne').neg).div_const 2
  have hA0 : Tendsto (fun q : Euc d × Euc d =>
      -Real.log (φ (midpoint ℝ q.1 q.2)) - -Real.log (φ q.1) / 2)
      (𝓝 ((x₀, y₀) : Euc d × Euc d))
      (𝓝 (-Real.log (φ (midpoint ℝ x₀ y₀)) - -Real.log (φ x₀) / 2)) := hA1.sub hA2
  have hA : Tendsto (fun q : Euc d × Euc d =>
      -Real.log (φ (midpoint ℝ q.1 q.2)) - -Real.log (φ q.1) / 2)
      (𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d))
      (𝓝 (-Real.log (φ (midpoint ℝ x₀ y₀)) - -Real.log (φ x₀) / 2)) :=
    hA0.mono_left nhdsWithin_le_nhds
  refine (hA.add_atBot hB).congr fun q => ?_
  simp only [concavityFn]
  ring

/-- **Continuity of the concavity function of `v = -log φ`** on `interior K × interior K`. -/
theorem continuousOn_concavityFn_pair {K : Set (Euc d)} (hK : IsGoodConvex K) {φ : Euc d → ℝ}
    (hφc : Continuous φ) (hpos : ∀ x ∈ interior K, 0 < φ x) :
    ContinuousOn (fun q : Euc d × Euc d => concavityFn (fun z => -Real.log (φ z)) q.1 q.2)
      (interior K ×ˢ interior K) := by
  have hmidcont : Continuous fun q : Euc d × Euc d => midpoint ℝ q.1 q.2 := by
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    fun_prop
  intro q hq
  have hmidmem : midpoint ℝ q.1 q.2 ∈ interior K :=
    midpoint_mem_interior hK.convex (subset_closure (interior_subset hq.1)) hq.2
  have hmidφ : ContinuousAt (fun q : Euc d × Euc d => φ (midpoint ℝ q.1 q.2)) q :=
    (hφc.comp hmidcont).continuousAt
  have hfstφ : ContinuousAt (fun q : Euc d × Euc d => φ q.1) q :=
    (hφc.comp continuous_fst).continuousAt
  have hsndφ : ContinuousAt (fun q : Euc d × Euc d => φ q.2) q :=
    (hφc.comp continuous_snd).continuousAt
  have h1 : ContinuousAt (fun q : Euc d × Euc d => -Real.log (φ (midpoint ℝ q.1 q.2))) q :=
    (hmidφ.log (hpos _ hmidmem).ne').neg
  have h2 : ContinuousAt (fun q : Euc d × Euc d => -Real.log (φ q.1)) q :=
    (hfstφ.log (hpos _ hq.1).ne').neg
  have h3 : ContinuousAt (fun q : Euc d × Euc d => -Real.log (φ q.2)) q :=
    (hsndφ.log (hpos _ hq.2).ne').neg
  have h4 : ContinuousAt
      (fun q : Euc d × Euc d => concavityFn (fun z => -Real.log (φ z)) q.1 q.2) q := by
    simp only [concavityFn]
    exact h1.sub ((h2.add h3).div_const 2)
  exact h4.continuousWithinAt

/-- **Attainment of the maximum of the concavity function at an interior pair** (Korevaar's step
(i) for `v = -log φ`): if `φ` is continuous, positive on `interior K` and zero outside the open
bounded convex set `K`, then the concavity function of `v = -log φ` attains its maximum over
`interior K × interior K`, provided it does not come arbitrarily close to that maximum at pairs
of *boundary* points (hypothesis `hdiag`).

`hdiag` is the one boundary case that `tendsto_concavityFn_pair_atBot_left` and
`tendsto_concavityFn_pair_atBot_right` do not cover: when *both* entries approach `∂K`, both
`v x, v y → +∞` **and** `v (midpoint x y) → +∞`, and the three blow-ups can cancel.  (Korevaar's
proof avoids the issue by running the argument on smooth *strongly* convex domains, where the
midpoint of two distinct boundary points is interior, and then approximating a general convex
`K`.)

Everything else is proved here: `closure (interior K × interior K)` is compact because `K` is
bounded, the concavity function is continuous on `interior K × interior K`
(`continuousOn_concavityFn_pair`), and at every boundary pair with one interior entry the
concavity function tends to `-∞`; `exists_isMaxOn_of_eventually_lt` then concludes. -/
theorem exists_isMaxOn_concavityFn {K : Set (Euc d)} (hK : IsGoodConvex K) {φ : Euc d → ℝ}
    (hφc : Continuous φ) (hzero : ∀ x, x ∉ K → φ x = 0)
    (hpos : ∀ x ∈ interior K, 0 < φ x) {a b : Euc d} (ha : a ∈ interior K) (hb : b ∈ interior K)
    (hdiag : ∀ x₀ ∈ frontier K, ∀ y₀ ∈ frontier K,
      ∀ᶠ q in 𝓝[interior K ×ˢ interior K] ((x₀, y₀) : Euc d × Euc d),
        concavityFn (fun z => -Real.log (φ z)) q.1 q.2
          < concavityFn (fun z => -Real.log (φ z)) a b) :
    ∃ q ∈ interior K ×ˢ interior K,
      IsMaxOn (fun q : Euc d × Euc d => concavityFn (fun z => -Real.log (φ z)) q.1 q.2)
        (interior K ×ˢ interior K) q := by
  have hKo : interior K = K := hK.isOpen.interior_eq
  have hclK : IsCompact (closure K) := hK.isBounded.isCompact_closure
  have hcl : IsCompact (closure (interior K ×ˢ interior K)) := by
    rw [closure_prod_eq, hKo]
    exact hclK.prod hclK
  have hg := continuousOn_concavityFn_pair hK hφc hpos
  have hfr : ∀ z ∈ closure (interior K), z ∉ interior K → z ∈ frontier K := by
    intro z hz hz'
    rw [hKo] at hz
    exact ⟨hz, hz'⟩
  refine exists_isMaxOn_of_eventually_lt hcl hg
    (show (a, b) ∈ interior K ×ˢ interior K from ⟨ha, hb⟩) fun q hq => ?_
  obtain ⟨hq1, hq2⟩ := hq
  rw [closure_prod_eq] at hq1
  have h1 : q.1 ∈ closure (interior K) := hq1.1
  have h2 : q.2 ∈ closure (interior K) := hq1.2
  by_cases hc1 : q.1 ∈ interior K
  · -- then the second entry has to be a boundary point
    have hc2 : q.2 ∉ interior K := fun h => hq2 ⟨hc1, h⟩
    exact (tendsto_concavityFn_pair_atBot_right hK hφc hzero hpos hc1
      (hfr q.2 h2 hc2)).eventually (eventually_lt_atBot _)
  · by_cases hc2 : q.2 ∈ interior K
    · exact (tendsto_concavityFn_pair_atBot_left hK hφc hzero hpos
        (hfr q.1 h1 hc1) hc2).eventually (eventually_lt_atBot _)
    · exact hdiag q.1 (hfr q.1 h1 hc1) q.2 (hfr q.2 h2 hc2)

/-- **Nonpositivity of the concavity function propagates from a dense subset.**  If
`C(x, y) = v (midpoint x y) - (v x + v y)/2` (for `v = -log φ`) is `≤ 0` on a subset `S` of
`interior K × interior K` and `(x, y)` lies in the closure of `S`, then `C(x, y) ≤ 0`.

This is the "continuity plus density" half of the **critical-set** step of MRS24, Theorem 1.1:
Korevaar's second-order argument runs only on the non-critical set `{∇φ ≠ 0}`, and the inequality
is then transported to the whole of `interior K × interior K` by continuity of `C` — which holds
on all of `interior K × interior K`, `continuousOn_concavityFn_pair`, since `φ` is continuous and
positive there.  (What is *not* available is the density of the non-critical set itself.) -/
theorem concavityFn_nonpos_of_mem_closure {K : Set (Euc d)} (hK : IsGoodConvex K) {φ : Euc d → ℝ}
    (hφc : Continuous φ) (hpos : ∀ x ∈ interior K, 0 < φ x) {S : Set (Euc d × Euc d)}
    (hSΩ : S ⊆ interior K ×ˢ interior K)
    (hle : ∀ q ∈ S, concavityFn (fun z => -Real.log (φ z)) q.1 q.2 ≤ 0)
    {x y : Euc d} (hx : x ∈ interior K) (hy : y ∈ interior K)
    (hmem : ((x, y) : Euc d × Euc d) ∈ closure S) :
    concavityFn (fun z => -Real.log (φ z)) x y ≤ 0 := by
  haveI : (𝓝[S] ((x, y) : Euc d × Euc d)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hmem
  have hg := continuousOn_concavityFn_pair hK hφc hpos
  have hcw : ContinuousWithinAt
      (fun q : Euc d × Euc d => concavityFn (fun z => -Real.log (φ z)) q.1 q.2)
      (interior K ×ˢ interior K) ((x, y) : Euc d × Euc d) :=
    hg ((x, y) : Euc d × Euc d) ⟨hx, hy⟩
  have hten : Tendsto (fun q : Euc d × Euc d => concavityFn (fun z => -Real.log (φ z)) q.1 q.2)
      (𝓝[S] ((x, y) : Euc d × Euc d))
      (𝓝 (concavityFn (fun z => -Real.log (φ z)) x y)) := hcw.mono hSΩ
  refine le_of_tendsto hten ?_
  filter_upwards [self_mem_nhdsWithin] with q hq using hle q hq

/-! ### Integration by parts on `ℝ^d` and the fundamental lemma of the calculus of variations

The four declarations of this subsection repeat `WangXia.EigenvalueConvexAssemblyAux`, which
imports `EigenfunctionData` and hence `LogConcave`, so cannot be imported here; they are in the
`Korevaar` namespace, so no name clashes with the downstream copies. -/

/-- A function vanishing outside a compact set has compact support. -/
theorem hasCompactSupport_of_zero_outside {E : Type*} [NormedAddCommGroup E] {K : Set (Euc d)}
    (hK : IsCompact K) {g : Euc d → E} (hg : ∀ x ∉ K, g x = 0) : HasCompactSupport g :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun x hx => by_contra fun h => hx (hg x h)) hK.isClosed)

/-- A function continuous on an open set `Ω`, multiplied by a continuous function vanishing
outside a closed subset `K ⊆ Ω`, is continuous on `ℝ^d`. -/
theorem continuous_mul_of_continuousOn {Ω : Set (Euc d)} (hΩ : IsOpen Ω) {f g : Euc d → ℝ}
    (hf : ContinuousOn f Ω) (hg : Continuous g) {K : Set (Euc d)} (hK : IsClosed K)
    (hKΩ : K ⊆ Ω) (hgK : ∀ x ∉ K, g x = 0) : Continuous fun x => f x * g x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (hf.continuousAt (hΩ.mem_nhds hx)).mul hg.continuousAt
  · have hmem : Kᶜ ∈ 𝓝 x := hK.isOpen_compl.mem_nhds fun h => hx (hKΩ h)
    refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    rw [hgK y hy, mul_zero]

/-- **Integration by parts on `ℝ^d`**: for a vector field `W ∈ C¹(Ω)` (`Ω` open) and `ψ ∈ C¹`
with compact support in `Ω`, `∫ ⟪W, ∇ψ⟫ = -∫ ψ · div W`. -/
theorem integral_inner_gradient_eq_neg_integral_divergence {Ω : Set (Euc d)} (hΩ : IsOpen Ω)
    {W : Euc d → Euc d} (hW : ContDiffOn ℝ 1 W Ω) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψs : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∫ x, ⟪W x, gradient ψ x⟫ = -∫ x, ψ x * divergence W x := by
  set e : Fin d → Euc d := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have hWd : ∀ x ∈ Ω, DifferentiableAt ℝ W x := fun x hx =>
    (hW.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hx)
  have hWc : ContinuousOn W Ω := hW.continuousOn
  have hWf : ContinuousOn (fderiv ℝ W) Ω := hW.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hψc : Continuous ψ := hψ.continuous
  have hψf : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hψK : ∀ x ∉ tsupport ψ, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hψfK : ∀ x ∉ tsupport ψ, fderiv ℝ ψ x = 0 := fun x hx => by
    by_contra h; exact hx (support_fderiv_subset ℝ (Function.mem_support.2 h))
  have hK : IsClosed (tsupport ψ) := isClosed_tsupport ψ
  -- the components `f i = ⟪e i, W⟫`
  set f : Fin d → Euc d → ℝ := fun i x => ⟪e i, W x⟫ with hf
  have hfd : ∀ i, ∀ x ∈ Ω, HasFDerivAt (f i) ((innerSL ℝ (e i)).comp (fderiv ℝ W x)) x :=
    fun i x hx => (innerSL ℝ (e i)).hasFDerivAt.comp x (hWd x hx).hasFDerivAt
  have hfc : ∀ i, ContinuousOn (f i) Ω := fun i =>
    (innerSL ℝ (e i)).continuous.comp_continuousOn hWc
  have hfderiv : ∀ i, ∀ x ∈ Ω, fderiv ℝ (f i) x (e i) = ⟪e i, fderiv ℝ W x (e i)⟫ :=
    fun i x hx => by rw [(hfd i x hx).fderiv]; rfl
  have hfderivc : ∀ i, ContinuousOn (fun x => fderiv ℝ (f i) x (e i)) Ω := fun i =>
    (continuousOn_const.inner (hWf.clm_apply continuousOn_const)).congr fun x hx =>
      hfderiv i x hx
  -- integrability of the three products
  have hint1 : ∀ i, Integrable fun x => f i x * fderiv ℝ ψ x (e i) := fun i =>
    (continuous_mul_of_continuousOn hΩ (hfc i) (hψf.clm_apply continuous_const) hK hψΩ
      fun x hx => by rw [hψfK x hx]; rfl).integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun x hx => by rw [hψfK x hx]; simp)
  have hint2 : ∀ i, Integrable fun x => fderiv ℝ (f i) x (e i) * ψ x := fun i =>
    (continuous_mul_of_continuousOn hΩ (hfderivc i) hψc hK hψΩ hψK).integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun x hx => by rw [hψK x hx, mul_zero])
  have hint3 : ∀ i, Integrable fun x => f i x * ψ x := fun i =>
    (continuous_mul_of_continuousOn hΩ (hfc i) hψc hK hψΩ hψK).integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun x hx => by rw [hψK x hx, mul_zero])
  -- integration by parts in each coordinate direction
  have hibp : ∀ i, ∫ x, f i x * fderiv ℝ ψ x (e i) = -∫ x, fderiv ℝ (f i) x (e i) * ψ x :=
    fun i => integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := e i) (hint2 i) (hint1 i)
      (hint3 i) (fun x hx => (hfd i x (hψΩ hx)).differentiableAt)
      (fun x _ => hψ.differentiable one_ne_zero x)
  -- summing over `i`
  have hL : ∫ x, ⟪W x, gradient ψ x⟫ = ∑ i, ∫ x, f i x * fderiv ℝ ψ x (e i) := by
    rw [← integral_finsetSum _ fun i _ => hint1 i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner (W x) (gradient ψ x)
    simp only [EuclideanSpace.basisFun_apply] at this
    dsimp only
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ⟪W x, EuclideanSpace.single i (1 : ℝ)⟫ * ⟪EuclideanSpace.single i (1 : ℝ), gradient ψ x⟫ =
      ⟪EuclideanSpace.single i (1 : ℝ), W x⟫ * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))
    rw [real_inner_comm (EuclideanSpace.single i (1 : ℝ)) (W x),
      real_inner_comm (gradient ψ x) (EuclideanSpace.single i (1 : ℝ)), inner_gradient_left]
  have hR : ∑ i, -∫ x, fderiv ℝ (f i) x (e i) * ψ x = -∫ x, ψ x * divergence W x := by
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hint2 i]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : x ∈ Ω
    · simp only [divergence, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfderiv i x hx, mul_comm]
    · rw [hψK x fun h => hx (hψΩ h)]
      simp
  rw [hL, ← hR]
  exact Finset.sum_congr rfl fun i _ => hibp i

/-- **The fundamental lemma of the calculus of variations**: if `g` is continuous on the open set
`Ω` and `∫ g ψ = 0` for every nonnegative smooth test function `ψ` of `Ω`, then `g = 0` on `Ω`. -/
theorem eq_zero_of_integral_mul_testFn_eq_zero {Ω : Set (Euc d)} (hΩ : IsOpen Ω)
    {g : Euc d → ℝ} (hg : ContinuousOn g Ω)
    (h : ∀ ψ : Euc d → ℝ, IsTestFn Ω ψ → (∀ x, 0 ≤ ψ x) → ∫ x, g x * ψ x = 0) {x₀ : Euc d}
    (hx₀ : x₀ ∈ Ω) : g x₀ = 0 := by
  by_contra hne
  have hcont : ContinuousAt g x₀ := hg.continuousAt (hΩ.mem_nhds hx₀)
  have hev : ∀ᶠ y in 𝓝 x₀, dist (g y) (g x₀) < |g x₀| / 2 :=
    Metric.tendsto_nhds.1 hcont _ (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hev (hΩ.mem_nhds hx₀))
  set φ : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hφdef
  have hφsupp : tsupport φ ⊆ Metric.ball x₀ r := by
    rw [φ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by simp [hφdef]; linarith)
  have hφx₀ : φ x₀ = 1 :=
    φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by simp [hφdef]; positivity))
  have hφ : IsTestFn Ω φ :=
    ⟨φ.contDiff, φ.hasCompactSupport, hφsupp.trans fun y hy => (hball hy).2, fun h0 => by
      have := congrFun h0 x₀
      rw [hφx₀, Pi.zero_apply] at this
      exact one_ne_zero this⟩
  have h0 := h φ hφ φ.nonneg'
  have hφK : ∀ y ∉ tsupport φ, φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  -- the sign of `g` on the ball
  have hsign : ∀ y ∈ Metric.ball x₀ r, 0 < g y * g x₀ := fun y hy => by
    have h1 : dist (g y) (g x₀) < |g x₀| / 2 := (hball hy).1
    rw [Real.dist_eq, abs_sub_lt_iff] at h1
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · rw [abs_of_neg hneg] at h1
      nlinarith
    · rw [abs_of_pos hpos] at h1
      nlinarith
  have hcontφ : Continuous fun y => g y * g x₀ * φ y :=
    continuous_mul_of_continuousOn hΩ (hg.mul continuousOn_const) φ.continuous
      (isClosed_tsupport φ) (hφsupp.trans fun y hy => (hball hy).2) hφK
  have hpos : 0 < ∫ y, g y * g x₀ * φ y := by
    refine hcontφ.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hasCompactSupport_of_zero_outside φ.hasCompactSupport fun y hy => by
        rw [hφK y hy, mul_zero])
      (fun y => ?_) (x := x₀) ?_
    · by_cases hy : y ∈ Metric.ball x₀ r
      · exact mul_nonneg (hsign y hy).le φ.nonneg
      · rw [hφK y fun h => hy (hφsupp h), mul_zero]
        exact le_rfl
    · rw [hφx₀, mul_one]
      exact (hsign x₀ (Metric.mem_ball_self hr)).ne'
  have hmul : ∫ y, g y * g x₀ * φ y = g x₀ * ∫ y, g y * φ y := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [hmul, h0, mul_zero] at hpos
  exact lt_irrefl _ hpos

/-! ### The strong (pointwise) form of the eigenvalue equation -/

/-- The non-critical region `interior K ∩ {∇φ ≠ 0}` of a `C¹` function is open. -/
theorem isOpen_noncritical {K : Set (Euc d)} {φ : Euc d → ℝ}
    (h1 : ContDiffOn ℝ 1 φ (interior K)) :
    IsOpen (interior K ∩ {x | gradient φ x ≠ 0}) := by
  have hc : ContinuousOn (gradient φ) (interior K) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (h1.continuousOn_fderiv_of_isOpen isOpen_interior le_rfl)
  exact hc.isOpen_inter_preimage isOpen_interior isOpen_compl_singleton

/-- The flux field `a(∇φ)` is `C¹` on the non-critical region `interior K ∩ {∇φ ≠ 0}`. -/
theorem contDiffOn_flux_gradient {p : ℝ} {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} {φ : Euc d → ℝ} (h1 : ContDiffOn ℝ 1 φ (interior K))
    (h2 : ContDiffOn ℝ 2 φ (interior K ∩ {x | gradient φ x ≠ 0})) :
    ContDiffOn ℝ 1 (fun x => flux p F (gradient φ x))
      (interior K ∩ {x | gradient φ x ≠ 0}) := by
  have hΩ : IsOpen (interior K ∩ {x | gradient φ x ≠ 0}) := isOpen_noncritical h1
  have hg : ContDiffOn ℝ 1 (gradient φ) (interior K ∩ {x | gradient φ x ≠ 0}) := by
    have h := h2.fderiv_of_isOpen (m := 1) hΩ (by norm_num)
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h
  exact ((hF.contDiffOn_flux' p).of_le (by exact_mod_cast le_top)).comp hg fun x hx => hx.2

/-- **The strong form of the eigenvalue equation** (paper Appendix A, *Eigenfunction inputs*:
"Where `∇u_i ≠ 0` … the equation is classical on this region"): for a continuous representative
`φ` of a weak first eigenfunction `u`, which is `C¹` on `interior K` and `C²` on the non-critical
region, the *pointwise* equation

  `div a(∇φ) + λ φ^{p-1} = 0`,    `λ = λ_{p,F}(K)`,

holds at every `x ∈ interior K` with `∇φ(x) ≠ 0`.

This is item 4 of the list of missing ingredients in `neg_log_concavityFn_nonpos`; it was missing
there only because the downstream copy `EigenfunctionData.divergence_flux_gradient_add_eq_zero`
(`WangXia.EigenvalueConvexAssemblyAux`) is not importable
(`EigenvalueConvexAssemblyAux → EigenfunctionData → LogConcave`).  **It is now proved.**

Proof: on the open non-critical region the flux field `W = a(∇φ)` is `C¹`
(`contDiffOn_flux_gradient`), so `div W` is continuous there; testing against a nonnegative
`ψ ∈ C_c^∞` of that region, integration by parts
(`integral_inner_gradient_eq_neg_integral_divergence`) turns the weak equation `hu.weakEL` — in
which the weak gradient may be replaced by the classical one, `gradient_ae_eq_weakGrad`'s interior
half `ae_gradient_eq_of_hasWeakGradient`, and `u` by `φ` — into
`∫ (div W + λ φ^{p-1}) ψ = 0`; the fundamental lemma of the calculus of variations
(`eq_zero_of_integral_mul_testFn_eq_zero`) concludes. -/
theorem divergence_flux_gradient_add_eq_zero {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {u φ : Euc d → ℝ}
    (hu : IsWeakFirstEigenfunction p F K u) (hφu : φ =ᵐ[volume] u) (hφc : Continuous φ)
    (h1 : ContDiffOn ℝ 1 φ (interior K))
    (h2 : ContDiffOn ℝ 2 φ (interior K ∩ {x | gradient φ x ≠ 0}))
    {x : Euc d} (hx : x ∈ interior K) (hx' : gradient φ x ≠ 0) :
    divergence (fun y => flux p F (gradient φ y)) x + lambdaGen p F K * φ x ^ (p - 1) = 0 := by
  set Ω : Set (Euc d) := interior K ∩ {x | gradient φ x ≠ 0}
  have hΩ : IsOpen Ω := isOpen_noncritical h1
  have hΩK : Ω ⊆ K := fun z hz => interior_subset hz.1
  set W : Euc d → Euc d := fun y => flux p F (gradient φ y) with hWdef
  have hW : ContDiffOn ℝ 1 W Ω := contDiffOn_flux_gradient hF h1 h2
  -- `div W` and the reaction term are continuous on the non-critical region
  have hdivc : ContinuousOn (divergence W) Ω := by
    have hfd := hW.continuousOn_fderiv_of_isOpen hΩ le_rfl
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact continuousOn_const.inner (hfd.clm_apply continuousOn_const)
  have hreact : ContinuousOn (fun y => lambdaGen p F K * φ y ^ (p - 1)) Ω :=
    continuousOn_const.mul (hφc.continuousOn.rpow_const fun _ _ => Or.inr (by linarith))
  -- the classical gradient of `φ` is the weak gradient of `u` a.e. on `K`
  have h1K : ContDiffOn ℝ 1 φ K := by rwa [hK.isOpen.interior_eq] at h1
  have hae : ∀ᵐ z : Euc d, z ∈ K → gradient φ z = weakGrad u z :=
    ae_gradient_eq_of_hasWeakGradient hu.memW0.hasWeakGradient hφu hK.isOpen h1K
  refine eq_zero_of_integral_mul_testFn_eq_zero hΩ (hdivc.add hreact) (fun ψ hψ _ => ?_)
    ⟨hx, hx'⟩
  -- `ψ` is a test function for `K` as well
  have hψK : IsTestFn K ψ :=
    ⟨hψ.contDiff, hψ.hasCompactSupport, hψ.supp_subset.trans hΩK, hψ.ne_zero⟩
  have hψc : Continuous ψ := hψ.contDiff.continuous
  have hψ0 : ∀ y ∉ tsupport ψ, ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hgradψ : ∀ y ∉ tsupport ψ, gradient ψ y = 0 := by
    intro y hy
    have hloc : ψ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hy] with w hw
      exact hψ0 w hw
    rw [hloc.gradient_eq, gradient_fun_const]
  -- replace the weak gradient by the classical one in the weak equation
  have hflux : (fun y => ⟪flux p F (weakGrad u y), gradient ψ y⟫)
      =ᵐ[volume] fun y => ⟪W y, gradient ψ y⟫ := by
    filter_upwards [hae] with y hy
    by_cases hyK : y ∈ K
    · simp only [hWdef]
      rw [hy hyK]
    · rw [hgradψ y fun h => hyK (hΩK (hψ.supp_subset h))]
      simp
  have hl : ∫ z, ⟪W z, gradient ψ z⟫ = ∫ z, ⟪flux p F (weakGrad u z), gradient ψ z⟫ :=
    (integral_congr_ae hflux).symm
  have hr : ∫ z, φ z ^ (p - 1) * ψ z = ∫ z, u z ^ (p - 1) * ψ z :=
    integral_congr_ae (hφu.mono fun z hz => by simp only [hz])
  have hEL : ∫ z, ⟪W z, gradient ψ z⟫ = lambdaGen p F K * ∫ z, φ z ^ (p - 1) * ψ z := by
    rw [hl, hr]
    exact hu.weakEL ψ hψK
  have hibp := integral_inner_gradient_eq_neg_integral_divergence hΩ hW hψ.contDiff_one
    hψ.hasCompactSupport hψ.supp_subset
  -- integrability of the two summands
  have hint1 : Integrable fun z => divergence W z * ψ z :=
    (continuous_mul_of_continuousOn hΩ hdivc hψc (isClosed_tsupport ψ) hψ.supp_subset hψ0)
      |>.integrable_of_hasCompactSupport
        (hasCompactSupport_of_zero_outside hψ.hasCompactSupport fun y hy => by
          rw [hψ0 y hy, mul_zero])
  have hint2 : Integrable fun z => lambdaGen p F K * φ z ^ (p - 1) * ψ z :=
    (continuous_mul_of_continuousOn hΩ hreact hψc (isClosed_tsupport ψ) hψ.supp_subset hψ0)
      |>.integrable_of_hasCompactSupport
        (hasCompactSupport_of_zero_outside hψ.hasCompactSupport fun y hy => by
          rw [hψ0 y hy, mul_zero])
  have hA : ∫ z, divergence W z * ψ z = -(lambdaGen p F K * ∫ z, φ z ^ (p - 1) * ψ z) := by
    rw [← hEL, hibp, neg_neg]
    exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  have hB : ∫ z, lambdaGen p F K * φ z ^ (p - 1) * ψ z
      = lambdaGen p F K * ∫ z, φ z ^ (p - 1) * ψ z := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  calc ∫ z, (divergence W z + lambdaGen p F K * φ z ^ (p - 1)) * ψ z
      = ∫ z, (divergence W z * ψ z + lambdaGen p F K * φ z ^ (p - 1) * ψ z) :=
        integral_congr_ae (Eventually.of_forall fun z => by ring)
    _ = (∫ z, divergence W z * ψ z) + ∫ z, lambdaGen p F K * φ z ^ (p - 1) * ψ z :=
        integral_add hint1 hint2
    _ = 0 := by rw [hA, hB]; ring

/-! ### The log transform `v = -log φ` -/

/-- **The gradient of the transform `v = -log φ`**: `∇(-log φ) = -φ⁻¹ ∇φ` on an open set where
`φ` is `C¹` and positive.  (The same statement is `hasGradientAt_neg_log` in `LogConcave.lean`,
which is downstream of this file.) -/
theorem hasGradientAt_neg_log {s : Set (Euc d)} (hs : IsOpen s) {φ : Euc d → ℝ}
    (h1 : ContDiffOn ℝ 1 φ s) (hpos : ∀ x ∈ s, 0 < φ x) {x : Euc d} (hx : x ∈ s) :
    HasGradientAt (fun y => -Real.log (φ y)) (-((φ x)⁻¹ • gradient φ x)) x := by
  have hφ : HasGradientAt φ (gradient φ x) x :=
    ((h1.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)).hasGradientAt
  have hlog : HasDerivAt Real.log (φ x)⁻¹ (φ x) := Real.hasDerivAt_log (hpos x hx).ne'
  have h := (hlog.comp_hasFDerivAt x hφ.hasFDerivAt).neg
  rw [hasGradientAt_iff_hasFDerivAt, map_neg, map_smul]
  exact h

/-- **The transform `v = -log φ` is critical exactly where `φ` is**: `∇v(x) ≠ 0 ↔ ∇φ(x) ≠ 0`,
since `∇v = -φ⁻¹ ∇φ` and `φ > 0`. -/
theorem gradient_neg_log_ne_zero_iff {s : Set (Euc d)} (hs : IsOpen s) {φ : Euc d → ℝ}
    (h1 : ContDiffOn ℝ 1 φ s) (hpos : ∀ x ∈ s, 0 < φ x) {x : Euc d} (hx : x ∈ s) :
    gradient (fun y => -Real.log (φ y)) x ≠ 0 ↔ gradient φ x ≠ 0 := by
  rw [(hasGradientAt_neg_log hs h1 hpos hx).gradient]
  constructor
  · intro h hg
    exact h (by rw [hg, smul_zero, neg_zero])
  · intro h hg
    refine h ?_
    have h0 : (φ x)⁻¹ • gradient φ x = 0 := neg_eq_zero.1 hg
    exact (smul_eq_zero.1 h0).resolve_left (inv_ne_zero (hpos x hx).ne')

/-- `v = -log φ` is differentiable near every interior point. -/
theorem eventually_differentiableAt_neg_log {K : Set (Euc d)} {φ : Euc d → ℝ}
    (h1 : ContDiffOn ℝ 1 φ (interior K)) (hpos : ∀ z ∈ interior K, 0 < φ z) {x : Euc d}
    (hx : x ∈ interior K) :
    ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ (fun w => -Real.log (φ w)) z := by
  have hvC1 : ContDiffOn ℝ 1 (fun w => -Real.log (φ w)) (interior K) :=
    (h1.log fun z hz => (hpos z hz).ne').neg
  filter_upwards [isOpen_interior.mem_nhds hx] with z hz
  exact (hvC1.differentiableOn one_ne_zero).differentiableAt (isOpen_interior.mem_nhds hz)

/-- `∇v` is differentiable at every non-critical interior point, i.e. the Hessian `D²v` exists
there. -/
theorem differentiableAt_gradient_neg_log {K : Set (Euc d)} {φ : Euc d → ℝ}
    (h1 : ContDiffOn ℝ 1 φ (interior K))
    (h2 : ContDiffOn ℝ 2 φ (interior K ∩ {x | gradient φ x ≠ 0}))
    (hpos : ∀ z ∈ interior K, 0 < φ z) {x : Euc d} (hx : x ∈ interior K)
    (hx' : gradient φ x ≠ 0) :
    DifferentiableAt ℝ (gradient fun w => -Real.log (φ w)) x := by
  have hΩ : IsOpen (interior K ∩ {x | gradient φ x ≠ 0}) := isOpen_noncritical h1
  have hvC2 : ContDiffOn ℝ 2 (fun w => -Real.log (φ w))
      (interior K ∩ {x | gradient φ x ≠ 0}) :=
    (h2.log fun z hz => (hpos z hz.1).ne').neg
  have hgC1 : ContDiffOn ℝ 1 (gradient fun w => -Real.log (φ w))
      (interior K ∩ {x | gradient φ x ≠ 0}) := by
    have h := hvC2.fderiv_of_isOpen (m := 1) hΩ (by norm_num)
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h
  exact (hgC1.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds ⟨hx, hx'⟩)

/-- **The transformed (log-eigenfunction) equation** (paper (A.log-eigenfunction)) for the
continuous representative `φ` of a weak first eigenfunction: at every non-critical interior point
the transform `v = -log φ` satisfies

  `div a(∇v) = λ + (p - 1) F(∇v)^p`,   `λ = λ_{p,F}(K)`.

This is the equation Korevaar's concavity maximum principle is applied to: its right-hand side is
a **convex** function of `∇v` (`convexOn_rpow_of_isSmoothStrictNorm`), which is the
concavity-preserving structure condition of MRS24, Theorem 1.1.

Proved by feeding the strong form `divergence_flux_gradient_add_eq_zero` into the chain-rule
computation `Korevaar.divergence_flux_gradient_neg_log` of `KorevaarAux.lean`. -/
theorem divergence_flux_gradient_neg_log_of_eigenfunction {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {u φ : Euc d → ℝ}
    (hu : IsWeakFirstEigenfunction p F K u) (hφu : φ =ᵐ[volume] u) (hφc : Continuous φ)
    (hpos : ∀ z ∈ interior K, 0 < φ z) (h1 : ContDiffOn ℝ 1 φ (interior K))
    (h2 : ContDiffOn ℝ 2 φ (interior K ∩ {x | gradient φ x ≠ 0}))
    {x : Euc d} (hx : x ∈ interior K)
    (hx' : gradient (fun w => -Real.log (φ w)) x ≠ 0) :
    divergence (fun y => flux p F (gradient (fun w => -Real.log (φ w)) y)) x =
      lambdaGen p F K + (p - 1) * F (gradient (fun w => -Real.log (φ w)) x) ^ p := by
  have hφx : gradient φ x ≠ 0 :=
    (gradient_neg_log_ne_zero_iff isOpen_interior h1 hpos hx).1 hx'
  have hposnhds : ∀ᶠ y in 𝓝 x, 0 < φ y := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy using hpos y hy
  have hv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun w => -Real.log (φ w)) y :=
    eventually_differentiableAt_neg_log h1 hpos hx
  have hv' : DifferentiableAt ℝ (gradient fun w => -Real.log (φ w)) x :=
    differentiableAt_gradient_neg_log h1 h2 hpos hx hφx
  have hstrong := divergence_flux_gradient_add_eq_zero hp hF hK hu hφu hφc h1 h2 hx hφx
  exact divergence_flux_gradient_neg_log hp hF hposnhds hv hv' hx' hstrong

/-! ### The degenerate case of Korevaar's interior step, assembled -/

/-- **Korevaar's interior second-order step for the first eigenfunction, assembled**
(MRS24, Theorem 1.1): at an interior local maximum `(x, y)` of the concavity function of
`v = -log φ` whose two points *and their midpoint* are non-critical, the Hessian of `v` at the
midpoint equals the average of the Hessians at `x` and `y` in **every** direction:

  `D²v(m)[ζ, ζ] = (D²v(x)[ζ, ζ] + D²v(y)[ζ, ζ]) / 2`.

This is the whole interior half of Korevaar's argument, now unconditional: the first-order
conditions (`Korevaar.gradient_eq_of_isLocalMax_pair`) make the three gradients agree, the
transformed equation (`divergence_flux_gradient_neg_log_of_eigenfunction`, which rests on the
strong form of the eigenvalue equation proved above) makes the three flux divergences agree, and
`Korevaar.inner_hessian_midpoint_eq_of_equation` — the trace step against the positive-definite
ellipticity matrix `A(q) = Da(q)` together with the second-order conditions — upgrades the
Loewner inequality to an equality.

It is exactly here that Korevaar's proof invokes the **strong maximum principle** for the operator
linearized at the common gradient `q`, to conclude that the concavity function is constant — the
one step of MRS24, Theorem 1.1 that is still missing (see the TODO in
`neg_log_concavityFn_nonpos`). -/
theorem inner_hessian_midpoint_eq_of_isLocalMax {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {u φ : Euc d → ℝ}
    (hu : IsWeakFirstEigenfunction p F K u) (hφu : φ =ᵐ[volume] u) (hφc : Continuous φ)
    (hpos : ∀ z ∈ interior K, 0 < φ z) (h1 : ContDiffOn ℝ 1 φ (interior K))
    (h2 : ContDiffOn ℝ 2 φ (interior K ∩ {x | gradient φ x ≠ 0}))
    {x y : Euc d} (hx : x ∈ interior K) (hy : y ∈ interior K)
    (hgx : gradient φ x ≠ 0) (hgy : gradient φ y ≠ 0)
    (hgm : gradient φ (midpoint ℝ x y) ≠ 0)
    (hmax : IsLocalMax
      (fun q : Euc d × Euc d => concavityFn (fun w => -Real.log (φ w)) q.1 q.2) (x, y))
    (ζ : Euc d) :
    ⟪fderiv ℝ (gradient fun w => -Real.log (φ w)) (midpoint ℝ x y) ζ, ζ⟫ =
      (⟪fderiv ℝ (gradient fun w => -Real.log (φ w)) x ζ, ζ⟫ +
        ⟪fderiv ℝ (gradient fun w => -Real.log (φ w)) y ζ, ζ⟫) / 2 := by
  have hm : midpoint ℝ x y ∈ interior K :=
    midpoint_mem_interior hK.convex (subset_closure (interior_subset hx)) hy
  -- differentiability of `v` near the three points, and of `∇v` at them
  have hdx := eventually_differentiableAt_neg_log h1 hpos hx
  have hdy := eventually_differentiableAt_neg_log h1 hpos hy
  have hdm := eventually_differentiableAt_neg_log h1 hpos hm
  have hHx : HasFDerivAt (gradient fun w => -Real.log (φ w))
      (fderiv ℝ (gradient fun w => -Real.log (φ w)) x) x :=
    (differentiableAt_gradient_neg_log h1 h2 hpos hx hgx).hasFDerivAt
  have hHy : HasFDerivAt (gradient fun w => -Real.log (φ w))
      (fderiv ℝ (gradient fun w => -Real.log (φ w)) y) y :=
    (differentiableAt_gradient_neg_log h1 h2 hpos hy hgy).hasFDerivAt
  have hHm : HasFDerivAt (gradient fun w => -Real.log (φ w))
      (fderiv ℝ (gradient fun w => -Real.log (φ w)) (midpoint ℝ x y)) (midpoint ℝ x y) :=
    (differentiableAt_gradient_neg_log h1 h2 hpos hm hgm).hasFDerivAt
  -- the first-order conditions: the three gradients of `v` coincide
  have hvx : HasGradientAt (fun w => -Real.log (φ w))
      (gradient (fun w => -Real.log (φ w)) x) x := hdx.self_of_nhds.hasGradientAt
  have hvy : HasGradientAt (fun w => -Real.log (φ w))
      (gradient (fun w => -Real.log (φ w)) y) y := hdy.self_of_nhds.hasGradientAt
  have hvm : HasGradientAt (fun w => -Real.log (φ w))
      (gradient (fun w => -Real.log (φ w)) (midpoint ℝ x y)) (midpoint ℝ x y) :=
    hdm.self_of_nhds.hasGradientAt
  obtain ⟨hqm, hqy⟩ := gradient_eq_of_isLocalMax_pair hvx hvy hvm hmax
  -- the common gradient of `v` does not vanish
  have hq : gradient (fun w => -Real.log (φ w)) x ≠ 0 :=
    (gradient_neg_log_ne_zero_iff isOpen_interior h1 hpos hx).2 hgx
  have hqy' : gradient (fun w => -Real.log (φ w)) y ≠ 0 :=
    (gradient_neg_log_ne_zero_iff isOpen_interior h1 hpos hy).2 hgy
  have hqm' : gradient (fun w => -Real.log (φ w)) (midpoint ℝ x y) ≠ 0 :=
    (gradient_neg_log_ne_zero_iff isOpen_interior h1 hpos hm).2 hgm
  -- the transformed equation at the three points
  have hEx := divergence_flux_gradient_neg_log_of_eigenfunction hp hF hK hu hφu hφc hpos h1 h2
    hx hq
  have hEy := divergence_flux_gradient_neg_log_of_eigenfunction hp hF hK hu hφu hφc hpos h1 h2
    hy hqy'
  have hEm := divergence_flux_gradient_neg_log_of_eigenfunction hp hF hK hu hφu hφc hpos h1 h2
    hm hqm'
  exact inner_hessian_midpoint_eq_of_equation hp hF hdx hdy hdm hHx hHy hHm hq hqy hqm hmax
    hEx hEy hEm ζ

end Korevaar

end Komlos.Literature
