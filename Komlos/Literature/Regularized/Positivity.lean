import Komlos.Literature.Regularized.BoundaryPositivity
import Komlos.Literature.Regularized.PositivityLower

/-!
# Lane `L2` (`reg/positivity`), step 4: positivity, and the assembly

`REGULARIZED_ROUTE.md`, Revision 2 (iii): the frozen lane statement
`IsRegMinimizer.exists_pos_continuous_rep` (formerly a named `sorry` in `Interface.lean`) is
proved here.

## Positivity

The functional is convex in the density `ρ̃ = w²`, and the entropy `(κ/4) ∫ ρ̃ log ρ̃` has
one-sided derivative `-∞` at `ρ̃ = 0`.  Comparing the minimizer with
`ρ̃_τ = (1-τ) u² + τ σ`, `σ` a smooth positive density compactly supported in `K`, and letting
`τ ↓ 0` therefore gives the quantitative bound `∫ σ log u ≥ -C(σ)`; in particular `u > 0` a.e.
and `log u ∈ L¹_loc(K)`.  One-sided variations `u + τψ`, `ψ ≥ 0` — which need only the *right*
derivative of the convex-in-`ρ̃` energy, and are therefore legitimate before the full
Euler–Lagrange equation is available — then show that `v = -log u` is a weak subsolution of a
uniformly elliptic inequality with bounded right-hand side on `{v ≥ 0}`, and De Giorgi's local
maximum principle (`exists_dg_sup_bound` / `exists_essSup_bound`) bounds `v` above on interior
balls, i.e. bounds `u` below by a positive constant.  This is `exists_local_lower_bound`,
proved by lane `reg/pos-lower` in `PositivityLower.lean` (route (A): the shifted logarithm
`Z_δ = log δ - log(v+δ)` carries its own De Giorgi class).

## The assembly

`IsRegMinimizer.exists_pos_continuous_rep` glues:

* `IsRegMinimizer.exists_interior_continuous_rep` (step 2) — a representative `φ₀` continuous
  on `K`;
* `exists_boundary_sup_decay` + `tendsto_zero_nhdsWithin_of_sup_decay` (step 3) — `φ₀ → 0` at
  every boundary point, hence `K.indicator φ₀` is continuous on `ℝ^d`;
* `exists_local_lower_bound` + `pos_of_ae_lower_bound_ball` (step 4) — `φ₀ > 0` on `K`.

No deviation: `exists_pos_continuous_rep` has *exactly* the frozen signature.  Every
De Giorgi–Nash input of lane `DGN` (`exists_dg_sup_bound`, `exists_dg_osc_decay`,
`IsDG.exists_holder_representative`) carries the hypothesis `0 < d` — it is the hypothesis of
the Sobolev inequality they are built on — so the main argument runs only for `d ≥ 1`; the
degenerate case `d = 0` is dispatched separately at the top of the proof, where `Euc 0` is a
one-point space, `u` is constant and the constraint `∫ u² = 1` forbids the value `0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### From local lower bounds to pointwise positivity -/

/-- **Positivity of a continuous representative from local essential lower bounds**: if `φ` is
continuous on the open set `U`, agrees a.e. on `U` with `v`, and around every point of `U` there
is a ball on which `v ≥ ε > 0` a.e., then `φ > 0` on `U`.  (A point with `φ ≤ 0` would, by
continuity, give a ball of positive measure on which `φ < ε`.) -/
theorem pos_of_ae_lower_bound_ball {U : Set (Euc d)} (hU : IsOpen U) {φ v : Euc d → ℝ}
    (hφc : ContinuousOn φ U) (hφv : ∀ᵐ x, x ∈ U → φ x = v x)
    (hlow : ∀ x ∈ U, ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧ Metric.ball x r ⊆ U ∧
      ∀ᵐ y ∂(volume.restrict (Metric.ball x r)), ε ≤ v y) :
    ∀ x ∈ U, 0 < φ x := by
  intro x₀ hx₀
  obtain ⟨r, ε, hr, hε, hrU, hlb⟩ := hlow x₀ hx₀
  by_contra hcon
  rw [not_lt] at hcon
  have hlt : φ x₀ < ε := lt_of_le_of_lt hcon hε
  have hev : ∀ᶠ y in 𝓝 x₀, φ y < ε :=
    (hφc.continuousAt (hU.mem_nhds hx₀)).eventually (gt_mem_nhds hlt)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hρ : 0 < min δ r := lt_min hδ hr
  have hnull : volume (Metric.ball x₀ (min δ r)) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hφv, (ae_restrict_iff' measurableSet_ball).1 hlb] with y h1 h2 hy
    have hyδ : y ∈ Metric.ball x₀ δ := Metric.ball_subset_ball (min_le_left δ r) hy
    have hyr : y ∈ Metric.ball x₀ r := Metric.ball_subset_ball (min_le_right δ r) hy
    have hyU : y ∈ U := hrU hyr
    have hφy := hδball y hyδ
    rw [h1 hyU] at hφy
    exact absurd (h2 hyr) (not_le.2 hφy)
  exact (Metric.measure_ball_pos volume x₀ hρ).ne' hnull

/-! ### Gluing with zero outside `K` -/

/-- Gluing with `0` outside an open set: if `φ` is continuous on the open set `K` and tends to
`0` at every frontier point from inside `K`, then `K.indicator φ` is continuous. -/
theorem continuous_indicator_of_tendsto (hK : IsOpen K) {φ : Euc d → ℝ}
    (hφc : ContinuousOn φ K) (hbd : ∀ x₀ ∈ frontier K, Tendsto φ (𝓝[K] x₀) (𝓝 0)) :
    Continuous (K.indicator φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ K
  · have heq : φ =ᶠ[𝓝 x] K.indicator φ := by
      filter_upwards [hK.mem_nhds hx] with y hy
      exact (Set.indicator_of_mem hy φ).symm
    exact (hφc.continuousAt (hK.mem_nhds hx)).congr heq
  by_cases hxc : x ∈ closure K
  · have hfr : x ∈ frontier K := by
      rw [hK.frontier_eq]
      exact ⟨hxc, hx⟩
    rw [ContinuousAt, Set.indicator_of_notMem hx]
    have h1 : Tendsto (K.indicator φ) (𝓝[K] x) (𝓝 0) :=
      (hbd x hfr).congr'
        (eventually_nhdsWithin_of_forall fun y hy => (Set.indicator_of_mem hy φ).symm)
    have h2 : Tendsto (K.indicator φ) (𝓝[Kᶜ] x) (𝓝 0) :=
      tendsto_const_nhds.congr'
        (eventually_nhdsWithin_of_forall fun y hy => (Set.indicator_of_notMem hy φ).symm)
    have h3 := h1.sup h2
    rwa [← nhdsWithin_union, Set.union_compl_self, nhdsWithin_univ] at h3
  · have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] K.indicator φ := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      exact (Set.indicator_of_notMem (fun h => hy (subset_closure h)) φ).symm
    exact continuousAt_const.congr heq

/-- A representative of `v` on the open set `K`, glued with `0` outside `K`, is a representative
of `v` on `ℝ^d` when `v` vanishes outside `K`. -/
theorem indicator_ae_eq_of_ae_eq (hK : IsOpen K) {φ v : Euc d → ℝ}
    (hφv : φ =ᵐ[volume.restrict K] v) (hvK : ∀ x, x ∉ K → v x = 0) :
    K.indicator φ =ᵐ[volume] v := by
  filter_upwards [(ae_restrict_iff' hK.measurableSet).1 hφv] with x hx
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK]
    exact hx hxK
  · rw [Set.indicator_of_notMem hxK, hvK x hxK]

/-! ### The frozen statement of lane `L2` -/

/-- **(L2, `reg/positivity`)** The minimizer has a continuous representative that vanishes off
`K` and is positive on `K`.

This is the frozen lane statement `IsRegMinimizer.exists_pos_continuous_rep`, verbatim. -/
theorem IsRegMinimizer.exists_pos_continuous_rep (hκ : 0 < κ)
    (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) :
    ∃ φ : Euc d → ℝ, Continuous φ ∧ φ =ᵐ[volume] u ∧ (∀ x, x ∉ K → φ x = 0) ∧
      ∀ x ∈ K, 0 < φ x := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `Euc 0` is a one-point space: `u` is constant, and the constraint `∫ u² = 1` forbids `0`
    obtain ⟨x₀, hx₀⟩ := hK.nonempty
    have hconst : ∀ y : Euc 0, u y = u x₀ := fun y => congrArg u (Subsingleton.elim y x₀)
    have hcont : Continuous u := by
      have hfun : u = fun _ => u x₀ := funext hconst
      rw [hfun]
      exact continuous_const
    have hpos : 0 < u x₀ := by
      rcases (hu.nonneg x₀).eq_or_lt with h | h
      · exfalso
        have hzero : ∀ y : Euc 0, u y ^ (2 : ℝ) = 0 := fun y => by
          rw [hconst y, ← h, Real.zero_rpow (by norm_num)]
        have hone := hu.integral_rpow
        rw [integral_congr_ae (Eventually.of_forall hzero)] at hone
        simp at hone
      · exact h
    exact ⟨u, hcont, ae_eq_refl u, hu.eq_zero_of_notMem,
      fun x _ => by rw [hconst x]; exact hpos⟩
  obtain ⟨cc, CC, hΨ'⟩ := hΨ.exists_isRegProfileWith
  obtain ⟨φ₀, v, M, hφc, hφv, hvu, hvmin, hvcomp, hvm, hM0, hvM, hv0, hvK, -⟩ :=
    hu.exists_interior_continuous_rep hd hκ hΨ' hK
  have hφv' : ∀ᵐ x : Euc d, x ∈ K → φ₀ x = v x := (ae_restrict_iff' hK.isOpen.measurableSet).1 hφv
  -- boundary values
  have hbd : ∀ x₀ ∈ frontier K, Tendsto φ₀ (𝓝[K] x₀) (𝓝 0) := fun x₀ hx₀ =>
    tendsto_zero_nhdsWithin_of_sup_decay hK hφc hφv hv0
      (fun ε hε => exists_boundary_sup_decay hd hκ hΨ' hK hvmin hvcomp hvm hx₀ hε)
  refine ⟨K.indicator φ₀, continuous_indicator_of_tendsto hK.isOpen hφc hbd, ?_, ?_, ?_⟩
  · exact (indicator_ae_eq_of_ae_eq hK.isOpen hφv hvK).trans hvu
  · exact fun x hx => Set.indicator_of_notMem hx _
  · intro x hx
    rw [Set.indicator_of_mem hx]
    refine pos_of_ae_lower_bound_ball hK.isOpen hφc hφv' (fun y hy => ?_) x hx
    exact exists_local_lower_bound hd hκ hΨ' hK hvmin hvcomp hvm hy

end Komlos.Literature.Regularized
