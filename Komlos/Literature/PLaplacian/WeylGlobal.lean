import Komlos.Literature.PLaplacian.WeylLemma

/-!
# Gluing the local smooth representatives in Weyl's lemma

The local representatives from `WeylLemma.lean` agree on overlaps: they are continuous
and agree almost everywhere with the same weak solution. A countable subcover then
preserves the almost-everywhere identities when the representatives are glued.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-- Local smooth representatives of a function and its gradient glue on an open set.
The countable subcover is essential: almost-everywhere statements cannot in general
be intersected over an uncountable family of neighborhoods. -/
theorem exists_contDiffOn_ae_eq_gradient_of_local
    {U : Set (Euc d)} {u : Euc d → ℝ} {G : Euc d → Euc d}
    (hloc : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U ∧
      ∃ v : Euc d → ℝ, ContDiff ℝ ∞ v ∧
        (∀ᵐ y, y ∈ Metric.ball x r → u y = v y) ∧
        ∀ᵐ y, y ∈ Metric.ball x r → G y = gradient v y) :
    ∃ v : Euc d → ℝ, ContDiffOn ℝ ∞ v U ∧
      (∀ᵐ x, x ∈ U → u x = v x) ∧
      ∀ᵐ x, x ∈ U → G x = gradient v x := by
  classical
  choose r hr hrU f hf huf hGf using fun x : U => hloc x x.property
  let B : U → Set (Euc d) := fun x => Metric.ball x.val (r x)
  have hBo : ∀ x : U, IsOpen (B x) := fun _ => Metric.isOpen_ball
  have hBself : ∀ x : U, x.val ∈ B x := fun x => Metric.mem_ball_self (hr x)
  have hcover : (⋃ x : U, B x) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => hrU x
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hBself ⟨x, hx⟩⟩
  have hagree : ∀ i j : U, EqOn (f i) (f j) (B i ∩ B j) := by
    intro i j
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ ((hBo i).inter (hBo j))
      (hf i).continuous.continuousOn (hf j).continuous.continuousOn
    apply (ae_restrict_iff' ((hBo i).inter (hBo j)).measurableSet).mpr
    filter_upwards [huf i, huf j] with x hi hj hx
    exact (hi hx.1).symm.trans (hj hx.2)
  let v : Euc d → ℝ := fun x => if hx : x ∈ U then f ⟨x, hx⟩ x else u x
  have hv_eq : ∀ i : U, EqOn v (f i) (B i) := by
    intro i y hy
    have hyU : y ∈ U := hrU i hy
    dsimp [v]
    rw [dif_pos hyU]
    exact hagree ⟨y, hyU⟩ i ⟨hBself ⟨y, hyU⟩, hy⟩
  have hv_eventually : ∀ i : U, ∀ y ∈ B i, v =ᶠ[𝓝 y] f i := by
    intro i y hy
    filter_upwards [(hBo i).mem_nhds hy] with z hz
    exact hv_eq i hz
  have hvcd : ContDiffOn ℝ ∞ v U := by
    intro x hx
    exact ((hf ⟨x, hx⟩).contDiffAt.congr_of_eventuallyEq
      (hv_eventually ⟨x, hx⟩ x (hBself ⟨x, hx⟩))).contDiffWithinAt
  have hvgrad : ∀ i : U, ∀ y ∈ B i, gradient v y = gradient (f i) y := by
    intro i y hy
    exact (hv_eventually i y hy).gradient_eq
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable B hBo
  let : Countable T := hTc.to_subtype
  have hpatches : ∀ᵐ y, ∀ i : T, y ∈ B i.val →
      u y = v y ∧ G y = gradient v y := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [huf i.val, hGf i.val] with y hu hG hy
    exact ⟨(hu hy).trans (hv_eq i.val hy).symm,
      (hG hy).trans (hvgrad i.val y hy).symm⟩
  have hglobal : ∀ᵐ y, y ∈ U → u y = v y ∧ G y = gradient v y := by
    filter_upwards [hpatches] with y hy hyU
    have hycover : y ∈ ⋃ i ∈ T, B i := by rwa [hT, hcover]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hycover
    obtain ⟨hiT, hyi⟩ := mem_iUnion.mp hi
    exact hy ⟨i, hiT⟩ hyi
  refine ⟨v, hvcd, ?_, ?_⟩
  · filter_upwards [hglobal] with y hy hyU
    exact (hy hyU).1
  · filter_upwards [hglobal] with y hy hyU
    exact (hy hyU).2

/-- **Weyl's lemma on an entire open set.** A weak solution for a constant symmetric
uniformly elliptic operator has a smooth representative on the open domain, with
classical gradient equal almost everywhere there to the prescribed weak gradient. -/
theorem exists_contDiffOn_ae_eq_gradient_of_weakSolution
    {A₀ : Euc d →L[ℝ] Euc d} (hsymm : ∀ p q : Euc d, ⟪A₀ p, q⟫ = ⟪p, A₀ q⟫)
    {μ : ℝ} (hμ : 0 < μ) (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    {U : Set (Euc d)} (hU : IsOpen U) {u : Euc d → ℝ} {G : Euc d → Euc d}
    (hG : HasWeakGradient u G)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ y, ⟪A₀ (G y), gradient ψ y⟫ = 0) :
    ∃ v : Euc d → ℝ, ContDiffOn ℝ ∞ v U ∧
      (∀ᵐ x, x ∈ U → u x = v x) ∧
      ∀ᵐ x, x ∈ U → G x = gradient v x := by
  apply exists_contDiffOn_ae_eq_gradient_of_local
  intro x hx
  exact exists_contDiff_ae_eq_gradient_of_weakSolution hsymm hμ hell hU hG hsol hx

end Komlos.Literature
