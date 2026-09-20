import Komlos.Literature.Regularized.PositivityEnergy

/-!
# Lane `L2` (`reg/positivity`), step 2: the De Giorgi class and interior continuity

`REGULARIZED_ROUTE.md`, Revision 2 (ii).  `PositivityLocal.lean` has removed the constraint:
the minimizer `u` minimizes the *local* functional

`J(w) = ∫ [ w² Ψ(∇w/w) + (κ/2) w² log w - Λ w² ]`,  `Λ = regMin 2 κ Ψ K + κ/4`,

over all nonnegative bounded `w ∈ W₀^{1,2}(K)` (`IsRegMinimizer.regFree_le`), and the integrand
obeys the **standard quadratic growth**

`(c/2) ‖ξ‖² + Ψ(0) s² + P(s) - Λ s² ≤ f(s, ξ) ≤ (C/2) ‖ξ‖² + Ψ(0) s² + P(s) - Λ s²`

(`IsRegProfileWith.le_homogeneousDensity`, `IsRegProfileWith.homogeneousDensity_le`), whose
lower-order part is *bounded* because `u` is bounded.  Comparison with `u - η²(u-k)_+` and with
`u + η²(k-u)_+` therefore puts `u` in the De Giorgi class `DG(K, γ, χ)` of
`Komlos/Literature/Regularized/DeGiorgiClass.lean`, and lane `DGN`'s
`IsDG.exists_holder_representative` supplies a representative that is continuous on `K` and
Hölder continuous on every compact subset.

## Contents

* `IsRegMinimizer.exists_measurable_regComp` — a *pointwise* bounded, nonnegative, **measurable**
  representative of the minimizer, together with a measurable weak gradient field.  The
  De Giorgi class demands genuine (not merely a.e.) measurability and pointwise bounds, and
  `MemLp` only gives the a.e. versions; this lemma does the plumbing once.
* `exists_isDGSub_univ` — the **sub** side of the De Giorgi class for the zero extension, on
  *all* of `ℝ^d`; this is what the boundary estimate consumes.
* `isDG_of_regMinimizer` — **the De Giorgi class membership**.  The level-set energy
  inequalities are `exists_energy_ineq` / `exists_energy_ineq_super`
  (`Komlos/Literature/Regularized/PositivityEnergy.lean`); the competitors, the localization of
  the comparison and the hole-filling iteration are in
  `Komlos/Literature/Regularized/PositivityCacc.lean`.
* `IsRegMinimizer.exists_interior_continuous_rep` — interior continuity, assembled from the
  previous two and `IsDG.exists_holder_representative`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### A measurable representative -/

/-- **A measurable representative of the minimizer.**  `MemLp` only provides an
`AEStronglyMeasurable` representative and an *essential* bound; the De Giorgi class
(`IsDGSub.measurable`, `IsDGSub.measurable_grad`) and `IsDG.exists_holder_representative`
(pointwise `|z| ≤ S`) both need honest pointwise statements.  Truncating a strongly measurable
version between `0` and the essential bound and multiplying by the indicator of `K` produces a
representative in the local competitor class `IsRegComp` that is measurable, pointwise
nonnegative, pointwise bounded and supported in `K`, together with a measurable weak gradient
field. -/
theorem IsRegMinimizer.exists_measurable_regComp (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) :
    ∃ (v : Euc d → ℝ) (G : Euc d → Euc d) (M : ℝ),
      v =ᵐ[volume] u ∧ IsRegMinimizer 2 κ Ψ K v ∧ IsRegComp K v ∧
        Measurable v ∧ Measurable G ∧ HasWeakGradient v G ∧ G =ᵐ[volume] weakGrad v ∧
        0 ≤ M ∧ (∀ x, v x ≤ M) ∧ (∀ x, 0 ≤ v x) ∧ ∀ x, x ∉ K → v x = 0 := by
  classical
  obtain ⟨M, hM⟩ := hu.exists_bound hκ hΨ hK
  set M' : ℝ := max M 0 with hM'def
  have hM0 : (0 : ℝ) ≤ M' := le_max_right _ _
  -- a strongly measurable version of `u`
  set ũ : Euc d → ℝ := hu.memW0.memLp.aestronglyMeasurable.mk u with hũdef
  have hũm : Measurable ũ := hu.memW0.memLp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hũu : ũ =ᵐ[volume] u := hu.memW0.memLp.aestronglyMeasurable.ae_eq_mk.symm
  -- truncate and localize
  set v : Euc d → ℝ := K.indicator (fun x => min (max (ũ x) 0) M') with hvdef
  have hvm : Measurable v :=
    ((hũm.max measurable_const).min measurable_const).indicator hK.isOpen.measurableSet
  have hv0 : ∀ x, 0 ≤ v x := by
    intro x
    refine Set.indicator_nonneg (fun y _ => ?_) x
    exact le_min (le_max_right _ _) hM0
  have hvK : ∀ x, x ∉ K → v x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hvM : ∀ x, v x ≤ M' := by
    intro x
    by_cases hx : x ∈ K
    · rw [hvdef, Set.indicator_of_mem hx]
      exact min_le_right _ _
    · rw [hvK x hx]; exact hM0
  have hvu : v =ᵐ[volume] u := by
    filter_upwards [hũu, hM] with x h1 h2
    by_cases hx : x ∈ K
    · rw [hvdef, Set.indicator_of_mem hx, h1, max_eq_left (hu.nonneg x),
        min_eq_left (h2.trans (le_max_left _ _))]
    · rw [hvK x hx, hu.eq_zero_of_notMem x hx]
  have hvmin : IsRegMinimizer 2 κ Ψ K v := hu.congr_ae hvu hv0 hvK
  have hvcomp : IsRegComp K v := ⟨hvmin.memW0, hv0, hvK, ⟨M', hvM⟩⟩
  -- a measurable weak gradient field
  set G : Euc d → Euc d := hvcomp.aestronglyMeasurable_grad.mk (weakGrad v) with hGdef
  have hGm : Measurable G :=
    hvcomp.aestronglyMeasurable_grad.stronglyMeasurable_mk.measurable
  have hGg : G =ᵐ[volume] weakGrad v := hvcomp.aestronglyMeasurable_grad.ae_eq_mk.symm
  exact ⟨v, G, M', hvu, hvmin, hvcomp, hvm, hGm,
    hvcomp.memW0.hasWeakGradient.congr_right hGg.symm, hGg, hM0, hvM, hv0, hvK⟩

/-! ### The De Giorgi sub-class of the zero extension, on all of `ℝ^d` -/

/-- **The zero extension of the minimizer lies in `DG⁺(ℝ^d, γ, 1)`.**

The sub-side level-set energy inequality `exists_energy_ineq` holds on *every* ball of `ℝ^d`,
because the competitor `u - ζ (u-k)_+` is admissible for the local problem whatever the
support of the cutoff (`IsRegComp.truncCompetitor`).  Only the sign case `k < 0` has to be
added: there `{u > k}` is everything, but `∇u = 0` a.e. on `{u = 0}`, so the left-hand side is
unchanged when the level is raised to `0`, while the right-hand side only grows.

This global membership is what the *boundary* estimate uses: De Giorgi's local maximum
principle `exists_dg_sup_bound` may then be applied on balls centred at a boundary point of
`K`. -/
theorem exists_isDGSub_univ (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegMinimizer 2 κ Ψ K u) (hcomp : IsRegComp K u)
    {G : Euc d → Euc d} (hG : HasWeakGradient u G) (hum : Measurable u) (hGm : Measurable G)
    (hGg : G =ᵐ[volume] weakGrad u) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ R₀ : ℝ, IsDGSub γ 1 R₀ Set.univ u G := by
  classical
  obtain ⟨M, hM⟩ := hcomp.exists_le
  obtain ⟨γ, hγ0, hsub⟩ := exists_energy_ineq hκ hΨ hK hu hcomp hum
  have hGnorm : (fun x : Euc d => ‖G x‖ ^ 2) =ᵐ[volume] fun x => ‖weakGrad u x‖ ^ 2 := by
    filter_upwards [hGg] with x hx; rw [hx]
  have hGint : Integrable (fun x : Euc d => ‖G x‖ ^ 2) volume :=
    hcomp.integrable_normSq_grad.congr hGnorm.symm
  have hposm : MeasurableSet {x : Euc d | (0 : ℝ) < u x} :=
    measurableSet_lt measurable_const hum
  have hshift : ∀ (x₀ : Euc d) (s k : ℝ),
      IntegrableOn (fun x => max (u x - k) 0 ^ 2) (Metric.ball x₀ s) volume := by
    intro x₀ s k
    have hc : Continuous fun t : ℝ => max (t - k) 0 :=
      (continuous_id.sub continuous_const).max continuous_const
    refine Integrable.mono'
      (integrableOn_const (μ := volume) (C := (max (M - k) 0 + |k|) ^ 2)
        (measure_ball_lt_top (x := x₀) (r := s)).ne)
      ((hc.comp_aestronglyMeasurable hcomp.aestronglyMeasurable).pow 2).restrict ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : max (u x - k) 0 ≤ max (M - k) 0 + |k| := by
      have h2 : u x - k ≤ M - k := by linarith [hM x]
      have h3 : (0 : ℝ) ≤ |k| := abs_nonneg k
      have h4 : max (u x - k) 0 ≤ max (M - k) 0 := max_le_max h2 le_rfl
      linarith
    exact sq_le_sq_of_nonneg (le_max_right _ _) h1
  refine ⟨γ, hγ0, fun R₀ => ?_⟩
  refine
    { hasWeakGradient := hG
      measurable := hum
      measurable_grad := hGm
      integrableOn := fun x₀ s _ => ⟨hcomp.integrable_sq.integrableOn, hGint.integrableOn⟩
      energy := ?_ }
  intro x₀ r s k hr hrs _ _
  have hkm : MeasurableSet {x : Euc d | k < u x} := measurableSet_lt measurable_const hum
  have hLHS : (∫ x in Metric.ball x₀ r ∩ {x | k < u x}, ‖G x‖ ^ 2) =
      ∫ x in Metric.ball x₀ r ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2 :=
    integral_congr_ae (ae_restrict_of_ae hGnorm)
  have hsr0 : (0 : ℝ) < (s - r) ^ 2 := by
    have h : 0 < s - r := by linarith
    positivity
  have hone : γ * 1 ^ 2 = γ := by ring
  rw [hLHS, hone]
  rcases le_or_gt 0 k with hk | hk
  · have h := hsub x₀ r s k hr hrs hk
    have hIe : (∫ x in Metric.ball x₀ s, posTrunc k u x ^ 2) =
        ∫ x in Metric.ball x₀ s, max (u x - k) 0 ^ 2 := rfl
    rw [hIe] at h
    exact h
  · -- `k < 0`: raise the level to `0`
    have hAsub : Metric.ball x₀ r ∩ {x : Euc d | (0 : ℝ) < u x} ⊆
        Metric.ball x₀ r ∩ {x : Euc d | k < u x} :=
      Set.inter_subset_inter_right _ fun x hx => lt_trans hk hx
    have hind : (Metric.ball x₀ r ∩ {x : Euc d | k < u x}).indicator
          (fun y => ‖weakGrad u y‖ ^ 2) =ᵐ[volume]
        (Metric.ball x₀ r ∩ {x : Euc d | (0 : ℝ) < u x}).indicator
          (fun y => ‖weakGrad u y‖ ^ 2) := by
      filter_upwards [hcomp.weakGrad_eq_zero] with x hx
      by_cases hA' : x ∈ Metric.ball x₀ r ∩ {x : Euc d | (0 : ℝ) < u x}
      · rw [Set.indicator_of_mem (hAsub hA'), Set.indicator_of_mem hA']
      · rw [Set.indicator_of_notMem hA']
        by_cases hA : x ∈ Metric.ball x₀ r ∩ {x : Euc d | k < u x}
        · rw [Set.indicator_of_mem hA]
          have hnot : ¬ ((0 : ℝ) < u x) := fun hpos => hA' ⟨hA.1, hpos⟩
          have hu0 : u x = 0 := le_antisymm (not_lt.1 hnot) (hcomp.nonneg x)
          rw [hx hu0]
          simp
        · rw [Set.indicator_of_notMem hA]
    have hEq : (∫ x in Metric.ball x₀ r ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2) =
        ∫ x in Metric.ball x₀ r ∩ {x | (0 : ℝ) < u x}, ‖weakGrad u x‖ ^ 2 := by
      rw [← integral_indicator (measurableSet_ball.inter hkm),
        ← integral_indicator (measurableSet_ball.inter hposm)]
      exact integral_congr_ae hind
    have h := hsub x₀ r s 0 hr hrs le_rfl
    have hIe : (∫ x in Metric.ball x₀ s, posTrunc 0 u x ^ 2) =
        ∫ x in Metric.ball x₀ s, max (u x - 0) 0 ^ 2 := rfl
    rw [hIe] at h
    have hIle : (∫ x in Metric.ball x₀ s, max (u x - 0) 0 ^ 2) ≤
        ∫ x in Metric.ball x₀ s, max (u x - k) 0 ^ 2 := by
      refine setIntegral_mono_on (hshift x₀ s 0) (hshift x₀ s k) measurableSet_ball
        fun x _ => ?_
      exact sq_le_sq_of_nonneg (le_max_right _ _) (max_le_max (by linarith) le_rfl)
    have hmle : (volume (Metric.ball x₀ s ∩ {x | (0 : ℝ) < u x})).toReal ≤
        (volume (Metric.ball x₀ s ∩ {x | k < u x})).toReal := by
      refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_right _
        fun x hx => lt_trans hk hx))
      exact ((measure_mono Set.inter_subset_left).trans_lt
        (measure_ball_lt_top (x := x₀) (r := s))).ne
    have hq0 : (0 : ℝ) ≤ γ / (s - r) ^ 2 := div_nonneg hγ0 hsr0.le
    have hq1 := mul_le_mul_of_nonneg_left hIle hq0
    have hq2 := mul_le_mul_of_nonneg_left hmle hγ0
    rw [hEq]
    linarith

/-! ### The De Giorgi class -/

/-- **The minimizer of the regularized energy lies in the De Giorgi class `DG(K, γ, χ)`**
(`REGULARIZED_ROUTE.md`, Revision 2 (ii); Giaquinta–Giusti, *On the regularity of the minima of
variational integrals*, Acta Math. 148 (1982), Theorem 4.1; Giusti, *Direct Methods in the
Calculus of Variations*, Ch. 7).

The two level-set energy inequalities are `exists_energy_ineq` (sub side, valid at every
nonnegative level and on every ball of `ℝ^d`) and `exists_energy_ineq_super` (super side, on
balls contained in `K`); both are proved in
`Komlos/Literature/Regularized/PositivityEnergy.lean` from minimality, the two-sided quadratic
growth of the density and the hole-filling iteration.  Only the two remaining sign cases are
done here:

* **sub side, `k < 0`.**  Then `{u > k}` is everything, but `∇u = 0` a.e. on `{u = 0}`, so the
  left-hand side is unchanged when the level is raised to `0`; and the right-hand side only
  grows, since `(u)_+ ≤ (u-k)_+` and `{u>0} ⊆ {u>k}`.
* **super side, `k ≥ 0`.**  Then `{-u > k} ⊆ {u < 0} = ∅` and the inequality is trivial. -/
theorem isDG_of_regMinimizer (_hd : 0 < d) (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) (hcomp : IsRegComp K u)
    {G : Euc d → Euc d} (hG : HasWeakGradient u G) (hum : Measurable u) (hGm : Measurable G)
    (hGg : G =ᵐ[volume] weakGrad u) {R₀ : ℝ} (_hR₀ : 0 < R₀) :
    ∃ γ χ : ℝ, 0 ≤ γ ∧ 0 ≤ χ ∧ IsDG γ χ R₀ K u G := by
  classical
  obtain ⟨M, hM⟩ := hcomp.exists_le
  obtain ⟨γ₁, hγ₁0, hsub⟩ := exists_energy_ineq hκ hΨ hK hu hcomp hum
  obtain ⟨γ₂, hγ₂0, hsup⟩ := exists_energy_ineq_super hκ hΨ hK hu hcomp hum
  have hγ0 : (0 : ℝ) ≤ max γ₁ γ₂ := le_max_of_le_left hγ₁0
  -- generic facts
  have hGnorm : (fun x : Euc d => ‖G x‖ ^ 2) =ᵐ[volume] fun x => ‖weakGrad u x‖ ^ 2 := by
    filter_upwards [hGg] with x hx; rw [hx]
  have hGint : Integrable (fun x : Euc d => ‖G x‖ ^ 2) volume :=
    hcomp.integrable_normSq_grad.congr hGnorm.symm
  have hintOn : ∀ (x₀ : Euc d) (s : ℝ), Metric.closedBall x₀ s ⊆ K →
      IntegrableOn (fun x => u x ^ 2) (Metric.closedBall x₀ s) volume ∧
        IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ s) volume :=
    fun x₀ s _ => ⟨hcomp.integrable_sq.integrableOn, hGint.integrableOn⟩
  have hposm : MeasurableSet {x : Euc d | (0 : ℝ) < u x} :=
    measurableSet_lt measurable_const hum
  -- integrability of the shifted truncations on balls
  have hshift : ∀ (x₀ : Euc d) (s k : ℝ),
      IntegrableOn (fun x => max (u x - k) 0 ^ 2) (Metric.ball x₀ s) volume := by
    intro x₀ s k
    have hc : Continuous fun t : ℝ => max (t - k) 0 :=
      (continuous_id.sub continuous_const).max continuous_const
    refine Integrable.mono'
      (integrableOn_const (μ := volume) (C := (max (M - k) 0 + |k|) ^ 2)
        (measure_ball_lt_top (x := x₀) (r := s)).ne)
      ((hc.comp_aestronglyMeasurable hcomp.aestronglyMeasurable).pow 2).restrict ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : max (u x - k) 0 ≤ max (M - k) 0 + |k| := by
      have h2 : u x - k ≤ M - k := by linarith [hM x]
      have h3 : (0 : ℝ) ≤ |k| := abs_nonneg k
      have h4 : max (u x - k) 0 ≤ max (M - k) 0 := max_le_max h2 le_rfl
      linarith
    exact sq_le_sq_of_nonneg (le_max_right _ _) h1
  -- the sub side
  have hsubE : ∀ (x₀ : Euc d) (r s k : ℝ), 0 < r → r < s → s ≤ R₀ →
      Metric.closedBall x₀ s ⊆ K →
      (∫ x in Metric.ball x₀ r ∩ {x | k < u x}, ‖G x‖ ^ 2) ≤
        max γ₁ γ₂ / (s - r) ^ 2 * (∫ x in Metric.ball x₀ s, max (u x - k) 0 ^ 2) +
          max γ₁ γ₂ * 1 ^ 2 * (volume (Metric.ball x₀ s ∩ {x | k < u x})).toReal := by
    intro x₀ r s k hr hrs hsR hball
    have hkm : MeasurableSet {x : Euc d | k < u x} := measurableSet_lt measurable_const hum
    have hLHS : (∫ x in Metric.ball x₀ r ∩ {x | k < u x}, ‖G x‖ ^ 2) =
        ∫ x in Metric.ball x₀ r ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2 :=
      integral_congr_ae (ae_restrict_of_ae hGnorm)
    have hsr0 : (0 : ℝ) < (s - r) ^ 2 := by
      have h : 0 < s - r := by linarith
      positivity
    rw [hLHS]
    rcases le_or_gt 0 k with hk | hk
    · have h := hsub x₀ r s k hr hrs hk
      have hIe : (∫ x in Metric.ball x₀ s, posTrunc k u x ^ 2) =
          ∫ x in Metric.ball x₀ s, max (u x - k) 0 ^ 2 := rfl
      rw [hIe] at h
      have hI0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ s, max (u x - k) 0 ^ 2 :=
        integral_nonneg fun x => sq_nonneg _
      have hm0 : (0 : ℝ) ≤ (volume (Metric.ball x₀ s ∩ {x | k < u x})).toReal :=
        ENNReal.toReal_nonneg
      have hq1 : γ₁ / (s - r) ^ 2 ≤ max γ₁ γ₂ / (s - r) ^ 2 :=
        div_le_div_of_nonneg_right (le_max_left _ _) hsr0.le
      have hq2 := mul_le_mul_of_nonneg_right hq1 hI0
      have hq3 := mul_le_mul_of_nonneg_right (le_max_left γ₁ γ₂) hm0
      have hone : max γ₁ γ₂ * 1 ^ 2 = max γ₁ γ₂ := by ring
      rw [hone]
      linarith
    · -- `k < 0`: raise the level to `0`
      have hAsub : Metric.ball x₀ r ∩ {x : Euc d | (0 : ℝ) < u x} ⊆
          Metric.ball x₀ r ∩ {x : Euc d | k < u x} :=
        Set.inter_subset_inter_right _ fun x hx => lt_trans hk hx
      have hind : (Metric.ball x₀ r ∩ {x : Euc d | k < u x}).indicator
            (fun y => ‖weakGrad u y‖ ^ 2) =ᵐ[volume]
          (Metric.ball x₀ r ∩ {x : Euc d | (0 : ℝ) < u x}).indicator
            (fun y => ‖weakGrad u y‖ ^ 2) := by
        filter_upwards [hcomp.weakGrad_eq_zero] with x hx
        by_cases hA' : x ∈ Metric.ball x₀ r ∩ {x : Euc d | (0 : ℝ) < u x}
        · rw [Set.indicator_of_mem (hAsub hA'), Set.indicator_of_mem hA']
        · rw [Set.indicator_of_notMem hA']
          by_cases hA : x ∈ Metric.ball x₀ r ∩ {x : Euc d | k < u x}
          · rw [Set.indicator_of_mem hA]
            have hnot : ¬ ((0 : ℝ) < u x) := fun hpos => hA' ⟨hA.1, hpos⟩
            have hu0 : u x = 0 := le_antisymm (not_lt.1 hnot) (hcomp.nonneg x)
            rw [hx hu0]
            simp
          · rw [Set.indicator_of_notMem hA]
      have hEq : (∫ x in Metric.ball x₀ r ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2) =
          ∫ x in Metric.ball x₀ r ∩ {x | (0 : ℝ) < u x}, ‖weakGrad u x‖ ^ 2 := by
        rw [← integral_indicator (measurableSet_ball.inter hkm),
          ← integral_indicator (measurableSet_ball.inter hposm)]
        exact integral_congr_ae hind
      have h := hsub x₀ r s 0 hr hrs le_rfl
      have hIe : (∫ x in Metric.ball x₀ s, posTrunc 0 u x ^ 2) =
          ∫ x in Metric.ball x₀ s, max (u x - 0) 0 ^ 2 := rfl
      rw [hIe] at h
      -- the right-hand side only grows when the level drops to `k`
      have hIle : (∫ x in Metric.ball x₀ s, max (u x - 0) 0 ^ 2) ≤
          ∫ x in Metric.ball x₀ s, max (u x - k) 0 ^ 2 := by
        refine setIntegral_mono_on (hshift x₀ s 0) (hshift x₀ s k) measurableSet_ball
          fun x _ => ?_
        refine sq_le_sq_of_nonneg (le_max_right _ _) (max_le_max (by linarith) le_rfl)
      have hmle : (volume (Metric.ball x₀ s ∩ {x | (0 : ℝ) < u x})).toReal ≤
          (volume (Metric.ball x₀ s ∩ {x | k < u x})).toReal := by
        refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_right _
          fun x hx => lt_trans hk hx))
        exact ((measure_mono Set.inter_subset_left).trans_lt
          (measure_ball_lt_top (x := x₀) (r := s))).ne
      have hI0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ s, max (u x - 0) 0 ^ 2 :=
        integral_nonneg fun x => sq_nonneg _
      have hm0 : (0 : ℝ) ≤ (volume (Metric.ball x₀ s ∩ {x | (0 : ℝ) < u x})).toReal :=
        ENNReal.toReal_nonneg
      have hq0 : (0 : ℝ) ≤ max γ₁ γ₂ / (s - r) ^ 2 := div_nonneg hγ0 hsr0.le
      have hq1 : γ₁ / (s - r) ^ 2 ≤ max γ₁ γ₂ / (s - r) ^ 2 :=
        div_le_div_of_nonneg_right (le_max_left _ _) hsr0.le
      have hq2 := mul_le_mul_of_nonneg_right hq1 hI0
      have hq3 := mul_le_mul_of_nonneg_left hIle hq0
      have hq4 := mul_le_mul_of_nonneg_right (le_max_left γ₁ γ₂) hm0
      have hq5 := mul_le_mul_of_nonneg_left hmle hγ0
      have hone : max γ₁ γ₂ * 1 ^ 2 = max γ₁ γ₂ := by ring
      rw [hEq, hone]
      linarith
  -- the super side
  have hGneg : HasWeakGradient (fun x => -u x) (fun x => -G x) := by
    have h := hG.smul (-1 : ℝ)
    refine (h.congr_left (Eventually.of_forall fun x => ?_)).congr_right
      (Eventually.of_forall fun x => ?_) <;> simp
  have hsupE : ∀ (x₀ : Euc d) (r s k : ℝ), 0 < r → r < s → s ≤ R₀ →
      Metric.closedBall x₀ s ⊆ K →
      (∫ x in Metric.ball x₀ r ∩ {x | k < -u x}, ‖-G x‖ ^ 2) ≤
        max γ₁ γ₂ / (s - r) ^ 2 * (∫ x in Metric.ball x₀ s, max (-u x - k) 0 ^ 2) +
          max γ₁ γ₂ * 1 ^ 2 * (volume (Metric.ball x₀ s ∩ {x | k < -u x})).toReal := by
    intro x₀ r s k hr hrs hsR hball
    have hsr0 : (0 : ℝ) < (s - r) ^ 2 := by
      have h : 0 < s - r := by linarith
      positivity
    have hset : {x : Euc d | k < -u x} = {x : Euc d | u x < -k} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hnormeq : (∫ x in Metric.ball x₀ r ∩ {x | k < -u x}, ‖-G x‖ ^ 2) =
        ∫ x in Metric.ball x₀ r ∩ {x | u x < -k}, ‖weakGrad u x‖ ^ 2 := by
      rw [hset]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hGnorm] with x hx
      rw [norm_neg, hx]
    have hmaxeq : (fun x : Euc d => max (-u x - k) 0 ^ 2) =
        fun x => negTrunc (-k) u x ^ 2 := by
      funext x
      rw [negTrunc]
      congr 2
      ring
    have hI0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ s, max (-u x - k) 0 ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have hm0 : (0 : ℝ) ≤ (volume (Metric.ball x₀ s ∩ {x | k < -u x})).toReal :=
      ENNReal.toReal_nonneg
    have hone : max γ₁ γ₂ * 1 ^ 2 = max γ₁ γ₂ := by ring
    rcases le_or_gt (-k) 0 with hl | hl
    · -- the level set is empty
      have hempty : Metric.ball x₀ r ∩ {x : Euc d | u x < -k} = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro _ hx
        linarith [hcomp.nonneg x]
      rw [hnormeq, hempty]
      simp only [Measure.restrict_empty, integral_zero_measure]
      rw [hone]
      have hq0 : (0 : ℝ) ≤ max γ₁ γ₂ / (s - r) ^ 2 := div_nonneg hγ0 hsr0.le
      have := mul_nonneg hq0 hI0
      have := mul_nonneg hγ0 hm0
      linarith
    · have h := hsup x₀ r s (-k) hr hrs hl.le hball
      rw [hnormeq, hone, hset, hmaxeq]
      have hq1 : γ₁ / (s - r) ^ 2 ≤ max γ₁ γ₂ / (s - r) ^ 2 :=
        div_le_div_of_nonneg_right (le_max_left _ _) hsr0.le
      have hq2 : γ₂ / (s - r) ^ 2 ≤ max γ₁ γ₂ / (s - r) ^ 2 :=
        div_le_div_of_nonneg_right (le_max_right _ _) hsr0.le
      have hI0' : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ s, negTrunc (-k) u x ^ 2 :=
        integral_nonneg fun x => sq_nonneg _
      have hm0' : (0 : ℝ) ≤ (volume (Metric.ball x₀ s ∩ {x : Euc d | u x < -k})).toReal :=
        ENNReal.toReal_nonneg
      have hq3 := mul_le_mul_of_nonneg_right hq2 hI0'
      have hq4 := mul_le_mul_of_nonneg_right (le_max_right γ₁ γ₂) hm0'
      linarith
  refine ⟨max γ₁ γ₂, 1, hγ0, zero_le_one, ?_, ?_⟩
  · exact
      { hasWeakGradient := hG
        measurable := hum
        measurable_grad := hGm
        integrableOn := hintOn
        energy := hsubE }
  · exact
      { hasWeakGradient := hGneg
        measurable := hum.neg
        measurable_grad := hGm.neg
        integrableOn := fun x₀ s hs => by
          obtain ⟨h1, h2⟩ := hintOn x₀ s hs
          exact ⟨h1.congr_fun (fun x _ => by ring) measurableSet_closedBall,
            h2.congr_fun (fun x _ => by rw [norm_neg]) measurableSet_closedBall⟩
        energy := hsupE }

/-! ### Interior continuity -/

/-- **Interior continuity of the minimizer** (`REGULARIZED_ROUTE.md`, Revision 2 (ii)): the
minimizer has a representative that is continuous on `K`, Hölder continuous on every compact
subset of `K`, pointwise bounded between `0` and the essential bound, and that is *exactly*
the minimizer's measurable representative `v` off a null set.

The three data returned are the continuous interior representative `φ`, the measurable
competitor-class representative `v` (needed later: the positivity argument and the boundary
argument both run on `v`), and the bound `M`. -/
theorem IsRegMinimizer.exists_interior_continuous_rep (hd : 0 < d) (hκ : 0 < κ)
    (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) :
    ∃ (φ v : Euc d → ℝ) (M : ℝ),
      ContinuousOn φ K ∧ φ =ᵐ[volume.restrict K] v ∧ v =ᵐ[volume] u ∧
        IsRegMinimizer 2 κ Ψ K v ∧ IsRegComp K v ∧ Measurable v ∧
        0 ≤ M ∧ (∀ x, v x ≤ M) ∧ (∀ x, 0 ≤ v x) ∧ (∀ x, x ∉ K → v x = 0) ∧
        ∀ T : Set (Euc d), IsCompact T → T ⊆ K →
          ∃ Cc r : NNReal, 0 < r ∧ HolderOnWith Cc r φ T := by
  obtain ⟨v, G, M, hvu, hvmin, hvcomp, hvm, hGm, hG, hGg, hM0, hvM, hv0, hvK⟩ :=
    hu.exists_measurable_regComp hκ hΨ.toIsRegProfile hK
  obtain ⟨γ, χ, hγ, hχ, hdg⟩ :=
    isDG_of_regMinimizer hd hκ hΨ hK hvmin hvcomp hG hvm hGm hGg (R₀ := 1) one_pos
  obtain ⟨φ, hφv, hφc, hφh⟩ :=
    IsDG.exists_holder_representative (z := v) (G := G) hd hγ hχ one_pos hK.isOpen hdg
      (S := M) (fun x => abs_le.2 ⟨by linarith [hv0 x], hvM x⟩)
  exact ⟨φ, v, M, hφc, hφv, hvu, hvmin, hvcomp, hvm, hM0, hvM, hv0, hvK, hφh⟩

end Komlos.Literature.Regularized
