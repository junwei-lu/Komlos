import Komlos.Literature.Regularized.DeGiorgiOscShrink

/-!
# Oscillation decay and Hölder continuity in the De Giorgi class

The oscillation half of lane `DGN` of `REGULARIZED_ROUTE.md` (Revision 2).  This file proves
primed versions — with statements identical to the frozen ones — of the three remaining
estimates of `Komlos/Literature/Regularized/DeGiorgiClass.lean`:

* `exists_dg_osc_decay`,
* `exists_dg_holder_osc`,
* `IsDG.exists_holder_representative`.

It uses `exists_dg_sup_bound` (De Giorgi's *first* lemma, proved in `DeGiorgiClass.lean`) and the
measure-shrinking lemma `exists_dg_measure_shrink` of
`Komlos/Literature/Regularized/DeGiorgiOscShrink.lean`, and it does **not** depend on any of the
three statements it proves.

## The argument

`exists_dg_osc_half` is De Giorgi's one-sided oscillation improvement: if `z ∈ DG⁺` is below `M`
on `B_{3R}` and below the midpoint `M - om/2` on at least half of `B_{2R}`, then
`z ≤ M - c₁ om` on `B_R`.  Indeed, the measure-shrinking lemma makes `|B_{2R} ∩ {z > k_s}|` a
small fraction of `|B_{2R}|` for a level `k_s` still at distance `2^{-s-1} om` below `M`, and
`exists_dg_sup_bound` at that level converts the smallness of the measure into the pointwise
bound.  The error `χ R` is harmless: the whole statement is trivial unless `χ R ≤ c₁ om`, and
`c₁` is fixed only after `s`.

`exists_dg_osc_decay` is De Giorgi's alternative: one of `z` and `-z` (both in `DG⁺`, since
`z ∈ DG`) is below its midpoint on at least half of `B_{2R}`.

`exists_dg_holder_osc` iterates the decay on the radii `R 4^{-n}`, and
`IsDG.exists_holder_representative` feeds the resulting oscillation bounds to the project's
abstract `Komlos.Literature.exists_holder_representative`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The average of a squared truncation -/

/-- If `z ≤ M` a.e. on a ball, the average of `((z - k)_+)²` over the ball is at most
`(M - k)²` times the fraction of the ball occupied by `{z > k}`. -/
theorem setAverage_max_sq_le {z : Euc d → ℝ} (hzm : Measurable z) {x₀ : Euc d} {r : ℝ}
    (hr : 0 < r) {M ks : ℝ} (hks : ks ≤ M)
    (hMbd : ∀ᵐ x, x ∈ Metric.ball x₀ r → z x ≤ M) :
    ⨍ y in Metric.ball x₀ r, max (z y - ks) 0 ^ 2 ≤
      (M - ks) ^ 2 * ((volume (Metric.ball x₀ r ∩ {x | ks < z x})).toReal /
        (volume (Metric.ball x₀ r)).toReal) := by
  obtain ⟨cc, hccdef⟩ : ∃ c : ℝ, c = (M - ks) ^ 2 := ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by rw [hccdef]; positivity
  have hV0 : 0 < (volume (Metric.ball x₀ r)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hr).ne' measure_ball_lt_top.ne
  have hsetm : MeasurableSet {x : Euc d | ks < z x} := measurableSet_lt measurable_const hzm
  have hind : Integrable (fun y => if ks < z y then cc else 0)
      (volume.restrict (Metric.ball x₀ r)) := by
    refine Integrable.mono' (integrableOn_const (C := cc) measure_ball_lt_top.ne)
      ((measurable_const.ite hsetm measurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : ks < z y
    · rw [if_pos h, abs_of_nonneg hcc0]
    · rw [if_neg h, abs_zero]
      exact hcc0
  have hbd : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ r)),
      max (z y - ks) 0 ^ 2 ≤ if ks < z y then cc else 0 := by
    filter_upwards [ae_restrict_of_ae hMbd, ae_restrict_mem measurableSet_ball] with y hy hyb
    have hzM : z y ≤ M := hy hyb
    by_cases h : ks < z y
    · rw [if_pos h, hccdef]
      have h1 : max (z y - ks) 0 ≤ M - ks := max_le (by linarith) (by linarith)
      nlinarith [le_max_right (z y - ks) 0]
    · rw [if_neg h, max_eq_right (by linarith [not_lt.1 h])]
      norm_num
  have hle := integral_mono_of_nonneg
    (Eventually.of_forall fun y => sq_nonneg (max (z y - ks) 0)) hind hbd
  have heq : ∫ y in Metric.ball x₀ r, (if ks < z y then cc else 0) =
      cc * (volume (Metric.ball x₀ r ∩ {x | ks < z x})).toReal := by
    have h1 : (fun y => if ks < z y then cc else 0) =
        {x : Euc d | ks < z x}.indicator (fun _ => cc) := by
      funext y
      by_cases h : ks < z y
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ {x : Euc d | ks < z x} from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ {x : Euc d | ks < z x} from h)]
    rw [h1, integral_indicator hsetm, setIntegral_const, Measure.real,
      Measure.restrict_apply hsetm, smul_eq_mul, Set.inter_comm, mul_comm]
  rw [heq, hccdef] at hle
  rw [setAverage_eq, smul_eq_mul, Measure.real]
  rw [mul_div_assoc']
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-! ### De Giorgi's one-sided oscillation improvement -/

/-- **De Giorgi's one-sided oscillation improvement** for the class `DG⁺`: there is
`c₁ ∈ (0, 1]`, depending only on `d` and `γ`, such that a function of `DG⁺(Ω, γ, χ)` which is
at most `M` on `closedBall x₀ (3R)` and at most `M - om/2` on at least half of `ball x₀ (2R)`
satisfies `z ≤ M - c₁ om` a.e. on `ball x₀ R`, provided `χ R ≤ c₁ om`.

Proof: `exists_dg_measure_shrink` on `ball x₀ (2R)` makes the measure of `{z > k_s}` an
arbitrarily small fraction of `|ball x₀ (2R)|` at the level `k_s = M - 2^{-s-1} om`, and
`exists_dg_sup_bound` at that level and radius `2R` converts this into
`z ≤ k_s + (M - k_s)/2 + C χ (2R)` a.e. on `ball x₀ R`. -/
theorem exists_dg_osc_half (hd : 0 < d) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧
      ∀ (χ R₀ : ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
        0 ≤ χ → IsDGSub γ χ R₀ Ω z G →
      ∀ (x₀ : Euc d) (R : ℝ), 0 < R → 3 * R ≤ R₀ → Metric.closedBall x₀ (3 * R) ⊆ Ω →
      ∀ M om : ℝ, 0 < om → χ * R ≤ c₁ * om →
      (∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → z x ≤ M) →
      volume (Metric.ball x₀ (2 * R)) ≤
        2 * volume (Metric.ball x₀ (2 * R) ∩ {x | z x ≤ M - om / 2}) →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), z x ≤ M - c₁ * om := by
  obtain ⟨C, hC0, hsup⟩ := exists_dg_sup_bound hd hγ
  obtain ⟨Cst, hCst0, hshrink⟩ := exists_dg_measure_shrink hγ hd
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = 1 / (4 * C ^ 2) := ⟨_, rfl⟩
  have hν0 : 0 < ν := by rw [hνdef]; positivity
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = ⌈Cst / ν ^ 4⌉₊ + 1 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; omega
  have hsCst : Cst ≤ ν ^ 4 * (s : ℝ) := by
    have h1 : Cst / ν ^ 4 ≤ (⌈Cst / ν ^ 4⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Cst / ν ^ 4⌉₊ : ℕ) : ℝ) ≤ (s : ℝ) := by
      rw [hsdef]
      push_cast
      linarith
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith [pow_pos hν0 4]
  obtain ⟨c₁, hc₁def⟩ : ∃ c : ℝ, c = min 1 ((1 / 2 : ℝ) ^ (s + 3) / (2 * C + 1)) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁def]; exact lt_min one_pos (by positivity)
  have hc₁small : c₁ ≤ (1 / 2 : ℝ) ^ (s + 3) / (2 * C + 1) := by
    rw [hc₁def]; exact min_le_right _ _
  have hpows : (0 : ℝ) < (1 / 2 : ℝ) ^ s := by positivity
  have h10 : (1 / 2 : ℝ) ^ (s + 3) = (1 / 2 : ℝ) ^ s / 8 := by rw [pow_add]; ring
  have hc₁pow : c₁ ≤ (1 / 2 : ℝ) ^ s / 8 := by
    refine hc₁small.trans ?_
    rw [h10, div_le_iff₀ (by positivity)]
    nlinarith
  have hCc₁ : 2 * C * c₁ ≤ (1 / 2 : ℝ) ^ s / 8 := by
    have h1 : 2 * C * c₁ ≤ 2 * C * ((1 / 2 : ℝ) ^ (s + 3) / (2 * C + 1)) :=
      mul_le_mul_of_nonneg_left hc₁small (by positivity)
    have h2 : 2 * C * ((1 / 2 : ℝ) ^ (s + 3) / (2 * C + 1)) ≤ (1 / 2 : ℝ) ^ (s + 3) := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 1 / 2) (s + 3)]
    rw [h10] at h1 h2
    linarith
  refine ⟨c₁, hc₁0, by rw [hc₁def]; exact min_le_left _ _, ?_⟩
  intro χ R₀ Ω z G hχ hz x₀ R hR hRR hball M om hom hχR hMbd hhalf
  have h32 : 3 / 2 * (2 * R) = 3 * R := by ring
  have hρ : (0 : ℝ) < 2 * R := by linarith
  have hballρ : Metric.closedBall x₀ (2 * R) ⊆ Ω :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (1 / 2 : ℝ) ^ s * om := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; positivity
  obtain ⟨ks, hksdef⟩ : ∃ k : ℝ, k = M - t / 2 := ⟨_, rfl⟩
  have hksM : ks ≤ M := by rw [hksdef]; linarith
  have hχρ : χ * (2 * R) ≤ (1 / 2 : ℝ) ^ s * om := by
    have h1 : χ * R ≤ c₁ * om := hχR
    have h2 : c₁ * om ≤ (1 / 2 : ℝ) ^ s / 8 * om := mul_le_mul_of_nonneg_right hc₁pow hom.le
    nlinarith
  have hMbdρ : ∀ᵐ x, x ∈ Metric.closedBall x₀ (3 / 2 * (2 * R)) → z x ≤ M := by
    rw [h32]; exact hMbd
  have hshr := hshrink χ R₀ Ω z G hχ hz x₀ (2 * R) hρ (by rw [h32]; exact hRR)
    (by rw [h32]; exact hball) M om hom hMbdρ hhalf s hχρ
  have hlev : M - (1 / 2 : ℝ) ^ s * om / 2 = ks := by rw [hksdef, htdef]
  rw [hlev] at hshr
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (Metric.ball x₀ (2 * R))).toReal := ⟨_, rfl⟩
  have hV0 : 0 < V := by
    rw [hVdef]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hρ).ne' measure_ball_lt_top.ne
  obtain ⟨as, hasdef⟩ : ∃ a : ℝ,
      a = (volume (Metric.ball x₀ (2 * R) ∩ {x | ks < z x})).toReal := ⟨_, rfl⟩
  have has0 : 0 ≤ as := by rw [hasdef]; exact ENNReal.toReal_nonneg
  have hasν : as ≤ ν * V := by
    have h1 : as ^ 4 ≤ (ν * V) ^ 4 := by
      have h2 : (s : ℝ) * as ^ 4 ≤ Cst * V ^ 4 := by rw [hasdef, hVdef]; exact hshr
      have h3 : Cst * V ^ 4 ≤ ν ^ 4 * (s : ℝ) * V ^ 4 :=
        mul_le_mul_of_nonneg_right hsCst (by positivity)
      have h4 : (s : ℝ) * as ^ 4 ≤ (s : ℝ) * ((ν * V) ^ 4) := by
        have h5 : ν ^ 4 * (s : ℝ) * V ^ 4 = (s : ℝ) * ((ν * V) ^ 4) := by ring
        linarith
      have hs0' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
      exact le_of_mul_le_mul_left h4 hs0'
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
  have hMbdball : ∀ᵐ x, x ∈ Metric.ball x₀ (2 * R) → z x ≤ M := by
    filter_upwards [hMbd] with x hx hxb
    exact hx (Metric.closedBall_subset_closedBall (by linarith)
      (Metric.ball_subset_closedBall hxb))
  have havg : ⨍ y in Metric.ball x₀ (2 * R), max (z y - ks) 0 ^ 2 ≤ (M - ks) ^ 2 * ν := by
    refine (setAverage_max_sq_le hz.measurable hρ hksM hMbdball).trans ?_
    rw [← hasdef, ← hVdef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ hV0]
    calc as ≤ ν * V := hasν
      _ = ν * V := rfl
  have hsb := hsup χ R₀ Ω z G hχ hz x₀ (2 * R) hρ (by linarith) hballρ ks
  have hhalfR : 2 * R / 2 = R := by ring
  rw [hhalfR] at hsb
  have hMks : M - ks = t / 2 := by rw [hksdef]; ring
  have hsqrt : Real.sqrt (⨍ y in Metric.ball x₀ (2 * R), max (z y - ks) 0 ^ 2) ≤
      (M - ks) * (1 / (2 * C)) := by
    refine (Real.sqrt_le_sqrt havg).trans ?_
    have h2 : (M - ks) ^ 2 * ν = ((M - ks) * (1 / (2 * C))) ^ 2 := by
      rw [hνdef]
      field_simp
      try ring
    rw [h2, Real.sqrt_sq (by rw [hMks]; positivity)]
  -- assemble
  have hstep1 : C * (χ * (2 * R)) ≤ 2 * C * (c₁ * om) := by
    have h := mul_le_mul_of_nonneg_left hχR (by positivity : (0 : ℝ) ≤ 2 * C)
    linarith
  have hstep2 : 2 * C * (c₁ * om) ≤ t / 8 := by
    have h := mul_le_mul_of_nonneg_right hCc₁ hom.le
    rw [htdef]
    nlinarith
  have hstep3 : c₁ * om ≤ t / 8 := by
    have h := mul_le_mul_of_nonneg_right hc₁pow hom.le
    rw [htdef]
    linarith
  filter_upwards [hsb] with x hx
  have h1 : z x ≤ ks + C * ((M - ks) * (1 / (2 * C)) + χ * (2 * R)) := by
    refine hx.trans ?_
    have h := mul_le_mul_of_nonneg_left (add_le_add_right hsqrt (χ * (2 * R))) hC0.le
    linarith
  have h2 : C * ((M - ks) * (1 / (2 * C)) + χ * (2 * R)) =
      (M - ks) / 2 + C * (χ * (2 * R)) := by
    field_simp
    try ring
  rw [h2] at h1
  rw [hksdef] at h1
  linarith

/-! ### De Giorgi's alternative: oscillation decay -/

/-- **De Giorgi's oscillation decay in the class `DG`** (Ladyzhenskaya–Ural'tseva, Ch. II,
Theorem 6.1 and §7; Giaquinta–Giusti, Theorem 5.1).  This is the frozen
`Komlos.Literature.Regularized.exists_dg_osc_decay`.

Proof: De Giorgi's alternative.  One of `z` and `-z` is below its midpoint on at least half of
`ball x₀ (2R)`, and `exists_dg_osc_half` applies to it (both lie in `DG⁺`).  If
`c₁ om ≤ χ R` the statement is trivial. -/
theorem exists_dg_osc_decay (hd : 0 < d) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧
      ∀ (χ R₀ : ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
        0 ≤ χ → IsDG γ χ R₀ Ω z G →
      ∀ (x₀ : Euc d) (R : ℝ), 0 < R → 3 * R ≤ R₀ → Metric.closedBall x₀ (3 * R) ⊆ Ω →
      ∀ m om : ℝ, 0 ≤ om →
      (∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → z x ∈ Icc m (m + om)) →
      ∃ m' : ℝ, ∀ᵐ x, x ∈ Metric.ball x₀ R →
        z x ∈ Icc m' (m' + ((1 - c₁) * om + χ * R)) := by
  obtain ⟨c₁, hc₁0, hc₁1, half⟩ := exists_dg_osc_half hd hγ
  refine ⟨c₁, hc₁0, hc₁1, ?_⟩
  intro χ R₀ Ω z G hχ hz x₀ R hR hRR hball m om hom hosc
  have hR3 : Metric.ball x₀ R ⊆ Metric.closedBall x₀ (3 * R) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hχR0 : 0 ≤ χ * R := mul_nonneg hχ hR.le
  by_cases htriv : c₁ * om ≤ χ * R
  · refine ⟨m, ?_⟩
    filter_upwards [hosc] with x hx hxb
    obtain ⟨h1, h2⟩ := hx (hR3 hxb)
    exact ⟨h1, by nlinarith⟩
  have hχc : χ * R < c₁ * om := not_le.1 htriv
  have hom0 : 0 < om := by nlinarith
  have hχRle : χ * R ≤ c₁ * om := hχc.le
  -- the alternative on `ball x₀ (2R)`
  have hsplit : volume (Metric.ball x₀ (2 * R)) ≤
      volume (Metric.ball x₀ (2 * R) ∩ {x | z x ≤ m + om / 2}) +
        volume (Metric.ball x₀ (2 * R) ∩ {x | m + om / 2 ≤ z x}) := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro x hx
    by_cases h : z x ≤ m + om / 2
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, le_of_lt (not_le.1 h)⟩
  have halt : volume (Metric.ball x₀ (2 * R)) ≤
        2 * volume (Metric.ball x₀ (2 * R) ∩ {x | z x ≤ m + om / 2}) ∨
      volume (Metric.ball x₀ (2 * R)) ≤
        2 * volume (Metric.ball x₀ (2 * R) ∩ {x | m + om / 2 ≤ z x}) := by
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    have hsum : 2 * volume (Metric.ball x₀ (2 * R)) ≤
        2 * volume (Metric.ball x₀ (2 * R) ∩ {x | z x ≤ m + om / 2}) +
          2 * volume (Metric.ball x₀ (2 * R) ∩ {x | m + om / 2 ≤ z x}) := by
      rw [← mul_add]
      exact mul_le_mul_right hsplit 2
    have hlt := ENNReal.add_lt_add hcon.1 hcon.2
    have he : volume (Metric.ball x₀ (2 * R)) + volume (Metric.ball x₀ (2 * R)) =
        2 * volume (Metric.ball x₀ (2 * R)) := by ring
    rw [he] at hlt
    exact absurd (hsum.trans_lt hlt) (lt_irrefl _)
  have hMbd : ∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → z x ≤ m + om :=
    hosc.mono fun x hx hxb => (hx hxb).2
  have hmbd : ∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → m ≤ z x :=
    hosc.mono fun x hx hxb => (hx hxb).1
  rcases halt with hcase | hcase
  · -- `z` is below its midpoint on half of the ball
    have hseteq : {x : Euc d | z x ≤ m + om - om / 2} = {x : Euc d | z x ≤ m + om / 2} := by
      have he : m + om - om / 2 = m + om / 2 := by ring
      rw [he]
    have hhalf : volume (Metric.ball x₀ (2 * R)) ≤
        2 * volume (Metric.ball x₀ (2 * R) ∩ {x | z x ≤ m + om - om / 2}) := by
      rw [hseteq]; exact hcase
    have hup := half χ R₀ Ω z G hχ hz.sub x₀ R hR hRR hball (m + om) om hom0 hχRle hMbd hhalf
    rw [ae_restrict_iff' measurableSet_ball] at hup
    refine ⟨m, ?_⟩
    filter_upwards [hup, hmbd] with x hx1 hx2 hxb
    exact ⟨hx2 (hR3 hxb), by nlinarith [hx1 hxb]⟩
  · -- `-z` is below its midpoint on half of the ball
    have hseteq : {x : Euc d | -z x ≤ -m - om / 2} = {x : Euc d | m + om / 2 ≤ z x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hhalf : volume (Metric.ball x₀ (2 * R)) ≤
        2 * volume (Metric.ball x₀ (2 * R) ∩ {x | (fun y => -z y) x ≤ -m - om / 2}) := by
      rw [show {x : Euc d | (fun y => -z y) x ≤ -m - om / 2} =
        {x : Euc d | -z x ≤ -m - om / 2} from rfl, hseteq]
      exact hcase
    have hMbd' : ∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → (fun y => -z y) x ≤ -m :=
      hmbd.mono fun x hx hxb => by
        show -z x ≤ -m
        linarith [hx hxb]
    have hup := half χ R₀ Ω (fun y => -z y) (fun y => -G y) hχ hz.neg x₀ R hR hRR hball
      (-m) om hom0 hχRle hMbd' hhalf
    rw [ae_restrict_iff' measurableSet_ball] at hup
    refine ⟨m + c₁ * om, ?_⟩
    filter_upwards [hup, hMbd] with x hx1 hx2 hxb
    have h1 : -z x ≤ -m - c₁ * om := hx1 hxb
    exact ⟨by linarith, by nlinarith [hx2 (hR3 hxb)]⟩

/-! ### Hölder decay of the oscillation -/

/-- **Hölder decay of the oscillation in the class `DG`**.  This is the primed version of the
frozen `Komlos.Literature.Regularized.exists_dg_holder_osc`.

Proof: iterate `exists_dg_osc_decay` on the radii `R 4^{-n}`; the errors `χ R 4^{-n}` decay
geometrically, so with `γ' = max (1 - c₁) (1/4)` one gets `om_n ≤ A₀ γ'^n` with
`A₀ = om + χ R/(γ'' - γ')` and `α = log(1/γ'')/log 4`. -/
theorem exists_dg_holder_osc (hd : 0 < d) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ α : ℝ, 0 < α ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (χ R₀ : ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
        0 ≤ χ → IsDG γ χ R₀ Ω z G →
      ∀ (x₀ : Euc d) (R : ℝ), 0 < R → 3 * R ≤ R₀ → Metric.closedBall x₀ (3 * R) ⊆ Ω →
      ∀ m om : ℝ, 0 ≤ om →
      (∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → z x ∈ Icc m (m + om)) →
      ∀ r : ℝ, 0 < r → r ≤ R →
      ∃ m' : ℝ, ∀ᵐ x, x ∈ Metric.ball x₀ r →
        z x ∈ Icc m' (m' + C₀ * (r / R) ^ α * (om + χ * R)) := by
  obtain ⟨c₁, hc₁0, hc₁1, hdec⟩ := exists_dg_osc_decay hd hγ
  obtain ⟨gb, hgbdef⟩ : ∃ g : ℝ, g = max (1 - c₁) (1 / 4) := ⟨_, rfl⟩
  have hgb1 : gb < 1 := by rw [hgbdef]; exact max_lt (by linarith) (by norm_num)
  have hgb14 : (1 : ℝ) / 4 ≤ gb := by rw [hgbdef]; exact le_max_right _ _
  have hgbc : 1 - c₁ ≤ gb := by rw [hgbdef]; exact le_max_left _ _
  have hgb0 : 0 < gb := by linarith
  obtain ⟨gp, hgpdef⟩ : ∃ g : ℝ, g = (1 + gb) / 2 := ⟨_, rfl⟩
  have hgbgp : gb < gp := by rw [hgpdef]; linarith
  have hgp1 : gp < 1 := by rw [hgpdef]; linarith
  have hgp0 : 0 < gp := by linarith
  obtain ⟨α, hαdef⟩ : ∃ a : ℝ, a = Real.log gp⁻¹ / Real.log 4 := ⟨_, rfl⟩
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hα0 : 0 < α := by
    rw [hαdef]
    exact div_pos (Real.log_pos ((one_lt_inv₀ hgp0).2 hgp1)) hlog4
  have h4α : (4 : ℝ) ^ α = gp⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num), hαdef,
      show Real.log 4 * (Real.log gp⁻¹ / Real.log 4) = Real.log gp⁻¹ by field_simp,
      Real.exp_log (inv_pos.2 hgp0)]
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max 1 (1 / (gp - gb)) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKinv : 1 / (gp - gb) ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hK0 : 0 < K := by linarith
  refine ⟨α, hα0, K * 4 ^ α, by positivity, ?_⟩
  intro χ R₀ Ω z G hχ hz x₀ R hR hRR hball m om hom hosc r hr hrR
  have hχR0 : 0 ≤ χ * R := mul_nonneg hχ hR.le
  obtain ⟨A₀, hA₀def⟩ : ∃ A : ℝ, A = om + χ * R / (gp - gb) := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by
    rw [hA₀def]
    have : 0 ≤ χ * R / (gp - gb) := div_nonneg hχR0 (by linarith)
    linarith
  have hA₀om : om ≤ A₀ := by
    rw [hA₀def]
    have : 0 ≤ χ * R / (gp - gb) := div_nonneg hχR0 (by linarith)
    linarith
  have hA₀χ : χ * R ≤ (gp - gb) * A₀ := by
    rw [hA₀def, mul_add, mul_div_cancel₀ _ (by linarith : gp - gb ≠ 0)]
    nlinarith
  have hA₀K : A₀ ≤ K * (om + χ * R) := by
    rw [hA₀def]
    have hKg : 1 ≤ K * (gp - gb) := by
      rw [div_le_iff₀ (by linarith)] at hKinv
      linarith
    have h1 : χ * R / (gp - gb) ≤ K * (χ * R) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith
  -- the geometric ladder of radii
  have key : ∀ n : ℕ, ∃ mn : ℝ, ∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * (R / 4 ^ n)) →
      z x ∈ Icc mn (mn + A₀ * gp ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨m, ?_⟩
      simp only [pow_zero, mul_one, div_one]
      filter_upwards [hosc] with x hx hxb
      obtain ⟨h1, h2⟩ := hx hxb
      exact ⟨h1, by linarith⟩
    | succ n ih =>
      obtain ⟨mn, hmn⟩ := ih
      have h4n : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
      have hRn : 0 < R / 4 ^ n := div_pos hR h4n
      have hRnR : R / 4 ^ n ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
      have hballn : Metric.closedBall x₀ (3 * (R / 4 ^ n)) ⊆ Ω :=
        (Metric.closedBall_subset_closedBall (by linarith)).trans hball
      obtain ⟨m', hm'⟩ := hdec χ R₀ Ω z G hχ hz x₀ (R / 4 ^ n) hRn (by linarith) hballn
        mn (A₀ * gp ^ n) (by positivity) hmn
      refine ⟨m', ?_⟩
      filter_upwards [hm'] with x hx hxb
      have hxb' : x ∈ Metric.ball x₀ (R / 4 ^ n) := by
        rw [Metric.mem_closedBall] at hxb
        rw [Metric.mem_ball]
        have e : 3 * (R / 4 ^ (n + 1)) = 3 / 4 * (R / 4 ^ n) := by
          rw [pow_succ]
          field_simp
        rw [e] at hxb
        linarith
      obtain ⟨h1, h2⟩ := hx hxb'
      refine ⟨h1, h2.trans (add_le_add le_rfl ?_)⟩
      have hbase : χ * (R / 4 ^ n) ≤ (gp - gb) * A₀ * gp ^ n := by
        have h3 : χ * (R / 4 ^ n) ≤ χ * R * (1 / 4 : ℝ) ^ n := by
          have e : χ * (R / 4 ^ n) = χ * R * (1 / 4 : ℝ) ^ n := by
            rw [div_pow, one_pow]
            ring
          exact le_of_eq e
        have h4 : (1 / 4 : ℝ) ^ n ≤ gp ^ n :=
          pow_le_pow_left₀ (by norm_num) (by linarith) n
        have h5 : χ * R * (1 / 4 : ℝ) ^ n ≤ χ * R * gp ^ n :=
          mul_le_mul_of_nonneg_left h4 hχR0
        have h6 : χ * R * gp ^ n ≤ (gp - gb) * A₀ * gp ^ n :=
          mul_le_mul_of_nonneg_right hA₀χ (by positivity)
        linarith
      have hgpn : (0 : ℝ) ≤ gp ^ n := by positivity
      calc (1 - c₁) * (A₀ * gp ^ n) + χ * (R / 4 ^ n)
          ≤ gb * (A₀ * gp ^ n) + (gp - gb) * A₀ * gp ^ n :=
            add_le_add (mul_le_mul_of_nonneg_right hgbc (by positivity)) hbase
        _ = A₀ * gp ^ (n + 1) := by ring
  -- choose the scale
  have hRr : 1 ≤ R / r := (one_le_div hr).2 hrR
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hRr (by norm_num : (1 : ℝ) < 4)
  obtain ⟨mn, hmn⟩ := key n
  refine ⟨mn, ?_⟩
  filter_upwards [hmn] with x hx hxb
  have h4n : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
  have hrn : r ≤ R / 4 ^ n := by
    rw [le_div_iff₀ h4n]
    rw [le_div_iff₀ hr] at hn1
    linarith
  have hxb' : x ∈ Metric.closedBall x₀ (3 * (R / 4 ^ n)) := by
    rw [Metric.mem_ball] at hxb
    rw [Metric.mem_closedBall]
    linarith
  obtain ⟨h1, h2⟩ := hx hxb'
  refine ⟨h1, h2.trans (add_le_add le_rfl ?_)⟩
  have hrR0 : 0 < r / R := div_pos hr hR
  have hlow : ((4 : ℝ) ^ (n + 1))⁻¹ ≤ r / R := by
    rw [div_lt_iff₀ hr] at hn2
    rw [inv_le_iff_one_le_mul₀ (pow_pos (by norm_num) _), div_mul_eq_mul_div, le_div_iff₀ hR]
    linarith
  have hpow : gp ^ (n + 1) ≤ (r / R) ^ α := by
    calc gp ^ (n + 1) = (((4 : ℝ) ^ (n + 1))⁻¹) ^ α := by
          rw [Real.inv_rpow (pow_nonneg (by norm_num) _), ← Real.rpow_natCast_mul (by norm_num),
            mul_comm, Real.rpow_mul_natCast (by norm_num), h4α, inv_pow, inv_inv]
      _ ≤ (r / R) ^ α :=
          Real.rpow_le_rpow (inv_nonneg.2 (pow_nonneg (by norm_num) _)) hlow hα0.le
  have hstep : A₀ * gp ^ n ≤ A₀ * 4 ^ α * (r / R) ^ α := by
    calc A₀ * gp ^ n = A₀ * (gp⁻¹ * gp ^ (n + 1)) := by
          rw [pow_succ]
          field_simp
      _ ≤ A₀ * (gp⁻¹ * (r / R) ^ α) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (inv_nonneg.2 hgp0.le)) hA₀0
      _ = A₀ * 4 ^ α * (r / R) ^ α := by rw [h4α]; ring
  refine hstep.trans ?_
  have h4αpos : (0 : ℝ) < (4 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hrRα : (0 : ℝ) ≤ (r / R) ^ α := Real.rpow_nonneg hrR0.le _
  have hfinal : A₀ * 4 ^ α ≤ K * 4 ^ α * (om + χ * R) := by
    have := mul_le_mul_of_nonneg_right hA₀K h4αpos.le
    nlinarith
  calc A₀ * 4 ^ α * (r / R) ^ α ≤ K * 4 ^ α * (om + χ * R) * (r / R) ^ α :=
        mul_le_mul_of_nonneg_right hfinal hrRα
    _ = K * 4 ^ α * (r / R) ^ α * (om + χ * R) := by ring

/-! ### A locally Hölder representative -/

/-- **Interior Hölder continuity in the class `DG`** (De Giorgi–Nash).  This is the primed
version of the frozen `Komlos.Literature.Regularized.IsDG.exists_holder_representative`.

Proof: `exists_dg_holder_osc` on balls of radius at most `min 1 (R₀/3)` supplies the
oscillation hypothesis of the project's abstract
`Komlos.Literature.exists_holder_representative` for the shifted function `z + S`, whose values
lie in `[0, 2S]`; subtracting the constant `S` from the resulting representative gives one
for `z`. -/
theorem IsDG.exists_holder_representative {γ χ R₀ : ℝ} {Ω : Set (Euc d)} {z : Euc d → ℝ}
    {G : Euc d → Euc d} (hd : 0 < d) (hγ : 0 ≤ γ) (hχ : 0 ≤ χ) (hR₀ : 0 < R₀) (hΩ : IsOpen Ω)
    (hz : IsDG γ χ R₀ Ω z G) {S : ℝ} (hS : ∀ x, |z x| ≤ S) :
    ∃ φ : Euc d → ℝ, φ =ᵐ[volume.restrict Ω] z ∧ ContinuousOn φ Ω ∧
      ∀ T : Set (Euc d), IsCompact T → T ⊆ Ω → ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r φ T := by
  obtain ⟨α, hα0, C₀, hC₀0, hosc⟩ := exists_dg_holder_osc hd hγ
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have hzbd : ∀ x, z x ∈ Icc (-S) (-S + 2 * S) := fun x => by
    have h := abs_le.1 (hS x)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨ρ₀, hρ₀def⟩ : ∃ p : ℝ, p = min 1 (R₀ / 3) := ⟨_, rfl⟩
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀def]; exact lt_min one_pos (by linarith)
  have hρ₀1 : ρ₀ ≤ 1 := by rw [hρ₀def]; exact min_le_left _ _
  have hρ₀R : 3 * ρ₀ ≤ R₀ := by
    rw [hρ₀def]
    have h := min_le_right (1 : ℝ) (R₀ / 3)
    linarith
  obtain ⟨C₁, hC₁def⟩ : ∃ C : ℝ,
      C = max (C₀ * (1 / ρ₀) ^ α * (2 * S + χ)) (2 * S / ρ₀ ^ α) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁def]
    exact le_max_of_le_right (div_nonneg (by linarith) (Real.rpow_nonneg hρ₀0.le _))
  have hC₁a : C₀ * (1 / ρ₀) ^ α * (2 * S + χ) ≤ C₁ := by rw [hC₁def]; exact le_max_left _ _
  have hC₁b : 2 * S / ρ₀ ^ α ≤ C₁ := by rw [hC₁def]; exact le_max_right _ _
  have hvmeas : Measurable fun x => z x + S := hz.sub.measurable.add_const S
  have hv0 : ∀ x, (fun x => z x + S) x ∈ Icc 0 (2 * S) := fun x => by
    have h := abs_le.1 (hS x)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hoscv : ∀ (x₀ : Euc d) (R₁ : ℝ), 0 < R₁ → R₁ ≤ 1 →
      Metric.closedBall x₀ (3 * R₁) ⊆ Ω → ∀ r : ℝ, 0 < r → r ≤ R₁ →
      ∃ m : ℝ, ∀ᵐ x, x ∈ Metric.ball x₀ r →
        (fun x => z x + S) x ∈ Icc m (m + C₁ * (r / R₁) ^ α) := by
    intro x₀ R₁ hR₁ hR₁1 hballΩ r hr hrR₁
    obtain ⟨R₂, hR₂def⟩ : ∃ R : ℝ, R = min R₁ ρ₀ := ⟨_, rfl⟩
    have hR₂0 : 0 < R₂ := by rw [hR₂def]; exact lt_min hR₁ hρ₀0
    have hR₂R₁ : R₂ ≤ R₁ := by rw [hR₂def]; exact min_le_left _ _
    have hR₂ρ : R₂ ≤ ρ₀ := by rw [hR₂def]; exact min_le_right _ _
    have hR₂1 : R₂ ≤ 1 := hR₂ρ.trans hρ₀1
    have hball₂ : Metric.closedBall x₀ (3 * R₂) ⊆ Ω :=
      (Metric.closedBall_subset_closedBall (by linarith)).trans hballΩ
    have h3R₂ : 3 * R₂ ≤ R₀ := by linarith
    have hR₂lb : ρ₀ * R₁ ≤ R₂ := by
      rw [hR₂def]
      exact le_min (by nlinarith) (by nlinarith)
    have hrR₁0 : 0 < r / R₁ := div_pos hr hR₁
    by_cases hcase : r ≤ R₂
    · obtain ⟨m', hm'⟩ := hosc χ R₀ Ω z G hχ hz x₀ R₂ hR₂0 h3R₂ hball₂ (-S) (2 * S)
        (by linarith) (Eventually.of_forall fun x _ => hzbd x) r hr hcase
      refine ⟨m' + S, ?_⟩
      have hratio : r / R₂ ≤ 1 / ρ₀ * (r / R₁) := by
        rw [div_le_iff₀ hR₂0]
        have h1 : 1 / ρ₀ * (r / R₁) * (ρ₀ * R₁) = r := by field_simp
        have h2 : (0 : ℝ) ≤ 1 / ρ₀ * (r / R₁) := by positivity
        calc r = 1 / ρ₀ * (r / R₁) * (ρ₀ * R₁) := h1.symm
          _ ≤ 1 / ρ₀ * (r / R₁) * R₂ := mul_le_mul_of_nonneg_left hR₂lb h2
      have hrpow : (r / R₂) ^ α ≤ (1 / ρ₀) ^ α * (r / R₁) ^ α := by
        rw [← Real.mul_rpow (by positivity) hrR₁0.le]
        exact Real.rpow_le_rpow (by positivity) hratio hα0.le
      have hbound : C₀ * (r / R₂) ^ α * (2 * S + χ * R₂) ≤ C₁ * (r / R₁) ^ α := by
        have hχR₂ : 2 * S + χ * R₂ ≤ 2 * S + χ := by nlinarith
        have h1 : C₀ * (r / R₂) ^ α * (2 * S + χ * R₂) ≤
            C₀ * ((1 / ρ₀) ^ α * (r / R₁) ^ α) * (2 * S + χ) := by
          have hA : (0 : ℝ) ≤ C₀ * (r / R₂) ^ α := by positivity
          have hB : C₀ * (r / R₂) ^ α ≤ C₀ * ((1 / ρ₀) ^ α * (r / R₁) ^ α) :=
            mul_le_mul_of_nonneg_left hrpow hC₀0
          nlinarith [Real.rpow_nonneg hrR₁0.le α,
            Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 / ρ₀) α]
        have h2 : C₀ * ((1 / ρ₀) ^ α * (r / R₁) ^ α) * (2 * S + χ) =
            C₀ * (1 / ρ₀) ^ α * (2 * S + χ) * (r / R₁) ^ α := by ring
        have h3 : C₀ * (1 / ρ₀) ^ α * (2 * S + χ) * (r / R₁) ^ α ≤ C₁ * (r / R₁) ^ α :=
          mul_le_mul_of_nonneg_right hC₁a (Real.rpow_nonneg hrR₁0.le α)
        linarith [h1, h2.le, h3]
      filter_upwards [hm'] with x hx hxb
      obtain ⟨h1, h2⟩ := hx hxb
      exact ⟨by linarith, by linarith⟩
    · refine ⟨0, ?_⟩
      have hgt : R₂ < r := not_le.1 hcase
      have hρα : ρ₀ ^ α ≤ (r / R₁) ^ α := by
        refine Real.rpow_le_rpow hρ₀0.le ?_ hα0.le
        rw [le_div_iff₀ hR₁]
        linarith
      have h2S : 2 * S ≤ C₁ * (r / R₁) ^ α := by
        have h1 : 2 * S / ρ₀ ^ α * ρ₀ ^ α = 2 * S := by
          field_simp
        have h2 : 2 * S / ρ₀ ^ α * ρ₀ ^ α ≤ C₁ * (r / R₁) ^ α := by
          refine mul_le_mul hC₁b hρα (Real.rpow_nonneg hρ₀0.le α) hC₁0
        linarith
      refine Eventually.of_forall fun x _ => ?_
      exact ⟨(hv0 x).1, by linarith [(hv0 x).2]⟩
  obtain ⟨φ, hφv, hφc, hφH⟩ :=
    Komlos.Literature.exists_holder_representative hΩ hvmeas hv0 hα0 hC₁0 hoscv
  refine ⟨fun x => φ x - S, ?_, (hφc.sub continuousOn_const : ContinuousOn (fun x => φ x - S) Ω),
    ?_⟩
  · filter_upwards [hφv] with x hx
    show φ x - S = z x
    rw [hx]
    ring
  · intro T hT hTΩ
    obtain ⟨C, rr, hrr, hH⟩ := hφH T hT hTΩ
    refine ⟨C, rr, hrr, fun x hx y hy => ?_⟩
    have he : edist (φ x - S) (φ y - S) = edist (φ x) (φ y) := by
      rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_right]
    rw [he]
    exact hH x hx y hy

end Komlos.Literature.Regularized
