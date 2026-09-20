import Komlos.Literature.Regularized.PositivityLowerSharp
import Komlos.Literature.Regularized.PositivityLowerLog

/-!
# Lane `L2p` (`reg/pos-lower`), step 6: the local positive lower bound

The **rescaled level function**

`w_l = (l − u)₊ / l − 1 = − min(u, l) / l ∈ [−1, 0]`

is what turns the *sharp* level-dependent energy inequality of `PositivityLowerSharp.lean` into
a De Giorgi class statement with constants **independent of the level `l`**: both sides of

`∫_{B_r ∩ {u<l'}} ‖∇u‖² ≤ γ(s−r)^{-2} ∫_{B_s}(l'−u)₊² + γ l'² |B_s ∩ {u<l'}|`

are homogeneous of degree two in the level, and the level sets of `w_l` are exactly the sets
`{u < l'}` with `l' = −k l`, `k ∈ [−1, 0)`.  Hence `w_l ∈ IsDGSub γ 1 …` for every
`0 < l ≤ e^{-1/2}`.

The positivity then follows from the De Giorgi sup bound alone, with no expansion of positivity
and no chain of balls: the `δ`-uniform `L¹` bound for `(−log(v+δ))₊`
(`exists_neg_log_shift_bound`, from the entropy comparison) gives

`|B_R ∩ {v < l}| ≤ A / log(1/(2l)) → 0   (l ↓ 0)`,

so for `R` small enough that `C_{DG} · 1 · R ≤ 1/4` and then `l` small enough that
`C_{DG} √(⨍_{B_R} w_l²) ≤ 1/4`, the sup bound at the level `k = −1` gives `w_l ≤ −1/2`, that is
`v ≥ l/2` a.e. on `B_{R/2}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}
  {l : ℝ} {x : Euc d} {G : Euc d → Euc d}

/-! ### The rescaled level function -/

/-- The **rescaled level function** `w_l = (l − u)₊/l − 1 = −min(u,l)/l`. -/
noncomputable def levelScaled (l : ℝ) (u : Euc d → ℝ) : Euc d → ℝ :=
  fun x => l⁻¹ * (negTrunc l u x - l)

/-- Its weak gradient `−1_{u<l} ∇u / l`. -/
noncomputable def levelScaledGrad (l : ℝ) (u : Euc d → ℝ) (G : Euc d → Euc d) :
    Euc d → Euc d := fun x => l⁻¹ • (-(levelIndLt l u x • G x))

theorem levelScaled_mul (hl : 0 < l) : l * levelScaled l u x = negTrunc l u x - l := by
  rw [levelScaled, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul]

theorem levelScaled_nonpos (hl : 0 < l) (hu : 0 ≤ u x) : levelScaled l u x ≤ 0 := by
  have hm := levelScaled_mul (l := l) (u := u) (x := x) hl
  have hle : negTrunc l u x ≤ l := max_le (by linarith) hl.le
  nlinarith [hm, hle, hl]

theorem neg_one_le_levelScaled (hl : 0 < l) : -1 ≤ levelScaled l u x := by
  have hm := levelScaled_mul (l := l) (u := u) (x := x) hl
  have h0 : 0 ≤ negTrunc l u x := negTrunc_nonneg l u x
  nlinarith [hm, h0, hl]

theorem abs_levelScaled_le_one (hl : 0 < l) (hu : 0 ≤ u x) : |levelScaled l u x| ≤ 1 :=
  abs_le.2 ⟨neg_one_le_levelScaled hl, le_trans (levelScaled_nonpos hl hu) zero_le_one⟩

theorem levelScaled_measurable (_hl : 0 < l) (hum : Measurable u) :
    Measurable (levelScaled l u) := by
  have h1 : Measurable fun x => negTrunc l u x :=
    (measurable_const.sub hum).max measurable_const
  exact measurable_const.mul (h1.sub measurable_const)

theorem levelIndLt_measurable (hum : Measurable u) : Measurable (levelIndLt l u) :=
  Measurable.ite (measurableSet_lt hum measurable_const) measurable_const measurable_const

theorem levelScaledGrad_measurable (hum : Measurable u) (hGm : Measurable G) :
    Measurable (levelScaledGrad l u G) := by
  have h1 : Measurable fun x => -(levelIndLt l u x • G x) :=
    ((levelIndLt_measurable hum).smul hGm).neg
  show Measurable fun x => l⁻¹ • (-(levelIndLt l u x • G x))
  exact h1.const_smul l⁻¹

theorem levelScaledGrad_of_not_lt (h : ¬ u x < l) : levelScaledGrad l u G x = 0 := by
  rw [levelScaledGrad, levelIndLt, if_neg h, zero_smul, neg_zero, smul_zero]

theorem norm_levelScaledGrad_sq (hl : 0 < l) :
    ‖levelScaledGrad l u G x‖ ^ 2 = l⁻¹ ^ 2 * (levelIndLt l u x * ‖G x‖ ^ 2) := by
  have hlinv : (0 : ℝ) < l⁻¹ := by positivity
  rw [levelScaledGrad, norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hlinv.le, abs_of_nonneg (levelIndLt_nonneg l u x)]
  by_cases h : u x < l
  · simp only [levelIndLt, if_pos h]; ring
  · simp only [levelIndLt, if_neg h]; ring

/-- The level sets of `w_l`: for `−1 ≤ k < 0`, `{k < w_l} = {u < −k l}`. -/
theorem levelScaled_lt_iff (hl : 0 < l) (_hu : 0 ≤ u x) {k : ℝ} (hk1 : -1 ≤ k)
    (_hk0 : k < 0) :
    k < levelScaled l u x ↔ u x < -k * l := by
  have hm := levelScaled_mul (l := l) (u := u) (x := x) hl
  constructor
  · intro h
    have h1 : l * k < negTrunc l u x - l := by
      rw [← hm]; exact mul_lt_mul_of_pos_left h hl
    by_cases hlt : u x < l
    · rw [negTrunc, max_eq_left (show (0 : ℝ) ≤ l - u x by linarith)] at h1
      nlinarith
    · rw [negTrunc, max_eq_right (show l - u x ≤ 0 by linarith [not_lt.1 hlt])] at h1
      nlinarith
  · intro h
    have hkl : -k * l ≤ l := by nlinarith
    have hlt : u x < l := lt_of_lt_of_le h hkl
    have h1 : negTrunc l u x = l - u x := by
      rw [negTrunc, max_eq_left (show (0 : ℝ) ≤ l - u x by linarith)]
    refine lt_of_mul_lt_mul_left (a := l) ?_ hl.le
    rw [hm, h1]
    nlinarith

/-- The positive part of `w_l − k` is `(−k l − u)₊ / l`. -/
theorem levelScaled_sub_max (hl : 0 < l) (_hu : 0 ≤ u x) {k : ℝ} (hk1 : -1 ≤ k)
    (_hk0 : k ≤ 0) :
    max (levelScaled l u x - k) 0 = l⁻¹ * negTrunc (-k * l) u x := by
  have hlinv : (0 : ℝ) < l⁻¹ := by positivity
  rw [negTrunc, mul_max_of_nonneg _ _ hlinv.le, mul_zero]
  by_cases hlt : u x < l
  · have hval : levelScaled l u x - k = l⁻¹ * (-k * l - u x) := by
      rw [levelScaled, negTrunc, max_eq_left (show (0 : ℝ) ≤ l - u x by linarith)]
      field_simp
      try ring
    rw [hval]
  · have hnl := not_lt.1 hlt
    have hneg : negTrunc l u x = 0 := by
      rw [negTrunc, max_eq_right (by linarith)]
    have h1 : levelScaled l u x - k ≤ 0 := by
      rw [levelScaled, hneg]
      have hval : l⁻¹ * (0 - l) = -1 := by
        rw [zero_sub, mul_neg, inv_mul_cancel₀ hl.ne']
      rw [hval]; linarith
    have h2 : l⁻¹ * (-k * l - u x) ≤ 0 := by
      have hkl : -k * l ≤ l := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hlinv.le (by linarith)
    rw [max_eq_right h1, max_eq_right h2]

/-! ### The uniform De Giorgi class membership -/

/-- If `f` vanishes on `A \ B` then the integral over `A` reduces to the integral over `B`. -/
theorem setIntegral_eq_of_vanishing {f : Euc d → ℝ} {A B : Set (Euc d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A)
    (hzero : ∀ x ∈ A, x ∉ B → f x = 0) (hint : IntegrableOn f A volume) :
    (∫ x in A, f x) = ∫ x in B, f x := by
  have hunion : B ∪ (A \ B) = A := Set.union_sdiff_cancel hBA
  have hintB : IntegrableOn f B volume := hint.mono_set hBA
  have hintD : IntegrableOn f (A \ B) volume := hint.mono_set Set.sdiff_subset
  have hz : (∫ x in A \ B, f x) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => hzero x hx.1 hx.2
  calc (∫ x in A, f x) = ∫ x in B ∪ (A \ B), f x := by rw [hunion]
    _ = (∫ x in B, f x) + ∫ x in A \ B, f x :=
        setIntegral_union disjoint_sdiff_right (hA.diff hB) hintB hintD
    _ = ∫ x in B, f x := by rw [hz, add_zero]

set_option maxHeartbeats 1000000 in
/-- **The rescaled level function lies in `DG⁻(γ, 1)` with constants independent of the level.**
This is the whole point of the sharp (logarithm-free) level inequality
`exists_energy_ineq_super_sharp`: after dividing by `l²` both the gradient term and the
lower-order term become level-free, and the level sets of `w_l` are exactly `{v < −k l}`. -/
theorem exists_isDGSub_levelScaled (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) {v : Euc d → ℝ} (hv : IsRegMinimizer 2 κ Ψ K v)
    (hcomp : IsRegComp K v) (hvm : Measurable v) {G : Euc d → Euc d}
    (hGm : Measurable G) (hGg : G =ᵐ[volume] weakGrad v) (R₀ : ℝ) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ l : ℝ, 0 < l → l ≤ Real.exp (-(1 / 2 : ℝ)) →
      IsDGSub γ 1 R₀ K (levelScaled l v) (levelScaledGrad l v G) := by
  obtain ⟨γ, hγ, henergy⟩ := exists_energy_ineq_super_sharp hκ hΨ hK hv hcomp hvm
  refine ⟨γ, hγ, fun l hl hle => ?_⟩
  have hlne : l ≠ 0 := hl.ne'
  have hlinv : (0 : ℝ) < l⁻¹ := by positivity
  have hGsq : Integrable (fun x => ‖G x‖ ^ 2) volume := by
    refine hcomp.integrable_normSq_grad.congr ?_
    filter_upwards [hGg] with x hx
    rw [hx]
  -- the weak gradient
  have hwg : HasWeakGradient (levelScaled l v) (levelScaledGrad l v G) := by
    have hwg0 := (memW0_negTrunc (l := l) (K := K) hl.le hcomp.memW0).2
    have hwg1 : HasWeakGradient (fun x => negTrunc l v x - l)
        (fun x => -(levelIndLt l v x • G x)) := by
      refine hwg0.congr_right ?_
      filter_upwards [hGg] with x hx
      rw [hx]
    have hwg2 := hwg1.smul l⁻¹
    have heq1 : (l⁻¹ • fun x => negTrunc l v x - l) = levelScaled l v := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, levelScaled]
    have heq2 : (l⁻¹ • fun x => -(levelIndLt l v x • G x)) = levelScaledGrad l v G := rfl
    rwa [heq1, heq2] at hwg2
  have hFnorm : ∀ x, ‖levelScaledGrad l v G x‖ ^ 2 ≤ l⁻¹ ^ 2 * ‖G x‖ ^ 2 := by
    intro x
    rw [norm_levelScaledGrad_sq hl]
    nlinarith [levelIndLt_le_one l v x, levelIndLt_nonneg l v x, sq_nonneg ‖G x‖,
      sq_nonneg l⁻¹, mul_nonneg (sq_nonneg l⁻¹) (sq_nonneg ‖G x‖)]
  have hFint : Integrable (fun x => ‖levelScaledGrad l v G x‖ ^ 2) volume := by
    refine Integrable.mono' (hGsq.const_mul (l⁻¹ ^ 2))
      ((levelScaledGrad_measurable hvm hGm).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hFnorm x
  refine ⟨hwg, levelScaled_measurable hl hvm, levelScaledGrad_measurable hvm hGm, ?_, ?_⟩
  · -- local square integrability
    intro x₀ s _
    refine ⟨?_, hFint.integrableOn⟩
    refine Integrable.mono' (integrableOn_const (μ := volume) (C := (1 : ℝ))
      (measure_closedBall_lt_top (x := x₀) (r := s)).ne)
      (((levelScaled_measurable hl hvm).pow_const 2).aestronglyMeasurable.restrict)
      (ae_restrict_of_ae (Eventually.of_forall fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := abs_le.1 (abs_levelScaled_le_one hl (hcomp.nonneg x))
    nlinarith [h.1, h.2]
  · -- the energy inequality
    intro x₀ r s k hr hrs _ hsub
    have hballs : MeasurableSet (Metric.ball x₀ s) := measurableSet_ball
    have hballr : MeasurableSet (Metric.ball x₀ r) := measurableSet_ball
    have hlev : ∀ kk : ℝ, MeasurableSet {x : Euc d | kk < levelScaled l v x} := fun kk =>
      measurableSet_lt measurable_const (levelScaled_measurable hl hvm)
    have hgap : (0 : ℝ) < (s - r) ^ 2 := by positivity
    have hγd : (0 : ℝ) ≤ γ / (s - r) ^ 2 := div_nonneg hγ (sq_nonneg _)
    have hγ1 : (0 : ℝ) ≤ γ * 1 ^ 2 := by nlinarith [hγ]
    have hPint : ∀ kk : ℝ, IntegrableOn
        (fun x => max (levelScaled l v x - kk) 0 ^ 2) (Metric.ball x₀ s) volume := by
      intro kk
      refine Integrable.mono' (integrableOn_const (μ := volume) (C := (1 + |kk|) ^ 2)
        (measure_ball_lt_top (x := x₀) (r := s)).ne)
        ((((levelScaled_measurable hl hvm).sub measurable_const).max
          measurable_const).pow_const 2).aestronglyMeasurable.restrict
        (ae_restrict_of_ae (Eventually.of_forall fun x => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := abs_le.1 (abs_levelScaled_le_one hl (hcomp.nonneg x))
      have h2 : max (levelScaled l v x - kk) 0 ≤ 1 + |kk| := by
        refine max_le ?_ (by positivity)
        linarith [h1.2, neg_abs_le kk]
      have h3 : 0 ≤ max (levelScaled l v x - kk) 0 := le_max_right _ _
      nlinarith [h2, h3]
    -- the main case `-1 ≤ k < 0`
    have key : ∀ kk : ℝ, -1 ≤ kk → kk < 0 →
        (∫ x in Metric.ball x₀ r ∩ {x | kk < levelScaled l v x},
            ‖levelScaledGrad l v G x‖ ^ 2) ≤
          γ / (s - r) ^ 2 * (∫ x in Metric.ball x₀ s, max (levelScaled l v x - kk) 0 ^ 2) +
            γ * 1 ^ 2 *
              (volume (Metric.ball x₀ s ∩ {x | kk < levelScaled l v x})).toReal := by
      intro kk hkk1 hkk0
      obtain ⟨l', hl'⟩ : ∃ l' : ℝ, l' = -kk * l := ⟨_, rfl⟩
      have hl'0 : 0 < l' := by rw [hl']; exact mul_pos (by linarith) hl
      have hl'l : l' ≤ l := by rw [hl']; nlinarith
      have hl'e : l' ≤ Real.exp (-(1 / 2 : ℝ)) := le_trans hl'l hle
      have hsetEq : {x : Euc d | kk < levelScaled l v x} = {x : Euc d | v x < l'} := by
        ext x
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, levelScaled_lt_iff hl (hcomp.nonneg x) hkk1 hkk0,
          ← hl']
      have hmain := henergy x₀ r s l' hr hrs hl'0 hl'e hsub
      have hl'meas : MeasurableSet {x : Euc d | v x < l'} := measurableSet_lt hvm measurable_const
      have hFeq : (∫ x in Metric.ball x₀ r ∩ {x | v x < l'},
            ‖levelScaledGrad l v G x‖ ^ 2) =
          l⁻¹ ^ 2 * ∫ x in Metric.ball x₀ r ∩ {x | v x < l'}, ‖weakGrad v x‖ ^ 2 := by
        rw [← integral_const_mul]
        refine setIntegral_congr_ae (hballr.inter hl'meas) ?_
        filter_upwards [hGg] with x hx hxs
        have hxlt : v x < l' := hxs.2
        have hind : levelIndLt l v x = 1 := by
          rw [levelIndLt, if_pos (lt_of_lt_of_le hxlt hl'l)]
        rw [norm_levelScaledGrad_sq hl, hind, one_mul, hx]
      have hPeq : (∫ x in Metric.ball x₀ s, max (levelScaled l v x - kk) 0 ^ 2) =
          l⁻¹ ^ 2 * ∫ x in Metric.ball x₀ s, negTrunc l' v x ^ 2 := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun hballs fun x _ => ?_
        rw [levelScaled_sub_max hl (hcomp.nonneg x) hkk1 hkk0.le, ← hl']
        ring
      have hll : l⁻¹ ^ 2 * l' ^ 2 = kk ^ 2 := by
        rw [hl']
        field_simp
        try ring
      have hmeas0 : (0 : ℝ) ≤ (volume (Metric.ball x₀ s ∩ {x : Euc d | v x < l'})).toReal :=
        ENNReal.toReal_nonneg
      have hcoef : γ * (l⁻¹ ^ 2 * l' ^ 2) ≤ γ * 1 ^ 2 := by
        rw [hll]
        have hkk2 : kk ^ 2 ≤ 1 := by nlinarith
        have hmm := mul_le_mul_of_nonneg_left hkk2 hγ
        nlinarith [hmm]
      rw [hsetEq, hFeq, hPeq]
      have hmul := mul_le_mul_of_nonneg_left hmain (sq_nonneg l⁻¹)
      have hstep := mul_le_mul_of_nonneg_right hcoef hmeas0
      nlinarith [hmul, hstep]
    rcases le_or_gt 0 k with hk0 | hk0
    · -- the level set is empty
      have hempty : Metric.ball x₀ r ∩ {x : Euc d | k < levelScaled l v x} = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and, not_lt]
        exact fun _ => le_trans (levelScaled_nonpos hl (hcomp.nonneg x)) hk0
      rw [hempty, MeasureTheory.setIntegral_empty]
      have h1 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ s, max (levelScaled l v x - k) 0 ^ 2 :=
        integral_nonneg fun x => sq_nonneg _
      have h2 : (0 : ℝ) ≤ (volume (Metric.ball x₀ s ∩
          {x : Euc d | k < levelScaled l v x})).toReal := ENNReal.toReal_nonneg
      exact add_nonneg (mul_nonneg hγd h1) (mul_nonneg hγ1 h2)
    · rcases le_or_gt (-1 : ℝ) k with hk1 | hk1
      · exact key k hk1 hk0
      · -- `k < -1`: the level set is everything, but the gradient vanishes off `{v < l}`
        have hkey := key (-1) le_rfl (by norm_num)
        have hsub' : Metric.ball x₀ r ∩ {x : Euc d | (-1 : ℝ) < levelScaled l v x} ⊆
            Metric.ball x₀ r ∩ {x : Euc d | k < levelScaled l v x} :=
          Set.inter_subset_inter_right _ fun x hx => lt_trans hk1 hx
        have hLeq : (∫ x in Metric.ball x₀ r ∩ {x : Euc d | k < levelScaled l v x},
              ‖levelScaledGrad l v G x‖ ^ 2) =
            ∫ x in Metric.ball x₀ r ∩ {x : Euc d | (-1 : ℝ) < levelScaled l v x},
              ‖levelScaledGrad l v G x‖ ^ 2 := by
          refine setIntegral_eq_of_vanishing (hballr.inter (hlev k))
            (hballr.inter (hlev (-1))) hsub' ?_ hFint.integrableOn
          intro x hx hnot
          have hmem : ¬ ((-1 : ℝ) < levelScaled l v x) := fun h => hnot ⟨hx.1, h⟩
          have heq : levelScaled l v x = -1 :=
            le_antisymm (not_lt.1 hmem) (neg_one_le_levelScaled hl)
          have hm := levelScaled_mul (l := l) (u := v) (x := x) hl
          rw [heq] at hm
          have hnt : negTrunc l v x = 0 := by linarith
          have hvl : ¬ (v x < l) := by
            intro hlt
            rw [negTrunc, max_eq_left (by linarith)] at hnt
            linarith
          rw [norm_levelScaledGrad_sq hl, levelIndLt, if_neg hvl]
          ring
        rw [hLeq]
        refine le_trans hkey (add_le_add ?_ ?_)
        · refine mul_le_mul_of_nonneg_left ?_ hγd
          refine setIntegral_mono_on (hPint (-1)) (hPint k) hballs fun x _ => ?_
          have h1 : (0 : ℝ) ≤ max (levelScaled l v x - (-1)) 0 := le_max_right _ _
          have h2 : max (levelScaled l v x - (-1)) 0 ≤ max (levelScaled l v x - k) 0 :=
            max_le_max (by linarith) le_rfl
          nlinarith [h1, h2]
        · refine mul_le_mul_of_nonneg_left ?_ hγ1
          refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_right _
            fun x hx => lt_trans hk1 hx))
          exact ((measure_mono Set.inter_subset_left).trans_lt
            (measure_ball_lt_top (x := x₀) (r := s))).ne

/-! ### Smallness of the sublevel sets from the `L¹` logarithm bound -/

/-- **The sublevel sets of the minimizer are small.**  The `δ`-uniform `L¹` bound for
`(−log(v+δ))₊` of `exists_neg_log_shift_bound` (entropy comparison) evaluated at `δ = l` gives
`log(1/(2l)) · |B_R ∩ {v < l}| ≤ A`, so the measure of `{v < l}` in `B_R` tends to `0` as
`l ↓ 0` — no rate beyond the logarithm is needed. -/
theorem exists_measure_sublevel_bound (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) {v : Euc d → ℝ} (hv : IsRegMinimizer 2 κ Ψ K v)
    (hcomp : IsRegComp K v) (hvm : Measurable v) {x₀ : Euc d} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall x₀ (2 * R) ⊆ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ l : ℝ, 0 < l → 2 * l < 1 →
      Real.log (1 / (2 * l)) *
        (volume (Metric.ball x₀ R ∩ {x | v x < l})).toReal ≤ A := by
  obtain ⟨A, hA0, hA⟩ := exists_neg_log_shift_bound hκ hΨ hK hv hcomp hR hball
  refine ⟨A, hA0, fun l hl0 hl1 => ?_⟩
  obtain ⟨hint, hbd⟩ := hA l hl0 (by linarith)
  have hSmeas : MeasurableSet (Metric.ball x₀ R ∩ {x : Euc d | v x < l}) :=
    measurableSet_ball.inter (measurableSet_lt hvm measurable_const)
  have hSfin : volume (Metric.ball x₀ R ∩ {x : Euc d | v x < l}) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt
      (measure_ball_lt_top (x := x₀) (r := R))).ne
  have hptw : ∀ x ∈ Metric.ball x₀ R ∩ {x : Euc d | v x < l},
      Real.log (1 / (2 * l)) ≤ max (-(Real.log (v x + l))) 0 := by
    intro x hx
    have hvl : v x < l := hx.2
    have hpos : 0 < v x + l := by linarith [hcomp.nonneg x]
    have h1 : Real.log (v x + l) ≤ Real.log (2 * l) := Real.log_le_log hpos (by linarith)
    have h2 : Real.log (1 / (2 * l)) = -Real.log (2 * l) := by rw [one_div, Real.log_inv]
    refine le_trans ?_ (le_max_left _ _)
    rw [h2]; linarith
  have hconst : IntegrableOn (fun _ : Euc d => Real.log (1 / (2 * l)))
      (Metric.ball x₀ R ∩ {x : Euc d | v x < l}) volume := integrableOn_const hSfin
  have hmono := setIntegral_mono_on hconst (hint.mono_set Set.inter_subset_left) hSmeas hptw
  have hmono' : (volume (Metric.ball x₀ R ∩ {x : Euc d | v x < l})).toReal *
      Real.log (1 / (2 * l)) ≤ ∫ x in Metric.ball x₀ R ∩ {x : Euc d | v x < l},
        max (-(Real.log (v x + l))) 0 := by
    simpa [measureReal_def] using hmono
  have hsub : (∫ x in Metric.ball x₀ R ∩ {x : Euc d | v x < l},
      max (-(Real.log (v x + l))) 0) ≤
      ∫ x in Metric.ball x₀ R, max (-(Real.log (v x + l))) 0 :=
    setIntegral_mono_set hint
      (ae_restrict_of_ae (Eventually.of_forall fun x => le_max_right _ _))
      (LE.le.eventuallyLE Set.inter_subset_left)
  linarith [hmono', hsub, hbd]

/-! ### The local positive lower bound -/

set_option maxHeartbeats 1000000 in
/-- **Local positive lower bound for the regularized minimizer** (`REGULARIZED_ROUTE.md`,
Revision 2 (iii)): on a ball around every point of `K` the minimizer is bounded below by a
positive constant.  This is the frozen lane statement `exists_local_lower_bound`, verbatim.

Proof.  The rescaled level function `w_l = −min(v,l)/l` lies in `DG⁻(γ, 1)` with constants
independent of `l` (`exists_isDGSub_levelScaled`, which rests on the sign of the entropy along
the super competitor).  Fix `R` so small that `C_{DG} R ≤ 1/4`; the `L¹` logarithm bound makes
`|B_R ∩ {v < l}|` — hence `⨍_{B_R} (w_l + 1)²` — arbitrarily small, so for `l` small the De
Giorgi sup bound at the level `k = −1` gives `w_l ≤ −1 + 1/4 + 1/4 = −1/2` a.e. on `B_{R/2}`,
i.e. `v ≥ l/2` there. -/
theorem exists_local_lower_bound' (hd : 0 < d) (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) {v : Euc d → ℝ} (hv : IsRegMinimizer 2 κ Ψ K v)
    (hcomp : IsRegComp K v) (hvm : Measurable v) {x₀ : Euc d} (hx₀ : x₀ ∈ K) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧ Metric.ball x₀ r ⊆ K ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), ε ≤ v x := by
  classical
  -- a measurable representative of the weak gradient
  obtain ⟨G, hGdef⟩ : ∃ G : Euc d → Euc d,
      G = hcomp.aestronglyMeasurable_grad.mk (weakGrad v) := ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hGdef]; exact hcomp.aestronglyMeasurable_grad.stronglyMeasurable_mk.measurable
  have hGg : G =ᵐ[volume] weakGrad v := by
    rw [hGdef]; exact hcomp.aestronglyMeasurable_grad.ae_eq_mk.symm
  -- the level-uniform De Giorgi class and its sup bound
  obtain ⟨γ, hγ, hDG⟩ := exists_isDGSub_levelScaled hκ hΨ hK hv hcomp hvm hGm hGg 1
  obtain ⟨Cc, hCc, hsup⟩ := exists_dg_sup_bound (d := d) hd hγ
  -- the radius
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hK.isOpen x₀ hx₀
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = min (min (ρ / 4) (1 / 2)) (1 / (4 * Cc)) := ⟨_, rfl⟩
  have hR : 0 < R := by
    rw [hRdef]; exact lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hRρ : R ≤ ρ / 4 := by
    rw [hRdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hR1 : R ≤ 1 / 2 := by
    rw [hRdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hRC : R ≤ 1 / (4 * Cc) := by rw [hRdef]; exact min_le_right _ _
  have hball2 : Metric.closedBall x₀ (2 * R) ⊆ K :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρK
  have hball1 : Metric.closedBall x₀ R ⊆ K :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball2
  have hCcR : Cc * (1 * R) ≤ 1 / 4 := by
    rw [one_mul]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * Cc)] at hRC
    nlinarith [hRC, hCc]
  -- the `L¹` logarithm bound
  obtain ⟨A, hA0, hAm⟩ := exists_measure_sublevel_bound hκ hΨ hK hv hcomp hvm hR hball2
  have hVol : (0 : ℝ) < (volume (Metric.ball x₀ R)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hR).ne' measure_ball_lt_top.ne
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ,
      T = 16 * Cc ^ 2 * A / (volume (Metric.ball x₀ R)).toReal + 1 := ⟨_, rfl⟩
  have hT : 0 < T := by
    rw [hTdef]
    have : (0:ℝ) ≤ 16 * Cc ^ 2 * A / (volume (Metric.ball x₀ R)).toReal := by positivity
    linarith
  have hTbig : 16 * Cc ^ 2 * A / (volume (Metric.ball x₀ R)).toReal ≤ T := by
    rw [hTdef]; linarith
  -- the level
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = Real.exp (-T) / 2 := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hldef]; positivity
  have h2l : 2 * l = Real.exp (-T) := by rw [hldef]; ring
  have h2l1 : 2 * l < 1 := by rw [h2l]; exact Real.exp_lt_one_iff.2 (by linarith)
  have hlog2l : Real.log (1 / (2 * l)) = T := by
    rw [h2l, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  have hle : l ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have hexp1 : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [hldef]
    linarith
  -- the measure of the sublevel set
  have hmeasle : (volume (Metric.ball x₀ R ∩ {x : Euc d | v x < l})).toReal ≤ A / T := by
    have h := hAm l hl0 h2l1
    rw [hlog2l] at h
    rw [le_div_iff₀ hT]
    linarith
  -- the average of `(w_l + 1)²`
  have hvan : ∀ x : Euc d, ¬ (v x < l) → max (levelScaled l v x - (-1)) 0 ^ 2 = 0 := by
    intro x hx
    have hm := levelScaled_mul (l := l) (u := v) (x := x) hl0
    have hnt : negTrunc l v x = 0 := by
      rw [negTrunc, max_eq_right (by linarith [not_lt.1 hx])]
    rw [hnt] at hm
    have hw : levelScaled l v x = -1 := by
      have : l * levelScaled l v x = l * (-1) := by rw [hm]; ring
      exact mul_left_cancel₀ hl0.ne' this
    rw [hw]
    norm_num
  have hboundone : ∀ x : Euc d, max (levelScaled l v x - (-1)) 0 ^ 2 ≤ 1 := by
    intro x
    have h2 : max (levelScaled l v x - (-1)) 0 ≤ 1 := by
      refine max_le ?_ (by norm_num)
      linarith [levelScaled_nonpos hl0 (hcomp.nonneg x)]
    have h3 : 0 ≤ max (levelScaled l v x - (-1)) 0 := le_max_right _ _
    nlinarith [h2, h3]
  have hPintR : IntegrableOn (fun x => max (levelScaled l v x - (-1)) 0 ^ 2)
      (Metric.ball x₀ R) volume := by
    refine Integrable.mono' (integrableOn_const (μ := volume) (C := (1 : ℝ))
      (measure_ball_lt_top (x := x₀) (r := R)).ne)
      ((((levelScaled_measurable hl0 hvm).sub measurable_const).max
        measurable_const).pow_const 2).aestronglyMeasurable.restrict
      (ae_restrict_of_ae (Eventually.of_forall fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hboundone x
  have hIeq : (∫ x in Metric.ball x₀ R, max (levelScaled l v x - (-1)) 0 ^ 2) =
      ∫ x in Metric.ball x₀ R ∩ {x : Euc d | v x < l},
        max (levelScaled l v x - (-1)) 0 ^ 2 := by
    refine setIntegral_eq_of_vanishing measurableSet_ball
      (measurableSet_ball.inter (measurableSet_lt hvm measurable_const))
      Set.inter_subset_left ?_ hPintR
    intro x hxA hnot
    exact hvan x fun hlt => hnot ⟨hxA, hlt⟩
  have hIle : (∫ x in Metric.ball x₀ R, max (levelScaled l v x - (-1)) 0 ^ 2) ≤ A / T := by
    rw [hIeq]
    refine le_trans ?_ hmeasle
    have hSmeas : MeasurableSet (Metric.ball x₀ R ∩ {x : Euc d | v x < l}) :=
      measurableSet_ball.inter (measurableSet_lt hvm measurable_const)
    have hSfin : volume (Metric.ball x₀ R ∩ {x : Euc d | v x < l}) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_left).trans_lt
        (measure_ball_lt_top (x := x₀) (r := R))).ne
    have hmono := setIntegral_mono_on (hPintR.mono_set Set.inter_subset_left)
      (integrableOn_const (μ := volume) (C := (1:ℝ)) hSfin) hSmeas (fun x _ => hboundone x)
    simpa [measureReal_def] using hmono
  -- the De Giorgi sup bound at the level `k = -1`
  have hmain := hsup 1 1 K (levelScaled l v) (levelScaledGrad l v G) zero_le_one
    (hDG l hl0 hle) x₀ R hR (by linarith) hball1 (-1)
  refine ⟨R / 2, l / 2, by linarith, by linarith, ?_, ?_⟩
  · exact Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (by linarith)).trans hball1)
  · filter_upwards [hmain] with x hx
    have havg : (⨍ y in Metric.ball x₀ R, max (levelScaled l v y - (-1)) 0 ^ 2) ≤
        A / T / (volume (Metric.ball x₀ R)).toReal := by
      have hrw : A / T / (volume (Metric.ball x₀ R)).toReal =
          (volume (Metric.ball x₀ R)).toReal⁻¹ * (A / T) := by ring
      rw [setAverage_eq, smul_eq_mul, Measure.real, hrw]
      exact mul_le_mul_of_nonneg_left hIle (by positivity)
    have hquad : Cc ^ 2 * (A / T / (volume (Metric.ball x₀ R)).toReal) ≤ (1 / 4) ^ 2 := by
      have h1 : 16 * Cc ^ 2 * A ≤ T * (volume (Metric.ball x₀ R)).toReal := by
        rw [div_le_iff₀ hVol] at hTbig
        linarith
      rw [div_div, ← mul_div_assoc,
        div_le_iff₀ (by positivity : (0:ℝ) < T * (volume (Metric.ball x₀ R)).toReal)]
      linarith [h1]
    have hsqrt : Cc * Real.sqrt (⨍ y in Metric.ball x₀ R,
        max (levelScaled l v y - (-1)) 0 ^ 2) ≤ 1 / 4 := by
      have h1 : Real.sqrt (⨍ y in Metric.ball x₀ R, max (levelScaled l v y - (-1)) 0 ^ 2) ≤
          Real.sqrt (A / T / (volume (Metric.ball x₀ R)).toReal) := Real.sqrt_le_sqrt havg
      have h2 : Cc * Real.sqrt (A / T / (volume (Metric.ball x₀ R)).toReal) =
          Real.sqrt (Cc ^ 2 * (A / T / (volume (Metric.ball x₀ R)).toReal)) := by
        rw [Real.sqrt_mul (sq_nonneg Cc), Real.sqrt_sq hCc.le]
      have h3 : Real.sqrt (Cc ^ 2 * (A / T / (volume (Metric.ball x₀ R)).toReal)) ≤ 1 / 4 := by
        calc Real.sqrt (Cc ^ 2 * (A / T / (volume (Metric.ball x₀ R)).toReal))
            ≤ Real.sqrt ((1 / 4) ^ 2) := Real.sqrt_le_sqrt hquad
          _ = 1 / 4 := Real.sqrt_sq (by norm_num)
      calc Cc * Real.sqrt (⨍ y in Metric.ball x₀ R, max (levelScaled l v y - (-1)) 0 ^ 2)
          ≤ Cc * Real.sqrt (A / T / (volume (Metric.ball x₀ R)).toReal) :=
            mul_le_mul_of_nonneg_left h1 hCc.le
        _ = Real.sqrt (Cc ^ 2 * (A / T / (volume (Metric.ball x₀ R)).toReal)) := h2
        _ ≤ 1 / 4 := h3
    -- conclude
    have hwle : levelScaled l v x ≤ -1 / 2 := by linarith [hx, hsqrt, hCcR]
    have hm := levelScaled_mul (l := l) (u := v) (x := x) hl0
    have hmul := mul_le_mul_of_nonneg_left hwle hl0.le
    have hnt : negTrunc l v x ≤ l / 2 := by linarith [hm, hmul]
    have hdef : negTrunc l v x = max (l - v x) 0 := rfl
    rw [hdef] at hnt
    have hleft := le_max_left (l - v x) 0
    linarith

end Komlos.Literature.Regularized
