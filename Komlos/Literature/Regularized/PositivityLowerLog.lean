import Komlos.Literature.Regularized.PositivityLowerEntropy

/-!
# Lane `L2p` (`reg/pos-lower`), step 3: the `L¹` bound for `(-log(v + δ))₊`

`REGULARIZED_ROUTE.md`, Revision 2 (iii).  The entropy comparison
(`exists_weighted_log_bound`) gives, for a cutoff `h` with `0 ≤ h ≤ 1` supported in `K`,

`∫ h² (-log(v² + τ)) ≤ B`  uniformly in `τ ∈ (0, 1]`.

The De Giorgi machinery of `Komlos/Literature/Regularized/PositivityLower.lean` is run on the
*shifted* logarithm `z_δ = -log(v + δ)`, which — unlike `-log v` — is globally bounded above and
constant off `K`, hence globally weakly differentiable.  The bound it needs is an `L¹` bound for
`(z_δ)₊` on a ball, **uniform in `δ`**, and that is exactly the statement above at `τ = δ²`:
`(v + δ)² ≥ v² + δ²`, so `-log(v + δ) ≤ -½ log(v² + δ²)`.

No monotone limit `τ ↓ 0` is needed anywhere, and in particular the a.e. positivity of `v` is
never used: the final lower bound `v ≥ e^{-θ} - δ` is obtained by choosing `δ` small, not by
first knowing `v > 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ} {K : Set (Euc d)} {v : Euc d → ℝ}

/-- **The `L¹` bound for the shifted negative logarithm** (`REGULARIZED_ROUTE.md`,
Revision 2 (iii)): on every ball `B_R` with `closedBall x₀ (2R) ⊆ K` the positive part of
`-log(v + δ)` has an integral bounded **independently of `δ ∈ (0, 1]`**.

Proof: take the cutoff `h` of `exists_cutoff_const` with `h = 1` on `closedBall x₀ R` and
`tsupport h ⊆ closedBall x₀ (2R) ⊆ K`, and apply `exists_weighted_log_bound` at `τ = δ²`.
Pointwise on the ball, `(v + δ)² ≥ v² + δ²` gives
`(-log(v + δ))₊ ≤ ½ (-log(v² + δ²))₊ = ½ h² (-log(v² + δ²))₊`, the positive part is controlled by
the signed quantity up to `L₁ h²` with `L₁ = (log(M² + 1))₊`, and the integral over the ball is at
most the integral over `ℝ^d` because the integrand is nonnegative. -/
theorem exists_neg_log_shift_bound (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hv : IsRegMinimizer 2 κ Ψ K v) (hcomp : IsRegComp K v)
    {x₀ : Euc d} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall x₀ (2 * R) ⊆ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      IntegrableOn (fun x => max (-(Real.log (v x + δ))) 0) (Metric.ball x₀ R) volume ∧
      (∫ x in Metric.ball x₀ R, max (-(Real.log (v x + δ))) 0) ≤ A := by
  classical
  obtain ⟨Ccut, hCcut, hcut⟩ := exists_cutoff_const d
  obtain ⟨h, hhC, hhs, hhsupp, hh0, hh1, hh1ball, -⟩ := hcut x₀ R (2 * R) hR (by linarith)
  have hhK : tsupport h ⊆ K := hhsupp.trans hball
  obtain ⟨B, hB⟩ := exists_weighted_log_bound hκ hΨ hK hv hcomp hhC hhs hhK hh0 hh1
  obtain ⟨M₀, hM₀⟩ := hcomp.exists_le
  have hM1 : (1 : ℝ) ≤ max M₀ 1 := le_max_right _ _
  have hvM : ∀ x, v x ≤ max M₀ 1 := fun x => (hM₀ x).trans (le_max_left _ _)
  have hh1' : ContDiff ℝ 1 h := hhC.of_le (by exact_mod_cast le_top)
  have hhcomp : IsRegComp K h := isRegComp_of_contDiff hh1' hhs hhK hh0
  have hhsqint : Integrable (fun x => h x ^ 2) volume := hhcomp.integrable_sq
  have hL₁0 : (0 : ℝ) ≤ max (Real.log ((max M₀ 1) ^ 2 + 1)) 0 := le_max_right _ _
  have hhsq0 : (0 : ℝ) ≤ ∫ x, h x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hvmeas : AEStronglyMeasurable v volume := hcomp.aestronglyMeasurable
  refine ⟨max (1 / 2 * (B + max (Real.log ((max M₀ 1) ^ 2 + 1)) 0 * ∫ x, h x ^ 2)) 0,
    le_max_right _ _, fun δ hδ0 hδ1 => ?_⟩
  have hτ0 : (0 : ℝ) < δ ^ 2 := by positivity
  have hτ1 : δ ^ 2 ≤ 1 := by nlinarith
  have hBδ := hB (δ ^ 2) hτ0 hτ1
  have hYint : Integrable (fun x => h x ^ 2 * (-(Real.log (v x ^ 2 + δ ^ 2)))) volume :=
    integrable_sq_mul_neg_log hK hcomp hhcomp hh1 hτ0 hτ1
  -- measurability of the shifted logarithm
  have hfmeas : AEStronglyMeasurable (fun x => max (-(Real.log (v x + δ))) 0) volume :=
    (((Real.measurable_log.comp_aemeasurable
      (hvmeas.aemeasurable.add_const δ)).neg).max aemeasurable_const).aestronglyMeasurable
  have hbd : ∀ x, max (-(Real.log (v x + δ))) 0 ≤ max (-(Real.log δ)) 0 := by
    intro x
    have hle : Real.log δ ≤ Real.log (v x + δ) :=
      Real.log_le_log hδ0 (by linarith [hcomp.nonneg x])
    exact max_le_max (by linarith) le_rfl
  have : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hint : IntegrableOn (fun x => max (-(Real.log (v x + δ))) 0)
      (Metric.ball x₀ R) volume := by
    refine Integrable.mono' (integrable_const (max (-(Real.log δ)) 0)) hfmeas.restrict
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hbd x
  refine ⟨hint, le_trans ?_ (le_max_left _ _)⟩
  -- the majorant `½ h² (-log(v² + δ²))₊`
  have hGmeas0 : AEStronglyMeasurable
      (fun x => h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0) volume := by
    have h1 : AEMeasurable (fun x => Real.log (v x ^ 2 + δ ^ 2)) volume :=
      Real.measurable_log.comp_aemeasurable
        ((hvmeas.aemeasurable.pow_const 2).add_const (δ ^ 2))
    exact (hhcomp.aestronglyMeasurable.pow 2).mul
      (h1.neg.max aemeasurable_const).aestronglyMeasurable
  have hGnn : ∀ x, 0 ≤ 1 / 2 * (h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0) := fun x => by
    have := le_max_right (-(Real.log (v x ^ 2 + δ ^ 2))) 0
    positivity
  -- the positive part is controlled by the signed quantity
  have hpp : ∀ x, h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0 ≤
      h x ^ 2 * (-(Real.log (v x ^ 2 + δ ^ 2))) +
        max (Real.log ((max M₀ 1) ^ 2 + 1)) 0 * h x ^ 2 := by
    intro x
    have hlogle : Real.log (v x ^ 2 + δ ^ 2) ≤ max (Real.log ((max M₀ 1) ^ 2 + 1)) 0 := by
      refine le_trans (Real.log_le_log (by positivity) ?_) (le_max_left _ _)
      nlinarith [hcomp.nonneg x, hvM x]
    have hh2 : 0 ≤ h x ^ 2 := sq_nonneg _
    rcases le_or_gt (-(Real.log (v x ^ 2 + δ ^ 2))) 0 with hneg | hpos
    · rw [max_eq_right hneg]
      nlinarith [mul_le_mul_of_nonneg_left hlogle hh2]
    · rw [max_eq_left hpos.le]
      nlinarith [mul_nonneg hL₁0 hh2]
  have hGint : Integrable
      (fun x => 1 / 2 * (h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0)) volume := by
    refine Integrable.const_mul ?_ (1 / 2)
    refine Integrable.mono' (hYint.add (hhsqint.const_mul
      (max (Real.log ((max M₀ 1) ^ 2 + 1)) 0))) hGmeas0 (Eventually.of_forall fun x => ?_)
    have hnn : (0 : ℝ) ≤ h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0 := by
      have := le_max_right (-(Real.log (v x ^ 2 + δ ^ 2))) 0
      positivity
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hpp x
  -- the pointwise comparison on the ball
  have hkey : ∀ x ∈ Metric.ball x₀ R, max (-(Real.log (v x + δ))) 0 ≤
      1 / 2 * (h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0) := by
    intro x hx
    have hhx : h x = 1 := hh1ball x (Metric.ball_subset_closedBall hx)
    rw [hhx, one_pow, one_mul]
    have hvx : 0 ≤ v x := hcomp.nonneg x
    have hpos : 0 < v x + δ := by linarith
    have hsq : v x ^ 2 + δ ^ 2 ≤ (v x + δ) ^ 2 := by nlinarith
    have hlog : Real.log (v x ^ 2 + δ ^ 2) ≤ 2 * Real.log (v x + δ) := by
      have h1 : Real.log (v x ^ 2 + δ ^ 2) ≤ Real.log ((v x + δ) ^ 2) :=
        Real.log_le_log (by positivity) hsq
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    rcases le_or_gt (-(Real.log (v x + δ))) 0 with hneg | hpos2
    · rw [max_eq_right hneg]
      have := le_max_right (-(Real.log (v x ^ 2 + δ ^ 2))) 0
      positivity
    · rw [max_eq_left hpos2.le, max_eq_left (by linarith : (0 : ℝ) ≤
        -(Real.log (v x ^ 2 + δ ^ 2)))]
      linarith
  calc (∫ x in Metric.ball x₀ R, max (-(Real.log (v x + δ))) 0)
      ≤ ∫ x in Metric.ball x₀ R,
          1 / 2 * (h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0) :=
        setIntegral_mono_on hint hGint.integrableOn measurableSet_ball hkey
    _ ≤ ∫ x, 1 / 2 * (h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0) :=
        setIntegral_le_integral hGint (Eventually.of_forall hGnn)
    _ = 1 / 2 * ∫ x, h x ^ 2 * max (-(Real.log (v x ^ 2 + δ ^ 2))) 0 := integral_const_mul _ _
    _ ≤ 1 / 2 * (B + max (Real.log ((max M₀ 1) ^ 2 + 1)) 0 * ∫ x, h x ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have hstep := integral_mono (hGint.const_mul 2 |>.congr
          (Eventually.of_forall fun x => by ring))
          (hYint.add (hhsqint.const_mul (max (Real.log ((max M₀ 1) ^ 2 + 1)) 0)))
          hpp
        simp only [Pi.add_apply] at hstep
        rw [integral_add hYint (hhsqint.const_mul _), integral_const_mul] at hstep
        linarith [hstep, hBδ]

end Komlos.Literature.Regularized
