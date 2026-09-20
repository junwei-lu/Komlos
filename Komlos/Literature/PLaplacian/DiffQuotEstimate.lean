import Komlos.Literature.PLaplacian.DiffQuotBasic
import Komlos.Literature.PLaplacian.FluxIncrement

/-!
# Absorption in the homogeneous difference-quotient estimate

The squared-cutoff energy estimate toward the regularity input of paper Appendix A.
The weight is retained on the cutoff error. In particular, the singular range needs
a further argument to control that error uniformly in the difference-quotient step.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-- Difference quotients of a Sobolev potential have an `L^p` bound independent
of the step. This is the quantitative translation estimate, including step zero. -/
theorem eLpNorm_diffQuot_le {p : ℝ} (hp : 1 < p)
    {v : Euc d → ℝ} {G : Euc d → Euc d} (hvG : HasWeakGradient v G)
    (hv : MemLp v (ENNReal.ofReal p)) (hG : MemLp G (ENNReal.ofReal p))
    (h : ℝ) (e : Euc d) :
    eLpNorm (diffQuot h e v) (ENNReal.ofReal p) ≤
      ‖e‖ₑ * eLpNorm G (ENNReal.ofReal p) := by
  have heq : eLpNorm (diffQuot h e v) (ENNReal.ofReal p) =
      ‖(h⁻¹ : ℝ)‖ₑ * eLpNorm (fun x => v (x + h • e) - v x) (ENNReal.ofReal p) :=
    eLpNorm_const_smul (𝕜 := ℝ) h⁻¹ (fun x => v (x + h • e) - v x)
      (ENNReal.ofReal p) volume
  have ht : eLpNorm (fun x => v (x + h • e) - v x) (ENNReal.ofReal p) ≤
      ‖h • e‖ₑ * eLpNorm G (ENNReal.ofReal p) := by
    simpa only [sub_neg_eq_add, enorm_neg] using
      eLpNorm_sub_translate_le hp hvG hv hG (-(h • e))
  have hcoef : ‖(h⁻¹ : ℝ)‖ₑ * ‖h • e‖ₑ ≤ ‖e‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    by_cases hh : h = 0
    · simp only [hh, inv_zero, norm_zero, zero_mul]
      exact norm_nonneg e
    · rw [norm_smul, norm_inv, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh), one_mul]
  have hmul := mul_le_mul_right ht ‖(h⁻¹ : ℝ)‖ₑ
  have hlast := mul_le_mul_left hcoef (eLpNorm G (ENNReal.ofReal p) volume)
  exact heq.le.trans (hmul.trans
    ((mul_assoc ‖(h⁻¹ : ℝ)‖ₑ ‖h • e‖ₑ (eLpNorm G (ENNReal.ofReal p) volume)).symm.le.trans hlast))

/-- The integral form of the uniform Sobolev difference-quotient bound. -/
theorem integral_norm_diffQuot_rpow_le {p : ℝ} (hp : 1 < p)
    {v : Euc d → ℝ} {G : Euc d → Euc d} (hvG : HasWeakGradient v G)
    (hv : MemLp v (ENNReal.ofReal p)) (hG : MemLp G (ENNReal.ofReal p))
    (h : ℝ) (e : Euc d) :
    (∫ x, ‖diffQuot h e v x‖ ^ p) ≤ ‖e‖ ^ p * ∫ x, ‖G x‖ ^ p := by
  have hp0 : 0 < p := by linarith
  rw [integral_norm_rpow_eq hp0 (memLp_diffQuot hv h e), integral_norm_rpow_eq hp0 hG,
    ← Real.mul_rpow (norm_nonneg _) ENNReal.toReal_nonneg]
  apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ hp0.le
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hG.eLpNorm_ne_top)
    (eLpNorm_diffQuot_le hp hvG hv hG h e)
  simpa only [ENNReal.toReal_mul, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using ht

/-- A coarse weighted Young estimate for `p ≥ 2`, sufficient to make the
cutoff error integrable from two `L^p` functions. -/
theorem rpow_sub_two_mul_sq_le_add {p s t : ℝ} (hp : 2 ≤ p) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s ^ (p - 2) * t ^ 2 ≤ s ^ p + t ^ p := by
  rcases le_total t s with hts | hst
  · by_cases hs0 : s = 0
    · have ht0 : t = 0 := le_antisymm (by simpa [hs0] using hts) ht
      simp [hs0, ht0, Real.zero_rpow (show p ≠ 0 by linarith)]
    have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    calc s ^ (p - 2) * t ^ 2 ≤ s ^ (p - 2) * s ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht hts 2) (Real.rpow_nonneg hs _)
      _ = s ^ p := rpow_sub_two_mul_sq hspos p
      _ ≤ _ := le_add_of_nonneg_right (Real.rpow_nonneg ht _)
  · by_cases ht0 : t = 0
    · simp only [ht0, zero_pow (by decide : 2 ≠ 0), mul_zero]
      positivity
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    calc s ^ (p - 2) * t ^ 2 ≤ t ^ (p - 2) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs hst (by linarith)) (sq_nonneg _)
      _ = t ^ p := rpow_sub_two_mul_sq htpos p
      _ ≤ _ := le_add_of_nonneg_left (Real.rpow_nonneg hs _)

/-- The `p`-energy of the sum of the translated and original gradient norms
has a bound independent of the translation. -/
theorem integral_norm_add_translate_rpow_le {p : ℝ} (hp : 1 < p)
    {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal p)) (t : Euc d) :
    (∫ x, (‖G (x + t)‖ + ‖G x‖) ^ p) ≤ (2 : ℝ) ^ p * ∫ x, ‖G x‖ ^ p := by
  have hp0 : 0 < p := by linarith
  have hshift := hG.comp_measurePreserving (measurePreserving_add_right volume t)
  have hsum := memLp_add_fun hshift.norm hG.norm
  have htri : eLpNorm (fun x => ‖G (x + t)‖ + ‖G x‖) (ENNReal.ofReal p) ≤
      eLpNorm (fun x => ‖G (x + t)‖) (ENNReal.ofReal p) +
        eLpNorm (fun x => ‖G x‖) (ENNReal.ofReal p) := by
    exact eLpNorm_add_le hshift.norm.aestronglyMeasurable hG.norm.aestronglyMeasurable
      (ENNReal.one_le_ofReal.mpr hp.le)
  have hnorms : eLpNorm (fun x => ‖G (x + t)‖ + ‖G x‖) (ENNReal.ofReal p) ≤
      2 * eLpNorm G (ENNReal.ofReal p) := by
    have htrans : eLpNorm (fun x => G (x + t)) (ENNReal.ofReal p) =
        eLpNorm G (ENNReal.ofReal p) :=
      eLpNorm_comp_measurePreserving hG.aestronglyMeasurable
        (measurePreserving_add_right volume t)
    simpa only [eLpNorm_norm, htrans, two_mul] using htri
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) hG.eLpNorm_ne_top) hnorms
  have heq : (∫ x, (‖G (x + t)‖ + ‖G x‖) ^ p) =
      (eLpNorm (fun x => ‖G (x + t)‖ + ‖G x‖) (ENNReal.ofReal p)).toReal ^ p := by
    simpa only [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
      Function.comp_def] using
      integral_norm_rpow_eq hp0 hsum
  rw [heq, integral_norm_rpow_eq hp0 hG,
    ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ENNReal.toReal_nonneg]
  apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ hp0.le
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hreal

/-- The upper flux increment estimate has the same weight after taking difference
quotients, including the convention at step zero. -/
theorem norm_diffQuot_flux_le {p L : ℝ} {F : Euc d → ℝ}
    (hupper : ∀ ξ ζ : Euc d, ‖flux p F ξ - flux p F ζ‖ ≤
      L * (‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖)
    (h : ℝ) (e : Euc d) (G : Euc d → Euc d) (x : Euc d) :
    ‖diffQuot h e (fun y => flux p F (G y)) x‖ ≤
      L * (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) * ‖diffQuot h e G x‖ := by
  rw [norm_diffQuot, norm_diffQuot]
  calc |h|⁻¹ * ‖flux p F (G (x + h • e)) - flux p F (G x)‖
      ≤ |h|⁻¹ * (L * (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) *
          ‖G (x + h • e) - G x‖) :=
        mul_le_mul_of_nonneg_left (hupper _ _) (inv_nonneg.2 (abs_nonneg _))
    _ = _ := by ring

/-- In the degenerate range the weighted cutoff error is integrable, with a
bound by the two unweighted `p`-energies and the squared cutoff derivative bound. -/
theorem weighted_cutoff_error_of_two_le {p B : ℝ} (hp : 2 ≤ p)
    {S q : Euc d → ℝ} {b : Euc d → Euc d}
    (hS : MemLp S (ENNReal.ofReal p)) (hq : MemLp q (ENNReal.ofReal p))
    (hS0 : ∀ x, 0 ≤ S x) (hb : AEStronglyMeasurable b volume)
    (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun x => S x ^ (p - 2) * q x ^ 2 * ‖b x‖ ^ 2) ∧
      (∫ x, S x ^ (p - 2) * q x ^ 2 * ‖b x‖ ^ 2) ≤
        B ^ 2 * ((∫ x, S x ^ p) + ∫ x, ‖q x‖ ^ p) := by
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hSp : Integrable (fun x => S x ^ p) := by
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_of_nonneg (hS0 _)] using
      hS.integrable_norm_rpow hpne ENNReal.ofReal_ne_top
  have hqp : Integrable (fun x => ‖q x‖ ^ p) := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hq.integrable_norm_rpow hpne ENNReal.ofReal_ne_top
  have hmajor : ∀ x, S x ^ (p - 2) * q x ^ 2 * ‖b x‖ ^ 2 ≤
      B ^ 2 * (S x ^ p + ‖q x‖ ^ p) := by
    intro x
    have hy := rpow_sub_two_mul_sq_le_add hp (hS0 x) (norm_nonneg (q x))
    simp only [Real.norm_eq_abs, sq_abs] at hy
    have hsq := pow_le_pow_left₀ (norm_nonneg (b x)) (hB x) 2
    calc S x ^ (p - 2) * q x ^ 2 * ‖b x‖ ^ 2
        ≤ (S x ^ p + ‖q x‖ ^ p) * B ^ 2 := by
          apply mul_le_mul
          · simpa only [Real.norm_eq_abs] using hy
          · exact hsq
          · exact sq_nonneg _
          · exact add_nonneg (Real.rpow_nonneg (hS0 x) _) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := mul_comm _ _
  have hm : AEStronglyMeasurable
      (fun x => S x ^ (p - 2) * q x ^ 2 * ‖b x‖ ^ 2) volume := by
    exact ((hS.aestronglyMeasurable.aemeasurable.pow_const (p - 2)).aestronglyMeasurable.mul
      ((continuous_pow 2).comp_aestronglyMeasurable hq.aestronglyMeasurable)).mul
      ((continuous_pow 2).comp_aestronglyMeasurable hb.norm)
  have hmajint := (hSp.add hqp).const_mul (B ^ 2)
  have hint : Integrable (fun x => S x ^ (p - 2) * q x ^ 2 * ‖b x‖ ^ 2) := by
    refine hmajint.mono' hm (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (hS0 x) _) (sq_nonneg _)) (sq_nonneg _))]
    exact hmajor x
  refine ⟨hint, ?_⟩
  have hi := integral_mono hint hmajint hmajor
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rwa [integral_add hSp hqp] at hi

/-- The cutoff error is bounded independently of the difference-quotient step
when `p ≥ 2`. The solution's global Sobolev data can be obtained by localization. -/
theorem diffQuot_cutoff_error_le_of_two_le {p B : ℝ} (hp : 2 ≤ p)
    {v : Euc d → ℝ} {G : Euc d → Euc d} (hvG : HasWeakGradient v G)
    (hv : MemLp v (ENNReal.ofReal p)) (hG : MemLp G (ENNReal.ofReal p))
    (h : ℝ) (e : Euc d) {b : Euc d → Euc d}
    (hb : AEStronglyMeasurable b volume) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun x => (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) *
      diffQuot h e v x ^ 2 * ‖b x‖ ^ 2) ∧
      (∫ x, (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) * diffQuot h e v x ^ 2 * ‖b x‖ ^ 2) ≤
        B ^ 2 * ((2 : ℝ) ^ p + ‖e‖ ^ p) * ∫ x, ‖G x‖ ^ p := by
  have hp1 : 1 < p := by linarith
  have hshift := hG.comp_measurePreserving (measurePreserving_add_right volume (h • e))
  obtain ⟨hi, hbound⟩ := weighted_cutoff_error_of_two_le hp
    (memLp_add_fun hshift.norm hG.norm) (memLp_diffQuot hv h e)
    (fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)) hb hB
  refine ⟨hi, hbound.trans ?_⟩
  have h1 := integral_norm_add_translate_rpow_le hp1 hG (h • e)
  have h2 := integral_norm_diffQuot_rpow_le hp1 hvG hv hG h e
  calc B ^ 2 * ((∫ x, (‖G (x + h • e)‖ + ‖G x‖) ^ p) + ∫ x, ‖diffQuot h e v x‖ ^ p)
      ≤ B ^ 2 * ((2 : ℝ) ^ p * (∫ x, ‖G x‖ ^ p) + ‖e‖ ^ p * ∫ x, ‖G x‖ ^ p) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (sq_nonneg _)
    _ = _ := by ring

/-- Pointwise absorption of the squared-cutoff cross term. This uses both flux
bounds and makes no division by the possibly zero or singular weight. -/
theorem cutoff_flux_cross_absorption {c L w : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hw : 0 ≤ w) {a z b : Euc d}
    (hlower : c * (w * ‖z‖ ^ 2) ≤ ⟪a, z⟫)
    (hupper : ‖a‖ ≤ L * w * ‖z‖) (η q : ℝ) :
    |q * ⟪a, (2 * η) • b⟫| ≤
      (1 / 2 : ℝ) * (η ^ 2 * ⟪a, z⟫) +
        (2 * L ^ 2 / c) * (w * q ^ 2 * ‖b‖ ^ 2) := by
  have hinner : |⟪a, b⟫| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
  have hnorm : |q| * (2 * |η|) * |⟪a, b⟫| ≤
      |q| * (2 * |η|) * (L * w * ‖z‖ * ‖b‖) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hinner.trans (mul_le_mul_of_nonneg_right hupper (norm_nonneg _))
  have hy := weighted_quadratic_young hc hw (|η| * ‖z‖) (L * |q| * ‖b‖)
  have hm := mul_le_mul_of_nonneg_left hlower (sq_nonneg η)
  have hmain : |q| * (2 * |η|) * (L * w * ‖z‖ * ‖b‖) ≤
      (1 / 2 : ℝ) * (η ^ 2 * ⟪a, z⟫) +
        (2 * L ^ 2 / c) * (w * q ^ 2 * ‖b‖ ^ 2) := by
    calc |q| * (2 * |η|) * (L * w * ‖z‖ * ‖b‖)
        = 2 * w * (|η| * ‖z‖) * (L * |q| * ‖b‖) := by ring
      _ ≤ _ := hy
      _ = (1 / 2 : ℝ) * (η ^ 2 * (c * (w * ‖z‖ ^ 2))) +
          (2 * L ^ 2 / c) * (w * q ^ 2 * ‖b‖ ^ 2) := by
            simp only [mul_pow, sq_abs]
            ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num)) le_rfl
  calc |q * ⟪a, (2 * η) • b⟫|
      = |q| * (2 * |η|) * |⟪a, b⟫| := by
        rw [real_inner_smul_right, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring
    _ ≤ _ := hnorm.trans hmain

/-- Integrating the cutoff cross-term estimate and absorbing half of the energy.
Integrability is explicit, so the identity cannot be satisfied through the Bochner
integral's convention for nonintegrable functions. -/
theorem integral_flux_energy_le_of_cutoff_balance {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    {η q w : Euc d → ℝ} {a z b : Euc d → Euc d}
    (hw : ∀ x, 0 ≤ w x)
    (hlower : ∀ x, c * (w x * ‖z x‖ ^ 2) ≤ ⟪a x, z x⟫)
    (hupper : ∀ x, ‖a x‖ ≤ L * w x * ‖z x‖)
    (henergy : Integrable (fun x => η x ^ 2 * ⟪a x, z x⟫))
    (hcross : Integrable (fun x => q x * ⟪a x, (2 * η x) • b x⟫))
    (herror : Integrable (fun x => w x * q x ^ 2 * ‖b x‖ ^ 2))
    (hbalance : (∫ x, η x ^ 2 * ⟪a x, z x⟫) =
      -(∫ x, q x * ⟪a x, (2 * η x) • b x⟫)) :
    (∫ x, η x ^ 2 * ⟪a x, z x⟫) ≤
      (4 * L ^ 2 / c) * ∫ x, w x * q x ^ 2 * ‖b x‖ ^ 2 := by
  have hpt : ∀ x, -(q x * ⟪a x, (2 * η x) • b x⟫) ≤
      (1 / 2 : ℝ) * (η x ^ 2 * ⟪a x, z x⟫) +
        (2 * L ^ 2 / c) * (w x * q x ^ 2 * ‖b x‖ ^ 2) := fun x =>
    (neg_le_abs _).trans
      (cutoff_flux_cross_absorption hc hL (hw x) (hlower x) (hupper x) (η x) (q x))
  have hint := integral_mono hcross.neg
    ((henergy.const_mul (1 / 2)).add (herror.const_mul (2 * L ^ 2 / c))) hpt
  simp only [Pi.neg_apply, Pi.add_apply] at hint
  rw [integral_neg, integral_add (henergy.const_mul _) (herror.const_mul _),
    integral_const_mul, integral_const_mul, ← hbalance] at hint
  have hconst : (4 * L ^ 2 / c) = 2 * (2 * L ^ 2 / c) := by ring
  rw [hconst]
  linarith

/-- Squared-cutoff Caccioppoli for a homogeneous flux solution. The error integral
still contains the natural weight; its uniform control is a separate regularity step. -/
theorem IsFluxSolutionOn.integral_squared_cutoff_flux_energy_le
    {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {v : Euc d → ℝ} {G : Euc d → Euc d} {x₀ : Euc d} {r₀ : ℝ}
    (hsol : IsFluxSolutionOn p F v G 0 x₀ r₀)
    (hvG : HasWeakGradient v G) (hv : MemLp v (ENNReal.ofReal p))
    (hG : MemLp G (ENNReal.ofReal p)) (h : ℝ) (e : Euc d)
    {U : Set (Euc d)} (hU : IsOpen U) (hUB : U ⊆ Metric.ball x₀ r₀)
    (hUh : ∀ y ∈ U, y + h • e ∈ Metric.ball x₀ r₀)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) {A B : ℝ}
    (hA : ∀ y, |η y| ≤ A) (hB : ∀ y, ‖gradient η y‖ ≤ B)
    {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hmono : ∀ ξ ζ : Euc d, c * ((‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ ^ 2)
      ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫)
    (hupper : ∀ ξ ζ : Euc d, ‖flux p F ξ - flux p F ζ‖ ≤
      L * (‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖)
    (herror : Integrable (fun y =>
      (‖G (y + h • e)‖ + ‖G y‖) ^ (p - 2) * diffQuot h e v y ^ 2 *
        ‖gradient η y‖ ^ 2)) :
    (∫ y, η y ^ 2 *
      ⟪diffQuot h e (fun z => flux p F (G z)) y, diffQuot h e G y⟫) ≤
      (4 * L ^ 2 / c) * ∫ y,
        (‖G (y + h • e)‖ + ‖G y‖) ^ (p - 2) * diffQuot h e v y ^ 2 *
          ‖gradient η y‖ ^ 2 := by
  have hA0 : 0 ≤ A := (abs_nonneg (η 0)).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg (gradient η 0)).trans (hB 0)
  have hη₂ : ContDiff ℝ ∞ (fun y => η y ^ 2) := hη.pow 2
  have hη₂s : HasCompactSupport (fun y => η y ^ 2) := by
    refine HasCompactSupport.intro hηs fun y hy => ?_
    rw [image_eq_zero_of_notMem_tsupport hy]
    norm_num
  have hη₂U : tsupport (fun y => η y ^ 2) ⊆ U := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := η) (g := η)).trans hηU
  have hgrad : ∀ y, gradient (fun z => η z ^ 2) y = (2 * η y) • gradient η y := by
    intro y
    simpa using gradient_pow_apply (hη.differentiable (by simp) y) 2
  have hA₂ : ∀ y, |η y ^ 2| ≤ A ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hA y) 2
  have hB₂ : ∀ y, ‖gradient (fun z => η z ^ 2) y‖ ≤ 2 * A * B := by
    intro y
    rw [hgrad y, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hA y) (by norm_num)) (hB y)
      (norm_nonneg _) (by positivity)
  have hbalance := hsol.integral_diffQuot_flux_energy_balance hp hF hvG hv hG h e
    hU hUB hUh hη₂ hη₂s hη₂U hA₂ hB₂
  simp only [hgrad] at hbalance
  have henergy : Integrable (fun y => η y ^ 2 *
      ⟪diffQuot h e (fun z => flux p F (G z)) y, diffQuot h e G y⟫) :=
    (integrable_diffQuot_flux_energy hp hF hG h e).bdd_mul
      hη₂.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hA₂ y)
  have htest : MemLp (fun y => diffQuot h e v y •
      gradient (fun z => η z ^ 2) y) (ENNReal.ofReal p) := by
    have hm : AEStronglyMeasurable (gradient (fun z => η z ^ 2)) volume :=
      (continuous_gradient (hη₂.of_le (by simp))).aestronglyMeasurable
    refine (memLp_diffQuot hv h e).of_le_mul (c := 2 * A * B)
      ((memLp_diffQuot hv h e).aestronglyMeasurable.smul hm)
      (Eventually.of_forall fun y => ?_)
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB₂ y) (norm_nonneg _)
  have hcross : Integrable (fun y => diffQuot h e v y *
      ⟪diffQuot h e (fun z => flux p F (G z)) y, (2 * η y) • gradient η y⟫) := by
    simpa only [hgrad, real_inner_smul_right] using
      integrable_inner_of_memLp hp (memLp_diffQuot (hF.memLp_flux hp hG) h e) htest
  apply integral_flux_energy_le_of_cutoff_balance hc hL
      (fun y => Real.rpow_nonneg (by positivity) _) _
      (fun y => norm_diffQuot_flux_le hupper h e G y) henergy hcross herror hbalance
  intro y
  have hh := mul_le_mul_of_nonneg_left
    (rpow_mul_normSq_diffQuot_le_inner_diffQuot_flux hc hmono h e G y) hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hh

end Komlos.Literature
