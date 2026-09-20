import Komlos.Literature.PLaplacian.DiffQuotLocalization

/-!
# Proved infrastructure for nonlinear difference-quotient estimates

This file contains the difference-quotient algebra, weighted flux monotonicity, honest local
weak-solution structure, Sobolev test upgrade, and exact homogeneous cutoff energy identities.
`IsFluxSolutionOn.exists_localized` supplies global Sobolev data agreeing with a solution on
any smaller closed ball. It uses the local potential integrability and cutoff constructions in
`DiffQuotLocalization.lean` for both classical and distributional gradient fields.

All declarations here are proved independently of the unresolved gradient regularity theorem
in `DiffQuotCaccioppoli.lean`. Separating them lets energy estimates use this infrastructure
without importing that theorem.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Difference quotients -/

/-- The **difference quotient** `Δ_h^e f (x) = (f(x + h e) - f(x)) / h` in the direction `e` at
step `h`.  Difference quotients are the substitute for derivatives in the second-order
Caccioppoli estimate: a bound on `∫ ‖Δ_h^e f‖²` uniform in `h` is exactly an `L²` bound on the
weak directional derivative `∂_e f`, and it is available for solutions that are a priori only
`W^{1,p}`. -/
noncomputable def diffQuot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (e : Euc d) (f : Euc d → E) : Euc d → E :=
  fun x => h⁻¹ • (f (x + h • e) - f x)

section DiffQuot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem diffQuot_apply (h : ℝ) (e : Euc d) (f : Euc d → E) (x : Euc d) :
    diffQuot h e f x = h⁻¹ • (f (x + h • e) - f x) := rfl

/-- The difference quotient of a constant vanishes. -/
theorem diffQuot_const (h : ℝ) (e : Euc d) (c : E) :
    diffQuot h e (fun _ : Euc d => c) = 0 := by
  funext x
  simp [diffQuot_apply]

/-- Difference quotients are additive in the function. -/
theorem diffQuot_add (h : ℝ) (e : Euc d) (f f' : Euc d → E) :
    diffQuot h e (f + f') = diffQuot h e f + diffQuot h e f' := by
  funext x
  show (h⁻¹ : ℝ) • ((f + f') (x + h • e) - (f + f') x)
      = h⁻¹ • (f (x + h • e) - f x) + h⁻¹ • (f' (x + h • e) - f' x)
  simp only [Pi.add_apply]
  rw [← smul_add]
  congr 1
  abel

/-- The norm of a difference quotient. -/
theorem norm_diffQuot (h : ℝ) (e : Euc d) (f : Euc d → E) (x : Euc d) :
    ‖diffQuot h e f x‖ = |h|⁻¹ * ‖f (x + h • e) - f x‖ := by
  rw [diffQuot_apply, norm_smul, norm_inv, Real.norm_eq_abs]

/-- For real-valued functions the difference quotient is the usual quotient. -/
theorem diffQuot_real (h : ℝ) (e : Euc d) (f : Euc d → ℝ) (x : Euc d) :
    diffQuot h e f x = (f (x + h • e) - f x) / h := by
  rw [diffQuot_apply, smul_eq_mul]
  ring

/-- Translation and scalar multiplication preserve `L^p` membership of a difference
quotient; no estimate uniform in the step is asserted here. -/
theorem memLp_diffQuot {p : ℝ≥0∞} {f : Euc d → E}
    (hf : MemLp f p volume) (h : ℝ) (e : Euc d) : MemLp (diffQuot h e f) p volume := by
  change MemLp (h⁻¹ • ((fun x => f (x + h • e)) - f)) p volume
  exact ((hf.comp_measurePreserving
    (measurePreserving_add_right volume (h • e))).sub hf).const_smul h⁻¹

end DiffQuot

/-- Difference quotients commute with the weak gradient. -/
theorem HasWeakGradient.diffQuot {v : Euc d → ℝ} {G : Euc d → Euc d}
    (hv : HasWeakGradient v G) (h : ℝ) (e : Euc d) :
    HasWeakGradient (diffQuot h e v) (diffQuot h e G) := by
  change HasWeakGradient (h⁻¹ • ((fun x => v (x + h • e)) - v))
    (h⁻¹ • ((fun x => G (x + h • e)) - G))
  simpa only [sub_neg_eq_add] using ((hv.comp_sub (-(h • e))).sub hv).smul h⁻¹

/-- A smooth cutoff times a Sobolev difference quotient is an admissible Sobolev test
function.  Its weak gradient is the product-rule field, and vanishes off the cutoff support.
This is the admissibility input for testing a difference-quotient equation with
`η² Δ_h^e v`; the caller can use `η²` as the cutoff in this statement. -/
theorem memW0_cutoff_diffQuot {p : ℝ} {v : Euc d → ℝ} {G : Euc d → Euc d}
    (hvG : HasWeakGradient v G) (hv : MemLp v (ENNReal.ofReal p))
    (hG : MemLp G (ENNReal.ofReal p)) (h : ℝ) (e : Euc d)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) {A B : ℝ}
    (hA : ∀ y, |η y| ≤ A) (hB : ∀ y, ‖gradient η y‖ ≤ B) :
    MemW0 p (tsupport η) (fun y => η y * diffQuot h e v y) ∧
      weakGrad (fun y => η y * diffQuot h e v y) =ᵐ[volume]
        (fun y => η y • diffQuot h e G y + diffQuot h e v y • gradient η y) ∧
      (∀ᵐ y, y ∉ tsupport η → weakGrad (fun z => η z * diffQuot h e v z) y = 0) := by
  have hbase : MemW0 p (Set.univ : Set (Euc d)) (diffQuot h e v) :=
    ⟨memLp_diffQuot hv h e, Eventually.of_forall (fun _ hy => (hy (Set.mem_univ _)).elim),
      ⟨diffQuot h e G, hvG.diffQuot h e, memLp_diffQuot hG h e⟩⟩
  obtain ⟨hmem, hweak⟩ := hbase.contDiff_mul hη hA hB
  have hgrad : weakGrad (fun y => η y * diffQuot h e v y) =ᵐ[volume]
      (fun y => η y • diffQuot h e G y + diffQuot h e v y • gradient η y) := by
    filter_upwards [hweak, (hvG.diffQuot h e).weakGrad_ae_eq] with y hy hGy
    simpa only [hGy] using hy
  refine ⟨⟨hmem.memLp, ?_, hmem.exists_weakGradient⟩, hgrad, ?_⟩
  · exact Eventually.of_forall fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · filter_upwards [hgrad] with y hy hyη
    rw [hy, image_eq_zero_of_notMem_tsupport hyη, gradient_eq_zero_of_notMem_tsupport hyη]
    simp

/-- **Summation by parts for difference quotients**: `∫ (Δ_h^e f) ψ = -∫ f (Δ_{-h}^e ψ)`.

This is the discrete analogue of the integration by parts `∫ (∂_e f) ψ = -∫ f (∂_e ψ)`, and it is
the step that moves a difference quotient off the solution and onto the test function in the
second-order Caccioppoli estimate.  Only the translation invariance of Lebesgue measure is used.
The two integrability hypotheses are the honest ones: Lean gives a divergent integral the junk
value `0`, so without them the identity would be a statement about junk values. -/
theorem integral_diffQuot_mul_eq_neg (h : ℝ) (e : Euc d) (f ψ : Euc d → ℝ)
    (hfψ : Integrable fun x => f x * ψ x)
    (hfψ' : Integrable fun x => f x * ψ (x + (-h) • e)) :
    ∫ x, diffQuot h e f x * ψ x = -∫ x, f x * diffQuot (-h) e ψ x := by
  have hcancel : ∀ x : Euc d, x + h • e + (-h) • e = x := by
    intro x
    module
  have hI1 : Integrable fun x => f (x + h • e) * ψ x := by
    refine (hfψ'.comp_add_right (h • e)).congr (Eventually.of_forall fun x => ?_)
    show f (x + h • e) * ψ (x + h • e + (-h) • e) = f (x + h • e) * ψ x
    rw [hcancel]
  have hshift : ∫ x, f (x + h • e) * ψ x = ∫ x, f x * ψ (x + (-h) • e) := by
    rw [← integral_add_right_eq_self (fun y => f y * ψ (y + (-h) • e)) (h • e)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show f (x + h • e) * ψ x = f (x + h • e) * ψ (x + h • e + (-h) • e)
    rw [hcancel]
  have hA : ∀ x : Euc d, diffQuot h e f x * ψ x
      = h⁻¹ * (f (x + h • e) * ψ x) - h⁻¹ * (f x * ψ x) := by
    intro x
    simp only [diffQuot_apply, smul_eq_mul]
    ring
  have hB : ∀ x : Euc d, f x * diffQuot (-h) e ψ x
      = h⁻¹ * (f x * ψ x) - h⁻¹ * (f x * ψ (x + (-h) • e)) := by
    intro x
    simp only [diffQuot_apply, smul_eq_mul, ← neg_inv]
    ring
  have e1 : (∫ x, diffQuot h e f x * ψ x)
      = ∫ x, (h⁻¹ * (f (x + h • e) * ψ x) - h⁻¹ * (f x * ψ x)) :=
    integral_congr_ae (Eventually.of_forall hA)
  have e2 : (∫ x, f x * diffQuot (-h) e ψ x)
      = ∫ x, (h⁻¹ * (f x * ψ x) - h⁻¹ * (f x * ψ (x + (-h) • e))) :=
    integral_congr_ae (Eventually.of_forall hB)
  rw [e1, e2, integral_sub (hI1.const_mul h⁻¹) (hfψ.const_mul h⁻¹),
    integral_sub (hfψ.const_mul h⁻¹) (hfψ'.const_mul h⁻¹)]
  simp only [integral_const_mul]
  rw [hshift]
  ring

/-! ### Weighted strong monotonicity of the flux, uniformly across the degeneracy -/

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- **Weighted strong monotonicity of the flux** (DiBenedetto 1983, Nonlinear Anal. **7**,
Lemma 1; Tolksdorf 1984, J. Differential Equations **51**, Lemma 1; Lieberman 1991, Comm. PDE
**16**, (1.4)): there is `c > 0`, depending only on `p`, `F` and `d`, with

`c (‖ξ‖ + ‖ζ‖)^{p-2} ‖ξ - ζ‖² ≤ ⟪a(ξ) - a(ζ), ξ - ζ⟫`   for all `ξ ζ : Euc d`.

This is the *integrated* form of the scale-invariant ellipticity
`IsSmoothStrictNorm.exists_pos_rpow_mul_normSq_le_inner_fderiv_flux` of `A = Da`, and it is the
single place where the nonlinearity of the flux enters the second-order Caccioppoli estimate: it
converts the flux energy `⟪Δ_h^e a(∇v), Δ_h^e ∇v⟫` produced by the difference-quotient argument
into the weighted square `(‖∇v(· + he)‖ + ‖∇v‖)^{p-2} ‖Δ_h^e ∇v‖²` of
`exists_degiorgi_uniform_gradient_bounds` (a); see
`rpow_mul_normSq_diffQuot_le_inner_diffQuot_flux`.
The weight `(‖ξ‖ + ‖ζ‖)^{p-2}` is the same on both sides of the two-sided bounds, which is why the
resulting De Giorgi class does not degenerate.

For `1 < p < 2` this is `IsSmoothStrictNorm.exists_pos_mul_normSq_le_inner_flux_sub`, extended to
the excluded configuration `ξ = ζ = 0` (where both sides vanish).  For `p ≥ 2` the shape
`c ‖ξ - ζ‖^p ≤ ⟪a(ξ) - a(ζ), ξ - ζ⟫` of `exists_pos_norm_rpow_le_inner_flux_sub` is strictly
*weaker* (since `‖ξ - ζ‖ ≤ ‖ξ‖ + ‖ζ‖` and `p - 2 ≥ 0`), so the segment argument has to be redone:
on one of the two subintervals `[0, 1/8]`, `[7/8, 1]` — the first if `‖ξ‖ ≤ ‖ζ‖`, the second
otherwise — the segment `t ↦ ζ + t(ξ - ζ)` stays at distance at least `3(‖ξ‖ + ‖ζ‖)/8` from the
origin, because the two lower bounds `(7‖ζ‖ - ‖ξ‖)/8` and `(7‖ξ‖ - ‖ζ‖)/8` valid there average to
exactly `3(‖ξ‖ + ‖ζ‖)/8`. -/
theorem exists_pos_weighted_normSq_le_inner_flux_sub {p : ℝ} (hp : 1 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ ζ : Euc d,
      c * ((‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ ^ 2) ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ := by
  by_cases hp2 : p < 2
  · obtain ⟨c, hc, hkey⟩ := hF.exists_pos_mul_normSq_le_inner_flux_sub hp hp2
    refine ⟨c, hc, fun ξ ζ => ?_⟩
    by_cases h00 : ξ = 0 ∧ ζ = 0
    · rw [h00.1, h00.2]
      simp
    · refine hkey ξ ζ ?_
      intro hc'
      simp only [Prod.mk.injEq] at hc'
      exact h00 hc'
  · have hp2' : (0 : ℝ) ≤ p - 2 := by linarith [not_lt.1 hp2]
    rcases isEmpty_or_nonempty (Fin d) with hd | hd
    · refine ⟨1, one_pos, fun ξ ζ => ?_⟩
      have hξζ : ξ = ζ := Subsingleton.elim _ _
      rw [hξζ]
      simp
    haveI : Nonempty (Fin d) := hd
    obtain ⟨c₀, hc₀, hell⟩ := hF.exists_pos_rpow_mul_normSq_le_inner_fderiv_flux hp
    obtain ⟨c₁, hc₁, hc₁F⟩ := hF.exists_pos_mul_norm_le
    obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = ((3 : ℝ) / 8) ^ (p - 2) := ⟨_, rfl⟩
    have hκ : 0 < κ := by
      rw [hκ_def]
      exact Real.rpow_pos_of_pos (by norm_num) _
    refine ⟨min (c₀ * κ / 8) ((2 : ℝ) ^ (1 - p) * c₁ ^ p),
      lt_min (div_pos (mul_pos hc₀ hκ) (by norm_num))
        (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
          (Real.rpow_pos_of_pos hc₁ _)), fun ξ ζ => ?_⟩
    rcases eq_or_ne ξ ζ with rfl | hne
    · simp
    have hr : 0 < ‖ξ - ζ‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hne
    have hrp : (0 : ℝ) ≤ ‖ξ - ζ‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
    have hS : 0 < ‖ξ‖ + ‖ζ‖ := lt_of_lt_of_le hr (norm_sub_le ξ ζ)
    have hSp : (0 : ℝ) ≤ (‖ξ‖ + ‖ζ‖) ^ (p - 2) := Real.rpow_nonneg hS.le _
    by_cases h0 : (0 : Euc d) ∈ segment ℝ ζ ξ
    · obtain ⟨a, b, ha, hb, hab, hξv, hζv⟩ := exists_collinear_of_zero_mem_segment h0
      have hnξ : ‖ξ‖ = a * ‖ξ - ζ‖ := by
        conv_lhs => rw [hξv]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      have hnζ : ‖ζ‖ = b * ‖ξ - ζ‖ := by
        conv_lhs => rw [hζv]
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      have hsum : ‖ξ‖ + ‖ζ‖ = ‖ξ - ζ‖ := by
        rw [hnξ, hnζ, ← add_mul, hab, one_mul]
      have hkey := hF.le_inner_flux_sub_of_collinear hp hc₁ hc₁F ha hb hab (ξ - ζ)
      rw [← hξv, ← hζv] at hkey
      refine le_trans ?_ hkey
      rw [hsum, rpow_sub_two_mul_sq hr p]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) hrp
    · have hm0 : (0 : ℝ) ≤ (3 * (‖ξ‖ + ‖ζ‖) / 8) ^ (p - 2) :=
        Real.rpow_nonneg (by positivity) _
      have hmain : (1 / 8 : ℝ) * (c₀ * ((3 * (‖ξ‖ + ‖ζ‖) / 8) ^ (p - 2) * ‖ξ - ζ‖ ^ 2))
          ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ := by
        rcases le_total ‖ξ‖ ‖ζ‖ with hAB | hAB
        · have hmb : ∀ t ∈ Icc (0 : ℝ) (1 / 8),
              (3 * (‖ξ‖ + ‖ζ‖) / 8) ^ (p - 2) ≤ ‖ζ + t • (ξ - ζ)‖ ^ (p - 2) := by
            intro t ht
            have h1 : ‖ζ‖ - |t| * ‖ξ - ζ‖ ≤ ‖ζ + t • (ξ - ζ)‖ :=
              norm_sub_le_norm_add_smul_sub_left ζ ξ t
            rw [abs_of_nonneg ht.1] at h1
            have h4 := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (ξ - ζ))
            have h5 := norm_sub_le ξ ζ
            have h2 : 3 * (‖ξ‖ + ‖ζ‖) / 8 ≤ ‖ζ + t • (ξ - ζ)‖ := by linarith
            exact Real.rpow_le_rpow (by positivity) h2 hp2'
          have hbound := hF.le_inner_flux_sub_of_segment hc₀.le hm0 hell h0
            (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 8)
            (by norm_num : (1 / 8 : ℝ) ≤ 1) hmb
          rwa [sub_zero] at hbound
        · have hmb : ∀ t ∈ Icc (7 / 8 : ℝ) 1,
              (3 * (‖ξ‖ + ‖ζ‖) / 8) ^ (p - 2) ≤ ‖ζ + t • (ξ - ζ)‖ ^ (p - 2) := by
            intro t ht
            have h1 : ‖ξ‖ - |1 - t| * ‖ξ - ζ‖ ≤ ‖ζ + t • (ξ - ζ)‖ :=
              norm_sub_le_norm_add_smul_sub_right ζ ξ t
            rw [abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)] at h1
            have h4 := mul_le_mul_of_nonneg_right
              (by linarith [ht.1] : (1 : ℝ) - t ≤ 1 / 8) (norm_nonneg (ξ - ζ))
            have h5 := norm_sub_le ξ ζ
            have h2 : 3 * (‖ξ‖ + ‖ζ‖) / 8 ≤ ‖ζ + t • (ξ - ζ)‖ := by linarith
            exact Real.rpow_le_rpow (by positivity) h2 hp2'
          have hbound := hF.le_inner_flux_sub_of_segment hc₀.le hm0 hell h0
            (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (7 / 8 : ℝ) ≤ 1)
            (le_refl (1 : ℝ)) hmb
          have he : (1 : ℝ) - 7 / 8 = 1 / 8 := by norm_num
          rwa [he] at hbound
      refine le_trans ?_ hmain
      have h1 : (3 * (‖ξ‖ + ‖ζ‖) / 8 : ℝ) ^ (p - 2) = (‖ξ‖ + ‖ζ‖) ^ (p - 2) * κ := by
        rw [show (3 * (‖ξ‖ + ‖ζ‖) / 8 : ℝ) = (‖ξ‖ + ‖ζ‖) * (3 / 8) from by ring, hκ_def,
          ← Real.mul_rpow hS.le (by norm_num : (0 : ℝ) ≤ 3 / 8)]
      have harith : (1 / 8 : ℝ) * (c₀ * ((3 * (‖ξ‖ + ‖ζ‖) / 8) ^ (p - 2) * ‖ξ - ζ‖ ^ 2))
          = c₀ * κ / 8 * ((‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ ^ 2) := by
        rw [h1]
        ring
      rw [harith]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (mul_nonneg hSp (sq_nonneg _))

end IsSmoothStrictNorm

/-- **The weighted difference-quotient energy density is controlled by the flux energy density.**
Pointwise, for every step `h`, direction `e` and field `G`,

`(‖G(x + he)‖ + ‖G x‖)^{p-2} ‖Δ_h^e G x‖² ≤ c⁻¹ ⟪Δ_h^e (a ∘ G) x, Δ_h^e G x⟫`,

whenever `c` is a constant of weighted strong monotonicity
(`IsSmoothStrictNorm.exists_pos_weighted_normSq_le_inner_flux_sub`).  Both sides carry the same
factor `h⁻²`, so the inequality is exactly the monotonicity inequality at the pair
`(G(x + he), G x)`; this is the step that turns the *flux* energy produced by the
difference-quotient Caccioppoli argument into the weighted second-order bound
`exists_degiorgi_uniform_gradient_bounds` (a). -/
theorem rpow_mul_normSq_diffQuot_le_inner_diffQuot_flux {p c : ℝ} (hc : 0 < c)
    {F : Euc d → ℝ}
    (hmono : ∀ ξ ζ : Euc d, c * ((‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ ^ 2)
      ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫)
    (h : ℝ) (e : Euc d) (G : Euc d → Euc d) (x : Euc d) :
    (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) * ‖diffQuot h e G x‖ ^ 2
      ≤ c⁻¹ * ⟪diffQuot h e (fun y => flux p F (G y)) x, diffQuot h e G x⟫ := by
  have hkey : (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) * ‖G (x + h • e) - G x‖ ^ 2
      ≤ c⁻¹ * ⟪flux p F (G (x + h • e)) - flux p F (G x), G (x + h • e) - G x⟫ := by
    have h2 := mul_le_mul_of_nonneg_left (hmono (G (x + h • e)) (G x)) (inv_nonneg.2 hc.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h2
  have hq : diffQuot h e G x = h⁻¹ • (G (x + h • e) - G x) := rfl
  have hqf : diffQuot h e (fun y => flux p F (G y)) x
      = h⁻¹ • (flux p F (G (x + h • e)) - flux p F (G x)) := rfl
  rw [hq, hqf, norm_smul, real_inner_smul_left, real_inner_smul_right]
  have hnorm : (‖(h⁻¹ : ℝ)‖ * ‖G (x + h • e) - G x‖) ^ 2
      = h⁻¹ * h⁻¹ * ‖G (x + h • e) - G x‖ ^ 2 := by
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [hnorm]
  have hs : (0 : ℝ) ≤ h⁻¹ * h⁻¹ := mul_self_nonneg _
  calc (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) * (h⁻¹ * h⁻¹ * ‖G (x + h • e) - G x‖ ^ 2)
      = h⁻¹ * h⁻¹ * ((‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) * ‖G (x + h • e) - G x‖ ^ 2) := by
        ring
    _ ≤ h⁻¹ * h⁻¹ *
        (c⁻¹ * ⟪flux p F (G (x + h • e)) - flux p F (G x), G (x + h • e) - G x⟫) :=
        mul_le_mul_of_nonneg_left hkey hs
    _ = c⁻¹ * (h⁻¹ * (h⁻¹ *
        ⟪flux p F (G (x + h • e)) - flux p F (G x), G (x + h • e) - G x⟫)) := by ring

/-! ### The hypotheses of the degenerate gradient theory -/

/-- **`G` is the gradient field of the potential `v` on `U`.**  Two forms are admitted, because
the two consumers of this theory produce different ones and both express `G = ∇v` on `U`:

* the classical form, `v` differentiable on `U` with `∇v = G` there (this is what a `C¹`
  solution supplies — `IsUnitBallSolution.differentiableAt`), and
* the distributional form, `G` a weak gradient of `v` (this is what a `W^{1,p}` solution
  supplies — `MemW0.hasWeakGradient` / `hasWeakGradient_weakGrad`).

That `G` is a *gradient* is not decoration: the whole De Giorgi theory below rests on the fact
that the components `∂_i v` solve the differentiated equation `div (A(∇v) ∇∂_i v) = ∂_i g`, which
is false for a general vector field. -/
def IsGradientFieldOn (v : Euc d → ℝ) (G : Euc d → Euc d) (U : Set (Euc d)) : Prop :=
  (∀ y ∈ U, DifferentiableAt ℝ v y ∧ gradient v y = G y) ∨ HasWeakGradient v G

/-- A weak gradient is a gradient field on every set. -/
theorem IsGradientFieldOn.of_hasWeakGradient {v : Euc d → ℝ} {G : Euc d → Euc d}
    (h : HasWeakGradient v G) (U : Set (Euc d)) : IsGradientFieldOn v G U := Or.inr h

/-- A classical gradient on `U` is a gradient field on `U`. -/
theorem IsGradientFieldOn.of_differentiableOn {v : Euc d → ℝ} {G : Euc d → Euc d}
    {U : Set (Euc d)} (h : ∀ y ∈ U, DifferentiableAt ℝ v y ∧ gradient v y = G y) :
    IsGradientFieldOn v G U := Or.inl h

/-- **A weak solution of `div a(G) = g` on the ball `B(x₀, r₀)`, with `G = ∇v`.**

This is the common hypothesis of the two degenerate gradient estimates.  The weak equation is
required only against *smooth* test functions compactly supported in the ball — the smallest
admissible class — so that both consumers can supply it: the `W^{1,p}` consumer by
`memW0_of_contDiff` and `weakGrad_ae_eq_gradient`, the `C¹` consumer directly.

Taking `g = 0` gives the homogeneous equation `div a(∇v) = 0`; taking
`g = fun y => μ ϕ(y)^{p-1}` gives the eigenvalue-type equation `-div a(∇ϕ) = μ ϕ^{p-1}`.

The closed-ball `L^p` energy is required explicitly.  The weak integral identity alone does
not express a distributional equation unless the flux pairing is integrable: Lean assigns a
nonintegrable Bochner integral the value `0`.  Both consumers supply this energy hypothesis,
from `MemW0.memLp_weakGrad` in the Sobolev case and compact gradient continuity in the
classical case.  The forcing also has an explicit integrability field; together with its
pointwise bound, this gives conjugate integrability for the Sobolev test-function upgrade. -/
structure IsFluxSolutionOn (p : ℝ) (F : Euc d → ℝ) (v : Euc d → ℝ) (G : Euc d → Euc d)
    (g : Euc d → ℝ) (x₀ : Euc d) (r₀ : ℝ) : Prop where
  /-- `G` is the gradient of the potential `v` on the ball. -/
  gradientField : IsGradientFieldOn v G (Metric.ball x₀ r₀)
  /-- `G` is integrable on the closed ball. -/
  integrableOn : IntegrableOn G (Metric.closedBall x₀ r₀)
  /-- The finite `p`-energy required by the weak-solution regularity theory. -/
  integrableOn_energy : IntegrableOn (fun y => ‖G y‖ ^ p) (Metric.closedBall x₀ r₀)
  /-- The forcing is integrable, so its weak pairing has no nonmeasurability junk values. -/
  integrableOn_rhs : IntegrableOn g (Metric.closedBall x₀ r₀)
  /-- The weak equation `∫ ⟪a(G), ∇ψ⟫ = ∫ g ψ` against smooth test functions. -/
  weak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Metric.ball x₀ r₀ →
    ∫ y, ⟪flux p F (G y), gradient ψ y⟫ = ∫ y, g y * ψ y

/-- The **homogeneous** case of `IsFluxSolutionOn`: the right-hand side is the zero function. -/
theorem isFluxSolutionOn_zero {p : ℝ} {F : Euc d → ℝ} {v : Euc d → ℝ} {G : Euc d → Euc d}
    {x₀ : Euc d} {r₀ : ℝ} (hgrad : IsGradientFieldOn v G (Metric.ball x₀ r₀))
    (hint : IntegrableOn G (Metric.closedBall x₀ r₀))
    (henergy : IntegrableOn (fun y => ‖G y‖ ^ p) (Metric.closedBall x₀ r₀))
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball x₀ r₀ → ∫ y, ⟪flux p F (G y), gradient ψ y⟫ = 0) :
    IsFluxSolutionOn p F v G 0 x₀ r₀ where
  gradientField := hgrad
  integrableOn := hint
  integrableOn_energy := henergy
  integrableOn_rhs := integrableOn_zero
  weak := by
    intro ψ hψ hψs hψb
    rw [hweak ψ hψ hψs hψb]
    simp

/-- The flux of an `L^p` field lies in the conjugate space `L^{p'}`.  This is the
integrability needed for the Sobolev test-function upgrade in the gradient argument. -/
theorem IsSmoothStrictNorm.memLp_flux {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {μ : Measure (Euc d)} {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p) μ) :
    MemLp (fun y => flux p F (G y)) (ENNReal.ofReal (Real.conjExponent p)) μ := by
  have hp1 : 0 < p - 1 := by linarith
  have hpow : MemLp (fun y => ‖G y‖ ^ (p - 1))
      (ENNReal.ofReal (Real.conjExponent p)) μ := by
    rw [Real.conjExponent, ENNReal.ofReal_div_of_pos hp1]
    simpa only [ENNReal.toReal_ofReal hp1.le] using
      hG.norm_rpow_div (ENNReal.ofReal (p - 1))
  obtain ⟨C, _, hC⟩ := hF.exists_norm_flux_le hp
  exact (hpow.const_mul C).mono'
    ((hF.continuous_flux' hp).comp_aestronglyMeasurable hG.aestronglyMeasurable)
    (Eventually.of_forall fun y => hC (G y))

/-- For each fixed step, the difference-quotient flux energy is integrable whenever the
field has finite `p`-energy.  This needs no equation and holds also in the singular range
`1 < p < 2`; the genuinely analytic issue is a bound uniform in the step. -/
theorem integrable_diffQuot_flux_energy {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) (h : ℝ) (e : Euc d) :
    Integrable (fun x => ⟪diffQuot h e (fun y => flux p F (G y)) x,
      diffQuot h e G x⟫) := by
  exact integrable_inner_of_memLp hp (memLp_diffQuot (hF.memLp_flux hp hG) h e)
    (memLp_diffQuot hG h e)

/-- The weighted difference-quotient energy is integrable at every fixed step for an
`L^p` field, including when its scalar weight has negative exponent.  Weighted strong
monotonicity provides the integrable majorant, so there is no assumption that the weight
itself is integrable. -/
theorem integrable_weighted_diffQuot_energy {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) (h : ℝ) (e : Euc d) :
    Integrable (fun x => (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) *
      ‖diffQuot h e G x‖ ^ 2) := by
  obtain ⟨c, hc, hmono⟩ := hF.exists_pos_weighted_normSq_le_inner_flux_sub hp
  have hshift := hG.comp_measurePreserving (measurePreserving_add_right volume (h • e))
  have hdiff := memLp_diffQuot hG h e
  have hweight : AEStronglyMeasurable
      (fun x => (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2)) volume := by
    exact ((hshift.aestronglyMeasurable.norm.add hG.aestronglyMeasurable.norm).aemeasurable.pow_const
      (p - 2)).aestronglyMeasurable
  have hsquare : AEStronglyMeasurable (fun x => ‖diffQuot h e G x‖ ^ 2) volume := by
    exact (continuous_pow 2).comp_aestronglyMeasurable hdiff.aestronglyMeasurable.norm
  refine ((integrable_diffQuot_flux_energy hp hF hG h e).const_mul c⁻¹).mono'
    (hweight.mul hsquare) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _) (sq_nonneg _))]
  exact rpow_mul_normSq_diffQuot_le_inner_diffQuot_flux hc hmono h e G x

namespace IsFluxSolutionOn

variable {p : ℝ} {F : Euc d → ℝ} {v : Euc d → ℝ} {G : Euc d → Euc d} {g : Euc d → ℝ}
  {x₀ : Euc d} {r₀ : ℝ}

/-- The finite energy in the weak-solution structure is precisely the local `L^p`
condition on its gradient field. -/
theorem memLp_gradient (hsol : IsFluxSolutionOn p F v G g x₀ r₀) (hp : 1 < p) :
    MemLp G (ENNReal.ofReal p) (volume.restrict (Metric.closedBall x₀ r₀)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  apply (memLp_norm_rpow_iff hsol.integrableOn.aestronglyMeasurable
    hpne ENNReal.ofReal_ne_top).mp
  rw [ENNReal.div_self hpne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
  exact memLp_one_iff_integrable.mpr hsol.integrableOn_energy

/-- A cutoff supported strictly inside the energy ball produces a global Sobolev potential
from either the classical or distributional gradient-field hypothesis. -/
theorem memW0_cutoff (hsol : IsFluxSolutionOn p F v G g x₀ r₀) (hp : 1 < p)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀) {η : Euc d → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηr : tsupport η ⊆ Metric.closedBall x₀ r) {A B : ℝ}
    (hA : ∀ x, |η x| ≤ A) (hB : ∀ x, ‖gradient η x‖ ≤ B) :
    MemW0 p (tsupport η) (fun x => η x * v x) ∧
      HasWeakGradient (fun x => η x * v x)
        (fun x => η x • G x + v x • gradient η x) := by
  have hGball : MemLp G (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ r₀)) :=
    (hsol.memLp_gradient hp).mono_measure
      (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hηball : tsupport η ⊆ Metric.ball x₀ r₀ :=
    hηr.trans (Metric.closedBall_subset_ball hrr₀)
  rcases hsol.gradientField with hclass | hweak
  · exact memW0_cutoff_of_differentiableOn hp.le Metric.isOpen_ball hclass hGball hη hηs
      hηball hA
  · let s := (r + r₀) / 2
    have hrs : r < s := by dsimp [s]; linarith
    have hsR : s < r₀ := by dsimp [s]; linarith
    have hvLp := hweak.memLp_restrict_ball hp (hr.trans hrs) hsR hGball
    exact hweak.memW0_cutoff hη
      (hvLp.mono_measure (Measure.restrict_mono_set volume
        (hηr.trans (Metric.closedBall_subset_ball hrs))))
      (hGball.mono_measure (Measure.restrict_mono_set volume hηball)) hA hB

/-- Every smaller concentric ball has a global `W^{1,p}` potential agreeing with the
original potential and gradient on its closed ball. The localized pair solves the same
equation there, so global difference-quotient tools apply without global assumptions on the
original solution. -/
theorem exists_localized (hsol : IsFluxSolutionOn p F v G g x₀ r₀) (hp : 1 < p)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀) :
    ∃ (w : Euc d → ℝ) (H : Euc d → Euc d),
      IsFluxSolutionOn p F w H g x₀ r ∧ HasWeakGradient w H ∧
      MemLp w (ENNReal.ofReal p) ∧ MemLp H (ENNReal.ofReal p) ∧
      EqOn w v (Metric.closedBall x₀ r) ∧ EqOn H G (Metric.closedBall x₀ r) := by
  let a := (r + r₀) / 2
  let b := (a + r₀) / 2
  have hra : r < a := by dsimp [a]; linarith
  have haR : a < r₀ := by dsimp [a]; linarith
  have hab : a < b := by dsimp [b]; linarith
  have hbR : b < r₀ := by dsimp [b]; linarith
  obtain ⟨Cη, _, hcut⟩ := exists_uniform_cutoff (hr.trans hra) hab
  obtain ⟨η, hη, hη0, hη1, hηeq, hηb, hDη⟩ := hcut x₀
  have hηs : HasCompactSupport η :=
    (isCompact_closedBall x₀ b).of_isClosed_subset (isClosed_tsupport η) hηb
  have hA : ∀ x, |η x| ≤ 1 := fun x => by rw [abs_of_nonneg (hη0 x)]; exact hη1 x
  obtain ⟨hmem, hweak⟩ := hsol.memW0_cutoff hp (hr.trans (hra.trans hab)) hbR
    hη hηs hηb hA hDη
  let w := fun x => η x * v x
  let H := fun x => η x • G x + v x • gradient η x
  have hH : MemLp H (ENNReal.ofReal p) :=
    hmem.memLp_weakGrad.ae_eq hweak.weakGrad_ae_eq
  have hηr : ∀ x ∈ Metric.closedBall x₀ r, η x = 1 ∧ gradient η x = 0 := by
    intro x hx
    have hxa : x ∈ Metric.ball x₀ a := Metric.closedBall_subset_ball hra hx
    have heq : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxa] with y hy
      exact hηeq y (Metric.ball_subset_closedBall hy)
    exact ⟨hηeq x (Metric.closedBall_subset_closedBall hra.le hx),
      ((hasGradientAt_const x (1 : ℝ)).congr_of_eventuallyEq heq).gradient⟩
  have hwv : EqOn w v (Metric.closedBall x₀ r) := by
    intro x hx
    simp only [w, (hηr x hx).1, one_mul]
  have hHG : EqOn H G (Metric.closedBall x₀ r) := by
    intro x hx
    simp only [H, (hηr x hx).1, (hηr x hx).2, one_smul, smul_zero, add_zero]
  refine ⟨w, H, ?_, hweak, hmem.memLp, hH, hwv, hHG⟩
  refine ⟨IsGradientFieldOn.of_hasWeakGradient hweak _,
    (hH.locallyIntegrable (ENNReal.one_le_ofReal.mpr hp.le)).integrableOn_isCompact
      (isCompact_closedBall _ _),
    (integrable_norm_rpow_of_memLp (lt_trans zero_lt_one hp) hH).integrableOn,
    hsol.integrableOn_rhs.mono_set (Metric.closedBall_subset_closedBall hrr₀.le), ?_⟩
  intro ψ hψ hψs hψr
  have heq : (∫ y, ⟪flux p F (H y), gradient ψ y⟫) =
      ∫ y, ⟪flux p F (G y), gradient ψ y⟫ := by
    apply integral_congr_ae
    refine Eventually.of_forall fun y => ?_
    change ⟪flux p F (H y), gradient ψ y⟫ = ⟪flux p F (G y), gradient ψ y⟫
    by_cases hy : y ∈ Metric.ball x₀ r
    · rw [hHG (Metric.ball_subset_closedBall hy)]
    · rw [gradient_eq_zero_of_notMem_tsupport (fun h => hy (hψr h))]
      simp
  rw [heq]
  exact hsol.weak ψ hψ hψs (hψr.trans (Metric.ball_subset_ball hrr₀.le))

/-- Both difference-quotient energy densities are locally integrable for every step
whose translate stays inside the energy ball.  This proves the two integrability clauses
of the homogeneous Caccioppoli assertion from the finite energy hypothesis alone. -/
theorem integrableOn_diffQuot_energies (hsol : IsFluxSolutionOn p F v G g x₀ r₀)
    (hp : 1 < p) (hF : IsSmoothStrictNorm F) {r : ℝ} (hrr₀ : r < r₀)
    (h : ℝ) (e : Euc d) (he : ‖e‖ ≤ 1) (hh : |h| < r₀ - r) :
    IntegrableOn (fun x => (‖G (x + h • e)‖ + ‖G x‖) ^ (p - 2) *
      ‖diffQuot h e G x‖ ^ 2) (Metric.ball x₀ r) ∧
    IntegrableOn (fun x => ⟪diffQuot h e (fun y => flux p F (G y)) x,
      diffQuot h e G x⟫) (Metric.ball x₀ r) := by
  let Gc : Euc d → Euc d := (Metric.closedBall x₀ r₀).indicator G
  have hGc : MemLp Gc (ENNReal.ofReal p) :=
    (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (hsol.memLp_gradient hp)
  have hGcx : ∀ x ∈ Metric.ball x₀ r, Gc x = G x ∧ Gc (x + h • e) = G (x + h • e) := by
    intro x hx
    have hxB : x ∈ Metric.closedBall x₀ r₀ :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hrr₀.le hx)
    have hnorm : ‖h • e‖ ≤ |h| := by
      rw [norm_smul, Real.norm_eq_abs]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg h)
    have hdist : dist (x + h • e) x ≤ |h| := by
      rw [dist_eq_norm, show x + h • e - x = h • e by abel]
      exact hnorm
    have hxshift : x + h • e ∈ Metric.closedBall x₀ r₀ := by
      rw [Metric.mem_closedBall]
      have hxlt := Metric.mem_ball.mp hx
      have htri := dist_triangle (x + h • e) x x₀
      linarith
    exact ⟨Set.indicator_of_mem hxB G, Set.indicator_of_mem hxshift G⟩
  refine ⟨(integrable_weighted_diffQuot_energy hp hF hGc h e).integrableOn.congr_fun ?_
      measurableSet_ball,
    (integrable_diffQuot_flux_energy hp hF hGc h e).integrableOn.congr_fun ?_
      measurableSet_ball⟩
  · intro x hx
    obtain ⟨h₁, h₂⟩ := hGcx x hx
    simp only [diffQuot_apply, h₁, h₂]
  · intro x hx
    obtain ⟨h₁, h₂⟩ := hGcx x hx
    simp only [diffQuot_apply, h₁, h₂]

/-- The flux restricted to the equation's ball has the conjugate integrability required
by the Sobolev density theorem. -/
theorem memLp_flux_indicator (hsol : IsFluxSolutionOn p F v G g x₀ r₀) (hp : 1 < p)
    (hF : IsSmoothStrictNorm F) :
    MemLp ((Metric.ball x₀ r₀).indicator (fun y => flux p F (G y)))
      (ENNReal.ofReal (Real.conjExponent p)) := by
  rw [memLp_indicator_iff_restrict measurableSet_ball]
  exact (hF.memLp_flux hp (hsol.memLp_gradient hp)).mono_measure
    (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)

/-- Bounded measurable forcing on the ball belongs to every finite conjugate space. -/
theorem memLp_rhs_indicator (hsol : IsFluxSolutionOn p F v G g x₀ r₀) {M : ℝ}
    (hg : ∀ y ∈ Metric.ball x₀ r₀, |g y| ≤ M) :
    MemLp ((Metric.ball x₀ r₀).indicator g)
      (ENNReal.ofReal (Real.conjExponent p)) := by
  rw [memLp_indicator_iff_restrict measurableSet_ball]
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ r₀)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine MemLp.of_bound
    (hsol.integrableOn_rhs.mono_set Metric.ball_subset_closedBall).aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  simpa only [Real.norm_eq_abs] using hg y hy

/-- The weak equation extends to Sobolev test functions supported strictly inside the
ball.  This supplies the density step in the difference-quotient Caccioppoli argument;
the construction and energy estimate for the cutoff difference quotient remain separate. -/
theorem integral_inner_weakGrad (hsol : IsFluxSolutionOn p F v G g x₀ r₀) (hp : 1 < p)
    (hF : IsSmoothStrictNorm F)
    {M : ℝ} (hg : ∀ y ∈ Metric.ball x₀ r₀, |g y| ≤ M)
    {K : Set (Euc d)} (hK : IsCompact K) (hKB : K ⊆ Metric.ball x₀ r₀)
    {ψ : Euc d → ℝ} (hψ : MemW0 p K ψ)
    (hψK : ∀ᵐ y, y ∉ K → weakGrad ψ y = 0) :
    ∫ y, ⟪flux p F (G y), weakGrad ψ y⟫ = ∫ y, g y * ψ y := by
  exact integral_inner_weakGrad_eq_of_memW0_indicator hp Metric.isOpen_ball
    (hsol.memLp_flux_indicator hp hF) (hsol.memLp_rhs_indicator hg)
    hsol.weak hK hKB hψ hψK

/-- In the homogeneous case the Sobolev test-function upgrade has no additional
integrability requirement on a right-hand side. -/
theorem integral_inner_weakGrad_zero (hsol : IsFluxSolutionOn p F v G 0 x₀ r₀)
    (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} (hK : IsCompact K) (hKB : K ⊆ Metric.ball x₀ r₀)
    {ψ : Euc d → ℝ} (hψ : MemW0 p K ψ)
    (hψK : ∀ᵐ y, y ∉ K → weakGrad ψ y = 0) :
    ∫ y, ⟪flux p F (G y), weakGrad ψ y⟫ = 0 := by
  have hg : ∀ y ∈ Metric.ball x₀ r₀, |(0 : Euc d → ℝ) y| ≤ 0 := by simp
  simpa using hsol.integral_inner_weakGrad hp hF hg hK hKB hψ hψK

/-- **The translated weak equation.**  For a shift `w` carrying `tsupport ψ` into the ball, the
shifted field `G(· + w)` satisfies the same weak equation with right-hand side `g(· + w)`.
Subtracting this identity from the equation for `G` itself and dividing by `‖w‖` is the first
step of the difference-quotient (weighted `W^{2,2}`) argument: it turns the equation for `G` into
an equation for `Δ_h^e G`.  This is the general form of `integral_inner_flux_translate`, whose
change-of-variables proof it follows. -/
theorem integral_inner_flux_shift (hsol : IsFluxSolutionOn p F v G g x₀ r₀) (w : Euc d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψU : ∀ x ∈ tsupport ψ, x + w ∈ Metric.ball x₀ r₀) :
    ∫ x, ⟪flux p F (G (x + w)), gradient ψ x⟫ = ∫ x, g (x + w) * ψ x := by
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : Euc d → ℝ, ψ' = fun y => ψ (y + -w) := ⟨_, rfl⟩
  have hψ'c : ContDiff ℝ ∞ ψ' := by
    rw [hψ']
    exact hψ.comp (contDiff_id.add contDiff_const)
  have hψ's : HasCompactSupport ψ' := by
    have h := hψs.comp_homeomorph (Homeomorph.addRight (-w))
    have he : ψ ∘ Homeomorph.addRight (-w) = ψ' := by
      rw [hψ']
      rfl
    rwa [he] at h
  have hψ'U : tsupport ψ' ⊆ Metric.ball x₀ r₀ := by
    intro y hy
    have h1 : tsupport ψ' = (Homeomorph.addRight (-w)) ⁻¹' tsupport ψ := by
      rw [← tsupport_comp_eq_preimage ψ (Homeomorph.addRight (-w)), hψ']
      rfl
    rw [h1] at hy
    have h2 := hψU _ hy
    simpa using h2
  have hgrad : ∀ y, gradient ψ' y = gradient ψ (y + -w) := fun y => by
    rw [hψ']
    unfold gradient
    rw [fderiv_comp_add_right]
  have e1 : ∫ x, ⟪flux p F (G (x + w)), gradient ψ x⟫ =
      ∫ y, ⟪flux p F (G y), gradient ψ' y⟫ := by
    rw [← integral_add_right_eq_self (fun y => ⟪flux p F (G y), gradient ψ' y⟫) w]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ⟪flux p F (G (x + w)), gradient ψ x⟫ =
      ⟪flux p F (G (x + w)), gradient ψ' (x + w)⟫
    rw [hgrad, add_neg_cancel_right]
  have e2 : ∫ x, g (x + w) * ψ x = ∫ y, g y * ψ' y := by
    rw [← integral_add_right_eq_self (fun y => g y * ψ' y) w]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show g (x + w) * ψ x = g (x + w) * ψ' (x + w)
    rw [hψ']
    simp only [add_neg_cancel_right]
  rw [e1, e2]
  exact hsol.weak ψ' hψ'c hψ's hψ'U


/-- **The difference-quotient weak equation.**  Subtracting the weak equation
`IsFluxSolutionOn.weak` from its translate `IsFluxSolutionOn.integral_inner_flux_shift` and
dividing by the step `h` turns the equation for `G` into an equation for the difference quotients:

`∫ ⟪Δ_h^e (a ∘ G), ∇ψ⟫ = ∫ (Δ_h^e g) ψ`.

This is the entry point of the second-order (weighted `W^{2,2}`) Caccioppoli argument.  Testing it
with `ψ = η² Δ_h^e v` — legitimate once the admissible test functions have been widened from
`C^∞_c` to `W^{1,p}_0` — produces on the left the flux energy `∫ η² ⟪Δ_h^e a(∇v), Δ_h^e ∇v⟫`,
which is bounded below by the weighted second-order energy through
`IsSmoothStrictNorm.exists_pos_weighted_normSq_le_inner_flux_sub`.

The four integrability hypotheses permit subtraction of the two integral identities without
using the junk value of a nonintegrable integral.  The finite energy field of
`IsFluxSolutionOn` and the forcing integrability make these hypotheses provable for the
compactly supported smooth test functions. -/
theorem integral_inner_diffQuot_flux (hsol : IsFluxSolutionOn p F v G g x₀ r₀) (h : ℝ)
    (e : Euc d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ Metric.ball x₀ r₀)
    (hψh : ∀ x ∈ tsupport ψ, x + h • e ∈ Metric.ball x₀ r₀)
    (hi : Integrable fun x => ⟪flux p F (G x), gradient ψ x⟫)
    (hi' : Integrable fun x => ⟪flux p F (G (x + h • e)), gradient ψ x⟫)
    (hj : Integrable fun x => g x * ψ x)
    (hj' : Integrable fun x => g (x + h • e) * ψ x) :
    ∫ x, ⟪diffQuot h e (fun y => flux p F (G y)) x, gradient ψ x⟫
      = ∫ x, diffQuot h e g x * ψ x := by
  have hA : ∀ x : Euc d, ⟪diffQuot h e (fun y => flux p F (G y)) x, gradient ψ x⟫
      = h⁻¹ * (⟪flux p F (G (x + h • e)), gradient ψ x⟫
        - ⟪flux p F (G x), gradient ψ x⟫) := by
    intro x
    simp only [diffQuot_apply, real_inner_smul_left, inner_sub_left]
  have hB : ∀ x : Euc d, diffQuot h e g x * ψ x
      = h⁻¹ * (g (x + h • e) * ψ x - g x * ψ x) := by
    intro x
    simp only [diffQuot_apply, smul_eq_mul]
    ring
  have e1 : (∫ x, ⟪diffQuot h e (fun y => flux p F (G y)) x, gradient ψ x⟫)
      = ∫ x, h⁻¹ * (⟪flux p F (G (x + h • e)), gradient ψ x⟫
        - ⟪flux p F (G x), gradient ψ x⟫) :=
    integral_congr_ae (Eventually.of_forall hA)
  have e2 : (∫ x, diffQuot h e g x * ψ x)
      = ∫ x, h⁻¹ * (g (x + h • e) * ψ x - g x * ψ x) :=
    integral_congr_ae (Eventually.of_forall hB)
  rw [e1, e2]
  simp only [integral_const_mul]
  rw [integral_sub hi' hi, integral_sub hj' hj, hsol.weak ψ hψ hψs hψU,
    hsol.integral_inner_flux_shift (h • e) hψ hψs hψh]

/-- The homogeneous difference-quotient equation holds for Sobolev tests supported in
an interior open set whose translate stays inside the equation's ball.  The global `L^p`
field hypothesis makes both translated fluxes `L^{p'}`. `IsFluxSolutionOn.exists_localized`
supplies such a global field on any smaller ball from the actual local solution data. -/
theorem integral_inner_diffQuot_flux_weakGrad_zero
    (hsol : IsFluxSolutionOn p F v G 0 x₀ r₀) (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hG : MemLp G (ENNReal.ofReal p)) (h : ℝ) (e : Euc d)
    {U : Set (Euc d)} (hU : IsOpen U) (hUB : U ⊆ Metric.ball x₀ r₀)
    (hUh : ∀ y ∈ U, y + h • e ∈ Metric.ball x₀ r₀)
    {K : Set (Euc d)} (hK : IsCompact K) (hKU : K ⊆ U)
    {ψ : Euc d → ℝ} (hψ : MemW0 p K ψ) :
    ∫ y, ⟪diffQuot h e (fun z => flux p F (G z)) y, weakGrad ψ y⟫ = 0 := by
  have ha : MemLp (fun y => flux p F (G y))
      (ENNReal.ofReal (Real.conjExponent p)) := hF.memLp_flux hp hG
  have haΔ := memLp_diffQuot ha h e
  have hzero : MemLp (0 : Euc d → ℝ)
      (ENNReal.ofReal (Real.conjExponent p)) := MemLp.zero
  have hweak : ∀ χ : Euc d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ U →
      ∫ y, ⟪diffQuot h e (fun z => flux p F (G z)) y, gradient χ y⟫ =
        ∫ y, (0 : Euc d → ℝ) y * χ y := by
    intro χ hχ hχs hχU
    have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
    have hχG : MemLp (gradient χ) (ENNReal.ofReal p) :=
      (continuous_gradient hχ1).memLp_of_hasCompactSupport (hasCompactSupport_gradient hχs)
    have hi := integrable_inner_of_memLp hp ha hχG
    have hi' := integrable_inner_of_memLp hp
      (ha.comp_measurePreserving (measurePreserving_add_right volume (h • e))) hχG
    have hj : Integrable (fun y => (0 : Euc d → ℝ) y * χ y) := by simp
    have hj' : Integrable (fun y => (0 : Euc d → ℝ) (y + h • e) * χ y) := by simp
    have hkey := hsol.integral_inner_diffQuot_flux h e hχ hχs (hχU.trans hUB)
      (fun y hy => hUh y (hχU hy)) hi hi' hj hj'
    simpa only [diffQuot, Pi.zero_apply, sub_self, smul_zero, zero_mul] using hkey
  simpa only [Pi.zero_apply, zero_mul, integral_zero] using
    integral_inner_weakGrad_eq_of_memW0 hp hU haΔ hzero hweak hK hKU hψ

/-- The exact tested difference-quotient identity underlying homogeneous Caccioppoli.
It is obtained by inserting a smooth cutoff times the potential's difference quotient
into the Sobolev equation; no regularity of the gradient is assumed. -/
theorem integral_inner_diffQuot_flux_cutoff_zero
    (hsol : IsFluxSolutionOn p F v G 0 x₀ r₀) (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hvG : HasWeakGradient v G) (hv : MemLp v (ENNReal.ofReal p))
    (hG : MemLp G (ENNReal.ofReal p)) (h : ℝ) (e : Euc d)
    {U : Set (Euc d)} (hU : IsOpen U) (hUB : U ⊆ Metric.ball x₀ r₀)
    (hUh : ∀ y ∈ U, y + h • e ∈ Metric.ball x₀ r₀)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) {A B : ℝ}
    (hA : ∀ y, |η y| ≤ A) (hB : ∀ y, ‖gradient η y‖ ≤ B) :
    ∫ y, ⟪diffQuot h e (fun z => flux p F (G z)) y,
      η y • diffQuot h e G y + diffQuot h e v y • gradient η y⟫ = 0 := by
  obtain ⟨hmem, hgrad, _⟩ := memW0_cutoff_diffQuot hvG hv hG h e hη hA hB
  have hweak := hsol.integral_inner_diffQuot_flux_weakGrad_zero hp hF hG h e
    hU hUB hUh hηs hηU hmem
  refine Eq.trans ?_ hweak
  refine integral_congr_ae ?_
  filter_upwards [hgrad] with y hy
  rw [hy]

/-- The homogeneous difference-quotient energy identity, with its two integrals split.
Both terms are genuinely integrable by conjugate Hölder and boundedness of the cutoff and
its gradient.  Taking a squared cutoff yields the energy and cross terms of Caccioppoli. -/
theorem integral_diffQuot_flux_energy_balance
    (hsol : IsFluxSolutionOn p F v G 0 x₀ r₀) (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hvG : HasWeakGradient v G) (hv : MemLp v (ENNReal.ofReal p))
    (hG : MemLp G (ENNReal.ofReal p)) (h : ℝ) (e : Euc d)
    {U : Set (Euc d)} (hU : IsOpen U) (hUB : U ⊆ Metric.ball x₀ r₀)
    (hUh : ∀ y ∈ U, y + h • e ∈ Metric.ball x₀ r₀)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) {A B : ℝ}
    (hA : ∀ y, |η y| ≤ A) (hB : ∀ y, ‖gradient η y‖ ≤ B) :
    (∫ y, η y * ⟪diffQuot h e (fun z => flux p F (G z)) y, diffQuot h e G y⟫) =
      -(∫ y, diffQuot h e v y *
        ⟪diffQuot h e (fun z => flux p F (G z)) y, gradient η y⟫) := by
  have ha := memLp_diffQuot (hF.memLp_flux hp hG) h e
  have hvΔ := memLp_diffQuot hv h e
  have hηm : AEStronglyMeasurable η volume := hη.continuous.aestronglyMeasurable
  have hgηm : AEStronglyMeasurable (gradient η) volume :=
    (continuous_gradient (hη.of_le (by simp))).aestronglyMeasurable
  have hi₁ : Integrable (fun y => η y *
      ⟪diffQuot h e (fun z => flux p F (G z)) y, diffQuot h e G y⟫) :=
    (integrable_diffQuot_flux_energy hp hF hG h e).bdd_mul hηm
      (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hA y)
  have hvη : MemLp (fun y => diffQuot h e v y • gradient η y) (ENNReal.ofReal p) := by
    refine hvΔ.of_le_mul (c := B) (hvΔ.aestronglyMeasurable.smul hgηm)
      (Eventually.of_forall fun y => ?_)
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
  have hi₂ : Integrable (fun y => diffQuot h e v y *
      ⟪diffQuot h e (fun z => flux p F (G z)) y, gradient η y⟫) := by
    simpa only [real_inner_smul_right] using integrable_inner_of_memLp hp ha hvη
  have hkey := hsol.integral_inner_diffQuot_flux_cutoff_zero hp hF hvG hv hG h e
    hU hUB hUh hη hηs hηU hA hB
  have hsplit : (∫ y, η y *
      ⟪diffQuot h e (fun z => flux p F (G z)) y, diffQuot h e G y⟫) +
      (∫ y, diffQuot h e v y *
        ⟪diffQuot h e (fun z => flux p F (G z)) y, gradient η y⟫) = 0 := by
    rw [← integral_add hi₁ hi₂]
    simpa only [inner_add_right, real_inner_smul_right] using hkey
  linarith

end IsFluxSolutionOn

/-- Weighted quadratic Young splitting.  The weight may vanish and need not have an
integrable reciprocal, which is essential for singular and degenerate fluxes. -/
theorem weighted_quadratic_young {c w : ℝ} (hc : 0 < c) (hw : 0 ≤ w) (a b : ℝ) :
    2 * w * a * b ≤ c / 2 * w * a ^ 2 + 2 / c * w * b ^ 2 := by
  have hmain : 2 * c * w * a * b ≤ c ^ 2 / 2 * w * a ^ 2 + 2 * w * b ^ 2 := by
    nlinarith [mul_nonneg hw (sq_nonneg (c * a - 2 * b))]
  calc 2 * w * a * b = (2 * c * w * a * b) / c := by field_simp [hc.ne']; try ring
    _ ≤ (c ^ 2 / 2 * w * a ^ 2 + 2 * w * b ^ 2) / c :=
      div_le_div_of_nonneg_right hmain hc.le
    _ = c / 2 * w * a ^ 2 + 2 / c * w * b ^ 2 := by
      field_simp [hc.ne']
      try ring

end Komlos.Literature
