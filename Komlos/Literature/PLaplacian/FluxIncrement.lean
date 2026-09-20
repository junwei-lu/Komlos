import Komlos.Literature.PLaplacian.FluxMonotone

/-!
# Upper increment bound for the anisotropic flux

The weighted Lipschitz estimate for `a(ξ) = F(ξ)^(p-1) ∇F(ξ)` used in the
homogeneous difference-quotient energy estimate (paper Appendix A, *Eigenfunction inputs*).

The proof splits pairs according to their distance relative to `‖ξ‖ + ‖ζ‖`.
For distant pairs the growth of the flux suffices. For close pairs their segment stays
uniformly away from zero, so the derivative bound and the mean value inequality apply.
This includes `1 < p < 2` and segments through zero without integrating a singular derivative.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-- A map with growth of degree `p-1` and derivative growth of degree `p-2`
satisfies the corresponding weighted increment estimate. -/
theorem exists_weighted_norm_sub_le_of_growth_fderiv {p : ℝ} (hp : 1 < p)
    {f : Euc d → Euc d} (hf : ∀ ξ : Euc d, ξ ≠ 0 → DifferentiableAt ℝ f ξ)
    (hgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ‖f ξ‖ ≤ C * ‖ξ‖ ^ (p - 1))
    (hderiv : ∃ D : ℝ, 0 ≤ D ∧ ∀ ξ : Euc d, ξ ≠ 0 →
      ‖fderiv ℝ f ξ‖ ≤ D * ‖ξ‖ ^ (p - 2)) :
    ∃ L : ℝ, 0 < L ∧ ∀ ξ ζ : Euc d,
      ‖f ξ - f ζ‖ ≤ L * (‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ := by
  obtain ⟨C, hC, hCg⟩ := hgrowth
  obtain ⟨D, hD, hDb⟩ := hderiv
  let K : ℝ := max 1 ((1 / 8 : ℝ) ^ (p - 2))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨8 * C + D * K + 1, by positivity, fun ξ ζ => ?_⟩
  rcases eq_or_ne ξ ζ with rfl | hne
  · simp
  let S : ℝ := ‖ξ‖ + ‖ζ‖
  have hδ : 0 < ‖ξ - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hS : 0 < S := hδ.trans_le (norm_sub_le ξ ζ)
  have hpow : 0 ≤ S ^ (p - 2) := Real.rpow_nonneg hS.le _
  have hrpow : S ^ (p - 2) * S = S ^ (p - 1) := by
    rw [← Real.rpow_add_one hS.ne']
    congr 1
    ring
  by_cases hfar : S / 4 ≤ ‖ξ - ζ‖
  · have hgrow : ‖f ξ - f ζ‖ ≤ 2 * C * S ^ (p - 1) := by
      calc ‖f ξ - f ζ‖ ≤ ‖f ξ‖ + ‖f ζ‖ := norm_sub_le _ _
        _ ≤ C * ‖ξ‖ ^ (p - 1) + C * ‖ζ‖ ^ (p - 1) := add_le_add (hCg ξ) (hCg ζ)
        _ ≤ C * S ^ (p - 1) + C * S ^ (p - 1) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (norm_nonneg ξ)
                (show ‖ξ‖ ≤ S from le_add_of_nonneg_right (norm_nonneg ζ)) (by linarith)) hC
          · exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (norm_nonneg ζ)
                (show ‖ζ‖ ≤ S from le_add_of_nonneg_left (norm_nonneg ξ)) (by linarith)) hC
        _ = 2 * C * S ^ (p - 1) := by ring
    have hstep : 2 * C * S ^ (p - 1) ≤ 8 * C * S ^ (p - 2) * ‖ξ - ζ‖ := by
      rw [← hrpow]
      nlinarith [mul_nonneg (mul_nonneg hC hpow) (show 0 ≤ 4 * ‖ξ - ζ‖ - S by linarith)]
    exact (hgrow.trans hstep).trans (by
      change 8 * C * S ^ (p - 2) * ‖ξ - ζ‖ ≤ _
      gcongr
      nlinarith [mul_nonneg hD hK.le])
  · have hnear : ‖ξ - ζ‖ < S / 4 := lt_of_not_ge hfar
    have hseg : ∀ η ∈ segment ℝ ζ ξ, S / 8 ≤ ‖η‖ ∧ ‖η‖ ≤ S := by
      intro η hη
      rw [segment_eq_image'] at hη
      obtain ⟨t, ht, rfl⟩ := hη
      refine ⟨?_, norm_add_smul_sub_le ζ ξ ht.1 ht.2⟩
      have hnorm := norm_sub_le_norm_add_smul_sub_left ζ ξ t
      rw [abs_of_nonneg ht.1] at hnorm
      have htri : ‖ξ‖ ≤ ‖ξ - ζ‖ + ‖ζ‖ := by
        calc ‖ξ‖ = ‖(ξ - ζ) + ζ‖ := by congr 1; module
          _ ≤ ‖ξ - ζ‖ + ‖ζ‖ := norm_add_le _ _
      have htδ : t * ‖ξ - ζ‖ ≤ ‖ξ - ζ‖ := by nlinarith [ht.2]
      dsimp [S] at hnear ⊢
      linarith
    have hseg0 : ∀ η ∈ segment ℝ ζ ξ, η ≠ 0 := by
      intro η hη
      exact norm_pos_iff.1 ((div_pos hS (by norm_num : (0 : ℝ) < 8)).trans_le (hseg η hη).1)
    have hsegpow : ∀ η ∈ segment ℝ ζ ξ, ‖η‖ ^ (p - 2) ≤ K * S ^ (p - 2) := by
      intro η hη
      by_cases hp2 : 2 ≤ p
      · calc ‖η‖ ^ (p - 2) ≤ S ^ (p - 2) :=
              Real.rpow_le_rpow (norm_nonneg _) (hseg η hη).2 (by linarith)
          _ ≤ K * S ^ (p - 2) := by
              calc S ^ (p - 2) = 1 * S ^ (p - 2) := (one_mul _).symm
                _ ≤ K * S ^ (p - 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
      · calc ‖η‖ ^ (p - 2) ≤ (S / 8) ^ (p - 2) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) (hseg η hη).1 (by linarith)
          _ = (1 / 8 : ℝ) ^ (p - 2) * S ^ (p - 2) := by
              rw [show S / 8 = (1 / 8 : ℝ) * S by ring,
                Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 8) hS.le]
          _ ≤ K * S ^ (p - 2) := mul_le_mul_of_nonneg_right (le_max_right _ _) hpow
    have hbound : ∀ η ∈ segment ℝ ζ ξ,
        ‖fderiv ℝ (f) η‖ ≤ D * K * S ^ (p - 2) := by
      intro η hη
      calc ‖fderiv ℝ (f) η‖ ≤ D * ‖η‖ ^ (p - 2) := hDb η (hseg0 η hη)
        _ ≤ D * (K * S ^ (p - 2)) := mul_le_mul_of_nonneg_left (hsegpow η hη) hD
        _ = D * K * S ^ (p - 2) := (mul_assoc _ _ _).symm
    have hmv := (convex_segment ζ ξ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun η hη => (hf η (hseg0 η hη)).hasFDerivAt.hasFDerivWithinAt)
      hbound (left_mem_segment ℝ ζ ξ) (right_mem_segment ℝ ζ ξ)
    exact hmv.trans (by
      change D * K * S ^ (p - 2) * ‖ξ - ζ‖ ≤ _
      gcongr
      linarith)


/-- The natural gradient variable for a `p`-growth energy. -/
noncomputable def naturalGradient (p : ℝ) (ξ : Euc d) : Euc d := ‖ξ‖ ^ ((p - 2) / 2) • ξ

/-- The natural gradient variable has growth of degree `p/2`. -/
theorem norm_naturalGradient (p : ℝ) (ξ : Euc d) (hp : 0 < p) :
    ‖naturalGradient p ξ‖ = ‖ξ‖ ^ (p / 2) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [naturalGradient, Real.zero_rpow (by linarith : p / 2 ≠ 0)]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [naturalGradient, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _),
    ← Real.rpow_add_one hn.ne']
  congr 1
  ring

/-- Derivative growth for the natural gradient variable, away from zero. -/
theorem naturalGradient_derivative_bound (p : ℝ) {ξ : Euc d} (hξ : ξ ≠ 0) :
    DifferentiableAt ℝ (naturalGradient p) ξ ∧
      ‖fderiv ℝ (naturalGradient p) ξ‖ ≤
        (1 + |(p - 2) / 2|) * ‖ξ‖ ^ ((p - 2) / 2) := by
  let q : ℝ := (p - 2) / 2
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hnorm : HasFDerivAt (fun η : Euc d => ‖η‖)
      (fderiv ℝ (fun η : Euc d => ‖η‖) ξ) ξ :=
    ((differentiableAt_id.norm ℝ hξ)).hasFDerivAt
  have hV := (hnorm.rpow_const (p := q) (Or.inl hn.ne')).smul (hasFDerivAt_id ξ)
  change HasFDerivAt (naturalGradient p)
    (‖ξ‖ ^ q • ContinuousLinearMap.id ℝ (Euc d) +
      ((q * ‖ξ‖ ^ (q - 1)) • fderiv ℝ (fun η : Euc d => ‖η‖) ξ).smulRight ξ) ξ at hV
  refine ⟨hV.differentiableAt, ?_⟩
  rw [hV.fderiv]
  have hdn : ‖fderiv ℝ (fun η : Euc d => ‖η‖) ξ‖ ≤ 1 := by
    simpa only [NNReal.coe_one] using
      (norm_fderiv_le_of_lipschitz ℝ (x₀ := ξ) (C := 1) lipschitzWith_one_norm)
  have hpow : ‖ξ‖ ^ (q - 1) * ‖ξ‖ = ‖ξ‖ ^ q := by
    rw [← Real.rpow_add_one hn.ne']
    congr 1
    ring
  calc
    ‖‖ξ‖ ^ q • ContinuousLinearMap.id ℝ (Euc d) +
        ((q * ‖ξ‖ ^ (q - 1)) • fderiv ℝ (fun η : Euc d => ‖η‖) ξ).smulRight ξ‖
      ≤ ‖‖ξ‖ ^ q • ContinuousLinearMap.id ℝ (Euc d)‖ +
        ‖((q * ‖ξ‖ ^ (q - 1)) • fderiv ℝ (fun η : Euc d => ‖η‖) ξ).smulRight ξ‖ :=
          norm_add_le _ _
    _ = ‖ξ‖ ^ q * ‖ContinuousLinearMap.id ℝ (Euc d)‖ +
        (|q| * ‖ξ‖ ^ (q - 1) * ‖fderiv ℝ (fun η : Euc d => ‖η‖) ξ‖) * ‖ξ‖ := by
          simp only [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _),
            ContinuousLinearMap.norm_smulRight_apply, norm_mul, Real.norm_eq_abs]
    _ ≤ ‖ξ‖ ^ q * 1 + (|q| * ‖ξ‖ ^ (q - 1) * 1) * ‖ξ‖ := by
          gcongr
          exact ContinuousLinearMap.norm_id_le
    _ = (1 + |q|) * ‖ξ‖ ^ q := by
          rw [mul_one, mul_one]
          calc ‖ξ‖ ^ q + |q| * ‖ξ‖ ^ (q - 1) * ‖ξ‖
              = ‖ξ‖ ^ q + |q| * (‖ξ‖ ^ (q - 1) * ‖ξ‖) := by ring
            _ = (1 + |q|) * ‖ξ‖ ^ q := by rw [hpow]; ring

/-- Squared increments of the natural gradient variable are controlled by the weighted
squared increments of the original gradient. -/
theorem exists_norm_naturalGradient_sub_sq_le {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ ζ : Euc d,
      ‖naturalGradient p ξ - naturalGradient p ζ‖ ^ 2 ≤
        C * ((‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ ^ 2) := by
  have he1 : p / 2 + 1 - 1 = p / 2 := by ring
  have he2 : p / 2 + 1 - 2 = (p - 2) / 2 := by ring
  obtain ⟨L, hL, hbound⟩ := exists_weighted_norm_sub_le_of_growth_fderiv
    (p := p / 2 + 1) (by linarith)
    (f := naturalGradient p) (fun ξ hξ => (naturalGradient_derivative_bound p hξ).1)
    (by
      refine ⟨1, zero_le_one, fun ξ => ?_⟩
      rw [one_mul, he1, norm_naturalGradient p ξ hp])
    (by
      refine ⟨1 + |(p - 2) / 2|, by positivity, fun ξ hξ => ?_⟩
      simpa only [he2] using (naturalGradient_derivative_bound p hξ).2)
  refine ⟨L ^ 2, sq_pos_of_pos hL, fun ξ ζ => ?_⟩
  have h := hbound ξ ζ
  rw [he2] at h
  have hsq : ‖naturalGradient p ξ - naturalGradient p ζ‖ ^ 2 ≤
      (L * (‖ξ‖ + ‖ζ‖) ^ ((p - 2) / 2) * ‖ξ - ζ‖) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hpow : ((‖ξ‖ + ‖ζ‖) ^ ((p - 2) / 2)) ^ 2 = (‖ξ‖ + ‖ζ‖) ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ ‖ξ‖ + ‖ζ‖)]
    congr 1
    ring
  calc ‖naturalGradient p ξ - naturalGradient p ζ‖ ^ 2
      ≤ (L * (‖ξ‖ + ‖ζ‖) ^ ((p - 2) / 2) * ‖ξ - ζ‖) ^ 2 := hsq
    _ = L ^ 2 * ((‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ ^ 2) := by
      rw [mul_pow, mul_pow, hpow]
      ring

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- The derivative of the flux has its natural `(p-2)`-homogeneous upper bound. -/
theorem exists_norm_fderiv_flux_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euc d, ξ ≠ 0 →
      ‖fderiv ℝ (flux p F) ξ‖ ≤ C * ‖ξ‖ ^ (p - 2) := by
  have hAc : ContinuousOn (fderiv ℝ (flux p F)) (Metric.sphere (0 : Euc d) 1) :=
    ((hF.contDiffOn_flux' p).continuousOn_fderiv_of_isOpen isOpen_compl_singleton
      (by exact_mod_cast le_top)).mono fun ξ hξ => ne_zero_of_mem_sphere' hξ
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Euc d) 1).exists_bound_of_continuousOn hAc
  refine ⟨max C 0, le_max_right _ _, fun ξ hξ => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  let u : Euc d := ‖ξ‖⁻¹ • ξ
  have hu : u ∈ Metric.sphere (0 : Euc d) 1 := by
    simp [u, norm_smul, inv_mul_cancel₀ hn.ne']
  have hξu : ξ = ‖ξ‖ • u := by
    simp [u, smul_smul, mul_inv_cancel₀ hn.ne']
  have heq : fderiv ℝ (flux p F) ξ = ‖ξ‖ ^ (p - 2) • fderiv ℝ (flux p F) u := by
    apply ContinuousLinearMap.ext
    intro w
    change fderiv ℝ (flux p F) ξ w = ‖ξ‖ ^ (p - 2) • fderiv ℝ (flux p F) u w
    conv_lhs => rw [hξu]
    exact hF.fderiv_flux_smul_apply hp hn (ne_zero_of_mem_sphere' hu) w
  rw [heq, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
  calc ‖ξ‖ ^ (p - 2) * ‖fderiv ℝ (flux p F) u‖
      ≤ ‖ξ‖ ^ (p - 2) * max C 0 :=
        mul_le_mul_of_nonneg_left ((hC u hu).trans (le_max_left _ _))
          (Real.rpow_nonneg hn.le _)
    _ = max C 0 * ‖ξ‖ ^ (p - 2) := mul_comm _ _

/-- The upper weighted increment estimate for the flux, valid for every `p > 1`,
including segments through zero in the singular range `1 < p < 2`. -/
theorem exists_norm_flux_sub_le {p : ℝ} (hp : 1 < p) :
    ∃ L : ℝ, 0 < L ∧ ∀ ξ ζ : Euc d,
      ‖flux p F ξ - flux p F ζ‖ ≤
        L * (‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ :=
  exists_weighted_norm_sub_le_of_growth_fderiv hp
    (fun _ hξ => (hF.hasFDerivAt_flux' p hξ).differentiableAt)
    (hF.exists_norm_flux_le hp) (hF.exists_norm_fderiv_flux_le hp)

end IsSmoothStrictNorm

end Komlos.Literature
