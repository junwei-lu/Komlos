import Komlos.Literature.PLaplacian.BoundaryBarrier

/-!
# Quantitative strong monotonicity of the anisotropic flux

The quantitative form of `Komlos.Literature.IsSmoothStrictNorm.inner_flux_sub_pos`
(`BoundaryBarrier.lean`), for the flux `a(ξ) = F(ξ)^{p-1} ∇F(ξ)` of a smooth strictly convex
norm `F` (paper Appendix A, *Eigenfunction inputs*).

## Main results

* `IsSmoothStrictNorm.exists_pos_rpow_mul_normSq_le_inner_fderiv_flux` — the **scale invariant
  ellipticity** `c₀ ‖η‖^{p-2} ‖w‖² ≤ ⟪A(η) w, w⟫` of `A = Da` (`η ≠ 0`), obtained from the
  compact (unit sphere) ellipticity of `RegularitySchauder.lean` and the `(p-2)`-homogeneity of
  `A` (`IsSmoothStrictNorm.fderiv_flux_smul_apply`).
* `IsSmoothStrictNorm.exists_pos_norm_rpow_le_inner_flux_sub` — for `p ≥ 2`,
  `∃ c > 0, ∀ ξ ζ, c ‖ξ - ζ‖^p ≤ ⟪a(ξ) - a(ζ), ξ - ζ⟫` (strong monotonicity).
* `IsSmoothStrictNorm.exists_pos_mul_normSq_le_inner_flux_sub` — for `1 < p < 2`,
  `∃ c > 0, ∀ (ξ, ζ) ≠ (0, 0), c (‖ξ‖ + ‖ζ‖)^{p-2} ‖ξ - ζ‖² ≤ ⟪a(ξ) - a(ζ), ξ - ζ⟫`
  (the `‖ξ - ζ‖^p` shape is *false* in this range).

## The route

The scalar mean value formula (`IsSmoothStrictNorm.inner_flux_sub_eq_intervalIntegral`, the
fundamental theorem of calculus applied to `t ↦ ⟪a(ζ + t(ξ-ζ)), ξ - ζ⟫`) gives

`⟪a(ξ) - a(ζ), ξ - ζ⟫ = ∫₀¹ ⟪A(ζ + t(ξ-ζ))(ξ-ζ), ξ-ζ⟫ dt`

on a segment avoiding the origin, and the scale invariant ellipticity bounds the integrand from
below by `c₀ ‖ζ + t(ξ-ζ)‖^{p-2} ‖ξ-ζ‖²`. For `p ≥ 2` the integrand is bounded below by a
*constant* multiple of `‖ξ-ζ‖^p` on a subinterval of length `1/8`: either `‖ζ‖ ≥ ‖ξ-ζ‖/4`, and
then `‖ζ + t(ξ-ζ)‖ ≥ ‖ξ-ζ‖/8` for `t ∈ [0, 1/8]`, or `‖ξ‖ ≥ 3‖ξ-ζ‖/4`, and then
`‖ζ + t(ξ-ζ)‖ ≥ 5‖ξ-ζ‖/8` for `t ∈ [7/8, 1]`. For `1 < p < 2` the exponent is negative and
`‖ζ + t(ξ-ζ)‖ ≤ ‖ξ‖ + ‖ζ‖` bounds the integrand below on all of `[0, 1]`.

The configurations with `0` on the segment `[ζ, ξ]` are exactly the ones with `ξ = a v`,
`ζ = -b v` for `a, b ≥ 0`, `a + b = 1`, `v = ξ - ζ`; there the homogeneity
(`flux_smul_of_pos`, `flux_neg`) and Euler's identity `⟪a(v), v⟫ = F(v)^p`
(`inner_flux_self_eq_rpow`) compute the pairing exactly, as
`(a^{p-1} + b^{p-1}) F(v)^p ≥ 2^{1-p} c₁^p ‖ξ - ζ‖^p` (`le_inner_flux_sub_of_collinear`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Elementary `rpow` arithmetic -/

/-- `r^{q-2} r² = r^q` for `r > 0`. -/
theorem rpow_sub_two_mul_sq {r : ℝ} (hr : 0 < r) (q : ℝ) : r ^ (q - 2) * r ^ 2 = r ^ q := by
  have h2 : (r : ℝ) ^ (2 : ℕ) = r ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h2, ← Real.rpow_add hr, sub_add_cancel]

/-- If `a, b ≥ 0` and `a + b = 1` then `2^{1-p} ≤ a^{p-1} + b^{p-1}` (`p ≥ 1`): the larger of the
two is at least `1/2`. -/
theorem two_rpow_one_sub_le_rpow_add_rpow {p : ℝ} (hp : 1 ≤ p) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) : (2 : ℝ) ^ (1 - p) ≤ a ^ (p - 1) + b ^ (p - 1) := by
  have hq : (0 : ℝ) ≤ p - 1 := by linarith
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hhalf : ((1 : ℝ) / 2) ^ (p - 1) = (2 : ℝ) ^ (1 - p) := by
    rw [one_div, Real.inv_rpow h2 (p - 1), ← Real.rpow_neg h2 (p - 1), neg_sub]
  have hkey : ∀ s : ℝ, (1 : ℝ) / 2 ≤ s → (2 : ℝ) ^ (1 - p) ≤ s ^ (p - 1) := by
    intro s hs
    rw [← hhalf]
    exact Real.rpow_le_rpow (by norm_num) hs hq
  rcases le_or_gt ((1 : ℝ) / 2) a with h | h
  · have h1 : (0 : ℝ) ≤ b ^ (p - 1) := Real.rpow_nonneg hb _
    linarith [hkey a h]
  · have hb' : (1 : ℝ) / 2 ≤ b := by linarith
    have h1 : (0 : ℝ) ≤ a ^ (p - 1) := Real.rpow_nonneg ha _
    linarith [hkey b hb']

/-! ### Norms along a segment -/

/-- `‖ζ‖ - |t| ‖ξ - ζ‖ ≤ ‖ζ + t (ξ - ζ)‖`. -/
theorem norm_sub_le_norm_add_smul_sub_left (ζ ξ : Euc d) (t : ℝ) :
    ‖ζ‖ - |t| * ‖ξ - ζ‖ ≤ ‖ζ + t • (ξ - ζ)‖ := by
  have h : ζ + t • (ξ - ζ) - t • (ξ - ζ) = ζ := by module
  have h1 : ‖ζ + t • (ξ - ζ) - t • (ξ - ζ)‖ ≤ ‖ζ + t • (ξ - ζ)‖ + ‖t • (ξ - ζ)‖ :=
    norm_sub_le _ _
  rw [h, norm_smul, Real.norm_eq_abs] at h1
  linarith

/-- `‖ξ‖ - |1 - t| ‖ξ - ζ‖ ≤ ‖ζ + t (ξ - ζ)‖`. -/
theorem norm_sub_le_norm_add_smul_sub_right (ζ ξ : Euc d) (t : ℝ) :
    ‖ξ‖ - |1 - t| * ‖ξ - ζ‖ ≤ ‖ζ + t • (ξ - ζ)‖ := by
  have h : ζ + t • (ξ - ζ) + (1 - t) • (ξ - ζ) = ξ := by module
  have h1 : ‖ζ + t • (ξ - ζ) + (1 - t) • (ξ - ζ)‖
      ≤ ‖ζ + t • (ξ - ζ)‖ + ‖(1 - t) • (ξ - ζ)‖ := norm_add_le _ _
  rw [h, norm_smul, Real.norm_eq_abs] at h1
  linarith

/-- `‖ζ + t (ξ - ζ)‖ ≤ ‖ξ‖ + ‖ζ‖` for `t ∈ [0, 1]` (the segment lies in the ball of radius
`‖ξ‖ + ‖ζ‖`). -/
theorem norm_add_smul_sub_le (ζ ξ : Euc d) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖ζ + t • (ξ - ζ)‖ ≤ ‖ξ‖ + ‖ζ‖ := by
  have h : ζ + t • (ξ - ζ) = (1 - t) • ζ + t • ξ := by module
  have hle : ‖(1 - t) • ζ + t • ξ‖ ≤ ‖(1 - t) • ζ‖ + ‖t • ξ‖ := norm_add_le _ _
  have e1 : ‖(1 - t) • ζ‖ = (1 - t) * ‖ζ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
  have e2 : ‖t • ξ‖ = t * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  rw [e1, e2] at hle
  rw [h]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) (norm_nonneg ξ),
    mul_nonneg h0 (norm_nonneg ζ)]

/-! ### A lower bound for an interval integral -/

/-- If `g` is continuous on `[0, 1]`, nonnegative there, and at least `k` on a subinterval
`[a, b] ⊆ [0, 1]`, then `(b - a) k ≤ ∫₀¹ g`. -/
theorem le_intervalIntegral_of_le_on {g : ℝ → ℝ} (hgc : ContinuousOn g (uIcc (0 : ℝ) 1))
    {a b k : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hg0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t) (hgk : ∀ t ∈ Icc a b, k ≤ g t) :
    (b - a) * k ≤ ∫ t in (0 : ℝ)..1, g t := by
  have hsub : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 → uIcc u v ⊆ uIcc (0 : ℝ) 1 := by
    intro u v hu huv hv
    rw [uIcc_of_le huv, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hu hv
  have hint : IntervalIntegrable g volume 0 1 := hgc.intervalIntegrable
  have hi1 : IntervalIntegrable g volume 0 a :=
    hint.mono_set (hsub 0 a le_rfl ha (by linarith))
  have hi2 : IntervalIntegrable g volume a b := hint.mono_set (hsub a b ha hab hb)
  have hi3 : IntervalIntegrable g volume b 1 :=
    hint.mono_set (hsub b 1 (by linarith) hb le_rfl)
  have hi4 : IntervalIntegrable g volume 0 b :=
    hint.mono_set (hsub 0 b le_rfl (by linarith) hb)
  have hadd1 : (∫ t in (0 : ℝ)..a, g t) + (∫ t in a..b, g t) = ∫ t in (0 : ℝ)..b, g t :=
    intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hadd2 : (∫ t in (0 : ℝ)..b, g t) + (∫ t in b..1, g t) = ∫ t in (0 : ℝ)..1, g t :=
    intervalIntegral.integral_add_adjacent_intervals hi4 hi3
  have hn1 : 0 ≤ ∫ t in (0 : ℝ)..a, g t :=
    intervalIntegral.integral_nonneg ha fun u hu => hg0 u ⟨hu.1, by linarith [hu.2]⟩
  have hn3 : 0 ≤ ∫ t in b..1, g t :=
    intervalIntegral.integral_nonneg (by linarith) fun u hu => hg0 u ⟨by linarith [hu.1], hu.2⟩
  have hck : IntervalIntegrable (fun _ : ℝ => k) volume a b := intervalIntegrable_const
  have hn2 : (b - a) * k ≤ ∫ t in a..b, g t := by
    have h := intervalIntegral.integral_mono_on hab hck hi2 hgk
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h
  linarith

/-! ### Segments through the origin -/

/-- If the origin lies on the segment `[ζ, ξ]` then `ξ = a v` and `ζ = -(b v)` for the direction
`v = ξ - ζ` and weights `a, b ≥ 0` with `a + b = 1` (namely the barycentric coordinates of `0`,
read off without any division). -/
theorem exists_collinear_of_zero_mem_segment {ξ ζ : Euc d} (h0 : (0 : Euc d) ∈ segment ℝ ζ ξ) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ ξ = a • (ξ - ζ) ∧ ζ = -(b • (ξ - ζ)) := by
  obtain ⟨a, b, ha, hb, hab, hzero⟩ := h0
  have ha1 : a • ζ = -(b • ξ) := eq_neg_of_add_eq_zero_left hzero
  have hb1 : b • ξ = -(a • ζ) := eq_neg_of_add_eq_zero_right hzero
  refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
  · calc ξ = (a + b) • ξ := by rw [hab, one_smul]
      _ = a • ξ + b • ξ := add_smul a b ξ
      _ = a • ξ + -(a • ζ) := by rw [hb1]
      _ = a • (ξ - ζ) := by module
  · calc ζ = (a + b) • ζ := by rw [hab, one_smul]
      _ = a • ζ + b • ζ := add_smul a b ζ
      _ = -(b • ξ) + b • ζ := by rw [ha1]
      _ = -(b • (ξ - ζ)) := by module

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-! ### `(p-2)`-homogeneity of `A = Da` -/

/-- **`A = Da` is `(p-2)`-homogeneous**: `A(s ξ) w = s^{p-2} A(ξ) w` for `s > 0`, `ξ ≠ 0`.
Differentiate the homogeneity `a(s η) = s^{p-1} a(η)` (`flux_smul_of_pos`) along the line
`t ↦ s (ξ + t w)`. -/
theorem fderiv_flux_smul_apply {p : ℝ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) {ξ : Euc d}
    (hξ : ξ ≠ 0) (w : Euc d) :
    fderiv ℝ (flux p F) (s • ξ) w = s ^ (p - 2) • fderiv ℝ (flux p F) ξ w := by
  have hs0 : s ≠ 0 := hs.ne'
  have hsξ : s • ξ ≠ 0 := smul_ne_zero hs0 hξ
  have hline1 : HasDerivAt (fun t : ℝ => s • ξ + t • (s • w)) (s • w) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (s • w)).const_add (s • ξ)
  have hu1 : HasDerivAt (fun t : ℝ => flux p F (s • ξ + t • (s • w)))
      (fderiv ℝ (flux p F) (s • ξ) (s • w)) 0 :=
    (hF.hasFDerivAt_flux' p hsξ).comp_hasDerivAt_of_eq (0 : ℝ) hline1 (by simp)
  have hline2 : HasDerivAt (fun t : ℝ => ξ + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add ξ
  have hu2 : HasDerivAt (fun t : ℝ => flux p F (ξ + t • w)) (fderiv ℝ (flux p F) ξ w) 0 :=
    (hF.hasFDerivAt_flux' p hξ).comp_hasDerivAt_of_eq (0 : ℝ) hline2 (by simp)
  have hu3 : HasDerivAt (fun t : ℝ => s ^ (p - 1) • flux p F (ξ + t • w))
      (s ^ (p - 1) • fderiv ℝ (flux p F) ξ w) 0 :=
    HasDerivAt.fun_const_smul (s ^ (p - 1)) hu2
  have heq : (fun t : ℝ => flux p F (s • ξ + t • (s • w)))
      = fun t : ℝ => s ^ (p - 1) • flux p F (ξ + t • w) := by
    funext t
    have hv : s • ξ + t • (s • w) = s • (ξ + t • w) := by module
    rw [hv, hF.flux_smul_of_pos hp hs]
  rw [heq] at hu1
  have hkey : fderiv ℝ (flux p F) (s • ξ) (s • w) = s ^ (p - 1) • fderiv ℝ (flux p F) ξ w :=
    hu1.unique hu3
  simp only [map_smul] at hkey
  have hval : s ^ (p - 2) * s = s ^ (p - 1) := by
    have hexp : p - 2 + 1 = p - 1 := by ring
    rw [← Real.rpow_add_one hs0 (p - 2), hexp]
  have hcoef : s⁻¹ * s ^ (p - 1) = s ^ (p - 2) := by
    rw [← hval]
    have hrw : s⁻¹ * (s ^ (p - 2) * s) = s ^ (p - 2) * (s⁻¹ * s) := by ring
    rw [hrw, inv_mul_cancel₀ hs0, mul_one]
  have h5 : fderiv ℝ (flux p F) (s • ξ) w
      = s⁻¹ • (s • fderiv ℝ (flux p F) (s • ξ) w) := by
    rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [h5, hkey, smul_smul, hcoef]

/-- The scalar form of `fderiv_flux_smul_apply`. -/
theorem inner_fderiv_flux_smul {p : ℝ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) {ξ : Euc d}
    (hξ : ξ ≠ 0) (w : Euc d) :
    ⟪fderiv ℝ (flux p F) (s • ξ) w, w⟫ = s ^ (p - 2) * ⟪fderiv ℝ (flux p F) ξ w, w⟫ := by
  rw [hF.fderiv_flux_smul_apply hp hs hξ w, real_inner_smul_left]

/-! ### Scale invariant ellipticity of `A = Da` -/

/-- **Ellipticity on the unit sphere**: `∃ c₀ > 0` with `c₀ ‖w‖² ≤ ⟪A(η) w, w⟫` for every unit
vector `η`. (Compactness of `S¹ × S¹` and the pointwise positivity
`IsSmoothStrictNorm.inner_fderiv_flux_pos`; the same argument as the `μ` part of
`IsSmoothStrictNorm.exists_fderiv_flux_bounds`, but on the sphere rather than on a compact
convex set, so that homogeneity can propagate it to every `η ≠ 0`.) -/
theorem exists_pos_inner_fderiv_flux_sphere {p : ℝ} (hp : 1 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ η : Euc d, η ∈ Metric.sphere (0 : Euc d) 1 → ∀ w : Euc d,
      c * ‖w‖ ^ 2 ≤ ⟪fderiv ℝ (flux p F) η w, w⟫ := by
  have hS0 : Metric.sphere (0 : Euc d) 1 ⊆ {0}ᶜ := fun η hη =>
    Set.mem_compl_singleton_iff.2 (ne_zero_of_mem_sphere' hη)
  have hA1 : ContDiffOn ℝ 1 (fderiv ℝ (flux p F)) {0}ᶜ :=
    (hF.contDiffOn_flux' p).fderiv_of_isOpen isOpen_compl_singleton (WithTop.coe_le_coe.2 le_top)
  have hAc : ContinuousOn (fderiv ℝ (flux p F)) (Metric.sphere (0 : Euc d) 1) :=
    hA1.continuousOn.mono hS0
  by_cases hne : (Metric.sphere (0 : Euc d) 1 ×ˢ Metric.sphere (0 : Euc d) 1).Nonempty
  · have hcont : ContinuousOn (fun z : Euc d × Euc d => ⟪fderiv ℝ (flux p F) z.1 z.2, z.2⟫)
        (Metric.sphere (0 : Euc d) 1 ×ˢ Metric.sphere (0 : Euc d) 1) :=
      ((hAc.comp continuousOn_fst fun z hz => hz.1).clm_apply continuousOn_snd).inner
        continuousOn_snd
    obtain ⟨z, hz, hmin⟩ := ((isCompact_sphere (0 : Euc d) 1).prod
      (isCompact_sphere (0 : Euc d) 1)).exists_isMinOn hne hcont
    refine ⟨⟪fderiv ℝ (flux p F) z.1 z.2, z.2⟫, hF.inner_fderiv_flux_pos hp
      (ne_zero_of_mem_sphere' hz.1) (ne_zero_of_mem_sphere' hz.2), fun η hη w => ?_⟩
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hn' : ‖w‖ ≠ 0 := hn.ne'
    have hmem : (η, ‖w‖⁻¹ • w) ∈
        Metric.sphere (0 : Euc d) 1 ×ˢ Metric.sphere (0 : Euc d) 1 :=
      ⟨hη, by simp [norm_smul, inv_mul_cancel₀ hn.ne']⟩
    have h1 : ⟪fderiv ℝ (flux p F) z.1 z.2, z.2⟫ ≤
        ⟪fderiv ℝ (flux p F) η (‖w‖⁻¹ • w), ‖w‖⁻¹ • w⟫ := hmin hmem
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
    calc ⟪fderiv ℝ (flux p F) z.1 z.2, z.2⟫ * ‖w‖ ^ 2
        ≤ ‖w‖⁻¹ * (‖w‖⁻¹ * ⟪fderiv ℝ (flux p F) η w, w⟫) * ‖w‖ ^ 2 := by gcongr
      _ = ⟪fderiv ℝ (flux p F) η w, w⟫ := by field_simp
  · refine ⟨1, one_pos, fun η hη w => ?_⟩
    exact absurd (⟨(η, η), hη, hη⟩ :
      (Metric.sphere (0 : Euc d) 1 ×ˢ Metric.sphere (0 : Euc d) 1).Nonempty) hne

/-- **Scale invariant ellipticity** (paper (A.ellipticity)): `∃ c₀ > 0` with
`c₀ ‖η‖^{p-2} ‖w‖² ≤ ⟪A(η) w, w⟫` for every `η ≠ 0` and every `w`. -/
theorem exists_pos_rpow_mul_normSq_le_inner_fderiv_flux {p : ℝ} (hp : 1 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ η : Euc d, η ≠ 0 → ∀ w : Euc d,
      c * (‖η‖ ^ (p - 2) * ‖w‖ ^ 2) ≤ ⟪fderiv ℝ (flux p F) η w, w⟫ := by
  obtain ⟨c, hc, hsph⟩ := hF.exists_pos_inner_fderiv_flux_sphere hp
  refine ⟨c, hc, fun η hη w => ?_⟩
  have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
  obtain ⟨u, hu_def⟩ : ∃ u : Euc d, u = ‖η‖⁻¹ • η := ⟨_, rfl⟩
  have hu : u ∈ Metric.sphere (0 : Euc d) 1 := by
    rw [hu_def]
    simp [norm_smul, inv_mul_cancel₀ hn.ne']
  have hu0 : u ≠ 0 := ne_zero_of_mem_sphere' hu
  have hηu : η = ‖η‖ • u := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have h : ⟪fderiv ℝ (flux p F) (‖η‖ • u) w, w⟫
      = ‖η‖ ^ (p - 2) * ⟪fderiv ℝ (flux p F) u w, w⟫ :=
    hF.inner_fderiv_flux_smul hp hn hu0 w
  rw [← hηu] at h
  rw [h]
  have hpow : (0 : ℝ) ≤ ‖η‖ ^ (p - 2) := Real.rpow_nonneg hn.le _
  calc c * (‖η‖ ^ (p - 2) * ‖w‖ ^ 2) = ‖η‖ ^ (p - 2) * (c * ‖w‖ ^ 2) := by ring
    _ ≤ ‖η‖ ^ (p - 2) * ⟪fderiv ℝ (flux p F) u w, w⟫ :=
        mul_le_mul_of_nonneg_left (hsph u hu w) hpow

/-! ### The scalar mean value formula for the flux -/

/-- **Scalar mean value formula**: on a convex set `N` avoiding the origin,
`⟪a(ξ) - a(ζ), ξ - ζ⟫ = ∫₀¹ ⟪A(ζ + t(ξ-ζ))(ξ-ζ), ξ-ζ⟫ dt`. (The fundamental theorem of
calculus for `t ↦ ⟪a(ζ + t(ξ-ζ)), ξ - ζ⟫`; the vector valued version is
`IsSmoothStrictNorm.flux_sub_eq_integral_fderiv`.) -/
theorem inner_flux_sub_eq_intervalIntegral (p : ℝ) {N : Set (Euc d)} (hNcv : Convex ℝ N)
    (hN0 : (0 : Euc d) ∉ N) {ξ ζ : Euc d} (hζ : ζ ∈ N) (hξ : ξ ∈ N) :
    ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ =
      ∫ t in (0 : ℝ)..1, ⟪fderiv ℝ (flux p F) (ζ + t • (ξ - ζ)) (ξ - ζ), ξ - ζ⟫ := by
  have hne : ∀ t ∈ uIcc (0 : ℝ) 1, ζ + t • (ξ - ζ) ≠ 0 := by
    intro t ht h
    rw [uIcc_of_le zero_le_one] at ht
    exact hN0 (h ▸ hNcv.add_smul_sub_mem hζ hξ ht)
  have hA1 : ContinuousOn (fderiv ℝ (flux p F)) {0}ᶜ :=
    (hF.contDiffOn_flux' p).continuousOn_fderiv_of_isOpen isOpen_compl_singleton
      (by exact_mod_cast le_top)
  have hAline : ContinuousOn (fun t : ℝ => fderiv ℝ (flux p F) (ζ + t • (ξ - ζ))) (uIcc 0 1) :=
    hA1.comp (by fun_prop : Continuous fun t : ℝ => ζ + t • (ξ - ζ)).continuousOn
      fun t ht => hne t ht
  have hcont : ContinuousOn
      (fun t : ℝ => ⟪fderiv ℝ (flux p F) (ζ + t • (ξ - ζ)) (ξ - ζ), ξ - ζ⟫) (uIcc 0 1) :=
    (hAline.clm_apply continuousOn_const).inner continuousOn_const
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => ⟪flux p F (ζ + t • (ξ - ζ)), ξ - ζ⟫)
        ⟪fderiv ℝ (flux p F) (ζ + t • (ξ - ζ)) (ξ - ζ), ξ - ζ⟫ t := by
    intro t ht
    have hl : HasDerivAt (fun t : ℝ => ζ + t • (ξ - ζ)) (ξ - ζ) t := by
      simpa using ((hasDerivAt_id t).smul_const (ξ - ζ)).const_add ζ
    have hc : HasDerivAt (fun t : ℝ => flux p F (ζ + t • (ξ - ζ)))
        (fderiv ℝ (flux p F) (ζ + t • (ξ - ζ)) (ξ - ζ)) t :=
      (hF.hasFDerivAt_flux' p (hne t ht)).comp_hasDerivAt_of_eq t hl rfl
    simpa using hc.inner ℝ (hasDerivAt_const t (ξ - ζ))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [one_smul, zero_smul, add_zero, add_sub_cancel] at hFTC
  rw [inner_sub_left, ← hFTC]

/-! ### The lower bound over a segment avoiding the origin -/

/-- **Quantitative monotonicity on a segment avoiding the origin.** With the scale invariant
ellipticity `c₀ ‖η‖^{p-2} ‖w‖² ≤ ⟪A(η) w, w⟫` and a lower bound `m ≤ ‖ζ + t(ξ-ζ)‖^{p-2}` valid on
a subinterval `[a, b] ⊆ [0, 1]`, the mean value formula gives
`(b - a) c₀ m ‖ξ - ζ‖² ≤ ⟪a(ξ) - a(ζ), ξ - ζ⟫`. -/
theorem le_inner_flux_sub_of_segment {p c₀ m : ℝ} (hc₀ : 0 ≤ c₀) (hm : 0 ≤ m)
    (hell : ∀ η : Euc d, η ≠ 0 → ∀ w : Euc d,
      c₀ * (‖η‖ ^ (p - 2) * ‖w‖ ^ 2) ≤ ⟪fderiv ℝ (flux p F) η w, w⟫)
    {ξ ζ : Euc d} (h0 : (0 : Euc d) ∉ segment ℝ ζ ξ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hmb : ∀ t ∈ Icc a b, m ≤ ‖ζ + t • (ξ - ζ)‖ ^ (p - 2)) :
    (b - a) * (c₀ * (m * ‖ξ - ζ‖ ^ 2)) ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ := by
  have hNcv : Convex ℝ (segment ℝ ζ ξ) := convex_segment ζ ξ
  have hζN : ζ ∈ segment ℝ ζ ξ := left_mem_segment ℝ ζ ξ
  have hξN : ξ ∈ segment ℝ ζ ξ := right_mem_segment ℝ ζ ξ
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, ζ + t • (ξ - ζ) ≠ 0 := by
    intro t ht h
    exact h0 (h ▸ hNcv.add_smul_sub_mem hζN hξN ht)
  have hIcc : uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := uIcc_of_le zero_le_one
  have hA1 : ContinuousOn (fderiv ℝ (flux p F)) {0}ᶜ :=
    (hF.contDiffOn_flux' p).continuousOn_fderiv_of_isOpen isOpen_compl_singleton
      (by exact_mod_cast le_top)
  have hAline : ContinuousOn (fun t : ℝ => fderiv ℝ (flux p F) (ζ + t • (ξ - ζ)))
      (uIcc (0 : ℝ) 1) := by
    refine hA1.comp (by fun_prop : Continuous fun t : ℝ => ζ + t • (ξ - ζ)).continuousOn ?_
    intro t ht
    rw [hIcc] at ht
    exact hne t ht
  have hgc : ContinuousOn
      (fun t : ℝ => ⟪fderiv ℝ (flux p F) (ζ + t • (ξ - ζ)) (ξ - ζ), ξ - ζ⟫) (uIcc (0 : ℝ) 1) :=
    (hAline.clm_apply continuousOn_const).inner continuousOn_const
  have hg0 : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ ⟪fderiv ℝ (flux p F) (ζ + t • (ξ - ζ)) (ξ - ζ), ξ - ζ⟫ := by
    intro t ht
    refine le_trans ?_ (hell _ (hne t ht) (ξ - ζ))
    have h1 : (0 : ℝ) ≤ ‖ζ + t • (ξ - ζ)‖ ^ (p - 2) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : (0 : ℝ) ≤ ‖ξ - ζ‖ ^ 2 := sq_nonneg _
    exact mul_nonneg hc₀ (mul_nonneg h1 h2)
  have hgk : ∀ t ∈ Icc a b, c₀ * (m * ‖ξ - ζ‖ ^ 2) ≤
      ⟪fderiv ℝ (flux p F) (ζ + t • (ξ - ζ)) (ξ - ζ), ξ - ζ⟫ := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
    refine le_trans ?_ (hell _ (hne t ht01) (ξ - ζ))
    have hmt : m ≤ ‖ζ + t • (ξ - ζ)‖ ^ (p - 2) := hmb t ht
    have h2 : (0 : ℝ) ≤ ‖ξ - ζ‖ ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmt h2) hc₀
  rw [hF.inner_flux_sub_eq_intervalIntegral p hNcv h0 hζN hξN]
  exact le_intervalIntegral_of_le_on hgc ha hab hb hg0 hgk

/-! ### The configurations with the origin on the segment -/

/-- The homogeneity `a(s ξ) = s^{p-1} a(ξ)` of `IsSmoothStrictNorm.flux_smul_of_pos`, extended to
`s = 0` (where both sides vanish, `p > 1`). -/
theorem flux_smul_of_nonneg {p : ℝ} (hp : 1 < p) {s : ℝ} (hs : 0 ≤ s) (ξ : Euc d) :
    flux p F (s • ξ) = s ^ (p - 1) • flux p F ξ := by
  rcases hs.lt_or_eq with h | h
  · exact hF.flux_smul_of_pos hp h ξ
  · rw [← h, zero_smul, flux_zero hp hF, Real.zero_rpow (by linarith : p - 1 ≠ 0), zero_smul]

/-- **Quantitative monotonicity on a line through the origin.** If `a, b ≥ 0` and `a + b = 1`,
then `⟪a(a v) - a(-(b v)), a v - (-(b v))⟫ = (a^{p-1} + b^{p-1}) F(v)^p`, which is at least
`2^{1-p} c₁^p ‖v‖^p` whenever `c₁ ‖·‖ ≤ F`. These are exactly the configurations `(ξ, ζ)` whose
segment contains the origin. -/
theorem le_inner_flux_sub_of_collinear {p c₁ : ℝ} (hp : 1 < p) (hc₁ : 0 < c₁)
    (hc₁F : ∀ η : Euc d, c₁ * ‖η‖ ≤ F η) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (v : Euc d) :
    (2 : ℝ) ^ (1 - p) * c₁ ^ p * ‖a • v - -(b • v)‖ ^ p
      ≤ ⟪flux p F (a • v) - flux p F (-(b • v)), a • v - -(b • v)⟫ := by
  have hv : a • v - -(b • v) = v := by
    rw [sub_neg_eq_add, ← add_smul, hab, one_smul]
  rw [hv]
  have hsub : flux p F (a • v) - flux p F (-(b • v))
      = (a ^ (p - 1) + b ^ (p - 1)) • flux p F v := by
    rw [hF.flux_smul_of_nonneg hp ha, hF.flux_neg hp, hF.flux_smul_of_nonneg hp hb,
      sub_neg_eq_add, ← add_smul]
  rw [hsub, real_inner_smul_left, hF.inner_flux_self_eq_rpow hp]
  have hsum : (2 : ℝ) ^ (1 - p) ≤ a ^ (p - 1) + b ^ (p - 1) :=
    two_rpow_one_sub_le_rpow_add_rpow hp.le ha hb hab
  have hFv : c₁ ^ p * ‖v‖ ^ p ≤ F v ^ p := by
    rw [← Real.mul_rpow hc₁.le (norm_nonneg v)]
    exact Real.rpow_le_rpow (mul_nonneg hc₁.le (norm_nonneg v)) (hc₁F v) (by linarith)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 - p) := Real.rpow_pos_of_pos (by norm_num) _
  have hFnn : (0 : ℝ) ≤ F v ^ p := Real.rpow_nonneg (hF.nonneg v) _
  calc (2 : ℝ) ^ (1 - p) * c₁ ^ p * ‖v‖ ^ p
      = (2 : ℝ) ^ (1 - p) * (c₁ ^ p * ‖v‖ ^ p) := by ring
    _ ≤ (2 : ℝ) ^ (1 - p) * F v ^ p := mul_le_mul_of_nonneg_left hFv h2.le
    _ ≤ (a ^ (p - 1) + b ^ (p - 1)) * F v ^ p := mul_le_mul_of_nonneg_right hsum hFnn

/-! ### Strong monotonicity for `p ≥ 2` -/

/-- **Quantitative strong monotonicity of the flux for `p ≥ 2`**:
`∃ c > 0, ∀ ξ ζ, c ‖ξ - ζ‖^p ≤ ⟪a(ξ) - a(ζ), ξ - ζ⟫`.

Away from the degenerate configurations this is the mean value formula plus the scale invariant
ellipticity, together with the elementary observation that on one of the two subintervals
`[0, 1/8]`, `[7/8, 1]` the segment `t ↦ ζ + t(ξ - ζ)` stays at distance `≥ ‖ξ - ζ‖/8` from the
origin. If the origin lies on the segment the pairing is computed exactly by homogeneity and
Euler's identity (`le_inner_flux_sub_of_collinear`). -/
theorem exists_pos_norm_rpow_le_inner_flux_sub {p : ℝ} (hp : 2 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ ζ : Euc d,
      c * ‖ξ - ζ‖ ^ p ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ := by
  have hp1 : 1 < p := by linarith
  have hp0 : p ≠ 0 := by linarith
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨1, one_pos, fun ξ ζ => ?_⟩
    have hξζ : ξ = ζ := Subsingleton.elim _ _
    rw [hξζ]
    simp [Real.zero_rpow hp0]
  haveI : Nonempty (Fin d) := hd
  obtain ⟨c₀, hc₀, hell⟩ := hF.exists_pos_rpow_mul_normSq_le_inner_fderiv_flux hp1
  obtain ⟨c₁, hc₁, hc₁F⟩ := hF.exists_pos_mul_norm_le
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = ((1 : ℝ) / 8) ^ (p - 2) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκ_def]
    exact Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min (c₀ * κ / 8) ((2 : ℝ) ^ (1 - p) * c₁ ^ p),
    lt_min (div_pos (mul_pos hc₀ hκ) (by norm_num))
      (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_pos_of_pos hc₁ _)), fun ξ ζ => ?_⟩
  rcases eq_or_ne ξ ζ with rfl | hne
  · simp [Real.zero_rpow hp0]
  have hr : 0 < ‖ξ - ζ‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  have hrp : (0 : ℝ) ≤ ‖ξ - ζ‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  by_cases h0 : (0 : Euc d) ∈ segment ℝ ζ ξ
  · obtain ⟨a, b, ha, hb, hab, hξv, hζv⟩ := exists_collinear_of_zero_mem_segment h0
    have hkey := hF.le_inner_flux_sub_of_collinear hp1 hc₁ hc₁F ha hb hab (ξ - ζ)
    rw [← hξv, ← hζv] at hkey
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hrp) hkey
  · have hm0 : (0 : ℝ) ≤ (‖ξ - ζ‖ / 8) ^ (p - 2) := Real.rpow_nonneg (by positivity) _
    have hquarter : ‖ξ - ζ‖ / 4 ≤ ‖ζ‖ ∨ 3 * ‖ξ - ζ‖ / 4 ≤ ‖ξ‖ := by
      rcases le_or_gt (‖ξ - ζ‖ / 4) ‖ζ‖ with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        have h1 : ‖ξ - ζ‖ ≤ ‖ξ‖ + ‖ζ‖ := norm_sub_le ξ ζ
        linarith
    have hmain : (1 / 8 : ℝ) * (c₀ * ((‖ξ - ζ‖ / 8) ^ (p - 2) * ‖ξ - ζ‖ ^ 2))
        ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ := by
      rcases hquarter with hA | hB
      · have hmb : ∀ t ∈ Icc (0 : ℝ) (1 / 8),
            (‖ξ - ζ‖ / 8) ^ (p - 2) ≤ ‖ζ + t • (ξ - ζ)‖ ^ (p - 2) := by
          intro t ht
          have h1 : ‖ζ‖ - |t| * ‖ξ - ζ‖ ≤ ‖ζ + t • (ξ - ζ)‖ :=
            norm_sub_le_norm_add_smul_sub_left ζ ξ t
          rw [abs_of_nonneg ht.1] at h1
          have h3 : t * ‖ξ - ζ‖ ≤ (1 / 8) * ‖ξ - ζ‖ :=
            mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          have h2 : ‖ξ - ζ‖ / 8 ≤ ‖ζ + t • (ξ - ζ)‖ := by linarith
          exact Real.rpow_le_rpow (by positivity) h2 (by linarith)
        have hbound := hF.le_inner_flux_sub_of_segment hc₀.le hm0 hell h0
          (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1) hmb
        rwa [sub_zero] at hbound
      · have hmb : ∀ t ∈ Icc (7 / 8 : ℝ) 1,
            (‖ξ - ζ‖ / 8) ^ (p - 2) ≤ ‖ζ + t • (ξ - ζ)‖ ^ (p - 2) := by
          intro t ht
          have h1 : ‖ξ‖ - |1 - t| * ‖ξ - ζ‖ ≤ ‖ζ + t • (ξ - ζ)‖ :=
            norm_sub_le_norm_add_smul_sub_right ζ ξ t
          rw [abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)] at h1
          have h3 : (1 - t) * ‖ξ - ζ‖ ≤ (1 / 8) * ‖ξ - ζ‖ :=
            mul_le_mul_of_nonneg_right (by linarith [ht.1]) (norm_nonneg _)
          have h2 : ‖ξ - ζ‖ / 8 ≤ ‖ζ + t • (ξ - ζ)‖ := by linarith
          exact Real.rpow_le_rpow (by positivity) h2 (by linarith)
        have hbound := hF.le_inner_flux_sub_of_segment hc₀.le hm0 hell h0
          (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (7 / 8 : ℝ) ≤ 1) (le_refl (1 : ℝ)) hmb
        have he : (1 : ℝ) - 7 / 8 = 1 / 8 := by norm_num
        rwa [he] at hbound
    refine le_trans ?_ hmain
    have harith : (1 / 8 : ℝ) * (c₀ * ((‖ξ - ζ‖ / 8) ^ (p - 2) * ‖ξ - ζ‖ ^ 2))
        = c₀ * κ / 8 * ‖ξ - ζ‖ ^ p := by
      have hdiv : (‖ξ - ζ‖ / 8 : ℝ) = ‖ξ - ζ‖ * (1 / 8) := by ring
      have h1 : (‖ξ - ζ‖ / 8 : ℝ) ^ (p - 2) = ‖ξ - ζ‖ ^ (p - 2) * κ := by
        rw [hdiv, hκ_def,
          ← Real.mul_rpow (norm_nonneg (ξ - ζ)) (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      rw [h1]
      calc (1 / 8 : ℝ) * (c₀ * (‖ξ - ζ‖ ^ (p - 2) * κ * ‖ξ - ζ‖ ^ 2))
          = c₀ * κ / 8 * (‖ξ - ζ‖ ^ (p - 2) * ‖ξ - ζ‖ ^ 2) := by ring
        _ = c₀ * κ / 8 * ‖ξ - ζ‖ ^ p := by rw [rpow_sub_two_mul_sq hr p]
    rw [harith]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hrp

/-! ### Monotonicity for `1 < p < 2` -/

/-- **Quantitative strong monotonicity of the flux for `1 < p < 2`**:
`∃ c > 0, ∀ (ξ, ζ) ≠ (0, 0), c ((‖ξ‖ + ‖ζ‖)^{p-2} ‖ξ - ζ‖²) ≤ ⟪a(ξ) - a(ζ), ξ - ζ⟫`.

In this range the exponent `p - 2` is negative, so `‖ζ + t(ξ - ζ)‖ ≤ ‖ξ‖ + ‖ζ‖` already bounds
the integrand `c₀ ‖ζ + t(ξ - ζ)‖^{p-2} ‖ξ - ζ‖²` of the mean value formula from below on all of
`[0, 1]`. The `‖ξ - ζ‖^p` shape of `exists_pos_norm_rpow_le_inner_flux_sub` is *false* here
(take `ζ` fixed and `ξ → ζ`). -/
theorem exists_pos_mul_normSq_le_inner_flux_sub {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ ζ : Euc d, (ξ, ζ) ≠ ((0 : Euc d), (0 : Euc d)) →
      c * ((‖ξ‖ + ‖ζ‖) ^ (p - 2) * ‖ξ - ζ‖ ^ 2) ≤ ⟪flux p F ξ - flux p F ζ, ξ - ζ⟫ := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨1, one_pos, fun ξ ζ hne => ?_⟩
    exfalso
    apply hne
    have h1 : ξ = 0 := Subsingleton.elim _ _
    have h2 : ζ = 0 := Subsingleton.elim _ _
    rw [h1, h2]
  haveI : Nonempty (Fin d) := hd
  obtain ⟨c₀, hc₀, hell⟩ := hF.exists_pos_rpow_mul_normSq_le_inner_fderiv_flux hp1
  obtain ⟨c₁, hc₁, hc₁F⟩ := hF.exists_pos_mul_norm_le
  refine ⟨min c₀ ((2 : ℝ) ^ (1 - p) * c₁ ^ p),
    lt_min hc₀ (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hc₁ _)), fun ξ ζ _ => ?_⟩
  rcases eq_or_ne ξ ζ with rfl | hne'
  · simp
  have hr : 0 < ‖ξ - ζ‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne'
  have hrp : (0 : ℝ) ≤ ‖ξ - ζ‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
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
    have hkey := hF.le_inner_flux_sub_of_collinear hp1 hc₁ hc₁F ha hb hab (ξ - ζ)
    rw [← hξv, ← hζv] at hkey
    refine le_trans ?_ hkey
    rw [hsum, rpow_sub_two_mul_sq hr p]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hrp
  · have hpos : 0 < ‖ξ‖ + ‖ζ‖ := lt_of_lt_of_le hr (norm_sub_le ξ ζ)
    have hm0 : (0 : ℝ) ≤ (‖ξ‖ + ‖ζ‖) ^ (p - 2) := Real.rpow_nonneg hpos.le _
    have hmb : ∀ t ∈ Icc (0 : ℝ) 1,
        (‖ξ‖ + ‖ζ‖) ^ (p - 2) ≤ ‖ζ + t • (ξ - ζ)‖ ^ (p - 2) := by
      intro t ht
      have hle : ‖ζ + t • (ξ - ζ)‖ ≤ ‖ξ‖ + ‖ζ‖ := norm_add_smul_sub_le ζ ξ ht.1 ht.2
      have hne0 : ζ + t • (ξ - ζ) ≠ 0 := by
        intro h
        exact h0 (h ▸ (convex_segment ζ ξ).add_smul_sub_mem (left_mem_segment ℝ ζ ξ)
          (right_mem_segment ℝ ζ ξ) ht)
      exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.2 hne0) hle (by linarith)
    have hbound := hF.le_inner_flux_sub_of_segment hc₀.le hm0 hell h0
      (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) (le_refl (1 : ℝ)) hmb
    rw [sub_zero, one_mul] at hbound
    refine le_trans ?_ hbound
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (mul_nonneg hm0 (sq_nonneg _))

end IsSmoothStrictNorm

end Komlos.Literature
