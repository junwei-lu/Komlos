import Komlos.Eigenvalue
import Komlos.Literature.PLaplacian.Rayleigh

/-!
# Smooth strictly convex norms and the flux (paper Appendix A)

The integrand class of paper Proposition A.1 and the flux of the anisotropic `p`-Laplacian.

* `IsSmoothStrictNorm F`: "a norm on `ℝ^d`, smooth away from zero, with `D²(F²)` positive definite
  there", with its elementary consequences (continuity, two-sided comparison with the Euclidean
  norm, fixed-`ξ` uniform positivity of the Hessian of `F²`).
* `flux p F ξ = F(ξ)^{p-1} ∇F(ξ)`, the flux `a(ξ)` of paper Appendix A (*Eigenfunction inputs*).
* `eventually_hasDerivAt_line`, `hasDerivAt_fderiv_line`: first and second derivatives along lines.

These declarations were split off `Komlos.Literature.PLaplacian.EigenfunctionData` so that the
direct method (`Eigenfunction.lean`) and the regularity inputs (`Regularity.lean`,
`LogConcave.lean`) can use them while `EigenfunctionData.lean` assembles `exists_eigenfunctionData`
from those files.

## Encoding of the strong convexity

"`D²(F²)` positive definite away from zero" is encoded pointwise, with the second Fréchet
derivative `fderiv ℝ (fderiv ℝ (F²)) ξ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ`:
`∀ ξ ≠ 0, ∀ ζ ≠ 0, 0 < fderiv ℝ (fderiv ℝ (fun x => F x ^ 2)) ξ ζ ζ`.
On the open set `{0}ᶜ` where `F` is smooth this is the genuine Hessian
(`iteratedFDeriv_two_apply`). Uniform ellipticity constants on the unit sphere, as in paper
(A.ellipticity), follow from this by compactness and `0`-homogeneity of `D²(F²)`;
`IsSmoothStrictNorm.exists_pos_mul_normSq_le_hessian` records the fixed-`ξ` version.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Smooth strictly convex norms -/

/-- The integrand class of paper Proposition A.1 (and of the smooth case of Lemma 3.2): `F` is a
norm on `ℝ^d` (`even`, `pos`, `homog`, `convexOn`), smooth away from the origin (`contDiffOn`),
with `D²(F²)` positive definite away from the origin (`hessian_sq_pos`; see the module docstring
for the encoding). The regularized mixture integrands `H_ε` satisfy this
(`Heps_isSmoothStrictNorm`). -/
structure IsSmoothStrictNorm (F : Euc d → ℝ) : Prop where
  /-- `F` is even. -/
  even : ∀ ξ, F (-ξ) = F ξ
  /-- `F` is positive away from the origin. -/
  pos : ∀ ξ, ξ ≠ 0 → 0 < F ξ
  /-- `F` is absolutely `1`-homogeneous. -/
  homog : ∀ (c : ℝ) (ξ : Euc d), F (c • ξ) = |c| * F ξ
  /-- `F` is convex (the triangle inequality). -/
  convexOn : ConvexOn ℝ Set.univ F
  /-- `F` is `C^∞` away from the origin. -/
  contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ
  /-- `D²(F²)` is positive definite away from the origin (paper: "with `D²(F²)` positive
  definite there"). -/
  hessian_sq_pos : ∀ ξ, ξ ≠ 0 → ∀ ζ, ζ ≠ 0 →
    0 < fderiv ℝ (fderiv ℝ (fun x => F x ^ 2)) ξ ζ ζ

/-- A point of the unit sphere is nonzero. -/
theorem ne_zero_of_mem_sphere' {η : Euc d} (hη : η ∈ Metric.sphere (0 : Euc d) 1) : η ≠ 0 := by
  rw [mem_sphere_zero_iff_norm] at hη
  exact norm_ne_zero_iff.1 (hη ▸ one_ne_zero)

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

theorem map_zero : F 0 = 0 := by
  simpa using hF.homog 0 0

theorem nonneg (ξ : Euc d) : 0 ≤ F ξ := by
  rcases eq_or_ne ξ 0 with rfl | h
  · rw [hF.map_zero]
  · exact (hF.pos ξ h).le

theorem eq_zero_iff {ξ : Euc d} : F ξ = 0 ↔ ξ = 0 :=
  ⟨fun h => by_contra fun h' => (hF.pos ξ h').ne' h, fun h => h ▸ hF.map_zero⟩

/-- `F` is `C^∞` at every nonzero point. -/
theorem contDiffAt {ξ : Euc d} (hξ : ξ ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) F ξ :=
  hF.contDiffOn.contDiffAt (isOpen_compl_singleton.mem_nhds hξ)

/-- `F²` is `C²` at every nonzero point. -/
theorem contDiffAt_sq {ξ : Euc d} (hξ : ξ ≠ 0) : ContDiffAt ℝ 2 (fun x => F x ^ 2) ξ :=
  ((hF.contDiffAt hξ).pow 2).of_le (WithTop.coe_le_coe.2 le_top)

/-- `F` is continuous on `{0}ᶜ`. -/
theorem continuousOn : ContinuousOn F {0}ᶜ := hF.contDiffOn.continuousOn

/-- `F` is bounded above by a multiple of the Euclidean norm (compactness of the unit sphere
plus homogeneity). -/
theorem exists_le_mul_norm : ∃ M : ℝ, ∀ ξ, F ξ ≤ M * ‖ξ‖ := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨0, fun ξ => ?_⟩
    have : ξ = 0 := Subsingleton.elim _ _
    simp [this, hF.map_zero]
  obtain ⟨M, hM⟩ : ∃ M, ∀ η ∈ Metric.sphere (0 : Euc d) 1, F η ≤ M := by
    have hc : IsCompact (F '' Metric.sphere (0 : Euc d) 1) :=
      (isCompact_sphere 0 1).image_of_continuousOn
        (hF.continuousOn.mono fun η hη => Set.mem_compl_singleton_iff.2 (ne_zero_of_mem_sphere' hη))
    obtain ⟨M, hM⟩ := hc.isBounded.bddAbove
    exact ⟨M, fun η hη => hM ⟨η, hη, rfl⟩⟩
  refine ⟨M, fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [hF.map_zero]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hη : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : Euc d) 1 := by
    simp [norm_smul, inv_mul_cancel₀ hn.ne']
  have h1 := hM _ hη
  rw [hF.homog, abs_of_pos (inv_pos.2 hn)] at h1
  calc F ξ = ‖ξ‖ * (‖ξ‖⁻¹ * F ξ) := by field_simp
    _ ≤ ‖ξ‖ * M := by gcongr
    _ = M * ‖ξ‖ := mul_comm _ _

/-- `F` is bounded below by a positive multiple of the Euclidean norm. -/
theorem exists_pos_mul_norm_le [Nonempty (Fin d)] : ∃ c : ℝ, 0 < c ∧ ∀ ξ, c * ‖ξ‖ ≤ F ξ := by
  have hne : (Metric.sphere (0 : Euc d) 1).Nonempty := by
    obtain ⟨η, hη⟩ := exists_ne (0 : Euc d)
    exact ⟨‖η‖⁻¹ • η, by simp [norm_smul, inv_mul_cancel₀ (norm_pos_iff.2 hη).ne']⟩
  obtain ⟨η₀, hη₀, hmin⟩ := (isCompact_sphere (0 : Euc d) 1).exists_isMinOn hne
    (hF.continuousOn.mono fun η hη => Set.mem_compl_singleton_iff.2 (ne_zero_of_mem_sphere' hη))
  refine ⟨F η₀, hF.pos η₀ (ne_zero_of_mem_sphere' hη₀), fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [hF.map_zero]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hη : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : Euc d) 1 := by
    simp [norm_smul, inv_mul_cancel₀ hn.ne']
  have h1 : F η₀ ≤ F (‖ξ‖⁻¹ • ξ) := hmin hη
  rw [hF.homog, abs_of_pos (inv_pos.2 hn)] at h1
  calc F η₀ * ‖ξ‖ ≤ ‖ξ‖⁻¹ * F ξ * ‖ξ‖ := by gcongr
    _ = F ξ := by field_simp

/-- `F` is continuous (on all of `ℝ^d`; at the origin by `F ≤ M‖·‖`). -/
theorem continuous : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
    rw [ContinuousAt, hF.map_zero]
    have h1 : Tendsto (fun ξ : Euc d => M * ‖ξ‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : Euc d)).const_mul M
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun ξ => hF.nonneg ξ) hM
  · exact hF.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hξ)

/-- Fixed-`ξ` uniform positivity of the Hessian of `F²`: at every `ξ ≠ 0` there is `c > 0` with
`c ‖ζ‖² ≤ D²(F²)(ξ)[ζ, ζ]` for all `ζ` (compactness of the unit sphere). -/
theorem exists_pos_mul_normSq_le_hessian {ξ : Euc d} (hξ : ξ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ ζ, c * ‖ζ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun x => F x ^ 2)) ξ ζ ζ := by
  set B := fderiv ℝ (fderiv ℝ (fun x => F x ^ 2)) ξ with hB
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · exact absurd (Subsingleton.elim ξ 0) hξ
  have hne : (Metric.sphere (0 : Euc d) 1).Nonempty := by
    obtain ⟨η, hη⟩ := exists_ne (0 : Euc d)
    exact ⟨‖η‖⁻¹ • η, by simp [norm_smul, inv_mul_cancel₀ (norm_pos_iff.2 hη).ne']⟩
  have hcont : Continuous fun ζ => B ζ ζ := by
    exact (B.continuous.clm_apply continuous_id)
  obtain ⟨ζ₀, hζ₀, hmin⟩ := (isCompact_sphere (0 : Euc d) 1).exists_isMinOn hne
    hcont.continuousOn
  refine ⟨B ζ₀ ζ₀, hF.hessian_sq_pos ξ hξ ζ₀ (ne_zero_of_mem_sphere' hζ₀), fun ζ => ?_⟩
  rcases eq_or_ne ζ 0 with rfl | hζ
  · simp
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  have hη : ‖ζ‖⁻¹ • ζ ∈ Metric.sphere (0 : Euc d) 1 := by
    simp [norm_smul, inv_mul_cancel₀ hn.ne']
  have h1 : B ζ₀ ζ₀ ≤ B (‖ζ‖⁻¹ • ζ) (‖ζ‖⁻¹ • ζ) := hmin hη
  simp only [map_smul, smul_eq_mul, FunLike.coe_smul, Pi.smul_apply] at h1
  calc B ζ₀ ζ₀ * ‖ζ‖ ^ 2 ≤ ‖ζ‖⁻¹ * (‖ζ‖⁻¹ * B ζ ζ) * ‖ζ‖ ^ 2 := by gcongr
    _ = B ζ ζ := by field_simp

end IsSmoothStrictNorm

/-! ### The flux `a(ξ) = F(ξ)^{p-1} ∇F(ξ)` -/

/-- The flux `a(ξ) = F(ξ)^{p-1} ∇F(ξ)` of paper Appendix A (*Eigenfunction inputs*), so that
`div a(∇u) + λ u^{p-1} = 0` is the (weak) eigenvalue equation. At `ξ = 0` the value is `0`
automatically for `p > 1` (since `F 0 = 0`), matching the paper's convention `a(0) = 0`. -/
noncomputable def flux (p : ℝ) (F : Euc d → ℝ) (ξ : Euc d) : Euc d :=
  F ξ ^ (p - 1) • gradient F ξ

theorem flux_zero {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) :
    flux p F 0 = 0 := by
  simp [flux, hF.map_zero, Real.zero_rpow (sub_pos.2 hp).ne']

/-! ### Derivatives along lines -/

/-- Along the line `t ↦ ξ + tζ`, near `t = 0`, `g` has derivative `Dg(ξ+tζ)ζ`. -/
theorem eventually_hasDerivAt_line {g : Euc d → ℝ} {ξ : Euc d} (hg : ContDiffAt ℝ 2 g ξ)
    (ζ : Euc d) :
    ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => g (ξ + t • ζ)) (fderiv ℝ g (ξ + t • ζ) ζ) t := by
  have hev : ∀ᶠ y in 𝓝 ξ, ContDiffAt ℝ 2 g y := hg.eventually (by simp)
  have hline : Continuous fun t : ℝ => ξ + t • ζ := by fun_prop
  have ht : Tendsto (fun t : ℝ => ξ + t • ζ) (𝓝 0) (𝓝 ξ) := by
    simpa using hline.tendsto 0
  filter_upwards [ht.eventually hev] with t ht
  have hd : HasFDerivAt g (fderiv ℝ g (ξ + t • ζ)) (ξ + t • ζ) :=
    (ht.differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ξ + t • ζ) ζ t := by
    simpa using ((hasDerivAt_id t).smul_const ζ).const_add ξ
  exact hd.comp_hasDerivAt t hl

/-- `t ↦ Dg(ξ+tζ)ζ` has derivative `D²g(ξ)[ζ,ζ]` at `t = 0`. -/
theorem hasDerivAt_fderiv_line {g : Euc d → ℝ} {ξ : Euc d} (hg : ContDiffAt ℝ 2 g ξ)
    (ζ : Euc d) :
    HasDerivAt (fun t : ℝ => fderiv ℝ g (ξ + t • ζ) ζ) (fderiv ℝ (fderiv ℝ g) ξ ζ ζ) 0 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) ξ := hg.fderiv_right (m := 1) (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) ξ) ξ :=
    (h1.differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ξ + t • ζ) ζ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add ξ
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ g (ξ + t • ζ)) (fderiv ℝ (fderiv ℝ g) ξ ζ) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  simpa using h2.clm_apply (hasDerivAt_const (0 : ℝ) ζ)

end Komlos.Literature
