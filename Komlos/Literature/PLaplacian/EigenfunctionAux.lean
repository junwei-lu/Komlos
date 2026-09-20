import Komlos.Literature.PLaplacian.SmoothStrictNorm

/-!
# Pointwise convexity and calculus of `F^p` for a smooth strictly convex norm

Auxiliary facts about the integrand `Φ(ξ) = F(ξ)^p`, for `F` a smooth strictly convex norm
(`IsSmoothStrictNorm`, the integrand class of paper Proposition A.1) and `1 < p`. They feed the
direct method of `Komlos.Literature.PLaplacian.Eigenfunction`.

* `rpow_sub_one_mul_le_add`, `add_rpow_le_two_rpow_mul`, `abs_rpow_sub_two_mul_abs` — elementary
  real inequalities used for domination;
* `IsSmoothStrictNorm.map_add_le_add`, `exists_lipschitzWith`, `exists_norm_gradient_le` — `F` is
  subadditive and Lipschitz, so `‖∇F‖` is bounded;
* `IsSmoothStrictNorm.eq_of_le_midpoint` — the unit ball of `F` is strictly convex (the Hessian
  of `F²` is positive definite at the midpoint of a flat segment, a contradiction);
* `rpow_midpoint_le`, `rpow_midpoint_lt` — midpoint convexity and strict midpoint convexity of
  `F^p`;
* `exists_norm_sub_rpow_le` — **uniform convexity** of `F^p`: for every `ε > 0` there is `C` with
  `‖ξ - η‖^p ≤ C (Φ(ξ)/2 + Φ(η)/2 - Φ((ξ+η)/2)) + ε (‖ξ‖ + ‖η‖)^p` (extreme value theorem on a
  compact subset of the unit sphere of `ℝ^d × ℝ^d`, then `p`-homogeneity);
* `hasFDerivAt_rpow`, `continuous_flux'`, `exists_norm_flux_le` — `Φ` is differentiable with
  `DΦ(ξ) = p ⟪a(ξ), ·⟫` for `a = flux p F`, `a` is continuous and `‖a(ξ)‖ ≤ C ‖ξ‖^{p-1}` (paper
  Appendix A, *Eigenfunction inputs*: "Also `F^p ∈ C¹(ℝ^d)`, since its gradient is
  `O(|ξ|^{p-1})` at zero").
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Elementary real inequalities -/

section RealIneq

variable {p : ℝ}

/-- A crude Young inequality: `s^{p-1} t ≤ s^p + t^p` for `s, t ≥ 0` and `p ≥ 1`. -/
theorem rpow_sub_one_mul_le_add (hp : 1 ≤ p) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s ^ (p - 1) * t ≤ s ^ p + t ^ p := by
  have hpow : ∀ r : ℝ, 0 ≤ r → r ^ (p - 1) * r = r ^ p := fun r hr => by
    rw [← Real.rpow_add_one' hr (ne_of_gt (by linarith)), sub_add_cancel]
  rcases le_total t s with h | h
  · calc s ^ (p - 1) * t ≤ s ^ (p - 1) * s := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hs _)
      _ = s ^ p := hpow s hs
      _ ≤ s ^ p + t ^ p := le_add_of_nonneg_right (Real.rpow_nonneg ht _)
  · calc s ^ (p - 1) * t ≤ t ^ (p - 1) * t :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs h (by linarith)) ht
      _ = t ^ p := hpow t ht
      _ ≤ s ^ p + t ^ p := le_add_of_nonneg_left (Real.rpow_nonneg hs _)

/-- `(s + t)^p ≤ 2^p (s^p + t^p)` for `s, t ≥ 0` and `p ≥ 0`. -/
theorem add_rpow_le_two_rpow_mul (hp : 0 ≤ p) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s + t) ^ p ≤ 2 ^ p * (s ^ p + t ^ p) := by
  have h2 : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) _
  rcases le_total s t with h | h
  · calc (s + t) ^ p ≤ (2 * t) ^ p := Real.rpow_le_rpow (add_nonneg hs ht) (by linarith) hp
      _ = 2 ^ p * t ^ p := Real.mul_rpow (by norm_num) ht
      _ ≤ 2 ^ p * (s ^ p + t ^ p) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg hs _)) h2
  · calc (s + t) ^ p ≤ (2 * s) ^ p := Real.rpow_le_rpow (add_nonneg hs ht) (by linarith) hp
      _ = 2 ^ p * s ^ p := Real.mul_rpow (by norm_num) hs
      _ ≤ 2 ^ p * (s ^ p + t ^ p) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg ht _)) h2

/-- `|s|^{p-2} |s| = |s|^{p-1}` for `p > 1`, including at `s = 0`. -/
theorem abs_rpow_sub_two_mul_abs (hp : 1 < p) (s : ℝ) : |s| ^ (p - 2) * |s| = |s| ^ (p - 1) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Real.zero_rpow (sub_pos.2 hp).ne']
  · rw [← Real.rpow_add_one (abs_pos.2 hs).ne']
    congr 1
    ring

end RealIneq

/-! ### Smooth strictly convex norms: Lipschitz bound and strict convexity -/

/-- The midpoint convexity defect `Φ(ξ)/2 + Φ(η)/2 - Φ((ξ + η)/2)` of `Φ = F^p`. -/
noncomputable def midDefect (p : ℝ) (F : Euc d → ℝ) (ξ η : Euc d) : ℝ :=
  F ξ ^ p / 2 + F η ^ p / 2 - F ((1 / 2 : ℝ) • (ξ + η)) ^ p

namespace IsSmoothStrictNorm

variable {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
include hF

/-- Subadditivity (the triangle inequality) of `F`, from convexity and homogeneity. (The same
statement is `IsSmoothStrictNorm.add_le` in `WangXia/EigenvalueConvexAssemblyAux`, which this file
does not import; the name differs to avoid a clash.) -/
theorem map_add_le_add (ξ η : Euc d) : F (ξ + η) ≤ F ξ + F η := by
  have h := hF.convexOn.2 (mem_univ ξ) (mem_univ η) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : ξ + η = (2 : ℝ) • ((1 / 2 : ℝ) • ξ + (1 / 2 : ℝ) • η) := by module
  rw [e, hF.homog, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [smul_eq_mul] at h
  linarith

/-- `F (c • ξ)^p = c^p F(ξ)^p` for `c ≥ 0`. -/
theorem rpow_smul {p c : ℝ} (hc : 0 ≤ c) (ξ : Euc d) : F (c • ξ) ^ p = c ^ p * F ξ ^ p := by
  rw [hF.homog, abs_of_nonneg hc, Real.mul_rpow hc (hF.nonneg ξ)]

/-- `F ((ξ + η)/2) ≤ F(ξ)/2 + F(η)/2`. -/
theorem midpoint_le (ξ η : Euc d) : F ((1 / 2 : ℝ) • (ξ + η)) ≤ F ξ / 2 + F η / 2 := by
  rw [hF.homog, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := hF.map_add_le_add ξ η
  linarith

/-- `F` is Lipschitz. -/
theorem exists_lipschitzWith : ∃ L : NNReal, LipschitzWith L F := by
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  have hM' : ∀ ξ, F ξ ≤ max M 0 * ‖ξ‖ := fun ξ =>
    (hM ξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨⟨max M 0, le_max_right _ _⟩, LipschitzWith.of_dist_le_mul fun ξ η => ?_⟩
  have h1 : F ξ ≤ F η + max M 0 * ‖ξ - η‖ := by
    have h := hF.map_add_le_add η (ξ - η)
    have e : η + (ξ - η) = ξ := by abel
    rw [e] at h
    linarith [hM' (ξ - η)]
  have h2 : F η ≤ F ξ + max M 0 * ‖ξ - η‖ := by
    have h := hF.map_add_le_add ξ (η - ξ)
    have e : ξ + (η - ξ) = η := by abel
    rw [e] at h
    have h3 := hM' (η - ξ)
    rw [norm_sub_rev] at h3
    linarith
  rw [Real.dist_eq, dist_eq_norm]
  show |F ξ - F η| ≤ max M 0 * ‖ξ - η‖
  rw [abs_le]
  constructor <;> linarith

/-- The gradient of `F` is bounded (by a Lipschitz constant of `F`). -/
theorem exists_norm_gradient_le : ∃ L : ℝ, 0 ≤ L ∧ ∀ ξ, ‖gradient F ξ‖ ≤ L := by
  obtain ⟨L, hL⟩ := hF.exists_lipschitzWith
  refine ⟨L, L.2, fun ξ => ?_⟩
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hL

/-- **The unit ball of `F` is strictly convex**: if `F ξ = F η = r ≤ F ((ξ + η)/2)` then
`ξ = η`. Otherwise `F ≡ r > 0` on the segment `[ξ, η]` by convexity, so the second derivative of
`F²` at the midpoint in the direction `η - ξ` vanishes, contradicting `hessian_sq_pos`. -/
theorem eq_of_le_midpoint {ξ η : Euc d} {r : ℝ} (hξ : F ξ = r) (hη : F η = r)
    (hm : r ≤ F ((1 / 2 : ℝ) • (ξ + η))) : ξ = η := by
  by_contra hne
  have h0r : 0 ≤ r := hξ ▸ hF.nonneg ξ
  have hr : 0 < r := lt_of_le_of_ne h0r fun h =>
    hne (((hF.eq_zero_iff).1 (hξ.trans h.symm)).trans ((hF.eq_zero_iff).1 (hη.trans h.symm)).symm)
  have hw0 : η - ξ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  -- `F ≤ r` on the segment
  have hup : ∀ s ∈ Icc (0 : ℝ) 1, F (ξ + s • (η - ξ)) ≤ r := by
    intro s hs
    have h := hF.convexOn.2 (mem_univ ξ) (mem_univ η) (sub_nonneg.2 hs.2) hs.1 (by ring)
    have e : (1 - s) • ξ + s • η = ξ + s • (η - ξ) := by module
    rw [e, hξ, hη, smul_eq_mul, smul_eq_mul] at h
    have e2 : (1 - s) * r + s * r = r := by ring
    linarith
  -- `F ≥ r` on the segment
  have hlow : ∀ s ∈ Icc (0 : ℝ) 1, r ≤ F (ξ + s • (η - ξ)) := by
    intro s hs
    have h1 := hup (1 - s) ⟨sub_nonneg.2 hs.2, by linarith [hs.1]⟩
    have e : (1 / 2 : ℝ) • (ξ + η) =
        (1 / 2 : ℝ) • ((ξ + s • (η - ξ)) + (ξ + (1 - s) • (η - ξ))) := by module
    have h2 := hF.midpoint_le (ξ + s • (η - ξ)) (ξ + (1 - s) • (η - ξ))
    rw [← e] at h2
    linarith
  set m : Euc d := (1 / 2 : ℝ) • (ξ + η) with hm_def
  have hmline : ∀ t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2), F (m + t • (η - ξ)) = r := by
    intro t ht
    have e : m + t • (η - ξ) = ξ + (1 / 2 + t) • (η - ξ) := by rw [hm_def]; module
    have hs : 1 / 2 + t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [e]
    exact le_antisymm (hup _ hs) (hlow _ hs)
  have hm0 : m ≠ 0 := by
    intro h0
    have h := hmline 0 ⟨by norm_num, by norm_num⟩
    rw [zero_smul, add_zero, h0, hF.map_zero] at h
    linarith
  have hg : ContDiffAt ℝ 2 (fun x => F x ^ 2) m := hF.contDiffAt_sq hm0
  have hI : Ioo (-(1 / 2) : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  -- the first derivative of `F²` along the line vanishes near `0`
  have hD1 : ∀ᶠ t in 𝓝 (0 : ℝ), fderiv ℝ (fun x => F x ^ 2) (m + t • (η - ξ)) (η - ξ) = 0 := by
    filter_upwards [eventually_hasDerivAt_line hg (η - ξ), hI] with t ht htI
    have hconst : (fun t : ℝ => F (m + t • (η - ξ)) ^ 2) =ᶠ[𝓝 t] fun _ => r ^ 2 := by
      filter_upwards [Ioo_mem_nhds htI.1 htI.2] with s hs
      rw [hmline s hs]
    exact ht.unique ((hasDerivAt_const t (r ^ 2)).congr_of_eventuallyEq hconst)
  have h2 := hasDerivAt_fderiv_line hg (η - ξ)
  have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ (fun x => F x ^ 2) (m + t • (η - ξ)) (η - ξ)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hD1
  have key : fderiv ℝ (fderiv ℝ (fun x => F x ^ 2)) m (η - ξ) (η - ξ) = 0 := h2.unique h3
  have hpos := hF.hessian_sq_pos m hm0 (η - ξ) hw0
  rw [key] at hpos
  exact lt_irrefl _ hpos

variable {p : ℝ}

/-- Midpoint convexity of `F^p` (`p ≥ 1`). -/
theorem rpow_midpoint_le (hp : 1 ≤ p) (ξ η : Euc d) :
    F ((1 / 2 : ℝ) • (ξ + η)) ^ p ≤ F ξ ^ p / 2 + F η ^ p / 2 := by
  have h2 := (convexOn_rpow hp).2 (mem_Ici.2 (hF.nonneg ξ)) (mem_Ici.2 (hF.nonneg η))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h2
  calc F ((1 / 2 : ℝ) • (ξ + η)) ^ p ≤ (F ξ / 2 + F η / 2) ^ p :=
        Real.rpow_le_rpow (hF.nonneg _) (hF.midpoint_le ξ η) (by linarith)
    _ = (1 / 2 * F ξ + 1 / 2 * F η) ^ p := by congr 1; ring
    _ ≤ 1 / 2 * F ξ ^ p + 1 / 2 * F η ^ p := h2
    _ = F ξ ^ p / 2 + F η ^ p / 2 := by ring

/-- **Strict midpoint convexity of `F^p`** (`p > 1`): `F((ξ+η)/2)^p < F(ξ)^p/2 + F(η)^p/2` for
`ξ ≠ η`. If `F ξ ≠ F η` this is strict convexity of `t ↦ t^p`; if `F ξ = F η` it is strict
convexity of the unit ball (`eq_of_le_midpoint`). -/
theorem rpow_midpoint_lt (hp : 1 < p) {ξ η : Euc d} (hne : ξ ≠ η) :
    F ((1 / 2 : ℝ) • (ξ + η)) ^ p < F ξ ^ p / 2 + F η ^ p / 2 := by
  have hp0 : 0 < p := by linarith
  have h1 := hF.midpoint_le ξ η
  by_cases hFeq : F ξ = F η
  · have hlt : F ((1 / 2 : ℝ) • (ξ + η)) < F ξ := by
      refine lt_of_le_of_ne (by rw [← hFeq] at h1; linarith) fun h => hne ?_
      exact hF.eq_of_le_midpoint rfl hFeq.symm h.ge
    calc F ((1 / 2 : ℝ) • (ξ + η)) ^ p < F ξ ^ p := Real.rpow_lt_rpow (hF.nonneg _) hlt hp0
      _ = F ξ ^ p / 2 + F η ^ p / 2 := by rw [← hFeq]; ring
  · have h2 := (strictConvexOn_rpow hp).2 (mem_Ici.2 (hF.nonneg ξ)) (mem_Ici.2 (hF.nonneg η))
      hFeq (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at h2
    calc F ((1 / 2 : ℝ) • (ξ + η)) ^ p ≤ (F ξ / 2 + F η / 2) ^ p :=
          Real.rpow_le_rpow (hF.nonneg _) h1 hp0.le
      _ = (1 / 2 * F ξ + 1 / 2 * F η) ^ p := by congr 1; ring
      _ < 1 / 2 * F ξ ^ p + 1 / 2 * F η ^ p := h2
      _ = F ξ ^ p / 2 + F η ^ p / 2 := by ring

theorem midDefect_nonneg (hp : 1 ≤ p) (ξ η : Euc d) : 0 ≤ midDefect p F ξ η := by
  have := hF.rpow_midpoint_le hp ξ η
  simp only [midDefect]
  linarith

theorem midDefect_pos (hp : 1 < p) {ξ η : Euc d} (hne : ξ ≠ η) : 0 < midDefect p F ξ η := by
  have := hF.rpow_midpoint_lt hp hne
  simp only [midDefect]
  linarith

/-- The midpoint defect is `p`-homogeneous. -/
theorem midDefect_smul {c : ℝ} (hc : 0 ≤ c) (ξ η : Euc d) :
    midDefect p F (c • ξ) (c • η) = c ^ p * midDefect p F ξ η := by
  have e : (1 / 2 : ℝ) • (c • ξ + c • η) = c • ((1 / 2 : ℝ) • (ξ + η)) := by module
  simp only [midDefect, e, hF.rpow_smul hc]
  ring

theorem continuous_rpow (hp : 0 ≤ p) : Continuous fun ξ => F ξ ^ p :=
  hF.continuous.rpow_const fun _ => Or.inr hp

theorem continuous_midDefect (hp : 0 ≤ p) :
    Continuous fun z : Euc d × Euc d => midDefect p F z.1 z.2 := by
  have hΦ := hF.continuous_rpow hp
  unfold midDefect
  exact (((hΦ.comp continuous_fst).div_const 2).add ((hΦ.comp continuous_snd).div_const 2)).sub
    (hΦ.comp ((continuous_fst.add continuous_snd).const_smul (1 / 2 : ℝ)))

/-- **Uniform convexity of `F^p`** (`p > 1`): for every `ε > 0` there is `C ≥ 0` with
`‖ξ - η‖^p ≤ C (F(ξ)^p/2 + F(η)^p/2 - F((ξ+η)/2)^p) + ε (‖ξ‖ + ‖η‖)^p` for all `ξ, η`.

On the compact set `S = {‖ξ‖ + ‖η‖ = 1, ‖ξ - η‖^p ≥ ε}` the defect is continuous and positive
(`rpow_midpoint_lt`), hence bounded below by some `c > 0`; both sides are `p`-homogeneous. -/
theorem exists_norm_sub_rpow_le (hp : 1 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ η : Euc d,
      ‖ξ - η‖ ^ p ≤ C * midDefect p F ξ η + ε * (‖ξ‖ + ‖η‖) ^ p := by
  have hp0 : 0 < p := by linarith
  set S : Set (Euc d × Euc d) := {z | ‖z.1‖ + ‖z.2‖ = 1 ∧ ε ≤ ‖z.1 - z.2‖ ^ p} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · show IsClosed ({z : Euc d × Euc d | ‖z.1‖ + ‖z.2‖ = 1} ∩ {z | ε ≤ ‖z.1 - z.2‖ ^ p})
      refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_le continuous_const ?_)
      · exact (continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd)
      · exact (continuous_norm.comp (continuous_fst.sub continuous_snd)).rpow_const
          fun _ => Or.inr hp0.le
    · refine ((Metric.isBounded_closedBall (x := (0 : Euc d)) (r := 1)).prod
        (Metric.isBounded_closedBall (x := (0 : Euc d)) (r := 1))).subset ?_
      rintro z ⟨hz1, -⟩
      exact ⟨mem_closedBall_zero_iff.2 (by linarith [norm_nonneg z.2]),
        mem_closedBall_zero_iff.2 (by linarith [norm_nonneg z.1])⟩
  have hpos : ∀ z ∈ S, 0 < midDefect p F z.1 z.2 := by
    rintro z ⟨-, hz⟩
    refine hF.midDefect_pos hp fun h => ?_
    rw [h, sub_self, norm_zero, Real.zero_rpow hp0.ne'] at hz
    linarith
  -- the normalized pair lies in `S`
  have hmemS : ∀ ξ η : Euc d, 0 < ‖ξ‖ + ‖η‖ → ε * (‖ξ‖ + ‖η‖) ^ p ≤ ‖ξ - η‖ ^ p →
      ((‖ξ‖ + ‖η‖)⁻¹ • ξ, (‖ξ‖ + ‖η‖)⁻¹ • η) ∈ S := by
    intro ξ η hs h
    have hs' : 0 < (‖ξ‖ + ‖η‖)⁻¹ := inv_pos.2 hs
    refine ⟨?_, ?_⟩
    · simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hs']
      rw [← mul_add, inv_mul_cancel₀ hs.ne']
    · show ε ≤ ‖(‖ξ‖ + ‖η‖)⁻¹ • ξ - (‖ξ‖ + ‖η‖)⁻¹ • η‖ ^ p
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs',
        Real.mul_rpow hs'.le (norm_nonneg _), Real.inv_rpow hs.le,
        le_inv_mul_iff₀ (Real.rpow_pos_of_pos hs p)]
      linarith
  have hdef : ∀ ξ η : Euc d, 0 < ‖ξ‖ + ‖η‖ → midDefect p F ξ η =
      (‖ξ‖ + ‖η‖) ^ p * midDefect p F ((‖ξ‖ + ‖η‖)⁻¹ • ξ) ((‖ξ‖ + ‖η‖)⁻¹ • η) := by
    intro ξ η hs
    rw [hF.midDefect_smul (inv_nonneg.2 hs.le), ← mul_assoc,
      ← Real.mul_rpow hs.le (inv_nonneg.2 hs.le), mul_inv_cancel₀ hs.ne', Real.one_rpow, one_mul]
  have htri : ∀ ξ η : Euc d, ‖ξ - η‖ ^ p ≤ (‖ξ‖ + ‖η‖) ^ p := fun ξ η =>
    Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le _ _) hp0.le
  have hzero : ∀ C : ℝ, 0 ≤ C → ∀ ξ η : Euc d, ¬ 0 < ‖ξ‖ + ‖η‖ →
      ‖ξ - η‖ ^ p ≤ C * midDefect p F ξ η + ε * (‖ξ‖ + ‖η‖) ^ p := by
    intro C hC ξ η hs
    have h0 : ‖ξ‖ + ‖η‖ = 0 :=
      le_antisymm (not_lt.1 hs) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    have h1 : ‖ξ - η‖ ^ p ≤ 0 := (htri ξ η).trans (by rw [h0, Real.zero_rpow hp0.ne'])
    have h2 := mul_nonneg hC (hF.midDefect_nonneg hp.le ξ η)
    have h3 : 0 ≤ ε * (‖ξ‖ + ‖η‖) ^ p := mul_nonneg hε.le (Real.rpow_nonneg (by rw [h0]) p)
    linarith
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · refine ⟨0, le_rfl, fun ξ η => ?_⟩
    by_cases hs : 0 < ‖ξ‖ + ‖η‖
    swap
    · exact hzero 0 le_rfl ξ η hs
    by_contra hlt
    have hmem := hmemS ξ η hs (by
      rw [zero_mul, zero_add] at hlt
      exact (not_le.1 hlt).le)
    rw [hS0] at hmem
    exact hmem
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      hSc.exists_isMinOn hSne (hF.continuous_midDefect hp0.le).continuousOn
    have hc : 0 < midDefect p F z₀.1 z₀.2 := hpos z₀ hz₀
    refine ⟨(midDefect p F z₀.1 z₀.2)⁻¹, inv_nonneg.2 hc.le, fun ξ η => ?_⟩
    by_cases hs : 0 < ‖ξ‖ + ‖η‖
    swap
    · exact hzero _ (inv_nonneg.2 hc.le) ξ η hs
    by_cases h : ε * (‖ξ‖ + ‖η‖) ^ p ≤ ‖ξ - η‖ ^ p
    · have hmin' := isMinOn_iff.1 hmin _ (hmemS ξ η hs h)
      have h1 : (‖ξ‖ + ‖η‖) ^ p * midDefect p F z₀.1 z₀.2 ≤ midDefect p F ξ η := by
        rw [hdef ξ η hs]
        exact mul_le_mul_of_nonneg_left hmin' (Real.rpow_nonneg hs.le p)
      have h2 : ‖ξ - η‖ ^ p ≤ (midDefect p F z₀.1 z₀.2)⁻¹ * midDefect p F ξ η := by
        rw [le_inv_mul_iff₀ hc]
        calc midDefect p F z₀.1 z₀.2 * ‖ξ - η‖ ^ p
            ≤ midDefect p F z₀.1 z₀.2 * (‖ξ‖ + ‖η‖) ^ p :=
              mul_le_mul_of_nonneg_left (htri ξ η) hc.le
          _ = (‖ξ‖ + ‖η‖) ^ p * midDefect p F z₀.1 z₀.2 := mul_comm _ _
          _ ≤ midDefect p F ξ η := h1
      linarith [mul_nonneg hε.le (Real.rpow_nonneg hs.le p)]
    · have h' := (not_le.1 h).le
      linarith [mul_nonneg (inv_nonneg.2 hc.le) (hF.midDefect_nonneg hp.le ξ η)]

/-! ### Differentiability of `F^p` and the flux -/

/-- `‖a(ξ)‖ ≤ C ‖ξ‖^{p-1}` for the flux `a = flux p F`. -/
theorem exists_norm_flux_le (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ‖flux p F ξ‖ ≤ C * ‖ξ‖ ^ (p - 1) := by
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  obtain ⟨L, hL0, hL⟩ := hF.exists_norm_gradient_le
  have hp1 : 0 ≤ p - 1 := (sub_pos.2 hp).le
  refine ⟨max M 0 ^ (p - 1) * L, mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) hL0,
    fun ξ => ?_⟩
  rw [flux, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (hF.nonneg ξ) _)]
  have hFξ : F ξ ≤ max M 0 * ‖ξ‖ :=
    (hM ξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  calc F ξ ^ (p - 1) * ‖gradient F ξ‖ ≤ (max M 0 * ‖ξ‖) ^ (p - 1) * L :=
        mul_le_mul (Real.rpow_le_rpow (hF.nonneg ξ) hFξ hp1) (hL ξ) (norm_nonneg _)
          (Real.rpow_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)) _)
    _ = max M 0 ^ (p - 1) * L * ‖ξ‖ ^ (p - 1) := by
        rw [Real.mul_rpow (le_max_right _ _) (norm_nonneg _)]
        ring

/-- **`F^p` is differentiable** (`p > 1`), with `D(F^p)(ξ) = p ⟪a(ξ), ·⟫` for `a = flux p F`
(paper Appendix A: "Also `F^p ∈ C¹(ℝ^d)`, since its gradient is `O(|ξ|^{p-1})` at zero"). -/
theorem hasFDerivAt_rpow (hp : 1 < p) (ξ : Euc d) :
    HasFDerivAt (fun ξ => F ξ ^ p) (p • innerSL ℝ (flux p F ξ)) ξ := by
  have hp0 : 0 < p := by linarith
  rcases eq_or_ne ξ 0 with rfl | hξ
  · obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
    have ht : Tendsto (fun h : Euc d => max M 0 ^ p * ‖h‖ ^ (p - 1)) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto (fun h : Euc d => ‖h‖ ^ (p - 1)) (𝓝 0) (𝓝 0) := by
        have := (continuous_norm.rpow_const fun _ => Or.inr (sub_pos.2 hp).le).tendsto
          (0 : Euc d)
        simpa [Real.zero_rpow (sub_pos.2 hp).ne'] using this
      simpa using h1.const_mul (max M 0 ^ p)
    filter_upwards [ht.eventually (gt_mem_nhds hc)] with h hh
    have hL : (p • innerSL ℝ (flux p F (0 : Euc d))) h = 0 := by
      show p • inner ℝ (flux p F 0) h = 0
      rw [flux_zero hp hF, inner_zero_left, smul_zero]
    have hFh : F h ≤ max M 0 * ‖h‖ :=
      (hM h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have key : F h ^ p ≤ c * ‖h‖ :=
      calc F h ^ p ≤ (max M 0 * ‖h‖) ^ p := Real.rpow_le_rpow (hF.nonneg h) hFh hp0.le
        _ = max M 0 ^ p * ‖h‖ ^ (p - 1) * ‖h‖ := by
            rw [Real.mul_rpow (le_max_right _ _) (norm_nonneg _), mul_assoc,
              ← Real.rpow_add_one' (norm_nonneg _) (ne_of_gt (by linarith)), sub_add_cancel]
        _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hh.le (norm_nonneg _)
    show ‖F (0 + h) ^ p - F 0 ^ p - (p • innerSL ℝ (flux p F (0 : Euc d))) h‖ ≤ c * ‖h‖
    rw [hL, zero_add, hF.map_zero, Real.zero_rpow hp0.ne', sub_zero, sub_zero,
      Real.norm_of_nonneg (Real.rpow_nonneg (hF.nonneg h) p)]
    exact key
  · have hd : HasFDerivAt F (fderiv ℝ F ξ) ξ :=
      ((hF.contDiffAt hξ).differentiableAt (by simp)).hasFDerivAt
    refine (hd.rpow_const (p := p) (Or.inl (hF.pos ξ hξ).ne')).congr_fderiv ?_
    ext ζ
    show p * F ξ ^ (p - 1) * fderiv ℝ F ξ ζ = p * inner ℝ (F ξ ^ (p - 1) • gradient F ξ) ζ
    rw [real_inner_smul_left, inner_gradient_left]
    ring

/-- The derivative of `t ↦ F(ξ + t ζ)^p` is `p ⟪a(ξ + t ζ), ζ⟫`. -/
theorem hasDerivAt_rpow_line (hp : 1 < p) (ξ ζ : Euc d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F (ξ + t • ζ) ^ p) (p * ⟪flux p F (ξ + t • ζ), ζ⟫) t := by
  have hl : HasDerivAt (fun t : ℝ => ξ + t • ζ) ζ t := by
    simpa using ((hasDerivAt_id t).smul_const ζ).const_add ξ
  exact (hF.hasFDerivAt_rpow hp (ξ + t • ζ)).comp_hasDerivAt t hl

/-- The flux `a = flux p F` is continuous (`p > 1`). (The same statement is
`IsSmoothStrictNorm.continuous_flux` in `WangXia/EigenvalueConvexAssemblyAux`; renamed to avoid a
clash.) -/
theorem continuous_flux' (hp : 1 < p) : Continuous (flux p F) := by
  obtain ⟨C, -, hC⟩ := hF.exists_norm_flux_le hp
  rw [continuous_iff_continuousAt]
  intro ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [ContinuousAt, flux_zero hp hF, tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    have h1 : Tendsto (fun ζ : Euc d => C * ‖ζ‖ ^ (p - 1)) (𝓝 0) (𝓝 0) := by
      have := ((continuous_norm.rpow_const fun _ => Or.inr (sub_pos.2 hp).le).tendsto
        (0 : Euc d)).const_mul C
      simpa [Real.zero_rpow (sub_pos.2 hp).ne'] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun ζ => norm_nonneg _) hC
  · have hF1 : ContDiffAt ℝ 1 F ξ := (hF.contDiffAt hξ).of_le (by exact_mod_cast le_top)
    have hfd : ContinuousAt (fderiv ℝ F) ξ :=
      (hF1.fderiv_right (m := 0) (by norm_num)).continuousAt
    have hgrad : ContinuousAt (gradient F) ξ :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.continuousAt.comp hfd
    exact ((hF.continuous_rpow (sub_pos.2 hp).le).continuousAt).smul hgrad

end IsSmoothStrictNorm

end Komlos.Literature
