import Komlos.Literature.PLaplacian.SchauderAux
import Komlos.Literature.PLaplacian.CampanatoIteration

/-!
# Quantitative gradient bootstrap from data-dependent excess decay

The constants in the estimates below are uniform in the gradient bound and the
working radius. This is the dependence needed by the interpolation/absorption
argument in `InteriorGradientBound`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-- The quadratic Campanato estimate with amplitude `N²` gives a linear-amplitude
`L¹` estimate. Choosing `N ρ^α` in Young's inequality preserves that dependence. -/
theorem setIntegral_norm_sub_setAverage_le_of_sq_scaled
    {V : Euc d → Euc d} {x : Euc d} {ρ D N α : ℝ}
    (hρ : 0 < ρ) (hN : 0 < N) (hV : ContinuousOn V (Metric.closedBall x ρ))
    (hsq : (∫ y in Metric.closedBall x ρ, ‖V y - ⨍ z in Metric.closedBall x ρ, V z‖ ^ 2) ≤
      D * N ^ 2 * ρ ^ ((d : ℝ) + 2 * α)) :
    (∫ y in Metric.closedBall x ρ, ‖V y - ⨍ z in Metric.closedBall x ρ, V z‖) ≤
      (D + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * N *
        ρ ^ ((d : ℝ) + α) := by
  let m := ⨍ z in Metric.closedBall x ρ, V z
  have hgi : IntegrableOn (fun y => ‖V y - m‖) (Metric.closedBall x ρ) :=
    (hV.sub continuousOn_const).norm.integrableOn_compact (isCompact_closedBall x ρ)
  have hg2 : IntegrableOn (fun y => ‖V y - m‖ ^ 2) (Metric.closedBall x ρ) :=
    ((hV.sub continuousOn_const).norm.pow 2).integrableOn_compact (isCompact_closedBall x ρ)
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have hp1 : (ρ ^ α) ^ 2 * ρ ^ d = ρ ^ ((d : ℝ) + 2 * α) := by
    rw [pow_two, ← Real.rpow_add hρ, ← Real.rpow_natCast ρ d, ← Real.rpow_add hρ]
    congr 1
    ring
  have hp2 : ρ ^ α * ρ ^ ((d : ℝ) + α) = ρ ^ ((d : ℝ) + 2 * α) := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  have hkey := two_mul_setIntegral_le_setIntegral_sq_add hgi hg2
    measure_closedBall_lt_top.ne (t := N * ρ ^ α)
  rw [volume_real_closedBall x hρ.le, mul_pow] at hkey
  have hvol : N ^ 2 * (ρ ^ α) ^ 2 *
      (ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) =
      N ^ 2 * volume.real (Metric.closedBall (0 : Euc d) 1) *
        ρ ^ ((d : ℝ) + 2 * α) := by
    calc _ = N ^ 2 * volume.real (Metric.closedBall (0 : Euc d) 1) *
        ((ρ ^ α) ^ 2 * ρ ^ d) := by ring
      _ = _ := by rw [hp1]
  rw [hvol] at hkey
  have hbig : 2 * (N * ρ ^ α) * (∫ y in Metric.closedBall x ρ, ‖V y - m‖) ≤
      (D + volume.real (Metric.closedBall (0 : Euc d) 1)) * N ^ 2 *
        ρ ^ ((d : ℝ) + 2 * α) := by
    dsimp [m] at hkey ⊢
    nlinarith [hsq]
  have heq : (D + volume.real (Metric.closedBall (0 : Euc d) 1)) * N ^ 2 *
      ρ ^ ((d : ℝ) + 2 * α) = 2 * (N * ρ ^ α) *
      ((D + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * N *
        ρ ^ ((d : ℝ) + α)) := by
    rw [← hp2]
    ring
  rw [heq] at hbig
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * (N * ρ ^ α))).mp hbig

/-- A data-dependent perturbed excess estimate yields a scaled Hölder estimate.
The output constant is independent of both the working scale and the bound `M`. -/
theorem exists_scaled_holder_of_perturbed_decay (d : ℕ) {α a b R : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 < R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : Euc d) (τ M : ℝ) (G : Euc d → Euc d),
      0 < τ → τ ≤ R → 0 ≤ M → ContinuousOn G (Metric.ball x (2 * τ)) →
      (∀ y ∈ Metric.closedBall x (3 * τ / 2), ‖G y‖ ≤ M) →
      (∀ y ∈ Metric.closedBall x τ, ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r →
        r ≤ min (τ / 16) (1 / 2) →
        (∫ z in Metric.closedBall y ρ, ‖G z - ⨍ t in Metric.closedBall y ρ, G t‖ ^ 2) ≤
          a * (ρ / r) ^ ((d : ℝ) + 2) *
            (∫ z in Metric.closedBall y r, ‖G z - ⨍ t in Metric.closedBall y r, G t‖ ^ 2) +
          b * (1 + M ^ 2) * r ^ ((d : ℝ) + 2 * α)) →
      ∀ y ∈ Metric.closedBall x τ, ∀ z ∈ Metric.closedBall x τ,
        τ ^ α * ‖G y - G z‖ ≤ C * (1 + M) * dist y z ^ α := by
  let ωd : ℝ := volume.real (Metric.closedBall (0 : Euc d) 1)
  have hωd : 0 < ωd := volume_real_closedBall_pos
  obtain ⟨c, hc, hcdec⟩ := campanato_iteration_constants ha
    (show 0 ≤ (d : ℝ) + 2 * α by positivity) (show (d : ℝ) + 2 * α < d + 2 by linarith)
  let D : ℝ := c * (ωd + b)
  have hD : 0 ≤ D := mul_nonneg hc (by dsimp [ωd] at hωd ⊢; linarith)
  obtain ⟨B, hB0, hB⟩ := exists_holder_of_campanato_scaled (d := d) (E := Euc d) hα
  let κ : ℝ := 1 / (16 + 2 * R)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ16 : κ ≤ 1 / 16 := by
    dsimp [κ]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have hκR : κ * R ≤ 1 / 2 := by
    dsimp [κ]
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  let Cnear := B * ((D + ωd) / 2) / κ ^ α
  let Cfar := 2 / (κ / 2) ^ α
  refine ⟨max 1 (max Cnear Cfar), le_max_left _ _, ?_⟩
  intro x τ M G hτ hτR hM hGc hGM hdec y hy z hz
  let r₀ := κ * τ
  have hr₀ : 0 < r₀ := mul_pos hκ hτ
  have hrτ : r₀ ≤ τ / 16 := by
    dsimp [r₀]
    calc κ * τ ≤ (1 / 16) * τ := mul_le_mul_of_nonneg_right hκ16 hτ.le
      _ = τ / 16 := by ring
  have hrhalf : r₀ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hτR hκ.le).trans hκR
  have hrone : r₀ ≤ 1 := by linarith
  have hrsmall : r₀ ≤ min (τ / 16) (1 / 2) := le_min hrτ hrhalf
  let N := (1 + M) / r₀ ^ α
  have hN : 0 < N := div_pos (by linarith) (Real.rpow_pos_of_pos hr₀ _)
  have hsub : ∀ v ∈ Metric.closedBall x τ, ∀ r : ℝ, r ≤ r₀ →
      Metric.closedBall v r ⊆ Metric.closedBall x (3 * τ / 2) := by
    intro v hv r hr t ht
    rw [Metric.mem_closedBall] at hv ht ⊢
    calc dist t x ≤ dist t v + dist v x := dist_triangle _ _ _
      _ ≤ r + τ := add_le_add ht hv
      _ ≤ 3 * τ / 2 := by linarith
  have hbigsub : Metric.closedBall x (3 * τ / 2) ⊆ Metric.ball x (2 * τ) :=
    Metric.closedBall_subset_ball (by linarith)
  have hcont : ∀ v ∈ Metric.closedBall x τ, ∀ r : ℝ, r ≤ r₀ →
      ContinuousOn G (Metric.closedBall v r) :=
    fun v hv r hr => hGc.mono ((hsub v hv r hr).trans hbigsub)
  have hbasepow : r₀ ^ ((d : ℝ) + 2 * α) = r₀ ^ d * (r₀ ^ α) ^ 2 := by
    rw [pow_two, ← Real.rpow_add hr₀, ← Real.rpow_natCast r₀ d, ← Real.rpow_add hr₀]
    congr 1
    ring
  have hNpow : N ^ 2 * r₀ ^ ((d : ℝ) + 2 * α) = (1 + M) ^ 2 * r₀ ^ d := by
    rw [hbasepow]
    dsimp [N]
    field_simp
  have hpowerle : r₀ ^ ((d : ℝ) + 2 * α) ≤ r₀ ^ d := by
    have h1 : r₀ ^ (2 * α) ≤ 1 :=
      Real.rpow_le_one hr₀.le hrone (by positivity)
    rw [Real.rpow_add hr₀, Real.rpow_natCast]
    simpa using mul_le_mul_of_nonneg_left h1 (pow_nonneg hr₀.le d)
  have hcamp2 : ∀ v ∈ Metric.closedBall x τ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ →
      (∫ t in Metric.closedBall v ρ, ‖G t - ⨍ q in Metric.closedBall v ρ, G q‖ ^ 2) ≤
        D * N ^ 2 * ρ ^ ((d : ℝ) + 2 * α) := by
    intro v hv ρ hρ hρr
    let Φ : ℝ → ℝ := fun r =>
      ∫ t in Metric.closedBall v r, ‖G t - ⨍ q in Metric.closedBall v r, G q‖ ^ 2
    have hΦ0 : ∀ r, 0 ≤ Φ r := fun r => integral_nonneg fun _ => sq_nonneg _
    have hstep := hcdec (b * (1 + M ^ 2)) r₀ (by positivity) hr₀ Φ hΦ0
      (fun s t hs hst ht => integral_norm_sub_setAverage_sq_mono hs hst (hcont v hv t ht))
      (fun s t hs hst ht => hdec v hv s t hs hst (ht.trans hrsmall)) ρ hρ hρr
    have hbase : Φ r₀ ≤ M ^ 2 * (r₀ ^ d * ωd) := by
      apply (integral_norm_sub_setAverage_sq_le_const hr₀ (hcont v hv r₀ le_rfl) 0).trans
      have h := setIntegral_norm_sub_sq_le (hcont v hv r₀ le_rfl)
        (c := (0 : Euc d)) (K := M) (fun t ht => by
          simpa using hGM t (hsub v hv r₀ le_rfl ht))
      simpa [volume_real_closedBall v hr₀.le, ωd] using h
    have hMpow : M ^ 2 ≤ (1 + M) ^ 2 := by nlinarith
    have hMp : 1 + M ^ 2 ≤ (1 + M) ^ 2 := by nlinarith
    have hdata : Φ r₀ + b * (1 + M ^ 2) * r₀ ^ ((d : ℝ) + 2 * α) ≤
        (ωd + b) * (1 + M) ^ 2 * r₀ ^ d := by
      calc _ ≤ (1 + M) ^ 2 * (r₀ ^ d * ωd) +
          b * (1 + M) ^ 2 * r₀ ^ d := by
            apply add_le_add
            · exact hbase.trans (mul_le_mul_of_nonneg_right hMpow (by positivity))
            · exact mul_le_mul (mul_le_mul_of_nonneg_left hMp hb) hpowerle
                (Real.rpow_nonneg hr₀.le _) (by positivity)
        _ = _ := by ring
    have hden : r₀ ^ ((d : ℝ) + 2 * α) ≠ 0 := (Real.rpow_pos_of_pos hr₀ _).ne'
    calc Φ ρ ≤ c * (Φ r₀ + b * (1 + M ^ 2) * r₀ ^ ((d : ℝ) + 2 * α)) *
          (ρ / r₀) ^ ((d : ℝ) + 2 * α) := hstep
      _ ≤ c * ((ωd + b) * (1 + M) ^ 2 * r₀ ^ d) *
          (ρ / r₀) ^ ((d : ℝ) + 2 * α) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdata hc)
          (Real.rpow_nonneg (div_nonneg hρ.le hr₀.le) _)
      _ = D * N ^ 2 * ρ ^ ((d : ℝ) + 2 * α) := by
        rw [show (ωd + b) * (1 + M) ^ 2 * r₀ ^ d =
          (ωd + b) * (N ^ 2 * r₀ ^ ((d : ℝ) + 2 * α)) by rw [hNpow]; ring,
          Real.div_rpow hρ.le hr₀.le]
        dsimp [D]
        field_simp
  have hcamp1 : ∀ v ∈ Metric.closedBall x τ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ →
      (∫ t in Metric.closedBall v ρ, ‖G t - ⨍ q in Metric.closedBall v ρ, G q‖) ≤
        ((D + ωd) / 2 * N) * ρ ^ ((d : ℝ) + α) := by
    intro v hv ρ hρ hρr
    exact setIntegral_norm_sub_setAverage_le_of_sq_scaled hρ hN
      (hcont v hv ρ hρr) (hcamp2 v hv ρ hρ hρr)
  have hlim : ∀ v ∈ Metric.closedBall x τ, ∀ ε : ℝ, 0 < ε → ∀ u : ℝ, 0 < u →
      ∃ s : ℝ, 0 < s ∧ s ≤ u ∧ ‖(⨍ t in Metric.closedBall v s, G t) - G v‖ ≤ ε := by
    intro v hv ε hε u hu
    have hvball : v ∈ Metric.ball x (2 * τ) :=
      Metric.closedBall_subset_ball (by linarith) hv
    have hcv : ContinuousAt G v := hGc.continuousAt (Metric.isOpen_ball.mem_nhds hvball)
    obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.mp hcv ε hε
    let s := min u (min r₀ (δ / 2))
    have hs : 0 < s := lt_min hu (lt_min hr₀ (by linarith))
    have hsu : s ≤ u := min_le_left _ _
    have hsr : s ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hsδ : s ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨s, hs, hsu, norm_setAverage_sub_le_of_forall hs
      ((hcont v hv s hsr).integrableOn_compact (isCompact_closedBall v s)) ?_⟩
    intro t ht
    have hdist : dist t v < δ := by
      have := Metric.mem_closedBall.mp ht
      linarith
    simpa only [dist_eq_norm] using (hδG hdist).le
  have hnorm : τ ^ α * N = (1 + M) / κ ^ α := by
    dsimp [N, r₀]
    rw [Real.mul_rpow hκ.le hτ.le]
    field_simp
  have hyM : ‖G y‖ ≤ M := hGM y (Metric.closedBall_subset_closedBall (by linarith) hy)
  have hzM : ‖G z‖ ≤ M := hGM z (Metric.closedBall_subset_closedBall (by linarith) hz)
  by_cases heq : y = z
  · subst z
    simp [Real.zero_rpow hα.ne']
  have hd : 0 < dist y z := dist_pos.mpr heq
  by_cases hnear : 2 * dist y z ≤ r₀
  · have hh := hB ((D + ωd) / 2 * N) (by positivity) r₀ G (Metric.closedBall x τ)
      (fun v hv r _ hr => (hcont v hv r hr).integrableOn_compact (isCompact_closedBall v r))
      (fun v hv r hr hrr => ⟨⨍ q in Metric.closedBall v r, G q, hcamp1 v hv r hr hrr⟩)
      hlim y hy z hz (dist y z) hd le_rfl hnear
    calc τ ^ α * ‖G y - G z‖ ≤ τ ^ α * (B * ((D + ωd) / 2 * N) * dist y z ^ α) :=
          mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hτ.le _)
      _ = Cnear * (1 + M) * dist y z ^ α := by
        dsimp [Cnear]
        calc _ = B * ((D + ωd) / 2) * (τ ^ α * N) * dist y z ^ α := by ring
          _ = _ := by rw [hnorm]; ring
      _ ≤ max 1 (max Cnear Cfar) * (1 + M) * dist y z ^ α := by
        gcongr
        exact (le_max_left _ _).trans (le_max_right _ _)
  · have hfar : r₀ / 2 ≤ dist y z := by linarith
    have hp : (r₀ / 2) ^ α ≤ dist y z ^ α :=
      Real.rpow_le_rpow (by positivity) hfar hα.le
    have hCfar : 0 ≤ Cfar := by dsimp [Cfar]; positivity
    have hrad : (r₀ / 2) ^ α = (κ / 2) ^ α * τ ^ α := by
      rw [show r₀ / 2 = (κ / 2) * τ by dsimp [r₀]; ring,
        Real.mul_rpow (by positivity) hτ.le]
    have hfar_eq : Cfar * (1 + M) * (r₀ / 2) ^ α = 2 * (1 + M) * τ ^ α := by
      rw [hrad]
      dsimp [Cfar]
      field_simp
    calc τ ^ α * ‖G y - G z‖ ≤ τ ^ α * (‖G y‖ + ‖G z‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.rpow_nonneg hτ.le _)
      _ ≤ 2 * (1 + M) * τ ^ α := by nlinarith [Real.rpow_pos_of_pos hτ α]
      _ = Cfar * (1 + M) * (r₀ / 2) ^ α := hfar_eq.symm
      _ ≤ Cfar * (1 + M) * dist y z ^ α :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hCfar (by linarith))
      _ ≤ max 1 (max Cnear Cfar) * (1 + M) * dist y z ^ α := by
        gcongr
        exact (le_max_right _ _).trans (le_max_right _ _)

end Komlos.Literature
