import Komlos.Literature.PLaplacian.SchauderConst
import Komlos.Literature.PLaplacian.FrozenRegularity

/-!
# Freezing with a supplied gradient bound

The comparison constant is proportional to `1 + M²`, where `M` bounds the gradient of
this particular solution.  This estimate precedes the interpolation bootstrap and does
not depend on the uniform interior gradient bound.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-- Data-dependent frozen comparison, with its constant independent of the domain radius
(Gilbarg–Trudinger, Theorem 8.32, step 2). -/
theorem exists_frozen_comparison_of_gradient_bound (d : ℕ) (hd : 0 < d)
    {α μ Λ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R M : ℝ}, 0 < R → 0 ≤ M →
      ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) →
      (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖gradient w x‖ ≤ M) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.ball x₀ R, ∀ r : ℝ, 0 < r → r ≤ min (R / 4) (1 / 2) →
        ∃ h : Euc d → ℝ, ContDiffOn ℝ 1 h (Metric.ball x (2 * r)) ∧
          IsWeakConstSolutionOn (A x) (Metric.ball x (2 * r)) h ∧
          (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) ≤
            C * (1 + M ^ 2) * r ^ ((d : ℝ) + 2 * α) := by
  let L := max Λ 0
  let V := volume.real (Metric.closedBall (0 : Euc d) 1)
  let K := V * (20 * L ^ 2 + 2 * L) / μ ^ 2
  have hL : 0 ≤ L := le_max_right _ _
  have hV : 0 ≤ V := volume_real_closedBall_pos.le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K * (2 : ℝ) ^ ((d : ℝ) + 2 * α),
    mul_nonneg hK (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro R M hR hM x₀ A g w hell hbdd hhol hgc hgbd hw hMbd hweak x hx r hr hrR
  have hrR4 : r ≤ R / 4 := hrR.trans (min_le_left _ _)
  have hr12 : r ≤ 1 / 2 := hrR.trans (min_le_right _ _)
  have hsub4 : Metric.closedBall x (2 * (2 * r)) ⊆ Metric.ball x₀ (2 * R) := by
    intro y hy
    have h1 := Metric.mem_closedBall.mp hy
    have h2 := Metric.mem_ball.mp hx
    have h3 := dist_triangle y x x₀
    exact Metric.mem_ball.mpr (by linarith)
  have hsub2 : Metric.closedBall x (2 * r) ⊆ Metric.ball x₀ (2 * R) :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hsub4
  have hxball : x ∈ Metric.ball x₀ (2 * R) := Metric.ball_subset_ball (by linarith) hx
  obtain ⟨h, ψ, hh, hH, hψ, hψgrad, hsol, htest⟩ :=
    exists_frozen_smooth_replacement_on_ball hd hμ (hell x hxball) (hbdd x hxball)
      (by linarith : 0 < 2 * r) Metric.isOpen_ball hw hsub4
  have hAc : ContinuousOn A (Metric.ball x₀ (2 * R)) := continuousOn_of_holder hα hhol
  have hWc : ContinuousOn (gradient w) (Metric.ball x₀ (2 * R)) :=
    continuousOn_gradient Metric.isOpen_ball hw
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ (2 * R))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hΦ : MemLp ((Metric.ball x₀ (2 * R)).indicator
      (fun y => A y (gradient w y))) 2 := by
    rw [memLp_indicator_iff_restrict measurableSet_ball]
    refine MemLp.of_bound ((hAc.clm_apply hWc).aestronglyMeasurable measurableSet_ball)
      (L * M) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact ((A y).le_opNorm _).trans
      (mul_le_mul ((hbdd y hy).trans (le_max_left _ _)) (hMbd y hy) (norm_nonneg _) hL)
  have hg : MemLp ((Metric.ball x₀ (2 * R)).indicator g) 2 := by
    rw [memLp_indicator_iff_restrict measurableSet_ball]
    refine MemLp.of_bound (hgc.aestronglyMeasurable measurableSet_ball) L ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    simpa only [Real.norm_eq_abs] using (hgbd y hy).trans (le_max_left _ _)
  have heqw := integral_inner_weakGrad_eq_of_memW0_two Metric.isOpen_ball hΦ hg hweak
    (isCompact_closedBall x (2 * r)) hsub2 hψ
    (hψ.weakGrad_eq_zero_of_isClosed Metric.isClosed_closedBall)
  have hosc : ∀ y ∈ Metric.closedBall x (2 * r), ‖A x - A y‖ ≤ L * (2 * r) ^ α := by
    intro y hy
    refine (hhol x hxball y (hsub2 hy)).trans ?_
    apply mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow dist_nonneg (by simpa [dist_comm] using Metric.mem_closedBall.mp hy)
        hα.le) (Real.rpow_nonneg dist_nonneg _) hL
  have hest := frozen_energy_estimate_of_memLp hd hα hα1.le hμ hL hM
    (by linarith : 0 < 2 * r) (by linarith : 2 * r ≤ 1) (hell x hxball) hosc
    (fun y hy => (hgbd y (hsub2 hy)).trans (le_max_left _ _))
    (fun y hy => hMbd y (hsub2 hy)) (hAc.mono hsub2) (hgc.mono hsub2) (hWc.mono hsub2)
    hH hψ hψgrad heqw htest
  have hpoly : 2 * L ^ 2 * M ^ 2 + 18 * L ^ 2 + L * M + L ≤
      (20 * L ^ 2 + 2 * L) * (1 + M ^ 2) := by
    have hlin : M ≤ 1 + M ^ 2 := by nlinarith [sq_nonneg (M - 1 / 2)]
    have hlinL := mul_le_mul_of_nonneg_left hlin hL
    nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg M),
      mul_nonneg hL (sq_nonneg M)]
  have hcoeff : V * (2 * L ^ 2 * M ^ 2 + 18 * L ^ 2 + L * M + L) / μ ^ 2 ≤
      K * (1 + M ^ 2) := by
    dsimp [K]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left hpoly hV]) (sq_nonneg μ)
  have hpow : (2 * r) ^ ((d : ℝ) + 2 * α) =
      (2 : ℝ) ^ ((d : ℝ) + 2 * α) * r ^ ((d : ℝ) + 2 * α) :=
    Real.mul_rpow (by norm_num) hr.le
  refine ⟨h, hh.of_le (by simp), hsol, ?_⟩
  have hmono : (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) ≤
      ∫ y in Metric.closedBall x (2 * r), ‖gradient w y - gradient h y‖ ^ 2 := by
    have hW : MemLp (gradient w) 2 (volume.restrict (Metric.closedBall x (2 * r))) :=
      (memLp_two_iff_integrable_sq_norm
        ((hWc.mono hsub2).aestronglyMeasurable measurableSet_closedBall)).2
        ((((hWc.mono hsub2).norm).pow 2).integrableOn_compact
          (isCompact_closedBall x (2 * r)))
    exact setIntegral_mono_set ((hW.sub hH).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Metric.closedBall_subset_closedBall (by linarith : r ≤ 2 * r)).eventuallyLE
  refine (hmono.trans hest).trans ?_
  refine (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by linarith) _)).trans_eq ?_
  rw [hpow]
  ring

/-- Perturbed excess decay with a supplied gradient bound, before interpolation has
made that bound uniform (Gilbarg–Trudinger, Theorem 8.32, steps 1–2). -/
theorem exists_perturbed_sqExcess_decay_of_gradient_bound (d : ℕ) (hd : 0 < d)
    {α μ Λ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hμ : 0 < μ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {R M : ℝ}, 0 < R → 0 ≤ M →
      ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖gradient w x‖ ≤ M) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.ball x₀ R, ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ min (R / 4) (1 / 2) →
        (∫ y in Metric.closedBall x ρ,
            ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
          C₁ * (ρ / r) ^ ((d : ℝ) + 2) *
            (∫ y in Metric.closedBall x r,
              ‖gradient w y - (⨍ z in Metric.closedBall x r, gradient w z)‖ ^ 2) +
          C₂ * (1 + M ^ 2) * r ^ ((d : ℝ) + 2 * α) := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_constCoeff_sqExcess_decay d (μ := μ) (Λ := Λ) hμ
  obtain ⟨CB, hCB0, hCB⟩ :=
    exists_frozen_comparison_of_gradient_bound d hd (α := α) (μ := μ) (Λ := Λ) hα hα1 hμ
  refine ⟨4 * CA, (2 + 4 * CA) * CB, by linarith, mul_nonneg (by linarith) hCB0, ?_⟩
  intro R M hR hM x₀ A g w hell hbdd hhol hgc hgbd hw hMbd hweak x hx ρ r hρ hρr hrR₀
  have hr : 0 < r := lt_of_lt_of_le hρ hρr
  have hrR2 : r ≤ R / 2 := by
    have h := hrR₀.trans (min_le_left _ _)
    linarith
  obtain ⟨h, hh1, hhsol, hcomp⟩ :=
    hCB hR hM x₀ A g w hell hbdd hhol hgc hgbd hw hMbd hweak x hx r hr hrR₀
  -- the two balls we work on
  have hsubW : Metric.closedBall x r ⊆ Metric.ball x₀ (2 * R) := by
    intro y hy
    have h1 : dist y x ≤ r := Metric.mem_closedBall.1 hy
    have h2 : dist x x₀ < R := Metric.mem_ball.1 hx
    have h3 : dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle y x x₀
    exact Metric.mem_ball.2 (by linarith)
  have hsubH : Metric.closedBall x r ⊆ Metric.ball x (2 * r) := fun y hy =>
    Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (by linarith))
  have hGwc : ContinuousOn (gradient w) (Metric.closedBall x r) :=
    (continuousOn_gradient Metric.isOpen_ball hw).mono hsubW
  have hGhc : ContinuousOn (gradient h) (Metric.closedBall x r) :=
    (continuousOn_gradient Metric.isOpen_ball hh1).mono hsubH
  have hsubρ : Metric.closedBall x ρ ⊆ Metric.closedBall x r :=
    Metric.closedBall_subset_closedBall hρr
  have hE0 : (0 : ℝ) ≤ ∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hq0 : (0 : ℝ) ≤ (ρ / r) ^ ((d : ℝ) + 2) :=
    Real.rpow_nonneg (div_nonneg hρ.le hr.le) _
  have hq1 : (ρ / r) ^ ((d : ℝ) + 2) ≤ 1 :=
    Real.rpow_le_one (div_nonneg hρ.le hr.le) ((div_le_one hr).2 hρr) (by positivity)
  have hSw0 : (0 : ℝ) ≤ sqExcess (gradient w) x r := sqExcess_nonneg _ _ _
  -- Step 1: the excess of `∇w` is controlled by the comparison error and the excess of `∇h`.
  have hstep1 : sqExcess (gradient w) x ρ ≤
      2 * (∫ y in Metric.closedBall x ρ, ‖gradient w y - gradient h y‖ ^ 2) +
        2 * sqExcess (gradient h) x ρ :=
    (sqExcess_le_const hρ (hGwc.mono hsubρ) (⨍ z in Metric.closedBall x ρ, gradient h z)).trans
      (setIntegral_norm_sub_sq_le_two_add (hGwc.mono hsubρ) (hGhc.mono hsubρ)
        (⨍ z in Metric.closedBall x ρ, gradient h z))
  have hEρ : (∫ y in Metric.closedBall x ρ, ‖gradient w y - gradient h y‖ ^ 2) ≤
      ∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2 :=
    setIntegral_norm_sub_sq_mono hρr hGwc hGhc
  -- Step 2: the constant-coefficient decay for the frozen solution `h`.
  have hstep2 : sqExcess (gradient h) x ρ ≤
      CA * ((ρ / r) ^ ((d : ℝ) + 2) * sqExcess (gradient h) x r) :=
    hCA (A x) h x r hr (hell x (Metric.ball_subset_ball (by linarith) hx))
      (hbdd x (Metric.ball_subset_ball (by linarith) hx)) hh1 hhsol ρ hρ hρr
  -- Step 3: the excess of `∇h` at scale `r` is controlled by that of `∇w`.
  have hswap : (∫ y in Metric.closedBall x r, ‖gradient h y - gradient w y‖ ^ 2) =
      ∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun y => by dsimp only; rw [norm_sub_rev])
  have hstep3 : sqExcess (gradient h) x r ≤
      2 * (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) +
        2 * sqExcess (gradient w) x r := by
    have h1 := setIntegral_norm_sub_sq_le_two_add (G := gradient h) (H := gradient w) (x := x)
      (r := r) hGhc hGwc (⨍ z in Metric.closedBall x r, gradient w z)
    rw [hswap] at h1
    exact (sqExcess_le_const hr hGhc (⨍ z in Metric.closedBall x r, gradient w z)).trans h1
  -- Combine.
  have hmul : CA * ((ρ / r) ^ ((d : ℝ) + 2) * sqExcess (gradient h) x r) ≤
      CA * ((ρ / r) ^ ((d : ℝ) + 2) *
        (2 * (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) +
          2 * sqExcess (gradient w) x r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 hq0) hCA0
  have hqE : 4 * CA * (ρ / r) ^ ((d : ℝ) + 2) *
      (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) ≤
      4 * CA * ∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2 := by
    linarith [mul_nonneg (mul_nonneg hCA0 hE0) (sub_nonneg.2 hq1)]
  have hEb : (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) ≤
      CB * (1 + M ^ 2) * r ^ ((d : ℝ) + 2 * α) := hcomp
  have hfin : (2 + 4 * CA) *
      (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) ≤
      (2 + 4 * CA) * (CB * (1 + M ^ 2) * r ^ ((d : ℝ) + 2 * α)) :=
    mul_le_mul_of_nonneg_left hEb (by linarith)
  have hkey : sqExcess (gradient w) x ρ ≤
      4 * CA * (ρ / r) ^ ((d : ℝ) + 2) * sqExcess (gradient w) x r +
        (2 + 4 * CA) * CB * (1 + M ^ 2) * r ^ ((d : ℝ) + 2 * α) := by
    linarith [hstep1, hEρ, hstep2, hmul, hqE, hfin]
  exact hkey

end Komlos.Literature
