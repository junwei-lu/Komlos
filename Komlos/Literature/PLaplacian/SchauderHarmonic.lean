import Komlos.Literature.PLaplacian.SchauderConst
import Komlos.Literature.PLaplacian.SchauderFreezing
import Komlos.Literature.PLaplacian.InteriorGradientBound

/-!
# Uniform freezing and perturbed gradient-energy decay

The constant-coefficient theory is in `SchauderConst`.  The uniform comparison and its
Campanato consequence are assembled here, keeping the constant-coefficient input available
to the independent interpolation bootstrap.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-- Uniform frozen Dirichlet data (Gilbarg–Trudinger, Theorem 8.32, step 2).
The independent interpolation bootstrap supplies the uniform gradient bound.  The
variational replacement and Weyl's lemma supply the smooth interior representative;
its gradient is only required to be `L²` on the closed comparison ball, which is the
regularity used by the energy comparison. -/
theorem exists_frozen_replacement_data (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hμ : 0 < μ) (hR : 0 < R) :
    ∃ M R₀ : ℝ, 0 < R₀ ∧ 0 ≤ M ∧
      ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.ball x₀ R, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        (∀ y ∈ Metric.closedBall x (2 * r), ‖gradient w y‖ ≤ M) ∧
        ∃ h : Euc d → ℝ, ContDiffOn ℝ 1 h (Metric.ball x (2 * r)) ∧
          MemLp (gradient h) 2 (volume.restrict (Metric.closedBall x (2 * r))) ∧
          IsWeakConstSolutionOn (A x) (Metric.ball x (2 * r)) h ∧
          ∃ ψ : Euc d → ℝ, MemW0 2 (Metric.closedBall x (2 * r)) ψ ∧
            weakGrad ψ =ᵐ[volume] (Metric.closedBall x (2 * r)).indicator
              (fun y => gradient w y - gradient h y) ∧
            (∫ y, ⟪A y (gradient w y), weakGrad ψ y⟫) = ∫ y, g y * ψ y ∧
            (∫ y, ⟪A x (gradient h y), weakGrad ψ y⟫) = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, 1, one_pos, le_rfl, ?_⟩
    intro x₀ A g w _ _ _ _ _ _ _ _ _ x _ r _ _
    refine ⟨?_, fun _ => (0 : ℝ), contDiffOn_const, ?_, ?_,
      (0 : Euc 0 → ℝ), MemW0.zero, ?_, ?_, ?_⟩
    · intro y _
      rw [eq_zero_of_dim_zero (gradient w y), norm_zero]
    · have hz : gradient (fun _ : Euc 0 => (0 : ℝ)) = 0 :=
        funext fun y => eq_zero_of_dim_zero _
      rw [hz]
      exact MemLp.zero
    · intro ψ _ _ _
      have hz : (fun y : Euc 0 =>
          ⟪A x (gradient (fun _ : Euc 0 => (0 : ℝ)) y), gradient ψ y⟫) =
          fun _ => (0 : ℝ) := by
        funext y
        rw [eq_zero_of_dim_zero (gradient ψ y), inner_zero_right]
      rw [hz, integral_zero]
    · exact Eventually.of_forall fun y => Subsingleton.elim _ _
    · have hz : (fun y : Euc 0 => ⟪A y (gradient w y), weakGrad (0 : Euc 0 → ℝ) y⟫) =
          fun _ => (0 : ℝ) := by
        funext y
        rw [eq_zero_of_dim_zero (weakGrad (0 : Euc 0 → ℝ) y), inner_zero_right]
      simp [hz]
    · have hz : (fun y : Euc 0 =>
          ⟪A x (gradient (fun _ : Euc 0 => (0 : ℝ)) y), weakGrad (0 : Euc 0 → ℝ) y⟫) =
          fun _ => (0 : ℝ) := by
        funext y
        rw [eq_zero_of_dim_zero (weakGrad (0 : Euc 0 → ℝ) y), inner_zero_right]
      rw [hz, integral_zero]
  obtain ⟨M, hM, hbound⟩ := exists_uniform_interior_gradient_bound d
    (α := α) (μ := μ) (Λ := Λ) (R := R) hα hα1 hμ hR
  refine ⟨M, R / 4, by linarith, hM, ?_⟩
  intro x₀ A g w hell hbdd hhol hgc hgbd hw hwbd hwlip hweak x hx r hr hrR
  have hMb := hbound x₀ A g w hell hbdd hhol hgc hgbd hw hwbd hwlip hweak
  have hsub4 : Metric.closedBall x (2 * (2 * r)) ⊆ Metric.ball x₀ (2 * R) := by
    intro y hy
    have h1 := Metric.mem_closedBall.mp hy
    have h2 := Metric.mem_ball.mp hx
    have h3 := dist_triangle y x x₀
    exact Metric.mem_ball.mpr (by linarith)
  have hsub2 : Metric.closedBall x (2 * r) ⊆ Metric.ball x₀ (3 * R / 2) := by
    intro y hy
    have h1 := Metric.mem_closedBall.mp hy
    have h2 := Metric.mem_ball.mp hx
    have h3 := dist_triangle y x x₀
    exact Metric.mem_ball.mpr (by linarith)
  have hsmall : Metric.ball x₀ (3 * R / 2) ⊆ Metric.ball x₀ (2 * R) :=
    Metric.ball_subset_ball (by linarith)
  have hxball : x ∈ Metric.ball x₀ (2 * R) := Metric.ball_subset_ball (by linarith) hx
  obtain ⟨h, ψ, hh, hH, hψ, hψgrad, hsol, htest⟩ :=
    exists_frozen_smooth_replacement_on_ball hd hμ (hell x hxball) (hbdd x hxball)
      (by linarith : 0 < 2 * r) Metric.isOpen_ball hw hsub4
  have hAc : ContinuousOn A (Metric.ball x₀ (3 * R / 2)) :=
    (continuousOn_of_holder hα hhol).mono hsmall
  have hWc : ContinuousOn (gradient w) (Metric.ball x₀ (3 * R / 2)) :=
    (continuousOn_gradient Metric.isOpen_ball hw).mono hsmall
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ (3 * R / 2))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hΦ : MemLp ((Metric.ball x₀ (3 * R / 2)).indicator
      (fun y => A y (gradient w y))) 2 := by
    rw [memLp_indicator_iff_restrict measurableSet_ball]
    refine MemLp.of_bound ((hAc.clm_apply hWc).aestronglyMeasurable measurableSet_ball)
      (max Λ 0 * M) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact ((A y).le_opNorm _).trans
      (mul_le_mul ((hbdd y (hsmall hy)).trans (le_max_left _ _))
        (hMb y (Metric.ball_subset_closedBall hy)) (norm_nonneg _) (le_max_right _ _))
  have hg : MemLp ((Metric.ball x₀ (3 * R / 2)).indicator g) 2 := by
    rw [memLp_indicator_iff_restrict measurableSet_ball]
    refine MemLp.of_bound ((hgc.mono hsmall).aestronglyMeasurable measurableSet_ball) Λ ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    simpa only [Real.norm_eq_abs] using hgbd y (hsmall hy)
  have heqw := integral_inner_weakGrad_eq_of_memW0_two Metric.isOpen_ball hΦ hg
    (fun χ hχ hχs hχB => hweak χ hχ hχs (hχB.trans hsmall))
    (isCompact_closedBall x (2 * r)) hsub2 hψ
    (hψ.weakGrad_eq_zero_of_isClosed Metric.isClosed_closedBall)
  exact ⟨fun y hy => hMb y (Metric.ball_subset_closedBall (hsub2 hy)),
    h, hh.of_le (by simp), hH, hsol, ψ, hψ, hψgrad, heqw, htest⟩

/-- **Freezing comparison** (Gilbarg–Trudinger, Theorem 8.32, step 2): on a small ball `B(x, r)`
inside the domain, a weak solution of `div (A ∇w) = g` with `α`-Hölder `A` is `L²`-close in
gradient to the solution `h` of the frozen equation `div (A(x) ∇h) = 0` with the same boundary
values, with the quantitative error `∫_{B(x,r)} ‖∇w - ∇h‖² ≤ C r^{d+2α}`, uniformly over the
family described by the standing hypotheses.

The analytic estimate is `frozen_energy_estimate_of_memLp`; the uniform gradient bound
and smooth interior replacement are supplied by `exists_frozen_replacement_data`. -/
theorem exists_frozen_comparison (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hμ : 0 < μ)
    (hR : 0 < R) :
    ∃ C R₀ : ℝ, 0 < R₀ ∧ 0 ≤ C ∧
      ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.ball x₀ R, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ h : Euc d → ℝ, ContDiffOn ℝ 1 h (Metric.ball x (2 * r)) ∧
          IsWeakConstSolutionOn (A x) (Metric.ball x (2 * r)) h ∧
          (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) ≤
            C * r ^ ((d : ℝ) + 2 * α) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `d = 0`: `Euc 0` is trivial, every gradient vanishes and the comparison error is `0`.
    refine ⟨0, 1, one_pos, le_rfl, ?_⟩
    intro x₀ A g w _ _ _ _ _ _ _ _ _ x _ r _ _
    refine ⟨fun _ => (0 : ℝ), contDiffOn_const, ?_, ?_⟩
    · intro ψ _ _ _
      have hz : (fun y : Euc 0 =>
          ⟪A x (gradient (fun _ : Euc 0 => (0 : ℝ)) y), gradient ψ y⟫) =ᵐ[volume]
          fun _ : Euc 0 => (0 : ℝ) := by
        refine Eventually.of_forall fun y => ?_
        show ⟪A x (gradient (fun _ : Euc 0 => (0 : ℝ)) y), gradient ψ y⟫ = (0 : ℝ)
        rw [eq_zero_of_dim_zero (gradient (fun _ : Euc 0 => (0 : ℝ)) y), map_zero,
          inner_zero_left]
      rw [integral_congr_ae hz]
      simp
    · have hz : (fun y : Euc 0 =>
          ‖gradient w y - gradient (fun _ : Euc 0 => (0 : ℝ)) y‖ ^ 2) =ᵐ[volume.restrict
            (Metric.closedBall x r)] fun _ : Euc 0 => (0 : ℝ) := by
        refine Eventually.of_forall fun y => ?_
        show ‖gradient w y - gradient (fun _ : Euc 0 => (0 : ℝ)) y‖ ^ 2 = (0 : ℝ)
        rw [eq_zero_of_dim_zero (gradient w y - gradient (fun _ : Euc 0 => (0 : ℝ)) y),
          norm_zero]
        norm_num
      rw [integral_congr_ae hz]
      simp
  -- the two classical inputs
  obtain ⟨M, R₁, hR₁, hM0, hdata⟩ :=
    exists_frozen_replacement_data d (α := α) (μ := μ) (Λ := Λ) (R := R) hα hα1 hμ hR
  have hΛ'0 : (0 : ℝ) ≤ max Λ 0 := le_max_right _ _
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = volume.real (Metric.closedBall (0 : Euc d) 1) *
      (2 * max Λ 0 ^ 2 * M ^ 2 + 18 * max Λ 0 ^ 2 + max Λ 0 * M + max Λ 0) / μ ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ volume.real (Metric.closedBall (0 : Euc d) 1) :=
      volume_real_closedBall_pos.le
    have h2 : (0 : ℝ) < μ ^ 2 := by positivity
    have t1 : (0 : ℝ) ≤ 2 * max Λ 0 ^ 2 * M ^ 2 := by positivity
    have t2 : (0 : ℝ) ≤ 18 * max Λ 0 ^ 2 := by positivity
    have t3 : (0 : ℝ) ≤ max Λ 0 * M := mul_nonneg hΛ'0 hM0
    have h4 : (0 : ℝ) ≤
        2 * max Λ 0 ^ 2 * M ^ 2 + 18 * max Λ 0 ^ 2 + max Λ 0 * M + max Λ 0 := by linarith
    rw [hKdef]
    exact div_nonneg (mul_nonneg h1 h4) h2.le
  refine ⟨K * (2 : ℝ) ^ ((d : ℝ) + 2 * α), min R₁ (min (1 / 2) (R / 2)),
    lt_min hR₁ (lt_min (by norm_num) (by linarith)),
    mul_nonneg hK0 (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro x₀ A g w hell hbdd hhol hgc hgbd hw hwbd hwlip hweak x hx r hr hrR₀
  have hrR₁ : r ≤ R₁ := hrR₀.trans (min_le_left _ _)
  have hr12 : r ≤ 1 / 2 := hrR₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrR2 : r ≤ R / 2 := hrR₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hMbd, h, hh1, hHcx, hhsol, ψ, hψW, hψgrad, heqw, heqh⟩ :=
    hdata x₀ A g w hell hbdd hhol hgc hgbd hw hwbd hwlip hweak x hx r hr hrR₁
  refine ⟨h, hh1, hhsol, ?_⟩
  -- the working ball `B̄(x, 2r)` — the ball of the frozen Dirichlet problem — sits inside
  -- `B(x₀, 2R)`, because `r ≤ R / 2`
  have hsubW : Metric.closedBall x (2 * r) ⊆ Metric.ball x₀ (2 * R) := by
    intro y hy
    have h1 : dist y x ≤ 2 * r := Metric.mem_closedBall.1 hy
    have h2 : dist x x₀ < R := Metric.mem_ball.1 hx
    have h3 : dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle y x x₀
    exact Metric.mem_ball.2 (by linarith)
  have hxball : x ∈ Metric.ball x₀ (2 * R) := Metric.ball_subset_ball (by linarith) hx
  -- the hypotheses of the comparison estimate
  have hoscx : ∀ y ∈ Metric.closedBall x (2 * r),
      ‖A x - A y‖ ≤ max Λ 0 * (2 * r) ^ α := by
    intro y hy
    have h1 := hhol x hxball y (hsubW hy)
    have h2 : dist x y ≤ 2 * r := by
      rw [dist_comm]
      exact Metric.mem_closedBall.1 hy
    have h3 : dist x y ^ α ≤ (2 * r) ^ α := Real.rpow_le_rpow dist_nonneg h2 hα.le
    have h4 : Λ * dist x y ^ α ≤ max Λ 0 * (2 * r) ^ α :=
      mul_le_mul (le_max_left _ _) h3 (Real.rpow_nonneg dist_nonneg _) hΛ'0
    linarith
  have hgbdx : ∀ y ∈ Metric.closedBall x (2 * r), |g y| ≤ max Λ 0 := fun y hy =>
    (hgbd y (hsubW hy)).trans (le_max_left _ _)
  have hAcx : ContinuousOn A (Metric.closedBall x (2 * r)) :=
    (continuousOn_of_holder (Λ := Λ) hα hhol).mono hsubW
  have hWcx : ContinuousOn (gradient w) (Metric.closedBall x (2 * r)) :=
    (continuousOn_gradient Metric.isOpen_ball hw).mono hsubW
  have hest := frozen_energy_estimate_of_memLp (d := d) hd (α := α) (μ := μ) (Λ := max Λ 0) (M := M)
    (s := 2 * r) (x := x) (A₀ := A x) (A := A) (g := g) (ψ := ψ) (W := gradient w)
    (H := gradient h) hα hα1.le hμ hΛ'0 hM0 (by linarith) (by linarith)
    (hell x hxball) hoscx hgbdx hMbd hAcx (hgc.mono hsubW) hWcx hHcx hψW hψgrad
    heqw heqh
  have hmono : (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) ≤
      ∫ y in Metric.closedBall x (2 * r), ‖gradient w y - gradient h y‖ ^ 2 := by
    have hsub : Metric.closedBall x r ⊆ Metric.closedBall x (2 * r) :=
      Metric.closedBall_subset_closedBall (by linarith)
    refine setIntegral_mono_set ?_ (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE
    have hW : MemLp (gradient w) 2 (volume.restrict (Metric.closedBall x (2 * r))) :=
      (memLp_two_iff_integrable_sq_norm
        (hWcx.aestronglyMeasurable measurableSet_closedBall)).2
        ((hWcx.norm.pow 2).integrableOn_compact (isCompact_closedBall x (2 * r)))
    exact (hW.sub hHcx).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hpow : (2 * r) ^ ((d : ℝ) + 2 * α) =
      (2 : ℝ) ^ ((d : ℝ) + 2 * α) * r ^ ((d : ℝ) + 2 * α) :=
    Real.mul_rpow (by norm_num) hr.le
  rw [hKdef]
  refine (hmono.trans hest).trans (le_of_eq ?_)
  rw [hpow]
  ring

/-! ### The perturbed (freezing) decay -/

/-- **Perturbed gradient-energy decay** (Gilbarg–Trudinger, Theorem 8.32, steps 1–2).  Writing
`Φ(x, s) = ∫_{B(x,s)} ‖∇w - (∇w)_{B(x,s)}‖²`, the constant-coefficient base decay
(`exists_constCoeff_sqExcess_decay`) together with the freezing comparison
(`exists_frozen_comparison`) give, uniformly over `x₀, A, g, w` obeying the standing hypotheses,
`Φ(x, ρ) ≤ C₁ (ρ/r)^{d+2} Φ(x, r) + C₂ r^{d+2α}` for all `0 < ρ ≤ r ≤ R₀`.

This is the statement of `Komlos.Literature.schauder_perturbed_energy_decay`. -/
theorem exists_perturbed_sqExcess_decay (d : ℕ) {α μ Λ R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hμ : 0 < μ) (hR : 0 < R) :
    ∃ C₁ C₂ R₀ : ℝ, 0 < R₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (x₀ : Euc d) (A : Euc d → Euc d →L[ℝ] Euc d) (g w : Euc d → ℝ),
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ ζ, μ * ‖ζ‖ ^ 2 ≤ ⟪A x ζ, ζ⟫) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ‖A x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖A x - A y‖ ≤ Λ * dist x y ^ α) →
      ContinuousOn g (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |g x| ≤ Λ) →
      ContDiffOn ℝ 1 w (Metric.ball x₀ (2 * R)) → (∀ x ∈ Metric.ball x₀ (2 * R), |w x| ≤ Λ) →
      (∃ Cw : ℝ, ∀ x ∈ Metric.ball x₀ (2 * R), ∀ y ∈ Metric.ball x₀ (2 * R),
        ‖gradient w x - gradient w y‖ ≤ Cw * dist x y ^ α) →
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * R) →
        ∫ x, ⟪A x (gradient w x), gradient ψ x⟫ = ∫ x, g x * ψ x) →
      ∀ x ∈ Metric.ball x₀ R, ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ →
        (∫ y in Metric.closedBall x ρ,
            ‖gradient w y - (⨍ z in Metric.closedBall x ρ, gradient w z)‖ ^ 2) ≤
          C₁ * (ρ / r) ^ ((d : ℝ) + 2) *
            (∫ y in Metric.closedBall x r,
              ‖gradient w y - (⨍ z in Metric.closedBall x r, gradient w z)‖ ^ 2) +
          C₂ * r ^ ((d : ℝ) + 2 * α) := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_constCoeff_sqExcess_decay d (μ := μ) (Λ := Λ) hμ
  obtain ⟨CB, RB, hRB, hCB0, hCB⟩ :=
    exists_frozen_comparison d (α := α) (μ := μ) (Λ := Λ) (R := R) hα hα1 hμ hR
  refine ⟨4 * CA, (2 + 4 * CA) * CB, min RB (R / 2), lt_min hRB (by linarith), by linarith,
    mul_nonneg (by linarith) hCB0, ?_⟩
  intro x₀ A g w hell hbdd hhol hgc hgbd hw hwbd hwlip hweak x hx ρ r hρ hρr hrR₀
  have hr : 0 < r := lt_of_lt_of_le hρ hρr
  have hrRB : r ≤ RB := hrR₀.trans (min_le_left _ _)
  have hrR2 : r ≤ R / 2 := hrR₀.trans (min_le_right _ _)
  obtain ⟨h, hh1, hhsol, hcomp⟩ :=
    hCB x₀ A g w hell hbdd hhol hgc hgbd hw hwbd hwlip hweak x hx r hr hrRB
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
      CB * r ^ ((d : ℝ) + 2 * α) := hcomp
  have hfin : (2 + 4 * CA) *
      (∫ y in Metric.closedBall x r, ‖gradient w y - gradient h y‖ ^ 2) ≤
      (2 + 4 * CA) * (CB * r ^ ((d : ℝ) + 2 * α)) :=
    mul_le_mul_of_nonneg_left hEb (by linarith)
  have hkey : sqExcess (gradient w) x ρ ≤
      4 * CA * (ρ / r) ^ ((d : ℝ) + 2) * sqExcess (gradient w) x r +
        (2 + 4 * CA) * CB * r ^ ((d : ℝ) + 2 * α) := by
    linarith [hstep1, hEρ, hstep2, hmul, hqE, hfin]
  exact hkey

end Komlos.Literature
