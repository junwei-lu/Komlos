import Komlos.Literature.PLaplacian.FluxIncrement
import Komlos.Literature.PLaplacian.DiffQuotBasic
import Komlos.Literature.Regularized.TruncatedProfileFlux

/-!
# Mollifying the monotonicity estimates of `∇Φ_R`

`REGULARIZED_ROUTE.md`, Revision 2, needs the *global* two-sided ellipticity of
`Ψ_p = Φ_R ∗ ρ_ε`.  The two-sided monotonicity estimates of `∇Φ_R`
(`Komlos/Literature/Regularized/TruncatedProfileFlux.lean`) degenerate at the origin for
`p > 2` and blow up there for `p < 2`; the mollification repairs both defects.  This file
carries the estimates through the convolution.

* `gradient_truncSmoothedProfile`: `∇Ψ_p = (∇Φ_R) ∗ ρ`, from the weak-gradient identity
  `Komlos.Literature.gradient_mollifyWith` — never by differentiating `Φ_R` twice.
* `inner_gradient_truncSmoothedProfile_sub`: the resulting two-point identity
  `⟪∇Ψ_p q - ∇Ψ_p q', q - q'⟫ = ∫ ρ(y) ⟪a(q - y) - a(q' - y), q - q'⟫ dy`.
* `exists_flux_two_bounds`: the *unweighted* two-sided monotonicity of `flux 2 F = ∇(F²/2)`,
  the `p = 2` instances of `IsSmoothStrictNorm.exists_pos_weighted_normSq_le_inner_flux_sub`
  and `IsSmoothStrictNorm.exists_norm_flux_sub_le`.
* The two *non-degenerate* regimes, where the pointwise constant already suffices:
  `exists_strongly_monotone_le_two` (`1 < p ≤ 2`) and `exists_lipschitz_two_le` (`2 ≤ p`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The kernel form of a mollification -/

section Kernel

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- `(ρ ∗ g)(x) = ∫ ρ(y) g(x - y) dy`, the vector-valued version of
`Komlos.Literature.Korevaar.mollifyWith_eq_kernel_integral`. -/
theorem mollifyWith_eq_kernel_integral' (ρ : Euc d → ℝ) (g : Euc d → H) (x : Euc d) :
    mollifyWith ρ g x = ∫ y, ρ y • g (x - y) := by
  rw [mollifyWith]
  have h := integral_sub_left_eq_self (fun t => ρ t • g (x - t)) volume x
  simp only [sub_sub_cancel] at h
  exact h

variable {ρ : Euc d → ℝ} {ε : ℝ}

theorem integrable_kernel_smul (hρ : IsMollifier ρ ε) {g : Euc d → H} (hg : Continuous g)
    (q : Euc d) : Integrable fun y => ρ y • g (q - y) :=
  (hρ.continuous.smul
      (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    hρ.hasCompactSupport.smul_right

theorem integrable_kernel_mul (hρ : IsMollifier ρ ε) {g : Euc d → ℝ} (hg : Continuous g)
    (q : Euc d) : Integrable fun y => ρ y * g (q - y) :=
  (hρ.continuous.mul
      (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    hρ.hasCompactSupport.mul_right

/-- `∫ ρ(y) c dy = c`. -/
theorem integral_kernel_const (hρ : IsMollifier ρ ε) (c : ℝ) : (∫ y, ρ y * c) = c := by
  rw [integral_mul_const, hρ.integral_eq_one, one_mul]

end Kernel


/-! ### Generic-domain integrability wrappers -/

theorem integrable_add_fun {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (fun x => f x + g x) μ := hf.add hg

theorem integrable_sub_fun {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (fun x => f x - g x) μ := hf.sub hg

/-! ### Elementary kernel facts -/

section KernelFacts

variable {ε : ℝ} {ρ : Euc d → ℝ}

/-- A mollifier is bounded. -/
theorem exists_kernel_bound (hρ : IsMollifier ρ ε) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ρ y ≤ M := by
  obtain ⟨y₀, hy₀⟩ :=
    hρ.continuous.exists_forall_ge_of_hasCompactSupport hρ.hasCompactSupport
  exact ⟨max (ρ y₀) 0, le_max_right _ _, fun y => (hy₀ y).trans (le_max_left _ _)⟩

/-- The change of variables `y ↦ q - y` in a kernel integral. -/
theorem integral_kernel_comm (ρ : Euc d → ℝ) (f : Euc d → ℝ) (q : Euc d) :
    (∫ y, ρ y * f (q - y)) = ∫ t, ρ (q - t) * f t := by
  have h := integral_sub_left_eq_self (fun y => ρ y * f (q - y)) volume q
  simp only [sub_sub_cancel] at h
  exact h.symm

theorem integral_kernel_shift (hρ : IsMollifier ρ ε) (q : Euc d) : (∫ t, ρ (q - t)) = 1 := by
  rw [integral_sub_left_eq_self ρ volume q, hρ.integral_eq_one]

end KernelFacts

/-! ### Smallness of the kernel mass of small `F`-balls -/

section Mass

variable {ε : ℝ} {F ρ : Euc d → ℝ}

/-- **The `ρ`-mass of an `F`-ball of small radius is small, uniformly in its centre.**  The
mass is at most `‖ρ‖_∞` times the Lebesgue measure of the ball, which is `O(δ^d)`. -/
theorem exists_delta_mass_le (hd : 0 < d) (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : Euc d,
      (∫ y, Set.indicator {y : Euc d | F (q - y) < δ} ρ y) ≤ η := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.1 hd
  have : Nontrivial (Euc d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  obtain ⟨M, hM0, hM⟩ := exists_kernel_bound hρ
  obtain ⟨c₁, hc₁, hc₁F⟩ := hF.exists_pos_mul_norm_le
  set V := (volume (Metric.ball (0 : Euc d) 1)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVfin : volume (Metric.ball (0 : Euc d) 1) ≠ ⊤ := measure_ball_lt_top.ne
  set Kc := M * V + 1 with hKcdef
  have hKc : 0 < Kc := by positivity
  set r := min 1 (η / Kc) with hrdef
  have hr0 : 0 < r := lt_min one_pos (div_pos hη hKc)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrη : r ≤ η / Kc := min_le_right _ _
  refine ⟨c₁ * r, mul_pos hc₁ hr0, fun q => ?_⟩
  set A := {y : Euc d | F (q - y) < c₁ * r} with hA
  have hAmeas : MeasurableSet A :=
    (isOpen_lt (hF.continuous.comp (continuous_const.sub continuous_id))
      continuous_const).measurableSet
  have hAsub : A ⊆ Metric.closedBall q r := by
    intro y hy
    have h1 : c₁ * ‖q - y‖ ≤ F (q - y) := hc₁F _
    have h2 : F (q - y) < c₁ * r := hy
    have h3 : ‖q - y‖ < r := by
      by_contra hcon
      exact absurd (le_trans (mul_le_mul_of_nonneg_left (not_lt.1 hcon) hc₁.le) h1) (not_le.2 h2)
    rw [Metric.mem_closedBall, dist_eq_norm, ← norm_neg]
    simpa using h3.le
  have hball : volume (Metric.closedBall q r) =
      ENNReal.ofReal (r ^ d) * volume (Metric.ball (0 : Euc d) 1) := by
    rw [Measure.addHaar_closedBall volume q hr0.le, finrank_euclideanSpace_fin]
  have hvolA : volume A ≤ ENNReal.ofReal (r ^ d) * volume (Metric.ball (0 : Euc d) 1) :=
    hball ▸ measure_mono hAsub
  have hfinA : volume A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hvolA
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin
  have htoreal : (volume A).toReal ≤ r ^ d * V := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) hvolA
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  have hsetint : (∫ y in A, ρ y) ≤ M * (volume A).toReal := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A) (f := ρ) (C := M)
      (lt_top_iff_ne_top.2 hfinA) (fun x _ => by
        rw [Real.norm_of_nonneg (hρ.nonneg x)]; exact hM x)
    refine le_trans (Real.le_norm_self _) ?_
    simpa [measureReal_def] using h
  have hrd : r ^ d ≤ r := by
    calc r ^ d ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1 hd
      _ = r := pow_one r
  rw [integral_indicator hAmeas]
  calc (∫ y in A, ρ y) ≤ M * (volume A).toReal := hsetint
    _ ≤ M * (r ^ d * V) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        exact htoreal
    _ ≤ M * (r * V) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        exact mul_le_mul_of_nonneg_right hrd hV0
    _ = (M * V) * r := by ring
    _ ≤ Kc * r := mul_le_mul_of_nonneg_right (by linarith) hr0.le
    _ ≤ Kc * (η / Kc) := mul_le_mul_of_nonneg_left hrη hKc.le
    _ = η := by field_simp

end Mass

/-! ### `∇Ψ_p = (∇Φ_R) ∗ ρ` and the two-point identity -/

section Gradient

variable {p R ε : ℝ} {F ρ : Euc d → ℝ}

/-- **The gradient of the mollified truncated profile is the mollified flux.** -/
theorem gradient_truncSmoothedProfile (hp : 1 < p) (hR : 0 < R) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) :
    gradient (truncSmoothedProfile p F R ρ) = mollifyWith ρ (truncFlux p F R) :=
  gradient_mollifyWith (hasWeakGradient_truncProfile hp hR hF) hρ.contDiff hρ.hasCompactSupport

/-- **The two-point monotonicity form of `∇Ψ_p` as an integral against the kernel.** -/
theorem inner_gradient_truncSmoothedProfile_sub (hp : 1 < p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) (q q' : Euc d) :
    ⟪gradient (truncSmoothedProfile p F R ρ) q -
        gradient (truncSmoothedProfile p F R ρ) q', q - q'⟫ =
      ∫ y, ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ := by
  have ha : Continuous (truncFlux p F R) := continuous_truncFlux hp hR hF
  have e : ∀ x : Euc d, ⟪mollifyWith ρ (truncFlux p F R) x, q - q'⟫ =
      ∫ y, ρ y * ⟪truncFlux p F R (x - y), q - q'⟫ := by
    intro x
    rw [mollifyWith_eq_kernel_integral', real_inner_comm,
      ← integral_inner (integrable_kernel_smul hρ ha x) (q - q')]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ⟪q - q', ρ y • truncFlux p F R (x - y)⟫ = ρ y * ⟪truncFlux p F R (x - y), q - q'⟫
    rw [real_inner_smul_right, real_inner_comm (q - q') (truncFlux p F R (x - y))]
  have hI1 : Integrable fun y => ρ y * ⟪truncFlux p F R (q - y), q - q'⟫ :=
    integrable_kernel_mul hρ (ha.inner continuous_const) q
  have hI2 : Integrable fun y => ρ y * ⟪truncFlux p F R (q' - y), q - q'⟫ :=
    integrable_kernel_mul hρ (ha.inner continuous_const) q'
  rw [gradient_truncSmoothedProfile hp hR hF hρ, inner_sub_left, e q, e q',
    ← integral_sub hI1 hI2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show ρ y * ⟪truncFlux p F R (q - y), q - q'⟫ - ρ y * ⟪truncFlux p F R (q' - y), q - q'⟫ =
    ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫
  rw [inner_sub_left]
  ring

/-- Integrability of the kernel integrand of the two-point monotonicity form. -/
theorem integrable_kernel_diff (hp : 1 < p) (hR : 0 < R) (hF : IsSmoothStrictNorm F)
    (hρ : IsMollifier ρ ε) (q q' : Euc d) :
    Integrable fun y : Euc d =>
      ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ := by
  have ha : Continuous (truncFlux p F R) := continuous_truncFlux hp hR hF
  have hc : Continuous fun y : Euc d =>
      ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ :=
    (((ha.comp (continuous_const.sub continuous_id)).sub
      (ha.comp (continuous_const.sub continuous_id)))).inner continuous_const
  exact (hρ.continuous.mul hc).integrable_of_hasCompactSupport hρ.hasCompactSupport.mul_right

end Gradient

/-! ### The unweighted monotonicity of `flux 2 F` -/

/-- **The `p = 2` flux is strongly monotone and Lipschitz, with no weight**: the weight
`(‖ξ‖+‖ζ‖)^{p-2}` of `IsSmoothStrictNorm.exists_pos_weighted_normSq_le_inner_flux_sub` and of
`IsSmoothStrictNorm.exists_norm_flux_sub_le` is `1` at `p = 2`. -/
theorem exists_flux_two_bounds {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) :
    ∃ c L : ℝ, 0 < c ∧ 0 ≤ L ∧ ∀ u v : Euc d,
      c * ‖u - v‖ ^ 2 ≤ ⟪flux 2 F u - flux 2 F v, u - v⟫ ∧
        ⟪flux 2 F u - flux 2 F v, u - v⟫ ≤ L * ‖u - v‖ ^ 2 := by
  obtain ⟨c, hc, hmono⟩ := hF.exists_pos_weighted_normSq_le_inner_flux_sub (p := 2) (by norm_num)
  obtain ⟨L, hL, hlip⟩ := hF.exists_norm_flux_sub_le (p := 2) (by norm_num)
  have hz : ((2 : ℝ) - 2) = 0 := by norm_num
  refine ⟨c, L, hc, hL.le, fun u v => ⟨?_, ?_⟩⟩
  · have h := hmono u v
    rwa [hz, Real.rpow_zero, one_mul] at h
  · have h := hlip u v
    rw [hz, Real.rpow_zero, mul_one] at h
    calc ⟪flux 2 F u - flux 2 F v, u - v⟫ ≤ ‖flux 2 F u - flux 2 F v‖ * ‖u - v‖ :=
          real_inner_le_norm _ _
      _ ≤ (L * ‖u - v‖) * ‖u - v‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = L * ‖u - v‖ ^ 2 := by ring

/-! ### The two non-degenerate regimes -/

section NonDegenerate

variable {p R ε : ℝ} {F ρ : Euc d → ℝ}

/-- **`1 < p ≤ 2`: strong monotonicity of `∇Ψ_p`.**  Here `Φ_R` is already uniformly convex
(with the constant of `(p-1)R^{p-2} F²/2`), and mollification preserves that. -/
theorem exists_strongly_monotone_le_two (hp : 1 < p) (hp2 : p ≤ 2) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ q q' : Euc d,
      c * ‖q - q'‖ ^ 2 ≤
        ⟪gradient (truncSmoothedProfile p F R ρ) q -
          gradient (truncSmoothedProfile p F R ρ) q', q - q'⟫ := by
  obtain ⟨c₂, L₂, hc₂, hL₂, hbounds⟩ := exists_flux_two_bounds hF
  have hlam : 0 < (p - 1) * R ^ (p - 2) := by
    have : (0 : ℝ) < R ^ (p - 2) := Real.rpow_pos_of_pos hR _
    nlinarith
  refine ⟨(p - 1) * R ^ (p - 2) * c₂, by positivity, fun q q' => ?_⟩
  have hpt : ∀ y : Euc d,
      ρ y * ((p - 1) * R ^ (p - 2) * c₂ * ‖q - q'‖ ^ 2) ≤
        ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ := by
    intro y
    have hsub : q - y - (q' - y) = q - q' := by abel
    have h1 := inner_truncFlux_sub_ge_const hp hp2 hR hF (q - y) (q' - y)
    have h2 := (hbounds (q - y) (q' - y)).1
    rw [hsub] at h1 h2
    have h3 : (p - 1) * R ^ (p - 2) * (c₂ * ‖q - q'‖ ^ 2) ≤
        (p - 1) * R ^ (p - 2) * ⟪flux 2 F (q - y) - flux 2 F (q' - y), q - q'⟫ :=
      mul_le_mul_of_nonneg_left h2 hlam.le
    refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg y)
    nlinarith [h1, h3]
  have hint1 : Integrable fun y : Euc d =>
      ρ y * ((p - 1) * R ^ (p - 2) * c₂ * ‖q - q'‖ ^ 2) := hρ.integrable.mul_const _
  have hint2 : Integrable fun y : Euc d =>
      ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ :=
    integrable_kernel_diff hp hR hF hρ q q'
  rw [inner_gradient_truncSmoothedProfile_sub hp hR hF hρ]
  calc (p - 1) * R ^ (p - 2) * c₂ * ‖q - q'‖ ^ 2
      = ∫ y, ρ y * ((p - 1) * R ^ (p - 2) * c₂ * ‖q - q'‖ ^ 2) :=
        (integral_kernel_const hρ _).symm
    _ ≤ _ := integral_mono hint1 hint2 hpt

/-- **`2 ≤ p`: the Lipschitz (upper ellipticity) bound for `∇Ψ_p`.** -/
theorem exists_lipschitz_two_le (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q q' : Euc d,
      ⟪gradient (truncSmoothedProfile p F R ρ) q -
          gradient (truncSmoothedProfile p F R ρ) q', q - q'⟫ ≤ C * ‖q - q'‖ ^ 2 := by
  obtain ⟨c₂, L₂, hc₂, hL₂, hbounds⟩ := exists_flux_two_bounds hF
  have hlam : 0 ≤ (p - 1) * R ^ (p - 2) := by
    have : (0 : ℝ) < R ^ (p - 2) := Real.rpow_pos_of_pos hR _
    nlinarith
  refine ⟨(p - 1) * R ^ (p - 2) * L₂, by positivity, fun q q' => ?_⟩
  have hpt : ∀ y : Euc d,
      ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ ≤
        ρ y * ((p - 1) * R ^ (p - 2) * L₂ * ‖q - q'‖ ^ 2) := by
    intro y
    have hsub : q - y - (q' - y) = q - q' := by abel
    have h1 := inner_truncFlux_sub_le_const hp hp2 hR hF (q - y) (q' - y)
    have h2 := (hbounds (q - y) (q' - y)).2
    rw [hsub] at h1 h2
    have h3 : (p - 1) * R ^ (p - 2) * ⟪flux 2 F (q - y) - flux 2 F (q' - y), q - q'⟫ ≤
        (p - 1) * R ^ (p - 2) * (L₂ * ‖q - q'‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hlam
    refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg y)
    nlinarith [h1, h3]
  have hint2 : Integrable fun y : Euc d =>
      ρ y * ((p - 1) * R ^ (p - 2) * L₂ * ‖q - q'‖ ^ 2) := hρ.integrable.mul_const _
  have hint1 : Integrable fun y : Euc d =>
      ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ :=
    integrable_kernel_diff hp hR hF hρ q q'
  rw [inner_gradient_truncSmoothedProfile_sub hp hR hF hρ]
  calc (∫ y, ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫)
      ≤ ∫ y, ρ y * ((p - 1) * R ^ (p - 2) * L₂ * ‖q - q'‖ ^ 2) := integral_mono hint1 hint2 hpt
    _ = (p - 1) * R ^ (p - 2) * L₂ * ‖q - q'‖ ^ 2 := integral_kernel_const hρ _

end NonDegenerate


/-! ### The degenerate regime `2 ≤ p`: strong monotonicity from the kernel mass -/

section Degenerate

variable {p R ε : ℝ} {F ρ : Euc d → ℝ}

/-- **`2 ≤ p`: strong monotonicity of `∇Ψ_p`.**  The weight `min(W(F u), W(F v))` of
`inner_truncFlux_sub_ge_weight` degenerates only where both `q - y` and `q' - y` are close to
the origin, a set of `y` of small `ρ`-mass (`exists_delta_mass_le`). -/
theorem exists_strongly_monotone_two_le (hd : 0 < d) (hp : 1 < p) (hp2 : 2 ≤ p) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ q q' : Euc d,
      c * ‖q - q'‖ ^ 2 ≤
        ⟪gradient (truncSmoothedProfile p F R ρ) q -
          gradient (truncSmoothedProfile p F R ρ) q', q - q'⟫ := by
  obtain ⟨c₂, L₂, hc₂, hL₂, hbounds⟩ := exists_flux_two_bounds hF
  obtain ⟨δ₀, hδ₀, hmass₀⟩ := exists_delta_mass_le hd hF hρ (η := 1 / 4) (by norm_num)
  set δ := min δ₀ R with hδdef
  have hδ : 0 < δ := lt_min hδ₀ hR
  have hδR : δ ≤ R := min_le_right _ _
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hmeasA : ∀ q : Euc d, MeasurableSet {y : Euc d | F (q - y) < δ} := fun q =>
    (isOpen_lt (hF.continuous.comp (continuous_const.sub continuous_id))
      continuous_const).measurableSet
  have hmeasA₀ : ∀ q : Euc d, MeasurableSet {y : Euc d | F (q - y) < δ₀} := fun q =>
    (isOpen_lt (hF.continuous.comp (continuous_const.sub continuous_id))
      continuous_const).measurableSet
  have hmass : ∀ q : Euc d,
      (∫ y, Set.indicator {y : Euc d | F (q - y) < δ} ρ y) ≤ 1 / 4 := by
    intro q
    refine le_trans (integral_mono (hρ.integrable.indicator (hmeasA q))
      (hρ.integrable.indicator (hmeasA₀ q)) ?_) (hmass₀ q)
    exact Set.indicator_le_indicator_of_subset
      (fun y hy => lt_of_lt_of_le hy hδδ₀) (fun y => hρ.nonneg y)
  set m₀ := δ ^ (p - 2) with hm₀def
  have hm₀ : 0 < m₀ := Real.rpow_pos_of_pos hδ _
  have hmw : ∀ z : Euc d, δ ≤ F z → m₀ ≤ truncWeight p R (F z) := by
    intro z hz
    exact Real.rpow_le_rpow hδ.le (le_min hz hδR) (by linarith)
  refine ⟨m₀ * c₂ / 2, by positivity, fun q q' => ?_⟩
  set A := {y : Euc d | F (q - y) < δ} with hA
  set A' := {y : Euc d | F (q' - y) < δ} with hA'
  set K := m₀ * c₂ * ‖q - q'‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hce : (0 : ℝ) ≤ c₂ * ‖q - q'‖ ^ 2 := by positivity
  have hpt : ∀ y : Euc d,
      K * (ρ y - Set.indicator A ρ y - Set.indicator A' ρ y) ≤
        ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ := by
    intro y
    have hsub : q - y - (q' - y) = q - q' := by abel
    have h1 := inner_truncFlux_sub_ge_weight hp hp2 hR hF (q - y) (q' - y)
    have h2 := (hbounds (q - y) (q' - y)).1
    rw [hsub] at h1 h2
    have hW0 : 0 ≤ min (truncWeight p R (F (q - y))) (truncWeight p R (F (q' - y))) :=
      le_min (truncWeight_nonneg hR.le (hF.nonneg _)) (truncWeight_nonneg hR.le (hF.nonneg _))
    have h3 : min (truncWeight p R (F (q - y))) (truncWeight p R (F (q' - y))) *
        (c₂ * ‖q - q'‖ ^ 2) ≤
          ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ :=
      le_trans (mul_le_mul_of_nonneg_left h2 hW0) h1
    have h4 : m₀ * (ρ y - Set.indicator A ρ y - Set.indicator A' ρ y) ≤
        ρ y * min (truncWeight p R (F (q - y))) (truncWeight p R (F (q' - y))) := by
      have hnn : 0 ≤ ρ y * min (truncWeight p R (F (q - y))) (truncWeight p R (F (q' - y))) :=
        mul_nonneg (hρ.nonneg y) hW0
      rcases Classical.em (y ∈ A) with hyA | hyA
      · rw [Set.indicator_of_mem hyA]
        have hA'0 : 0 ≤ Set.indicator A' ρ y :=
          Set.indicator_nonneg (fun _ _ => hρ.nonneg _) y
        nlinarith [hm₀.le]
      · rcases Classical.em (y ∈ A') with hyA' | hyA'
        · rw [Set.indicator_of_notMem hyA, Set.indicator_of_mem hyA']
          have : m₀ * (ρ y - 0 - ρ y) = 0 := by ring
          rw [this]
          exact hnn
        · rw [Set.indicator_of_notMem hyA, Set.indicator_of_notMem hyA']
          have hWm : m₀ ≤ min (truncWeight p R (F (q - y))) (truncWeight p R (F (q' - y))) :=
            le_min (hmw _ (not_lt.1 hyA)) (hmw _ (not_lt.1 hyA'))
          nlinarith [hρ.nonneg y]
    calc K * (ρ y - Set.indicator A ρ y - Set.indicator A' ρ y)
        = (c₂ * ‖q - q'‖ ^ 2) * (m₀ * (ρ y - Set.indicator A ρ y - Set.indicator A' ρ y)) := by
          rw [hK]; ring
      _ ≤ (c₂ * ‖q - q'‖ ^ 2) *
            (ρ y * min (truncWeight p R (F (q - y))) (truncWeight p R (F (q' - y)))) :=
          mul_le_mul_of_nonneg_left h4 hce
      _ = ρ y * (min (truncWeight p R (F (q - y))) (truncWeight p R (F (q' - y))) *
            (c₂ * ‖q - q'‖ ^ 2)) := by ring
      _ ≤ ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ :=
          mul_le_mul_of_nonneg_left h3 (hρ.nonneg y)
  have hsub1 : Integrable fun y : Euc d => ρ y - Set.indicator A ρ y :=
    integrable_sub_fun hρ.integrable (hρ.integrable.indicator (hmeasA q))
  have hsub2 : Integrable fun y : Euc d =>
      ρ y - Set.indicator A ρ y - Set.indicator A' ρ y :=
    integrable_sub_fun hsub1 (hρ.integrable.indicator (hmeasA q'))
  have hintL : Integrable fun y : Euc d =>
      K * (ρ y - Set.indicator A ρ y - Set.indicator A' ρ y) := hsub2.const_mul K
  have hintR := integrable_kernel_diff hp hR hF hρ q q'
  have hmain := integral_mono hintL hintR hpt
  have eL : (∫ y, K * (ρ y - Set.indicator A ρ y - Set.indicator A' ρ y)) =
      K * (1 - (∫ y, Set.indicator A ρ y) - ∫ y, Set.indicator A' ρ y) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_sub hsub1 (hρ.integrable.indicator (hmeasA q')),
      integral_sub hρ.integrable (hρ.integrable.indicator (hmeasA q)), hρ.integral_eq_one]
  rw [eL] at hmain
  rw [inner_gradient_truncSmoothedProfile_sub hp hR hF hρ]
  refine le_trans ?_ hmain
  have h1 := hmass q
  have h2 := hmass q'
  have : K / 2 ≤ K * (1 - (∫ y, Set.indicator A ρ y) - ∫ y, Set.indicator A' ρ y) := by
    nlinarith [hK0]
  calc m₀ * c₂ / 2 * ‖q - q'‖ ^ 2 = K / 2 := by rw [hK]; ring
    _ ≤ _ := this

end Degenerate

/-! ### The singular regime `p < 2`: a Lipschitz bound from an integrable weight -/

section Singular

variable {p R ε : ℝ} {F ρ : Euc d → ℝ}

/-- For `p < 2` the weight `W ∘ F` is continuous away from the origin and vanishes there (the
`Real.rpow` convention `0 ^ (p-2) = 0`), hence measurable. -/
theorem measurable_truncWeight_comp (hp2 : p < 2) (hR : 0 < R) (hF : IsSmoothStrictNorm F) :
    Measurable fun z : Euc d => truncWeight p R (F z) := by
  have hmin : Continuous fun z : Euc d => min (F z) R := hF.continuous.min continuous_const
  have key : (fun z : Euc d => truncWeight p R (F z)) =
      Set.indicator {(0 : Euc d)}ᶜ
        (fun z => Real.exp (Real.log (min (F z) R) * (p - 2))) := by
    funext z
    rcases eq_or_ne z 0 with rfl | hz
    · rw [Set.indicator_of_notMem (by simp), truncWeight, hF.map_zero, min_eq_left hR.le]
      exact Real.zero_rpow (by intro hc; linarith)
    · rw [Set.indicator_of_mem (by simpa using hz), truncWeight,
        Real.rpow_def_of_pos (lt_min (hF.pos z hz) hR)]
  rw [key]
  exact (Real.measurable_exp.comp
    ((Real.measurable_log.comp hmin.measurable).mul measurable_const)).indicator
      (measurableSet_singleton _).compl

/-- For `p < 2` the weight `W ∘ F` is integrable on the ball where the truncation is inactive:
there `W(F z) ≤ (c₁ ‖z‖)^{p-2}` and `p - 2 > -1 ≥ -d`. -/
theorem integrableOn_truncWeight_ball (hd : 0 < d) (hp : 1 < p) (hp2 : p < 2) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) {c₁ : ℝ} (hc₁ : 0 < c₁) (hc₁F : ∀ ξ : Euc d, c₁ * ‖ξ‖ ≤ F ξ) :
    IntegrableOn (fun z : Euc d => truncWeight p R (F z)) (Metric.ball 0 (R / c₁)) volume := by
  have hdim : 1 ≤ Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]; exact hd
  have hα : (2 - p) < (Module.finrank ℝ (Euc d) : ℝ) := by
    rw [finrank_euclideanSpace_fin]
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := c₁ ^ (p - 2)) hdim hα ?_
    (measurable_truncWeight_comp hp2 hR hF).aestronglyMeasurable
  refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
  have hzn : ‖z‖ < R / c₁ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    exact hz
  have hzc : c₁ * ‖z‖ < R := by
    rw [lt_div_iff₀ hc₁] at hzn
    linarith
  rw [Real.norm_of_nonneg (truncWeight_nonneg hR.le (hF.nonneg z)), truncWeight, neg_sub]
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [hF.map_zero, min_eq_left hR.le, norm_zero,
      Real.zero_rpow (by intro hc; linarith : p - 2 ≠ 0), mul_zero]
  · have hpos : 0 < c₁ * ‖z‖ := mul_pos hc₁ (norm_pos_iff.2 hz0)
    have hle : c₁ * ‖z‖ ≤ min (F z) R := le_min (hc₁F z) hzc.le
    have h1 : min (F z) R ^ (p - 2) ≤ (c₁ * ‖z‖) ^ (p - 2) :=
      Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    rwa [Real.mul_rpow hc₁.le (norm_nonneg z)] at h1

/-- **A uniform bound for the mollified weight** `∫ ρ(y) W(F(q - y)) dy ≤ M`, `p < 2`. -/
theorem exists_kernel_weight_bound (hd : 0 < d) (hp : 1 < p) (hp2 : p < 2) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Euc d,
      Integrable (fun y : Euc d => ρ y * truncWeight p R (F (q - y))) ∧
        (∫ y, ρ y * truncWeight p R (F (q - y))) ≤ M := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.1 hd
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_kernel_bound hρ
  obtain ⟨c₁, hc₁, hc₁F⟩ := hF.exists_pos_mul_norm_le
  set w : Euc d → ℝ := fun z => truncWeight p R (F z) with hw
  have hw0 : ∀ z, 0 ≤ w z := fun z => truncWeight_nonneg hR.le (hF.nonneg z)
  have hwmeas : Measurable w := measurable_truncWeight_comp hp2 hR hF
  set r₀ := R / c₁ with hr₀
  have hIB : IntegrableOn w (Metric.ball 0 r₀) volume :=
    integrableOn_truncWeight_ball hd hp hp2 hR hF hc₁ hc₁F
  have hindint : Integrable (Set.indicator (Metric.ball (0 : Euc d) r₀) w) :=
    hIB.integrable_indicator measurableSet_ball
  set A := ∫ t, Set.indicator (Metric.ball (0 : Euc d) r₀) w t with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun t => Set.indicator_nonneg (fun _ _ => hw0 _) t
  have hRp : (0 : ℝ) ≤ R ^ (p - 2) := Real.rpow_nonneg hR.le _
  refine ⟨R ^ (p - 2) + Mρ * A, by positivity, fun q => ?_⟩
  have hshift : Integrable fun t : Euc d => ρ (q - t) := (integrable_comp_sub_left ρ q).2 hρ.integrable
  have hmajint : Integrable fun t : Euc d =>
      R ^ (p - 2) * ρ (q - t) + Mρ * Set.indicator (Metric.ball (0 : Euc d) r₀) w t :=
    integrable_add_fun (hshift.const_mul _) (hindint.const_mul _)
  have hmaj : ∀ t : Euc d, ρ (q - t) * w t ≤
      R ^ (p - 2) * ρ (q - t) + Mρ * Set.indicator (Metric.ball (0 : Euc d) r₀) w t := by
    intro t
    rcases lt_or_ge ‖t‖ r₀ with hlt | hge
    · rw [Set.indicator_of_mem (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hlt)]
      have h1 : ρ (q - t) * w t ≤ Mρ * w t := mul_le_mul_of_nonneg_right (hMρ _) (hw0 t)
      have h2 : 0 ≤ R ^ (p - 2) * ρ (q - t) := mul_nonneg hRp (hρ.nonneg _)
      linarith
    · have hRle : R ≤ F t := by
        rw [hr₀, div_le_iff₀ hc₁] at hge
        exact le_trans (by linarith) (hc₁F t)
      have hwt : w t = R ^ (p - 2) := by
        simp only [hw, truncWeight]
        rw [min_eq_right hRle]
      have h2 : 0 ≤ Mρ * Set.indicator (Metric.ball (0 : Euc d) r₀) w t :=
        mul_nonneg hMρ0 (Set.indicator_nonneg (fun _ _ => hw0 _) t)
      rw [hwt]
      nlinarith [hρ.nonneg (q - t)]
  have hint_t : Integrable fun t : Euc d => ρ (q - t) * w t := by
    refine Integrable.mono' hmajint ?_ (Eventually.of_forall fun t => ?_)
    · exact ((hρ.continuous.comp (continuous_const.sub continuous_id)).measurable.mul
        hwmeas).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (hρ.nonneg _) (hw0 t))]
      exact hmaj t
  constructor
  · have h := (integrable_comp_sub_left (fun t : Euc d => ρ (q - t) * w t) q).2 hint_t
    refine h.congr (Eventually.of_forall fun y => ?_)
    show ρ (q - (q - y)) * w (q - y) = ρ y * w (q - y)
    rw [sub_sub_cancel]
  · have hcomm : (∫ y, ρ y * truncWeight p R (F (q - y))) = ∫ t, ρ (q - t) * w t :=
      integral_kernel_comm ρ w q
    rw [hcomm]
    calc (∫ t, ρ (q - t) * w t)
        ≤ ∫ t, (R ^ (p - 2) * ρ (q - t) +
            Mρ * Set.indicator (Metric.ball (0 : Euc d) r₀) w t) :=
          integral_mono hint_t hmajint hmaj
      _ = R ^ (p - 2) * 1 + Mρ * A := by
          rw [integral_add (hshift.const_mul _) (hindint.const_mul _), integral_const_mul,
            integral_const_mul, integral_kernel_shift hρ q]
      _ = R ^ (p - 2) + Mρ * A := by ring

/-- **`p < 2`: the Lipschitz (upper ellipticity) bound for `∇Ψ_p`.** -/
theorem exists_lipschitz_lt_two (hd : 0 < d) (hp : 1 < p) (hp2 : p < 2) (hR : 0 < R)
    (hF : IsSmoothStrictNorm F) (hρ : IsMollifier ρ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q q' : Euc d,
      ⟪gradient (truncSmoothedProfile p F R ρ) q -
          gradient (truncSmoothedProfile p F R ρ) q', q - q'⟫ ≤ C * ‖q - q'‖ ^ 2 := by
  obtain ⟨c₂, L₂, hc₂, hL₂, hbounds⟩ := exists_flux_two_bounds hF
  obtain ⟨M, hM0, hMbound⟩ := exists_kernel_weight_bound hd hp hp2 hR hF hρ
  refine ⟨2 * L₂ * M, by positivity, fun q q' => ?_⟩
  set E := L₂ * ‖q - q'‖ ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hpt : ∀ y : Euc d,
      ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ ≤
        E * (ρ y * truncWeight p R (F (q - y)) + ρ y * truncWeight p R (F (q' - y))) := by
    intro y
    have hsub : q - y - (q' - y) = q - q' := by abel
    have h1 := inner_truncFlux_sub_le_weight hp hp2.le hR hF (q - y) (q' - y)
    have h2 := (hbounds (q - y) (q' - y)).2
    rw [hsub] at h1 h2
    have hW0 : 0 ≤ truncWeight p R (F (q - y)) + truncWeight p R (F (q' - y)) :=
      add_nonneg (truncWeight_nonneg hR.le (hF.nonneg _))
        (truncWeight_nonneg hR.le (hF.nonneg _))
    have h3 : ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫ ≤
        (truncWeight p R (F (q - y)) + truncWeight p R (F (q' - y))) * E :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 hW0)
    have h4 := mul_le_mul_of_nonneg_left h3 (hρ.nonneg y)
    calc ρ y * ⟪truncFlux p F R (q - y) - truncFlux p F R (q' - y), q - q'⟫
        ≤ ρ y * ((truncWeight p R (F (q - y)) + truncWeight p R (F (q' - y))) * E) := h4
      _ = E * (ρ y * truncWeight p R (F (q - y)) + ρ y * truncWeight p R (F (q' - y))) := by
          ring
  have hI1 := (hMbound q).1
  have hI2 := (hMbound q').1
  have hintR : Integrable fun y : Euc d =>
      E * (ρ y * truncWeight p R (F (q - y)) + ρ y * truncWeight p R (F (q' - y))) :=
    (integrable_add_fun hI1 hI2).const_mul E
  have hintL := integrable_kernel_diff hp hR hF hρ q q'
  have hmain := integral_mono hintL hintR hpt
  have eR : (∫ y, E * (ρ y * truncWeight p R (F (q - y)) +
      ρ y * truncWeight p R (F (q' - y)))) =
      E * ((∫ y, ρ y * truncWeight p R (F (q - y))) +
        ∫ y, ρ y * truncWeight p R (F (q' - y))) := by
    rw [integral_const_mul, integral_add hI1 hI2]
  rw [eR] at hmain
  rw [inner_gradient_truncSmoothedProfile_sub hp hR hF hρ]
  refine le_trans hmain ?_
  have h1 := (hMbound q).2
  have h2 := (hMbound q').2
  nlinarith [hE0, hL₂, norm_nonneg (q - q')]

end Singular

end Komlos.Literature.Regularized
