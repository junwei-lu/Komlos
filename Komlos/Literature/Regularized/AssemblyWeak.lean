import Komlos.Literature.Regularized.AssemblyPointwise

/-!
# Wang–Xia for the regularized route: the weak inequality for `U = e^{-w}` (lane `L5`)

`REGULARIZED_ROUTE.md`, Revision 2, Wang–Xia step 2.  Multiplying the pointwise inequality of
`AssemblyPointwise` by `e^{-2 w_η} > 0` and using the product rule

`div (e^{-2w} ∇Ψ(∇w)) = e^{-2w} (div ∇Ψ(∇w) - 2 ⟪∇Ψ(∇w), ∇w⟫)`

turns `div ∇Ψ(∇w_η) ≤ κ w_η + Λ + B(∇w_η)`, `B(q) = 2(⟪∇Ψ q, q⟫ - Ψ q)`, into

`2 e^{-2w_η} Ψ(∇w_η) + κ (-w_η) e^{-2w_η} ≤ Λ e^{-2w_η} - div (e^{-2w_η} ∇Ψ(∇w_η))`.

Integrating against a nonnegative `C¹` test function `ψ` with compact support in `K_t` and
integrating by parts gives `integral_regDensity_le`; the limit `η ↓ 0` (local uniform
convergence `w_η → w`, `∇w_η → ∇w`) gives `integral_regDensity_le_zero`.

At `η = 0` and on `K_t` the three densities are, with `U = e^{-w}`:
`regMass = U²`, `regKin = U² Ψ(∇w) = U² Ψ(∇U/U)` (`Ψ` is even) and `regEnt = U² log U`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### A continuity helper -/

/-- The inner-product analogue of `continuous_mul_of_continuousOn`. -/
theorem continuous_inner_of_continuousOn {Ω : Set (Euc d)} (hΩ : IsOpen Ω)
    {f g : Euc d → Euc d} (hf : ContinuousOn f Ω) (hg : Continuous g) {S : Set (Euc d)}
    (hS : IsClosed S) (hSΩ : S ⊆ Ω) (hgS : ∀ x ∉ S, g x = 0) :
    Continuous fun x => ⟪f x, g x⟫ := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (hf.continuousAt (hΩ.mem_nhds hx)).inner hg.continuousAt
  · have hmem : Sᶜ ∈ 𝓝 x := hS.isOpen_compl.mem_nhds fun h => hx (hSΩ h)
    refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    rw [hgS y hy, inner_zero_right]

/-! ### The three densities and the flux -/

variable {κ : ℝ} {Ψ : Euc d → ℝ} {D : InfConvData d}

/-- The flux `G_η = e^{-2 w_η} ∇Ψ(∇w_η)`; at `η = 0` this is `U² ∇Ψ(∇w)`. -/
noncomputable def regFlux (Ψ : Euc d → ℝ) (D : InfConvData d) (η : ℝ) (z : Euc d) : Euc d :=
  Real.exp (-(2 * D.w η z)) • gradient Ψ (gradient (D.w η) z)

/-- The mass density `e^{-2 w_η}`; at `η = 0` this is `U²`. -/
noncomputable def regMass (D : InfConvData d) (η : ℝ) (z : Euc d) : ℝ :=
  Real.exp (-(2 * D.w η z))

/-- The kinetic density `e^{-2 w_η} Ψ(∇w_η)`; at `η = 0` this is `U² Ψ(∇U/U)`. -/
noncomputable def regKin (Ψ : Euc d → ℝ) (D : InfConvData d) (η : ℝ) (z : Euc d) : ℝ :=
  Real.exp (-(2 * D.w η z)) * Ψ (gradient (D.w η) z)

/-- The entropy density `-w_η e^{-2 w_η}`; at `η = 0` this is `U² log U`. -/
noncomputable def regEnt (D : InfConvData d) (η : ℝ) (z : Euc d) : ℝ :=
  -D.w η z * Real.exp (-(2 * D.w η z))

theorem regMass_pos (D : InfConvData d) (η : ℝ) (z : Euc d) : 0 < regMass D η z :=
  Real.exp_pos _

/-! ### The divergence identity -/

/-- `div (e^{-2w_η} ∇Ψ(∇w_η)) = e^{-2w_η} (div ∇Ψ(∇w_η) - 2 ⟪∇Ψ(∇w_η), ∇w_η⟫)`. -/
theorem divergence_regFlux (hΨ : IsRegProfile Ψ) {η : ℝ} (hη : 0 ≤ η) {z : Euc d}
    (hz : z ∈ D.Kt) (hcd : ContDiffAt ℝ 1 (gradient (D.w η)) z) :
    divergence (regFlux Ψ D η) z =
      Real.exp (-(2 * D.w η z)) *
        (divergence (fun y => gradient Ψ (gradient (D.w η) y)) z -
          2 * ⟪gradient Ψ (gradient (D.w η) z), gradient (D.w η) z⟫) := by
  have hw : HasGradientAt (D.w η) (gradient (D.w η) z) z :=
    ((D.differentiableOn_w hη).differentiableAt (D.isOpen_Kt.mem_nhds hz)).hasGradientAt
  have hc : HasGradientAt (fun y => Real.exp (-(2 * D.w η y)))
      ((-(2 * Real.exp (-(2 * D.w η z)))) • gradient (D.w η) z) z :=
    hasGradientAt_exp_neg_mul hw 2
  have hwd : HasFDerivAt (gradient (D.w η)) (fderiv ℝ (gradient (D.w η)) z) z :=
    (hcd.differentiableAt one_ne_zero).hasFDerivAt
  have hW : HasFDerivAt (fun y => gradient Ψ (gradient (D.w η) y))
      ((fderiv ℝ (gradient Ψ) (gradient (D.w η) z)).comp
        (fderiv ℝ (gradient (D.w η)) z)) z :=
    (hΨ.hasFDerivAt_gradient _).comp z hwd
  have h := divergence_smul hc hW
  have hfl : regFlux Ψ D η =
      fun y => Real.exp (-(2 * D.w η y)) • gradient Ψ (gradient (D.w η) y) := rfl
  rw [hfl, h, real_inner_smul_left,
    real_inner_comm (gradient Ψ (gradient (D.w η) z)) (gradient (D.w η) z)]
  ring

/-! ### The integrated inequality at level `η > 0` -/

/-- **The integrated inequality for `U_η = e^{-w_η}`**: if on `supp ψ ⊆ K_t` the differential
inequality `div ∇Ψ(∇w_η) ≤ κ w_η + c + B(∇w_η)` holds, then for `ψ ≥ 0` of class `C¹` with
compact support in `K_t`,
`∫ (2 regKin + κ regEnt) ψ ≤ c ∫ regMass ψ + ∫ ⟪G_η, ∇ψ⟫`. -/
theorem integral_regDensity_le (hΨ : IsRegProfile Ψ)
    (hc₀ : ContDiffOn ℝ 1 (gradient D.v₀) D.K₀) (hc₁ : ContDiffOn ℝ 1 (gradient D.v₁) D.K₁)
    {η : ℝ} (hη : 0 < η) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψK : tsupport ψ ⊆ D.Kt) {c : ℝ}
    (hZ : ∀ z ∈ tsupport ψ,
      divergence (fun y => gradient Ψ (gradient (D.w η) y)) z ≤
        κ * D.w η z + c +
          2 * (⟪gradient Ψ (gradient (D.w η) z), gradient (D.w η) z⟫ -
            Ψ (gradient (D.w η) z))) :
    ∫ z, (2 * regKin Ψ D η z + κ * regEnt D η z) * ψ z ≤
      c * (∫ z, regMass D η z * ψ z) + ∫ z, ⟪regFlux Ψ D η z, gradient ψ z⟫ := by
  have hcdall : ∀ z ∈ D.Kt, ContDiffAt ℝ 1 (gradient (D.w η)) z := fun z hz =>
    contDiffAt_gradient_w_reg D hc₀ hc₁ hη hz
  have hψc : Continuous ψ := hψ.continuous
  have hψ0' : ∀ y ∉ tsupport ψ, ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hgψ0 : ∀ y ∉ tsupport ψ, gradient ψ y = 0 := fun y hy => by
    have h : fderiv ℝ ψ y = 0 := by
      by_contra h
      exact hy (support_fderiv_subset ℝ (Function.mem_support.2 h))
    simp [gradient, h]
  have hgψc : Continuous (gradient ψ) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hψ.continuous_fderiv one_ne_zero)
  have hwc : ContinuousOn (D.w η) D.Kt := D.continuousOn_w hη.le
  have hgwc : ContinuousOn (gradient (D.w η)) D.Kt := D.continuousOn_gradient_w_fixed hη.le
  -- `G_η` is `C¹` on `K_t`
  have hW : ContDiffOn ℝ 1 (regFlux Ψ D η) D.Kt := by
    intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    have hwy : ContDiffAt ℝ 1 (D.w η) y :=
      (D.contDiffOn_w hη.le).contDiffAt (D.isOpen_Kt.mem_nhds hy)
    have h1 : ContDiffAt ℝ 1 (fun z => Real.exp (-(2 * D.w η z))) y := by
      exact Real.contDiff_exp.contDiffAt.comp y ((hwy.const_smul (2 : ℝ)).neg)
    have h2 : ContDiffAt ℝ 1 (fun z => gradient Ψ (gradient (D.w η) z)) y :=
      ContDiffAt.comp (g := gradient Ψ) y
        (hΨ.contDiff_gradient.contDiffAt.of_le (by exact_mod_cast le_top)) (hcdall y hy)
    exact h1.smul h2
  have hdivc : ContinuousOn (divergence (regFlux Ψ D η)) D.Kt := by
    have hf := hW.continuousOn_fderiv_of_isOpen D.isOpen_Kt le_rfl
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact continuousOn_const.inner (hf.clm_apply continuousOn_const)
  -- integrability
  have hkin : ContinuousOn (fun z => 2 * regKin Ψ D η z + κ * regEnt D η z) D.Kt := by
    refine ContinuousOn.add (continuousOn_const.mul ?_) (continuousOn_const.mul ?_)
    · exact ((continuousOn_const.mul hwc).neg.rexp).mul
        (hΨ.contDiff.continuous.comp_continuousOn hgwc)
    · exact hwc.neg.mul ((continuousOn_const.mul hwc).neg.rexp)
  have hmassc : ContinuousOn (regMass D η) D.Kt := (continuousOn_const.mul hwc).neg.rexp
  have hint1 : Integrable fun z => (2 * regKin Ψ D η z + κ * regEnt D η z) * ψ z :=
    (continuous_mul_of_continuousOn D.isOpen_Kt hkin hψc (isClosed_tsupport ψ) hψK
      hψ0').integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun y hy => by rw [hψ0' y hy, mul_zero])
  have hint2 : Integrable fun z => regMass D η z * ψ z :=
    (continuous_mul_of_continuousOn D.isOpen_Kt hmassc hψc (isClosed_tsupport ψ) hψK
      hψ0').integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun y hy => by rw [hψ0' y hy, mul_zero])
  have hint3 : Integrable fun z => ψ z * divergence (regFlux Ψ D η) z :=
    ((continuous_mul_of_continuousOn D.isOpen_Kt hdivc hψc (isClosed_tsupport ψ) hψK
      hψ0').integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside hψs fun y hy => by
        rw [hψ0' y hy, mul_zero])).congr (Eventually.of_forall fun y => mul_comm _ _)
  have hIBP : ∫ z, ⟪regFlux Ψ D η z, gradient ψ z⟫ =
      -∫ z, ψ z * divergence (regFlux Ψ D η) z :=
    integral_inner_gradient_eq_neg_integral_divergence D.isOpen_Kt hW hψ hψs hψK
  have hint2' : Integrable fun z => c * (regMass D η z * ψ z) := hint2.const_mul c
  have hint3' : Integrable fun z => -(ψ z * divergence (regFlux Ψ D η) z) := hint3.neg
  have hsplit : (∫ z, (c * (regMass D η z * ψ z) +
        -(ψ z * divergence (regFlux Ψ D η) z))) =
      c * (∫ z, regMass D η z * ψ z) + ∫ z, ⟪regFlux Ψ D η z, gradient ψ z⟫ := by
    rw [integral_add hint2' hint3', integral_const_mul, integral_neg, ← hIBP]
  rw [← hsplit]
  refine integral_mono hint1 (hint2'.add hint3') fun z => ?_
  by_cases hz : z ∈ tsupport ψ
  · have hzK := hψK hz
    have hdiv := divergence_regFlux hΨ hη.le hzK (hcdall z hzK)
    have hE : 0 < Real.exp (-(2 * D.w η z)) := Real.exp_pos _
    have hle := hZ z hz
    have key : 2 * regKin Ψ D η z + κ * regEnt D η z ≤
        c * regMass D η z + -divergence (regFlux Ψ D η) z := by
      rw [hdiv]
      have := mul_le_mul_of_nonneg_left hle hE.le
      simp only [regKin, regEnt, regMass]
      nlinarith [this]
    have := mul_le_mul_of_nonneg_right key (hψ0 z)
    show (2 * regKin Ψ D η z + κ * regEnt D η z) * ψ z ≤
      c * (regMass D η z * ψ z) + -(ψ z * divergence (regFlux Ψ D η) z)
    nlinarith [this]
  · show (2 * regKin Ψ D η z + κ * regEnt D η z) * ψ z ≤
      c * (regMass D η z * ψ z) + -(ψ z * divergence (regFlux Ψ D η) z)
    rw [hψ0' z hz]
    simp

/-! ### Continuity of the three integrands -/

theorem continuousOn_regKin_add (hΨ : IsRegProfile Ψ) {η : ℝ} (hη : 0 ≤ η) :
    ContinuousOn (fun z => 2 * regKin Ψ D η z + κ * regEnt D η z) D.Kt := by
  have hwc : ContinuousOn (D.w η) D.Kt := D.continuousOn_w hη
  have hgwc : ContinuousOn (gradient (D.w η)) D.Kt := D.continuousOn_gradient_w_fixed hη
  refine ContinuousOn.add (continuousOn_const.mul ?_) (continuousOn_const.mul ?_)
  · exact ((continuousOn_const.mul hwc).neg.rexp).mul
      (hΨ.contDiff.continuous.comp_continuousOn hgwc)
  · exact hwc.neg.mul ((continuousOn_const.mul hwc).neg.rexp)

theorem continuousOn_regMass (D : InfConvData d) {η : ℝ} (hη : 0 ≤ η) :
    ContinuousOn (regMass D η) D.Kt := (continuousOn_const.mul (D.continuousOn_w hη)).neg.rexp

theorem continuousOn_regFlux (hΨ : IsRegProfile Ψ) {η : ℝ} (hη : 0 ≤ η) :
    ContinuousOn (regFlux Ψ D η) D.Kt :=
  ((continuousOn_const.mul (D.continuousOn_w hη)).neg.rexp).smul
    (hΨ.contDiff_gradient.continuous.comp_continuousOn (D.continuousOn_gradient_w_fixed hη))

/-! ### The limit `η ↓ 0` -/

/-- **The weak inequality for `U = e^{-w}`** (`REGULARIZED_ROUTE.md`, Revision 2, Wang–Xia
step 2): for every nonnegative `C¹` test function `ψ` with compact support in `K_t`,
`∫ (2 U²Ψ(∇w) + κ U² log U) ψ ≤ ((1-t)Λ₀ + tΛ₁) ∫ U² ψ + ∫ ⟪U² ∇Ψ(∇w), ∇ψ⟫`.
Obtained from `integral_regDensity_le` at level `η > 0` with constant
`(1-t)Λ₀ + tΛ₁ + ε`, by dominated convergence as `η ↓ 0` and then `ε ↓ 0`. -/
theorem integral_regDensity_le_zero (D : InfConvData d) (hΨ : IsRegProfile Ψ) (hκ : 0 ≤ κ)
    (hc₀ : ContDiffOn ℝ 1 (gradient D.v₀) D.K₀) (hc₁ : ContDiffOn ℝ 1 (gradient D.v₁) D.K₁)
    {lam₀ lam₁ : ℝ}
    (he₀ : ∀ x ∈ D.K₀, divergence (fun y => gradient Ψ (gradient D.v₀ y)) x =
      κ * D.v₀ x + lam₀ +
        2 * (⟪gradient Ψ (gradient D.v₀ x), gradient D.v₀ x⟫ - Ψ (gradient D.v₀ x)))
    (he₁ : ∀ x ∈ D.K₁, divergence (fun y => gradient Ψ (gradient D.v₁ y)) x =
      κ * D.v₁ x + lam₁ +
        2 * (⟪gradient Ψ (gradient D.v₁ x), gradient D.v₁ x⟫ - Ψ (gradient D.v₁ x)))
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψK : tsupport ψ ⊆ D.Kt) :
    ∫ z, (2 * regKin Ψ D 0 z + κ * regEnt D 0 z) * ψ z ≤
      ((1 - D.t) * lam₀ + D.t * lam₁) * (∫ z, regMass D 0 z * ψ z) +
        ∫ z, ⟪regFlux Ψ D 0 z, gradient ψ z⟫ := by
  have hZc : IsCompact (tsupport ψ) := hψs
  have hψc : Continuous ψ := hψ.continuous
  have hψ0' : ∀ y ∉ tsupport ψ, ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hgψ0 : ∀ y ∉ tsupport ψ, gradient ψ y = 0 := fun y hy => by
    have h : fderiv ℝ ψ y = 0 := by
      by_contra h
      exact hy (support_fderiv_subset ℝ (Function.mem_support.2 h))
    simp [gradient, h]
  have hgψc : Continuous (gradient ψ) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hψ.continuous_fderiv one_ne_zero)
  obtain ⟨R₀, hR₀⟩ := D.h₀.isBounded.subset_closedBall 0
  obtain ⟨R₁, hR₁⟩ := D.h₁.isBounded.subset_closedBall 0
  have hR₀' : D.K₀ ⊆ Metric.closedBall 0 (max R₀ R₁) :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR₁' : D.K₁ ⊆ Metric.closedBall 0 (max R₀ R₁) :=
    hR₁.trans (Metric.closedBall_subset_closedBall (le_max_right _ _))
  -- step 1: the integrated inequality for small `η > 0`
  have hstep : ∀ ε > 0, ∀ᶠ η in 𝓝[>] (0 : ℝ),
      ∫ z, (2 * regKin Ψ D η z + κ * regEnt D η z) * ψ z ≤
        ((1 - D.t) * lam₀ + D.t * lam₁ + ε) * (∫ z, regMass D η z * ψ z) +
          ∫ z, ⟪regFlux Ψ D η z, gradient ψ z⟫ := by
    intro ε hε
    filter_upwards [self_mem_nhdsWithin, eventually_divergence_gradPsi_gradient_w_le D hΨ hκ
      hc₀ hc₁ he₀ he₁ hZc hψK hR₀' hR₁' hε] with η hη hev
    have hη0 : 0 < η := Set.mem_Ioi.1 hη
    refine integral_regDensity_le hΨ hc₀ hc₁ hη0 hψ hψs hψ0 hψK fun z hz => ?_
    have := hev z hz
    linarith
  -- uniform bounds on `supp ψ` for `0 ≤ η ≤ 1`
  obtain ⟨mlb, hmlb⟩ := D.exists_forall_le_w
  obtain ⟨Cw, hCw0, hCw⟩ := D.exists_w_le_w_zero_add
  obtain ⟨Bw, hBw⟩ := hZc.exists_bound_of_continuousOn ((D.continuousOn_w le_rfl).mono hψK)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hZc).exists_bound_of_continuousOn
    (D.continuousOn_gradient_w.mono (prod_mono Icc_subset_Ici_self hψK))
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hM' : ∀ η ∈ Icc (0 : ℝ) 1, ∀ z ∈ tsupport ψ, ‖gradient (D.w η) z‖ ≤ M' :=
    fun η hη z hz => le_trans (hM (η, z) ⟨hη, hz⟩) (le_max_left _ _)
  obtain ⟨BΨ, hBΨ⟩ := (isCompact_closedBall (0 : Euc d) M').exists_bound_of_continuousOn
    hΨ.contDiff.continuous.continuousOn
  set BΨ' : ℝ := max BΨ 0 with hBΨ'def
  have hBΨ'0 : 0 ≤ BΨ' := le_max_right _ _
  have hBΨ' : ∀ q : Euc d, ‖q‖ ≤ M' → |Ψ q| ≤ BΨ' := fun q hq => by
    have := hBΨ q (mem_closedBall_zero_iff.2 hq)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨CL, hCL0, -, hCLg⟩ := hΨ.exists_lipschitz_gradient
  set W : ℝ := |mlb| + |Bw| + |Cw| with hWdef
  have hW0 : 0 ≤ W := by positivity
  have hwbdd : ∀ η ∈ Icc (0 : ℝ) 1, ∀ z ∈ tsupport ψ, |D.w η z| ≤ W := by
    intro η hη z hz
    have h1 : mlb ≤ D.w η z := hmlb η hη.1 z (hψK hz)
    have h2 : D.w η z ≤ D.w 0 z + η * Cw := hCw η hη.1 z (hψK hz)
    have h3 : |D.w 0 z| ≤ Bw := by
      have := hBw z hz; rwa [Real.norm_eq_abs] at this
    have h4 : η * Cw ≤ Cw := by nlinarith [hη.1, hη.2, hCw0]
    have h5 : D.w 0 z ≤ |Bw| := le_trans (le_abs_self _) (le_trans h3 (le_abs_self _))
    have h6 : -|mlb| ≤ mlb := neg_abs_le _
    have h7 : Cw ≤ |Cw| := le_abs_self _
    have h8 : (0:ℝ) ≤ |mlb| := abs_nonneg _
    have h9 : (0:ℝ) ≤ |Bw| := abs_nonneg _
    have h10 : (0:ℝ) ≤ |Cw| := abs_nonneg _
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hmass_le : ∀ η ∈ Icc (0 : ℝ) 1, ∀ z ∈ tsupport ψ,
      regMass D η z ≤ Real.exp (2 * W) := by
    intro η hη z hz
    have := hwbdd η hη z hz
    rw [abs_le] at this
    exact Real.exp_le_exp.2 (by linarith [this.1])
  have hE0 : (0 : ℝ) < Real.exp (2 * W) := Real.exp_pos _
  set Cdom : ℝ := Real.exp (2 * W) * (2 * BΨ' + κ * W) with hCdomdef
  have hCdom0 : 0 ≤ Cdom := by
    have : (0:ℝ) ≤ 2 * BΨ' + κ * W := by positivity
    positivity
  set CF : ℝ := Real.exp (2 * W) * (CL * M') with hCFdef
  have hCF0 : 0 ≤ CF := by positivity
  -- pointwise convergence
  have hwlim : ∀ z ∈ D.Kt, Tendsto (fun η => D.w η z) (𝓝[>] 0) (𝓝 (D.w 0 z)) := fun z hz => by
    have hup : Tendsto (fun η : ℝ => D.w 0 z + η * Cw) (𝓝[>] 0) (𝓝 (D.w 0 z)) := by
      have h : Continuous fun η : ℝ => D.w 0 z + η * Cw := by fun_prop
      have h' := h.tendsto 0
      simp only [zero_mul, add_zero] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact D.w_zero_le_w (Set.mem_Ioi.1 hη).le hz
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact hCw η (Set.mem_Ioi.1 hη).le z hz
  have hglim : ∀ z ∈ tsupport ψ,
      Tendsto (fun η => gradient (D.w η) z) (𝓝[>] 0) (𝓝 (gradient (D.w 0) z)) := fun z hz =>
    (D.tendstoUniformlyOn_gradient_w_pos hZc hψK).tendsto_at hz
  -- step 2: the three limits
  have hlimA : Tendsto (fun η => ∫ z, (2 * regKin Ψ D η z + κ * regEnt D η z) * ψ z)
      (𝓝[>] 0) (𝓝 (∫ z, (2 * regKin Ψ D 0 z + κ * regEnt D 0 z) * ψ z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => Cdom * ψ z) ?_ ?_
      ((hψc.integrable_of_hasCompactSupport hψs).const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (continuous_mul_of_continuousOn D.isOpen_Kt
        (continuousOn_regKin_add hΨ (Set.mem_Ioi.1 hη).le) hψc (isClosed_tsupport ψ) hψK
        hψ0').aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη hη1
      have hηI : η ∈ Icc (0 : ℝ) 1 := ⟨(Set.mem_Ioi.1 hη).le, hη1.2.le⟩
      refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ tsupport ψ
      · have hb1 : |Ψ (gradient (D.w η) z)| ≤ BΨ' := hBΨ' _ (hM' η hηI z hz)
        have hb2 : regMass D η z ≤ Real.exp (2 * W) := hmass_le η hηI z hz
        have hb3 : |D.w η z| ≤ W := hwbdd η hηI z hz
        have hb4 : (0:ℝ) < regMass D η z := regMass_pos D η z
        have hkey : |2 * regKin Ψ D η z + κ * regEnt D η z| ≤ Cdom := by
          have e1 : |regKin Ψ D η z| ≤ Real.exp (2 * W) * BΨ' := by
            rw [regKin, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul hb2 hb1 (abs_nonneg _) hE0.le
          have hb2' : Real.exp (-(2 * D.w η z)) ≤ Real.exp (2 * W) := hb2
          have e2 : |regEnt D η z| ≤ W * Real.exp (2 * W) := by
            rw [regEnt, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul hb3 hb2' (Real.exp_pos _).le hW0
          calc |2 * regKin Ψ D η z + κ * regEnt D η z|
              ≤ |2 * regKin Ψ D η z| + |κ * regEnt D η z| := abs_add_le _ _
            _ = 2 * |regKin Ψ D η z| + κ * |regEnt D η z| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
                  abs_of_nonneg hκ]
            _ ≤ 2 * (Real.exp (2 * W) * BΨ') + κ * (W * Real.exp (2 * W)) := by
                gcongr
            _ = Cdom := by rw [hCdomdef]; ring
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 z)]
        exact mul_le_mul_of_nonneg_right hkey (hψ0 z)
      · rw [hψ0' z hz, mul_zero, mul_zero, norm_zero]
    · refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ tsupport ψ
      · have hzK := hψK hz
        have hw := hwlim z hzK
        have hg := hglim z hz
        have hmasslim : Tendsto (fun η => Real.exp (-(2 * D.w η z))) (𝓝[>] 0)
            (𝓝 (Real.exp (-(2 * D.w 0 z)))) :=
          (Real.continuous_exp.tendsto _).comp ((hw.const_mul 2).neg)
        have hkinlim : Tendsto (fun η => regKin Ψ D η z) (𝓝[>] 0) (𝓝 (regKin Ψ D 0 z)) :=
          hmasslim.mul ((hΨ.contDiff.continuous.tendsto _).comp hg)
        have hentlim : Tendsto (fun η => regEnt D η z) (𝓝[>] 0) (𝓝 (regEnt D 0 z)) :=
          (hw.neg).mul hmasslim
        exact ((hkinlim.const_mul 2).add (hentlim.const_mul κ)).mul_const (ψ z)
      · simp only [hψ0' z hz, mul_zero]
        exact tendsto_const_nhds
  have hlimB : Tendsto (fun η => ∫ z, regMass D η z * ψ z) (𝓝[>] 0)
      (𝓝 (∫ z, regMass D 0 z * ψ z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => Real.exp (2 * W) * ψ z) ?_ ?_
      ((hψc.integrable_of_hasCompactSupport hψs).const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (continuous_mul_of_continuousOn D.isOpen_Kt
        (continuousOn_regMass D (Set.mem_Ioi.1 hη).le) hψc (isClosed_tsupport ψ) hψK
        hψ0').aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη hη1
      have hηI : η ∈ Icc (0 : ℝ) 1 := ⟨(Set.mem_Ioi.1 hη).le, hη1.2.le⟩
      refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ tsupport ψ
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (regMass_pos D η z),
          abs_of_nonneg (hψ0 z)]
        exact mul_le_mul_of_nonneg_right (hmass_le η hηI z hz) (hψ0 z)
      · rw [hψ0' z hz, mul_zero, mul_zero, norm_zero]
    · refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ tsupport ψ
      · exact (((Real.continuous_exp.tendsto _).comp
          (((hwlim z (hψK hz)).const_mul 2).neg))).mul_const (ψ z)
      · simp only [hψ0' z hz, mul_zero]
        exact tendsto_const_nhds
  have hlimC : Tendsto (fun η => ∫ z, ⟪regFlux Ψ D η z, gradient ψ z⟫) (𝓝[>] 0)
      (𝓝 (∫ z, ⟪regFlux Ψ D 0 z, gradient ψ z⟫)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => CF * ‖gradient ψ z‖) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (continuous_inner_of_continuousOn D.isOpen_Kt
        (continuousOn_regFlux hΨ (Set.mem_Ioi.1 hη).le) hgψc (isClosed_tsupport ψ) hψK
        hgψ0).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη hη1
      have hηI : η ∈ Icc (0 : ℝ) 1 := ⟨(Set.mem_Ioi.1 hη).le, hη1.2.le⟩
      refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ tsupport ψ
      · have hfl : ‖regFlux Ψ D η z‖ ≤ CF := by
          rw [regFlux, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, hCFdef]
          refine mul_le_mul (hmass_le η hηI z hz) ?_ (norm_nonneg _) hE0.le
          exact (hCLg _).trans (mul_le_mul_of_nonneg_left (hM' η hηI z hz) hCL0)
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right hfl (norm_nonneg _))
      · rw [hgψ0 z hz, inner_zero_right, norm_zero, norm_zero, mul_zero]
    · exact (hgψc.norm.integrable_of_hasCompactSupport
        (hasCompactSupport_of_zero_outside hZc fun z hz => by
          rw [hgψ0 z hz, norm_zero])).const_mul _
    · refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ tsupport ψ
      · have hzK := hψK hz
        have hmasslim : Tendsto (fun η => Real.exp (-(2 * D.w η z))) (𝓝[>] 0)
            (𝓝 (Real.exp (-(2 * D.w 0 z)))) :=
          (Real.continuous_exp.tendsto _).comp (((hwlim z hzK).const_mul 2).neg)
        have hv : Tendsto (fun η => regFlux Ψ D η z) (𝓝[>] 0) (𝓝 (regFlux Ψ D 0 z)) :=
          hmasslim.smul ((hΨ.contDiff_gradient.continuous.tendsto _).comp (hglim z hz))
        exact hv.inner tendsto_const_nhds
      · simp only [hgψ0 z hz, inner_zero_right]
        exact tendsto_const_nhds
  -- step 3: `η ↓ 0`, then `ε ↓ 0`
  have hbound : ∀ ε > 0,
      ∫ z, (2 * regKin Ψ D 0 z + κ * regEnt D 0 z) * ψ z ≤
        ((1 - D.t) * lam₀ + D.t * lam₁ + ε) * (∫ z, regMass D 0 z * ψ z) +
          ∫ z, ⟪regFlux Ψ D 0 z, gradient ψ z⟫ :=
    fun ε hε => le_of_tendsto_of_tendsto hlimA ((hlimB.const_mul _).add hlimC) (hstep ε hε)
  have hlim : Tendsto (fun ε : ℝ => ((1 - D.t) * lam₀ + D.t * lam₁ + ε) *
      (∫ z, regMass D 0 z * ψ z) + ∫ z, ⟪regFlux Ψ D 0 z, gradient ψ z⟫) (𝓝[>] 0)
      (𝓝 (((1 - D.t) * lam₀ + D.t * lam₁) * (∫ z, regMass D 0 z * ψ z) +
        ∫ z, ⟪regFlux Ψ D 0 z, gradient ψ z⟫)) := by
    have h : Continuous fun ε : ℝ => ((1 - D.t) * lam₀ + D.t * lam₁ + ε) *
        (∫ z, regMass D 0 z * ψ z) + ∫ z, ⟪regFlux Ψ D 0 z, gradient ψ z⟫ := by fun_prop
    have h' := h.tendsto 0
    simp only [add_zero] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε (Set.mem_Ioi.1 hε)

end Komlos.Literature.Regularized
