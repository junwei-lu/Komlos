import Komlos.Literature.Regularized.AssemblyCutoff

/-!
# Wang–Xia for the regularized route: the assembly (lane `L5`)

The final step of lane `L5` of `REGULARIZED_ROUTE.md` (Revision 2).  Given the energy
inequality `regU_energy_le`

`2 ∫ U² Ψ(∇U/U) + κ ∫ U² log U ≤ 2((1-t) m(K₀) + t m(K₁)) ∫ U²`,

we show that `Û = U / ‖U‖₂` is an admissible competitor on `K_t` (`MemW0 2 K_t U` is produced
by the same integrability that the inequality delivers, via the `C¹` truncations
`θ_s ∘ U`), compute

`regEnergy(Û) = ‖U‖₂⁻² (∫ U² Ψ(∇U/U) + (κ/2) ∫ U² log U) - (κ/4) log ‖U‖₂²
              ≤ (1-t) m(K₀) + t m(K₁) - (κ/4) log ∫U²`,

and finish with **Prékopa–Leindler**, `∫ U² ≥ 1` (`one_le_integral_regU_sq`), which makes the
logarithmic term nonpositive.  The constant of `exists_regMin_convexity_const` is therefore
`C = 0`.

## Main results

* `hasWeakGradient_regU`, `memW0_regU`: `U ∈ W₀^{1,2}(K_t)`;
* `exists_regMin_convexity_const`: the frozen lane statement of `L5` (formerly a named
  `sorry` in `Interface.lean`), proved with `C = 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### `U ∈ W₀^{1,2}(K_t)` -/

theorem integrable_norm_gradient_regU (E : InfConvData d)
    (hgi : Integrable fun z => ‖gradient (regU E) z‖ ^ 2) :
    Integrable fun z => ‖gradient (regU E) z‖ := by
  have hind : Integrable (E.Kt.indicator fun _ => (1 : ℝ)) := by
    rw [integrable_indicator_iff E.isOpen_Kt.measurableSet]
    exact integrableOn_const (C := (1 : ℝ)) E.isBounded_Kt.measure_lt_top.ne
  have hsum : Integrable fun z =>
      E.Kt.indicator (fun _ => (1 : ℝ)) z + ‖gradient (regU E) z‖ ^ 2 := hind.add hgi
  refine Integrable.mono' (hsum.const_mul (1 / 2)) ?_ (Eventually.of_forall fun z => ?_)
  · exact (measurable_gradient' (regU E)).norm.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    by_cases hz : z ∈ E.Kt
    · rw [indicator_of_mem hz]
      nlinarith [sq_nonneg (‖gradient (regU E) z‖ - 1), norm_nonneg (gradient (regU E) z)]
    · rw [gradient_regU_of_notMem hz, indicator_of_notMem hz, norm_zero]
      norm_num

/-- **`U` has a weak gradient, namely its classical gradient.**  The `C¹` truncations
`θ_s ∘ U` (compactly supported in `K_t` since `U → 0` at `∂K_t`) satisfy the
integration-by-parts identity; `θ_s ∘ U → U` uniformly and
`∇(θ_s ∘ U) = Θ'(U/s) ∇U → ∇U` dominated by `C ‖∇U‖ ∈ L¹`. -/
theorem hasWeakGradient_regU (E : InfConvData d)
    (hgi : Integrable fun z => ‖gradient (regU E) z‖ ^ 2) :
    HasWeakGradient (regU E) (gradient (regU E)) := by
  have hKt : IsGoodConvex E.Kt := ⟨E.nonempty_Kt, E.isBounded_Kt, E.isOpen_Kt, E.convex_Kt⟩
  have hUc : Continuous (regU E) := continuous_regU E
  have hU0 : ∀ z, 0 ≤ regU E z := regU_nonneg E
  have hsupp : Function.support (regU E) ⊆ E.Kt := support_regU E
  have hC1 : ContDiffOn ℝ 1 (regU E) E.Kt := contDiffOn_regU E
  have hgint : Integrable fun z => ‖gradient (regU E) z‖ := integrable_norm_gradient_regU E hgi
  have hgv : Integrable (gradient (regU E)) :=
    Integrable.mono' hgint (measurable_gradient' (regU E)).aestronglyMeasurable
      (Eventually.of_forall fun z => le_rfl)
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_trunc'
  refine ⟨hUc.locallyIntegrable, hgv.locallyIntegrable, fun ψ hψ hψs v => ?_⟩
  -- notation
  set sm : ℕ → ℝ := fun n => 1 / (n + 1) with hsmdef
  have hsm0 : ∀ n, 0 < sm n := fun n => by rw [hsmdef]; positivity
  have hsmlim : Tendsto sm atTop (𝓝[>] (0 : ℝ)) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h0 : Tendsto sm atTop (𝓝 (0 : ℝ)) := by rw [hsmdef]; exact h
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within sm h0
      (Eventually.of_forall fun n => hsm0 n)
  -- the identity for the truncations
  have hid : ∀ n, ∫ x, truncS (sm n) (regU E x) * fderiv ℝ ψ x v =
      -∫ x, ⟪gradient (fun y => truncS (sm n) (regU E y)) x, v⟫ * ψ x := fun n =>
    (hasWeakGradient_gradient (truncU_contDiff hKt hUc hsupp hC1 (hsm0 n))
      (truncU_hasCompactSupport hKt hUc hsupp (hsm0 n))).integral_mul_fderiv ψ hψ hψs v
  have hgradtr : ∀ n x, gradient (fun y => truncS (sm n) (regU E y)) x =
      trunc' (regU E x / sm n) • gradient (regU E) x := fun n x =>
    truncU_gradient hKt hUc hU0 hsupp hC1 (hsm0 n) x
  -- bounds
  have hψc : Continuous ψ := hψ.continuous
  have hLc : Continuous fun x => fderiv ℝ ψ x v :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hLs : HasCompactSupport fun x => fderiv ℝ ψ x v :=
    (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
  have hLdom : Integrable fun x => regU E x * |fderiv ℝ ψ x v| :=
    (hUc.mul hLc.abs).integrable_of_hasCompactSupport
      ((hLs.comp_left (g := fun r : ℝ => |r|) (by simp)).mul_left)
  obtain ⟨Bψ, hBψ⟩ := exists_bound_of_zero_outside (S := tsupport ψ) hψs
    hψc.continuousOn (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  -- limit of the left-hand sides
  have hlimL : Tendsto (fun n => ∫ x, truncS (sm n) (regU E x) * fderiv ℝ ψ x v)
      atTop (𝓝 (∫ x, regU E x * fderiv ℝ ψ x v)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => regU E x * |fderiv ℝ ψ x v|) (fun n => ?_) hLdom (fun n => ?_) ?_
    · exact (((contDiff_truncS (n := 1) (sm n)).continuous.comp hUc).mul
        hLc).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (truncS_nonneg (hsm0 n) (hU0 x))]
      exact mul_le_mul_of_nonneg_right (truncS_le (hsm0 n) (hU0 x)) (abs_nonneg _)
    · refine Eventually.of_forall fun x => ?_
      exact ((tendsto_truncS (hU0 x)).comp hsmlim).mul_const _
  -- limit of the right-hand sides
  have hRdom : Integrable fun x => C₁ * ‖v‖ * max Bψ 0 * ‖gradient (regU E) x‖ :=
    hgint.const_mul _
  have hlimR : Tendsto
      (fun n => ∫ x, ⟪gradient (fun y => truncS (sm n) (regU E y)) x, v⟫ * ψ x)
      atTop (𝓝 (∫ x, ⟪gradient (regU E) x, v⟫ * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => C₁ * ‖v‖ * max Bψ 0 * ‖gradient (regU E) x‖) (fun n => ?_) hRdom
      (fun n => ?_) ?_
    · refine (Measurable.mul ?_ hψc.measurable).aestronglyMeasurable
      exact ((measurable_gradient' _).inner measurable_const)
    · refine Eventually.of_forall fun x => ?_
      rw [hgradtr n x, real_inner_smul_left, Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |⟪gradient (regU E) x, v⟫| ≤ ‖gradient (regU E) x‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      have h2 : |ψ x| ≤ max Bψ 0 := by
        have := hBψ x
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      have h3 : |trunc' (regU E x / sm n)| ≤ C₁ := hC₁ _
      have h4 : (0 : ℝ) ≤ max Bψ 0 := le_max_right _ _
      have h5 : (0 : ℝ) ≤ ‖gradient (regU E) x‖ := norm_nonneg _
      have h6 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
      have e1 : |trunc' (regU E x / sm n)| * |⟪gradient (regU E) x, v⟫| * |ψ x| ≤
          C₁ * (‖gradient (regU E) x‖ * ‖v‖) * max Bψ 0 := by
        refine mul_le_mul (mul_le_mul h3 h1 (abs_nonneg _) hC₁0) h2 (abs_nonneg _) ?_
        positivity
      have e2 : C₁ * (‖gradient (regU E) x‖ * ‖v‖) * max Bψ 0
          = C₁ * ‖v‖ * max Bψ 0 * ‖gradient (regU E) x‖ := by ring
      exact e1.trans (le_of_eq e2)
    · refine Eventually.of_forall fun x => ?_
      simp only [hgradtr, real_inner_smul_left]
      rcases (hU0 x).eq_or_lt with h | h
      · have hgz : gradient (regU E) x = 0 := gradient_eq_zero_of_eq_zero hU0 h.symm
        rw [hgz]
        simp
      · have ht := ((tendsto_trunc'_div h).comp hsmlim).mul_const
          (⟪gradient (regU E) x, v⟫ * ψ x)
        rw [one_mul] at ht
        exact ht.congr fun n => (mul_assoc _ _ _).symm
  -- conclusion
  have hlimL' : Tendsto
      (fun n => -∫ x, ⟪gradient (fun y => truncS (sm n) (regU E y)) x, v⟫ * ψ x) atTop
      (𝓝 (∫ x, regU E x * fderiv ℝ ψ x v)) := hlimL.congr fun n => hid n
  exact tendsto_nhds_unique hlimL' hlimR.neg

theorem memW0_regU (E : InfConvData d)
    (hgi : Integrable fun z => ‖gradient (regU E) z‖ ^ 2) : MemW0 2 E.Kt (regU E) where
  memLp := (continuous_regU E).memLp_of_hasCompactSupport (hasCompactSupport_regU E)
  ae_eq_zero := Eventually.of_forall fun x hx => regU_of_notMem hx
  exists_weakGradient := by
    refine ⟨gradient (regU E), hasWeakGradient_regU E hgi, ?_⟩
    have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
    rw [h2]
    exact (memLp_two_iff_integrable_sq_norm
      (measurable_gradient' (regU E)).aestronglyMeasurable).2 hgi

/-! ### The main theorem -/

/-- **(L5, `reg/wangxia`)** Almost-convexity of `K ↦ regMin 2 κ Ψ K` along Minkowski
combinations.  This is the frozen lane statement `exists_regMin_convexity_const`, formerly a
named `sorry` of
`Komlos/Literature/Regularized/Interface.lean`, proved here with the **absolute constant
`C = 0`**: the Wang–Xia infimal convolution makes the affine term `κ v` pass through exactly,
and Prékopa–Leindler (`∫ U² ≥ 1`) makes the logarithmic term nonpositive, so no `O(κ)` error
is left over.

The chain is: `U = e^{-w}` with `w` the infimal convolution of `v_i = -log φ_i`; the
differential inequality `div ∇Ψ(∇w) ≤ κ w + 2((1-t)m₀ + t m₁) + B(∇w)`
(`eventually_divergence_gradPsi_gradient_w_le`); its weak form
(`integral_regDensity_le_zero`); testing with `χ_s ∘ U` and `s ↓ 0` (`regU_energy_le`):
`2 ∫ U²Ψ(∇U/U) + κ ∫ U² log U ≤ 2((1-t)m₀ + t m₁) ∫ U²`; normalization
`Û = U / ‖U‖₂`, which is admissible (`memW0_regU`), with
`regEnergy(Û) = ‖U‖₂⁻²(∫U²Ψ(∇U/U) + (κ/2)∫U² log U) + (κ/2) log ‖U‖₂⁻¹
 ≤ (1-t)m₀ + t m₁ - (κ/4) log ∫U² ≤ (1-t)m₀ + t m₁`. -/
theorem exists_regMin_convexity_const :
    ∃ C : ℝ, ∀ (κ : ℝ) (Ψ : Euc d → ℝ) (K₀ K₁ : Set (Euc d)) (t : ℝ),
      0 < κ → IsRegProfile Ψ → IsGoodConvex K₀ → IsGoodConvex K₁ → 0 < t → t < 1 →
      regMin 2 κ Ψ ((1 - t) • K₀ + t • K₁) ≤
        (1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁ + C * κ := by
  refine ⟨0, fun κ Ψ K₀ K₁ t hκ hΨ hK₀ hK₁ ht₀ ht₁ => ?_⟩
  obtain ⟨D₀⟩ := exists_regEigenData hκ hΨ hK₀
  obtain ⟨D₁⟩ := exists_regEigenData hκ hΨ hK₁
  have hKt : IsGoodConvex ((1 - t) • K₀ + t • K₁) := isGoodConvex_convexCombo hK₀ hK₁ ht₀ ht₁
  obtain ⟨Dt⟩ := exists_regEigenData hκ hΨ hKt
  set E := regInfConvData hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁ with hE
  have hK0e : E.K₀ = K₀ := rfl
  have hK1e : E.K₁ = K₁ := rfl
  have hv0e : E.v₀ = D₀.logFn := rfl
  have hv1e : E.v₁ = D₁.logFn := rfl
  have hte : E.t = t := rfl
  -- the hypotheses of the analytic core
  have hc₀ : ContDiffOn ℝ 1 (gradient E.v₀) E.K₀ := by
    rw [hv0e, hK0e]; exact D₀.contDiffOn_gradient_logFn hK₀
  have hc₁ : ContDiffOn ℝ 1 (gradient E.v₁) E.K₁ := by
    rw [hv1e, hK1e]; exact D₁.contDiffOn_gradient_logFn hK₁
  have he₀ : ∀ x ∈ E.K₀, divergence (fun y => gradient Ψ (gradient E.v₀ y)) x =
      κ * E.v₀ x + 2 * regMin 2 κ Ψ K₀ +
        2 * (⟪gradient Ψ (gradient E.v₀ x), gradient E.v₀ x⟫ - Ψ (gradient E.v₀ x)) := by
    rw [hv0e, hK0e]
    intro x hx
    exact D₀.equation x hx
  have he₁ : ∀ x ∈ E.K₁, divergence (fun y => gradient Ψ (gradient E.v₁ y)) x =
      κ * E.v₁ x + 2 * regMin 2 κ Ψ K₁ +
        2 * (⟪gradient Ψ (gradient E.v₁ x), gradient E.v₁ x⟫ - Ψ (gradient E.v₁ x)) := by
    rw [hv1e, hK1e]
    intro x hx
    exact D₁.equation x hx
  obtain ⟨hDi, hgi, hkey⟩ := regU_energy_le E hΨ hκ hc₀ hc₁ he₀ he₁
  rw [hte] at hkey
  -- the normalization
  set N : ℝ := ∫ z, regU E z ^ 2 with hNdef
  have hN1 : 1 ≤ N := one_le_integral_regU_sq hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  set α : ℝ := (Real.sqrt N)⁻¹ with hαdef
  have hα0 : 0 < α := inv_pos.2 hsqrt
  have hα2 : α ^ 2 * N = 1 := by
    rw [hαdef, inv_pow, Real.sq_sqrt hN0.le]
    field_simp
  have hlogα : Real.log α ≤ 0 := by
    rw [hαdef, Real.log_inv, neg_nonpos]
    exact Real.log_nonneg (by nlinarith [Real.sq_sqrt hN0.le, Real.sqrt_nonneg N])
  set Uh : Euc d → ℝ := α • regU E with hUhdef
  have hUhapp : ∀ x, Uh x = α * regU E x := fun x => rfl
  -- admissibility
  have hmemUh : MemW0 2 E.Kt Uh := (memW0_regU E hgi).smul α
  have hUh0 : ∀ x, 0 ≤ Uh x := fun x => by
    rw [hUhapp]; exact mul_nonneg hα0.le (regU_nonneg E x)
  have hUhz : ∀ x, x ∉ E.Kt → Uh x = 0 := fun x hx => by
    rw [hUhapp, regU_of_notMem hx, mul_zero]
  have hrpow2 : ((2 : ℝ)) = ((2 : ℕ) : ℝ) := by norm_num
  have hUhnorm : ∫ x, Uh x ^ (2 : ℝ) = 1 := by
    have hpt : ∀ x, Uh x ^ (2 : ℝ) = α ^ 2 * regU E x ^ 2 := by
      intro x
      rw [hUhapp, hrpow2, Real.rpow_natCast]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, ← hNdef]
    exact hα2
  have hadm : IsRegAdmissible 2 E.Kt Uh := ⟨hmemUh, hUh0, hUhz, hUhnorm⟩
  -- the energy of the normalized competitor
  have hwg : HasWeakGradient Uh (α • gradient (regU E)) :=
    (hasWeakGradient_regU E hgi).smul α
  have hdensae : (fun x => Korevaar.homogeneousDensity 2 Ψ (Uh x) (weakGrad Uh x))
      =ᵐ[volume] fun x => α ^ 2 * regDens Ψ E x := by
    filter_upwards [hwg.weakGrad_ae_eq] with x hx
    rw [hx]
    rcases eq_or_lt_of_le (regU_nonneg E x) with h | h
    · have h0 : regU E x = 0 := h.symm
      simp [Korevaar.homogeneousDensity, regDens, hUhapp, h0]
    · have hg : (Uh x)⁻¹ • (α • gradient (regU E)) x
          = (regU E x)⁻¹ • gradient (regU E) x := by
        show (α * regU E x)⁻¹ • (α • gradient (regU E) x) = (regU E x)⁻¹ • gradient (regU E) x
        rw [smul_smul]
        congr 1
        field_simp
      rw [Korevaar.homogeneousDensity, regDens, Korevaar.homogeneousDensity, hg, hUhapp,
        Real.mul_rpow hα0.le (regU_nonneg E x), hrpow2, Real.rpow_natCast, Real.rpow_natCast]
      ring
  have hentae : (fun x => Korevaar.entropyPotential 2 κ (Uh x))
      =ᵐ[volume] fun x => κ / 2 * α ^ 2 * (regU E x ^ 2 * Real.log (regU E x))
        + κ / 2 * α ^ 2 * Real.log α * regU E x ^ 2 := by
    refine Eventually.of_forall fun x => ?_
    rcases eq_or_lt_of_le (regU_nonneg E x) with h | h
    · have h0 : regU E x = 0 := h.symm
      simp [Korevaar.entropyPotential, hUhapp, h0]
    · show κ / 2 * (Uh x ^ (2 : ℝ) * Real.log (Uh x)) = _
      rw [hUhapp, Real.log_mul (ne_of_gt hα0) (ne_of_gt h),
        Real.mul_rpow hα0.le (regU_nonneg E x), hrpow2, Real.rpow_natCast, Real.rpow_natCast]
      ring
  have hIdens : (∫ x, Korevaar.homogeneousDensity 2 Ψ (Uh x) (weakGrad Uh x))
      = α ^ 2 * (∫ z, regDens Ψ E z) := by
    rw [integral_congr_ae hdensae, integral_const_mul]
  have hIent : (∫ x, Korevaar.entropyPotential 2 κ (Uh x))
      = κ / 2 * α ^ 2 * (∫ z, regU E z ^ 2 * Real.log (regU E z))
        + κ / 2 * α ^ 2 * Real.log α * N := by
    rw [integral_congr_ae hentae,
      integral_add ((integrable_regU_sq_log E).const_mul _)
        ((integrable_regU_sq E).const_mul _),
      integral_const_mul, integral_const_mul, ← hNdef]
  have hEnergy : regEnergy 2 κ Ψ Uh =
      α ^ 2 * ((∫ z, regDens Ψ E z) +
        κ / 2 * (∫ z, regU E z ^ 2 * Real.log (regU E z))) + κ / 2 * Real.log α := by
    rw [regEnergy, hIdens, hIent]
    have h : κ / 2 * α ^ 2 * Real.log α * N = κ / 2 * Real.log α * (α ^ 2 * N) := by ring
    rw [h, hα2]
    ring
  -- the bound
  have hα2pos : (0 : ℝ) < α ^ 2 := by positivity
  have hstep : (∫ z, regDens Ψ E z) + κ / 2 * (∫ z, regU E z ^ 2 * Real.log (regU E z)) ≤
      ((1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁) * N := by
    nlinarith [hkey]
  have hEbound : regEnergy 2 κ Ψ Uh ≤
      (1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁ := by
    rw [hEnergy]
    have h1 : α ^ 2 * ((∫ z, regDens Ψ E z) +
        κ / 2 * (∫ z, regU E z ^ 2 * Real.log (regU E z))) ≤
        α ^ 2 * (((1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁) * N) :=
      mul_le_mul_of_nonneg_left hstep hα2pos.le
    have h2 : α ^ 2 * (((1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁) * N)
        = (1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁ := by
      have : α ^ 2 * (((1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁) * N)
          = ((1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁) * (α ^ 2 * N) := by ring
      rw [this, hα2, mul_one]
    have h3 : κ / 2 * Real.log α ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hlogα
    linarith [h1, h2.le, h2.ge]
  -- conclusion
  have hadm' : IsRegAdmissible 2 ((1 - t) • K₀ + t • K₁) Uh := hadm
  have hmin : regMin 2 κ Ψ ((1 - t) • K₀ + t • K₁) ≤ regEnergy 2 κ Ψ Uh := by
    rw [regMin]
    exact ciInf_le Dt.isRegMinimizer.bddBelow ⟨Uh, hadm'⟩
  have : regMin 2 κ Ψ ((1 - t) • K₀ + t • K₁) ≤
      (1 - t) * regMin 2 κ Ψ K₀ + t * regMin 2 κ Ψ K₁ := hmin.trans hEbound
  linarith

end Komlos.Literature.Regularized
