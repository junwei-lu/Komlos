import Komlos.Literature.Regularized.AssemblyWeak

/-!
# Wang–Xia for the regularized route: testing with `(U - s)_+` (lane `L5`)

`REGULARIZED_ROUTE.md`, Revision 2, Wang–Xia step 3.  We test the weak inequality
`integral_regDensity_le_zero` with the smooth cutoff `χ_s ∘ U`, `χ_s = 0` on `(-∞, s]`,
`χ_s = 1` on `[2s, ∞)`, `0 ≤ χ_s ≤ 1`, `χ_s' ≥ 0`.  Two things happen:

* the boundary term has the good sign, since
  `⟪U² ∇Ψ(∇w), ∇(χ_s ∘ U)⟫ = -χ_s'(U) U³ ⟪∇Ψ(∇w), ∇w⟫ ≤ 0`
  (convexity of `Ψ` with `∇Ψ(0) = 0` gives `⟪∇Ψ q, q⟫ ≥ 0`), and **no global gradient bound
  is needed**: `χ_s ∘ U` is `C¹` with compact support in `K_t` because `U → 0` at `∂K_t`;
* letting `s ↓ 0` along `s = 1/(n+1)`, the nonnegative part
  `A = 2 U²(Ψ(∇w) - Ψ(0)) ≥ c ‖∇U‖² ≥ 0` is handled by monotone convergence, which produces
  its integrability *for free* out of the uniform bound, and the remaining terms by
  dominated convergence.

The outcome (`regU_energy_le`) is

`2 ∫ U² Ψ(∇U/U) + κ ∫ U² log U ≤ ((1-t)Λ₀ + tΛ₁) ∫ U²`,  `Λ_i = 2 m(K_i)`,

together with `∫ U² Ψ(∇U/U) < ∞` and `∫ ‖∇U‖² < ∞`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The smooth cutoff `χ_s` -/

/-- The smooth cutoff `χ_s(r) = T(r/s - 1)` with `T = Real.smoothTransition`: zero for
`r ≤ s`, one for `r ≥ 2s`, valued in `[0,1]` and nondecreasing. -/
noncomputable def cutoff (s r : ℝ) : ℝ := Real.smoothTransition (r / s - 1)

theorem contDiff_cutoff {n : ℕ∞} (s : ℝ) : ContDiff ℝ n (cutoff s) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.div_const s).sub contDiff_const)

theorem differentiable_cutoff (s : ℝ) : Differentiable ℝ (cutoff s) :=
  (contDiff_cutoff (n := 1) s).differentiable one_ne_zero

theorem cutoff_nonneg (s r : ℝ) : 0 ≤ cutoff s r := Real.smoothTransition.nonneg _

theorem cutoff_le_one (s r : ℝ) : cutoff s r ≤ 1 := Real.smoothTransition.le_one _

theorem cutoff_of_le {s r : ℝ} (hs : 0 < s) (h : r ≤ s) : cutoff s r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one hs]; exact h)

theorem cutoff_of_ge {s r : ℝ} (hs : 0 < s) (h : 2 * s ≤ r) : cutoff s r = 1 :=
  Real.smoothTransition.one_of_one_le (by
    rw [le_sub_iff_add_le, le_div_iff₀ hs]; linarith)

theorem monotone_cutoff {s : ℝ} (hs : 0 < s) : Monotone (cutoff s) := fun a b hab =>
  Real.smoothTransition.monotone (by
    have h : a / s ≤ b / s := by gcongr
    linarith)

theorem deriv_cutoff_nonneg {s : ℝ} (hs : 0 < s) (r : ℝ) : 0 ≤ deriv (cutoff s) r :=
  (monotone_cutoff hs).deriv_nonneg

theorem hasDerivAt_cutoff (s r : ℝ) : HasDerivAt (cutoff s) (deriv (cutoff s) r) r :=
  (differentiable_cutoff s r).hasDerivAt

/-- `χ_s` increases as `s` decreases, at nonnegative arguments. -/
theorem cutoff_mono_param {s s' r : ℝ} (hs' : 0 < s') (hss' : s' ≤ s) (hr : 0 ≤ r) :
    cutoff s r ≤ cutoff s' r :=
  Real.smoothTransition.monotone (by
    have h : r / s ≤ r / s' := by gcongr
    linarith)

/-! ### The cutoff composed with `U` -/

section CutoffU

variable {K : Set (Euc d)} (hK : IsGoodConvex K) {U : Euc d → ℝ} (hUc : Continuous U)
  (hU0 : ∀ x, 0 ≤ U x) (hsupp : Function.support U ⊆ K) (hC1 : ContDiffOn ℝ 1 U K)
  {s : ℝ} (hs : 0 < s)

include hUc hsupp hs in
/-- Near a point outside `K`, the cutoff `χ_s ∘ U` vanishes. -/
theorem cutoffU_eventually_zero {x : Euc d} (hx : x ∉ K) :
    (fun y => cutoff s (U y)) =ᶠ[𝓝 x] fun _ => 0 := by
  have h0 : U x = 0 := eq_zero_of_notMem_of_support_subset hsupp hx
  have hlt : ∀ᶠ y in 𝓝 x, U y < s :=
    hUc.continuousAt.eventually_lt continuousAt_const (by rw [h0]; exact hs)
  filter_upwards [hlt] with y hy
  exact cutoff_of_le hs hy.le

include hK hUc hsupp hC1 hs in
/-- `χ_s ∘ U ∈ C¹(ℝ^d)`. -/
theorem cutoffU_contDiff : ContDiff ℝ 1 fun x => cutoff s (U x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ K
  · exact (contDiff_cutoff s).contDiffAt.comp x (hC1.contDiffAt (hK.isOpen.mem_nhds hx))
  · exact contDiffAt_const.congr_of_eventuallyEq (cutoffU_eventually_zero hUc hsupp hs hx)

include hs in
theorem cutoffU_support_subset :
    Function.support (fun x => cutoff s (U x)) ⊆ {x | s ≤ U x} := by
  intro x hx
  by_contra h
  exact hx (cutoff_of_le hs (not_le.1 h).le)

include hUc hs in
theorem cutoffU_tsupport_subset_superlevel :
    tsupport (fun x => cutoff s (U x)) ⊆ {x | s ≤ U x} :=
  closure_minimal (cutoffU_support_subset hs) (isClosed_le continuous_const hUc)

include hK hUc hsupp hs in
theorem cutoffU_hasCompactSupport : HasCompactSupport fun x => cutoff s (U x) :=
  (isCompact_superlevel hK hUc hsupp hs).of_isClosed_subset (isClosed_tsupport _)
    (cutoffU_tsupport_subset_superlevel hUc hs)

include hUc hsupp hs in
theorem cutoffU_tsupport_subset : tsupport (fun x => cutoff s (U x)) ⊆ K :=
  (cutoffU_tsupport_subset_superlevel hUc hs).trans fun x hx =>
    hsupp (Function.mem_support.2 (by
      have : s ≤ U x := hx
      linarith))

include hK hUc hU0 hsupp hC1 hs in
/-- `∇(χ_s ∘ U) = χ_s'(U) ∇U`. -/
theorem cutoffU_hasGradientAt (x : Euc d) :
    HasGradientAt (fun x => cutoff s (U x)) (deriv (cutoff s) (U x) • gradient U x) x := by
  by_cases hx : x ∈ K
  · have hU : HasGradientAt U (gradient U x) x :=
      ((hC1.differentiableOn one_ne_zero).differentiableAt (hK.isOpen.mem_nhds hx)).hasGradientAt
    have h := (hasDerivAt_cutoff s (U x)).comp_hasFDerivAt x hU.hasFDerivAt
    rw [hasGradientAt_iff_hasFDerivAt, map_smul]
    exact h
  · rw [gradient_eq_zero_of_eq_zero hU0 (eq_zero_of_notMem_of_support_subset hsupp hx),
      smul_zero]
    exact HasGradientAt.congr_of_eventuallyEq (hasGradientAt_const x (0 : ℝ))
      (cutoffU_eventually_zero hUc hsupp hs hx)

include hK hUc hU0 hsupp hC1 hs in
theorem cutoffU_gradient (x : Euc d) :
    gradient (fun x => cutoff s (U x)) x = deriv (cutoff s) (U x) • gradient U x :=
  (cutoffU_hasGradientAt hK hUc hU0 hsupp hC1 hs x).gradient

end CutoffU

/-! ### The kinetic density of `U` -/

variable {κ : ℝ} {Ψ : Euc d → ℝ} {E : InfConvData d}

/-- The kinetic density `U² Ψ(∇U/U)` of `U = e^{-w}`, in the form used by `regEnergy`. -/
noncomputable def regDens (Ψ : Euc d → ℝ) (E : InfConvData d) (z : Euc d) : ℝ :=
  Korevaar.homogeneousDensity 2 Ψ (regU E z) (gradient (regU E) z)

theorem regDens_of_notMem {z : Euc d} (hz : z ∉ E.Kt) : regDens Ψ E z = 0 := by
  rw [regDens, Korevaar.homogeneousDensity, regU_of_notMem hz,
    Real.zero_rpow (by norm_num), zero_mul]

theorem regDens_eq (hΨ : IsRegProfile Ψ) {z : Euc d} (hz : z ∈ E.Kt) :
    regDens Ψ E z = regU E z ^ 2 * Ψ (gradient (E.w 0) z) := by
  have hpos : 0 < regU E z := regU_pos hz
  have hg : (regU E z)⁻¹ • gradient (regU E) z = -gradient (E.w 0) z := by
    rw [gradient_regU hz, smul_neg, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  rw [regDens, Korevaar.homogeneousDensity, hg, hΨ.even,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem regMass_eq {z : Euc d} (hz : z ∈ E.Kt) : regMass E 0 z = regU E z ^ 2 := by
  rw [regMass, regU_of_mem hz, ← Real.exp_nat_mul]
  congr 1
  ring

theorem regKin_eq (hΨ : IsRegProfile Ψ) {z : Euc d} (hz : z ∈ E.Kt) :
    regKin Ψ E 0 z = regDens Ψ E z := by
  rw [regDens_eq hΨ hz, regKin, ← regMass, regMass_eq hz]

theorem regEnt_eq {z : Euc d} (hz : z ∈ E.Kt) :
    regEnt E 0 z = regU E z ^ 2 * Real.log (regU E z) := by
  have hlog : Real.log (regU E z) = -E.w 0 z := by
    rw [regU_of_mem hz, Real.log_exp]
  rw [regEnt, ← regMass, regMass_eq hz, hlog, mul_comm]

/-- `‖∇U‖ = U ‖∇w‖` on `K_t`. -/
theorem norm_gradient_regU {z : Euc d} (hz : z ∈ E.Kt) :
    ‖gradient (regU E) z‖ = regU E z * ‖gradient (E.w 0) z‖ := by
  rw [gradient_regU hz, norm_neg, norm_smul, Real.norm_of_nonneg (regU_nonneg E z)]

/-! ### The nonnegative kinetic part and the integrable remainder -/

/-- The nonnegative part `A = 2 U² (Ψ(∇w) - Ψ(0))` of twice the kinetic density. -/
noncomputable def regPos (Ψ : Euc d → ℝ) (E : InfConvData d) (z : Euc d) : ℝ :=
  2 * (regDens Ψ E z - Ψ 0 * regU E z ^ 2)

/-- The integrable remainder `B = 2 Ψ(0) U² + κ U² log U`. -/
noncomputable def regRest (κ : ℝ) (Ψ : Euc d → ℝ) (E : InfConvData d) (z : Euc d) : ℝ :=
  2 * Ψ 0 * regU E z ^ 2 + κ * (regU E z ^ 2 * Real.log (regU E z))

theorem regPos_add_regRest (κ : ℝ) (Ψ : Euc d → ℝ) (E : InfConvData d) (z : Euc d) :
    regPos Ψ E z + regRest κ Ψ E z =
      2 * regDens Ψ E z + κ * (regU E z ^ 2 * Real.log (regU E z)) := by
  rw [regPos, regRest]; ring

theorem regPos_of_notMem {z : Euc d} (hz : z ∉ E.Kt) : regPos Ψ E z = 0 := by
  rw [regPos, regDens_of_notMem hz, regU_of_notMem hz]; ring

theorem regRest_of_notMem (κ : ℝ) {z : Euc d} (hz : z ∉ E.Kt) : regRest κ Ψ E z = 0 := by
  rw [regRest, regU_of_notMem hz]; ring

variable {c Cq : ℝ}

/-- `c ‖∇U‖² ≤ A`: strong convexity of `Ψ` around its minimum at the origin. -/
theorem regPos_ge (hΨ : IsRegProfile Ψ) (hprof : IsRegProfileWith Ψ c Cq)
    (E : InfConvData d) (z : Euc d) :
    c * ‖gradient (regU E) z‖ ^ 2 ≤ regPos Ψ E z := by
  by_cases hz : z ∈ E.Kt
  · rw [regPos, regDens_eq hΨ hz, norm_gradient_regU hz, mul_pow]
    have h := hprof.quadratic_lower (gradient (E.w 0) z)
    have hsq : (0 : ℝ) ≤ regU E z ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h hsq]
  · rw [regPos, regDens_of_notMem hz, gradient_regU_of_notMem hz, regU_of_notMem hz]
    simp

theorem regPos_nonneg (hΨ : IsRegProfile Ψ) (hprof : IsRegProfileWith Ψ c Cq)
    (E : InfConvData d) (z : Euc d) : 0 ≤ regPos Ψ E z := by
  have h := regPos_ge hΨ hprof E z
  nlinarith [sq_nonneg ‖gradient (regU E) z‖, hprof.c_pos]

theorem measurable_regDens (hΨ : IsRegProfile Ψ) (E : InfConvData d) :
    Measurable (regDens Ψ E) := by
  have h1 : Measurable fun z => regU E z ^ (2 : ℝ) :=
    (continuous_regU E).measurable.pow_const _
  have h2 : Measurable fun z => Ψ ((regU E z)⁻¹ • gradient (regU E) z) :=
    hΨ.contDiff.continuous.measurable.comp
      (((continuous_regU E).measurable.inv).smul (measurable_gradient' (regU E)))
  exact h1.mul h2

theorem measurable_regPos (hΨ : IsRegProfile Ψ) (E : InfConvData d) :
    Measurable (regPos Ψ E) :=
  (measurable_const.mul ((measurable_regDens hΨ E).sub
    (measurable_const.mul ((continuous_regU E).measurable.pow_const 2))))

theorem continuous_regU_sq_log (E : InfConvData d) :
    Continuous fun z => regU E z ^ 2 * Real.log (regU E z) := by
  have h : Continuous fun z => regU E z * (regU E z * Real.log (regU E z)) :=
    (continuous_regU E).mul (Real.continuous_mul_log.comp (continuous_regU E))
  exact h.congr fun z => by ring

theorem continuous_regRest (κ : ℝ) (Ψ : Euc d → ℝ) (E : InfConvData d) :
    Continuous (regRest κ Ψ E) :=
  ((continuous_const.mul (((continuous_regU E).pow 2))).add
    (continuous_const.mul (continuous_regU_sq_log E)))

theorem hasCompactSupport_regRest (κ : ℝ) (Ψ : Euc d → ℝ) (E : InfConvData d) :
    HasCompactSupport (regRest κ Ψ E) :=
  hasCompactSupport_of_zero_outside E.isBounded_Kt.isCompact_closure fun _z hz =>
    regRest_of_notMem κ fun h => hz (subset_closure h)

theorem integrable_regRest (κ : ℝ) (Ψ : Euc d → ℝ) (E : InfConvData d) :
    Integrable (regRest κ Ψ E) :=
  (continuous_regRest κ Ψ E).integrable_of_hasCompactSupport
    (hasCompactSupport_regRest κ Ψ E)

theorem integrable_regU_sq (E : InfConvData d) : Integrable fun z => regU E z ^ 2 :=
  ((continuous_regU E).pow 2).integrable_of_hasCompactSupport
    (hasCompactSupport_of_zero_outside E.isBounded_Kt.isCompact_closure fun z hz => by
      have h0 : regU E z = 0 := regU_of_notMem fun h => hz (subset_closure h)
      show regU E z ^ 2 = 0
      rw [h0]; ring)

theorem integrable_regU_sq_log (E : InfConvData d) :
    Integrable fun z => regU E z ^ 2 * Real.log (regU E z) :=
  (continuous_regU_sq_log E).integrable_of_hasCompactSupport
    (hasCompactSupport_of_zero_outside E.isBounded_Kt.isCompact_closure fun z hz => by
      have h0 : regU E z = 0 := regU_of_notMem fun h => hz (subset_closure h)
      show regU E z ^ 2 * Real.log (regU E z) = 0
      rw [h0]; ring)

/-! ### The energy inequality for `U` -/

/-- **The energy inequality for `U = e^{-w}`** (`REGULARIZED_ROUTE.md`, Revision 2, Wang–Xia
step 3).  Testing the weak inequality with the smooth cutoffs `χ_{1/(n+1)} ∘ U` — legitimate
because `U → 0` at `∂K_t`, so these are `C¹` with compact support in `K_t` — kills the
boundary term (it has the good sign, by `⟪∇Ψ q, q⟫ ≥ 0`) and yields, in the limit,

`2 ∫ U² Ψ(∇U/U) + κ ∫ U² log U ≤ ((1-t)Λ₀ + tΛ₁) ∫ U²`.

The integrability of the kinetic density and of `‖∇U‖²` is *produced* by the argument: the
nonnegative part `A = 2U²(Ψ(∇w) - Ψ(0)) ≥ c‖∇U‖²` has uniformly bounded integrals against the
cutoffs, so monotone convergence makes it integrable. -/
theorem regU_energy_le (E : InfConvData d) (hΨ : IsRegProfile Ψ) (hκ : 0 < κ)
    (hc₀ : ContDiffOn ℝ 1 (gradient E.v₀) E.K₀) (hc₁ : ContDiffOn ℝ 1 (gradient E.v₁) E.K₁)
    {lam₀ lam₁ : ℝ}
    (he₀ : ∀ x ∈ E.K₀, divergence (fun y => gradient Ψ (gradient E.v₀ y)) x =
      κ * E.v₀ x + lam₀ +
        2 * (⟪gradient Ψ (gradient E.v₀ x), gradient E.v₀ x⟫ - Ψ (gradient E.v₀ x)))
    (he₁ : ∀ x ∈ E.K₁, divergence (fun y => gradient Ψ (gradient E.v₁ y)) x =
      κ * E.v₁ x + lam₁ +
        2 * (⟪gradient Ψ (gradient E.v₁ x), gradient E.v₁ x⟫ - Ψ (gradient E.v₁ x))) :
    Integrable (regDens Ψ E) ∧ Integrable (fun z => ‖gradient (regU E) z‖ ^ 2) ∧
      2 * (∫ z, regDens Ψ E z) + κ * (∫ z, regU E z ^ 2 * Real.log (regU E z)) ≤
        ((1 - E.t) * lam₀ + E.t * lam₁) * (∫ z, regU E z ^ 2) := by
  obtain ⟨c, Cq, hprof⟩ := hΨ.exists_isRegProfileWith
  have hKt : IsGoodConvex E.Kt := ⟨E.nonempty_Kt, E.isBounded_Kt, E.isOpen_Kt, E.convex_Kt⟩
  have hUc : Continuous (regU E) := continuous_regU E
  have hU0 : ∀ z, 0 ≤ regU E z := regU_nonneg E
  have hsupp : Function.support (regU E) ⊆ E.Kt := support_regU E
  have hC1 : ContDiffOn ℝ 1 (regU E) E.Kt := contDiffOn_regU E
  have hinnernn : ∀ q : Euc d, 0 ≤ ⟪gradient Ψ q, q⟫ := by
    intro q
    have h := hprof.inner_gradient_sub q 0
    rw [hΨ.gradient_zero, sub_zero, sub_zero] at h
    have h2 := mul_nonneg hprof.c_pos.le (sq_nonneg ‖q‖)
    linarith
  -- the sequence of cutoff levels
  set sm : ℕ → ℝ := fun n => 1 / (n + 1) with hsmdef
  have hsm0 : ∀ n, 0 < sm n := fun n => by rw [hsmdef]; positivity
  have hsmanti : ∀ m n : ℕ, m ≤ n → sm n ≤ sm m := by
    intro m n hmn
    rw [hsmdef]
    simp only
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
      linarith
    exact one_div_le_one_div_of_le h1 h2
  set χ : ℕ → Euc d → ℝ := fun n z => cutoff (sm n) (regU E z) with hχdef
  have hχ1 : ∀ n, ContDiff ℝ 1 (χ n) := fun n => by
    simp only [hχdef]
    exact cutoffU_contDiff hKt hUc hsupp hC1 (hsm0 n)
  have hχs : ∀ n, HasCompactSupport (χ n) := fun n => by
    simp only [hχdef]
    exact cutoffU_hasCompactSupport hKt hUc hsupp (hsm0 n)
  have hχK : ∀ n, tsupport (χ n) ⊆ E.Kt := fun n => by
    simp only [hχdef]
    exact cutoffU_tsupport_subset hUc hsupp (hsm0 n)
  have hχ0 : ∀ n z, 0 ≤ χ n z := fun n z => cutoff_nonneg _ _
  have hχle : ∀ n z, χ n z ≤ 1 := fun n z => cutoff_le_one _ _
  have hχgrad : ∀ n z, gradient (χ n) z = deriv (cutoff (sm n)) (regU E z) • gradient (regU E) z :=
    fun n z => by
      simp only [hχdef]
      exact cutoffU_gradient hKt hUc hU0 hsupp hC1 (hsm0 n) z
  have hχzero : ∀ n, ∀ z ∉ E.Kt, χ n z = 0 := fun n z hz => by
    simp only [hχdef]
    rw [regU_of_notMem hz]
    exact cutoff_of_le (hsm0 n) (hsm0 n).le
  have hχsupp0 : ∀ n, ∀ z ∉ tsupport (χ n), χ n z = 0 := fun n z hz =>
    image_eq_zero_of_notMem_tsupport hz
  -- the boundary term has the good sign
  have hsign : ∀ n, ∫ z, ⟪regFlux Ψ E 0 z, gradient (χ n) z⟫ ≤ 0 := by
    intro n
    refine integral_nonpos fun z => ?_
    show ⟪regFlux Ψ E 0 z, gradient (χ n) z⟫ ≤ 0
    rw [hχgrad n z, real_inner_smul_right]
    by_cases hz : z ∈ E.Kt
    · rw [gradient_regU hz, inner_neg_right, real_inner_smul_right]
      simp only [regFlux]
      rw [real_inner_smul_left]
      have h1 := hinnernn (gradient (E.w 0) z)
      have h2 : 0 ≤ deriv (cutoff (sm n)) (regU E z) := deriv_cutoff_nonneg (hsm0 n) _
      have h3 : 0 ≤ regU E z := hU0 z
      have h4 : (0 : ℝ) < Real.exp (-(2 * E.w 0 z)) := Real.exp_pos _
      have h5 : 0 ≤ regU E z * (Real.exp (-(2 * E.w 0 z)) *
          ⟪gradient Ψ (gradient (E.w 0) z), gradient (E.w 0) z⟫) :=
        mul_nonneg h3 (mul_nonneg h4.le h1)
      nlinarith [mul_nonneg h2 h5]
    · rw [gradient_regU_of_notMem hz, inner_zero_right, mul_zero]
  -- the pointwise rewritings
  have hrw : ∀ n z, (2 * regKin Ψ E 0 z + κ * regEnt E 0 z) * χ n z =
      (regPos Ψ E z + regRest κ Ψ E z) * χ n z := by
    intro n z
    by_cases hz : z ∈ E.Kt
    · rw [regKin_eq hΨ hz, regEnt_eq hz, regPos, regRest]
      ring
    · rw [hχzero n z hz, mul_zero, mul_zero]
  have hrwM : ∀ n z, regMass E 0 z * χ n z = regU E z ^ 2 * χ n z := by
    intro n z
    by_cases hz : z ∈ E.Kt
    · rw [regMass_eq hz]
    · rw [hχzero n z hz, mul_zero, mul_zero]
  -- integrability of the tested densities
  have hKinχ : ∀ n, Integrable fun z => (2 * regKin Ψ E 0 z + κ * regEnt E 0 z) * χ n z := by
    intro n
    have hcont : Continuous fun z => (2 * regKin Ψ E 0 z + κ * regEnt E 0 z) * χ n z :=
      continuous_mul_of_continuousOn E.isOpen_Kt (continuousOn_regKin_add hΨ le_rfl)
        (hχ1 n).continuous (isClosed_tsupport _) (hχK n) (hχsupp0 n)
    exact hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_of_zero_outside (hχs n) fun z hz => by
        rw [hχsupp0 n z hz, mul_zero])
  have hABχ : ∀ n, Integrable fun z => (regPos Ψ E z + regRest κ Ψ E z) * χ n z :=
    fun n => (hKinχ n).congr (Eventually.of_forall fun z => hrw n z)
  have hRi : Integrable (regRest κ Ψ E) := integrable_regRest κ Ψ E
  have hU2i : Integrable fun z => regU E z ^ 2 := integrable_regU_sq E
  have hRχ : ∀ n, Integrable fun z => regRest κ Ψ E z * χ n z := fun n =>
    ((continuous_regRest κ Ψ E).mul (hχ1 n).continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_regRest κ Ψ E).mul_right)
  have hU2χ : ∀ n, Integrable fun z => regU E z ^ 2 * χ n z := fun n =>
    (((continuous_regU E).pow 2).mul (hχ1 n).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hχs n))
  have hAχ : ∀ n, Integrable fun z => regPos Ψ E z * χ n z := by
    intro n
    have h := (hABχ n).sub (hRχ n)
    refine h.congr (Eventually.of_forall fun z => ?_)
    show (regPos Ψ E z + regRest κ Ψ E z) * χ n z - regRest κ Ψ E z * χ n z
      = regPos Ψ E z * χ n z
    ring
  -- the tested inequality
  have hkey : ∀ n, ∫ z, (regPos Ψ E z + regRest κ Ψ E z) * χ n z ≤
      ((1 - E.t) * lam₀ + E.t * lam₁) * (∫ z, regU E z ^ 2 * χ n z) := by
    intro n
    have hmain := integral_regDensity_le_zero E hΨ hκ.le hc₀ hc₁ he₀ he₁
      (hχ1 n) (hχs n) (hχ0 n) (hχK n)
    have e1 : ∫ z, (2 * regKin Ψ E 0 z + κ * regEnt E 0 z) * χ n z
        = ∫ z, (regPos Ψ E z + regRest κ Ψ E z) * χ n z :=
      integral_congr_ae (Eventually.of_forall fun z => hrw n z)
    have e2 : ∫ z, regMass E 0 z * χ n z = ∫ z, regU E z ^ 2 * χ n z :=
      integral_congr_ae (Eventually.of_forall fun z => hrwM n z)
    rw [e1, e2] at hmain
    linarith [hsign n]
  -- a uniform bound for the nonnegative part
  set Kb : ℝ := |(1 - E.t) * lam₀ + E.t * lam₁| * (∫ z, regU E z ^ 2) +
    ∫ z, |regRest κ Ψ E z| with hKbdef
  have hsplitn : ∀ n, ∫ z, (regPos Ψ E z + regRest κ Ψ E z) * χ n z
      = (∫ z, regPos Ψ E z * χ n z) + ∫ z, regRest κ Ψ E z * χ n z := by
    intro n
    rw [← integral_add (hAχ n) (hRχ n)]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  have hbnd : ∀ n, ∫ z, regPos Ψ E z * χ n z ≤ Kb := by
    intro n
    have h2 := hkey n
    rw [hsplitn n] at h2
    have h3 : (0 : ℝ) ≤ ∫ z, regU E z ^ 2 * χ n z :=
      integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hχ0 n z)
    have h4 : (∫ z, regU E z ^ 2 * χ n z) ≤ ∫ z, regU E z ^ 2 :=
      integral_mono (hU2χ n) hU2i fun z => by
        nlinarith [sq_nonneg (regU E z), hχ0 n z, hχle n z]
    have h5 : -∫ z, regRest κ Ψ E z * χ n z ≤ ∫ z, |regRest κ Ψ E z| := by
      rw [← integral_neg]
      refine integral_mono ((hRχ n).neg) hRi.abs fun z => ?_
      show -(regRest κ Ψ E z * χ n z) ≤ |regRest κ Ψ E z|
      calc -(regRest κ Ψ E z * χ n z) ≤ |regRest κ Ψ E z * χ n z| := neg_le_abs _
        _ = |regRest κ Ψ E z| * |χ n z| := abs_mul _ _
        _ ≤ |regRest κ Ψ E z| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [abs_of_nonneg (hχ0 n z)]
            exact hχle n z
        _ = |regRest κ Ψ E z| := mul_one _
    have h8 : ((1 - E.t) * lam₀ + E.t * lam₁) * (∫ z, regU E z ^ 2 * χ n z) ≤
        |(1 - E.t) * lam₀ + E.t * lam₁| * (∫ z, regU E z ^ 2) := by
      have hnn : (0 : ℝ) ≤ ∫ z, regU E z ^ 2 := integral_nonneg fun z => sq_nonneg _
      rcases le_or_gt 0 ((1 - E.t) * lam₀ + E.t * lam₁) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_neg h]; nlinarith
    rw [hKbdef]
    linarith
  -- monotone convergence: the nonnegative part is integrable
  have hAmeas : Measurable (regPos Ψ E) := measurable_regPos hΨ E
  have hlint : ∫⁻ z, ENNReal.ofReal (regPos Ψ E z) ≤ ENNReal.ofReal Kb := by
    have hmeas : ∀ n, Measurable fun z => ENNReal.ofReal (regPos Ψ E z * χ n z) := fun n =>
      (hAmeas.mul (hχ1 n).continuous.measurable).ennreal_ofReal
    have hmono : Monotone fun n => fun z => ENNReal.ofReal (regPos Ψ E z * χ n z) := by
      intro m n hmn z
      refine ENNReal.ofReal_le_ofReal ?_
      refine mul_le_mul_of_nonneg_left ?_ (regPos_nonneg hΨ hprof E z)
      show cutoff (sm m) (regU E z) ≤ cutoff (sm n) (regU E z)
      exact cutoff_mono_param (hsm0 n) (hsmanti m n hmn) (hU0 z)
    have hsup : ∀ z, ⨆ n, ENNReal.ofReal (regPos Ψ E z * χ n z)
        = ENNReal.ofReal (regPos Ψ E z) := by
      intro z
      refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal ?_) ?_
      · nlinarith [regPos_nonneg hΨ hprof E z, hχ0 n z, hχle n z]
      · by_cases hz : z ∈ E.Kt
        · have hUz : 0 < regU E z := regU_pos hz
          obtain ⟨n, hn⟩ := exists_nat_ge (2 / regU E z)
          have hle : 2 * sm n ≤ regU E z := by
            rw [hsmdef]
            simp only
            rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
            rw [div_le_iff₀ hUz] at hn
            nlinarith [Nat.cast_nonneg (α := ℝ) n]
          refine le_iSup_of_le n (le_of_eq ?_)
          have hone : χ n z = 1 := by
            show cutoff (sm n) (regU E z) = 1
            exact cutoff_of_ge (hsm0 n) hle
          rw [hone, mul_one]
        · rw [regPos_of_notMem hz]
          simp
    calc ∫⁻ z, ENNReal.ofReal (regPos Ψ E z)
        = ∫⁻ z, ⨆ n, ENNReal.ofReal (regPos Ψ E z * χ n z) :=
          lintegral_congr fun z => (hsup z).symm
      _ = ⨆ n, ∫⁻ z, ENNReal.ofReal (regPos Ψ E z * χ n z) := lintegral_iSup hmeas hmono
      _ ≤ ENNReal.ofReal Kb := by
          refine iSup_le fun n => ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hAχ n)
            (Eventually.of_forall fun z =>
              mul_nonneg (regPos_nonneg hΨ hprof E z) (hχ0 n z))]
          exact ENNReal.ofReal_le_ofReal (hbnd n)
  have hAi : Integrable (regPos Ψ E) := by
    refine ⟨hAmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun z => regPos_nonneg hΨ hprof E z)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  -- the three limits
  have hχlim : ∀ z, 0 < regU E z → Tendsto (fun n => χ n z) atTop (𝓝 1) := by
    intro z hUz
    obtain ⟨N, hN⟩ := exists_nat_ge (2 / regU E z)
    have hev : ∀ᶠ n in atTop, χ n z = 1 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : 2 * sm n ≤ regU E z := by
        rw [hsmdef]
        simp only
        rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
        rw [div_le_iff₀ hUz] at hN
        have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      show cutoff (sm n) (regU E z) = 1
      exact cutoff_of_ge (hsm0 n) hle
    exact tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)
  have hlimA : Tendsto (fun n => ∫ z, regPos Ψ E z * χ n z) atTop
      (𝓝 (∫ z, regPos Ψ E z)) := by
    refine tendsto_integral_of_dominated_convergence (regPos Ψ E)
      (fun n => (hAχ n).aestronglyMeasurable) hAi
      (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · rw [Real.norm_of_nonneg
        (mul_nonneg (regPos_nonneg hΨ hprof E z) (hχ0 n z))]
      nlinarith [regPos_nonneg hΨ hprof E z, hχ0 n z, hχle n z]
    · rcases (hU0 z).eq_or_lt with h | h
      · have hz : z ∉ E.Kt := fun hz => (regU_pos hz).ne' h.symm
        rw [regPos_of_notMem hz]
        simp
      · simpa using (tendsto_const_nhds (x := regPos Ψ E z)).mul (hχlim z h)
  have hlimR : Tendsto (fun n => ∫ z, regRest κ Ψ E z * χ n z) atTop
      (𝓝 (∫ z, regRest κ Ψ E z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => |regRest κ Ψ E z|)
      (fun n => (hRχ n).aestronglyMeasurable) hRi.abs
      (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ0 n z)]
      refine mul_le_mul_of_nonneg_left (hχle n z) (abs_nonneg _) |>.trans ?_
      rw [mul_one]
    · rcases (hU0 z).eq_or_lt with h | h
      · have hz : z ∉ E.Kt := fun hz => (regU_pos hz).ne' h.symm
        rw [regRest_of_notMem κ hz]
        simp
      · simpa using (tendsto_const_nhds (x := regRest κ Ψ E z)).mul (hχlim z h)
  have hlimU : Tendsto (fun n => ∫ z, regU E z ^ 2 * χ n z) atTop
      (𝓝 (∫ z, regU E z ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => regU E z ^ 2)
      (fun n => (hU2χ n).aestronglyMeasurable) hU2i
      (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hχ0 n z))]
      nlinarith [sq_nonneg (regU E z), hχ0 n z, hχle n z]
    · rcases (hU0 z).eq_or_lt with h | h
      · rw [← h]
        simp
      · simpa using (tendsto_const_nhds (x := regU E z ^ 2)).mul (hχlim z h)
  -- passing to the limit
  have hfin : (∫ z, regPos Ψ E z) + (∫ z, regRest κ Ψ E z) ≤
      ((1 - E.t) * lam₀ + E.t * lam₁) * (∫ z, regU E z ^ 2) := by
    refine le_of_tendsto_of_tendsto (f := fun n => ∫ z, (regPos Ψ E z + regRest κ Ψ E z) * χ n z)
      ?_ (hlimU.const_mul _) (Eventually.of_forall hkey)
    refine (hlimA.add hlimR).congr fun n => (hsplitn n).symm
  -- unwinding
  have hDi : Integrable (regDens Ψ E) := by
    have h := (hAi.const_mul (1 / 2 : ℝ)).add (hU2i.const_mul (Ψ 0))
    refine h.congr (Eventually.of_forall fun z => ?_)
    show 1 / 2 * regPos Ψ E z + Ψ 0 * regU E z ^ 2 = regDens Ψ E z
    rw [regPos]; ring
  have hgi : Integrable fun z => ‖gradient (regU E) z‖ ^ 2 := by
    refine Integrable.mono' (hAi.const_mul (1 / c)) ?_ (Eventually.of_forall fun z => ?_)
    · exact ((measurable_gradient' (regU E)).norm.pow_const 2).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h := regPos_ge hΨ hprof E z
      have hc0 := hprof.c_pos
      have he : ‖gradient (regU E) z‖ ^ 2 = 1 / c * (c * ‖gradient (regU E) z‖ ^ 2) := by
        field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_left h (by positivity)
  have hUlogi : Integrable fun z => regU E z ^ 2 * Real.log (regU E z) :=
    integrable_regU_sq_log E
  have hsplitA : (∫ z, regPos Ψ E z)
      = 2 * (∫ z, regDens Ψ E z) - 2 * Ψ 0 * (∫ z, regU E z ^ 2) := by
    have hfun : (fun z => regPos Ψ E z)
        = fun z => 2 * regDens Ψ E z - 2 * Ψ 0 * regU E z ^ 2 := by
      funext z; rw [regPos]; ring
    rw [hfun, integral_sub (hDi.const_mul 2) (hU2i.const_mul (2 * Ψ 0)), integral_const_mul,
      integral_const_mul]
  have hsplitB : (∫ z, regRest κ Ψ E z)
      = 2 * Ψ 0 * (∫ z, regU E z ^ 2) + κ * (∫ z, regU E z ^ 2 * Real.log (regU E z)) := by
    have hfun : (fun z => regRest κ Ψ E z)
        = fun z => 2 * Ψ 0 * regU E z ^ 2 + κ * (regU E z ^ 2 * Real.log (regU E z)) := by
      funext z; rw [regRest]
    rw [hfun, integral_add (hU2i.const_mul (2 * Ψ 0)) (hUlogi.const_mul κ), integral_const_mul,
      integral_const_mul]
  refine ⟨hDi, hgi, ?_⟩
  rw [hsplitA, hsplitB] at hfin
  linarith

end Komlos.Literature.Regularized
