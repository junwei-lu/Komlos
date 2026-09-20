import Komlos.Literature.Regularized.ProfileBasic
import Komlos.Literature.Regularized.LogConcave
import Komlos.Literature.Regularized.PrekopaLeindler
import Komlos.Literature.WangXia.EigenvalueConvexHessian

/-!
# Wang–Xia for the regularized route: the infimal-convolution data (lane `L5`)

This is the first of the `Assembly*` files of lane `L5` (`reg/wangxia`) of
`REGULARIZED_ROUTE.md` (Revision 2).  It sets up the infimal convolution of the two
log-minimizers `v_i = -log φ_i` of `RegEigenData 2 κ Ψ K_i` and proves the facts about
`U = e^{-w}` that the rest of the lane uses.

Everything here is *equation-independent*: it only uses that `v_i` is convex, `C²` on `K_i`
and blows up at `∂K_i`, so the infimal-convolution calculus of
`Komlos/Literature/WangXia/InfConv.lean` applies verbatim.

## Main results

* `RegEigenData.logFn`, `RegEigenData.isInputData`: `v = -log φ` is an admissible input of the
  infimal convolution (`IsInputData`); the compactness of its sublevel sets comes from
  positivity and continuity of `φ` together with `φ = 0` off `K`.
* `regInfConvData`: the data `(K_i, v_i, t)`.
* `regU`: `U = e^{-w}` on `K_t`, extended by zero; continuity, positivity, `C¹` on `K_t`,
  `∇U = -U ∇w`, and the boundedness `U ≤ e^{-m}`.
* `one_le_integral_regU_sq`: **Prékopa–Leindler** gives `1 ≤ ∫ U²`.  This is the step that
  makes the logarithmic term of the regularized energy have the good sign; it uses
  `one_le_integral_of_geometric_mean_le` with `f = φ₀²`, `g = φ₁²`, `h = U²`, the pointwise
  bound `U((1-t)x + ty) ≥ φ₀(x)^{1-t} φ₁(y)^t` being the definition of the infimal
  convolution.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The log-minimizer as an input of the infimal convolution -/

namespace RegEigenData

variable {p κ : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} (D : RegEigenData p κ Ψ K)

/-- The log-minimizer `v = -log φ` (`REGULARIZED_ROUTE.md`, Revision 2, Wang–Xia step). -/
noncomputable def logFn (x : Euc d) : ℝ := -Real.log (D.φ x)

theorem logFn_eq : D.logFn = fun x => -Real.log (D.φ x) := rfl

theorem logFn_le_iff {x : Euc d} (hx : x ∈ K) {M : ℝ} :
    D.logFn x ≤ M ↔ Real.exp (-M) ≤ D.φ x := by
  rw [logFn, neg_le, Real.le_log_iff_exp_le (D.pos x hx)]

/-- `φ` is positive only on `K`. -/
theorem mem_of_pos {x : Euc d} (hx : 0 < D.φ x) : x ∈ K := by
  by_contra h
  exact hx.ne' (D.eq_zero_of_notMem x h)

/-- `exp (-v) = φ` on `K`. -/
theorem exp_neg_logFn {x : Euc d} (hx : x ∈ K) : Real.exp (-D.logFn x) = D.φ x := by
  rw [logFn, neg_neg, Real.exp_log (D.pos x hx)]

/-- The sublevel sets of `v = -log φ` are compact: `v` is bounded below and blows up at the
boundary, because `φ` is continuous, positive on `K` and zero off `K`. -/
theorem isCompact_sublevel_logFn (hK : IsGoodConvex K) (M : ℝ) :
    IsCompact {x ∈ K | D.logFn x ≤ M} := by
  have hmem : ∀ x, Real.exp (-M) ≤ D.φ x → x ∈ K := fun x hx =>
    D.mem_of_pos ((Real.exp_pos _).trans_le hx)
  have heq : {x ∈ K | D.logFn x ≤ M} = {x | Real.exp (-M) ≤ D.φ x} := by
    ext x
    constructor
    · rintro ⟨hx, hle⟩
      exact (D.logFn_le_iff hx).1 hle
    · intro h
      exact ⟨hmem x h, (D.logFn_le_iff (hmem x h)).2 h⟩
  rw [heq]
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_const D.continuous)
    (hK.isBounded.subset fun x hx => hmem x hx)

/-- `v = -log φ` is `C¹` on `K`. -/
theorem contDiffOn_one_logFn : ContDiffOn ℝ 1 D.logFn K := D.contDiffOn_two.of_le (by norm_num)

/-- `∇v` is `C¹` on `K` (there is no critical set to avoid: `v` is `C²` on all of `K`). -/
theorem contDiffOn_gradient_logFn (hK : IsGoodConvex K) :
    ContDiffOn ℝ 1 (gradient D.logFn) K := by
  have h := D.contDiffOn_two.fderiv_of_isOpen (m := 1) hK.isOpen (by norm_num)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h

/-- `(K, -log φ)` is an admissible input of the infimal convolution. -/
theorem isInputData (hK : IsGoodConvex K) (hD : ConvexOn ℝ K D.logFn) :
    IsInputData K D.logFn where
  isOpen := hK.isOpen
  convex := hK.convex
  nonempty := hK.nonempty
  isBounded := hK.isBounded
  convexOn := hD
  contDiffOn := D.contDiffOn_one_logFn
  isCompact_sublevel := D.isCompact_sublevel_logFn hK

end RegEigenData

/-! ### The infimal-convolution data of the two log-minimizers -/

/-- The infimal-convolution data `(K_i, v_i = -log φ_i, t)` of the regularized route. -/
noncomputable def regInfConvData {κ : ℝ} {Ψ : Euc d → ℝ} {K₀ K₁ : Set (Euc d)}
    (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK₀ : IsGoodConvex K₀) (hK₁ : IsGoodConvex K₁)
    (D₀ : RegEigenData 2 κ Ψ K₀) (D₁ : RegEigenData 2 κ Ψ K₁) {t : ℝ} (ht₀ : 0 < t)
    (ht₁ : t < 1) : InfConvData d where
  K₀ := K₀
  K₁ := K₁
  v₀ := D₀.logFn
  v₁ := D₁.logFn
  t := t
  h₀ := D₀.isInputData hK₀ (RegEigenData.convexOn_neg_log hκ hΨ hK₀ D₀)
  h₁ := D₁.isInputData hK₁ (RegEigenData.convexOn_neg_log hκ hΨ hK₁ D₁)
  t_pos := ht₀
  t_lt_one := ht₁

/-! ### The function `U = e^{-w}` -/

/-- `U = e^{-w}` on `K_t`, extended by zero outside `K_t`. -/
noncomputable def regU (E : InfConvData d) : Euc d → ℝ :=
  E.Kt.indicator fun z => Real.exp (-E.w 0 z)

variable {E : InfConvData d}

theorem regU_of_mem {z : Euc d} (hz : z ∈ E.Kt) : regU E z = Real.exp (-E.w 0 z) :=
  indicator_of_mem hz _

theorem regU_of_notMem {z : Euc d} (hz : z ∉ E.Kt) : regU E z = 0 := indicator_of_notMem hz _

theorem regU_nonneg (E : InfConvData d) (z : Euc d) : 0 ≤ regU E z :=
  indicator_nonneg (fun _ _ => (Real.exp_pos _).le) z

theorem regU_pos {z : Euc d} (hz : z ∈ E.Kt) : 0 < regU E z := by
  rw [regU_of_mem hz]; exact Real.exp_pos _

theorem support_regU (E : InfConvData d) : Function.support (regU E) ⊆ E.Kt :=
  support_indicator_subset

theorem regU_eq_zero_of_notMem {z : Euc d} (hz : z ∉ E.Kt) : regU E z = 0 := regU_of_notMem hz

theorem regU_ne_zero (E : InfConvData d) : regU E ≠ 0 := fun h => by
  obtain ⟨z, hz⟩ := E.nonempty_Kt
  exact (regU_pos hz).ne' (congrFun h z)

/-- `U` is continuous on `ℝ^d`: on `K_t` it is `e^{-w}`, and `w → +∞` at `∂K_t`. -/
theorem continuous_regU (E : InfConvData d) : Continuous (regU E) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ E.Kt
  · have hc : ContinuousAt (fun z => Real.exp (-E.w 0 z)) z :=
      Real.continuous_exp.continuousAt.comp
        ((E.continuousOn_w le_rfl).continuousAt (E.isOpen_Kt.mem_nhds hz)).neg
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [E.isOpen_Kt.mem_nhds hz] with y hy
    exact regU_of_mem hy
  · by_cases hcl : z ∈ closure E.Kt
    · have hfr : z ∈ frontier E.Kt := ⟨hcl, by rwa [E.isOpen_Kt.interior_eq]⟩
      rw [ContinuousAt, regU_of_notMem hz,
        nhds_eq_nhdsWithin_sup_nhdsWithin z (I₁ := E.Kt) (I₂ := E.Ktᶜ) (union_compl_self _).symm,
        tendsto_sup]
      constructor
      · have h2 : Tendsto (fun z => Real.exp (-E.w 0 z)) (𝓝[E.Kt] z) (𝓝 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp (E.tendsto_w_frontier le_rfl hfr)
        refine h2.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (regU_of_mem hy).symm
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (regU_of_notMem hy).symm
    · have hmem : (closure E.Kt)ᶜ ∈ 𝓝 z := isClosed_closure.isOpen_compl.mem_nhds hcl
      refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hmem] with y hy
      exact regU_of_notMem fun h => hy (subset_closure h)

/-- `U ∈ C¹(K_t)`. -/
theorem contDiffOn_regU (E : InfConvData d) : ContDiffOn ℝ 1 (regU E) E.Kt := by
  refine ContDiffOn.congr ?_ fun z hz => regU_of_mem hz
  exact Real.contDiff_exp.comp_contDiffOn (E.contDiffOn_w le_rfl).neg

/-- `∇U = -U ∇w` on `K_t`. -/
theorem hasGradientAt_regU {z : Euc d} (hz : z ∈ E.Kt) :
    HasGradientAt (regU E) (-(regU E z • gradient (E.w 0) z)) z := by
  have hw : HasGradientAt (E.w 0) (gradient (E.w 0) z) z :=
    ((E.differentiableOn_w le_rfl).differentiableAt (E.isOpen_Kt.mem_nhds hz)).hasGradientAt
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-E.w 0 z)) (E.w 0 z) := by
    simpa using (hasDerivAt_neg (E.w 0 z)).exp
  have h := hexp.comp_hasFDerivAt z hw.hasFDerivAt
  have hU : regU E =ᶠ[𝓝 z] (fun s : ℝ => Real.exp (-s)) ∘ E.w 0 := by
    filter_upwards [E.isOpen_Kt.mem_nhds hz] with y hy
    exact regU_of_mem hy
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (h.congr_of_eventuallyEq hU).congr_fderiv ?_
  rw [regU_of_mem hz, map_neg, map_smul, neg_smul]

theorem gradient_regU {z : Euc d} (hz : z ∈ E.Kt) :
    gradient (regU E) z = -(regU E z • gradient (E.w 0) z) :=
  (hasGradientAt_regU hz).gradient

/-- The gradient of `U` vanishes outside `K_t`. -/
theorem gradient_regU_of_notMem {z : Euc d} (hz : z ∉ E.Kt) : gradient (regU E) z = 0 :=
  gradient_eq_zero_of_eq_zero (regU_nonneg E) (regU_of_notMem hz)

/-- `U` is bounded: `w` is bounded below on `K_t`. -/
theorem exists_regU_le (E : InfConvData d) : ∃ M : ℝ, 0 < M ∧ ∀ z, regU E z ≤ M := by
  obtain ⟨m, hm⟩ := E.exists_forall_le_w
  refine ⟨Real.exp (-m), Real.exp_pos _, fun z => ?_⟩
  by_cases hz : z ∈ E.Kt
  · rw [regU_of_mem hz]
    exact Real.exp_le_exp.2 (neg_le_neg (hm 0 le_rfl z hz))
  · rw [regU_of_notMem hz]; exact (Real.exp_pos _).le

/-- `U` has compact support. -/
theorem hasCompactSupport_regU (E : InfConvData d) : HasCompactSupport (regU E) :=
  E.isBounded_Kt.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
    (closure_mono (support_regU E))

/-! ### Prékopa–Leindler: `1 ≤ ∫ U²` -/

section PL

variable {κ : ℝ} {Ψ : Euc d → ℝ} {K₀ K₁ : Set (Euc d)} (hκ : 0 < κ) (hΨ : IsRegProfile Ψ)
  (hK₀ : IsGoodConvex K₀) (hK₁ : IsGoodConvex K₁) (D₀ : RegEigenData 2 κ Ψ K₀)
  (D₁ : RegEigenData 2 κ Ψ K₁) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)

/-- The defining inequality of the infimal convolution, in multiplicative form:
`U((1-t)x + ty) ≥ φ₀(x)^{1-t} φ₁(y)^t` for all `x, y` (both sides vanish outside the
domains). -/
theorem rpow_mul_rpow_le_regU (x y : Euc d) :
    D₀.φ x ^ (1 - t) * D₁.φ y ^ t ≤
      regU (regInfConvData hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁) ((1 - t) • x + t • y) := by
  set E := regInfConvData hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁ with hE
  have ht0' : (0 : ℝ) < 1 - t := sub_pos.2 ht₁
  by_cases hx : x ∈ K₀
  · by_cases hy : y ∈ K₁
    · have hz : (1 - t) • x + t • y ∈ E.Kt := E.combo_mem_Kt hx hy
      have hfeas : ((x, y) : Euc d × Euc d) ∈ E.feasible ((1 - t) • x + t • y) :=
        ⟨hx, hy, rfl⟩
      have hle : E.w 0 ((1 - t) • x + t • y) ≤ (1 - t) * D₀.logFn x + t * D₁.logFn y := by
        have h := E.w_le_obj le_rfl hfeas
        rwa [InfConvData.obj_zero] at h
      rw [regU_of_mem hz]
      have hexp : D₀.φ x ^ (1 - t) * D₁.φ y ^ t =
          Real.exp (-((1 - t) * D₀.logFn x + t * D₁.logFn y)) := by
        rw [Real.rpow_def_of_pos (D₀.pos x hx), Real.rpow_def_of_pos (D₁.pos y hy),
          ← Real.exp_add]
        congr 1
        simp only [RegEigenData.logFn]
        ring
      rw [hexp]
      exact Real.exp_le_exp.2 (neg_le_neg hle)
    · rw [D₁.eq_zero_of_notMem y hy, Real.zero_rpow ht₀.ne', mul_zero]
      exact regU_nonneg E _
  · rw [D₀.eq_zero_of_notMem x hx, Real.zero_rpow ht0'.ne', zero_mul]
    exact regU_nonneg E _

/-- The squared form of `rpow_mul_rpow_le_regU`, as required by Prékopa–Leindler. -/
theorem sq_rpow_mul_sq_rpow_le_regU_sq (x y : Euc d) :
    (D₀.φ x ^ 2) ^ (1 - t) * (D₁.φ y ^ 2) ^ t ≤
      regU (regInfConvData hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁) ((1 - t) • x + t • y) ^ 2 := by
  have hsq : ∀ (a : ℝ) (r : ℝ), 0 ≤ a → (a ^ 2) ^ r = (a ^ r) ^ 2 := by
    intro a r ha
    have e1 : (a ^ 2 : ℝ) = a ^ (2 : ℝ) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e2 : ((a ^ r) ^ 2 : ℝ) = (a ^ r) ^ (2 : ℝ) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e1, e2, ← Real.rpow_mul ha, ← Real.rpow_mul ha, mul_comm]
  rw [hsq _ _ (D₀.isRegMinimizer.nonneg x), hsq _ _ (D₁.isRegMinimizer.nonneg y), ← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (D₀.isRegMinimizer.nonneg x) _)
      (Real.rpow_nonneg (D₁.isRegMinimizer.nonneg y) _))
    (rpow_mul_rpow_le_regU hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁ x y) 2

/-- **Prékopa–Leindler for the regularized route**: `1 ≤ ∫ U²`.  With `f = φ₀²` and `g = φ₁²`
of unit integral and `h = U²`, the pointwise inequality
`f(x)^{1-t} g(y)^t ≤ h((1-t)x + ty)` is `sq_rpow_mul_sq_rpow_le_regU_sq`. -/
theorem one_le_integral_regU_sq :
    1 ≤ ∫ z, regU (regInfConvData hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁) z ^ 2 := by
  set E := regInfConvData hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁ with hE
  have hc₀ : Continuous fun x => D₀.φ x ^ 2 := D₀.continuous.pow 2
  have hc₁ : Continuous fun x => D₁.φ x ^ 2 := D₁.continuous.pow 2
  have hcU : Continuous fun z => regU E z ^ 2 := (continuous_regU E).pow 2
  have hs₀ : HasCompactSupport fun x => D₀.φ x ^ 2 :=
    hasCompactSupport_of_zero_outside hK₀.isBounded.isCompact_closure fun x hx => by
      have h0 : D₀.φ x = 0 := D₀.eq_zero_of_notMem x fun h => hx (subset_closure h)
      show D₀.φ x ^ 2 = 0
      rw [h0]; ring
  have hs₁ : HasCompactSupport fun x => D₁.φ x ^ 2 :=
    hasCompactSupport_of_zero_outside hK₁.isBounded.isCompact_closure fun x hx => by
      have h0 : D₁.φ x = 0 := D₁.eq_zero_of_notMem x fun h => hx (subset_closure h)
      show D₁.φ x ^ 2 = 0
      rw [h0]; ring
  have hsU : HasCompactSupport fun z => regU E z ^ 2 :=
    hasCompactSupport_of_zero_outside E.isBounded_Kt.isCompact_closure fun z hz => by
      have h0 : regU E z = 0 := regU_of_notMem fun h => hz (subset_closure h)
      show regU E z ^ 2 = 0
      rw [h0]; ring
  have hfi : Integrable fun x => D₀.φ x ^ 2 := hc₀.integrable_of_hasCompactSupport hs₀
  have hgi : Integrable fun x => D₁.φ x ^ 2 := hc₁.integrable_of_hasCompactSupport hs₁
  have hhi : Integrable fun z => regU E z ^ 2 := hcU.integrable_of_hasCompactSupport hsU
  exact one_le_integral_of_geometric_mean_le ht₀ ht₁ (fun x => sq_nonneg _)
    (fun x => sq_nonneg _) (fun z => sq_nonneg _) hfi hgi hhi
    (sq_rpow_mul_sq_rpow_le_regU_sq hκ hΨ hK₀ hK₁ D₀ D₁ ht₀ ht₁)
    D₀.isRegMinimizer.toIsRegAdmissible.integral_sq
    D₁.isRegMinimizer.toIsRegAdmissible.integral_sq

end PL

end Komlos.Literature.Regularized
