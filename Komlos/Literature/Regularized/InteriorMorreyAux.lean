import Komlos.Literature.Regularized.InteriorWeakEq
import Komlos.Literature.Regularized.DeGiorgiNashAux

/-!
# Globalizing a local weak solution (lane `L3a`, links 4 and 5)

Both remaining links of this lane — the interior Hölder estimate
(`IsWeakLogSol.exists_local_holder`) and the Morrey/Caccioppoli bound
(`IsWeakLogSol.exists_morrey`) — test the equation of `v` with functions built out of `v`
itself, and both want to quote machinery (`Komlos.Literature.MemW0`,
`Komlos.Literature.Regularized.IsDGSub`, `memW0_two_mul_cutoff`,
`MemW0.contDiff_mul_const_add`) that is stated for **globally** weakly differentiable
functions.  `IsWeakLogSol`, on the other hand, only provides a weak gradient *on the open set*
`U` (`HasWeakGradientOn`): near `∂K` the function `v = -log φ` blows up, so no global statement
is available.

This file bridges the two.  The device is a smooth cutoff `ζ` compactly supported in `U`:

* `continuous_smul_of_continuousOn` — the vector-valued companion of
  `Komlos.Literature.Korevaar.continuous_mul_of_continuousOn`: a function continuous on the open
  set `U`, multiplied by a vector field vanishing outside a closed subset of `U`, is continuous
  on all of `ℝ^d`.
* `integrableOn_of_integrableOn_sq_norm` — `L²` on a finite-measure set implies `L¹` there
  (elementary: `a ≤ (a² + 1)/2`).
* `HasWeakGradientOn.hasWeakGradient_mul` — **the localization**: `ζ v` has the *global* weak
  gradient `ζ ∇v + v ∇ζ`.  Test the local identity with `ζ ψ`, which is an admissible test
  function for `U` because `tsupport (ζ ψ) ⊆ tsupport ζ ⊆ U`.
* `IsWeakLogSol.memW0_mul_cutoff` — the packaged form: `ζ v ∈ W₀^{1,2}(tsupport ζ)` with the
  product-rule weak gradient, and `ζ v = v`, `∇(ζ v) = G` on any open set where `ζ ≡ 1`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ m : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-! ### Two elementary helpers -/

/-- A function continuous on an open set `Ω`, multiplied by a *vector field* vanishing outside a
closed subset `S ⊆ Ω`, is continuous on `ℝ^d`.  (Vector-valued version of
`Komlos.Literature.Korevaar.continuous_mul_of_continuousOn`.) -/
theorem continuous_smul_of_continuousOn {Ω : Set (Euc d)} (hΩ : IsOpen Ω) {f : Euc d → ℝ}
    {g : Euc d → Euc d} (hf : ContinuousOn f Ω) (hg : Continuous g) {S : Set (Euc d)}
    (hS : IsClosed S) (hSΩ : S ⊆ Ω) (hgS : ∀ x ∉ S, g x = 0) :
    Continuous fun x => f x • g x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (hf.continuousAt (hΩ.mem_nhds hx)).smul hg.continuousAt
  · have hxS : x ∉ S := fun h => hx (hSΩ h)
    have hev : (fun _ : Euc d => (0 : Euc d)) =ᶠ[𝓝 x] fun z => f z • g z := by
      filter_upwards [hS.isOpen_compl.mem_nhds hxS] with z hz
      rw [hgS z hz, smul_zero]
    exact ContinuousAt.congr continuousAt_const hev

/-- On a set of finite measure, square-integrability implies integrability: `a ≤ (a² + 1)/2`. -/
theorem integrableOn_of_integrableOn_sq_norm {E : Type*} [NormedAddCommGroup E]
    {S : Set (Euc d)} {g : Euc d → E} (hS : volume S ≠ ⊤)
    (hm : AEStronglyMeasurable g (volume.restrict S))
    (h : IntegrableOn (fun x => ‖g x‖ ^ 2) S volume) : IntegrableOn g S volume := by
  have hdom : IntegrableOn (fun x => 2⁻¹ * (‖g x‖ ^ 2 + 1)) S volume := by
    have h1 : IntegrableOn (fun x => ‖g x‖ ^ 2 + 1) S volume :=
      h.add (integrableOn_const hS)
    exact h1.const_mul _
  refine Integrable.mono' hdom hm (Eventually.of_forall fun x => ?_)
  have : ‖g x‖ ≤ 2⁻¹ * (‖g x‖ ^ 2 + 1) := by nlinarith [sq_nonneg (‖g x‖ - 1), norm_nonneg (g x)]
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (g x))] using this

/-! ### The gradient of `η²` -/

/-- `∇(η²) = 2 η ∇η`. -/
theorem gradient_sq {η : Euc d → ℝ} (hη : ContDiff ℝ 1 η) (x : Euc d) :
    gradient (fun z => η z ^ 2) x = (2 * η x) • gradient η x := by
  refine ext_inner_right ℝ fun w => ?_
  have hd : HasFDerivAt η (fderiv ℝ η x) x := (hη.differentiable one_ne_zero x).hasFDerivAt
  rw [← fderiv_apply_eq_inner_gradient, real_inner_smul_left,
    ← fderiv_apply_eq_inner_gradient, (hd.pow 2).fderiv]
  simp
  try ring

/-! ### Localization of a local weak gradient -/

/-- **Localization**: if `G` is a weak gradient of `v` on the open set `U` (in the *local* sense
of `HasWeakGradientOn`), `v` is continuous on `U`, `G` is integrable on the support of a smooth
cutoff `ζ` compactly supported in `U`, then `ζ v` has the **global** weak gradient
`ζ ∇v + v ∇ζ`.

The proof tests the local identity with `ζ ψ`, which is admissible for `U` because
`tsupport (ζ ψ) ⊆ tsupport ζ ⊆ U`, and moves the derivative of `ζ` to the other side. -/
theorem HasWeakGradientOn.hasWeakGradient_mul (hU : IsOpen U) (hvc : ContinuousOn v U)
    (hGm : AEStronglyMeasurable G volume) (hvG : HasWeakGradientOn U v G)
    {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U)
    (hGint : IntegrableOn G (tsupport ζ) volume) :
    HasWeakGradient (fun x => ζ x * v x) (fun x => ζ x • G x + v x • gradient ζ x) := by
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have hgζc : Continuous (gradient ζ) := continuous_gradient hζ1
  have hζ0 : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hgζ0 : ∀ x, x ∉ tsupport ζ → gradient ζ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport hx
  have hdζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx => by
    have := hgζ0 x hx
    ext w
    rw [fderiv_apply_eq_inner_gradient, this, inner_zero_left]
    simp
  obtain ⟨Bζ, hBζ⟩ := hζ.continuous.bounded_above_of_compact_support hζs
  have hBζ0 : 0 ≤ Bζ := (norm_nonneg _).trans (hBζ 0)
  -- `ζ v` is continuous with compact support
  have hcont : Continuous fun x => ζ x * v x := by
    have h := Komlos.Literature.Korevaar.continuous_mul_of_continuousOn hU hvc hζ.continuous
      (isClosed_tsupport ζ) hζU hζ0
    exact h.congr fun x => mul_comm (v x) (ζ x)
  have hcs : HasCompactSupport fun x => ζ x * v x := hζs.mul_right
  -- `v ∇ζ` is continuous with compact support
  have hvgζ : Continuous fun x => v x • gradient ζ x :=
    continuous_smul_of_continuousOn hU hvc hgζc (isClosed_tsupport ζ) hζU hgζ0
  have hvgζs : HasCompactSupport fun x => v x • gradient ζ x :=
    Komlos.Literature.Korevaar.hasCompactSupport_of_zero_outside hζs fun x hx => by
      rw [hgζ0 x hx, smul_zero]
  have hvgζi : Integrable fun x => v x • gradient ζ x :=
    hvgζ.integrable_of_hasCompactSupport hvgζs
  -- `ζ G` is integrable
  have hind : Integrable ((tsupport ζ).indicator G) volume :=
    (integrable_indicator_iff (isClosed_tsupport ζ).measurableSet).2 hGint
  have hζG : Integrable fun x => ζ x • G x := by
    refine Integrable.mono' (hind.norm.const_mul Bζ)
      (hζ.continuous.aestronglyMeasurable.smul hGm) (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hx : x ∈ tsupport ζ
    · rw [Set.indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (by rw [← Real.norm_eq_abs]; exact hBζ x) (norm_nonneg _)
    · rw [hζ0 x hx, abs_zero, zero_mul]
      exact mul_nonneg hBζ0 (norm_nonneg _)
  refine ⟨hcont.locallyIntegrable, (hζG.add hvgζi).locallyIntegrable, ?_⟩
  intro ψ hψ hψs e
  obtain ⟨Bψ, hBψ⟩ := hψ.continuous.bounded_above_of_compact_support hψs
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hχ : ContDiff ℝ ∞ fun x => ζ x * ψ x := hζ.mul hψ
  have hχs : HasCompactSupport fun x => ζ x * ψ x := hψs.mul_left
  have hχU : tsupport (fun x => ζ x * ψ x) ⊆ U := by
    have hsub : Function.support (fun x => ζ x * ψ x) ⊆ tsupport ζ := fun x hx =>
      subset_closure (show ζ x ≠ 0 from fun h => hx (by simp [h]))
    exact (closure_minimal hsub (isClosed_tsupport ζ)).trans hζU
  have key := hvG.integral_eq _ hχ hχs hχU e
  have hder : ∀ x, fderiv ℝ (fun z => ζ z * ψ z) x e =
      ζ x * fderiv ℝ ψ x e + ψ x * fderiv ℝ ζ x e := by
    intro x
    have h : HasFDerivAt (fun z => ζ z * ψ z) (ζ x • fderiv ℝ ψ x + ψ x • fderiv ℝ ζ x) x :=
      (hζ1.differentiable one_ne_zero x).hasFDerivAt.mul
        (hψ1.differentiable one_ne_zero x).hasFDerivAt
    rw [h.fderiv]
    rfl
  have hDψ : Continuous fun x => fderiv ℝ ψ x e :=
    (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDζ : Continuous fun x => fderiv ℝ ζ x e :=
    (hζ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsDψ : ∀ x, x ∉ tsupport ψ → fderiv ℝ ψ x e = 0 := fun x hx => by
    rw [fderiv_apply_eq_inner_gradient, gradient_eq_zero_of_notMem_tsupport hx, inner_zero_left]
  -- the three integrable pieces
  have iA : Integrable fun x => v x * (ζ x * fderiv ℝ ψ x e) := by
    have hc : Continuous fun x => ζ x * v x * fderiv ℝ ψ x e := hcont.mul hDψ
    have hsupp : HasCompactSupport fun x => ζ x * v x * fderiv ℝ ψ x e :=
      Komlos.Literature.Korevaar.hasCompactSupport_of_zero_outside hψs fun x hx => by
        rw [hsDψ x hx, mul_zero]
    exact (hc.integrable_of_hasCompactSupport hsupp).congr
      (Eventually.of_forall fun x => by ring)
  have iB : Integrable fun x => v x * (ψ x * fderiv ℝ ζ x e) := by
    have hvd : Continuous fun x => v x * fderiv ℝ ζ x e :=
      Komlos.Literature.Korevaar.continuous_mul_of_continuousOn hU hvc hDζ
        (isClosed_tsupport ζ) hζU fun x hx => by rw [hdζ0 x hx]; simp
    have hc : Continuous fun x => v x * fderiv ℝ ζ x e * ψ x := hvd.mul hψ.continuous
    have hsupp : HasCompactSupport fun x => v x * fderiv ℝ ζ x e * ψ x :=
      Komlos.Literature.Korevaar.hasCompactSupport_of_zero_outside hψs fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    exact (hc.integrable_of_hasCompactSupport hsupp).congr
      (Eventually.of_forall fun x => by ring)
  have iD : Integrable fun x => ⟪G x, e⟫ * (ζ x * ψ x) := by
    have hbase : Integrable fun x => ⟪e, ζ x • G x⟫ :=
      Integrable.const_inner (𝕜 := ℝ) e hζG
    refine Integrable.mono' (hbase.norm.const_mul Bψ)
      ((hGm.inner (aestronglyMeasurable_const (b := e))).mul
        (hζ.continuous.aestronglyMeasurable.mul hψ.continuous.aestronglyMeasurable))
      (Eventually.of_forall fun x => ?_)
    have hcomm : ⟪G x, e⟫ * (ζ x * ψ x) = ⟪e, ζ x • G x⟫ * ψ x := by
      rw [real_inner_smul_right, real_inner_comm]
      ring
    rw [hcomm, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hBψ x) (norm_nonneg _)
  -- the computation
  have e1 : (∫ x, v x * fderiv ℝ (fun z => ζ z * ψ z) x e) =
      (∫ x, v x * (ζ x * fderiv ℝ ψ x e)) + ∫ x, v x * (ψ x * fderiv ℝ ζ x e) := by
    rw [← integral_add iA iB]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hder]; ring)
  show (∫ x, ζ x * v x * fderiv ℝ ψ x e) =
    -∫ x, ⟪ζ x • G x + v x • gradient ζ x, e⟫ * ψ x
  have e2 : (∫ x, ⟪ζ x • G x + v x • gradient ζ x, e⟫ * ψ x) =
      (∫ x, ⟪G x, e⟫ * (ζ x * ψ x)) + ∫ x, v x * (ψ x * fderiv ℝ ζ x e) := by
    rw [← integral_add iD iB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [inner_add_left, real_inner_smul_left, fderiv_apply_eq_inner_gradient]
    ring
  have e3 : (∫ x, ζ x * v x * fderiv ℝ ψ x e) = ∫ x, v x * (ζ x * fderiv ℝ ψ x e) :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e3, e2]
  rw [e1] at key
  linarith

/-! ### The packaged globalization -/

/-- **`ζ v ∈ W₀^{1,2}(tsupport ζ)`**, with the product-rule weak gradient, for a smooth cutoff
`ζ` supported in a closed ball inside `U`.  This is the form the two remaining links of the lane
consume: it turns the *local* data of `IsWeakLogSol` into a genuine Sobolev function, to which
`Komlos.Literature.MemW0.contDiff_mul_const_add` and the De Giorgi class machinery apply. -/
theorem IsWeakLogSol.memW0_mul_cutoff (hsol : IsWeakLogSol κ m Ψ U v G)
    {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U)
    {y : Euc d} {s : ℝ} (hbs : Metric.closedBall y s ⊆ U)
    (hζb : tsupport ζ ⊆ Metric.closedBall y s) :
    MemW0 2 (tsupport ζ) (fun x => ζ x * v x) ∧
      HasWeakGradient (fun x => ζ x * v x) (fun x => ζ x • G x + v x • gradient ζ x) := by
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have hζ0 : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hgζ0 : ∀ x, x ∉ tsupport ζ → gradient ζ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport hx
  obtain ⟨Bζ, hBζ⟩ := hζ.continuous.bounded_above_of_compact_support hζs
  have hBζ0 : 0 ≤ Bζ := (norm_nonneg _).trans (hBζ 0)
  have hGsq : IntegrableOn (fun x => ‖G x‖ ^ 2) (tsupport ζ) volume :=
    (hsol.integrableOn_sq y s hbs).mono_set hζb
  have hGint : IntegrableOn G (tsupport ζ) volume :=
    integrableOn_of_integrableOn_sq_norm hζs.measure_lt_top.ne
      hsol.measurable_grad.aestronglyMeasurable.restrict hGsq
  have hwg : HasWeakGradient (fun x => ζ x * v x) (fun x => ζ x • G x + v x • gradient ζ x) :=
    HasWeakGradientOn.hasWeakGradient_mul hsol.isOpen hsol.continuousOn
      hsol.measurable_grad.aestronglyMeasurable hsol.hasWeakGradientOn hζ hζs hζU hGint
  -- `ζ v` is continuous with compact support
  have hcont : Continuous fun x => ζ x * v x := by
    have h := Komlos.Literature.Korevaar.continuous_mul_of_continuousOn hsol.isOpen
      hsol.continuousOn hζ.continuous (isClosed_tsupport ζ) hζU hζ0
    exact h.congr fun x => mul_comm (v x) (ζ x)
  have hcs : HasCompactSupport fun x => ζ x * v x := hζs.mul_right
  -- the two halves of the gradient
  have hζG2 : MemLp (fun x => ζ x • G x) (ENNReal.ofReal (2 : ℝ)) volume := by
    refine memLp_two_of_integrableOn_sq_norm (B := tsupport ζ)
      (hζ.continuous.aestronglyMeasurable.smul
        hsol.measurable_grad.aestronglyMeasurable) ?_ ?_
    · refine Integrable.mono' (hGsq.const_mul (Bζ ^ 2))
        (((hζ.continuous.aestronglyMeasurable.smul
          hsol.measurable_grad.aestronglyMeasurable).norm.pow 2).restrict)
        (Eventually.of_forall fun x => ?_)
      have h1 : ‖ζ x • G x‖ ^ 2 = ζ x ^ 2 * ‖G x‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have h2 : ζ x ^ 2 ≤ Bζ ^ 2 := by
        have := hBζ x
        rw [Real.norm_eq_abs] at this
        nlinarith [abs_nonneg (ζ x), sq_abs (ζ x)]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), h1]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    · intro x hx
      rw [hζ0 x hx, zero_smul]
  have hvgζ : Continuous fun x => v x • gradient ζ x :=
    continuous_smul_of_continuousOn hsol.isOpen hsol.continuousOn (continuous_gradient hζ1)
      (isClosed_tsupport ζ) hζU hgζ0
  have hvgζs : HasCompactSupport fun x => v x • gradient ζ x :=
    Komlos.Literature.Korevaar.hasCompactSupport_of_zero_outside hζs fun x hx => by
      rw [hgζ0 x hx, smul_zero]
  have hvgζ2 : MemLp (fun x => v x • gradient ζ x) (ENNReal.ofReal (2 : ℝ)) volume :=
    hvgζ.memLp_of_hasCompactSupport hvgζs
  refine ⟨⟨hcont.memLp_of_hasCompactSupport hcs,
    Eventually.of_forall fun x hx => by rw [hζ0 x hx, zero_mul], ⟨_, hwg, ?_⟩⟩, hwg⟩
  exact hζG2.add hvgζ2

end Komlos.Literature.Regularized
