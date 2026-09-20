import Komlos.Literature.PLaplacian.RegularityHarnack

/-!
# Scale-invariant tools for the Hölder continuity of weak eigensolutions

Auxiliary facts for `Komlos.Literature.PLaplacian.RegularityHolder` (De Giorgi–Nash–Moser Hölder
continuity of bounded weak solutions of `-div a(∇u) = λ u^{p-1}`; Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Theorem 8.22; towards Mosconi–Riey–Squassina 2024,
Proposition 4.5, paper Appendix A, *Eigenfunction inputs*). Oscillation decay needs constants that
do not depend on the radius of the ball, so the Sobolev inequality and the cutoffs are rescaled
explicitly.

## Main results

* `lintegral_comp_add_smul'` — `∫⁻ G(x₀ + R y) dy = R^{-d} ∫⁻ G` (no measurability needed).
* `exists_rescaled_cutoff` — cutoffs `η` with `η = 1` on `closedBall x₀ (aR)`,
  `tsupport η ⊆ closedBall x₀ (bR)` and `‖∇η‖ ≤ G / R`, with `G` independent of `x₀` and `R`.
* `HasWeakGradient.comp_add_right'`, `MemW0.comp_add_smul` — translates and rescalings of
  `W₀^{1,p}` functions.
* `exists_sobolev_ball` — **the Sobolev inequality on balls with explicit scaling**:
  `∫ |w|^{κp} ≤ C R^d (R^{p-d})^κ (∫ |∇w|^p)^κ` for `w ∈ W₀^{1,p}(closedBall x₀ R)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Change of variables and gradients -/

/-- `∫⁻ G(x₀ + R • y) dy = (R^d)⁻¹ ∫⁻ G` for `R > 0`, for any `G`. -/
theorem lintegral_comp_add_smul' (G : Euc d → ℝ≥0∞) (x₀ : Euc d) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y, G (x₀ + R • y) = ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x, G x := by
  have h1 : ∫⁻ y, G (x₀ + R • y) = ∫⁻ y, G (x₀ + R⁻¹⁻¹ • ((y + x₀) - x₀)) := by
    congr 1
    funext y
    rw [inv_inv, add_sub_cancel_right]
  rw [h1, lintegral_add_right_eq_self (fun y => G (x₀ + R⁻¹⁻¹ • (y - x₀))) x₀,
    lintegral_comp_dilate G x₀ (inv_pos.2 hR), inv_pow]

/-- `‖∇f(x)‖ = ‖Df(x)‖`. -/
theorem norm_gradient_eq_norm_fderiv (f : Euc d → ℝ) (x : Euc d) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]

/-- **Rescaled cutoffs**: for `0 < a < b` there is `G ≥ 0` such that for every centre `x₀` and
radius `R > 0` there is a smooth compactly supported `η` with `0 ≤ η ≤ 1`, `η = 1` on
`closedBall x₀ (aR)`, `tsupport η ⊆ closedBall x₀ (bR)` and `‖∇η‖ ≤ G / R` (a fixed bump
composed with `x ↦ R⁻¹ (x - x₀)`). -/
theorem exists_rescaled_cutoff {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (x₀ : Euc d) (R : ℝ), 0 < R → ∃ η : Euc d → ℝ, ContDiff ℝ ∞ η ∧
      HasCompactSupport η ∧ tsupport η ⊆ Metric.closedBall x₀ (b * R) ∧ (∀ x, 0 ≤ η x) ∧
      (∀ x, η x ≤ 1) ∧ (∀ x ∈ Metric.closedBall x₀ (a * R), η x = 1) ∧
      ∀ x, ‖gradient η x‖ ≤ G / R := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ContDiffBump (0 : Euc d), b₀.rIn = a ∧ b₀.rOut = b :=
    ⟨⟨a, b, ha, hab⟩, rfl, rfl⟩
  obtain ⟨G, hG⟩ := ((b₀.contDiff (n := 1)).continuous_fderiv
    one_ne_zero).bounded_above_of_compact_support (b₀.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  refine ⟨G, hG0, fun x₀ R hR => ?_⟩
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  have hsupp : Function.support (fun x => b₀ (R⁻¹ • (x - x₀))) ⊆ Metric.ball x₀ (b * R) := by
    intro x hx
    have h1 : R⁻¹ • (x - x₀) ∈ Function.support b₀ := hx
    rw [b₀.support_eq, hb₀.2, Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg hRi] at h1
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖x - x₀‖ = R * (R⁻¹ * ‖x - x₀‖) := by field_simp
      _ < R * b := mul_lt_mul_of_pos_left h1 hR
      _ = b * R := mul_comm _ _
  have htsupp : tsupport (fun x => b₀ (R⁻¹ • (x - x₀))) ⊆ Metric.closedBall x₀ (b * R) :=
    closure_minimal (hsupp.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  refine ⟨fun x => b₀ (R⁻¹ • (x - x₀)), ?_, ?_, htsupp, fun x => b₀.nonneg' _,
    fun x => b₀.le_one, fun x hx => ?_, fun x => ?_⟩
  · exact b₀.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul R⁻¹)
  · exact (isCompact_closedBall x₀ (b * R)).of_isClosed_subset (isClosed_tsupport _) htsupp
  · refine b₀.one_of_mem_closedBall ?_
    rw [hb₀.1, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hRi]
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    calc R⁻¹ * ‖x - x₀‖ ≤ R⁻¹ * (a * R) := mul_le_mul_of_nonneg_left hx hRi
      _ = a := by field_simp
  · have h1 : HasFDerivAt (fun x : Euc d => R⁻¹ • (x - x₀))
        (R⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) x :=
      ((hasFDerivAt_id x).sub_const x₀).const_smul R⁻¹
    have h2 : HasFDerivAt (fun x => b₀ (R⁻¹ • (x - x₀)))
        ((fderiv ℝ b₀ (R⁻¹ • (x - x₀))).comp (R⁻¹ • ContinuousLinearMap.id ℝ (Euc d))) x :=
      (((b₀.contDiff (n := 1)).differentiable one_ne_zero) _).hasFDerivAt.comp x h1
    rw [norm_gradient_eq_norm_fderiv, h2.fderiv]
    have h3 : ‖R⁻¹ • ContinuousLinearMap.id ℝ (Euc d)‖ ≤ R⁻¹ := by
      refine (norm_smul_le R⁻¹ (ContinuousLinearMap.id ℝ (Euc d))).trans ?_
      rw [Real.norm_of_nonneg hRi]
      exact mul_le_of_le_one_right hRi ContinuousLinearMap.norm_id_le
    calc ‖(fderiv ℝ b₀ (R⁻¹ • (x - x₀))).comp (R⁻¹ • ContinuousLinearMap.id ℝ (Euc d))‖
        ≤ ‖fderiv ℝ b₀ (R⁻¹ • (x - x₀))‖ * ‖R⁻¹ • ContinuousLinearMap.id ℝ (Euc d)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ G * R⁻¹ := mul_le_mul (hG _) h3 (norm_nonneg _) hG0
      _ = G / R := (div_eq_mul_inv G R).symm

/-! ### Translates and rescalings of Sobolev functions -/

/-- `MemLp.const_smul` with the product written as a lambda (generic domain). -/
theorem memLp_smul_fun {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : ℝ≥0∞} {f : α → E} (hf : MemLp f q μ) (c : ℝ) :
    MemLp (fun x => c • f x) q μ :=
  hf.const_smul c

/-- **Weak gradients of translates**: `∇[f(· + a)] = (∇f)(· + a)`. -/
theorem HasWeakGradient.comp_add_right' {f : Euc d → ℝ} {g : Euc d → Euc d}
    (hfg : HasWeakGradient f g) {q : ℝ} (hq : 1 ≤ q) (hf : MemLp f (ENNReal.ofReal q))
    (hg : MemLp g (ENNReal.ofReal q)) (a : Euc d) :
    HasWeakGradient (fun x => f (x + a)) (fun x => g (x + a)) := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq
  have hmp := measurePreserving_add_right (volume : Measure (Euc d)) a
  refine ⟨(hf.comp_measurePreserving hmp).locallyIntegrable hq1,
    (hg.comp_measurePreserving hmp).locallyIntegrable hq1, fun ψ hψ hψs v => ?_⟩
  have hψ' : ContDiff ℝ ∞ (fun y => ψ (y + -a)) := hψ.comp (contDiff_id.add contDiff_const)
  have hψ's : HasCompactSupport (fun y => ψ (y + -a)) := by
    have h := hψs.comp_homeomorph (Homeomorph.addRight (-a))
    have he : ψ ∘ Homeomorph.addRight (-a) = fun y => ψ (y + -a) := rfl
    rwa [he] at h
  have key := hfg.integral_mul_fderiv _ hψ' hψ's v
  have e1 : ∫ x, f (x + a) * fderiv ℝ ψ x v =
      ∫ y, f y * fderiv ℝ (fun y => ψ (y + -a)) y v := by
    rw [← integral_add_right_eq_self (fun y => f y * fderiv ℝ (fun y => ψ (y + -a)) y v) a]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show f (x + a) * fderiv ℝ ψ x v = f (x + a) * fderiv ℝ (fun y => ψ (y + -a)) (x + a) v
    rw [fderiv_comp_add_right, add_neg_cancel_right]
  have e2 : ∫ x, inner ℝ (g (x + a)) v * ψ x = ∫ y, inner ℝ (g y) v * ψ (y + -a) := by
    rw [← integral_add_right_eq_self (fun y => inner ℝ (g y) v * ψ (y + -a)) a]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show inner ℝ (g (x + a)) v * ψ x = inner ℝ (g (x + a)) v * ψ (x + a + -a)
    rw [add_neg_cancel_right]
  show ∫ x, f (x + a) * fderiv ℝ ψ x v = -∫ x, inner ℝ (g (x + a)) v * ψ x
  rw [e1, e2, key]

/-- **Rescaling `W₀^{1,p}` of a ball to the unit ball**: if `w ∈ W₀^{1,p}(closedBall x₀ R)` then
`y ↦ w(x₀ + R y)` lies in `W₀^{1,p}(closedBall 0 1)` with weak gradient `R (∇w)(x₀ + R y)`. -/
theorem MemW0.comp_add_smul {p : ℝ} (hp : 1 < p) {x₀ : Euc d} {R : ℝ} (hR : 0 < R)
    {w : Euc d → ℝ} (hw : MemW0 p (Metric.closedBall x₀ R) w) :
    MemW0 p (Metric.closedBall 0 1) (fun y => w (x₀ + R • y)) ∧
      weakGrad (fun y => w (x₀ + R • y)) =ᵐ[volume] fun y => R • weakGrad w (x₀ + R • y) := by
  have hp0 : 0 < p := by linarith
  have hRi : 0 < R⁻¹ := inv_pos.2 hR
  have hdil := hw.hasWeakGradient.comp_dilate hp.le hw.memLp hw.memLp_weakGrad x₀ hRi
  have hm1 := memLp_comp_dilate hp0 hw.memLp x₀ hRi
  have hm2 := memLp_smul_fun (memLp_comp_dilate hp0 hw.memLp_weakGrad x₀ hRi) R⁻¹⁻¹
  have htr := hdil.comp_add_right' hp.le hm1 hm2 x₀
  have hmp := measurePreserving_add_right (volume : Measure (Euc d)) x₀
  have hf : (fun y => w (x₀ + R⁻¹⁻¹ • (y + x₀ - x₀))) = fun y => w (x₀ + R • y) := by
    funext y
    rw [inv_inv, add_sub_cancel_right]
  have hg : (fun y => R⁻¹⁻¹ • weakGrad w (x₀ + R⁻¹⁻¹ • (y + x₀ - x₀))) =
      fun y => R • weakGrad w (x₀ + R • y) := by
    funext y
    rw [inv_inv, add_sub_cancel_right]
  have htr' : HasWeakGradient (fun y => w (x₀ + R • y))
      (fun y => R • weakGrad w (x₀ + R • y)) := by
    simpa only [inv_inv, add_sub_cancel_right] using htr
  have hvp : MemLp (fun y => w (x₀ + R • y)) (ENNReal.ofReal p) := by
    rw [← hf]
    exact hm1.comp_measurePreserving hmp
  have hgp : MemLp (fun y => R • weakGrad w (x₀ + R • y)) (ENNReal.ofReal p) := by
    rw [← hg]
    exact hm2.comp_measurePreserving hmp
  have hqmp : Measure.QuasiMeasurePreserving (fun y : Euc d => x₀ + R • y) volume volume :=
    (measurePreserving_add_left volume x₀).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul volume hR.ne')
  refine ⟨⟨hvp, ?_, _, htr', hgp⟩, htr'.weakGrad_ae_eq⟩
  filter_upwards [hqmp.ae hw.ae_eq_zero] with y hy hy1
  refine hy ?_
  intro hmem
  refine hy1 ?_
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg hR.le] at hmem
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg y]

/-- From `a⁻¹ X ≤ C (b Y)^κ` deduce `X ≤ C (a b^κ) Y^κ` in `ℝ≥0∞` (`a > 0`, `b, κ ≥ 0`). -/
theorem le_mul_ofReal_mul_rpow_of_le {X Y C : ℝ≥0∞} {a b κ : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hκ : 0 ≤ κ) (h : ENNReal.ofReal a⁻¹ * X ≤ C * (ENNReal.ofReal b * Y) ^ κ) :
    X ≤ C * ENNReal.ofReal (a * b ^ κ) * Y ^ κ := by
  have h1 : X = ENNReal.ofReal a * (ENNReal.ofReal a⁻¹ * X) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one,
      one_mul]
  rw [h1]
  refine (mul_le_mul_right h _).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hκ, ENNReal.ofReal_rpow_of_nonneg hb hκ,
    ENNReal.ofReal_mul ha.le]
  ring

/-- **The Sobolev inequality on balls with explicit scaling**: there are `κ > 1` and `C < ∞` such
that for every ball `closedBall x₀ R` and `w ∈ W₀^{1,p}(closedBall x₀ R)`,
`∫ |w|^{κp} ≤ C R^d (R^p R^{-d})^κ (∫ |∇w|^p)^κ` (`sobolev_inequality` on the unit ball applied to
the rescaled function `MemW0.comp_add_smul`). -/
theorem exists_sobolev_ball (hd : 0 < d) {p : ℝ} (hp : 1 < p) :
    ∃ κ : ℝ, 1 < κ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (x₀ : Euc d) (R : ℝ), 0 < R → ∀ w : Euc d → ℝ,
      MemW0 p (Metric.closedBall x₀ R) w →
      ∫⁻ x, ‖w x‖ₑ ^ (κ * p) ≤
        C * ENNReal.ofReal (R ^ d * (R ^ p * (R ^ d)⁻¹) ^ κ) *
          (∫⁻ x, ‖weakGrad w x‖ₑ ^ p) ^ κ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨κ, hκ, C₀, hC₀, hSob⟩ :=
    sobolev_inequality hd hp (Metric.isBounded_closedBall (x := (0 : Euc d)) (r := 1))
  have hκ0 : 0 < κ := by linarith
  have hκp : 0 < κ * p := mul_pos hκ0 hp0
  refine ⟨κ, hκ, C₀ ^ (κ * p), ENNReal.rpow_ne_top_of_nonneg hκp.le hC₀,
    fun x₀ R hR w hw => ?_⟩
  obtain ⟨hv, hvg⟩ := hw.comp_add_smul hp hR
  have h1 := lintegral_rpow_le_of_eLpNorm_le hp0 hκ0 (hSob _ hv)
  have hRd : 0 < R ^ d := pow_pos hR d
  have hL : ∫⁻ y, ‖w (x₀ + R • y)‖ₑ ^ (κ * p) =
      ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x, ‖w x‖ₑ ^ (κ * p) :=
    lintegral_comp_add_smul' (fun x => ‖w x‖ₑ ^ (κ * p)) x₀ hR
  have hG : ∫⁻ y, ‖weakGrad (fun y => w (x₀ + R • y)) y‖ₑ ^ p =
      ENNReal.ofReal (R ^ p * (R ^ d)⁻¹) * ∫⁻ x, ‖weakGrad w x‖ₑ ^ p := by
    have hcongr : ∫⁻ y, ‖weakGrad (fun y => w (x₀ + R • y)) y‖ₑ ^ p =
        ∫⁻ y, ‖R • weakGrad w (x₀ + R • y)‖ₑ ^ p :=
      lintegral_congr_ae (hvg.mono fun y hy => by simp only [hy])
    have e : ∀ y, ‖R • weakGrad w (x₀ + R • y)‖ₑ ^ p =
        ENNReal.ofReal (R ^ p) * ‖weakGrad w (x₀ + R • y)‖ₑ ^ p := fun y => by
      rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, Real.enorm_eq_ofReal hR.le,
        ENNReal.ofReal_rpow_of_nonneg hR.le hp0.le]
    rw [hcongr, lintegral_congr e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_comp_add_smul' (fun x => ‖weakGrad w x‖ₑ ^ p) x₀ hR, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
  rw [hL, hG] at h1
  exact le_mul_ofReal_mul_rpow_of_le hRd
    (mul_nonneg (Real.rpow_nonneg hR.le _) (inv_nonneg.2 hRd.le)) hκ0.le h1

/-! ### Level functions `σ (u - k)` -/

/-- The level function `σ (t - k)` clamped to `[0, om]`. -/
noncomputable def levelClamp (σ k om t : ℝ) : ℝ := max 0 (min (σ * (t - k)) om)

theorem continuous_levelClamp (σ k om : ℝ) : Continuous (levelClamp σ k om) :=
  continuous_const.max ((continuous_const.mul (continuous_id.sub continuous_const)).min
    continuous_const)

theorem levelClamp_mem {σ k om : ℝ} (hom : 0 ≤ om) (t : ℝ) : levelClamp σ k om t ∈ Icc 0 om :=
  ⟨le_max_left _ _, max_le hom (min_le_right _ _)⟩

theorem levelClamp_eq {σ k om t : ℝ} (ht : σ * (t - k) ∈ Icc 0 om) :
    levelClamp σ k om t = σ * (t - k) := by
  unfold levelClamp
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- On the segment from `k` to `t`, `σ (s - k)` stays in `[0, σ (t - k)]` (for `σ = ±1`). -/
theorem mem_Icc_of_mem_uIcc_level {σ k t s : ℝ} (hσ : σ = 1 ∨ σ = -1) (ht : 0 ≤ σ * (t - k))
    (hs : s ∈ uIcc k t) : σ * (s - k) ∈ Icc 0 (σ * (t - k)) := by
  rcases hσ with rfl | rfl
  · have htk : k ≤ t := by linarith
    rw [uIcc_of_le htk] at hs
    constructor <;> linarith [hs.1, hs.2]
  · have htk : t ≤ k := by linarith
    rw [uIcc_of_ge htk] at hs
    constructor <;> linarith [hs.1, hs.2]

/-- **Chain rule for profiles of a level function**: for `f ∈ W₀^{1,p}(K)`, `σ = ±1`, `k`,
`om ≥ 0` and `Φ` with a derivative `φ'` on `[0, om]`, continuous there, there are `c` and a `C¹`
function `G` with `c + G(t) = Φ(σ(t - k))` whenever `σ(t - k) ∈ [0, om]`, `G ∘ f ∈ W₀^{1,p}(K)`
and `∇(G ∘ f) = σ φ'(levelClamp f) ∇f`. -/
theorem memW0_comp_level {p : ℝ} (hp : 1 < p) {K : Set (Euc d)} {f : Euc d → ℝ}
    (hf : MemW0 p K f) {σ k om : ℝ} (hσ : σ = 1 ∨ σ = -1) (hom : 0 ≤ om) {Φ φ' : ℝ → ℝ}
    (hΦ : ∀ t ∈ Icc 0 om, HasDerivAt Φ (φ' t) t) (hφ' : ContinuousOn φ' (Icc 0 om)) :
    ∃ c : ℝ, ∃ G : ℝ → ℝ, (∀ t, σ * (t - k) ∈ Icc 0 om → c + G t = Φ (σ * (t - k))) ∧
      MemW0 p K (fun x => G (f x)) ∧
      weakGrad (fun x => G (f x)) =ᵐ[volume]
        fun x => (σ * φ' (levelClamp σ k om (f x))) • weakGrad f x := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → ℝ, γ = fun s => σ * φ' (levelClamp σ k om s) := ⟨_, rfl⟩
  have hγc : Continuous γ := by
    rw [hγ]
    exact continuous_const.mul
      (hφ'.comp_continuous (continuous_levelClamp σ k om) (levelClamp_mem hom))
  obtain ⟨Lφ, hLφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ'
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun t => ∫ s in (0 : ℝ)..t, γ s := ⟨_, rfl⟩
  have hGd : ∀ t, HasDerivAt G (γ t) t := fun t => by
    rw [hG]
    exact intervalIntegral.integral_hasDerivAt_right (hγc.intervalIntegrable _ _)
      (hγc.stronglyMeasurableAtFilter _ _) hγc.continuousAt
  have hderiv : deriv G = γ := funext fun t => (hGd t).deriv
  have hGc : ContDiff ℝ 1 G := contDiff_one_iff_deriv.2
    ⟨fun t => (hGd t).differentiableAt, by rw [hderiv]; exact hγc⟩
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hGL : ∀ t, |deriv G t| ≤ Lφ := fun t => by
    rw [hderiv, hγ]
    show |σ * φ' (levelClamp σ k om t)| ≤ Lφ
    rw [abs_mul, hσ1, one_mul, ← Real.norm_eq_abs]
    exact hLφ _ (levelClamp_mem hom t)
  have hG0 : G 0 = 0 := by
    rw [hG]
    exact intervalIntegral.integral_same
  obtain ⟨hGw, hGg⟩ := memW0_comp hp hf hGc hG0 hGL
  refine ⟨Φ 0 - G k, G, fun t ht => ?_, hGw, hGg.mono fun x hx => ?_⟩
  · have hint : ∫ s in k..t, γ s = Φ (σ * (t - k)) - Φ (σ * (k - k)) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Φ (σ * (s - k)))
        (fun s hs => ?_) (hγc.intervalIntegrable _ _)
      have hs' := mem_Icc_of_mem_uIcc_level hσ ht.1 hs
      have hs'' : σ * (s - k) ∈ Icc 0 om := ⟨hs'.1, hs'.2.trans ht.2⟩
      have h1 : HasDerivAt (fun s => σ * (s - k)) σ s := by
        simpa using ((hasDerivAt_id s).sub_const k).const_mul σ
      have h2 : HasDerivAt (fun s => Φ (σ * (s - k))) (φ' (σ * (s - k)) * σ) s :=
        (hΦ _ hs'').comp s h1
      rw [hγ]
      show HasDerivAt (fun s => Φ (σ * (s - k))) (σ * φ' (levelClamp σ k om s)) s
      rw [levelClamp_eq hs'']
      exact h2.congr_deriv (mul_comm _ _)
    have hsub : G t - G k = ∫ s in k..t, γ s := by
      rw [hG]
      exact intervalIntegral.integral_interval_sub_left (hγc.intervalIntegrable _ _)
        (hγc.intervalIntegrable _ _)
    rw [sub_self, mul_zero] at hint
    linarith
  · rw [hx, hderiv, hγ]

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- A continuous profile of the clamped level function of `u` is a.e.-strongly measurable and
bounded. -/
theorem comp_levelClamp (hu : IsWeakEigensolution p F K lam u) {σ k om : ℝ} (hom : 0 ≤ om)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 om)) :
    AEStronglyMeasurable (fun x => g (levelClamp σ k om (u x))) volume ∧
      ∃ C, ∀ x, |g (levelClamp σ k om (u x))| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine ⟨(hg.comp_continuous (continuous_levelClamp σ k om)
    (levelClamp_mem hom)).comp_aestronglyMeasurable hu.memW0.memLp.aestronglyMeasurable, C,
    fun x => ?_⟩
  rw [← Real.norm_eq_abs]
  exact hC _ (levelClamp_mem hom _)

/-- **Testing the equation with `η^m Φ(σ(u - k))`**, where `σ(u - k) ∈ [0, om]` a.e. on the support
of `η`: `σ ∫ η^m φ'(w) F(∇u)^p + ∫ Φ(w) m η^{m-1} ⟪a(∇u), ∇η⟫ = λ ∫ u^{p-1} η^m Φ(w)` with `w` the
clamped level function. -/
theorem integral_test_level_eq (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {σ k om : ℝ} (hσ : σ = 1 ∨ σ = -1) (hom : 0 ≤ om)
    {Φ φ' : ℝ → ℝ} (hΦ : ∀ t ∈ Icc 0 om, HasDerivAt Φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Icc 0 om)) {m : ℕ} (hm0 : m ≠ 0) {η : Euc d → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (hlevel : ∀ᵐ x, x ∈ tsupport η → σ * (u x - k) ∈ Icc 0 om) :
    σ * (∫ x, η x ^ m * φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p) +
        ∫ x, Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1)) *
          ⟪flux p F (weakGrad u x), gradient η x⟫ =
      lam * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  obtain ⟨c, G, hcG, hGw, hGg⟩ := memW0_comp_level hp hu.memW0 hσ hom hΦ hφ'
  obtain ⟨hζ, hζs, hζt⟩ := cutoff_pow hη hηs hm0
  obtain ⟨hψ, hψg⟩ := hGw.contDiff_mul_const_add hζ hζs (hζt.trans hηK) c
  have h := hu.weakEq _ hψ
  have hΦc : ContinuousOn Φ (Icc 0 om) := fun t ht => (hΦ t ht).continuousAt.continuousWithinAt
  obtain ⟨hΦm, CΦ, hCΦ⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hΦc
  obtain ⟨hφm, Cφ, hCφ⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hφ'
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hAη0 : 0 ≤ Aη := (norm_nonneg _).trans (hAη 0)
  have hηpow : ∀ n : ℕ, ∀ x, |η x ^ n| ≤ Aη ^ n := fun n x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [← Real.norm_eq_abs]; exact hAη x) n
  have i1 : Integrable fun x => σ * (η x ^ m * φ' (levelClamp σ k om (u x)) *
      F (weakGrad u x) ^ p) :=
    (hu.integrable_mul_rpow hp hF (hζ.continuous.aestronglyMeasurable.mul hφm)
      (B := Aη ^ m * Cφ) fun x => by
        show |η x ^ m * φ' (levelClamp σ k om (u x))| ≤ Aη ^ m * Cφ
        rw [abs_mul]
        exact mul_le_mul (hηpow m x) (hCφ x) (abs_nonneg _) (pow_nonneg hAη0 m)).const_mul σ
  have i2 : Integrable fun x => Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1)) *
      ⟪flux p F (weakGrad u x), gradient η x⟫ :=
    hu.integrable_mul_inner_flux_of_hasCompactSupport hp hF (continuous_gradient hη1)
      (hasCompactSupport_gradient hηs)
      (b := fun x => Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1)))
      (hΦm.mul (continuous_const.mul (hη.continuous.pow _)).aestronglyMeasurable)
      (B := CΦ * ((m : ℝ) * Aη ^ (m - 1))) fun x => by
        show |Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1))| ≤
          CΦ * ((m : ℝ) * Aη ^ (m - 1))
        rw [abs_mul, abs_mul, Nat.abs_cast]
        exact mul_le_mul (hCΦ x) (mul_le_mul_of_nonneg_left (hηpow (m - 1) x)
          (Nat.cast_nonneg m)) (by positivity) ((abs_nonneg _).trans (hCΦ x))
  have hL : ∀ᵐ x, ⟪flux p F (weakGrad u x), weakGrad (fun x => η x ^ m * (c + G (u x))) x⟫ =
      σ * (η x ^ m * φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p) +
        Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1)) *
          ⟪flux p F (weakGrad u x), gradient η x⟫ := by
    filter_upwards [hψg, hGg, hlevel] with x h1 h2 h3
    rw [h1, h2, gradient_pow_apply (hη1.differentiable one_ne_zero x) m]
    by_cases hx : x ∈ tsupport η
    · have h4 := h3 hx
      rw [hcG _ h4, levelClamp_eq h4]
      simp only [inner_add_right, real_inner_smul_right, hF.inner_flux_self_eq_rpow hp]
      ring
    · have hg0 : gradient η x = 0 := gradient_eq_zero_of_notMem_tsupport hx
      have he0 : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hg0, he0, zero_pow hm0]
  have hR : ∫ x, u x ^ (p - 1) * (η x ^ m * (c + G (u x))) =
      ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) := by
    refine integral_congr_ae (hlevel.mono fun x h3 => ?_)
    show u x ^ (p - 1) * (η x ^ m * (c + G (u x))) =
      u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x)))
    by_cases hx : x ∈ tsupport η
    · rw [hcG _ (h3 hx), levelClamp_eq (h3 hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx, zero_pow hm0]
  rw [← integral_const_mul, ← integral_add i1 i2, ← integral_congr_ae hL, h, hR]

/-- **The energy inequality for level functions with a bounded right-hand side** (`σ = 1`,
`w = u - k`, or `σ = -1`, `w = k - u`): if `σ(u - k) ∈ [0, om]` a.e. on the support of `η`, `Φ ≥ 0`
has a nonpositive derivative `φ'` on `[0, om]` and `Φ^p ≤ Θ |φ'|^{p-1}`, then
`∫ η^m |φ'(w)| F(∇u)^p ≤ 2^p (mL)^p ∫ η^{m-p} |∇η|^p Θ(w) + 2 |λ| S^{p-1} ∫ η^m Φ(w)`
(`integral_test_level_eq` and `caccioppoli_pointwise_weight`; `|λ u^{p-1}| ≤ |λ| S^{p-1}`). -/
theorem energy_le_level (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (huS : ∀ x, u x ∈ Icc 0 S)
    {σ k om : ℝ} (hσ : σ = 1 ∨ σ = -1) (hom : 0 ≤ om) {Φ φ' Θ : ℝ → ℝ}
    (hΦ : ∀ t ∈ Icc 0 om, HasDerivAt Φ (φ' t) t) (hφ' : ContinuousOn φ' (Icc 0 om))
    (hΘc : ContinuousOn Θ (Icc 0 om)) (hΦ0 : ∀ t ∈ Icc 0 om, 0 ≤ Φ t)
    (hφ'0 : ∀ t ∈ Icc 0 om, φ' t ≤ 0) (hΘ0 : ∀ t ∈ Icc 0 om, 0 ≤ Θ t)
    (hΦΘ : ∀ t ∈ Icc 0 om, Φ t ^ p ≤ Θ t * (-φ' t) ^ (p - 1))
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {m : ℕ} (hm : p ≤ m)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (hη0 : ∀ x, 0 ≤ η x) (hlevel : ∀ᵐ x, x ∈ tsupport η → σ * (u x - k) ∈ Icc 0 om) :
    ∫ x, η x ^ m * -φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p ≤
      2 ^ p * ((m : ℝ) * L) ^ p *
          (∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (levelClamp σ k om (u x))) +
        2 * (|lam| * S ^ (p - 1)) * ∫ x, η x ^ m * Φ (levelClamp σ k om (u x)) := by
  have hp0 : 0 < p := by linarith
  have hm1 : (1 : ℝ) < m := lt_of_lt_of_le hp hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm1
  have hmp : 0 ≤ (m : ℝ) - p := sub_nonneg.2 hm
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hid := hu.integral_test_level_eq hp hF hσ hom hΦ hφ' hm0 hη hηs hηK hlevel
  have hΦc : ContinuousOn Φ (Icc 0 om) := fun t ht => (hΦ t ht).continuousAt.continuousWithinAt
  obtain ⟨hΦm, CΦ, hCΦ⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hΦc
  obtain ⟨hφm, Cφ, hCφ⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hφ'
  obtain ⟨hΘm, CΘ, hCΘ⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hΘc
  obtain ⟨hζ, hζs, hζt⟩ := cutoff_pow hη hηs hm0
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hAη0 : 0 ≤ Aη := (norm_nonneg _).trans (hAη 0)
  have hηpow : ∀ n : ℕ, ∀ x, |η x ^ n| ≤ Aη ^ n := fun n x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [← Real.norm_eq_abs]; exact hAη x) n
  have i1 : Integrable fun x =>
      η x ^ m * -φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p :=
    hu.integrable_mul_rpow hp hF (hζ.continuous.aestronglyMeasurable.mul hφm.neg)
      (B := Aη ^ m * Cφ) fun x => by
        show |η x ^ m * -φ' (levelClamp σ k om (u x))| ≤ Aη ^ m * Cφ
        rw [abs_mul, abs_neg]
        exact mul_le_mul (hηpow m x) (hCφ x) (abs_nonneg _) (pow_nonneg hAη0 m)
  have hwc : Continuous fun x => η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p :=
    (hη.continuous.rpow_const fun _ => Or.inr hmp).mul
      ((continuous_gradient hη1).norm.rpow_const fun _ => Or.inr hp0.le)
  have hws : HasCompactSupport fun x => η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p := by
    refine (hasCompactSupport_gradient hηs).mono fun x hx h0 => hx ?_
    show η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p = 0
    rw [h0, norm_zero, Real.zero_rpow hp0.ne', mul_zero]
  have i3 : Integrable fun x => η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
      Θ (levelClamp σ k om (u x)) :=
    (hwc.integrable_of_hasCompactSupport hws).mul_bdd (c := CΘ) hΘm
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCΘ x)
  have i4 : Integrable fun x => η x ^ m * Φ (levelClamp σ k om (u x)) :=
    ((hη.continuous.pow m).integrable_of_hasCompactSupport hζs).mul_bdd (c := CΦ) hΦm
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCΦ x)
  have i5 : Integrable fun x => u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) := by
    refine (i4.const_mul (S ^ (p - 1))).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((continuous_id.rpow_const fun _ => Or.inr (by linarith)).comp_aestronglyMeasurable
        hu.memW0.memLp.aestronglyMeasurable).mul i4.aestronglyMeasurable
    · have hux := huS x
      have h0 : 0 ≤ η x ^ m * Φ (levelClamp σ k om (u x)) :=
        mul_nonneg (pow_nonneg (hη0 x) m) (hΦ0 _ (levelClamp_mem hom _))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hux.1 _), abs_of_nonneg h0]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hux.1 hux.2 (by linarith)) h0
  have i2 : Integrable fun x =>
      -(((m : ℝ) * η x ^ (m - 1)) * Φ (levelClamp σ k om (u x)) *
        -(σ * ⟪flux p F (weakGrad u x), gradient η x⟫)) := by
    have h := hu.integrable_mul_inner_flux_of_hasCompactSupport hp hF (continuous_gradient hη1)
      (hasCompactSupport_gradient hηs)
      (b := fun x => σ * (Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1))))
      (aestronglyMeasurable_const.mul
        (hΦm.mul (continuous_const.mul (hη.continuous.pow _)).aestronglyMeasurable))
      (B := CΦ * ((m : ℝ) * Aη ^ (m - 1))) fun x => by
        show |σ * (Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1)))| ≤
          CΦ * ((m : ℝ) * Aη ^ (m - 1))
        rw [abs_mul, hσ1, one_mul, abs_mul, abs_mul, Nat.abs_cast]
        exact mul_le_mul (hCΦ x) (mul_le_mul_of_nonneg_left (hηpow (m - 1) x)
          (Nat.cast_nonneg m)) (by positivity) ((abs_nonneg _).trans (hCΦ x))
    refine h.congr (Eventually.of_forall fun x => ?_)
    show σ * (Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1))) *
        ⟪flux p F (weakGrad u x), gradient η x⟫ =
      -(((m : ℝ) * η x ^ (m - 1)) * Φ (levelClamp σ k om (u x)) *
        -(σ * ⟪flux p F (weakGrad u x), gradient η x⟫))
    ring
  have hpt : ∀ x, -(((m : ℝ) * η x ^ (m - 1)) * Φ (levelClamp σ k om (u x)) *
      -(σ * ⟪flux p F (weakGrad u x), gradient η x⟫)) ≤
      η x ^ m * -φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p / 2 +
        2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
          (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (levelClamp σ k om (u x))) := fun x => by
    have hw := levelClamp_mem (σ := σ) (k := k) hom (u x)
    have h := caccioppoli_pointwise_weight hp hm (hη0 x) (hF.nonneg (weakGrad u x))
      (norm_nonneg (gradient η x)) hL0 (neg_nonneg.2 (hφ'0 _ hw)) (hΦ0 _ hw) (hΘ0 _ hw)
      (hΦΘ _ hw) (I := -(σ * ⟪flux p F (weakGrad u x), gradient η x⟫))
      (by rw [abs_neg, abs_mul, hσ1, one_mul]; exact hF.abs_inner_flux_le hL _ _)
    calc -(((m : ℝ) * η x ^ (m - 1)) * Φ (levelClamp σ k om (u x)) *
          -(σ * ⟪flux p F (weakGrad u x), gradient η x⟫))
        ≤ η x ^ m * (-φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p) / 2 +
          2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
            (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (levelClamp σ k om (u x))) := h
      _ = η x ^ m * -φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p / 2 +
          2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
            (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (levelClamp σ k om (u x))) := by
          ring
  have hint : ∫ x, -(((m : ℝ) * η x ^ (m - 1)) * Φ (levelClamp σ k om (u x)) *
      -(σ * ⟪flux p F (weakGrad u x), gradient η x⟫)) ≤
      ∫ x, (η x ^ m * -φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p / 2 +
        2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
          (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (levelClamp σ k om (u x)))) :=
    integral_mono i2 ((i1.div_const 2).add (i3.const_mul _)) hpt
  rw [integral_add (i1.div_const 2) (i3.const_mul _), integral_div, integral_const_mul] at hint
  have e2 : ∫ x, -(((m : ℝ) * η x ^ (m - 1)) * Φ (levelClamp σ k om (u x)) *
      -(σ * ⟪flux p F (weakGrad u x), gradient η x⟫)) =
      σ * ∫ x, Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1)) *
        ⟪flux p F (weakGrad u x), gradient η x⟫ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show -(((m : ℝ) * η x ^ (m - 1)) * Φ (levelClamp σ k om (u x)) *
        -(σ * ⟪flux p F (weakGrad u x), gradient η x⟫)) =
      σ * (Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1)) *
        ⟪flux p F (weakGrad u x), gradient η x⟫)
    ring
  have e1 : ∫ x, η x ^ m * -φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p =
      -∫ x, η x ^ m * φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      show η x ^ m * -φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p =
        -(η x ^ m * φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p)
      ring)
  have hU : -(σ * (lam * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))))) ≤
      |lam| * S ^ (p - 1) * ∫ x, η x ^ m * Φ (levelClamp σ k om (u x)) := by
    have hU0 : 0 ≤ ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) :=
      integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (huS x).1 _)
        (mul_nonneg (pow_nonneg (hη0 x) m) (hΦ0 _ (levelClamp_mem hom _)))
    have hU1 : ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) ≤
        S ^ (p - 1) * ∫ x, η x ^ m * Φ (levelClamp σ k om (u x)) := by
      rw [← integral_const_mul]
      refine integral_mono i5 (i4.const_mul _) fun x => ?_
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (huS x).1 (huS x).2 (by linarith))
        (mul_nonneg (pow_nonneg (hη0 x) m) (hΦ0 _ (levelClamp_mem hom _)))
    have h1 : -(σ * (lam * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))))) ≤
        |lam| * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) := by
      calc -(σ * (lam * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x)))))
          = -(σ * lam) * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) := by
            ring
        _ ≤ |σ * lam| * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) :=
            mul_le_mul_of_nonneg_right (neg_le_abs _) hU0
        _ = |lam| * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x))) := by
            rw [abs_mul, hσ1, one_mul]
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hU1 (abs_nonneg lam)
  have h2p : (2 : ℝ) ^ (p - 1) = 2 ^ p / 2 := Real.rpow_sub_one two_ne_zero p
  rw [e2, h2p] at hint
  rw [e1] at hint ⊢
  have hid' : -∫ x, η x ^ m * φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p =
      σ * (∫ x, Φ (levelClamp σ k om (u x)) * ((m : ℝ) * η x ^ (m - 1)) *
        ⟪flux p F (weakGrad u x), gradient η x⟫) -
        σ * (lam * ∫ x, u x ^ (p - 1) * (η x ^ m * Φ (levelClamp σ k om (u x)))) := by
    linear_combination (-σ) * hid +
      (∫ x, η x ^ m * φ' (levelClamp σ k om (u x)) * F (weakGrad u x) ^ p) * hσ2
  linarith [hid', hint, hU]

end IsWeakEigensolution

/-! ### Logarithmic estimates for level functions -/

/-- For `z ≤ 0`, `t ↦ t^z` is antitone on `(0, ∞)`. -/
theorem rpow_le_rpow_of_nonpos_exponent' {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  have hy : 0 < y := hx.trans_le hxy
  have h := Real.rpow_le_rpow hx.le hxy (neg_nonneg.2 hz)
  have e1 : y ^ z = (y ^ (-z))⁻¹ := by rw [Real.rpow_neg hy.le, inv_inv]
  have e2 : x ^ z = (x ^ (-z))⁻¹ := by rw [Real.rpow_neg hx.le, inv_inv]
  rw [e1, e2]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx _) h

/-- The arithmetic closing `moser_log_energy_level`. -/
theorem moser_level_arith {cp q r b1p K1 Y L2 Z1 Z e β' : ℝ} (hcp : 0 ≤ cp) (hq0 : 0 ≤ q)
    (hqβ : q ≤ β') (hr : r ≤ 1) (hqb : q * b1p = r) (hK1 : 0 ≤ K1) (hY : 0 ≤ Y)
    (hL2 : 0 ≤ L2) (hZ1 : Z1 ≤ e * Z) (heZ : 0 ≤ e * Z) :
    cp * q * (K1 * (b1p * Y) + L2 * Z1) ≤ cp * (K1 * Y + β' * L2 * e * Z) := by
  have h1 : q * (K1 * (b1p * Y)) ≤ K1 * Y := by
    calc q * (K1 * (b1p * Y)) = K1 * (r * Y) := by rw [← hqb]; ring
      _ ≤ K1 * (1 * Y) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hY) hK1
      _ = K1 * Y := by ring
  have h2 : q * (L2 * Z1) ≤ β' * L2 * e * Z := by
    calc q * (L2 * Z1) ≤ q * (L2 * (e * Z)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ1 hL2) hq0
      _ ≤ β' * (L2 * (e * Z)) := mul_le_mul_of_nonneg_right hqβ (mul_nonneg hL2 heZ)
      _ = β' * L2 * e * Z := by ring
  calc cp * q * (K1 * (b1p * Y) + L2 * Z1) = cp * (q * (K1 * (b1p * Y)) + q * (L2 * Z1)) := by
        ring
    _ ≤ cp * (K1 * Y + β' * L2 * e * Z) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hcp

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- **The logarithmic Caccioppoli estimate for level functions**: with `w = σ(u - k) ∈ [0, om]`
a.e. on the support of `η`, `ε > 0` and `Λ = |λ| S^{p-1}`,
`∫ η^m (w + ε)^{-p} |∇u|^p ≤ c^{-p} (p-1)^{-1} (2^p (mL)^p (p-1)^{1-p} ∫ η^{m-p} |∇η|^p
  + 2 Λ ε^{1-p} ∫ η^m)`. -/
theorem log_caccioppoli_level (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    {σ k om : ℝ} (hσ : σ = 1 ∨ σ = -1) (hom : 0 ≤ om) {ε : ℝ} (hε : 0 < ε)
    {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {m : ℕ} (hm : p ≤ m) {η : Euc d → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (hη0 : ∀ x, 0 ≤ η x) (hlevel : ∀ᵐ x, x ∈ tsupport η → σ * (u x - k) ∈ Icc 0 om) :
    ∫ x, η x ^ m * ((levelClamp σ k om (u x) + ε) ^ (-p) * ‖weakGrad u x‖ ^ p) ≤
      c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((m : ℝ) * L) ^ p * (p - 1) ^ (1 - p) *
        (∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p) +
        2 * (|lam| * S ^ (p - 1)) * ε ^ (1 - p) * ∫ x, η x ^ m) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hm1 : (1 : ℝ) < m := lt_of_lt_of_le hp hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm1
  have hpos : ∀ t ∈ Icc 0 om, 0 < t + ε := fun t ht => by linarith [ht.1]
  have hψc : ContinuousOn (fun t => (1 - p) * (t + ε) ^ (-p)) (Icc 0 om) :=
    continuousOn_const.mul ((continuousOn_id.add continuousOn_const).rpow_const
      fun t ht => Or.inl (hpos t ht).ne')
  have hΦΘ : ∀ t ∈ Icc 0 om, ((t + ε) ^ (1 - p)) ^ p ≤
      (p - 1) ^ (1 - p) * (-((1 - p) * (t + ε) ^ (-p))) ^ (p - 1) := by
    intro t ht
    have htε := hpos t ht
    have e1 : -((1 - p) * (t + ε) ^ (-p)) = (p - 1) * (t + ε) ^ (-p) := by ring
    rw [e1, Real.mul_rpow hp1.le (Real.rpow_nonneg htε.le _), ← mul_assoc,
      ← Real.rpow_add hp1, show 1 - p + (p - 1) = (0 : ℝ) by ring, Real.rpow_zero, one_mul,
      ← Real.rpow_mul htε.le, ← Real.rpow_mul htε.le]
    exact le_of_eq (by congr 1; ring)
  have hen := hu.energy_le_level hp hF huS hσ hom (Φ := fun t => (t + ε) ^ (1 - p))
    (φ' := fun t => (1 - p) * (t + ε) ^ (-p)) (Θ := fun _ => (p - 1) ^ (1 - p))
    (fun t ht => by
      have h := hasDerivAt_add_rpow (q := 1 - p) (hpos t ht)
      rwa [show 1 - p - 1 = -p by ring] at h)
    hψc continuousOn_const (fun t ht => Real.rpow_nonneg (hpos t ht).le _)
    (fun t ht => by nlinarith [Real.rpow_nonneg (hpos t ht).le (-p)])
    (fun _ _ => Real.rpow_nonneg hp1.le _) hΦΘ hL0 hL hm hη hηs hηK hη0 hlevel
  beta_reduce at hen
  rw [integral_mul_const] at hen
  obtain ⟨hψm, Cψ, hCψ⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hψc
  have hΦc : ContinuousOn (fun t => (t + ε) ^ (1 - p)) (Icc 0 om) :=
    (continuousOn_id.add continuousOn_const).rpow_const fun t ht => Or.inl (hpos t ht).ne'
  obtain ⟨hΦm, CΦ, hCΦ⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hΦc
  obtain ⟨hζ, hζs, hζt⟩ := cutoff_pow hη hηs hm0
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hAη0 : 0 ≤ Aη := (norm_nonneg _).trans (hAη 0)
  have iζ : Integrable fun x => η x ^ m :=
    (hη.continuous.pow m).integrable_of_hasCompactSupport hζs
  have hZ : ∫ x, η x ^ m * (levelClamp σ k om (u x) + ε) ^ (1 - p) ≤
      ε ^ (1 - p) * ∫ x, η x ^ m := by
    rw [← integral_const_mul]
    refine integral_mono (iζ.mul_bdd (c := CΦ) hΦm (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hCΦ x)) (iζ.const_mul _) fun x => ?_
    show η x ^ m * (levelClamp σ k om (u x) + ε) ^ (1 - p) ≤ ε ^ (1 - p) * η x ^ m
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos_exponent' hε
      (by linarith [(levelClamp_mem (σ := σ) (k := k) hom (u x)).1]) (by linarith))
      (pow_nonneg (hη0 x) m)
  have iR : Integrable fun x => η x ^ m * -((1 - p) * (levelClamp σ k om (u x) + ε) ^ (-p)) *
      F (weakGrad u x) ^ p :=
    hu.integrable_mul_rpow hp hF ((hη.continuous.pow m).aestronglyMeasurable.mul hψm.neg)
      (B := Aη ^ m * Cψ) fun x => by
        show |η x ^ m * -((1 - p) * (levelClamp σ k om (u x) + ε) ^ (-p))| ≤ Aη ^ m * Cψ
        rw [abs_mul, abs_neg, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _)
          (by rw [← Real.norm_eq_abs]; exact hAη x) m) (hCψ x) (abs_nonneg _)
          (pow_nonneg hAη0 m)
  have hpt : ∀ x, η x ^ m * ((levelClamp σ k om (u x) + ε) ^ (-p) * ‖weakGrad u x‖ ^ p) ≤
      c⁻¹ ^ p * (p - 1)⁻¹ * (η x ^ m * -((1 - p) * (levelClamp σ k om (u x) + ε) ^ (-p)) *
        F (weakGrad u x) ^ p) := by
    intro x
    have hux := hpos _ (levelClamp_mem (σ := σ) (k := k) hom (u x))
    have h2 := norm_rpow_le_inv_rpow_mul hc hcF hp0 (weakGrad u x)
    have hX : 0 ≤ (levelClamp σ k om (u x) + ε) ^ (-p) := Real.rpow_nonneg hux.le _
    have hp1' : p - 1 ≠ 0 := hp1.ne'
    calc η x ^ m * ((levelClamp σ k om (u x) + ε) ^ (-p) * ‖weakGrad u x‖ ^ p)
        ≤ η x ^ m * ((levelClamp σ k om (u x) + ε) ^ (-p) *
            (c⁻¹ ^ p * F (weakGrad u x) ^ p)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hX) (pow_nonneg (hη0 x) m)
      _ = c⁻¹ ^ p * (p - 1)⁻¹ * (η x ^ m *
            -((1 - p) * (levelClamp σ k om (u x) + ε) ^ (-p)) * F (weakGrad u x) ^ p) := by
          field_simp
          ring
  have hmono := integral_mono_of_nonneg (Eventually.of_forall fun x =>
    mul_nonneg (pow_nonneg (hη0 x) m) (mul_nonneg (Real.rpow_nonneg
      (hpos _ (levelClamp_mem (σ := σ) (k := k) hom (u x))).le _)
      (Real.rpow_nonneg (norm_nonneg _) _)))
    (iR.const_mul (c⁻¹ ^ p * (p - 1)⁻¹)) (Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  refine hmono.trans ?_
  have hC0 : 0 ≤ c⁻¹ ^ p * (p - 1)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _) (inv_nonneg.2 hp1.le)
  refine mul_le_mul_of_nonneg_left (hen.trans ?_) hC0
  have hΛ0 : 0 ≤ 2 * (|lam| * S ^ (p - 1)) :=
    mul_nonneg zero_le_two (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hS _))
  refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hZ hΛ0)).trans (le_of_eq ?_)
  ring

/-- **The Moser energy bound for level functions**: with `w = σ(u - k) ∈ [0, om]` a.e. on the
support of `η`, `ε > 0`, `T ≥ 2(om + ε)` (so `W = log T - log(w + ε) ≥ log 2`) and `β ≥ 1`,
`∫ η^m |∇ W^β|^p ≤ c^{-p} (2^p (mL)^p ∫ η^{m-p} |∇η|^p W^{βp}
  + 2 β^p Λ ε^{1-p} (log 2)^{1-p} ∫ η^m W^{βp})`, `Λ = |λ| S^{p-1}`. -/
theorem moser_log_energy_level (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    {σ k om : ℝ} (hσ : σ = 1 ∨ σ = -1) (hom : 0 ≤ om) {ε : ℝ} (hε : 0 < ε) {T : ℝ}
    (hT : 2 * (om + ε) ≤ T) {β : ℝ} (hβ : 1 ≤ β) {c : ℝ} (hc : 0 < c)
    (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {m : ℕ}
    (hm : p ≤ m) {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηK : tsupport η ⊆ K) (hη0 : ∀ x, 0 ≤ η x)
    (hlevel : ∀ᵐ x, x ∈ tsupport η → σ * (u x - k) ∈ Icc 0 om) :
    ∫ x, η x ^ m * ‖(-(β * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
        (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ ^ p ≤
      c⁻¹ ^ p * (2 ^ p * ((m : ℝ) * L) ^ p *
          (∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
            ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p) +
        β ^ p * (2 * (|lam| * S ^ (p - 1))) * (ε ^ (1 - p) * Real.log 2 ^ (1 - p)) *
          ∫ x, η x ^ m * ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = p * (β - 1) + 1 := ⟨_, rfl⟩
  have hb1 : 1 ≤ b := by rw [hb]; nlinarith
  have hb0 : 0 < b := by linarith
  have hβb : β ≤ b := by rw [hb]; nlinarith
  have hpos : ∀ t ∈ Icc 0 om, 0 < t + ε := fun t ht => by linarith [ht.1]
  have hle : ∀ t ∈ Icc 0 om, t + ε ≤ T := fun t ht => by linarith [ht.2]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hw2 : ∀ t ∈ Icc 0 om, Real.log 2 ≤ Real.log T - Real.log (t + ε) := by
    intro t ht
    have hT0 : 0 < T := (hpos t ht).trans_le (hle t ht)
    rw [← Real.log_div hT0.ne' (hpos t ht).ne']
    exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ (hpos t ht)]; linarith [ht.2])
  have hw0 : ∀ t ∈ Icc 0 om, 0 ≤ Real.log T - Real.log (t + ε) := fun t ht =>
    hlog2.le.trans (hw2 t ht)
  have hzc : ContinuousOn (fun t => t + ε) (Icc 0 om) := continuousOn_id.add continuousOn_const
  have hwc : ContinuousOn (fun t => Real.log T - Real.log (t + ε)) (Icc 0 om) :=
    continuousOn_const.sub (hzc.log fun t ht => (hpos t ht).ne')
  have hψc : ContinuousOn (fun t => -((t + ε) ^ (-p) *
      (b * (Real.log T - Real.log (t + ε)) ^ (b - 1) +
        (p - 1) * (Real.log T - Real.log (t + ε)) ^ b))) (Icc 0 om) :=
    ((hzc.rpow_const fun t ht => Or.inl (hpos t ht).ne').mul
      ((continuousOn_const.mul (hwc.rpow_const fun _ _ => Or.inr (by linarith))).add
        (continuousOn_const.mul (hwc.rpow_const fun _ _ => Or.inr hb0.le)))).neg
  have hΘc : ContinuousOn
      (fun t => b ^ (1 - p) * (Real.log T - Real.log (t + ε)) ^ (b + p - 1)) (Icc 0 om) :=
    continuousOn_const.mul (hwc.rpow_const fun _ _ => Or.inr (by linarith))
  have hΦc : ContinuousOn
      (fun t => (Real.log T - Real.log (t + ε)) ^ b * (t + ε) ^ (1 - p)) (Icc 0 om) :=
    (hwc.rpow_const fun _ _ => Or.inr hb0.le).mul
      (hzc.rpow_const fun t ht => Or.inl (hpos t ht).ne')
  have hWc : ContinuousOn (fun t => ((Real.log T - Real.log (t + ε)) ^ β) ^ p) (Icc 0 om) :=
    (hwc.rpow_const fun _ _ => Or.inr (by linarith)).rpow_const fun _ _ => Or.inr hp0.le
  have hen := hu.energy_le_level hp hF huS hσ hom
    (Φ := fun t => (Real.log T - Real.log (t + ε)) ^ b * (t + ε) ^ (1 - p))
    (φ' := fun t => -((t + ε) ^ (-p) * (b * (Real.log T - Real.log (t + ε)) ^ (b - 1) +
      (p - 1) * (Real.log T - Real.log (t + ε)) ^ b)))
    (Θ := fun t => b ^ (1 - p) * (Real.log T - Real.log (t + ε)) ^ (b + p - 1))
    (fun t ht => hasDerivAt_logProfile hb1 (hpos t ht)) hψc hΘc
    (fun t ht => mul_nonneg (Real.rpow_nonneg (hw0 t ht) _) (Real.rpow_nonneg (hpos t ht).le _))
    (fun t ht => neg_nonpos.2 (mul_nonneg (Real.rpow_nonneg (hpos t ht).le _)
      (add_nonneg (mul_nonneg hb0.le (Real.rpow_nonneg (hw0 t ht) _))
        (mul_nonneg hp1.le (Real.rpow_nonneg (hw0 t ht) _)))))
    (fun t ht => mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg (hw0 t ht) _))
    (fun t ht => logProfile_rpow_le hp hb1 (hpos t ht) (hle t ht)) hL0 hL hm hη hηs hηK hη0
    hlevel
  beta_reduce at hen
  obtain ⟨hAm, CA, hCA⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hψc
  obtain ⟨hΦm, CΦ, hCΦ⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hΦc
  obtain ⟨hWm, CW, hCW⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hWc
  have hm1 : (1 : ℝ) < m := lt_of_lt_of_le hp hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm1
  obtain ⟨hζ, hζs, hζt⟩ := cutoff_pow hη hηs hm0
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hAη0 : 0 ≤ Aη := (norm_nonneg _).trans (hAη 0)
  have iζ : Integrable fun x => η x ^ m :=
    (hη.continuous.pow m).integrable_of_hasCompactSupport hζs
  have iR : Integrable fun x => η x ^ m * -(-((levelClamp σ k om (u x) + ε) ^ (-p) *
      (b * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (b - 1) +
        (p - 1) * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b))) *
      F (weakGrad u x) ^ p :=
    hu.integrable_mul_rpow hp hF ((hη.continuous.pow m).aestronglyMeasurable.mul hAm.neg)
      (B := Aη ^ m * CA) fun x => by
        show |η x ^ m * -(-((levelClamp σ k om (u x) + ε) ^ (-p) *
          (b * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (b - 1) +
            (p - 1) * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b)))| ≤
          Aη ^ m * CA
        rw [abs_mul, abs_neg, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _)
          (by rw [← Real.norm_eq_abs]; exact hAη x) m) (hCA x) (abs_nonneg _)
          (pow_nonneg hAη0 m)
  have hpt : ∀ x, η x ^ m * ‖(-(β * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^
      (β - 1) * (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ ^ p ≤
      c⁻¹ ^ p * (β ^ p / b) * (η x ^ m * -(-((levelClamp σ k om (u x) + ε) ^ (-p) *
        (b * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (b - 1) +
          (p - 1) * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b))) *
        F (weakGrad u x) ^ p) := by
    intro x
    have hw := levelClamp_mem (σ := σ) (k := k) hom (u x)
    rw [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Real.norm_eq_abs]
    have h1 := abs_logPow_deriv_rpow_le (T := T) hp hβ hb (hpos _ hw) (hle _ hw)
    have h2 := norm_rpow_le_inv_rpow_mul hc hcF hp0 (weakGrad u x)
    have hηm : 0 ≤ η x ^ m := pow_nonneg (hη0 x) m
    have hA0 := (Real.rpow_nonneg (abs_nonneg _) _).trans h1
    calc η x ^ m * (|-(β * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
          (levelClamp σ k om (u x) + ε)⁻¹)| ^ p * ‖weakGrad u x‖ ^ p)
        ≤ η x ^ m * ((β ^ p / b * -(-((levelClamp σ k om (u x) + ε) ^ (-p) *
            (b * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (b - 1) +
              (p - 1) * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b)))) *
            (c⁻¹ ^ p * F (weakGrad u x) ^ p)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.rpow_nonneg (norm_nonneg _) _) hA0)
            hηm
      _ = c⁻¹ ^ p * (β ^ p / b) * (η x ^ m * -(-((levelClamp σ k om (u x) + ε) ^ (-p) *
          (b * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (b - 1) +
            (p - 1) * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b))) *
          F (weakGrad u x) ^ p) := by ring
  have hC0 : 0 ≤ c⁻¹ ^ p * (β ^ p / b) :=
    mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      (div_nonneg (Real.rpow_nonneg (by linarith) _) hb0.le)
  have hmono := integral_mono_of_nonneg (Eventually.of_forall fun x =>
    mul_nonneg (pow_nonneg (hη0 x) m) (Real.rpow_nonneg (norm_nonneg _) _))
    (iR.const_mul (c⁻¹ ^ p * (β ^ p / b))) (Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  refine (hmono.trans (mul_le_mul_of_nonneg_left hen hC0)).trans ?_
  -- rewrite the weight integral and bound the right-hand-side term
  have hI : ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
      (b ^ (1 - p) * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (b + p - 1)) =
      b ^ (1 - p) * ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
        ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
        (b ^ (1 - p) * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (b + p - 1)) =
      b ^ (1 - p) * (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
        ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p)
    rw [← Real.rpow_mul (hw0 _ (levelClamp_mem hom _)), show β * p = b + p - 1 by rw [hb]; ring]
    ring
  have iW : Integrable fun x => η x ^ m *
      ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p :=
    iζ.mul_bdd (c := CW) hWm (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hCW x)
  have hZ : ∫ x, η x ^ m * ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b *
      (levelClamp σ k om (u x) + ε) ^ (1 - p)) ≤
      (ε ^ (1 - p) * Real.log 2 ^ (1 - p)) * ∫ x, η x ^ m *
        ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p := by
    rw [← integral_const_mul]
    refine integral_mono (iζ.mul_bdd (c := CΦ) hΦm (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hCΦ x)) (iW.const_mul _) fun x => ?_
    have hw := levelClamp_mem (σ := σ) (k := k) hom (u x)
    have hwpos : 0 < Real.log T - Real.log (levelClamp σ k om (u x) + ε) :=
      hlog2.trans_le (hw2 _ hw)
    have h1 : (levelClamp σ k om (u x) + ε) ^ (1 - p) ≤ ε ^ (1 - p) :=
      rpow_le_rpow_of_nonpos_exponent' hε (by linarith [hw.1]) (by linarith)
    have h2 : (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b ≤
        Real.log 2 ^ (1 - p) * ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p := by
      have hsplit : (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b =
          (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (1 - p) *
            ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p := by
        rw [← Real.rpow_mul hwpos.le, ← Real.rpow_add hwpos]
        congr 1
        rw [hb]
        ring
      rw [hsplit]
      have hz : 1 - p ≤ 0 := by linarith
      exact mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos_exponent' hlog2 (hw2 _ hw) hz)
        (Real.rpow_nonneg (Real.rpow_nonneg hwpos.le _) _)
    show η x ^ m * ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b *
        (levelClamp σ k om (u x) + ε) ^ (1 - p)) ≤
      ε ^ (1 - p) * Real.log 2 ^ (1 - p) * (η x ^ m *
        ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p)
    have hηm : 0 ≤ η x ^ m := pow_nonneg (hη0 x) m
    calc η x ^ m * ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ b *
          (levelClamp σ k om (u x) + ε) ^ (1 - p))
        ≤ η x ^ m * ((Real.log 2 ^ (1 - p) *
            ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p) * ε ^ (1 - p)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h1 (Real.rpow_nonneg (by linarith [hw.1]) _)
            (mul_nonneg (Real.rpow_nonneg hlog2.le _)
              (Real.rpow_nonneg (Real.rpow_nonneg hwpos.le _) _))) hηm
      _ = ε ^ (1 - p) * Real.log 2 ^ (1 - p) * (η x ^ m *
            ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p) := by ring
  rw [hI]
  have hY : 0 ≤ ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
      ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p :=
    integral_nonneg fun x => mul_nonneg (mul_nonneg (Real.rpow_nonneg (hη0 x) _)
      (Real.rpow_nonneg (norm_nonneg _) _))
      (Real.rpow_nonneg (Real.rpow_nonneg (hw0 _ (levelClamp_mem hom _)) _) _)
  have hZ0 : 0 ≤ (ε ^ (1 - p) * Real.log 2 ^ (1 - p)) * ∫ x, η x ^ m *
      ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hlog2.le _))
      (integral_nonneg fun x => mul_nonneg (pow_nonneg (hη0 x) m)
        (Real.rpow_nonneg (Real.rpow_nonneg (hw0 _ (levelClamp_mem hom _)) _) _))
  have e : β ^ p / b * b ^ (1 - p) = (β / b) ^ p := by
    rw [Real.rpow_sub hb0, Real.rpow_one, Real.div_rpow (by linarith) hb0.le]
    field_simp
  have hr : (β / b) ^ p ≤ 1 :=
    Real.rpow_le_one (div_nonneg (by linarith) hb0.le) ((div_le_one hb0).2 hβb) hp0.le
  have hqβ : β ^ p / b ≤ β ^ p := div_le_self (Real.rpow_nonneg (by linarith) _) hb1
  have hK1 : 0 ≤ 2 ^ p * ((m : ℝ) * L) ^ p :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg m) hL0) _)
  have hL2 : 0 ≤ 2 * (|lam| * S ^ (p - 1)) :=
    mul_nonneg zero_le_two (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hS _))
  have key := moser_level_arith (Real.rpow_nonneg (inv_nonneg.2 hc.le) p)
    (div_nonneg (Real.rpow_nonneg (by linarith) _) hb0.le) hqβ hr e hK1 hY hL2 hZ hZ0
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · ring
  · ring

end IsWeakEigensolution

/-! ### The Moser step for level functions at scale `R` -/

/-- The scaling identity behind the normalized Moser step:
`R^{-d} (2R)^d ((2R)^p (2R)^{-d})^κ (R^{-p})^κ = 2^d (2^p 2^{-d})^κ (R^{-d})^κ`. -/
theorem moser_scale_identity {R : ℝ} (hR : 0 < R) (p κ : ℝ) :
    (R ^ d)⁻¹ * ((2 * R) ^ d * ((2 * R) ^ p * ((2 * R) ^ d)⁻¹) ^ κ) * ((R ^ p)⁻¹) ^ κ =
      2 ^ d * (2 ^ p * (2 ^ d)⁻¹) ^ κ * ((R ^ d)⁻¹) ^ κ := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  have hRd : 0 < R ^ d := pow_pos hR d
  have h2p : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos h2 p
  have h2d : 0 < (2 : ℝ) ^ d := pow_pos h2 d
  have hRd' := hRd.ne'
  have hRp' := hRp.ne'
  rw [Real.mul_rpow h2.le hR.le, mul_pow]
  have e1 : 2 ^ p * R ^ p * (2 ^ d * R ^ d)⁻¹ = (2 ^ p * (2 ^ d)⁻¹) * (R ^ p * (R ^ d)⁻¹) := by
    field_simp
  rw [e1, Real.mul_rpow (mul_nonneg h2p.le (inv_nonneg.2 h2d.le))
    (mul_nonneg hRp.le (inv_nonneg.2 hRd.le))]
  have e2 : (R ^ p * (R ^ d)⁻¹) ^ κ * ((R ^ p)⁻¹) ^ κ = ((R ^ d)⁻¹) ^ κ := by
    rw [← Real.mul_rpow (mul_nonneg hRp.le (inv_nonneg.2 hRd.le)) (inv_nonneg.2 hRp.le)]
    congr 1
    field_simp
  calc (R ^ d)⁻¹ * (2 ^ d * R ^ d * ((2 ^ p * (2 ^ d)⁻¹) ^ κ * (R ^ p * (R ^ d)⁻¹) ^ κ)) *
        ((R ^ p)⁻¹) ^ κ
      = 2 ^ d * (2 ^ p * (2 ^ d)⁻¹) ^ κ * ((R ^ p * (R ^ d)⁻¹) ^ κ * ((R ^ p)⁻¹) ^ κ) *
          ((R ^ d)⁻¹ * R ^ d) := by ring
    _ = 2 ^ d * (2 ^ p * (2 ^ d)⁻¹) ^ κ * ((R ^ d)⁻¹) ^ κ := by
        rw [e2, inv_mul_cancel₀ hRd', mul_one]

/-- The `ℝ≥0∞` rearrangement of the normalized Moser step. -/
theorem ennreal_moser_rescale {C J : ℝ≥0∞} {a s q M t κ : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hq : 0 ≤ q) (hM : 0 ≤ M) (ht : 0 ≤ t) (hκ : 0 ≤ κ) (hid : a * s * q ^ κ = t * a ^ κ) :
    ENNReal.ofReal a * (C * ENNReal.ofReal s * (ENNReal.ofReal (q * M) * J) ^ κ) =
      C * ENNReal.ofReal t * (ENNReal.ofReal M * (ENNReal.ofReal a * J)) ^ κ := by
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hκ, ENNReal.ofReal_mul hq,
    ENNReal.ofReal_rpow_of_nonneg hq hκ, ENNReal.ofReal_rpow_of_nonneg hM hκ,
    ENNReal.ofReal_rpow_of_nonneg ha hκ]
  have h1 : ENNReal.ofReal a * ENNReal.ofReal s * ENNReal.ofReal (q ^ κ) =
      ENNReal.ofReal t * ENNReal.ofReal (a ^ κ) := by
    rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hs), hid,
      ENNReal.ofReal_mul ht]
  calc ENNReal.ofReal a * (C * ENNReal.ofReal s *
        (ENNReal.ofReal (q ^ κ) * ENNReal.ofReal (M ^ κ) * J ^ κ))
      = C * (ENNReal.ofReal a * ENNReal.ofReal s * ENNReal.ofReal (q ^ κ)) *
          ENNReal.ofReal (M ^ κ) * J ^ κ := by ring
    _ = C * (ENNReal.ofReal t * ENNReal.ofReal (a ^ κ)) * ENNReal.ofReal (M ^ κ) * J ^ κ := by
        rw [h1]
    _ = C * ENNReal.ofReal t * (ENNReal.ofReal (M ^ κ) * (ENNReal.ofReal (a ^ κ) * J ^ κ)) := by
        ring

/-- The real arithmetic of the normalized Moser step. -/
theorem moser_step_arith {X Y Zw I cp mp bp Lp Gp ir l2 Λ e t2 : ℝ}
    (hcp : 0 ≤ cp) (hmp : 1 ≤ mp) (hbp : 1 ≤ bp) (hLp : 0 ≤ Lp) (hGp : 0 ≤ Gp) (hir : 0 ≤ ir)
    (hl2 : 0 ≤ l2) (hΛe : Λ * e ≤ ir) (ht2 : 0 ≤ t2) (hI : 0 ≤ I)
    (hen : X ≤ cp * (t2 * (mp * Lp) * Y + bp * (2 * Λ) * (e * l2) * Zw))
    (hY : Y ≤ Gp * ir * I) (hZw : Zw ≤ I) (hZw0 : 0 ≤ Zw) :
    t2 * (X + mp * (Gp * ir) * I) ≤
      ir * ((mp * bp) * (t2 * (cp * (t2 * Lp * Gp + 2 * l2) + Gp))) * I := by
  have h1 : t2 * (mp * Lp) * Y ≤ t2 * (mp * Lp) * (Gp * ir * I) :=
    mul_le_mul_of_nonneg_left hY (mul_nonneg ht2 (mul_nonneg (by linarith) hLp))
  have h2 : bp * (2 * Λ) * (e * l2) * Zw ≤ bp * 2 * ir * l2 * I := by
    have h3 : Λ * e * Zw ≤ ir * I := by
      rcases le_total 0 (Λ * e) with h | h
      · exact mul_le_mul hΛe hZw hZw0 hir
      · exact (mul_nonpos_of_nonpos_of_nonneg h hZw0).trans (mul_nonneg hir hI)
    calc bp * (2 * Λ) * (e * l2) * Zw = (2 * bp * l2) * (Λ * e * Zw) := by ring
      _ ≤ (2 * bp * l2) * (ir * I) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg zero_le_two (by linarith)) hl2)
      _ = bp * 2 * ir * l2 * I := by ring
  have hX : X ≤ cp * (t2 * (mp * Lp) * (Gp * ir * I) + bp * 2 * ir * l2 * I) :=
    hen.trans (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hcp)
  have hmb1 : mp ≤ mp * bp := le_mul_of_one_le_right (by linarith) hbp
  have hmb2 : bp ≤ mp * bp := le_mul_of_one_le_left (by linarith) hmp
  have hirI : 0 ≤ ir * I := mul_nonneg hir hI
  calc t2 * (X + mp * (Gp * ir) * I)
      ≤ t2 * (cp * (t2 * (mp * Lp) * (Gp * ir * I) + bp * 2 * ir * l2 * I) +
          mp * (Gp * ir) * I) :=
        mul_le_mul_of_nonneg_left (add_le_add hX le_rfl) ht2
    _ = t2 * (ir * I) * (cp * (t2 * mp * Lp * Gp + 2 * bp * l2) + mp * Gp) := by ring
    _ ≤ t2 * (ir * I) * (cp * (t2 * (mp * bp) * Lp * Gp + 2 * (mp * bp) * l2) +
          (mp * bp) * Gp) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
          (add_le_add ?_ ?_) hcp) (mul_le_mul_of_nonneg_right hmb1 hGp)) (mul_nonneg ht2 hirI)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmb1 ht2) hLp) hGp
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmb2 zero_le_two) hl2
    _ = ir * ((mp * bp) * (t2 * (cp * (t2 * Lp * Gp + 2 * l2) + Gp))) * I := by ring

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- **The normalized Moser step for level functions at scale `R`**: with `W = log T - log(w + ε)`,
`w = σ(u - k) ∈ [0, om]` a.e. on the support of a cutoff `0 ≤ η ≤ 1` supported in
`closedBall x₀ (2R)` with `‖∇η‖ ≤ G/R`, the scaled Sobolev inequality on `closedBall x₀ (2R)`,
`|λ| S^{p-1} R^p ≤ ε^{p-1}`, `β ≥ 1` and an integer `m > p`,
`R^{-d} ∫ η^{mκp} W^{βκp} ≤ C 2^d (2^p 2^{-d})^κ ((mβ)^p D R^{-d} ∫ η^{m-p} W^{βp})^κ`,
`D = 2^p (c^{-p} (2^p L^p G^p + 2 (log 2)^{1-p}) + G^p)`; no constant depends on `R`, `ε`, `k`. -/
theorem moser_level_step (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    {σ k om : ℝ} (hσ : σ = 1 ∨ σ = -1) (hom : 0 ≤ om) {ε : ℝ} (hε : 0 < ε) {T : ℝ}
    (hT : 2 * (om + ε) ≤ T) {β : ℝ} (hβ : 1 ≤ β) {c : ℝ} (hc : 0 < c)
    (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L)
    {κ : ℝ} (hκ : 0 < κ) {C : ℝ≥0∞} {x₀ : Euc d} {R : ℝ} (hR : 0 < R)
    (hSob : ∀ w : Euc d → ℝ, MemW0 p (Metric.closedBall x₀ (2 * R)) w →
      ∫⁻ x, ‖w x‖ₑ ^ (κ * p) ≤ C * ENNReal.ofReal ((2 * R) ^ d * ((2 * R) ^ p *
        ((2 * R) ^ d)⁻¹) ^ κ) * (∫⁻ x, ‖weakGrad w x‖ₑ ^ p) ^ κ)
    (hΛ : |lam| * S ^ (p - 1) * R ^ p ≤ ε ^ (p - 1))
    {m : ℕ} (hm : p < m) {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηK : tsupport η ⊆ K) (hηB : tsupport η ⊆ Metric.closedBall x₀ (2 * R))
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ x, ‖gradient η x‖ ≤ G / R)
    (hlevel : ∀ᵐ x, x ∈ tsupport η → σ * (u x - k) ∈ Icc 0 om) :
    ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) * (κ * p)) *
        (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β * (κ * p))) ≤
      C * ENNReal.ofReal (2 ^ d * (2 ^ p * (2 ^ d)⁻¹) ^ κ) *
        (ENNReal.ofReal (((m : ℝ) * β) ^ p * (2 ^ p * (c⁻¹ ^ p *
          (2 ^ p * L ^ p * G ^ p + 2 * Real.log 2 ^ (1 - p)) + G ^ p))) *
          (ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) - p) *
            (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β * p)))) ^ κ := by
  have hp0 : 0 < p := by linarith
  have hκp : 0 < κ * p := mul_pos hκ hp0
  have hm1 : (1 : ℝ) < m := lt_trans hp hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm1
  have hmN : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
  have hmp : 0 < (m : ℝ) - p := sub_pos.2 hm
  have hη1' : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  have hRd : 0 < R ^ d := pow_pos hR d
  have hpos : ∀ t ∈ Icc 0 om, 0 < t + ε := fun t ht => by linarith [ht.1]
  have hle : ∀ t ∈ Icc 0 om, t + ε ≤ T := fun t ht => by linarith [ht.2]
  have hw0 : ∀ t ∈ Icc 0 om, 0 ≤ Real.log T - Real.log (t + ε) := fun t ht =>
    sub_nonneg.2 (Real.log_le_log (hpos t ht) (hle t ht))
  have hzc : ContinuousOn (fun t => t + ε) (Icc 0 om) := continuousOn_id.add continuousOn_const
  have hwc : ContinuousOn (fun t => Real.log T - Real.log (t + ε)) (Icc 0 om) :=
    continuousOn_const.sub (hzc.log fun t ht => (hpos t ht).ne')
  have hΦc : ContinuousOn
      (fun t => -(β * (Real.log T - Real.log (t + ε)) ^ (β - 1) * (t + ε)⁻¹)) (Icc 0 om) :=
    ((continuousOn_const.mul (hwc.rpow_const fun _ _ => Or.inr (by linarith))).mul
      (hzc.inv₀ fun t ht => (hpos t ht).ne')).neg
  obtain ⟨cW, GW, hcGW, hGWw, hGWg⟩ := memW0_comp_level hp hu.memW0 hσ hom
    (Φ := fun t => (Real.log T - Real.log (t + ε)) ^ β)
    (fun t ht => hasDerivAt_log_sub_rpow hβ (hpos t ht)) hΦc
  obtain ⟨hζ, hζs, hζt⟩ := cutoff_pow hη hηs hm0
  obtain ⟨hZ, hZg⟩ := hGWw.contDiff_mul_const_add hζ hζs (hζt.trans hηK) cW
  have hZB : MemW0 p (Metric.closedBall x₀ (2 * R)) (fun x => η x ^ m * (cW + GW (u x))) :=
    ⟨hZ.memLp, Eventually.of_forall fun x hx => by
      have h0 : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hηB h)
      simp [h0, zero_pow hm0], hZ.exists_weakGradient⟩
  have hS1 := hSob _ hZB
  -- the values of `η^m W`
  have hZval : ∀ᵐ x, ‖η x ^ m * (cW + GW (u x))‖ₑ ^ (κ * p) =
      ENNReal.ofReal (η x ^ ((m : ℝ) * (κ * p)) *
        (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β * (κ * p))) := by
    filter_upwards [hlevel] with x h3
    by_cases hx : x ∈ tsupport η
    · have h4 := h3 hx
      have hwx := hw0 _ (levelClamp_mem (σ := σ) (k := k) hom (u x))
      rw [hcGW _ h4, ← levelClamp_eq h4]
      have h0 : 0 ≤ η x ^ m * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β :=
        mul_nonneg (pow_nonneg (hη0 x) m) (Real.rpow_nonneg hwx _)
      rw [← ofReal_norm, Real.norm_of_nonneg h0, ENNReal.ofReal_rpow_of_nonneg h0 hκp.le,
        Real.mul_rpow (pow_nonneg (hη0 x) m) (Real.rpow_nonneg hwx _), ← Real.rpow_natCast,
        ← Real.rpow_mul (hη0 x), ← Real.rpow_mul hwx]
    · have he0 : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hmκp : 0 < (m : ℝ) * (κ * p) := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm0) hκp
      rw [he0, zero_pow hm0, zero_mul, enorm_zero, ENNReal.zero_rpow_of_pos hκp,
        Real.zero_rpow hmκp.ne', zero_mul, ENNReal.ofReal_zero]
  rw [lintegral_congr_ae hZval] at hS1
  -- the gradient of `η^m W`
  have hZpt : ∀ᵐ x, ‖weakGrad (fun x => η x ^ m * (cW + GW (u x))) x‖ ^ p ≤
      2 ^ p * (η x ^ m * ‖(-(β * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
        (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ ^ p + (m : ℝ) ^ p * (G / R) ^ p *
          (η x ^ ((m : ℝ) - p) *
            ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p)) := by
    filter_upwards [hZg, hGWg, hlevel] with x h1 h2 h3
    rw [h1, h2, gradient_pow_apply (hη1'.differentiable one_ne_zero x) m]
    by_cases hx : x ∈ tsupport η
    · have h4 := h3 hx
      rw [hcGW _ h4, ← levelClamp_eq h4]
      have h5 := norm_smul_add_smul_rpow_le hp.le hmN hm.le (hη0 x) (hη1 x)
        (Real.rpow_nonneg (hw0 _ (levelClamp_mem (σ := σ) (k := k) hom (u x))) β)
        ((σ * -(β * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
          (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x) (gradient η x) (hG x)
      have hnormV : ‖(σ * -(β * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^
          (β - 1) * (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ =
          ‖(-(β * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
            (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ := by
        rw [norm_smul, norm_smul, norm_mul, Real.norm_eq_abs σ, hσ1, one_mul]
      rwa [hnormV] at h5
    · have hg0 : gradient η x = 0 := gradient_eq_zero_of_notMem_tsupport hx
      have he0 : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hg0, he0, zero_pow hm0, Real.zero_rpow hp0.ne', Real.zero_rpow hmp.ne']
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hVint : Integrable fun x => ‖(-(β * (Real.log T -
      Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
        (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ ^ p := by
    refine (integrable_norm_rpow_of_memLp hp0 hGWw.memLp_weakGrad).congr
      (hGWg.mono fun x hx => ?_)
    show ‖weakGrad (fun x => GW (u x)) x‖ ^ p = ‖(-(β * (Real.log T -
      Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
        (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ ^ p
    rw [hx, norm_smul, norm_smul, norm_mul, Real.norm_eq_abs σ, hσ1, one_mul]
  have i1 : Integrable fun x => η x ^ m * ‖(-(β * (Real.log T -
      Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
        (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ ^ p :=
    hVint.bdd_mul (c := Aη ^ m) (hη.continuous.pow m).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (by rw [← Real.norm_eq_abs]; exact hAη x) m)
  have hWpc : ContinuousOn (fun t => ((Real.log T - Real.log (t + ε)) ^ β) ^ p) (Icc 0 om) :=
    (hwc.rpow_const fun _ _ => Or.inr (by linarith)).rpow_const fun _ _ => Or.inr hp0.le
  obtain ⟨hWpm, CW, hCW⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hWpc
  have hηc : Continuous fun x => η x ^ ((m : ℝ) - p) :=
    hη.continuous.rpow_const fun _ => Or.inr hmp.le
  have hηcs : HasCompactSupport fun x => η x ^ ((m : ℝ) - p) := by
    refine hηs.mono fun x hx h0 => hx ?_
    show η x ^ ((m : ℝ) - p) = 0
    rw [h0, Real.zero_rpow hmp.ne']
  have iW : Integrable fun x => η x ^ ((m : ℝ) - p) *
      ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p :=
    (hηc.integrable_of_hasCompactSupport hηcs).mul_bdd (c := CW) hWpm
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCW x)
  have hen := hu.moser_log_energy_level hp hF hS huS hσ hom hε hT hβ hc hcF hL0 hL hm.le hη
    hηs hηK hη0 hlevel
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ x, η x ^ ((m : ℝ) - p) *
      ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p := ⟨_, rfl⟩
  have hWx0 : ∀ x, 0 ≤ ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p :=
    fun x => Real.rpow_nonneg (Real.rpow_nonneg (hw0 _ (levelClamp_mem hom _)) _) _
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (hη0 x) _) (hWx0 x)
  have hY : ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
      ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p ≤
      G ^ p * (R ^ p)⁻¹ * I := by
    rw [hI, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) (iW.const_mul _)
      (Eventually.of_forall fun x => ?_)
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hη0 x) _)
        (Real.rpow_nonneg (norm_nonneg _) _)) (hWx0 x)
    · show η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
          ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p ≤
        G ^ p * (R ^ p)⁻¹ * (η x ^ ((m : ℝ) - p) *
          ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p)
      have h1 : ‖gradient η x‖ ^ p ≤ G ^ p * (R ^ p)⁻¹ := by
        rw [← div_eq_mul_inv, ← Real.div_rpow hG0 hR.le]
        exact Real.rpow_le_rpow (norm_nonneg _) (hG x) hp0.le
      have h2 := mul_nonneg (Real.rpow_nonneg (hη0 x) ((m : ℝ) - p)) (hWx0 x)
      nlinarith
  have hZw : ∫ x, η x ^ m * ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p ≤
      I := by
    rw [hI]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
      mul_nonneg (pow_nonneg (hη0 x) m) (hWx0 x)) iW (Eventually.of_forall fun x => ?_)
    show η x ^ m * ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p ≤
      η x ^ ((m : ℝ) - p) * ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p
    refine mul_le_mul_of_nonneg_right ?_ (hWx0 x)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge' (hη0 x) (hη1 x) hmp.le (by linarith)
  have hZw0 : 0 ≤ ∫ x, η x ^ m *
      ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p :=
    integral_nonneg fun x => mul_nonneg (pow_nonneg (hη0 x) m) (hWx0 x)
  have hΛε : |lam| * S ^ (p - 1) * ε ^ (1 - p) ≤ (R ^ p)⁻¹ := by
    have hε1 : ε ^ (p - 1) * ε ^ (1 - p) = 1 := by
      rw [← Real.rpow_add hε, show p - 1 + (1 - p) = (0 : ℝ) by ring, Real.rpow_zero]
    have hεpos : 0 < ε ^ (1 - p) := Real.rpow_pos_of_pos hε _
    have hRp' := hRp.ne'
    calc |lam| * S ^ (p - 1) * ε ^ (1 - p) =
          (|lam| * S ^ (p - 1) * R ^ p) * ε ^ (1 - p) * (R ^ p)⁻¹ := by field_simp
      _ ≤ ε ^ (p - 1) * ε ^ (1 - p) * (R ^ p)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΛ hεpos.le)
            (inv_nonneg.2 hRp.le)
      _ = (R ^ p)⁻¹ := by rw [hε1, one_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg m) hL0] at hen
  have hgrad : ∫ x, ‖weakGrad (fun x => η x ^ m * (cW + GW (u x))) x‖ ^ p ≤
      (R ^ p)⁻¹ * (((m : ℝ) * β) ^ p * (2 ^ p * (c⁻¹ ^ p *
        (2 ^ p * L ^ p * G ^ p + 2 * Real.log 2 ^ (1 - p)) + G ^ p))) * I := by
    have h1 : ∫ x, ‖weakGrad (fun x => η x ^ m * (cW + GW (u x))) x‖ ^ p ≤
        ∫ x, 2 ^ p * (η x ^ m * ‖(-(β * (Real.log T -
          Real.log (levelClamp σ k om (u x) + ε)) ^ (β - 1) *
            (levelClamp σ k om (u x) + ε)⁻¹)) • weakGrad u x‖ ^ p + (m : ℝ) ^ p * (G / R) ^ p *
              (η x ^ ((m : ℝ) - p) *
                ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ β) ^ p)) :=
      integral_mono_ae (integrable_norm_rpow_of_memLp hp0 hZ.memLp_weakGrad)
        ((i1.add (iW.const_mul ((m : ℝ) ^ p * (G / R) ^ p))).const_mul (2 ^ p)) hZpt
    rw [integral_const_mul, integral_add i1 (iW.const_mul _), integral_const_mul, ← hI,
      Real.div_rpow hG0 hR.le, div_eq_mul_inv] at h1
    refine h1.trans (le_of_le_of_eq (moser_step_arith
      (Real.rpow_nonneg (inv_nonneg.2 hc.le) p) (Real.one_le_rpow (by exact_mod_cast hmN) hp0.le)
      (Real.one_le_rpow hβ hp0.le) (Real.rpow_nonneg hL0 p) (Real.rpow_nonneg hG0 p)
      (inv_nonneg.2 hRp.le) (Real.rpow_nonneg (Real.log_pos (by norm_num)).le _) hΛε
      (Real.rpow_nonneg (by norm_num) p) hI0 hen hY hZw hZw0) ?_)
    rw [Real.mul_rpow (Nat.cast_nonneg m) (by linarith : (0 : ℝ) ≤ β)]
  have hIL : ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) - p) *
      (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β * p)) = ENNReal.ofReal I := by
    rw [hI, ofReal_integral_eq_lintegral_ofReal iW (Eventually.of_forall fun x =>
      mul_nonneg (Real.rpow_nonneg (hη0 x) _) (hWx0 x))]
    refine lintegral_congr fun x => ?_
    rw [Real.rpow_mul (hw0 _ (levelClamp_mem hom _))]
  have hD0 : 0 ≤ ((m : ℝ) * β) ^ p * (2 ^ p * (c⁻¹ ^ p *
      (2 ^ p * L ^ p * G ^ p + 2 * Real.log 2 ^ (1 - p)) + G ^ p)) :=
    mul_nonneg (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith)) _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg (mul_nonneg
        (Real.rpow_nonneg (inv_nonneg.2 hc.le) _) (add_nonneg (mul_nonneg (mul_nonneg
          (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hL0 _))
            (Real.rpow_nonneg hG0 _)) (mul_nonneg zero_le_two
              (Real.rpow_nonneg (Real.log_pos (by norm_num)).le _))))
        (Real.rpow_nonneg hG0 _)))
  have hgradL : ∫⁻ x, ‖weakGrad (fun x => η x ^ m * (cW + GW (u x))) x‖ₑ ^ p ≤
      ENNReal.ofReal ((R ^ p)⁻¹ * (((m : ℝ) * β) ^ p * (2 ^ p * (c⁻¹ ^ p *
        (2 ^ p * L ^ p * G ^ p + 2 * Real.log 2 ^ (1 - p)) + G ^ p)))) *
        ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) - p) *
          (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (β * p)) := by
    rw [lintegral_enorm_rpow_eq_ofReal_integral hp0 hZ.memLp_weakGrad, hIL,
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hRp.le) hD0)]
    exact ENNReal.ofReal_le_ofReal hgrad
  have hstep := mul_le_mul_right (hS1.trans (mul_le_mul_right
    (ENNReal.rpow_le_rpow hgradL hκ.le) _)) (ENNReal.ofReal ((R ^ d)⁻¹))
  refine hstep.trans (le_of_eq ?_)
  exact ennreal_moser_rescale (inv_nonneg.2 hRd.le)
    (mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg (mul_nonneg
      (Real.rpow_nonneg (by linarith) _) (inv_nonneg.2 (pow_nonneg (by linarith) _))) _))
    (inv_nonneg.2 hRp.le) hD0
    (mul_nonneg (pow_nonneg zero_le_two _) (Real.rpow_nonneg (mul_nonneg
      (Real.rpow_nonneg zero_le_two _) (inv_nonneg.2 (pow_nonneg zero_le_two _))) _))
    hκ.le (moser_scale_identity hR p κ)

end IsWeakEigensolution

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- **The scale-invariant sup bound for level functions** (Moser's iteration of
`moser_level_step` with the growing powers `η^{N^{j+1}}`, `N ≥ κp + p`, and `β = κ^j`): there is
`B`, depending only on the structural constants, such that for every ball `closedBall x₀ (2R)`
(`R ≤ 1`) carrying the scaled Sobolev inequality, every cutoff `0 ≤ η ≤ 1` supported there with
`‖∇η‖ ≤ G/R`, every level function `w = σ(u - k) ∈ [0, om]` (a.e. on the support of `η`), `ε > 0`
with `|λ| S^{p-1} R^p ≤ ε^{p-1}` and `T ≥ 2(om + ε)`, a.e. on `{η = 1}`
`(log T - log(w + ε))^p ≤ B R^{-d} ∫ η^{N-p} (log T - log(w + ε))^p`. -/
theorem moser_level_sup (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {κ : ℝ} (hκ : 1 < κ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {G : ℝ} (hG0 : 0 ≤ G) {N : ℕ} (hN : κ * p + p ≤ N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x₀ : Euc d) (R : ℝ), 0 < R → R ≤ 1 →
      (∀ w : Euc d → ℝ, MemW0 p (Metric.closedBall x₀ (2 * R)) w →
        ∫⁻ x, ‖w x‖ₑ ^ (κ * p) ≤ C * ENNReal.ofReal ((2 * R) ^ d * ((2 * R) ^ p *
          ((2 * R) ^ d)⁻¹) ^ κ) * (∫⁻ x, ‖weakGrad w x‖ₑ ^ p) ^ κ) →
      ∀ η : Euc d → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ K →
        tsupport η ⊆ Metric.closedBall x₀ (2 * R) → (∀ x, 0 ≤ η x) → (∀ x, η x ≤ 1) →
        (∀ x, ‖gradient η x‖ ≤ G / R) →
      ∀ σ k om ε T : ℝ, (σ = 1 ∨ σ = -1) → 0 ≤ om → 0 < ε → 2 * (om + ε) ≤ T →
        |lam| * S ^ (p - 1) * R ^ p ≤ ε ^ (p - 1) →
        (∀ᵐ x, x ∈ tsupport η → σ * (u x - k) ∈ Icc 0 om) →
        ∀ᵐ x, η x = 1 →
          ENNReal.ofReal ((Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ p) ≤
            ENNReal.ofReal B * (ENNReal.ofReal ((R ^ d)⁻¹) *
              ∫⁻ x, ENNReal.ofReal (η x ^ ((N : ℝ) - p) *
                (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ p)) := by
  have hp0 : 0 < p := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκp : 0 < κ * p := mul_pos hκ0 hp0
  have hN1 : (1 : ℝ) ≤ N := by nlinarith
  have hNp : p < (N : ℝ) := by nlinarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 ^ p * (c⁻¹ ^ p *
      (2 ^ p * L ^ p * G ^ p + 2 * Real.log 2 ^ (1 - p)) + G ^ p) := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ≥0∞, C' = C * ENNReal.ofReal (2 ^ d * (2 ^ p * (2 ^ d)⁻¹) ^ κ) :=
    ⟨_, rfl⟩
  have hC'top : C' ≠ ⊤ := by
    rw [hC']
    exact ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞,
      E = max (C' ^ κ⁻¹) 1 * ENNReal.ofReal (max D 1 * ((N : ℝ) * κ) ^ p) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by
    rw [hE]
    refine one_le_mul_of_one_le_of_one_le (le_max_right _ _) (ENNReal.one_le_ofReal.2 ?_)
    exact one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hN1 hκ.le) hp0.le)
  have hEtop : E ≠ ⊤ := by
    rw [hE]
    exact ENNReal.mul_ne_top (max_lt (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hκ0.le)
      hC'top) ENNReal.one_lt_top).ne ENNReal.ofReal_ne_top
  obtain ⟨B, hB0, hB⟩ := exists_rpow_iterate_bound hE1 hEtop hκ
  refine ⟨B, hB0, fun x₀ R hR hR1 hSob η hη hηs hηK hηB hη0 hη1 hG σ k om ε T hσ hom hε hT hΛ
    hlevel => ?_⟩
  have hpos : ∀ t ∈ Icc 0 om, 0 < t + ε := fun t ht => by linarith [ht.1]
  have hle : ∀ t ∈ Icc 0 om, t + ε ≤ T := fun t ht => by linarith [ht.2]
  have hw0 : ∀ x, 0 ≤ Real.log T - Real.log (levelClamp σ k om (u x) + ε) := fun x =>
    sub_nonneg.2 (Real.log_le_log (hpos _ (levelClamp_mem hom _)) (hle _ (levelClamp_mem hom _)))
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ≥0∞, ∀ j, a j = ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x,
      ENNReal.ofReal (η x ^ (((N ^ (j + 1) : ℕ) : ℝ) - p) *
        (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (κ ^ j * p)) :=
    ⟨_, fun _ => rfl⟩
  have hNj : ∀ j : ℕ, (1 : ℝ) ≤ ((N ^ (j + 1) : ℕ) : ℝ) := fun j => by
    push_cast
    exact one_le_pow₀ hN1
  have hmj : ∀ j : ℕ, κ * p * ((N ^ (j + 1) : ℕ) : ℝ) + p ≤ ((N ^ (j + 1 + 1) : ℕ) : ℝ) := by
    intro j
    have h1 := hNj j
    have e : ((N ^ (j + 1 + 1) : ℕ) : ℝ) = ((N ^ (j + 1) : ℕ) : ℝ) * N := by
      push_cast
      ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hN (zero_le_one.trans h1)]
  have hstep : ∀ j : ℕ, a (j + 1) ≤ (E ^ (j + 1) * a j) ^ κ := by
    intro j
    have hmjp : p < ((N ^ (j + 1) : ℕ) : ℝ) := by
      push_cast
      exact hNp.trans_le (le_self_pow₀ hN1 (Nat.succ_ne_zero j))
    have h1 := hu.moser_level_step hp hF hS huS hσ hom hε hT (β := κ ^ j) (one_le_pow₀ hκ.le) hc
      hcF hL0 hL hκ0 hR hSob hΛ hmjp hη hηs hηK hηB hη0 hη1 hG0 hG hlevel
    rw [← hD, ← hC', ← ha j] at h1
    have h2 : a (j + 1) ≤ ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x, ENNReal.ofReal
        (η x ^ (((N ^ (j + 1) : ℕ) : ℝ) * (κ * p)) *
          (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ (κ ^ j * (κ * p))) := by
      rw [ha (j + 1)]
      refine mul_le_mul_right (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) _
      have hexp : κ ^ (j + 1) * p = κ ^ j * (κ * p) := by ring
      rw [hexp]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (hw0 x) _)
      refine Real.rpow_le_rpow_of_exponent_ge' (hη0 x) (hη1 x)
        (mul_nonneg (Nat.cast_nonneg _) hκp.le) ?_
      have := hmj j
      linarith
    have hCX : C' ^ κ⁻¹ * ENNReal.ofReal ((((N ^ (j + 1) : ℕ) : ℝ) * κ ^ j) ^ p * D) ≤
        E ^ (j + 1) := by
      rw [hE, mul_pow]
      refine mul_le_mul' ((le_max_left _ _).trans
        (le_self_pow₀ (le_max_right _ _) (Nat.succ_ne_zero j))) ?_
      rw [← ENNReal.ofReal_pow (mul_nonneg (zero_le_one.trans (le_max_right _ _))
        (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) hκ0.le) _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hbase : ((N ^ (j + 1) : ℕ) : ℝ) * κ ^ j ≤ ((N : ℝ) * κ) ^ (j + 1) := by
        push_cast
        rw [mul_pow, pow_succ κ j]
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (pow_nonneg hκ0.le j) hκ.le)
          (pow_nonneg (Nat.cast_nonneg N) _)
      have h3 : (((N ^ (j + 1) : ℕ) : ℝ) * κ ^ j) ^ p ≤ (((N : ℝ) * κ) ^ p) ^ (j + 1) := by
        calc (((N ^ (j + 1) : ℕ) : ℝ) * κ ^ j) ^ p ≤ (((N : ℝ) * κ) ^ (j + 1)) ^ p :=
              Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hκ0.le j)) hbase
                hp0.le
          _ = (((N : ℝ) * κ) ^ p) ^ (j + 1) := by
              rw [← Real.rpow_natCast_mul (mul_nonneg (Nat.cast_nonneg N) hκ0.le),
                ← Real.rpow_mul_natCast (mul_nonneg (Nat.cast_nonneg N) hκ0.le),
                mul_comm ((j + 1 : ℕ) : ℝ) p]
      have hD1 : D ≤ max D 1 ^ (j + 1) :=
        (le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) (Nat.succ_ne_zero j))
      rw [mul_pow]
      calc (((N ^ (j + 1) : ℕ) : ℝ) * κ ^ j) ^ p * D
          ≤ (((N : ℝ) * κ) ^ p) ^ (j + 1) * max D 1 ^ (j + 1) := by
            rcases le_total 0 D with hD0 | hD0
            · exact mul_le_mul h3 hD1 hD0 (pow_nonneg (Real.rpow_nonneg
                (mul_nonneg (Nat.cast_nonneg N) hκ0.le) _) _)
            · exact (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (mul_nonneg
                (Nat.cast_nonneg _) (pow_nonneg hκ0.le j)) _) hD0).trans (mul_nonneg
                  (pow_nonneg (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) hκ0.le) _) _)
                  (pow_nonneg (zero_le_one.trans (le_max_right _ _)) _))
        _ = max D 1 ^ (j + 1) * (((N : ℝ) * κ) ^ p) ^ (j + 1) := mul_comm _ _
    have h3 : C' * (ENNReal.ofReal ((((N ^ (j + 1) : ℕ) : ℝ) * κ ^ j) ^ p * D) * a j) ^ κ ≤
        (E ^ (j + 1) * a j) ^ κ := by
      have e : C' = (C' ^ κ⁻¹) ^ κ := by
        rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hκ0.ne', ENNReal.rpow_one]
      rw [e, ← ENNReal.mul_rpow_of_nonneg _ _ hκ0.le, ← mul_assoc]
      exact ENNReal.rpow_le_rpow (mul_le_mul_left hCX _) hκ0.le
    exact h2.trans (h1.trans h3)
  have hbound := hB a hstep
  have ha0 : a 0 = ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x, ENNReal.ofReal (η x ^ ((N : ℝ) - p) *
      (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ p) := by
    rw [ha 0]
    simp only [zero_add, pow_one, pow_zero, one_mul]
  have hwpc : ContinuousOn (fun t => (Real.log T - Real.log (t + ε)) ^ p) (Icc 0 om) :=
    ((continuousOn_const.sub ((continuousOn_id.add continuousOn_const).log
      fun t ht => (hpos t ht).ne')).rpow_const fun _ _ => Or.inr hp0.le)
  obtain ⟨hwpm, Cw, hCw⟩ := hu.comp_levelClamp (σ := σ) (k := k) hom hwpc
  have hNp' : 0 < (N : ℝ) - p := by linarith
  have hRd : 0 < R ^ d := pow_pos hR d
  have ha0top : a 0 ≠ ⊤ := by
    rw [ha0]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (b := ∫⁻ x, (tsupport η).indicator (fun _ => ENNReal.ofReal Cw) x) ?_ ?_)
    · rw [lintegral_indicator (isClosed_tsupport η).measurableSet, setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hηs.isCompact.measure_lt_top.ne
    · refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ tsupport η
      · rw [indicator_of_mem hx]
        refine ENNReal.ofReal_le_ofReal ?_
        calc η x ^ ((N : ℝ) - p) * (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ p
            ≤ 1 * Cw :=
              mul_le_mul (Real.rpow_le_one (hη0 x) (hη1 x) hNp'.le)
                ((le_abs_self _).trans (hCw x)) (Real.rpow_nonneg (hw0 x) _) zero_le_one
          _ = Cw := one_mul _
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
          Real.zero_rpow hNp'.ne', zero_mul, ENNReal.ofReal_zero]
  have hUm : MeasurableSet {x : Euc d | η x = 1} :=
    measurableSet_eq_fun hη.continuous.measurable measurable_const
  have hq : ∀ n : ℕ, eLpNorm (fun x => (Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ p)
      (ENNReal.ofReal (κ ^ n)) (volume.restrict {x | η x = 1}) ≤
      ENNReal.ofReal (B * (a 0).toReal) := by
    intro n
    have hkn : 0 < κ ^ n := pow_pos hκ0 n
    have hk' : ENNReal.ofReal (κ ^ n) ≠ 0 := by simpa using hkn
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hk' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hkn.le]
    have h1 : ∫⁻ x in {x | η x = 1},
        ‖(Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ p‖ₑ ^ (κ ^ n) ≤
        ENNReal.ofReal (R ^ d) * a n := by
      rw [ha n, ← mul_assoc, ← ENNReal.ofReal_mul hRd.le, mul_inv_cancel₀ hRd.ne',
        ENNReal.ofReal_one, one_mul]
      refine (setLIntegral_mono' hUm fun x hx => le_of_eq ?_).trans
        (setLIntegral_le_lintegral _ _)
      have hx1 : η x = 1 := hx
      rw [hx1, Real.one_rpow, one_mul, ← ofReal_norm,
        Real.norm_of_nonneg (Real.rpow_nonneg (hw0 x) _),
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hw0 x) _) hkn.le,
        ← Real.rpow_mul (hw0 x), mul_comm]
    have hRd1 : ENNReal.ofReal (R ^ d) ^ (1 / κ ^ n) ≤ 1 :=
      ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (pow_le_one₀ hR.le hR1))
        (one_div_pos.2 hkn).le
    calc (∫⁻ x in {x | η x = 1},
          ‖(Real.log T - Real.log (levelClamp σ k om (u x) + ε)) ^ p‖ₑ ^ (κ ^ n)) ^ (1 / κ ^ n)
        ≤ (ENNReal.ofReal (R ^ d) * a n) ^ (1 / κ ^ n) :=
          ENNReal.rpow_le_rpow h1 (one_div_pos.2 hkn).le
      _ = ENNReal.ofReal (R ^ d) ^ (1 / κ ^ n) * a n ^ (κ ^ n)⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hkn).le, one_div]
      _ ≤ 1 * (ENNReal.ofReal B * a 0) := mul_le_mul' hRd1 (hbound n)
      _ = ENNReal.ofReal (B * (a 0).toReal) := by
          rw [one_mul, ENNReal.ofReal_mul hB0, ENNReal.ofReal_toReal ha0top]
  have hae := ae_le_of_eLpNorm_le hwpm.restrict (q := fun n => κ ^ n)
    (fun n => pow_pos hκ0 n) (tendsto_pow_atTop_atTop_of_one_lt hκ)
    (mul_nonneg hB0 ENNReal.toReal_nonneg) hq
  rw [ae_restrict_iff' hUm] at hae
  filter_upwards [hae] with x hx hx1
  rw [← ha0, ← ENNReal.ofReal_toReal ha0top, ← ENNReal.ofReal_mul hB0]
  exact ENNReal.ofReal_le_ofReal (hx hx1)

end IsWeakEigensolution

end Komlos.Literature
