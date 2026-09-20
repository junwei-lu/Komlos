import Mathlib
import Komlos.Defs
import Komlos.Literature.WangXia.MatrixAMHM

/-!
# Infimal convolution calculus (paper Appendix A)

This file formalizes the convex-analytic part of the proof of paper Proposition A.1
(Wang–Xia, Theorem 1.2), namely the paragraph *Infimal convolution and its gradients* of
paper Appendix A.

Given nonempty bounded open convex sets `K₀, K₁ ⊆ ℝ^d`, convex `C¹` functions
`v_i : K_i → ℝ` which are bounded below and tend to `+∞` at `∂K_i` (packaged as
`IsInputData`: all sublevel sets `{v_i ≤ M}` are compact), and `0 < t < 1`, the paper defines
for `z ∈ K_t = (1-t)K₀ + tK₁` and `η ≥ 0`
```
  w_η(z) = inf { (1-t)(v₀(x₀) + η|x₀|²) + t(v₁(x₁) + η|x₁|²) : x_i ∈ K_i, (1-t)x₀ + tx₁ = z }.
```
(`InfConvData.w`).  We prove:

* the infimum is attained (`InfConvData.exists_minimizer`), uniquely when `η > 0`
  (`InfConvData.IsMinimizer.eq_of_pos`);
* `w_η` is convex, continuous and bounded below on `K_t`, with `0 ≤ w_η - w₀ ≤ Cη`;
* minimizing pairs for `z` in a compact subset of `K_t` and `0 ≤ η ≤ 1` stay in fixed compact
  subsets of `K₀, K₁` (`InfConvData.exists_isCompact_minimizers`);
* the sublevel sets of `w_η` are compact, so `w_η → +∞` at `∂K_t`
  (`InfConvData.isCompact_sublevel_w`, `InfConvData.tendsto_w_frontier`);
* stationarity `∇v₀(x₀) + 2ηx₀ = ∇v₁(x₁) + 2ηx₁` at a minimizing pair
  (`InfConvData.IsMinimizer.gradient_eq`), `w_η` is differentiable with this common gradient
  (`InfConvData.IsMinimizer.hasGradientAt_w`), `w_η ∈ C¹(K_t)`
  (`InfConvData.contDiffOn_w`), and `∇w_η → ∇w₀` uniformly on compact subsets of `K_t`
  (`InfConvData.tendstoUniformlyOn_gradient_w`);
* the critical set `{∇w₀ = 0}` is a nonempty compact convex subset of `K_t`
  (`InfConvData.critical_set`).

The Hessian comparison `D²w_η = ((1-t)B₀⁻¹ + tB₁⁻¹)⁻¹ ≤ (1-t)B₀ + tB₁` (paper Appendix A,
*The differential inequality away from the critical set*) needs `C²` input data and implicit
differentiation of the stationarity equation; it is **not** part of this file.  The
arithmetic–harmonic inequality it relies on is `Komlos.Literature.matrix_amhm`.
-/

noncomputable section

namespace Komlos.Literature

open Set Filter Topology Metric Bornology
open scoped Pointwise RealInnerProductSpace

variable {d : ℕ}

/-! ### Input data -/

/-- The hypotheses on one input pair `(K, v)` of the infimal convolution of paper Appendix A:
`K` is a nonempty bounded open convex subset of `ℝ^d` and `v` is convex and `C¹` on `K`.
"Bounded below and tends to `+∞` at `∂K`" is packaged as compactness of all sublevel sets
`{x ∈ K | v x ≤ M}` (for a continuous `v` on a bounded open `K` the two are equivalent). -/
structure IsInputData (K : Set (Euc d)) (v : Euc d → ℝ) : Prop where
  isOpen : IsOpen K
  convex : Convex ℝ K
  nonempty : K.Nonempty
  isBounded : IsBounded K
  convexOn : ConvexOn ℝ K v
  contDiffOn : ContDiffOn ℝ 1 v K
  isCompact_sublevel : ∀ M : ℝ, IsCompact {x ∈ K | v x ≤ M}

namespace IsInputData

variable {K : Set (Euc d)} {v : Euc d → ℝ} (h : IsInputData K v)
include h

theorem continuousOn : ContinuousOn v K := h.contDiffOn.continuousOn

theorem differentiableAt {x : Euc d} (hx : x ∈ K) : DifferentiableAt ℝ v x :=
  (h.contDiffOn.differentiableOn one_ne_zero).differentiableAt (h.isOpen.mem_nhds hx)

theorem hasGradientAt {x : Euc d} (hx : x ∈ K) : HasGradientAt v (gradient v x) x :=
  (h.differentiableAt hx).hasGradientAt

theorem continuousOn_gradient : ContinuousOn (gradient v) K := by
  have hf := h.contDiffOn.continuousOn_fderiv_of_isOpen h.isOpen le_rfl
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn hf

/-- `v` is bounded below on `K` (it attains its minimum on a compact sublevel set). -/
theorem exists_lowerBound : ∃ m : ℝ, ∀ x ∈ K, m ≤ v x := by
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  obtain ⟨y, -, hymin⟩ := (h.isCompact_sublevel (v x₀)).exists_isMinOn ⟨x₀, hx₀, le_rfl⟩
    (h.continuousOn.mono fun x hx => hx.1)
  refine ⟨v y, fun x hx => ?_⟩
  by_cases hxle : v x ≤ v x₀
  · exact hymin ⟨hx, hxle⟩
  · exact (hymin ⟨hx₀, le_rfl⟩).trans (not_le.1 hxle).le

/-- `v → +∞` at every boundary point of `K`. -/
theorem tendsto_frontier {y : Euc d} (hy : y ∈ frontier K) : Tendsto v (𝓝[K] y) atTop := by
  refine tendsto_atTop.2 fun M => ?_
  have hyK : y ∉ K := fun hyK => hy.2 (by rwa [h.isOpen.interior_eq])
  have hcl : IsClosed {x ∈ K | v x ≤ M} := (h.isCompact_sublevel M).isClosed
  have hmem : {x ∈ K | v x ≤ M}ᶜ ∈ 𝓝 y :=
    hcl.isOpen_compl.mem_nhds fun hx => hyK hx.1
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with x hx hxK
  by_contra hlt
  exact hx ⟨hxK, (not_le.1 hlt).le⟩

end IsInputData

/-! ### Convex-analysis helpers -/

/-- Tangent-plane inequality: a convex function lies above its tangent plane at a point where it
has a gradient. -/
theorem convexOn_inner_gradient_le_sub {K : Set (Euc d)} {f : Euc d → ℝ} (hf : ConvexOn ℝ K f)
    {x y g : Euc d} (hx : x ∈ K) (hy : y ∈ K) (hg : HasGradientAt f g x) :
    ⟪g, y - x⟫ ≤ f y - f x := by
  have hconv : ConvexOn ℝ (AffineMap.lineMap x y ⁻¹' K) (f ∘ AffineMap.lineMap x y) :=
    hf.comp_affineMap _
  have h0 : (0 : ℝ) ∈ AffineMap.lineMap x y ⁻¹' K := by simp [hx]
  have h1 : (1 : ℝ) ∈ AffineMap.lineMap x y ⁻¹' K := by simp [hy]
  have hl : HasFDerivAt f (InnerProductSpace.toDual ℝ (Euc d) g)
      (AffineMap.lineMap x y (0 : ℝ)) := by
    rw [AffineMap.lineMap_apply_zero]; exact hasGradientAt_iff_hasFDerivAt.1 hg
  have hd : HasDerivAt (f ∘ AffineMap.lineMap x y) ⟪g, y - x⟫ (0 : ℝ) := by
    have := hl.comp_hasDerivAt (0 : ℝ) AffineMap.hasDerivAt_lineMap
    simpa [InnerProductSpace.toDual_apply_apply] using this
  have := hconv.le_slope_of_hasDerivAt h0 h1 zero_lt_one hd
  simpa [slope_def_field] using this

/-- The exact convexity identity for the squared norm along a convex combination. -/
theorem norm_sq_combo (x y : Euc d) {a b : ℝ} (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 = a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  rw [@norm_add_sq_real, @norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  linear_combination (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) * hab

/-- The quadratically perturbed function `v + η‖·‖²`. -/
def pert (v : Euc d → ℝ) (η : ℝ) (x : Euc d) : ℝ := v x + η * ‖x‖ ^ 2

theorem pert_zero (v : Euc d → ℝ) : pert v 0 = v := by
  ext x; simp [pert]

theorem hasGradientAt_pert {v : Euc d → ℝ} {g x : Euc d} (hv : HasGradientAt v g x) (η : ℝ) :
    HasGradientAt (pert v η) (g + (2 * η) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hv ⊢
  have h2 : HasFDerivAt (fun x : Euc d => η * ‖x‖ ^ 2) (η • (2 • innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul η
  have heq : InnerProductSpace.toDual ℝ (Euc d) g + η • (2 • innerSL ℝ x)
      = InnerProductSpace.toDual ℝ (Euc d) (g + (2 * η) • x) := by
    ext y
    simp only [_root_.add_apply, _root_.smul_apply, InnerProductSpace.toDual_apply_apply,
      innerSL_apply_apply, inner_add_left, real_inner_smul_left, smul_eq_mul]
    ring
  exact (hv.add h2).congr_fderiv heq

/-- Convexity inequality for `pert v η`, with the exact quadratic defect. -/
theorem pert_combo_le {K : Set (Euc d)} {v : Euc d → ℝ} (hv : ConvexOn ℝ K v) {x y : Euc d}
    (hx : x ∈ K) (hy : y ∈ K) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (η : ℝ) :
    pert v η (a • x + b • y) ≤ a * pert v η x + b * pert v η y - η * (a * b * ‖x - y‖ ^ 2) := by
  have h1 := hv.2 hx hy ha hb hab
  have h2 := norm_sq_combo x y hab
  simp only [smul_eq_mul] at h1
  unfold pert
  rw [h2]
  nlinarith [h1]

theorem convexOn_pert {K : Set (Euc d)} {v : Euc d → ℝ} (hv : ConvexOn ℝ K v) {η : ℝ}
    (hη : 0 ≤ η) : ConvexOn ℝ K (pert v η) := by
  refine ⟨hv.1, fun x hx y hy a b ha hb hab => ?_⟩
  have := pert_combo_le hv hx hy ha hb hab η
  have h0 : 0 ≤ η * (a * b * ‖x - y‖ ^ 2) := by positivity
  simp only [smul_eq_mul]
  linarith

theorem continuousOn_pert {K : Set (Euc d)} {v : Euc d → ℝ} (hv : ContinuousOn v K) :
    ContinuousOn (fun q : ℝ × Euc d => pert v q.1 q.2) (univ ×ˢ K) := by
  unfold pert
  refine ContinuousOn.add (hv.comp continuousOn_snd fun q hq => hq.2) ?_
  exact continuousOn_fst.mul (by fun_prop)

/-! ### The infimal-convolution data -/

/-- The data of the infimal convolution of paper Appendix A: two input pairs `(K_i, v_i)`
satisfying `IsInputData` and a parameter `0 < t < 1`. -/
structure InfConvData (d : ℕ) where
  /-- first input domain -/
  K₀ : Set (Euc d)
  /-- second input domain -/
  K₁ : Set (Euc d)
  /-- first input function -/
  v₀ : Euc d → ℝ
  /-- second input function -/
  v₁ : Euc d → ℝ
  /-- interpolation parameter -/
  t : ℝ
  h₀ : IsInputData K₀ v₀
  h₁ : IsInputData K₁ v₁
  t_pos : 0 < t
  t_lt_one : t < 1

namespace InfConvData

variable (D : InfConvData d)

/-- The Minkowski combination `K_t = (1 - t) K₀ + t K₁`. -/
def Kt : Set (Euc d) := (1 - D.t) • D.K₀ + D.t • D.K₁

/-- The feasible decompositions of `z`: pairs `(x₀, x₁) ∈ K₀ × K₁` with `(1-t)x₀ + tx₁ = z`. -/
def feasible (z : Euc d) : Set (Euc d × Euc d) :=
  {p | p.1 ∈ D.K₀ ∧ p.2 ∈ D.K₁ ∧ (1 - D.t) • p.1 + D.t • p.2 = z}

/-- The objective `(1-t)(v₀(x₀) + η|x₀|²) + t(v₁(x₁) + η|x₁|²)`. -/
def obj (η : ℝ) (p : Euc d × Euc d) : ℝ :=
  (1 - D.t) * pert D.v₀ η p.1 + D.t * pert D.v₁ η p.2

/-- The perturbed infimal convolution `w_η` of paper Appendix A. -/
noncomputable def w (η : ℝ) (z : Euc d) : ℝ := sInf (D.obj η '' D.feasible z)

/-- `p` is a minimizing pair for `w_η(z)`. -/
def IsMinimizer (η : ℝ) (z : Euc d) (p : Euc d × Euc d) : Prop :=
  p ∈ D.feasible z ∧ IsMinOn (D.obj η) (D.feasible z) p

/-- The common gradient `q_η = ∇v₀(x₀) + 2ηx₀` of a minimizing pair (see
`IsMinimizer.gradient_eq` for the equality with `∇v₁(x₁) + 2ηx₁`). -/
noncomputable def commonGrad (η : ℝ) (p : Euc d × Euc d) : Euc d :=
  gradient D.v₀ p.1 + (2 * η) • p.1

theorem one_sub_t_pos : 0 < 1 - D.t := sub_pos.2 D.t_lt_one

theorem mem_Kt {z : Euc d} : z ∈ D.Kt ↔ (D.feasible z).Nonempty := by
  constructor
  · rintro ⟨_, ⟨x₀, hx₀, rfl⟩, _, ⟨x₁, hx₁, rfl⟩, rfl⟩
    exact ⟨(x₀, x₁), hx₀, hx₁, rfl⟩
  · rintro ⟨⟨x₀, x₁⟩, hx₀, hx₁, rfl⟩
    exact ⟨_, ⟨x₀, hx₀, rfl⟩, _, ⟨x₁, hx₁, rfl⟩, rfl⟩

theorem combo_mem_Kt {x₀ x₁ : Euc d} (hx₀ : x₀ ∈ D.K₀) (hx₁ : x₁ ∈ D.K₁) :
    (1 - D.t) • x₀ + D.t • x₁ ∈ D.Kt :=
  D.mem_Kt.2 ⟨(x₀, x₁), hx₀, hx₁, rfl⟩

theorem mem_Kt_of_mem_feasible {z : Euc d} {p : Euc d × Euc d} (hp : p ∈ D.feasible z) :
    z ∈ D.Kt := D.mem_Kt.2 ⟨p, hp⟩

theorem isOpen_Kt : IsOpen D.Kt := (D.h₁.isOpen.smul₀ D.t_pos.ne').add_left

theorem convex_Kt : Convex ℝ D.Kt := (D.h₀.convex.smul _).add (D.h₁.convex.smul _)

theorem nonempty_Kt : D.Kt.Nonempty := by
  obtain ⟨x₀, hx₀⟩ := D.h₀.nonempty
  obtain ⟨x₁, hx₁⟩ := D.h₁.nonempty
  exact ⟨_, D.combo_mem_Kt hx₀ hx₁⟩

theorem isBounded_Kt : IsBounded D.Kt := (D.h₀.isBounded.smul₀ _).add (D.h₁.isBounded.smul₀ _)

theorem obj_zero (p : Euc d × Euc d) : D.obj 0 p = (1 - D.t) * D.v₀ p.1 + D.t * D.v₁ p.2 := by
  simp [obj, pert]

/-- The objective is jointly continuous in `(η, p)` on `ℝ × (K₀ × K₁)`. -/
theorem continuousOn_obj :
    ContinuousOn (fun q : ℝ × (Euc d × Euc d) => D.obj q.1 q.2) (univ ×ˢ (D.K₀ ×ˢ D.K₁)) := by
  have h0 := continuousOn_pert (K := D.K₀) D.h₀.continuousOn
  have h1 := continuousOn_pert (K := D.K₁) D.h₁.continuousOn
  unfold obj
  refine ContinuousOn.add (continuousOn_const.mul ?_) (continuousOn_const.mul ?_)
  · exact h0.comp (f := fun q : ℝ × (Euc d × Euc d) => (q.1, q.2.1)) (by fun_prop)
      fun q hq => ⟨trivial, hq.2.1⟩
  · exact h1.comp (f := fun q : ℝ × (Euc d × Euc d) => (q.1, q.2.2)) (by fun_prop)
      fun q hq => ⟨trivial, hq.2.2⟩

theorem continuousOn_obj_fixed (η : ℝ) : ContinuousOn (D.obj η) (D.K₀ ×ˢ D.K₁) :=
  D.continuousOn_obj.comp (f := fun p : Euc d × Euc d => (η, p)) (by fun_prop)
    fun p hp => ⟨trivial, hp⟩

/-- Lower bounds `m₀, m₁` of the input functions. -/
theorem exists_lowerBounds :
    ∃ m₀ m₁ : ℝ, (∀ x ∈ D.K₀, m₀ ≤ D.v₀ x) ∧ ∀ x ∈ D.K₁, m₁ ≤ D.v₁ x := by
  obtain ⟨m₀, hm₀⟩ := D.h₀.exists_lowerBound
  obtain ⟨m₁, hm₁⟩ := D.h₁.exists_lowerBound
  exact ⟨m₀, m₁, hm₀, hm₁⟩

theorem obj_zero_le_obj {η : ℝ} (hη : 0 ≤ η) (p : Euc d × Euc d) : D.obj 0 p ≤ D.obj η p := by
  unfold obj pert
  have := D.t_pos; have := D.one_sub_t_pos
  have h0 : 0 ≤ η * ‖p.1‖ ^ 2 := by positivity
  have h1 : 0 ≤ η * ‖p.2‖ ^ 2 := by positivity
  nlinarith

/-- A bound on the objective bounds each input value: `v₀(x₀) ≤ (obj - t m₁) / (1 - t)`. -/
theorem v₀_le_of_obj_le {m₁ : ℝ} (hm₁ : ∀ x ∈ D.K₁, m₁ ≤ D.v₁ x) {η : ℝ} (hη : 0 ≤ η)
    {p : Euc d × Euc d} (hp₁ : p.2 ∈ D.K₁) {M : ℝ} (hM : D.obj η p ≤ M) :
    D.v₀ p.1 ≤ (M - D.t * m₁) / (1 - D.t) := by
  rw [le_div_iff₀ D.one_sub_t_pos]
  have h := D.obj_zero_le_obj hη p
  rw [obj_zero] at h
  have := hm₁ _ hp₁
  have := D.t_pos
  nlinarith

/-- A bound on the objective bounds each input value: `v₁(x₁) ≤ (obj - (1-t) m₀) / t`. -/
theorem v₁_le_of_obj_le {m₀ : ℝ} (hm₀ : ∀ x ∈ D.K₀, m₀ ≤ D.v₀ x) {η : ℝ} (hη : 0 ≤ η)
    {p : Euc d × Euc d} (hp₀ : p.1 ∈ D.K₀) {M : ℝ} (hM : D.obj η p ≤ M) :
    D.v₁ p.2 ≤ (M - (1 - D.t) * m₀) / D.t := by
  rw [le_div_iff₀ D.t_pos]
  have h := D.obj_zero_le_obj hη p
  rw [obj_zero] at h
  have := hm₀ _ hp₀
  have := D.one_sub_t_pos
  nlinarith

/-- **Attainment** (paper Appendix A: "the infima are attained at interior pairs, because the
`v_i` are bounded below and blow up on their boundaries"). -/
theorem exists_minimizer {η : ℝ} (hη : 0 ≤ η) {z : Euc d} (hz : z ∈ D.Kt) :
    ∃ p, D.IsMinimizer η z p := by
  obtain ⟨a, ha⟩ := D.mem_Kt.1 hz
  obtain ⟨m₀, m₁, hm₀, hm₁⟩ := D.exists_lowerBounds
  set M := D.obj η a with hM
  -- the candidate minimizers lie in the compact set `C`
  set S₀ := {x ∈ D.K₀ | D.v₀ x ≤ (M - D.t * m₁) / (1 - D.t)} with hS₀
  set S₁ := {x ∈ D.K₁ | D.v₁ x ≤ (M - (1 - D.t) * m₀) / D.t} with hS₁
  set C := (S₀ ×ˢ S₁) ∩ {p : Euc d × Euc d | (1 - D.t) • p.1 + D.t • p.2 = z} with hC
  have hCc : IsCompact C := by
    refine ((D.h₀.isCompact_sublevel _).prod (D.h₁.isCompact_sublevel _)).inter_right ?_
    exact isClosed_eq (by fun_prop) continuous_const
  have hCfeas : C ⊆ D.feasible z := fun p hp => ⟨hp.1.1.1, hp.1.2.1, hp.2⟩
  have hmemC : ∀ p ∈ D.feasible z, D.obj η p ≤ M → p ∈ C := fun p hp hpM =>
    ⟨⟨⟨hp.1, D.v₀_le_of_obj_le hm₁ hη hp.2.1 hpM⟩, ⟨hp.2.1, D.v₁_le_of_obj_le hm₀ hη hp.1 hpM⟩⟩,
      hp.2.2⟩
  have haC : a ∈ C := hmemC a ha le_rfl
  obtain ⟨p, hpC, hpmin⟩ := hCc.exists_isMinOn ⟨a, haC⟩
    ((D.continuousOn_obj_fixed η).mono fun q hq => ⟨hq.1.1.1, hq.1.2.1⟩)
  refine ⟨p, hCfeas hpC, fun q hq => ?_⟩
  by_cases hqM : D.obj η q ≤ M
  · exact hpmin (hmemC q hq hqM)
  · exact (hpmin haC).trans (not_le.1 hqM).le

section Minimizer

variable {D}

theorem IsMinimizer.mem_feasible {η : ℝ} {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) : p ∈ D.feasible z := hp.1

theorem IsMinimizer.fst_mem {η : ℝ} {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) : p.1 ∈ D.K₀ := hp.1.1

theorem IsMinimizer.snd_mem {η : ℝ} {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) : p.2 ∈ D.K₁ := hp.1.2.1

theorem IsMinimizer.combo_eq {η : ℝ} {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) : (1 - D.t) • p.1 + D.t • p.2 = z := hp.1.2.2

theorem IsMinimizer.mem_Kt {η : ℝ} {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) : z ∈ D.Kt := D.mem_Kt_of_mem_feasible hp.1

theorem IsMinimizer.obj_le {η : ℝ} {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) {q : Euc d × Euc d} (hq : q ∈ D.feasible z) :
    D.obj η p ≤ D.obj η q := hp.2 hq

/-- The value of the infimal convolution at a minimizing pair. -/
theorem IsMinimizer.w_eq {η : ℝ} {z : Euc d} {p : Euc d × Euc d} (hp : D.IsMinimizer η z p) :
    D.w η z = D.obj η p :=
  IsLeast.csInf_eq ⟨⟨p, hp.1, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hp.2 hq⟩

end Minimizer

/-- `w_η(z) ≤ obj_η(p)` for every feasible `p`. -/
theorem w_le_obj {η : ℝ} (hη : 0 ≤ η) {z : Euc d} {p : Euc d × Euc d} (hp : p ∈ D.feasible z) :
    D.w η z ≤ D.obj η p := by
  obtain ⟨q, hq⟩ := D.exists_minimizer hη (D.mem_Kt_of_mem_feasible hp)
  rw [hq.w_eq]
  exact hq.obj_le hp

/-- A feasible pair realizing the value of `w_η` is a minimizer. -/
theorem isMinimizer_of_w_eq {η : ℝ} (hη : 0 ≤ η) {z : Euc d} {p : Euc d × Euc d}
    (hp : p ∈ D.feasible z) (hw : D.obj η p ≤ D.w η z) : D.IsMinimizer η z p :=
  ⟨hp, fun _ hq => hw.trans (D.w_le_obj hη hq)⟩


/-! ### Bounds, convexity and continuity of `w_η` -/

/-- `w_η` is bounded below on `K_t`, uniformly in `η ≥ 0`. -/
theorem exists_forall_le_w : ∃ m : ℝ, ∀ η, 0 ≤ η → ∀ z ∈ D.Kt, m ≤ D.w η z := by
  obtain ⟨m₀, m₁, hm₀, hm₁⟩ := D.exists_lowerBounds
  refine ⟨(1 - D.t) * m₀ + D.t * m₁, fun η hη z hz => ?_⟩
  obtain ⟨p, hp⟩ := D.exists_minimizer hη hz
  rw [hp.w_eq]
  refine le_trans ?_ (D.obj_zero_le_obj hη p)
  rw [obj_zero]
  have := hm₀ _ hp.fst_mem
  have := hm₁ _ hp.snd_mem
  have := D.t_pos
  have := D.one_sub_t_pos
  nlinarith

/-- `w₀ ≤ w_η` for `η ≥ 0`. -/
theorem w_zero_le_w {η : ℝ} (hη : 0 ≤ η) {z : Euc d} (hz : z ∈ D.Kt) : D.w 0 z ≤ D.w η z := by
  obtain ⟨p, hp⟩ := D.exists_minimizer hη hz
  rw [hp.w_eq]
  exact (D.w_le_obj le_rfl hp.mem_feasible).trans (D.obj_zero_le_obj hη p)

/-- `w_η ≤ w₀ + Cη` with `C` depending only on the (bounded) input domains
(paper Appendix A: "since the input domains are bounded, `0 ≤ w_η - w ≤ Cη`"). -/
theorem exists_w_le_w_zero_add :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η, 0 ≤ η → ∀ z ∈ D.Kt, D.w η z ≤ D.w 0 z + η * C := by
  obtain ⟨R₀, hR₀⟩ := D.h₀.isBounded.subset_closedBall 0
  obtain ⟨R₁, hR₁⟩ := D.h₁.isBounded.subset_closedBall 0
  have ht := D.t_pos.le
  have ht' := D.one_sub_t_pos.le
  refine ⟨(1 - D.t) * R₀ ^ 2 + D.t * R₁ ^ 2,
    add_nonneg (mul_nonneg ht' (sq_nonneg _)) (mul_nonneg ht (sq_nonneg _)), fun η hη z hz => ?_⟩
  obtain ⟨p, hp⟩ := D.exists_minimizer le_rfl hz
  have h1 : ‖p.1‖ ≤ R₀ := by simpa using hR₀ hp.fst_mem
  have h2 : ‖p.2‖ ≤ R₁ := by simpa using hR₁ hp.snd_mem
  have h1' : ‖p.1‖ ^ 2 ≤ R₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' : ‖p.2‖ ^ 2 ≤ R₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  calc D.w η z ≤ D.obj η p := D.w_le_obj hη hp.mem_feasible
    _ = D.obj 0 p + η * ((1 - D.t) * ‖p.1‖ ^ 2 + D.t * ‖p.2‖ ^ 2) := by
        simp only [obj, pert]; ring
    _ ≤ D.w 0 z + η * ((1 - D.t) * R₀ ^ 2 + D.t * R₁ ^ 2) := by
        rw [hp.w_eq]
        gcongr

theorem quad_nonneg (p q : Euc d × Euc d) :
    0 ≤ (1 - D.t) * ‖p.1 - q.1‖ ^ 2 + D.t * ‖p.2 - q.2‖ ^ 2 :=
  add_nonneg (mul_nonneg D.one_sub_t_pos.le (sq_nonneg _)) (mul_nonneg D.t_pos.le (sq_nonneg _))

/-- Convex combinations of feasible pairs are feasible for the combined output. -/
theorem combo_mem_feasible {z z' : Euc d} {p q : Euc d × Euc d} (hp : p ∈ D.feasible z)
    (hq : q ∈ D.feasible z') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • p + b • q ∈ D.feasible (a • z + b • z') := by
  refine ⟨D.h₀.convex hp.1 hq.1 ha hb hab, D.h₁.convex hp.2.1 hq.2.1 ha hb hab, ?_⟩
  rw [← hp.2.2, ← hq.2.2]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  module

/-- Convexity of the objective, with the exact quadratic defect coming from `η‖·‖²`. -/
theorem obj_combo_le {p q : Euc d × Euc d} (hp : p ∈ D.K₀ ×ˢ D.K₁) (hq : q ∈ D.K₀ ×ˢ D.K₁)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (η : ℝ) :
    D.obj η (a • p + b • q) ≤ a * D.obj η p + b * D.obj η q
      - η * (a * b * ((1 - D.t) * ‖p.1 - q.1‖ ^ 2 + D.t * ‖p.2 - q.2‖ ^ 2)) := by
  have h0 := pert_combo_le D.h₀.convexOn hp.1 hq.1 ha hb hab η
  have h1 := pert_combo_le D.h₁.convexOn hp.2 hq.2 ha hb hab η
  have e0 := mul_le_mul_of_nonneg_left h0 D.one_sub_t_pos.le
  have e1 := mul_le_mul_of_nonneg_left h1 D.t_pos.le
  simp only [obj, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  linarith

/-- **Convexity** of `w_η` on `K_t`. -/
theorem convexOn_w {η : ℝ} (hη : 0 ≤ η) : ConvexOn ℝ D.Kt (D.w η) := by
  refine ⟨D.convex_Kt, fun z hz z' hz' a b ha hb hab => ?_⟩
  obtain ⟨p, hp⟩ := D.exists_minimizer hη hz
  obtain ⟨q, hq⟩ := D.exists_minimizer hη hz'
  have hfeas := D.combo_mem_feasible hp.mem_feasible hq.mem_feasible ha hb hab
  have hdef : 0 ≤ η * (a * b * ((1 - D.t) * ‖p.1 - q.1‖ ^ 2 + D.t * ‖p.2 - q.2‖ ^ 2)) :=
    mul_nonneg hη (mul_nonneg (mul_nonneg ha hb) (D.quad_nonneg p q))
  calc D.w η (a • z + b • z') ≤ D.obj η (a • p + b • q) := D.w_le_obj hη hfeas
    _ ≤ a * D.obj η p + b * D.obj η q
        - η * (a * b * ((1 - D.t) * ‖p.1 - q.1‖ ^ 2 + D.t * ‖p.2 - q.2‖ ^ 2)) :=
        D.obj_combo_le ⟨hp.fst_mem, hp.snd_mem⟩ ⟨hq.fst_mem, hq.snd_mem⟩ ha hb hab η
    _ ≤ a • D.w η z + b • D.w η z' := by
        rw [hp.w_eq, hq.w_eq, smul_eq_mul, smul_eq_mul]
        linarith

/-- **Continuity** of `w_η` on the open convex set `K_t` (finite-dimensional convex functions
are continuous on open sets). -/
theorem continuousOn_w {η : ℝ} (hη : 0 ≤ η) : ContinuousOn (D.w η) D.Kt :=
  (D.convexOn_w hη).continuousOn D.isOpen_Kt

/-! ### Compactness of minimizing pairs and blow-up at the boundary -/

/-- **Compactness of minimizing pairs** (paper Appendix A: "for every compact `Z ⊂ K_t`, all
minimizing pairs with `z ∈ Z` and `0 ≤ η ≤ 1` lie in fixed compact subsets of the input
domains"). -/
theorem exists_isCompact_minimizers (H : ℝ) {Z : Set (Euc d)} (hZ : IsCompact Z)
    (hZK : Z ⊆ D.Kt) :
    ∃ S₀ S₁ : Set (Euc d), IsCompact S₀ ∧ IsCompact S₁ ∧ S₀ ⊆ D.K₀ ∧ S₁ ⊆ D.K₁ ∧
      ∀ η ∈ Icc (0 : ℝ) H, ∀ z ∈ Z, ∀ p, D.IsMinimizer η z p → p.1 ∈ S₀ ∧ p.2 ∈ S₁ := by
  obtain ⟨m₀, m₁, hm₀, hm₁⟩ := D.exists_lowerBounds
  obtain ⟨C, hC0, hC⟩ := D.exists_w_le_w_zero_add
  obtain ⟨B, hB⟩ := hZ.exists_bound_of_continuousOn ((D.continuousOn_w le_rfl).mono hZK)
  refine ⟨{x ∈ D.K₀ | D.v₀ x ≤ (B + H * C - D.t * m₁) / (1 - D.t)},
    {x ∈ D.K₁ | D.v₁ x ≤ (B + H * C - (1 - D.t) * m₀) / D.t}, D.h₀.isCompact_sublevel _,
    D.h₁.isCompact_sublevel _, fun x hx => hx.1, fun x hx => hx.1, fun η hη z hz p hp => ?_⟩
  have hM : D.obj η p ≤ B + H * C := by
    rw [← hp.w_eq]
    have h1 := hB z hz
    rw [Real.norm_eq_abs] at h1
    have h2 := le_abs_self (D.w 0 z)
    have h3 : η * C ≤ H * C := mul_le_mul_of_nonneg_right hη.2 hC0
    linarith [hC η hη.1 z (hZK hz)]
  exact ⟨⟨hp.fst_mem, D.v₀_le_of_obj_le hm₁ hη.1 hp.snd_mem hM⟩,
    ⟨hp.snd_mem, D.v₁_le_of_obj_le hm₀ hη.1 hp.fst_mem hM⟩⟩

/-- The sublevel sets of `w_η` are compact: `w_η` is bounded below and `→ +∞` at `∂K_t`
(paper Appendix A: "as `z` approaches `∂K_t`, every limiting decomposition has a component on
its input boundary; thus `w(z) → ∞`"). -/
theorem isCompact_sublevel_w {η : ℝ} (hη : 0 ≤ η) (M : ℝ) :
    IsCompact {z ∈ D.Kt | D.w η z ≤ M} := by
  obtain ⟨m₀, m₁, hm₀, hm₁⟩ := D.exists_lowerBounds
  set S₀ := {x ∈ D.K₀ | D.v₀ x ≤ (M - D.t * m₁) / (1 - D.t)} with hS₀
  set S₁ := {x ∈ D.K₁ | D.v₁ x ≤ (M - (1 - D.t) * m₀) / D.t} with hS₁
  set L := (1 - D.t) • S₀ + D.t • S₁ with hL
  have hLc : IsCompact L :=
    ((D.h₀.isCompact_sublevel _).smul _).add ((D.h₁.isCompact_sublevel _).smul _)
  have hLK : L ⊆ D.Kt :=
    add_subset_add (smul_set_mono fun x hx => hx.1) (smul_set_mono fun x hx => hx.1)
  have hsub : {z ∈ D.Kt | D.w η z ≤ M} ⊆ L := by
    rintro z ⟨hz, hzM⟩
    obtain ⟨p, hp⟩ := D.exists_minimizer hη hz
    have hM : D.obj η p ≤ M := hp.w_eq ▸ hzM
    rw [← hp.combo_eq]
    exact ⟨_, ⟨p.1, ⟨hp.fst_mem, D.v₀_le_of_obj_le hm₁ hη hp.snd_mem hM⟩, rfl⟩,
      _, ⟨p.2, ⟨hp.snd_mem, D.v₁_le_of_obj_le hm₀ hη hp.fst_mem hM⟩, rfl⟩, rfl⟩
  have heq : {z ∈ D.Kt | D.w η z ≤ M} = L ∩ D.w η ⁻¹' Iic M := by
    ext z
    exact ⟨fun hz => ⟨hsub hz, hz.2⟩, fun hz => ⟨hLK hz.1, hz.2⟩⟩
  rw [heq]
  exact hLc.of_isClosed_subset
    (((D.continuousOn_w hη).mono hLK).preimage_isClosed_of_isClosed hLc.isClosed isClosed_Iic)
    inter_subset_left

/-- `w_η → +∞` at every boundary point of `K_t`. -/
theorem tendsto_w_frontier {η : ℝ} (hη : 0 ≤ η) {y : Euc d} (hy : y ∈ frontier D.Kt) :
    Tendsto (D.w η) (𝓝[D.Kt] y) atTop := by
  refine tendsto_atTop.2 fun M => ?_
  have hyK : y ∉ D.Kt := fun hyK => hy.2 (by rwa [D.isOpen_Kt.interior_eq])
  have hmem : {z ∈ D.Kt | D.w η z ≤ M}ᶜ ∈ 𝓝 y :=
    (D.isCompact_sublevel_w hη M).isClosed.isOpen_compl.mem_nhds fun hz => hyK hz.1
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with z hz hzK
  by_contra hlt
  exact hz ⟨hzK, (not_le.1 hlt).le⟩

/-- `w_η` attains its minimum on `K_t`. -/
theorem exists_isMinOn_w {η : ℝ} (hη : 0 ≤ η) : ∃ z ∈ D.Kt, IsMinOn (D.w η) D.Kt z := by
  obtain ⟨z₀, hz₀⟩ := D.nonempty_Kt
  obtain ⟨z, hz, hzmin⟩ := (D.isCompact_sublevel_w hη (D.w η z₀)).exists_isMinOn
    ⟨z₀, hz₀, le_rfl⟩ ((D.continuousOn_w hη).mono fun x hx => hx.1)
  refine ⟨z, hz.1, fun x hx => ?_⟩
  by_cases hxle : D.w η x ≤ D.w η z₀
  · exact hzmin ⟨hx, hxle⟩
  · exact (hzmin ⟨hz₀, le_rfl⟩).trans (not_le.1 hxle).le

/-! ### Uniqueness for `η > 0` -/

variable {D} in
/-- **Uniqueness** of the minimizing pair for `η > 0` (paper Appendix A: "when `η > 0`, the
pair is unique by strict convexity"). -/
theorem IsMinimizer.eq_of_pos {η : ℝ} (hη : 0 < η) {z : Euc d} {p q : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) (hq : D.IsMinimizer η z q) : p = q := by
  by_contra hne
  have hz : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • z = z := Convex.combo_self (by norm_num) z
  have hfeas := D.combo_mem_feasible hp.mem_feasible hq.mem_feasible (a := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  rw [hz] at hfeas
  have h1 := D.obj_combo_le ⟨hp.fst_mem, hp.snd_mem⟩ ⟨hq.fst_mem, hq.snd_mem⟩ (a := 1 / 2)
    (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num) η
  have h2 := hp.obj_le hfeas
  have hpq : D.obj η p = D.obj η q :=
    le_antisymm (hp.obj_le hq.mem_feasible) (hq.obj_le hp.mem_feasible)
  have hpos : 0 < (1 - D.t) * ‖p.1 - q.1‖ ^ 2 + D.t * ‖p.2 - q.2‖ ^ 2 := by
    have hne' : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := not_and_or.1 (Prod.ext_iff.not.1 hne)
    rcases hne' with h | h
    · have : 0 < ‖p.1 - q.1‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
      have := mul_pos D.one_sub_t_pos (pow_pos this 2)
      have := mul_nonneg D.t_pos.le (sq_nonneg ‖p.2 - q.2‖)
      linarith
    · have : 0 < ‖p.2 - q.2‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
      have := mul_pos D.t_pos (pow_pos this 2)
      have := mul_nonneg D.one_sub_t_pos.le (sq_nonneg ‖p.1 - q.1‖)
      linarith
  have := mul_pos hη hpos
  nlinarith

/-- For `η > 0` the minimizing pair is unique. -/
theorem existsUnique_minimizer {η : ℝ} (hη : 0 < η) {z : Euc d} (hz : z ∈ D.Kt) :
    ∃! p, D.IsMinimizer η z p := by
  obtain ⟨p, hp⟩ := D.exists_minimizer hη.le hz
  exact ⟨p, hp, fun q hq => hq.eq_of_pos hη hp⟩


/-! ### Stationarity and the gradient of `w_η` -/

section Gradient

variable {D}

/-- **Stationarity** at a minimizing pair (paper Appendix A: "stationarity gives a common
gradient `q_η = ∇v_i(x_i) + 2ηx_i`").  Proof: the perturbation
`h ↦ (x₀ + t h, x₁ - (1 - t) h)` preserves feasibility, so `h = 0` is a local minimum of the
perturbed objective, whose derivative there is `t(1-t)(⟪q₀, ·⟫ - ⟪q₁, ·⟫)`. -/
theorem IsMinimizer.gradient_eq {η : ℝ} {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) :
    gradient D.v₀ p.1 + (2 * η) • p.1 = gradient D.v₁ p.2 + (2 * η) • p.2 := by
  set g₀ := gradient D.v₀ p.1 + (2 * η) • p.1 with hg₀def
  set g₁ := gradient D.v₁ p.2 + (2 * η) • p.2 with hg₁def
  have hg₀ : HasFDerivAt (pert D.v₀ η) (InnerProductSpace.toDual ℝ (Euc d) g₀) p.1 :=
    hasGradientAt_iff_hasFDerivAt.1 (hasGradientAt_pert (D.h₀.hasGradientAt hp.fst_mem) η)
  have hg₁ : HasFDerivAt (pert D.v₁ η) (InnerProductSpace.toDual ℝ (Euc d) g₁) p.2 :=
    hasGradientAt_iff_hasFDerivAt.1 (hasGradientAt_pert (D.h₁.hasGradientAt hp.snd_mem) η)
  set F : Euc d → ℝ := fun h =>
    (1 - D.t) * pert D.v₀ η (p.1 + D.t • h) + D.t * pert D.v₁ η (p.2 - (1 - D.t) • h) with hF
  have hmin : IsLocalMin F 0 := by
    have h0 : ∀ᶠ h in 𝓝 (0 : Euc d), p.1 + D.t • h ∈ D.K₀ :=
      (by fun_prop : Continuous fun h : Euc d => p.1 + D.t • h).continuousAt.eventually_mem
        (by simpa using D.h₀.isOpen.mem_nhds hp.fst_mem)
    have h1 : ∀ᶠ h in 𝓝 (0 : Euc d), p.2 - (1 - D.t) • h ∈ D.K₁ :=
      (by fun_prop : Continuous fun h : Euc d => p.2 - (1 - D.t) • h).continuousAt.eventually_mem
        (by simpa using D.h₁.isOpen.mem_nhds hp.snd_mem)
    filter_upwards [h0, h1] with h hh0 hh1
    have hfeas : (p.1 + D.t • h, p.2 - (1 - D.t) • h) ∈ D.feasible z := by
      refine ⟨hh0, hh1, ?_⟩
      rw [← hp.combo_eq]
      module
    have hF0 : F 0 = D.obj η p := by simp [hF, obj]
    rw [hF0]
    exact hp.obj_le hfeas
  have hd : HasFDerivAt F
      ((1 - D.t) • ((InnerProductSpace.toDual ℝ (Euc d) g₀).comp
          (D.t • ContinuousLinearMap.id ℝ (Euc d)))
        + D.t • ((InnerProductSpace.toDual ℝ (Euc d) g₁).comp
          (-((1 - D.t) • ContinuousLinearMap.id ℝ (Euc d))))) 0 := by
    have hc₀ : HasFDerivAt (fun h : Euc d => p.1 + D.t • h)
        (D.t • ContinuousLinearMap.id ℝ (Euc d)) 0 :=
      ((hasFDerivAt_id (0 : Euc d)).const_smul D.t).const_add p.1
    have hc₁ : HasFDerivAt (fun h : Euc d => p.2 - (1 - D.t) • h)
        (-((1 - D.t) • ContinuousLinearMap.id ℝ (Euc d))) 0 :=
      ((hasFDerivAt_id (0 : Euc d)).const_smul (1 - D.t)).const_sub p.2
    have hg₀' : HasFDerivAt (pert D.v₀ η) (InnerProductSpace.toDual ℝ (Euc d) g₀)
        (p.1 + D.t • (0 : Euc d)) := by simpa using hg₀
    have hg₁' : HasFDerivAt (pert D.v₁ η) (InnerProductSpace.toDual ℝ (Euc d) g₁)
        (p.2 - (1 - D.t) • (0 : Euc d)) := by simpa using hg₁
    exact ((hg₀'.comp (0 : Euc d) hc₀).const_mul (1 - D.t)).add
      ((hg₁'.comp (0 : Euc d) hc₁).const_mul D.t)
  have hzero := hmin.hasFDerivAt_eq_zero hd
  have key : ∀ h : Euc d, ⟪g₀, h⟫ = ⟪g₁, h⟫ := by
    intro h
    have := congrArg (fun L : Euc d →L[ℝ] ℝ => L h) hzero
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      _root_.neg_apply, ContinuousLinearMap.id_apply,
      InnerProductSpace.toDual_apply_apply, _root_.zero_apply, smul_eq_mul,
      inner_smul_right, inner_neg_right] at this
    have ht := mul_pos D.one_sub_t_pos D.t_pos
    have h' : (1 - D.t) * D.t * (⟪g₀, h⟫ - ⟪g₁, h⟫) = 0 := by linarith
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd h'' ht.ne'
    · linarith
  exact ext_inner_right ℝ key

/-- The common gradient can also be computed from the second component. -/
theorem IsMinimizer.commonGrad_eq {η : ℝ} {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) : D.commonGrad η p = gradient D.v₁ p.2 + (2 * η) • p.2 :=
  hp.gradient_eq

/-- The supporting-hyperplane inequality `w_η(z) + ⟪q_η, z' - z⟫ ≤ w_η(z')` at a minimizing pair
(paper Appendix A: "convexity gives the supporting lower bound"). -/
theorem IsMinimizer.w_add_inner_le {η : ℝ} (hη : 0 ≤ η) {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) {z' : Euc d} (hz' : z' ∈ D.Kt) :
    D.w η z + ⟪D.commonGrad η p, z' - z⟫ ≤ D.w η z' := by
  have hg₀ : HasGradientAt (pert D.v₀ η) (D.commonGrad η p) p.1 :=
    hasGradientAt_pert (D.h₀.hasGradientAt hp.fst_mem) η
  have hg₁ : HasGradientAt (pert D.v₁ η) (D.commonGrad η p) p.2 := by
    rw [hp.commonGrad_eq]
    exact hasGradientAt_pert (D.h₁.hasGradientAt hp.snd_mem) η
  obtain ⟨p', hp'⟩ := D.exists_minimizer hη hz'
  rw [hp'.w_eq, hp.w_eq]
  have h0 := convexOn_inner_gradient_le_sub (convexOn_pert D.h₀.convexOn hη) hp.fst_mem
    hp'.fst_mem hg₀
  have h1 := convexOn_inner_gradient_le_sub (convexOn_pert D.h₁.convexOn hη) hp.snd_mem
    hp'.snd_mem hg₁
  have hzz : z' - z = (1 - D.t) • (p'.1 - p.1) + D.t • (p'.2 - p.2) := by
    rw [← hp.combo_eq, ← hp'.combo_eq]
    module
  rw [hzz, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have e0 := mul_le_mul_of_nonneg_left h0 D.one_sub_t_pos.le
  have e1 := mul_le_mul_of_nonneg_left h1 D.t_pos.le
  simp only [obj]
  linarith

/-- **Differentiability of the infimal convolution** (paper Appendix A: "convexity gives the
supporting lower bound for `w_η(z+h)`, while shifting `x₀` by `h/(1-t)` gives the matching
first-order upper bound; hence `w_η` is differentiable and `∇w_η(z) = q_η`, also at `η = 0`,
even if the minimizing pair is not unique"). -/
theorem IsMinimizer.hasGradientAt_w {η : ℝ} (hη : 0 ≤ η) {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) : HasGradientAt (D.w η) (D.commonGrad η p) z := by
  set q := D.commonGrad η p with hq
  have hz := hp.mem_Kt
  have hg₀ : HasGradientAt (pert D.v₀ η) q p.1 :=
    hasGradientAt_pert (D.h₀.hasGradientAt hp.fst_mem) η
  -- first-order upper bound from the shifted pair `(x₀ + h/(1-t), x₁)`
  set c : ℝ := (1 - D.t)⁻¹ with hc
  set u : Euc d → ℝ := fun h =>
    (1 - D.t) * pert D.v₀ η (p.1 + c • h) + D.t * pert D.v₁ η p.2 with hu
  have hu0 : u 0 = D.w η z := by simp [hu, hp.w_eq, obj]
  have hud : HasFDerivAt u (InnerProductSpace.toDual ℝ (Euc d) q) 0 := by
    have hc₀ : HasFDerivAt (fun h : Euc d => p.1 + c • h) (c • ContinuousLinearMap.id ℝ (Euc d))
        0 := ((hasFDerivAt_id (0 : Euc d)).const_smul c).const_add p.1
    have hg₀' : HasFDerivAt (pert D.v₀ η) (InnerProductSpace.toDual ℝ (Euc d) q)
        (p.1 + c • (0 : Euc d)) := by simpa using hasGradientAt_iff_hasFDerivAt.1 hg₀
    have := ((hg₀'.comp (0 : Euc d) hc₀).const_mul (1 - D.t)).add_const (D.t * pert D.v₁ η p.2)
    refine this.congr_fderiv ?_
    ext h
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      InnerProductSpace.toDual_apply_apply, smul_eq_mul, inner_smul_right, hc]
    have hne := D.one_sub_t_pos.ne'
    field_simp
  have hupper : ∀ᶠ h in 𝓝 (0 : Euc d), D.w η (z + h) ≤ u h := by
    have h0 : ∀ᶠ h in 𝓝 (0 : Euc d), p.1 + c • h ∈ D.K₀ :=
      (by fun_prop : Continuous fun h : Euc d => p.1 + c • h).continuousAt.eventually_mem
        (by simpa using D.h₀.isOpen.mem_nhds hp.fst_mem)
    filter_upwards [h0] with h hh
    refine D.w_le_obj hη (p := (p.1 + c • h, p.2)) ⟨hh, hp.snd_mem, ?_⟩
    rw [← hp.combo_eq, smul_add, smul_smul, hc, mul_inv_cancel₀ D.one_sub_t_pos.ne', one_smul]
    abel
  -- supporting lower bound
  have hlow : ∀ᶠ h in 𝓝 (0 : Euc d), 0 ≤ D.w η (z + h) - D.w η z - ⟪q, h⟫ := by
    have hmem : ∀ᶠ h in 𝓝 (0 : Euc d), z + h ∈ D.Kt :=
      (by fun_prop : Continuous fun h : Euc d => z + h).continuousAt.eventually_mem
        (by simpa using D.isOpen_Kt.mem_nhds hz)
    filter_upwards [hmem] with h hh
    have := hp.w_add_inner_le hη hh
    rw [add_sub_cancel_left] at this
    linarith
  -- squeeze
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hu' := hasFDerivAt_iff_isLittleO_nhds_zero.1 hud
  simp only [zero_add, hu0, InnerProductSpace.toDual_apply_apply] at hu' ⊢
  refine (Asymptotics.IsBigO.of_bound 1 ?_).trans_isLittleO hu'
  filter_upwards [hlow, hupper] with h h1 h2
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1]
  exact le_trans (by linarith) (le_abs_self _)

/-- `∇w_η(z) = q_η` at any minimizing pair. -/
theorem IsMinimizer.gradient_w {η : ℝ} (hη : 0 ≤ η) {z : Euc d} {p : Euc d × Euc d}
    (hp : D.IsMinimizer η z p) : gradient (D.w η) z = D.commonGrad η p :=
  (hp.hasGradientAt_w hη).gradient

end Gradient

/-- `w_η` is differentiable on `K_t`. -/
theorem differentiableOn_w {η : ℝ} (hη : 0 ≤ η) : DifferentiableOn ℝ (D.w η) D.Kt :=
  fun z hz => by
    obtain ⟨p, hp⟩ := D.exists_minimizer hη hz
    exact (hp.hasGradientAt_w hη).differentiableAt.differentiableWithinAt


/-! ### Continuity of the gradient and uniform convergence `∇w_η → ∇w₀` -/

/-- The common gradient is jointly continuous in `(η, p)` on `ℝ × (K₀ × K₁)`. -/
theorem continuousOn_commonGrad :
    ContinuousOn (fun q : ℝ × (Euc d × Euc d) => D.commonGrad q.1 q.2)
      (univ ×ˢ (D.K₀ ×ˢ D.K₁)) := by
  unfold commonGrad
  refine ContinuousOn.add ?_ (by fun_prop)
  exact D.h₀.continuousOn_gradient.comp (f := fun q : ℝ × (Euc d × Euc d) => q.2.1) (by fun_prop)
    fun q hq => hq.2.1

/-- **Joint continuity of the gradient** `(η, z) ↦ ∇w_η(z)` on `[0, ∞) × K_t` (paper
Appendix A: "the compactness of minimizing pairs and continuity of `∇v_i` now show that
`w_η ∈ C¹(K_t)` and `∇w_η → ∇w` uniformly on compact subsets of `K_t`.  Indeed, a convergent
sequence of output points and perturbation parameters has a subsequence of minimizing pairs
converging to a minimizer for the limiting problem; its common gradient is uniquely determined
by the output point"). -/
theorem continuousOn_gradient_w :
    ContinuousOn (fun q : ℝ × Euc d => gradient (D.w q.1) q.2) (Ici (0 : ℝ) ×ˢ D.Kt) := by
  rintro ⟨η, z⟩ ⟨hη, hz⟩
  simp only [mem_Ici] at hη hz
  -- a compact neighbourhood `Z` of `z` in `K_t`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 D.isOpen_Kt z hz
  set Z := closedBall z (r / 2) with hZ
  have hZc : IsCompact Z := isCompact_closedBall z (r / 2)
  have hZK : Z ⊆ D.Kt := (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨S₀, S₁, hS₀, hS₁, hS₀K, hS₁K, hS⟩ := D.exists_isCompact_minimizers (η + 1) hZc hZK
  -- a choice of minimizers
  choose! m hm using fun (q : ℝ × Euc d) (hq : 0 ≤ q.1 ∧ q.2 ∈ D.Kt) =>
    D.exists_minimizer hq.1 hq.2
  have hnhds : ∀ p ∈ D.K₀ ×ˢ D.K₁, univ ×ˢ (D.K₀ ×ˢ D.K₁) ∈ 𝓝 (η, p) := fun p hp =>
    prod_mem_nhds univ_mem
      (prod_mem_nhds (D.h₀.isOpen.mem_nhds hp.1) (D.h₁.isOpen.mem_nhds hp.2))
  -- sequential criterion
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro u hu
  have hu_nhds : Tendsto u atTop (𝓝 (η, z)) := hu.mono_right nhdsWithin_le_nhds
  have hu_mem : ∀ᶠ n in atTop, u n ∈ Ici (0 : ℝ) ×ˢ D.Kt := (tendsto_nhdsWithin_iff.1 hu).2
  have huη : Tendsto (fun n => (u n).1) atTop (𝓝 η) := hu_nhds.fst_nhds
  have huz : Tendsto (fun n => (u n).2) atTop (𝓝 z) := hu_nhds.snd_nhds
  have hu_Z : ∀ᶠ n in atTop, (u n).2 ∈ Z := huz (closedBall_mem_nhds z (by positivity))
  have hu_le : ∀ᶠ n in atTop, (u n).1 ≤ η + 1 := huη (Iic_mem_nhds (by linarith))
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hmS : ∀ᶠ n in atTop, m (u (ns n)) ∈ S₀ ×ˢ S₁ := by
    filter_upwards [hns.eventually hu_mem, hns.eventually hu_Z, hns.eventually hu_le] with n
      hmem hZ' hle
    exact hS _ ⟨hmem.1, hle⟩ _ hZ' _ (hm _ ⟨hmem.1, hmem.2⟩)
  obtain ⟨p, hpS, φ, hφ, hφlim⟩ := (hS₀.prod hS₁).tendsto_subseq' hmS.frequently
  refine ⟨φ, ?_⟩
  set v : ℕ → ℝ × Euc d := fun n => u (ns (φ n)) with hv
  have hvt : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hlim : Tendsto v atTop (𝓝 (η, z)) := hu_nhds.comp hvt
  have hlimη : Tendsto (fun n => (v n).1) atTop (𝓝 η) := hlim.fst_nhds
  have hlimz : Tendsto (fun n => (v n).2) atTop (𝓝 z) := hlim.snd_nhds
  have hvmem : ∀ᶠ n in atTop, v n ∈ Ici (0 : ℝ) ×ˢ D.Kt := hvt.eventually hu_mem
  have hmin : ∀ᶠ n in atTop, D.IsMinimizer (v n).1 (v n).2 (m (v n)) := by
    filter_upwards [hvmem] with n hn
    exact hm _ ⟨hn.1, hn.2⟩
  have hmlim : Tendsto (fun n => m (v n)) atTop (𝓝 p) := hφlim
  have hpK : p ∈ D.K₀ ×ˢ D.K₁ := ⟨hS₀K hpS.1, hS₁K hpS.2⟩
  -- the limit pair is feasible for `z`
  have hpfeas : p ∈ D.feasible z := by
    refine ⟨hpK.1, hpK.2, ?_⟩
    have h1 : Tendsto (fun n => (1 - D.t) • (m (v n)).1 + D.t • (m (v n)).2) atTop
        (𝓝 ((1 - D.t) • p.1 + D.t • p.2)) :=
      (hmlim.fst_nhds.const_smul _).add (hmlim.snd_nhds.const_smul _)
    have h2 : Tendsto (fun n => (1 - D.t) • (m (v n)).1 + D.t • (m (v n)).2) atTop (𝓝 z) := by
      refine hlimz.congr' ?_
      filter_upwards [hmin] with n hn
      exact hn.combo_eq.symm
    exact tendsto_nhds_unique h1 h2
  -- the limit pair is a minimizer for `(η, z)`
  have hobj : Tendsto (fun n => D.obj (v n).1 (m (v n))) atTop (𝓝 (D.obj η p)) :=
    (D.continuousOn_obj.continuousAt (hnhds p hpK)).tendsto.comp (hlimη.prodMk_nhds hmlim)
  obtain ⟨p₀, hp₀⟩ := D.exists_minimizer hη hz
  set c : ℝ := (1 - D.t)⁻¹ with hc
  have hshift : Tendsto (fun n => (p₀.1 + c • ((v n).2 - z), p₀.2)) atTop (𝓝 p₀) := by
    have : Tendsto (fun n => p₀.1 + c • ((v n).2 - z)) atTop (𝓝 (p₀.1 + c • (z - z))) :=
      ((hlimz.sub_const z).const_smul c).const_add p₀.1
    simp only [sub_self, smul_zero, add_zero] at this
    exact this.prodMk_nhds tendsto_const_nhds
  -- (stated via `simpa` to keep the unifier from unfolding the shifted pair)
  have hup : Tendsto (fun n => D.obj (v n).1 (p₀.1 + c • ((v n).2 - z), p₀.2)) atTop
      (𝓝 (D.obj η p₀)) := by
    have h1 : Tendsto (fun n => ((v n).1, (p₀.1 + c • ((v n).2 - z), p₀.2))) atTop
        (𝓝 (η, p₀)) := hlimη.prodMk_nhds hshift
    have h2 : ContinuousAt (fun q : ℝ × (Euc d × Euc d) => D.obj q.1 q.2) (η, p₀) :=
      D.continuousOn_obj.continuousAt (hnhds p₀ ⟨hp₀.fst_mem, hp₀.snd_mem⟩)
    simpa only [Function.comp_def] using h2.tendsto.comp h1
  have hle : ∀ᶠ n in atTop,
      D.obj (v n).1 (m (v n)) ≤ D.obj (v n).1 (p₀.1 + c • ((v n).2 - z), p₀.2) := by
    have hK : ∀ᶠ n in atTop, p₀.1 + c • ((v n).2 - z) ∈ D.K₀ :=
      hshift.fst_nhds (D.h₀.isOpen.mem_nhds hp₀.fst_mem)
    filter_upwards [hK, hmin, hvmem] with n hn hmn hmem
    rw [← hmn.w_eq]
    refine D.w_le_obj hmem.1 (p := (p₀.1 + c • ((v n).2 - z), p₀.2)) ⟨hn, hp₀.snd_mem, ?_⟩
    rw [← hp₀.combo_eq, smul_add, smul_smul, hc, mul_inv_cancel₀ D.one_sub_t_pos.ne', one_smul]
    abel
  have hpmin : D.IsMinimizer η z p :=
    D.isMinimizer_of_w_eq hη hpfeas (by rw [hp₀.w_eq]; exact le_of_tendsto_of_tendsto hobj hup hle)
  -- the gradients converge
  have hgrad : Tendsto (fun n => D.commonGrad (v n).1 (m (v n))) atTop
      (𝓝 (D.commonGrad η p)) := by
    have h1 : Tendsto (fun n => ((v n).1, m (v n))) atTop (𝓝 (η, p)) :=
      hlimη.prodMk_nhds hmlim
    have h2 : ContinuousAt (fun q : ℝ × (Euc d × Euc d) => D.commonGrad q.1 q.2) (η, p) :=
      D.continuousOn_commonGrad.continuousAt (hnhds p hpK)
    simpa only [Function.comp_def] using h2.tendsto.comp h1
  rw [← hpmin.gradient_w hη] at hgrad
  refine hgrad.congr' ?_
  filter_upwards [hmin, hvmem] with n hn hmem
  exact (hn.gradient_w hmem.1).symm

/-- `∇w_η` is continuous on `K_t` for each `η ≥ 0`. -/
theorem continuousOn_gradient_w_fixed {η : ℝ} (hη : 0 ≤ η) :
    ContinuousOn (gradient (D.w η)) D.Kt :=
  D.continuousOn_gradient_w.comp (f := fun z => (η, z)) (by fun_prop) fun z hz => ⟨hη, hz⟩

/-- **`w_η ∈ C¹(K_t)`** for every `η ≥ 0` (paper Appendix A). -/
theorem contDiffOn_w {η : ℝ} (hη : 0 ≤ η) : ContDiffOn ℝ 1 (D.w η) D.Kt := by
  have hf : ContinuousOn (fderiv ℝ (D.w η)) D.Kt := by
    rw [← toDual_comp_gradient]
    exact (InnerProductSpace.toDual ℝ (Euc d)).continuous.comp_continuousOn
      (D.continuousOn_gradient_w_fixed hη)
  have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0) (f := D.w η)
    D.isOpen_Kt).2 ⟨D.differentiableOn_w hη, by simp, contDiffOn_zero.2 hf⟩
  simpa using h

/-- **Uniform convergence of the gradients** `∇w_η → ∇w₀` as `η ↓ 0`, on every compact subset
of `K_t` (paper Appendix A). -/
theorem tendstoUniformlyOn_gradient_w {Z : Set (Euc d)} (hZ : IsCompact Z) (hZK : Z ⊆ D.Kt) :
    TendstoUniformlyOn (fun η => gradient (D.w η)) (gradient (D.w 0)) (𝓝[Ici 0] 0) Z := by
  have hc : ContinuousOn (fun q : ℝ × Euc d => gradient (D.w q.1) q.2) (Icc (0 : ℝ) 1 ×ˢ Z) :=
    D.continuousOn_gradient_w.mono (prod_mono Icc_subset_Ici_self hZK)
  have huc : UniformContinuousOn (↿fun η : ℝ => gradient (D.w η)) (Icc (0 : ℝ) 1 ×ˢ Z) :=
    (isCompact_Icc.prod hZ).uniformContinuousOn_of_continuous hc
  have := huc.tendstoUniformlyOn (left_mem_Icc.2 zero_le_one)
  rwa [nhdsWithin_Icc_eq_nhdsGE zero_lt_one] at this

/-- `tendstoUniformlyOn_gradient_w` along `η ↓ 0`, `η > 0`. -/
theorem tendstoUniformlyOn_gradient_w_pos {Z : Set (Euc d)} (hZ : IsCompact Z)
    (hZK : Z ⊆ D.Kt) :
    TendstoUniformlyOn (fun η => gradient (D.w η)) (gradient (D.w 0)) (𝓝[>] 0) Z := by
  have := D.tendstoUniformlyOn_gradient_w hZ hZK
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at this ⊢
  exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-! ### The critical set of `w_η` -/

/-- On the open convex set `K_t`, the critical points of `w_η` are exactly its global
minimizers. -/
theorem gradient_w_eq_zero_iff {η : ℝ} (hη : 0 ≤ η) {z : Euc d} (hz : z ∈ D.Kt) :
    gradient (D.w η) z = 0 ↔ IsMinOn (D.w η) D.Kt z := by
  obtain ⟨p, hp⟩ := D.exists_minimizer hη hz
  have hg := hp.hasGradientAt_w hη
  constructor
  · intro h0 z' hz'
    have hq : D.commonGrad η p = 0 := (hp.gradient_w hη).symm.trans h0
    have := convexOn_inner_gradient_le_sub (D.convexOn_w hη) hz hz' hg
    rw [hq, inner_zero_left] at this
    exact sub_nonneg.1 this
  · intro hmin
    have h := (hmin.isLocalMin (D.isOpen_Kt.mem_nhds hz)).hasFDerivAt_eq_zero
      (hasGradientAt_iff_hasFDerivAt.1 hg)
    rw [hp.gradient_w hη]
    exact (InnerProductSpace.toDual ℝ (Euc d)).map_eq_zero_iff.1 h

/-- The critical set `{∇w_η = 0} ⊆ K_t` is the sublevel set of `w_η` at its minimum value. -/
theorem exists_critical_eq_sublevel {η : ℝ} (hη : 0 ≤ η) :
    ∃ M : ℝ, {z ∈ D.Kt | gradient (D.w η) z = 0} = {z ∈ D.Kt | D.w η z ≤ M} := by
  obtain ⟨z₀, hz₀, hmin⟩ := D.exists_isMinOn_w hη
  refine ⟨D.w η z₀, ?_⟩
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hz, h0⟩
    exact ⟨hz, (D.gradient_w_eq_zero_iff hη hz).1 h0 hz₀⟩
  · rintro ⟨hz, hle⟩
    exact ⟨hz, (D.gradient_w_eq_zero_iff hη hz).2 fun z' hz' => hle.trans (hmin hz')⟩

/-- The critical set `C = {∇w = 0}` is compact (paper Appendix A). -/
theorem isCompact_critical {η : ℝ} (hη : 0 ≤ η) :
    IsCompact {z ∈ D.Kt | gradient (D.w η) z = 0} := by
  obtain ⟨M, hM⟩ := D.exists_critical_eq_sublevel hη
  rw [hM]
  exact D.isCompact_sublevel_w hη M

/-- The critical set `C = {∇w = 0}` is convex (paper Appendix A). -/
theorem convex_critical {η : ℝ} (hη : 0 ≤ η) :
    Convex ℝ {z ∈ D.Kt | gradient (D.w η) z = 0} := by
  obtain ⟨M, hM⟩ := D.exists_critical_eq_sublevel hη
  rw [hM]
  exact (D.convexOn_w hη).convex_le M

/-- The critical set `C = {∇w = 0}` is nonempty (paper Appendix A). -/
theorem nonempty_critical {η : ℝ} (hη : 0 ≤ η) :
    ({z ∈ D.Kt | gradient (D.w η) z = 0}).Nonempty := by
  obtain ⟨z₀, hz₀, hmin⟩ := D.exists_isMinOn_w hη
  exact ⟨z₀, hz₀, (D.gradient_w_eq_zero_iff hη hz₀).2 hmin⟩

end InfConvData

end Komlos.Literature

end
