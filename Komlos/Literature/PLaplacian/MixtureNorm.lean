import Komlos.Eigenvalue
import Komlos.Literature.PLaplacian.Rayleigh
import Komlos.Literature.PLaplacian.SmoothStrictNorm

/-!
# The regularized mixture integrands `H_ε` are smooth strictly convex norms

Paper Lemma 3.2 / Appendix A: the mixture integrand `H(ξ) = ∑ α_l |⟪u_l, ξ⟫|` of a mixture is
regularized to `H_ε(ξ) = ∑ α_l √(⟪u_l, ξ⟫² + ε²‖ξ‖²)`, and `Heps_isSmoothStrictNorm` says that
`H_ε` is a norm that is `C^∞` away from the origin with `D²(H_ε²) ≻ 0` there — the hypothesis
`IsSmoothStrictNorm` of `Komlos.Literature.eigenvalue_convexity_gen`
(`Komlos/Literature/WangXia/EigenvalueConvexGen.lean`), used in `Komlos/EigenvalueConvex.lean`.

This file was split off from the former `EigenfunctionData.lean`, whose other half
(`EigenfunctionData`, `exists_eigenfunctionData`) belonged to the degenerate `p`-Laplacian
eigenfunction route that the regularized route of `REGULARIZED_ROUTE.md` replaced; see
`Komlos/Literature/Regularized/NOTES_integrate.md`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Second derivatives of `√(quadratic)` -/

/-- For `c > 0`: near `t = 0`, `t ↦ √(a t² + 2bt + c)` has derivative
`(a t + b)/√(a t² + 2bt + c)`. -/
theorem eventually_hasDerivAt_sqrt_quad {a b c : ℝ} (hc : 0 < c) :
    ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => √(a * t ^ 2 + 2 * b * t + c))
      ((a * t + b) / √(a * t ^ 2 + 2 * b * t + c)) t := by
  have hcont : Continuous fun t : ℝ => a * t ^ 2 + 2 * b * t + c := by fun_prop
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < a * t ^ 2 + 2 * b * t + c := by
    have : Tendsto (fun t : ℝ => a * t ^ 2 + 2 * b * t + c) (𝓝 0) (𝓝 c) := by
      simpa using hcont.tendsto 0
    exact this.eventually_const_lt hc
  filter_upwards [hpos] with t ht
  have hP : HasDerivAt (fun t : ℝ => a * t ^ 2 + 2 * b * t + c) (2 * a * t + 2 * b) t := by
    have := (((hasDerivAt_pow 2 t).const_mul a).add
      ((hasDerivAt_id' t).const_mul (2 * b))).add_const c
    refine this.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one]
    ring
  have hs : √(a * t ^ 2 + 2 * b * t + c) ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  refine (hP.sqrt ht.ne').congr_deriv ?_
  field_simp

/-- The derivative of `(a t + b)/√(a t² + 2bt + c)` at `t = 0` is `(a c - b²)/(c √c)`. -/
theorem hasDerivAt_sqrt_quad_deriv {a b c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun t : ℝ => (a * t + b) / √(a * t ^ 2 + 2 * b * t + c))
      ((a * c - b ^ 2) / (c * √c)) 0 := by
  have hsq := (eventually_hasDerivAt_sqrt_quad (a := a) (b := b) hc).self_of_nhds
  have hnum : HasDerivAt (fun t : ℝ => a * t + b) a 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul a).add_const b
  have hs : √(a * 0 ^ 2 + 2 * b * 0 + c) ≠ 0 := by
    simp only [mul_zero, zero_pow two_ne_zero, zero_add]
    exact (Real.sqrt_pos.2 hc).ne'
  refine (hnum.div hsq hs).congr_deriv ?_
  simp only [mul_zero, zero_pow two_ne_zero, zero_add]
  have hs' : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  field_simp
  rw [Real.sq_sqrt hc.le]
  ring

/-! ### The regularized mixture integrands `H_ε` are smooth strictly convex norms -/

section Heps

variable {N : ℕ} {α : Fin N → ℝ} {u : Fin N → Euc d}

/-- The ellipsoidal summand `√((v·ξ)² + ε²‖ξ‖²)` of `H_ε` (paper Lemma 3.2, last paragraph). -/
noncomputable def ellNorm (ε : ℝ) (v ξ : Euc d) : ℝ := √(⟪v, ξ⟫ ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2)

theorem Heps_eq_sum_ellNorm (ε : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d) (ξ : Euc d) :
    Heps ε α u ξ = ∑ l, α l * ellNorm ε (u l) ξ := rfl

/-- The ellipsoidal summand is the `L²`-product norm of the linear image `ξ ↦ (v·ξ, εξ)`, hence
convex. -/
theorem convexOn_ellNorm (ε : ℝ) (v : Euc d) : ConvexOn ℝ Set.univ (ellNorm ε v) := by
  let T : Euc d →ₗ[ℝ] WithLp 2 (ℝ × Euc d) :=
    (WithLp.linearEquiv 2 ℝ (ℝ × Euc d)).symm.toLinearMap ∘ₗ
      LinearMap.prod (innerSL ℝ v).toLinearMap (ε • LinearMap.id)
  have h := ((normSeminorm ℝ (WithLp 2 (ℝ × Euc d))).comp T).convexOn
  have heq : ellNorm ε v = ⇑((normSeminorm ℝ (WithLp 2 (ℝ × Euc d))).comp T) := by
    funext ξ
    simp only [ellNorm, Seminorm.comp_apply, coe_normSeminorm, WithLp.prod_norm_eq_of_L2]
    congr 1
    have h1 : (T ξ).fst = ⟪v, ξ⟫ := rfl
    have h2 : (T ξ).snd = ε • ξ := rfl
    rw [h1, h2, Real.norm_eq_abs, sq_abs, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [heq]
  exact h

theorem ellNorm_smul (ε : ℝ) (v : Euc d) (c : ℝ) (ξ : Euc d) :
    ellNorm ε v (c • ξ) = |c| * ellNorm ε v ξ := by
  unfold ellNorm
  have : ⟪v, c • ξ⟫ ^ 2 + ε ^ 2 * ‖c • ξ‖ ^ 2 = c ^ 2 * (⟪v, ξ⟫ ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2) := by
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem ellNorm_nonneg (ε : ℝ) (v ξ : Euc d) : 0 ≤ ellNorm ε v ξ := Real.sqrt_nonneg _

theorem mul_norm_le_ellNorm {ε : ℝ} (hε : 0 ≤ ε) (v ξ : Euc d) : ε * ‖ξ‖ ≤ ellNorm ε v ξ := by
  unfold ellNorm
  rw [Real.le_sqrt (by positivity) (by positivity), mul_pow]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The argument of the square root in `ellNorm` is positive at `ξ ≠ 0` when `ε ≠ 0`. -/
theorem ellNorm_arg_pos {ε : ℝ} (hε : ε ≠ 0) (v : Euc d) {ξ : Euc d} (hξ : ξ ≠ 0) :
    0 < ⟪v, ξ⟫ ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2 := by
  have h1 : 0 < ε ^ 2 := by positivity
  have h2 : 0 < ‖ξ‖ ^ 2 := by positivity
  positivity

/-- `H_ε(cξ) = |c| H_ε(ξ)`. -/
theorem Heps_smul (ε : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d) (c : ℝ) (ξ : Euc d) :
    Heps ε α u (c • ξ) = |c| * Heps ε α u ξ := by
  simp only [Heps_eq_sum_ellNorm, ellNorm_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `H_ε(-ξ) = H_ε(ξ)`. -/
theorem Heps_neg (ε : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d) (ξ : Euc d) :
    Heps ε α u (-ξ) = Heps ε α u ξ := by
  simpa using Heps_smul ε α u (-1) ξ

/-- `ε ‖ξ‖ ≤ H_ε(ξ)` for a mixture and `ε ≥ 0`. -/
theorem mul_norm_le_Heps (hmix : IsMixture α u) {ε : ℝ} (hε : 0 ≤ ε) (ξ : Euc d) :
    ε * ‖ξ‖ ≤ Heps ε α u ξ := by
  rw [Heps_eq_sum_ellNorm]
  calc ε * ‖ξ‖ = ∑ l, α l * (ε * ‖ξ‖) := by rw [← Finset.sum_mul, hmix.sum_eq_one, one_mul]
    _ ≤ ∑ l, α l * ellNorm ε (u l) ξ := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (mul_norm_le_ellNorm hε _ _) (hmix.nonneg l)

/-- `H_ε(ξ) > 0` for `ξ ≠ 0` and `ε > 0`. -/
theorem Heps_pos (hmix : IsMixture α u) {ε : ℝ} (hε : 0 < ε) {ξ : Euc d} (hξ : ξ ≠ 0) :
    0 < Heps ε α u ξ :=
  (mul_pos hε (norm_pos_iff.2 hξ)).trans_le (mul_norm_le_Heps hmix hε.le ξ)

/-- `H_ε` is convex for a mixture. -/
theorem convexOn_Heps (hmix : IsMixture α u) (ε : ℝ) : ConvexOn ℝ Set.univ (Heps ε α u) := by
  have : Heps ε α u = ∑ l, fun ξ => α l • ellNorm ε (u l) ξ := by
    funext ξ; rw [Finset.sum_apply, Heps_eq_sum_ellNorm]; simp only [smul_eq_mul]
  rw [this]
  exact Finset.sum_induction _ (fun f => ConvexOn ℝ Set.univ f) (fun f g hf hg => hf.add hg)
    (convexOn_const 0 convex_univ) fun l _ => (convexOn_ellNorm ε (u l)).smul (hmix.nonneg l)

/-- `H_ε` is `C^∞` away from the origin when `ε ≠ 0`. -/
theorem contDiffOn_Heps {ε : ℝ} (hε : ε ≠ 0) (α : Fin N → ℝ) (u : Fin N → Euc d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Heps ε α u) {0}ᶜ := by
  have : Heps ε α u = fun ξ => ∑ l, α l * √(⟪u l, ξ⟫ ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2) := rfl
  rw [this]
  refine ContDiffOn.sum fun l _ => contDiffOn_const.mul (ContDiffOn.sqrt ?_ ?_)
  · exact ((contDiffOn_const.inner ℝ contDiffOn_id).pow 2).add
      (contDiffOn_const.mul (contDiff_norm_sq ℝ).contDiffOn)
  · exact fun ξ hξ => (ellNorm_arg_pos hε (u l) hξ).ne'

/-- Cauchy–Schwarz for the ellipsoidal quadratic form: with `a = q(ζ)`, `b = B(ξ,ζ)`,
`c = q(ξ)` for `q(ξ) = (v·ξ)² + ε²‖ξ‖²`, one has
`a c - b² = ε² ‖(v·ζ)ξ - (v·ξ)ζ‖² + ε⁴ (‖ξ‖²‖ζ‖² - ⟪ξ,ζ⟫²)`. -/
theorem ell_ac_sub_b_sq (ε : ℝ) (v ξ ζ : Euc d) :
    (⟪v, ζ⟫ ^ 2 + ε ^ 2 * ‖ζ‖ ^ 2) * (⟪v, ξ⟫ ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2)
        - (⟪v, ξ⟫ * ⟪v, ζ⟫ + ε ^ 2 * ⟪ξ, ζ⟫) ^ 2
      = ε ^ 2 * ‖⟪v, ζ⟫ • ξ - ⟪v, ξ⟫ • ζ‖ ^ 2 + ε ^ 4 * (‖ξ‖ ^ 2 * ‖ζ‖ ^ 2 - ⟪ξ, ζ⟫ ^ 2) := by
  rw [norm_sub_sq_real, inner_smul_left, inner_smul_right, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  simp only [RCLike.conj_to_real]
  ring

theorem ell_b_sq_le (ε : ℝ) (v ξ ζ : Euc d) :
    (⟪v, ξ⟫ * ⟪v, ζ⟫ + ε ^ 2 * ⟪ξ, ζ⟫) ^ 2 ≤
      (⟪v, ζ⟫ ^ 2 + ε ^ 2 * ‖ζ‖ ^ 2) * (⟪v, ξ⟫ ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2) := by
  have h := ell_ac_sub_b_sq ε v ξ ζ
  have hY : 0 ≤ ‖ξ‖ ^ 2 * ‖ζ‖ ^ 2 - ⟪ξ, ζ⟫ ^ 2 := by
    have := real_inner_mul_inner_self_le ξ ζ
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    nlinarith
  nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖⟪v, ζ⟫ • ξ - ⟪v, ξ⟫ • ζ‖),
    mul_nonneg (pow_nonneg (sq_nonneg ε) 2) hY]

/-- Strict Cauchy–Schwarz for nonparallel `ξ, ζ`. -/
theorem ell_b_sq_lt {ε : ℝ} (hε : ε ≠ 0) (v : Euc d) {ξ ζ : Euc d} (hξ : ξ ≠ 0) (hζ : ζ ≠ 0)
    (hpar : ¬ ∃ μ : ℝ, ζ = μ • ξ) :
    (⟪v, ξ⟫ * ⟪v, ζ⟫ + ε ^ 2 * ⟪ξ, ζ⟫) ^ 2 <
      (⟪v, ζ⟫ ^ 2 + ε ^ 2 * ‖ζ‖ ^ 2) * (⟪v, ξ⟫ ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2) := by
  have h := ell_ac_sub_b_sq ε v ξ ζ
  have hY : 0 < ‖ξ‖ ^ 2 * ‖ζ‖ ^ 2 - ⟪ξ, ζ⟫ ^ 2 := by
    have h0 := real_inner_mul_inner_self_le ξ ζ
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h0
    refine lt_of_le_of_ne (by nlinarith) fun heq => hpar ?_
    have h1 : ⟪ξ, ζ⟫ ^ 2 = (‖ξ‖ * ‖ζ‖) ^ 2 := by rw [mul_pow]; linarith
    have h2 : |⟪ξ, ζ⟫| = ‖ξ‖ * ‖ζ‖ := by
      rw [← abs_of_nonneg (mul_nonneg (norm_nonneg ξ) (norm_nonneg ζ))]
      exact (sq_eq_sq_iff_abs_eq_abs _ _).1 h1
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff (𝕜 := ℝ) hξ hζ).1
      (by rw [Real.norm_eq_abs]; exact h2)
    exact ⟨r, hr⟩
  have hε4 : 0 < ε ^ 4 := by positivity
  nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖⟪v, ζ⟫ • ξ - ⟪v, ξ⟫ • ζ‖), mul_pos hε4 hY]

/-- A mixture has a positive weight. -/
theorem exists_pos_of_isMixture (hmix : IsMixture α u) : ∃ l, 0 < α l := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have := Finset.sum_nonpos (s := Finset.univ) fun l _ => h l
  rw [hmix.sum_eq_one] at this
  exact absurd this (by norm_num)

/-- **Strong convexity of `H_ε²`** (paper Lemma 3.2, last paragraph): for a mixture and
`ε > 0`, `D²(H_ε²)(ξ)` is positive definite at every `ξ ≠ 0`. -/
theorem Heps_sq_hessian_pos (hmix : IsMixture α u) {ε : ℝ} (hε : 0 < ε) {ξ : Euc d}
    (hξ : ξ ≠ 0) {ζ : Euc d} (hζ : ζ ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (fun x => Heps ε α u x ^ 2)) ξ ζ ζ := by
  set g : Euc d → ℝ := fun x => Heps ε α u x ^ 2 with hg_def
  have hg : ContDiffAt ℝ 2 g ξ :=
    (((contDiffOn_Heps hε.ne' α u).contDiffAt (isOpen_compl_singleton.mem_nhds hξ)).pow 2).of_le
      (WithTop.coe_le_coe.2 le_top)
  -- the coefficients of the quadratic polynomials `q_l(ξ + tζ) = a_l t² + 2 b_l t + c_l`
  set a : Fin N → ℝ := fun l => ⟪u l, ζ⟫ ^ 2 + ε ^ 2 * ‖ζ‖ ^ 2 with ha_def
  set b : Fin N → ℝ := fun l => ⟪u l, ξ⟫ * ⟪u l, ζ⟫ + ε ^ 2 * ⟪ξ, ζ⟫ with hb_def
  set c : Fin N → ℝ := fun l => ⟪u l, ξ⟫ ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2 with hc_def
  have hP : ∀ l (t : ℝ), ⟪u l, ξ + t • ζ⟫ ^ 2 + ε ^ 2 * ‖ξ + t • ζ‖ ^ 2
      = a l * t ^ 2 + 2 * b l * t + c l := by
    intro l t
    simp only [ha_def, hb_def, hc_def, inner_add_right, inner_smul_right, norm_add_sq_real,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hc : ∀ l, 0 < c l := fun l => ellNorm_arg_pos hε.ne' (u l) hξ
  have hcs : ∀ l, 0 < √(c l) := fun l => Real.sqrt_pos.2 (hc l)
  have hac : ∀ l, b l ^ 2 ≤ a l * c l := fun l => ell_b_sq_le ε (u l) ξ ζ
  -- the one-dimensional restriction `h(t) = H_ε(ξ + tζ)` and its derivative
  set h : ℝ → ℝ := fun t => ∑ l, α l * √(a l * t ^ 2 + 2 * b l * t + c l) with hh_def
  set h' : ℝ → ℝ := fun t =>
    ∑ l, α l * ((a l * t + b l) / √(a l * t ^ 2 + 2 * b l * t + c l)) with hh'_def
  set h''0 : ℝ := ∑ l, α l * ((a l * c l - b l ^ 2) / (c l * √(c l))) with hh''_def
  have hh : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt h (h' t) t := by
    have : ∀ᶠ t : ℝ in 𝓝 0, ∀ l, HasDerivAt (fun t => √(a l * t ^ 2 + 2 * b l * t + c l))
        ((a l * t + b l) / √(a l * t ^ 2 + 2 * b l * t + c l)) t :=
      eventually_all.2 fun l => eventually_hasDerivAt_sqrt_quad (hc l)
    filter_upwards [this] with t ht
    exact HasDerivAt.fun_sum fun l _ => (ht l).const_mul (α l)
  have hh' : HasDerivAt h' h''0 0 :=
    HasDerivAt.fun_sum fun l _ => (hasDerivAt_sqrt_quad_deriv (hc l)).const_mul (α l)
  have hfun : (fun t : ℝ => g (ξ + t • ζ)) = fun t => h t ^ 2 := by
    funext t
    simp only [hg_def, hh_def, Heps, hP]
  -- the second derivative along the line, computed two ways
  have hφ : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => g (ξ + t • ζ)) (2 * h t * h' t) t := by
    rw [hfun]
    filter_upwards [hh] with t ht
    refine (ht.fun_pow 2).congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  have heq : (fun t : ℝ => fderiv ℝ g (ξ + t • ζ) ζ) =ᶠ[𝓝 0] fun t => 2 * h t * h' t := by
    filter_upwards [hφ, eventually_hasDerivAt_line hg ζ] with t h1 h2
    exact h2.unique h1
  have hD : HasDerivAt (fun t : ℝ => 2 * h t * h' t) (fderiv ℝ (fderiv ℝ g) ξ ζ ζ) 0 :=
    (hasDerivAt_fderiv_line hg ζ).congr_of_eventuallyEq heq.symm
  have hD' : HasDerivAt (fun t : ℝ => 2 * h t * h' t) (2 * h' 0 * h' 0 + 2 * h 0 * h''0) 0 :=
    (hh.self_of_nhds.const_mul 2).mul hh'
  rw [hD.unique hD']
  -- evaluate at `t = 0`
  have h0 : h 0 = Heps ε α u ξ := by
    simp only [hh_def, Heps, hc_def, mul_zero, zero_pow two_ne_zero, zero_add]
  have h'0 : h' 0 = ∑ l, α l * (b l / √(c l)) := by
    simp only [hh'_def, mul_zero, zero_pow two_ne_zero, zero_add]
  have hHpos : 0 < h 0 := h0 ▸ Heps_pos hmix hε hξ
  have hh''_nonneg : 0 ≤ h''0 :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hmix.nonneg l)
      (div_nonneg (by linarith [hac l]) (mul_pos (hc l) (hcs l)).le)
  -- strictness: either `ζ ∥ ξ` (then `h'(0) = μ H_ε(ξ) ≠ 0`) or not (then `h''(0) > 0`)
  have key : 0 < h''0 ∨ h' 0 ≠ 0 := by
    by_cases hpar : ∃ μ : ℝ, ζ = μ • ξ
    · right
      obtain ⟨μ, rfl⟩ := hpar
      have hμ : μ ≠ 0 := by rintro rfl; simp at hζ
      have hb : ∀ l, b l = μ * c l := by
        intro l
        simp only [hb_def, hc_def, inner_smul_right, real_inner_self_eq_norm_sq]
        ring
      have : h' 0 = μ * Heps ε α u ξ := by
        rw [h'0, Heps_eq_sum_ellNorm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hb, mul_div_assoc, Real.div_sqrt]
        simp only [ellNorm, hc_def]
        ring
      rw [this]
      exact mul_ne_zero hμ (Heps_pos hmix hε hξ).ne'
    · left
      obtain ⟨l₀, hl₀⟩ := exists_pos_of_isMixture hmix
      refine Finset.sum_pos' (fun l _ => mul_nonneg (hmix.nonneg l)
        (div_nonneg (by linarith [hac l]) (mul_pos (hc l) (hcs l)).le)) ⟨l₀, Finset.mem_univ _, ?_⟩
      have hlt : b l₀ ^ 2 < a l₀ * c l₀ := ell_b_sq_lt hε.ne' (u l₀) hξ hζ hpar
      exact mul_pos hl₀ (div_pos (by linarith) (mul_pos (hc l₀) (hcs l₀)))
  rcases key with hk | hk
  · nlinarith [mul_self_nonneg (h' 0), mul_pos hHpos hk]
  · nlinarith [mul_self_pos.2 hk, mul_nonneg hHpos.le hh''_nonneg]

/-- **`H_ε` is a smooth strictly convex norm** (paper Lemma 3.2, last paragraph): for a mixture
`(α, u)` and `ε > 0`, `Heps ε α u` belongs to the class of Proposition A.1. -/
theorem Heps_isSmoothStrictNorm (hmix : IsMixture α u) {ε : ℝ} (hε : 0 < ε) :
    IsSmoothStrictNorm (Heps ε α u) where
  even := Heps_neg ε α u
  pos := fun _ hξ => Heps_pos hmix hε hξ
  homog := Heps_smul ε α u
  convexOn := convexOn_Heps hmix ε
  contDiffOn := contDiffOn_Heps hε.ne' α u
  hessian_sq_pos := fun _ hξ _ hζ => Heps_sq_hessian_pos hmix hε hξ hζ

end Heps

end Komlos.Literature
