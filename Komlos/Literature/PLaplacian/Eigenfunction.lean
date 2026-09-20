import Komlos.Literature.Sobolev.Defs
import Komlos.Literature.Sobolev.Density
import Komlos.Literature.Sobolev.Rellich
import Komlos.Literature.PLaplacian.Rayleigh
import Komlos.Literature.PLaplacian.SmoothStrictNorm
import Komlos.Literature.PLaplacian.EigenfunctionAux

/-!
# The direct method: a first eigenfunction of the anisotropic `p`-Laplacian

Paper Appendix A, *Eigenfunction inputs*: "The direct method gives a nonnegative, nonzero first
eigenfunction `u_i ∈ W_0^{1,p}(K_i)`. It minimizes `w ↦ (1/p) ∫ F(∇w)^p − (λ_i/p) ∫ w^p`, whose
minimum is zero by the definition of `λ_i`." This file proves that sentence for a smooth strictly
convex norm `F` (`IsSmoothStrictNorm`), `1 < p`, and a nonempty bounded open convex `K`, together
with the weak Euler–Lagrange (eigenvalue) equation.

## Main results

* `exists_minimizer` — there is `u ∈ W₀^{1,p}(K)`, `u ≥ 0`, `u = 0` off `K`, `∫ |u|^p = 1`, with
  `∫ F(∇u)^p = lambdaSob p F K` (the Rayleigh infimum over `W₀^{1,p}(K)`, equal to the smooth
  one `lambdaGen p F K` by `lambdaSob_eq_lambdaGen`);
* `weak_euler_lagrange` — a minimizer satisfies `∫ ⟪a(∇u), ∇ψ⟫ = λ ∫ |u|^{p-2} u ψ` for every
  `ψ ∈ W₀^{1,p}(K)`, where `a = flux p F`; `weak_euler_lagrange_testFn` is the form
  `∫ ⟪a(∇u), ∇ψ⟫ = λ ∫ u^{p-1} ψ` against smooth test functions used by `EigenfunctionData`;
* `exists_eigenfunction_weak` — the two combined, with `λ = lambdaGen p F K`.

## Proof strategy (no weak compactness)

Mathlib has no weak compactness of bounded sets in `L^p`, so the classical "weak limit + weak
lower semicontinuity" step is replaced by **uniform convexity** of `Φ = F^p`
(`IsSmoothStrictNorm.exists_norm_sub_rpow_le`), which makes a minimizing sequence converge
*strongly* in `W^{1,p}`:

1. `exists_nonneg_near_minimizer`: nonnegative normalized near-minimizers exist among smooth test
   functions (replace a test function `f` by `√(f² + ε²) − ε`, which does not increase the energy).
2. Rellich (`rellich`) gives an `L^p`-convergent subsequence `w_k → u`, `‖u‖_p = 1`.
3. `integral_norm_sub_rpow_le`: `∫ ‖∇w_k − ∇w_l‖^p ≤ C_ε (E_k/2 + E_l/2 − λ ∫ |(w_k+w_l)/2|^p)
   + ε 2^p (∫ ‖∇w_k‖^p + ∫ ‖∇w_l‖^p)`, since `(w_k + w_l)/2` is an admissible competitor. As
   `E_k → λ` and `∫ |(w_k+w_l)/2|^p → 1`, the gradients are Cauchy in `L^p`
   (`tendsto_integral_norm_gradient_sub`).
4. The gradient limit is a weak gradient of `u` (`HasWeakGradient.of_tendsto`), and the energy
   passes to the limit by continuity of Nemytskii functionals.

The Euler–Lagrange equation follows by differentiating `t ↦ ∫ F(∇u + t∇ψ)^p − λ ∫ |u + tψ|^p`
(which is `≥ 0` with a zero at `t = 0`) under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), using `D(F^p)(ξ) = p ⟪a(ξ), ·⟫`
(`IsSmoothStrictNorm.hasFDerivAt_rpow`) and `‖a(ξ)‖ ≤ C ‖ξ‖^{p-1}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Preliminaries -/

section Prelim

/-- A lower bound `c ‖ξ‖ ≤ F ξ` with `c > 0`, in every dimension (for `d = 0` the norm vanishes). -/
theorem IsSmoothStrictNorm.exists_pos_mul_norm_le' {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ, c * ‖ξ‖ ≤ F ξ := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨1, one_pos, fun ξ => ?_⟩
    have : ξ = 0 := Subsingleton.elim _ _
    simp [this, hF.map_zero]
  · exact hF.exists_pos_mul_norm_le

/-- `∫ ‖f‖^p` is finite for `f ∈ L^p`. -/
theorem integrable_norm_rpow_of_memLp {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ} (hp0 : 0 < p) {f : α → E}
    (hf : MemLp f (ENNReal.ofReal p) μ) : Integrable (fun x => ‖f x‖ ^ p) μ := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  simpa [ENNReal.toReal_ofReal hp0.le] using hf.integrable_norm_rpow hp' ENNReal.ofReal_ne_top

/-- `‖f‖_{L^p} = (∫ ‖f‖^p)^{1/p}` for `f ∈ L^p`. -/
theorem eLpNorm_eq_ofReal_integral {E : Type*} [NormedAddCommGroup E] {p : ℝ} (hp0 : 0 < p)
    {f : Euc d → E} (hf : MemLp f (ENNReal.ofReal p)) :
    eLpNorm f (ENNReal.ofReal p) = ENNReal.ofReal ((∫ x, ‖f x‖ ^ p) ^ p⁻¹) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]

/-- A `C¹` compactly supported function with support in `K` lies in `W₀^{1,p}(K)`. -/
theorem memW0_of_contDiff {K : Set (Euc d)} {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) (hfK : tsupport f ⊆ K) (p : ℝ) : MemW0 p K f where
  memLp := hf.continuous.memLp_of_hasCompactSupport hfs
  ae_eq_zero := Eventually.of_forall fun _ hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfK h)
  exists_weakGradient :=
    ⟨gradient f, hasWeakGradient_gradient hf hfs,
      (continuous_gradient hf).memLp_of_hasCompactSupport (hasCompactSupport_gradient hfs)⟩

/-- If `g` has derivative `c • Df(x)` at `x`, then `∇g(x) = c • ∇f(x)`. -/
theorem gradient_eq_smul_of_hasFDerivAt {f g : Euc d → ℝ} {x : Euc d} {c : ℝ}
    (h : HasFDerivAt g (c • fderiv ℝ f x) x) : gradient g x = c • gradient f x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [real_inner_smul_left, inner_gradient_left, inner_gradient_left, h.fderiv]
  try rfl

theorem gradient_const_smul_apply {f : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x)
    (c : ℝ) : gradient (c • f) x = c • gradient f x :=
  gradient_eq_smul_of_hasFDerivAt (hf.hasFDerivAt.const_smul c)

/-- The gradient of `(f + g)/2`, written as a lambda. -/
theorem gradient_half_add_apply {f g : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => (1 / 2 : ℝ) * (f y + g y)) x =
      (1 / 2 : ℝ) • (gradient f x + gradient g x) := by
  have h : HasFDerivAt (fun y => (1 / 2 : ℝ) * (f y + g y))
      ((1 / 2 : ℝ) • (fderiv ℝ f x + fderiv ℝ g x)) x :=
    (hf.hasFDerivAt.add hg.hasFDerivAt).const_mul (1 / 2 : ℝ)
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, h.fderiv, real_inner_smul_left, inner_add_left, inner_gradient_left,
    inner_gradient_left]
  try rfl

/-- Continuity of `(ξ, η) ↦ c ⟪G(ξ + t η), η⟫` (stated for a general inner product space so that it
specializes to `ℝ^d` without unfolding the Euclidean-space instances). -/
theorem continuous_mul_inner_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : E → E} (hG : Continuous G) (c t : ℝ) :
    Continuous fun z : E × E => c * ⟪G (z.1 + t • z.2), z.2⟫ :=
  continuous_const.mul ((hG.comp (continuous_fst.add (continuous_snd.const_smul t))).inner
    continuous_snd)

/-- Measurability of `x ↦ c ⟪G(a x + t b x), b x⟫`. -/
theorem aestronglyMeasurable_mul_inner_comp {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {G : E → E} (hG : Continuous G) (c t : ℝ)
    {a b : α → E} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) :
    AEStronglyMeasurable (fun x => c * ⟪G (a x + t • b x), b x⟫) μ :=
  (continuous_mul_inner_comp hG c t).comp_aestronglyMeasurable (ha.prodMk hb)

/-- `‖g i‖_q → ‖g_∞‖_q` along any filter when `‖g i − g_∞‖_q → 0` (`1 ≤ q`). -/
theorem tendsto_eLpNorm_of_tendsto_eLpNorm_sub_filter {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {q : ℝ≥0∞} (hq : 1 ≤ q) {g : ι → α → ℝ} {gLim : α → ℝ}
    (hg : ∀ i, AEStronglyMeasurable (g i) μ) (hgLim : MemLp gLim q μ)
    (hlim : Tendsto (fun i => eLpNorm (g i - gLim) q μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (g i) q μ) l (𝓝 (eLpNorm gLim q μ)) := by
  have hup : ∀ n, eLpNorm (g n) q μ ≤ eLpNorm (g n - gLim) q μ + eLpNorm gLim q μ := fun n => by
    have := eLpNorm_add_le ((hg n).sub hgLim.1) hgLim.1 hq
    simpa only [sub_add_cancel] using this
  have hlow : ∀ n, eLpNorm gLim q μ - eLpNorm (g n - gLim) q μ ≤ eLpNorm (g n) q μ := fun n => by
    rw [tsub_le_iff_left]
    have := eLpNorm_add_le (hgLim.1.sub (hg n)) (hg n) hq
    rw [sub_add_cancel, eLpNorm_sub_comm] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_ hlow hup
  · have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := eLpNorm gLim q μ)) hlim
      (Or.inl hgLim.eLpNorm_ne_top)
    simpa using this
  · simpa using hlim.add (tendsto_const_nhds (x := eLpNorm gLim q μ))

/-- `λ_{p,F}(K) ∫ |f|^p ≤ ∫ F(∇f)^p` for every smooth `f` compactly supported in `K` (including
`f = 0`). -/
theorem lambdaGen_mul_le {p : ℝ} (hp : 0 < p) {F : Euc d → ℝ} (hF0 : ∀ ξ, 0 ≤ F ξ)
    {K : Set (Euc d)} {f : Euc d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfs : HasCompactSupport f)
    (hfK : tsupport f ⊆ K) :
    lambdaGen p F K * ∫ x, |f x| ^ p ≤ ∫ x, F (gradient f x) ^ p := by
  by_cases h0 : f = 0
  · subst h0
    simp only [Pi.zero_apply, abs_zero, Real.zero_rpow hp.ne', integral_zero, mul_zero]
    exact integral_nonneg fun _ => Real.rpow_nonneg (hF0 _) p
  · have htf : IsTestFn K f := ⟨hf, hfs, hfK, h0⟩
    have hpos : 0 < ∫ x, |f x| ^ p :=
      integral_abs_rpow_pos hp (htf.memW0 p).memLp htf.not_ae_eq_zero
    have h := lambdaGen_le_rayleighGen hF0 p htf
    rwa [rayleighGen, le_div_iff₀ hpos] at h

/-- `λ ∫ |f|^p ≤ ∫ F(∇f)^p` for every `f ∈ W₀^{1,p}(K)`, `λ = lambdaSob p F K` (including
`f =ᵐ 0`). -/
theorem lambdaSob_mul_le {p : ℝ} (hp : 0 < p) {F : Euc d → ℝ} (hF0 : ∀ ξ, 0 ≤ F ξ)
    {K : Set (Euc d)} {f : Euc d → ℝ} (hf : MemW0 p K f) :
    lambdaSob p F K * ∫ x, |f x| ^ p ≤ ∫ x, F (weakGrad f x) ^ p := by
  by_cases h0 : f =ᵐ[volume] 0
  · have h1 : (fun x => |f x| ^ p) =ᵐ[volume] fun _ => (0 : ℝ) :=
      h0.mono fun x hx => by simp only [hx, Pi.zero_apply, abs_zero, Real.zero_rpow hp.ne']
    rw [integral_congr_ae h1, integral_zero, mul_zero]
    exact integral_nonneg fun _ => Real.rpow_nonneg (hF0 _) p
  · have hpos := integral_abs_rpow_pos hp hf.memLp h0
    have h := lambdaSob_le_sobolevRayleigh hF0 hf h0
    rwa [sobolevRayleigh, sobolevEnergy, le_div_iff₀ hpos] at h

end Prelim

/-! ### Nonnegative normalized near-minimizers -/

section NearMinimizer

/-- The derivative of `√(f² + ε²) − ε` is `(f / √(f² + ε²)) Df`. -/
theorem hasFDerivAt_sqrt_sq_add_sq_sub {f : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x)
    {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt (fun y => √(f y ^ 2 + ε ^ 2) - ε)
      ((f x / √(f x ^ 2 + ε ^ 2)) • fderiv ℝ f x) x := by
  have hpos : 0 < f x ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ε ^ 2) (2 * f x) (f x) := by
    simpa using (hasDerivAt_pow 2 (f x)).add_const (ε ^ 2)
  have hg : HasDerivAt (fun s : ℝ => √(s ^ 2 + ε ^ 2) - ε) (f x / √(f x ^ 2 + ε ^ 2)) (f x) := by
    refine ((h1.sqrt hpos.ne').sub_const ε).congr_deriv ?_
    exact mul_div_mul_left _ _ two_ne_zero
  exact hg.comp_hasFDerivAt x hf.hasFDerivAt

/-- **Nonnegative normalized near-minimizers** (step 1 of the direct method): for every `δ > 0`
there is a nonnegative smooth test function `v` on `K` with `∫ |v|^p = 1` and
`∫ F(∇v)^p < λ_{p,F}(K) + δ`. A near-minimizing test function `f` is replaced by
`√(f² + ε²) − ε` (smooth, same support, energy not larger since `|f| ≤ √(f² + ε²)`, and
`∫ |·|^p → ∫ |f|^p` as `ε → 0`), then normalized. -/
theorem exists_nonneg_near_minimizer {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : Euc d → ℝ, IsTestFn K v ∧ (∀ x, 0 ≤ v x) ∧ ∫ x, |v x| ^ p = 1 ∧
      ∫ x, F (gradient v x) ^ p < lambdaGen p F K + δ := by
  have hp0 : 0 < p := by linarith
  have := hK.nonempty_testFn
  obtain ⟨f, hf, hlt⟩ := exists_testFn_rayleighGen_lt (K := K) p F (half_pos hδ)
  have hApos : 0 < ∫ x, |f x| ^ p :=
    integral_abs_rpow_pos hp0 (hf.memW0 p).memLp hf.not_ae_eq_zero
  have hfd : ∀ x, DifferentiableAt ℝ f x := fun x => hf.contDiff_one.differentiable one_ne_zero x
  -- the regularizations `√(f² + εₙ²) − εₙ`, `εₙ = 1/(n+1)`
  have hε : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => Nat.one_div_pos_of_nat
  have hpos : ∀ (n : ℕ) x, 0 < f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2 := fun n x =>
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (hε n) 2)
  have hgrad : ∀ (n : ℕ) x, gradient (fun y => √(f y ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) -
      1 / ((n : ℝ) + 1)) x = (f x / √(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) • gradient f x :=
    fun n x => gradient_eq_smul_of_hasFDerivAt (hasFDerivAt_sqrt_sq_add_sq_sub (hfd x) (hε n))
  have hsmooth : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => √(f y ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)) := fun n =>
    (((hf.contDiff.pow 2).add contDiff_const).sqrt fun x => (hpos n x).ne').sub contDiff_const
  have hh0 : ∀ (n : ℕ) x, 0 ≤ √(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1) := by
    intro n x
    have h1 : 1 / ((n : ℝ) + 1) ≤ √(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) := by
      calc 1 / ((n : ℝ) + 1) = √((1 / ((n : ℝ) + 1)) ^ 2) := (Real.sqrt_sq (hε n).le).symm
        _ ≤ √(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
    linarith
  have hhle : ∀ (n : ℕ) x, √(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1) ≤ |f x| := by
    intro n x
    have h1 : f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2 ≤ (|f x| + 1 / ((n : ℝ) + 1)) ^ 2 := by
      nlinarith [abs_nonneg (f x), (hε n).le, sq_abs (f x)]
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (add_nonneg (abs_nonneg _) (hε n).le)] at h2
    linarith
  have hsupp : ∀ n : ℕ, Function.support
      (fun y => √(f y ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)) =
      Function.support f := by
    intro n
    ext x
    simp only [Function.mem_support, ne_eq, sub_eq_zero]
    constructor
    · intro hx hfx
      apply hx
      rw [hfx, zero_pow two_ne_zero, zero_add, Real.sqrt_sq (hε n).le]
    · intro hfx hx
      apply hfx
      have h2 : √(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ^ 2 = (1 / ((n : ℝ) + 1)) ^ 2 := by
        rw [hx]
      rw [Real.sq_sqrt (hpos n x).le] at h2
      exact pow_eq_zero_iff two_ne_zero |>.1 (by linarith)
  have htsupp : ∀ n : ℕ, tsupport
      (fun y => √(f y ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)) = tsupport f :=
    fun n => by rw [tsupport, hsupp n, ← tsupport]
  have htest : ∀ n : ℕ, IsTestFn K
      (fun y => √(f y ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)) := fun n =>
    ⟨hsmooth n, by rw [HasCompactSupport, htsupp n]; exact hf.hasCompactSupport,
      by rw [htsupp n]; exact hf.supp_subset,
      fun h0 => hf.ne_zero (Function.support_eq_empty_iff.1
        ((hsupp n).symm.trans (Function.support_eq_empty_iff.2 h0)))⟩
  have hEle : ∀ n : ℕ, ∫ x, F (gradient
      (fun y => √(f y ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)) x) ^ p ≤
      ∫ x, F (gradient f x) ^ p := by
    intro n
    refine integral_mono (integrable_integrand_rpow (htest n) hF.continuous hF.map_zero hp0)
      (integrable_integrand_rpow hf hF.continuous hF.map_zero hp0) fun x => ?_
    show F (gradient (fun y => √(f y ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)) x) ^ p
      ≤ F (gradient f x) ^ p
    rw [hgrad n x, hF.homog]
    have hq : |f x / √(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (hpos n x)), div_le_one (Real.sqrt_pos.2 (hpos n x))]
      exact Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    exact Real.rpow_le_rpow (mul_nonneg (abs_nonneg _) (hF.nonneg _))
      (mul_le_of_le_one_left (hF.nonneg _) hq) hp0.le
  have hAlim : Tendsto (fun n : ℕ => ∫ x,
      |√(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)| ^ p) atTop
      (𝓝 (∫ x, |f x| ^ p)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |f x| ^ p) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · exact ((hsmooth n).continuous.abs.rpow_const fun _ => Or.inr hp0.le).aestronglyMeasurable
    · exact Continuous.integrable_of_hasCompactSupport
        (hf.contDiff.continuous.abs.rpow_const fun _ => Or.inr hp0.le)
        (hf.hasCompactSupport.comp_left (g := fun t : ℝ => |t| ^ p)
          (by simp [Real.zero_rpow hp0.ne']))
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_of_nonneg (hh0 n x)]
      exact Real.rpow_le_rpow (hh0 n x) (hhle n x) hp0.le
    · refine Eventually.of_forall fun x => ?_
      have hεlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := (((hεlim.pow 2).const_add (f x ^ 2)).sqrt).sub hεlim
      rw [zero_pow two_ne_zero, add_zero, sub_zero, Real.sqrt_sq_eq_abs] at h1
      simpa [abs_abs] using h1.abs.rpow_const (Or.inr hp0.le)
  -- choose `n` with `E(f) / ∫ |hₙ|^p < λ + δ`
  have hev : ∀ᶠ n : ℕ in atTop, (∫ x, F (gradient f x) ^ p) / ∫ x,
      |√(f x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)| ^ p < lambdaGen p F K + δ := by
    have hlim := (tendsto_const_nhds (x := ∫ x, F (gradient f x) ^ p)).div hAlim hApos.ne'
    have hEA : (∫ x, F (gradient f x) ^ p) / (∫ x, |f x| ^ p) < lambdaGen p F K + δ := by
      have : rayleighGen p F f = (∫ x, F (gradient f x) ^ p) / (∫ x, |f x| ^ p) := rfl
      linarith
    exact hlim.eventually (gt_mem_nhds hEA)
  obtain ⟨n, hn⟩ := hev.exists
  set h : Euc d → ℝ := fun y => √(f y ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) - 1 / ((n : ℝ) + 1)
    with hh_def
  have hBpos : 0 < ∫ x, |h x| ^ p :=
    integral_abs_rpow_pos hp0 ((htest n).memW0 p).memLp (htest n).not_ae_eq_zero
  set c : ℝ := ((∫ x, |h x| ^ p) ^ p⁻¹)⁻¹ with hc_def
  have hc0 : 0 < c := inv_pos.2 (Real.rpow_pos_of_pos hBpos _)
  have hcp : c ^ p = (∫ x, |h x| ^ p)⁻¹ := by
    rw [hc_def, Real.inv_rpow (Real.rpow_nonneg hBpos.le _), Real.rpow_inv_rpow hBpos.le hp0.ne']
  have hsuppc : Function.support (c • h) = Function.support f := by
    rw [← hsupp n]
    ext x
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc0.ne',
      false_or, hh_def]
  have htsuppc : tsupport (c • h) = tsupport f := by rw [tsupport, hsuppc, ← tsupport]
  have htestc : IsTestFn K (c • h) := by
    refine ⟨(hsmooth n).const_smul c, ?_, ?_, ?_⟩
    · show IsCompact (tsupport (c • h))
      rw [htsuppc]
      exact hf.hasCompactSupport
    · rw [htsuppc]
      exact hf.supp_subset
    · intro h0
      exact hf.ne_zero (Function.support_eq_empty_iff.1
        (hsuppc.symm.trans (Function.support_eq_empty_iff.2 h0)))
  refine ⟨c • h, htestc, fun x => mul_nonneg hc0.le (hh0 n x), ?_, ?_⟩
  · calc ∫ x, |(c • h) x| ^ p = ∫ x, c ^ p * |h x| ^ p := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          show |c * h x| ^ p = c ^ p * |h x| ^ p
          rw [abs_mul, abs_of_pos hc0, Real.mul_rpow hc0.le (abs_nonneg _)]
      _ = c ^ p * ∫ x, |h x| ^ p := integral_const_mul _ _
      _ = 1 := by rw [hcp, inv_mul_cancel₀ hBpos.ne']
  · have hhd : ∀ x, DifferentiableAt ℝ h x := fun x =>
      ((hsmooth n).differentiable (by simp)) x
    calc ∫ x, F (gradient (c • h) x) ^ p = ∫ x, c ^ p * F (gradient h x) ^ p := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          show F (gradient (c • h) x) ^ p = c ^ p * F (gradient h x) ^ p
          rw [gradient_const_smul_apply (hhd x) c, hF.rpow_smul hc0.le]
      _ = c ^ p * ∫ x, F (gradient h x) ^ p := integral_const_mul _ _
      _ ≤ c ^ p * ∫ x, F (gradient f x) ^ p :=
          mul_le_mul_of_nonneg_left (hEle n) (Real.rpow_nonneg hc0.le _)
      _ = (∫ x, F (gradient f x) ^ p) / ∫ x, |h x| ^ p := by rw [hcp, div_eq_inv_mul]
      _ < lambdaGen p F K + δ := hn

end NearMinimizer

/-! ### The uniform convexity estimate -/

section Cauchy

/-- A function `Ψ(a x, b x)` of two continuous compactly supported maps with `Ψ(0,0) = 0` is
integrable. -/
theorem integrable_comp₂_of_continuous {α E : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [R1Space α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    [TopologicalSpace E] [Zero E] {a b : α → E} (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) {Ψ : E → E → ℝ}
    (hΨ : Continuous fun z : E × E => Ψ z.1 z.2) (hΨ0 : Ψ 0 0 = 0) :
    Integrable (fun x => Ψ (a x) (b x)) μ := by
  have hs : HasCompactSupport fun x => Ψ (a x) (b x) := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((show IsCompact (tsupport a) from hac).union (show IsCompact (tsupport b) from hbc))
      fun x hx => ?_
    rw [Function.mem_support] at hx
    by_contra hmem
    simp only [mem_union, not_or] at hmem
    apply hx
    rw [image_eq_zero_of_notMem_tsupport hmem.1, image_eq_zero_of_notMem_tsupport hmem.2, hΨ0]
  exact (hΨ.comp (ha.prodMk hb)).integrable_of_hasCompactSupport hs

/-- **Integrated uniform convexity** on a general domain: for continuous compactly supported
`a, b : α → ℝ^d` and a pointwise bound `‖ξ - η‖^p ≤ C · midDefect + ε (‖ξ‖+‖η‖)^p`,
`∫ ‖a − b‖^p ≤ C (∫ F(a)^p/2 + ∫ F(b)^p/2 − ∫ F((a+b)/2)^p) + ε 2^p (∫ ‖a‖^p + ∫ ‖b‖^p)`. -/
theorem integral_norm_sub_rpow_le_of_continuous {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [R1Space α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {ε C : ℝ} (hε : 0 < ε)
    (hC : ∀ ξ η : Euc d, ‖ξ - η‖ ^ p ≤ C * midDefect p F ξ η + ε * (‖ξ‖ + ‖η‖) ^ p)
    {a b : α → Euc d} (ha : Continuous a) (hb : Continuous b) (hac : HasCompactSupport a)
    (hbc : HasCompactSupport b) :
    ∫ x, ‖a x - b x‖ ^ p ∂μ ≤
      C * ((∫ x, F (a x) ^ p ∂μ) / 2 + (∫ x, F (b x) ^ p ∂μ) / 2 -
        ∫ x, F ((1 / 2 : ℝ) • (a x + b x)) ^ p ∂μ) +
      ε * (2 ^ p * ((∫ x, ‖a x‖ ^ p ∂μ) + ∫ x, ‖b x‖ ^ p ∂μ)) := by
  have hp0 : 0 < p := by linarith
  have hΦ := hF.continuous_rpow hp0.le
  have hIfp : Integrable (fun x => F (a x) ^ p) μ :=
    integrable_comp₂_of_continuous (Ψ := fun ξ _ => F ξ ^ p) ha hb hac hbc
      (hΦ.comp continuous_fst) (by simp [hF.map_zero, Real.zero_rpow hp0.ne'])
  have hIgp : Integrable (fun x => F (b x) ^ p) μ :=
    integrable_comp₂_of_continuous (Ψ := fun _ η => F η ^ p) ha hb hac hbc
      (hΦ.comp continuous_snd) (by simp [hF.map_zero, Real.zero_rpow hp0.ne'])
  have hImp : Integrable (fun x => F ((1 / 2 : ℝ) • (a x + b x)) ^ p) μ :=
    integrable_comp₂_of_continuous (Ψ := fun ξ η => F ((1 / 2 : ℝ) • (ξ + η)) ^ p) ha hb hac hbc
      (hΦ.comp ((continuous_fst.add continuous_snd).const_smul (1 / 2 : ℝ)))
      (by simp [hF.map_zero, Real.zero_rpow hp0.ne'])
  have hInf : Integrable (fun x => ‖a x‖ ^ p) μ :=
    integrable_comp₂_of_continuous (Ψ := fun ξ _ => ‖ξ‖ ^ p) ha hb hac hbc
      ((continuous_norm.comp continuous_fst).rpow_const fun _ => Or.inr hp0.le)
      (by simp [Real.zero_rpow hp0.ne'])
  have hIng : Integrable (fun x => ‖b x‖ ^ p) μ :=
    integrable_comp₂_of_continuous (Ψ := fun _ η => ‖η‖ ^ p) ha hb hac hbc
      ((continuous_norm.comp continuous_snd).rpow_const fun _ => Or.inr hp0.le)
      (by simp [Real.zero_rpow hp0.ne'])
  have hIsum : Integrable (fun x => (‖a x‖ + ‖b x‖) ^ p) μ :=
    integrable_comp₂_of_continuous (Ψ := fun ξ η => (‖ξ‖ + ‖η‖) ^ p) ha hb hac hbc
      (((continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd)).rpow_const
        fun _ => Or.inr hp0.le) (by simp [Real.zero_rpow hp0.ne'])
  have hIdiff : Integrable (fun x => ‖a x - b x‖ ^ p) μ :=
    integrable_comp₂_of_continuous (Ψ := fun ξ η => ‖ξ - η‖ ^ p) ha hb hac hbc
      ((continuous_norm.comp (continuous_fst.sub continuous_snd)).rpow_const
        fun _ => Or.inr hp0.le) (by simp [Real.zero_rpow hp0.ne'])
  have hI12 : Integrable (fun x => F (a x) ^ p / 2 + F (b x) ^ p / 2) μ :=
    (hIfp.div_const 2).add (hIgp.div_const 2)
  have hIdef : Integrable (fun x => midDefect p F (a x) (b x)) μ := hI12.sub hImp
  have step1 : ∫ x, ‖a x - b x‖ ^ p ∂μ ≤
      ∫ x, (C * midDefect p F (a x) (b x) + ε * (‖a x‖ + ‖b x‖) ^ p) ∂μ :=
    integral_mono hIdiff ((hIdef.const_mul C).add (hIsum.const_mul ε)) fun x => hC _ _
  have step2 : ∫ x, (C * midDefect p F (a x) (b x) + ε * (‖a x‖ + ‖b x‖) ^ p) ∂μ =
      C * (∫ x, midDefect p F (a x) (b x) ∂μ) + ε * ∫ x, (‖a x‖ + ‖b x‖) ^ p ∂μ := by
    rw [integral_add (hIdef.const_mul C) (hIsum.const_mul ε), integral_const_mul,
      integral_const_mul]
  have step3 : ∫ x, midDefect p F (a x) (b x) ∂μ =
      (∫ x, F (a x) ^ p ∂μ) / 2 + (∫ x, F (b x) ^ p ∂μ) / 2 -
        ∫ x, F ((1 / 2 : ℝ) • (a x + b x)) ^ p ∂μ := by
    simp only [midDefect]
    rw [integral_sub hI12 hImp, integral_add (hIfp.div_const 2) (hIgp.div_const 2), integral_div,
      integral_div]
  have step4 : ∫ x, (‖a x‖ + ‖b x‖) ^ p ∂μ ≤
      2 ^ p * ((∫ x, ‖a x‖ ^ p ∂μ) + ∫ x, ‖b x‖ ^ p ∂μ) := by
    rw [← integral_add hInf hIng, ← integral_const_mul]
    exact integral_mono hIsum ((hInf.add hIng).const_mul _) fun x =>
      add_rpow_le_two_rpow_mul hp0.le (norm_nonneg _) (norm_nonneg _)
  rw [step3] at step2
  have h6 := mul_le_mul_of_nonneg_left step4 hε.le
  linarith [step1, step2, h6]


/-- **The key estimate of the direct method.** If `‖ξ - η‖^p ≤ C · midDefect + ε (‖ξ‖+‖η‖)^p`
pointwise (`IsSmoothStrictNorm.exists_norm_sub_rpow_le`), then for test functions `f, g` on `K`,
comparing with the competitor `(f + g)/2`:
`∫ ‖∇f − ∇g‖^p ≤ C (E(f)/2 + E(g)/2 − λ ∫ |(f+g)/2|^p) + ε 2^p (∫ ‖∇f‖^p + ∫ ‖∇g‖^p)`. -/
theorem integral_norm_sub_rpow_le {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} {ε C : ℝ} (hε : 0 < ε) (hC0 : 0 ≤ C)
    (hC : ∀ ξ η : Euc d, ‖ξ - η‖ ^ p ≤ C * midDefect p F ξ η + ε * (‖ξ‖ + ‖η‖) ^ p)
    {f g : Euc d → ℝ} (hf : IsTestFn K f) (hg : IsTestFn K g) :
    ∫ x, ‖gradient f x - gradient g x‖ ^ p ≤
      C * ((∫ x, F (gradient f x) ^ p) / 2 + (∫ x, F (gradient g x) ^ p) / 2 -
        lambdaGen p F K * ∫ x, |(1 / 2 : ℝ) * (f x + g x)| ^ p) +
      ε * (2 ^ p * ((∫ x, ‖gradient f x‖ ^ p) + ∫ x, ‖gradient g x‖ ^ p)) := by
  have h := integral_norm_sub_rpow_le_of_continuous (μ := volume) hp hF hε hC
    (continuous_gradient hf.contDiff_one) (continuous_gradient hg.contDiff_one)
    (hasCompactSupport_gradient hf.hasCompactSupport)
    (hasCompactSupport_gradient hg.hasCompactSupport)
  -- the competitor `(f + g)/2`
  have hmid : lambdaGen p F K * ∫ x, |(1 / 2 : ℝ) * (f x + g x)| ^ p ≤
      ∫ x, F ((1 / 2 : ℝ) • (gradient f x + gradient g x)) ^ p := by
    have hp0 : 0 < p := by linarith
    have hfd : ∀ x, DifferentiableAt ℝ f x := fun x => hf.contDiff_one.differentiable one_ne_zero x
    have hgd : ∀ x, DifferentiableAt ℝ g x := fun x => hg.contDiff_one.differentiable one_ne_zero x
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) fun x => (1 / 2 : ℝ) * (f x + g x) :=
      contDiff_const.mul (hf.contDiff.add hg.contDiff)
    have hmsupp : Function.support (fun x => (1 / 2 : ℝ) * (f x + g x)) ⊆
        tsupport f ∪ tsupport g := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hmem
      simp only [mem_union, not_or] at hmem
      apply hx
      rw [image_eq_zero_of_notMem_tsupport hmem.1, image_eq_zero_of_notMem_tsupport hmem.2,
        add_zero, mul_zero]
    have hms : HasCompactSupport fun x => (1 / 2 : ℝ) * (f x + g x) :=
      HasCompactSupport.of_support_subset_isCompact
        ((show IsCompact (tsupport f) from hf.hasCompactSupport).union
          (show IsCompact (tsupport g) from hg.hasCompactSupport)) hmsupp
    have hmK : tsupport (fun x => (1 / 2 : ℝ) * (f x + g x)) ⊆ K :=
      (closure_minimal hmsupp ((isClosed_tsupport _).union (isClosed_tsupport _))).trans
        (union_subset hf.supp_subset hg.supp_subset)
    have h := lambdaGen_mul_le hp0 hF.nonneg hsmooth hms hmK
    have e : ∀ x, gradient (fun y => (1 / 2 : ℝ) * (f y + g y)) x =
        (1 / 2 : ℝ) • (gradient f x + gradient g x) := fun x =>
      gradient_half_add_apply (hfd x) (hgd x)
    simp only [e] at h
    exact h
  have h2 : C * ((∫ x, F (gradient f x) ^ p) / 2 + (∫ x, F (gradient g x) ^ p) / 2 -
        ∫ x, F ((1 / 2 : ℝ) • (gradient f x + gradient g x)) ^ p) ≤
      C * ((∫ x, F (gradient f x) ^ p) / 2 + (∫ x, F (gradient g x) ^ p) / 2 -
        lambdaGen p F K * ∫ x, |(1 / 2 : ℝ) * (f x + g x)| ^ p) :=
    mul_le_mul_of_nonneg_left (by linarith [hmid]) hC0
  linarith [h, h2]

/-- **The gradients of a minimizing sequence are Cauchy in `L^p`**: if test functions `w k` on `K`
have energies `E_k → λ_{p,F}(K)`, uniformly bounded `∫ ‖∇w_k‖^p`, and
`∫ |(w_k + w_l)/2|^p → 1`, then `∫ ‖∇w_k − ∇w_l‖^p → 0` as `k, l → ∞`. -/
theorem tendsto_integral_norm_gradient_sub {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} {w : ℕ → Euc d → ℝ}
    (hw : ∀ k, IsTestFn K (w k))
    (hE : Tendsto (fun k => ∫ x, F (gradient (w k) x) ^ p) atTop (𝓝 (lambdaGen p F K)))
    {B : ℝ} (hB : ∀ k, ∫ x, ‖gradient (w k) x‖ ^ p ≤ B)
    (hm : Tendsto (fun kl : ℕ × ℕ => ∫ x, |(1 / 2 : ℝ) * (w kl.1 x + w kl.2 x)| ^ p)
      (atTop ×ˢ atTop) (𝓝 1)) :
    Tendsto (fun kl : ℕ × ℕ => ∫ x, ‖gradient (w kl.1) x - gradient (w kl.2) x‖ ^ p)
      (atTop ×ˢ atTop) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hB0 : 0 ≤ B := (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p).trans (hB 0)
  have hD : Tendsto (fun kl : ℕ × ℕ => (∫ x, F (gradient (w kl.1) x) ^ p) / 2 +
      (∫ x, F (gradient (w kl.2) x) ^ p) / 2 -
      lambdaGen p F K * ∫ x, |(1 / 2 : ℝ) * (w kl.1 x + w kl.2 x)| ^ p)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h := (((hE.comp tendsto_fst).div_const 2).add ((hE.comp tendsto_snd).div_const 2)).sub
      (hm.const_mul (lambdaGen p F K))
    have e : lambdaGen p F K / 2 + lambdaGen p F K / 2 - lambdaGen p F K * 1 = 0 := by ring
    rw [e] at h
    exact h
  rw [Metric.tendsto_nhds]
  intro η hη
  have hX0 : 0 ≤ 2 ^ p * (2 * B) := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  have hK1 : 0 < 2 * (2 ^ p * (2 * B) + 1) := by linarith
  obtain ⟨ε, hε, hεX⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (2 ^ p * (2 * B)) < η / 2 :=
    ⟨η / (2 * (2 ^ p * (2 * B) + 1)), div_pos hη hK1, by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hK1]
      nlinarith⟩
  obtain ⟨C, hC0, hC⟩ := hF.exists_norm_sub_rpow_le hp hε
  have hev : ∀ᶠ kl in atTop ×ˢ atTop, C * ((∫ x, F (gradient (w kl.1) x) ^ p) / 2 +
      (∫ x, F (gradient (w kl.2) x) ^ p) / 2 -
      lambdaGen p F K * ∫ x, |(1 / 2 : ℝ) * (w kl.1 x + w kl.2 x)| ^ p) < η / 2 := by
    have h := hD.const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (half_pos hη))
  filter_upwards [hev] with kl hkl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  have h1 := integral_norm_sub_rpow_le hp hF hε hC0 hC (hw kl.1) (hw kl.2)
  have h2 : ε * (2 ^ p * ((∫ x, ‖gradient (w kl.1) x‖ ^ p) + ∫ x, ‖gradient (w kl.2) x‖ ^ p)) ≤
      ε * (2 ^ p * (2 * B)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hB kl.1, hB kl.2])
      (Real.rpow_nonneg (by norm_num) _)) hε.le
  linarith

/-- If `w k → u` in `L^p` with `‖u‖_p = 1`, then `∫ |(w_k + w_l)/2|^p → 1` as `k, l → ∞`. -/
theorem tendsto_integral_abs_midpoint_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ} (hp : 1 < p) {w : ℕ → α → ℝ} (hw : ∀ k, MemLp (w k) (ENNReal.ofReal p) μ) {u : α → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) μ) (hu1 : eLpNorm u (ENNReal.ofReal p) μ = 1)
    (hlim : Tendsto (fun k => eLpNorm (w k - u) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun kl : ℕ × ℕ => ∫ x, |(1 / 2 : ℝ) * (w kl.1 x + w kl.2 x)| ^ p ∂μ)
      (atTop ×ˢ atTop) (𝓝 1) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hmm : ∀ kl : ℕ × ℕ, MemLp ((1 / 2 : ℝ) • (w kl.1 + w kl.2)) (ENNReal.ofReal p) μ :=
    fun kl => ((hw kl.1).add (hw kl.2)).const_smul _
  have hsub : ∀ kl : ℕ × ℕ, eLpNorm ((1 / 2 : ℝ) • (w kl.1 + w kl.2) - u) (ENNReal.ofReal p) μ ≤
      ‖(1 / 2 : ℝ)‖ₑ * (eLpNorm (w kl.1 - u) (ENNReal.ofReal p) μ +
        eLpNorm (w kl.2 - u) (ENNReal.ofReal p) μ) := by
    intro kl
    have e : (1 / 2 : ℝ) • (w kl.1 + w kl.2) - u =
        (1 / 2 : ℝ) • ((w kl.1 - u) + (w kl.2 - u)) := by
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [e]
    exact eLpNorm_const_smul_le.trans
      (mul_le_mul' le_rfl (eLpNorm_add_le ((hw _).1.sub hu.1) ((hw _).1.sub hu.1) hp1))
  have hup : Tendsto (fun kl : ℕ × ℕ => ‖(1 / 2 : ℝ)‖ₑ *
      (eLpNorm (w kl.1 - u) (ENNReal.ofReal p) μ + eLpNorm (w kl.2 - u) (ENNReal.ofReal p) μ))
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul ((hlim.comp tendsto_fst).add (hlim.comp tendsto_snd))
      (Or.inr (enorm_ne_top (x := (1 / 2 : ℝ))))
    simpa only [add_zero, mul_zero, Function.comp_def] using h
  have hmsub : Tendsto (fun kl : ℕ × ℕ =>
      eLpNorm ((1 / 2 : ℝ) • (w kl.1 + w kl.2) - u) (ENNReal.ofReal p) μ) (atTop ×ˢ atTop)
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le) hsub
  have hnorm := tendsto_eLpNorm_of_tendsto_eLpNorm_sub_filter hp1 (fun kl => (hmm kl).1) hu hmsub
  rw [hu1] at hnorm
  have hint : ∀ kl : ℕ × ℕ, ∫ x, |(1 / 2 : ℝ) * (w kl.1 x + w kl.2 x)| ^ p ∂μ =
      (eLpNorm ((1 / 2 : ℝ) • (w kl.1 + w kl.2)) (ENNReal.ofReal p) μ).toReal ^ p := fun kl => by
    rw [← integral_norm_rpow_eq hp0 (hmm kl)]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Real.norm_eq_abs]
  have h := ((ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hnorm).rpow_const (Or.inr hp0.le)
  simp only [Function.comp_def, ENNReal.toReal_one, Real.one_rpow] at h
  exact h.congr fun kl => (hint kl).symm

end Cauchy

/-! ### Existence of a minimizer -/

/-- **Existence of a first eigenfunction by the direct method** (paper Appendix A, *Eigenfunction
inputs*: "The direct method gives a nonnegative, nonzero first eigenfunction
`u_i ∈ W_0^{1,p}(K_i)`"): for `1 < p`, a smooth strictly convex norm `F` and a nonempty bounded
open convex `K`, there is `u ∈ W₀^{1,p}(K)` with `u ≥ 0`, `u = 0` outside `K`, `∫ |u|^p = 1` and
`∫ F(∇u)^p = lambdaSob p F K`, i.e. `u` attains the Rayleigh infimum over `W₀^{1,p}(K)` (which
equals `lambdaGen p F K`, `lambdaSob_eq_lambdaGen`). -/
theorem exists_minimizer {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} (hK : IsGoodConvex K) :
    ∃ u : Euc d → ℝ, MemW0 p K u ∧ (∀ x, 0 ≤ u x) ∧ (∀ x, x ∉ K → u x = 0) ∧
      ∫ x, |u x| ^ p = 1 ∧ ∫ x, F (weakGrad u x) ^ p = lambdaSob p F K := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  obtain ⟨c, hc, hcF⟩ := hF.exists_pos_mul_norm_le'
  have hlam : lambdaSob p F K = lambdaGen p F K :=
    lambdaSob_eq_lambdaGen hp hF.continuous hF.nonneg hM hK
  -- a minimizing sequence of nonnegative normalized smooth test functions
  have hseq := fun n : ℕ =>
    exists_nonneg_near_minimizer hp hF hK (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  choose v hvt hv0 hv1 hvE using hseq
  have hvW : ∀ n, MemW0 p K (v n) := fun n => (hvt n).memW0 p
  have hGmem : ∀ n, MemLp (gradient (v n)) (ENNReal.ofReal p) := fun n =>
    (continuous_gradient (hvt n).contDiff_one).memLp_of_hasCompactSupport
      (hasCompactSupport_gradient (hvt n).hasCompactSupport)
  have hElow : ∀ n, lambdaGen p F K ≤ ∫ x, F (gradient (v n) x) ^ p := fun n => by
    have h := lambdaGen_mul_le hp0 hF.nonneg (hvt n).contDiff (hvt n).hasCompactSupport
      (hvt n).supp_subset
    rwa [hv1 n, mul_one] at h
  have hElim : Tendsto (fun n => ∫ x, F (gradient (v n) x) ^ p) atTop
      (𝓝 (lambdaGen p F K)) := by
    have h := (tendsto_const_nhds (x := lambdaGen p F K)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [add_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h hElow
      fun n => (hvE n).le
  -- uniform bounds
  have hGint : ∀ n, ∫ x, ‖gradient (v n) x‖ ^ p ≤ (lambdaGen p F K + 1) / c ^ p := fun n => by
    have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc p
    rw [le_div_iff₀ hcp, mul_comm, ← integral_const_mul]
    calc ∫ x, c ^ p * ‖gradient (v n) x‖ ^ p ≤ ∫ x, F (gradient (v n) x) ^ p := by
          refine integral_mono
            ((integrable_integrand_rpow (hvt n) continuous_norm norm_zero hp0).const_mul _)
            (integrable_integrand_rpow (hvt n) hF.continuous hF.map_zero hp0) fun x => ?_
          show c ^ p * ‖gradient (v n) x‖ ^ p ≤ F (gradient (v n) x) ^ p
          rw [← Real.mul_rpow hc.le (norm_nonneg _)]
          exact Real.rpow_le_rpow (mul_nonneg hc.le (norm_nonneg _)) (hcF _) hp0.le
      _ ≤ lambdaGen p F K + 1 := by
          have h1 := hvE n
          have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          linarith
  have hv1' : ∀ n, eLpNorm (v n) (ENNReal.ofReal p) = 1 := fun n => by
    rw [eLpNorm_eq_ofReal_integral hp0 (hvW n).memLp]
    simp only [Real.norm_eq_abs, hv1 n, Real.one_rpow, ENNReal.ofReal_one]
  have hBg0 : 0 ≤ (lambdaGen p F K + 1) / c ^ p :=
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p).trans (hGint 0)
  have hbound : ∀ n, eLpNorm (v n) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (max 1 (((lambdaGen p F K + 1) / c ^ p) ^ p⁻¹)) ∧
      gradLpNorm p (v n) ≤ ENNReal.ofReal (max 1 (((lambdaGen p F K + 1) / c ^ p) ^ p⁻¹)) := by
    intro n
    refine ⟨?_, ?_⟩
    · rw [hv1' n, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    · rw [gradLpNorm, eLpNorm_congr_ae
        (weakGrad_ae_eq_gradient (hvt n).contDiff_one (hvt n).hasCompactSupport),
        eLpNorm_eq_ofReal_integral hp0 (hGmem n)]
      exact ENNReal.ofReal_le_ofReal ((Real.rpow_le_rpow
        (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) (hGint n)
        (inv_nonneg.2 hp0.le)).trans (le_max_right _ _))
  -- Rellich: an `L^p`-convergent subsequence
  obtain ⟨u₀, hu₀, φ, hφ, hlim⟩ := rellich hp hK.isBounded v hvW ENNReal.ofReal_ne_top hbound
  have hu1 : eLpNorm u₀ (ENNReal.ofReal p) = 1 := by
    have h := tendsto_eLpNorm_of_tendsto_eLpNorm_sub hp1
      (fun k => (hvW (φ k)).memLp.aestronglyMeasurable) hu₀ hlim
    simp only [hv1'] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- the gradients are Cauchy in `L^p`
  have hInt := tendsto_integral_norm_gradient_sub hp hF (w := fun k => v (φ k))
    (fun k => hvt (φ k)) (hElim.comp hφ.tendsto_atTop) (fun k => hGint (φ k))
    (tendsto_integral_abs_midpoint_rpow hp (w := fun k => v (φ k)) (fun k => (hvW (φ k)).memLp)
      hu₀ hu1 hlim)
  have hcauchy : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      eLpNorm (gradient (v (φ m)) - gradient (v (φ n))) (ENNReal.ofReal p) < ε := by
    intro ε hε
    have hT : Tendsto (fun kl : ℕ × ℕ =>
        eLpNorm (gradient (v (φ kl.1)) - gradient (v (φ kl.2))) (ENNReal.ofReal p))
        (atTop ×ˢ atTop) (𝓝 0) := by
      have h0 := ((Real.continuous_rpow_const (inv_nonneg.2 hp0.le)).tendsto 0).comp hInt
      have h1 := (ENNReal.continuous_ofReal.tendsto _).comp h0
      simp only [Function.comp_def, Real.zero_rpow (inv_ne_zero hp0.ne'),
        ENNReal.ofReal_zero] at h1
      refine h1.congr fun kl => ?_
      rw [eLpNorm_eq_ofReal_integral hp0 ((hGmem _).sub (hGmem _))]
      simp only [Pi.sub_apply]
    have hev := hT.eventually (gt_mem_nhds hε)
    rw [prod_atTop_atTop_eq] at hev
    obtain ⟨N, hN⟩ := Filter.eventually_atTop_prod_self.1 hev
    exact ⟨N, fun m n hm hn => hN m n hm hn⟩
  obtain ⟨g, hg, hGg⟩ := exists_memLp_tendsto_of_cauchy hp1 (fun k => hGmem (φ k)) hcauchy
  have hwg : HasWeakGradient u₀ g :=
    HasWeakGradient.of_tendsto hp (u := fun k => v (φ k)) (G := fun k => gradient (v (φ k)))
      (fun k => hasWeakGradient_gradient (hvt (φ k)).contDiff_one (hvt (φ k)).hasCompactSupport)
      hu₀ hg hlim hGg
  -- a.e. properties of the limit
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp'
    (fun k => (hvW (φ k)).memLp.aestronglyMeasurable) hu₀.aestronglyMeasurable
    hlim).exists_seq_tendsto_ae
  have hvanish : ∀ᵐ x, x ∉ K → u₀ x = 0 := by
    filter_upwards [hae, ae_all_iff.2 fun n => (hvW n).ae_eq_zero] with x hx hzero hxK
    exact tendsto_nhds_unique (hx.congr fun i => hzero (φ (ns i)) hxK) tendsto_const_nhds
  have hnonneg : ∀ᵐ x, 0 ≤ u₀ x := by
    filter_upwards [hae] with x hx
    exact ge_of_tendsto' hx fun i => hv0 _ x
  have hu₀W : MemW0 p K u₀ := ⟨hu₀, hvanish, g, hwg, hg⟩
  -- the energy and the normalization pass to the limit
  have hEg : Tendsto (fun k => ∫ x, F (gradient (v (φ k)) x) ^ p) atTop
      (𝓝 (∫ x, F (g x) ^ p)) :=
    tendsto_integral_comp_of_tendsto_eLpNorm hp.le (hF.continuous_rpow hp0.le)
      (norm_rpow_le_of_le_mul_norm hF.nonneg hM hp0) (fun k => hGmem (φ k)) hg hGg
  have hEu : ∫ x, F (g x) ^ p = lambdaGen p F K :=
    tendsto_nhds_unique hEg (hElim.comp hφ.tendsto_atTop)
  have hIu : ∫ x, |u₀ x| ^ p = 1 := by
    have h := integral_norm_rpow_eq hp0 hu₀
    simp only [Real.norm_eq_abs, hu1, ENNReal.toReal_one, Real.one_rpow] at h
    exact h
  -- a nonnegative representative vanishing outside `K`
  set u : Euc d → ℝ := K.indicator fun x => max (u₀ x) 0 with hu_def
  have hae_u : u₀ =ᵐ[volume] u := by
    filter_upwards [hvanish, hnonneg] with x hx hx0
    by_cases hxK : x ∈ K
    · rw [hu_def, Set.indicator_of_mem hxK, max_eq_left hx0]
    · rw [hu_def, Set.indicator_of_notMem hxK, hx hxK]
  have hwgu : weakGrad u =ᵐ[volume] g := (hwg.congr_left hae_u).weakGrad_ae_eq
  refine ⟨u, hu₀W.congr hae_u, fun x => Set.indicator_nonneg (fun y _ => le_max_right _ _) x,
    fun x hx => Set.indicator_of_notMem hx _, ?_, ?_⟩
  · rw [← hIu]
    exact integral_congr_ae (hae_u.mono fun x hx => by simp only [hx])
  · rw [hlam, ← hEu]
    exact integral_congr_ae (hwgu.mono fun x hx => by simp only [hx])

/-! ### Differentiation under the integral sign -/

/-- `d/dt|_{t=0} ∫ |u + tψ|^p = ∫ p |u|^{p-2} u ψ` for `u, ψ ∈ L^p`, `p > 1` (dominated by
`p((|u| + |ψ|)^p + |ψ|^p)` for `|t| < 1`). -/
theorem hasDerivAt_integral_abs_rpow_add_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ} (hp : 1 < p) {u ψ : α → ℝ} (hu : MemLp u (ENNReal.ofReal p) μ)
    (hψ : MemLp ψ (ENNReal.ofReal p) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, |u x + t * ψ x| ^ p ∂μ)
      (∫ x, p * |u x| ^ (p - 2) * u x * ψ x ∂μ) 0 := by
  have hp0 : 0 < p := by linarith
  have hum := hu.aestronglyMeasurable
  have hψm := hψ.aestronglyMeasurable
  have hupair : AEStronglyMeasurable (fun x => (u x, ψ x)) μ := hum.prodMk hψm
  have hS_meas : ∀ t : ℝ, AEStronglyMeasurable (fun x => |u x + t * ψ x| ^ p) μ := by
    intro t
    have hc : Continuous fun z : ℝ × ℝ => |z.1 + t * z.2| ^ p :=
      (continuous_abs.comp (continuous_fst.add (continuous_const.mul continuous_snd))).rpow_const
        fun _ => Or.inr hp0.le
    exact hc.comp_aestronglyMeasurable hupair
  have hS_int : Integrable (fun x => |u x + (0 : ℝ) * ψ x| ^ p) μ := by
    simp only [zero_mul, add_zero]
    simpa only [Real.norm_eq_abs] using integrable_norm_rpow_of_memLp hp0 hu
  have hgm : Measurable fun z : ℝ × ℝ => p * |z.1 + (0 : ℝ) * z.2| ^ (p - 2) *
      (z.1 + (0 : ℝ) * z.2) * z.2 := by
    fun_prop
  have hS'_meas : AEStronglyMeasurable (fun x => p * |u x + (0 : ℝ) * ψ x| ^ (p - 2) *
      (u x + (0 : ℝ) * ψ x) * ψ x) μ :=
    (hgm.comp_aemeasurable hupair.aemeasurable).aestronglyMeasurable
  have hS_bound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖p * |u x + t * ψ x| ^ (p - 2) * (u x + t * ψ x) * ψ x‖ ≤
        p * ((|u x| + |ψ x|) ^ p + |ψ x| ^ p) := by
    refine Eventually.of_forall fun x t ht => ?_
    have ht1 : |t| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht.le
    have hs : |u x + t * ψ x| ≤ |u x| + |ψ x| := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
    have e : ‖p * |u x + t * ψ x| ^ (p - 2) * (u x + t * ψ x) * ψ x‖ =
        p * (|u x + t * ψ x| ^ (p - 2) * |u x + t * ψ x| * |ψ x|) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hp0,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      ring
    rw [e, abs_rpow_sub_two_mul_abs hp]
    refine mul_le_mul_of_nonneg_left ?_ hp0.le
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hs (sub_pos.2 hp).le)
      (abs_nonneg _)).trans
      (rpow_sub_one_mul_le_add hp.le (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
  have hSbound_int : Integrable (fun x => p * ((|u x| + |ψ x|) ^ p + |ψ x| ^ p)) μ := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) p
    · refine (integrable_norm_rpow_of_memLp hp0 (hu.norm.add hψ.norm)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (abs_nonneg (u x)) (abs_nonneg (ψ x)))]
    · simpa only [Real.norm_eq_abs] using integrable_norm_rpow_of_memLp hp0 hψ
  have hS_diff : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => |u x + t * ψ x| ^ p)
        (p * |u x + t * ψ x| ^ (p - 2) * (u x + t * ψ x) * ψ x) t := by
    refine Eventually.of_forall fun x t _ => ?_
    have hl : HasDerivAt (fun t : ℝ => u x + t * ψ x) (ψ x) t := by
      simpa using ((hasDerivAt_id t).mul_const (ψ x)).const_add (u x)
    exact (hasDerivAt_abs_rpow (u x + t * ψ x) hp).comp t hl
  have hSd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (Eventually.of_forall hS_meas) hS_int hS'_meas
    hS_bound hSbound_int hS_diff).2
  simpa only [zero_mul, add_zero] using hSd

/-- `d/dt|_{t=0} ∫ F(A + tB)^p = ∫ p ⟪a(A), B⟫` for `A, B ∈ L^p` and `a = flux p F`
(dominated using `‖a(ξ)‖ ≤ C ‖ξ‖^{p-1}`). -/
theorem hasDerivAt_integral_rpow_add_smul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {A B : α → Euc d}
    (hAp : MemLp A (ENNReal.ofReal p) μ) (hBp : MemLp B (ENNReal.ofReal p) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, F (A x + t • B x) ^ p ∂μ)
      (∫ x, p * ⟪flux p F (A x), B x⟫ ∂μ) 0 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  obtain ⟨Ca, hCa0, hCa⟩ := hF.exists_norm_flux_le hp
  have hAm := hAp.aestronglyMeasurable
  have hBm := hBp.aestronglyMeasurable
  have hΦc := hF.continuous_rpow hp0.le
  have hsum_int : Integrable (fun x => (‖A x‖ + ‖B x‖) ^ p) μ := by
    refine (integrable_norm_rpow_of_memLp hp0 (hAp.norm.add hBp.norm)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg (A x)) (norm_nonneg (B x)))]
  have hpair : AEStronglyMeasurable (fun x => (A x, B x)) μ := hAm.prodMk hBm
  have hF_meas : ∀ t : ℝ, AEStronglyMeasurable (fun x => F (A x + t • B x) ^ p) μ := fun t =>
    (hΦc.comp (continuous_fst.add (continuous_snd.const_smul t))).comp_aestronglyMeasurable hpair
  have hF_int : Integrable (fun x => F (A x + (0 : ℝ) • B x) ^ p) μ := by
    refine ((integrable_norm_rpow_of_memLp hp0 hAp).const_mul (max M 0 ^ p)).mono' (hF_meas 0)
      (Eventually.of_forall fun x => ?_)
    have h1 := norm_rpow_le_of_le_mul_norm hF.nonneg hM hp0 (A x + (0 : ℝ) • B x)
    rw [zero_smul, add_zero] at h1 ⊢
    exact h1
  have hF'_meas : AEStronglyMeasurable (fun x => p * ⟪flux p F (A x + (0 : ℝ) • B x), B x⟫) μ :=
    aestronglyMeasurable_mul_inner_comp (hF.continuous_flux' hp) p 0 hAm hBm
  have h_bound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖p * ⟪flux p F (A x + t • B x), B x⟫‖ ≤ p * (Ca * ((‖A x‖ + ‖B x‖) ^ p + ‖B x‖ ^ p)) := by
    refine Eventually.of_forall fun x t ht => ?_
    have ht1 : |t| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht.le
    have hnorm : ‖A x + t • B x‖ ≤ ‖A x‖ + ‖B x‖ := by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) ht1
    rw [norm_mul, Real.norm_of_nonneg hp0.le]
    refine mul_le_mul_of_nonneg_left ?_ hp0.le
    have h1 : ‖⟪flux p F (A x + t • B x), B x⟫‖ ≤ Ca * (‖A x‖ + ‖B x‖) ^ (p - 1) * ‖B x‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ((hCa _).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm (sub_pos.2 hp).le)
          hCa0)) (norm_nonneg _))
    have h2 := rpow_sub_one_mul_le_add hp.le (add_nonneg (norm_nonneg (A x)) (norm_nonneg (B x)))
      (norm_nonneg (B x))
    calc ‖⟪flux p F (A x + t • B x), B x⟫‖ ≤ Ca * ((‖A x‖ + ‖B x‖) ^ (p - 1) * ‖B x‖) := by
          rw [← mul_assoc]; exact h1
      _ ≤ Ca * ((‖A x‖ + ‖B x‖) ^ p + ‖B x‖ ^ p) := mul_le_mul_of_nonneg_left h2 hCa0
  have hbound_int : Integrable (fun x => p * (Ca * ((‖A x‖ + ‖B x‖) ^ p + ‖B x‖ ^ p))) μ :=
    ((hsum_int.add (integrable_norm_rpow_of_memLp hp0 hBp)).const_mul Ca).const_mul p
  have h_diff : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (A x + t • B x) ^ p) (p * ⟪flux p F (A x + t • B x), B x⟫) t :=
    Eventually.of_forall fun x t _ => hF.hasDerivAt_rpow_line hp _ _ t
  have hΦd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (Eventually.of_forall hF_meas) hF_int hF'_meas
    h_bound hbound_int h_diff).2
  simpa only [zero_smul, add_zero] using hΦd

/-! ### The weak Euler–Lagrange equation -/

/-- **The weak Euler–Lagrange (eigenvalue) equation** (paper Appendix A, *Eigenfunction inputs*:
the weak eigenfunction equation `∫ a(∇u)·∇ψ = λ ∫ |u|^{p-2} u ψ`): if `u ∈ W₀^{1,p}(K)` attains the
Rayleigh infimum, `∫ F(∇u)^p = λ ∫ |u|^p` with `λ = lambdaSob p F K`, then for every
`ψ ∈ W₀^{1,p}(K)`, `∫ ⟪a(∇u), ∇ψ⟫ = λ ∫ |u|^{p-2} u ψ` with `a = flux p F`.

Proof: `t ↦ ∫ F(∇u + t∇ψ)^p − λ ∫ |u + tψ|^p` is `≥ 0` (definition of `λ`) and vanishes at
`t = 0`; its derivative at `0`, computed under the integral sign, is
`p (∫ ⟪a(∇u), ∇ψ⟫ − λ ∫ |u|^{p-2} u ψ)`. -/
theorem weak_euler_lagrange {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} {u : Euc d → ℝ} (hu : MemW0 p K u)
    (hmin : ∫ x, F (weakGrad u x) ^ p = lambdaSob p F K * ∫ x, |u x| ^ p)
    {ψ : Euc d → ℝ} (hψ : MemW0 p K ψ) :
    ∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ =
      lambdaSob p F K * ∫ x, |u x| ^ (p - 2) * u x * ψ x := by
  have hp0 : 0 < p := by linarith
  -- the competitors `u + tψ`
  have hineq : ∀ t : ℝ, lambdaSob p F K * ∫ x, |u x + t * ψ x| ^ p ≤
      ∫ x, F (weakGrad u x + t • weakGrad ψ x) ^ p := by
    intro t
    have hgw : HasWeakGradient (u + t • ψ) (weakGrad u + t • weakGrad ψ) :=
      hu.hasWeakGradient.add (hψ.hasWeakGradient.smul t)
    have h := lambdaSob_mul_le hp0 hF.nonneg (hu.add (hψ.smul t))
    have e1 : ∫ x, F (weakGrad (u + t • ψ) x) ^ p =
        ∫ x, F (weakGrad u x + t • weakGrad ψ x) ^ p :=
      integral_congr_ae (hgw.weakGrad_ae_eq.mono fun x hx => by
        simp only [hx, Pi.add_apply, Pi.smul_apply])
    rw [e1] at h
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have hlocmin : IsLocalMin (fun t : ℝ => (∫ x, F (weakGrad u x + t • weakGrad ψ x) ^ p) -
      lambdaSob p F K * ∫ x, |u x + t * ψ x| ^ p) 0 := by
    refine Eventually.of_forall fun t => ?_
    simp only [zero_smul, add_zero, zero_mul]
    have h := hineq t
    linarith [hmin]
  -- the two derivatives at `t = 0`
  have hΦd := hasDerivAt_integral_rpow_add_smul (μ := volume) hp hF hu.memLp_weakGrad
    hψ.memLp_weakGrad
  have hSd := hasDerivAt_integral_abs_rpow_add_mul (μ := volume) hp hu.memLp hψ.memLp
  -- the derivative vanishes at the minimum
  have h0 := hlocmin.hasDerivAt_eq_zero (hΦd.sub (hSd.const_mul (lambdaSob p F K)))
  have e1 : ∫ x, p * ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ =
      p * ∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ := integral_const_mul _ _
  have e2 : ∫ x, p * |u x| ^ (p - 2) * u x * ψ x = p * ∫ x, |u x| ^ (p - 2) * u x * ψ x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e1, e2] at h0
  have h3 : p * ((∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫) -
      lambdaSob p F K * ∫ x, |u x| ^ (p - 2) * u x * ψ x) = 0 := by
    rw [← h0]
    ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hp0.ne')

/-- **The weak eigenvalue equation against test functions** for a nonnegative minimizer:
`∫ ⟪a(∇u), ∇ψ⟫ = λ ∫ u^{p-1} ψ` for `ψ ∈ C_c^∞(K)` (paper Appendix A, *Eigenfunction inputs*;
the form of `EigenfunctionData.weakEL`). -/
theorem weak_euler_lagrange_testFn {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} {u : Euc d → ℝ} (hu : MemW0 p K u)
    (hu0 : ∀ x, 0 ≤ u x)
    (hmin : ∫ x, F (weakGrad u x) ^ p = lambdaSob p F K * ∫ x, |u x| ^ p)
    {ψ : Euc d → ℝ} (hψ : IsTestFn K ψ) :
    ∫ x, ⟪flux p F (weakGrad u x), gradient ψ x⟫ =
      lambdaSob p F K * ∫ x, u x ^ (p - 1) * ψ x := by
  have h := weak_euler_lagrange hp hF hu hmin (hψ.memW0 p)
  have e1 : ∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ =
      ∫ x, ⟪flux p F (weakGrad u x), gradient ψ x⟫ :=
    integral_congr_ae ((weakGrad_ae_eq_gradient hψ.contDiff_one hψ.hasCompactSupport).mono
      fun x hx => by simp only [hx])
  have e2 : ∫ x, |u x| ^ (p - 2) * u x * ψ x = ∫ x, u x ^ (p - 1) * ψ x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show |u x| ^ (p - 2) * u x * ψ x = u x ^ (p - 1) * ψ x
    have h1 := abs_rpow_sub_two_mul_abs hp (u x)
    rw [abs_of_nonneg (hu0 x)] at h1
    rw [abs_of_nonneg (hu0 x), h1]
  rw [← e1, h, e2]

/-- **Existence of a weak first eigenfunction** (paper Appendix A, *Eigenfunction inputs*, the
direct-method half of `exists_eigenfunctionData`): for `1 < p`, a smooth strictly convex norm `F`
and a nonempty bounded open convex `K`, there is a nonnegative `u ∈ W₀^{1,p}(K)` vanishing outside
`K` with `∫ |u|^p = 1`, `∫ F(∇u)^p = λ_{p,F}(K)`, and the weak eigenvalue equation
`∫ ⟪a(∇u), ∇ψ⟫ = λ_{p,F}(K) ∫ u^{p-1} ψ` for all `ψ ∈ C_c^∞(K)`, where
`λ_{p,F}(K) = lambdaGen p F K` is the eigenvalue of `EigenfunctionData`. -/
theorem exists_eigenfunction_weak {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) :
    ∃ u : Euc d → ℝ, MemW0 p K u ∧ (∀ x, 0 ≤ u x) ∧ (∀ x, x ∉ K → u x = 0) ∧
      ∫ x, |u x| ^ p = 1 ∧ ∫ x, F (weakGrad u x) ^ p = lambdaGen p F K ∧
      ∀ ψ : Euc d → ℝ, IsTestFn K ψ →
        ∫ x, ⟪flux p F (weakGrad u x), gradient ψ x⟫ =
          lambdaGen p F K * ∫ x, u x ^ (p - 1) * ψ x := by
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  have hlam : lambdaSob p F K = lambdaGen p F K :=
    lambdaSob_eq_lambdaGen hp hF.continuous hF.nonneg hM hK
  obtain ⟨u, hu, hu0, huK, hu1, hE⟩ := exists_minimizer hp hF hK
  have hmin : ∫ x, F (weakGrad u x) ^ p = lambdaSob p F K * ∫ x, |u x| ^ p := by
    rw [hE, hu1, mul_one]
  refine ⟨u, hu, hu0, huK, hu1, hE.trans hlam, fun ψ hψ => ?_⟩
  rw [← hlam]
  exact weak_euler_lagrange_testFn hp hF hu hu0 hmin hψ

end Komlos.Literature
