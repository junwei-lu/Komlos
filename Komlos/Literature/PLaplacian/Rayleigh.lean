import Komlos.Eigenvalue

/-!
# The general-integrand anisotropic `p`-eigenvalue and the `H_ε ↓ H` limit

This file is the general-integrand layer of paper Lemma 3.2. It introduces the anisotropic
`p`-eigenvalue `λ_{p,F}(K)` (paper (3.7)) for an arbitrary integrand `F : Euc d → ℝ`, realized
over smooth test functions exactly like `lambdaMix`, together with the mixture integrand
`Hmix α u ξ = ∑ α_ℓ |u_ℓ·ξ|` (paper (3.6)) and its smooth strongly convex regularization
`Heps ε α u ξ = ∑ α_ℓ √((u_ℓ·ξ)² + ε²‖ξ‖²)` (paper Lemma 3.2, last paragraph).

Main results:
* `mixtureGrad_eq_Hmix_gradient`, `lambdaMix_eq_lambdaGen`: `lambdaMix p α u K = lambdaGen p
  (Hmix α u) K`, i.e. the Phase-A eigenvalue is the general one at the mixture integrand;
* `Hmix_le_Heps`, `Heps_le_Hmix_add`: the sandwich `H ≤ H_ε ≤ H + ε ‖·‖` of the paper;
* `lambdaGen_mono_integrand`, `lambdaGen_nonneg`: monotonicity in the integrand, nonnegativity;
* `Heps_tendsto`: `λ_{p,H_ε}(K) → λ_{p,H}(K)` as `ε ↓ 0` at fixed `p > 1` (paper Lemma 3.2,
  the `H_ε` limit, at the level of the `p`-eigenvalue rather than the Cheeger value).

Once eigenvalue convexity is known for the smooth integrands `Heps ε` (paper Proposition A.1),
`Komlos.eigenvalue_convexity` follows by applying it to `Heps ε` and letting `ε ↓ 0` via
`Heps_tendsto`. That assembly is not done here.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-! ### The gradient of a test function -/

section Gradient

/-- The gradient of `f` is the Riesz representative of `fderiv ℝ f`; it vanishes outside the
topological support of `f`. -/
theorem gradient_eq_zero_of_notMem_tsupport {f : Euc d → ℝ} {x : Euc d} (hx : x ∉ tsupport f) :
    gradient f x = 0 := by
  have h : fderiv ℝ f x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 h))
  simp [gradient, h]

/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  (toDual ℝ (Euc d)).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

/-- The gradient of a compactly supported function has compact support. -/
theorem hasCompactSupport_gradient {f : Euc d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (gradient f) :=
  (hf.fderiv (𝕜 := ℝ)).comp_left (g := (toDual ℝ (Euc d)).symm) (map_zero _)

/-- For a smooth test function `f`, a continuous integrand `G` with `G 0 = 0` and `p > 0`, the
integrand `G(∇f)^p` is integrable (continuous with compact support). -/
theorem integrable_integrand_rpow {K : Set (Euc d)} {f : Euc d → ℝ} (hf : IsTestFn K f)
    {G : Euc d → ℝ} (hG : Continuous G) (hG0 : G 0 = 0) {p : ℝ} (hp : 0 < p) :
    Integrable fun x => G (gradient f x) ^ p := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hG.comp (continuous_gradient hf.contDiff_one)).rpow_const fun _ => Or.inr hp.le
  · exact (hasCompactSupport_gradient hf.hasCompactSupport).comp_left
      (g := fun ξ => G ξ ^ p) (by simp [hG0, Real.zero_rpow hp.ne'])

end Gradient

/-! ### The general-integrand eigenvalue -/

/-- The Rayleigh quotient of `f` for a general integrand `F` at exponent `p`:
`(∫ F(∇f)^p) / (∫ |f|^p)` (paper (3.7), the quotient). -/
noncomputable def rayleighGen (p : ℝ) (F : Euc d → ℝ) (f : Euc d → ℝ) : ℝ :=
  (∫ x, F (gradient f x) ^ p) / (∫ x, |f x| ^ p)

/-- The anisotropic `p`-eigenvalue `λ_{p,F}(K)` for a general integrand `F` (paper (3.7)),
realized over smooth test functions, with the same subtype index as `lambdaMix` (so that the
value is `0` when `K` admits no test function, e.g. `K = ∅`). -/
noncomputable def lambdaGen (p : ℝ) (F : Euc d → ℝ) (K : Set (Euc d)) : ℝ :=
  ⨅ f : {f : Euc d → ℝ // IsTestFn K f}, rayleighGen p F f.1

/-- The mixture integrand `H(ξ) = ∑_ℓ α_ℓ |u_ℓ · ξ|` (paper (3.6)). -/
noncomputable def Hmix {N : ℕ} (α : Fin N → ℝ) (u : Fin N → Euc d) (ξ : Euc d) : ℝ :=
  ∑ l, α l * |inner ℝ (u l) ξ|

/-- The smooth strongly convex regularization
`H_ε(ξ) = ∑_ℓ α_ℓ √((u_ℓ · ξ)² + ε² ‖ξ‖²)` of the mixture integrand (paper Lemma 3.2). -/
noncomputable def Heps {N : ℕ} (ε : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d) (ξ : Euc d) : ℝ :=
  ∑ l, α l * Real.sqrt ((inner ℝ (u l) ξ) ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2)

section General

variable {p : ℝ} {F G : Euc d → ℝ} {K : Set (Euc d)}

/-- The Rayleigh quotient of a nonnegative integrand is nonnegative. -/
theorem rayleighGen_nonneg (hF : ∀ ξ, 0 ≤ F ξ) (p : ℝ) (f : Euc d → ℝ) :
    0 ≤ rayleighGen p F f :=
  div_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (hF _) p)
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) p)

/-- The set of Rayleigh quotients of a nonnegative integrand is bounded below (by `0`). -/
theorem bddBelow_range_rayleighGen (hF : ∀ ξ, 0 ≤ F ξ) (p : ℝ) (K : Set (Euc d)) :
    BddBelow (Set.range fun f : {f : Euc d → ℝ // IsTestFn K f} => rayleighGen p F f.1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact rayleighGen_nonneg hF p g.1

/-- `λ_{p,F}(K) ≥ 0` for a nonnegative integrand. -/
theorem lambdaGen_nonneg (hF : ∀ ξ, 0 ≤ F ξ) (p : ℝ) (K : Set (Euc d)) :
    0 ≤ lambdaGen p F K :=
  Real.iInf_nonneg fun f => rayleighGen_nonneg hF p f.1

/-- `λ_{p,F}(K) ≤ rayleighGen p F f` for every test function `f` (nonnegative integrand). -/
theorem lambdaGen_le_rayleighGen (hF : ∀ ξ, 0 ≤ F ξ) (p : ℝ) {f : Euc d → ℝ}
    (hf : IsTestFn K f) : lambdaGen p F K ≤ rayleighGen p F f :=
  ciInf_le (bddBelow_range_rayleighGen hF p K) ⟨f, hf⟩

/-- Near-minimizers: if `K` admits a test function, then for every `δ > 0` there is a test
function whose Rayleigh quotient is within `δ` of `λ_{p,F}(K)`. -/
theorem exists_testFn_rayleighGen_lt [Nonempty {f : Euc d → ℝ // IsTestFn K f}] (p : ℝ)
    (F : Euc d → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : Euc d → ℝ, IsTestFn K f ∧ rayleighGen p F f < lambdaGen p F K + δ := by
  obtain ⟨f, hf⟩ := exists_lt_of_ciInf_lt (f := fun f : {f : Euc d → ℝ // IsTestFn K f} =>
    rayleighGen p F f.1) (lt_add_of_pos_right (lambdaGen p F K) hδ)
  exact ⟨f.1, f.2, hf⟩

/-- Monotonicity of the Rayleigh quotient in the integrand: if `0 ≤ F ≤ G` pointwise and `G`
is continuous with `G 0 = 0` (so that `G(∇f)^p` is integrable), then
`rayleighGen p F f ≤ rayleighGen p G f` for every test function `f`. -/
theorem rayleighGen_mono_integrand (hF : ∀ ξ, 0 ≤ F ξ) (hFG : ∀ ξ, F ξ ≤ G ξ)
    (hG : Continuous G) (hG0 : G 0 = 0) (hp : 0 < p) {f : Euc d → ℝ} (hf : IsTestFn K f) :
    rayleighGen p F f ≤ rayleighGen p G f := by
  unfold rayleighGen
  refine div_le_div_of_nonneg_right ?_
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) p)
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => Real.rpow_nonneg (hF _) p)
    (integrable_integrand_rpow hf hG hG0 hp)
    (Eventually.of_forall fun x => Real.rpow_le_rpow (hF _) (hFG _) hp.le)

/-- **Monotonicity of `λ_{p,F}(K)` in the integrand**: `0 ≤ F ≤ G` pointwise, `G` continuous
with `G 0 = 0`, `p > 0` give `λ_{p,F}(K) ≤ λ_{p,G}(K)`. -/
theorem lambdaGen_mono_integrand (hF : ∀ ξ, 0 ≤ F ξ) (hFG : ∀ ξ, F ξ ≤ G ξ)
    (hG : Continuous G) (hG0 : G 0 = 0) (hp : 0 < p) (K : Set (Euc d)) :
    lambdaGen p F K ≤ lambdaGen p G K :=
  ciInf_mono (bddBelow_range_rayleighGen hF p K) fun f =>
    rayleighGen_mono_integrand hF hFG hG hG0 hp f.2

end General

/-! ### The mixture integrand and its regularization -/

section Mixture

variable {N : ℕ} {α : Fin N → ℝ} {u : Fin N → Euc d}

/-- `H(∇f)(x) = mixtureGrad α u f x` (paper (3.6)): the directional-derivative expression of
`Komlos/Eigenvalue.lean` is the mixture integrand evaluated at the gradient. No differentiability
is needed, since `⟪∇f(x), v⟫ = Df(x) v` holds for Mathlib's `gradient` unconditionally. -/
theorem mixtureGrad_eq_Hmix_gradient (α : Fin N → ℝ) (u : Fin N → Euc d) (f : Euc d → ℝ)
    (x : Euc d) : mixtureGrad α u f x = Hmix α u (gradient f x) := by
  unfold mixtureGrad Hmix
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [real_inner_comm, inner_gradient_left]

/-- `rayleighMix p α u f = rayleighGen p (Hmix α u) f`. -/
theorem rayleighMix_eq_rayleighGen (p : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d)
    (f : Euc d → ℝ) : rayleighMix p α u f = rayleighGen p (Hmix α u) f := by
  simp only [rayleighMix, rayleighGen, mixtureGrad_eq_Hmix_gradient]

/-- **The mixture eigenvalue is the general one at the mixture integrand**:
`lambdaMix p α u K = lambdaGen p (Hmix α u) K`. -/
theorem lambdaMix_eq_lambdaGen (p : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d)
    (K : Set (Euc d)) : lambdaMix p α u K = lambdaGen p (Hmix α u) K := by
  simp only [lambdaMix, lambdaGen, rayleighMix_eq_rayleighGen]

/-- `Hmix ≥ 0` for nonnegative weights. -/
theorem Hmix_nonneg (hmix : IsMixture α u) (ξ : Euc d) : 0 ≤ Hmix α u ξ :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hmix.nonneg l) (abs_nonneg _)

/-- `Heps ε ≥ 0` for nonnegative weights. -/
theorem Heps_nonneg (hmix : IsMixture α u) (ε : ℝ) (ξ : Euc d) : 0 ≤ Heps ε α u ξ :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hmix.nonneg l) (Real.sqrt_nonneg _)

@[simp] theorem Hmix_zero (α : Fin N → ℝ) (u : Fin N → Euc d) : Hmix α u 0 = 0 := by
  simp [Hmix]

@[simp] theorem Heps_zero (ε : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d) : Heps ε α u 0 = 0 := by
  simp [Heps]

/-- At `ε = 0` the regularization is the mixture integrand itself. -/
theorem Heps_zero_eps (α : Fin N → ℝ) (u : Fin N → Euc d) (ξ : Euc d) :
    Heps 0 α u ξ = Hmix α u ξ := by
  simp [Heps, Hmix, Real.sqrt_sq_eq_abs]

/-- `Hmix` is continuous. -/
theorem continuous_Hmix (α : Fin N → ℝ) (u : Fin N → Euc d) : Continuous (Hmix α u) := by
  unfold Hmix
  exact continuous_finsetSum _ fun l _ =>
    continuous_const.mul (continuous_const.inner continuous_id).abs

/-- `Heps ε` is continuous. -/
theorem continuous_Heps (ε : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d) :
    Continuous (Heps ε α u) := by
  unfold Heps
  refine continuous_finsetSum _ fun l _ => continuous_const.mul (Real.continuous_sqrt.comp ?_)
  exact ((continuous_const.inner continuous_id).pow 2).add
    (continuous_const.mul (continuous_norm.pow 2))

/-- `ε ↦ Heps ε α u ξ` is continuous at `ε = 0` with value `Hmix α u ξ`. -/
theorem tendsto_Heps (α : Fin N → ℝ) (u : Fin N → Euc d) (ξ : Euc d) :
    Tendsto (fun ε => Heps ε α u ξ) (𝓝 0) (𝓝 (Hmix α u ξ)) := by
  have hc : Continuous fun ε : ℝ => Heps ε α u ξ := by
    unfold Heps
    refine continuous_finsetSum _ fun l _ => continuous_const.mul (Real.continuous_sqrt.comp ?_)
    exact continuous_const.add ((continuous_id.pow 2).mul continuous_const)
  simpa only [Heps_zero_eps] using hc.tendsto 0

/-- `H ≤ ‖·‖` for a mixture (unit directions, weights summing to one). -/
theorem Hmix_le_norm (hmix : IsMixture α u) (ξ : Euc d) : Hmix α u ξ ≤ ‖ξ‖ := by
  unfold Hmix
  calc ∑ l, α l * |inner ℝ (u l) ξ| ≤ ∑ l, α l * ‖ξ‖ := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hmix.nonneg l)
        calc |inner ℝ (u l) ξ| ≤ ‖u l‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
          _ = ‖ξ‖ := by rw [hmix.norm_eq_one, one_mul]
    _ = ‖ξ‖ := by rw [← Finset.sum_mul, hmix.sum_eq_one, one_mul]

/-- The lower sandwich bound `H ≤ H_ε` (paper Lemma 3.2), for every real `ε`. -/
theorem Hmix_le_Heps (hmix : IsMixture α u) (ε : ℝ) (ξ : Euc d) :
    Hmix α u ξ ≤ Heps ε α u ξ := by
  unfold Hmix Heps
  refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hmix.nonneg l)
  exact Real.abs_le_sqrt (le_add_of_nonneg_right (by positivity))

/-- The upper sandwich bound `H_ε ≤ H + |ε| ‖·‖` (paper Lemma 3.2), for every real `ε`. -/
theorem Heps_le_Hmix_add_abs (hmix : IsMixture α u) (ε : ℝ) (ξ : Euc d) :
    Heps ε α u ξ ≤ Hmix α u ξ + |ε| * ‖ξ‖ := by
  unfold Hmix Heps
  calc ∑ l, α l * Real.sqrt ((inner ℝ (u l) ξ) ^ 2 + ε ^ 2 * ‖ξ‖ ^ 2)
      ≤ ∑ l, α l * (|inner ℝ (u l) ξ| + |ε| * ‖ξ‖) := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hmix.nonneg l)
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        have h1 : (inner ℝ (u l) ξ) ^ 2 = |inner ℝ (u l) ξ| ^ 2 := (sq_abs _).symm
        have h2 : ε ^ 2 = |ε| ^ 2 := (sq_abs _).symm
        rw [h1, h2]
        nlinarith [abs_nonneg (inner ℝ (u l) ξ), abs_nonneg ε, norm_nonneg ξ,
          mul_nonneg (abs_nonneg (inner ℝ (u l) ξ)) (mul_nonneg (abs_nonneg ε) (norm_nonneg ξ))]
    _ = ∑ l, α l * |inner ℝ (u l) ξ| + |ε| * ‖ξ‖ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmix.sum_eq_one, one_mul]

/-- The upper sandwich bound `H_ε ≤ H + ε ‖·‖` (paper Lemma 3.2) for `ε ≥ 0`. -/
theorem Heps_le_Hmix_add (hmix : IsMixture α u) {ε : ℝ} (hε : 0 ≤ ε) (ξ : Euc d) :
    Heps ε α u ξ ≤ Hmix α u ξ + ε * ‖ξ‖ := by
  simpa only [abs_of_nonneg hε] using Heps_le_Hmix_add_abs hmix ε ξ

/-- `H_ε ≤ 2 ‖·‖` for `|ε| ≤ 1`. -/
theorem Heps_le_two_mul_norm (hmix : IsMixture α u) {ε : ℝ} (hε : |ε| ≤ 1) (ξ : Euc d) :
    Heps ε α u ξ ≤ 2 * ‖ξ‖ := by
  calc Heps ε α u ξ ≤ Hmix α u ξ + |ε| * ‖ξ‖ := Heps_le_Hmix_add_abs hmix ε ξ
    _ ≤ ‖ξ‖ + 1 * ‖ξ‖ := by gcongr; exact Hmix_le_norm hmix ξ
    _ = 2 * ‖ξ‖ := by ring

/-- `λ_{p,H}(K) ≤ λ_{p,H_ε}(K)` for every `ε` (from `H ≤ H_ε`). -/
theorem lambdaMix_le_lambdaGen_Heps (hmix : IsMixture α u) {p : ℝ} (hp : 0 < p) (ε : ℝ)
    (K : Set (Euc d)) : lambdaMix p α u K ≤ lambdaGen p (Heps ε α u) K := by
  rw [lambdaMix_eq_lambdaGen]
  exact lambdaGen_mono_integrand (Hmix_nonneg hmix) (Hmix_le_Heps hmix ε)
    (continuous_Heps ε α u) (Heps_zero ε α u) hp K

/-- **Dominated convergence for the `H_ε` numerator**: for a fixed `C¹` compactly supported `f`,
`∫ H_ε(∇f)^p → ∫ H(∇f)^p` as `ε → 0`, dominated by `(2‖∇f‖)^p`. -/
theorem tendsto_integral_Heps_rpow (hmix : IsMixture α u) {p : ℝ} (hp : 0 < p)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) :
    Tendsto (fun ε => ∫ x, Heps ε α u (gradient f x) ^ p) (𝓝 0)
      (𝓝 (∫ x, Hmix α u (gradient f x) ^ p)) := by
  have hgc : Continuous (gradient f) := continuous_gradient hf
  have hgs : HasCompactSupport (gradient f) := hasCompactSupport_gradient hsupp
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, |ε| ≤ 1 := by
    filter_upwards [eventually_lt_nhds one_pos, eventually_gt_nhds (neg_one_lt_zero)]
      with ε h1 h2
    exact abs_le.2 ⟨h2.le, h1.le⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (2 * ‖gradient f x‖) ^ p)
    ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ε =>
      (((continuous_Heps ε α u).comp hgc).rpow_const fun _ => Or.inr hp.le).aestronglyMeasurable
  · filter_upwards [hev] with ε hε
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Heps_nonneg hmix ε _) p)]
    exact Real.rpow_le_rpow (Heps_nonneg hmix ε _) (Heps_le_two_mul_norm hmix hε _) hp.le
  · refine Continuous.integrable_of_hasCompactSupport
      ((continuous_const.mul hgc.norm).rpow_const fun _ => Or.inr hp.le) ?_
    exact hgs.comp_left (g := fun ξ : Euc d => (2 * ‖ξ‖) ^ p)
      (by simp [Real.zero_rpow hp.ne'])
  · exact Eventually.of_forall fun x => (tendsto_Heps α u _).rpow_const (Or.inr hp.le)

/-- For a fixed test function, the `H_ε` Rayleigh quotient converges to the mixture one as
`ε → 0`. -/
theorem tendsto_rayleighGen_Heps (hmix : IsMixture α u) {p : ℝ} (hp : 0 < p)
    {K : Set (Euc d)} {f : Euc d → ℝ} (hf : IsTestFn K f) :
    Tendsto (fun ε => rayleighGen p (Heps ε α u) f) (𝓝 0) (𝓝 (rayleighMix p α u f)) := by
  rw [rayleighMix_eq_rayleighGen]
  exact (tendsto_integral_Heps_rpow hmix hp hf.contDiff_one hf.hasCompactSupport).div_const _

/-- **The `H_ε ↓ H` limit at fixed `p`** (paper Lemma 3.2, last paragraph, at the level of the
`p`-eigenvalue): `λ_{p,H_ε}(K) → λ_{p,H}(K)` as `ε → 0`, for every `K` and every `p > 0`.

Proof: the lower bound `λ_{p,H} ≤ λ_{p,H_ε}` is monotonicity in the integrand (`H ≤ H_ε`); for
the upper bound, fix a near-optimal test function `f` for `λ_{p,H}`; then
`λ_{p,H_ε} ≤ rayleighGen p H_ε f → rayleighMix p f < λ_{p,H} + δ` by dominated convergence. -/
theorem Heps_tendsto_nhds (hmix : IsMixture α u) {p : ℝ} (hp : 0 < p) (K : Set (Euc d)) :
    Tendsto (fun ε => lambdaGen p (Heps ε α u) K) (𝓝 0) (𝓝 (lambdaMix p α u K)) := by
  rcases isEmpty_or_nonempty {f : Euc d → ℝ // IsTestFn K f} with hne | hne
  · simp only [lambdaGen, lambdaMix, Real.iInf_of_isEmpty]
    exact tendsto_const_nhds
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Eventually.of_forall fun ε => ha.trans_le (lambdaMix_le_lambdaGen_Heps hmix hp ε K)
  · intro b hb
    obtain ⟨f, hf, hlt⟩ := exists_testFn_rayleighGen_lt (K := K) p (Hmix α u)
      (half_pos (sub_pos.2 hb))
    rw [← lambdaMix_eq_lambdaGen, ← rayleighMix_eq_rayleighGen] at hlt
    have hb' : rayleighMix p α u f < b := by linarith
    filter_upwards [(tendsto_rayleighGen_Heps hmix hp hf).eventually (eventually_lt_nhds hb')]
      with ε hε
    exact (lambdaGen_le_rayleighGen (Heps_nonneg hmix ε) p hf).trans_lt hε

/-- **The `H_ε ↓ H` limit at fixed `p > 1`** (paper Lemma 3.2): `λ_{p,H_ε}(K) → λ_{p,H}(K)` as
`ε ↓ 0`. This is the bridge from eigenvalue convexity for the smooth strongly convex integrands
`H_ε` back to the mixture integrand `H`. -/
theorem Heps_tendsto (hmix : IsMixture α u) {p : ℝ} (hp : 1 < p) (K : Set (Euc d)) :
    Tendsto (fun ε => lambdaGen p (Heps ε α u) K) (𝓝[>] 0) (𝓝 (lambdaMix p α u K)) :=
  (Heps_tendsto_nhds hmix (by linarith) K).mono_left nhdsWithin_le_nhds

/-- **Reduction of mixture eigenvalue convexity to the smooth integrands `H_ε`** (paper Lemma
3.2, last paragraph, at fixed `p`): if the convexity inequality (3.8) holds for
`lambdaGen p (Heps ε α u)` for all small `ε > 0`, then it holds for `lambdaMix p α u`. Together
with eigenvalue convexity for smooth strongly convex integrands (paper Proposition A.1, applied to
`Heps ε`), this discharges `Komlos.eigenvalue_convexity`. -/
theorem lambdaMix_convex_of_Heps (hmix : IsMixture α u) {p : ℝ} (hp : 1 < p)
    {K₀ K₁ : Set (Euc d)} {t : ℝ}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), lambdaGen p (Heps ε α u) ((1 - t) • K₀ + t • K₁) ≤
      (1 - t) * lambdaGen p (Heps ε α u) K₀ + t * lambdaGen p (Heps ε α u) K₁) :
    lambdaMix p α u ((1 - t) • K₀ + t • K₁) ≤
      (1 - t) * lambdaMix p α u K₀ + t * lambdaMix p α u K₁ :=
  le_of_tendsto_of_tendsto (Heps_tendsto hmix hp _)
    (((Heps_tendsto hmix hp K₀).const_mul _).add ((Heps_tendsto hmix hp K₁).const_mul _)) h

end Mixture

end Komlos
