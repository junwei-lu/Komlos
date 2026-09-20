import Komlos.Literature.Regularized.ScalarLimitAux

/-!
# The upper scalar limit: `regMin 2 κ Ψ K ≤ λ_{p,F}(K)/p + δ`

`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*, upper half.  The bound is obtained by
exhibiting **one** admissible competitor, whose regularized energy is computed classically.

## The competitor

Revision 2 prescribes competitors of the form `u = g^k` with `g = (f² + τ)^{1/(2k)} η`.  Here we
use the cutoff-free variant

`S = (f² + τ)^β - τ^β`  with  `β = p/(4m)`,  `m = ⌈p/2⌉ + 1`,

which vanishes exactly where the test function `f` vanishes (so no cutoff `η` is needed), is
`C^∞` because `f² + τ ≥ τ > 0`, and satisfies `S ≤ |f|^{2β}` by subadditivity of `t ↦ t^β`
(`Real.rpow_add_le_add_rpow`, `β ≤ 1`).  The exponent-`2` competitor is the normalization of
`T = S^m`, and the exponent-`p` function it corresponds to is `u = T^{2/p} = S^{2m/p}`; the two
conditions `1 ≤ m` and `p ≤ 2m` are exactly what make the integrands
`S^{2m-p} F(∇S)^p` and `S^{2m-2}(…)²` bounded.

The pointwise heart of the estimate is `powShift_pointwise_bound`:

`(2m/p)^p · S^{2m-p} · F(∇S)^p ≤ F(∇f)^p`,

where the two sides differ exactly by the factor `(s²)^e / (s²+τ)^e ≤ 1` with `e = p(1-β) > 0`.

## Main results

* `powShift`, `powShift_pointwise_bound`: the shifted power and the scalar inequality;
* `exists_upperCompetitor`: a nonnegative test function `S` and an exponent `m` with
  `(2m/p)^p ∫ S^{2m-p} F(∇S)^p ≤ (λ + δ) ∫ S^{2m}`;
* `eventually_regMin_le_of_params`: the upper scalar limit along any family of parameters with
  `R → ∞`, `ε → 0`, `κ → 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The shifted power `s ↦ (s² + τ)^β - τ^β` -/

/-- The shifted power `(s² + τ)^β - τ^β`: a `C^∞` nonnegative function of `s` vanishing exactly
at `s = 0`, bounded by `|s|^{2β}`. -/
noncomputable def powShift (β τ s : ℝ) : ℝ := (s ^ 2 + τ) ^ β - τ ^ β

section PowShift

variable {β τ : ℝ}

theorem powShift_base_pos (hτ : 0 < τ) (s : ℝ) : 0 < s ^ 2 + τ := by positivity

theorem powShift_nonneg (hβ : 0 ≤ β) (hτ : 0 < τ) (s : ℝ) : 0 ≤ powShift β τ s := by
  rw [powShift, sub_nonneg]
  exact Real.rpow_le_rpow hτ.le (by nlinarith [sq_nonneg s]) hβ

/-- Subadditivity of `t ↦ t^β` for `β ≤ 1` gives `S ≤ |s|^{2β}`. -/
theorem powShift_le_abs_rpow (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hτ : 0 < τ) (s : ℝ) :
    powShift β τ s ≤ |s| ^ (2 * β) := by
  have h := Real.rpow_add_le_add_rpow (sq_nonneg s) hτ.le hβ0 hβ1
  have hsq : (s ^ 2) ^ β = |s| ^ (2 * β) := by
    rw [← sq_abs s, ← Real.rpow_natCast |s| 2, ← Real.rpow_mul (abs_nonneg s)]
    norm_num
  rw [powShift]
  rw [hsq] at h
  linarith

theorem powShift_eq_zero_iff (hβ : 0 < β) (hτ : 0 < τ) (s : ℝ) :
    powShift β τ s = 0 ↔ s = 0 := by
  constructor
  · intro h
    by_contra hs
    have hs2 : 0 < s ^ 2 := by
      rcases lt_trichotomy s 0 with h' | h' | h'
      · nlinarith
      · exact absurd h' hs
      · nlinarith
    have hlt : τ < s ^ 2 + τ := by linarith
    have := Real.rpow_lt_rpow hτ.le hlt hβ
    rw [powShift, sub_eq_zero] at h
    linarith
  · rintro rfl
    simp [powShift]

theorem hasDerivAt_powShift (hτ : 0 < τ) (β s : ℝ) :
    HasDerivAt (powShift β τ) (2 * β * s * (s ^ 2 + τ) ^ (β - 1)) s := by
  have hb : HasDerivAt (fun t : ℝ => t ^ 2 + τ) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const τ
  have h := hb.rpow_const (p := β) (Or.inl (powShift_base_pos hτ s).ne')
  have h2 := h.sub_const (τ ^ β)
  have heq : 2 * s * β * (s ^ 2 + τ) ^ (β - 1) = 2 * β * s * (s ^ 2 + τ) ^ (β - 1) := by ring
  rw [heq] at h2
  exact h2

theorem differentiable_powShift (hτ : 0 < τ) (β : ℝ) : Differentiable ℝ (powShift β τ) :=
  fun s => (hasDerivAt_powShift hτ β s).differentiableAt

theorem deriv_powShift (hτ : 0 < τ) (β s : ℝ) :
    deriv (powShift β τ) s = 2 * β * s * (s ^ 2 + τ) ^ (β - 1) :=
  (hasDerivAt_powShift hτ β s).deriv

theorem contDiff_powShift (hτ : 0 < τ) (β : ℝ) : ContDiff ℝ ∞ (powShift β τ) := by
  have hbase : ContDiff ℝ ∞ fun s : ℝ => s ^ 2 + τ := (contDiff_id.pow 2).add contDiff_const
  refine ContDiff.sub ?_ contDiff_const
  rw [contDiff_iff_contDiffAt]
  intro s
  have h := (Real.contDiffAt_rpow_const_of_ne (x := s ^ 2 + τ) (p := β) (n := ∞)
    (powShift_base_pos hτ s).ne').comp s hbase.contDiffAt
  simpa only [Function.comp_def] using h

end PowShift

/-! ### The scalar heart of the competitor estimate -/

/-- **The pointwise competitor bound.**  With `β = p/(4m)` and `e = p(1-β) > 0`,
`(2m/p)^p · S^{2m-p} · (|S'(s)| v)^p = (s²)^e (s²+τ)^{-e} v^p ≤ v^p`. -/
theorem powShift_pointwise_bound {p β τ : ℝ} {m : ℕ} (hp : 0 < p) (hτ : 0 < τ)
    (hm : (0 : ℝ) < m) (hβ : β = p / (4 * m)) (hβ1 : β < 1) (hpm : p ≤ 2 * m) (s : ℝ) {v : ℝ}
    (hv : 0 ≤ v) :
    (2 * m / p) ^ p *
        (powShift β τ s ^ ((2 * (m : ℝ)) - p) *
          (|2 * β * s * (s ^ 2 + τ) ^ (β - 1)| * v) ^ p) ≤ v ^ p := by
  set A : ℝ := s ^ 2 + τ with hA
  have hApos : 0 < A := powShift_base_pos hτ s
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hn : (0 : ℝ) ≤ 2 * (m : ℝ) - p := by linarith
  set e : ℝ := p * (1 - β) with he
  have hepos : 0 < e := by rw [he]; nlinarith
  -- the derivative in absolute value
  have habs : |2 * β * s * A ^ (β - 1)| = 2 * β * |s| * A ^ (β - 1) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hApos _),
      abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hβ0]
  -- Step 1: bound the shifted power
  have h1 : powShift β τ s ^ (2 * (m : ℝ) - p) ≤ |s| ^ (2 * β * (2 * (m : ℝ) - p)) := by
    refine le_trans (Real.rpow_le_rpow (powShift_nonneg hβ0.le hτ s)
      (powShift_le_abs_rpow hβ0.le hβ1.le hτ s) hn) ?_
    rw [← Real.rpow_mul (abs_nonneg s)]
  -- Step 2: expand the flux power
  have h2 : (2 * β * |s| * A ^ (β - 1) * v) ^ p =
      (2 * β) ^ p * |s| ^ p * A ^ ((β - 1) * p) * v ^ p := by
    rw [Real.mul_rpow (by positivity) hv, Real.mul_rpow (by positivity)
      (Real.rpow_nonneg hApos.le _), Real.mul_rpow (by positivity) (abs_nonneg s),
      ← Real.rpow_mul hApos.le]
  -- Step 3: combine the two powers of `|s|`
  have hsum : 2 * β * (2 * (m : ℝ) - p) + p = 2 * e := by
    have h4m : 4 * (m : ℝ) * β = p := by rw [hβ]; field_simp
    rw [he]; nlinarith [h4m]
  have h3 : |s| ^ (2 * β * (2 * (m : ℝ) - p)) * |s| ^ p = |s| ^ (2 * e) := by
    rw [← Real.rpow_add' (abs_nonneg s) (by rw [hsum]; positivity), hsum]
  -- Step 4: the normalizing constant
  have hconst : (2 * (m : ℝ) / p) ^ p * (2 * β) ^ p = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : 2 * (m : ℝ) / p * (2 * β) = 1 := by rw [hβ]; field_simp; ring
    rw [this, Real.one_rpow]
  -- Step 5: the ratio `(s²)^e / A^e ≤ 1`
  have hratio : |s| ^ (2 * e) * A ^ ((β - 1) * p) ≤ 1 := by
    have hsq : |s| ^ (2 * e) = (s ^ 2) ^ e := by
      rw [← sq_abs s, ← Real.rpow_natCast |s| 2, ← Real.rpow_mul (abs_nonneg s)]
      norm_num
    have hAe : A ^ ((β - 1) * p) = (A ^ e)⁻¹ := by
      rw [he, show (β - 1) * p = -(p * (1 - β)) by ring, Real.rpow_neg hApos.le]
    have hle : (s ^ 2) ^ e ≤ A ^ e :=
      Real.rpow_le_rpow (sq_nonneg s) (by rw [hA]; linarith) hepos.le
    have hApose : 0 < A ^ e := Real.rpow_pos_of_pos hApos _
    rw [hsq, hAe, ← div_eq_mul_inv, div_le_one hApose]
    exact hle
  -- assemble
  have hvp : 0 ≤ v ^ p := Real.rpow_nonneg hv _
  calc (2 * (m : ℝ) / p) ^ p *
        (powShift β τ s ^ (2 * (m : ℝ) - p) * (|2 * β * s * A ^ (β - 1)| * v) ^ p)
      = (2 * (m : ℝ) / p) ^ p *
          (powShift β τ s ^ (2 * (m : ℝ) - p) * ((2 * β) ^ p * |s| ^ p *
            A ^ ((β - 1) * p) * v ^ p)) := by rw [habs, h2]
    _ ≤ (2 * (m : ℝ) / p) ^ p *
          (|s| ^ (2 * β * (2 * (m : ℝ) - p)) * ((2 * β) ^ p * |s| ^ p *
            A ^ ((β - 1) * p) * v ^ p)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 ?_) (by positivity)
          positivity
    _ = ((2 * (m : ℝ) / p) ^ p * (2 * β) ^ p) *
          ((|s| ^ (2 * β * (2 * (m : ℝ) - p)) * |s| ^ p) * A ^ ((β - 1) * p)) * v ^ p := by
          ring
    _ = (|s| ^ (2 * e) * A ^ ((β - 1) * p)) * v ^ p := by rw [hconst, h3]; ring
    _ ≤ 1 * v ^ p := mul_le_mul_of_nonneg_right hratio hvp
    _ = v ^ p := one_mul _

/-! ### The competitor -/

/-- **The competitor of the upper scalar limit.**  Given `δ > 0` there is a nonnegative test
function `S` and an integer `m ≥ max(1, p/2)` with

`(2m/p)^p ∫ S^{2m-p} F(∇S)^p ≤ (λ_{p,F}(K) + δ) ∫ S^{2m}`.

The exponent-`2` competitor is the `L²`-normalization of `S^m`; the displayed quantity is
`∫ F(∇u)^p` for `u = S^{2m/p}`, i.e. the `p`-Rayleigh numerator of the function the substitution
`w = u^{p/2}` turns `S^m` into.

`S` is `(f² + τ)^{p/(4m)} - τ^{p/(4m)}` for a near-optimal test function `f` and a small `τ`;
the numerator estimate is `powShift_pointwise_bound` (which holds for every `τ`), and `τ` is
chosen only to make the denominator `∫ S^{2m}` close to `∫ |f|^p`. -/
theorem exists_upperCompetitor {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Euc d → ℝ) (m : ℕ), IsTestFn K S ∧ (∀ x, 0 ≤ S x) ∧ 1 ≤ m ∧ p < 2 * m ∧
      (2 * (m : ℝ) / p) ^ p * ∫ x, S x ^ (2 * (m : ℝ) - p) * F (gradient S x) ^ p ≤
        (lambdaGen p F K + δ) * ∫ x, S x ^ (2 * m) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hlam0 : 0 ≤ lambdaGen p F K := lambdaGen_nonneg hF.nonneg p K
  haveI := hK.nonempty_testFn
  obtain ⟨f, hf, hflt⟩ := exists_testFn_rayleighGen_lt (K := K) p F (half_pos hδ)
  -- the exponent `m`
  set m : ℕ := ⌈p / 2⌉₊ + 1 with hmdef
  have hm1 : 1 ≤ m := Nat.le_add_left 1 _
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  have hpm : p < 2 * (m : ℝ) := by
    have h1 : p / 2 ≤ (⌈p / 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((m : ℕ) : ℝ) = (⌈p / 2⌉₊ : ℝ) + 1 := by rw [hmdef]; push_cast; ring
    rw [h2]; linarith
  set β : ℝ := p / (4 * (m : ℝ)) with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβ1 : β < 1 := by
    rw [hβdef, div_lt_one (by positivity)]
    linarith
  -- the `τ`-family of competitors
  set τ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hτdef
  have hτpos : ∀ k, 0 < τ k := fun k => by rw [hτdef]; positivity
  set S : ℕ → Euc d → ℝ := fun k x => powShift β (τ k) (f x) with hSdef
  have hSnn : ∀ k x, 0 ≤ S k x := fun k x => powShift_nonneg hβ0.le (hτpos k) _
  have hScd : ∀ k, ContDiff ℝ ∞ (S k) := fun k => by
    have h := (contDiff_powShift (hτpos k) β).comp
      (hf.contDiff.of_le (by exact_mod_cast le_top))
    simpa only [Function.comp_def, hSdef] using h
  have hSsupp : ∀ k, Function.support (S k) = Function.support f := by
    intro k
    ext x
    simp only [Function.mem_support, hSdef, ne_eq]
    rw [powShift_eq_zero_iff hβ0 (hτpos k)]
  have hStsupp : ∀ k, tsupport (S k) = tsupport f := by
    intro k; unfold tsupport; rw [hSsupp k]
  have hStest : ∀ k, IsTestFn K (S k) := fun k =>
    { contDiff := (hScd k).of_le (by exact_mod_cast le_top)
      hasCompactSupport := by
        show IsCompact (tsupport (S k)); rw [hStsupp k]; exact hf.hasCompactSupport
      supp_subset := by rw [hStsupp k]; exact hf.supp_subset
      ne_zero := by
        intro hcon
        refine hf.ne_zero (funext fun x => ?_)
        have hx : x ∉ Function.support (S k) := by
          simp [hcon]
        rw [hSsupp k] at hx
        simpa using hx }
  -- the gradient of the competitor
  have hSgrad : ∀ k x, gradient (S k) x =
      (2 * β * f x * (f x ^ 2 + τ k) ^ (β - 1)) • gradient f x := by
    intro k x
    have h := gradient_comp_apply (G := powShift β (τ k)) (differentiable_powShift (hτpos k) β)
      (v := f) (x := x) (hf.contDiff.differentiable (by simp) x)
    rw [hSdef]
    simpa only [deriv_powShift (hτpos k) β] using h
  -- the pointwise numerator bound
  have hptw : ∀ k x, (2 * (m : ℝ) / p) ^ p *
      (S k x ^ (2 * (m : ℝ) - p) * F (gradient (S k) x) ^ p) ≤ F (gradient f x) ^ p := by
    intro k x
    have hFg : F (gradient (S k) x) =
        |2 * β * f x * (f x ^ 2 + τ k) ^ (β - 1)| * F (gradient f x) := by
      rw [hSgrad k x, hF.homog]
    rw [hFg]
    exact powShift_pointwise_bound hp0 (hτpos k) hmR hβdef hβ1 hpm.le (f x) (hF.nonneg _)
  -- integrability
  have hFf : Integrable fun x => F (gradient f x) ^ p :=
    integrable_integrand_rpow hf hF.continuous hF.map_zero hp0
  have hrpowc : ∀ a : ℝ, 0 ≤ a → Continuous fun t : ℝ => t ^ a := fun a ha =>
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x a (Or.inr ha)
  have hnum_cont : ∀ k, Continuous fun x =>
      S k x ^ (2 * (m : ℝ) - p) * F (gradient (S k) x) ^ p := by
    intro k
    exact ((hrpowc _ (by linarith [hpm])).comp (hScd k).continuous).mul
      ((hrpowc p hp0.le).comp (hF.continuous.comp (continuous_gradient
        ((hScd k).of_le (by exact_mod_cast le_top)))))
  have hnum_supp : ∀ k, HasCompactSupport fun x =>
      S k x ^ (2 * (m : ℝ) - p) * F (gradient (S k) x) ^ p := by
    intro k
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport (S k)) (hStest k).hasCompactSupport fun x hx => ?_
    by_contra hxs0
    exact absurd (by
      have hg : gradient (S k) x = 0 := gradient_eq_zero_of_notMem_tsupport hxs0
      show S k x ^ (2 * (m : ℝ) - p) * F (gradient (S k) x) ^ p = 0
      rw [hg, hF.map_zero, Real.zero_rpow hp0.ne', mul_zero]) hx
  have hnum_int : ∀ k, Integrable fun x =>
      S k x ^ (2 * (m : ℝ) - p) * F (gradient (S k) x) ^ p := fun k =>
    (hnum_cont k).integrable_of_hasCompactSupport (hnum_supp k)
  -- the numerator bound, integrated
  have hnum : ∀ k, (2 * (m : ℝ) / p) ^ p *
      ∫ x, S k x ^ (2 * (m : ℝ) - p) * F (gradient (S k) x) ^ p ≤
        ∫ x, F (gradient f x) ^ p := by
    intro k
    rw [← integral_const_mul]
    exact integral_mono ((hnum_int k).const_mul _) hFf (hptw k)
  -- the denominator converges to `∫ |f|^p`
  have hdom : ∀ k x, S k x ^ (2 * m) ≤ |f x| ^ p := by
    intro k x
    have h1 : S k x ≤ |f x| ^ (2 * β) :=
      powShift_le_abs_rpow hβ0.le hβ1.le (hτpos k) (f x)
    have h2 : S k x ^ (2 * m) ≤ (|f x| ^ (2 * β)) ^ (2 * m) :=
      pow_le_pow_left₀ (hSnn k x) h1 (2 * m)
    have h3 : (|f x| ^ (2 * β)) ^ (2 * m) = |f x| ^ p := by
      rw [← Real.rpow_natCast (|f x| ^ (2 * β)) (2 * m), ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      rw [hβdef]
      push_cast
      field_simp
      ring
    linarith [h2, h3.le, h3.ge]
  have hfp_int : Integrable fun x => |f x| ^ p := by
    refine Continuous.integrable_of_hasCompactSupport
      ((hrpowc p hp0.le).comp hf.contDiff.continuous.abs) ?_
    have h := hf.hasCompactSupport.comp_left (g := fun t : ℝ => |t| ^ p)
      (by simp [Real.zero_rpow hp0.ne'])
    simpa [Function.comp_def] using h
  have hden_lim : Tendsto (fun k => ∫ x, S k x ^ (2 * m)) atTop (𝓝 (∫ x, |f x| ^ p)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |f x| ^ p)
      (fun k => (((hScd k).continuous.pow (2 * m)).aestronglyMeasurable)) hfp_int
      (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hSnn k x) _)]
      exact hdom k x
    · -- pointwise convergence
      have hτlim : Tendsto τ atTop (𝓝 0) := by
        rw [hτdef]; exact tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun k => (f x ^ 2 + τ k) ^ β) atTop (𝓝 ((f x ^ 2) ^ β)) := by
        have := (hrpowc β hβ0.le).tendsto (f x ^ 2)
        exact this.comp (by simpa using tendsto_const_nhds.add hτlim)
      have h2 : Tendsto (fun k => τ k ^ β) atTop (𝓝 0) := by
        have := (hrpowc β hβ0.le).tendsto (0 : ℝ)
        have h3 := this.comp hτlim
        rwa [Real.zero_rpow hβ0.ne'] at h3
      have h4 : Tendsto (fun k => S k x) atTop (𝓝 ((f x ^ 2) ^ β)) := by
        have := h1.sub h2
        rw [sub_zero] at this
        simpa only [hSdef, powShift] using this
      have h5 := (continuous_pow (2 * m)).continuousAt.tendsto.comp h4
      have h6 : ((f x ^ 2) ^ β) ^ (2 * m) = |f x| ^ p := by
        rw [← sq_abs (f x), ← Real.rpow_natCast |f x| 2, ← Real.rpow_mul (abs_nonneg _),
          ← Real.rpow_natCast (|f x| ^ ((2 : ℕ) * β)) (2 * m), ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        rw [hβdef]
        push_cast
        field_simp
        ring
      rw [← h6]
      simpa only [Function.comp_def] using h5
  -- choose `τ`
  have hfp_pos : 0 < ∫ x, |f x| ^ p :=
    integral_abs_rpow_pos hp0 (hf.memW0 p).memLp hf.not_ae_eq_zero
  have hnumlt : (∫ x, F (gradient f x) ^ p) < (lambdaGen p F K + δ / 2) * ∫ x, |f x| ^ p := by
    rw [rayleighGen, div_lt_iff₀ hfp_pos] at hflt
    exact hflt
  have hgt : (∫ x, F (gradient f x) ^ p) < (lambdaGen p F K + δ) * ∫ x, |f x| ^ p := by
    nlinarith [hfp_pos, hnumlt]
  obtain ⟨k, hk⟩ := ((hden_lim.const_mul (lambdaGen p F K + δ)).eventually
    (eventually_gt_nhds hgt)).exists
  exact ⟨S k, m, hStest k, hSnn k, hm1, hpm, le_trans (hnum k) hk.le⟩

/-! ### Auxiliary power and gradient identities -/

/-- `(s^k)^a = s^{ka}` for `s ≥ 0`, a natural power inside a real power. -/
theorem natPow_rpow {s : ℝ} (hs : 0 ≤ s) (k : ℕ) (a : ℝ) : (s ^ k) ^ a = s ^ ((k : ℝ) * a) := by
  rw [← Real.rpow_natCast s k, ← Real.rpow_mul hs]

theorem hasGradientAt_const_mul {f : Euc d → ℝ} {g x : Euc d} (hf : HasGradientAt f g x) (c : ℝ) :
    HasGradientAt (fun y => c * f y) (c • g) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  simpa using hf.const_mul c

/-- The classical chain rule for a natural power: `∇(S^m) = m S^{m-1} ∇S`. -/
theorem gradient_natPow {S : Euc d → ℝ} (hS : Differentiable ℝ S) (m : ℕ) (x : Euc d) :
    gradient (fun y => S y ^ m) x = ((m : ℝ) * S x ^ (m - 1)) • gradient S x := by
  have h := gradient_comp_apply (G := fun t : ℝ => t ^ m) (differentiable_pow m) (hS x)
  simpa [deriv_pow] using h

/-! ### The two densities of the `S^m` competitor -/

/-- The numerator density of the `S^m` competitor with mollification error `η = M ε`:
`S^{2m-p} ((2m/p) F(∇S) + η S)^p`.  At `η = 0` it is `(2m/p)^p S^{2m-p} F(∇S)^p`, the integrand
of `exists_upperCompetitor`. -/
noncomputable def upperNum (p : ℝ) (F : Euc d → ℝ) (m : ℕ) (η : ℝ) (S : Euc d → ℝ) (x : Euc d) :
    ℝ := S x ^ (2 * (m : ℝ) - p) * (2 * (m : ℝ) / p * F (gradient S x) + η * S x) ^ p

/-- The quadratic correction density `S^{2m-2} ((2m/p) F(∇S) + η S)²`, which carries the
`R^{p-2}` error of the truncation for `p < 2`. -/
noncomputable def upperCorr (p : ℝ) (F : Euc d → ℝ) (m : ℕ) (η : ℝ) (S : Euc d → ℝ) (x : Euc d) :
    ℝ := S x ^ (2 * (m : ℝ) - 2) * (2 * (m : ℝ) / p * F (gradient S x) + η * S x) ^ (2 : ℝ)

section Densities

variable {p : ℝ} {F : Euc d → ℝ} {S : Euc d → ℝ} {m : ℕ} {η : ℝ}

theorem upperNum_nonneg (hp : 0 < p) (hF : IsSmoothStrictNorm F) (hSnn : ∀ x, 0 ≤ S x)
    (hη : 0 ≤ η) (x : Euc d) : 0 ≤ upperNum p F m η S x := by
  refine mul_nonneg (Real.rpow_nonneg (hSnn x) _) (Real.rpow_nonneg ?_ _)
  have := hF.nonneg (gradient S x)
  have := hSnn x
  positivity

theorem upperCorr_nonneg (hp : 0 < p) (hF : IsSmoothStrictNorm F) (hSnn : ∀ x, 0 ≤ S x)
    (hη : 0 ≤ η) (x : Euc d) : 0 ≤ upperCorr p F m η S x := by
  refine mul_nonneg (Real.rpow_nonneg (hSnn x) _) (Real.rpow_nonneg ?_ _)
  have := hF.nonneg (gradient S x)
  have := hSnn x
  positivity

/-- Both densities are monotone in the mollification error. -/
theorem upperNum_mono (hp : 0 < p) (hF : IsSmoothStrictNorm F) (hSnn : ∀ x, 0 ≤ S x)
    {η η' : ℝ} (hη : 0 ≤ η) (hηη : η ≤ η') (x : Euc d) :
    upperNum p F m η S x ≤ upperNum p F m η' S x := by
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ ?_ hp.le)
    (Real.rpow_nonneg (hSnn x) _)
  · have := hF.nonneg (gradient S x); have := hSnn x; positivity
  · have hx := hSnn x
    nlinarith [mul_le_mul_of_nonneg_right hηη hx]

theorem upperCorr_mono (hp : 0 < p) (hF : IsSmoothStrictNorm F) (hSnn : ∀ x, 0 ≤ S x)
    {η η' : ℝ} (hη : 0 ≤ η) (hηη : η ≤ η') (x : Euc d) :
    upperCorr p F m η S x ≤ upperCorr p F m η' S x := by
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ ?_ (by norm_num))
    (Real.rpow_nonneg (hSnn x) _)
  · have := hF.nonneg (gradient S x); have := hSnn x; positivity
  · have := hSnn x
    have := mul_le_mul_of_nonneg_right hηη this
    linarith

theorem continuous_upperNum (hp : 0 < p) (hF : IsSmoothStrictNorm F) (hSc : ContDiff ℝ ∞ S)
    (hSnn : ∀ x, 0 ≤ S x) (hpm : p ≤ 2 * (m : ℝ)) (η : ℝ) : Continuous (upperNum p F m η S) := by
  have hrpowc : ∀ a : ℝ, 0 ≤ a → Continuous fun t : ℝ => t ^ a := fun a ha =>
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x a (Or.inr ha)
  have hgS : Continuous (gradient S) := continuous_gradient (hSc.of_le (by simp))
  exact ((hrpowc _ (by linarith)).comp hSc.continuous).mul
    ((hrpowc p hp.le).comp (((hF.continuous.comp hgS).const_mul _).add
      (hSc.continuous.const_mul η)))

theorem continuous_upperCorr (hp : 0 < p) (hF : IsSmoothStrictNorm F) (hSc : ContDiff ℝ ∞ S)
    (hSnn : ∀ x, 0 ≤ S x) (hm1 : 1 ≤ m) (η : ℝ) : Continuous (upperCorr p F m η S) := by
  have hrpowc : ∀ a : ℝ, 0 ≤ a → Continuous fun t : ℝ => t ^ a := fun a ha =>
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x a (Or.inr ha)
  have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hgS : Continuous (gradient S) := continuous_gradient (hSc.of_le (by simp))
  exact ((hrpowc _ (by linarith)).comp hSc.continuous).mul
    ((hrpowc 2 (by norm_num)).comp (((hF.continuous.comp hgS).const_mul _).add
      (hSc.continuous.const_mul η)))

theorem integrable_upperNum (hp : 0 < p) (hF : IsSmoothStrictNorm F) {K : Set (Euc d)}
    (hS : IsTestFn K S) (hSnn : ∀ x, 0 ≤ S x) (hpm : p ≤ 2 * (m : ℝ)) (η : ℝ) :
    Integrable (upperNum p F m η S) := by
  have hSc : ContDiff ℝ ∞ S := hS.contDiff
  refine (continuous_upperNum hp hF hSc hSnn hpm η).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := tsupport S) hS.hasCompactSupport
    fun x hx => ?_
  by_contra hxs
  refine hx ?_
  have hS0 : S x = 0 := by
    have := image_eq_zero_of_notMem_tsupport hxs
    exact this
  have hg : gradient S x = 0 := gradient_eq_zero_of_notMem_tsupport hxs
  show upperNum p F m η S x = 0
  have hAz : 2 * (m : ℝ) / p * F (gradient S x) + η * S x = 0 := by
    rw [hg, hF.map_zero, hS0]; ring
  rw [upperNum, hAz, Real.zero_rpow hp.ne', mul_zero]

theorem integrable_upperCorr (hp : 0 < p) (hF : IsSmoothStrictNorm F) {K : Set (Euc d)}
    (hS : IsTestFn K S) (hSnn : ∀ x, 0 ≤ S x) (hm1 : 1 ≤ m) (η : ℝ) :
    Integrable (upperCorr p F m η S) := by
  have hSc : ContDiff ℝ ∞ S := hS.contDiff
  refine (continuous_upperCorr hp hF hSc hSnn hm1 η).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := tsupport S) hS.hasCompactSupport
    fun x hx => ?_
  by_contra hxs
  refine hx ?_
  have hS0 : S x = 0 := image_eq_zero_of_notMem_tsupport hxs
  have hg : gradient S x = 0 := gradient_eq_zero_of_notMem_tsupport hxs
  show upperCorr p F m η S x = 0
  have hAz : 2 * (m : ℝ) / p * F (gradient S x) + η * S x = 0 := by
    rw [hg, hF.map_zero, hS0]; ring
  rw [upperCorr, hAz, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0), mul_zero]

end Densities

/-! ### The pointwise kinetic bound -/

section Pointwise

variable {p R ε : ℝ} {F ρ : Euc d → ℝ}

/-- **The pointwise upper bound for the kinetic density of `regProfile`.**  It combines the
mollification bound `Ψ_p ≤ h_R(F + Mε)` with a bound `h_R(s) ≤ s^p/p + θ s²` and the
`2`-homogeneity of the kinetic density. -/
theorem homogeneousDensity_regProfile_le (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hR : 0 < R) (hρ : IsMollifier ρ ε) {M : ℝ} (hM : 0 ≤ M)
    (hMle : ∀ q : Euc d, truncSmoothedProfile p F R ρ q ≤ truncPow p R (F q + M * ε))
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hθle : ∀ s : ℝ, 0 ≤ s → truncPow p R s ≤ s ^ p / p + θ * s ^ (2 : ℝ))
    {t : ℝ} (ht : 0 ≤ t) (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 (regProfile p F R ρ) t ξ ≤
      t ^ ((2 : ℝ) - p) * (2 / p * F ξ + M * ε * t) ^ p / p +
        θ * (2 / p * F ξ + M * ε * t) ^ (2 : ℝ) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hε : 0 < ε := hρ.eps_pos
  have hFξ : 0 ≤ F ξ := hF.nonneg ξ
  rcases ht.eq_or_lt with rfl | htpos
  · rw [homogeneousDensity_two_zero]
    have hA : (0 : ℝ) ≤ 2 / p * F ξ + M * ε * 0 := by
      rw [show M * ε * (0 : ℝ) = 0 by ring, add_zero]; positivity
    have h1 : (0 : ℝ) ≤ (0 : ℝ) ^ ((2 : ℝ) - p) * (2 / p * F ξ + M * ε * 0) ^ p / p :=
      div_nonneg (mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg hA _)) hp0.le
    have h2 : (0 : ℝ) ≤ θ * (2 / p * F ξ + M * ε * 0) ^ (2 : ℝ) :=
      mul_nonneg hθ (Real.rpow_nonneg hA _)
    linarith
  · have hq : F ((2 / p) • (t⁻¹ • ξ)) = 2 / p * t⁻¹ * F ξ := by
      rw [smul_smul, hF.homog, abs_of_pos (by positivity)]
    set s : ℝ := 2 / p * t⁻¹ * F ξ + M * ε with hsdef
    have hs0 : 0 ≤ s := by rw [hsdef]; positivity
    have hΨ : regProfile p F R ρ (t⁻¹ • ξ) ≤ truncPow p R s := by
      calc regProfile p F R ρ (t⁻¹ • ξ)
          = truncSmoothedProfile p F R ρ ((2 / p) • (t⁻¹ • ξ)) := rfl
        _ ≤ truncPow p R (F ((2 / p) • (t⁻¹ • ξ)) + M * ε) := hMle _
        _ = truncPow p R s := by rw [hq]
    have hkey : Korevaar.homogeneousDensity 2 (regProfile p F R ρ) t ξ ≤
        t ^ 2 * (s ^ p / p + θ * s ^ (2 : ℝ)) := by
      rw [Korevaar.homogeneousDensity, rpow_two_eq_sq]
      exact mul_le_mul_of_nonneg_left (hΨ.trans (hθle s hs0)) (sq_nonneg t)
    refine hkey.trans (le_of_eq ?_)
    have hts : t * s = 2 / p * F ξ + M * ε * t := by
      rw [hsdef]; field_simp; try ring
    have e1 : t ^ ((2 : ℝ) - p) * (t * s) ^ p = t ^ 2 * s ^ p := by
      rw [Real.mul_rpow htpos.le hs0, ← mul_assoc, ← Real.rpow_add htpos,
        show (2 : ℝ) - p + p = 2 by ring, rpow_two_eq_sq]
    have e2 : (t * s) ^ (2 : ℝ) = t ^ 2 * s ^ (2 : ℝ) := by
      rw [Real.mul_rpow htpos.le hs0, rpow_two_eq_sq]
    rw [← hts, e1, e2]
    ring

/-- **The pointwise kinetic bound for the competitor `T = S^m`.** -/
theorem homogeneousDensity_pow_le (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hR : 0 < R) (hρ : IsMollifier ρ ε) {M : ℝ} (hM : 0 ≤ M)
    (hMle : ∀ q : Euc d, truncSmoothedProfile p F R ρ q ≤ truncPow p R (F q + M * ε))
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hθle : ∀ s : ℝ, 0 ≤ s → truncPow p R s ≤ s ^ p / p + θ * s ^ (2 : ℝ))
    {S : Euc d → ℝ} (hSd : Differentiable ℝ S) (hSnn : ∀ x, 0 ≤ S x) {m : ℕ} (hm1 : 1 ≤ m)
    (hpm : p < 2 * (m : ℝ)) (x : Euc d) :
    Korevaar.homogeneousDensity 2 (regProfile p F R ρ) (S x ^ m)
        (gradient (fun y => S y ^ m) x) ≤
      upperNum p F m (M * ε) S x / p + θ * upperCorr p F m (M * ε) S x := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hSx : 0 ≤ S x := hSnn x
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := hm1
    push_cast [Nat.cast_sub this]
    ring
  have hcoef : 0 ≤ (m : ℝ) * S x ^ (m - 1) := by positivity
  have hFg : F (gradient (fun y => S y ^ m) x) = (m : ℝ) * S x ^ (m - 1) * F (gradient S x) := by
    rw [gradient_natPow hSd m x, hF.homog, abs_of_nonneg hcoef]
  have hsplit : S x ^ m = S x ^ (m - 1) * S x := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  set A : ℝ := 2 * (m : ℝ) / p * F (gradient S x) + M * ε * S x with hA
  have hεnn : 0 ≤ ε := hρ.eps_pos.le
  have hA0 : 0 ≤ A := by
    have := hF.nonneg (gradient S x)
    rw [hA]; positivity
  have hB : 2 / p * F (gradient (fun y => S y ^ m) x) + M * ε * S x ^ m = S x ^ (m - 1) * A := by
    rw [hFg, hA, hsplit]; ring
  have h := homogeneousDensity_regProfile_le hp hF hR hρ hM hMle hθ hθle
    (t := S x ^ m) (pow_nonneg hSx m) (gradient (fun y => S y ^ m) x)
  refine h.trans (le_of_eq ?_)
  rw [hB]
  -- the numerator
  have hne : (m : ℝ) * ((2 : ℝ) - p) + ((m : ℝ) - 1) * p ≠ 0 := by
    have he : (m : ℝ) * ((2 : ℝ) - p) + ((m : ℝ) - 1) * p = 2 * (m : ℝ) - p := by ring
    rw [he]
    intro hc
    linarith
  have hexp : (m : ℝ) * ((2 : ℝ) - p) + ((m : ℝ) - 1) * p = 2 * (m : ℝ) - p := by ring
  have hexp2 : ((m : ℝ) - 1) * 2 = 2 * (m : ℝ) - 2 := by ring
  have hnum : (S x ^ m) ^ ((2 : ℝ) - p) * (S x ^ (m - 1) * A) ^ p =
      upperNum p F m (M * ε) S x := by
    rw [Real.mul_rpow (pow_nonneg hSx _) hA0, natPow_rpow hSx m ((2 : ℝ) - p),
      natPow_rpow hSx (m - 1) p, hmcast, ← mul_assoc, ← Real.rpow_add' hSx hne, hexp, upperNum]
  -- the correction
  have hcorr : (S x ^ (m - 1) * A) ^ (2 : ℝ) = upperCorr p F m (M * ε) S x := by
    rw [Real.mul_rpow (pow_nonneg hSx _) hA0, natPow_rpow hSx (m - 1) 2, hmcast, hexp2, upperCorr]
  rw [hnum, hcorr]

end Pointwise

/-! ### The competitor `T = S^m` -/

/-- A positive power of a test function is a test function. -/
theorem isTestFn_pow {K : Set (Euc d)} {S : Euc d → ℝ} (hS : IsTestFn K S) {m : ℕ}
    (hm0 : m ≠ 0) : IsTestFn K (fun y => S y ^ m) := by
  have hsupp : Function.support (fun y => S y ^ m) = Function.support S := by
    ext x
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff hm0]
  have htsupp : tsupport (fun y => S y ^ m) = tsupport S := by unfold tsupport; rw [hsupp]
  exact
    { contDiff := hS.contDiff.pow m
      hasCompactSupport := by
        show IsCompact (tsupport fun y => S y ^ m)
        rw [htsupp]; exact hS.hasCompactSupport
      supp_subset := by rw [htsupp]; exact hS.supp_subset
      ne_zero := by
        intro hcon
        refine hS.ne_zero (funext fun x => ?_)
        have hx : x ∉ Function.support fun y => S y ^ m := by simp [hcon]
        rw [hsupp] at hx
        simpa using hx }

theorem tsupport_pow {S : Euc d → ℝ} {m : ℕ} (hm0 : m ≠ 0) :
    tsupport (fun y => S y ^ m) = tsupport S := by
  have hsupp : Function.support (fun y => S y ^ m) = Function.support S := by
    ext x
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff hm0]
  unfold tsupport; rw [hsupp]

/-- `∫ S^{2m} = ∫ (S^m)²` is positive for a test function `S` and `m ≥ 1`. -/
theorem integral_pow_pos {K : Set (Euc d)} {S : Euc d → ℝ} (hS : IsTestFn K S) {m : ℕ}
    (hm0 : m ≠ 0) : 0 < ∫ x, S x ^ (2 * m) := by
  have hD : (∫ y, (S y ^ m) ^ 2) = ∫ x, S x ^ (2 * m) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (S x ^ m) ^ 2 = S x ^ (2 * m)
    rw [← pow_mul, mul_comm]
  rw [← hD]
  exact integral_sq_testFn_pos (isTestFn_pow hS hm0)

/-! ### The energy of the normalized `S^m` competitor -/

/-- **The regularized energy of the `L²`-normalized competitor `S^m`.**  The entropy constant
`E` depends only on `S` and `m`; the kinetic part is the quotient of the two densities of
`upperNum`/`upperCorr` by `∫ S^{2m}`. -/
theorem exists_regMin_le_of_powCompetitor {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K)
    {S : Euc d → ℝ} (hS : IsTestFn K S) (hSnn : ∀ x, 0 ≤ S x) {m : ℕ} (hm1 : 1 ≤ m)
    (hpm : p < 2 * (m : ℝ)) {M : ℝ} (hM : 0 ≤ M) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (R ε κ θ : ℝ) (ρ : Euc d → ℝ), 0 < R → IsMollifier ρ ε → 0 < κ →
      0 ≤ θ → (∀ s : ℝ, 0 ≤ s → truncPow p R s ≤ s ^ p / p + θ * s ^ (2 : ℝ)) →
      (∀ q : Euc d, truncSmoothedProfile p F R ρ q ≤ truncPow p R (F q + M * ε)) →
      regMin 2 κ (regProfile p F R ρ) K ≤
        ((∫ x, upperNum p F m (M * ε) S x) / p + θ * ∫ x, upperCorr p F m (M * ε) S x) /
          (∫ x, S x ^ (2 * m)) + κ * E := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hm0 : m ≠ 0 := by omega
  have hSd : Differentiable ℝ S := hS.contDiff.differentiable (by simp)
  -- the competitor `T = S^m`
  have hTnn : ∀ x, 0 ≤ S x ^ m := fun x => pow_nonneg (hSnn x) m
  have htsupp : tsupport (fun y => S y ^ m) = tsupport S := tsupport_pow hm0
  have hTtest : IsTestFn K (fun y => S y ^ m) := isTestFn_pow hS hm0
  have hTc1 : ContDiff ℝ 1 (fun y => S y ^ m) := hTtest.contDiff.of_le (by simp)
  have hTcs : HasCompactSupport (fun y => S y ^ m) := hTtest.hasCompactSupport
  obtain ⟨c, hcpos, hcsq, hWadm⟩ := exists_isRegAdmissible_smul_testFn hTtest hTnn
  have hD : (∫ y, (S y ^ m) ^ 2) = ∫ x, S x ^ (2 * m) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (S x ^ m) ^ 2 = S x ^ (2 * m)
    rw [← pow_mul, mul_comm]
  have hDpos : 0 < ∫ x, S x ^ (2 * m) := by
    rw [← hD]; exact integral_sq_testFn_pos hTtest
  have hc2 : c ^ 2 = (∫ x, S x ^ (2 * m))⁻¹ := by
    rw [hD] at hcsq
    field_simp at hcsq ⊢
    linarith [hcsq]
  -- smoothness of the normalized competitor
  have hWc1 : ContDiff ℝ 1 (c • fun y => S y ^ m) := hTc1.const_smul c
  have hWcs : HasCompactSupport (c • fun y => S y ^ m) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := tsupport S) hS.hasCompactSupport ?_
    intro x hx
    rw [← htsupp]
    refine subset_tsupport _ ?_
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul, ne_eq] at hx ⊢
    intro h0
    exact hx (by rw [h0, mul_zero])
  have hgrad : ∀ x, gradient (c • fun y => S y ^ m) x = c • gradient (fun y => S y ^ m) x := by
    intro x
    have hTd : HasGradientAt (fun y => S y ^ m) (gradient (fun y => S y ^ m) x) x :=
      ((hTtest.contDiff.differentiable (by simp)) x).hasGradientAt
    exact (hasGradientAt_const_mul hTd c).gradient
  refine ⟨|(1 / 2) * ∫ x, (c * S x ^ m) ^ 2 * Real.log (c * S x ^ m)|, abs_nonneg _, ?_⟩
  intro R ε κ θ ρ hR hρ hκ hθ hθle hMle
  have hΨ : IsRegProfile (regProfile p F R ρ) := isRegProfile_regProfile hp hR hF hρ
  obtain ⟨c₀, C₀, hΨW⟩ := hΨ.exists_isRegProfileWith
  refine le_trans (regMin_le_of_isRegAdmissible hκ hΨ hK hWadm) ?_
  rw [regEnergy]
  -- the entropy term
  have hent : (∫ x, Korevaar.entropyPotential 2 κ ((c • fun y => S y ^ m) x)) ≤
      κ * |(1 / 2) * ∫ x, (c * S x ^ m) ^ 2 * Real.log (c * S x ^ m)| := by
    have hentfun : (fun x => Korevaar.entropyPotential 2 κ ((c • fun y => S y ^ m) x)) =
        fun x => κ * ((1 / 2) * ((c * S x ^ m) ^ 2 * Real.log (c * S x ^ m))) := by
      funext x
      simp only [Korevaar.entropyPotential, Pi.smul_apply, smul_eq_mul, rpow_two_eq_sq]
      ring
    rw [hentfun, integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hκ.le
  -- the kinetic term
  have hkineq : (∫ x, Korevaar.homogeneousDensity 2 (regProfile p F R ρ)
        ((c • fun y => S y ^ m) x) (weakGrad (c • fun y => S y ^ m) x)) =
      c ^ 2 * ∫ x, Korevaar.homogeneousDensity 2 (regProfile p F R ρ) (S x ^ m)
        (gradient (fun y => S y ^ m) x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [weakGrad_ae_eq_gradient hWc1 hWcs] with x hx
    rw [hx, hgrad x]
    exact scalarLimit_homogeneousDensity_two_smul _ hcpos (S x ^ m) (gradient (fun y => S y ^ m) x)
  have hintN : Integrable (upperNum p F m (M * ε) S) :=
    integrable_upperNum hp0 hF hS hSnn hpm.le (M * ε)
  have hintC : Integrable (upperCorr p F m (M * ε) S) :=
    integrable_upperCorr hp0 hF hS hSnn hm1 (M * ε)
  have hint1 : Integrable fun x => Korevaar.homogeneousDensity 2 (regProfile p F R ρ)
      (S x ^ m) (gradient (fun y => S y ^ m) x) := by
    refine (integrable_kinetic hΨW (hTtest.memW0 2) hTnn).congr ?_
    filter_upwards [weakGrad_ae_eq_gradient hTc1 hTcs] with x hx
    rw [hx]
  have hint2 : Integrable fun x =>
      upperNum p F m (M * ε) S x / p + θ * upperCorr p F m (M * ε) S x :=
    (hintN.div_const p).add (hintC.const_mul θ)
  have hkinbound : (∫ x, Korevaar.homogeneousDensity 2 (regProfile p F R ρ) (S x ^ m)
      (gradient (fun y => S y ^ m) x)) ≤
      (∫ x, upperNum p F m (M * ε) S x) / p + θ * ∫ x, upperCorr p F m (M * ε) S x := by
    have hmono := integral_mono hint1 hint2 fun x =>
      homogeneousDensity_pow_le hp hF hR hρ hM hMle hθ hθle hSd hSnn hm1 hpm x
    rwa [integral_add (hintN.div_const p) (hintC.const_mul θ), integral_div,
      integral_const_mul] at hmono
  have hkin : (∫ x, Korevaar.homogeneousDensity 2 (regProfile p F R ρ)
        ((c • fun y => S y ^ m) x) (weakGrad (c • fun y => S y ^ m) x)) ≤
      ((∫ x, upperNum p F m (M * ε) S x) / p + θ * ∫ x, upperCorr p F m (M * ε) S x) /
        (∫ x, S x ^ (2 * m)) := by
    rw [hkineq, hc2, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hkinbound (by positivity)
  linarith [hkin, hent]

/-! ### The upper scalar limit -/

/-- **The upper scalar limit** (`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*): along any
family of regularization parameters with `R → ∞`, `ε → 0` and `κ → 0`,

`regMin 2 κ_n Ψ_n K ≤ λ_{p,F}(K)/p + δ`  eventually.

The competitor is fixed once and for all (`exists_upperCompetitor`); the three error terms are
the mollification error `M ε_n` inside `upperNum` (dominated convergence), the truncation error
`θ_n ∫ upperCorr` (with `θ_n = (p-1) R_n^{p-2}/2` for `p < 2` and `θ_n = 0` for `p ≥ 2`), and
the entropy error `κ_n E`. -/
theorem eventually_regMin_le_of_params {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ)
    {Rs εs κs : ℕ → ℝ} {ρs : ℕ → Euc d → ℝ}
    (hRpos : ∀ n, 0 < Rs n) (hRlim : Tendsto Rs atTop atTop)
    (hρ : ∀ n, IsMollifier (ρs n) (εs n)) (hεlim : Tendsto εs atTop (𝓝 0))
    (hκpos : ∀ n, 0 < κs n) (hκlim : Tendsto κs atTop (𝓝 0)) :
    ∀ᶠ n in atTop, regMin 2 (κs n) (regProfile p F (Rs n) (ρs n)) K ≤
      lambdaGen p F K / p + δ := by
  have hp0 : (0 : ℝ) < p := by linarith
  -- the competitor
  obtain ⟨S, m, hS, hSnn, hm1, hpm, hcomp⟩ :=
    exists_upperCompetitor hp hF hK (δ := p * δ / 2) (by positivity)
  have hm0 : m ≠ 0 := by omega
  obtain ⟨M, hM0, hMle⟩ := exists_truncSmoothedProfile_le hp hF
  obtain ⟨E, hE0, hEbd⟩ := exists_regMin_le_of_powCompetitor hp hF hK hS hSnn hm1 hpm hM0
  set L : ℝ := lambdaGen p F K with hLdef
  set D : ℝ := ∫ x, S x ^ (2 * m) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact integral_pow_pos hS hm0
  -- the truncation error
  obtain ⟨θs, hθ0, hθle, hθlim⟩ : ∃ θs : ℕ → ℝ, (∀ n, 0 ≤ θs n) ∧
      (∀ n, ∀ s : ℝ, 0 ≤ s → truncPow p (Rs n) s ≤ s ^ p / p + θs n * s ^ (2 : ℝ)) ∧
      Tendsto θs atTop (𝓝 0) := by
    rcases lt_or_ge p 2 with h2 | h2
    · refine ⟨fun n => (p - 1) * Rs n ^ (p - 2) / 2, fun n => ?_, fun n s hs => ?_, ?_⟩
      · have := Real.rpow_pos_of_pos (hRpos n) (p - 2)
        positivity
      · rw [rpow_two_eq_sq]
        exact truncPow_le_rpow_div_add_sq hp (hRpos n) hs
      · have h0 := (tendsto_rpow_neg_atTop (y := 2 - p) (by linarith)).comp hRlim
        have h : Tendsto (fun n => Rs n ^ (p - 2)) atTop (𝓝 0) := by
          simpa [Function.comp_def, show -(2 - p) = p - 2 by ring] using h0
        simpa using (h.const_mul (p - 1)).div_const 2
    · refine ⟨fun _ => 0, fun _ => le_rfl, fun n s hs => ?_, tendsto_const_nhds⟩
      rw [zero_mul, add_zero]
      exact truncPow_le_rpow_div hp h2 (hRpos n) hs
  -- the competitor bound at each `n`
  have hbound : ∀ n, regMin 2 (κs n) (regProfile p F (Rs n) (ρs n)) K ≤
      ((∫ x, upperNum p F m (M * εs n) S x) / p +
        θs n * ∫ x, upperCorr p F m (M * εs n) S x) / D + κs n * E := fun n =>
    hEbd (Rs n) (εs n) (κs n) (θs n) (ρs n) (hRpos n) (hρ n) (hκpos n) (hθ0 n) (hθle n)
      (hMle (Rs n) (hRpos n).le (ρs n) (εs n) (hρ n))
  -- the three errors vanish
  have hε1 : ∀ᶠ n in atTop, εs n ≤ 1 :=
    (hεlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono fun n hn => hn.le
  have hεnn : ∀ n, 0 ≤ εs n := fun n => (hρ n).eps_pos.le
  have hNlim : Tendsto (fun n => ∫ x, upperNum p F m (M * εs n) S x) atTop
      (𝓝 (∫ x, upperNum p F m 0 S x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (upperNum p F m M S)
      (Eventually.of_forall fun n =>
        (continuous_upperNum hp0 hF hS.contDiff hSnn hpm.le _).aestronglyMeasurable) ?_
      (integrable_upperNum hp0 hF hS hSnn hpm.le M) ?_
    · filter_upwards [hε1] with n hn
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs,
        abs_of_nonneg (upperNum_nonneg hp0 hF hSnn (mul_nonneg hM0 (hεnn n)) x)]
      refine upperNum_mono hp0 hF hSnn (mul_nonneg hM0 (hεnn n)) ?_ x
      nlinarith [hM0, hεnn n]
    · refine Eventually.of_forall fun x => ?_
      have hc : Continuous fun η : ℝ =>
          S x ^ (2 * (m : ℝ) - p) *
            (2 * (m : ℝ) / p * F (gradient S x) + η * S x) ^ p := by
        refine continuous_const.mul ?_
        refine (continuous_iff_continuousAt.2 fun y =>
          Real.continuousAt_rpow_const y p (Or.inr hp0.le)).comp ?_
        exact continuous_const.add (continuous_id.mul continuous_const)
      have h2 : Tendsto (fun n => M * εs n) atTop (𝓝 0) := by simpa using hεlim.const_mul M
      exact (hc.tendsto 0).comp h2
  have hCnn : ∀ n, 0 ≤ ∫ x, upperCorr p F m (M * εs n) S x := fun n =>
    integral_nonneg fun x => upperCorr_nonneg hp0 hF hSnn (mul_nonneg hM0 (hεnn n)) x
  have hθC : Tendsto (fun n => θs n * ∫ x, upperCorr p F m (M * εs n) S x) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n => θs n * ∫ x, upperCorr p F m M S x)
      (Eventually.of_forall fun n => mul_nonneg (hθ0 n) (hCnn n)) ?_ ?_
    · filter_upwards [hε1] with n hn
      refine mul_le_mul_of_nonneg_left ?_ (hθ0 n)
      refine integral_mono (integrable_upperCorr hp0 hF hS hSnn hm1 _)
        (integrable_upperCorr hp0 hF hS hSnn hm1 _) fun x => ?_
      refine upperCorr_mono hp0 hF hSnn (mul_nonneg hM0 (hεnn n)) ?_ x
      nlinarith [hM0, hεnn n]
    · simpa using hθlim.mul_const (∫ x, upperCorr p F m M S x)
  have hglim : Tendsto (fun n =>
      ((∫ x, upperNum p F m (M * εs n) S x) / p +
        θs n * ∫ x, upperCorr p F m (M * εs n) S x) / D + κs n * E) atTop
      (𝓝 ((∫ x, upperNum p F m 0 S x) / p / D)) := by
    have h1 : Tendsto (fun n => (∫ x, upperNum p F m (M * εs n) S x) / p +
        θs n * ∫ x, upperCorr p F m (M * εs n) S x) atTop
        (𝓝 ((∫ x, upperNum p F m 0 S x) / p)) := by
      simpa using (hNlim.div_const p).add hθC
    have hκE : Tendsto (fun n => κs n * E) atTop (𝓝 0) := by simpa using hκlim.mul_const E
    have h3 := (h1.div_const D).add hκE
    rwa [add_zero] at h3
  -- the limit is below `λ/p + δ`
  have hN0eq : (∫ x, upperNum p F m 0 S x) =
      (2 * (m : ℝ) / p) ^ p * ∫ x, S x ^ (2 * (m : ℝ) - p) * F (gradient S x) ^ p := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show S x ^ (2 * (m : ℝ) - p) * (2 * (m : ℝ) / p * F (gradient S x) + 0 * S x) ^ p =
      (2 * (m : ℝ) / p) ^ p * (S x ^ (2 * (m : ℝ) - p) * F (gradient S x) ^ p)
    rw [zero_mul, add_zero, Real.mul_rpow (by positivity) (hF.nonneg _)]
    ring
  have hle : (∫ x, upperNum p F m 0 S x) / p / D ≤ L / p + δ / 2 := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have hkey : (∫ x, upperNum p F m 0 S x) ≤ (L + p * δ / 2) * D := by rw [hN0eq]; exact hcomp
    have heq : (L / p + δ / 2) * (p * D) = (L + p * δ / 2) * D := by field_simp; try ring
    rw [heq]
    exact hkey
  have hlt : (∫ x, upperNum p F m 0 S x) / p / D < L / p + δ := by linarith
  filter_upwards [hglim.eventually (eventually_lt_nhds hlt)] with n hn
  exact le_trans (hbound n) hn.le

end Komlos.Literature.Regularized
