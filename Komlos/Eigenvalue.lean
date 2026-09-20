import Komlos.Cheeger
import Komlos.EigenvalueAux
import Komlos.Variation

/-!
# The anisotropic `p`-eigenvalue: definitions and bridges

This file defines the anisotropic `p`-eigenvalue `λ_{p,H}(K)` over smooth test functions and
proves the elementary bridges to the Cheeger value `h_H`. The `p ↓ 1` limit and Minkowski
convexity of `h_H` are in `Komlos/EigenvalueLimit.lean`; the external eigenvalue-convexity input
(Wang–Xia 2011) is in `Komlos/EigenvalueConvex.lean`.

For the mixture integrand `H(ξ) = ∑ α_ℓ |u_ℓ·ξ|`, `H(∇f)(x) = ∑_ℓ α_ℓ |∂_{u_ℓ}f(x)|` is
`mixtureGrad α u f x`, a directional-derivative expression needing no gradient vector.

Contents: `mixtureGrad`, `IsTestFn`, `rayleighMix`, `lambdaMix`, `cheegerSmooth`;
`dirVar_eq_lintegral_fderiv`, `mixtureEnergy_eq_ofReal_integral_mixtureGrad`,
`cheegerSmooth_eq_cheeger` (paper Lemma 3.2 "smooth densities suffice"), `lambdaMix_nonneg`,
`isGoodConvex_convexCombo`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-- The mixture integrand evaluated at the derivative of a differentiable `f`:
`H(∇f)(x) = ∑_ℓ α_ℓ |∂_{u_ℓ} f(x)| = ∑_ℓ α_ℓ |Df(x)·u_ℓ|` (paper (3.6)). -/
noncomputable def mixtureGrad {N : ℕ} (α : Fin N → ℝ) (u : Fin N → Euc d) (f : Euc d → ℝ)
    (x : Euc d) : ℝ :=
  ∑ l, α l * |fderiv ℝ f x (u l)|

/-- Smooth test functions for `K`: `C^∞`, compactly supported inside the open set `K`, and not
identically zero (so the Rayleigh denominator is positive). -/
structure IsTestFn (K : Set (Euc d)) (f : Euc d → ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) f
  hasCompactSupport : HasCompactSupport f
  supp_subset : tsupport f ⊆ K
  ne_zero : f ≠ 0

/-- The mixture Rayleigh quotient at exponent `p` (paper (A.1) integrand):
`(∫ H(∇f)^p) / (∫ |f|^p)`. -/
noncomputable def rayleighMix {N : ℕ} (p : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d)
    (f : Euc d → ℝ) : ℝ :=
  (∫ x, mixtureGrad α u f x ^ p) / (∫ x, |f x| ^ p)

/-- The anisotropic `p`-eigenvalue `λ_{p,H}(K)` (paper (A.1)), realized over smooth test
functions.

The index set is the *subtype* of test functions rather than a Prop-bounded `⨅`: in `ℝ` the
empty infimum is `0` (`Real.iInf_of_isEmpty`), so `⨅ f (_ : IsTestFn K f), …` would take the
value `0` at every non-test `f` (e.g. `f = 0`) and be identically zero. With the subtype index
this is `sInf {rayleighMix p α u f | IsTestFn K f}`, the paper's infimum (the set is bounded
below by `0`, and nonempty whenever `K` has nonempty interior). -/
noncomputable def lambdaMix {N : ℕ} (p : ℝ) (α : Fin N → ℝ) (u : Fin N → Euc d)
    (K : Set (Euc d)) : ℝ :=
  ⨅ f : {f : Euc d → ℝ // IsTestFn K f}, rayleighMix p α u f.1

/-- The Cheeger value restricted to smooth compactly supported probability densities. Paper:
"smooth compactly supported probability densities suffice for the infimum in (3.2)". -/
noncomputable def cheegerSmooth {N : ℕ} (α : Fin N → ℝ) (u : Fin N → Euc d) (K : Set (Euc d)) :
    ℝ≥0∞ :=
  ⨅ (f : Euc d → ℝ) (_ : IsTestFn K f) (_ : 0 ≤ f) (_ : ∫ x, f x = 1), mixtureEnergy α u f

section Bridges

variable {N : ℕ} {α : Fin N → ℝ} {u : Fin N → Euc d}

/-- For a `C¹` compactly supported `f` and every direction, the directional variation equals the
integral of the modulus of the directional derivative (paper, after (2.1); the `W^{1,1}` case).
Strengthens `dirVar_le_lintegral_fderiv` to an equality. -/
theorem dirVar_eq_lintegral_fderiv (w : Euc d) (f : Euc d → ℝ) (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) :
    dirVar w f = ∫⁻ x, ‖fderiv ℝ f x w‖ₑ :=
  le_antisymm (dirVar_le_lintegral_fderiv w f hf hsupp) (lintegral_fderiv_le_dirVar w f hf)

/-- A smooth test function is `C¹`. -/
theorem IsTestFn.contDiff_one {K : Set (Euc d)} {f : Euc d → ℝ} (hf : IsTestFn K f) :
    ContDiff ℝ 1 f :=
  hf.contDiff.of_le (by exact_mod_cast le_top)

/-- A nonnegative smooth test function of mass one lies in `𝒫(K)`. -/
theorem IsTestFn.memP {K : Set (Euc d)} {f : Euc d → ℝ} (hf : IsTestFn K f) (h0 : 0 ≤ f)
    (h1 : ∫ x, f x = 1) : MemP K f where
  measurable := hf.contDiff.continuous.measurable
  nonneg := h0
  integrable := hf.contDiff.continuous.integrable_of_hasCompactSupport hf.hasCompactSupport
  integral_eq_one := h1
  ae_zero_outside := Eventually.of_forall fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hf.supp_subset h)
  dirVar_ne_top := fun w => ne_top_of_le_ne_top
    (lintegral_enorm_fderiv_ne_top hf.contDiff_one hf.hasCompactSupport w)
    (dirVar_le_lintegral_fderiv w f hf.contDiff_one hf.hasCompactSupport)

/-- For a smooth test density, the mixture energy is the integral of `mixtureGrad`
(paper: `E_H(ρ) = ∑ α_ℓ V_{u_ℓ}(ρ)` and `V_{u_ℓ}(f) = ∫ |∂_{u_ℓ}f|` for smooth `f`). -/
theorem mixtureEnergy_eq_ofReal_integral_mixtureGrad (hmix : IsMixture α u) {K : Set (Euc d)}
    {f : Euc d → ℝ} (hf : IsTestFn K f) :
    mixtureEnergy α u f = ENNReal.ofReal (∫ x, mixtureGrad α u f x) := by
  have hf1 : ContDiff ℝ 1 f := hf.contDiff_one
  have hint : ∀ l, Integrable fun x => |fderiv ℝ f x (u l)| := fun l =>
    (integrable_fderiv_apply hf1 hf.hasCompactSupport (u l)).abs
  unfold mixtureEnergy mixtureGrad
  rw [integral_finset_sum _ fun l _ => (hint l).const_mul (α l)]
  simp_rw [integral_const_mul]
  rw [ENNReal.ofReal_sum_of_nonneg fun l _ =>
    mul_nonneg (hmix.nonneg l) (integral_nonneg fun x => abs_nonneg _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [dirVar_eq_lintegral_fderiv (u l) f hf1 hf.hasCompactSupport,
    ENNReal.ofReal_mul (hmix.nonneg l),
    ← ofReal_integral_norm_eq_lintegral_enorm
      (integrable_fderiv_apply hf1 hf.hasCompactSupport (u l))]
  simp only [Real.norm_eq_abs]

/-- **Smooth densities suffice** (paper Lemma 3.2, first paragraph): the smooth-density Cheeger
value equals the Cheeger value. The `≤` direction is the mollification/contraction argument;
`≥` holds because smooth test densities lie in `𝒫(K)`. -/
theorem cheeger_le_cheegerSmooth {K : Set (Euc d)} : cheeger α u K ≤ cheegerSmooth α u K :=
  le_iInf fun _ => le_iInf fun hf => le_iInf fun h0 => le_iInf fun h1 =>
    cheeger_le_mixtureEnergy (hf.memP h0 h1)

/-- Every `ρ ∈ 𝒫(K)` is matched in energy by smooth test densities: the contract-and-mollify
construction `exists_smooth_approx` gives `h^∞_H(K) ≤ r⁻¹ E_H(ρ)` for every `0 < r < 1`, and
`r ↑ 1` concludes (paper Lemma 3.2, first paragraph). -/
theorem cheegerSmooth_le_mixtureEnergy {K : Set (Euc d)} (hK : IsGoodConvex K) {ρ : Euc d → ℝ}
    (hρ : MemP K ρ) : cheegerSmooth α u K ≤ mixtureEnergy α u ρ := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  obtain ⟨r, hr0, hr1, rfl⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ a = ENNReal.ofReal r := by
    have hat : a ≠ ⊤ := ha.ne_top
    refine ⟨a.toReal, ENNReal.toReal_pos ha0 hat, ?_, (ENNReal.ofReal_toReal hat).symm⟩
    simpa using (ENNReal.toReal_lt_toReal hat ENNReal.one_ne_top).2 ha
  obtain ⟨f, hf, hfs, hfK, hf0, hf1, hfE⟩ := exists_smooth_approx α u hK hρ hr0 hr1
  have hfne : f ≠ 0 := by
    rintro rfl
    simp at hf1
  have hle : cheegerSmooth α u K ≤ mixtureEnergy α u f :=
    iInf_le_of_le f (iInf_le_of_le ⟨hf, hfs, hfK, hfne⟩
      (iInf_le_of_le hf0 (iInf_le_of_le hf1 le_rfl)))
  calc ENNReal.ofReal r * cheegerSmooth α u K
      ≤ ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * mixtureEnergy α u ρ) := by
        gcongr; exact hle.trans hfE
    _ = mixtureEnergy α u ρ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hr0.le, mul_inv_cancel₀ hr0.ne',
          ENNReal.ofReal_one, one_mul]

theorem cheegerSmooth_eq_cheeger (hmix : IsMixture α u) {K : Set (Euc d)} (hK : IsGoodConvex K) :
    cheegerSmooth α u K = cheeger α u K :=
  le_antisymm (le_iInf₂ fun _ hρ => cheegerSmooth_le_mixtureEnergy hK hρ) cheeger_le_cheegerSmooth

/-- `lambdaMix` is nonnegative (the Rayleigh quotient is a ratio of nonnegative integrals). -/
theorem mixtureGrad_nonneg (hmix : IsMixture α u) (f : Euc d → ℝ) (x : Euc d) :
    0 ≤ mixtureGrad α u f x :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hmix.nonneg l) (abs_nonneg _)

/-- The Rayleigh quotient is nonnegative. -/
theorem rayleighMix_nonneg (hmix : IsMixture α u) (p : ℝ) (f : Euc d → ℝ) :
    0 ≤ rayleighMix p α u f :=
  div_nonneg (integral_nonneg fun x => Real.rpow_nonneg (mixtureGrad_nonneg hmix f x) p)
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) p)

theorem lambdaMix_nonneg (hmix : IsMixture α u) {p : ℝ} (hp : 1 ≤ p) (K : Set (Euc d)) :
    0 ≤ lambdaMix p α u K :=
  Real.iInf_nonneg fun f => rayleighMix_nonneg hmix p f.1

end Bridges

/-- A convex combination of nonempty bounded open convex sets is nonempty bounded open convex. -/
theorem isGoodConvex_convexCombo {K₀ K₁ : Set (Euc d)} (hK₀ : IsGoodConvex K₀)
    (hK₁ : IsGoodConvex K₁) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    IsGoodConvex ((1 - t) • K₀ + t • K₁) where
  nonempty := hK₀.nonempty.smul_set.add hK₁.nonempty.smul_set
  isBounded := (hK₀.isBounded.smul₀ _).add (hK₁.isBounded.smul₀ _)
  isOpen := (hK₁.isOpen.smul₀ ht₀.ne').add_left
  convex := (hK₀.convex.smul _).add (hK₁.convex.smul _)

end Komlos
