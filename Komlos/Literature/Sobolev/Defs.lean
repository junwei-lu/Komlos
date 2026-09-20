import Komlos.Eigenvalue
import Komlos.Literature.PLaplacian.Rayleigh
import Komlos.Literature.Sobolev.Mollify

/-!
# Sobolev substrate: weak gradients, `W₀^{1,p}(K)`, and the Dirichlet Poincaré inequality

This file begins the `W^{1,p}` layer of Phase B (`BLUEPRINT_LITERATURE.md`, `Literature/Sobolev`),
needed for the direct-method existence of first eigenfunctions of the anisotropic `p`-Laplacian
(paper Appendix A, "The direct method gives a nonnegative, nonzero first eigenfunction
`u_i ∈ W_0^{1,p}(K_i)`"), i.e. for `Komlos.Literature.exists_eigenfunctionData`.

Design: everything is concrete, on functions `Euc d → ℝ` with Lebesgue measure; no quotient or
abstract completion is built.

* `HasWeakGradient f g`: `f` and `g` are locally integrable and `g` is the distributional
  gradient of `f`, in the integration-by-parts form
  `∫ f ∂_v ψ = -∫ ⟪g, v⟫ ψ` for all `ψ ∈ C_c^∞(ℝ^d)` and all directions `v`.
  Weak gradients are unique a.e. (`HasWeakGradient.ae_eq`, from Mathlib's fundamental lemma of
  the calculus of variations `ae_eq_of_integral_contDiff_smul_eq`), and a `C¹` compactly
  supported function has weak gradient equal to its classical `gradient`
  (`hasWeakGradient_gradient`, by `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).
* `MemW0 p K f`: `f ∈ L^p`, `f = 0` a.e. outside `K`, and `f` has a weak gradient in `L^p`.
  For the bounded open convex sets of interest this is `W_0^{1,p}(K)`
  (paper (3.7): `λ_{p,H}(K) = inf_{0 ≠ f ∈ W_0^{1,p}(K)} …`). `weakGrad f` is a chosen weak
  gradient; `gradLpNorm p f = ‖weakGrad f‖_{L^p}`.
* `sobolevRayleigh p F f` is the Rayleigh quotient `(∫ F(∇f)^p) / (∫ |f|^p)` over the weak
  gradient; it agrees with `rayleighGen` on test functions, and the Sobolev eigenvalue
  `lambdaSob p F K` (infimum over `W_0^{1,p}(K) ∖ {0}`) is at most the smooth one `lambdaGen`.
* Poincaré (paper Lemma 3.2, "the Dirichlet Poincaré inequality"): for `f` supported in
  `closedBall 0 R` and `T > 2R`, `‖f‖_{L^p} ≤ T ‖∇f‖_{L^p}`, first for `C¹` compactly supported
  `f` (`eLpNorm_le_eLpNorm_gradient`, by the fundamental theorem of calculus along a coordinate
  line, Hölder, Tonelli and translation invariance), then for `MemW0` by mollification
  (`MemW0.eLpNorm_le_eLpNorm_weakGrad`).
* Positivity of the eigenvalue (paper Lemma 3.2, "Norm equivalence and the Dirichlet Poincaré
  inequality make this quantity positive"): `rpow_le_lambdaSob`, `lambdaSob_pos`, `lambdaGen_pos`.
* Weak gradients pass to `L^p` limits (`HasWeakGradient.of_tendsto`), hence `W₀^{1,p}(K)` is
  complete under the graph norm (`W0_complete`, via completeness of `MeasureTheory.Lp`).
* The eigenvalue-level density of `C_c^∞(K)` in `W₀^{1,p}(K)` (`lambdaGen_le_lambdaSob`) is
  proved in `Komlos.Literature.Sobolev.Density`, and Rellich–Kondrachov (`rellich`) in
  `Komlos.Literature.Sobolev.Rellich`; the `L^p` facts about mollification (Young,
  approximation of the identity, Nemytskii continuity) are in `Komlos.Literature.Sobolev.Mollify`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal Pointwise ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Weak gradients -/

/-- `g : ℝ^d → ℝ^d` is a weak (distributional) gradient of `f : ℝ^d → ℝ`: both are locally
integrable and `∫ f ∂_v ψ = -∫ ⟪g, v⟫ ψ` for every `ψ ∈ C_c^∞(ℝ^d)` and every direction `v`
(the integration-by-parts characterization of `W^{1,1}_{loc}`). -/
structure HasWeakGradient (f : Euc d → ℝ) (g : Euc d → Euc d) : Prop where
  /-- `f` is locally integrable. -/
  locallyIntegrable : LocallyIntegrable f
  /-- `g` is locally integrable. -/
  locallyIntegrable_grad : LocallyIntegrable g
  /-- The integration-by-parts identity against smooth compactly supported test functions. -/
  integral_mul_fderiv : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ v : Euc d,
    ∫ x, f x * fderiv ℝ ψ x v = -∫ x, inner ℝ (g x) v * ψ x

namespace HasWeakGradient

variable {f f' : Euc d → ℝ} {g g' : Euc d → Euc d}

/-- The integration-by-parts identity in the form `∫ ψ • g = ∫ ψ • ∇f`-free: the vector-valued
integral `∫ ψ x • g x` is determined by `f` alone. -/
theorem integral_smul_eq (hg : HasWeakGradient f g) (hg' : HasWeakGradient f g')
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) :
    ∫ x, ψ x • g x = ∫ x, ψ x • g' x := by
  have hint : Integrable fun x => ψ x • g x :=
    hg.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport hψ.continuous hψs
  have hint' : Integrable fun x => ψ x • g' x :=
    hg'.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport hψ.continuous hψs
  refine ext_inner_left ℝ fun v => ?_
  rw [← integral_inner hint v, ← integral_inner hint' v]
  have h1 := hg.integral_mul_fderiv ψ hψ hψs v
  have h2 := hg'.integral_mul_fderiv ψ hψ hψs v
  have key : ∫ x, inner ℝ (g x) v * ψ x = ∫ x, inner ℝ (g' x) v * ψ x :=
    neg_injective (h1.symm.trans h2)
  have e : ∀ h : Euc d → Euc d, ∀ x, ψ x * inner ℝ v (h x) = inner ℝ (h x) v * ψ x :=
    fun h x => by rw [real_inner_comm, mul_comm]
  simp only [inner_smul_right, e]
  exact key

/-- **Uniqueness of weak gradients** (fundamental lemma of the calculus of variations). -/
theorem ae_eq (hg : HasWeakGradient f g) (hg' : HasWeakGradient f g') : g =ᵐ[volume] g' :=
  ae_eq_of_integral_contDiff_smul_eq hg.locallyIntegrable_grad hg'.locallyIntegrable_grad
    fun _ hψ hψs => hg.integral_smul_eq hg' hψ hψs

/-- A weak gradient of `f` is a weak gradient of any `f' =ᵐ f`. -/
theorem congr_left (hg : HasWeakGradient f g) (hff' : f =ᵐ[volume] f') :
    HasWeakGradient f' g where
  locallyIntegrable := hg.locallyIntegrable.congr hff'
  locallyIntegrable_grad := hg.locallyIntegrable_grad
  integral_mul_fderiv ψ hψ hψs v := by
    rw [← hg.integral_mul_fderiv ψ hψ hψs v]
    exact integral_congr_ae (hff'.mono fun x hx => by simp [hx])

/-- Any `g' =ᵐ g` is again a weak gradient of `f`. -/
theorem congr_right (hg : HasWeakGradient f g) (hgg' : g =ᵐ[volume] g') :
    HasWeakGradient f g' where
  locallyIntegrable := hg.locallyIntegrable
  locallyIntegrable_grad := hg.locallyIntegrable_grad.congr hgg'
  integral_mul_fderiv ψ hψ hψs v := by
    rw [hg.integral_mul_fderiv ψ hψ hψs v]
    congr 1
    exact integral_congr_ae (hgg'.mono fun x hx => by simp [hx])

/-- The weak gradient of `0` is `0`. -/
theorem zero : HasWeakGradient (0 : Euc d → ℝ) 0 where
  locallyIntegrable := locallyIntegrable_zero
  locallyIntegrable_grad := locallyIntegrable_zero
  integral_mul_fderiv _ _ _ _ := by simp

/-- Weak gradients are additive. -/
theorem add (hg : HasWeakGradient f g) (hg' : HasWeakGradient f' g') :
    HasWeakGradient (f + f') (g + g') where
  locallyIntegrable := hg.locallyIntegrable.add hg'.locallyIntegrable
  locallyIntegrable_grad := hg.locallyIntegrable_grad.add hg'.locallyIntegrable_grad
  integral_mul_fderiv ψ hψ hψs v := by
    have hc : Continuous fun x => fderiv ℝ ψ x v :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport fun x => fderiv ℝ ψ x v :=
      (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
    have i1 : Integrable fun x => f x * fderiv ℝ ψ x v := by
      simpa only [smul_eq_mul, mul_comm] using
        hg.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hc hcs
    have i2 : Integrable fun x => f' x * fderiv ℝ ψ x v := by
      simpa only [smul_eq_mul, mul_comm] using
        hg'.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hc hcs
    have j1 : Integrable fun x => inner ℝ (g x) v * ψ x := by
      refine (Integrable.const_inner (𝕜 := ℝ) v
        (hg.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport hψ.continuous
          hψs)).congr (Eventually.of_forall fun x => ?_)
      simp only [inner_smul_right]
      rw [real_inner_comm, mul_comm]
    have j2 : Integrable fun x => inner ℝ (g' x) v * ψ x := by
      refine (Integrable.const_inner (𝕜 := ℝ) v
        (hg'.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport hψ.continuous
          hψs)).congr (Eventually.of_forall fun x => ?_)
      simp only [inner_smul_right]
      rw [real_inner_comm, mul_comm]
    simp only [Pi.add_apply, add_mul, inner_add_left]
    rw [integral_add i1 i2, integral_add j1 j2, hg.integral_mul_fderiv ψ hψ hψs v,
      hg'.integral_mul_fderiv ψ hψ hψs v, neg_add]

/-- Weak gradients are homogeneous. -/
theorem smul (hg : HasWeakGradient f g) (c : ℝ) : HasWeakGradient (c • f) (c • g) where
  locallyIntegrable := hg.locallyIntegrable.smul c
  locallyIntegrable_grad := hg.locallyIntegrable_grad.smul c
  integral_mul_fderiv ψ hψ hψs v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, inner_smul_left, RCLike.conj_to_real]
    rw [integral_const_mul, integral_const_mul, hg.integral_mul_fderiv ψ hψ hψs v, mul_neg]

/-- The coordinate form of the integration-by-parts identity. -/
theorem integral_mul_fderiv_single (hg : HasWeakGradient f g) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (i : Fin d) :
    ∫ x, f x * fderiv ℝ ψ x (EuclideanSpace.single i 1) = -∫ x, g x i * ψ x := by
  rw [hg.integral_mul_fderiv ψ hψ hψs]
  simp [EuclideanSpace.inner_single_right]

end HasWeakGradient

/-! ### Classical gradients are weak gradients -/

/-- `fderiv ℝ f x v = ⟪∇f x, v⟫`. -/
theorem fderiv_apply_eq_inner_gradient (f : Euc d → ℝ) (x v : Euc d) :
    fderiv ℝ f x v = inner ℝ (gradient f x) v := by
  rw [← toDual_gradient, toDual_apply_apply]

/-- A `C¹` compactly supported function has its classical gradient as weak gradient
(integration by parts, `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`). -/
theorem hasWeakGradient_gradient {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) : HasWeakGradient f (gradient f) where
  locallyIntegrable := (hf.continuous.integrable_of_hasCompactSupport hfs).locallyIntegrable
  locallyIntegrable_grad :=
    ((continuous_gradient hf).integrable_of_hasCompactSupport
      (hasCompactSupport_gradient hfs)).locallyIntegrable
  integral_mul_fderiv ψ hψ hψs v := by
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hfv : Continuous fun x => fderiv ℝ f x v :=
      (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hψv : Continuous fun x => fderiv ℝ ψ x v :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v)
      (f := f) (g := ψ)
      ((hfv.mul hψ.continuous).integrable_of_hasCompactSupport (hψs.mul_left))
      ((hf.continuous.mul hψv).integrable_of_hasCompactSupport (hfs.mul_right))
      ((hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport (hfs.mul_right))
      (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hψ1.differentiable one_ne_zero x)
    rw [h]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only [fderiv_apply_eq_inner_gradient])

/-! ### The space `W₀^{1,p}(K)` -/

/-- `f ∈ W₀^{1,p}(K)` (paper (3.7)): `f ∈ L^p`, `f = 0` a.e. outside `K`, and `f` has a weak
gradient lying in `L^p`. For the bounded open convex sets of interest this is the usual
`W_0^{1,p}(K)` (closure of `C_c^∞(K)`); no closure is taken here. -/
structure MemW0 (p : ℝ) (K : Set (Euc d)) (f : Euc d → ℝ) : Prop where
  /-- `f ∈ L^p`. -/
  memLp : MemLp f (ENNReal.ofReal p)
  /-- `f` vanishes a.e. outside `K`. -/
  ae_eq_zero : ∀ᵐ x, x ∉ K → f x = 0
  /-- `f` has a weak gradient in `L^p`. -/
  exists_weakGradient : ∃ g : Euc d → Euc d, HasWeakGradient f g ∧ MemLp g (ENNReal.ofReal p)

open Classical in
/-- A chosen weak gradient of `f` (the zero function if `f` has none). It is a.e. unique
(`HasWeakGradient.weakGrad_ae_eq`). -/
noncomputable def weakGrad (f : Euc d → ℝ) : Euc d → Euc d :=
  if h : ∃ g, HasWeakGradient f g then h.choose else 0

theorem hasWeakGradient_weakGrad {f : Euc d → ℝ} (h : ∃ g, HasWeakGradient f g) :
    HasWeakGradient f (weakGrad f) := by
  rw [weakGrad, dif_pos h]
  exact h.choose_spec

/-- The chosen weak gradient agrees a.e. with any weak gradient. -/
theorem HasWeakGradient.weakGrad_ae_eq {f : Euc d → ℝ} {g : Euc d → Euc d}
    (hg : HasWeakGradient f g) : weakGrad f =ᵐ[volume] g :=
  (hasWeakGradient_weakGrad ⟨g, hg⟩).ae_eq hg

/-- The chosen weak gradient of a `C¹` compactly supported function is a.e. its gradient. -/
theorem weakGrad_ae_eq_gradient {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) : weakGrad f =ᵐ[volume] gradient f :=
  (hasWeakGradient_gradient hf hfs).weakGrad_ae_eq

namespace MemW0

variable {p : ℝ} {K : Set (Euc d)} {f f' : Euc d → ℝ}

theorem hasWeakGradient (hf : MemW0 p K f) : HasWeakGradient f (weakGrad f) :=
  hasWeakGradient_weakGrad (hf.exists_weakGradient.imp fun _ h => h.1)

theorem memLp_weakGrad (hf : MemW0 p K f) : MemLp (weakGrad f) (ENNReal.ofReal p) := by
  obtain ⟨g, hg, hgp⟩ := hf.exists_weakGradient
  exact hgp.ae_eq hg.weakGrad_ae_eq.symm

theorem zero : MemW0 p K (0 : Euc d → ℝ) where
  memLp := MemLp.zero
  ae_eq_zero := Eventually.of_forall fun _ _ => rfl
  exists_weakGradient := ⟨0, HasWeakGradient.zero, MemLp.zero⟩

theorem add (hf : MemW0 p K f) (hf' : MemW0 p K f') : MemW0 p K (f + f') where
  memLp := hf.memLp.add hf'.memLp
  ae_eq_zero := by
    filter_upwards [hf.ae_eq_zero, hf'.ae_eq_zero] with x h h' hx
    simp [h hx, h' hx]
  exists_weakGradient := by
    obtain ⟨g, hg, hgp⟩ := hf.exists_weakGradient
    obtain ⟨g', hg', hgp'⟩ := hf'.exists_weakGradient
    exact ⟨g + g', hg.add hg', hgp.add hgp'⟩

theorem smul (hf : MemW0 p K f) (c : ℝ) : MemW0 p K (c • f) where
  memLp := hf.memLp.const_smul c
  ae_eq_zero := by
    filter_upwards [hf.ae_eq_zero] with x h hx
    simp [h hx]
  exists_weakGradient := by
    obtain ⟨g, hg, hgp⟩ := hf.exists_weakGradient
    exact ⟨c • g, hg.smul c, hgp.const_smul c⟩

/-- Membership in `W₀^{1,p}(K)` only depends on the a.e.-class of `f`. -/
theorem congr (hf : MemW0 p K f) (hff' : f =ᵐ[volume] f') : MemW0 p K f' where
  memLp := hf.memLp.ae_eq hff'
  ae_eq_zero := by
    filter_upwards [hf.ae_eq_zero, hff'] with x h hx hxK
    rw [← hx]
    exact h hxK
  exists_weakGradient := by
    obtain ⟨g, hg, hgp⟩ := hf.exists_weakGradient
    exact ⟨g, hg.congr_left hff', hgp⟩

theorem mono {K' : Set (Euc d)} (hf : MemW0 p K f) (hK : K ⊆ K') : MemW0 p K' f where
  memLp := hf.memLp
  ae_eq_zero := hf.ae_eq_zero.mono fun _ h hx => h fun hxK => hx (hK hxK)
  exists_weakGradient := hf.exists_weakGradient

end MemW0

/-- The `L^p` seminorm of the weak gradient, `‖∇f‖_{L^p}`. -/
noncomputable def gradLpNorm (p : ℝ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  eLpNorm (weakGrad f) (ENNReal.ofReal p)

theorem MemW0.gradLpNorm_lt_top {p : ℝ} {K : Set (Euc d)} {f : Euc d → ℝ} (hf : MemW0 p K f) :
    gradLpNorm p f < ⊤ :=
  hf.memLp_weakGrad.eLpNorm_lt_top

/-- A smooth test function on `K` lies in `W₀^{1,p}(K)`: `C_c^∞(K) ⊆ W₀^{1,p}(K)`. -/
theorem _root_.Komlos.IsTestFn.memW0 {K : Set (Euc d)} {f : Euc d → ℝ} (hf : IsTestFn K f)
    (p : ℝ) : MemW0 p K f where
  memLp := hf.contDiff.continuous.memLp_of_hasCompactSupport hf.hasCompactSupport
  ae_eq_zero := Eventually.of_forall fun _ hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hf.supp_subset h)
  exists_weakGradient :=
    ⟨gradient f, hasWeakGradient_gradient hf.contDiff_one hf.hasCompactSupport,
      (continuous_gradient hf.contDiff_one).memLp_of_hasCompactSupport
        (hasCompactSupport_gradient hf.hasCompactSupport)⟩

/-- A nonzero test function is not a.e. zero. -/
theorem _root_.Komlos.IsTestFn.not_ae_eq_zero {K : Set (Euc d)} {f : Euc d → ℝ}
    (hf : IsTestFn K f) : ¬ f =ᵐ[volume] 0 := fun h =>
  hf.ne_zero ((hf.contDiff.continuous.ae_eq_iff_eq volume continuous_const).1 h)

/-! ### Rayleigh quotients over `W₀^{1,p}` -/

/-- The Sobolev energy `∫ F(∇f)^p` of `f`, over the weak gradient. -/
noncomputable def sobolevEnergy (p : ℝ) (F : Euc d → ℝ) (f : Euc d → ℝ) : ℝ :=
  ∫ x, F (weakGrad f x) ^ p

/-- The Rayleigh quotient `(∫ F(∇f)^p) / (∫ |f|^p)` over the weak gradient (paper (3.7)). -/
noncomputable def sobolevRayleigh (p : ℝ) (F : Euc d → ℝ) (f : Euc d → ℝ) : ℝ :=
  sobolevEnergy p F f / ∫ x, |f x| ^ p

/-- The Sobolev-space eigenvalue `inf_{0 ≠ f ∈ W_0^{1,p}(K)} (∫ F(∇f)^p) / (∫ |f|^p)`
(paper (3.7), literally), with a subtype index as in `lambdaGen`. -/
noncomputable def lambdaSob (p : ℝ) (F : Euc d → ℝ) (K : Set (Euc d)) : ℝ :=
  ⨅ f : {f : Euc d → ℝ // MemW0 p K f ∧ ¬ f =ᵐ[volume] 0}, sobolevRayleigh p F f.1

section Rayleigh

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)}

/-- On a `C¹` compactly supported function the Sobolev energy is the classical one. -/
theorem sobolevEnergy_eq_integral_gradient {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) : sobolevEnergy p F f = ∫ x, F (gradient f x) ^ p :=
  integral_congr_ae ((weakGrad_ae_eq_gradient hf hfs).mono fun x hx => by simp [hx])

/-- On a test function the Sobolev Rayleigh quotient is `rayleighGen`. -/
theorem sobolevRayleigh_eq_rayleighGen {f : Euc d → ℝ} (hf : IsTestFn K f) :
    sobolevRayleigh p F f = rayleighGen p F f := by
  rw [sobolevRayleigh, rayleighGen,
    sobolevEnergy_eq_integral_gradient hf.contDiff_one hf.hasCompactSupport]

theorem sobolevEnergy_nonneg (hF : ∀ ξ, 0 ≤ F ξ) (f : Euc d → ℝ) : 0 ≤ sobolevEnergy p F f :=
  integral_nonneg fun _ => Real.rpow_nonneg (hF _) p

theorem sobolevRayleigh_nonneg (hF : ∀ ξ, 0 ≤ F ξ) (f : Euc d → ℝ) :
    0 ≤ sobolevRayleigh p F f :=
  div_nonneg (sobolevEnergy_nonneg hF f)
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) p)

theorem lambdaSob_nonneg (hF : ∀ ξ, 0 ≤ F ξ) : 0 ≤ lambdaSob p F K :=
  Real.iInf_nonneg fun f => sobolevRayleigh_nonneg hF f.1

theorem bddBelow_range_sobolevRayleigh (hF : ∀ ξ, 0 ≤ F ξ) (p : ℝ) (K : Set (Euc d)) :
    BddBelow (Set.range fun f : {f : Euc d → ℝ // MemW0 p K f ∧ ¬ f =ᵐ[volume] 0} =>
      sobolevRayleigh p F f.1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact sobolevRayleigh_nonneg hF g.1

theorem lambdaSob_le_sobolevRayleigh (hF : ∀ ξ, 0 ≤ F ξ) {f : Euc d → ℝ} (hf : MemW0 p K f)
    (hf0 : ¬ f =ᵐ[volume] 0) : lambdaSob p F K ≤ sobolevRayleigh p F f :=
  ciInf_le (bddBelow_range_sobolevRayleigh hF p K) ⟨f, hf, hf0⟩

/-- The Sobolev eigenvalue is at most the smooth-test-function eigenvalue: `C_c^∞(K) ⊆
W₀^{1,p}(K)` with the same Rayleigh quotients. (The reverse inequality is the density of
`C_c^∞(K)` in `W₀^{1,p}(K)`, `lambdaGen_le_lambdaSob`.) -/
theorem lambdaSob_le_lambdaGen [Nonempty {f : Euc d → ℝ // IsTestFn K f}]
    (hF : ∀ ξ, 0 ≤ F ξ) : lambdaSob p F K ≤ lambdaGen p F K := by
  refine le_ciInf fun f => ?_
  rw [← sobolevRayleigh_eq_rayleighGen f.2]
  exact lambdaSob_le_sobolevRayleigh hF (f.2.memW0 p) f.2.not_ae_eq_zero

end Rayleigh

/-! ### The Dirichlet Poincaré inequality, smooth case -/

section Poincare

variable {p : ℝ}

/-- `|∂_e f (y)| ≤ ‖∇f(y)‖` for a unit vector `e`. -/
theorem enorm_fderiv_apply_le (f : Euc d → ℝ) (y : Euc d) {e : Euc d} (he : ‖e‖ = 1) :
    ‖fderiv ℝ f y e‖ₑ ≤ ‖gradient f y‖ₑ := by
  rw [fderiv_apply_eq_inner_gradient, enorm_eq_nnnorm, enorm_eq_nnnorm]
  have := abs_real_inner_le_norm (gradient f y) e
  rw [he, mul_one] at this
  exact_mod_cast (Real.norm_eq_abs _).trans_le this

/-- Fundamental theorem of calculus along the line `x + ℝ e`: if `f` is `C¹` with support in
`closedBall 0 R`, `‖e‖ = 1` and `T > 2R`, then `|f x| ≤ ∫₀^T ‖∇f(x + t e)‖ dt`. -/
theorem enorm_le_lintegral_gradient_line {R T : ℝ} {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : tsupport f ⊆ Metric.closedBall 0 R) {e : Euc d} (he : ‖e‖ = 1) (hT : 2 * R < T)
    (x : Euc d) : ‖f x‖ₑ ≤ ∫⁻ t in Ioc 0 T, ‖gradient f (x + t • e)‖ₑ := by
  by_cases hx : x ∈ Metric.closedBall 0 R
  swap
  · have : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)
    simp [this]
  have hxR : ‖x‖ ≤ R := by simpa using hx
  have hT0 : 0 ≤ T := by linarith [norm_nonneg x]
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => f (x + t • e)) (fderiv ℝ f (x + t • e) e) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    exact (hf.differentiable one_ne_zero (x + t • e)).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous fun t : ℝ => fderiv ℝ f (x + t • e) e :=
    ((hf.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hftc : ∫ t in (0 : ℝ)..T, fderiv ℝ f (x + t • e) e = f (x + T • e) - f (x + (0 : ℝ) • e) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 T)
  have hzero : f (x + T • e) = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have h1 := hsupp h
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 := norm_sub_norm_le (T • e) (-x)
    rw [norm_neg, sub_neg_eq_add, add_comm, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hT0] at h2
    linarith
  have hfx : f x = -∫ t in (0 : ℝ)..T, fderiv ℝ f (x + t • e) e := by
    rw [hftc, hzero, zero_smul, add_zero, zero_sub, neg_neg]
  calc ‖f x‖ₑ = ‖∫ t in Ioc 0 T, fderiv ℝ f (x + t • e) e‖ₑ := by
        rw [hfx, enorm_neg, intervalIntegral.integral_of_le hT0]
    _ ≤ ∫⁻ t in Ioc 0 T, ‖fderiv ℝ f (x + t • e) e‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Ioc 0 T, ‖gradient f (x + t • e)‖ₑ :=
        lintegral_mono fun t => enorm_fderiv_apply_le f _ he

/-- Hölder on `(0, T]`: `(∫₀^T h)^p ≤ T^{p-1} ∫₀^T h^p`. -/
theorem lintegral_Ioc_rpow_le (T : ℝ) (hp : 1 < p) {h : ℝ → ℝ≥0∞}
    (hh : AEMeasurable h (volume.restrict (Ioc 0 T))) :
    (∫⁻ t in Ioc 0 T, h t) ^ p ≤ ENNReal.ofReal T ^ (p - 1) * ∫⁻ t in Ioc 0 T, h t ^ p := by
  set q := Real.conjExponent p with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc 0 T)) hpq hh
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, one_mul, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero] at key
  calc (∫⁻ t in Ioc 0 T, h t) ^ p
      ≤ ((∫⁻ t in Ioc 0 T, h t ^ p) ^ (1 / p) * ENNReal.ofReal T ^ (1 / q)) ^ p :=
        ENNReal.rpow_le_rpow key hp0.le
    _ = (∫⁻ t in Ioc 0 T, h t ^ p) ^ (1 / p * p) * ENNReal.ofReal T ^ (1 / q * p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    _ = ENNReal.ofReal T ^ (p - 1) * ∫⁻ t in Ioc 0 T, h t ^ p := by
        rw [one_div_mul_cancel hp0.ne', ENNReal.rpow_one, mul_comm]
        congr 2
        rw [one_div, inv_mul_eq_div, hpq.div_conj_eq_sub_one]

/-- Conversion: `∫ |f|^p ≤ C^p ∫ ‖g‖^p` gives `‖f‖_{L^p} ≤ C ‖g‖_{L^p}`. -/
theorem eLpNorm_le_of_lintegral_rpow_le (hp : 0 < p) {f : Euc d → ℝ} {g : Euc d → Euc d}
    {C : ℝ≥0∞} (h : ∫⁻ x, ‖f x‖ₑ ^ p ≤ C ^ p * ∫⁻ x, ‖g x‖ₑ ^ p) :
    eLpNorm f (ENNReal.ofReal p) ≤ C * eLpNorm g (ENNReal.ofReal p) := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp' hpt, ENNReal.toReal_ofReal hp.le]
  calc (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p)
      ≤ (C ^ p * ∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow h (by positivity)
    _ = C * (∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- The `∫⁻`-level Poincaré inequality for `C¹` compactly supported functions:
`∫ |f|^p ≤ T^p ∫ ‖∇f‖^p` when `tsupport f ⊆ closedBall 0 R` and `T > 2R` (`d ≥ 1`). -/
theorem lintegral_rpow_le_lintegral_rpow_gradient (hd : 0 < d) {R T : ℝ} (hR : 0 ≤ R)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hsupp : tsupport f ⊆ Metric.closedBall 0 R)
    (hp : 1 < p) (hT : 2 * R < T) :
    ∫⁻ x, ‖f x‖ₑ ^ p ≤ ENNReal.ofReal T ^ p * ∫⁻ x, ‖gradient f x‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hT0 : 0 < T := by linarith
  set e : Euc d := EuclideanSpace.single ⟨0, hd⟩ 1 with he_def
  have he : ‖e‖ = 1 := by simp [he_def]
  have hTne : ENNReal.ofReal T ≠ 0 := by simpa using hT0
  have hTtop : ENNReal.ofReal T ≠ ⊤ := ENNReal.ofReal_ne_top
  have hG : Continuous fun q : Euc d × ℝ => ‖gradient f (q.1 + q.2 • e)‖ₑ ^ p :=
    ENNReal.continuous_rpow_const.comp (continuous_enorm.comp
      ((continuous_gradient hf).comp (continuous_fst.add (continuous_snd.smul continuous_const))))
  calc ∫⁻ x, ‖f x‖ₑ ^ p
      ≤ ∫⁻ x, (∫⁻ t in Ioc 0 T, ‖gradient f (x + t • e)‖ₑ) ^ p :=
        lintegral_mono fun x =>
          ENNReal.rpow_le_rpow (enorm_le_lintegral_gradient_line hf hsupp he hT x) hp0.le
    _ ≤ ∫⁻ x, ENNReal.ofReal T ^ (p - 1) * ∫⁻ t in Ioc 0 T, ‖gradient f (x + t • e)‖ₑ ^ p :=
        lintegral_mono fun x => lintegral_Ioc_rpow_le T hp
          (continuous_enorm.comp ((continuous_gradient hf).comp
            (continuous_const.add (continuous_id.smul continuous_const)))).measurable.aemeasurable
    _ = ENNReal.ofReal T ^ (p - 1) *
          ∫⁻ x, ∫⁻ t in Ioc 0 T, ‖gradient f (x + t • e)‖ₑ ^ p :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hTtop)
    _ = ENNReal.ofReal T ^ (p - 1) *
          ∫⁻ t in Ioc 0 T, ∫⁻ x, ‖gradient f (x + t • e)‖ₑ ^ p := by
        rw [lintegral_lintegral_swap hG.measurable.aemeasurable]
    _ = ENNReal.ofReal T ^ (p - 1) * ∫⁻ t in Ioc 0 T, ∫⁻ x, ‖gradient f x‖ₑ ^ p := by
        congr 1
        refine lintegral_congr fun t => ?_
        exact lintegral_add_right_eq_self (fun x => ‖gradient f x‖ₑ ^ p) (t • e)
    _ = ENNReal.ofReal T ^ p * ∫⁻ x, ‖gradient f x‖ₑ ^ p := by
        have h1 : ENNReal.ofReal T ^ (p - 1) * ENNReal.ofReal T = ENNReal.ofReal T ^ p := by
          calc ENNReal.ofReal T ^ (p - 1) * ENNReal.ofReal T
              = ENNReal.ofReal T ^ (p - 1) * ENNReal.ofReal T ^ (1 : ℝ) := by
                rw [ENNReal.rpow_one]
            _ = ENNReal.ofReal T ^ (p - 1 + 1) := (ENNReal.rpow_add _ _ hTne hTtop).symm
            _ = ENNReal.ofReal T ^ p := by rw [sub_add_cancel]
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← h1]
        ring

/-- **Dirichlet Poincaré inequality, smooth case** (paper Lemma 3.2, "the Dirichlet Poincaré
inequality"): for `f ∈ C¹_c` with `tsupport f ⊆ closedBall 0 R`, `1 < p`, and any `T > 2R`,
`‖f‖_{L^p} ≤ T ‖∇f‖_{L^p}`. (Requires `d ≥ 1`.) -/
theorem eLpNorm_le_eLpNorm_gradient (hd : 0 < d) {R T : ℝ} (hR : 0 ≤ R) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 1 f) (hsupp : tsupport f ⊆ Metric.closedBall 0 R) (hp : 1 < p)
    (hT : 2 * R < T) :
    eLpNorm f (ENNReal.ofReal p) ≤ ENNReal.ofReal T * eLpNorm (gradient f) (ENNReal.ofReal p) :=
  eLpNorm_le_of_lintegral_rpow_le (by linarith)
    (lintegral_rpow_le_lintegral_rpow_gradient hd hR hf hsupp hp hT)

end Poincare

/-! ### Mollification -/

section Mollify

open scoped Convolution

variable {p : ℝ}

/-- Scalar convolution is commutative: `(ρ ⋆ f)(x) = (f ⋆ ρ)(x)`. -/
theorem convolution_lsmul_comm (f ρ : Euc d → ℝ) (x : Euc d) :
    (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x := by
  rw [convolution_eq_swap, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]

/-- Support of a mollification: `supp f ⊆ B̄(0,R)`, `supp ρ ⊆ B̄(0,r)` give
`tsupport (f ⋆ ρ) ⊆ B̄(0, R + r)`. -/
theorem tsupport_convolution_subset_closedBall {f ρ : Euc d → ℝ} {R r : ℝ} (hR : 0 ≤ R)
    (hr : 0 ≤ r) (hf : Function.support f ⊆ Metric.closedBall 0 R)
    (hρ : Function.support ρ ⊆ Metric.closedBall 0 r) :
    tsupport (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) ⊆ Metric.closedBall 0 (R + r) := by
  refine closure_minimal ((support_convolution_subset _).trans ?_) Metric.isClosed_closedBall
  calc Function.support f + Function.support ρ
      ⊆ Metric.closedBall 0 R + Metric.closedBall 0 r := Set.add_subset_add hf hρ
    _ = Metric.closedBall 0 (R + r) := by rw [closedBall_add_closedBall hR hr, add_zero]

/-- The gradient of the mollification `f ⋆ ρ` of a function with weak gradient `g` is the
mollification `x ↦ ∫ ρ(x - t) g(t) dt` of `g` (differentiation under the integral plus the
weak-gradient identity with the test function `t ↦ ρ(x - t)`). -/
theorem gradient_convolution_eq {f : Euc d → ℝ} {g : Euc d → Euc d} (hg : HasWeakGradient f g)
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρs : HasCompactSupport ρ) (x : Euc d) :
    gradient (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x = ∫ t, ρ (x - t) • g t := by
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hder := hρs.hasFDerivAt_convolution_right (L := L) hg.locallyIntegrable hρ1 x
  -- the test function `ψ t = ρ (x - t)`
  set ψ : Euc d → ℝ := fun t => ρ (x - t) with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := hρ.comp (contDiff_const.sub contDiff_id)
  have hψs : HasCompactSupport ψ := hρs.comp_homeomorph (Homeomorph.subLeft x)
  have hψd : ∀ t v, fderiv ℝ ψ t v = -(fderiv ℝ ρ (x - t) v) := by
    intro t v
    have h : HasFDerivAt ψ ((fderiv ℝ ρ (x - t)).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) t :=
      ((hρ1.differentiable one_ne_zero) (x - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub x)
    rw [h.fderiv]
    simp
  have hgi : Integrable fun t => ρ (x - t) • g t :=
    hg.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport hψ.continuous hψs
  refine ext_inner_right ℝ fun v => ?_
  rw [← fderiv_apply_eq_inner_gradient, hder.fderiv,
    convolution_precompR_apply L hg.locallyIntegrable (hρs.fderiv (𝕜 := ℝ))
      (hρ1.continuous_fderiv one_ne_zero), convolution_def]
  simp only [hL, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have key := hg.integral_mul_fderiv ψ hψ hψs v
  simp only [hψd, mul_neg, integral_neg, neg_inj] at key
  rw [key, real_inner_comm, ← integral_inner hgi v]
  simp only [inner_smul_right]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hψ_def]
  rw [real_inner_comm, mul_comm]

/-- The gradient of the mollification `mollifyWith ρ f` of a function with weak gradient `g` is
the mollification `mollifyWith ρ g`. -/
theorem gradient_mollifyWith {f : Euc d → ℝ} {g : Euc d → Euc d} (hg : HasWeakGradient f g)
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρs : HasCompactSupport ρ) :
    gradient (mollifyWith ρ f) = mollifyWith ρ g := by
  funext x
  rw [mollifyWith_eq_convolution_right]
  exact gradient_convolution_eq hg hρ hρs x

/-- The standard mollifier sequence: bumps with `rIn = 1/(n+2)`, `rOut = 1/(n+1)`. -/
noncomputable def mollifierBump (n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity,
    one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩

/-- Mollifications of a locally integrable `f` converge to `f` a.e. (Lebesgue differentiation,
Mathlib's `ae_convolution_tendsto_right_of_locallyIntegrable`). -/
theorem ae_tendsto_convolution_stdBump {f : Euc d → ℝ} (hf : LocallyIntegrable f) :
    ∀ᵐ x, Tendsto
      (fun n => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (mollifierBump n).normed volume) x)
      atTop (𝓝 (f x)) := by
  have hφ : Tendsto (fun n : ℕ => (mollifierBump (d := d) n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h'φ : ∀ᶠ n : ℕ in atTop,
      (mollifierBump (d := d) n).rOut ≤ 2 * (mollifierBump (d := d) n).rIn := by
    refine Eventually.of_forall fun n => ?_
    show 1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((n : ℝ) + 2))
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ h'φ hf]
    with x hx
  simpa only [convolution_lsmul_comm] using hx

end Mollify

/-! ### The Dirichlet Poincaré inequality on `W₀^{1,p}` -/

section PoincareW0

open scoped Convolution

variable {p : ℝ}

/-- **Dirichlet Poincaré inequality on `W₀^{1,p}`** (paper Lemma 3.2, "the Dirichlet Poincaré
inequality"): if `K ⊆ closedBall 0 R`, `f ∈ W₀^{1,p}(K)`, `1 < p` and `T > 2R`, then
`‖f‖_{L^p} ≤ T ‖∇f‖_{L^p}`. Proof: mollify (`gradient_convolution_eq`,
`lintegral_enorm_mollifyWith_rpow_le`), apply the smooth case, and pass to the limit by Fatou. -/
theorem MemW0.eLpNorm_le_eLpNorm_weakGrad (hd : 0 < d) (hp : 1 < p) {K : Set (Euc d)} {R : ℝ}
    (hR : 0 ≤ R) (hK : K ⊆ Metric.closedBall 0 R) {f : Euc d → ℝ} (hf : MemW0 p K f) {T : ℝ}
    (hT : 2 * R < T) :
    eLpNorm f (ENNReal.ofReal p) ≤ ENNReal.ofReal T * eLpNorm (weakGrad f) (ENNReal.ofReal p) := by
  have hp0 : 0 < p := by linarith
  set g := weakGrad f with hg_def
  have hg : HasWeakGradient f g := hf.hasWeakGradient
  have hgp : MemLp g (ENNReal.ofReal p) := hf.memLp_weakGrad
  -- replace `f` by a representative supported in the ball
  set f' := (Metric.closedBall (0 : Euc d) R).indicator f with hf'_def
  have hff' : f =ᵐ[volume] f' := by
    filter_upwards [hf.ae_eq_zero] with x hx
    by_cases hxR : x ∈ Metric.closedBall (0 : Euc d) R
    · simp [hf'_def, Set.indicator_of_mem hxR]
    · simp [hf'_def, Set.indicator_of_notMem hxR, hx fun hxK => hxR (hK hxK)]
  have hg' : HasWeakGradient f' g := hg.congr_left hff'
  have hsupp' : Function.support f' ⊆ Metric.closedBall 0 R := fun x hx => by
    by_contra h
    exact hx (Set.indicator_of_notMem h f)
  -- the mollified sequence
  set ρ : ℕ → Euc d → ℝ := fun n => (mollifierBump n).normed volume with hρ_def
  set u : ℕ → Euc d → ℝ := fun n => f' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ n with hu_def
  set G : ℕ → Euc d → Euc d := fun n x => ∫ t, ρ n (x - t) • g t with hG_def
  have hu_smooth : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    (mollifierBump n).hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hg'.locallyIntegrable (ContDiffBump.contDiff_normed _)
  have hu_supp : ∀ n, tsupport (u n) ⊆ Metric.closedBall 0 (R + 1 / ((n : ℝ) + 1)) := fun n =>
    tsupport_convolution_subset_closedBall hR (by positivity) hsupp'
      (by rw [ContDiffBump.support_normed_eq]; exact Metric.ball_subset_closedBall)
  have hu_grad : ∀ n, gradient (u n) = G n := fun n => funext fun x =>
    gradient_convolution_eq hg' (ContDiffBump.contDiff_normed _)
      (mollifierBump n).hasCompactSupport_normed x
  have hG_le : ∀ n, ∫⁻ x, ‖G n x‖ₑ ^ p ≤ ∫⁻ x, ‖g x‖ₑ ^ p := fun n =>
    lintegral_enorm_mollifyWith_rpow_le hgp.aestronglyMeasurable (ContDiffBump.continuous_normed _)
      (ContDiffBump.nonneg_normed _) (ContDiffBump.integrable_normed _)
      (ContDiffBump.integral_normed _) hp
  -- the smooth Poincaré inequality, eventually in `n`
  have hev : ∀ᶠ n : ℕ in atTop,
      ∫⁻ x, ‖u n x‖ₑ ^ p ≤ ENNReal.ofReal T ^ p * ∫⁻ x, ‖g x‖ₑ ^ p := by
    have hlt : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < (T - 2 * R) / 2 :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hlt] with n hn
    calc ∫⁻ x, ‖u n x‖ₑ ^ p
        ≤ ENNReal.ofReal T ^ p * ∫⁻ x, ‖gradient (u n) x‖ₑ ^ p :=
          lintegral_rpow_le_lintegral_rpow_gradient hd (by positivity) (hu_smooth n) (hu_supp n)
            hp (by linarith)
      _ ≤ ENNReal.ofReal T ^ p * ∫⁻ x, ‖g x‖ₑ ^ p := by
          rw [hu_grad n]
          exact mul_le_mul_right (hG_le n) _
  -- Fatou
  have hae := ae_tendsto_convolution_stdBump hg'.locallyIntegrable
  have hfatou : ∫⁻ x, ‖f' x‖ₑ ^ p ≤ liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ p) atTop := by
    calc ∫⁻ x, ‖f' x‖ₑ ^ p = ∫⁻ x, liminf (fun n => ‖u n x‖ₑ ^ p) atTop := by
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          exact ((ENNReal.continuous_rpow_const.tendsto _).comp
            ((continuous_enorm.tendsto _).comp hx)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ p) atTop :=
          lintegral_liminf_le' fun n =>
            (ENNReal.continuous_rpow_const.comp
              (hu_smooth n).continuous.enorm).measurable.aemeasurable
  have hmain : ∫⁻ x, ‖f x‖ₑ ^ p ≤ ENNReal.ofReal T ^ p * ∫⁻ x, ‖g x‖ₑ ^ p :=
    calc ∫⁻ x, ‖f x‖ₑ ^ p = ∫⁻ x, ‖f' x‖ₑ ^ p :=
          lintegral_congr_ae (hff'.mono fun x hx => by simp only [hx])
      _ ≤ liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ p) atTop := hfatou
      _ ≤ ENNReal.ofReal T ^ p * ∫⁻ x, ‖g x‖ₑ ^ p := liminf_le_of_frequently_le' hev.frequently
  exact eLpNorm_le_of_lintegral_rpow_le hp0 hmain

/-- Poincaré on a bounded set, in terms of `gradLpNorm`: there is `C < ∞` with
`‖f‖_{L^p} ≤ C ‖∇f‖_{L^p}` for all `f ∈ W₀^{1,p}(K)`. -/
theorem exists_poincare_const (hd : 0 < d) (hp : 1 < p) {K : Set (Euc d)}
    (hK : Bornology.IsBounded K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : Euc d → ℝ, MemW0 p K f →
      eLpNorm f (ENNReal.ofReal p) ≤ C * gradLpNorm p f := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : Euc d)
  refine ⟨ENNReal.ofReal (2 * |R| + 1), ENNReal.ofReal_ne_top, fun f hf => ?_⟩
  exact hf.eLpNorm_le_eLpNorm_weakGrad hd hp (abs_nonneg R)
    (hR.trans (Metric.closedBall_subset_closedBall (le_abs_self R))) (by linarith [abs_nonneg R])

end PoincareW0

/-! ### Positivity of the eigenvalue -/

section Positivity

variable {p : ℝ}

/-- A bounded open nonempty set admits a smooth test function (a bump at an interior point). -/
theorem _root_.Komlos.IsGoodConvex.nonempty_testFn {K : Set (Euc d)} (hK : IsGoodConvex K) :
    Nonempty {f : Euc d → ℝ // IsTestFn K f} := by
  obtain ⟨x₀, hx₀⟩ := hK.nonempty
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isOpen x₀ hx₀
  let φ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨⟨φ, φ.contDiff, φ.hasCompactSupport, ?_, ?_⟩⟩
  · rw [φ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show ε / 2 < ε by linarith)).trans hball
  · intro h
    have := φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    rw [h] at this
    simp at this

/-- A test function on `K` gives a nonzero element of `W₀^{1,p}(K)`. -/
theorem nonempty_memW0_of_testFn {K : Set (Euc d)} [h : Nonempty {f : Euc d → ℝ // IsTestFn K f}]
    (p : ℝ) : Nonempty {f : Euc d → ℝ // MemW0 p K f ∧ ¬ f =ᵐ[volume] 0} :=
  ⟨⟨h.some.1, h.some.2.memW0 p, h.some.2.not_ae_eq_zero⟩⟩

/-- **Positivity of the eigenvalue** (paper Lemma 3.2: "Norm equivalence and the Dirichlet
Poincaré inequality make this quantity positive"): if `c‖ξ‖ ≤ F ξ ≤ C‖ξ‖` with `c > 0`,
`K ⊆ closedBall 0 R` and `T > 2R`, then `(c/T)^p ≤ λ_{p,F}(K)` over `W₀^{1,p}(K)`. -/
theorem rpow_le_lambdaSob (hd : 0 < d) (hp : 1 < p) {F : Euc d → ℝ} (hF : Continuous F)
    {c C : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) (hFC : ∀ ξ, F ξ ≤ C * ‖ξ‖)
    {K : Set (Euc d)} [Nonempty {f : Euc d → ℝ // MemW0 p K f ∧ ¬ f =ᵐ[volume] 0}] {R : ℝ}
    (hR : 0 ≤ R) (hK : K ⊆ Metric.closedBall 0 R) {T : ℝ} (hT : 2 * R < T) :
    (c / T) ^ p ≤ lambdaSob p F K := by
  have hp0 : 0 < p := by linarith
  have hT0 : 0 < T := by linarith
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  -- `C ≥ c > 0`, testing at a unit vector
  have hC : 0 ≤ C := by
    set e : Euc d := EuclideanSpace.single ⟨0, hd⟩ 1 with he_def
    have he : ‖e‖ = 1 := by simp [he_def]
    have h1 := hcF e
    have h2 := hFC e
    rw [he] at h1 h2
    linarith
  refine le_ciInf fun f => ?_
  obtain ⟨f, hf, hf0⟩ := f
  show (c / T) ^ p ≤ sobolevRayleigh p F f
  set g := weakGrad f with hg_def
  have hgp : MemLp g (ENNReal.ofReal p) := hf.memLp_weakGrad
  set Nf := (eLpNorm f (ENNReal.ofReal p)).toReal with hNf
  set Ng := (eLpNorm g (ENNReal.ofReal p)).toReal with hNg
  have hNf_pos : 0 < Nf := by
    refine ENNReal.toReal_pos (fun h => hf0 ?_) hf.memLp.eLpNorm_ne_top
    exact (eLpNorm_eq_zero_iff hf.memLp.aestronglyMeasurable hp').1 h
  have hpoinc : Nf ≤ T * Ng := by
    have h1 := hf.eLpNorm_le_eLpNorm_weakGrad hd hp hR hK hT
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgp.eLpNorm_ne_top) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hT0.le] at h2
  have hNg_nonneg : 0 ≤ Ng := ENNReal.toReal_nonneg
  have hden : ∫ x, |f x| ^ p = Nf ^ p := by
    simpa only [Real.norm_eq_abs] using integral_norm_rpow_eq hp0 hf.memLp
  have hgint : Integrable fun x => ‖g x‖ ^ p := by
    simpa [ENNReal.toReal_ofReal hp0.le] using hgp.integrable_norm_rpow hp' ENNReal.ofReal_ne_top
  have hF0 : ∀ ξ, 0 ≤ F ξ := fun ξ => (mul_nonneg hc.le (norm_nonneg _)).trans (hcF ξ)
  have hFint : Integrable fun x => F (g x) ^ p := by
    refine (hgint.const_mul (C ^ p)).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable
        (hF.comp_aestronglyMeasurable hgp.aestronglyMeasurable)
    · rw [Real.norm_of_nonneg (Real.rpow_nonneg (hF0 _) p), ← Real.mul_rpow hC (norm_nonneg _)]
      exact Real.rpow_le_rpow (hF0 _) (hFC _) hp0.le
  have hnum : c ^ p * Ng ^ p ≤ ∫ x, F (g x) ^ p := by
    rw [← integral_norm_rpow_eq hp0 hgp, ← integral_const_mul]
    refine integral_mono (hgint.const_mul _) hFint fun x => ?_
    rw [← Real.mul_rpow hc.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (hcF _) hp0.le
  rw [sobolevRayleigh, sobolevEnergy, hden, le_div_iff₀ (by positivity)]
  calc (c / T) ^ p * Nf ^ p = c ^ p * (Nf / T) ^ p := by
        rw [Real.div_rpow hc.le hT0.le, Real.div_rpow hNf_pos.le hT0.le]
        ring
    _ ≤ c ^ p * Ng ^ p := by
        gcongr
        exact (div_le_iff₀ hT0).2 (by linarith)
    _ ≤ ∫ x, F (g x) ^ p := hnum

/-- The Sobolev eigenvalue of a bounded set is positive for an integrand comparable to the norm. -/
theorem lambdaSob_pos (hd : 0 < d) (hp : 1 < p) {F : Euc d → ℝ} (hF : Continuous F) {c C : ℝ}
    (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) (hFC : ∀ ξ, F ξ ≤ C * ‖ξ‖) {K : Set (Euc d)}
    [Nonempty {f : Euc d → ℝ // MemW0 p K f ∧ ¬ f =ᵐ[volume] 0}] (hK : Bornology.IsBounded K) :
    0 < lambdaSob p F K := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : Euc d)
  have hR' : K ⊆ Metric.closedBall 0 |R| :=
    hR.trans (Metric.closedBall_subset_closedBall (le_abs_self R))
  refine lt_of_lt_of_le ?_ (rpow_le_lambdaSob hd hp hF hc hcF hFC (abs_nonneg R) hR'
    (T := 2 * |R| + 1) (by linarith [abs_nonneg R]))
  have : 0 < c / (2 * |R| + 1) := by positivity
  positivity

/-- **The smooth eigenvalue `λ_{p,F}(K)` is positive** for a bounded open nonempty convex `K` and
an integrand comparable to the norm (paper Lemma 3.2: "positive and finite for every nonempty
bounded open `K`"). -/
theorem lambdaGen_pos (hd : 0 < d) (hp : 1 < p) {F : Euc d → ℝ} (hF : Continuous F) {c C : ℝ}
    (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) (hFC : ∀ ξ, F ξ ≤ C * ‖ξ‖) {K : Set (Euc d)}
    (hK : IsGoodConvex K) : 0 < lambdaGen p F K := by
  have := hK.nonempty_testFn
  have := nonempty_memW0_of_testFn (K := K) p
  exact lt_of_lt_of_le (lambdaSob_pos hd hp hF hc hcF hFC hK.isBounded)
    (lambdaSob_le_lambdaGen fun ξ => (mul_nonneg hc.le (norm_nonneg _)).trans (hcF ξ))

end Positivity

/-! ### Weak gradients pass to `L^p` limits -/

section Closedness

variable {p : ℝ}

/-- Hölder for products of enorms: `∫ ‖h‖ ‖φ‖ ≤ ‖h‖_{L^p} ‖φ‖_{L^q}` with `1/p + 1/q = 1`. -/
theorem lintegral_enorm_mul_enorm_le (hp : 1 < p) {H H' : Type*} [NormedAddCommGroup H]
    [NormedAddCommGroup H'] {h : Euc d → H} (hh : AEStronglyMeasurable h volume) {φ : Euc d → H'}
    (hφ : AEStronglyMeasurable φ volume) :
    ∫⁻ x, ‖h x‖ₑ * ‖φ x‖ₑ ≤
      eLpNorm h (ENNReal.ofReal p) * eLpNorm φ (ENNReal.ofReal (Real.conjExponent p)) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < Real.conjExponent p := hpq.symm.pos
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hq' : ENNReal.ofReal (Real.conjExponent p) ≠ 0 := by simpa using hq0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0.le]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hh.enorm hφ.enorm

/-- `‖∫ h φ‖ ≤ ‖h‖_{L^p} ‖φ‖_{L^q}` for scalar `h, φ`. -/
theorem enorm_integral_mul_le (hp : 1 < p) {h φ : Euc d → ℝ} (hh : AEStronglyMeasurable h volume)
    (hφ : AEStronglyMeasurable φ volume) :
    ‖∫ x, h x * φ x‖ₑ ≤
      eLpNorm h (ENNReal.ofReal p) * eLpNorm φ (ENNReal.ofReal (Real.conjExponent p)) :=
  (enorm_integral_le_lintegral_enorm _).trans
    ((lintegral_mono fun _ => (enorm_mul _ _).le).trans (lintegral_enorm_mul_enorm_le hp hh hφ))

/-- `‖⟪a, b⟫‖ₑ ≤ ‖a‖ₑ ‖b‖ₑ`. -/
theorem enorm_real_inner_le (a b : Euc d) : ‖inner ℝ a b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm a b)

/-- `‖∫ ⟪h, v⟫ φ‖ ≤ ‖v‖ ‖h‖_{L^p} ‖φ‖_{L^q}`. -/
theorem enorm_integral_inner_mul_le (hp : 1 < p) {h : Euc d → Euc d}
    (hh : AEStronglyMeasurable h volume) {φ : Euc d → ℝ} (hφ : AEStronglyMeasurable φ volume)
    (v : Euc d) :
    ‖∫ x, inner ℝ (h x) v * φ x‖ₑ ≤
      ‖v‖ₑ * (eLpNorm h (ENNReal.ofReal p) * eLpNorm φ (ENNReal.ofReal (Real.conjExponent p))) :=
  calc ‖∫ x, inner ℝ (h x) v * φ x‖ₑ
      ≤ ∫⁻ x, ‖inner ℝ (h x) v * φ x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ‖v‖ₑ * (‖h x‖ₑ * ‖φ x‖ₑ) := lintegral_mono fun x => by
        rw [enorm_mul, ← mul_assoc, mul_comm ‖v‖ₑ]
        exact mul_le_mul_left (enorm_real_inner_le _ _) _
    _ = ‖v‖ₑ * ∫⁻ x, ‖h x‖ₑ * ‖φ x‖ₑ := lintegral_const_mul' _ _ enorm_ne_top
    _ ≤ _ := mul_le_mul_right (lintegral_enorm_mul_enorm_le hp hh hφ) _

/-- A convergence principle: if `‖A n - A∞‖ₑ ≤ E n` with `E n → 0`, then `A n → A∞`. -/
theorem tendsto_of_enorm_sub_le {A : ℕ → ℝ} {a : ℝ} {E : ℕ → ℝ≥0∞}
    (hE : Tendsto E atTop (𝓝 0)) (hle : ∀ n, ‖A n - a‖ₑ ≤ E n) : Tendsto A atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun n => (E n).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
  have hfin : ∀ᶠ n in atTop, E n < ⊤ := hE.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
    (Eventually.of_forall fun n => norm_nonneg _) (hfin.mono fun n hn => ?_)
  rw [← toReal_enorm (A n - a)]
  exact ENNReal.toReal_mono hn.ne (hle n)

/-- **Weak gradients pass to `L^p` limits**: if `u n → f` and `G n → g` in `L^p`, `1 < p`, with
`G n` a weak gradient of `u n`, then `g` is a weak gradient of `f`. This is the analytic core of
`W0_complete` (the remaining input being completeness of `L^p`). -/
theorem HasWeakGradient.of_tendsto (hp : 1 < p) {u : ℕ → Euc d → ℝ} {G : ℕ → Euc d → Euc d}
    (hu : ∀ n, HasWeakGradient (u n) (G n)) {f : Euc d → ℝ} {g : Euc d → Euc d}
    (hf : MemLp f (ENNReal.ofReal p)) (hg : MemLp g (ENNReal.ofReal p))
    (hfu : Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p)) atTop (𝓝 0))
    (hgG : Tendsto (fun n => eLpNorm (G n - g) (ENNReal.ofReal p)) atTop (𝓝 0)) :
    HasWeakGradient f g := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hfl : LocallyIntegrable f := hf.locallyIntegrable hp1
  have hgl : LocallyIntegrable g := hg.locallyIntegrable hp1
  refine ⟨hfl, hgl, fun ψ hψ hψs v => ?_⟩
  set q := Real.conjExponent p with hq
  set φ : Euc d → ℝ := fun x => fderiv ℝ ψ x v with hφ_def
  have hφc : Continuous φ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφs : HasCompactSupport φ :=
    (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
  have hφq : eLpNorm φ (ENNReal.ofReal q) ≠ ⊤ :=
    (hφc.memLp_of_hasCompactSupport hφs).eLpNorm_ne_top
  have hψq : eLpNorm ψ (ENNReal.ofReal q) ≠ ⊤ :=
    (hψ.continuous.memLp_of_hasCompactSupport hψs).eLpNorm_ne_top
  have int1 : ∀ h : Euc d → ℝ, LocallyIntegrable h → Integrable fun x => h x * φ x :=
    fun h hh => by
      simpa only [smul_eq_mul, mul_comm] using
        hh.integrable_smul_left_of_hasCompactSupport hφc hφs
  have int2 : ∀ h : Euc d → Euc d, LocallyIntegrable h →
      Integrable fun x => inner ℝ (h x) v * ψ x := fun h hh => by
    refine (Integrable.const_inner (𝕜 := ℝ) v
      (hh.integrable_smul_left_of_hasCompactSupport hψ.continuous hψs)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [inner_smul_right]
    rw [real_inner_comm, mul_comm]
  -- `∫ u n φ → ∫ f φ`
  have hA : Tendsto (fun n => ∫ x, u n x * φ x) atTop (𝓝 (∫ x, f x * φ x)) := by
    refine tendsto_of_enorm_sub_le (E := fun n =>
      eLpNorm (u n - f) (ENNReal.ofReal p) * eLpNorm φ (ENNReal.ofReal q))
      (by simpa using ENNReal.Tendsto.mul_const hfu (Or.inr hφq)) fun n => ?_
    rw [← integral_sub (int1 _ (hu n).locallyIntegrable) (int1 _ hfl)]
    have := enorm_integral_mul_le hp (h := u n - f)
      ((hu n).locallyIntegrable.aestronglyMeasurable.sub hf.aestronglyMeasurable)
      hφc.aestronglyMeasurable
    simpa only [Pi.sub_apply, sub_mul] using this
  -- `∫ ⟪G n, v⟫ ψ → ∫ ⟪g, v⟫ ψ`
  have hB : Tendsto (fun n => ∫ x, inner ℝ (G n x) v * ψ x) atTop
      (𝓝 (∫ x, inner ℝ (g x) v * ψ x)) := by
    have hE : Tendsto (fun n =>
        ‖v‖ₑ * (eLpNorm (G n - g) (ENNReal.ofReal p) * eLpNorm ψ (ENNReal.ofReal q)))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (a := ‖v‖ₑ)
        (ENNReal.Tendsto.mul_const hgG (Or.inr hψq)) (Or.inr enorm_ne_top)
    refine tendsto_of_enorm_sub_le hE fun n => ?_
    rw [← integral_sub (int2 _ (hu n).locallyIntegrable_grad) (int2 _ hgl)]
    have := enorm_integral_inner_mul_le hp (h := G n - g)
      ((hu n).locallyIntegrable_grad.aestronglyMeasurable.sub hg.aestronglyMeasurable)
      hψ.continuous.aestronglyMeasurable v
    simpa only [Pi.sub_apply, inner_sub_left, sub_mul] using this
  have heq : ∀ n, ∫ x, u n x * φ x = -∫ x, inner ℝ (G n x) v * ψ x := fun n =>
    (hu n).integral_mul_fderiv ψ hψ hψs v
  exact tendsto_nhds_unique hA (hB.neg.congr fun n => (heq n).symm)

end Closedness

/-! ### Completeness of `W₀^{1,p}(K)` -/

section Completeness

variable {p : ℝ}

/-- An `L^p`-Cauchy sequence of `MemLp` functions has an `L^p` limit (completeness of
`MeasureTheory.Lp`). -/
theorem exists_memLp_tendsto_of_cauchy {H : Type*} [NormedAddCommGroup H] [CompleteSpace H]
    {p' : ℝ≥0∞} (hp : 1 ≤ p') {v : ℕ → Euc d → H} (hv : ∀ n, MemLp (v n) p')
    (hcauchy : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      eLpNorm (v m - v n) p' < ε) :
    ∃ w : Euc d → H, MemLp w p' ∧ Tendsto (fun n => eLpNorm (v n - w) p') atTop (𝓝 0) := by
  have : Fact (1 ≤ p') := ⟨hp⟩
  set F : ℕ → Lp H p' (volume : Measure (Euc d)) := fun n => (hv n).toLp (v n) with hF
  have hF_cauchy : CauchySeq F := by
    refine EMetric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [hF, Lp.edist_toLp_toLp]
    exact hN m n hm hn
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hF_cauchy
  refine ⟨G, Lp.memLp G, ?_⟩
  rw [← Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv G (Lp.memLp G), Lp.toLp_coeFn]
  exact hG

/-- **Completeness of `W₀^{1,p}(K)` under the graph norm**: a sequence in `W₀^{1,p}(K)` that is
Cauchy for `‖·‖_{L^p} + ‖∇·‖_{L^p}` converges in that norm to some `f ∈ W₀^{1,p}(K)`
(completeness of `L^p` plus `HasWeakGradient.of_tendsto`). -/
theorem W0_complete (hp : 1 < p) {K : Set (Euc d)} (u : ℕ → Euc d → ℝ)
    (hu : ∀ n, MemW0 p K (u n))
    (hcauchy : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      eLpNorm (u m - u n) (ENNReal.ofReal p) +
        eLpNorm (weakGrad (u m) - weakGrad (u n)) (ENNReal.ofReal p) < ε) :
    ∃ f : Euc d → ℝ, MemW0 p K f ∧
      Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p) +
        eLpNorm (weakGrad (u n) - weakGrad f) (ENNReal.ofReal p)) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using (zero_lt_one.trans hp)
  obtain ⟨f, hf, hfu⟩ := exists_memLp_tendsto_of_cauchy hp1 (fun n => (hu n).memLp)
    fun ε hε => (hcauchy ε hε).imp fun N hN m n hm hn => lt_of_le_of_lt le_self_add (hN m n hm hn)
  obtain ⟨g, hg, hgG⟩ := exists_memLp_tendsto_of_cauchy hp1 (fun n => (hu n).memLp_weakGrad)
    fun ε hε => (hcauchy ε hε).imp fun N hN m n hm hn => lt_of_le_of_lt le_add_self (hN m n hm hn)
  have hwg : HasWeakGradient f g :=
    HasWeakGradient.of_tendsto hp (fun n => (hu n).hasWeakGradient) hf hg hfu hgG
  -- the limit vanishes a.e. outside `K` (along an a.e.-convergent subsequence)
  have hvanish : ∀ᵐ x, x ∉ K → f x = 0 := by
    obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp'
      (fun n => (hu n).memLp.aestronglyMeasurable) hf.aestronglyMeasurable
      hfu).exists_seq_tendsto_ae
    filter_upwards [hae, ae_all_iff.2 fun n => (hu n).ae_eq_zero] with x hx hzero hxK
    exact tendsto_nhds_unique (hx.congr fun i => hzero (ns i) hxK) tendsto_const_nhds
  refine ⟨f, ⟨hf, hvanish, g, hwg, hg⟩, ?_⟩
  have hgrad : Tendsto (fun n => eLpNorm (weakGrad (u n) - weakGrad f) (ENNReal.ofReal p)) atTop
      (𝓝 0) := by
    refine hgG.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [hwg.weakGrad_ae_eq] with x hx
    simp [hx]
  simpa using hfu.add hgrad

end Completeness

end Komlos.Literature
