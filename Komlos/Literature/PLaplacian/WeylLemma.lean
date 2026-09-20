import Komlos.Literature.PLaplacian.HarmonicMVP
import Komlos.Literature.Sobolev.Defs

/-!
# Weyl's lemma on `ℝ^d` for a constant symmetric elliptic operator

A *distributional* solution of `div (A₀ ∇u) = 0` on an open set `U` — a function `u ∈ W^{1,1}_loc`
with weak gradient `G` satisfying `∫ ⟪A₀ G, ∇ψ⟫ = 0` for every `ψ ∈ C_c^∞(U)` — is almost
everywhere equal, near every point of `U`, to a `C^∞` function.

Nothing in the repository previously upgraded an `L¹` field to the gradient of a smooth function;
this file supplies that step, the missing regularity input of
`Komlos.Literature.exists_frozen_replacement_data`.

## The route

Mollification turns the problem into one about smooth functions, which
`Komlos.Literature.PLaplacian.HarmonicMVP` already handles.

* `integral_bilin_mollifyWith_left` — **the adjoint identity** `∫ L (ρ ⋆ g) V = ∫ L g (ρ̌ ⋆ V)`
  (Fubini; `ρ̌ z = ρ (-z)`), stated for a bilinear pairing `L` so that it covers both the product
  of scalars and the inner product of `ℝ^d`.
* `mollifyWith_mollifyWith_comm` — mollifications commute, an immediate consequence.
* `integral_inner_gradient_mollifyWith_eq_zero` — **the mollified function solves the same
  equation** on the `ε`-interior: `∇(ρ ⋆ u) = ρ ⋆ G` (`gradient_mollifyWith`), and the adjoint
  identity moves `ρ` onto the test function, where `ρ̌ ⋆ ψ` is again admissible.
* `integral_mvpKernel_mul_comp_eq_of_contDiff` — the **mean value property** of
  `integral_mvpKernel_mul_comp_eq`, freed of its global compact-support hypothesis by a cutoff.
* `exists_contDiff_ae_eq_of_weakSolution` — **Weyl's lemma.**  The mean value property reads
  `(∫ χ_S) (ρ_n ⋆ u) = ρ_n ⋆ (K ⋆ u)` on a ball, for a *fixed* smooth compactly supported kernel
  `K = χ_S(-(·)/s)`; letting `n → ∞` along the standard mollifiers and using Lebesgue
  differentiation (`ae_tendsto_convolution_stdBump`) on both sides gives `(∫ χ_S) u = K ⋆ u`
  almost everywhere, and `K ⋆ u` is `C^∞` because `K` is.  No compactness argument
  (Arzelà–Ascoli) is needed: the smooth representative is produced by an explicit formula.
* `weakGrad_ae_eq_gradient_of_ae_eq` — the companion statement that the weak gradient is a.e. the
  classical gradient of that smooth representative.
* `exists_contDiff_ae_eq_gradient_of_weakSolution` — the two combined, which is the form the
  Campanato iteration consumes.
-/

open MeasureTheory Set Filter Topology InnerProductSpace

open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### The adjoint of a mollification -/

/-- **The adjoint identity for mollification.**  For a bilinear pairing `L`, moving the kernel of
a mollification from one factor to the other replaces it by its reflection `ρ̌ z = ρ (-z)`:
`∫ L (ρ ⋆ g) V = ∫ L g (ρ̌ ⋆ V)`.

This is Fubini's theorem.  The double integrand `ρ (y - t) L (g t) (V y)` vanishes unless
`y ∈ tsupport V` and `t` lies in a fixed ball, so it is dominated by the product
`(C ‖V y‖) · (‖g t‖ 1_B t)` of two integrable functions of the separate variables. -/
theorem integral_bilin_mollifyWith_left {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F →L[ℝ] ℝ) {g : Euc d → E} (hg : LocallyIntegrable g)
    {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hρs : HasCompactSupport ρ)
    {V : Euc d → F} (hV : Continuous V) (hVs : HasCompactSupport V) :
    ∫ y, L (mollifyWith ρ g y) (V y) = ∫ t, L (g t) (mollifyWith (fun z => ρ (-z)) V t) := by
  obtain ⟨Cρ, hCρ⟩ := hρ.bounded_above_of_compact_support hρs
  have hCρ0 : (0 : ℝ) ≤ Cρ := (norm_nonneg _).trans (hCρ 0)
  obtain ⟨Rv, hRv⟩ := hVs.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨Rr, hRr⟩ := hρs.isBounded.subset_closedBall (0 : Euc d)
  have hVzero : ∀ y : Euc d, y ∉ Metric.closedBall (0 : Euc d) Rv → V y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hc => hy (hRv hc)
  -- the reflected kernel, written out
  have hrefl : ∀ t : Euc d, mollifyWith (fun z : Euc d => ρ (-z)) V t = ∫ y, ρ (y - t) • V y := by
    intro t
    simp only [mollifyWith, neg_sub]
  -- the two one-variable identities
  have hL1 : ∀ y : Euc d, L (mollifyWith ρ g y) (V y) = ∫ t, ρ (y - t) * L (g t) (V y) := by
    intro y
    have hi : Integrable fun t => ρ (y - t) • g t :=
      integrable_mollifyWith_integrand hρ hρs hg y
    have hT := (L.flip (V y)).integral_comp_comm hi
    have hpt : ∀ t : Euc d, (L.flip (V y)) (ρ (y - t) • g t) = ρ (y - t) * L (g t) (V y) := by
      intro t
      rw [map_smul, ContinuousLinearMap.flip_apply, smul_eq_mul]
    simp only [hpt] at hT
    rw [hT, ContinuousLinearMap.flip_apply, mollifyWith]
  have hL2 : ∀ t : Euc d,
      ∫ y, ρ (y - t) * L (g t) (V y) = L (g t) (mollifyWith (fun z : Euc d => ρ (-z)) V t) := by
    intro t
    have hcont : Continuous fun y : Euc d => ρ (y - t) • V y :=
      (hρ.comp (continuous_id.sub continuous_const)).smul hV
    have hsupp : HasCompactSupport fun y : Euc d => ρ (y - t) • V y := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) Rv) fun y hy => ?_
      rw [hVzero y hy, smul_zero]
    have hi : Integrable fun y => ρ (y - t) • V y :=
      hcont.integrable_of_hasCompactSupport hsupp
    have hT := (L (g t)).integral_comp_comm hi
    have hpt : ∀ y : Euc d, (L (g t)) (ρ (y - t) • V y) = ρ (y - t) * L (g t) (V y) := by
      intro y
      rw [map_smul, smul_eq_mul]
    simp only [hpt] at hT
    rw [hT, hrefl t]
  -- the domination needed for Fubini
  have hvanish : ∀ p : Euc d × Euc d, p.2 ∉ Metric.closedBall (0 : Euc d) (Rv + Rr) →
      ρ (p.1 - p.2) * L (g p.2) (V p.1) = 0 := by
    intro p hp
    by_contra hne
    have h1 : ρ (p.1 - p.2) ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : V p.1 ≠ 0 := fun h => hne (by rw [h, map_zero, mul_zero])
    have hρmem := hRr (subset_tsupport ρ (Function.mem_support.2 h1))
    have hVmem := hRv (subset_tsupport V (Function.mem_support.2 h2))
    rw [Metric.mem_closedBall, dist_zero_right] at hρmem hVmem
    refine hp ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖p.2‖ = ‖p.1 - (p.1 - p.2)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖p.1‖ + ‖p.1 - p.2‖ := norm_sub_le _ _
      _ ≤ Rv + Rr := add_le_add hVmem hρmem
  have hmeas : AEStronglyMeasurable
      (fun p : Euc d × Euc d => ρ (p.1 - p.2) * L (g p.2) (V p.1)) (volume.prod volume) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hρ.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    · exact L.aestronglyMeasurable_comp₂
        (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
        (hV.comp continuous_fst).aestronglyMeasurable
  have hF : Integrable fun y : Euc d => Cρ * ‖L‖ * ‖V y‖ := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_const.mul hV.norm) ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) Rv) fun y hy => ?_
    rw [hVzero y hy, norm_zero, mul_zero]
  have hH : Integrable
      ((Metric.closedBall (0 : Euc d) (Rv + Rr)).indicator fun t => ‖g t‖) :=
    IntegrableOn.integrable_indicator
      ((hg.integrableOn_isCompact (isCompact_closedBall (0 : Euc d) (Rv + Rr))).norm)
      measurableSet_closedBall
  have hdom : Integrable (fun p : Euc d × Euc d => (Cρ * ‖L‖ * ‖V p.1‖) *
      (Metric.closedBall (0 : Euc d) (Rv + Rr)).indicator (fun t => ‖g t‖) p.2)
      (volume.prod volume) := Integrable.mul_prod hF hH
  have hbound : ∀ᵐ p : Euc d × Euc d ∂(volume.prod volume),
      ‖ρ (p.1 - p.2) * L (g p.2) (V p.1)‖ ≤ (Cρ * ‖L‖ * ‖V p.1‖) *
        (Metric.closedBall (0 : Euc d) (Rv + Rr)).indicator (fun t => ‖g t‖) p.2 := by
    refine Eventually.of_forall fun p => ?_
    by_cases hp : p.2 ∈ Metric.closedBall (0 : Euc d) (Rv + Rr)
    · rw [Set.indicator_of_mem hp]
      calc ‖ρ (p.1 - p.2) * L (g p.2) (V p.1)‖
          = ‖ρ (p.1 - p.2)‖ * ‖L (g p.2) (V p.1)‖ := norm_mul _ _
        _ ≤ Cρ * (‖L‖ * ‖g p.2‖ * ‖V p.1‖) :=
            mul_le_mul (hCρ _) (L.le_opNorm₂ _ _) (norm_nonneg _) hCρ0
        _ = Cρ * ‖L‖ * ‖V p.1‖ * ‖g p.2‖ := by ring
    · simp only [Set.indicator_of_notMem hp, mul_zero, hvanish p hp, norm_zero]
      exact le_rfl
  have hint : Integrable (Function.uncurry
      fun y t : Euc d => ρ (y - t) * L (g t) (V y)) (volume.prod volume) :=
    hdom.mono' hmeas hbound
  calc ∫ y, L (mollifyWith ρ g y) (V y)
      = ∫ y, ∫ t, ρ (y - t) * L (g t) (V y) := integral_congr_ae (Eventually.of_forall hL1)
    _ = ∫ t, ∫ y, ρ (y - t) * L (g t) (V y) := integral_integral_swap hint
    _ = ∫ t, L (g t) (mollifyWith (fun z : Euc d => ρ (-z)) V t) :=
        integral_congr_ae (Eventually.of_forall hL2)

/-- The scalar form of the adjoint identity: `∫ (ρ ⋆ f) b = ∫ f (ρ̌ ⋆ b)`. -/
theorem integral_mul_mollifyWith_left {f : Euc d → ℝ} (hf : LocallyIntegrable f)
    {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hρs : HasCompactSupport ρ)
    {b : Euc d → ℝ} (hb : Continuous b) (hbs : HasCompactSupport b) :
    ∫ y, mollifyWith ρ f y * b y = ∫ t, f t * mollifyWith (fun z => ρ (-z)) b t := by
  have h := integral_bilin_mollifyWith_left (ContinuousLinearMap.lsmul ℝ ℝ) hf hρ hρs hb hbs
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h

/-- The inner-product form of the adjoint identity: `∫ ⟪ρ ⋆ g, V⟫ = ∫ ⟪g, ρ̌ ⋆ V⟫`. -/
theorem integral_inner_mollifyWith_left {g : Euc d → Euc d} (hg : LocallyIntegrable g)
    {ρ : Euc d → ℝ} (hρ : Continuous ρ) (hρs : HasCompactSupport ρ)
    {V : Euc d → Euc d} (hV : Continuous V) (hVs : HasCompactSupport V) :
    ∫ y, ⟪mollifyWith ρ g y, V y⟫ = ∫ t, ⟪g t, mollifyWith (fun z => ρ (-z)) V t⟫ := by
  have h := integral_bilin_mollifyWith_left (innerSL ℝ (E := Euc d)) hg hρ hρs hV hVs
  -- `innerSL ℝ a b` and `⟪ a, b ⟫` are definitionally equal (`innerSL_apply_apply` is `rfl`),
  -- so `exact` closes the gap; mathlib's `fourierIntegral_convergent_iff` does the same.
  exact h

/-- `mollifyWith κ h y = ∫ h t · κ (y - t)`: the mollification with the factors in the order in
which the adjoint identity consumes them. -/
theorem mollifyWith_eq_integral_mul (κ h : Euc d → ℝ) (y : Euc d) :
    mollifyWith κ h y = ∫ t, h t * κ (y - t) := by
  rw [mollifyWith]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  -- beta-reduce first: `rw` cannot see through `(fun t => _) t`
  show κ (y - t) • h t = h t * κ (y - t)
  rw [smul_eq_mul, mul_comm]

/-- **Mollifications commute**: `K ⋆ (ρ ⋆ f) = ρ ⋆ (K ⋆ f)`.  Both sides equal
`∫ f z (∫ ρ (t - z) K (y - t) dt) dz` by the adjoint identity, and the two inner integrals agree
after the substitution `t ↦ y + z - t`. -/
theorem mollifyWith_mollifyWith_comm {f : Euc d → ℝ} (hf : LocallyIntegrable f)
    {ρ K : Euc d → ℝ} (hρ : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hK : Continuous K) (hKs : HasCompactSupport K) :
    mollifyWith K (mollifyWith ρ f) = mollifyWith ρ (mollifyWith K f) := by
  funext x
  have hbK : Continuous fun t : Euc d => K (x - t) :=
    hK.comp (continuous_const.sub continuous_id)
  have hbKs : HasCompactSupport fun t : Euc d => K (x - t) :=
    hKs.comp_homeomorph (Homeomorph.subLeft x)
  have hbρ : Continuous fun t : Euc d => ρ (x - t) :=
    hρ.comp (continuous_const.sub continuous_id)
  have hbρs : HasCompactSupport fun t : Euc d => ρ (x - t) :=
    hρs.comp_homeomorph (Homeomorph.subLeft x)
  have key : ∀ z : Euc d,
      mollifyWith (fun w : Euc d => ρ (-w)) (fun t : Euc d => K (x - t)) z =
        mollifyWith (fun w : Euc d => K (-w)) (fun t : Euc d => ρ (x - t)) z := by
    intro z
    have h1 : mollifyWith (fun w : Euc d => ρ (-w)) (fun t : Euc d => K (x - t)) z =
        ∫ t, ρ (t - z) * K (x - t) := by
      simp only [mollifyWith, neg_sub, smul_eq_mul]
    have h2 : mollifyWith (fun w : Euc d => K (-w)) (fun t : Euc d => ρ (x - t)) z =
        ∫ t, K (t - z) * ρ (x - t) := by
      simp only [mollifyWith, neg_sub, smul_eq_mul]
    have h3 := integral_sub_left_eq_self
      (fun t : Euc d => ρ (t - z) * K (x - t)) volume (x + z)
    have he : ∀ t : Euc d,
        ρ (x + z - t - z) * K (x - (x + z - t)) = K (t - z) * ρ (x - t) := by
      intro t
      have e1 : x + z - t - z = x - t := by abel
      have e2 : x - (x + z - t) = t - z := by abel
      rw [e1, e2, mul_comm]
    simp only [he] at h3
    rw [h1, h2]
    exact h3.symm
  rw [mollifyWith_eq_integral_mul K (mollifyWith ρ f) x,
    mollifyWith_eq_integral_mul ρ (mollifyWith K f) x,
    integral_mul_mollifyWith_left hf hρ hρs hbK hbKs,
    integral_mul_mollifyWith_left hf hK hKs hbρ hbρs]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  -- beta-reduce first: `rw` cannot see through `(fun t => _) z`
  show f z * mollifyWith (fun w : Euc d => ρ (-w)) (fun t : Euc d => K (x - t)) z =
    f z * mollifyWith (fun w : Euc d => K (-w)) (fun t : Euc d => ρ (x - t)) z
  rw [key z]

/-- Mollifications of a locally integrable `f` by the standard bumps converge to `f` a.e.
(the `mollifyWith` form of `ae_tendsto_convolution_stdBump`). -/
theorem ae_tendsto_mollifyWith_stdBump {f : Euc d → ℝ} (hf : LocallyIntegrable f) :
    ∀ᵐ x : Euc d, Tendsto
      (fun n => mollifyWith ((mollifierBump n).normed volume) f x) atTop (𝓝 (f x)) := by
  filter_upwards [ae_tendsto_convolution_stdBump hf] with x hx
  simpa only [mollifyWith_eq_convolution_right] using hx

/-! ### The mollified function solves the same equation -/

/-- **The mollification of a distributional solution is a solution on the `ε`-interior.**
`∇(ρ ⋆ u) = ρ ⋆ G` (`gradient_mollifyWith`), and the adjoint identity moves the kernel onto the
test function: `∫ ⟪A₀ (ρ ⋆ G), ∇ψ⟫ = ∫ ⟪A₀ G, ∇(ρ̌ ⋆ ψ)⟫`, where `ρ̌ ⋆ ψ` is supported in
`B̄(c, a + ε) ⊆ B̄(c, b) ⊆ U` and is therefore admissible. -/
theorem integral_inner_gradient_mollifyWith_eq_zero
    {A₀ : Euc d →L[ℝ] Euc d} {U : Set (Euc d)} {u : Euc d → ℝ} {G : Euc d → Euc d}
    (hG : HasWeakGradient u G)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ y, ⟪A₀ (G y), gradient ψ y⟫ = 0)
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρs : HasCompactSupport ρ)
    {ε : ℝ} (hρsupp : Function.support ρ ⊆ Metric.closedBall 0 ε)
    {c : Euc d} {a b : ℝ} (hab : a + ε ≤ b) (hbU : Metric.closedBall c b ⊆ U)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Metric.closedBall c a) :
    ∫ y, ⟪A₀ (gradient (mollifyWith ρ u) y), gradient ψ y⟫ = 0 := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  -- the reflected kernel
  have hρ'c : ContDiff ℝ ∞ (fun z : Euc d => ρ (-z)) := by
    have h : ContDiff ℝ ∞ (ρ ∘ fun z : Euc d => -z) := hρ.comp contDiff_neg
    exact h
  have hρ's : HasCompactSupport (fun z : Euc d => ρ (-z)) :=
    hρs.comp_homeomorph (Homeomorph.neg (Euc d))
  -- the mollified test function vanishes off `B̄(c, b)`
  have hφzero : ∀ w : Euc d, w ∉ Metric.closedBall c b →
      mollifyWith (fun z : Euc d => ρ (-z)) ψ w = 0 := by
    intro w hw
    have hz : ∀ t : Euc d, ρ (-(w - t)) • ψ t = (0 : ℝ) := by
      intro t
      by_cases h1 : ρ (-(w - t)) = 0
      · rw [h1, zero_smul]
      · have hε : ‖w - t‖ ≤ ε := by
          have h := hρsupp (Function.mem_support.2 h1)
          rw [Metric.mem_closedBall, dist_zero_right, norm_neg] at h
          exact h
        have hψt : ψ t = 0 := by
          by_contra h2
          have ht : dist t c ≤ a := by
            have hmem := hψsupp (subset_tsupport ψ (Function.mem_support.2 h2))
            rwa [Metric.mem_closedBall] at hmem
          refine hw ?_
          rw [Metric.mem_closedBall]
          calc dist w c ≤ dist w t + dist t c := dist_triangle _ _ _
            _ ≤ ε + a := add_le_add (by rwa [dist_eq_norm]) ht
            _ ≤ b := by linarith
        rw [hψt, smul_zero]
    have hzero : mollifyWith (fun z : Euc d => ρ (-z)) ψ w = ∫ _t : Euc d, (0 : ℝ) := by
      rw [mollifyWith]
      exact integral_congr_ae (Eventually.of_forall hz)
    rw [hzero, integral_zero]
  have hφsupp : Function.support (mollifyWith (fun z : Euc d => ρ (-z)) ψ)
      ⊆ Metric.closedBall c b := by
    intro w hw
    by_contra hcon
    exact (Function.mem_support.1 hw) (hφzero w hcon)
  have hφs : HasCompactSupport (mollifyWith (fun z : Euc d => ρ (-z)) ψ) :=
    HasCompactSupport.intro (isCompact_closedBall c b) fun w hw => hφzero w hw
  have hφU : tsupport (mollifyWith (fun z : Euc d => ρ (-z)) ψ) ⊆ U :=
    (closure_minimal hφsupp Metric.isClosed_closedBall).trans hbU
  have hφc : ContDiff ℝ ∞ (mollifyWith (fun z : Euc d => ρ (-z)) ψ) :=
    contDiff_mollifyWith (n := ⊤) hρ'c hρ's hψ.continuous.locallyIntegrable
  -- `A₀` passes through the mollification
  have hA : ∀ y : Euc d, A₀ (mollifyWith ρ G y) = mollifyWith ρ (fun t => A₀ (G t)) y := by
    intro y
    have hi : Integrable fun t => ρ (y - t) • G t :=
      integrable_mollifyWith_integrand hρ.continuous hρs hG.locallyIntegrable_grad y
    simp only [mollifyWith]
    rw [← A₀.integral_comp_comm hi]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    -- beta-reduce first: `rw` cannot see through `(fun x => _) t`
    show A₀ (ρ (y - t) • G t) = ρ (y - t) • A₀ (G t)
    rw [map_smul]
  have hgA : LocallyIntegrable fun t => A₀ (G t) := by
    intro z
    obtain ⟨t, ht, hint⟩ := hG.locallyIntegrable_grad z
    exact ⟨t, ht, A₀.integrable_comp hint⟩
  have hstep : ∀ y : Euc d, ⟪A₀ (mollifyWith ρ G y), gradient ψ y⟫ =
      ⟪mollifyWith ρ (fun t => A₀ (G t)) y, gradient ψ y⟫ := fun y => by rw [hA y]
  -- the chain of identities
  have hkey : ∫ y, ⟪A₀ (gradient (mollifyWith ρ u) y), gradient ψ y⟫ =
      ∫ t, ⟪A₀ (G t), gradient (mollifyWith (fun z : Euc d => ρ (-z)) ψ) t⟫ := by
    rw [gradient_mollifyWith hG hρ hρs, integral_congr_ae (Eventually.of_forall hstep),
      integral_inner_mollifyWith_left hgA hρ.continuous hρs (continuous_gradient hψ1)
        (hasCompactSupport_gradient hψs),
      gradient_mollifyWith (hasWeakGradient_gradient hψ1 hψs) hρ'c hρ's]
  rw [hkey]
  exact hsol _ hφc hφs hφU

/-! ### The mean value property without a global support hypothesis -/

/-- **The mean value property for a `C^∞` local solution.**  `integral_mvpKernel_mul_comp_eq`
asks for a globally `C¹`, compactly supported solution; cutting `v` off by a bump which is `1` on
`B̄(c, R)` produces such a function without changing the equation on `B(c, R)` nor the values of
`v` on the ball swept out by the kernel. -/
theorem integral_mvpKernel_mul_comp_eq_of_contDiff
    {A S : Euc d →L[ℝ] Euc d} (hSsymm : ∀ p q : Euc d, ⟪S p, q⟫ = ⟪p, S q⟫)
    (hSA : ∀ w : Euc d, S (A w) = w)
    {α : ℝ} (hα : 0 < α) (hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w)
    {v : Euc d → ℝ} (hv : ContDiff ℝ ∞ v) {c : Euc d} {R : ℝ} (hR : 0 < R)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball c R → ∫ y, ⟪A (gradient v y), gradient ψ y⟫ = 0)
    {x : Euc d} {s : ℝ} (hs : 0 < s)
    (hball : Metric.closedBall x (s * mvpRadius α) ⊆ Metric.ball c R) :
    ∫ w, mvpKernel S w * v (x + s • w) = (∫ w, mvpKernel S w) * v x := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by simp)
  obtain ⟨η, hηin, _hηout⟩ : ∃ η : ContDiffBump c, η.rIn = R ∧ η.rOut = R + 1 :=
    ⟨⟨R, R + 1, hR, by linarith⟩, rfl, rfl⟩
  have hη1 : ∀ z : Euc d, z ∈ Metric.closedBall c R → (η : Euc d → ℝ) z = 1 := by
    intro z hz
    exact η.one_of_mem_closedBall (by rw [hηin]; exact hz)
  -- the cut-off solution
  have hhc : ContDiff ℝ 1 fun y : Euc d => (η : Euc d → ℝ) y * v y :=
    (η.contDiff (n := 1)).mul hv1
  have hhs : HasCompactSupport fun y : Euc d => (η : Euc d → ℝ) y * v y := by
    refine HasCompactSupport.intro (isCompact_closedBall c η.rOut) fun y hy => ?_
    have hz : (η : Euc d → ℝ) y = 0 := by
      refine image_eq_zero_of_notMem_tsupport ?_
      rw [η.tsupport_eq]
      exact hy
    rw [hz, zero_mul]
  have hgradh : ∀ y ∈ Metric.ball c R,
      gradient (fun z : Euc d => (η : Euc d → ℝ) z * v z) y = gradient v y := by
    intro y hy
    refine Filter.EventuallyEq.gradient_eq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    rw [hη1 z (Metric.ball_subset_closedBall hz), one_mul]
  have hsolh : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball c R →
      ∫ y, ⟪A (gradient (fun z : Euc d => (η : Euc d → ℝ) z * v z) y), gradient ψ y⟫ = 0 := by
    intro ψ hψ hψs hψsupp
    have hpt : ∀ y : Euc d,
        ⟪A (gradient (fun z : Euc d => (η : Euc d → ℝ) z * v z) y), gradient ψ y⟫ =
          ⟪A (gradient v y), gradient ψ y⟫ := by
      intro y
      by_cases hy : y ∈ Metric.ball c R
      · rw [hgradh y hy]
      · have hyt : y ∉ tsupport ψ := fun h => hy (hψsupp h)
        have hψ0 : ψ =ᶠ[𝓝 y] fun _ : Euc d => (0 : ℝ) := by
          filter_upwards [(isOpen_compl_iff.2
            (isClosed_closure (s := Function.support ψ))).mem_nhds hyt] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        rw [hψ0.gradient_eq, gradient_fun_const]
        simp
    rw [integral_congr_ae (Eventually.of_forall hpt)]
    exact hsol ψ hψ hψs hψsupp
  have hmvp := integral_mvpKernel_mul_comp_eq hSsymm hSA hα hQ hhc hhs hsolh hs hball
  -- undo the cut-off
  have hxmem : x ∈ Metric.closedBall c R :=
    Metric.ball_subset_closedBall
      (hball (Metric.mem_closedBall_self (mul_nonneg hs.le (mvpRadius_pos hα).le)))
  have hpt : ∀ w : Euc d,
      mvpKernel S w * ((η : Euc d → ℝ) (x + s • w) * v (x + s • w)) =
        mvpKernel S w * v (x + s • w) := by
    intro w
    by_cases hw : mvpKernel S w = 0
    · rw [hw, zero_mul, zero_mul]
    · have hwle : ‖w‖ ≤ mvpRadius α := by
        have h := support_mvpKernel_subset hα hQ (Function.mem_support.2 hw)
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have hmem : x + s • w ∈ Metric.closedBall x (s * mvpRadius α) := by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos hs]
        exact mul_le_mul_of_nonneg_left hwle hs.le
      rw [hη1 _ (Metric.ball_subset_closedBall (hball hmem)), one_mul]
  rw [integral_congr_ae (Eventually.of_forall hpt), hη1 x hxmem, one_mul] at hmvp
  exact hmvp

/-! ### Weyl's lemma -/

/-- **Weyl's lemma on `ℝ^d` for a constant symmetric elliptic operator.**  If `u ∈ W^{1,1}_loc`
has weak gradient `G` and `∫ ⟪A₀ G, ∇ψ⟫ = 0` for every `ψ ∈ C_c^∞(U)`, with `A₀` a constant
symmetric `μ`-elliptic matrix, then near every point of the open set `U` the function `u` agrees
almost everywhere with a `C^∞` function.

The smooth representative is explicit: a fixed multiple of the mollification of `u` by the
mean-value kernel `χ_S(-(·)/s)` at one fixed scale `s`. -/
theorem exists_contDiff_ae_eq_of_weakSolution
    {A₀ : Euc d →L[ℝ] Euc d} (hsymm : ∀ p q : Euc d, ⟪A₀ p, q⟫ = ⟪p, A₀ q⟫)
    {μ : ℝ} (hμ : 0 < μ) (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    {U : Set (Euc d)} (hU : IsOpen U) {u : Euc d → ℝ} {G : Euc d → Euc d}
    (hG : HasWeakGradient u G)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ y, ⟪A₀ (G y), gradient ψ y⟫ = 0)
    {x₀ : Euc d} (hx₀ : x₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x₀ r ⊆ U ∧ ∃ v : Euc d → ℝ, ContDiff ℝ ∞ v ∧
      ∀ᵐ x, x ∈ Metric.ball x₀ r → u x = v x := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `Euc 0` is a single point: every function on it is smooth.
    refine ⟨1, one_pos, ?_, u, ?_, Eventually.of_forall fun _ _ => rfl⟩
    · intro z _
      have hzx : z = x₀ := by rw [eq_zero_of_dim_zero z, eq_zero_of_dim_zero x₀]
      rw [hzx]
      exact hx₀
    · have hconst : u = fun _ : Euc 0 => u 0 :=
        funext fun z => by rw [eq_zero_of_dim_zero z]
      rw [hconst]
      exact contDiff_const
  obtain ⟨R, hR0, hRU⟩ : ∃ R > 0, Metric.ball x₀ R ⊆ U := Metric.isOpen_iff.1 hU x₀ hx₀
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = R / 8 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hr3R : 3 * r < R := by rw [hrdef]; linarith
  -- the inverse of `A₀` and the elliptic bump
  obtain ⟨S, hSsymm, hSA, hSn, hQ0⟩ := exists_inverse_of_symmetric_elliptic hμ A₀ hsymm hell
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = μ / (‖A₀‖ + 1) ^ 2 := ⟨_, rfl⟩
  have hα : 0 < α := by
    rw [hαdef]
    exact div_pos hμ (pow_pos (by positivity) 2)
  have hQ : ∀ w : Euc d, α * ‖w‖ ^ 2 ≤ ellQuad S w := by
    intro w
    rw [hαdef]
    exact hQ0 w
  have hρ₀ : 0 < mvpRadius α := mvpRadius_pos hα
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = r / mvpRadius α := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; exact div_pos hr0 hρ₀
  have hsr : s * mvpRadius α = r := by rw [hsdef]; exact div_mul_cancel₀ r hρ₀.ne'
  -- the mean value kernel has negative total mass
  obtain ⟨e, hedef⟩ : ∃ w : Euc d, w = EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) := ⟨_, rfl⟩
  have he : e ≠ 0 := by
    rw [hedef]
    intro hcon
    have h1 : (1 : ℝ) = 0 := EuclideanSpace.single_eq_zero_iff.1 hcon
    norm_num at h1
  obtain ⟨κ, hκ0, hκ⟩ := exists_integral_mvpKernel_le_neg d hα (one_div_pos.2 hμ) he
  have hcneg : (∫ w, mvpKernel S w) ≤ -κ := hκ S hSsymm hQ hSn
  have hcne : (∫ w, mvpKernel S w) ≠ 0 := by
    intro h
    rw [h] at hcneg
    linarith
  -- the fixed smooth kernel `K`
  obtain ⟨K, hKdef⟩ : ∃ K : Euc d → ℝ, K = fun z => mvpKernel S (s⁻¹ • (-z)) := ⟨_, rfl⟩
  have hKcd : ContDiff ℝ ∞ K := by
    rw [hKdef]
    have h : ContDiff ℝ ∞ (mvpKernel S ∘ fun z : Euc d => s⁻¹ • (-z)) :=
      (contDiff_mvpKernel S).comp (contDiff_neg.const_smul s⁻¹)
    exact h
  have hKc : Continuous K := hKcd.continuous
  have hKsupp : Function.support K ⊆ Metric.closedBall 0 r := by
    intro z hz
    have hz' : mvpKernel S (s⁻¹ • (-z)) ≠ 0 := by
      have hmem := Function.mem_support.1 hz
      rwa [hKdef] at hmem
    have h := support_mvpKernel_subset hα hQ (Function.mem_support.2 hz')
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, norm_neg,
      abs_of_pos (inv_pos.2 hs)] at h
    rw [Metric.mem_closedBall, dist_zero_right, ← hsr]
    have hss : s * (s⁻¹ * ‖z‖) ≤ s * mvpRadius α := mul_le_mul_of_nonneg_left h hs.le
    rwa [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hss
  have hKs : HasCompactSupport K :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) r) fun z hz => by
      by_contra hne
      exact hz (hKsupp (Function.mem_support.2 hne))
  have hKapply : ∀ y t : Euc d, K (y - t) = mvpKernel S (s⁻¹ • (t - y)) := by
    intro y t
    simp only [hKdef, neg_sub]
  have hmollK : ∀ (f : Euc d → ℝ) (y : Euc d),
      mollifyWith K f y = ∫ t, mvpKernel S (s⁻¹ • (t - y)) * f t := by
    intro f y
    rw [mollifyWith]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    -- beta-reduce first: `rw` cannot see through `(fun t => _) t`
    show K (y - t) • f t = mvpKernel S (s⁻¹ • (t - y)) * f t
    rw [smul_eq_mul, hKapply y t]
  -- the standard mollifiers
  have hρc : ∀ n : ℕ, ContDiff ℝ ∞ ((mollifierBump (d := d) n).normed volume) :=
    fun _ => ContDiffBump.contDiff_normed _
  have hρs : ∀ n : ℕ, HasCompactSupport ((mollifierBump (d := d) n).normed volume) :=
    fun n => (mollifierBump n).hasCompactSupport_normed
  have hrOut : ∀ n : ℕ, (mollifierBump (d := d) n).rOut = 1 / ((n : ℝ) + 1) := fun _ => rfl
  have hρsupp : ∀ n : ℕ, Function.support ((mollifierBump (d := d) n).normed volume)
      ⊆ Metric.closedBall 0 (1 / ((n : ℝ) + 1)) := by
    intro n
    rw [ContDiffBump.support_normed_eq, hrOut n]
    exact Metric.ball_subset_closedBall
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / ((N : ℝ) + 1) < r := exists_nat_one_div_lt hr0
  -- the key identity, for every large `n` and every point of the small ball
  have hkey : ∀ n : ℕ, N ≤ n → ∀ x ∈ Metric.ball x₀ r,
      |(s ^ d)⁻¹| * mollifyWith ((mollifierBump n).normed volume) (mollifyWith K u) x =
        (∫ w, mvpKernel S w) * mollifyWith ((mollifierBump n).normed volume) u x := by
    intro n hn x hx
    have hnr : 1 / ((n : ℝ) + 1) ≤ r := by
      refine le_of_lt (lt_of_le_of_lt ?_ hN)
      refine one_div_le_one_div_of_le (by positivity) ?_
      -- in this mathlib `add_le_add_left h a : b + a ≤ c + a` (the `to_additive` of
      -- `mul_le_mul_left`); `add_le_add_right` is the one that adds on the left
      exact add_le_add_left (Nat.cast_le.2 hn) 1
    have hun : ContDiff ℝ ∞ (mollifyWith ((mollifierBump n).normed volume) u) :=
      contDiff_mollifyWith (n := ⊤) (hρc n) (hρs n) hG.locallyIntegrable
    have hsoln : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball x₀ (2 * r) →
        ∫ y, ⟪A₀ (gradient (mollifyWith ((mollifierBump n).normed volume) u) y),
          gradient ψ y⟫ = 0 := by
      intro ψ hψ hψs hψsupp
      refine integral_inner_gradient_mollifyWith_eq_zero (c := x₀) (a := 2 * r) (b := 3 * r)
        hG hsol (hρc n) (hρs n) (hρsupp n) (by linarith) ?_ hψ hψs
        (hψsupp.trans Metric.ball_subset_closedBall)
      refine subset_trans (fun z hz => ?_) hRU
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hballx : Metric.closedBall x (s * mvpRadius α) ⊆ Metric.ball x₀ (2 * r) := by
      rw [hsr]
      intro z hz
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball] at hx ⊢
      calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
        _ < r + r := by linarith
        _ = 2 * r := by ring
    have hmvp := integral_mvpKernel_mul_comp_eq_of_contDiff (c := x₀) (R := 2 * r)
      hSsymm hSA hα hQ hun (by linarith) hsoln hs hballx
    -- rewrite the mean as a mollification with the fixed kernel `K`
    have hchange : ∫ w, mvpKernel S w *
        (mollifyWith ((mollifierBump n).normed volume) u) (x + s • w) =
        |(s ^ d)⁻¹| * mollifyWith K (mollifyWith ((mollifierBump n).normed volume) u) x := by
      have h := integral_comp_inv_smul_sub (fun w : Euc d => mvpKernel S w *
        (mollifyWith ((mollifierBump n).normed volume) u) (x + s • w)) x hs
      rw [h, hmollK]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hy : x + s • (s⁻¹ • (y - x)) = y := by
        rw [smul_inv_smul₀ hs.ne']
        abel
      -- beta-reduce first: `rw` cannot see through `(fun y => _) y`
      show mvpKernel S (s⁻¹ • (y - x)) *
          mollifyWith ((mollifierBump n).normed volume) u (x + s • (s⁻¹ • (y - x))) =
        mvpKernel S (s⁻¹ • (y - x)) * mollifyWith ((mollifierBump n).normed volume) u y
      rw [hy]
    rw [hchange] at hmvp
    rw [← mollifyWith_mollifyWith_comm hG.locallyIntegrable (hρc n).continuous (hρs n) hKc hKs]
    exact hmvp
  -- pass to the limit
  refine ⟨r, hr0, (Metric.ball_subset_ball (by linarith)).trans hRU,
    fun x => (|(s ^ d)⁻¹| / (∫ w, mvpKernel S w)) * mollifyWith K u x, ?_, ?_⟩
  · exact contDiff_const.mul (contDiff_mollifyWith (n := ⊤) hKcd hKs hG.locallyIntegrable)
  have hae1 := ae_tendsto_mollifyWith_stdBump hG.locallyIntegrable
  have hae2 := ae_tendsto_mollifyWith_stdBump
    (continuous_mollifyWith hKc hKs hG.locallyIntegrable).locallyIntegrable
  filter_upwards [hae1, hae2] with x hx1 hx2 hxmem
  have hlim1 : Tendsto (fun n => (∫ w, mvpKernel S w) *
      mollifyWith ((mollifierBump n).normed volume) u x) atTop
      (𝓝 ((∫ w, mvpKernel S w) * u x)) := hx1.const_mul (∫ w, mvpKernel S w)
  have hlim2 : Tendsto (fun n => |(s ^ d)⁻¹| *
      mollifyWith ((mollifierBump n).normed volume) (mollifyWith K u) x) atTop
      (𝓝 (|(s ^ d)⁻¹| * mollifyWith K u x)) := hx2.const_mul (|(s ^ d)⁻¹|)
  have heq : ∀ᶠ n in atTop, |(s ^ d)⁻¹| *
      mollifyWith ((mollifierBump n).normed volume) (mollifyWith K u) x =
      (∫ w, mvpKernel S w) * mollifyWith ((mollifierBump n).normed volume) u x := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hkey n hn x hxmem
  have hfin := tendsto_nhds_unique (hlim2.congr' heq) hlim1
  have hgoal : |(s ^ d)⁻¹| / (∫ w, mvpKernel S w) * mollifyWith K u x = u x := by
    rw [div_mul_eq_mul_div, hfin, mul_comm (∫ w, mvpKernel S w) (u x), mul_div_assoc,
      div_self hcne, mul_one]
  exact hgoal.symm

/-- The companion statement for the gradient: if `u` has weak gradient `G` and agrees almost
everywhere with a `C¹` function `v` on an open set `W`, then `G` is almost everywhere on `W` the
classical gradient of `v`.  Combined with `exists_contDiff_ae_eq_of_weakSolution` this says that
the distributional gradient of a weak solution is the gradient of a smooth function. -/
theorem weakGrad_ae_eq_gradient_of_ae_eq
    {u : Euc d → ℝ} {G : Euc d → Euc d} (hG : HasWeakGradient u G)
    {v : Euc d → ℝ} (hv : ContDiff ℝ 1 v) {W : Set (Euc d)} (hW : IsOpen W)
    (huv : ∀ᵐ x, x ∈ W → u x = v x) :
    ∀ᵐ x, x ∈ W → G x = gradient v x := by
  have hvc : Continuous (gradient v) := continuous_gradient hv
  have hvG : LocallyIntegrable (fun x => G x - gradient v x) := by
    have h : LocallyIntegrable (G - gradient v) :=
      hG.locallyIntegrable_grad.sub hvc.locallyIntegrable
    exact h
  have hzero : ∀ᵐ x, x ∈ W → (fun x => G x - gradient v x) x = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hvG.locallyIntegrableOn W) ?_
    intro ψ hψ hψs hψW
    -- a smooth cutoff equal to `1` on a neighbourhood of `tsupport ψ`
    obtain ⟨Rψ, hRψ⟩ := hψs.isBounded.subset_closedBall (0 : Euc d)
    obtain ⟨η, hηin, _hηout⟩ : ∃ η : ContDiffBump (0 : Euc d),
        η.rIn = |Rψ| + 1 ∧ η.rOut = |Rψ| + 2 :=
      ⟨⟨|Rψ| + 1, |Rψ| + 2, by positivity, by linarith⟩, rfl, rfl⟩
    have hηball : tsupport ψ ⊆ Metric.ball (0 : Euc d) (|Rψ| + 1) := by
      refine hRψ.trans fun x hx => ?_
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖x‖ ≤ Rψ := hx
        _ ≤ |Rψ| := le_abs_self Rψ
        _ < |Rψ| + 1 := by linarith
    have hη1 : ∀ x ∈ Metric.ball (0 : Euc d) (|Rψ| + 1), (η : Euc d → ℝ) x = 1 := by
      intro x hx
      refine η.one_of_mem_closedBall ?_
      rw [hηin]
      exact Metric.ball_subset_closedBall hx
    -- the cut-off smooth function, which does have a weak gradient
    have hwc : ContDiff ℝ 1 fun x : Euc d => (η : Euc d → ℝ) x * v x :=
      (η.contDiff (n := 1)).mul hv
    have hws : HasCompactSupport fun x : Euc d => (η : Euc d → ℝ) x * v x := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) η.rOut) fun x hx => ?_
      have hz : (η : Euc d → ℝ) x = 0 := by
        refine image_eq_zero_of_notMem_tsupport ?_
        rw [η.tsupport_eq]
        exact hx
      rw [hz, zero_mul]
    have hwG := hasWeakGradient_gradient hwc hws
    have hgradψ : ∀ x : Euc d, x ∉ tsupport ψ → gradient ψ x = 0 := by
      intro x hx
      have hψ0 : ψ =ᶠ[𝓝 x] fun _ : Euc d => (0 : ℝ) := by
        filter_upwards [(isOpen_compl_iff.2
          (isClosed_closure (s := Function.support ψ))).mem_nhds hx] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      rw [hψ0.gradient_eq, gradient_fun_const]
    -- the two integration-by-parts identities have the same left-hand side
    refine ext_inner_left ℝ fun z => ?_
    have hint : Integrable fun x => ψ x • (G x - gradient v x) :=
      hvG.integrable_smul_left_of_hasCompactSupport hψ.continuous hψs
    have hi1 : Integrable fun x => ⟪G x, z⟫ * ψ x := by
      refine (Integrable.const_inner (𝕜 := ℝ) z
        (hG.locallyIntegrable_grad.integrable_smul_left_of_hasCompactSupport hψ.continuous
          hψs)).congr (Eventually.of_forall fun x => ?_)
      simp only [inner_smul_right]
      rw [real_inner_comm, mul_comm]
    have hi2 : Integrable fun x => ⟪gradient v x, z⟫ * ψ x := by
      refine (Integrable.const_inner (𝕜 := ℝ) z
        (hvc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous
          hψs)).congr (Eventually.of_forall fun x => ?_)
      simp only [inner_smul_right]
      rw [real_inner_comm, mul_comm]
    have hsame : ∫ x, u x * fderiv ℝ ψ x z
        = ∫ x, ((η : Euc d → ℝ) x * v x) * fderiv ℝ ψ x z := by
      refine integral_congr_ae ?_
      filter_upwards [huv] with x hx
      by_cases hxs : x ∈ tsupport ψ
      · rw [hx (hψW hxs), hη1 x (hηball hxs), one_mul]
      · have h0 : fderiv ℝ ψ x z = 0 := by
          rw [fderiv_apply_eq_inner_gradient, hgradψ x hxs]
          simp
        rw [h0, mul_zero, mul_zero]
    have hrhs : ∫ x, ⟪gradient (fun y : Euc d => (η : Euc d → ℝ) y * v y) x, z⟫ * ψ x
        = ∫ x, ⟪gradient v x, z⟫ * ψ x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      -- beta-reduce first: `rw` cannot see through `(fun x => _) x`
      show ⟪gradient (fun y : Euc d => (η : Euc d → ℝ) y * v y) x, z⟫ * ψ x
          = ⟪gradient v x, z⟫ * ψ x
      by_cases hxs : x ∈ tsupport ψ
      · have hgr : gradient (fun y : Euc d => (η : Euc d → ℝ) y * v y) x = gradient v x := by
          refine Filter.EventuallyEq.gradient_eq ?_
          filter_upwards [Metric.isOpen_ball.mem_nhds (hηball hxs)] with y hy
          rw [hη1 y hy, one_mul]
        rw [hgr]
      · rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero, mul_zero]
    have hcompare : ∫ x, ⟪G x, z⟫ * ψ x = ∫ x, ⟪gradient v x, z⟫ * ψ x := by
      have h := (hG.integral_mul_fderiv ψ hψ hψs z).symm.trans
        (hsame.trans (hwG.integral_mul_fderiv ψ hψ hψs z))
      rw [hrhs] at h
      exact neg_injective h
    have hpt : ∀ x : Euc d, ⟪z, ψ x • (G x - gradient v x)⟫
        = ⟪G x, z⟫ * ψ x - ⟪gradient v x, z⟫ * ψ x := by
      intro x
      have h1 : ⟪z, ψ x • (G x - gradient v x)⟫
          = ψ x * (⟪z, G x⟫ - ⟪z, gradient v x⟫) := by
        simp only [real_inner_smul_right, inner_sub_right]
      rw [h1, real_inner_comm (G x) z, real_inner_comm (gradient v x) z]
      ring
    rw [← integral_inner hint z, integral_congr_ae (Eventually.of_forall hpt),
      integral_sub hi1 hi2, hcompare, sub_self]
    simp
  filter_upwards [hzero] with x hx hxW
  have hsub := hx hxW
  rwa [sub_eq_zero] at hsub

/-- **Weyl's lemma in the form the Campanato/Schauder iteration consumes**: a distributional
solution of `div (A₀ ∇u) = 0` on `U` agrees, on a ball around any point of `U`, almost everywhere
with a `C^∞` function *together with its gradient*.  In particular `G` is a.e. a continuous field
there, so `u` is (a.e.) a genuine `C¹` solution near every point of `U`. -/
theorem exists_contDiff_ae_eq_gradient_of_weakSolution
    {A₀ : Euc d →L[ℝ] Euc d} (hsymm : ∀ p q : Euc d, ⟪A₀ p, q⟫ = ⟪p, A₀ q⟫)
    {μ : ℝ} (hμ : 0 < μ) (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    {U : Set (Euc d)} (hU : IsOpen U) {u : Euc d → ℝ} {G : Euc d → Euc d}
    (hG : HasWeakGradient u G)
    (hsol : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ y, ⟪A₀ (G y), gradient ψ y⟫ = 0)
    {x₀ : Euc d} (hx₀ : x₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x₀ r ⊆ U ∧ ∃ v : Euc d → ℝ, ContDiff ℝ ∞ v ∧
      (∀ᵐ x, x ∈ Metric.ball x₀ r → u x = v x) ∧
      ∀ᵐ x, x ∈ Metric.ball x₀ r → G x = gradient v x := by
  obtain ⟨r, hr0, hrU, v, hv, hae⟩ :=
    exists_contDiff_ae_eq_of_weakSolution hsymm hμ hell hU hG hsol hx₀
  exact ⟨r, hr0, hrU, v, hv, hae,
    weakGrad_ae_eq_gradient_of_ae_eq hG (hv.of_le (by simp)) Metric.isOpen_ball hae⟩

end Komlos.Literature
