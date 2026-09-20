import Komlos.Literature.Regularized.AssemblyData

/-!
# Wang–Xia for the regularized route: the pointwise differential inequality (lane `L5`)

`REGULARIZED_ROUTE.md`, Revision 2, Wang–Xia step 1.  For the perturbed infimal convolution
`w_η` of two log-minimizers `v_i` solving

`div ∇Ψ(∇v_i) = κ v_i + Λ_i + B(∇v_i)`,  `B(q) = 2 (⟪∇Ψ q, q⟫ - Ψ q)`,  `Λ_i = 2 m(K_i)`,

we prove the differential inequality

`div ∇Ψ(∇w_η)(z) ≤ κ w_η(z) + ((1-t)Λ₀ + tΛ₁ + ε) + B(∇w_η(z))`

uniformly for `z` in a compact subset of `K_t` and all small `η > 0`.

Two things make this simpler than the degenerate case of `Komlos/Literature/WangXia`:

* `D²Ψ(q) ≻ 0` for **every** `q`, including `q = 0`, so there is no critical set: no
  off-critical restriction and no cutoff are needed, and `∇w_η ∈ C¹` at *every* point of `K_t`
  for `η > 0` (`contDiffAt_gradient_w_reg`);
* the affine term `κ v` passes through the infimal convolution exactly: at a minimizing pair,
  `(1-t) v₀(x₀) + t v₁(x₁) = obj_0(x₀,x₁) ≤ obj_η(x₀,x₁) = w_η(z)`, so the `η`-perturbation
  only helps (`κ > 0`).

## Main results

* `regRemFn`: the remainder functional
  `Φ(ξ, x, η) = tr(D∇Ψ(ξ)(D²v(x) + 2ηI)) - κ v(x) - B(ξ)`, continuous on `ℝ^d × Ω × ℝ`;
* `regRemFn_apply_gradient`: `Φ(∇v(x), x, 0) = div ∇Ψ(∇v)(x) - κ v(x) - B(∇v(x))`, which the
  equation identifies with `Λ`;
* `divergence_gradPsi_gradient_w_le`: the pointwise inequality at a minimizing pair, from the
  Hessian comparison `D²w_η ≤ (1-t)(D²v₀ + 2ηI) + t(D²v₁ + 2ηI)` and the trace inequality
  against the symmetric positive semidefinite `D∇Ψ(q)`;
* `eventually_divergence_gradPsi_gradient_w_le`: the uniform version.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-- The two notions of divergence in this development coincide (they are the same
definition, in two namespaces). -/
theorem korevaar_divergence_eq (W : Euc d → Euc d) (x : Euc d) :
    Korevaar.divergence W x = divergence W x := rfl

/-! ### The remainder functional -/

/-- The functional `Φ(ξ, x, η) = tr(D∇Ψ(ξ)(D²v(x) + 2ηI)) - κ v(x) - 2(⟪∇Ψ ξ, ξ⟫ - Ψ ξ)`.
Compare `Komlos.Literature.remFn`; here `D∇Ψ` is defined and continuous at every `ξ`, so no
annulus `{ξ ≠ 0}` is needed. -/
noncomputable def regRemFn (κ : ℝ) (Ψ v : Euc d → ℝ) (a : Euc d × Euc d × ℝ) : ℝ :=
  (∑ i, ⟪EuclideanSpace.single i (1 : ℝ), fderiv ℝ (gradient Ψ) a.1
      (fderiv ℝ (gradient v) a.2.1 (EuclideanSpace.single i (1 : ℝ)) +
        (2 * a.2.2) • EuclideanSpace.single i (1 : ℝ))⟫) -
    κ * v a.2.1 - 2 * (⟪gradient Ψ a.1, a.1⟫ - Ψ a.1)

variable {κ : ℝ} {Ψ : Euc d → ℝ}

/-- `D(∇Ψ)` is continuous on all of `ℝ^d`. -/
theorem continuous_fderiv_gradient (hΨ : IsRegProfile Ψ) :
    Continuous (fderiv ℝ (gradient Ψ)) :=
  (contDiff_infty_iff_fderiv.1 hΨ.contDiff_gradient).2.continuous

/-- `Φ` is continuous on `ℝ^d × Ω × ℝ` when `v` is continuous and `∇v` is `C¹` on the open set
`Ω`. -/
theorem continuousOn_regRemFn (hΨ : IsRegProfile Ψ) {v : Euc d → ℝ} {Ω : Set (Euc d)}
    (hΩ : IsOpen Ω) (hvc : ContinuousOn v Ω) (hv : ContDiffOn ℝ 1 (gradient v) Ω) :
    ContinuousOn (regRemFn κ Ψ v) (univ ×ˢ Ω ×ˢ univ) := by
  have hA : Continuous (fderiv ℝ (gradient Ψ)) := continuous_fderiv_gradient hΨ
  have hB : ContinuousOn (fderiv ℝ (gradient v)) Ω := hv.continuousOn_fderiv_of_isOpen hΩ le_rfl
  unfold regRemFn
  refine ContinuousOn.sub (ContinuousOn.sub (continuousOn_finsetSum _ fun i _ => ?_) ?_) ?_
  · refine continuousOn_const.inner ?_
    refine ContinuousOn.clm_apply (hA.comp_continuousOn continuousOn_fst) ?_
    refine ContinuousOn.add ?_
      ((continuousOn_const.mul continuousOn_snd.snd).smul continuousOn_const)
    exact ContinuousOn.clm_apply (hB.comp continuousOn_snd.fst fun a ha => ha.2.1)
      continuousOn_const
  · exact continuousOn_const.mul (hvc.comp continuousOn_snd.fst fun a ha => ha.2.1)
  · refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
    · exact (hΨ.contDiff_gradient.continuous.comp_continuousOn continuousOn_fst).inner
        continuousOn_fst
    · exact hΨ.contDiff.continuous.comp_continuousOn continuousOn_fst

/-- At `(∇v(x), x, 0)`, `Φ = div ∇Ψ(∇v)(x) - κ v(x) - 2(⟪∇Ψ(∇v x), ∇v x⟫ - Ψ(∇v x))`. -/
theorem regRemFn_apply_gradient (hΨ : IsRegProfile Ψ) {v : Euc d → ℝ} {x : Euc d}
    (hv : DifferentiableAt ℝ (gradient v) x) :
    regRemFn κ Ψ v (gradient v x, x, 0) =
      divergence (fun y => gradient Ψ (gradient v y)) x - κ * v x -
        2 * (⟪gradient Ψ (gradient v x), gradient v x⟫ - Ψ (gradient v x)) := by
  rw [divergence_comp (hΨ.hasFDerivAt_gradient (gradient v x)) hv.hasFDerivAt]
  simp [regRemFn]

/-- Uniform continuity of `Φ` on `closedBall 0 M × S × [0,1]` for a compact `S ⊆ Ω`, in
`ε`-`δ` form. -/
theorem exists_delta_regRemFn (hΨ : IsRegProfile Ψ) {v : Euc d → ℝ} {Ω : Set (Euc d)}
    (hΩ : IsOpen Ω) (hvc : ContinuousOn v Ω) (hv : ContDiffOn ℝ 1 (gradient v) Ω)
    {S : Set (Euc d)} (hS : IsCompact S) (hSΩ : S ⊆ Ω) (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : Euc d × Euc d × ℝ, ‖a.1‖ ≤ M → ‖b.1‖ ≤ M → a.2.1 ∈ S → b.2.1 ∈ S →
      a.2.2 ∈ Icc (0 : ℝ) 1 → b.2.2 ∈ Icc (0 : ℝ) 1 → dist a b < δ →
      |regRemFn κ Ψ v a - regRemFn κ Ψ v b| < ε := by
  set Q := Metric.closedBall (0 : Euc d) M ×ˢ (S ×ˢ Icc (0 : ℝ) 1) with hQdef
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (hS.prod isCompact_Icc)
  have hQsub : Q ⊆ univ ×ˢ Ω ×ˢ univ := by
    rintro ⟨ξ, x, η⟩ ⟨-, hx, -⟩
    exact ⟨trivial, hSΩ hx, trivial⟩
  have huc : UniformContinuousOn (regRemFn κ Ψ v) Q :=
    hQ.uniformContinuousOn_of_continuous ((continuousOn_regRemFn hΨ hΩ hvc hv).mono hQsub)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  refine ⟨δ, hδ, fun a b ha1 hb1 ha2 hb2 ha3 hb3 hab => ?_⟩
  have haQ : a ∈ Q := ⟨mem_closedBall_zero_iff.2 ha1, ha2, ha3⟩
  have hbQ : b ∈ Q := ⟨mem_closedBall_zero_iff.2 hb1, hb2, hb3⟩
  have := hδ' a haQ b hbQ hab
  rwa [Real.dist_eq] at this

/-! ### `∇w_η ∈ C¹` everywhere on `K_t` -/

/-- **No critical set**: for `η > 0`, `∇w_η` is `C¹` at every point of `K_t`, because
`D²v_i + 2ηI ≻ 0` at every minimizing pair (no nondegeneracy of `∇v_i` is needed). -/
theorem contDiffAt_gradient_w_reg (D : InfConvData d)
    (hc₀ : ContDiffOn ℝ 1 (gradient D.v₀) D.K₀) (hc₁ : ContDiffOn ℝ 1 (gradient D.v₁) D.K₁)
    {η : ℝ} (hη : 0 < η) {z : Euc d} (hz : z ∈ D.Kt) :
    ContDiffAt ℝ 1 (gradient (D.w η)) z := by
  obtain ⟨m, hm⟩ := D.exists_minimizer hη.le hz
  exact hm.contDiffAt_gradient_w hη (hc₀.contDiffAt (D.h₀.isOpen.mem_nhds hm.fst_mem))
    (hc₁.contDiffAt (D.h₁.isOpen.mem_nhds hm.snd_mem))

/-! ### The pointwise inequality at a minimizing pair -/

/-- **The pointwise inequality at a minimizing pair**: from the Hessian comparison
`D²w_η ≤ (1-t)(D²v₀(x₀) + 2ηI) + t(D²v₁(x₁) + 2ηI)`, the trace inequality against the
symmetric positive semidefinite `D∇Ψ(q)`, and the fact that the affine term passes through:
`(1-t)v₀(x₀) + t v₁(x₁) = obj_0 ≤ obj_η = w_η(z)`. -/
theorem divergence_gradPsi_gradient_w_le {D : InfConvData d} (hΨ : IsRegProfile Ψ)
    (hκ : 0 ≤ κ) {η : ℝ} (hη : 0 < η) {z : Euc d} {m : Euc d × Euc d}
    (hm : D.IsMinimizer η z m) (h₀ : ContDiffAt ℝ 1 (gradient D.v₀) m.1)
    (h₁ : ContDiffAt ℝ 1 (gradient D.v₁) m.2) :
    divergence (fun y => gradient Ψ (gradient (D.w η) y)) z ≤
      (1 - D.t) * regRemFn κ Ψ D.v₀ (gradient (D.w η) z, m.1, η) +
        D.t * regRemFn κ Ψ D.v₁ (gradient (D.w η) z, m.2, η) +
        κ * D.w η z +
        2 * (⟪gradient Ψ (gradient (D.w η) z), gradient (D.w η) z⟫ -
          Ψ (gradient (D.w η) z)) := by
  set q := gradient (D.w η) z with hqdef
  set A := fderiv ℝ (gradient Ψ) q with hAdef
  set H := fderiv ℝ (gradient (D.w η)) z with hHdef
  set H₀ := fderiv ℝ (gradient D.v₀) m.1 with hH₀def
  set H₁ := fderiv ℝ (gradient D.v₁) m.2 with hH₁def
  have hwd : HasFDerivAt (gradient (D.w η)) H z :=
    ((hm.contDiffAt_gradient_w hη h₀ h₁).differentiableAt one_ne_zero).hasFDerivAt
  have hd₀ : HasFDerivAt (gradient D.v₀) H₀ m.1 := (h₀.differentiableAt one_ne_zero).hasFDerivAt
  have hd₁ : HasFDerivAt (gradient D.v₁) H₁ m.2 := (h₁.differentiableAt one_ne_zero).hasFDerivAt
  rw [divergence_comp (hΨ.hasFDerivAt_gradient q) hwd]
  set H' : Euc d →L[ℝ] Euc d :=
    (1 - D.t) • (H₀ + (2 * η) • ContinuousLinearMap.id ℝ (Euc d)) +
      D.t • (H₁ + (2 * η) • ContinuousLinearMap.id ℝ (Euc d)) with hH'def
  have hle : ∀ ζ, ⟪H ζ, ζ⟫ ≤ ⟪H' ζ, ζ⟫ := fun ζ => by
    have := hm.inner_fderiv_gradient_w_le hη.le hwd hd₀ hd₁ ζ
    simp only [hH'def, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
      inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith
  have hAs : ∀ ζ ζ' : Euc d, ⟪A ζ, ζ'⟫ = ⟪ζ, A ζ'⟫ := hΨ.inner_fderiv_gradient_comm q
  have hAn : ∀ ζ : Euc d, 0 ≤ ⟪A ζ, ζ⟫ := by
    obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
    exact fun ζ => le_trans (mul_nonneg h.c_pos.le (sq_nonneg _)) (h.lower q ζ)
  have htr := sum_inner_single_apply_le hAs hAn hle
  -- the affine term passes through
  have haff : (1 - D.t) * D.v₀ m.1 + D.t * D.v₁ m.2 ≤ D.w η z := by
    have h1 := D.obj_zero_le_obj hη.le m
    rw [InfConvData.obj_zero] at h1
    rw [hm.w_eq]
    exact h1
  have hκaff : κ * ((1 - D.t) * D.v₀ m.1 + D.t * D.v₁ m.2) ≤ κ * D.w η z :=
    mul_le_mul_of_nonneg_left haff hκ
  have hexpand : ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), A (H' (EuclideanSpace.single i (1 : ℝ)))⟫
      = (1 - D.t) * regRemFn κ Ψ D.v₀ (q, m.1, η) + D.t * regRemFn κ Ψ D.v₁ (q, m.2, η) +
        κ * ((1 - D.t) * D.v₀ m.1 + D.t * D.v₁ m.2) +
        2 * (⟪gradient Ψ q, q⟫ - Ψ q) := by
    have ht : (1 - D.t) + D.t = 1 := by ring
    simp only [regRemFn, hH'def, hAdef, hH₀def, hH₁def, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, map_add, map_smul, inner_add_right, inner_smul_right,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hexpand] at htr
  linarith

/-! ### The uniform differential inequality -/

/-- **The differential inequality, uniformly on compact subsets of `K_t`**
(`REGULARIZED_ROUTE.md`, Revision 2: "`div ∇Ψ(∇w_η) ≤ κ w_η + 2((1-t)m₀ + t m₁) + B(∇w_η) +
r_η`, `r_η → 0` locally uniformly"): for a compact `Z ⊆ K_t`, an `R` bounding the input
domains and `ε > 0`, for all small `η > 0` and all `z ∈ Z`,
`div ∇Ψ(∇w_η)(z) ≤ κ w_η(z) + ((1-t)Λ₀ + tΛ₁ + ε) + B(∇w_η(z))`. -/
theorem eventually_divergence_gradPsi_gradient_w_le (D : InfConvData d) (hΨ : IsRegProfile Ψ)
    (hκ : 0 ≤ κ) (hc₀ : ContDiffOn ℝ 1 (gradient D.v₀) D.K₀)
    (hc₁ : ContDiffOn ℝ 1 (gradient D.v₁) D.K₁) {lam₀ lam₁ : ℝ}
    (he₀ : ∀ x ∈ D.K₀, divergence (fun y => gradient Ψ (gradient D.v₀ y)) x =
      κ * D.v₀ x + lam₀ +
        2 * (⟪gradient Ψ (gradient D.v₀ x), gradient D.v₀ x⟫ - Ψ (gradient D.v₀ x)))
    (he₁ : ∀ x ∈ D.K₁, divergence (fun y => gradient Ψ (gradient D.v₁ y)) x =
      κ * D.v₁ x + lam₁ +
        2 * (⟪gradient Ψ (gradient D.v₁ x), gradient D.v₁ x⟫ - Ψ (gradient D.v₁ x)))
    {Z : Set (Euc d)} (hZ : IsCompact Z) (hZK : Z ⊆ D.Kt) {R : ℝ}
    (hR₀ : D.K₀ ⊆ Metric.closedBall 0 R) (hR₁ : D.K₁ ⊆ Metric.closedBall 0 R) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ z ∈ Z,
      divergence (fun y => gradient Ψ (gradient (D.w η) y)) z ≤
        κ * D.w η z + ((1 - D.t) * lam₀ + D.t * lam₁ + ε) +
          2 * (⟪gradient Ψ (gradient (D.w η) z), gradient (D.w η) z⟫ -
            Ψ (gradient (D.w η) z)) := by
  rcases Z.eq_empty_or_nonempty with rfl | hZne
  · exact Eventually.of_forall fun η z hz => absurd hz (notMem_empty z)
  have hR : 0 ≤ R := by
    obtain ⟨x, hx⟩ := D.h₀.nonempty
    exact (norm_nonneg x).trans (mem_closedBall_zero_iff.1 (hR₀ hx))
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hZ).exists_bound_of_continuousOn
    (D.continuousOn_gradient_w.mono (prod_mono Icc_subset_Ici_self hZK))
  obtain ⟨S₀, S₁, hS₀, hS₁, hS₀K, hS₁K, hS⟩ := D.exists_isCompact_minimizers 1 hZ hZK
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := exists_delta_regRemFn (κ := κ) hΨ D.h₀.isOpen D.h₀.continuousOn
    hc₀ hS₀ hS₀K (M + 2 * R) hε
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := exists_delta_regRemFn (κ := κ) hΨ D.h₁.isOpen D.h₁.continuousOn
    hc₁ hS₁ hS₁K (M + 2 * R) hε
  have h1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη
    exact hη.2.le
  have h3 : ∀ᶠ η in 𝓝[>] (0 : ℝ), (2 * R + 1) * η < min δ₀ δ₁ := by
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < min δ₀ δ₁ / (2 * R + 1))] with η hη
    have := (lt_div_iff₀ (by positivity)).1 hη.2
    linarith
  filter_upwards [self_mem_nhdsWithin, h1, h3] with η hη hη1 hη3 z hz
  have hη0 : 0 < η := hη
  have hηI : η ∈ Icc (0 : ℝ) 1 := ⟨hη0.le, hη1⟩
  set q := gradient (D.w η) z with hqdef
  have hqM : ‖q‖ ≤ M := hM (η, z) ⟨hηI, hz⟩
  obtain ⟨m, hm⟩ := D.exists_minimizer hη0.le (hZK hz)
  have hmS := hS η hηI z hz m hm
  have hm1R : ‖m.1‖ ≤ R := mem_closedBall_zero_iff.1 (hR₀ hm.fst_mem)
  have hm2R : ‖m.2‖ ≤ R := mem_closedBall_zero_iff.1 (hR₁ hm.snd_mem)
  have hg₀ : gradient D.v₀ m.1 = q - (2 * η) • m.1 := by
    rw [hqdef, hm.gradient_w hη0.le]
    simp [InfConvData.commonGrad]
  have hg₁ : gradient D.v₁ m.2 = q - (2 * η) • m.2 := by
    rw [hqdef, hm.gradient_w hη0.le, hm.commonGrad_eq]
    simp
  have h2η : 0 ≤ 2 * η := by positivity
  have hn₀ : ‖(2 * η) • m.1‖ ≤ 2 * η * R := by
    rw [norm_smul, Real.norm_of_nonneg h2η]
    exact mul_le_mul_of_nonneg_left hm1R h2η
  have hn₁ : ‖(2 * η) • m.2‖ ≤ 2 * η * R := by
    rw [norm_smul, Real.norm_of_nonneg h2η]
    exact mul_le_mul_of_nonneg_left hm2R h2η
  have hg₀M : ‖gradient D.v₀ m.1‖ ≤ M + 2 * R := by
    rw [hg₀]
    have := norm_sub_le q ((2 * η) • m.1)
    nlinarith
  have hg₁M : ‖gradient D.v₁ m.2‖ ≤ M + 2 * R := by
    rw [hg₁]
    have := norm_sub_le q ((2 * η) • m.2)
    nlinarith
  have hqM' : ‖q‖ ≤ M + 2 * R := by nlinarith
  have hcd₀ : ContDiffAt ℝ 1 (gradient D.v₀) m.1 :=
    hc₀.contDiffAt (D.h₀.isOpen.mem_nhds hm.fst_mem)
  have hcd₁ : ContDiffAt ℝ 1 (gradient D.v₁) m.2 :=
    hc₁.contDiffAt (D.h₁.isOpen.mem_nhds hm.snd_mem)
  have hpt := divergence_gradPsi_gradient_w_le (κ := κ) hΨ hκ hη0 hm hcd₀ hcd₁
  have hδ₀m : (2 * R + 1) * η < δ₀ := lt_of_lt_of_le hη3 (min_le_left _ _)
  have hδ₁m : (2 * R + 1) * η < δ₁ := lt_of_lt_of_le hη3 (min_le_right _ _)
  have hr₀ : regRemFn κ Ψ D.v₀ (q, m.1, η) < lam₀ + ε := by
    have hb : regRemFn κ Ψ D.v₀ (gradient D.v₀ m.1, m.1, 0) = lam₀ := by
      rw [regRemFn_apply_gradient hΨ (hcd₀.differentiableAt one_ne_zero),
        he₀ m.1 hm.fst_mem]
      ring
    have hd1 : dist q (gradient D.v₀ m.1) = ‖(2 * η) • m.1‖ := by
      rw [hg₀, dist_eq_norm, sub_sub_cancel]
    have hdist : dist (q, m.1, η) (gradient D.v₀ m.1, m.1, 0) < δ₀ := by
      simp only [Prod.dist_eq, hd1, dist_self, Real.dist_eq, sub_zero, abs_of_pos hη0]
      exact max_lt (by nlinarith) (max_lt (by linarith) (by nlinarith))
    have := hδ₀' (q, m.1, η) (gradient D.v₀ m.1, m.1, 0) hqM' hg₀M hmS.1 hmS.1 hηI
      ⟨le_rfl, zero_le_one⟩ hdist
    rw [hb, abs_sub_lt_iff] at this
    linarith [this.1]
  have hr₁ : regRemFn κ Ψ D.v₁ (q, m.2, η) < lam₁ + ε := by
    have hb : regRemFn κ Ψ D.v₁ (gradient D.v₁ m.2, m.2, 0) = lam₁ := by
      rw [regRemFn_apply_gradient hΨ (hcd₁.differentiableAt one_ne_zero),
        he₁ m.2 hm.snd_mem]
      ring
    have hd1 : dist q (gradient D.v₁ m.2) = ‖(2 * η) • m.2‖ := by
      rw [hg₁, dist_eq_norm, sub_sub_cancel]
    have hdist : dist (q, m.2, η) (gradient D.v₁ m.2, m.2, 0) < δ₁ := by
      simp only [Prod.dist_eq, hd1, dist_self, Real.dist_eq, sub_zero, abs_of_pos hη0]
      exact max_lt (by nlinarith) (max_lt (by linarith) (by nlinarith))
    have := hδ₁' (q, m.2, η) (gradient D.v₁ m.2, m.2, 0) hqM' hg₁M hmS.2 hmS.2 hηI
      ⟨le_rfl, zero_le_one⟩ hdist
    rw [hb, abs_sub_lt_iff] at this
    linarith [this.1]
  have e0 := mul_le_mul_of_nonneg_left hr₀.le D.one_sub_t_pos.le
  have e1 := mul_le_mul_of_nonneg_left hr₁.le D.t_pos.le
  have ht : (1 - D.t) * (lam₀ + ε) + D.t * (lam₁ + ε) =
      (1 - D.t) * lam₀ + D.t * lam₁ + ε := by
    have : (1 - D.t) + D.t = 1 := by ring
    nlinarith [this]
  linarith

end Komlos.Literature.Regularized
