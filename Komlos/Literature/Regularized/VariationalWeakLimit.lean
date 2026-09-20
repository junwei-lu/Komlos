import Komlos.Literature.Regularized.VariationalEnergy

/-!
# Weak `L²` limits of gradients

Lane `L1` (`reg/variational`).  The direct method needs a *weak* limit of the gradients of a
minimizing sequence: Mathlib has no weak compactness for `L^p` in general, but `L²` is a
separable Hilbert space, and Mathlib *does* have the **sequential Banach–Alaoglu theorem**
(`WeakDual.isSeqCompact_closedBall`, for a separable normed space).  Combined with the Riesz
representation `InnerProductSpace.toDual` this gives weak sequential compactness of bounded
sets in `L²`.

## Main results

* `exists_weak_limit_of_bounded`: a bounded sequence in a separable Hilbert space has a
  weakly convergent subsequence.
* `exists_weak_L2_limit`: the `L²(ℝ^d; ℝ^d)` version, phrased with integrals.
* `tendsto_integral_mul_of_tendsto_eLpNorm`: strong `L²` convergence passes to the pairing
  with a fixed `L²` function (continuity of the inner product on `L²`).
* `exists_weakGrad_of_bounded`: **the weak limit of a bounded sequence of weak gradients is a
  weak gradient of the strong `L²` limit**, and the convergence is weak in `L²`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Abstract weak sequential compactness in a separable Hilbert space -/

/-- **Weak sequential compactness of bounded sequences in a separable Hilbert space.**  Riesz
representation (`InnerProductSpace.toDual`) turns the sequence into a bounded sequence of
functionals, and the sequential Banach–Alaoglu theorem `WeakDual.isSeqCompact_closedBall`
extracts a weak-* convergent subsequence. -/
theorem exists_weak_limit_of_bounded {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {v : ℕ → H} {M : ℝ} (hM : ∀ n, ‖v n‖ ≤ M) :
    ∃ (w : H) (σ : ℕ → ℕ), StrictMono σ ∧ ‖w‖ ≤ M ∧
      ∀ φ : H, Tendsto (fun k => ⟪v (σ k), φ⟫) atTop (𝓝 ⟪w, φ⟫) := by
  set T := InnerProductSpace.toDual ℝ H with hT
  have hmem : ∀ n, (StrongDual.toWeakDual (T (v n))) ∈
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) M) := by
    intro n
    simp only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual, Metric.mem_closedBall,
      dist_zero_right]
    calc ‖T (v n)‖ = ‖v n‖ := T.norm_map (v n)
      _ ≤ M := hM n
  obtain ⟨y, hy, σ, hσ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) M hmem
  have hyM : ‖WeakDual.toStrongDual y‖ ≤ M := by
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hy
  refine ⟨T.symm (WeakDual.toStrongDual y), σ, hσ, ?_, fun φ => ?_⟩
  · calc ‖T.symm (WeakDual.toStrongDual y)‖ = ‖WeakDual.toStrongDual y‖ :=
        T.symm.norm_map _
      _ ≤ M := hyM
  · have h1 : Tendsto (fun k => (StrongDual.toWeakDual (T (v (σ k)))) φ) atTop (𝓝 (y φ)) := by
      have := ((WeakDual.eval_continuous φ).tendsto y).comp hlim
      simpa only [Function.comp_def] using this
    have h2 : ∀ k, (StrongDual.toWeakDual (T (v (σ k)))) φ = ⟪v (σ k), φ⟫ := fun k => rfl
    have h3 : ⟪T.symm (WeakDual.toStrongDual y), φ⟫ = y φ :=
      InnerProductSpace.toDual_symm_apply
    simp only [h2] at h1
    rw [h3]
    exact h1

/-! ### The `L²` version -/

section L2

variable {G : ℕ → Euc d → Euc d}

/-- Strong `L²` convergence passes to the pairing with a fixed `L²` function. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm {u : ℕ → Euc d → ℝ} {f φ : Euc d → ℝ}
    (hu : ∀ n, MemLp (u n) 2 (volume : Measure (Euc d))) (hf : MemLp f 2 volume)
    (hφ : MemLp φ 2 volume)
    (h : Tendsto (fun n => eLpNorm (u n - f) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, u n x * φ x) atTop (𝓝 (∫ x, f x * φ x)) := by
  have hinner : ∀ (g : Euc d → ℝ) (hg : MemLp g 2 volume),
      ⟪hg.toLp g, hφ.toLp φ⟫ = ∫ x, g x * φ x := by
    intro g hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hφ.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp [RCLike.inner_apply, mul_comm]
  have hnorm : Tendsto (fun n => ‖(hu n).toLp (u n) - hf.toLp f‖) atTop (𝓝 0) := by
    have heq : ∀ n, ‖(hu n).toLp (u n) - hf.toLp f‖ = (eLpNorm (u n - f) 2 volume).toReal := by
      intro n
      rw [← MemLp.toLp_sub (hu n) hf, Lp.norm_toLp]
    simp only [heq]
    have hc := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def] using hc
  have htend : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hnorm
  have hlim : Tendsto (fun n => ⟪(hu n).toLp (u n), hφ.toLp φ⟫) atTop
      (𝓝 ⟪hf.toLp f, hφ.toLp φ⟫) := Filter.Tendsto.inner htend tendsto_const_nhds
  rw [hinner f hf] at hlim
  exact hlim.congr fun n => hinner (u n) (hu n)

/-- A bounded sequence in `L²(ℝ^d; ℝ^d)` has a weakly convergent subsequence. -/
theorem exists_weak_L2_limit (hG : ∀ n, MemLp (G n) 2 (volume : Measure (Euc d)))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ n, eLpNorm (G n) 2 volume ≤ ENNReal.ofReal M) :
    ∃ (g : Euc d → Euc d) (σ : ℕ → ℕ), MemLp g 2 volume ∧ StrictMono σ ∧
      eLpNorm g 2 volume ≤ ENNReal.ofReal M ∧
      ∀ φ : Euc d → Euc d, MemLp φ 2 volume →
        Tendsto (fun k => ∫ x, ⟪G (σ k) x, φ x⟫) atTop (𝓝 (∫ x, ⟪g x, φ x⟫)) := by
  have h2ne : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  have hnorm : ∀ n, ‖(hG n).toLp (G n)‖ ≤ M := by
    intro n
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hM0 (hM n)
  obtain ⟨w, σ, hσ, hwM, hlim⟩ :=
    exists_weak_limit_of_bounded (H := Lp (Euc d) 2 (volume : Measure (Euc d)))
      (v := fun n => (hG n).toLp (G n)) hnorm
  refine ⟨(w : Euc d → Euc d), σ, Lp.memLp w, hσ, ?_, fun φ hφ => ?_⟩
  · rw [← Lp.enorm_def]
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hwM
  · have hinner : ∀ (g : Euc d → Euc d) (hg : MemLp g 2 volume),
        ⟪hg.toLp g, hφ.toLp φ⟫ = ∫ x, ⟪g x, φ x⟫ := by
      intro g hg
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hg.coeFn_toLp, hφ.coeFn_toLp] with x hx hy
      rw [hx, hy]
    have hw : ⟪w, hφ.toLp φ⟫ = ∫ x, ⟪(w : Euc d → Euc d) x, φ x⟫ := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hφ.coeFn_toLp] with x hy
      rw [hy]
    have := hlim (hφ.toLp φ)
    rw [hw] at this
    exact this.congr fun k => hinner (G (σ k)) (hG (σ k))

/-! ### Cauchy–Schwarz and the `L²` norm as an integral -/

/-- The `L²` inner product of two scalar functions is the integral of their product. -/
theorem inner_toLp_eq_integral_mul {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 volume) : ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [RCLike.inner_apply, mul_comm]

/-- The `L²` inner product of two vector fields is the integral of their pointwise pairing. -/
theorem inner_toLp_eq_integral_inner {f g : Euc d → Euc d}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hg : MemLp g 2 volume) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, ⟪f x, g x⟫ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- **Cauchy–Schwarz** for the pairing of two scalar `L²` functions. -/
theorem abs_integral_mul_le {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  rw [← inner_toLp_eq_integral_mul hf hg]
  calc |⟪hf.toLp f, hg.toLp g⟫| ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := abs_real_inner_le_norm _ _
    _ = (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
        rw [Lp.norm_toLp, Lp.norm_toLp]

/-- **Cauchy–Schwarz** for the pairing of two `L²` vector fields. -/
theorem abs_integral_inner_le {f g : Euc d → Euc d} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 volume) :
    |∫ x, ⟪f x, g x⟫| ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  rw [← inner_toLp_eq_integral_inner hf hg]
  calc |⟪hf.toLp f, hg.toLp g⟫| ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := abs_real_inner_le_norm _ _
    _ = (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
        rw [Lp.norm_toLp, Lp.norm_toLp]

/-- `‖f‖₂² = ∫ ‖f‖²` for scalar functions. -/
theorem toReal_eLpNorm_sq {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    (eLpNorm f 2 volume).toReal ^ 2 = ∫ x, f x ^ 2 := by
  have h := inner_toLp_eq_integral_mul hf hf
  rw [real_inner_self_eq_norm_sq, Lp.norm_toLp] at h
  rw [h]
  exact integral_congr_ae (Eventually.of_forall fun x => (sq (f x)).symm)

/-- `‖F‖₂² = ∫ ‖F‖²` for vector fields. -/
theorem toReal_eLpNorm_sq' {f : Euc d → Euc d} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    (eLpNorm f 2 volume).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := inner_toLp_eq_integral_inner hf hf
  rw [real_inner_self_eq_norm_sq, Lp.norm_toLp] at h
  rw [h]
  exact integral_congr_ae (Eventually.of_forall fun x => (real_inner_self_eq_norm_sq (f x)))

/-- The pointwise product of two scalar `L²` functions is integrable. -/
theorem integrable_mul_of_memLp {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 volume) : Integrable (fun x => f x * g x) volume := by
  have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  refine hI.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [RCLike.inner_apply, mul_comm]

/-- The pointwise pairing of two `L²` vector fields is integrable. -/
theorem integrable_inner_of_memLp {f g : Euc d → Euc d}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hg : MemLp g 2 volume) :
    Integrable (fun x => ⟪f x, g x⟫) volume := by
  have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  refine hI.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- The square of a scalar `L²` function is integrable. -/
theorem integrable_sq_of_memLp {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    Integrable (fun x => f x ^ 2) volume :=
  (integrable_mul_of_memLp hf hf).congr (Eventually.of_forall fun x => (pow_two (f x)).symm)

/-- The squared norm of an `L²` vector field is integrable. -/
theorem integrable_normSq_of_memLp {f : Euc d → Euc d}
    (hf : MemLp f 2 (volume : Measure (Euc d))) :
    Integrable (fun x => ‖f x‖ ^ 2) volume :=
  (integrable_inner_of_memLp hf hf).congr
    (Eventually.of_forall fun x => real_inner_self_eq_norm_sq (f x))

/-- `‖f‖₂ ≤ b` from the squared form, for `b ≥ 0`. -/
theorem toReal_eLpNorm_le_of_sq_le {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    {b : ℝ} (hb : 0 ≤ b) (hsq : (∫ x, f x ^ 2) ≤ b ^ 2) :
    (eLpNorm f 2 volume).toReal ≤ b := by
  have h1 := toReal_eLpNorm_sq hf
  have h2 : (0 : ℝ) ≤ (eLpNorm f 2 volume).toReal := ENNReal.toReal_nonneg
  nlinarith [h1, hsq]

/-- `‖F‖₂ ≤ b` from the squared form, for `b ≥ 0`. -/
theorem toReal_eLpNorm_le_of_sq_le' {f : Euc d → Euc d}
    (hf : MemLp f 2 (volume : Measure (Euc d))) {b : ℝ} (hb : 0 ≤ b)
    (hsq : (∫ x, ‖f x‖ ^ 2) ≤ b ^ 2) : (eLpNorm f 2 volume).toReal ≤ b := by
  have h1 := toReal_eLpNorm_sq' hf
  have h2 : (0 : ℝ) ≤ (eLpNorm f 2 volume).toReal := ENNReal.toReal_nonneg
  nlinarith [h1, hsq]

end L2

/-! ### The weak limit of weak gradients -/

/-- `ENNReal.ofReal 2 = 2`, used to move between the `MemW0 2` formulation and the `L²`
Hilbert space `Lp _ 2 volume`. -/
theorem ofReal_two : ENNReal.ofReal (2 : ℝ) = 2 := by
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
  norm_num

/-- **The weak limit of a bounded sequence of weak gradients is a weak gradient.**  If
`u n → f` strongly in `L²` and `G n` is a weak gradient of `u n` with `‖G n‖₂ ≤ M`, then some
subsequence of `G n` converges weakly in `L²` to a weak gradient `g` of `f`, with
`‖g‖₂ ≤ M`. -/
theorem exists_weakGrad_of_bounded {u : ℕ → Euc d → ℝ} {G : ℕ → Euc d → Euc d}
    (hwg : ∀ n, HasWeakGradient (u n) (G n))
    (hG : ∀ n, MemLp (G n) 2 (volume : Measure (Euc d)))
    (hu : ∀ n, MemLp (u n) 2 volume) {f : Euc d → ℝ} (hf : MemLp f 2 volume)
    (hfu : Tendsto (fun n => eLpNorm (u n - f) 2 volume) atTop (𝓝 0))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ n, eLpNorm (G n) 2 volume ≤ ENNReal.ofReal M) :
    ∃ (g : Euc d → Euc d) (σ : ℕ → ℕ), MemLp g 2 volume ∧ StrictMono σ ∧
      eLpNorm g 2 volume ≤ ENNReal.ofReal M ∧ HasWeakGradient f g ∧
      ∀ φ : Euc d → Euc d, MemLp φ 2 volume →
        Tendsto (fun k => ∫ x, ⟪G (σ k) x, φ x⟫) atTop (𝓝 (∫ x, ⟪g x, φ x⟫)) := by
  obtain ⟨g, σ, hgmem, hσ, hgM, hlim⟩ := exists_weak_L2_limit hG hM0 hM
  have hp1 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
  refine ⟨g, σ, hgmem, hσ, hgM, ⟨hf.locallyIntegrable hp1, hgmem.locallyIntegrable hp1, ?_⟩, hlim⟩
  intro ψ hψ hψs v
  -- the test field `φ = ψ • v`
  set φ : Euc d → Euc d := fun x => ψ x • v with hφ_def
  have hφmem : MemLp φ 2 volume := by
    have hc : Continuous φ := hψ.continuous.smul continuous_const
    have hcs : HasCompactSupport φ :=
      hψs.comp_left (g := fun t : ℝ => t • v) (by simp)
    exact hc.memLp_of_hasCompactSupport hcs
  -- the scalar test function `∂_v ψ`
  set χ : Euc d → ℝ := fun x => fderiv ℝ ψ x v with hχ_def
  have hχc : Continuous χ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχs : HasCompactSupport χ :=
    (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
  have hχmem : MemLp χ 2 volume := hχc.memLp_of_hasCompactSupport hχs
  -- pass to the limit in the integration-by-parts identity
  have hA : Tendsto (fun k => ∫ x, u (σ k) x * χ x) atTop (𝓝 (∫ x, f x * χ x)) :=
    (tendsto_integral_mul_of_tendsto_eLpNorm hu hf hχmem hfu).comp hσ.tendsto_atTop
  have hB : Tendsto (fun k => ∫ x, ⟪G (σ k) x, φ x⟫) atTop (𝓝 (∫ x, ⟪g x, φ x⟫)) :=
    hlim φ hφmem
  have hBeq : ∀ (h : Euc d → Euc d), (∫ x, ⟪h x, φ x⟫) = ∫ x, inner ℝ (h x) v * ψ x := by
    intro h
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [hφ_def]
    simp only [real_inner_smul_right]
    ring
  simp only [hBeq] at hB
  have heq : ∀ k, ∫ x, u (σ k) x * χ x = -∫ x, inner ℝ (G (σ k) x) v * ψ x := fun k =>
    (hwg (σ k)).integral_mul_fderiv ψ hψ hψs v
  simp only [heq] at hA
  exact tendsto_nhds_unique hA hB.neg

end Komlos.Literature.Regularized
