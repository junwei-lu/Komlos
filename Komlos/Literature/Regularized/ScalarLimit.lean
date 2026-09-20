import Komlos.Literature.Regularized.ScalarLimitLower

/-!
# The scalar limits `regMin 2 κ Ψ K → λ_{p,F}(K) / p`

`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*.  The regularized route produces, for each
choice of the three regularization parameters

* a truncation level `R` (the profile is `s^p/p` only for `F ≤ R`),
* a mollification radius `ε`,
* an entropy weight `κ`,

a number `m(K) = regMin 2 κ Ψ K`, and the almost-convexity `exists_regMin_convexity_const` of
`K ↦ m(K)`.  What lane `L6` has to supply is that `m(K)` converges to `λ_{p,F}(K)/p` when
`R → ∞` and `ε, κ → 0`.  To keep the assembly (`EigenvalueConvexityReg.lean`) free of any
uniformity bookkeeping across the three bodies `K₀`, `K₁`, `K_t`, the parameters are tied
together in a single **canonical sequence**

`R = n + 1`,  `ε = 1/(n+1)`,  `κ = 1/(n+1)`,

so that the statement to prove is a plain convergence of real sequences, and the three bodies
automatically see the *same* profile.

## The substitution and the constants

The exponent-`2` energy is `regEnergy 2 κ Ψ w = ∫ w² Ψ(∇w/w) + (κ/2) ∫ w² log w`.  Writing
`w = u^{p/2}` gives `∇w/w = (p/2) ∇u/u`, so with `Ψ(q) = Ψ_p((2/p) q)` (`regProfile`)

* `w² Ψ(∇w/w) = u^p Ψ_p(∇u/u)` (`homogeneousDensity_regProfile_rpow`), and
* `(κ/2) w² log w = (κ'/p) u^p log u` with `κ' = p² κ / 4`
  (`entropyPotential_two_rpow`),

while `∫ w² = ∫ u^p`.  Both identities are proved below.  Since `Ψ_p ≈ F^p/p` and
`u^p (F(∇u/u))^p/p = F(∇u)^p/p` by the `p`-homogeneity of `F`, the kinetic part is
`(1/p) ∫ F(∇u)^p`, whose infimum over normalized `u ∈ W₀^{1,p}(K)` is
`lambdaSob p F K / p = lambdaGen p F K / p` (`lambdaSob_eq_lambdaGen`).

## A remark on Bochner-integral junk values

`regEnergy` is written with Bochner integrals, which take the value `0` on a non-integrable
integrand.  For `IsRegProfile Ψ` this is harmless for the kinetic term: the quadratic growth
`Ψ 0 + (c/2)‖q‖² ≤ Ψ q ≤ Ψ 0 + (C/2)‖q‖²` (`IsRegProfileWith.quadratic_lower`,
`IsRegProfileWith.quadratic_upper`) squeezes `w² Ψ(∇w/w)` between
`Ψ(0) w² + (c/2)‖∇w‖²` and `Ψ(0) w² + (C/2)‖∇w‖²`, both integrable for `w ∈ W₀^{1,2}(K)`.  The
entropy `(κ/2) w² log w` has an integrable negative part (`x² log x ≥ -1/(2e)`, and `K` is
bounded) and an integrable positive part by the Sobolev embedding `W₀^{1,2}(K) ⊆ L^{2+η}`.  Any
proof of the two open statements below has to go through these two observations, since without
them `regMin` could be smaller than the true infimum.

## Main results

* `regKernel`, `isMollifier_regKernel`: the canonical even mollifier of radius `1/(n+1)`,
  a symmetrized normalized `ContDiffBump`;
* `regProfileSeq`, `regKappa`, `isRegProfile_regProfileSeq`: the canonical profile sequence;
* `homogeneousDensity_regProfile_rpow`, `entropyPotential_two_rpow`: the substitution
  identities that fix the constants;
* `eventually_regMin_le` (proved in `ScalarLimitUpper.lean`) and `eventually_le_regMin`
  (proved in `ScalarLimitLower.lean`, modulo the open `p > 2` case `le_regMin_of_gt_two`): the
  two scalar limits;
* `tendsto_regMin`: their combination, the statement consumed by the assembly.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The canonical mollifier sequence -/

/-- The `ContDiffBump` of outer radius `1/(n+1)` centred at the origin. -/
noncomputable def regBump (n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have hx : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have heq : (1 : ℝ) / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) / 2 := by
      rw [div_div, mul_comm]
    rw [heq]
    linarith⟩

@[simp] theorem regBump_rOut (n : ℕ) : (regBump (d := d) n).rOut = 1 / ((n : ℝ) + 1) := rfl

/-- **The canonical mollifier of radius `1/(n+1)`**: the normalized bump, symmetrized so that it
is even (the `IsMollifier` class requires an even kernel; Jensen's inequality
`le_mollifyWith_of_convexOn` uses evenness). -/
noncomputable def regKernel (n : ℕ) : Euc d → ℝ :=
  fun x => ((regBump n).normed volume x + (regBump n).normed volume (-x)) / 2

theorem contDiff_regKernel (n : ℕ) : ContDiff ℝ ∞ (regKernel (d := d) n) := by
  have h1 : ContDiff ℝ ∞ ((regBump (d := d) n).normed volume) := ContDiffBump.contDiff_normed _
  have h2 : ContDiff ℝ ∞ fun x : Euc d => (regBump n).normed volume (-x) :=
    h1.comp contDiff_neg
  exact (h1.add h2).div_const 2

theorem continuous_regKernel (n : ℕ) : Continuous (regKernel (d := d) n) :=
  (contDiff_regKernel n).continuous

theorem regKernel_nonneg (n : ℕ) (x : Euc d) : 0 ≤ regKernel n x :=
  div_nonneg (add_nonneg (ContDiffBump.nonneg_normed _ _) (ContDiffBump.nonneg_normed _ _))
    (by norm_num)

theorem regKernel_even (n : ℕ) (x : Euc d) : regKernel n (-x) = regKernel n x := by
  simp only [regKernel, neg_neg]
  ring

/-- Outside the ball of radius `1/(n+1)` the kernel vanishes. -/
theorem regKernel_eq_zero {n : ℕ} {x : Euc d} (hx : 1 / ((n : ℝ) + 1) ≤ ‖x‖) :
    regKernel n x = 0 := by
  have hsupp : Function.support ((regBump (d := d) n).normed volume) =
      Metric.ball 0 (1 / ((n : ℝ) + 1)) := by
    simpa using ContDiffBump.support_normed_eq (μ := volume) (f := regBump (d := d) n)
  have h1 : (regBump (d := d) n).normed volume x = 0 := by
    have hmem : x ∉ Function.support ((regBump (d := d) n).normed volume) := by
      rw [hsupp, mem_ball_zero_iff]
      exact not_lt.2 hx
    simpa using hmem
  have h2 : (regBump (d := d) n).normed volume (-x) = 0 := by
    have hmem : -x ∉ Function.support ((regBump (d := d) n).normed volume) := by
      rw [hsupp, mem_ball_zero_iff, norm_neg]
      exact not_lt.2 hx
    simpa using hmem
  simp [regKernel, h1, h2]

theorem hasCompactSupport_regKernel (n : ℕ) : HasCompactSupport (regKernel (d := d) n) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euc d) (1 / ((n : ℝ) + 1))) fun x hx => ?_
  rw [mem_closedBall_zero_iff]
  by_contra hlt
  exact hx (regKernel_eq_zero (le_of_lt (not_le.1 hlt)))

theorem integral_regKernel (n : ℕ) : ∫ x, regKernel (d := d) n x = 1 := by
  have hint : Integrable ((regBump (d := d) n).normed volume) :=
    ContDiffBump.integrable_normed _
  have hint2 : Integrable fun x : Euc d => (regBump n).normed volume (-x) := by
    refine Continuous.integrable_of_hasCompactSupport
      (((ContDiffBump.contDiff_normed (n := 0) (regBump (d := d) n)).continuous).comp
        continuous_neg) ?_
    exact (ContDiffBump.hasCompactSupport_normed _).comp_homeomorph (Homeomorph.neg (Euc d))
  have hstep : ∫ x : Euc d, regKernel n x =
      ((∫ x, (regBump (d := d) n).normed volume x) +
        ∫ x, (regBump (d := d) n).normed volume (-x)) / 2 := by
    simp only [regKernel]
    rw [integral_div, integral_add hint hint2]
  rw [hstep, integral_neg_eq_self, ContDiffBump.integral_normed]
  norm_num

/-- **The canonical kernel is a mollifier of radius `1/(n+1)`.** -/
theorem isMollifier_regKernel (n : ℕ) :
    IsMollifier (regKernel (d := d) n) (1 / ((n : ℝ) + 1)) where
  contDiff := contDiff_regKernel n
  nonneg := regKernel_nonneg n
  even := regKernel_even n
  integral_eq_one := integral_regKernel n
  tsupport_subset := by
    refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    rw [mem_closedBall_zero_iff]
    by_contra hlt
    exact hx (regKernel_eq_zero (le_of_lt (not_le.1 hlt)))
  eps_pos := by positivity

/-! ### The canonical parameter sequence -/

/-- The entropy weight of the canonical sequence. -/
noncomputable def regKappa (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem regKappa_pos (n : ℕ) : 0 < regKappa n := by
  rw [regKappa]; positivity

theorem tendsto_regKappa : Tendsto regKappa atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The canonical exponent-`2` profile sequence**: truncation level `R = n+1`, mollification
radius `ε = 1/(n+1)`. -/
noncomputable def regProfileSeq (p : ℝ) (F : Euc d → ℝ) (n : ℕ) : Euc d → ℝ :=
  regProfile p F ((n : ℝ) + 1) (regKernel n)

theorem isRegProfile_regProfileSeq {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) (n : ℕ) : IsRegProfile (regProfileSeq p F n) :=
  isRegProfile_regProfile hp (by positivity) hF (isMollifier_regKernel n)

/-! ### The substitution `w = u^{p/2}` -/

section Substitution

variable {p : ℝ}

/-- **The kinetic density under the substitution `w = u^{p/2}`.**  With
`∇w = (p/2) u^{p/2-1} ∇u`, the exponent-`2` density of `w` at the dilated profile
`Ψ(q) = Ψ_p((2/p) q)` is the `p`-density of `u` at `Ψ_p`:
`w² Ψ(∇w/w) = u^p Ψ_p(∇u/u)`.  This is what fixes the dilation factor `2/p` in `regProfile`. -/
theorem homogeneousDensity_regProfile_rpow (hp : 0 < p) {Ψp : Euc d → ℝ} {u : ℝ} (hu : 0 < u)
    (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 (fun q : Euc d => Ψp ((2 / p) • q)) (u ^ (p / 2))
        ((p / 2 * u ^ (p / 2 - 1)) • ξ) = Korevaar.homogeneousDensity p Ψp u ξ := by
  have hu2 : (0 : ℝ) < u ^ (p / 2) := Real.rpow_pos_of_pos hu _
  have hpow : (u ^ (p / 2)) ^ (2 : ℝ) = u ^ p := by
    rw [← Real.rpow_mul hu.le]
    congr 1
    ring
  have hu' : u ≠ 0 := ne_of_gt hu
  have hp' : p ≠ 0 := ne_of_gt hp
  have hu2' : u ^ (p / 2) ≠ 0 := ne_of_gt hu2
  have harg : (2 / p) • ((u ^ (p / 2))⁻¹ • ((p / 2 * u ^ (p / 2 - 1)) • ξ)) = u⁻¹ • ξ := by
    rw [smul_smul, smul_smul]
    congr 1
    rw [Real.rpow_sub hu, Real.rpow_one]
    field_simp
    try ring
  simp only [Korevaar.homogeneousDensity]
  rw [hpow, harg]

/-- **The entropy under the substitution `w = u^{p/2}`**: `(κ/2) w² log w = (κ'/p) u^p log u`
with `κ' = p² κ / 4`.  Equivalently `κ = 4 κ' / p²`; this is the translation between the
entropy weight of the exponent-`2` energy and that of the `p`-energy. -/
theorem entropyPotential_two_rpow (hp : 0 < p) {κ : ℝ} {u : ℝ} (hu : 0 < u) :
    Korevaar.entropyPotential 2 κ (u ^ (p / 2)) =
      Korevaar.entropyPotential p (p ^ 2 * κ / 4) u := by
  have hpow : (u ^ (p / 2)) ^ (2 : ℝ) = u ^ p := by
    rw [← Real.rpow_mul hu.le]
    congr 1
    ring
  simp only [Korevaar.entropyPotential]
  rw [hpow, Real.log_rpow hu]
  field_simp
  ring

end Substitution

/-! ### The profile sandwich along the canonical sequence -/

section Sandwich

variable {p : ℝ} {F : Euc d → ℝ}

/-- **`1 < p ≤ 2`**: the canonical profile dominates `F^p/p` at the dilated argument,
`F(q)^p/p ≤ Ψ_n((p/2) q)` for every `n`.  (Truncation and mollification both push the profile
*up* when `p ≤ 2`.) -/
theorem rpow_div_le_regProfileSeq (hp : 1 < p) (hp2 : p ≤ 2) (hF : IsSmoothStrictNorm F)
    (n : ℕ) (q : Euc d) : F q ^ p / p ≤ regProfileSeq p F n ((p / 2) • q) :=
  rpow_div_le_regProfile hp hp2 (by positivity) hF (isMollifier_regKernel n) q

/-- **`2 ≤ p`**: the canonical profile is dominated by `(F + M/(n+1))^p/p` at the dilated
argument, with `M ≥ 0` depending only on `F`.  (Truncation pushes the profile *down* when
`p ≥ 2`; only the mollification pushes it up, by `M ε`.) -/
theorem exists_regProfileSeq_le (hp : 1 < p) (hp2 : 2 ≤ p) (hF : IsSmoothStrictNorm F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (q : Euc d),
      regProfileSeq p F n ((p / 2) • q) ≤ (F q + M * (1 / ((n : ℝ) + 1))) ^ p / p := by
  obtain ⟨M, hM0, hM⟩ := exists_regProfile_le hp hp2 hF
  exact ⟨M, hM0, fun n q =>
    hM ((n : ℝ) + 1) (by positivity) (regKernel n) _ (isMollifier_regKernel n) q⟩

end Sandwich

/-! ### The two scalar limits -/

section Limits

variable {p : ℝ} {F : Euc d → ℝ}

/-- **The upper scalar limit** (`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*):
eventually `regMin 2 κ_n Ψ_n K ≤ λ_{p,F}(K)/p + δ`.

For `p ≥ 2` this is the easy half: `h_R ≤ s^p/p` (`truncPow_le_rpow_div`) gives
`Ψ_p ≤ (F + Mε)^p/p` (`exists_truncSmoothedProfile_le`), so for a *fixed* smooth test function
`f` normalized in `L^p`, the substitution identities `homogeneousDensity_regProfile_rpow` and
`entropyPotential_two_rpow` applied to `w = |f|^{p/2}` turn the regularized energy into
`(1/p) ∫ (F(∇f) + Mε‖∇f‖…)^p + O(κ)`, which tends to `(1/p)∫F(∇f)^p` by dominated convergence;
then take `f` almost optimal for `lambdaGen p F K`.

For `p < 2` the profile is *above* `s^p/p`, and the competitor must be chosen so that
`F(∇u/u) ≤ R` on the region that matters: Revision 2 uses `u = g^k` with
`g = (f² + τ)^{1/(2k)} η`, `η` a cutoff, so that `∇u/u = k ∇g/g` is bounded by a constant
depending on `f`, `τ` and `η` but not on `R`; for `R` large enough the truncation is then
invisible and the previous computation applies. -/
theorem eventually_regMin_le (hp : 1 < p) (hF : IsSmoothStrictNorm F) {K : Set (Euc d)}
    (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      regMin 2 (regKappa n) (regProfileSeq p F n) K ≤ lambdaGen p F K / p + δ := by
  have hRlim : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hεlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact eventually_regMin_le_of_params hp hF hK hδ
    (Rs := fun n => (n : ℝ) + 1) (εs := fun n => 1 / ((n : ℝ) + 1)) (κs := regKappa)
    (ρs := regKernel) (fun n => by positivity) hRlim (fun n => isMollifier_regKernel n) hεlim
    regKappa_pos tendsto_regKappa

/-- **The lower scalar limit** (`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*):
eventually `λ_{p,F}(K)/p - δ ≤ regMin 2 κ_n Ψ_n K`.

For `p ≤ 2` this is the easy half: `s^p/p ≤ h_R` (`rpow_div_le_truncPow`) and Jensen
(`truncProfile_le_truncSmoothedProfile`) give `F^p/p ≤ Ψ_p`, so for any admissible `w` the
kinetic part of `regEnergy 2 κ Ψ w` is at least `(1/p) ∫ F(∇u)^p` with `u = w^{2/p}`, which is
at least `lambdaSob p F K / p = lambdaGen p F K / p` (`lambdaSob_mul_le`,
`lambdaSob_eq_lambdaGen`); finiteness of the regularized energy for `p ≤ 2` is exactly what
puts `u` in `W₀^{1,p}(K)`.  The entropy is controlled by Jensen,
`∫ ρ̃ log ρ̃ ≥ -log |K|` for `ρ̃ = w²`, so it contributes at most `C_K κ_n → 0`.

For `p > 2` the profile is below `s^p/p` and this argument is unavailable: Revision 2 obtains
the lower bound from compactness (`u_n^{p/2}` bounded in `W^{1,2}`), lower semicontinuity of
the convex kinetic functional, and monotone convergence in `R` (`truncPow` is nondecreasing in
`R`, with limit `s^p/p`). -/
theorem eventually_le_regMin (hp : 1 < p) (hF : IsSmoothStrictNorm F) {K : Set (Euc d)}
    (hK : IsGoodConvex K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      lambdaGen p F K / p - δ ≤ regMin 2 (regKappa n) (regProfileSeq p F n) K := by
  have hRlim : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hεlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact eventually_le_regMin_of_params hp hF hK hδ
    (Rs := fun n => (n : ℝ) + 1) (εs := fun n => 1 / ((n : ℝ) + 1)) (κs := regKappa)
    (ρs := regKernel) (fun n => by positivity) hRlim (fun n => isMollifier_regKernel n) hεlim
    regKappa_pos tendsto_regKappa

/-- **The scalar limit** `m_n(K) → λ_{p,F}(K)/p` along the canonical parameter sequence
(`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*).  This is the only statement about the
regularized minima that the assembly in
`Komlos/Literature/Regularized/EigenvalueConvexityReg.lean` consumes. -/
theorem tendsto_regMin (hp : 1 < p) (hF : IsSmoothStrictNorm F) {K : Set (Euc d)}
    (hK : IsGoodConvex K) :
    Tendsto (fun n : ℕ => regMin 2 (regKappa n) (regProfileSeq p F n) K) atTop
      (𝓝 (lambdaGen p F K / p)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hδ : 0 < (lambdaGen p F K / p - a) / 2 := by linarith
    filter_upwards [eventually_le_regMin hp hF hK hδ] with n hn
    linarith
  · intro b hb
    have hδ : 0 < (b - lambdaGen p F K / p) / 2 := by linarith
    filter_upwards [eventually_regMin_le hp hF hK hδ] with n hn
    linarith

end Limits

end Komlos.Literature.Regularized
