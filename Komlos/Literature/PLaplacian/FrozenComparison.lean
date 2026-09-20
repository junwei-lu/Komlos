import Komlos.Literature.PLaplacian.GradientBound

/-!
# Translation invariance, the ball Poincaré constant, and the frozen-coefficient comparison

This file supplies the analytic inputs of the **freezing (comparison) step** of the interior
Schauder estimate (Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Theorem 8.32, step 2), which is assembled in
`Komlos.Literature.exists_frozen_comparison` (`PLaplacian/SchauderHarmonic.lean`).

## Contents

* **Translation invariance** (`locallyIntegrable_comp_sub`, `HasWeakGradient.comp_sub`,
  `MemW0.comp_sub`, `eLpNorm_comp_sub`).  The repo's Dirichlet–Poincaré inequality
  `MemW0.eLpNorm_le_eLpNorm_weakGrad` uses as its constant the diameter of an **origin-centred**
  ball containing the domain; translating the whole `W₀^{1,p}` package turns it into
  `MemW0.eLpNorm_le_eLpNorm_weakGrad_closedBall`, the Poincaré inequality on `B̄(c, s)` with the
  scale-correct constant `T > 2 s`, *independent of the centre* `c`.
* **The real-integral `L²` form** (`integral_norm_sq_eq_sq_eLpNorm`,
  `MemW0.integral_sq_le_of_closedBall`): `∫ |f|² ≤ T² ∫ ‖∇f‖²` for `f ∈ W₀^{1,2}(B̄(c,s))`.
* **The quadratic norm and its flux** (`isSmoothStrictNorm_normComp`, `flux_two_normComp`):
  for a self-adjoint invertible `L` with `L ∘ L = A₀`, the function `ξ ↦ ‖L ξ‖` is an
  `IsSmoothStrictNorm` whose flux at `p = 2` is the linear map `A₀` itself, so that the frozen
  equation `div (A₀ ∇h) = 0` is the Euler–Lagrange equation of the direct method for
  `∫ ‖L ∇h‖²` (`exists_pharmonic_replacement` with `p = 2`).
* **The comparison estimate itself** (`frozen_energy_estimate`): the quantitative core of the
  freezing step.  Testing the difference of the two weak equations with `ψ = w - h` and using
  ellipticity, the coefficient oscillation `‖A(x) - A(y)‖ ≤ Λ s^α`, the interior sup bound
  `‖∇w‖ ≤ M` and the Poincaré inequality above gives
  `∫_{B̄(x,s)} ‖∇w - ∇h‖² ≤ C(d, α, μ, Λ, M) s^{d + 2α}`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace

open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Translation invariance of local integrability -/

/-- The translate of a locally integrable function is locally integrable. -/
theorem locallyIntegrable_comp_sub {E : Type*} [NormedAddCommGroup E] {f : Euc d → E}
    (hf : LocallyIntegrable f volume) (v : Euc d) :
    LocallyIntegrable (fun x => f (x - v)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Euc d), S = (fun y : Euc d => y - v) '' K := ⟨_, rfl⟩
  have hScpt : IsCompact S := by
    rw [hSdef]
    exact hK.image (continuous_id.sub continuous_const)
  have hSint : Integrable (S.indicator f) volume :=
    (hf.integrableOn_isCompact hScpt).integrable_indicator hScpt.isClosed.measurableSet
  have h2 : Integrable (fun x : Euc d => (S.indicator f) (x - v)) volume :=
    hSint.comp_sub_right v
  rw [← integrable_indicator_iff hK.isClosed.measurableSet]
  have he : K.indicator (fun x : Euc d => f (x - v)) =
      fun x : Euc d => (S.indicator f) (x - v) := by
    funext x
    by_cases hx : x ∈ K
    · have hxS : x - v ∈ S := by
        rw [hSdef]
        exact ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx (fun z : Euc d => f (z - v)), Set.indicator_of_mem hxS f]
    · have hxS : x - v ∉ S := by
        rw [hSdef]
        rintro ⟨y, hy, hyx⟩
        have hyx' : y = x := by
          have h := congrArg (fun z : Euc d => z + v) hyx
          simpa using h
        exact hx (hyx' ▸ hy)
      rw [Set.indicator_of_notMem hx (fun z : Euc d => f (z - v)),
        Set.indicator_of_notMem hxS f]
  rw [he]
  exact h2

/-! ### Translation invariance of the weak gradient and of `W₀^{1,p}` -/

/-- **Translation invariance of the weak gradient**: if `g` is a weak gradient of `f`, then
`g (· - v)` is a weak gradient of `f (· - v)`.  (Change of variables in the integration-by-parts
identity, with the pulled-back test function `ψ (· + v)`; compare
`HasWeakGradient.comp_dilate` in `Sobolev/Density.lean`.) -/
theorem HasWeakGradient.comp_sub {f : Euc d → ℝ} {g : Euc d → Euc d}
    (hfg : HasWeakGradient f g) (v : Euc d) :
    HasWeakGradient (fun x => f (x - v)) (fun x => g (x - v)) := by
  refine ⟨locallyIntegrable_comp_sub hfg.locallyIntegrable v,
    locallyIntegrable_comp_sub hfg.locallyIntegrable_grad v, fun ψ hψ hψs w => ?_⟩
  obtain ⟨ψ', hψ'def⟩ : ∃ ψ' : Euc d → ℝ, ψ' = fun y => ψ (y + v) := ⟨_, rfl⟩
  have hψ'app : ∀ y : Euc d, ψ' y = ψ (y + v) := fun y => by rw [hψ'def]
  have hcancel : ∀ x : Euc d, x - v + v = x := fun x => by abel
  have hψ'c : ContDiff ℝ ∞ ψ' := by
    rw [hψ'def]
    exact hψ.comp (contDiff_id.add contDiff_const)
  have hψ's : HasCompactSupport ψ' := by
    refine HasCompactSupport.intro (K := (fun z : Euc d => z - v) '' tsupport ψ)
      (IsCompact.image hψs (continuous_id.sub continuous_const)) fun y hy => ?_
    rw [hψ'app]
    refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
    exact ⟨y + v, hmem, by simp⟩
  have hfd : ∀ y : Euc d, fderiv ℝ ψ' y w = fderiv ℝ ψ (y + v) w := by
    intro y
    have h1 : HasFDerivAt (fun z : Euc d => z + v) (ContinuousLinearMap.id ℝ (Euc d)) y := by
      simpa using (hasFDerivAt_id y).add_const v
    have h3 : HasFDerivAt (fun z : Euc d => ψ (z + v))
        ((fderiv ℝ ψ (y + v)).comp (ContinuousLinearMap.id ℝ (Euc d))) y :=
      ((hψ.differentiable (by simp)) (y + v)).hasFDerivAt.comp y h1
    have h2 : HasFDerivAt ψ' (fderiv ℝ ψ (y + v)) y := by
      rw [hψ'def]
      simpa using h3
    rw [h2.fderiv]
  have key := hfg.integral_mul_fderiv ψ' hψ'c hψ's w
  have hL : ∀ x : Euc d, f (x - v) * fderiv ℝ ψ x w =
      (fun y : Euc d => f y * fderiv ℝ ψ' y w) (x - v) := by
    intro x
    show f (x - v) * fderiv ℝ ψ x w = f (x - v) * fderiv ℝ ψ' (x - v) w
    rw [hfd (x - v), hcancel x]
  have hR : ∀ x : Euc d, inner ℝ (g (x - v)) w * ψ x =
      (fun y : Euc d => inner ℝ (g y) w * ψ' y) (x - v) := by
    intro x
    show inner ℝ (g (x - v)) w * ψ x = inner ℝ (g (x - v)) w * ψ' (x - v)
    rw [hψ'app, hcancel x]
  have e1 : ∫ x, f (x - v) * fderiv ℝ ψ x w = ∫ y, f y * fderiv ℝ ψ' y w :=
    (integral_congr_ae (Eventually.of_forall hL)).trans
      (integral_sub_right_eq_self (fun y : Euc d => f y * fderiv ℝ ψ' y w) v)
  have e2 : ∫ x, inner ℝ (g (x - v)) w * ψ x = ∫ y, inner ℝ (g y) w * ψ' y :=
    (integral_congr_ae (Eventually.of_forall hR)).trans
      (integral_sub_right_eq_self (fun y : Euc d => inner ℝ (g y) w * ψ' y) v)
  show ∫ x, f (x - v) * fderiv ℝ ψ x w = -∫ x, inner ℝ (g (x - v)) w * ψ x
  rw [e1, e2]
  exact key

/-- **Translation invariance of `W₀^{1,p}`**: `f ∈ W₀^{1,p}(K)` implies
`f (· - v) ∈ W₀^{1,p}(v + K)`, with weak gradient `∇f (· - v)`. -/
theorem MemW0.comp_sub {q : ℝ} {K : Set (Euc d)} {f : Euc d → ℝ} (hf : MemW0 q K f) (v : Euc d) :
    MemW0 q {x : Euc d | x - v ∈ K} (fun x => f (x - v)) := by
  have hmp : MeasurePreserving (fun x : Euc d => x - v) volume volume :=
    measurePreserving_sub_right volume v
  refine ⟨hf.memLp.comp_measurePreserving hmp,
    hmp.quasiMeasurePreserving.ae (p := fun y : Euc d => y ∉ K → f y = 0) hf.ae_eq_zero,
    ⟨fun x => weakGrad f (x - v), hf.hasWeakGradient.comp_sub v,
      hf.memLp_weakGrad.comp_measurePreserving hmp⟩⟩

/-- Translation invariance of the `L^q` seminorm. -/
theorem eLpNorm_comp_sub {E : Type*} [NormedAddCommGroup E] {F : Euc d → E}
    (hF : AEStronglyMeasurable F volume) (v : Euc d) (q : ℝ≥0∞) :
    eLpNorm (fun x => F (x - v)) q volume = eLpNorm F q volume :=
  eLpNorm_comp_measurePreserving hF (measurePreserving_sub_right volume v)

/-! ### The Poincaré inequality on a ball, with a scale-correct constant -/

/-- **Dirichlet Poincaré inequality on an arbitrary ball** (the centre-free form of
`MemW0.eLpNorm_le_eLpNorm_weakGrad`): for `f ∈ W₀^{1,q}(B̄(c, s))`, `1 < q` and any `T > 2 s`,
`‖f‖_{L^q} ≤ T ‖∇f‖_{L^q}`.  The constant depends only on the *radius*, not on the distance of
the ball to the origin: this is what makes the freezing estimate scale correctly. -/
theorem MemW0.eLpNorm_le_eLpNorm_weakGrad_closedBall (hd : 0 < d) {q : ℝ} (hq : 1 < q)
    {c : Euc d} {s : ℝ} (hs : 0 ≤ s) {f : Euc d → ℝ}
    (hf : MemW0 q (Metric.closedBall c s) f) {T : ℝ} (hT : 2 * s < T) :
    eLpNorm f (ENNReal.ofReal q) ≤
      ENNReal.ofReal T * eLpNorm (weakGrad f) (ENNReal.ofReal q) := by
  obtain ⟨F, hFdef⟩ : ∃ F : Euc d → ℝ, F = fun x => f (x - -c) := ⟨_, rfl⟩
  have hset : {x : Euc d | x - -c ∈ Metric.closedBall c s} = Metric.closedBall (0 : Euc d) s := by
    ext x
    have h : dist (x - -c) c = dist x 0 := by
      rw [dist_eq_norm, dist_eq_norm, sub_neg_eq_add, add_sub_cancel_right, sub_zero]
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, h]
  have hFmem : MemW0 q (Metric.closedBall (0 : Euc d) s) F := by
    rw [hFdef, ← hset]
    exact hf.comp_sub (-c)
  have hgrad : HasWeakGradient F (fun x => weakGrad f (x - -c)) := by
    rw [hFdef]
    exact hf.hasWeakGradient.comp_sub (-c)
  have hpo := hFmem.eLpNorm_le_eLpNorm_weakGrad hd hq hs Set.Subset.rfl hT
  have e1 : eLpNorm F (ENNReal.ofReal q) = eLpNorm f (ENNReal.ofReal q) := by
    rw [hFdef]
    exact eLpNorm_comp_sub hf.memLp.aestronglyMeasurable (-c) _
  have e2 : eLpNorm (weakGrad F) (ENNReal.ofReal q) =
      eLpNorm (weakGrad f) (ENNReal.ofReal q) := by
    rw [eLpNorm_congr_ae hgrad.weakGrad_ae_eq]
    exact eLpNorm_comp_sub hf.memLp_weakGrad.aestronglyMeasurable (-c) _
  rw [← e1, ← e2]
  exact hpo

/-! ### The `L²` Poincaré inequality on a ball in real-integral form -/

/-- For an `L²` function, the integral of `‖·‖²` is the square of the `L²` seminorm. -/
theorem integral_norm_sq_eq_sq_eLpNorm {E : Type*} [NormedAddCommGroup E] {F : Euc d → E}
    (hF : MemLp F (ENNReal.ofReal 2)) :
    (∫ x, ‖F x‖ ^ 2) = (eLpNorm F (ENNReal.ofReal 2) volume).toReal ^ 2 := by
  have h0 : (ENNReal.ofReal (2 : ℝ)) ≠ 0 := by simp
  have htop : (ENNReal.ofReal (2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htr : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by
    rw [ENNReal.toReal_ofReal]
    norm_num
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ x, ‖F x‖ ^ ((ENNReal.ofReal (2 : ℝ)).toReal) := ⟨_, rfl⟩
  have hI0 : (0 : ℝ) ≤ I := by
    rw [hIdef]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hIeq : I = ∫ x, ‖F x‖ ^ (2 : ℕ) := by
    rw [hIdef]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖F x‖ ^ ((ENNReal.ofReal (2 : ℝ)).toReal) = ‖F x‖ ^ (2 : ℕ)
    rw [htr, ← Real.rpow_natCast ‖F x‖ 2]
    norm_num
  have hmul : ((ENNReal.ofReal (2 : ℝ)).toReal)⁻¹ * ((2 : ℕ) : ℝ) = 1 := by
    rw [htr]
    norm_num
  have hstep : (I ^ ((ENNReal.ofReal (2 : ℝ)).toReal)⁻¹) ^ (2 : ℕ) = I := by
    rw [← Real.rpow_natCast (I ^ ((ENNReal.ofReal (2 : ℝ)).toReal)⁻¹) 2,
      ← Real.rpow_mul hI0, hmul, Real.rpow_one]
  rw [hF.eLpNorm_eq_integral_rpow_norm h0 htop, ← hIdef,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hI0 _), hstep]
  exact hIeq.symm

/-- **The `L²` Poincaré inequality on a ball in real-integral form**: for `f ∈ W₀^{1,2}(B̄(c,s))`
and `T > 2 s`, `∫ |f|² ≤ T² ∫ ‖∇f‖²`.  The constant is proportional to the radius. -/
theorem MemW0.integral_sq_le_of_closedBall (hd : 0 < d) {c : Euc d} {s : ℝ} (hs : 0 ≤ s)
    {f : Euc d → ℝ} (hf : MemW0 2 (Metric.closedBall c s) f) {T : ℝ} (hT : 2 * s < T) :
    (∫ x, f x ^ 2) ≤ T ^ 2 * ∫ x, ‖weakGrad f x‖ ^ 2 := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hpo := hf.eLpNorm_le_eLpNorm_weakGrad_closedBall hd one_lt_two hs hT
  have hfin : eLpNorm (weakGrad f) (ENNReal.ofReal 2) volume ≠ ⊤ :=
    hf.memLp_weakGrad.eLpNorm_lt_top.ne
  have hmulne : (ENNReal.ofReal T * eLpNorm (weakGrad f) (ENNReal.ofReal 2) volume) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hre : (eLpNorm f (ENNReal.ofReal 2) volume).toReal ≤
      T * (eLpNorm (weakGrad f) (ENNReal.ofReal 2) volume).toReal := by
    have h := ENNReal.toReal_mono hmulne hpo
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hT0] at h
  have hA : (∫ x, f x ^ 2) = (eLpNorm f (ENNReal.ofReal 2) volume).toReal ^ 2 := by
    rw [← integral_norm_sq_eq_sq_eLpNorm hf.memLp]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show f x ^ 2 = ‖f x‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs]
  have hB : (∫ x, ‖weakGrad f x‖ ^ 2) =
      (eLpNorm (weakGrad f) (ENNReal.ofReal 2) volume).toReal ^ 2 :=
    integral_norm_sq_eq_sq_eLpNorm hf.memLp_weakGrad
  have ha0 : (0 : ℝ) ≤ (eLpNorm f (ENNReal.ofReal 2) volume).toReal := ENNReal.toReal_nonneg
  have hb0 : (0 : ℝ) ≤ (eLpNorm (weakGrad f) (ENNReal.ofReal 2) volume).toReal :=
    ENNReal.toReal_nonneg
  rw [hA, hB]
  nlinarith [hre, ha0, hb0, hT0, mul_le_mul hre hre ha0 (mul_nonneg hT0 hb0)]

/-! ### The absorption step -/

/-- **The absorption step of the freezing estimate.**  Suppose `μ E ≤ a I + b J`, where `I` and
`J` obey the Young inequalities `2 t I ≤ E + t² m` and `2 t J ≤ T² E + t² m` for every `t > 0`
(the repo's `two_mul_setIntegral_le_setIntegral_sq_add`, applied to `‖∇(w - h)‖` and — after the
Poincaré inequality — to `|w - h|`).  Then, for every regularizer `θ > 0`,
`μ² E ≤ (2 a² + 2 b² T² + (a + b) θ) m`.

Choosing the two Young parameters `t = (2a + θ)/μ` and `u = (2 b T² + θ)/μ` puts *half* of `μ E`
on the right-hand side, where it is absorbed; the regularizer `θ` only serves to keep `t, u > 0`
when `a` or `b T²` vanishes.  This is Cauchy–Schwarz with the optimal constant, obtained without
leaving the ordered-field fragment. -/
theorem frozen_energy_absorb {μ a b T E I J m θ : ℝ} (hμ : 0 < μ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 ≤ m) (hθ : 0 < θ) (hE : 0 ≤ E)
    (hmain : μ * E ≤ a * I + b * J)
    (hY1 : ∀ t : ℝ, 0 < t → 2 * t * I ≤ E + t ^ 2 * m)
    (hY2 : ∀ t : ℝ, 0 < t → 2 * t * J ≤ T ^ 2 * E + t ^ 2 * m) :
    μ ^ 2 * E ≤ (2 * a ^ 2 + 2 * b ^ 2 * T ^ 2 + (a + b) * θ) * m := by
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (2 * a + θ) / μ := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = (2 * b * T ^ 2 + θ) / μ := ⟨_, rfl⟩
  have hbT : (0 : ℝ) ≤ b * T ^ 2 := mul_nonneg hb (sq_nonneg T)
  have ht0 : 0 < t := by
    rw [htdef]
    exact div_pos (by linarith) hμ
  have hu0 : 0 < u := by
    rw [hudef]
    exact div_pos (by linarith) hμ
  have hμne : μ ≠ 0 := hμ.ne'
  have htμ : μ * t = 2 * a + θ := by
    rw [htdef]
    field_simp
  have huμ : μ * u = 2 * b * T ^ 2 + θ := by
    rw [hudef]
    field_simp
  have hθE : (0 : ℝ) ≤ θ / 2 * E := mul_nonneg (by linarith) hE
  -- the first absorbed bound
  have hkey1 : a * I * (2 * t) ≤ μ * t / 2 * E + a * t ^ 2 * m := by
    have hstep : a * (2 * t * I) ≤ a * (E + t ^ 2 * m) :=
      mul_le_mul_of_nonneg_left (hY1 t ht0) ha
    have hexp : μ * t / 2 * E = a * E + θ / 2 * E := by
      rw [htμ]; ring
    linarith
  have h1 : a * I ≤ μ / 4 * E + a * t / 2 * m := by
    have h2t : (0 : ℝ) < 2 * t := by linarith
    have hrw : μ * t / 2 * E + a * t ^ 2 * m = (μ / 4 * E + a * t / 2 * m) * (2 * t) := by ring
    rw [hrw] at hkey1
    exact le_of_mul_le_mul_right hkey1 h2t
  -- the second absorbed bound
  have hkey2 : b * J * (2 * u) ≤ μ * u / 2 * E + b * u ^ 2 * m := by
    have hstep : b * (2 * u * J) ≤ b * (T ^ 2 * E + u ^ 2 * m) :=
      mul_le_mul_of_nonneg_left (hY2 u hu0) hb
    have hexp : μ * u / 2 * E = b * T ^ 2 * E + θ / 2 * E := by
      rw [huμ]; ring
    linarith
  have h2 : b * J ≤ μ / 4 * E + b * u / 2 * m := by
    have h2u : (0 : ℝ) < 2 * u := by linarith
    have hrw : μ * u / 2 * E + b * u ^ 2 * m = (μ / 4 * E + b * u / 2 * m) * (2 * u) := by ring
    rw [hrw] at hkey2
    exact le_of_mul_le_mul_right hkey2 h2u
  have h5 : μ * E ≤ (a * t + b * u) * m := by linarith
  have h8 : μ * ((a * t + b * u) * m) =
      (2 * a ^ 2 + 2 * b ^ 2 * T ^ 2 + (a + b) * θ) * m := by
    have hab : μ * (a * t + b * u) = a * (μ * t) + b * (μ * u) := by ring
    rw [← mul_assoc, hab, htμ, huμ]
    ring
  calc μ ^ 2 * E = μ * (μ * E) := by ring
    _ ≤ μ * ((a * t + b * u) * m) := mul_le_mul_of_nonneg_left h5 hμ.le
    _ = (2 * a ^ 2 + 2 * b ^ 2 * T ^ 2 + (a + b) * θ) * m := h8

/-! ### The frozen-coefficient comparison estimate -/

/-- **The frozen-coefficient comparison estimate** (Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Theorem 8.32, step 2; the quantitative core of the
freezing argument).

Let `W = ∇w` solve `div (A ∇w) = g` weakly on `B̄(x, s)` and let `H = ∇h` solve the **frozen**
equation `div (A₀ ∇h) = 0`, with `ψ = w - h ∈ W₀^{1,2}(B̄(x,s))` — so that `∇ψ` is `W - H` on the
ball and `0` outside.  Testing the difference of the two equations with `ψ`:

* ellipticity gives `μ ∫ ‖W - H‖² ≤ ∫ ⟪A₀ (W - H), W - H⟫`;
* the frozen equation kills `∫ ⟪A₀ H, ∇ψ⟫`;
* the coefficient oscillation `‖A₀ - A y‖ ≤ Λ s^α` and the interior gradient bound `‖W‖ ≤ M`
  control the first error term by `Λ s^α M ∫ ‖W - H‖`;
* `|g| ≤ Λ` and the Poincaré inequality on the ball (constant `3 s`) control the second by
  `Λ ∫ |ψ| ≲ Λ s (∫ ‖W - H‖²)^{1/2} |B|^{1/2}`.

Young's inequality (`frozen_energy_absorb`) then absorbs the energy on the right, giving
`∫_{B̄(x,s)} ‖W - H‖² ≤ C(d, μ, Λ, M) s^{d + 2α}` with `C` *independent of the data*. -/
theorem frozen_energy_estimate_of_integrable (hd : 0 < d) {α μ Λ M s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hμ : 0 < μ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (hs : 0 < s) (hs1 : s ≤ 1)
    {x : Euc d} {A₀ : Euc d →L[ℝ] Euc d} {A : Euc d → Euc d →L[ℝ] Euc d} {g ψ : Euc d → ℝ}
    {W H : Euc d → Euc d}
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    (hosc : ∀ y ∈ Metric.closedBall x s, ‖A₀ - A y‖ ≤ Λ * s ^ α)
    (hgbd : ∀ y ∈ Metric.closedBall x s, |g y| ≤ Λ)
    (hWbd : ∀ y ∈ Metric.closedBall x s, ‖W y‖ ≤ M)
    (iD1 : IntegrableOn (fun y => ‖W y - H y‖) (Metric.closedBall x s))
    (iD2 : IntegrableOn (fun y => ‖W y - H y‖ ^ 2) (Metric.closedBall x s))
    (iψ1 : IntegrableOn (fun y => |ψ y|) (Metric.closedBall x s))
    (iψ2 : IntegrableOn (fun y => ψ y ^ 2) (Metric.closedBall x s))
    (iAD : IntegrableOn (fun y => ⟪A₀ (W y - H y), W y - H y⟫) (Metric.closedBall x s))
    (iAW : IntegrableOn (fun y => ⟪A₀ (W y), W y - H y⟫) (Metric.closedBall x s))
    (iAH : IntegrableOn (fun y => ⟪A₀ (H y), W y - H y⟫) (Metric.closedBall x s))
    (iosc : IntegrableOn (fun y => ⟪(A₀ - A y) (W y), W y - H y⟫)
      (Metric.closedBall x s))
    (iAyW : IntegrableOn (fun y => ⟪A y (W y), W y - H y⟫) (Metric.closedBall x s))
    (igψ : IntegrableOn (fun y => g y * ψ y) (Metric.closedBall x s))
    (hψW : MemW0 2 (Metric.closedBall x s) ψ)
    (hψgrad : weakGrad ψ =ᵐ[volume]
      (Metric.closedBall x s).indicator (fun y => W y - H y))
    (heqw : (∫ y, ⟪A y (W y), weakGrad ψ y⟫) = ∫ y, g y * ψ y)
    (heqh : (∫ y, ⟪A₀ (H y), weakGrad ψ y⟫) = 0) :
    (∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2) ≤
      volume.real (Metric.closedBall (0 : Euc d) 1) *
        (2 * Λ ^ 2 * M ^ 2 + 18 * Λ ^ 2 + Λ * M + Λ) / μ ^ 2 * s ^ ((d : ℝ) + 2 * α) := by
  have hBcpt : IsCompact (Metric.closedBall x s) := isCompact_closedBall x s
  have hBmeas : MeasurableSet (Metric.closedBall x s) := hBcpt.isClosed.measurableSet
  have hBfin : volume (Metric.closedBall x s) ≠ ⊤ := hBcpt.measure_lt_top.ne
  have hm0 : (0 : ℝ) ≤ volume.real (Metric.closedBall x s) := by
    rw [measureReal_def]
    exact ENNReal.toReal_nonneg
  have hE0 : (0 : ℝ) ≤ ∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  -- rewriting global integrals against `∇ψ` as integrals over the ball
  have hconv : ∀ u : Euc d → Euc d, (∫ y, ⟪u y, weakGrad ψ y⟫) =
      ∫ y in Metric.closedBall x s, ⟪u y, W y - H y⟫ := by
    intro u
    have hpt : (fun y => ⟪u y, weakGrad ψ y⟫) =ᵐ[volume]
        (Metric.closedBall x s).indicator (fun y => ⟪u y, W y - H y⟫) := by
      filter_upwards [hψgrad] with y hy
      show ⟪u y, weakGrad ψ y⟫ =
        (Metric.closedBall x s).indicator (fun z => ⟪u z, W z - H z⟫) y
      by_cases hyB : y ∈ Metric.closedBall x s
      · rw [hy, Set.indicator_of_mem hyB (fun z => W z - H z),
          Set.indicator_of_mem hyB (fun z => ⟪u z, W z - H z⟫)]
      · rw [hy, Set.indicator_of_notMem hyB (fun z => W z - H z),
          Set.indicator_of_notMem hyB (fun z => ⟪u z, W z - H z⟫), inner_zero_right]
    rw [integral_congr_ae hpt, integral_indicator hBmeas]
  have hconvH : (∫ y, ⟪A₀ (H y), weakGrad ψ y⟫) =
      ∫ y in Metric.closedBall x s, ⟪A₀ (H y), W y - H y⟫ := hconv fun y => A₀ (H y)
  have hconvW : (∫ y, ⟪A y (W y), weakGrad ψ y⟫) =
      ∫ y in Metric.closedBall x s, ⟪A y (W y), W y - H y⟫ := hconv fun y => A y (W y)
  have heqh' : (∫ y in Metric.closedBall x s, ⟪A₀ (H y), W y - H y⟫) = 0 := by
    rw [← hconvH]
    exact heqh
  have hgψ : (∫ y, g y * ψ y) = ∫ y in Metric.closedBall x s, g y * ψ y :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero
      (hψW.ae_eq_zero.mono fun y hy hyB => by rw [hy hyB, mul_zero])).symm
  have heqw' : (∫ y in Metric.closedBall x s, ⟪A y (W y), W y - H y⟫) =
      ∫ y in Metric.closedBall x s, g y * ψ y := by
    rw [← hconvW, heqw, hgψ]
  -- ellipticity
  have hell' : μ * (∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2) ≤
      ∫ y in Metric.closedBall x s, ⟪A₀ (W y - H y), W y - H y⟫ := by
    rw [← integral_const_mul]
    exact setIntegral_mono (iD2.const_mul μ) iAD fun y => hell (W y - H y)
  -- splitting off the frozen equation
  have hdiff : (∫ y in Metric.closedBall x s, ⟪A₀ (W y - H y), W y - H y⟫) =
      (∫ y in Metric.closedBall x s, ⟪A₀ (W y), W y - H y⟫) -
        ∫ y in Metric.closedBall x s, ⟪A₀ (H y), W y - H y⟫ := by
    rw [← integral_sub iAW iAH]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ⟪A₀ (W y - H y), W y - H y⟫ =
      ⟪A₀ (W y), W y - H y⟫ - ⟪A₀ (H y), W y - H y⟫
    rw [map_sub, inner_sub_left]
  -- splitting off the coefficient oscillation
  have hsplit : (∫ y in Metric.closedBall x s, ⟪A₀ (W y), W y - H y⟫) =
      (∫ y in Metric.closedBall x s, ⟪(A₀ - A y) (W y), W y - H y⟫) +
        ∫ y in Metric.closedBall x s, ⟪A y (W y), W y - H y⟫ := by
    rw [← integral_add iosc iAyW]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ⟪A₀ (W y), W y - H y⟫ =
      ⟪(A₀ - A y) (W y), W y - H y⟫ + ⟪A y (W y), W y - H y⟫
    rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    ring
  -- the two error terms
  have hbnd1 : (∫ y in Metric.closedBall x s, ⟪(A₀ - A y) (W y), W y - H y⟫) ≤
      Λ * s ^ α * M * ∫ y in Metric.closedBall x s, ‖W y - H y‖ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on iosc (iD1.const_mul _) hBmeas fun y hy => ?_
    have h1 : ⟪(A₀ - A y) (W y), W y - H y⟫ ≤ ‖(A₀ - A y) (W y)‖ * ‖W y - H y‖ :=
      real_inner_le_norm _ _
    have h2 : ‖(A₀ - A y) (W y)‖ ≤ Λ * s ^ α * M := by
      refine ((A₀ - A y).le_opNorm (W y)).trans ?_
      exact mul_le_mul (hosc y hy) (hWbd y hy) (norm_nonneg _)
        (mul_nonneg hΛ (Real.rpow_nonneg hs.le α))
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have hbnd2 : (∫ y in Metric.closedBall x s, g y * ψ y) ≤
      Λ * ∫ y in Metric.closedBall x s, |ψ y| := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on igψ (iψ1.const_mul _) hBmeas fun y hy => ?_
    have h1 : g y * ψ y ≤ |g y| * |ψ y| := by
      rw [← abs_mul]
      exact le_abs_self _
    exact h1.trans (mul_le_mul_of_nonneg_right (hgbd y hy) (abs_nonneg _))
  -- the main inequality fed to the absorption lemma
  have hmain : μ * (∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2) ≤
      Λ * s ^ α * M * (∫ y in Metric.closedBall x s, ‖W y - H y‖) +
        Λ * ∫ y in Metric.closedBall x s, |ψ y| := by
    rw [hdiff, heqh', hsplit, heqw'] at hell'
    linarith [hell', hbnd1, hbnd2]
  -- the two Young inequalities
  have hY1 : ∀ t : ℝ, 0 < t →
      2 * t * (∫ y in Metric.closedBall x s, ‖W y - H y‖) ≤
        (∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2) +
          t ^ 2 * volume.real (Metric.closedBall x s) :=
    fun t _ => two_mul_setIntegral_le_setIntegral_sq_add iD1 iD2 hBfin (t := t)
  have hψsq : (∫ y in Metric.closedBall x s, ψ y ^ 2) = ∫ y, ψ y ^ 2 :=
    setIntegral_eq_integral_of_ae_compl_eq_zero
      (hψW.ae_eq_zero.mono fun y hy hyB => by rw [hy hyB]; norm_num)
  have hgradsq : (∫ y, ‖weakGrad ψ y‖ ^ 2) =
      ∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2 := by
    have hpt : (fun y => ‖weakGrad ψ y‖ ^ 2) =ᵐ[volume]
        (Metric.closedBall x s).indicator (fun y => ‖W y - H y‖ ^ 2) := by
      filter_upwards [hψgrad] with y hy
      show ‖weakGrad ψ y‖ ^ 2 =
        (Metric.closedBall x s).indicator (fun z => ‖W z - H z‖ ^ 2) y
      by_cases hyB : y ∈ Metric.closedBall x s
      · rw [hy, Set.indicator_of_mem hyB (fun z => W z - H z),
          Set.indicator_of_mem hyB (fun z => ‖W z - H z‖ ^ 2)]
      · rw [hy, Set.indicator_of_notMem hyB (fun z => W z - H z),
          Set.indicator_of_notMem hyB (fun z => ‖W z - H z‖ ^ 2), norm_zero]
        norm_num
    rw [integral_congr_ae hpt, integral_indicator hBmeas]
  have hQ : (∫ y in Metric.closedBall x s, ψ y ^ 2) ≤
      (3 * s) ^ 2 * ∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2 := by
    have h := hψW.integral_sq_le_of_closedBall hd hs.le (T := 3 * s) (by linarith)
    rwa [← hψsq, hgradsq] at h
  have hY2 : ∀ t : ℝ, 0 < t →
      2 * t * (∫ y in Metric.closedBall x s, |ψ y|) ≤
        (3 * s) ^ 2 * (∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2) +
          t ^ 2 * volume.real (Metric.closedBall x s) := by
    intro t _
    have h := two_mul_setIntegral_le_setIntegral_sq_add iψ1
      (by simpa only [sq_abs] using iψ2) hBfin (t := t)
    have habs : (∫ y in Metric.closedBall x s, |ψ y| ^ 2) =
        ∫ y in Metric.closedBall x s, ψ y ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun y => sq_abs (ψ y))
    rw [habs] at h
    linarith [h, hQ]
  -- absorption
  have ha0 : (0 : ℝ) ≤ Λ * s ^ α * M :=
    mul_nonneg (mul_nonneg hΛ (Real.rpow_nonneg hs.le α)) hM
  have hθ0 : (0 : ℝ) < s ^ (2 * α) := Real.rpow_pos_of_pos hs _
  have habs := frozen_energy_absorb (μ := μ) (a := Λ * s ^ α * M) (b := Λ) (T := 3 * s)
    (E := ∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2)
    (I := ∫ y in Metric.closedBall x s, ‖W y - H y‖)
    (J := ∫ y in Metric.closedBall x s, |ψ y|)
    (m := volume.real (Metric.closedBall x s)) (θ := s ^ (2 * α))
    hμ ha0 hΛ hm0 hθ0 hE0 hmain hY1 hY2
  -- the elementary power bookkeeping
  have hpow2 : (s ^ α) ^ (2 : ℕ) = s ^ (2 * α) := by
    rw [← Real.rpow_natCast (s ^ α) 2, ← Real.rpow_mul hs.le]
    congr 1
    push_cast
    ring
  have hs2 : s ^ (2 : ℕ) ≤ s ^ (2 * α) := by
    have h1 : s ^ (2 : ℕ) = s ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast s 2]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have hs3 : s ^ (3 * α) ≤ s ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have hsα3 : s ^ α * s ^ (2 * α) = s ^ (3 * α) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hP : volume.real (Metric.closedBall x s) =
      s ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) := volume_real_closedBall x hs.le
  have hsd : s ^ (2 * α) * s ^ d = s ^ ((d : ℝ) + 2 * α) := by
    rw [← Real.rpow_natCast s d, ← Real.rpow_add hs]
    congr 1
    ring
  have hNC : 2 * (Λ * s ^ α * M) ^ 2 + 2 * Λ ^ 2 * (3 * s) ^ 2 +
      (Λ * s ^ α * M + Λ) * s ^ (2 * α) ≤
      (2 * Λ ^ 2 * M ^ 2 + 18 * Λ ^ 2 + Λ * M + Λ) * s ^ (2 * α) := by
    have e1 : 2 * (Λ * s ^ α * M) ^ 2 = 2 * Λ ^ 2 * M ^ 2 * s ^ (2 * α) := by
      rw [← hpow2]; ring
    have e2 : 2 * Λ ^ 2 * (3 * s) ^ 2 = 18 * Λ ^ 2 * s ^ (2 : ℕ) := by ring
    have e3 : (Λ * s ^ α * M + Λ) * s ^ (2 * α) =
        Λ * M * s ^ (3 * α) + Λ * s ^ (2 * α) := by
      rw [← hsα3]; ring
    have h1 : 18 * Λ ^ 2 * s ^ (2 : ℕ) ≤ 18 * Λ ^ 2 * s ^ (2 * α) :=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    have h2 : Λ * M * s ^ (3 * α) ≤ Λ * M * s ^ (2 * α) :=
      mul_le_mul_of_nonneg_left hs3 (mul_nonneg hΛ hM)
    rw [e1, e2, e3]
    nlinarith [h1, h2]
  have hfinal : (2 * (Λ * s ^ α * M) ^ 2 + 2 * Λ ^ 2 * (3 * s) ^ 2 +
      (Λ * s ^ α * M + Λ) * s ^ (2 * α)) * volume.real (Metric.closedBall x s) ≤
      volume.real (Metric.closedBall (0 : Euc d) 1) *
        (2 * Λ ^ 2 * M ^ 2 + 18 * Λ ^ 2 + Λ * M + Λ) * s ^ ((d : ℝ) + 2 * α) := by
    refine (mul_le_mul_of_nonneg_right hNC hm0).trans (le_of_eq ?_)
    rw [hP, ← hsd]
    ring
  have hmu2 : (0 : ℝ) < μ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hmu2]
  linarith [habs, hfinal]

/-- The continuous-data form of `frozen_energy_estimate_of_integrable`, preserving the
original freezing estimate (Gilbarg–Trudinger, Theorem 8.32, step 2).  Continuity on the
closed ball is used only to supply the integrability hypotheses of the more general theorem. -/
theorem frozen_energy_estimate (hd : 0 < d) {α μ Λ M s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hμ : 0 < μ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (hs : 0 < s) (hs1 : s ≤ 1)
    {x : Euc d} {A₀ : Euc d →L[ℝ] Euc d} {A : Euc d → Euc d →L[ℝ] Euc d} {g ψ : Euc d → ℝ}
    {W H : Euc d → Euc d}
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    (hosc : ∀ y ∈ Metric.closedBall x s, ‖A₀ - A y‖ ≤ Λ * s ^ α)
    (hgbd : ∀ y ∈ Metric.closedBall x s, |g y| ≤ Λ)
    (hWbd : ∀ y ∈ Metric.closedBall x s, ‖W y‖ ≤ M)
    (hAc : ContinuousOn A (Metric.closedBall x s))
    (hgc : ContinuousOn g (Metric.closedBall x s))
    (hWc : ContinuousOn W (Metric.closedBall x s))
    (hHc : ContinuousOn H (Metric.closedBall x s))
    (hψc : ContinuousOn ψ (Metric.closedBall x s))
    (hψ0 : ∀ y, y ∉ Metric.closedBall x s → ψ y = 0)
    (hψW : MemW0 2 (Metric.closedBall x s) ψ)
    (hψgrad : weakGrad ψ =ᵐ[volume]
      (Metric.closedBall x s).indicator (fun y => W y - H y))
    (heqw : (∫ y, ⟪A y (W y), weakGrad ψ y⟫) = ∫ y, g y * ψ y)
    (heqh : (∫ y, ⟪A₀ (H y), weakGrad ψ y⟫) = 0) :
    (∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2) ≤
      volume.real (Metric.closedBall (0 : Euc d) 1) *
        (2 * Λ ^ 2 * M ^ 2 + 18 * Λ ^ 2 + Λ * M + Λ) / μ ^ 2 * s ^ ((d : ℝ) + 2 * α) := by
  have hBcpt : IsCompact (Metric.closedBall x s) := isCompact_closedBall x s
  have hDc : ContinuousOn (fun y => W y - H y) (Metric.closedBall x s) := hWc.sub hHc
  refine frozen_energy_estimate_of_integrable hd hα hα1 hμ hΛ hM hs hs1 hell hosc hgbd hWbd
    (hDc.norm.integrableOn_compact hBcpt) ((hDc.norm.pow 2).integrableOn_compact hBcpt)
    ?_ ((hψc.pow 2).integrableOn_compact hBcpt)
    (((A₀.continuous.comp_continuousOn hDc).inner hDc).integrableOn_compact hBcpt)
    (((A₀.continuous.comp_continuousOn hWc).inner hDc).integrableOn_compact hBcpt)
    (((A₀.continuous.comp_continuousOn hHc).inner hDc).integrableOn_compact hBcpt)
    ((((continuousOn_const.sub hAc).clm_apply hWc).inner hDc).integrableOn_compact hBcpt)
    (((hAc.clm_apply hWc).inner hDc).integrableOn_compact hBcpt)
    ((hgc.mul hψc).integrableOn_compact hBcpt) hψW hψgrad heqw heqh
  simpa only [Real.norm_eq_abs] using hψc.norm.integrableOn_compact hBcpt

/-- Inner products of two square-integrable fields are integrable. -/
theorem integrable_inner_of_memLp_two {ν : Measure (Euc d)} {V W : Euc d → Euc d}
    (hV : MemLp V 2 ν) (hW : MemLp W 2 ν) :
    Integrable (fun y => ⟪V y, W y⟫) ν := by
  refine (hV.norm.integrable_mul hW.norm).mono'
    (hV.aestronglyMeasurable.inner hW.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun y => norm_inner_le_norm _ _

/-- The Sobolev form of the freezing estimate (Gilbarg–Trudinger, Theorem 8.32, step 2).
The frozen field only needs to be square-integrable on the ball, and the comparison function
only needs its `MemW0` regularity.  Thus no regularity at the boundary of the frozen Dirichlet
problem is needed to apply the energy estimate. -/
theorem frozen_energy_estimate_of_memLp (hd : 0 < d) {α μ Λ M s : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hμ : 0 < μ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M)
    (hs : 0 < s) (hs1 : s ≤ 1) {x : Euc d}
    {A₀ : Euc d →L[ℝ] Euc d} {A : Euc d → Euc d →L[ℝ] Euc d} {g ψ : Euc d → ℝ}
    {W H : Euc d → Euc d}
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫)
    (hosc : ∀ y ∈ Metric.closedBall x s, ‖A₀ - A y‖ ≤ Λ * s ^ α)
    (hgbd : ∀ y ∈ Metric.closedBall x s, |g y| ≤ Λ)
    (hWbd : ∀ y ∈ Metric.closedBall x s, ‖W y‖ ≤ M)
    (hAc : ContinuousOn A (Metric.closedBall x s))
    (hgc : ContinuousOn g (Metric.closedBall x s))
    (hWc : ContinuousOn W (Metric.closedBall x s))
    (hH : MemLp H 2 (volume.restrict (Metric.closedBall x s)))
    (hψW : MemW0 2 (Metric.closedBall x s) ψ)
    (hψgrad : weakGrad ψ =ᵐ[volume]
      (Metric.closedBall x s).indicator (fun y => W y - H y))
    (heqw : (∫ y, ⟪A y (W y), weakGrad ψ y⟫) = ∫ y, g y * ψ y)
    (heqh : (∫ y, ⟪A₀ (H y), weakGrad ψ y⟫) = 0) :
    (∫ y in Metric.closedBall x s, ‖W y - H y‖ ^ 2) ≤
      volume.real (Metric.closedBall (0 : Euc d) 1) *
        (2 * Λ ^ 2 * M ^ 2 + 18 * Λ ^ 2 + Λ * M + Λ) / μ ^ 2 * s ^ ((d : ℝ) + 2 * α) := by
  have hBcpt : IsCompact (Metric.closedBall x s) := isCompact_closedBall x s
  letI : IsFiniteMeasure (volume.restrict (Metric.closedBall x s)) :=
    ⟨by simpa using hBcpt.measure_lt_top (μ := volume)⟩
  have hBmeas : MeasurableSet (Metric.closedBall x s) := hBcpt.isClosed.measurableSet
  have hW : MemLp W 2 (volume.restrict (Metric.closedBall x s)) :=
    (memLp_two_iff_integrable_sq_norm (hWc.aestronglyMeasurable hBmeas)).2
      ((hWc.norm.pow 2).integrableOn_compact hBcpt)
  have hD : MemLp (fun y => W y - H y) 2 (volume.restrict (Metric.closedBall x s)) :=
    hW.sub hH
  have hψ : MemLp ψ 2 (volume.restrict (Metric.closedBall x s)) := by
    simpa using hψW.memLp.mono_measure Measure.restrict_le_self
  have hAW : MemLp (fun y => A y (W y)) 2 (volume.restrict (Metric.closedBall x s)) :=
    (memLp_two_iff_integrable_sq_norm
      ((hAc.clm_apply hWc).aestronglyMeasurable hBmeas)).2
      (((hAc.clm_apply hWc).norm.pow 2).integrableOn_compact hBcpt)
  have hoscW : MemLp (fun y => (A₀ - A y) (W y)) 2
      (volume.restrict (Metric.closedBall x s)) :=
    (memLp_two_iff_integrable_sq_norm
      (((continuousOn_const.sub hAc).clm_apply hWc).aestronglyMeasurable hBmeas)).2
      ((((continuousOn_const.sub hAc).clm_apply hWc).norm.pow 2).integrableOn_compact hBcpt)
  have hg : MemLp g 2 (volume.restrict (Metric.closedBall x s)) :=
    (memLp_two_iff_integrable_sq (hgc.aestronglyMeasurable hBmeas)).2
      ((hgc.pow 2).integrableOn_compact hBcpt)
  refine frozen_energy_estimate_of_integrable hd hα hα1 hμ hΛ hM hs hs1 hell hosc hgbd hWbd
    (hD.integrable (by norm_num)).norm
    (hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    ?_ hψ.integrable_sq
    (integrable_inner_of_memLp_two (A₀.comp_memLp' hD) hD)
    (integrable_inner_of_memLp_two (A₀.comp_memLp' hW) hD)
    (integrable_inner_of_memLp_two (A₀.comp_memLp' hH) hD)
    (integrable_inner_of_memLp_two hoscW hD) (integrable_inner_of_memLp_two hAW hD)
    (hg.integrable_mul hψ) hψW hψgrad heqw heqh
  simpa only [IntegrableOn, Real.norm_eq_abs] using (hψ.integrable (by norm_num)).norm

/-! ### Two auxiliary facts used when assembling the freezing step -/

/-- In dimension `0` every vector vanishes. -/
theorem eq_zero_of_dim_zero (z : Euc 0) : z = 0 := by
  rw [← norm_eq_zero]
  simp [EuclideanSpace.norm_eq]

/-- An `α`-Hölder bound on a set implies continuity on that set.  (The interior Schauder
hypotheses give `‖A x - A y‖ ≤ Λ ‖x - y‖^α`; the freezing estimate needs the continuity of `A`
for the integrability of the error term.) -/
theorem continuousOn_of_holder {E : Type*} [NormedAddCommGroup E] {A : Euc d → E}
    {U : Set (Euc d)} {Λ α : ℝ} (hα : 0 < α)
    (h : ∀ y ∈ U, ∀ z ∈ U, ‖A y - A z‖ ≤ Λ * dist y z ^ α) : ContinuousOn A U := by
  obtain ⟨Λ', hΛ'def⟩ : ∃ Λ' : ℝ, Λ' = max Λ 0 := ⟨_, rfl⟩
  have hΛ'0 : (0 : ℝ) ≤ Λ' := by rw [hΛ'def]; exact le_max_right _ _
  have hΛΛ' : Λ ≤ Λ' := by rw [hΛ'def]; exact le_max_left _ _
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (ε / (Λ' + 1)) ^ (1 / α) := ⟨_, rfl⟩
  have hq0 : (0 : ℝ) < ε / (Λ' + 1) := div_pos hε (by linarith)
  have hδ0 : 0 < δ := by rw [hδdef]; exact Real.rpow_pos_of_pos hq0 _
  have hδα : δ ^ α = ε / (Λ' + 1) := by
    rw [hδdef, ← Real.rpow_mul hq0.le, one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one]
  refine ⟨δ, hδ0, fun a ha hab => ?_⟩
  have h1 : dist (A a) (A b) ≤ Λ * dist a b ^ α := by
    rw [dist_eq_norm]
    exact h a ha b hb
  have h2 : dist a b ^ α ≤ δ ^ α :=
    Real.rpow_le_rpow dist_nonneg hab.le hα.le
  have h3 : Λ * dist a b ^ α ≤ Λ' * (ε / (Λ' + 1)) := by
    rw [← hδα]
    exact mul_le_mul hΛΛ' h2 (Real.rpow_nonneg dist_nonneg α) hΛ'0
  have h4 : Λ' * (ε / (Λ' + 1)) < ε := by
    have hpos : (0 : ℝ) < Λ' + 1 := by linarith
    rw [mul_comm Λ' (ε / (Λ' + 1)), div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith
  linarith
