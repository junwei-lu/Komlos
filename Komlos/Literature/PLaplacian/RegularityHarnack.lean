import Komlos.Literature.PLaplacian.RegularityInterior
import Komlos.Literature.PLaplacian.RegularityPoincare

/-!
# Positivity of weak eigensolutions (weak Harnack inequality)

Towards Mosconi–Riey–Squassina 2024, Proposition 4.5 (paper Appendix A, *Eigenfunction inputs*:
"Proposition 4.5 of [MRS24] gives positivity …"): a nonnegative weak solution `u ∈ W₀^{1,p}(K)`
of `-div a(∇u) = λ u^{p-1}` (`λ ≥ 0`) on a good convex set `K` that is not a.e. zero is bounded
below by a positive constant on every compact subset of `K` (`weak_harnack_pos`; Trudinger 1967,
*On Harnack type inequalities and their application to quasilinear elliptic equations*, Comm. Pure
Appl. Math. 20, Theorem 1.2).

## Proof

Let `ε > 0`. Testing the equation with `η^m Ψ(u)` for a nonnegative nonincreasing `Ψ` gives
`∫ η^m |Ψ'(u)| F(∇u)^p ≤ 2^p (mL)^p ∫ η^{m-p} |∇η|^p Θ(u)` whenever `Ψ^p ≤ Θ |Ψ'|^{p-1}`
(`IsWeakEigensolution.energy_le`). Two choices of `Ψ` are used.

* `Ψ(t) = (t + ε)^{1-p}` gives the **logarithmic Caccioppoli estimate**
  `∫ η^m |∇ log(u + ε)|^p ≤ C`, uniformly in `ε` (`IsWeakEigensolution.log_caccioppoli`).
* `Ψ(t) = w(t)^b (t + ε)^{1-p}` with `w(t) = log(T/(t + ε))` (`T ≥ 2 sup (u + ε)`) gives the
  energy bound `∫ η^m |∇ w(u)^β|^p ≤ C ∫ η^{m-p} |∇η|^p w(u)^{βp}` for all `β ≥ 1`, uniformly in
  `β` and `ε`: `w(u)` behaves like a subsolution. Moser's iteration with the Sobolev inequality
  and a single cutoff whose power grows geometrically bounds `sup w(u)` on a ball by the `L^p`
  norm of `w(u)` on a larger ball.

On a ball `B` where `u ≥ δ` on a set `E` of positive measure, the Poincaré inequality
`MemW0.measure_mul_lintegral_sub_rpow_le` and the logarithmic Caccioppoli estimate bound
`∫_B ((log δ - log(u + ε))^+)^p` independently of `ε`, hence the `L^p` norm of `w(u)`, hence
`sup_B w(u)`: `u + ε ≥ c > 0` on the smaller ball with `c` independent of `ε`. So every point of
`K` has a ball on which either `u = 0` a.e. or `u ≥ c > 0` a.e.; both sets of centres are open,
`K` is connected, and `u` is not a.e. zero, so the second alternative holds everywhere, and
compactness gives the uniform lower bound.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Clamping and the chain rule on an interval -/

theorem continuous_clamp (S : ℝ) : Continuous fun s : ℝ => max 0 (min s S) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp_mem {S : ℝ} (hS : 0 ≤ S) (s : ℝ) : max 0 (min s S) ∈ Icc 0 S :=
  ⟨le_max_left _ _, max_le hS (min_le_right _ _)⟩

theorem clamp_eq {S t : ℝ} (ht : t ∈ Icc 0 S) : max 0 (min t S) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- A function continuous on `[0, S]` composed with a measurable `f` taking values in `[0, S]` is
a.e.-strongly measurable and bounded. -/
theorem continuousOn_comp_aestronglyMeasurable_Icc {g : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    (hg : ContinuousOn g (Icc 0 S)) {f : Euc d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hfS : ∀ x, f x ∈ Icc 0 S) :
    AEStronglyMeasurable (fun x => g (f x)) volume ∧ ∃ C, ∀ x, |g (f x)| ≤ C := by
  have hc : Continuous fun s => g (max 0 (min s S)) :=
    hg.comp_continuous (continuous_clamp S) (clamp_mem hS)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine ⟨(hc.comp_aestronglyMeasurable hf).congr (Eventually.of_forall fun x => ?_),
    C, fun x => ?_⟩
  · simp only [clamp_eq (hfS x)]
  · rw [← Real.norm_eq_abs]
    exact hC _ (hfS x)

/-- **Chain rule for functions `C¹` on `[0, S]`**: if `f ∈ W₀^{1,p}(K)` takes values in `[0, S]`
and `Ψ` has a derivative `ψ'` at every point of `[0, S]`, continuous on `[0, S]`, then
`Ψ ∘ f - Ψ(0) ∈ W₀^{1,p}(K)` with weak gradient `ψ'(f) ∇f` (`memW0_comp` for the `C¹` function
`t ↦ ∫₀ᵗ ψ'(clamp s) ds`, which agrees with `Ψ - Ψ(0)` on `[0, S]`). -/
theorem memW0_comp_sub_of_hasDerivAt {p : ℝ} (hp : 1 < p) {K : Set (Euc d)} {f : Euc d → ℝ}
    (hf : MemW0 p K f) {S : ℝ} (hS : 0 ≤ S) (hfS : ∀ x, f x ∈ Icc 0 S) {Ψ ψ' : ℝ → ℝ}
    (hΨ : ∀ t ∈ Icc 0 S, HasDerivAt Ψ (ψ' t) t) (hψ' : ContinuousOn ψ' (Icc 0 S)) :
    MemW0 p K (fun x => Ψ (f x) - Ψ 0) ∧
      weakGrad (fun x => Ψ (f x) - Ψ 0) =ᵐ[volume] fun x => ψ' (f x) • weakGrad f x := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → ℝ, γ = fun s => ψ' (max 0 (min s S)) := ⟨_, rfl⟩
  have hγc : Continuous γ := by
    rw [hγ]
    exact hψ'.comp_continuous (continuous_clamp S) (clamp_mem hS)
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ'
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun t => ∫ s in (0 : ℝ)..t, γ s := ⟨_, rfl⟩
  have hGd : ∀ t, HasDerivAt G (γ t) t := fun t => by
    rw [hG]
    exact intervalIntegral.integral_hasDerivAt_right (hγc.intervalIntegrable _ _)
      (hγc.stronglyMeasurableAtFilter _ _) hγc.continuousAt
  have hderiv : deriv G = γ := funext fun t => (hGd t).deriv
  have hGc : ContDiff ℝ 1 G := contDiff_one_iff_deriv.2
    ⟨fun t => (hGd t).differentiableAt, by rw [hderiv]; exact hγc⟩
  have hGL : ∀ t, |deriv G t| ≤ L := fun t => by
    rw [hderiv, hγ, ← Real.norm_eq_abs]
    exact hL _ (clamp_mem hS t)
  have hG0 : G 0 = 0 := by
    rw [hG]
    exact intervalIntegral.integral_same
  obtain ⟨hGw, hGg⟩ := memW0_comp hp hf hGc hG0 hGL
  have hGΨ : ∀ t ∈ Icc 0 S, G t = Ψ t - Ψ 0 := by
    intro t ht
    rw [hG]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => ?_)
      (hγc.intervalIntegrable _ _)
    rw [uIcc_of_le ht.1] at hs
    have hs' : s ∈ Icc 0 S := ⟨hs.1, hs.2.trans ht.2⟩
    have h := hΨ s hs'
    simp only [hγ, clamp_eq hs']
    exact h
  have heq : (fun x => G (f x)) = fun x => Ψ (f x) - Ψ 0 := funext fun x => hGΨ _ (hfS x)
  rw [heq] at hGw hGg
  refine ⟨hGw, hGg.mono fun x hx => ?_⟩
  rw [hx, hderiv, hγ]
  simp only [clamp_eq (hfS x)]

/-- **Products with smooth cutoffs**: for `h ∈ W₀^{1,p}(K)`, a smooth compactly supported `ζ`
with `tsupport ζ ⊆ K` and a constant `c`, `ζ (c + h) ∈ W₀^{1,p}(K)` with weak gradient
`ζ ∇h + (c + h) ∇ζ`. -/
theorem MemW0.contDiff_mul_const_add {p : ℝ} {K : Set (Euc d)} {h : Euc d → ℝ}
    (hh : MemW0 p K h) {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ)
    (hζK : tsupport ζ ⊆ K) (c : ℝ) :
    MemW0 p K (fun x => ζ x * (c + h x)) ∧
      weakGrad (fun x => ζ x * (c + h x)) =ᵐ[volume]
        fun x => ζ x • weakGrad h x + (c + h x) • gradient ζ x := by
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  obtain ⟨A, hA⟩ := hζ.continuous.bounded_above_of_compact_support hζs
  obtain ⟨B, hB⟩ := (continuous_gradient hζ1).bounded_above_of_compact_support
    (hasCompactSupport_gradient hζs)
  obtain ⟨h1, h1g⟩ := hh.contDiff_mul hζ (A := A) (B := B)
    (fun x => by rw [← Real.norm_eq_abs]; exact hA x) hB
  have h2 : MemW0 p K (c • ζ) := (memW0_of_contDiff hζ1 hζs hζK p).smul c
  have heq : ((fun x => ζ x * h x) + c • ζ) = fun x => ζ x * (c + h x) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsum := h1.add h2
  rw [heq] at hsum
  refine ⟨hsum, ?_⟩
  have hg2 : HasWeakGradient (c • ζ) (c • gradient ζ) :=
    (hasWeakGradient_gradient hζ1 hζs).smul c
  have hg := (h1.hasWeakGradient.congr_right h1g).add hg2
  rw [heq] at hg
  refine hg.weakGrad_ae_eq.trans (Eventually.of_forall fun x => ?_)
  show ζ x • weakGrad h x + h x • gradient ζ x + c • gradient ζ x =
    ζ x • weakGrad h x + (c + h x) • gradient ζ x
  rw [add_smul]
  abel

/-! ### The weighted Young inequality -/

/-- **Young's inequality with a weight**: with `e = η(x)`, `Φ = F(∇u(x))`, `G = |∇η(x)|`,
`A = |Ψ'(u(x))|`, `Ψ = Ψ(u(x))`, `|I| ≤ L Φ^{p-1} G` and `Ψ^p ≤ Θ A^{p-1}`,
`-(m e^{m-1} Ψ I) ≤ e^m A Φ^p / 2 + 2^{p-1} (mL)^p e^{m-p} G^p Θ`
(`caccioppoli_pointwise` with `U = Θ^{1/p}` and `A^{1/p} Φ` in place of `Φ`). -/
theorem caccioppoli_pointwise_weight {p : ℝ} (hp : 1 < p) {m : ℕ} (hm : p ≤ m)
    {e Φ G I L A Ψ Θ : ℝ} (he : 0 ≤ e) (hΦ : 0 ≤ Φ) (hG : 0 ≤ G) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hΨ : 0 ≤ Ψ) (hΘ : 0 ≤ Θ) (hΨΘ : Ψ ^ p ≤ Θ * A ^ (p - 1))
    (hI : |I| ≤ L * Φ ^ (p - 1) * G) :
    -(((m : ℝ) * e ^ (m - 1)) * Ψ * I) ≤
      e ^ m * (A * Φ ^ p) / 2 +
        2 ^ (p - 1) * ((m : ℝ) * L) ^ p * (e ^ ((m : ℝ) - p) * G ^ p * Θ) := by
  have hp0 : 0 < p := by linarith
  have hU : 0 ≤ Θ ^ p⁻¹ := Real.rpow_nonneg hΘ _
  have hUp : (Θ ^ p⁻¹) ^ p = Θ := by
    rw [← Real.rpow_mul hΘ, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hAq : 0 ≤ A ^ ((p - 1) / p) := Real.rpow_nonneg hA _
  have hΦ' : 0 ≤ A ^ p⁻¹ * Φ := mul_nonneg (Real.rpow_nonneg hA _) hΦ
  have hΨle : Ψ ≤ Θ ^ p⁻¹ * A ^ ((p - 1) / p) := by
    have h1 : (Θ ^ p⁻¹ * A ^ ((p - 1) / p)) ^ p = Θ * A ^ (p - 1) := by
      rw [Real.mul_rpow hU hAq, hUp, ← Real.rpow_mul hA, div_mul_cancel₀ _ hp0.ne']
    exact (Real.rpow_le_rpow_iff hΨ (mul_nonneg hU hAq) hp0).1 (h1 ▸ hΨΘ)
  have hΦ'p : (A ^ p⁻¹ * Φ) ^ (p - 1) = A ^ ((p - 1) / p) * Φ ^ (p - 1) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA _) hΦ, ← Real.rpow_mul hA, inv_mul_eq_div]
  have hΦ'pp : (A ^ p⁻¹ * Φ) ^ p = A * Φ ^ p := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA _) hΦ, ← Real.rpow_mul hA, inv_mul_cancel₀ hp0.ne',
      Real.rpow_one]
  have hI' : |-(A ^ ((p - 1) / p) * |I|)| ≤ L * (A ^ p⁻¹ * Φ) ^ (p - 1) * G := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg hAq (abs_nonneg I)), hΦ'p]
    calc A ^ ((p - 1) / p) * |I| ≤ A ^ ((p - 1) / p) * (L * Φ ^ (p - 1) * G) :=
          mul_le_mul_of_nonneg_left hI hAq
      _ = L * (A ^ ((p - 1) / p) * Φ ^ (p - 1)) * G := by ring
  have key := caccioppoli_pointwise hp hm he hΦ' hU hG hL hI'
  rw [hΦ'pp, hUp] at key
  have hme : 0 ≤ (m : ℝ) * e ^ (m - 1) := mul_nonneg (Nat.cast_nonneg m) (pow_nonneg he _)
  calc -(((m : ℝ) * e ^ (m - 1)) * Ψ * I) = ((m : ℝ) * e ^ (m - 1)) * Ψ * (-I) := by ring
    _ ≤ ((m : ℝ) * e ^ (m - 1)) * Ψ * |I| :=
        mul_le_mul_of_nonneg_left (neg_le_abs I) (mul_nonneg hme hΨ)
    _ ≤ ((m : ℝ) * e ^ (m - 1)) * (Θ ^ p⁻¹ * A ^ ((p - 1) / p)) * |I| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΨle hme) (abs_nonneg I)
    _ = -(Θ ^ p⁻¹ * (((m : ℝ) * e ^ (m - 1)) * -(A ^ ((p - 1) / p) * |I|))) := by ring
    _ ≤ e ^ m * (A * Φ ^ p) / 2 +
          2 ^ (p - 1) * ((m : ℝ) * L) ^ p * (e ^ ((m : ℝ) - p) * G ^ p * Θ) := key

/-! ### Testing the equation with `η^m Ψ(u)` -/

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- `b ⟪a(∇u), V⟫` is integrable for bounded measurable `b` and continuous compactly supported
`V` (`F^{p-1} ≤ F^p + 1`). -/
theorem integrable_mul_inner_flux_of_hasCompactSupport (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {V : Euc d → Euc d} (hV : Continuous V)
    (hVs : HasCompactSupport V) {b : Euc d → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hB : ∀ x, |b x| ≤ B) :
    Integrable fun x => b x * ⟪flux p F (weakGrad u x), V x⟫ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨L, hL0, hL⟩ := hF.exists_norm_gradient_le
  obtain ⟨CV, hCV⟩ := hV.bounded_above_of_compact_support hVs
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hG := hu.memW0.memLp_weakGrad
  have i1 : Integrable fun x => ‖V x‖ * F (weakGrad u x) ^ p :=
    (hF.integrable_rpow_comp hp0 hG).bdd_mul hV.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [norm_norm]; exact hCV x)
  have i2 : Integrable fun x => ‖V x‖ :=
    (hV.norm.integrable_of_hasCompactSupport hVs.norm)
  have hdom : Integrable fun x => B * L * (‖V x‖ * F (weakGrad u x) ^ p + ‖V x‖) :=
    (i1.add i2).const_mul (B * L)
  refine hdom.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact hb.mul (((hF.continuous_flux' hp).comp_aestronglyMeasurable
      hG.aestronglyMeasurable).inner hV.aestronglyMeasurable)
  · have h1 := hF.abs_inner_flux_le (p := p) hL (weakGrad u x) (V x)
    have h2 : F (weakGrad u x) ^ (p - 1) ≤ F (weakGrad u x) ^ p + 1 := by
      have := rpow_sub_one_mul_le_add hp.le (hF.nonneg (weakGrad u x)) zero_le_one
      simpa only [mul_one, Real.one_rpow] using this
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |b x| * |⟪flux p F (weakGrad u x), V x⟫|
        ≤ B * (L * F (weakGrad u x) ^ (p - 1) * ‖V x‖) :=
          mul_le_mul (hB x) h1 (abs_nonneg _) hB0
      _ ≤ B * (L * (F (weakGrad u x) ^ p + 1) * ‖V x‖) := by
          gcongr
      _ = B * L * (‖V x‖ * F (weakGrad u x) ^ p + ‖V x‖) := by ring

/-- Integrability of `b F(∇u)^p` for bounded measurable `b`. -/
theorem integrable_mul_rpow (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {b : Euc d → ℝ} (hb : AEStronglyMeasurable b volume)
    {B : ℝ} (hB : ∀ x, |b x| ≤ B) : Integrable fun x => b x * F (weakGrad u x) ^ p :=
  (hF.integrable_rpow_comp (by linarith) hu.memW0.memLp_weakGrad).bdd_mul hb
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

/-- Powers of a cutoff: `η^m` is smooth, compactly supported in `tsupport η`, and bounded. -/
theorem cutoff_pow {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) {m : ℕ}
    (hm0 : m ≠ 0) :
    ContDiff ℝ ∞ (fun x => η x ^ m) ∧ HasCompactSupport (fun x => η x ^ m) ∧
      tsupport (fun x => η x ^ m) ⊆ tsupport η := by
  have hsupp : Function.support (fun x => η x ^ m) ⊆ Function.support η := fun x hx h0 =>
    hx (by simp only [h0, zero_pow hm0])
  exact ⟨hη.pow m, hηs.mono hsupp, closure_mono hsupp⟩

/-- **Testing the equation with `η^m Ψ(u)`**: for `u` with values in `[0, S]`, a smooth
compactly supported `η` with `tsupport η ⊆ K`, and `Ψ` with derivative `ψ'` on `[0, S]`,
`∫ η^m ψ'(u) F(∇u)^p + ∫ Ψ(u) m η^{m-1} ⟪a(∇u), ∇η⟫ = λ ∫ u^{p-1} η^m Ψ(u)`. -/
theorem integral_test_eq (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    {Ψ ψ' : ℝ → ℝ} (hΨ : ∀ t ∈ Icc 0 S, HasDerivAt Ψ (ψ' t) t)
    (hψ' : ContinuousOn ψ' (Icc 0 S)) {m : ℕ} (hm0 : m ≠ 0) {η : Euc d → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K) :
    (∫ x, η x ^ m * ψ' (u x) * F (weakGrad u x) ^ p) +
        ∫ x, Ψ (u x) * ((m : ℝ) * η x ^ (m - 1)) * ⟪flux p F (weakGrad u x), gradient η x⟫ =
      lam * ∫ x, u x ^ (p - 1) * (η x ^ m * Ψ (u x)) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hmeasU := hu.memW0.memLp.aestronglyMeasurable
  obtain ⟨hw, hwg⟩ := memW0_comp_sub_of_hasDerivAt hp hu.memW0 hS huS hΨ hψ'
  obtain ⟨hζ, hζs, hζt⟩ := cutoff_pow hη hηs hm0
  obtain ⟨hψ, hψg⟩ := hw.contDiff_mul_const_add hζ hζs (hζt.trans hηK) (Ψ 0)
  have h := hu.weakEq _ hψ
  have hΨc : ContinuousOn Ψ (Icc 0 S) := fun t ht => (hΨ t ht).continuousAt.continuousWithinAt
  obtain ⟨hΨm, CΨ, hCΨ⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hΨc hmeasU huS
  obtain ⟨hψm, Cψ, hCψ⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hψ' hmeasU huS
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hAη0 : 0 ≤ Aη := (norm_nonneg _).trans (hAη 0)
  have hηpow : ∀ n : ℕ, ∀ x, |η x ^ n| ≤ Aη ^ n := fun n x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [← Real.norm_eq_abs]; exact hAη x) n
  have i1 : Integrable fun x => η x ^ m * ψ' (u x) * F (weakGrad u x) ^ p :=
    hu.integrable_mul_rpow hp hF (hζ.continuous.aestronglyMeasurable.mul hψm)
      (B := Aη ^ m * Cψ) fun x => by
        rw [abs_mul]
        exact mul_le_mul (hηpow m x) (hCψ x) (abs_nonneg _) (pow_nonneg hAη0 m)
  have i2 : Integrable fun x =>
      Ψ (u x) * ((m : ℝ) * η x ^ (m - 1)) * ⟪flux p F (weakGrad u x), gradient η x⟫ :=
    hu.integrable_mul_inner_flux_of_hasCompactSupport hp hF (continuous_gradient hη1)
      (hasCompactSupport_gradient hηs)
      (hΨm.mul (continuous_const.mul (hη.continuous.pow _)).aestronglyMeasurable)
      (B := CΨ * ((m : ℝ) * Aη ^ (m - 1))) fun x => by
        rw [abs_mul, abs_mul, Nat.abs_cast]
        exact mul_le_mul (hCΨ x) (mul_le_mul_of_nonneg_left (hηpow (m - 1) x)
          (Nat.cast_nonneg m)) (by positivity) ((abs_nonneg _).trans (hCΨ x))
  have hL : ∀ᵐ x, ⟪flux p F (weakGrad u x),
      weakGrad (fun x => η x ^ m * (Ψ 0 + (Ψ (u x) - Ψ 0))) x⟫ =
      η x ^ m * ψ' (u x) * F (weakGrad u x) ^ p +
        Ψ (u x) * ((m : ℝ) * η x ^ (m - 1)) * ⟪flux p F (weakGrad u x), gradient η x⟫ := by
    filter_upwards [hψg, hwg] with x h1 h2
    rw [h1, h2, gradient_pow_apply (hη1.differentiable one_ne_zero x) m]
    simp only [inner_add_right, real_inner_smul_right, hF.inner_flux_self_eq_rpow hp]
    ring
  have hR : ∫ x, u x ^ (p - 1) * (η x ^ m * (Ψ 0 + (Ψ (u x) - Ψ 0))) =
      ∫ x, u x ^ (p - 1) * (η x ^ m * Ψ (u x)) :=
    integral_congr_ae (Eventually.of_forall fun x => by
      show u x ^ (p - 1) * (η x ^ m * (Ψ 0 + (Ψ (u x) - Ψ 0))) =
        u x ^ (p - 1) * (η x ^ m * Ψ (u x))
      ring)
  rw [← integral_add i1 i2, ← integral_congr_ae hL, h, hR]

/-- **The energy inequality for nonincreasing test profiles**: for `u` with values in `[0, S]`,
`λ ≥ 0`, a smooth compactly supported cutoff `η ≥ 0` with `tsupport η ⊆ K`, an integer `m ≥ p`,
and `Ψ ≥ 0` with nonpositive derivative `ψ'` on `[0, S]` such that `Ψ^p ≤ Θ |ψ'|^{p-1}`,
`∫ η^m |ψ'(u)| F(∇u)^p ≤ 2^p (mL)^p ∫ η^{m-p} |∇η|^p Θ(u)`
(testing with `η^m Ψ(u)`, `integral_test_eq`, and absorbing by `caccioppoli_pointwise_weight`). -/
theorem energy_le (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) (hlam : 0 ≤ lam) {S : ℝ} (hS : 0 ≤ S)
    (huS : ∀ x, u x ∈ Icc 0 S) {Ψ ψ' Θ : ℝ → ℝ}
    (hΨ : ∀ t ∈ Icc 0 S, HasDerivAt Ψ (ψ' t) t) (hψ' : ContinuousOn ψ' (Icc 0 S))
    (hΘc : ContinuousOn Θ (Icc 0 S)) (hΨ0 : ∀ t ∈ Icc 0 S, 0 ≤ Ψ t)
    (hψ'0 : ∀ t ∈ Icc 0 S, ψ' t ≤ 0) (hΘ0 : ∀ t ∈ Icc 0 S, 0 ≤ Θ t)
    (hΨΘ : ∀ t ∈ Icc 0 S, Ψ t ^ p ≤ Θ t * (-ψ' t) ^ (p - 1))
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {m : ℕ} (hm : p ≤ m)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (hη0 : ∀ x, 0 ≤ η x) :
    ∫ x, η x ^ m * -ψ' (u x) * F (weakGrad u x) ^ p ≤
      2 ^ p * ((m : ℝ) * L) ^ p * ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (u x) := by
  have hp0 : 0 < p := by linarith
  have hm1 : (1 : ℝ) < m := lt_of_lt_of_le hp hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm1
  have hmp : 0 ≤ (m : ℝ) - p := sub_nonneg.2 hm
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hmeasU := hu.memW0.memLp.aestronglyMeasurable
  have hid := hu.integral_test_eq hp hF hS huS hΨ hψ' hm0 hη hηs hηK
  have hRHS : 0 ≤ lam * ∫ x, u x ^ (p - 1) * (η x ^ m * Ψ (u x)) :=
    mul_nonneg hlam (integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (huS x).1 _)
      (mul_nonneg (pow_nonneg (hη0 x) m) (hΨ0 _ (huS x))))
  have hΨc : ContinuousOn Ψ (Icc 0 S) := fun t ht => (hΨ t ht).continuousAt.continuousWithinAt
  obtain ⟨hΨm, CΨ, hCΨ⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hΨc hmeasU huS
  obtain ⟨hψm, Cψ, hCψ⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hψ' hmeasU huS
  obtain ⟨hΘm, CΘ, hCΘ⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hΘc hmeasU huS
  obtain ⟨hζ, hζs, hζt⟩ := cutoff_pow hη hηs hm0
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hAη0 : 0 ≤ Aη := (norm_nonneg _).trans (hAη 0)
  have hηpow : ∀ x, |η x ^ m| ≤ Aη ^ m := fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [← Real.norm_eq_abs]; exact hAη x) m
  -- integrability
  have i1 : Integrable fun x => η x ^ m * -ψ' (u x) * F (weakGrad u x) ^ p :=
    hu.integrable_mul_rpow hp hF (hζ.continuous.aestronglyMeasurable.mul hψm.neg)
      (B := Aη ^ m * Cψ) fun x => by
        rw [abs_mul, abs_neg]
        exact mul_le_mul (hηpow x) (hCψ x) (abs_nonneg _) (pow_nonneg hAη0 m)
  have i1' : Integrable fun x => η x ^ m * ψ' (u x) * F (weakGrad u x) ^ p :=
    hu.integrable_mul_rpow hp hF (hζ.continuous.aestronglyMeasurable.mul hψm)
      (B := Aη ^ m * Cψ) fun x => by
        rw [abs_mul]
        exact mul_le_mul (hηpow x) (hCψ x) (abs_nonneg _) (pow_nonneg hAη0 m)
  have hwc : Continuous fun x => η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p :=
    (hη.continuous.rpow_const fun _ => Or.inr hmp).mul
      ((continuous_gradient hη1).norm.rpow_const fun _ => Or.inr hp0.le)
  have hws : HasCompactSupport fun x => η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p := by
    refine (hasCompactSupport_gradient hηs).mono fun x hx h0 => hx ?_
    show η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p = 0
    rw [h0, norm_zero, Real.zero_rpow hp0.ne', mul_zero]
  obtain ⟨Cw, hCw⟩ := hwc.bounded_above_of_compact_support hws
  have i3 : Integrable fun x => η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (u x) := by
    refine (hwc.integrable_of_hasCompactSupport hws).mul_bdd (c := CΘ) hΘm
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hCΘ x
  have i2 : Integrable fun x =>
      -(((m : ℝ) * η x ^ (m - 1)) * Ψ (u x) * -⟪flux p F (weakGrad u x), gradient η x⟫) := by
    have h := hu.integrable_mul_inner_flux_of_hasCompactSupport hp hF (continuous_gradient hη1)
      (hasCompactSupport_gradient hηs) (b := fun x => Ψ (u x) * ((m : ℝ) * η x ^ (m - 1)))
      (hΨm.mul (continuous_const.mul (hη.continuous.pow _)).aestronglyMeasurable)
      (B := CΨ * ((m : ℝ) * Aη ^ (m - 1))) fun x => by
        show |Ψ (u x) * ((m : ℝ) * η x ^ (m - 1))| ≤ CΨ * ((m : ℝ) * Aη ^ (m - 1))
        rw [abs_mul, abs_mul, Nat.abs_cast, abs_pow]
        exact mul_le_mul (hCΨ x) (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (by rw [← Real.norm_eq_abs]; exact hAη x) _)
          (Nat.cast_nonneg m)) (by positivity) ((abs_nonneg _).trans (hCΨ x))
    refine h.congr (Eventually.of_forall fun x => ?_)
    show Ψ (u x) * ((m : ℝ) * η x ^ (m - 1)) * ⟪flux p F (weakGrad u x), gradient η x⟫ =
      -(((m : ℝ) * η x ^ (m - 1)) * Ψ (u x) * -⟪flux p F (weakGrad u x), gradient η x⟫)
    ring
  -- the pointwise Young inequality
  have hpt : ∀ x,
      -(((m : ℝ) * η x ^ (m - 1)) * Ψ (u x) * -⟪flux p F (weakGrad u x), gradient η x⟫) ≤
        η x ^ m * -ψ' (u x) * F (weakGrad u x) ^ p / 2 + 2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
          (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (u x)) := fun x => by
    have h := caccioppoli_pointwise_weight hp hm (hη0 x) (hF.nonneg (weakGrad u x))
      (norm_nonneg (gradient η x)) hL0 (neg_nonneg.2 (hψ'0 _ (huS x))) (hΨ0 _ (huS x))
      (hΘ0 _ (huS x)) (hΨΘ _ (huS x)) (I := -⟪flux p F (weakGrad u x), gradient η x⟫)
      (by rw [abs_neg]; exact hF.abs_inner_flux_le hL _ _)
    calc -(((m : ℝ) * η x ^ (m - 1)) * Ψ (u x) * -⟪flux p F (weakGrad u x), gradient η x⟫)
        ≤ η x ^ m * (-ψ' (u x) * F (weakGrad u x) ^ p) / 2 + 2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
          (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (u x)) := h
      _ = η x ^ m * -ψ' (u x) * F (weakGrad u x) ^ p / 2 + 2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
          (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (u x)) := by ring
  have hint : ∫ x,
      -(((m : ℝ) * η x ^ (m - 1)) * Ψ (u x) * -⟪flux p F (weakGrad u x), gradient η x⟫) ≤
      ∫ x, (η x ^ m * -ψ' (u x) * F (weakGrad u x) ^ p / 2 + 2 ^ (p - 1) *
        ((m : ℝ) * L) ^ p * (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * Θ (u x))) :=
    integral_mono i2 ((i1.div_const 2).add (i3.const_mul _)) hpt
  rw [integral_add (i1.div_const 2) (i3.const_mul _), integral_div, integral_const_mul] at hint
  have e2 : ∫ x,
      -(((m : ℝ) * η x ^ (m - 1)) * Ψ (u x) * -⟪flux p F (weakGrad u x), gradient η x⟫) =
      ∫ x, Ψ (u x) * ((m : ℝ) * η x ^ (m - 1)) * ⟪flux p F (weakGrad u x), gradient η x⟫ :=
    integral_congr_ae (Eventually.of_forall fun x => by
      show -(((m : ℝ) * η x ^ (m - 1)) * Ψ (u x) * -⟪flux p F (weakGrad u x), gradient η x⟫) =
        Ψ (u x) * ((m : ℝ) * η x ^ (m - 1)) * ⟪flux p F (weakGrad u x), gradient η x⟫
      ring)
  have e1 : ∫ x, η x ^ m * -ψ' (u x) * F (weakGrad u x) ^ p =
      -∫ x, η x ^ m * ψ' (u x) * F (weakGrad u x) ^ p := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      show η x ^ m * -ψ' (u x) * F (weakGrad u x) ^ p =
        -(η x ^ m * ψ' (u x) * F (weakGrad u x) ^ p)
      ring)
  have h2p : (2 : ℝ) ^ (p - 1) = 2 ^ p / 2 := Real.rpow_sub_one two_ne_zero p
  rw [e2, h2p, e1] at hint
  rw [e1]
  nlinarith [hid, hRHS, hint]

end IsWeakEigensolution

/-! ### Generic helpers -/

/-- `∫⁻ ‖f‖^{κp} ≤ C^{κp} (∫⁻ ‖g‖^p)^κ` from `‖f‖_{L^{κp}} ≤ C ‖g‖_{L^p}`. -/
theorem lintegral_rpow_le_of_eLpNorm_le {α E E' : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup E'] {p κ : ℝ} (hp0 : 0 < p) (hκ : 0 < κ)
    {f : α → E} {g : α → E'} {C : ℝ≥0∞}
    (h : eLpNorm f (ENNReal.ofReal (κ * p)) μ ≤ C * eLpNorm g (ENNReal.ofReal p) μ) :
    ∫⁻ x, ‖f x‖ₑ ^ (κ * p) ∂μ ≤ C ^ (κ * p) * (∫⁻ x, ‖g x‖ₑ ^ p ∂μ) ^ κ := by
  have hκp : 0 < κ * p := mul_pos hκ hp0
  rw [lintegral_enorm_rpow_eq_eLpNorm_rpow hκp, lintegral_enorm_rpow_eq_eLpNorm_rpow hp0,
    ← ENNReal.rpow_mul, mul_comm p κ, ← ENNReal.mul_rpow_of_nonneg _ _ hκp.le]
  exact ENNReal.rpow_le_rpow h hκp.le

/-- `∫⁻ ‖f‖^p = ofReal (∫ ‖f‖^p)` for `f ∈ L^p`. -/
theorem lintegral_enorm_rpow_eq_ofReal_integral {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {p : ℝ} (hp0 : 0 < p) {f : α → E}
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ p ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_of_memLp hp0 hf)
    (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]

/-- The pointwise bound for the gradient of `η^m W`: with `e = η(x) ∈ [0, 1]`, `W ≥ 0`,
`‖∇η‖ ≤ G` and an integer `m ≥ p ≥ 1`,
`‖e^m V + W m e^{m-1} ∇η‖^p ≤ 2^p (e^m ‖V‖^p + m^p G^p e^{m-p} W^p)`. -/
theorem norm_smul_add_smul_rpow_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ} (hp : 1 ≤ p) {m : ℕ} (hmN : 1 ≤ m) (hmp : p ≤ m) {e W G : ℝ} (he0 : 0 ≤ e)
    (he1 : e ≤ 1) (hW : 0 ≤ W) (V g : E) (hg : ‖g‖ ≤ G) :
    ‖e ^ m • V + W • (((m : ℝ) * e ^ (m - 1)) • g)‖ ^ p ≤
      2 ^ p * (e ^ m * ‖V‖ ^ p + (m : ℝ) ^ p * G ^ p * (e ^ ((m : ℝ) - p) * W ^ p)) := by
  have hp0 : 0 < p := by linarith
  have ha0 : 0 ≤ e ^ m := pow_nonneg he0 m
  have ha1 : e ^ m ≤ 1 := pow_le_one₀ he0 he1
  have hb0 : 0 ≤ (m : ℝ) * e ^ (m - 1) := mul_nonneg (Nat.cast_nonneg m) (pow_nonneg he0 _)
  have hn : ‖e ^ m • V + W • (((m : ℝ) * e ^ (m - 1)) • g)‖ ≤
      e ^ m * ‖V‖ + W * ((m : ℝ) * e ^ (m - 1) * ‖g‖) := by
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
    · rw [norm_smul, Real.norm_of_nonneg ha0]
    · rw [norm_smul, norm_smul, Real.norm_of_nonneg hW, Real.norm_of_nonneg hb0, mul_assoc]
  have hA : 0 ≤ e ^ m * ‖V‖ := mul_nonneg ha0 (norm_nonneg _)
  have hB : 0 ≤ W * ((m : ℝ) * e ^ (m - 1) * ‖g‖) := mul_nonneg hW (mul_nonneg hb0 (norm_nonneg _))
  have h1 : (e ^ m * ‖V‖) ^ p ≤ e ^ m * ‖V‖ ^ p := by
    rw [Real.mul_rpow ha0 (norm_nonneg _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
    have := Real.rpow_le_rpow_of_exponent_ge' ha0 ha1 zero_le_one hp
    rwa [Real.rpow_one] at this
  have h2 : (W * ((m : ℝ) * e ^ (m - 1) * ‖g‖)) ^ p ≤
      (m : ℝ) ^ p * G ^ p * (e ^ ((m : ℝ) - p) * W ^ p) := by
    rw [Real.mul_rpow hW (mul_nonneg hb0 (norm_nonneg _)), Real.mul_rpow hb0 (norm_nonneg _),
      Real.mul_rpow (Nat.cast_nonneg m) (pow_nonneg he0 _)]
    have h3 : (e ^ (m - 1)) ^ p ≤ e ^ ((m : ℝ) - p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul he0]
      refine Real.rpow_le_rpow_of_exponent_ge' he0 he1 (sub_nonneg.2 hmp) ?_
      rw [Nat.cast_sub hmN, Nat.cast_one]
      nlinarith
    have h4 : ‖g‖ ^ p ≤ G ^ p := Real.rpow_le_rpow (norm_nonneg _) hg hp0.le
    have hm0 : 0 ≤ (m : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg m) _
    have hW0 : 0 ≤ W ^ p := Real.rpow_nonneg hW _
    calc W ^ p * ((m : ℝ) ^ p * (e ^ (m - 1)) ^ p * ‖g‖ ^ p)
        ≤ W ^ p * ((m : ℝ) ^ p * e ^ ((m : ℝ) - p) * G ^ p) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left h3 hm0) h4
            (Real.rpow_nonneg (norm_nonneg _) _)
            (mul_nonneg hm0 (Real.rpow_nonneg he0 _))) hW0
      _ = (m : ℝ) ^ p * G ^ p * (e ^ ((m : ℝ) - p) * W ^ p) := by ring
  calc ‖e ^ m • V + W • (((m : ℝ) * e ^ (m - 1)) • g)‖ ^ p
      ≤ (e ^ m * ‖V‖ + W * ((m : ℝ) * e ^ (m - 1) * ‖g‖)) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) hn hp0.le
    _ ≤ 2 ^ p * ((e ^ m * ‖V‖) ^ p + (W * ((m : ℝ) * e ^ (m - 1) * ‖g‖)) ^ p) :=
        add_rpow_le_two_rpow_mul hp0.le hA hB
    _ ≤ 2 ^ p * (e ^ m * ‖V‖ ^ p + (m : ℝ) ^ p * G ^ p * (e ^ ((m : ℝ) - p) * W ^ p)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.rpow_nonneg (by norm_num) _)

/-! ### The logarithmic profiles -/

/-- `(t + ε)^q` has derivative `q (t + ε)^{q-1}` where `t + ε > 0`. -/
theorem hasDerivAt_add_rpow {ε q t : ℝ} (ht : 0 < t + ε) :
    HasDerivAt (fun t => (t + ε) ^ q) (q * (t + ε) ^ (q - 1)) t := by
  have h := ((hasDerivAt_id' t).add_const ε).rpow_const (p := q) (Or.inl ht.ne')
  convert h using 1
  ring

/-- `(log T - log(t + ε))^b` has derivative `-b (log T - log(t + ε))^{b-1} (t + ε)⁻¹`. -/
theorem hasDerivAt_log_sub_rpow {ε T b t : ℝ} (hb : 1 ≤ b) (ht : 0 < t + ε) :
    HasDerivAt (fun t => (Real.log T - Real.log (t + ε)) ^ b)
      (-(b * (Real.log T - Real.log (t + ε)) ^ (b - 1) * (t + ε)⁻¹)) t := by
  have h1 := ((hasDerivAt_id' t).add_const ε).log ht.ne'
  have h3 : HasDerivAt (fun t => Real.log T - Real.log (t + ε)) (0 - 1 / (t + ε)) t :=
    (hasDerivAt_const t (Real.log T)).sub h1
  refine (h3.rpow_const (p := b) (Or.inr hb)).congr_deriv ?_
  rw [one_div]
  ring

/-- The test profile `Ψ(t) = w^b (t + ε)^{1-p}` with `w = log T - log(t + ε)` has derivative
`-(t + ε)^{-p} (b w^{b-1} + (p - 1) w^b)`. -/
theorem hasDerivAt_logProfile {ε T b p t : ℝ} (hb : 1 ≤ b) (ht : 0 < t + ε) :
    HasDerivAt (fun t => (Real.log T - Real.log (t + ε)) ^ b * (t + ε) ^ (1 - p))
      (-((t + ε) ^ (-p) * (b * (Real.log T - Real.log (t + ε)) ^ (b - 1) +
        (p - 1) * (Real.log T - Real.log (t + ε)) ^ b))) t := by
  have h : HasDerivAt (fun t => (Real.log T - Real.log (t + ε)) ^ b * (t + ε) ^ (1 - p))
      (-(b * (Real.log T - Real.log (t + ε)) ^ (b - 1) * (t + ε)⁻¹) * (t + ε) ^ (1 - p) +
        (Real.log T - Real.log (t + ε)) ^ b * ((1 - p) * (t + ε) ^ (1 - p - 1))) t :=
    (hasDerivAt_log_sub_rpow (T := T) hb ht).mul (hasDerivAt_add_rpow (q := 1 - p) ht)
  refine h.congr_deriv ?_
  have e : (t + ε)⁻¹ * (t + ε) ^ (1 - p) = (t + ε) ^ (-p) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    congr 1
    ring
  have e2 : (1 - p - 1) = -p := by ring
  rw [e2]
  linear_combination (-(b * (Real.log T - Real.log (t + ε)) ^ (b - 1))) * e

/-- The Young hypothesis for the logarithmic profile: `Ψ^p ≤ Θ |Ψ'|^{p-1}` with
`Θ = b^{1-p} w^{b+p-1}` (using only `|Ψ'| ≥ b (t + ε)^{-p} w^{b-1}`). -/
theorem logProfile_rpow_le {ε T b p t : ℝ} (hp : 1 < p) (hb : 1 ≤ b) (ht : 0 < t + ε)
    (htT : t + ε ≤ T) :
    ((Real.log T - Real.log (t + ε)) ^ b * (t + ε) ^ (1 - p)) ^ p ≤
      b ^ (1 - p) * (Real.log T - Real.log (t + ε)) ^ (b + p - 1) *
        (-(-((t + ε) ^ (-p) * (b * (Real.log T - Real.log (t + ε)) ^ (b - 1) +
          (p - 1) * (Real.log T - Real.log (t + ε)) ^ b)))) ^ (p - 1) := by
  have hp1 : 0 < p - 1 := by linarith
  have hb0 : 0 < b := by linarith
  have hy : 0 ≤ Real.log T - Real.log (t + ε) := sub_nonneg.2 (Real.log_le_log ht htT)
  obtain ⟨y, hy_def⟩ : ∃ y, y = Real.log T - Real.log (t + ε) := ⟨_, rfl⟩
  rw [← hy_def] at hy ⊢
  obtain ⟨z, hz_def⟩ : ∃ z, z = t + ε := ⟨_, rfl⟩
  rw [← hz_def] at ht ⊢
  rw [neg_neg]
  have hzp : 0 ≤ z ^ (-p) := Real.rpow_nonneg ht.le _
  have hyb1 : 0 ≤ y ^ (b - 1) := Real.rpow_nonneg hy _
  have hA0 : 0 ≤ z ^ (-p) * (b * y ^ (b - 1)) := mul_nonneg hzp (mul_nonneg hb0.le hyb1)
  have hA : z ^ (-p) * (b * y ^ (b - 1)) ≤ z ^ (-p) * (b * y ^ (b - 1) + (p - 1) * y ^ b) :=
    mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg hp1.le (Real.rpow_nonneg hy _))) hzp
  have h1 := Real.rpow_le_rpow hA0 hA hp1.le
  have hΘ0 : 0 ≤ b ^ (1 - p) * y ^ (b + p - 1) :=
    mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hy _)
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h1 hΘ0)
  rw [Real.mul_rpow (Real.rpow_nonneg hy _) (Real.rpow_nonneg ht.le _),
    Real.mul_rpow hzp (mul_nonneg hb0.le hyb1), Real.mul_rpow hb0.le hyb1,
    ← Real.rpow_mul hy, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le, ← Real.rpow_mul hy]
  have e1 : b ^ (1 - p) * b ^ (p - 1) = 1 := by
    rw [← Real.rpow_add hb0, show (1 - p) + (p - 1) = (0 : ℝ) by ring, Real.rpow_zero]
  have e2 : y ^ (b + p - 1) * y ^ ((b - 1) * (p - 1)) = y ^ (b * p) := by
    rw [← Real.rpow_add' hy (by nlinarith : 0 < b + p - 1 + (b - 1) * (p - 1)).ne']
    congr 1
    ring
  have e3 : -p * (p - 1) = (1 - p) * p := by ring
  rw [e3]
  calc y ^ (b * p) * z ^ ((1 - p) * p)
      = (b ^ (1 - p) * b ^ (p - 1)) * (y ^ (b + p - 1) * y ^ ((b - 1) * (p - 1))) *
          z ^ ((1 - p) * p) := by rw [e1, e2, one_mul]
    _ = b ^ (1 - p) * y ^ (b + p - 1) *
          (z ^ ((1 - p) * p) * (b ^ (p - 1) * y ^ ((b - 1) * (p - 1)))) := by ring

/-- The derivative of `w^β` is controlled by the derivative of the test profile:
`|(w^β)'|^p ≤ (β^p / b) |Ψ'|` when `b = p (β - 1) + 1`. -/
theorem abs_logPow_deriv_rpow_le {ε T β b p t : ℝ} (hp : 1 < p) (hβ : 1 ≤ β)
    (hb : b = p * (β - 1) + 1) (ht : 0 < t + ε) (htT : t + ε ≤ T) :
    |-(β * (Real.log T - Real.log (t + ε)) ^ (β - 1) * (t + ε)⁻¹)| ^ p ≤
      β ^ p / b * (-(-((t + ε) ^ (-p) * (b * (Real.log T - Real.log (t + ε)) ^ (b - 1) +
          (p - 1) * (Real.log T - Real.log (t + ε)) ^ b)))) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hb0 : 0 < b := by rw [hb]; nlinarith
  have hy : 0 ≤ Real.log T - Real.log (t + ε) := sub_nonneg.2 (Real.log_le_log ht htT)
  obtain ⟨y, hy_def⟩ : ∃ y, y = Real.log T - Real.log (t + ε) := ⟨_, rfl⟩
  rw [← hy_def] at hy ⊢
  obtain ⟨z, hz_def⟩ : ∃ z, z = t + ε := ⟨_, rfl⟩
  rw [← hz_def] at ht ⊢
  rw [neg_neg, abs_neg, abs_of_nonneg (by positivity)]
  have hzp : 0 ≤ z ^ (-p) := Real.rpow_nonneg ht.le _
  have hlhs : (β * y ^ (β - 1) * z⁻¹) ^ p = β ^ p * y ^ (b - 1) * z ^ (-p) := by
    rw [Real.mul_rpow (mul_nonneg (by linarith) (Real.rpow_nonneg hy _)) (inv_nonneg.2 ht.le),
      Real.mul_rpow (by linarith) (Real.rpow_nonneg hy _), ← Real.rpow_mul hy,
      Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    congr 2
    rw [hb]
    ring_nf
  rw [hlhs]
  have h1 : z ^ (-p) * (b * y ^ (b - 1)) ≤ z ^ (-p) * (b * y ^ (b - 1) + (p - 1) * y ^ b) :=
    mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg hp1.le (Real.rpow_nonneg hy _))) hzp
  have hβp : 0 ≤ β ^ p / b := div_nonneg (Real.rpow_nonneg (by linarith) _) hb0.le
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h1 hβp)
  field_simp

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- `c^p ‖ξ‖^p ≤ F(ξ)^p`, in the form `‖ξ‖^p ≤ c⁻¹^p F(ξ)^p`. -/
theorem norm_rpow_le_inv_rpow_mul {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) (hp0 : 0 < p)
    (ξ : Euc d) : ‖ξ‖ ^ p ≤ c⁻¹ ^ p * F ξ ^ p := by
  have h := Real.rpow_le_rpow (mul_nonneg hc.le (norm_nonneg _)) (hcF ξ) hp0.le
  rw [Real.mul_rpow hc.le (norm_nonneg _)] at h
  have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc p
  rw [Real.inv_rpow hc.le]
  calc ‖ξ‖ ^ p = (c ^ p)⁻¹ * (c ^ p * ‖ξ‖ ^ p) := by field_simp
    _ ≤ (c ^ p)⁻¹ * F ξ ^ p := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hcp.le)

/-- **The logarithmic Caccioppoli estimate**: for `u` with values in `[0, S]`, `λ ≥ 0` and
`ε > 0`,
`∫ η^m |∇ log(u + ε)|^p ≤ c^{-p} 2^p (mL)^p (p - 1)^{-p} ∫ η^{m-p} |∇η|^p`,
uniformly in `ε` (`energy_le` with `Ψ(t) = (t + ε)^{1-p}`, `Θ = (p - 1)^{1-p}`). -/
theorem log_caccioppoli (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) (hlam : 0 ≤ lam) {S : ℝ} (hS : 0 ≤ S)
    (huS : ∀ x, u x ∈ Icc 0 S) {ε : ℝ} (hε : 0 < ε) {c : ℝ} (hc : 0 < c)
    (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {m : ℕ}
    (hm : p ≤ m) {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηK : tsupport η ⊆ K) (hη0 : ∀ x, 0 ≤ η x) :
    ∫ x, η x ^ m * ‖(u x + ε)⁻¹ • weakGrad u x‖ ^ p ≤
      c⁻¹ ^ p * 2 ^ p * ((m : ℝ) * L) ^ p * (p - 1)⁻¹ ^ p *
        ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hpos : ∀ t ∈ Icc 0 S, 0 < t + ε := fun t ht => by linarith [ht.1]
  have hmeasU := hu.memW0.memLp.aestronglyMeasurable
  have hψc : ContinuousOn (fun t => (1 - p) * (t + ε) ^ (-p)) (Icc 0 S) :=
    continuousOn_const.mul ((continuousOn_id.add continuousOn_const).rpow_const
      fun t ht => Or.inl (hpos t ht).ne')
  have hΨΘ : ∀ t ∈ Icc 0 S, ((t + ε) ^ (1 - p)) ^ p ≤
      (p - 1) ^ (1 - p) * (-((1 - p) * (t + ε) ^ (-p))) ^ (p - 1) := by
    intro t ht
    have htε := hpos t ht
    have e1 : -((1 - p) * (t + ε) ^ (-p)) = (p - 1) * (t + ε) ^ (-p) := by ring
    rw [e1, Real.mul_rpow hp1.le (Real.rpow_nonneg htε.le _), ← mul_assoc,
      ← Real.rpow_add hp1, show 1 - p + (p - 1) = (0 : ℝ) by ring, Real.rpow_zero, one_mul,
      ← Real.rpow_mul htε.le, ← Real.rpow_mul htε.le]
    exact le_of_eq (by congr 1; ring)
  have hen := hu.energy_le hp hF hlam hS huS (Ψ := fun t => (t + ε) ^ (1 - p))
    (ψ' := fun t => (1 - p) * (t + ε) ^ (-p)) (Θ := fun _ => (p - 1) ^ (1 - p))
    (fun t ht => by
      have h := hasDerivAt_add_rpow (q := 1 - p) (hpos t ht)
      rwa [show 1 - p - 1 = -p by ring] at h)
    hψc continuousOn_const (fun t ht => Real.rpow_nonneg (hpos t ht).le _)
    (fun t ht => by nlinarith [Real.rpow_nonneg (hpos t ht).le (-p)])
    (fun _ _ => Real.rpow_nonneg hp1.le _) hΨΘ hL0 hL hm hη hηs hηK hη0
  beta_reduce at hen
  rw [integral_mul_const] at hen
  obtain ⟨hψm, Cψ, hCψ⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hψc hmeasU huS
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hAη0 : 0 ≤ Aη := (norm_nonneg _).trans (hAη 0)
  have iR : Integrable fun x =>
      η x ^ m * -((1 - p) * (u x + ε) ^ (-p)) * F (weakGrad u x) ^ p :=
    hu.integrable_mul_rpow hp hF ((hη.continuous.pow m).aestronglyMeasurable.mul hψm.neg)
      (B := Aη ^ m * Cψ) fun x => by
        rw [abs_mul, abs_neg, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _)
          (by rw [← Real.norm_eq_abs]; exact hAη x) m) (hCψ x) (abs_nonneg _)
          (pow_nonneg hAη0 m)
  have hpt : ∀ x, η x ^ m * ‖(u x + ε)⁻¹ • weakGrad u x‖ ^ p ≤
      c⁻¹ ^ p * (p - 1)⁻¹ *
        (η x ^ m * -((1 - p) * (u x + ε) ^ (-p)) * F (weakGrad u x) ^ p) := by
    intro x
    have hux := hpos _ (huS x)
    have hηm : 0 ≤ η x ^ m := pow_nonneg (hη0 x) m
    have h1 : ‖(u x + ε)⁻¹ • weakGrad u x‖ ^ p = (u x + ε) ^ (-p) * ‖weakGrad u x‖ ^ p := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hux.le),
        Real.mul_rpow (inv_nonneg.2 hux.le) (norm_nonneg _), Real.inv_rpow hux.le,
        Real.rpow_neg hux.le]
    have h2 := norm_rpow_le_inv_rpow_mul hc hcF hp0 (weakGrad u x)
    have hX : 0 ≤ (u x + ε) ^ (-p) := Real.rpow_nonneg hux.le _
    rw [h1]
    have hp1' : p - 1 ≠ 0 := hp1.ne'
    calc η x ^ m * ((u x + ε) ^ (-p) * ‖weakGrad u x‖ ^ p)
        ≤ η x ^ m * ((u x + ε) ^ (-p) * (c⁻¹ ^ p * F (weakGrad u x) ^ p)) := by gcongr
      _ = c⁻¹ ^ p * (p - 1)⁻¹ *
          (η x ^ m * -((1 - p) * (u x + ε) ^ (-p)) * F (weakGrad u x) ^ p) := by
          field_simp
          ring
  have hmono := integral_mono_of_nonneg (Eventually.of_forall fun x =>
    mul_nonneg (pow_nonneg (hη0 x) m) (Real.rpow_nonneg (norm_nonneg _) _))
    (iR.const_mul (c⁻¹ ^ p * (p - 1)⁻¹)) (Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  refine hmono.trans ?_
  have hC0 : 0 ≤ c⁻¹ ^ p * (p - 1)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _) (inv_nonneg.2 hp1.le)
  refine (mul_le_mul_of_nonneg_left hen hC0).trans (le_of_eq ?_)
  have e : (p - 1)⁻¹ * (p - 1) ^ (1 - p) = (p - 1)⁻¹ ^ p := by
    rw [Real.inv_rpow hp1.le, ← Real.rpow_neg_one, ← Real.rpow_add hp1, ← Real.rpow_neg hp1.le]
    congr 1
    ring
  calc c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((m : ℝ) * L) ^ p *
        ((∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p) * (p - 1) ^ (1 - p)))
      = c⁻¹ ^ p * 2 ^ p * ((m : ℝ) * L) ^ p * ((p - 1)⁻¹ * (p - 1) ^ (1 - p)) *
          ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p := by ring
    _ = _ := by rw [e]

/-- **The Moser energy bound for `w(u)^β`**, `w = log T - log(u + ε)`, `T ≥ S + ε`, `β ≥ 1`:
`∫ η^m |∇ w(u)^β|^p ≤ c^{-p} 2^p (mL)^p ∫ η^{m-p} |∇η|^p w(u)^{βp}`, uniformly in `β` and `ε`
(`energy_le` with `Ψ = w^b (t + ε)^{1-p}`, `b = p(β - 1) + 1`, and
`|(w^β)'|^p ≤ (β^p / b) |Ψ'|`, `abs_logPow_deriv_rpow_le`). -/
theorem moser_log_energy (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) (hlam : 0 ≤ lam) {S : ℝ} (hS : 0 ≤ S)
    (huS : ∀ x, u x ∈ Icc 0 S) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : S + ε ≤ T) {β : ℝ}
    (hβ : 1 ≤ β) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {m : ℕ} (hm : p ≤ m) {η : Euc d → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (hη0 : ∀ x, 0 ≤ η x) :
    ∫ x, η x ^ m * ‖(-(β * (Real.log T - Real.log (u x + ε)) ^ (β - 1) * (u x + ε)⁻¹)) •
        weakGrad u x‖ ^ p ≤
      c⁻¹ ^ p * 2 ^ p * ((m : ℝ) * L) ^ p *
        ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
          ((Real.log T - Real.log (u x + ε)) ^ β) ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = p * (β - 1) + 1 := ⟨_, rfl⟩
  have hb1 : 1 ≤ b := by rw [hb]; nlinarith
  have hb0 : 0 < b := by linarith
  have hβb : β ≤ b := by rw [hb]; nlinarith
  have hpos : ∀ t ∈ Icc 0 S, 0 < t + ε := fun t ht => by linarith [ht.1]
  have hle : ∀ t ∈ Icc 0 S, t + ε ≤ T := fun t ht => by linarith [ht.2]
  have hmeasU := hu.memW0.memLp.aestronglyMeasurable
  have hzc : ContinuousOn (fun t => t + ε) (Icc 0 S) := continuousOn_id.add continuousOn_const
  have hwc : ContinuousOn (fun t => Real.log T - Real.log (t + ε)) (Icc 0 S) :=
    continuousOn_const.sub (hzc.log fun t ht => (hpos t ht).ne')
  have hψc : ContinuousOn (fun t => -((t + ε) ^ (-p) *
      (b * (Real.log T - Real.log (t + ε)) ^ (b - 1) +
        (p - 1) * (Real.log T - Real.log (t + ε)) ^ b))) (Icc 0 S) :=
    ((hzc.rpow_const fun t ht => Or.inl (hpos t ht).ne').mul
      ((continuousOn_const.mul (hwc.rpow_const fun _ _ => Or.inr (by linarith))).add
        (continuousOn_const.mul (hwc.rpow_const fun _ _ => Or.inr hb0.le)))).neg
  have hΘc : ContinuousOn
      (fun t => b ^ (1 - p) * (Real.log T - Real.log (t + ε)) ^ (b + p - 1)) (Icc 0 S) :=
    continuousOn_const.mul (hwc.rpow_const fun _ _ => Or.inr (by linarith))
  have hw0 : ∀ t ∈ Icc 0 S, 0 ≤ Real.log T - Real.log (t + ε) := fun t ht =>
    sub_nonneg.2 (Real.log_le_log (hpos t ht) (hle t ht))
  have hen := hu.energy_le hp hF hlam hS huS
    (Ψ := fun t => (Real.log T - Real.log (t + ε)) ^ b * (t + ε) ^ (1 - p))
    (ψ' := fun t => -((t + ε) ^ (-p) * (b * (Real.log T - Real.log (t + ε)) ^ (b - 1) +
      (p - 1) * (Real.log T - Real.log (t + ε)) ^ b)))
    (Θ := fun t => b ^ (1 - p) * (Real.log T - Real.log (t + ε)) ^ (b + p - 1))
    (fun t ht => hasDerivAt_logProfile hb1 (hpos t ht)) hψc hΘc
    (fun t ht => mul_nonneg (Real.rpow_nonneg (hw0 t ht) _) (Real.rpow_nonneg (hpos t ht).le _))
    (fun t ht => neg_nonpos.2 (mul_nonneg (Real.rpow_nonneg (hpos t ht).le _)
      (add_nonneg (mul_nonneg hb0.le (Real.rpow_nonneg (hw0 t ht) _))
        (mul_nonneg hp1.le (Real.rpow_nonneg (hw0 t ht) _)))))
    (fun t ht => mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg (hw0 t ht) _))
    (fun t ht => logProfile_rpow_le hp hb1 (hpos t ht) (hle t ht)) hL0 hL hm hη hηs hηK hη0
  beta_reduce at hen
  obtain ⟨hAm, CA, hCA⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hψc hmeasU huS
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hAη0 : 0 ≤ Aη := (norm_nonneg _).trans (hAη 0)
  have iR : Integrable fun x => η x ^ m * -(-((u x + ε) ^ (-p) *
      (b * (Real.log T - Real.log (u x + ε)) ^ (b - 1) +
        (p - 1) * (Real.log T - Real.log (u x + ε)) ^ b))) * F (weakGrad u x) ^ p :=
    hu.integrable_mul_rpow hp hF ((hη.continuous.pow m).aestronglyMeasurable.mul hAm.neg)
      (B := Aη ^ m * CA) fun x => by
        rw [abs_mul, abs_neg, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _)
          (by rw [← Real.norm_eq_abs]; exact hAη x) m) (hCA x) (abs_nonneg _)
          (pow_nonneg hAη0 m)
  have hpt : ∀ x, η x ^ m * ‖(-(β * (Real.log T - Real.log (u x + ε)) ^ (β - 1) *
      (u x + ε)⁻¹)) • weakGrad u x‖ ^ p ≤
      c⁻¹ ^ p * (β ^ p / b) * (η x ^ m * -(-((u x + ε) ^ (-p) *
        (b * (Real.log T - Real.log (u x + ε)) ^ (b - 1) +
          (p - 1) * (Real.log T - Real.log (u x + ε)) ^ b))) * F (weakGrad u x) ^ p) := by
    intro x
    have hux := hpos _ (huS x)
    have hle' := hle _ (huS x)
    rw [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Real.norm_eq_abs]
    have h1 := abs_logPow_deriv_rpow_le hp hβ hb hux hle'
    have h2 := norm_rpow_le_inv_rpow_mul hc hcF hp0 (weakGrad u x)
    have hηm : 0 ≤ η x ^ m := pow_nonneg (hη0 x) m
    have hA0 := (Real.rpow_nonneg (abs_nonneg _) _).trans h1
    calc η x ^ m * (|-(β * (Real.log T - Real.log (u x + ε)) ^ (β - 1) * (u x + ε)⁻¹)| ^ p *
          ‖weakGrad u x‖ ^ p)
        ≤ η x ^ m * ((β ^ p / b * -(-((u x + ε) ^ (-p) *
            (b * (Real.log T - Real.log (u x + ε)) ^ (b - 1) +
              (p - 1) * (Real.log T - Real.log (u x + ε)) ^ b)))) *
            (c⁻¹ ^ p * F (weakGrad u x) ^ p)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.rpow_nonneg (norm_nonneg _) _) hA0)
            hηm
      _ = c⁻¹ ^ p * (β ^ p / b) * (η x ^ m * -(-((u x + ε) ^ (-p) *
          (b * (Real.log T - Real.log (u x + ε)) ^ (b - 1) +
            (p - 1) * (Real.log T - Real.log (u x + ε)) ^ b))) * F (weakGrad u x) ^ p) := by
          ring
  have hC0 : 0 ≤ c⁻¹ ^ p * (β ^ p / b) :=
    mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      (div_nonneg (Real.rpow_nonneg (by linarith) _) hb0.le)
  have hmono := integral_mono_of_nonneg (Eventually.of_forall fun x =>
    mul_nonneg (pow_nonneg (hη0 x) m) (Real.rpow_nonneg (norm_nonneg _) _))
    (iR.const_mul (c⁻¹ ^ p * (β ^ p / b))) (Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  refine (hmono.trans (mul_le_mul_of_nonneg_left hen hC0)).trans ?_
  have hI : ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
      (b ^ (1 - p) * (Real.log T - Real.log (u x + ε)) ^ (b + p - 1)) =
      b ^ (1 - p) * ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
        ((Real.log T - Real.log (u x + ε)) ^ β) ^ p := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
        (b ^ (1 - p) * (Real.log T - Real.log (u x + ε)) ^ (b + p - 1)) =
      b ^ (1 - p) * (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
        ((Real.log T - Real.log (u x + ε)) ^ β) ^ p)
    rw [← Real.rpow_mul (hw0 _ (huS x)), show β * p = b + p - 1 by rw [hb]; ring]
    ring
  rw [hI]
  have hY : 0 ≤ ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
      ((Real.log T - Real.log (u x + ε)) ^ β) ^ p :=
    integral_nonneg fun x => mul_nonneg (mul_nonneg (Real.rpow_nonneg (hη0 x) _)
      (Real.rpow_nonneg (norm_nonneg _) _))
      (Real.rpow_nonneg (Real.rpow_nonneg (hw0 _ (huS x)) _) _)
  have hK0 : 0 ≤ c⁻¹ ^ p * 2 ^ p * ((m : ℝ) * L) ^ p :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg m) hL0) _)
  have e : β ^ p / b * b ^ (1 - p) = (β / b) ^ p := by
    rw [Real.rpow_sub hb0, Real.rpow_one, Real.div_rpow (by linarith) hb0.le]
    field_simp
  have h1 : (β / b) ^ p ≤ 1 :=
    Real.rpow_le_one (div_nonneg (by linarith) hb0.le) ((div_le_one hb0).2 hβb) hp0.le
  calc c⁻¹ ^ p * (β ^ p / b) * (2 ^ p * ((m : ℝ) * L) ^ p *
        (b ^ (1 - p) * ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
          ((Real.log T - Real.log (u x + ε)) ^ β) ^ p))
      = c⁻¹ ^ p * 2 ^ p * ((m : ℝ) * L) ^ p * (β ^ p / b * b ^ (1 - p)) *
          ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
            ((Real.log T - Real.log (u x + ε)) ^ β) ^ p := by ring
    _ ≤ c⁻¹ ^ p * 2 ^ p * ((m : ℝ) * L) ^ p * 1 *
          ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
            ((Real.log T - Real.log (u x + ε)) ^ β) ^ p := by
        rw [e]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK0) hY
    _ = _ := by rw [mul_one]

/-- **One Moser step for `w(u)^β`** (`w = log T - log(u + ε)`, `T ≥ S + ε`, `β ≥ 1`): given a
Sobolev inequality `‖v‖_{κp} ≤ C ‖∇v‖_p` on `W₀^{1,p}(K)`, an integer `m > p` and a cutoff
`0 ≤ η ≤ 1` with `|∇η| ≤ G`,
`∫ η^{mκp} w(u)^{βκp} ≤ C^{κp} (D m^p ∫ η^{m-p} w(u)^{βp})^κ`,
`D = 2^p (c^{-p} 2^p L^p + 1) G^p` (Sobolev for `η^m w(u)^β ∈ W₀^{1,p}(K)`,
`norm_smul_add_smul_rpow_le` and `moser_log_energy`). -/
theorem moser_log_step (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) (hlam : 0 ≤ lam) {S : ℝ} (hS : 0 ≤ S)
    (huS : ∀ x, u x ∈ Icc 0 S) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : S + ε ≤ T) {β : ℝ}
    (hβ : 1 ≤ β) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {κ : ℝ} (hκ : 0 < κ) {C : ℝ≥0∞}
    (hSob : ∀ w : Euc d → ℝ, MemW0 p K w →
      eLpNorm w (ENNReal.ofReal (κ * p)) ≤ C * eLpNorm (weakGrad w) (ENNReal.ofReal p))
    {m : ℕ} (hm : p < m) {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηK : tsupport η ⊆ K) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {G : ℝ}
    (hG : ∀ x, ‖gradient η x‖ ≤ G) :
    ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) * (κ * p)) *
        (Real.log T - Real.log (u x + ε)) ^ (β * (κ * p))) ≤
      C ^ (κ * p) * (ENNReal.ofReal (2 ^ p * (c⁻¹ ^ p * 2 ^ p * L ^ p + 1) * G ^ p *
        (m : ℝ) ^ p) * ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) - p) *
          (Real.log T - Real.log (u x + ε)) ^ (β * p))) ^ κ := by
  have hp0 : 0 < p := by linarith
  have hκp : 0 < κ * p := mul_pos hκ hp0
  have hm1 : (1 : ℝ) < m := lt_trans hp hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm1
  have hmN : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
  have hmp : 0 < (m : ℝ) - p := sub_pos.2 hm
  have hη1' : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hpos : ∀ t ∈ Icc 0 S, 0 < t + ε := fun t ht => by linarith [ht.1]
  have hle : ∀ t ∈ Icc 0 S, t + ε ≤ T := fun t ht => by linarith [ht.2]
  have hw0 : ∀ t ∈ Icc 0 S, 0 ≤ Real.log T - Real.log (t + ε) := fun t ht =>
    sub_nonneg.2 (Real.log_le_log (hpos t ht) (hle t ht))
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hmeasU := hu.memW0.memLp.aestronglyMeasurable
  have hzc : ContinuousOn (fun t => t + ε) (Icc 0 S) := continuousOn_id.add continuousOn_const
  have hwc : ContinuousOn (fun t => Real.log T - Real.log (t + ε)) (Icc 0 S) :=
    continuousOn_const.sub (hzc.log fun t ht => (hpos t ht).ne')
  have hΦc : ContinuousOn
      (fun t => -(β * (Real.log T - Real.log (t + ε)) ^ (β - 1) * (t + ε)⁻¹)) (Icc 0 S) :=
    ((continuousOn_const.mul (hwc.rpow_const fun _ _ => Or.inr (by linarith))).mul
      (hzc.inv₀ fun t ht => (hpos t ht).ne')).neg
  obtain ⟨hWw, hWg⟩ := memW0_comp_sub_of_hasDerivAt hp hu.memW0 hS huS
    (Ψ := fun t => (Real.log T - Real.log (t + ε)) ^ β)
    (fun t ht => hasDerivAt_log_sub_rpow hβ (hpos t ht)) hΦc
  obtain ⟨hζ, hζs, hζt⟩ := cutoff_pow hη hηs hm0
  obtain ⟨hZ, hZg⟩ := hWw.contDiff_mul_const_add hζ hζs (hζt.trans hηK)
    ((Real.log T - Real.log (0 + ε)) ^ β)
  have hS1 := lintegral_rpow_le_of_eLpNorm_le hp0 hκ (hSob _ hZ)
  -- the left side
  have hLHS : ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) * (κ * p)) *
      (Real.log T - Real.log (u x + ε)) ^ (β * (κ * p))) =
      ∫⁻ x, ‖η x ^ m * ((Real.log T - Real.log (0 + ε)) ^ β +
        ((Real.log T - Real.log (u x + ε)) ^ β - (Real.log T - Real.log (0 + ε)) ^ β))‖ₑ ^
          (κ * p) := by
    refine lintegral_congr fun x => ?_
    have hwx := hw0 _ (huS x)
    have h0 : 0 ≤ η x ^ m * (Real.log T - Real.log (u x + ε)) ^ β :=
      mul_nonneg (pow_nonneg (hη0 x) m) (Real.rpow_nonneg hwx _)
    rw [add_sub_cancel, ← ofReal_norm, Real.norm_of_nonneg h0,
      ENNReal.ofReal_rpow_of_nonneg h0 hκp.le, Real.mul_rpow (pow_nonneg (hη0 x) m)
      (Real.rpow_nonneg hwx _), ← Real.rpow_natCast, ← Real.rpow_mul (hη0 x),
      ← Real.rpow_mul hwx]
  -- the gradient
  have hZpt : ∀ᵐ x, ‖weakGrad (fun x => η x ^ m * ((Real.log T - Real.log (0 + ε)) ^ β +
      ((Real.log T - Real.log (u x + ε)) ^ β - (Real.log T - Real.log (0 + ε)) ^ β))) x‖ ^ p ≤
      2 ^ p * (η x ^ m * ‖(-(β * (Real.log T - Real.log (u x + ε)) ^ (β - 1) *
        (u x + ε)⁻¹)) • weakGrad u x‖ ^ p + (m : ℝ) ^ p * G ^ p *
          (η x ^ ((m : ℝ) - p) * ((Real.log T - Real.log (u x + ε)) ^ β) ^ p)) := by
    filter_upwards [hZg, hWg] with x h1 h2
    rw [h1, h2, gradient_pow_apply (hη1'.differentiable one_ne_zero x) m, add_sub_cancel]
    exact norm_smul_add_smul_rpow_le hp.le hmN hm.le (hη0 x) (hη1 x)
      (Real.rpow_nonneg (hw0 _ (huS x)) _) _ _ (hG x)
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  have hVint : Integrable fun x => ‖(-(β * (Real.log T - Real.log (u x + ε)) ^ (β - 1) *
      (u x + ε)⁻¹)) • weakGrad u x‖ ^ p :=
    (integrable_norm_rpow_of_memLp hp0 hWw.memLp_weakGrad).congr
      (hWg.mono fun x hx => by simp only [hx])
  have i1 : Integrable fun x => η x ^ m * ‖(-(β * (Real.log T - Real.log (u x + ε)) ^ (β - 1) *
      (u x + ε)⁻¹)) • weakGrad u x‖ ^ p :=
    hVint.bdd_mul (c := Aη ^ m) (hη.continuous.pow m).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (by rw [← Real.norm_eq_abs]; exact hAη x) m)
  have hWpc : ContinuousOn (fun t => ((Real.log T - Real.log (t + ε)) ^ β) ^ p) (Icc 0 S) :=
    (hwc.rpow_const fun _ _ => Or.inr (by linarith)).rpow_const fun _ _ => Or.inr hp0.le
  obtain ⟨hWpm, CW, hCW⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hWpc hmeasU huS
  have hηc : Continuous fun x => η x ^ ((m : ℝ) - p) :=
    hη.continuous.rpow_const fun _ => Or.inr hmp.le
  have hηcs : HasCompactSupport fun x => η x ^ ((m : ℝ) - p) := by
    refine hηs.mono fun x hx h0 => hx ?_
    show η x ^ ((m : ℝ) - p) = 0
    rw [h0, Real.zero_rpow hmp.ne']
  have iW : Integrable fun x => η x ^ ((m : ℝ) - p) *
      ((Real.log T - Real.log (u x + ε)) ^ β) ^ p :=
    (hηc.integrable_of_hasCompactSupport hηcs).mul_bdd (c := CW) hWpm
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCW x)
  have hen := hu.moser_log_energy hp hF hlam hS huS hε hT hβ hc hcF hL0 hL hm.le hη hηs hηK hη0
  have hGW : ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
      ((Real.log T - Real.log (u x + ε)) ^ β) ^ p ≤
      G ^ p * ∫ x, η x ^ ((m : ℝ) - p) * ((Real.log T - Real.log (u x + ε)) ^ β) ^ p := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) (iW.const_mul _)
      (Eventually.of_forall fun x => ?_)
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hη0 x) _)
        (Real.rpow_nonneg (norm_nonneg _) _))
        (Real.rpow_nonneg (Real.rpow_nonneg (hw0 _ (huS x)) _) _)
    · show η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p *
          ((Real.log T - Real.log (u x + ε)) ^ β) ^ p ≤
        G ^ p * (η x ^ ((m : ℝ) - p) * ((Real.log T - Real.log (u x + ε)) ^ β) ^ p)
      have h1 := Real.rpow_le_rpow (norm_nonneg _) (hG x) hp0.le
      have h2 : 0 ≤ η x ^ ((m : ℝ) - p) * ((Real.log T - Real.log (u x + ε)) ^ β) ^ p :=
        mul_nonneg (Real.rpow_nonneg (hη0 x) _)
          (Real.rpow_nonneg (Real.rpow_nonneg (hw0 _ (huS x)) _) _)
      nlinarith
  obtain ⟨I, hI⟩ : ∃ I : ℝ,
      I = ∫ x, η x ^ ((m : ℝ) - p) * ((Real.log T - Real.log (u x + ε)) ^ β) ^ p := ⟨_, rfl⟩
  have hK0 : 0 ≤ c⁻¹ ^ p * 2 ^ p * ((m : ℝ) * L) ^ p :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg m) hL0) _)
  have hD0 : 0 ≤ 2 ^ p * (c⁻¹ ^ p * 2 ^ p * L ^ p + 1) * G ^ p * (m : ℝ) ^ p :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
        (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hL0 _)) zero_le_one))
      (Real.rpow_nonneg hG0 _)) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hgrad : ∫ x, ‖weakGrad (fun x => η x ^ m * ((Real.log T - Real.log (0 + ε)) ^ β +
      ((Real.log T - Real.log (u x + ε)) ^ β - (Real.log T - Real.log (0 + ε)) ^ β))) x‖ ^ p ≤
      2 ^ p * (c⁻¹ ^ p * 2 ^ p * L ^ p + 1) * G ^ p * (m : ℝ) ^ p * I := by
    have h1 : ∫ x, ‖weakGrad (fun x => η x ^ m * ((Real.log T - Real.log (0 + ε)) ^ β +
        ((Real.log T - Real.log (u x + ε)) ^ β - (Real.log T - Real.log (0 + ε)) ^ β))) x‖ ^ p ≤
        ∫ x, 2 ^ p * (η x ^ m * ‖(-(β * (Real.log T - Real.log (u x + ε)) ^ (β - 1) *
          (u x + ε)⁻¹)) • weakGrad u x‖ ^ p + (m : ℝ) ^ p * G ^ p *
            (η x ^ ((m : ℝ) - p) * ((Real.log T - Real.log (u x + ε)) ^ β) ^ p)) :=
      integral_mono_ae (integrable_norm_rpow_of_memLp hp0 hZ.memLp_weakGrad)
        ((i1.add (iW.const_mul ((m : ℝ) ^ p * G ^ p))).const_mul (2 ^ p)) hZpt
    rw [integral_const_mul, integral_add i1 (iW.const_mul _), integral_const_mul, ← hI] at h1
    have h2 := hen.trans (mul_le_mul_of_nonneg_left hGW hK0)
    rw [← hI, Real.mul_rpow (Nat.cast_nonneg m) hL0] at h2
    have h2p : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) _
    refine h1.trans ?_
    calc 2 ^ p * ((∫ x, η x ^ m * ‖(-(β * (Real.log T - Real.log (u x + ε)) ^ (β - 1) *
          (u x + ε)⁻¹)) • weakGrad u x‖ ^ p) + (m : ℝ) ^ p * G ^ p * I)
        ≤ 2 ^ p * (c⁻¹ ^ p * 2 ^ p * ((m : ℝ) ^ p * L ^ p) * (G ^ p * I) +
            (m : ℝ) ^ p * G ^ p * I) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 le_rfl) h2p
      _ = 2 ^ p * (c⁻¹ ^ p * 2 ^ p * L ^ p + 1) * G ^ p * (m : ℝ) ^ p * I := by ring
  have hIL : ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) - p) *
      (Real.log T - Real.log (u x + ε)) ^ (β * p)) = ENNReal.ofReal I := by
    rw [hI, ofReal_integral_eq_lintegral_ofReal iW (Eventually.of_forall fun x =>
      mul_nonneg (Real.rpow_nonneg (hη0 x) _)
        (Real.rpow_nonneg (Real.rpow_nonneg (hw0 _ (huS x)) _) _))]
    refine lintegral_congr fun x => ?_
    rw [Real.rpow_mul (hw0 _ (huS x))]
  have hgradL : ∫⁻ x, ‖weakGrad (fun x => η x ^ m * ((Real.log T - Real.log (0 + ε)) ^ β +
      ((Real.log T - Real.log (u x + ε)) ^ β - (Real.log T - Real.log (0 + ε)) ^ β))) x‖ₑ ^ p ≤
      ENNReal.ofReal (2 ^ p * (c⁻¹ ^ p * 2 ^ p * L ^ p + 1) * G ^ p * (m : ℝ) ^ p) *
        ∫⁻ x, ENNReal.ofReal (η x ^ ((m : ℝ) - p) *
          (Real.log T - Real.log (u x + ε)) ^ (β * p)) := by
    rw [lintegral_enorm_rpow_eq_ofReal_integral hp0 hZ.memLp_weakGrad, hIL,
      ← ENNReal.ofReal_mul hD0]
    exact ENNReal.ofReal_le_ofReal hgrad
  rw [hLHS]
  exact hS1.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hgradL hκ.le) _)

end IsWeakEigensolution

/-! ### The Moser iteration with growing powers of the cutoff -/

/-- The product bound of the Moser iteration (`exists_iterate_bound`) with the constant chosen
before the sequence. -/
theorem exists_iterate_bound_uniform {D κ : ℝ} (hD : 1 ≤ D) (hκ : 1 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ → ℝ≥0∞,
      (∀ j : ℕ, N (j + 1) ≤ ENNReal.ofReal (D ^ (((j : ℝ) + 1) * κ⁻¹ ^ j)) * N j) →
        ∀ n, N n ≤ ENNReal.ofReal B * N 0 := by
  have hr0 : 0 ≤ κ⁻¹ := inv_nonneg.2 (by linarith)
  have hr1 : κ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
  have hD0 : 0 < D := by linarith
  have hsum : Summable fun j : ℕ => ((j : ℝ) + 1) * κ⁻¹ ^ j := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖κ⁻¹‖ < 1 by rwa [Real.norm_of_nonneg hr0])
    have h2 := summable_geometric_of_lt_one hr0 hr1
    refine (h1.add h2).congr fun j => ?_
    simp only [pow_one]
    ring
  refine ⟨D ^ (∑' j : ℕ, ((j : ℝ) + 1) * κ⁻¹ ^ j), Real.rpow_nonneg hD0.le _,
    fun N hstep n => ?_⟩
  have hpart : ∀ n : ℕ,
      N n ≤ ENNReal.ofReal (D ^ (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * κ⁻¹ ^ j)) * N 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc N (n + 1) ≤ ENNReal.ofReal (D ^ (((n : ℝ) + 1) * κ⁻¹ ^ n)) * N n := hstep n
        _ ≤ ENNReal.ofReal (D ^ (((n : ℝ) + 1) * κ⁻¹ ^ n)) *
            (ENNReal.ofReal (D ^ (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * κ⁻¹ ^ j)) * N 0) := by
          gcongr
        _ = ENNReal.ofReal (D ^ (∑ j ∈ Finset.range (n + 1), ((j : ℝ) + 1) * κ⁻¹ ^ j)) *
            N 0 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD0.le _),
            ← Real.rpow_add hD0, Finset.sum_range_succ,
            add_comm (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * κ⁻¹ ^ j)]
  refine (hpart n).trans ?_
  gcongr
  exact hsum.sum_le_tsum (Finset.range n) fun j _ => mul_nonneg (by positivity) (pow_nonneg hr0 j)

/-- **The Moser iteration in exponent form**: if `a_{j+1} ≤ (E^{j+1} a_j)^κ` with `1 ≤ E < ∞` and
`κ > 1`, then `a_n^{κ^{-n}} ≤ B a_0`, with `B` depending only on `E` and `κ`. -/
theorem exists_rpow_iterate_bound {E : ℝ≥0∞} (hE1 : 1 ≤ E) (hEtop : E ≠ ⊤) {κ : ℝ}
    (hκ : 1 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℕ → ℝ≥0∞, (∀ j : ℕ, a (j + 1) ≤ (E ^ (j + 1) * a j) ^ κ) →
      ∀ n, a n ^ (κ ^ n)⁻¹ ≤ ENNReal.ofReal B * a 0 := by
  have hκ0 : 0 < κ := by linarith
  have hD : 1 ≤ E.toReal := by simpa using ENNReal.toReal_mono hEtop hE1
  obtain ⟨B, hB0, hB⟩ := exists_iterate_bound_uniform hD hκ
  refine ⟨B, hB0, fun a ha n => ?_⟩
  have hstep : ∀ j : ℕ, a (j + 1) ^ (κ ^ (j + 1))⁻¹ ≤
      ENNReal.ofReal (E.toReal ^ (((j : ℝ) + 1) * κ⁻¹ ^ j)) * a j ^ (κ ^ j)⁻¹ := by
    intro j
    have hkj : 0 < κ ^ j := pow_pos hκ0 j
    have h1 : a (j + 1) ^ (κ ^ (j + 1))⁻¹ ≤ ((E ^ (j + 1) * a j) ^ κ) ^ (κ ^ (j + 1))⁻¹ :=
      ENNReal.rpow_le_rpow (ha j) (inv_nonneg.2 (pow_nonneg hκ0.le _))
    have h2 : ((E ^ (j + 1) * a j) ^ κ) ^ (κ ^ (j + 1))⁻¹ =
        (E ^ (j + 1) * a j) ^ (κ ^ j)⁻¹ := by
      rw [← ENNReal.rpow_mul]
      congr 1
      rw [pow_succ]
      field_simp
    have h3 : (E ^ (j + 1) * a j) ^ (κ ^ j)⁻¹ = (E ^ (j + 1)) ^ (κ ^ j)⁻¹ * a j ^ (κ ^ j)⁻¹ :=
      ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hkj.le)
    have h4 : (E ^ (j + 1)) ^ (κ ^ j)⁻¹ =
        ENNReal.ofReal (E.toReal ^ (((j : ℝ) + 1) * κ⁻¹ ^ j)) := by
      have hE : E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEtop).symm
      conv_lhs => rw [hE]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hkj.le)), inv_pow]
      push_cast
      rfl
    rw [h3, h4] at h2
    exact h1.trans (le_of_eq h2)
  have h := hB (fun j => a j ^ (κ ^ j)⁻¹) hstep n
  simpa using h

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- **The sup bound for `w(u) = log T - log(u + ε)`** (Moser's iteration for the subsolution-like
`w(u)`, with one cutoff `0 ≤ η ≤ 1` and the growing powers `η^{N^{j+1}}`, `N ≥ κp + p`): there is
`B`, independent of `ε` and `T`, such that for all `ε > 0` and `T ≥ S + ε`, a.e. on `{η = 1}`,
`w(u)^p ≤ B ∫ η^{N-p} w(u)^p`. -/
theorem moser_log_sup (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) (hlam : 0 ≤ lam) {S : ℝ} (hS : 0 ≤ S)
    (huS : ∀ x, u x ∈ Icc 0 S) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {κ : ℝ} (hκ : 1 < κ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hSob : ∀ w : Euc d → ℝ, MemW0 p K w →
      eLpNorm w (ENNReal.ofReal (κ * p)) ≤ C * eLpNorm (weakGrad w) (ENNReal.ofReal p))
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {G : ℝ} (hG : ∀ x, ‖gradient η x‖ ≤ G)
    {N : ℕ} (hN : κ * p + p ≤ N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, S + ε ≤ T →
      ∀ᵐ x, η x = 1 → ENNReal.ofReal ((Real.log T - Real.log (u x + ε)) ^ p) ≤
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (η x ^ ((N : ℝ) - p) *
          (Real.log T - Real.log (u x + ε)) ^ p) := by
  have hp0 : 0 < p := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκp : 0 < κ * p := mul_pos hκ0 hp0
  have hN1 : (1 : ℝ) ≤ N := by nlinarith
  have hNp : p < (N : ℝ) := by nlinarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 ^ p * (c⁻¹ ^ p * 2 ^ p * L ^ p + 1) * G ^ p := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞,
      E = max (C ^ p) 1 * ENNReal.ofReal (max D 1 * (N : ℝ) ^ p) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by
    rw [hE]
    refine one_le_mul_of_one_le_of_one_le (le_max_right _ _) (ENNReal.one_le_ofReal.2 ?_)
    exact one_le_mul_of_one_le_of_one_le (le_max_right _ _) (Real.one_le_rpow hN1 hp0.le)
  have hEtop : E ≠ ⊤ := by
    rw [hE]
    exact ENNReal.mul_ne_top (max_lt (ENNReal.rpow_lt_top_of_nonneg hp0.le hC)
      ENNReal.one_lt_top).ne ENNReal.ofReal_ne_top
  obtain ⟨B, hB0, hB⟩ := exists_rpow_iterate_bound hE1 hEtop hκ
  refine ⟨B, hB0, fun ε hε T hT => ?_⟩
  have hpos : ∀ t ∈ Icc 0 S, 0 < t + ε := fun t ht => by linarith [ht.1]
  have hle : ∀ t ∈ Icc 0 S, t + ε ≤ T := fun t ht => by linarith [ht.2]
  have hw0 : ∀ x, 0 ≤ Real.log T - Real.log (u x + ε) := fun x =>
    sub_nonneg.2 (Real.log_le_log (hpos _ (huS x)) (hle _ (huS x)))
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ≥0∞, ∀ j, a j = ∫⁻ x, ENNReal.ofReal
      (η x ^ (((N ^ (j + 1) : ℕ) : ℝ) - p) * (Real.log T - Real.log (u x + ε)) ^ (κ ^ j * p)) :=
    ⟨_, fun _ => rfl⟩
  have hNj : ∀ j : ℕ, (1 : ℝ) ≤ ((N ^ (j + 1) : ℕ) : ℝ) := fun j => by
    push_cast
    exact one_le_pow₀ hN1
  have hmj : ∀ j : ℕ, κ * p * ((N ^ (j + 1) : ℕ) : ℝ) + p ≤ ((N ^ (j + 1 + 1) : ℕ) : ℝ) := by
    intro j
    have h1 := hNj j
    have e : ((N ^ (j + 1 + 1) : ℕ) : ℝ) = ((N ^ (j + 1) : ℕ) : ℝ) * N := by
      push_cast
      ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hN (zero_le_one.trans h1)]
  have hstep : ∀ j : ℕ, a (j + 1) ≤ (E ^ (j + 1) * a j) ^ κ := by
    intro j
    have hmjp : p < ((N ^ (j + 1) : ℕ) : ℝ) := by
      push_cast
      exact hNp.trans_le (le_self_pow₀ hN1 (Nat.succ_ne_zero j))
    have h1 := hu.moser_log_step hp hF hlam hS huS hε hT (β := κ ^ j) (one_le_pow₀ hκ.le) hc
      hcF hL0 hL hκ0 hSob hmjp hη hηs hηK hη0 hη1 hG
    rw [← hD, ← ha j] at h1
    have h2 : a (j + 1) ≤ ∫⁻ x, ENNReal.ofReal (η x ^ (((N ^ (j + 1) : ℕ) : ℝ) * (κ * p)) *
        (Real.log T - Real.log (u x + ε)) ^ (κ ^ j * (κ * p))) := by
      rw [ha (j + 1)]
      refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
      have hexp : κ ^ (j + 1) * p = κ ^ j * (κ * p) := by ring
      rw [hexp]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (hw0 x) _)
      refine Real.rpow_le_rpow_of_exponent_ge' (hη0 x) (hη1 x)
        (mul_nonneg (Nat.cast_nonneg _) hκp.le) ?_
      have := hmj j
      linarith
    have hCX : C ^ p * ENNReal.ofReal (D * ((N ^ (j + 1) : ℕ) : ℝ) ^ p) ≤ E ^ (j + 1) := by
      rw [hE, mul_pow]
      refine mul_le_mul' ((le_max_left _ _).trans
        (le_self_pow₀ (le_max_right _ _) (Nat.succ_ne_zero j))) ?_
      rw [← ENNReal.ofReal_pow (mul_nonneg (zero_le_one.trans (le_max_right _ _))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have e1 : (((N ^ (j + 1) : ℕ) : ℝ)) ^ p = ((N : ℝ) ^ p) ^ (j + 1) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg N),
          ← Real.rpow_mul_natCast (Nat.cast_nonneg N), mul_comm]
      rw [e1, mul_pow]
      exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans
        (le_self_pow₀ (le_max_right _ _) (Nat.succ_ne_zero j)))
        (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) _)
    have h3 : C ^ (κ * p) * (ENNReal.ofReal (D * ((N ^ (j + 1) : ℕ) : ℝ) ^ p) * a j) ^ κ ≤
        (E ^ (j + 1) * a j) ^ κ := by
      rw [mul_comm κ p, ENNReal.rpow_mul, ← ENNReal.mul_rpow_of_nonneg _ _ hκ0.le, ← mul_assoc]
      exact ENNReal.rpow_le_rpow (mul_le_mul_left hCX _) hκ0.le
    exact h2.trans (h1.trans h3)
  have hbound := hB a hstep
  have ha0 : a 0 = ∫⁻ x, ENNReal.ofReal (η x ^ ((N : ℝ) - p) *
      (Real.log T - Real.log (u x + ε)) ^ p) := by
    rw [ha 0]
    simp only [zero_add, pow_one, pow_zero, one_mul]
  have hmeasU := hu.memW0.memLp.aestronglyMeasurable
  have hzc : ContinuousOn (fun t => t + ε) (Icc 0 S) := continuousOn_id.add continuousOn_const
  have hwc : ContinuousOn (fun t => Real.log T - Real.log (t + ε)) (Icc 0 S) :=
    continuousOn_const.sub (hzc.log fun t ht => (hpos t ht).ne')
  have hwpc : ContinuousOn (fun t => (Real.log T - Real.log (t + ε)) ^ p) (Icc 0 S) :=
    hwc.rpow_const fun _ _ => Or.inr hp0.le
  obtain ⟨hwpm, Cw, hCw⟩ := continuousOn_comp_aestronglyMeasurable_Icc hS hwpc hmeasU huS
  have ha0top : a 0 ≠ ⊤ := by
    rw [ha0]
    refine ne_top_of_le_ne_top (b := ∫⁻ x, (tsupport η).indicator (fun _ => ENNReal.ofReal Cw) x)
      ?_ ?_
    · rw [lintegral_indicator (isClosed_tsupport η).measurableSet, setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hηs.isCompact.measure_lt_top.ne
    · refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ tsupport η
      · rw [indicator_of_mem hx]
        refine ENNReal.ofReal_le_ofReal ?_
        calc η x ^ ((N : ℝ) - p) * (Real.log T - Real.log (u x + ε)) ^ p ≤ 1 * Cw :=
              mul_le_mul (Real.rpow_le_one (hη0 x) (hη1 x) (by linarith))
                ((le_abs_self _).trans (hCw x)) (Real.rpow_nonneg (hw0 x) _) zero_le_one
          _ = Cw := one_mul _
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
          Real.zero_rpow (by linarith), zero_mul, ENNReal.ofReal_zero]
  have hUm : MeasurableSet {x : Euc d | η x = 1} :=
    measurableSet_eq_fun hη.continuous.measurable measurable_const
  have hq : ∀ n : ℕ, eLpNorm (fun x => (Real.log T - Real.log (u x + ε)) ^ p)
      (ENNReal.ofReal (κ ^ n)) (volume.restrict {x | η x = 1}) ≤
      ENNReal.ofReal (B * (a 0).toReal) := by
    intro n
    have hkn : 0 < κ ^ n := pow_pos hκ0 n
    have hk' : ENNReal.ofReal (κ ^ n) ≠ 0 := by simpa using hkn
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hk' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hkn.le]
    have h1 : ∫⁻ x in {x | η x = 1}, ‖(Real.log T - Real.log (u x + ε)) ^ p‖ₑ ^ (κ ^ n) ≤
        a n := by
      rw [ha n]
      refine (setLIntegral_mono' hUm fun x hx => le_of_eq ?_).trans
        (setLIntegral_le_lintegral _ _)
      have hx1 : η x = 1 := hx
      rw [hx1, Real.one_rpow, one_mul, ← ofReal_norm,
        Real.norm_of_nonneg (Real.rpow_nonneg (hw0 x) _),
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hw0 x) _) hkn.le,
        ← Real.rpow_mul (hw0 x), mul_comm]
    calc (∫⁻ x in {x | η x = 1}, ‖(Real.log T - Real.log (u x + ε)) ^ p‖ₑ ^ (κ ^ n)) ^
          (1 / κ ^ n)
        ≤ a n ^ (1 / κ ^ n) := ENNReal.rpow_le_rpow h1 (one_div_pos.2 hkn).le
      _ = a n ^ (κ ^ n)⁻¹ := by rw [one_div]
      _ ≤ ENNReal.ofReal B * a 0 := hbound n
      _ = ENNReal.ofReal (B * (a 0).toReal) := by
          rw [ENNReal.ofReal_mul hB0, ENNReal.ofReal_toReal ha0top]
  have hae := ae_le_of_eLpNorm_le hwpm.restrict (q := fun n => κ ^ n)
    (fun n => pow_pos hκ0 n) (tendsto_pow_atTop_atTop_of_one_lt hκ)
    (mul_nonneg hB0 ENNReal.toReal_nonneg) hq
  rw [ae_restrict_iff' hUm] at hae
  filter_upwards [hae] with x hx hx1
  rw [← ha0, ← ENNReal.ofReal_toReal ha0top, ← ENNReal.ofReal_mul hB0]
  exact ENNReal.ofReal_le_ofReal (hx hx1)

end IsWeakEigensolution

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- A weak eigensolution changed on a null set (and kept nonnegative) is a weak eigensolution. -/
theorem congr_ae (hu : IsWeakEigensolution p F K lam u) {v : Euc d → ℝ}
    (hvu : v =ᵐ[volume] u) (hv0 : ∀ x, 0 ≤ v x) : IsWeakEigensolution p F K lam v where
  memW0 := hu.memW0.congr hvu.symm
  nonneg := hv0
  weakEq ψ hψ := by
    have hg : weakGrad v =ᵐ[volume] weakGrad u :=
      (hu.memW0.hasWeakGradient.congr_left hvu.symm).weakGrad_ae_eq
    have h1 : ∫ x, ⟪flux p F (weakGrad v x), weakGrad ψ x⟫ =
        ∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ :=
      integral_congr_ae (hg.mono fun x hx => by simp only [hx])
    have h2 : ∫ x, v x ^ (p - 1) * ψ x = ∫ x, u x ^ (p - 1) * ψ x :=
      integral_congr_ae (hvu.mono fun x hx => by simp only [hx])
    rw [h1, h2]
    exact hu.weakEq ψ hψ

/-- **The dichotomy on a ball**: for a bounded measurable weak eigensolution with `λ ≥ 0` and a
ball with `closedBall x₀ (3r) ⊆ K`, either `u = 0` a.e. on `ball x₀ r`, or `u ≥ c > 0` a.e. on
`ball x₀ r`. Proof: if `u ≥ δ` on a set `E ⊆ ball x₀ r` of positive measure, the Poincaré
inequality on `closedBall x₀ (2r)` (`MemW0.measure_mul_lintegral_sub_rpow_le`) and the logarithmic
Caccioppoli estimate (`log_caccioppoli`) bound `∫ ((log δ - log(u + ε))^+)^p` independently of
`ε`; hence the Moser sup bound (`moser_log_sup`) bounds `log T - log(u + ε)` on `ball x₀ r`
independently of `ε`, i.e. `u + ε ≥ c₀ > 0`; take `ε ≤ c₀/2`. -/
theorem ae_eq_zero_or_lower_bound_ball (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hK : Bornology.IsBounded K) (hu : IsWeakEigensolution p F K lam u) (hlam : 0 ≤ lam)
    (hd : 0 < d) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S) (humeas : Measurable u)
    {x₀ : Euc d} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x₀ (3 * r) ⊆ K) :
    (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), u x = 0) ∨
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), c ≤ u x := by
  by_cases hzero : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), u x = 0
  · exact Or.inl hzero
  right
  have hp0 : 0 < p := by linarith
  -- a set of positive measure where `u ≥ δ`
  obtain ⟨δ, hδ, hEpos⟩ : ∃ δ : ℝ, 0 < δ ∧ volume (Metric.ball x₀ r ∩ {x | δ ≤ u x}) ≠ 0 := by
    by_contra hcon
    apply hzero
    rw [ae_restrict_iff' measurableSet_ball, ae_iff]
    have hnull : volume (⋃ n : ℕ, Metric.ball x₀ r ∩ {x | 1 / ((n : ℝ) + 1) ≤ u x}) = 0 :=
      measure_iUnion_null fun n => by
        by_contra h
        exact hcon ⟨_, by positivity, h⟩
    refine measure_mono_null (fun x hx => ?_) hnull
    obtain ⟨hxB, hux⟩ := Classical.not_imp.1 hx
    have hpos : 0 < u x := lt_of_le_of_ne (huS x).1 (Ne.symm hux)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    exact mem_iUnion.2 ⟨n, hxB, hn.le⟩
  obtain ⟨E, hEdef⟩ : ∃ E : Set (Euc d), E = Metric.ball x₀ r ∩ {x | δ ≤ u x} := ⟨_, rfl⟩
  rw [← hEdef] at hEpos
  have hEm : MeasurableSet E := by
    rw [hEdef]
    exact measurableSet_ball.inter (measurableSet_le measurable_const humeas)
  have hEB : E ⊆ Metric.closedBall x₀ (2 * r) := by
    rw [hEdef]
    exact fun x hx => (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith))) hx.1
  have hB₂fin : volume (Metric.closedBall x₀ (2 * r)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hEfin : volume E ≠ ⊤ := ((measure_mono hEB).trans_lt hB₂fin.lt_top).ne
  have hdiam : ∀ x ∈ Metric.closedBall x₀ (2 * r), ∀ y ∈ Metric.closedBall x₀ (2 * r),
      ‖y - x‖ ≤ 4 * r := by
    intro x hx y hy
    rw [← dist_eq_norm]
    rw [Metric.mem_closedBall] at hx hy
    calc dist y x ≤ dist y x₀ + dist x₀ x := dist_triangle _ _ _
      _ ≤ 2 * r + 2 * r := add_le_add hy (by rw [dist_comm]; exact hx)
      _ = 4 * r := by ring
  obtain ⟨y₀, hy₀⟩ : E.Nonempty := nonempty_of_measure_ne_zero hEpos
  have hδS : δ ≤ S := by
    rw [hEdef] at hy₀
    exact hy₀.2.trans (huS y₀).2
  -- constants
  obtain ⟨c, hc, hcF⟩ := hF.exists_pos_mul_norm_le'
  obtain ⟨L, hL0, hL⟩ := hF.exists_norm_gradient_le
  obtain ⟨κ, hκ, C, hC, hSob⟩ := sobolev_inequality hd hp hK
  obtain ⟨b₁, hb₁⟩ : ∃ b : ContDiffBump x₀, b.rIn = r ∧ b.rOut = 2 * r :=
    ⟨⟨r, 2 * r, hr, by linarith⟩, rfl, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b : ContDiffBump x₀, b.rIn = 2 * r ∧ b.rOut = 3 * r :=
    ⟨⟨2 * r, 3 * r, by linarith, by linarith⟩, rfl, rfl⟩
  have hη₁K : tsupport (b₁ : Euc d → ℝ) ⊆ K := by
    rw [b₁.tsupport_eq, hb₁.2]
    exact (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have hη₂K : tsupport (b₂ : Euc d → ℝ) ⊆ K := by
    rw [b₂.tsupport_eq, hb₂.2]
    exact hball
  obtain ⟨G₁, hG₁⟩ := (continuous_gradient (b₁.contDiff (n := 1))).bounded_above_of_compact_support
    (hasCompactSupport_gradient b₁.hasCompactSupport)
  obtain ⟨B, hB0, hBsup⟩ := hu.moser_log_sup hp hF hlam hS huS hc hcF hL0 hL hκ hC hSob
    b₁.contDiff b₁.hasCompactSupport hη₁K (fun x => b₁.nonneg' x) (fun x => b₁.le_one) hG₁
    (Nat.le_ceil (κ * p + p))
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = S + 1 := ⟨_, rfl⟩
  have hT0 : 0 < T := by linarith
  have hδT : δ ≤ T := by linarith
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = c⁻¹ ^ p * 2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1)⁻¹ ^ p *
      ∫ x, (b₂ : Euc d → ℝ) x ^ ((⌈p⌉₊ : ℝ) - p) * ‖gradient b₂ x‖ ^ p := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ≥0∞, Y = 2 ^ d * ENNReal.ofReal (4 * r) ^ p *
      volume (Metric.closedBall x₀ (2 * r)) * ENNReal.ofReal C₁ := ⟨_, rfl⟩
  have hYtop : Y ≠ ⊤ := by
    rw [hY]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (by simp)) (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top))
      hB₂fin) ENNReal.ofReal_ne_top
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ≥0∞, Q = ENNReal.ofReal (2 ^ p) * (Y / volume E +
      ENNReal.ofReal ((Real.log T - Real.log δ) ^ p) * volume (Metric.closedBall x₀ (2 * r))) :=
    ⟨_, rfl⟩
  have hQtop : Q ≠ ⊤ := by
    rw [hQ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.div_ne_top hYtop hEpos, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB₂fin⟩)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ((ENNReal.ofReal B * Q).toReal) ^ p⁻¹ := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = T * Real.exp (-M) := ⟨_, rfl⟩
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    exact mul_pos hT0 (Real.exp_pos _)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min 1 (c₀ / 2) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    exact lt_min one_pos (half_pos hc₀pos)
  have hε1 : ε ≤ 1 := by
    rw [hε]
    exact min_le_left _ _
  have hεc : ε ≤ c₀ / 2 := by
    rw [hε]
    exact min_le_right _ _
  have hTε : S + ε ≤ T := by linarith
  refine ⟨c₀ / 2, half_pos hc₀pos, ?_⟩
  have hpos : ∀ t ∈ Icc 0 S, 0 < t + ε := fun t ht => by linarith [ht.1]
  -- the logarithmic Caccioppoli estimate on `closedBall x₀ (2r)`
  have hlog := hu.log_caccioppoli hp hF hlam hS huS hε0 hc hcF hL0 hL (Nat.le_ceil p) b₂.contDiff
    b₂.hasCompactSupport hη₂K (fun x => b₂.nonneg' x)
  rw [← hC₁] at hlog
  obtain ⟨hfw, hfg⟩ := memW0_comp_sub_of_hasDerivAt hp hu.memW0 hS huS
    (Ψ := fun t => Real.log (t + ε)) (ψ' := fun t => (t + ε)⁻¹)
    (fun t ht => by
      have h := ((hasDerivAt_id' t).add_const ε).log (hpos t ht).ne'
      rwa [one_div] at h)
    ((continuousOn_id.add continuousOn_const).inv₀ fun t ht => (hpos t ht).ne')
  have hgradB : ∫⁻ z in Metric.closedBall x₀ (2 * r),
      ‖weakGrad (fun x => Real.log (u x + ε) - Real.log (0 + ε)) z‖ₑ ^ p ≤
      ENNReal.ofReal C₁ := by
    have hint : Integrable fun x =>
        (b₂ : Euc d → ℝ) x ^ ⌈p⌉₊ * ‖(u x + ε)⁻¹ • weakGrad u x‖ ^ p := by
      have h1 : Integrable fun x => ‖(u x + ε)⁻¹ • weakGrad u x‖ ^ p :=
        (integrable_norm_rpow_of_memLp hp0 hfw.memLp_weakGrad).congr
          (hfg.mono fun x hx => by simp only [hx])
      exact h1.bdd_mul (c := 1) (b₂.continuous.pow _).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (b₂.nonneg' x) _)]
          exact pow_le_one₀ (b₂.nonneg' x) b₂.le_one)
    calc ∫⁻ z in Metric.closedBall x₀ (2 * r),
          ‖weakGrad (fun x => Real.log (u x + ε) - Real.log (0 + ε)) z‖ₑ ^ p
        = ∫⁻ z in Metric.closedBall x₀ (2 * r), ENNReal.ofReal
            ((b₂ : Euc d → ℝ) z ^ ⌈p⌉₊ * ‖(u z + ε)⁻¹ • weakGrad u z‖ ^ p) := by
          refine setLIntegral_congr_fun_ae measurableSet_closedBall ?_
          filter_upwards [hfg] with z hz hzB
          have h1 : (b₂ : Euc d → ℝ) z = 1 := b₂.one_of_mem_closedBall (by rwa [hb₂.1])
          rw [hz, h1, one_pow, one_mul, ← ofReal_norm,
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
      _ ≤ ∫⁻ z, ENNReal.ofReal
            ((b₂ : Euc d → ℝ) z ^ ⌈p⌉₊ * ‖(u z + ε)⁻¹ • weakGrad u z‖ ^ p) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal
            (∫ z, (b₂ : Euc d → ℝ) z ^ ⌈p⌉₊ * ‖(u z + ε)⁻¹ • weakGrad u z‖ ^ p) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z =>
            mul_nonneg (pow_nonneg (b₂.nonneg' z) _) (Real.rpow_nonneg (norm_nonneg _) _))).symm
      _ ≤ ENNReal.ofReal C₁ := ENNReal.ofReal_le_ofReal hlog
  -- the Poincaré inequality
  have hPo := hfw.measure_mul_lintegral_sub_rpow_le hp (convex_closedBall x₀ (2 * r))
    measurableSet_closedBall hB₂fin hdiam hEm hEB (a := Real.log δ - Real.log (0 + ε))
    (fun y hy => by
      rw [hEdef] at hy
      show Real.log δ - Real.log (0 + ε) ≤ Real.log (u y + ε) - Real.log (0 + ε)
      have hy2 : δ ≤ u y := hy.2
      have h1 : Real.log δ ≤ Real.log (u y + ε) := Real.log_le_log hδ (by linarith)
      linarith)
  beta_reduce at hPo
  have hX : ∫⁻ x in Metric.closedBall x₀ (2 * r),
      ENNReal.ofReal (Real.log δ - Real.log (u x + ε)) ^ p ≤ Y / volume E := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hEpos) (Or.inl hEfin), mul_comm]
    have e : ∫⁻ x in Metric.closedBall x₀ (2 * r), ENNReal.ofReal (Real.log δ -
        Real.log (0 + ε) - (Real.log (u x + ε) - Real.log (0 + ε))) ^ p =
        ∫⁻ x in Metric.closedBall x₀ (2 * r),
          ENNReal.ofReal (Real.log δ - Real.log (u x + ε)) ^ p := by
      refine lintegral_congr fun x => ?_
      congr 2
      ring
    rw [← e]
    refine hPo.trans ?_
    rw [hY]
    exact mul_le_mul_right hgradB _
  -- the `L^p` norm of `w(u)` on the support of the cutoff
  have hNp : 0 < ((⌈κ * p + p⌉₊ : ℕ) : ℝ) - p := by
    have h1 := Nat.le_ceil (κ * p + p)
    have h2 : 0 < κ * p := mul_pos (by linarith) hp0
    linarith
  have ha₀ : ∫⁻ x, ENNReal.ofReal ((b₁ : Euc d → ℝ) x ^ ((⌈κ * p + p⌉₊ : ℝ) - p) *
      (Real.log T - Real.log (u x + ε)) ^ p) ≤ Q := by
    have hTδ : 0 ≤ Real.log T - Real.log δ := sub_nonneg.2 (Real.log_le_log hδ hδT)
    have hpt : ∀ x, ENNReal.ofReal ((b₁ : Euc d → ℝ) x ^ ((⌈κ * p + p⌉₊ : ℝ) - p) *
        (Real.log T - Real.log (u x + ε)) ^ p) ≤
        (Metric.closedBall x₀ (2 * r)).indicator (fun x => ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal (Real.log δ - Real.log (u x + ε)) ^ p +
            ENNReal.ofReal ((Real.log T - Real.log δ) ^ p))) x := by
      intro x
      by_cases hx : x ∈ Metric.closedBall x₀ (2 * r)
      · rw [indicator_of_mem hx]
        have hw : 0 ≤ Real.log T - Real.log (u x + ε) :=
          sub_nonneg.2 (Real.log_le_log (hpos _ (huS x)) (by linarith [(huS x).2]))
        have hA : Real.log T - Real.log (u x + ε) ≤
            max (Real.log δ - Real.log (u x + ε)) 0 + (Real.log T - Real.log δ) := by
          have := le_max_left (Real.log δ - Real.log (u x + ε)) 0
          linarith
        have h1 : (b₁ : Euc d → ℝ) x ^ ((⌈κ * p + p⌉₊ : ℝ) - p) *
            (Real.log T - Real.log (u x + ε)) ^ p ≤
            2 ^ p * (max (Real.log δ - Real.log (u x + ε)) 0 ^ p +
              (Real.log T - Real.log δ) ^ p) := by
          calc (b₁ : Euc d → ℝ) x ^ ((⌈κ * p + p⌉₊ : ℝ) - p) *
                (Real.log T - Real.log (u x + ε)) ^ p
              ≤ 1 * (Real.log T - Real.log (u x + ε)) ^ p :=
                mul_le_mul_of_nonneg_right (Real.rpow_le_one (b₁.nonneg' x) b₁.le_one hNp.le)
                  (Real.rpow_nonneg hw _)
            _ = (Real.log T - Real.log (u x + ε)) ^ p := one_mul _
            _ ≤ (max (Real.log δ - Real.log (u x + ε)) 0 + (Real.log T - Real.log δ)) ^ p :=
                Real.rpow_le_rpow hw hA hp0.le
            _ ≤ 2 ^ p * (max (Real.log δ - Real.log (u x + ε)) 0 ^ p +
                  (Real.log T - Real.log δ) ^ p) :=
                add_rpow_le_two_rpow_mul hp0.le (le_max_right _ _) hTδ
        refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
        have hmax : ENNReal.ofReal (max (Real.log δ - Real.log (u x + ε)) 0) =
            ENNReal.ofReal (Real.log δ - Real.log (u x + ε)) := by
          rcases le_total (Real.log δ - Real.log (u x + ε)) 0 with h | h
          · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
          · rw [max_eq_left h]
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
          ENNReal.ofReal_add (Real.rpow_nonneg (le_max_right _ _) _) (Real.rpow_nonneg hTδ _),
          ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hp0.le, hmax]
      · rw [indicator_of_notMem hx]
        have hx' : x ∉ tsupport (b₁ : Euc d → ℝ) := by
          rw [b₁.tsupport_eq, hb₁.2]
          exact hx
        rw [image_eq_zero_of_notMem_tsupport hx', Real.zero_rpow hNp.ne', zero_mul,
          ENNReal.ofReal_zero]
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_indicator measurableSet_closedBall,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
      setLIntegral_const, hQ]
    exact mul_le_mul_right (add_le_add hX le_rfl) _
  -- the sup bound
  have hsup := hBsup ε hε0 T hTε
  filter_upwards [ae_restrict_of_ae hsup, ae_restrict_mem measurableSet_ball] with x hx hxB
  have h1 : (b₁ : Euc d → ℝ) x = 1 :=
    b₁.one_of_mem_closedBall (by rw [hb₁.1]; exact Metric.ball_subset_closedBall hxB)
  have h2 := (hx h1).trans (mul_le_mul_right ha₀ _)
  have hBQ : ENNReal.ofReal B * Q ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQtop
  have h3 : (Real.log T - Real.log (u x + ε)) ^ p ≤ (ENNReal.ofReal B * Q).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hBQ).1 h2
  have hux := hpos _ (huS x)
  have hw : 0 ≤ Real.log T - Real.log (u x + ε) :=
    sub_nonneg.2 (Real.log_le_log hux (by linarith [(huS x).2]))
  have h4 : Real.log T - Real.log (u x + ε) ≤ M := by
    have h5 := Real.rpow_le_rpow (Real.rpow_nonneg hw _) h3 (inv_nonneg.2 hp0.le)
    rwa [Real.rpow_rpow_inv hw hp0.ne', ← hM] at h5
  have h6 : c₀ ≤ u x + ε := by
    rw [hc₀]
    calc T * Real.exp (-M) ≤ T * Real.exp (Real.log (u x + ε) - Real.log T) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hT0.le
      _ = u x + ε := by
          rw [Real.exp_sub, Real.exp_log hux, Real.exp_log hT0]
          field_simp
  linarith

end IsWeakEigensolution

/-- A finite family of positive reals has a positive lower bound. -/
theorem exists_pos_forall_le_of_finset {ι : Type*} (t : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ t, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ t, c ≤ f i := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  · obtain ⟨i₀, hi₀, hmin⟩ := t.exists_min_image f ht
    exact ⟨f i₀, hf i₀ hi₀, hmin⟩

/-- **From the local dichotomy to a uniform lower bound**: if `u` vanishes a.e. outside the good
convex set `K`, is not a.e. zero, and every point of `K` has a ball on which either `u = 0` a.e. or
`u ≥ c > 0` a.e., then `u` is bounded below by a positive constant a.e. on every compact subset
of `K` (the two sets of centres are open and disjoint, `K` is connected, and a compact set is
covered by finitely many balls). -/
theorem lower_bound_of_local_dichotomy {K : Set (Euc d)} (hK : IsGoodConvex K)
    {u : Euc d → ℝ} (hne : ¬ u =ᵐ[volume] 0) (hout : ∀ᵐ x, x ∉ K → u x = 0)
    (hdich : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧
      ((∀ᵐ y ∂(volume.restrict (Metric.ball x r)), u y = 0) ∨
        ∃ c : ℝ, 0 < c ∧ ∀ᵐ y ∂(volume.restrict (Metric.ball x r)), c ≤ u y)) :
    ∀ S : Set (Euc d), IsCompact S → S ⊆ K →
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂(volume.restrict S), c ≤ u x := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Set (Euc d), Z = {x | ∃ r : ℝ, 0 < r ∧
      ∀ᵐ y ∂(volume.restrict (Metric.ball x r)), u y = 0} := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Set (Euc d), P = {x | ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᵐ y ∂(volume.restrict (Metric.ball x r)), c ≤ u y} := ⟨_, rfl⟩
  have hsub : ∀ {x y : Euc d} {r : ℝ}, y ∈ Metric.ball x r →
      Metric.ball y (r - dist y x) ⊆ Metric.ball x r := fun {x y r} hy z hz => by
    rw [Metric.mem_ball] at hz ⊢
    linarith [dist_triangle z y x]
  have hZo : IsOpen Z := by
    rw [hZ, Metric.isOpen_iff]
    rintro x ⟨r, hr, hx⟩
    exact ⟨r, hr, fun y hy => ⟨r - dist y x, sub_pos.2 hy,
      ae_restrict_of_ae_restrict_of_subset (hsub hy) hx⟩⟩
  have hPo : IsOpen P := by
    rw [hP, Metric.isOpen_iff]
    rintro x ⟨r, hr, c, hc, hx⟩
    exact ⟨r, hr, fun y hy => ⟨r - dist y x, sub_pos.2 hy, c, hc,
      ae_restrict_of_ae_restrict_of_subset (hsub hy) hx⟩⟩
  have hdisj : K ∩ (Z ∩ P) = ∅ := by
    rw [hZ, hP]
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨r₁, hr₁, h₁⟩ ⟨r₂, hr₂, c, hc, h₂⟩
    have h₁' := ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (min_le_left r₁ r₂)) h₁
    have h₂' := ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (min_le_right r₁ r₂)) h₂
    have hfalse : ∀ᵐ y ∂(volume.restrict (Metric.ball x (min r₁ r₂))), False := by
      filter_upwards [h₁', h₂'] with y hy1 hy2
      rw [hy1] at hy2
      linarith
    rw [ae_iff, Measure.restrict_apply' measurableSet_ball] at hfalse
    simp only [not_false_eq_true, Set.ofPred_true, univ_inter] at hfalse
    exact (Metric.measure_ball_pos volume x (lt_min hr₁ hr₂)).ne' hfalse
  have hcover : K ⊆ Z ∪ P := fun x hx => by
    obtain ⟨r, hr, h | ⟨c, hc, h⟩⟩ := hdich x hx
    · left
      rw [hZ]
      exact ⟨r, hr, h⟩
    · right
      rw [hP]
      exact ⟨r, hr, c, hc, h⟩
  have hKP : K ⊆ P := by
    rcases isPreconnected_iff_subset_of_disjoint.1 hK.convex.isPreconnected Z P hZo hPo hcover
      hdisj with hKZ | hKP
    · exfalso
      apply hne
      have hKnull : volume {x | x ∈ K ∧ u x ≠ 0} = 0 := by
        refine measure_null_of_locally_null _ fun x hx => ?_
        have hxZ := hKZ hx.1
        rw [hZ] at hxZ
        obtain ⟨r, hr, h⟩ := hxZ
        refine ⟨{x | x ∈ K ∧ u x ≠ 0} ∩ Metric.ball x r,
          inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x hr), ?_⟩
        rw [ae_restrict_iff' measurableSet_ball, ae_iff] at h
        refine measure_mono_null (fun y hy => ?_) h
        exact Classical.not_imp.2 ⟨hy.2, hy.1.2⟩
      filter_upwards [hout, measure_eq_zero_iff_ae_notMem.1 hKnull] with x hx1 hx2
      by_cases hxK : x ∈ K
      · by_contra hux
        exact hx2 ⟨hxK, hux⟩
      · exact hx1 hxK
    · exact hKP
  intro S hS hSK
  have hSP : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᵐ y ∂(volume.restrict (Metric.ball x r)), c ≤ u y := fun x hx => by
    have h := hKP (hSK hx)
    rw [hP] at h
    exact h
  choose! r hr c hc hlow using hSP
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun x : S => Metric.ball (x : Euc d) (r x))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hr x hx)⟩)
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_pos_forall_le_of_finset t (fun i : S => c i)
    (fun i _ => hc i i.2)
  refine ⟨c₀, hc₀, ae_restrict_of_ae_restrict_of_subset ht ?_⟩
  rw [ae_restrict_biUnion_finset_iff]
  intro i hi
  filter_upwards [hlow i i.2] with y hy
  exact (hc₀le i hi).trans hy

/-- **Positivity: the weak Harnack inequality** (Trudinger 1967, *On Harnack type inequalities and
their application to quasilinear elliptic equations*, Comm. Pure Appl. Math. 20, Theorem 1.2;
towards Mosconi–Riey–Squassina 2024, Proposition 4.5; paper Appendix A, *Eigenfunction inputs*):
a nonnegative weak solution (`λ ≥ 0`) on the good convex set `K` that is not a.e. zero is bounded
below by a positive constant on every compact subset of `K`.

Proof: `u` is bounded (`exists_ae_le`), so we may pass to a measurable representative with values
in `[0, S]` (`congr_ae`); every point of `K` has a ball with the dichotomy
`ae_eq_zero_or_lower_bound_ball`, and `lower_bound_of_local_dichotomy` concludes. In dimension `0`
the space is a point. -/
theorem weak_harnack_pos {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} (hK : IsGoodConvex K) {lam : ℝ} {u : Euc d → ℝ}
    (hu : IsWeakEigensolution p F K lam u) (hlam : 0 ≤ lam) (hne : ¬ u =ᵐ[volume] 0) :
    ∀ S : Set (Euc d), IsCompact S → S ⊆ K →
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂(volume.restrict S), c ≤ u x := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · intro S _ _
    have hconst : ∀ x : Euc d, x = 0 := fun x => Subsingleton.elim x 0
    have hu0 : u 0 ≠ 0 := fun h0 =>
      hne (Eventually.of_forall fun x => by rw [hconst x]; exact h0)
    refine ⟨u 0, lt_of_le_of_ne (hu.nonneg 0) (Ne.symm hu0), Eventually.of_forall fun x => ?_⟩
    rw [hconst x]
  have hd0 : 0 < d := Fin.pos_iff_nonempty.2 hd
  obtain ⟨M, hM⟩ := hu.exists_ae_le hp hF hK.isBounded
  have hS0 : 0 ≤ max M 0 := le_max_right _ _
  have hmeas := hu.memW0.memLp.aestronglyMeasurable
  obtain ⟨v, hvdef⟩ : ∃ v : Euc d → ℝ, v = fun x => max 0 (min (hmeas.mk u x) (max M 0)) :=
    ⟨_, rfl⟩
  have hvmeas : Measurable v := by
    rw [hvdef]
    exact measurable_const.max (hmeas.stronglyMeasurable_mk.measurable.min measurable_const)
  have hvS : ∀ x, v x ∈ Icc 0 (max M 0) := fun x => by
    rw [hvdef]
    exact clamp_mem hS0 _
  have hvu : v =ᵐ[volume] u := by
    filter_upwards [hmeas.ae_eq_mk, hM] with x h1 h2
    rw [hvdef]
    show max 0 (min (hmeas.mk u x) (max M 0)) = u x
    rw [← h1]
    exact clamp_eq ⟨hu.nonneg x, h2.trans (le_max_left _ _)⟩
  have hv := hu.congr_ae hvu fun x => (hvS x).1
  have hvne : ¬ v =ᵐ[volume] 0 := fun h => hne (hvu.symm.trans h)
  have key := lower_bound_of_local_dichotomy hK hvne hv.memW0.ae_eq_zero fun x hx => by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK.isOpen x hx
    have hr' : 0 < r / 4 := by positivity
    exact ⟨r / 4, hr', hv.ae_eq_zero_or_lower_bound_ball hp hF hK.isBounded hlam hd0 hS0 hvS
      hvmeas hr' ((Metric.closedBall_subset_ball (by linarith)).trans hball)⟩
  intro S hS hSK
  obtain ⟨c, hc, hcS⟩ := key S hS hSK
  refine ⟨c, hc, ?_⟩
  filter_upwards [hcS, ae_restrict_of_ae hvu] with x h1 h2
  rwa [← h2]

end Komlos.Literature
