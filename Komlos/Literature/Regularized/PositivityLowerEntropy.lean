import Komlos.Literature.Regularized.PositivityLowerSqrt

/-!
# Lane `L2p` (`reg/pos-lower`), step 2: the entropy comparison

`REGULARIZED_ROUTE.md`, Revision 2 (iii), route (A)(i): *the minimizer has an integrable
logarithm*.  This is the only place where the **entropy** of the regularized energy is used,
and it is what replaces the Euler–Lagrange equation (which is not available: the integrand
`w²Ψ(∇w/w)` is not differentiable in `w` at `w = 0`).

## The argument

Write `ρ = v²` for the density of the minimizer and `J` for the local (unconstrained) functional
`regFree`, which `v` minimizes over the whole competitor class (`IsRegMinimizer.regFree_le`).
For a smooth `h` with `0 ≤ h ≤ 1` compactly supported in `K` and `τ ∈ (0, 1]`, compare `v` with
`w = √(v² + τ h²)`, whose density is `ρ + τ h²`.  Three elementary facts:

* the **kinetic** part is subadditive in the density (`homogeneousDensity_two_add_le`, i.e. joint
  convexity of the perspective of `Ψ`): `∫D(w, ∇w) ≤ ∫D(v, ∇v) + τ ∫D(h, ∇h)`;
* the **normalization** term is exactly linear: `∫w² = ∫v² + τ ∫h²`;
* the **entropy** `(κ/4) ∫ ρ log ρ` is convex in `ρ`, so `ρ log ρ ≥ ρ_w log ρ_w +
  (log ρ_w + 1)(ρ - ρ_w)` pointwise, i.e. the entropy *decrease* is at most
  `(κ/4) τ ∫ h² (log ρ_w + 1)` (`mul_log_convexity`).

Minimality `J(v) ≤ J(w)` therefore gives, after dividing by `τ > 0`,

`∫ h² (-log(v² + τ h²)) ≤ (4/κ) (∫D(h,∇h) - Λ ∫h²) + ∫h²`,

a bound **independent of `τ`**.  Since `h ≤ 1` gives `v² + τh² ≤ v² + τ`, the same bound holds
for `∫ h² (-log(v² + τ))`, and that is the statement `exists_weighted_log_bound` of this file;
the monotone limit `τ ↓ 0` is taken in
`Komlos/Literature/Regularized/PositivityLowerLog.lean`.

The competitor `v + τψ`, which would be far easier to handle, is useless here: it perturbs the
density by `2τvψ + τ²ψ²`, which vanishes exactly where `v` does — exactly where the information
is wanted.  This is why the square-root competitor of
`Komlos/Literature/Regularized/PositivityLowerSqrt.lean` is needed.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ} {K : Set (Euc d)} {v h : Euc d → ℝ}

/-! ### Elementary facts about `s ↦ s log s` -/

/-- The entropy potential at `p = 2` written in the density variable: `P(s) = (κ/4) ρ log ρ`
with `ρ = s²`. -/
theorem entropyPotential_two_sq (κ s : ℝ) :
    Korevaar.entropyPotential 2 κ s = κ / 4 * (s ^ 2 * Real.log (s ^ 2)) := by
  rw [pos_entropyPotential_two, Real.log_pow]
  push_cast
  ring

/-- **Convexity of `t ↦ t log t`** in the form of the supporting line at `t`:
`t log t + (log t + 1)(s - t) ≤ s log s` for `s ≥ 0` and `t > 0`. -/
theorem mul_log_convexity {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    t * Real.log t + (Real.log t + 1) * (s - t) ≤ s * Real.log s := by
  rcases hs.eq_or_lt with rfl | hspos
  · simp only [Real.log_zero, zero_mul, zero_sub]
    nlinarith [Real.log_le_sub_one_of_pos ht]
  · have hlog : Real.log (t / s) ≤ t / s - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hkey : s * Real.log (t / s) ≤ t - s := by
      have := mul_le_mul_of_nonneg_left hlog hspos.le
      have hts : s * (t / s - 1) = t - s := by field_simp
      linarith [hts.le, hts.ge]
    rw [Real.log_div ht.ne' hspos.ne'] at hkey
    nlinarith [hkey]

/-! ### Smooth compactly supported functions as competitors -/

/-- A smooth nonnegative function compactly supported in `K` is a competitor of the local
problem. -/
theorem isRegComp_of_contDiff (hh : ContDiff ℝ 1 h) (hhs : HasCompactSupport h)
    (hhK : tsupport h ⊆ K) (hh0 : ∀ x, 0 ≤ h x) : IsRegComp K h := by
  obtain ⟨A, hA⟩ := hh.continuous.bounded_above_of_compact_support hhs
  refine ⟨memW0_of_contDiff hh hhs hhK 2, hh0,
    fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => hx (hhK hmem), ⟨A, fun x => ?_⟩⟩
  exact le_trans (le_abs_self _) (by rw [← Real.norm_eq_abs]; exact hA x)

/-- The gradient of a constant multiple. -/
theorem gradient_const_mul (hh : ContDiff ℝ 1 h) (a : ℝ) (x : Euc d) :
    gradient (fun y => a * h y) x = a • gradient h x := by
  refine gradient_eq_smul_of_hasFDerivAt ?_
  simpa using ((hh.differentiable one_ne_zero) x).hasFDerivAt.const_mul a

/-- Scaling a smooth compactly supported nonnegative function by `√τ`. -/
theorem contDiff_sqrt_smul (hh : ContDiff ℝ ∞ h) (hhs : HasCompactSupport h)
    (hhK : tsupport h ⊆ K) (hh0 : ∀ x, 0 ≤ h x) (τ : ℝ) :
    ContDiff ℝ ∞ (fun x => Real.sqrt τ * h x) ∧
      HasCompactSupport (fun x => Real.sqrt τ * h x) ∧
      tsupport (fun x => Real.sqrt τ * h x) ⊆ K ∧
      (∀ x, 0 ≤ Real.sqrt τ * h x) := by
  have hsub : tsupport (fun x => Real.sqrt τ * h x) ⊆ tsupport h := by
    refine closure_mono (fun x hx => ?_)
    simp only [Function.mem_support] at hx ⊢
    exact fun hzero => hx (by rw [hzero, mul_zero])
  refine ⟨contDiff_const.mul hh, IsCompact.of_isClosed_subset hhs isClosed_closure hsub,
    hsub.trans hhK, fun x => mul_nonneg (Real.sqrt_nonneg _) (hh0 x)⟩

/-- **Integrability of the weighted logarithm**: `h² log(v² + τ)` is bounded (because
`τ ≤ v² + τ ≤ M² + 1`) and supported in `K`, hence integrable. -/
theorem integrable_sq_mul_neg_log (hK : IsGoodConvex K) (hcomp : IsRegComp K v)
    (hhcomp : IsRegComp K h) (hh1 : ∀ x, h x ≤ 1) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    Integrable (fun x => h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) volume := by
  obtain ⟨M₀, hM₀⟩ := hcomp.exists_le
  have hM1 : (1 : ℝ) ≤ max M₀ 1 := le_max_right _ _
  have hvM : ∀ x, v x ≤ max M₀ 1 := fun x => (hM₀ x).trans (le_max_left _ _)
  have hvmeas : AEStronglyMeasurable v volume := hcomp.aestronglyMeasurable
  have hlogmeas : AEStronglyMeasurable (fun x => Real.log (v x ^ 2 + τ)) volume :=
    (Real.measurable_log.comp_aemeasurable
      ((hvmeas.aemeasurable.pow_const 2).add_const τ)).aestronglyMeasurable
  have hlogbd : ∀ x, |Real.log (v x ^ 2 + τ)| ≤
      |Real.log τ| + |Real.log ((max M₀ 1) ^ 2 + 1)| := by
    intro x
    have h1 : Real.log τ ≤ Real.log (v x ^ 2 + τ) :=
      Real.log_le_log hτ0 (by nlinarith [sq_nonneg (v x)])
    have h2 : Real.log (v x ^ 2 + τ) ≤ Real.log ((max M₀ 1) ^ 2 + 1) := by
      refine Real.log_le_log (by positivity) ?_
      nlinarith [hcomp.nonneg x, hvM x]
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le (Real.log τ), le_abs_self (Real.log ((max M₀ 1) ^ 2 + 1)),
        abs_nonneg (Real.log ((max M₀ 1) ^ 2 + 1)), abs_nonneg (Real.log τ)]
    · nlinarith [le_abs_self (Real.log ((max M₀ 1) ^ 2 + 1)), abs_nonneg (Real.log τ)]
  refine integrable_of_bounded_of_support
    (B := |Real.log τ| + |Real.log ((max M₀ 1) ^ 2 + 1)|) hK
    ((hhcomp.aestronglyMeasurable.pow 2).mul hlogmeas.neg) (fun x => ?_)
    (fun x hx => by rw [hhcomp.eq_zero_of_notMem x hx]; ring)
  rw [abs_mul, abs_neg]
  have h1 : |h x ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hhcomp.nonneg x, hh1 x]
  nlinarith [hlogbd x, abs_nonneg (Real.log (v x ^ 2 + τ)), abs_nonneg (h x ^ 2)]

/-! ### The entropy comparison -/

/-- **The weighted logarithmic bound** (`REGULARIZED_ROUTE.md`, Revision 2 (iii), route (A)(i)).
For a smooth cutoff `0 ≤ h ≤ 1` compactly supported in `K` there is a constant `B`,
*independent of `τ`*, with

`∫ h² (-log(v² + τ)) ≤ B`  for every `τ ∈ (0, 1]`.

Proof: compare the minimizer `v` with the square-root competitor `w = √(v² + τ h²)`, whose
density is `v² + τ h²`.  Local minimality (`IsRegMinimizer.regFree_le`) gives
`∫D(v,∇v) + ∫P(v) - Λ∫v² ≤ ∫D(w,∇w) + ∫P(w) - Λ∫w²`.  The kinetic term is subadditive in the
density (`homogeneousDensity_two_add_le`), so `∫D(w,∇w) ≤ ∫D(v,∇v) + τ∫D(h,∇h)`, and
`∫w² = ∫v² + τ∫h²` exactly.  Hence `∫P(v) - ∫P(w) ≤ τ(∫D(h,∇h) - Λ∫h²)`.  On the other hand the
entropy `P(s) = (κ/4) ρ log ρ` (`entropyPotential_two_sq`) is convex in `ρ = s²`, so its
supporting line at `ρ_w = v² + τh²` gives the pointwise bound
`P(v) - P(w) ≥ -(κ/4)(log ρ_w + 1) τ h² ≥ -(κ/4)(log(v² + τ) + 1) τ h²`
(the last step because `ρ_w ≤ v² + τ` when `h ≤ 1`, and both sides vanish where `h = 0`).
Dividing by `τ > 0` removes every trace of `τ` from the estimate. -/
theorem exists_weighted_log_bound (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hv : IsRegMinimizer 2 κ Ψ K v) (hcomp : IsRegComp K v)
    (hh : ContDiff ℝ ∞ h) (hhs : HasCompactSupport h) (hhK : tsupport h ⊆ K)
    (hh0 : ∀ x, 0 ≤ h x) (hh1 : ∀ x, h x ≤ 1) :
    ∃ B : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      (∫ x, h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) ≤ B := by
  classical
  obtain ⟨M₀, hM₀⟩ := hcomp.exists_le
  have hM1 : (1 : ℝ) ≤ max M₀ 1 := le_max_right _ _
  have hvM : ∀ x, v x ≤ max M₀ 1 := fun x => (hM₀ x).trans (le_max_left _ _)
  have hh1' : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast le_top)
  have hhcomp : IsRegComp K h := isRegComp_of_contDiff hh1' hhs hhK hh0
  have hhgrad : weakGrad h =ᵐ[volume] gradient h := weakGrad_ae_eq_gradient hh1' hhs
  have hhsqint : Integrable (fun x => h x ^ 2) volume := hhcomp.integrable_sq
  have hDhint : Integrable
      (fun x => Korevaar.homogeneousDensity 2 Ψ (h x) (gradient h x)) volume := by
    refine (hhcomp.integrable_density hΨ).congr ?_
    filter_upwards [hhgrad] with x hx
    rw [hx]
  have hvDint : Integrable
      (fun x => Korevaar.homogeneousDensity 2 Ψ (v x) (weakGrad v x)) volume :=
    hcomp.integrable_density hΨ
  have hv2int : Integrable (fun x => v x ^ 2) volume := hcomp.integrable_sq
  have hPvint : Integrable (fun x => Korevaar.entropyPotential 2 κ (v x)) volume :=
    hcomp.integrable_entropy hK κ
  have hvmeas : AEStronglyMeasurable v volume := hcomp.aestronglyMeasurable
  refine ⟨4 / κ * ((∫ x, Korevaar.homogeneousDensity 2 Ψ (h x) (gradient h x)) -
    (regMin 2 κ Ψ K + κ / 4) * ∫ x, h x ^ 2) + ∫ x, h x ^ 2, fun τ hτ0 hτ1 => ?_⟩
  -- the competitor `w = √(v² + τ h²)`
  obtain ⟨hgC, hgs, hgK, hg0⟩ := contDiff_sqrt_smul hh hhs hhK hh0 τ
  have hsqτ : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ0.le
  have hsqτpos : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  obtain ⟨hwgrad, hwcomp⟩ := hcomp.sqrtAdd_spec hK hgC hgs hgK hg0
  have hwsq : ∀ x, sqrtAdd v (fun y => Real.sqrt τ * h y) x ^ 2 = v x ^ 2 + τ * h x ^ 2 := by
    intro x
    rw [sqrtAdd_sq]
    congr 1
    rw [mul_pow, hsqτ]
  have hwgradae : weakGrad (sqrtAdd v fun y => Real.sqrt τ * h y) =ᵐ[volume]
      sqrtAddGrad v (fun y => Real.sqrt τ * h y) := hwgrad.weakGrad_ae_eq
  -- the normalization is exactly linear
  have hnorm : (∫ x, sqrtAdd v (fun y => Real.sqrt τ * h y) x ^ 2) =
      (∫ x, v x ^ 2) + τ * ∫ x, h x ^ 2 := by
    rw [← integral_const_mul, ← integral_add hv2int (hhsqint.const_mul τ)]
    exact integral_congr_ae (Eventually.of_forall hwsq)
  -- the kinetic part is subadditive in the density
  have hDgeq : ∀ x, Korevaar.homogeneousDensity 2 Ψ ((fun y => Real.sqrt τ * h y) x)
      (gradient (fun y => Real.sqrt τ * h y) x) =
      τ * Korevaar.homogeneousDensity 2 Ψ (h x) (gradient h x) := by
    intro x
    rw [gradient_const_mul hh1' _ x, pos_homogeneousDensity_two_smul Ψ hsqτpos, hsqτ]
  have hDgint : Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ
      ((fun y => Real.sqrt τ * h y) x) (gradient (fun y => Real.sqrt τ * h y) x)) volume :=
    (hDhint.const_mul τ).congr (Eventually.of_forall fun x => (hDgeq x).symm)
  have hDwint : Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ
      (sqrtAdd v (fun y => Real.sqrt τ * h y) x)
      (sqrtAddGrad v (fun y => Real.sqrt τ * h y) x)) volume := by
    refine (hwcomp.integrable_density hΨ).congr ?_
    filter_upwards [hwgradae] with x hx
    rw [hx]
  have hkin : (∫ x, Korevaar.homogeneousDensity 2 Ψ
        (sqrtAdd v (fun y => Real.sqrt τ * h y) x)
        (weakGrad (sqrtAdd v fun y => Real.sqrt τ * h y) x)) ≤
      (∫ x, Korevaar.homogeneousDensity 2 Ψ (v x) (weakGrad v x)) +
        τ * ∫ x, Korevaar.homogeneousDensity 2 Ψ (h x) (gradient h x) := by
    have hcongr : (∫ x, Korevaar.homogeneousDensity 2 Ψ
          (sqrtAdd v (fun y => Real.sqrt τ * h y) x)
          (weakGrad (sqrtAdd v fun y => Real.sqrt τ * h y) x)) =
        ∫ x, Korevaar.homogeneousDensity 2 Ψ (sqrtAdd v (fun y => Real.sqrt τ * h y) x)
          (sqrtAddGrad v (fun y => Real.sqrt τ * h y) x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwgradae] with x hx
      rw [hx]
    have hptw : ∀ x, Korevaar.homogeneousDensity 2 Ψ
        (sqrtAdd v (fun y => Real.sqrt τ * h y) x)
        (sqrtAddGrad v (fun y => Real.sqrt τ * h y) x) ≤
        Korevaar.homogeneousDensity 2 Ψ (v x) (weakGrad v x) +
          Korevaar.homogeneousDensity 2 Ψ ((fun y => Real.sqrt τ * h y) x)
            (gradient (fun y => Real.sqrt τ * h y) x) := fun x =>
      homogeneousDensity_two_add_le hΨ.convexOn (hcomp.nonneg x) (hg0 x) _ _
    have hstep := integral_mono hDwint (hvDint.add hDgint) hptw
    have hDgval : (∫ x, Korevaar.homogeneousDensity 2 Ψ ((fun y => Real.sqrt τ * h y) x)
        (gradient (fun y => Real.sqrt τ * h y) x)) =
        τ * ∫ x, Korevaar.homogeneousDensity 2 Ψ (h x) (gradient h x) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall hDgeq)
    rw [hcongr]
    refine le_trans hstep ?_
    simp only [Pi.add_apply]
    rw [integral_add hvDint hDgint, hDgval]
  -- the entropy comparison, pointwise
  have hentr : ∀ x, -(κ / 4) * (Real.log (v x ^ 2 + τ) + 1) * (τ * h x ^ 2) ≤
      Korevaar.entropyPotential 2 κ (v x) -
        Korevaar.entropyPotential 2 κ (sqrtAdd v (fun y => Real.sqrt τ * h y) x) := by
    intro x
    rcases (hh0 x).eq_or_lt with hzero | hpos
    · have hhx : h x = 0 := hzero.symm
      have hwx : sqrtAdd v (fun y => Real.sqrt τ * h y) x = v x := by
        show Real.sqrt (v x ^ 2 + (Real.sqrt τ * h x) ^ 2) = v x
        rw [hhx, mul_zero]
        simpa using Real.sqrt_sq (hcomp.nonneg x)
      rw [hhx, hwx]
      simp
    · have hρwpos : 0 < sqrtAdd v (fun y => Real.sqrt τ * h y) x ^ 2 := by
        rw [hwsq x]; positivity
      have hle : Real.log (sqrtAdd v (fun y => Real.sqrt τ * h y) x ^ 2) ≤
          Real.log (v x ^ 2 + τ) := by
        refine Real.log_le_log hρwpos ?_
        rw [hwsq x]
        have hsq1 : h x ^ 2 ≤ 1 := by nlinarith [hh0 x, hh1 x]
        nlinarith [mul_le_mul_of_nonneg_left hsq1 hτ0.le]
      have hconv := mul_log_convexity (sq_nonneg (v x)) hρwpos
      rw [hwsq x] at hconv hρwpos hle
      rw [entropyPotential_two_sq, entropyPotential_two_sq, hwsq x]
      have hT : (0 : ℝ) ≤ τ * h x ^ 2 := by positivity
      have hstep1 : -((Real.log (v x ^ 2 + τ * h x ^ 2) + 1) * (τ * h x ^ 2)) ≤
          v x ^ 2 * Real.log (v x ^ 2) -
            (v x ^ 2 + τ * h x ^ 2) * Real.log (v x ^ 2 + τ * h x ^ 2) := by
        linarith [hconv]
      have hstep2 : -((Real.log (v x ^ 2 + τ) + 1) * (τ * h x ^ 2)) ≤
          -((Real.log (v x ^ 2 + τ * h x ^ 2) + 1) * (τ * h x ^ 2)) := by
        linarith [mul_nonneg (sub_nonneg.2 hle) hT]
      linarith [mul_le_mul_of_nonneg_left (hstep2.trans hstep1)
        (by positivity : (0 : ℝ) ≤ κ / 4)]
  -- integrability of the weighted logarithm
  have hYint : Integrable (fun x => h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) volume :=
    integrable_sq_mul_neg_log hK hcomp hhcomp hh1 hτ0 hτ1
  have hPhiint : Integrable
      (fun x => -(κ / 4) * (Real.log (v x ^ 2 + τ) + 1) * (τ * h x ^ 2)) volume := by
    have heq : ∀ x, -(κ / 4) * (Real.log (v x ^ 2 + τ) + 1) * (τ * h x ^ 2) =
        κ / 4 * τ * (h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) - κ / 4 * τ * h x ^ 2 := by
      intro x; ring
    exact ((hYint.const_mul (κ / 4 * τ)).sub (hhsqint.const_mul (κ / 4 * τ))).congr
      (Eventually.of_forall fun x => (heq x).symm)
  have hPwint : Integrable (fun x => Korevaar.entropyPotential 2 κ
      (sqrtAdd v (fun y => Real.sqrt τ * h y) x)) volume := hwcomp.integrable_entropy hK κ
  have hentrint := integral_mono hPhiint (hPvint.sub hPwint) hentr
  simp only [Pi.sub_apply] at hentrint
  rw [integral_sub hPvint hPwint] at hentrint
  have hPhival : (∫ x, -(κ / 4) * (Real.log (v x ^ 2 + τ) + 1) * (τ * h x ^ 2)) =
      κ / 4 * τ * ((∫ x, h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) - ∫ x, h x ^ 2) := by
    have heq : ∀ x, -(κ / 4) * (Real.log (v x ^ 2 + τ) + 1) * (τ * h x ^ 2) =
        κ / 4 * τ * (h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) - κ / 4 * τ * h x ^ 2 := by
      intro x; ring
    rw [integral_congr_ae (Eventually.of_forall heq),
      integral_sub (hYint.const_mul (κ / 4 * τ)) (hhsqint.const_mul (κ / 4 * τ)),
      integral_const_mul, integral_const_mul]
    ring
  -- minimality
  have hmin := hv.regFree_le hκ hΨ hK hcomp hwcomp
  rw [regFree_eq_regEnergy_sub hK hcomp hΨ, regFree_eq_regEnergy_sub hK hwcomp hΨ] at hmin
  simp only [regEnergy] at hmin
  rw [hnorm] at hmin
  -- assemble
  rw [hPhival] at hentrint
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hchain : κ / 4 * τ * ((∫ x, h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) - ∫ x, h x ^ 2) ≤
      τ * ((∫ x, Korevaar.homogeneousDensity 2 Ψ (h x) (gradient h x)) -
        (regMin 2 κ Ψ K + κ / 4) * ∫ x, h x ^ 2) := by
    linarith [hmin, hkin, hentrint]
  have hdiv : κ / 4 * ((∫ x, h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) - ∫ x, h x ^ 2) ≤
      (∫ x, Korevaar.homogeneousDensity 2 Ψ (h x) (gradient h x)) -
        (regMin 2 κ Ψ K + κ / 4) * ∫ x, h x ^ 2 := by
    by_contra hcon
    rw [not_le] at hcon
    linarith [mul_lt_mul_of_pos_left hcon hτ0, hchain]
  have hmul := mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 4 / κ)
  have hLHS : 4 / κ * (κ / 4 * ((∫ x, h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) - ∫ x, h x ^ 2)) =
      (∫ x, h x ^ 2 * (-(Real.log (v x ^ 2 + τ)))) - ∫ x, h x ^ 2 := by
    field_simp
  linarith [hmul, hLHS.le, hLHS.ge]

end Komlos.Literature.Regularized
