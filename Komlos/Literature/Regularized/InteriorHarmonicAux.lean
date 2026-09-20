import Komlos.Literature.Regularized.DeGiorgiNash
import Komlos.Literature.Regularized.InteriorDefs

/-!
# Auxiliary material for the `Ψ`-harmonic comparison problem (lane `L3b`)

Lane `L3b` (`reg/c2b`) of `REGULARIZED_ROUTE.md`, Revision 2 (v), proves links 2
(`exists_regHarmonic_campanato`) and 6 (`IsWeakLogSol.exists_holder_gradient`) of the interior
regularity chain of `Komlos/Literature/Regularized/InteriorRegularity.lean`.  This file collects
the material that both links need and that is independent of the equations:

* `ball_ae_eq_closedBall` and its consequences for set integrals and set averages — the frozen
  statements are written with open balls, the project's Campanato toolbox
  (`Komlos/Literature/PLaplacian/SchauderAux.lean`) with closed balls, and the two agree because
  spheres are Lebesgue null;
* `contDiffOn_one_continuousOn_gradient` — a `C¹` function on an open set has a continuous
  gradient there;
* `regLinCoeff Ψ H x = D(∇Ψ)(H x)`, the coefficient field of the *linearized* (differentiated)
  equation, and `isUnifElliptic_regLinCoeff`: it is uniformly elliptic and bounded in the sense
  of `Komlos.Literature.Regularized.IsUnifElliptic`, with the ellipticity constants of the
  profile.  This is the input the De Giorgi–Nash lane (`DeGiorgiNash.lean`) consumes in step (3)
  of the chain;
* `excess_decay_of_holder` — the elementary passage from a *scale-invariant* Hölder estimate for
  a continuous vector field on a half ball to the Campanato decay of its `L²` excess with
  exponent `d + 2β`.  This is what turns the De Giorgi–Nash Hölder estimate for `∇h` into the
  decay required by link 2.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {c C : ℝ} {Ψ : Euc d → ℝ}

/-! ### Open balls and closed balls -/

/-- An open ball and the corresponding closed ball agree up to a Lebesgue null set (the sphere
between them). -/
theorem ball_ae_eq_closedBall (x : Euc d) {r : ℝ} (hr : r ≠ 0) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  have hs : volume (Metric.sphere x r) = 0 :=
    Measure.addHaar_sphere_of_ne_zero volume x hr
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · rw [Set.sdiff_eq_empty.2 Metric.ball_subset_closedBall]
    simp
  · refine measure_mono_null (fun y hy => ?_) hs
    have h1 : dist y x ≤ r := Metric.mem_closedBall.1 hy.1
    have h2 : ¬ dist y x < r := fun hlt => hy.2 (Metric.mem_ball.1 hlt)
    exact Metric.mem_sphere.2 (le_antisymm h1 (not_lt.1 h2))

/-- Set integrals over an open ball and over the closed ball agree. -/
theorem setIntegral_ball_eq_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Euc d → E) (x : Euc d) {r : ℝ} (hr : r ≠ 0) :
    ∫ y in Metric.ball x r, f y = ∫ y in Metric.closedBall x r, f y :=
  setIntegral_congr_set (ball_ae_eq_closedBall x hr)

/-- Set averages over an open ball and over the closed ball agree. -/
theorem setAverage_ball_eq_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Euc d → E) (x : Euc d) {r : ℝ} (hr : r ≠ 0) :
    (⨍ y in Metric.ball x r, f y) = ⨍ y in Metric.closedBall x r, f y :=
  setAverage_congr (ball_ae_eq_closedBall x hr)

/-- The `L²` Campanato excess of a field over an open ball equals the one over the closed ball. -/
theorem excess_ball_eq_closedBall (W : Euc d → Euc d) (x : Euc d) {r : ℝ} (hr : r ≠ 0) :
    (∫ y in Metric.ball x r, ‖W y - ⨍ z in Metric.ball x r, W z‖ ^ 2) =
      ∫ y in Metric.closedBall x r, ‖W y - ⨍ z in Metric.closedBall x r, W z‖ ^ 2 := by
  rw [setAverage_ball_eq_closedBall W x hr]
  exact setIntegral_ball_eq_closedBall _ x hr

/-! ### Gradients of `C¹` functions -/

/-- On an open set, the gradient of a `C¹` function is continuous. -/
theorem contDiffOn_one_continuousOn_gradient {Ω : Set (Euc d)} (hΩ : IsOpen Ω) {h : Euc d → ℝ}
    (hh : ContDiffOn ℝ 1 h Ω) : ContinuousOn (gradient h) Ω := by
  have hfd : ContinuousOn (fderiv ℝ h) Ω := hh.continuousOn_fderiv_of_isOpen hΩ le_rfl
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn hfd

/-! ### The linearized coefficient field -/

/-- **The coefficient field of the differentiated equation**: `A(x) = D(∇Ψ)(H x)`, where `H` is
the gradient field of a `Ψ`-harmonic function.  Differentiating `div ∇Ψ(∇h) = 0` in a direction
`e` gives the *linear* divergence-form equation `div (A ∇(∂_e h)) = 0` with these coefficients
(`REGULARIZED_ROUTE.md`, Revision 2 (v); `InteriorRegularity.lean`, step (3)). -/
noncomputable def regLinCoeff (Ψ : Euc d → ℝ) (H : Euc d → Euc d) (x : Euc d) :
    Euc d →L[ℝ] Euc d :=
  fderiv ℝ (gradient Ψ) (H x)

/-- **The linearized coefficients are uniformly elliptic and bounded**, with the ellipticity
constants of the profile: this is the hypothesis `IsUnifElliptic c C Ω (regLinCoeff Ψ H)` that
the De Giorgi–Nash lane consumes.  No regularity of `H` is needed, only measurability of the
resulting field, which is not part of `IsUnifElliptic`. -/
theorem isUnifElliptic_regLinCoeff (h : IsRegProfileWith Ψ c C) (H : Euc d → Euc d)
    (Ω : Set (Euc d)) : IsUnifElliptic c C Ω (regLinCoeff Ψ H) where
  elliptic := Eventually.of_forall fun x _ ξ => h.lower (H x) ξ
  bddCoeff := Eventually.of_forall fun x _ => h.norm_fderiv_gradient_le (H x)



/-- The `L²` excess only depends on the field on the ball. -/
theorem sqExcess_congr_of_eqOn {W W' : Euc d → Euc d} {x₀ : Euc d} {ρ : ℝ}
    (hWW : Set.EqOn W W' (Metric.closedBall x₀ ρ)) :
    Komlos.Literature.sqExcess W x₀ ρ = Komlos.Literature.sqExcess W' x₀ ρ := by
  rw [Komlos.Literature.sqExcess_eq, Komlos.Literature.sqExcess_eq,
    setAverage_congr_fun measurableSet_closedBall
      (Eventually.of_forall fun x hx => hWW hx)]
  exact setIntegral_congr_fun measurableSet_closedBall fun x hx => by rw [hWW hx]

/-! ### `Ψ`-harmonic gradient fields -/

/-- **`H` is a `Ψ`-harmonic gradient field on `U`**: `H` is a weak gradient of `h` on the open set
`U`, square integrable on the closed balls inside `U`, and `div ∇Ψ(H) = 0` weakly.

This is `Komlos.Literature.Regularized.IsRegHarmonic` with the field `continuousOn h` **dropped**
(`IsRegHarmonic.toIsRegHarmonicField`, in `InteriorHarmonic.lean`).  Continuity of the potential
`h` plays no role in the interior regularity theory of link 2 — what that theory produces is a
continuous representative of the *gradient field* — and it is expensive to supply for the
`Ψ`-harmonic replacement of link 6, which is a Sobolev object.  Working with the field is
therefore both weaker as a hypothesis and stronger as a conclusion. -/
structure IsRegHarmonicField (Ψ : Euc d → ℝ) (U : Set (Euc d)) (h : Euc d → ℝ)
    (H : Euc d → Euc d) : Prop where
  /-- `U` is open. -/
  isOpen : IsOpen U
  /-- `h` is globally measurable. -/
  measurable : Measurable h
  /-- `H` is globally measurable. -/
  measurable_grad : Measurable H
  /-- `H` is a weak gradient of `h` on `U`. -/
  hasWeakGradientOn : HasWeakGradientOn U h H
  /-- `H` is square integrable on every closed ball inside `U`. -/
  integrableOn_sq : ∀ (x₀ : Euc d) (r : ℝ), Metric.closedBall x₀ r ⊆ U →
    IntegrableOn (fun x => ‖H x‖ ^ 2) (Metric.closedBall x₀ r) volume
  /-- The homogeneous weak equation. -/
  weakEq : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    (∫ x, ⟪gradient Ψ (H x), gradient ψ x⟫) = 0

/-! ### From a scale-invariant Hölder estimate to the Campanato decay -/

/-- **The Campanato decay of the `L²` excess out of a scale-invariant Hölder estimate.**

If a continuous field `W` on `closedBall x₀ (r/2)` satisfies

`‖W y - W z‖² ≤ Ch (dist y z / r)^{2β} ⨍_{B_{r/2}} ‖W - (W)_{B_{r/2}}‖²`

for all `y, z` in that ball, then its `L²` excess decays at the rate `(2ρ/r)^{d+2β}`:

`∫_{B_ρ} ‖W - (W)_{B_ρ}‖² ≤ Ch (2ρ/r)^{d+2β} ∫_{B_{r/2}} ‖W - (W)_{B_{r/2}}‖²`.

The proof is the classical two-line computation: the mean minimizes the `L²` deviation
(`Komlos.Literature.integral_norm_sub_setAverage_sq_le_const`), so one may compare with the
value `W x₀`; the pointwise bound then gives a factor `|B_ρ| = (2ρ/r)^d |B_{r/2}|`, which turns
the average on the right-hand side into the integral. -/
theorem excess_decay_of_holder {W : Euc d → Euc d} {x₀ : Euc d} {r Ch β : ℝ}
    (hr : 0 < r) (hβ : 0 < β) (hCh : 0 ≤ Ch)
    (hW : ContinuousOn W (Metric.closedBall x₀ (r / 2)))
    (hhol : ∀ y ∈ Metric.closedBall x₀ (r / 2), ∀ z ∈ Metric.closedBall x₀ (r / 2),
      ‖W y - W z‖ ^ 2 ≤ Ch * (dist y z / r) ^ (2 * β) *
        ⨍ w in Metric.closedBall x₀ (r / 2),
          ‖W w - ⨍ z' in Metric.closedBall x₀ (r / 2), W z'‖ ^ 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r / 2) :
    (∫ y in Metric.closedBall x₀ ρ, ‖W y - ⨍ z in Metric.closedBall x₀ ρ, W z‖ ^ 2) ≤
      Ch * (2 * ρ / r) ^ ((d : ℝ) + 2 * β) *
        ∫ y in Metric.closedBall x₀ (r / 2),
          ‖W y - ⨍ z in Metric.closedBall x₀ (r / 2), W z‖ ^ 2 := by
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  set V : ℝ := volume.real (Metric.closedBall (0 : Euc d) 1) with hVdef
  have hV : 0 < V := Komlos.Literature.volume_real_closedBall_pos
  set A : ℝ := ∫ y in Metric.closedBall x₀ (r / 2),
    ‖W y - ⨍ z in Metric.closedBall x₀ (r / 2), W z‖ ^ 2 with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hvol2 : volume.real (Metric.closedBall x₀ (r / 2)) = (r / 2) ^ d * V :=
    Komlos.Literature.volume_real_closedBall x₀ hr2.le
  have hvolρ : volume.real (Metric.closedBall x₀ ρ) = ρ ^ d * V :=
    Komlos.Literature.volume_real_closedBall x₀ hρ.le
  have hd2 : (0 : ℝ) < (r / 2) ^ d * V := by positivity
  -- the average on the right-hand side, written out
  have havg : (⨍ w in Metric.closedBall x₀ (r / 2),
      ‖W w - ⨍ z' in Metric.closedBall x₀ (r / 2), W z'‖ ^ 2) = ((r / 2) ^ d * V)⁻¹ * A := by
    rw [setAverage_eq, hvol2, hAdef, smul_eq_mul]
  -- the constant bounding `‖W y - W x₀‖` on `closedBall x₀ ρ`
  set Ksq : ℝ := Ch * (ρ / r) ^ (2 * β) * (((r / 2) ^ d * V)⁻¹ * A) with hKsqdef
  have hKsq0 : 0 ≤ Ksq := by
    have h1 : (0 : ℝ) ≤ (ρ / r) ^ (2 * β) := Real.rpow_nonneg (by positivity) _
    have h2 : (0 : ℝ) ≤ ((r / 2) ^ d * V)⁻¹ * A := mul_nonneg (by positivity) hA0
    exact mul_nonneg (mul_nonneg hCh h1) h2
  set K : ℝ := Real.sqrt Ksq with hKdef
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hKK : K ^ 2 = Ksq := Real.sq_sqrt hKsq0
  have hsubρ : Metric.closedBall x₀ ρ ⊆ Metric.closedBall x₀ (r / 2) :=
    Metric.closedBall_subset_closedBall hρr
  have hx₀ : x₀ ∈ Metric.closedBall x₀ (r / 2) := Metric.mem_closedBall_self hr2.le
  -- the pointwise bound
  have hbd : ∀ y ∈ Metric.closedBall x₀ ρ, ‖W y - W x₀‖ ≤ K := by
    intro y hy
    have hy2 : y ∈ Metric.closedBall x₀ (r / 2) := hsubρ hy
    have hdist : dist y x₀ / r ≤ ρ / r :=
      div_le_div_of_nonneg_right (Metric.mem_closedBall.1 hy) hr.le
    have hmono : (dist y x₀ / r) ^ (2 * β) ≤ (ρ / r) ^ (2 * β) :=
      Real.rpow_le_rpow (by positivity) hdist (by linarith)
    have hstep : ‖W y - W x₀‖ ^ 2 ≤ Ksq := by
      refine (hhol y hy2 x₀ hx₀).trans ?_
      rw [havg, hKsqdef]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hCh) ?_
      exact mul_nonneg (by positivity) hA0
    calc ‖W y - W x₀‖ = Real.sqrt (‖W y - W x₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt Ksq := Real.sqrt_le_sqrt hstep
  -- integrate
  have h1 : (∫ y in Metric.closedBall x₀ ρ, ‖W y - ⨍ z in Metric.closedBall x₀ ρ, W z‖ ^ 2) ≤
      ∫ y in Metric.closedBall x₀ ρ, ‖W y - W x₀‖ ^ 2 :=
    Komlos.Literature.integral_norm_sub_setAverage_sq_le_const hρ (hW.mono hsubρ) (W x₀)
  have h2 : (∫ y in Metric.closedBall x₀ ρ, ‖W y - W x₀‖ ^ 2) ≤
      K ^ 2 * volume.real (Metric.closedBall x₀ ρ) :=
    Komlos.Literature.setIntegral_norm_sub_sq_le (hW.mono hsubρ) hbd
  refine (h1.trans h2).trans ?_
  -- arithmetic
  rw [hKK, hKsqdef, hvolρ]
  have hpos : (0 : ℝ) < 2 * ρ / r := by positivity
  have hdpow : ρ ^ d * V / ((r / 2) ^ d * V) = (2 * ρ / r) ^ ((d : ℝ)) := by
    have hVne : V ≠ 0 := hV.ne'
    have hrdne : ((r / 2) ^ d : ℝ) ≠ 0 := by positivity
    have h2r : (2 : ℝ) * ρ / r = ρ / (r / 2) := by rw [div_div_eq_mul_div]; ring
    have hcancel : ρ ^ d * V / ((r / 2) ^ d * V) = ρ ^ d / (r / 2) ^ d := by
      rw [div_eq_div_iff (by positivity : (0 : ℝ) < (r / 2) ^ d * V).ne' hrdne]
      ring
    rw [Real.rpow_natCast, hcancel, h2r]
    exact (div_pow ρ (r / 2) d).symm
  have hsplit : (2 * ρ / r) ^ ((d : ℝ) + 2 * β) = (2 * ρ / r) ^ ((d : ℝ)) * (2 * ρ / r) ^ (2 * β) :=
    Real.rpow_add hpos _ _
  have hmono2 : (ρ / r) ^ (2 * β) ≤ (2 * ρ / r) ^ (2 * β) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    rw [div_le_div_iff_of_pos_right hr]
    linarith
  have hchain : Ch * (ρ / r) ^ (2 * β) * (((r / 2) ^ d * V)⁻¹ * A) * (ρ ^ d * V) =
      Ch * (ρ / r) ^ (2 * β) * (ρ ^ d * V / ((r / 2) ^ d * V)) * A := by
    field_simp
    try ring
  rw [hchain, hdpow, hsplit]
  have hP : (0 : ℝ) ≤ Ch * (2 * ρ / r) ^ ((d : ℝ)) * A :=
    mul_nonneg (mul_nonneg hCh (Real.rpow_nonneg hpos.le _)) hA0
  have e1 : Ch * (ρ / r) ^ (2 * β) * (2 * ρ / r) ^ ((d : ℝ)) * A =
      Ch * (2 * ρ / r) ^ ((d : ℝ)) * A * (ρ / r) ^ (2 * β) := by ring
  have e2 : Ch * ((2 * ρ / r) ^ ((d : ℝ)) * (2 * ρ / r) ^ (2 * β)) * A =
      Ch * (2 * ρ / r) ^ ((d : ℝ)) * A * (2 * ρ / r) ^ (2 * β) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hmono2 hP

end Komlos.Literature.Regularized
