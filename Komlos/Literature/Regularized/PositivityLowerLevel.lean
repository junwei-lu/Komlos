import Komlos.Literature.Regularized.PositivityLowerVar

/-!
# Lane `L2p` (`reg/pos-lower`), step 4b: the *level-dependent* De Giorgi inequality

`isDG_of_regMinimizer` (lane `L2`) puts the minimizer in a De Giorgi class whose lower-order
constant `χ` is **fixed**.  That is not enough for positivity — the function `v(x) = |x₁|` lies
in such a class and vanishes on a hyperplane.  What is true, and what the logarithmic
Caccioppoli estimate of `PositivityLowerVar.lean` needs in order to control its one bad term, is
the *super side* with the level-dependence of the lower-order term kept:

`∫_{B_r ∩ {v<l}} ‖∇v‖² ≤ γ (s−r)^{-2} ∫_{B_s} (l−v)₊² + γ l²(log(1/l)+1) |B_s ∩ {v<l}|`
for `0 < l ≤ 1`.

The point is that on `S = B_t ∩ {v < l}` *both* the minimizer and the competitor
`v + ζ(l−v)₊` take values in `[0, l]`, so the lower-order density `regLow` is bounded there by
`O(l²(log(1/l)+1))` rather than by `O(M²)`.  Everything else — the Caccioppoli comparison, the
Young inequality of one scale and the hole-filling iteration — is unchanged, so this file is a
level-aware copy of `exists_caccioppoli_core` (`PositivityCacc.lean`),
`caccioppoli_one_scale_super` and `exists_energy_ineq_super` (`PositivityEnergy.lean`); those
files belong to lane `L2` and may not be edited from here.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### The lower-order density at a small level -/

/-- `|t² log t| ≤ 1` on `[0,1]`. -/
theorem abs_sq_mul_log_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |t ^ 2 * Real.log t| ≤ 1 := by
  have h := pos_abs_sq_mul_log_le ht0 ht1 (le_refl (1 : ℝ))
  simpa using h

/-- `|s² log s| ≤ l² (log(1/l) + 1)` for `0 ≤ s ≤ l ≤ 1`. -/
theorem abs_sq_mul_log_le_level {l s : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hs0 : 0 ≤ s)
    (hsl : s ≤ l) : |s ^ 2 * Real.log s| ≤ l ^ 2 * (Real.log (1 / l) + 1) := by
  have hlogl : Real.log (1 / l) = -Real.log l := by
    rw [one_div, Real.log_inv]
  have hlognn : 0 ≤ Real.log (1 / l) := by
    rw [hlogl]
    simpa using Real.log_nonpos hl0.le hl1
  rcases hs0.eq_or_lt with hs | hs
  · rw [← hs]
    simp
    nlinarith [hlognn, sq_nonneg l]
  · have hsplit : s ^ 2 * Real.log s
        = l ^ 2 * ((s / l) ^ 2 * Real.log (s / l)) + s ^ 2 * Real.log l := by
      rw [Real.log_div hs.ne' hl0.ne']
      field_simp
      ring
    have h1 : |(s / l) ^ 2 * Real.log (s / l)| ≤ 1 :=
      abs_sq_mul_log_le_one (by positivity) ((div_le_one hl0).2 hsl)
    have h2 : |s ^ 2 * Real.log l| ≤ l ^ 2 * Real.log (1 / l) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg s), hlogl, abs_of_nonpos
        (Real.log_nonpos hl0.le hl1)]
      have hs2 : s ^ 2 ≤ l ^ 2 := by nlinarith
      nlinarith [hlognn]
    calc |s ^ 2 * Real.log s|
        ≤ |l ^ 2 * ((s / l) ^ 2 * Real.log (s / l))| + |s ^ 2 * Real.log l| := by
          rw [hsplit]; exact abs_add_le _ _
      _ ≤ l ^ 2 * 1 + l ^ 2 * Real.log (1 / l) := by
          refine add_le_add ?_ h2
          rw [abs_mul, abs_of_nonneg (sq_nonneg l)]
          exact mul_le_mul_of_nonneg_left h1 (sq_nonneg l)
      _ = l ^ 2 * (Real.log (1 / l) + 1) := by ring

/-- **The lower-order density at a small level**: for `0 ≤ s ≤ l ≤ 1`,
`|regLow κ Λ Ψ s| ≤ (|Ψ 0| + |Λ| + |κ|/2) · l² (log(1/l) + 1)`. -/
theorem abs_regLow_le_level {Λ : ℝ} {l s : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hs0 : 0 ≤ s)
    (hsl : s ≤ l) :
    |regLow κ Λ Ψ s| ≤ (|Ψ 0| + |Λ| + |κ| / 2) * (l ^ 2 * (Real.log (1 / l) + 1)) := by
  have hlognn : 0 ≤ Real.log (1 / l) := by
    rw [one_div, Real.log_inv]
    simpa using Real.log_nonpos hl0.le hl1
  have hs2 : s ^ 2 ≤ l ^ 2 := by nlinarith
  have hbase : (1 : ℝ) ≤ Real.log (1 / l) + 1 := by linarith
  have hkey : s ^ 2 ≤ l ^ 2 * (Real.log (1 / l) + 1) := by
    nlinarith [mul_nonneg (sq_nonneg l) hlognn]
  have h1 : |Ψ 0 * s ^ 2| ≤ |Ψ 0| * (l ^ 2 * (Real.log (1 / l) + 1)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    exact mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
  have h2 : |Λ * s ^ 2| ≤ |Λ| * (l ^ 2 * (Real.log (1 / l) + 1)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    exact mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
  have h3 : |Korevaar.entropyPotential 2 κ s| ≤
      |κ| / 2 * (l ^ 2 * (Real.log (1 / l) + 1)) := by
    rw [pos_entropyPotential_two, abs_mul, abs_div]
    have habs2 : |(2 : ℝ)| = 2 := by norm_num
    rw [habs2]
    exact mul_le_mul_of_nonneg_left (abs_sq_mul_log_le_level hl0 hl1 hs0 hsl) (by positivity)
  rw [regLow]
  calc |Ψ 0 * s ^ 2 + Korevaar.entropyPotential 2 κ s - Λ * s ^ 2|
      ≤ |Ψ 0 * s ^ 2 + Korevaar.entropyPotential 2 κ s| + |Λ * s ^ 2| := abs_sub _ _
    _ ≤ (|Ψ 0 * s ^ 2| + |Korevaar.entropyPotential 2 κ s|) + |Λ * s ^ 2| :=
        add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by linarith

/-! ### The Caccioppoli comparison at a level -/

set_option maxHeartbeats 1000000 in
/-- **The Caccioppoli comparison, level-aware form.**  Identical to
`exists_caccioppoli_core` (`PositivityCacc.lean`) except that the bound on the lower-order
density is taken over the *values attained on `S`* rather than over the global range of the
minimizer: if `u ≤ l` and `w ≤ l` on `S` with `0 < l ≤ 1`, the additive error is
`B₁ l² (log(1/l) + 1) |S|`. -/
theorem exists_caccioppoli_core_level (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) (hucomp : IsRegComp K u) :
    ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∀ l : ℝ, 0 < l → l ≤ 1 → ∀ w : Euc d → ℝ, IsRegComp K w →
      ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
      (∀ x ∈ S, u x ≤ l) → (∀ x ∈ S, w x ≤ l) →
      (∀ᵐ x, x ∉ S → u x = w x) → (∀ᵐ x, x ∉ S → weakGrad u x = weakGrad w x) →
      c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
        C / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) +
          B₁ * (l ^ 2 * (Real.log (1 / l) + 1)) * (volume S).toReal := by
  classical
  set Λ : ℝ := regMin 2 κ Ψ K + κ / 4 with hΛ
  refine ⟨2 * (|Ψ 0| + |Λ| + |κ| / 2), by positivity, ?_⟩
  intro l hl0 hl1 w hw S hS hSfin huS hwS hoffv hoffg
  have hlognn : (0 : ℝ) ≤ Real.log (1 / l) := by
    rw [one_div, Real.log_inv]
    simpa using Real.log_nonpos hl0.le hl1
  have hLfac : (0 : ℝ) ≤ l ^ 2 * (Real.log (1 / l) + 1) := by
    nlinarith [sq_nonneg l, hlognn]
  set B₀ : ℝ := (|Ψ 0| + |Λ| + |κ| / 2) * (l ^ 2 * (Real.log (1 / l) + 1)) with hB₀
  have hB₀0 : 0 ≤ B₀ := by
    rw [hB₀]
    have : (0 : ℝ) ≤ |Ψ 0| + |Λ| + |κ| / 2 := by positivity
    exact mul_nonneg this hLfac
  -- the two local energy densities
  set Fu : Euc d → ℝ := fun x => Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x) +
    Korevaar.entropyPotential 2 κ (u x) - Λ * u x ^ 2 with hFu
  set Fw : Euc d → ℝ := fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) +
    Korevaar.entropyPotential 2 κ (w x) - Λ * w x ^ 2 with hFw
  have hFuInt : Integrable Fu volume :=
    ((hucomp.integrable_density hΨ).add (hucomp.integrable_entropy hK κ)).sub
      (hucomp.integrable_sq.const_mul Λ)
  have hFwInt : Integrable Fw volume :=
    ((hw.integrable_density hΨ).add (hw.integrable_entropy hK κ)).sub
      (hw.integrable_sq.const_mul Λ)
  have hle : (∫ x, Fu x) ≤ ∫ x, Fw x := hu.regFree_le hκ hΨ hK hucomp hw
  have hoffF : ∀ᵐ x, x ∉ S → Fu x = Fw x := by
    filter_upwards [hoffv, hoffg] with x h1 h2 hx
    rw [hFu, hFw]
    simp only []
    rw [h1 hx, h2 hx]
  have hlocal : (∫ x in S, Fu x) ≤ ∫ x in S, Fw x :=
    setIntegral_le_of_integral_le_of_eq_off hS hFuInt hFwInt hle hoffF
  have hLu : Integrable (fun x => regLow κ Λ Ψ (u x)) volume :=
    ((hucomp.integrable_sq.const_mul (Ψ 0)).add (hucomp.integrable_entropy hK κ)).sub
      (hucomp.integrable_sq.const_mul Λ)
  have hLw : Integrable (fun x => regLow κ Λ Ψ (w x)) volume :=
    ((hw.integrable_sq.const_mul (Ψ 0)).add (hw.integrable_entropy hK κ)).sub
      (hw.integrable_sq.const_mul Λ)
  have hcstInt : IntegrableOn (fun _ : Euc d => B₀) S volume := integrableOn_const hSfin
  have hcstInt' : IntegrableOn (fun _ : Euc d => -B₀) S volume := integrableOn_const hSfin
  have hDu : IntegrableOn (fun x => ‖weakGrad u x‖ ^ 2) S volume :=
    hucomp.integrable_normSq_grad.integrableOn
  have hDw : IntegrableOn (fun x => ‖weakGrad w x‖ ^ 2) S volume :=
    hw.integrable_normSq_grad.integrableOn
  have hlow : c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) + (∫ x in S, regLow κ Λ Ψ (u x)) ≤
      ∫ x in S, Fu x := by
    have hptw : ∀ᵐ x ∂(volume.restrict S),
        c / 2 * ‖weakGrad u x‖ ^ 2 + regLow κ Λ Ψ (u x) ≤ Fu x := by
      refine ae_restrict_of_ae ?_
      filter_upwards [hucomp.weakGrad_eq_zero] with x hx
      have h := hΨ.le_homogeneousDensity (hucomp.nonneg x) hx
      rw [hFu, regLow]
      simp only []
      linarith
    have hIl : IntegrableOn (fun x => c / 2 * ‖weakGrad u x‖ ^ 2 + regLow κ Λ Ψ (u x))
        S volume := (hDu.const_mul _).add hLu.integrableOn
    have := integral_mono_ae hIl hFuInt.integrableOn hptw
    rwa [integral_add (hDu.const_mul _) hLu.integrableOn, integral_const_mul] at this
  have hup : (∫ x in S, Fw x) ≤
      C / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + ∫ x in S, regLow κ Λ Ψ (w x) := by
    have hptw : ∀ᵐ x ∂(volume.restrict S),
        Fw x ≤ C / 2 * ‖weakGrad w x‖ ^ 2 + regLow κ Λ Ψ (w x) := by
      refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
      have h := hΨ.homogeneousDensity_le (hw.nonneg x) (weakGrad w x)
      rw [hFw, regLow]
      simp only []
      linarith
    have hIu : IntegrableOn (fun x => C / 2 * ‖weakGrad w x‖ ^ 2 + regLow κ Λ Ψ (w x))
        S volume := (hDw.const_mul _).add hLw.integrableOn
    have := integral_mono_ae hFwInt.integrableOn hIu hptw
    rwa [integral_add (hDw.const_mul _) hLw.integrableOn, integral_const_mul] at this
  have hLuS : -(B₀ * (volume S).toReal) ≤ ∫ x in S, regLow κ Λ Ψ (u x) := by
    have hptw : ∀ᵐ x ∂(volume.restrict S), -B₀ ≤ regLow κ Λ Ψ (u x) := by
      rw [ae_restrict_iff' hS]
      refine Eventually.of_forall fun x hx => ?_
      have := abs_regLow_le_level (Λ := Λ) (Ψ := Ψ) (κ := κ) hl0 hl1 (hucomp.nonneg x)
        (huS x hx)
      have hle2 : |regLow κ Λ Ψ (u x)| ≤ B₀ := by rw [hB₀]; exact this
      exact neg_le_of_abs_le hle2
    have := integral_mono_ae hcstInt' hLu.integrableOn hptw
    rw [setIntegral_const] at this
    simpa [measureReal_def, neg_mul, mul_comm] using this
  have hLwS : (∫ x in S, regLow κ Λ Ψ (w x)) ≤ B₀ * (volume S).toReal := by
    have hptw : ∀ᵐ x ∂(volume.restrict S), regLow κ Λ Ψ (w x) ≤ B₀ := by
      rw [ae_restrict_iff' hS]
      refine Eventually.of_forall fun x hx => ?_
      have := abs_regLow_le_level (Λ := Λ) (Ψ := Ψ) (κ := κ) hl0 hl1 (hw.nonneg x) (hwS x hx)
      have hle2 : |regLow κ Λ Ψ (w x)| ≤ B₀ := by rw [hB₀]; exact this
      exact le_of_abs_le hle2
    have := integral_mono_ae hLw.integrableOn hcstInt hptw
    rw [setIntegral_const] at this
    simpa [measureReal_def, mul_comm] using this
  have hfinal : 2 * (|Ψ 0| + |Λ| + |κ| / 2) * (l ^ 2 * (Real.log (1 / l) + 1)) *
      (volume S).toReal = 2 * B₀ * (volume S).toReal := by
    rw [hB₀]; ring
  rw [hfinal]
  linarith [hlocal, hlow, hup, hLuS, hLwS]

/-! ### One scale of the level-dependent Caccioppoli inequality -/

set_option maxHeartbeats 1000000 in
/-- **One scale of the Caccioppoli inequality, super side, level-aware.**  A copy of
`caccioppoli_one_scale_super` (`PositivityEnergy.lean`) in which the global bound `Mbig` is
replaced by the level `l`: on `S = closedBall x₁ t ∩ {u < l}` the minimizer satisfies `u ≤ l`,
and the competitor `u + ζ(l−u)₊` satisfies `w ≤ l` as well. -/
theorem caccioppoli_one_scale_super_level (hΨ : IsRegProfileWith Ψ c C)
    (hcomp : IsRegComp K u) (hum : Measurable u) {B₁ : ℝ} (_hB₁0 : 0 ≤ B₁)
    {l : ℝ} (hl : 0 ≤ l)
    (hcore : ∀ w : Euc d → ℝ, IsRegComp K w →
      ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
      (∀ x ∈ S, u x ≤ l) → (∀ x ∈ S, w x ≤ l) → (∀ x ∈ S, u x ≤ w x) →
      (∀ᵐ x, x ∉ S → u x = w x) → (∀ᵐ x, x ∉ S → weakGrad u x = weakGrad w x) →
      c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
        (C + c) / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + B₁ * (volume S).toReal)
    {ζ : Euc d → ℝ} (hζsm : ContDiff ℝ ∞ ζ) (hζcs : HasCompactSupport ζ)
    (hζK : tsupport ζ ⊆ K) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1)
    {Vb : ℝ} (hζgrad : ∀ x, ‖gradient ζ x‖ ≤ Vb)
    {x₁ : Euc d} {t : ℝ} (hζts : tsupport ζ ⊆ Metric.closedBall x₁ t) :
    (∫ x in Metric.closedBall x₁ t ∩ {x | u x < l}, ζ x * ‖weakGrad u x‖ ^ 2) ≤
      (1 - c / (2 * (C + c))) *
          (∫ x in Metric.closedBall x₁ t ∩ {x | u x < l}, ‖weakGrad u x‖ ^ 2) +
        Vb ^ 2 * (∫ x in Metric.closedBall x₁ t ∩ {x | u x < l}, negTrunc l u x ^ 2) +
        (B₁ / (C + c)) *
          (volume (Metric.closedBall x₁ t ∩ {x | u x < l})).toReal := by
  classical
  set C' : ℝ := C + c with hC'def
  have hC'pos : 0 < C' := by rw [hC'def]; linarith [hΨ.C_nonneg, hΨ.c_pos]
  set A : Set (Euc d) := {x | u x < l} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_lt hum measurable_const
  obtain ⟨hwcomp, hwg⟩ := hcomp.truncCompetitorSuper hl hζsm hζcs hζK hζ0 hζ1
  set w : Euc d → ℝ := fun x => u x + ζ x * negTrunc l u x with hwdef
  set S : Set (Euc d) := Metric.closedBall x₁ t ∩ A with hSdef
  have hSmeas : MeasurableSet S := measurableSet_closedBall.inter hAmeas
  have hSfin : volume S ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt
      (measure_closedBall_lt_top (x := x₁) (r := t))).ne
  have hζoff : ∀ x, x ∉ Metric.closedBall x₁ t → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hζts h)
  have hgζoff : ∀ x, x ∉ Metric.closedBall x₁ t → gradient ζ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport fun h => hx (hζts h)
  have hTzero : ∀ x, x ∉ A → negTrunc l u x = 0 := fun x hx => by
    rw [negTrunc, max_eq_right]
    simp only [hAdef, Set.mem_ofPred_eq, not_lt] at hx
    linarith
  have hIndzero : ∀ x, x ∉ A → levelIndLt l u x = 0 := fun x hx => by
    simp only [hAdef, Set.mem_ofPred_eq, not_lt] at hx
    rw [levelIndLt, if_neg (by linarith)]
  have hoffv : ∀ᵐ x : Euc d, x ∉ S → u x = w x := by
    refine Eventually.of_forall fun x hx => ?_
    rw [hwdef]
    simp only []
    rcases Classical.em (x ∈ A) with hxA | hxA
    · have hxb : x ∉ Metric.closedBall x₁ t := fun h => hx ⟨h, hxA⟩
      rw [hζoff x hxb]; ring
    · rw [hTzero x hxA]; ring
  have hoffg : ∀ᵐ x : Euc d, x ∉ S → weakGrad u x = weakGrad w x := by
    filter_upwards [hwg] with x hx hxS
    rw [hx]
    rcases Classical.em (x ∈ A) with hxA | hxA
    · have hxb : x ∉ Metric.closedBall x₁ t := fun h => hxS ⟨h, hxA⟩
      rw [hζoff x hxb, hgζoff x hxb]
      simp
    · rw [hTzero x hxA, hIndzero x hxA]
      simp
  have huS : ∀ x ∈ S, u x ≤ l := by
    intro x hx
    have := hx.2
    simp only [hAdef, Set.mem_ofPred_eq] at this
    linarith
  have hwS : ∀ x ∈ S, w x ≤ l := by
    intro x hx
    have hlt := hx.2
    simp only [hAdef, Set.mem_ofPred_eq] at hlt
    have hneg : negTrunc l u x = l - u x := by
      rw [negTrunc, max_eq_left (by linarith)]
    rw [hwdef]
    simp only [hneg]
    nlinarith [hζ0 x, hζ1 x]
  have huwS : ∀ x ∈ S, u x ≤ w x := fun x _ => by
    rw [hwdef]
    exact le_add_of_nonneg_right (mul_nonneg (hζ0 x) (negTrunc_nonneg l u x))
  have hcc := hcore w hwcomp S hSmeas hSfin huS hwS huwS hoffv hoffg
  -- the pointwise gradient bound on `S`
  have hgw : ∀ᵐ x ∂(volume.restrict S), ‖weakGrad w x‖ ^ 2 ≤
      2 * ((1 - ζ x) * ‖weakGrad u x‖ ^ 2) + (2 * Vb ^ 2) * negTrunc l u x ^ 2 := by
    rw [ae_restrict_iff' hSmeas]
    filter_upwards [hwg] with x hx hxS
    have hxA : x ∈ A := hxS.2
    have hind : levelIndLt l u x = 1 := by
      simp only [hAdef, Set.mem_ofPred_eq] at hxA
      rw [levelIndLt, if_pos hxA]
    rw [hx, hind, mul_one]
    have hsplit : weakGrad u x - ζ x • weakGrad u x + negTrunc l u x • gradient ζ x =
        (1 - ζ x) • weakGrad u x - (-(negTrunc l u x • gradient ζ x)) := by
      rw [sub_smul, one_smul]
      abel
    rw [hsplit]
    have h1 := norm_sub_sq_le_two_add ((1 - ζ x) • weakGrad u x)
      (-(negTrunc l u x • gradient ζ x))
    have h2 : ‖(1 - ζ x) • weakGrad u x‖ ^ 2 ≤ (1 - ζ x) * ‖weakGrad u x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hζ1 x]), mul_pow]
      have hp : 0 ≤ ζ x * ((1 - ζ x) * ‖weakGrad u x‖ ^ 2) :=
        mul_nonneg (hζ0 x) (mul_nonneg (by linarith [hζ1 x]) (sq_nonneg _))
      nlinarith [hp]
    have h3 : ‖-(negTrunc l u x • gradient ζ x)‖ ^ 2 ≤ Vb ^ 2 * negTrunc l u x ^ 2 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (negTrunc_nonneg l u x), mul_pow]
      have hsq : ‖gradient ζ x‖ ^ 2 ≤ Vb ^ 2 := by
        nlinarith [hζgrad x, norm_nonneg (gradient ζ x)]
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (negTrunc l u x))]
    linarith
  have hIu : IntegrableOn (fun x => ‖weakGrad u x‖ ^ 2) S volume :=
    hcomp.integrable_normSq_grad.integrableOn
  have hIw : IntegrableOn (fun x => ‖weakGrad w x‖ ^ 2) S volume :=
    hwcomp.integrable_normSq_grad.integrableOn
  have hIT : IntegrableOn (fun x => negTrunc l u x ^ 2) S volume := by
    refine Integrable.mono' (integrableOn_const (μ := volume) (C := l ^ 2) hSfin)
      ((hcomp.aesm_negTrunc l).pow 2).restrict ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq_of_nonneg (negTrunc_nonneg l u x) (hcomp.negTrunc_le hl x)
  have hIζ : IntegrableOn (fun x => ζ x * ‖weakGrad u x‖ ^ 2) S volume := by
    refine Integrable.mono' hIu
      ((hζsm.continuous.aestronglyMeasurable.mul
        (hcomp.aestronglyMeasurable_grad.norm.pow 2)).restrict) ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hζ0 x), abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg ‖weakGrad u x‖, hζ0 x, hζ1 x]
  have hI1ζ : IntegrableOn (fun x => (1 - ζ x) * ‖weakGrad u x‖ ^ 2) S volume := by
    have he : (fun x => (1 - ζ x) * ‖weakGrad u x‖ ^ 2) =
        fun x => ‖weakGrad u x‖ ^ 2 - ζ x * ‖weakGrad u x‖ ^ 2 := by
      funext x; ring
    rw [he]
    exact hIu.sub hIζ
  have hbound : (∫ x in S, ‖weakGrad w x‖ ^ 2) ≤
      2 * ((∫ x in S, ‖weakGrad u x‖ ^ 2) - ∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2) +
        (2 * Vb ^ 2) * ∫ x in S, negTrunc l u x ^ 2 := by
    have hsum : IntegrableOn
        (fun x => 2 * ((1 - ζ x) * ‖weakGrad u x‖ ^ 2) + (2 * Vb ^ 2) * negTrunc l u x ^ 2)
        S volume := (hI1ζ.const_mul 2).add (hIT.const_mul (2 * Vb ^ 2))
    have hmono := integral_mono_ae hIw hsum hgw
    refine hmono.trans (le_of_eq ?_)
    rw [integral_add (hI1ζ.const_mul 2) (hIT.const_mul (2 * Vb ^ 2)),
      integral_const_mul, integral_const_mul]
    have hsplit : (∫ x in S, (1 - ζ x) * ‖weakGrad u x‖ ^ 2) =
        (∫ x in S, ‖weakGrad u x‖ ^ 2) - ∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2 := by
      rw [← integral_sub hIu hIζ]
      refine setIntegral_congr_fun hSmeas fun x _ => ?_
      ring
    rw [hsplit]
  have hhalf : (0 : ℝ) ≤ C' / 2 := by linarith
  have h1 := mul_le_mul_of_nonneg_left hbound hhalf
  have hexp : C' / 2 * (2 * ((∫ x in S, ‖weakGrad u x‖ ^ 2) -
        ∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2) + (2 * Vb ^ 2) * ∫ x in S, negTrunc l u x ^ 2) =
      C' * (∫ x in S, ‖weakGrad u x‖ ^ 2) - C' * (∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2) +
        C' * (Vb ^ 2 * ∫ x in S, negTrunc l u x ^ 2) := by ring
  rw [hexp] at h1
  have hkey : C' * (∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2) ≤
      (C' - c / 2) * (∫ x in S, ‖weakGrad u x‖ ^ 2) +
        C' * (Vb ^ 2 * ∫ x in S, negTrunc l u x ^ 2) + B₁ * (volume S).toReal := by
    linarith [hcc, h1]
  have hmul : C' * ((1 - c / (2 * C')) * (∫ x in S, ‖weakGrad u x‖ ^ 2) +
        Vb ^ 2 * (∫ x in S, negTrunc l u x ^ 2) + (B₁ / C') * (volume S).toReal) =
      (C' - c / 2) * (∫ x in S, ‖weakGrad u x‖ ^ 2) +
        C' * (Vb ^ 2 * ∫ x in S, negTrunc l u x ^ 2) + B₁ * (volume S).toReal := by
    field_simp
    try ring
  rw [← hmul] at hkey
  exact le_of_mul_le_mul_left hkey hC'pos

/-! ### The assembled level-dependent energy inequality -/

set_option maxHeartbeats 1000000 in
/-- **The level-dependent De Giorgi (super-side) inequality for the regularized minimizer.**
For every ball `closedBall x₁ s ⊆ K`, every `0 < r < s` and every level `l ∈ (0, 1]`,

`∫_{B_r ∩ {u<l}} ‖∇u‖² ≤ γ(s−r)^{-2} ∫_{B_s}(l−u)₊² + γ l²(log(1/l)+1) |B_s ∩ {u<l}|`.

This is `exists_energy_ineq_super` (`PositivityEnergy.lean`) with the level-dependence of the
lower-order term kept.  It is the missing input of the logarithmic Caccioppoli estimate: the
factor `l²` in the measure term is what makes `a^{-2}∫_{B ∩ {v<a e^{C/c}}}‖∇v‖²` bounded as the
truncation level `a` of the profile tends to `0`, and no fixed-`χ` De Giorgi class can supply
it. -/
theorem exists_energy_ineq_super_level (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) (hcomp : IsRegComp K u)
    (hum : Measurable u) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ (x₁ : Euc d) (r s l : ℝ), 0 < r → r < s → 0 < l → l ≤ 1 →
      Metric.closedBall x₁ s ⊆ K →
      (∫ x in Metric.ball x₁ r ∩ {x | u x < l}, ‖weakGrad u x‖ ^ 2) ≤
        γ / (s - r) ^ 2 * (∫ x in Metric.ball x₁ s, negTrunc l u x ^ 2) +
          γ * (l ^ 2 * (Real.log (1 / l) + 1)) *
            (volume (Metric.ball x₁ s ∩ {x | u x < l})).toReal := by
  classical
  obtain ⟨B₁, hB₁0, hcore0⟩ := exists_caccioppoli_core_level hκ hΨ.add_c hK hu hcomp
  obtain ⟨c₀, hc₀pos, hcut⟩ := exists_cutoff_const d
  have hC'pos : (0 : ℝ) < C + c := by linarith [hΨ.C_nonneg, hΨ.c_pos]
  have hθ0 : (0 : ℝ) ≤ 1 - c / (2 * (C + c)) := by
    have h : c / (2 * (C + c)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith [hΨ.C_nonneg, hΨ.c_pos]
    linarith
  have hθ1 : (1 : ℝ) - c / (2 * (C + c)) < 1 := by
    have h : 0 < c / (2 * (C + c)) := div_pos hΨ.c_pos (by linarith)
    linarith
  obtain ⟨cc, hcc0, hhf⟩ := exists_holefilling_const hθ0 hθ1
  have hγ0 : (0 : ℝ) ≤ 4 * cc * c₀ ^ 2 := mul_nonneg (by linarith) (sq_nonneg c₀)
  refine ⟨max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))), le_max_of_le_left hγ0, ?_⟩
  intro x₁ r s l hr hrs hl0 hl1 hKball
  have hl : (0 : ℝ) ≤ l := hl0.le
  have hlognn : (0 : ℝ) ≤ Real.log (1 / l) := by
    rw [one_div, Real.log_inv]
    simpa using Real.log_nonpos hl0.le hl1
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = l ^ 2 * (Real.log (1 / l) + 1) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; nlinarith [sq_nonneg l, hlognn]
  have hcore : ∀ w : Euc d → ℝ, IsRegComp K w →
      ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
      (∀ x ∈ S, u x ≤ l) → (∀ x ∈ S, w x ≤ l) → (∀ x ∈ S, u x ≤ w x) →
      (∀ᵐ x, x ∉ S → u x = w x) → (∀ᵐ x, x ∉ S → weakGrad u x = weakGrad w x) →
      c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
        (C + c) / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + (B₁ * L) * (volume S).toReal := by
    intro w hw S hS hSfin huS hwS _huwS h1 h2
    have := hcore0 l hl0 hl1 w hw S hS hSfin huS hwS h1 h2
    rw [hLdef]
    linarith [this]
  have hAmeas : MeasurableSet {x : Euc d | u x < l} := measurableSet_lt hum measurable_const
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ x in Metric.ball x₁ s, negTrunc l u x ^ 2 := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ,
      m = (volume (Metric.ball x₁ s ∩ {x : Euc d | u x < l})).toReal := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hIdef]; exact integral_nonneg fun x => sq_nonneg _
  have hm0 : 0 ≤ m := by rw [hmdef]; exact ENNReal.toReal_nonneg
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun tt =>
      ∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l}, ‖weakGrad u x‖ ^ 2 := ⟨_, rfl⟩
  have hf0 : ∀ tt, 0 ≤ f tt := fun tt => by
    rw [hfdef]; exact integral_nonneg fun x => sq_nonneg _
  have hfM : ∀ tt, f tt ≤ ∫ x, ‖weakGrad u x‖ ^ 2 := fun tt => by
    rw [hfdef]
    exact setIntegral_le_integral hcomp.integrable_normSq_grad
      (Eventually.of_forall fun x => sq_nonneg _)
  obtain ⟨s', hs'def⟩ : ∃ s' : ℝ, s' = (r + s) / 2 := ⟨_, rfl⟩
  have hrs' : r < s' := by rw [hs'def]; linarith
  have hs's : s' < s := by rw [hs'def]; linarith
  have hITint : Integrable (fun x => negTrunc l u x ^ 2)
      (volume.restrict (Metric.ball x₁ s)) := by
    refine Integrable.mono'
      (integrableOn_const (μ := volume) (C := l ^ 2)
        (measure_ball_lt_top (x := x₁) (r := s)).ne)
      ((hcomp.aesm_negTrunc l).pow 2).restrict ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq_of_nonneg (negTrunc_nonneg l u x) (hcomp.negTrunc_le hl x)
  have hstep : ∀ ρ tt : ℝ, r ≤ ρ → ρ < tt → tt ≤ s' →
      f ρ ≤ (1 - c / (2 * (C + c))) * f tt + (c₀ ^ 2 * I) / (tt - ρ) ^ 2 +
        ((B₁ * L) / (C + c)) * m := by
    intro ρ tt hrρ hρt htts
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr hrρ
    have hgap : (0 : ℝ) < tt - ρ := by linarith
    have hcgap : (0 : ℝ) < (tt - ρ) ^ 2 := by positivity
    obtain ⟨ζ, hζsm, hζcs, hζts, hζ0, hζ1, hζone, hζgrad⟩ := hcut x₁ ρ tt hρ0 hρt
    have hζK : tsupport ζ ⊆ K :=
      hζts.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hKball)
    have hone := caccioppoli_one_scale_super_level hΨ hcomp hum
      (by positivity : (0:ℝ) ≤ B₁ * L) hl hcore hζsm hζcs hζK hζ0 hζ1 hζgrad hζts
    have hIζglob : Integrable (fun x => ζ x * ‖weakGrad u x‖ ^ 2) volume := by
      refine Integrable.mono' hcomp.integrable_normSq_grad
        (hζsm.continuous.aestronglyMeasurable.mul
          (hcomp.aestronglyMeasurable_grad.norm.pow 2))
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hζ0 x), abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg ‖weakGrad u x‖, hζ0 x, hζ1 x]
    have hfρ : f ρ ≤
        ∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l},
          ζ x * ‖weakGrad u x‖ ^ 2 := by
      have hsub : Metric.closedBall x₁ ρ ∩ {x : Euc d | u x < l} ⊆
          Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l} :=
        Set.inter_subset_inter_left _ (Metric.closedBall_subset_closedBall hρt.le)
      have heq : f ρ =
          ∫ x in Metric.closedBall x₁ ρ ∩ {x : Euc d | u x < l},
            ζ x * ‖weakGrad u x‖ ^ 2 := by
        rw [hfdef]
        refine setIntegral_congr_fun (measurableSet_closedBall.inter hAmeas) fun x hx => ?_
        rw [hζone x hx.1, one_mul]
      rw [heq]
      refine setIntegral_mono_set hIζglob.integrableOn ?_ (LE.le.eventuallyLE hsub)
      exact ae_restrict_of_ae (Eventually.of_forall fun x => mul_nonneg (hζ0 x) (sq_nonneg _))
    have hsubs : Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l} ⊆ Metric.ball x₁ s :=
      fun x hx => Metric.closedBall_subset_ball (by linarith) hx.1
    have hITle : (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l},
        negTrunc l u x ^ 2) ≤ I := by
      rw [hIdef]
      refine setIntegral_mono_set hITint ?_ (LE.le.eventuallyLE hsubs)
      exact ae_restrict_of_ae (Eventually.of_forall fun x => sq_nonneg _)
    have hSm : (volume (Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l})).toReal ≤ m := by
      rw [hmdef]
      refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_left _
        (Metric.closedBall_subset_ball (by linarith))))
      exact ((measure_mono Set.inter_subset_left).trans_lt
        (measure_ball_lt_top (x := x₁) (r := s))).ne
    have hVb : (c₀ / (tt - ρ)) ^ 2 *
        (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l}, negTrunc l u x ^ 2) ≤
        (c₀ ^ 2 * I) / (tt - ρ) ^ 2 := by
      rw [div_pow, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hITle (sq_nonneg c₀)) hcgap.le
    have hBm : ((B₁ * L) / (C + c)) *
        (volume (Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l})).toReal ≤
        ((B₁ * L) / (C + c)) * m :=
      mul_le_mul_of_nonneg_left hSm (by positivity)
    have hfe : (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l},
        ‖weakGrad u x‖ ^ 2) = f tt := by rw [hfdef]
    rw [hfe] at hone
    linarith [hfρ, hone, hVb, hBm]
  have hA0 : 0 ≤ c₀ ^ 2 * I := by positivity
  have hB0 : 0 ≤ ((B₁ * L) / (C + c)) * m := mul_nonneg (by positivity) hm0
  have hhole := hhf f r s' (c₀ ^ 2 * I) (((B₁ * L) / (C + c)) * m) (∫ x, ‖weakGrad u x‖ ^ 2)
    hrs' hA0 hB0 hf0 hfM hstep
  have hball : (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l},
      ‖weakGrad u x‖ ^ 2) ≤ f r := by
    rw [hfdef]
    refine setIntegral_mono_set hcomp.integrable_normSq_grad.integrableOn ?_
      (LE.le.eventuallyLE (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall))
    exact ae_restrict_of_ae (Eventually.of_forall fun x => sq_nonneg _)
  have hsr : s' - r = (s - r) / 2 := by rw [hs'def]; ring
  have hsr0 : (0 : ℝ) < (s - r) ^ 2 := by
    have h : 0 < s - r := by linarith
    positivity
  have hexpand : cc * ((c₀ ^ 2 * I) / (s' - r) ^ 2 + ((B₁ * L) / (C + c)) * m) =
      (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I + (cc * (B₁ / (C + c))) * (L * m) := by
    rw [hsr]
    field_simp
    try ring
  have h1 : (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 * I :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_left _ _) hsr0.le) hI0
  have h2 : (cc * (B₁ / (C + c))) * (L * m) ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * (L * m) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hL0 hm0)
  have hfinal : (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l}, ‖weakGrad u x‖ ^ 2) ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 * I +
        max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * (L * m) := by
    calc (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l}, ‖weakGrad u x‖ ^ 2)
        ≤ f r := hball
      _ ≤ cc * ((c₀ ^ 2 * I) / (s' - r) ^ 2 + ((B₁ * L) / (C + c)) * m) := hhole
      _ = (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I + (cc * (B₁ / (C + c))) * (L * m) := hexpand
      _ ≤ _ := by linarith
  rw [hIdef, hmdef, hLdef] at hfinal
  calc (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l}, ‖weakGrad u x‖ ^ 2)
      ≤ _ := hfinal
    _ = max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 *
          (∫ x in Metric.ball x₁ s, negTrunc l u x ^ 2) +
        max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * (l ^ 2 * (Real.log (1 / l) + 1)) *
          (volume (Metric.ball x₁ s ∩ {x : Euc d | u x < l})).toReal := by ring

end Komlos.Literature.Regularized
