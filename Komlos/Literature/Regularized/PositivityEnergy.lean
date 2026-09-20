import Komlos.Literature.Regularized.PositivityCacc

/-!
# Lane `L2` (`reg/positivity`): the Caccioppoli (De Giorgi class) inequality

This file proves the **level-set energy inequality** for the minimizer of the regularized
energy, in the two forms the rest of the lane needs:

* `exists_energy_ineq` — the **sub side**, valid on *every* ball of `ℝ^d` (the ball need not be
  contained in `K`) and at every **nonnegative** level `k`:

  `∫_{B_r ∩ {u>k}} ‖∇u‖² ≤ γ (s-r)⁻² ∫_{B_s} (u-k)_+² + γ |B_s ∩ {u>k}|`.

  This is what makes both the interior De Giorgi class membership and the *boundary* estimate
  available: the competitor `u - ζ (u-k)_+` is admissible for the local problem whatever the
  support of `ζ`, because `(u-k)_+` already vanishes off `K` when `k ≥ 0`
  (`IsRegComp.truncCompetitor`).

* `exists_energy_ineq_super` — the **super side**, for balls `closedBall x₁ s ⊆ K` and levels
  `l > 0`, with the competitor `u + ζ (l-u)_+`, which does need `tsupport ζ ⊆ K`.

Both are assembled from `exists_caccioppoli_core` (minimality plus the two-sided quadratic
growth), the pointwise expansion of the competitor's weak gradient, Young's inequality with the
absorption `(1-ζ)² ≤ 1-ζ`, and `exists_holefilling_const`.

The one-scale inequalities `caccioppoli_one_scale` and `caccioppoli_one_scale_super` are stated
with the Caccioppoli core as a *hypothesis*, so that the constant `B₁` is produced once and for
all outside the quantification over radii and levels.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### Elementary helpers -/

/-- Young's inequality in the crude form `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_sub_sq_le_two_add {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b),
    sq_nonneg (‖a‖ - ‖b‖)]

/-- Squaring is monotone on the nonnegative reals. -/
theorem sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith

/-- The upper ellipticity constant may always be increased; `C + c` is positive and at least
`c`, which is what the absorption step needs. -/
theorem IsRegProfileWith.add_c (hΨ : IsRegProfileWith Ψ c C) : IsRegProfileWith Ψ c (C + c) :=
  { hΨ.toIsRegProfile with
    c_pos := hΨ.c_pos
    C_nonneg := by linarith [hΨ.C_nonneg, hΨ.c_pos]
    lower := hΨ.lower
    upper := fun q ξ => (hΨ.upper q ξ).trans (by nlinarith [sq_nonneg ‖ξ‖, hΨ.c_pos]) }

/-! ### Integrability of the truncations -/

theorem IsRegComp.posTrunc_le (h : IsRegComp K u) {k : ℝ} (hk : 0 ≤ k) (x : Euc d) :
    posTrunc k u x ≤ u x := by
  rw [posTrunc]
  rcases le_or_gt (u x) k with hx | hx
  · rw [max_eq_right (by linarith)]; exact h.nonneg x
  · rw [max_eq_left (by linarith)]; linarith

theorem IsRegComp.aesm_posTrunc (h : IsRegComp K u) (k : ℝ) :
    AEStronglyMeasurable (posTrunc k u) volume := by
  have hc : Continuous fun t : ℝ => max (t - k) 0 :=
    (continuous_id.sub continuous_const).max continuous_const
  exact hc.comp_aestronglyMeasurable h.aestronglyMeasurable

theorem IsRegComp.integrable_posTrunc_sq (h : IsRegComp K u) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (fun x => posTrunc k u x ^ 2) volume := by
  refine Integrable.mono' h.integrable_sq ((h.aesm_posTrunc k).pow 2)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [posTrunc_nonneg k u x, h.posTrunc_le hk x, h.nonneg x]

theorem IsRegComp.aesm_negTrunc (h : IsRegComp K u) (l : ℝ) :
    AEStronglyMeasurable (negTrunc l u) volume := by
  have hc : Continuous fun t : ℝ => max (l - t) 0 :=
    (continuous_const.sub continuous_id).max continuous_const
  exact hc.comp_aestronglyMeasurable h.aestronglyMeasurable

theorem IsRegComp.negTrunc_le (h : IsRegComp K u) {l : ℝ} (hl : 0 ≤ l) (x : Euc d) :
    negTrunc l u x ≤ l := by
  rw [negTrunc]
  rcases le_or_gt (u x) l with hx | hx
  · rw [max_eq_left (by linarith)]; linarith [h.nonneg x]
  · rw [max_eq_right (by linarith)]; exact hl

/-! ### The one-scale Caccioppoli inequality, sub side -/

/-- **One scale of the Caccioppoli inequality (sub side).**

With `w = u - ζ (u-k)_+` as competitor (`IsRegComp.truncCompetitor`) and
`S = closedBall x₁ t ∩ {u > k}`, minimality gives
`(c/2) ∫_S ‖∇u‖² ≤ ((C+c)/2) ∫_S ‖∇w‖² + B₁ |S|`; on `S` one has
`∇w = (1-ζ)∇u - (u-k)_+ ∇ζ`, so `‖∇w‖² ≤ 2(1-ζ)‖∇u‖² + 2 (u-k)_+² ‖∇ζ‖²` — Young, together
with the absorption `(1-ζ)² ≤ 1-ζ` that is the whole point of using a cutoff between `0` and
`1` linearly rather than quadratically.  Dividing by `C + c` gives the statement. -/
theorem caccioppoli_one_scale (hΨ : IsRegProfileWith Ψ c C)
    (hcomp : IsRegComp K u) (hum : Measurable u)
    {Mbig B₁ : ℝ} (_hB₁0 : 0 ≤ B₁) (huM : ∀ x, u x ≤ Mbig)
    (hcore : ∀ w : Euc d → ℝ, IsRegComp K w → (∀ x, w x ≤ Mbig) →
      ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
      (∀ᵐ x, x ∉ S → u x = w x) → (∀ᵐ x, x ∉ S → weakGrad u x = weakGrad w x) →
      c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
        (C + c) / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + B₁ * (volume S).toReal)
    {ζ : Euc d → ℝ} (hζsm : ContDiff ℝ ∞ ζ) (hζcs : HasCompactSupport ζ)
    (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) {Vb : ℝ} (hζgrad : ∀ x, ‖gradient ζ x‖ ≤ Vb)
    {x₁ : Euc d} {t : ℝ} (hζts : tsupport ζ ⊆ Metric.closedBall x₁ t)
    {k : ℝ} (hk : 0 ≤ k) :
    (∫ x in Metric.closedBall x₁ t ∩ {x | k < u x}, ζ x * ‖weakGrad u x‖ ^ 2) ≤
      (1 - c / (2 * (C + c))) *
          (∫ x in Metric.closedBall x₁ t ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2) +
        Vb ^ 2 * (∫ x in Metric.closedBall x₁ t ∩ {x | k < u x}, posTrunc k u x ^ 2) +
        (B₁ / (C + c)) *
          (volume (Metric.closedBall x₁ t ∩ {x | k < u x})).toReal := by
  classical
  set C' : ℝ := C + c with hC'def
  have hC'pos : 0 < C' := by rw [hC'def]; linarith [hΨ.C_nonneg, hΨ.c_pos]
  have hcC' : c ≤ C' := by rw [hC'def]; linarith [hΨ.C_nonneg]
  set A : Set (Euc d) := {x | k < u x} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_lt measurable_const hum
  obtain ⟨hwcomp, hwg⟩ := hcomp.truncCompetitor hk hζsm hζcs hζ0 hζ1
  set w : Euc d → ℝ := fun x => u x - ζ x * posTrunc k u x with hwdef
  set S : Set (Euc d) := Metric.closedBall x₁ t ∩ A with hSdef
  have hSmeas : MeasurableSet S := measurableSet_closedBall.inter hAmeas
  have hSfin : volume S ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt
      (measure_closedBall_lt_top (x := x₁) (r := t))).ne
  -- off `S` the competitor and its gradient agree with `u`
  have hζoff : ∀ x, x ∉ Metric.closedBall x₁ t → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hζts h)
  have hgζoff : ∀ x, x ∉ Metric.closedBall x₁ t → gradient ζ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport fun h => hx (hζts h)
  have hTzero : ∀ x, x ∉ A → posTrunc k u x = 0 := fun x hx => by
    rw [posTrunc, max_eq_right]
    simp only [hAdef, Set.mem_ofPred_eq, not_lt] at hx
    linarith
  have hIndzero : ∀ x, x ∉ A → levelInd k u x = 0 := fun x hx => by
    simp only [hAdef, Set.mem_ofPred_eq, not_lt] at hx
    rw [levelInd, if_neg (by linarith)]
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
  have hwM : ∀ x, w x ≤ Mbig := fun x => by
    have h0 : 0 ≤ ζ x * posTrunc k u x := mul_nonneg (hζ0 x) (posTrunc_nonneg k u x)
    rw [hwdef]
    simp only []
    linarith [huM x]
  have hcc := hcore w hwcomp hwM S hSmeas hSfin hoffv hoffg
  -- the pointwise gradient bound on `S`
  have hgw : ∀ᵐ x ∂(volume.restrict S), ‖weakGrad w x‖ ^ 2 ≤
      2 * ((1 - ζ x) * ‖weakGrad u x‖ ^ 2) + (2 * Vb ^ 2) * posTrunc k u x ^ 2 := by
    rw [ae_restrict_iff' hSmeas]
    filter_upwards [hwg] with x hx hxS
    have hxA : x ∈ A := hxS.2
    have hind : levelInd k u x = 1 := by
      simp only [hAdef, Set.mem_ofPred_eq] at hxA
      rw [levelInd, if_pos hxA]
    rw [hx, hind, mul_one]
    have hsplit : weakGrad u x - ζ x • weakGrad u x - posTrunc k u x • gradient ζ x =
        (1 - ζ x) • weakGrad u x - posTrunc k u x • gradient ζ x := by
      rw [sub_smul, one_smul]
    rw [hsplit]
    have h1 := norm_sub_sq_le_two_add ((1 - ζ x) • weakGrad u x)
      (posTrunc k u x • gradient ζ x)
    have h2 : ‖(1 - ζ x) • weakGrad u x‖ ^ 2 ≤ (1 - ζ x) * ‖weakGrad u x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hζ1 x]), mul_pow]
      have hp : 0 ≤ ζ x * ((1 - ζ x) * ‖weakGrad u x‖ ^ 2) :=
        mul_nonneg (hζ0 x) (mul_nonneg (by linarith [hζ1 x]) (sq_nonneg _))
      nlinarith [hp]
    have h3 : ‖posTrunc k u x • gradient ζ x‖ ^ 2 ≤ Vb ^ 2 * posTrunc k u x ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (posTrunc_nonneg k u x), mul_pow]
      have hsq : ‖gradient ζ x‖ ^ 2 ≤ Vb ^ 2 := by
        nlinarith [hζgrad x, norm_nonneg (gradient ζ x)]
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (posTrunc k u x))]
    linarith
  -- integrability
  have hIu : IntegrableOn (fun x => ‖weakGrad u x‖ ^ 2) S volume :=
    hcomp.integrable_normSq_grad.integrableOn
  have hIw : IntegrableOn (fun x => ‖weakGrad w x‖ ^ 2) S volume :=
    hwcomp.integrable_normSq_grad.integrableOn
  have hIT : IntegrableOn (fun x => posTrunc k u x ^ 2) S volume :=
    (hcomp.integrable_posTrunc_sq hk).integrableOn
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
  -- integrate the pointwise gradient bound
  have hbound : (∫ x in S, ‖weakGrad w x‖ ^ 2) ≤
      2 * ((∫ x in S, ‖weakGrad u x‖ ^ 2) - ∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2) +
        (2 * Vb ^ 2) * ∫ x in S, posTrunc k u x ^ 2 := by
    have hsum : IntegrableOn
        (fun x => 2 * ((1 - ζ x) * ‖weakGrad u x‖ ^ 2) + (2 * Vb ^ 2) * posTrunc k u x ^ 2)
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
  -- absorb
  have hhalf : (0 : ℝ) ≤ C' / 2 := by linarith
  have h1 := mul_le_mul_of_nonneg_left hbound hhalf
  have hexp : C' / 2 * (2 * ((∫ x in S, ‖weakGrad u x‖ ^ 2) -
        ∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2) + (2 * Vb ^ 2) * ∫ x in S, posTrunc k u x ^ 2) =
      C' * (∫ x in S, ‖weakGrad u x‖ ^ 2) - C' * (∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2) +
        C' * (Vb ^ 2 * ∫ x in S, posTrunc k u x ^ 2) := by ring
  rw [hexp] at h1
  have hkey : C' * (∫ x in S, ζ x * ‖weakGrad u x‖ ^ 2) ≤
      (C' - c / 2) * (∫ x in S, ‖weakGrad u x‖ ^ 2) +
        C' * (Vb ^ 2 * ∫ x in S, posTrunc k u x ^ 2) + B₁ * (volume S).toReal := by
    linarith [hcc, h1]
  have hmul : C' * ((1 - c / (2 * C')) * (∫ x in S, ‖weakGrad u x‖ ^ 2) +
        Vb ^ 2 * (∫ x in S, posTrunc k u x ^ 2) + (B₁ / C') * (volume S).toReal) =
      (C' - c / 2) * (∫ x in S, ‖weakGrad u x‖ ^ 2) +
        C' * (Vb ^ 2 * ∫ x in S, posTrunc k u x ^ 2) + B₁ * (volume S).toReal := by
    field_simp
    try ring
  rw [← hmul] at hkey
  exact le_of_mul_le_mul_left hkey hC'pos

/-! ### The one-scale Caccioppoli inequality, super side -/

/-- **One scale of the Caccioppoli inequality (super side).**  Identical to
`caccioppoli_one_scale`, with the competitor `u + ζ (l-u)_+` of
`IsRegComp.truncCompetitorSuper`; the cutoff must now be supported inside `K`, and the level
`l` must be nonnegative and below the bound `Mbig` used by the Caccioppoli core (the competitor
takes values in `[u, max (u, l)]`). -/
theorem caccioppoli_one_scale_super (hΨ : IsRegProfileWith Ψ c C)
    (hcomp : IsRegComp K u) (hum : Measurable u)
    {Mbig B₁ : ℝ} (_hB₁0 : 0 ≤ B₁) (huM : ∀ x, u x ≤ Mbig)
    (hcore : ∀ w : Euc d → ℝ, IsRegComp K w → (∀ x, w x ≤ Mbig) →
      ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
      (∀ᵐ x, x ∉ S → u x = w x) → (∀ᵐ x, x ∉ S → weakGrad u x = weakGrad w x) →
      c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
        (C + c) / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + B₁ * (volume S).toReal)
    {ζ : Euc d → ℝ} (hζsm : ContDiff ℝ ∞ ζ) (hζcs : HasCompactSupport ζ)
    (hζK : tsupport ζ ⊆ K) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1)
    {Vb : ℝ} (hζgrad : ∀ x, ‖gradient ζ x‖ ≤ Vb)
    {x₁ : Euc d} {t : ℝ} (hζts : tsupport ζ ⊆ Metric.closedBall x₁ t)
    {l : ℝ} (hl : 0 ≤ l) (hlM : l ≤ Mbig) :
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
  have hwM : ∀ x, w x ≤ Mbig := fun x => by
    have h1 : ζ x * negTrunc l u x ≤ negTrunc l u x := by
      nlinarith [negTrunc_nonneg l u x, hζ0 x, hζ1 x]
    have h2 : u x + negTrunc l u x ≤ Mbig := by
      rw [negTrunc]
      rcases le_or_gt (u x) l with h | h
      · rw [max_eq_left (by linarith)]
        have he : u x + (l - u x) = l := by ring
        rw [he]; exact hlM
      · rw [max_eq_right (by linarith)]
        have he : u x + 0 = u x := by ring
        rw [he]; exact huM x
    rw [hwdef]
    simp only []
    linarith
  have hcc := hcore w hwcomp hwM S hSmeas hSfin hoffv hoffg
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
  -- integrability
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


/-! ### The assembled energy inequality, sub side -/

set_option maxHeartbeats 1000000 in
/-- **The Caccioppoli inequality for the regularized minimizer, sub side.**

For every ball of `ℝ^d` — *not* only balls contained in `K` — and every level `k ≥ 0`,

`∫_{B_r ∩ {u>k}} ‖∇u‖² ≤ γ (s-r)⁻² ∫_{B_s} (u-k)_+² + γ |B_s ∩ {u>k}|`

with `γ` depending only on `κ`, the ellipticity constants of `Ψ`, `K` and the bound on `u`.

The one-scale inequality `caccioppoli_one_scale`, applied with the cutoffs of
`exists_cutoff_const` between `closedBall x₁ ρ` and `closedBall x₁ t`, gives
`f(ρ) ≤ θ f(t) + c₀² (t-ρ)⁻² ∫_{B_s}(u-k)_+² + (B₁/(C+c)) |B_s ∩ {u>k}|` for
`f(ρ) = ∫_{closedBall x₁ ρ ∩ {u>k}} ‖∇u‖²` and `θ = 1 - c/(2(C+c)) < 1`; the hole-filling
iteration `exists_holefilling_const` on `[r, (r+s)/2]` removes the first term. -/
theorem exists_energy_ineq (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegMinimizer 2 κ Ψ K u) (hcomp : IsRegComp K u) (hum : Measurable u) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ (x₁ : Euc d) (r s k : ℝ), 0 < r → r < s → 0 ≤ k →
      (∫ x in Metric.ball x₁ r ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2) ≤
        γ / (s - r) ^ 2 * (∫ x in Metric.ball x₁ s, posTrunc k u x ^ 2) +
          γ * (volume (Metric.ball x₁ s ∩ {x | k < u x})).toReal := by
  classical
  obtain ⟨M, hM⟩ := hcomp.exists_le
  obtain ⟨Mbig, hMbigdef⟩ : ∃ Mbig : ℝ, Mbig = max M 1 + 1 := ⟨_, rfl⟩
  have hMbig : (1 : ℝ) ≤ Mbig := by rw [hMbigdef]; linarith [le_max_right M 1]
  have huM : ∀ x, u x ≤ Mbig := fun x => by
    rw [hMbigdef]; linarith [hM x, le_max_left M 1]
  obtain ⟨B₁, hB₁0, hcore⟩ := exists_caccioppoli_core hκ hΨ.add_c hK hu hcomp hMbig huM
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
  intro x₁ r s k hr hrs hk
  have hAmeas : MeasurableSet {x : Euc d | k < u x} := measurableSet_lt measurable_const hum
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ x in Metric.ball x₁ s, posTrunc k u x ^ 2 := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ,
      m = (volume (Metric.ball x₁ s ∩ {x : Euc d | k < u x})).toReal := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hIdef]; exact integral_nonneg fun x => sq_nonneg _
  have hm0 : 0 ≤ m := by rw [hmdef]; exact ENNReal.toReal_nonneg
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun tt =>
      ∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x}, ‖weakGrad u x‖ ^ 2 := ⟨_, rfl⟩
  have hf0 : ∀ tt, 0 ≤ f tt := fun tt => by
    rw [hfdef]; exact integral_nonneg fun x => sq_nonneg _
  have hfM : ∀ tt, f tt ≤ ∫ x, ‖weakGrad u x‖ ^ 2 := fun tt => by
    rw [hfdef]
    exact setIntegral_le_integral hcomp.integrable_normSq_grad
      (Eventually.of_forall fun x => sq_nonneg _)
  obtain ⟨s', hs'def⟩ : ∃ s' : ℝ, s' = (r + s) / 2 := ⟨_, rfl⟩
  have hrs' : r < s' := by rw [hs'def]; linarith
  have hs's : s' < s := by rw [hs'def]; linarith
  -- the one-scale inequality
  have hstep : ∀ ρ tt : ℝ, r ≤ ρ → ρ < tt → tt ≤ s' →
      f ρ ≤ (1 - c / (2 * (C + c))) * f tt + (c₀ ^ 2 * I) / (tt - ρ) ^ 2 +
        (B₁ / (C + c)) * m := by
    intro ρ tt hrρ hρt htts
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr hrρ
    have hgap : (0 : ℝ) < tt - ρ := by linarith
    have hcgap : (0 : ℝ) < (tt - ρ) ^ 2 := by positivity
    obtain ⟨ζ, hζsm, hζcs, hζts, hζ0, hζ1, hζone, hζgrad⟩ := hcut x₁ ρ tt hρ0 hρt
    have hone := caccioppoli_one_scale hΨ hcomp hum hB₁0 huM hcore hζsm hζcs hζ0 hζ1
      hζgrad hζts hk
    -- integrability of the `ζ`-weighted energy
    have hIζglob : Integrable (fun x => ζ x * ‖weakGrad u x‖ ^ 2) volume := by
      refine Integrable.mono' hcomp.integrable_normSq_grad
        (hζsm.continuous.aestronglyMeasurable.mul
          (hcomp.aestronglyMeasurable_grad.norm.pow 2))
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hζ0 x), abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg ‖weakGrad u x‖, hζ0 x, hζ1 x]
    -- `f ρ` is dominated by the `ζ`-weighted energy
    have hfρ : f ρ ≤
        ∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x}, ζ x * ‖weakGrad u x‖ ^ 2 := by
      have hsub : Metric.closedBall x₁ ρ ∩ {x : Euc d | k < u x} ⊆
          Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x} :=
        Set.inter_subset_inter_left _ (Metric.closedBall_subset_closedBall hρt.le)
      have heq : f ρ =
          ∫ x in Metric.closedBall x₁ ρ ∩ {x : Euc d | k < u x}, ζ x * ‖weakGrad u x‖ ^ 2 := by
        rw [hfdef]
        refine setIntegral_congr_fun (measurableSet_closedBall.inter hAmeas) fun x hx => ?_
        rw [hζone x hx.1, one_mul]
      rw [heq]
      refine setIntegral_mono_set hIζglob.integrableOn ?_
        (LE.le.eventuallyLE hsub)
      exact ae_restrict_of_ae (Eventually.of_forall fun x => mul_nonneg (hζ0 x) (sq_nonneg _))
    -- the truncation and measure terms are dominated by those on `B_s`
    have hsubs : Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x} ⊆ Metric.ball x₁ s :=
      fun x hx => Metric.closedBall_subset_ball (by linarith) hx.1
    have hITle : (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x},
        posTrunc k u x ^ 2) ≤ I := by
      rw [hIdef]
      refine setIntegral_mono_set (hcomp.integrable_posTrunc_sq hk).integrableOn ?_
        (LE.le.eventuallyLE hsubs)
      exact ae_restrict_of_ae (Eventually.of_forall fun x => sq_nonneg _)
    have hSm : (volume (Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x})).toReal ≤ m := by
      rw [hmdef]
      refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_left _
        (Metric.closedBall_subset_ball (by linarith))))
      exact ((measure_mono Set.inter_subset_left).trans_lt
        (measure_ball_lt_top (x := x₁) (r := s))).ne
    -- combine
    have hVb : (c₀ / (tt - ρ)) ^ 2 * (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x},
        posTrunc k u x ^ 2) ≤ (c₀ ^ 2 * I) / (tt - ρ) ^ 2 := by
      rw [div_pow, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hITle (sq_nonneg c₀)) hcgap.le
    have hBm : (B₁ / (C + c)) *
        (volume (Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x})).toReal ≤
        (B₁ / (C + c)) * m :=
      mul_le_mul_of_nonneg_left hSm (by positivity)
    have hfe : (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | k < u x},
        ‖weakGrad u x‖ ^ 2) = f tt := by rw [hfdef]
    rw [hfe] at hone
    linarith [hfρ, hone, hVb, hBm]
  -- the hole-filling iteration
  have hA0 : 0 ≤ c₀ ^ 2 * I := by positivity
  have hB0 : 0 ≤ (B₁ / (C + c)) * m := mul_nonneg (by positivity) hm0
  have hhole := hhf f r s' (c₀ ^ 2 * I) ((B₁ / (C + c)) * m) (∫ x, ‖weakGrad u x‖ ^ 2)
    hrs' hA0 hB0 hf0 hfM hstep
  -- conclude
  have hball : (∫ x in Metric.ball x₁ r ∩ {x : Euc d | k < u x}, ‖weakGrad u x‖ ^ 2) ≤ f r := by
    rw [hfdef]
    refine setIntegral_mono_set hcomp.integrable_normSq_grad.integrableOn ?_
      (LE.le.eventuallyLE
        (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall))
    exact ae_restrict_of_ae (Eventually.of_forall fun x => sq_nonneg _)
  have hsr : s' - r = (s - r) / 2 := by rw [hs'def]; ring
  have hsr0 : (0 : ℝ) < (s - r) ^ 2 := by
    have h : 0 < s - r := by linarith
    positivity
  have hexpand : cc * ((c₀ ^ 2 * I) / (s' - r) ^ 2 + (B₁ / (C + c)) * m) =
      (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I + (cc * (B₁ / (C + c))) * m := by
    rw [hsr]
    field_simp
    try ring
  have h1 : (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 * I :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_left _ _) hsr0.le) hI0
  have h2 : (cc * (B₁ / (C + c))) * m ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * m :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hm0
  rw [← hIdef, ← hmdef]
  calc (∫ x in Metric.ball x₁ r ∩ {x : Euc d | k < u x}, ‖weakGrad u x‖ ^ 2)
      ≤ f r := hball
    _ ≤ cc * ((c₀ ^ 2 * I) / (s' - r) ^ 2 + (B₁ / (C + c)) * m) := hhole
    _ = (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I + (cc * (B₁ / (C + c))) * m := hexpand
    _ ≤ _ := by linarith


/-! ### The assembled energy inequality, super side -/

set_option maxHeartbeats 1000000 in
/-- **The Caccioppoli inequality for the regularized minimizer, super side.**

For every ball `closedBall x₁ s ⊆ K` and every level `l ≥ 0`,

`∫_{B_r ∩ {u<l}} ‖∇u‖² ≤ γ (s-r)⁻² ∫_{B_s} (l-u)_+² + γ |B_s ∩ {u<l}|`.

The support condition on the ball is genuinely needed here: the competitor
`u + ζ (l-u)_+` only vanishes off `K` when `ζ` does.  Levels above the bound on `u` are reduced
to the level `Mbig` (there `{u < l}` is all of `ℝ^d` either way, and `(Mbig-u)_+ ≤ (l-u)_+`). -/
theorem exists_energy_ineq_super (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) (hcomp : IsRegComp K u)
    (hum : Measurable u) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ (x₁ : Euc d) (r s l : ℝ), 0 < r → r < s → 0 ≤ l →
      Metric.closedBall x₁ s ⊆ K →
      (∫ x in Metric.ball x₁ r ∩ {x | u x < l}, ‖weakGrad u x‖ ^ 2) ≤
        γ / (s - r) ^ 2 * (∫ x in Metric.ball x₁ s, negTrunc l u x ^ 2) +
          γ * (volume (Metric.ball x₁ s ∩ {x | u x < l})).toReal := by
  classical
  obtain ⟨M, hM⟩ := hcomp.exists_le
  obtain ⟨Mbig, hMbigdef⟩ : ∃ Mbig : ℝ, Mbig = max M 1 + 1 := ⟨_, rfl⟩
  have hMbig : (1 : ℝ) ≤ Mbig := by rw [hMbigdef]; linarith [le_max_right M 1]
  have huM : ∀ x, u x ≤ Mbig := fun x => by
    rw [hMbigdef]; linarith [hM x, le_max_left M 1]
  have huMlt : ∀ x, u x < Mbig := fun x => by
    rw [hMbigdef]; linarith [hM x, le_max_left M 1]
  obtain ⟨B₁, hB₁0, hcore⟩ := exists_caccioppoli_core hκ hΨ.add_c hK hu hcomp hMbig huM
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
  intro x₁ r s l hr hrs hl hKball
  -- reduce to a level below `Mbig`
  obtain ⟨l', hl'def⟩ : ∃ l' : ℝ, l' = min l Mbig := ⟨_, rfl⟩
  have hl'0 : 0 ≤ l' := by rw [hl'def]; exact le_min hl (by linarith)
  have hl'M : l' ≤ Mbig := by rw [hl'def]; exact min_le_right _ _
  have hl'l : l' ≤ l := by rw [hl'def]; exact min_le_left _ _
  have hseteq : {x : Euc d | u x < l} = {x : Euc d | u x < l'} := by
    ext x
    simp only [Set.mem_ofPred_eq, hl'def, lt_min_iff]
    exact ⟨fun h => ⟨h, huMlt x⟩, fun h => h.1⟩
  have hnegle : ∀ x, negTrunc l' u x ≤ negTrunc l u x := fun x => by
    rw [negTrunc, negTrunc]
    exact max_le_max (by linarith) le_rfl
  have hAmeas : MeasurableSet {x : Euc d | u x < l'} := measurableSet_lt hum measurable_const
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ x in Metric.ball x₁ s, negTrunc l' u x ^ 2 := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ,
      m = (volume (Metric.ball x₁ s ∩ {x : Euc d | u x < l'})).toReal := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hIdef]; exact integral_nonneg fun x => sq_nonneg _
  have hm0 : 0 ≤ m := by rw [hmdef]; exact ENNReal.toReal_nonneg
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun tt =>
      ∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'}, ‖weakGrad u x‖ ^ 2 := ⟨_, rfl⟩
  have hf0 : ∀ tt, 0 ≤ f tt := fun tt => by
    rw [hfdef]; exact integral_nonneg fun x => sq_nonneg _
  have hfM : ∀ tt, f tt ≤ ∫ x, ‖weakGrad u x‖ ^ 2 := fun tt => by
    rw [hfdef]
    exact setIntegral_le_integral hcomp.integrable_normSq_grad
      (Eventually.of_forall fun x => sq_nonneg _)
  obtain ⟨s', hs'def⟩ : ∃ s' : ℝ, s' = (r + s) / 2 := ⟨_, rfl⟩
  have hrs' : r < s' := by rw [hs'def]; linarith
  have hs's : s' < s := by rw [hs'def]; linarith
  have hITint : Integrable (fun x => negTrunc l' u x ^ 2)
      (volume.restrict (Metric.ball x₁ s)) := by
    refine Integrable.mono'
      (integrableOn_const (μ := volume) (C := l' ^ 2)
        (measure_ball_lt_top (x := x₁) (r := s)).ne)
      ((hcomp.aesm_negTrunc l').pow 2).restrict ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq_of_nonneg (negTrunc_nonneg l' u x) (hcomp.negTrunc_le hl'0 x)
  have hstep : ∀ ρ tt : ℝ, r ≤ ρ → ρ < tt → tt ≤ s' →
      f ρ ≤ (1 - c / (2 * (C + c))) * f tt + (c₀ ^ 2 * I) / (tt - ρ) ^ 2 +
        (B₁ / (C + c)) * m := by
    intro ρ tt hrρ hρt htts
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr hrρ
    have hgap : (0 : ℝ) < tt - ρ := by linarith
    have hcgap : (0 : ℝ) < (tt - ρ) ^ 2 := by positivity
    obtain ⟨ζ, hζsm, hζcs, hζts, hζ0, hζ1, hζone, hζgrad⟩ := hcut x₁ ρ tt hρ0 hρt
    have hζK : tsupport ζ ⊆ K :=
      hζts.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hKball)
    have hone := caccioppoli_one_scale_super hΨ hcomp hum hB₁0 huM hcore hζsm hζcs hζK
      hζ0 hζ1 hζgrad hζts hl'0 hl'M
    have hIζglob : Integrable (fun x => ζ x * ‖weakGrad u x‖ ^ 2) volume := by
      refine Integrable.mono' hcomp.integrable_normSq_grad
        (hζsm.continuous.aestronglyMeasurable.mul
          (hcomp.aestronglyMeasurable_grad.norm.pow 2))
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hζ0 x), abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg ‖weakGrad u x‖, hζ0 x, hζ1 x]
    have hfρ : f ρ ≤
        ∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'},
          ζ x * ‖weakGrad u x‖ ^ 2 := by
      have hsub : Metric.closedBall x₁ ρ ∩ {x : Euc d | u x < l'} ⊆
          Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'} :=
        Set.inter_subset_inter_left _ (Metric.closedBall_subset_closedBall hρt.le)
      have heq : f ρ =
          ∫ x in Metric.closedBall x₁ ρ ∩ {x : Euc d | u x < l'},
            ζ x * ‖weakGrad u x‖ ^ 2 := by
        rw [hfdef]
        refine setIntegral_congr_fun (measurableSet_closedBall.inter hAmeas) fun x hx => ?_
        rw [hζone x hx.1, one_mul]
      rw [heq]
      refine setIntegral_mono_set hIζglob.integrableOn ?_ (LE.le.eventuallyLE hsub)
      exact ae_restrict_of_ae (Eventually.of_forall fun x => mul_nonneg (hζ0 x) (sq_nonneg _))
    have hsubs : Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'} ⊆ Metric.ball x₁ s :=
      fun x hx => Metric.closedBall_subset_ball (by linarith) hx.1
    have hITle : (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'},
        negTrunc l' u x ^ 2) ≤ I := by
      rw [hIdef]
      refine setIntegral_mono_set hITint ?_ (LE.le.eventuallyLE hsubs)
      exact ae_restrict_of_ae (Eventually.of_forall fun x => sq_nonneg _)
    have hSm : (volume (Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'})).toReal ≤ m := by
      rw [hmdef]
      refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_left _
        (Metric.closedBall_subset_ball (by linarith))))
      exact ((measure_mono Set.inter_subset_left).trans_lt
        (measure_ball_lt_top (x := x₁) (r := s))).ne
    have hVb : (c₀ / (tt - ρ)) ^ 2 *
        (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'}, negTrunc l' u x ^ 2) ≤
        (c₀ ^ 2 * I) / (tt - ρ) ^ 2 := by
      rw [div_pow, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hITle (sq_nonneg c₀)) hcgap.le
    have hBm : (B₁ / (C + c)) *
        (volume (Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'})).toReal ≤
        (B₁ / (C + c)) * m :=
      mul_le_mul_of_nonneg_left hSm (by positivity)
    have hfe : (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l'},
        ‖weakGrad u x‖ ^ 2) = f tt := by rw [hfdef]
    rw [hfe] at hone
    linarith [hfρ, hone, hVb, hBm]
  have hA0 : 0 ≤ c₀ ^ 2 * I := by positivity
  have hB0 : 0 ≤ (B₁ / (C + c)) * m := mul_nonneg (by positivity) hm0
  have hhole := hhf f r s' (c₀ ^ 2 * I) ((B₁ / (C + c)) * m) (∫ x, ‖weakGrad u x‖ ^ 2)
    hrs' hA0 hB0 hf0 hfM hstep
  have hball : (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l'},
      ‖weakGrad u x‖ ^ 2) ≤ f r := by
    rw [hfdef]
    refine setIntegral_mono_set hcomp.integrable_normSq_grad.integrableOn ?_
      (LE.le.eventuallyLE (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall))
    exact ae_restrict_of_ae (Eventually.of_forall fun x => sq_nonneg _)
  have hsr : s' - r = (s - r) / 2 := by rw [hs'def]; ring
  have hsr0 : (0 : ℝ) < (s - r) ^ 2 := by
    have h : 0 < s - r := by linarith
    positivity
  have hexpand : cc * ((c₀ ^ 2 * I) / (s' - r) ^ 2 + (B₁ / (C + c)) * m) =
      (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I + (cc * (B₁ / (C + c))) * m := by
    rw [hsr]
    field_simp
    try ring
  have h1 : (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 * I :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_left _ _) hsr0.le) hI0
  have h2 : (cc * (B₁ / (C + c))) * m ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * m :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hm0
  have hmain : (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l'}, ‖weakGrad u x‖ ^ 2) ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 * I +
        max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * m := by
    calc (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l'}, ‖weakGrad u x‖ ^ 2)
        ≤ f r := hball
      _ ≤ cc * ((c₀ ^ 2 * I) / (s' - r) ^ 2 + (B₁ / (C + c)) * m) := hhole
      _ = (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I + (cc * (B₁ / (C + c))) * m := hexpand
      _ ≤ _ := by linarith
  -- return to the original level `l`
  rw [hseteq]
  refine hmain.trans (add_le_add ?_ (le_of_eq (by rw [hmdef])))
  have hIle : I ≤ ∫ x in Metric.ball x₁ s, negTrunc l u x ^ 2 := by
    rw [hIdef]
    refine setIntegral_mono_on hITint ?_ measurableSet_ball fun x _ => ?_
    · refine Integrable.mono'
        (integrableOn_const (μ := volume) (C := l ^ 2)
          (measure_ball_lt_top (x := x₁) (r := s)).ne)
        ((hcomp.aesm_negTrunc l).pow 2).restrict ?_
      refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq_of_nonneg (negTrunc_nonneg l u x) (hcomp.negTrunc_le hl x)
    · exact sq_le_sq_of_nonneg (negTrunc_nonneg l' u x) (hnegle x)
  have hq : (0 : ℝ) ≤ max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 := by
    apply div_nonneg _ hsr0.le
    exact le_max_of_le_left hγ0
  exact mul_le_mul_of_nonneg_left hIle hq


end Komlos.Literature.Regularized
