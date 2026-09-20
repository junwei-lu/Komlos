import Komlos.Literature.PLaplacian.SchauderAux
import Komlos.Literature.PLaplacian.SchauderConst

/-!
# From a Campanato decay to an `L²` energy decay: the means telescope (lane `L8`)

Real-analysis auxiliaries for `exists_regHarmonic_energy_decay`
(`Komlos/Literature/Regularized/InteriorCampanatoAux.lean`), the last input of the
Campanato iteration of link 6.  Nothing here involves an equation: every statement is
about a field `f : Euc d → Euc d` continuous on a closed ball.

## The problem

Lane `reg/c2h` showed the scale-invariant *sup* bound for a `Ψ`-harmonic gradient field to be
false (`NOTES_L3h.md`, DEVIATION 1); what its Campanato decay
`exists_regHarmonic_campanato_field` really gives is a decay of the `L²` **excess**

`sqExcess f x t = ∫_{B_t} ‖f - (f)_{B_t}‖² ≤ Cdec (t/R)^{d+2β} sqExcess f x R`.

The energy decay `∫_{B_ρ} ‖f‖² ≤ Cs (ρ/R)^d ∫_{B_R} ‖f‖²` that link 6 iterates needs, on top of
that, control of the *means* `(f)_{B_ρ}` themselves.  The three ingredients are

* `setIntegral_norm_sq_eq_sqExcess_add` — the Pythagoras identity
  `∫_{B_t} ‖f‖² = sqExcess f x t + |B_t| ‖(f)_{B_t}‖²`;
* `volume_real_mul_norm_setAverage_sub_sq_le` — `|B_ρ| ‖(f)_{B_ρ} - (f)_{B_t}‖² ≤ sqExcess f x t`
  for `ρ ≤ t`, an immediate consequence of the previous item applied to `f - (f)_{B_t}`;
* `exists_norm_setAverage_sub_setAverage_bound` — the **geometric telescoping of the means**:
  the previous two items give `‖(f)_{B_ρ} - (f)_{B_t}‖ ≤ √(2^d Cdec) (t/R)^β √(A_R/|B_R|)` for
  comparable radii `ρ ≤ t ≤ 2ρ`, and summing over the halvings of `R` (induction on the number
  of halvings, as in `Komlos.Literature.exists_norm_setAverage_sub_setAverage_le`) bounds
  `‖(f)_{B_ρ} - (f)_{B_R}‖` by `K √(A_R/|B_R|)` uniformly in `ρ ∈ (0, R]`.

Nothing here needs `d > 0`: for `d = 0` all the balls have the same (positive, finite) volume
and every displayed factor `(t/R)^d` is `1`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Two elementary facts -/

/-- Comparison of nonnegative reals through their squares. -/
theorem edec_le_of_sq_le_sq {a b : ℝ} (hab : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b := by
  by_cases ha : a ≤ 0
  · linarith
  · push Not at ha
    nlinarith

/-- The ratio of the volumes of two concentric closed balls is `(ρ/t)^d`. -/
theorem volume_real_closedBall_eq_ratio (x : Euc d) {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 < t) :
    volume.real (Metric.closedBall x ρ) =
      (ρ / t) ^ d * volume.real (Metric.closedBall x t) := by
  have htd : (t : ℝ) ^ d ≠ 0 := pow_ne_zero d ht.ne'
  rw [Komlos.Literature.volume_real_closedBall x hρ,
    Komlos.Literature.volume_real_closedBall x ht.le, div_pow]
  field_simp

/-! ### Pythagoras for the mean -/

/-- **The energy splits into the excess and the mean:**
`∫_{B_t} ‖f‖² = sqExcess f x t + |B_t| ‖(f)_{B_t}‖²`. -/
theorem setIntegral_norm_sq_eq_sqExcess_add {f : Euc d → Euc d} {x : Euc d} {t : ℝ} (ht : 0 < t)
    (hf : ContinuousOn f (Metric.closedBall x t)) :
    (∫ y in Metric.closedBall x t, ‖f y‖ ^ 2) =
      Komlos.Literature.sqExcess f x t +
        volume.real (Metric.closedBall x t) * ‖⨍ z in Metric.closedBall x t, f z‖ ^ 2 := by
  have hcpt : IsCompact (Metric.closedBall x t) := isCompact_closedBall x t
  have hfin : volume (Metric.closedBall x t) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hfi : IntegrableOn f (Metric.closedBall x t) volume := hf.integrableOn_compact hcpt
  obtain ⟨m, hm⟩ : ∃ m : Euc d, m = ⨍ z in Metric.closedBall x t, f z := ⟨_, rfl⟩
  rw [Komlos.Literature.sqExcess_eq, ← hm]
  have hfmi : IntegrableOn (fun y => f y - m) (Metric.closedBall x t) volume :=
    hfi.sub (integrableOn_const hfin)
  have hzero : (∫ y in Metric.closedBall x t, (f y - m)) = 0 := by
    rw [hm]
    exact setAverage_sub_setAverage hfin f
  have hsqi : IntegrableOn (fun y => ‖f y - m‖ ^ 2) (Metric.closedBall x t) volume :=
    (((hf.sub continuousOn_const).norm).pow 2).integrableOn_compact hcpt
  have hinn : IntegrableOn (fun y => (inner ℝ m (f y - m) : ℝ)) (Metric.closedBall x t) volume :=
    (continuousOn_const.inner (hf.sub continuousOn_const)).integrableOn_compact hcpt
  have hrest : IntegrableOn (fun y => (2 : ℝ) * inner ℝ m (f y - m) + ‖m‖ ^ 2)
      (Metric.closedBall x t) volume := (hinn.const_mul 2).add (integrableOn_const hfin)
  have hI : (∫ y in Metric.closedBall x t, ((2 : ℝ) * inner ℝ m (f y - m) + ‖m‖ ^ 2)) =
      volume.real (Metric.closedBall x t) * ‖m‖ ^ 2 := by
    rw [integral_add (hinn.const_mul 2) (integrableOn_const hfin), integral_const_mul,
      integral_inner hfmi, hzero, inner_zero_right, mul_zero, zero_add, setIntegral_const,
      smul_eq_mul]
  have hpt : ∀ y : Euc d,
      ‖f y‖ ^ 2 = ‖f y - m‖ ^ 2 + ((2 : ℝ) * inner ℝ m (f y - m) + ‖m‖ ^ 2) := by
    intro y
    have h := norm_add_sq_real m (f y - m)
    rw [show m + (f y - m) = f y by abel] at h
    rw [h]
    ring
  calc (∫ y in Metric.closedBall x t, ‖f y‖ ^ 2)
      = ∫ y in Metric.closedBall x t,
          (‖f y - m‖ ^ 2 + ((2 : ℝ) * inner ℝ m (f y - m) + ‖m‖ ^ 2)) := by
        simp only [hpt]
    _ = (∫ y in Metric.closedBall x t, ‖f y - m‖ ^ 2) +
          ∫ y in Metric.closedBall x t, ((2 : ℝ) * inner ℝ m (f y - m) + ‖m‖ ^ 2) :=
        integral_add hsqi hrest
    _ = _ := by rw [hI]

/-- **Jensen for the mean of a field**: `|B_t| ‖(f)_{B_t}‖² ≤ ∫_{B_t} ‖f‖²`. -/
theorem volume_real_mul_norm_setAverage_sq_le {f : Euc d → Euc d} {x : Euc d} {t : ℝ} (ht : 0 < t)
    (hf : ContinuousOn f (Metric.closedBall x t)) :
    volume.real (Metric.closedBall x t) * ‖⨍ z in Metric.closedBall x t, f z‖ ^ 2 ≤
      ∫ y in Metric.closedBall x t, ‖f y‖ ^ 2 := by
  have h := setIntegral_norm_sq_eq_sqExcess_add ht hf
  have h0 := Komlos.Literature.sqExcess_nonneg f x t
  linarith

/-- `⨍_s (f - c) = (⨍_s f) - c` on a closed ball of positive radius. -/
theorem setAverage_sub_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {x : Euc d} {t : ℝ} (ht : 0 < t) {f : Euc d → E}
    (hf : IntegrableOn f (Metric.closedBall x t) volume) (c : E) :
    (⨍ y in Metric.closedBall x t, (f y - c)) = (⨍ y in Metric.closedBall x t, f y) - c := by
  have hfin : volume (Metric.closedBall x t) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hreal : (0 : ℝ) < volume.real (Metric.closedBall x t) :=
    Komlos.Literature.volume_real_closedBall_pos' x ht
  rw [setAverage_eq, setAverage_eq, integral_sub hf (integrableOn_const hfin),
    setIntegral_const, smul_sub, smul_smul, inv_mul_cancel₀ hreal.ne', one_smul]

/-- **The distance between two concentric means is controlled by the bigger excess:**
`|B_ρ| ‖(f)_{B_ρ} - (f)_{B_t}‖² ≤ sqExcess f x t` for `0 < ρ ≤ t`. -/
theorem volume_real_mul_norm_setAverage_sub_sq_le {f : Euc d → Euc d} {x : Euc d} {ρ t : ℝ}
    (hρ : 0 < ρ) (hρt : ρ ≤ t) (hf : ContinuousOn f (Metric.closedBall x t)) :
    volume.real (Metric.closedBall x ρ) *
        ‖(⨍ z in Metric.closedBall x ρ, f z) - ⨍ z in Metric.closedBall x t, f z‖ ^ 2 ≤
      Komlos.Literature.sqExcess f x t := by
  have ht : 0 < t := lt_of_lt_of_le hρ hρt
  have hsub : Metric.closedBall x ρ ⊆ Metric.closedBall x t :=
    Metric.closedBall_subset_closedBall hρt
  obtain ⟨m, hm⟩ : ∃ m : Euc d, m = ⨍ z in Metric.closedBall x t, f z := ⟨_, rfl⟩
  have hgc : ContinuousOn (fun y => f y - m) (Metric.closedBall x t) :=
    hf.sub continuousOn_const
  have havg : (⨍ z in Metric.closedBall x ρ, (f z - m)) =
      (⨍ z in Metric.closedBall x ρ, f z) - m :=
    setAverage_sub_const hρ ((hf.mono hsub).integrableOn_compact (isCompact_closedBall x ρ)) m
  rw [← hm, ← havg, Komlos.Literature.sqExcess_eq, ← hm]
  calc volume.real (Metric.closedBall x ρ) * ‖⨍ z in Metric.closedBall x ρ, (f z - m)‖ ^ 2
      ≤ ∫ y in Metric.closedBall x ρ, ‖f y - m‖ ^ 2 :=
        volume_real_mul_norm_setAverage_sq_le hρ (hgc.mono hsub)
    _ ≤ ∫ y in Metric.closedBall x t, ‖f y - m‖ ^ 2 :=
        setIntegral_mono_set ((hgc.norm.pow 2).integrableOn_compact (isCompact_closedBall x t))
          (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE

/-! ### The geometric telescoping of the means -/

/-- **The telescoped bound for the means.**  If the `L²` excess of a continuous field `f` decays
at the Campanato rate `Cdec (t/R)^{d+2β}` on every scale `t ≤ R`, then the mean of `f` over
`B_ρ` stays within `K √(sqExcess f x R / |B_R|)` of the mean over `B_R`, with `K` depending only
on `d`, `Cdec` and `β`.

The proof is the standard geometric series over the halvings of `R`: for comparable radii
`ρ ≤ t ≤ 2ρ` the previous lemma and the decay give
`‖(f)_{B_ρ} - (f)_{B_t}‖ ≤ √(2^d Cdec) (t/R)^β √(sqExcess f x R / |B_R|)`, and the bound
`(t/2/R)^β = (t/R)^β / 2^β` makes the induction on the number of halvings from `R` down to `ρ`
sum to the geometric factor `2^β/(2^β - 1)`. -/
theorem exists_norm_setAverage_sub_setAverage_bound {Cdec β : ℝ} (hCdec : 0 ≤ Cdec)
    (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (f : Euc d → Euc d) (x : Euc d) (R : ℝ), 0 < R →
        ContinuousOn f (Metric.closedBall x R) →
        (∀ t : ℝ, 0 < t → t ≤ R →
          Komlos.Literature.sqExcess f x t ≤
            Cdec * (t / R) ^ ((d : ℝ) + 2 * β) * Komlos.Literature.sqExcess f x R) →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
          ‖(⨍ z in Metric.closedBall x ρ, f z) - ⨍ z in Metric.closedBall x R, f z‖ ≤
            K * Real.sqrt (Komlos.Literature.sqExcess f x R /
              volume.real (Metric.closedBall x R)) := by
  have h2β : (1 : ℝ) < (2 : ℝ) ^ β := Real.one_lt_rpow one_lt_two hβ
  have h2β0 : (0 : ℝ) < (2 : ℝ) ^ β := by positivity
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = Real.sqrt ((2 : ℝ) ^ d * Cdec) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; exact Real.sqrt_nonneg _
  have hc₁2 : c₁ ^ 2 = (2 : ℝ) ^ d * Cdec := by rw [hc₁]; exact Real.sq_sqrt (by positivity)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = c₁ * (2 : ℝ) ^ β / ((2 : ℝ) ^ β - 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact div_nonneg (by positivity) (by linarith)
  have hKc : c₁ ≤ K := by
    rw [hK, le_div_iff₀ (by linarith : (0 : ℝ) < (2 : ℝ) ^ β - 1)]
    nlinarith
  have hKeq : K / (2 : ℝ) ^ β + c₁ = K := by
    have h1 : (2 : ℝ) ^ β - 1 ≠ 0 := by linarith
    rw [hK]
    field_simp
    ring
  refine ⟨K, hK0, ?_⟩
  intro f x R hR hf hdec
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Komlos.Literature.sqExcess f x R := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact Komlos.Literature.sqExcess_nonneg _ _ _
  have hvR : (0 : ℝ) < volume.real (Metric.closedBall x R) :=
    Komlos.Literature.volume_real_closedBall_pos' x hR
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Real.sqrt (A / volume.real (Metric.closedBall x R)) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.sqrt_nonneg _
  have hD2 : D ^ 2 = A / volume.real (Metric.closedBall x R) := by
    rw [hD]; exact Real.sq_sqrt (by positivity)
  have hrp : ∀ t : ℝ, 0 < t → (0 : ℝ) ≤ (t / R) ^ β := fun t ht =>
    Real.rpow_nonneg (div_nonneg ht.le hR.le) _
  -- the comparable-radii step
  have hnear : ∀ ρ t : ℝ, 0 < ρ → ρ ≤ t → t ≤ 2 * ρ → t ≤ R →
      ‖(⨍ z in Metric.closedBall x ρ, f z) - ⨍ z in Metric.closedBall x t, f z‖ ≤
        c₁ * ((t / R) ^ β * D) := by
    intro ρ t hρ hρt ht2 htR
    have ht : 0 < t := lt_of_lt_of_le hρ hρt
    have htR0 : (0 : ℝ) < t / R := div_pos ht hR
    have hP0 : (0 : ℝ) ≤ (t / R) ^ (2 * β) := Real.rpow_nonneg htR0.le _
    have hPsq : (t / R) ^ (2 * β) = ((t / R) ^ β) ^ 2 := by
      rw [two_mul, Real.rpow_add htR0, sq]
    have hsplit : (t / R) ^ ((d : ℝ) + 2 * β) = (t / R) ^ d * (t / R) ^ (2 * β) := by
      rw [Real.rpow_add htR0, Real.rpow_natCast]
    -- the excess side
    have h1 := volume_real_mul_norm_setAverage_sub_sq_le hρ hρt
      (hf.mono (Metric.closedBall_subset_closedBall htR))
    have h2 := hdec t ht htR
    rw [hsplit, ← hA] at h2
    -- the volume side
    have hvρ : volume.real (Metric.closedBall x ρ) =
        (ρ / t) ^ d * volume.real (Metric.closedBall x t) :=
      volume_real_closedBall_eq_ratio x hρ.le ht
    have hvt : volume.real (Metric.closedBall x t) =
        (t / R) ^ d * volume.real (Metric.closedBall x R) :=
      volume_real_closedBall_eq_ratio x ht.le hR
    have hhalf : ((2 : ℝ) ^ d)⁻¹ ≤ (ρ / t) ^ d := by
      rw [← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      rw [le_div_iff₀ ht]
      linarith
    have hu0 : (0 : ℝ) < ((2 : ℝ) ^ d)⁻¹ := by positivity
    have hlow : ((2 : ℝ) ^ d)⁻¹ * ((t / R) ^ d * volume.real (Metric.closedBall x R)) ≤
        volume.real (Metric.closedBall x ρ) := by
      rw [hvρ, hvt]
      exact mul_le_mul_of_nonneg_right hhalf (by positivity)
    -- the squared estimate
    obtain ⟨N, hN⟩ : ∃ N : ℝ,
        N = ‖(⨍ z in Metric.closedBall x ρ, f z) - ⨍ z in Metric.closedBall x t, f z‖ :=
      ⟨_, rfl⟩
    have hN0 : 0 ≤ N := by rw [hN]; exact norm_nonneg _
    rw [← hN] at h1 ⊢
    have hcpos : (0 : ℝ) <
        ((2 : ℝ) ^ d)⁻¹ * ((t / R) ^ d * volume.real (Metric.closedBall x R)) := by
      have : (0 : ℝ) < (t / R) ^ d := by positivity
      positivity
    have hsq : N ^ 2 ≤ (c₁ * ((t / R) ^ β * D)) ^ 2 := by
      have hstep : (((2 : ℝ) ^ d)⁻¹ * ((t / R) ^ d * volume.real (Metric.closedBall x R))) *
          N ^ 2 ≤ Cdec * ((t / R) ^ d * (t / R) ^ (2 * β)) * A := by
        exact le_trans (mul_le_mul_of_nonneg_right hlow (sq_nonneg N)) (le_trans h1 h2)
      have hid : (c₁ * ((t / R) ^ β * D)) ^ 2 =
          (((2 : ℝ) ^ d)⁻¹ * ((t / R) ^ d * volume.real (Metric.closedBall x R)))⁻¹ *
            (Cdec * ((t / R) ^ d * (t / R) ^ (2 * β)) * A) := by
        rw [mul_pow, mul_pow, hc₁2, hD2, ← hPsq]
        field_simp
        try ring
      rw [hid]
      rw [← le_div_iff₀' hcpos] at hstep
      rw [div_eq_inv_mul] at hstep
      exact hstep
    exact edec_le_of_sq_le_sq hsq (by
      have := hrp t ht
      positivity)
  -- the induction on the number of halvings
  have hind : ∀ k : ℕ, ∀ t : ℝ, 0 < t → t ≤ R → ∀ ρ : ℝ, t / 2 ^ k ≤ ρ → ρ ≤ t →
      ‖(⨍ z in Metric.closedBall x ρ, f z) - ⨍ z in Metric.closedBall x t, f z‖ ≤
        K * ((t / R) ^ β * D) := by
    intro k
    induction k with
    | zero =>
      intro t ht htR ρ hρk hρt
      have hρt' : ρ = t := le_antisymm hρt (by simpa using hρk)
      rw [hρt', sub_self, norm_zero]
      exact mul_nonneg hK0 (mul_nonneg (hrp t ht) hD0)
    | succ k ih =>
      intro t ht htR ρ hρk hρt
      have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρk
      by_cases h2 : t ≤ 2 * ρ
      · exact (hnear ρ t hρ0 hρt h2 htR).trans
          (mul_le_mul_of_nonneg_right hKc (mul_nonneg (hrp t ht) hD0))
      · push Not at h2
        have hρk' : t / 2 / 2 ^ k ≤ ρ := by
          rw [div_div, ← pow_succ']
          exact hρk
        have h1 := ih (t / 2) (by positivity) (by linarith) ρ hρk' (by linarith)
        have h3 := hnear (t / 2) t (by positivity) (by linarith) (by linarith) htR
        have e : (t / 2 / R) ^ β = (t / R) ^ β / (2 : ℝ) ^ β := by
          rw [show t / 2 / R = t / R / 2 by ring,
            Real.div_rpow (div_nonneg ht.le hR.le) (by norm_num : (0 : ℝ) ≤ 2)]
        rw [e] at h1
        calc ‖(⨍ z in Metric.closedBall x ρ, f z) - ⨍ z in Metric.closedBall x t, f z‖
            ≤ ‖(⨍ z in Metric.closedBall x ρ, f z) -
                  ⨍ z in Metric.closedBall x (t / 2), f z‖ +
                ‖(⨍ z in Metric.closedBall x (t / 2), f z) -
                  ⨍ z in Metric.closedBall x t, f z‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ K * ((t / R) ^ β / (2 : ℝ) ^ β * D) + c₁ * ((t / R) ^ β * D) := add_le_add h1 h3
          _ = (K / (2 : ℝ) ^ β + c₁) * ((t / R) ^ β * D) := by ring
          _ = K * ((t / R) ^ β * D) := by rw [hKeq]
  intro ρ hρ hρR
  obtain ⟨k, hk⟩ : ∃ k : ℕ, R / 2 ^ k ≤ ρ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R / ρ) (one_lt_two (α := ℝ))
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hρ] at hk
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h := hind k R hR le_rfl ρ hk hρR
  rw [div_self hR.ne', Real.one_rpow, one_mul] at h
  rw [← hA, ← hD]
  exact h

end Komlos.Literature.Regularized
