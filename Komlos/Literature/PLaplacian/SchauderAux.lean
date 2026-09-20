import Komlos.Literature.PLaplacian.RegularityCampanato

/-!
# Real-analysis auxiliaries for the interior Schauder estimate

Quantitative companions of the Campanato machinery of `RegularityCampanato.lean`, used to assemble
the interior Schauder estimate (`RegularitySchauder.lean`, Gilbarg–Trudinger Theorem 8.32) by
Campanato's method.  Nothing here involves an equation: these are statements about an arbitrary
locally integrable (or continuous) function on `ℝ^d`.

The point of every statement below is **uniformity of the constants**: the Campanato criterion
`exists_holder_of_campanato` produces a Hölder constant by an existential statement, whereas a
Schauder estimate needs one constant valid for *every* solution of the family.  Each lemma
therefore either quantifies over the function inside the existential for the constant, or computes
the constant explicitly.

## Main results

* `integral_norm_sub_setAverage_sq_le_const` — the mean minimizes the `L²` deviation.
* `integral_norm_sub_setAverage_sq_mono` — the gradient-energy oscillation
  `ρ ↦ ∫_{B(x,ρ)} ‖f - (f)_{B(x,ρ)}‖²` is monotone, the `hmono` hypothesis of
  `campanato_iteration`.
* `two_mul_setIntegral_le_setIntegral_sq_add` — the elementary `L² → L¹` bound
  `2t ∫_s g ≤ ∫_s g² + t² |s|` (Young, not Cauchy–Schwarz).
* `exists_norm_setAverage_sub_setAverage_le_uniform` — the Campanato chain of ball averages, with
  a constant depending only on `d`, `α` and the Campanato constant.
* `exists_holder_of_campanato_uniform` — the uniform Hölder estimate on the values of a continuous
  function out of a uniform Campanato bound.
-/

open MeasureTheory Set Filter Topology InnerProductSpace

open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Basic estimates for averages over balls -/

section Balls

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The real volume of a closed ball of positive radius is positive. -/
theorem volume_real_closedBall_pos' (x : Euc d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (Metric.closedBall x r) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume x hr).ne'
    measure_closedBall_lt_top.ne

/-- If `‖f - c‖ ≤ K` pointwise on a ball, then the average of `f` over the ball is within `K`
of `c`. -/
theorem norm_setAverage_sub_le_of_forall {f : Euc d → E} {x : Euc d} {r K : ℝ} (hr : 0 < r)
    (hf : IntegrableOn f (Metric.closedBall x r)) {c : E}
    (hbd : ∀ y ∈ Metric.closedBall x r, ‖f y - c‖ ≤ K) :
    ‖(⨍ y in Metric.closedBall x r, f y) - c‖ ≤ K := by
  have hpos := volume_real_closedBall_pos' x hr
  have hfin : volume (Metric.closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have h1 := norm_setAverage_sub_le (Metric.measure_closedBall_pos volume x hr).ne' hfin
    (subset_rfl : Metric.closedBall x r ⊆ Metric.closedBall x r) hfin hf c
  have h2 : ∫ y in Metric.closedBall x r, ‖f y - c‖ ≤
      volume.real (Metric.closedBall x r) * K := by
    have h3 : ∫ y in Metric.closedBall x r, ‖f y - c‖ ≤
        ∫ _y in Metric.closedBall x r, K :=
      setIntegral_mono_on (hf.sub (integrableOn_const hfin)).norm (integrableOn_const hfin)
        measurableSet_closedBall hbd
    rwa [setIntegral_const, smul_eq_mul] at h3
  calc ‖(⨍ y in Metric.closedBall x r, f y) - c‖
      ≤ (volume.real (Metric.closedBall x r))⁻¹ * ∫ y in Metric.closedBall x r, ‖f y - c‖ := h1
    _ ≤ (volume.real (Metric.closedBall x r))⁻¹ * (volume.real (Metric.closedBall x r) * K) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hpos.le)
    _ = K := inv_mul_cancel_left₀ hpos.ne' K

/-- If `‖f - c‖ ≤ K` pointwise on a ball, then `∫_{B} ‖f - c‖² ≤ K² |B|`. -/
theorem setIntegral_norm_sub_sq_le {f : Euc d → E} {x : Euc d} {r K : ℝ}
    (hf : ContinuousOn f (Metric.closedBall x r)) {c : E}
    (hbd : ∀ y ∈ Metric.closedBall x r, ‖f y - c‖ ≤ K) :
    ∫ y in Metric.closedBall x r, ‖f y - c‖ ^ 2 ≤
      K ^ 2 * volume.real (Metric.closedBall x r) := by
  have hcpt : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  have hfin : volume (Metric.closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hsq : IntegrableOn (fun y => ‖f y - c‖ ^ 2) (Metric.closedBall x r) :=
    ((hf.sub continuousOn_const).norm.pow 2).integrableOn_compact hcpt
  have h3 : ∫ y in Metric.closedBall x r, ‖f y - c‖ ^ 2 ≤
      ∫ _y in Metric.closedBall x r, K ^ 2 :=
    setIntegral_mono_on hsq (integrableOn_const hfin) measurableSet_closedBall
      fun y hy => pow_le_pow_left₀ (norm_nonneg _) (hbd y hy) 2
  rwa [setIntegral_const, smul_eq_mul,
    mul_comm (volume.real (Metric.closedBall x r)) (K ^ 2)] at h3

end Balls

/-! ### The mean minimizes the `L²` deviation -/

section Minimizing

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **The mean minimizes the `L²` deviation**: for a function continuous on a closed ball,
`∫_B ‖f - (f)_B‖² ≤ ∫_B ‖f - c‖²` for every constant `c`. -/
theorem integral_norm_sub_setAverage_sq_le_const {f : Euc d → F} {x : Euc d} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (Metric.closedBall x r)) (c : F) :
    ∫ y in Metric.closedBall x r, ‖f y - ⨍ z in Metric.closedBall x r, f z‖ ^ 2 ≤
      ∫ y in Metric.closedBall x r, ‖f y - c‖ ^ 2 := by
  have hcpt : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  have hfin : volume (Metric.closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hreal : (0 : ℝ) < volume.real (Metric.closedBall x r) := volume_real_closedBall_pos' x hr
  have hfi : IntegrableOn f (Metric.closedBall x r) := hf.integrableOn_compact hcpt
  obtain ⟨m, hm⟩ : ∃ m : F, m = ⨍ z in Metric.closedBall x r, f z := ⟨_, rfl⟩
  rw [← hm]
  have hsq : ∀ e : F, IntegrableOn (fun y => ‖f y - e‖ ^ 2) (Metric.closedBall x r) := fun e =>
    ((hf.sub continuousOn_const).norm.pow 2).integrableOn_compact hcpt
  have hfmi : IntegrableOn (fun y => f y - m) (Metric.closedBall x r) :=
    hfi.sub (integrableOn_const hfin)
  have hinnerc : ContinuousOn (fun y => (inner ℝ (m - c) (f y - m) : ℝ))
      (Metric.closedBall x r) := continuousOn_const.inner (hf.sub continuousOn_const)
  have hinner0 : IntegrableOn (fun y => (inner ℝ (m - c) (f y - m) : ℝ))
      (Metric.closedBall x r) := hinnerc.integrableOn_compact hcpt
  have hinner : IntegrableOn (fun y => (2 : ℝ) * inner ℝ (m - c) (f y - m))
      (Metric.closedBall x r) := hinner0.const_mul 2
  have hzero : ∫ y in Metric.closedBall x r, (f y - m) = 0 := by
    rw [integral_sub hfi (integrableOn_const hfin), setIntegral_const, hm, setAverage_eq,
      smul_smul, mul_inv_cancel₀ hreal.ne', one_smul, sub_self]
  have hI : ∫ y in Metric.closedBall x r, (2 : ℝ) * inner ℝ (m - c) (f y - m) = 0 := by
    rw [integral_const_mul, integral_inner hfmi, hzero, inner_zero_right, mul_zero]
  rw [← sub_nonneg, ← integral_sub (hsq c) (hsq m)]
  have hpt : ∀ y : Euc d, ‖f y - c‖ ^ 2 - ‖f y - m‖ ^ 2 =
      (2 : ℝ) * inner ℝ (m - c) (f y - m) + ‖m - c‖ ^ 2 := by
    intro y
    rw [show f y - c = (m - c) + (f y - m) by abel, norm_add_sq_real]
    ring
  simp only [hpt]
  rw [integral_add hinner (integrableOn_const hfin), hI, setIntegral_const, smul_eq_mul, zero_add]
  exact mul_nonneg hreal.le (sq_nonneg _)

/-- **Monotonicity of the mean oscillation energy**: the quantity
`ρ ↦ ∫_{B(x,ρ)} ‖f - (f)_{B(x,ρ)}‖²` is nondecreasing.  This is the `hmono` hypothesis of
`campanato_iteration`. -/
theorem integral_norm_sub_setAverage_sq_mono {f : Euc d → F} {x : Euc d} {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hf : ContinuousOn f (Metric.closedBall x r)) :
    (∫ y in Metric.closedBall x ρ, ‖f y - ⨍ z in Metric.closedBall x ρ, f z‖ ^ 2) ≤
      ∫ y in Metric.closedBall x r, ‖f y - ⨍ z in Metric.closedBall x r, f z‖ ^ 2 := by
  have hsub : Metric.closedBall x ρ ⊆ Metric.closedBall x r :=
    Metric.closedBall_subset_closedBall hρr
  refine le_trans (integral_norm_sub_setAverage_sq_le_const hρ (hf.mono hsub)
    (⨍ z in Metric.closedBall x r, f z)) ?_
  exact setIntegral_mono_set
    (((hf.sub continuousOn_const).norm.pow 2).integrableOn_compact (isCompact_closedBall x r))
    (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE

end Minimizing

/-! ### The elementary `L² → L¹` bound -/

/-- **Young's inequality in integral form**: for a nonnegative `g` and `t > 0`,
`2t ∫_s g ≤ ∫_s g² + t² |s|`.  Applied with `t` a power of the radius this converts an `L²`
Campanato bound into an `L¹` one without invoking Cauchy–Schwarz. -/
theorem two_mul_setIntegral_le_setIntegral_sq_add {s : Set (Euc d)} {g : Euc d → ℝ}
    (hgi : IntegrableOn g s) (hg2 : IntegrableOn (fun y => g y ^ 2) s)
    (hsfin : volume s ≠ ⊤) {t : ℝ} :
    2 * t * (∫ y in s, g y) ≤ (∫ y in s, g y ^ 2) + t ^ 2 * volume.real s := by
  have hpt : ∀ y : Euc d, 2 * t * g y ≤ g y ^ 2 + t ^ 2 := fun y => by
    nlinarith [sq_nonneg (g y - t)]
  have h1 : ∫ y in s, 2 * t * g y ≤ ∫ y in s, (g y ^ 2 + t ^ 2) :=
    setIntegral_mono (hgi.const_mul _) (hg2.add (integrableOn_const hsfin)) hpt
  rwa [integral_const_mul, integral_add hg2 (integrableOn_const hsfin), setIntegral_const,
    smul_eq_mul, mul_comm (volume.real s) (t ^ 2)] at h1

/-- **`L¹` Campanato bound out of an `L²` (Morrey) bound on a ball.**  Combining Young's
inequality with the choice `t = ρ^α` converts the `L²` mean-oscillation bound
`∫_{B(x,ρ)} ‖V - (V)_{B(x,ρ)}‖² ≤ C₃ ρ^{d+2α}` (which is what the Campanato iteration produces)
into the `L¹` bound `∫_{B(x,ρ)} ‖V - (V)_{B(x,ρ)}‖ ≤ ((C₃ + |B₁|)/2) ρ^{d+α}` required by
Campanato's criterion. -/
theorem setIntegral_norm_sub_setAverage_le_of_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {V : Euc d → E} {x : Euc d} {ρ C₃ α : ℝ}
    (hρ : 0 < ρ) (hV : ContinuousOn V (Metric.closedBall x ρ))
    (hsq : (∫ y in Metric.closedBall x ρ, ‖V y - ⨍ z in Metric.closedBall x ρ, V z‖ ^ 2) ≤
      C₃ * ρ ^ ((d : ℝ) + 2 * α)) :
    (∫ y in Metric.closedBall x ρ, ‖V y - ⨍ z in Metric.closedBall x ρ, V z‖) ≤
      (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * ρ ^ ((d : ℝ) + α) := by
  obtain ⟨m, hm⟩ : ∃ m : E, m = ⨍ z in Metric.closedBall x ρ, V z := ⟨_, rfl⟩
  rw [← hm] at hsq ⊢
  have hcpt : IsCompact (Metric.closedBall x ρ) := isCompact_closedBall x ρ
  have hfin : volume (Metric.closedBall x ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hgi : IntegrableOn (fun y => ‖V y - m‖) (Metric.closedBall x ρ) :=
    ((hV.sub continuousOn_const).norm).integrableOn_compact hcpt
  have hg2 : IntegrableOn (fun y => ‖V y - m‖ ^ 2) (Metric.closedBall x ρ) :=
    (((hV.sub continuousOn_const).norm).pow 2).integrableOn_compact hcpt
  have hvol : volume.real (Metric.closedBall x ρ) =
      ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) := volume_real_closedBall x hρ.le
  have hρα : (0 : ℝ) < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have hpow1 : (ρ ^ α) ^ 2 = ρ ^ (2 * α) := by
    rw [pow_two, ← Real.rpow_add hρ, two_mul]
  have hpow2 : ρ ^ (2 * α) * ρ ^ d = ρ ^ ((d : ℝ) + 2 * α) := by
    rw [← Real.rpow_natCast ρ d, ← Real.rpow_add hρ]; congr 1; ring
  have hpow3 : ρ ^ ((d : ℝ) + α) * ρ ^ α = ρ ^ ((d : ℝ) + 2 * α) := by
    rw [← Real.rpow_add hρ]; congr 1; ring
  have hkey := two_mul_setIntegral_le_setIntegral_sq_add hgi hg2 hfin (t := ρ ^ α)
  have hbig : 2 * ρ ^ α * (∫ y in Metric.closedBall x ρ, ‖V y - m‖) ≤
      (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) * ρ ^ ((d : ℝ) + 2 * α) := by
    refine le_trans hkey ?_
    rw [hvol, hpow1]
    calc (∫ y in Metric.closedBall x ρ, ‖V y - m‖ ^ 2) +
          ρ ^ (2 * α) * (ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))
        ≤ C₃ * ρ ^ ((d : ℝ) + 2 * α) +
            ρ ^ (2 * α) * (ρ ^ d * volume.real (Metric.closedBall (0 : Euc d) 1)) := by
          linarith [hsq]
      _ = C₃ * ρ ^ ((d : ℝ) + 2 * α) +
            volume.real (Metric.closedBall (0 : Euc d) 1) * (ρ ^ (2 * α) * ρ ^ d) := by ring
      _ = (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) * ρ ^ ((d : ℝ) + 2 * α) := by
          rw [hpow2]; ring
  have hne : (2 : ℝ) * ρ ^ α ≠ 0 := ne_of_gt (by linarith)
  have hstep : 2 * ρ ^ α * (∫ y in Metric.closedBall x ρ, ‖V y - m‖) ≤
      2 * ρ ^ α *
        ((C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * ρ ^ ((d : ℝ) + α)) := by
    refine hbig.trans (le_of_eq ?_)
    rw [← hpow3]; ring
  calc (∫ y in Metric.closedBall x ρ, ‖V y - m‖)
      = (2 * ρ ^ α)⁻¹ * (2 * ρ ^ α * ∫ y in Metric.closedBall x ρ, ‖V y - m‖) :=
        (inv_mul_cancel_left₀ hne _).symm
    _ ≤ (2 * ρ ^ α)⁻¹ * (2 * ρ ^ α *
          ((C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * ρ ^ ((d : ℝ) + α))) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 (by linarith))
    _ = (C₃ + volume.real (Metric.closedBall (0 : Euc d) 1)) / 2 * ρ ^ ((d : ℝ) + α) :=
        inv_mul_cancel_left₀ hne _

/-! ### The Campanato chain with a uniform constant -/

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **One Campanato step, localized.**  Exactly `norm_setAverage_sub_le_of_campanato`
(`RegularityCampanato`), but with the global `LocallyIntegrable g` replaced by integrability on the
single ball that the proof actually uses.  This matters for the Schauder estimate, where the
gradient of the solution is only known to be continuous on the ball where the equation holds. -/
theorem norm_setAverage_sub_le_of_campanato' {g : Euc d → E} {x z : Euc d} {s t C α : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hts : t ≤ 2 * s)
    (hsub : Metric.closedBall z s ⊆ Metric.closedBall x t)
    (hgt : IntegrableOn g (Metric.closedBall x t)) (hC : 0 ≤ C) {m : E}
    (hm : ∫ y in Metric.closedBall x t, ‖g y - m‖ ≤ C * t ^ ((d : ℝ) + α)) :
    ‖(⨍ y in Metric.closedBall z s, g y) - m‖ ≤
      C * 2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1) * t ^ α := by
  have hω := volume_real_closedBall_pos (d := d)
  have hvol := volume_real_closedBall z hs.le
  have h1 := norm_setAverage_sub_le (Metric.measure_closedBall_pos volume z hs).ne'
    measure_closedBall_lt_top.ne hsub measure_closedBall_lt_top.ne hgt m
  have hpow : t ^ ((d : ℝ) + α) = t ^ d * t ^ α := by rw [Real.rpow_add ht, Real.rpow_natCast]
  have htd : t ^ d ≤ 2 ^ d * s ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ ht.le hts d
  calc ‖(⨍ y in Metric.closedBall z s, g y) - m‖
      ≤ (volume.real (Metric.closedBall z s))⁻¹ * ∫ y in Metric.closedBall x t, ‖g y - m‖ := h1
    _ ≤ (s ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))⁻¹ *
          (C * (2 ^ d * s ^ d * t ^ α)) := by
        rw [hvol]
        refine mul_le_mul_of_nonneg_left (hm.trans ?_) (by positivity)
        rw [hpow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htd (Real.rpow_nonneg ht.le _)) hC
    _ = C * 2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1) * t ^ α := by
        field_simp

/-- **Campanato chain along concentric balls, uniformly in the function.**  This is
`exists_norm_setAverage_sub_setAverage_le` (`RegularityCampanato`) with the existential for the
constant pulled outside `C`, `R₀`, `g`, and `S`: the coefficient
`2 · 2^d ω⁻¹ 2^α / (2^α - 1)` depends only on `d` and `α`, while the bound is linear in the
Campanato constant `C`. -/
theorem exists_norm_setAverage_sub_setAverage_le_scaled {α : ℝ} (hα : 0 < α) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (C : ℝ), 0 ≤ C → ∀ (R₀ : ℝ)
      (g : Euc d → E) (S : Set (Euc d)),
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ → IntegrableOn g (Metric.closedBall x r)) →
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ m : E, ∫ y in Metric.closedBall x r, ‖g y - m‖ ≤ C * r ^ ((d : ℝ) + α)) →
      ∀ x ∈ S, ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ R₀ →
        ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖ ≤
          B * C * t ^ α := by
  have hω := volume_real_closedBall_pos (d := d)
  have h2α : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow one_lt_two hα
  have hden : 0 < (2 : ℝ) ^ α - 1 := by linarith
  refine ⟨2 * (2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1)) *
    2 ^ α / (2 ^ α - 1), by positivity, ?_⟩
  intro C hC R₀
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ,
      C₁ = C * 2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * C₁ * 2 ^ α / (2 ^ α - 1) := ⟨_, rfl⟩
  have hB2 : 2 * C₁ ≤ B := by
    rw [hB, le_div_iff₀ (by linarith)]
    nlinarith
  have hB0 : 0 ≤ B := by linarith
  have hBq : B / 2 ^ α + 2 * C₁ = B := by
    have h2 : (2 : ℝ) ^ α - 1 ≠ 0 := by linarith
    have h3 : (2 : ℝ) ^ α ≠ 0 := by positivity
    rw [hB]
    field_simp
    ring
  intro g S hint hcamp x hx
  -- comparable radii
  have hnear : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 2 * s → t ≤ R₀ →
      ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖ ≤
        2 * C₁ * t ^ α := by
    intro s t hs hst hts htR
    have ht : 0 < t := hs.trans_le hst
    obtain ⟨m, hm⟩ := hcamp x hx t ht htR
    have h1 := norm_setAverage_sub_le_of_campanato' hs ht hts
      (Metric.closedBall_subset_closedBall hst) (hint x hx t ht htR) hC hm
    have h2 := norm_setAverage_sub_le_of_campanato' ht ht (by linarith) subset_rfl
      (hint x hx t ht htR) hC hm
    rw [← hC₁] at h1 h2
    calc ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖
        = ‖((⨍ y in Metric.closedBall x s, g y) - m) -
            ((⨍ y in Metric.closedBall x t, g y) - m)‖ := by
          congr 1
          abel
      _ ≤ ‖(⨍ y in Metric.closedBall x s, g y) - m‖ +
            ‖(⨍ y in Metric.closedBall x t, g y) - m‖ := norm_sub_le _ _
      _ ≤ C₁ * t ^ α + C₁ * t ^ α := add_le_add h1 h2
      _ = 2 * C₁ * t ^ α := by ring
  have hind : ∀ k : ℕ, ∀ t : ℝ, 0 < t → t ≤ R₀ → ∀ s : ℝ, t / 2 ^ k ≤ s → s ≤ t →
      ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖ ≤
        B * t ^ α := by
    intro k
    induction k with
    | zero =>
      intro t ht htR s hs hst
      have hst' : s = t := le_antisymm hst (by simpa using hs)
      rw [hst', sub_self, norm_zero]
      exact mul_nonneg hB0 (Real.rpow_nonneg ht.le _)
    | succ k ih =>
      intro t ht htR s hs hst
      have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
      by_cases h2 : t ≤ 2 * s
      · exact (hnear s t hs0 hst h2 htR).trans
          (mul_le_mul_of_nonneg_right hB2 (Real.rpow_nonneg ht.le _))
      · push Not at h2
        have hs' : t / 2 / 2 ^ k ≤ s := by
          rw [div_div, ← pow_succ']
          exact hs
        have h1 := ih (t / 2) (by positivity) (by linarith) s hs' (by linarith)
        have h3 := hnear (t / 2) t (by positivity) (by linarith) (by linarith) htR
        have e : (t / 2) ^ α = t ^ α / 2 ^ α := Real.div_rpow ht.le zero_le_two α
        calc ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖
            ≤ ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x (t / 2), g y‖ +
                ‖(⨍ y in Metric.closedBall x (t / 2), g y) -
                  ⨍ y in Metric.closedBall x t, g y‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ B * (t / 2) ^ α + 2 * C₁ * t ^ α := add_le_add h1 h3
          _ = (B / 2 ^ α + 2 * C₁) * t ^ α := by rw [e]; ring
          _ = B * t ^ α := by rw [hBq]
  intro s t hs hst htR
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t / 2 ^ k ≤ s := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (t / s) one_lt_two
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hs] at hk
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc _ ≤ B * t ^ α := hind k t (hs.trans_le hst) htR s hk hst
       _ = _ := by rw [hB, hC₁]; ring

/-- The uniform average-chain estimate with the Campanato constant absorbed into the
Hölder constant. The stronger scaled version exposes linear dependence on `C`. -/
theorem exists_norm_setAverage_sub_setAverage_le_uniform {α C R₀ : ℝ} (hα : 0 < α) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g : Euc d → E) (S : Set (Euc d)),
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ → IntegrableOn g (Metric.closedBall x r)) →
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ m : E, ∫ y in Metric.closedBall x r, ‖g y - m‖ ≤ C * r ^ ((d : ℝ) + α)) →
      ∀ x ∈ S, ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ R₀ →
        ‖(⨍ y in Metric.closedBall x s, g y) - ⨍ y in Metric.closedBall x t, g y‖ ≤
          B * t ^ α := by
  obtain ⟨B, hB, h⟩ :=
    exists_norm_setAverage_sub_setAverage_le_scaled (d := d) (E := E) hα
  exact ⟨B * C, mul_nonneg hB hC, h C hC R₀⟩

/-- **Uniform Hölder estimate from a uniform Campanato bound.**  If, for every `x` in `S`, the
mean oscillations of `f` on the balls `B(x, r)` with `r ≤ R₀` are bounded by `C r^{d+α}`, and if
the averages of `f` over small balls centred at `x ∈ S` approach the *value* `f x` (which holds
whenever `f` is continuous at `x`), then `‖f x - f y‖ ≤ B |x - y|^α` for `x, y ∈ S` at distance
at most `R₀ / 2`. The conclusion keeps the factor `C` explicit, so `B` depends only on
`d` and `α` and is chosen before the radius cutoff `R₀`. -/
theorem exists_holder_of_campanato_scaled {α : ℝ} (hα : 0 < α) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (C : ℝ), 0 ≤ C → ∀ (R₀ : ℝ)
      (f : Euc d → E) (S : Set (Euc d)),
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ → IntegrableOn f (Metric.closedBall x r)) →
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ m : E, ∫ y in Metric.closedBall x r, ‖f y - m‖ ≤ C * r ^ ((d : ℝ) + α)) →
      (∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∀ u : ℝ, 0 < u → ∃ s : ℝ, 0 < s ∧ s ≤ u ∧
        ‖(⨍ y in Metric.closedBall x s, f y) - f x‖ ≤ ε) →
      ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 < t → dist x y ≤ t → 2 * t ≤ R₀ →
        ‖f x - f y‖ ≤ B * C * t ^ α := by
  obtain ⟨Bbase, hBbase, hchain⟩ :=
    exists_norm_setAverage_sub_setAverage_le_scaled (d := d) (E := E) hα
  have hω := volume_real_closedBall_pos (d := d)
  refine ⟨Bbase * (2 ^ α + 1) +
    2 * (2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1)) * 2 ^ α, by positivity, ?_⟩
  intro C hC R₀
  let B₀ : ℝ := Bbase * C
  have hB₀ := hchain C hC R₀
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ,
      C₁ = C * 2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1) := ⟨_, rfl⟩
  intro f S hint hcamp hlim x hx y hy t ht hxy h2t
  have htR : t ≤ R₀ := by linarith
  have h2tpos : (0 : ℝ) < 2 * t := by linarith
  -- **Step A**: the value `f z` is within `B₀ u^α` of the average of `f` on `B(z, u)`.
  have hstepA : ∀ z ∈ S, ∀ u : ℝ, 0 < u → u ≤ R₀ →
      ‖f z - ⨍ w in Metric.closedBall z u, f w‖ ≤ B₀ * u ^ α := by
    intro z hz u hu huR
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨s, hs, hsu, hsε⟩ := hlim z hz ε hε u hu
    calc ‖f z - ⨍ w in Metric.closedBall z u, f w‖
        ≤ ‖f z - ⨍ w in Metric.closedBall z s, f w‖ +
            ‖(⨍ w in Metric.closedBall z s, f w) - ⨍ w in Metric.closedBall z u, f w‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + B₀ * u ^ α := by
          refine add_le_add ?_ (hB₀ f S hint hcamp z hz s u hs hsu huR)
          rw [norm_sub_rev]
          exact hsε
      _ = B₀ * u ^ α + ε := by ring
  -- **Step B**: compare the two averages through the Campanato constant on `B(x, 2t)`.
  obtain ⟨m, hmm⟩ := hcamp x hx (2 * t) h2tpos h2t
  have hAx : ‖(⨍ w in Metric.closedBall x (2 * t), f w) - m‖ ≤ C₁ * (2 * t) ^ α := by
    have h := norm_setAverage_sub_le_of_campanato' h2tpos h2tpos (by linarith) subset_rfl
      (hint x hx (2 * t) h2tpos h2t) hC hmm
    rwa [← hC₁] at h
  have hAy : ‖(⨍ w in Metric.closedBall y t, f w) - m‖ ≤ C₁ * (2 * t) ^ α := by
    have hsub : Metric.closedBall y t ⊆ Metric.closedBall x (2 * t) := by
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ ≤ t + t := add_le_add hz (by rwa [dist_comm])
        _ = 2 * t := by ring
    have h := norm_setAverage_sub_le_of_campanato' ht h2tpos (by linarith) hsub
      (hint x hx (2 * t) h2tpos h2t) hC hmm
    rwa [← hC₁] at h
  have hab : ‖(⨍ w in Metric.closedBall x (2 * t), f w) -
      ⨍ w in Metric.closedBall y t, f w‖ ≤ 2 * (C₁ * (2 * t) ^ α) := by
    calc ‖(⨍ w in Metric.closedBall x (2 * t), f w) - ⨍ w in Metric.closedBall y t, f w‖
        ≤ ‖(⨍ w in Metric.closedBall x (2 * t), f w) - m‖ +
            ‖m - ⨍ w in Metric.closedBall y t, f w‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C₁ * (2 * t) ^ α + C₁ * (2 * t) ^ α := by
          refine add_le_add hAx ?_
          rw [norm_sub_rev]
          exact hAy
      _ = 2 * (C₁ * (2 * t) ^ α) := by ring
  have hexp : ((2 : ℝ) * t) ^ α = 2 ^ α * t ^ α := Real.mul_rpow zero_le_two ht.le
  calc ‖f x - f y‖
      ≤ ‖f x - ⨍ w in Metric.closedBall x (2 * t), f w‖ +
          ‖(⨍ w in Metric.closedBall x (2 * t), f w) - f y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖f x - ⨍ w in Metric.closedBall x (2 * t), f w‖ +
          (‖(⨍ w in Metric.closedBall x (2 * t), f w) - ⨍ w in Metric.closedBall y t, f w‖ +
            ‖(⨍ w in Metric.closedBall y t, f w) - f y‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ B₀ * (2 * t) ^ α + (2 * (C₁ * (2 * t) ^ α) + B₀ * t ^ α) := by
        refine add_le_add (hstepA x hx (2 * t) h2tpos h2t) (add_le_add hab ?_)
        rw [norm_sub_rev]
        exact hstepA y hy t ht htR
    _ = (Bbase * (2 ^ α + 1) +
        2 * (2 ^ d / volume.real (Metric.closedBall (0 : Euc d) 1)) * 2 ^ α) * C * t ^ α := by
          rw [hexp, hC₁]
          dsimp [B₀]
          ring

/-- The uniform Hölder estimate with the Campanato constant absorbed into the resulting
constant. The stronger scaled version chooses its constant before both `C` and `R₀`. -/
theorem exists_holder_of_campanato_uniform {α C R₀ : ℝ} (hα : 0 < α) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : Euc d → E) (S : Set (Euc d)),
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ → IntegrableOn f (Metric.closedBall x r)) →
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ m : E, ∫ y in Metric.closedBall x r, ‖f y - m‖ ≤ C * r ^ ((d : ℝ) + α)) →
      (∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∀ u : ℝ, 0 < u → ∃ s : ℝ, 0 < s ∧ s ≤ u ∧
        ‖(⨍ y in Metric.closedBall x s, f y) - f x‖ ≤ ε) →
      ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 < t → dist x y ≤ t → 2 * t ≤ R₀ →
        ‖f x - f y‖ ≤ B * t ^ α := by
  obtain ⟨B, hB, h⟩ := exists_holder_of_campanato_scaled (d := d) (E := E) hα
  exact ⟨B * C, mul_nonneg hB hC, h C hC R₀⟩

end Uniform

end Komlos.Literature
