import Komlos.Literature.Regularized.VariationalTruncation

/-!
# The minimizer is essentially bounded

Lane `L1` (`reg/variational`), the frozen lane statement `IsRegMinimizer.exists_bound`
(formerly a named `sorry` in `Interface.lean`, proved here).

## Truncation comparison (Revision 2 (i))

Let `u` be a minimizer, `M ≥ 1`, `u_M = min (u, M)` and `T = ∫ u_M²`.  Then
`z = T^{-1/2} u_M` is an admissible competitor, and the scaling relations

`Q(λ s, λ ξ) = λ² Q(s, ξ)`,  `P(λ s) = λ² P(s) + λ² (κ/2) (log λ) s²`

(`homogeneousDensity_two_smul`, `entropyPotential_two_smul`) turn `m ≤ E(z)` into

`T·m + (κ/4) T log T ≤ ∫ [Q(u_M, ∇u_M) + P(u_M)]`.

On the other hand the pointwise comparison (`truncation_pointwise_le`)

`Q(u_M, ∇u_M) + P(u_M) ≤ Q(u, ∇u) + P(u) - (u² - u_M²)(Ψ 0 + (κ/2) log M)`

— which uses `Q(s, ξ) ≥ Ψ 0 · s²` and `log u ≥ log M` on `{u > M}` — integrates to

`∫ [Q(u_M, ∇u_M) + P(u_M)] ≤ m - (1 - T)(Ψ 0 + (κ/2) log M)`.

Combining and using `-T log T ≤ 1 - T` gives `(1 - T)(Ψ 0 + (κ/2) log M - m - κ/4) ≤ 0`, so
for `M` large `T = 1`, i.e. `u = u_M` a.e., i.e. `u ≤ M` a.e.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### Scaling of the two densities -/

/-- The kinetic density is jointly `2`-homogeneous. -/
theorem homogeneousDensity_two_smul (Ψ : Euc d → ℝ) {lam : ℝ} (hlam : lam ≠ 0) (s : ℝ)
    (ξ : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ (lam * s) (lam • ξ)
      = lam ^ 2 * Korevaar.homogeneousDensity 2 Ψ s ξ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [homogeneousDensity_two]
  · rw [homogeneousDensity_two, homogeneousDensity_two]
    have h1 : (lam * s)⁻¹ • (lam • ξ) = s⁻¹ • ξ := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [h1]
    ring

/-- The entropy potential under scaling. -/
theorem entropyPotential_two_smul {κ lam : ℝ} (hlam : 0 < lam) {s : ℝ} (hs : 0 ≤ s) :
    Korevaar.entropyPotential 2 κ (lam * s)
      = lam ^ 2 * Korevaar.entropyPotential 2 κ s + lam ^ 2 * (κ / 2 * Real.log lam) * s ^ 2 := by
  rw [entropyPotential_two κ (mul_nonneg hlam.le hs), entropyPotential_two κ hs]
  rcases hs.lt_or_eq with hpos | hzero
  · rw [Real.log_mul hlam.ne' hpos.ne']
    ring
  · rw [← hzero]
    simp

/-! ### The pointwise truncation comparison -/

/-- **The pointwise truncation comparison.**  With `A = Ψ 0 + (κ/2) log M` and `M ≥ 1`,
truncating at level `M` lowers the density by at least `(u² - u_M²) A`. -/
theorem truncation_pointwise_le (h : IsRegProfileWith Ψ c C) (hκ : 0 ≤ κ) {M : ℝ} (hM : 1 ≤ M)
    {s : ℝ} (hs : 0 ≤ s) {ξ : Euc d} (hξ : s = 0 → ξ = 0) :
    Korevaar.homogeneousDensity 2 Ψ (min s M) (if s ≤ M then ξ else 0)
        + Korevaar.entropyPotential 2 κ (min s M)
      ≤ Korevaar.homogeneousDensity 2 Ψ s ξ + Korevaar.entropyPotential 2 κ s
        - (s ^ 2 - min s M ^ 2) * (Ψ 0 + κ / 2 * Real.log M) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  by_cases hle : s ≤ M
  · rw [if_pos hle, min_eq_left hle]
    simp
  · push Not at hle
    rw [if_neg (not_le.2 hle), min_eq_right hle.le]
    have hQ : Ψ 0 * s ^ 2 ≤ Korevaar.homogeneousDensity 2 Ψ s ξ := by
      have hb := h.homogeneousDensity_two_lower hs hξ
      have := mul_nonneg (by linarith [h.c_pos] : (0:ℝ) ≤ c / 2) (sq_nonneg ‖ξ‖)
      linarith
    have hMd : Korevaar.homogeneousDensity 2 Ψ M (0 : Euc d) = Ψ 0 * M ^ 2 := by
      rw [homogeneousDensity_two]
      simp [mul_comm]
    have hlog : Real.log M ≤ Real.log s := Real.log_le_log hM0 hle.le
    have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have hent : Korevaar.entropyPotential 2 κ M + κ / 2 * (s ^ 2 - M ^ 2) * Real.log M
        ≤ Korevaar.entropyPotential 2 κ s := by
      rw [entropyPotential_two κ hM0.le, entropyPotential_two κ hs]
      linarith [mul_le_mul_of_nonneg_left hlog
        (mul_nonneg (by linarith : (0:ℝ) ≤ κ / 2) hs2)]
    rw [hMd]
    have hks : (0 : ℝ) ≤ κ / 2 * s ^ 2 := mul_nonneg (by linarith) hs2
    have hkm : (0 : ℝ) ≤ κ / 2 * M ^ 2 := mul_nonneg (by linarith) (sq_nonneg M)
    linarith [hQ, hent, hks, hkm]

/-! ### The `L^∞` bound -/

/-- **(L1, `reg/variational`)** The minimizer is essentially bounded: truncation at a large
level lowers the energy, because the entropy potential is increasing past `s₀`.  This is the
frozen statement `IsRegMinimizer.exists_bound` of the interface. -/
theorem IsRegMinimizer.exists_bound (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K)
    (hu : IsRegMinimizer 2 κ Ψ K u) : ∃ M : ℝ, ∀ᵐ x, u x ≤ M := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  set m : ℝ := regMin 2 κ Ψ K with hm
  set M : ℝ := max 1 (Real.exp (2 / κ * (m + κ / 4 - Ψ 0) + 1)) with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  refine ⟨M, ?_⟩
  -- the bracket is positive
  have hbracket : 0 < Ψ 0 + κ / 2 * Real.log M - m - κ / 4 := by
    have hexp : Real.exp (2 / κ * (m + κ / 4 - Ψ 0) + 1) ≤ M := le_max_right _ _
    have hlog : 2 / κ * (m + κ / 4 - Ψ 0) + 1 ≤ Real.log M := by
      rw [← Real.log_exp (2 / κ * (m + κ / 4 - Ψ 0) + 1)]
      exact Real.log_le_log (Real.exp_pos _) hexp
    have h1 : κ / 2 * (2 / κ * (m + κ / 4 - Ψ 0) + 1) ≤ κ / 2 * Real.log M :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    have h2 : κ / 2 * (2 / κ * (m + κ / 4 - Ψ 0) + 1) = m + κ / 4 - Ψ 0 + κ / 2 := by
      field_simp
      try ring
    rw [h2] at h1
    linarith
  -- the truncation
  have hKm := hK.measurableSet'
  have hKv := hK.volume_ne_top
  obtain ⟨huMmem, -⟩ := memW0_min hKm hKv hu.memW0 hu.nonneg hM0.le
  have huMg := ae_weakGrad_min hKm hKv hu.memW0 hu.nonneg hM0
  have huM0 : ∀ x, 0 ≤ min (u x) M := fun x => le_min (hu.nonneg x) hM0.le
  have huMle : ∀ x, min (u x) M ≤ u x := fun x => min_le_left _ _
  have huMsq : Integrable (fun x => min (u x) M ^ 2) volume := by
    refine Integrable.mono' hu.integrable_sq
      (((huMmem.memLp.aestronglyMeasurable.aemeasurable).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [huM0 x, huMle x]
  set T : ℝ := ∫ x, min (u x) M ^ 2 with hTdef
  have hTnn : 0 ≤ T := integral_nonneg fun x => sq_nonneg _
  have hTle : T ≤ 1 := by
    rw [← hu.integral_sq]
    exact integral_mono huMsq hu.integrable_sq fun x => by nlinarith [huM0 x, huMle x]
  have hTpos : 0 < T := by
    rcases hTnn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have h0 : (fun x => min (u x) M ^ 2) =ᵐ[volume] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) huMsq).1 heq.symm
      have hz : (fun x => u x ^ 2) =ᵐ[volume] (fun _ => (0 : ℝ)) := by
        filter_upwards [h0] with x hx
        have hx1 : min (u x) M ^ 2 = 0 := hx
        have hx0 : min (u x) M = 0 := by
          have hsq0 := congrArg Real.sqrt hx1
          rwa [Real.sqrt_sq (huM0 x), Real.sqrt_zero] at hsq0
        have hux : u x = 0 := by
          rcases le_or_gt (u x) M with hle | hgt
          · rwa [min_eq_left hle] at hx0
          · rw [min_eq_right hgt.le] at hx0; linarith
        rw [hux]; ring
      have h1 := hu.integral_sq
      rw [integral_congr_ae hz] at h1
      simp at h1
  set t : ℝ := Real.sqrt T with htdef
  have ht0 : 0 < t := Real.sqrt_pos.2 hTpos
  have ht2 : t ^ 2 = T := Real.sq_sqrt hTnn
  -- the rescaled competitor
  set z : Euc d → ℝ := fun x => t⁻¹ * min (u x) M with hzdef
  have hzx : ∀ x, z x = t⁻¹ * min (u x) M := fun _ => rfl
  have hzmem : MemW0 2 K z :=
    (huMmem.smul t⁻¹).congr (Eventually.of_forall fun _ => rfl)
  have hzg : weakGrad z =ᵐ[volume] fun x => t⁻¹ • weakGrad (fun y => min (u y) M) x :=
    ((huMmem.hasWeakGradient.smul t⁻¹).congr_left
      (Eventually.of_forall fun _ => rfl)).weakGrad_ae_eq
  have hzsq : ∀ x, T * z x ^ 2 = min (u x) M ^ 2 := by
    intro x
    rw [hzx, ← ht2]
    field_simp
  have hzint : ∫ x, z x ^ 2 = 1 := by
    have heq : (∫ x, T * z x ^ 2) = ∫ x, min (u x) M ^ 2 :=
      integral_congr_ae (Eventually.of_forall hzsq)
    rw [integral_const_mul, ← hTdef] at heq
    have h2 : T * (∫ x, z x ^ 2) = T * 1 := by rw [mul_one]; exact heq
    exact mul_left_cancel₀ hTpos.ne' h2
  have hzadm : IsRegAdmissible 2 K z := by
    refine ⟨hzmem, fun x => mul_nonneg (le_of_lt (inv_pos.2 ht0)) (huM0 x), ?_, ?_⟩
    · intro x hx
      have hux : u x = 0 := hu.eq_zero_of_notMem x hx
      rw [hzx, hux, min_eq_left hM0.le, mul_zero]
    · rw [← hzint]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show z x ^ (2 : ℝ) = z x ^ 2
      exact rpow_two_eq _
  -- the pointwise comparison, transported to `z`
  set A : ℝ := Ψ 0 + κ / 2 * Real.log M with hA
  have hkey : ∀ᵐ x, T * (Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x)
        + Korevaar.entropyPotential 2 κ (z x)) + T * (κ / 2 * Real.log t) * z x ^ 2
      ≤ Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)
        + Korevaar.entropyPotential 2 κ (u x) - (u x ^ 2 - T * z x ^ 2) * A := by
    filter_upwards [huMg, hzg, hu.ae_weakGrad_eq_zero hK] with x hgM hgz hgu
    have huMz : min (u x) M = t * z x := by
      rw [hzx x, ← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul]
    have hgMz : weakGrad (fun y => min (u y) M) x = t • weakGrad z x := by
      rw [hgz, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
    have hQ : T * Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x)
        = Korevaar.homogeneousDensity 2 Ψ (min (u x) M)
            (weakGrad (fun y => min (u y) M) x) := by
      rw [huMz, hgMz, homogeneousDensity_two_smul Ψ ht0.ne' (z x) (weakGrad z x), ht2]
    have hzx0 : 0 ≤ z x := mul_nonneg (le_of_lt (inv_pos.2 ht0)) (huM0 x)
    have hP : T * Korevaar.entropyPotential 2 κ (z x) + T * (κ / 2 * Real.log t) * z x ^ 2
        = Korevaar.entropyPotential 2 κ (min (u x) M) := by
      rw [huMz, entropyPotential_two_smul ht0 hzx0, ht2]
      try ring
    have hcomp := truncation_pointwise_le h hκ.le hM1 (hu.nonneg x) (ξ := weakGrad u x) hgu
    rw [hzsq x]
    calc T * (Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x)
            + Korevaar.entropyPotential 2 κ (z x)) + T * (κ / 2 * Real.log t) * z x ^ 2
        = Korevaar.homogeneousDensity 2 Ψ (min (u x) M)
              (weakGrad (fun y => min (u y) M) x)
            + Korevaar.entropyPotential 2 κ (min (u x) M) := by
          rw [← hQ, ← hP]; ring
      _ ≤ Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)
            + Korevaar.entropyPotential 2 κ (u x) - (u x ^ 2 - min (u x) M ^ 2) * A := by
          rw [hgM]; exact hcomp
  -- integrate
  have hIz := hzadm.integrable_kinetic h hK
  have hJz := hzadm.integrable_entropy hκ.le hK
  have hIu := hu.integrable_kinetic h hK
  have hJu := hu.integrable_entropy hκ.le hK
  have hz2 := hzadm.integrable_sq
  have hu2 := hu.integrable_sq
  have hA1 : Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x)
      + Korevaar.entropyPotential 2 κ (z x)) volume :=
    (hIz.add hJz).congr (Eventually.of_forall fun _ => rfl)
  have hA2 : Integrable (fun x => T * (Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x)
      + Korevaar.entropyPotential 2 κ (z x))) volume := hA1.const_mul T
  have hA3 : Integrable (fun x => T * (κ / 2 * Real.log t) * z x ^ 2) volume := hz2.const_mul _
  have hL : Integrable (fun x => T * (Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x)
      + Korevaar.entropyPotential 2 κ (z x)) + T * (κ / 2 * Real.log t) * z x ^ 2) volume :=
    (hA2.add hA3).congr (Eventually.of_forall fun _ => rfl)
  have hB1 : Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)
      + Korevaar.entropyPotential 2 κ (u x)) volume :=
    (hIu.add hJu).congr (Eventually.of_forall fun _ => rfl)
  have hB2 : Integrable (fun x => u x ^ 2 - T * z x ^ 2) volume :=
    (hu2.sub (hz2.const_mul T)).congr (Eventually.of_forall fun _ => rfl)
  have hB3 : Integrable (fun x => (u x ^ 2 - T * z x ^ 2) * A) volume := hB2.mul_const A
  have hR : Integrable (fun x => Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)
      + Korevaar.entropyPotential 2 κ (u x) - (u x ^ 2 - T * z x ^ 2) * A) volume :=
    (hB1.sub hB3).congr (Eventually.of_forall fun _ => rfl)
  have hint := integral_mono_ae hL hR hkey
  have eL : (∫ x, T * (Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x)
        + Korevaar.entropyPotential 2 κ (z x)) + T * (κ / 2 * Real.log t) * z x ^ 2)
      = T * ((∫ x, Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x))
          + ∫ x, Korevaar.entropyPotential 2 κ (z x)) + T * (κ / 2 * Real.log t) := by
    rw [integral_add hA2 hA3, integral_const_mul, integral_const_mul, hzint, mul_one,
      integral_add hIz hJz]
    try ring
  have eR : (∫ x, Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)
        + Korevaar.entropyPotential 2 κ (u x) - (u x ^ 2 - T * z x ^ 2) * A)
      = ((∫ x, Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x))
          + ∫ x, Korevaar.entropyPotential 2 κ (u x)) - (1 - T) * A := by
    rw [integral_sub hB1 hB3, integral_mul_const,
      integral_sub hu2 (hz2.const_mul T), integral_const_mul, hzint, hu.integral_sq,
      integral_add hIu hJu, mul_one]
    try ring
  rw [eL, eR] at hint
  have hEz : m ≤ (∫ x, Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x))
      + ∫ x, Korevaar.entropyPotential 2 κ (z x) :=
    regMin_le_regEnergy h hκ.le hK hzadm
  have hEu : (∫ x, Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x))
      + ∫ x, Korevaar.entropyPotential 2 κ (u x) = m := hu.energy_eq
  -- the elementary inequality `-T log T ≤ 1 - T`
  have hTlog : -(T * Real.log T) ≤ 1 - T := by
    have h1 : 1 - T⁻¹ ≤ Real.log T := by
      have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hTpos)
      rw [Real.log_inv] at h2
      linarith
    have h3 : T * (1 - T⁻¹) ≤ T * Real.log T := mul_le_mul_of_nonneg_left h1 hTnn
    have h4 : T * (1 - T⁻¹) = T - 1 := by field_simp
    linarith [h3, h4]
  have hlogt : Real.log t = Real.log T / 2 := by
    rw [htdef, Real.log_sqrt hTnn]
  rw [hlogt] at hint
  -- conclude `T = 1`
  have hfinal : (1 - T) * (A - m - κ / 4) ≤ 0 := by
    have hmul : T * m ≤ T * ((∫ x, Korevaar.homogeneousDensity 2 Ψ (z x) (weakGrad z x))
        + ∫ x, Korevaar.entropyPotential 2 κ (z x)) := mul_le_mul_of_nonneg_left hEz hTnn
    nlinarith [hint, hmul, hEu, hTlog, hTnn]
  have hT1 : T = 1 := by
    rcases eq_or_lt_of_le hTle with heq | hlt
    · exact heq
    · exfalso
      nlinarith [hfinal, hbracket]
  -- `u = min (u, M)` a.e.
  have hsq : ∫ x, (u x ^ 2 - min (u x) M ^ 2) = 0 := by
    rw [integral_sub hu2 huMsq, hu.integral_sq, ← hTdef, hT1]
    ring
  have hdiffnn : ∀ x : Euc d, 0 ≤ u x ^ 2 - min (u x) M ^ 2 := by
    intro x
    have h1 : 0 ≤ u x - min (u x) M := by linarith [huMle x]
    have h2 : 0 ≤ u x + min (u x) M := by linarith [huM0 x, huMle x]
    nlinarith [mul_nonneg h1 h2]
  have hzero : (fun x => u x ^ 2 - min (u x) M ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hdiffnn (hu2.sub huMsq)).1 hsq
  filter_upwards [hzero] with x hx
  have hx0 : u x ^ 2 - min (u x) M ^ 2 = 0 := hx
  have hxe : u x = min (u x) M := by
    have hA2 : u x ^ 2 = min (u x) M ^ 2 := by linarith
    have hsq0 := congrArg Real.sqrt hA2
    rwa [Real.sqrt_sq (hu.nonneg x), Real.sqrt_sq (huM0 x)] at hsq0
  rw [hxe]
  exact min_le_right _ _

end Komlos.Literature.Regularized
