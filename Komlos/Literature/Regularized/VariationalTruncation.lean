import Komlos.Literature.Regularized.VariationalExistence

/-!
# Truncation in `W₀^{1,2}`

Lane `L1` (`reg/variational`).  The `L^∞` bound for the minimizer (Revision 2 (i) of
`REGULARIZED_ROUTE.md`) compares `u` with its truncation `min (u, M)`; this file supplies the
corresponding chain rule.

`t ↦ min (t, M)` is Lipschitz but not `C¹`, so `Komlos.Literature.memW0_comp` does not apply
directly.  As in `Komlos/Literature/Regularized/VariationalZeroSet.lean` we approximate it by
the smooth family

`minApprox M ε t = (H_ε(t - M) - H_ε(-M)) / 2`,  `H_ε(s) = s + ε - √(s² + ε²)`,

which satisfies `minApprox M ε 0 = 0`, `|minApprox M ε t - min (t, M)| ≤ ε`,
`|(minApprox M ε)'| ≤ 1` and `(minApprox M ε)'(t) → minMul M t` pointwise, where
`minMul M t` is `1` for `t < M`, `1/2` for `t = M` and `0` for `t > M`.

Combined with `weakGrad_eq_zero_of_eq_zero` applied to `(u - M)⁺` this gives the clean form
`weakGrad (min (u, M)) = 1_{u ≤ M} ∇u` a.e. (`ae_weakGrad_min`), because `∇u = 0` a.e. on the
level set `{u = M}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### The smooth approximation of `min (·, M)` -/

/-- The limiting multiplier: `1` below the level, `1/2` at the level, `0` above. -/
noncomputable def minMul (M t : ℝ) : ℝ := if t < M then 1 else if t = M then 1 / 2 else 0

theorem minMul_nonneg (M t : ℝ) : 0 ≤ minMul M t := by
  rw [minMul]
  split_ifs <;> norm_num

theorem abs_minMul_le_one (M t : ℝ) : |minMul M t| ≤ 1 := by
  rw [minMul]
  split_ifs <;> norm_num

/-- The smooth approximation of `t ↦ min (t, M)`. -/
noncomputable def minApprox (M ε t : ℝ) : ℝ := (sqrtDefect ε (t - M) - sqrtDefect ε (-M)) / 2

@[simp] theorem minApprox_zero (M ε : ℝ) : minApprox M ε 0 = 0 := by
  simp [minApprox]

theorem hasDerivAt_minApprox {ε : ℝ} (hε : 0 < ε) (M t : ℝ) :
    HasDerivAt (minApprox M ε)
      ((1 - (t - M) / Real.sqrt ((t - M) ^ 2 + ε ^ 2)) / 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => s - M) 1 t := by
    simpa using (hasDerivAt_id t).sub_const M
  have h2 := (hasDerivAt_sqrtDefect hε (t - M)).comp t h1
  rw [mul_one] at h2
  have h3 := (h2.sub_const (sqrtDefect ε (-M))).div_const 2
  exact h3

theorem deriv_minApprox {ε : ℝ} (hε : 0 < ε) (M t : ℝ) :
    deriv (minApprox M ε) t = (1 - (t - M) / Real.sqrt ((t - M) ^ 2 + ε ^ 2)) / 2 :=
  (hasDerivAt_minApprox hε M t).deriv

theorem contDiff_minApprox {ε : ℝ} (hε : 0 < ε) (M : ℝ) : ContDiff ℝ 1 (minApprox M ε) :=
  (((contDiff_sqrtDefect hε).comp (contDiff_id.sub contDiff_const)).sub contDiff_const).div_const 2

theorem abs_deriv_minApprox_le {ε : ℝ} (hε : 0 < ε) (M t : ℝ) :
    |deriv (minApprox M ε) t| ≤ 1 := by
  rw [deriv_minApprox hε]
  have hpos : 0 < (t - M) ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)
  have hs : 0 < Real.sqrt ((t - M) ^ 2 + ε ^ 2) := Real.sqrt_pos.2 hpos
  have hq : |(t - M) / Real.sqrt ((t - M) ^ 2 + ε ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    calc |t - M| = Real.sqrt ((t - M) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((t - M) ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), div_le_one (by norm_num : (0:ℝ) < 2)]
  calc |1 - (t - M) / Real.sqrt ((t - M) ^ 2 + ε ^ 2)|
      ≤ |(1 : ℝ)| + |(t - M) / Real.sqrt ((t - M) ^ 2 + ε ^ 2)| := abs_sub _ _
    _ ≤ 1 + 1 := by rw [abs_one]; linarith
    _ = 2 := by norm_num

/-- `|H_ε(s) - (s - |s|)| ≤ ε`. -/
theorem abs_sqrtDefect_sub_le {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) :
    |sqrtDefect ε s - (s - |s|)| ≤ ε := by
  have h1 : |s| ≤ Real.sqrt (s ^ 2 + ε ^ 2) := by
    calc |s| = Real.sqrt (s ^ 2) := (Real.sqrt_sq_eq_abs s).symm
      _ ≤ Real.sqrt (s ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  have h2 : Real.sqrt (s ^ 2 + ε ^ 2) ≤ |s| + ε := by
    rw [show |s| + ε = Real.sqrt ((|s| + ε) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [abs_nonneg s, sq_abs s]
  have he : sqrtDefect ε s - (s - |s|) = ε + |s| - Real.sqrt (s ^ 2 + ε ^ 2) := by
    simp only [sqrtDefect]; ring
  rw [he, abs_le]
  constructor <;> linarith

/-- `|minApprox M ε t - min (t, M)| ≤ ε` for `M ≥ 0`. -/
theorem abs_minApprox_sub_min_le {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M) (t : ℝ) :
    |minApprox M ε t - min t M| ≤ ε := by
  have hmin : min t M = ((t - M) - |t - M| - ((-M) - |(-M)|)) / 2 := by
    rw [abs_neg, abs_of_nonneg hM, min_def]
    rcases le_or_gt t M with hle | hgt
    · rw [if_pos hle, abs_of_nonpos (by linarith)]; ring
    · rw [if_neg (by linarith), abs_of_pos (by linarith)]; ring
  rw [minApprox, hmin]
  have e1 : (sqrtDefect ε (t - M) - sqrtDefect ε (-M)) / 2
      - ((t - M) - |t - M| - ((-M) - |(-M)|)) / 2
      = ((sqrtDefect ε (t - M) - ((t - M) - |t - M|))
          - (sqrtDefect ε (-M) - ((-M) - |(-M)|))) / 2 := by ring
  rw [e1, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  calc |(sqrtDefect ε (t - M) - ((t - M) - |t - M|))
          - (sqrtDefect ε (-M) - ((-M) - |(-M)|))|
      ≤ |sqrtDefect ε (t - M) - ((t - M) - |t - M|)|
        + |sqrtDefect ε (-M) - ((-M) - |(-M)|)| := abs_sub _ _
    _ ≤ ε + ε := add_le_add (abs_sqrtDefect_sub_le hε _) (abs_sqrtDefect_sub_le hε _)
    _ = ε * 2 := by ring

/-- The general-sign limit of `H_ε'`. -/
theorem tendsto_deriv_sqrtDefect' {e : ℕ → ℝ} (he : ∀ n, 0 < e n)
    (he0 : Tendsto e atTop (𝓝 0)) (s : ℝ) :
    Tendsto (fun n => deriv (sqrtDefect (e n)) s) atTop
      (𝓝 (if s < 0 then 2 else if s = 0 then 1 else 0)) := by
  simp only [deriv_sqrtDefect (he _)]
  rcases lt_trichotomy s 0 with hs | hs | hs
  · rw [if_pos hs]
    have hcont : Tendsto (fun n => Real.sqrt (s ^ 2 + e n ^ 2)) atTop (𝓝 |s|) := by
      have h := (Real.continuous_sqrt.tendsto (s ^ 2 + 0 ^ 2)).comp
        (by simpa using (tendsto_const_nhds (x := s ^ 2)).add (he0.pow 2))
      simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using h
    rw [abs_of_neg hs] at hcont
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := s)).div hcont (by linarith))
    rw [div_neg, div_self hs.ne, sub_neg_eq_add] at h
    have htwo : (1 : ℝ) + 1 = 2 := by norm_num
    rwa [htwo] at h
  · rw [if_neg (by rw [hs]; norm_num), if_pos hs, hs]
    simp
  · rw [if_neg (by linarith), if_neg (by linarith)]
    have hcont : Tendsto (fun n => Real.sqrt (s ^ 2 + e n ^ 2)) atTop (𝓝 |s|) := by
      have h := (Real.continuous_sqrt.tendsto (s ^ 2 + 0 ^ 2)).comp
        (by simpa using (tendsto_const_nhds (x := s ^ 2)).add (he0.pow 2))
      simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using h
    rw [abs_of_pos hs] at hcont
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := s)).div hcont hs.ne')
    rw [div_self hs.ne', sub_self] at h
    exact h

theorem tendsto_deriv_minApprox {e : ℕ → ℝ} (he : ∀ n, 0 < e n)
    (he0 : Tendsto e atTop (𝓝 0)) (M t : ℝ) :
    Tendsto (fun n => deriv (minApprox M (e n)) t) atTop (𝓝 (minMul M t)) := by
  have h := (tendsto_deriv_sqrtDefect' he he0 (t - M)).div_const 2
  have heq : ∀ n, deriv (sqrtDefect (e n)) (t - M) / 2 = deriv (minApprox M (e n)) t := by
    intro n
    rw [deriv_minApprox (he n), deriv_sqrtDefect (he n)]
  simp only [heq] at h
  have hval : (if t - M < 0 then (2:ℝ) else if t - M = 0 then 1 else 0) / 2 = minMul M t := by
    rw [minMul]
    rcases lt_trichotomy t M with hlt | heqt | hgt
    · rw [if_pos (by linarith), if_pos hlt]; norm_num
    · rw [if_neg (by rw [heqt]; norm_num), if_pos (by rw [heqt]; ring),
        if_neg (by rw [heqt]; exact lt_irrefl M), if_pos heqt]
    · rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
        if_neg (by linarith)]
      norm_num
  rwa [hval] at h

/-! ### The chain rule for the truncation -/

/-- **The truncation `min (u, M)` lies in `W₀^{1,2}(K)`**, with weak gradient
`minMul M (u ·) ∇u`. -/
theorem memW0_min (hKm : MeasurableSet K) (hKvol : volume K ≠ ⊤) (hu : MemW0 2 K u)
    (hu0 : ∀ x, 0 ≤ u x) {M : ℝ} (hM : 0 ≤ M) :
    MemW0 2 K (fun x => min (u x) M) ∧
      weakGrad (fun x => min (u x) M) =ᵐ[volume] fun x => minMul M (u x) • weakGrad u x := by
  set e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with he_def
  have he : ∀ n, 0 < e n := fun n => Nat.one_div_pos_of_nat
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hchain := fun n => memW0_comp (K := K) (f := u) one_lt_two hu
    (contDiff_minApprox (he n) M) (minApprox_zero M (e n)) (L := 1)
    (fun t => abs_deriv_minApprox_le (he n) M t)
  set a : ℕ → Euc d → ℝ := fun n x => deriv (minApprox M (e n)) (u x) with ha_def
  set al : Euc d → ℝ := fun x => minMul M (u x) with hal_def
  have hwm : AEStronglyMeasurable u volume := hu.memLp.aestronglyMeasurable
  have ham : ∀ n, AEStronglyMeasurable (a n) volume := fun n => by
    have heq : deriv (minApprox M (e n)) =
        fun t : ℝ => (1 - (t - M) / Real.sqrt ((t - M) ^ 2 + e n ^ 2)) / 2 := by
      funext t
      exact deriv_minApprox (he n) M t
    have hc : Continuous (deriv (minApprox M (e n))) := by
      rw [heq]
      refine Continuous.div_const ?_ 2
      refine continuous_const.sub ((continuous_id.sub continuous_const).div
        (Real.continuous_sqrt.comp (((continuous_id.sub continuous_const).pow 2).add
          continuous_const)) fun t => ?_)
      exact (Real.sqrt_pos.2
        (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (he n) 2))).ne'
    exact hc.comp_aestronglyMeasurable hwm
  have halm : AEStronglyMeasurable al volume := by
    have hmeas : Measurable (minMul M) := by
      have heq : minMul M =
          fun t : ℝ => if t < M then (1 : ℝ) else if t = M then 1 / 2 else 0 := rfl
      rw [heq]
      refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
      exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
        measurable_const measurable_const
    exact (hmeas.comp_aemeasurable hwm.aemeasurable).aestronglyMeasurable
  have hal1 : ∀ x, |al x| ≤ 1 := fun x => abs_minMul_le_one M (u x)
  -- the limit function and its candidate gradient
  have hminLp : MemLp (fun x => min (u x) M) (ENNReal.ofReal 2) volume := by
    refine hu.memLp.of_le_mul (c := 1)
      ((hwm.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_min (hu0 x) hM), abs_of_nonneg (hu0 x)]
    exact min_le_left _ _
  have hgLp : MemLp (fun x => al x • weakGrad u x) (ENNReal.ofReal 2) volume :=
    hu.memLp_weakGrad.of_le_mul (c := 1) (halm.smul hu.memLp_weakGrad.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, one_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hal1 x))
  -- convergence of the values
  have hind : MemLp (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) volume :=
    memLp_indicator_const _ hKm _ (Or.inr hKvol)
  have hf0 : Tendsto (fun n => eLpNorm ((fun x => minApprox M (e n) (u x))
      - fun x => min (u x) M) (ENNReal.ofReal 2) volume) atTop (𝓝 0) := by
    have hle : ∀ n, eLpNorm ((fun x => minApprox M (e n) (u x)) - fun x => min (u x) M)
        (ENNReal.ofReal 2) volume ≤ ENNReal.ofReal (e n) *
          eLpNorm (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) volume := by
      intro n
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ _
      filter_upwards [hu.ae_eq_zero] with x hx
      show ‖minApprox M (e n) (u x) - min (u x) M‖ ≤ e n * ‖K.indicator (fun _ => (1 : ℝ)) x‖
      rw [Real.norm_eq_abs]
      by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxK]
        simp only [Real.norm_eq_abs, abs_one, mul_one]
        exact abs_minApprox_sub_min_le (he n).le hM (u x)
      · rw [Set.indicator_of_notMem hxK, hx hxK]
        simp [min_eq_left hM]
    have hlim : Tendsto (fun n => ENNReal.ofReal (e n) *
        eLpNorm (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) volume) atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.mul_const
        ((ENNReal.continuous_ofReal.tendsto 0).comp he0) (Or.inr hind.eLpNorm_ne_top)
      simpa [Function.comp_def] using hc
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle
  -- convergence of the gradients
  have hgrad := tendsto_eLpNorm_smul_sub_smul (μ := volume) (p := 2) one_lt_two
    (a := a) (al := al) (b := fun _ => weakGrad u) (bl := weakGrad u)
    hu.memLp_weakGrad (L := 1) (fun n x => abs_deriv_minApprox_le (he n) M (u x))
    hal1 ham halm (fun _ => hu.memLp_weakGrad.aestronglyMeasurable)
    (Eventually.of_forall fun x => tendsto_deriv_minApprox he he0 M (u x)) (by simp)
  have hwg : HasWeakGradient (fun x => min (u x) M) (fun x => al x • weakGrad u x) := by
    refine HasWeakGradient.of_tendsto one_lt_two
      (u := fun n x => minApprox M (e n) (u x))
      (G := fun n x => a n x • weakGrad u x) (fun n => ?_) hminLp hgLp hf0 hgrad
    exact (hchain n).1.hasWeakGradient.congr_right (hchain n).2
  refine ⟨⟨hminLp, ?_, ⟨_, hwg, hgLp⟩⟩, hwg.weakGrad_ae_eq⟩
  filter_upwards [hu.ae_eq_zero] with x hx hxK
  rw [hx hxK, min_eq_left hM]

/-! ### The weak gradient vanishes on a level set -/

/-- **Stampacchia at a positive level**: `∇u = 0` a.e. on `{u = M}`.  Apply
`weakGrad_eq_zero_of_eq_zero` to `(u - M)⁺ = u - min (u, M)`, whose weak gradient is
`(1 - minMul M u) ∇u = (1/2) ∇u` on `{u = M}`. -/
theorem ae_weakGrad_eq_of_eq_level (hKm : MeasurableSet K) (hKvol : volume K ≠ ⊤)
    (hu : MemW0 2 K u) (hu0 : ∀ x, 0 ≤ u x) {M : ℝ} (hM : 0 < M) :
    ∀ᵐ x, u x = M → weakGrad u x = 0 := by
  obtain ⟨hmin, hgmin⟩ := memW0_min hKm hKvol hu hu0 hM.le
  have hpt : ∀ x, (u + (-1 : ℝ) • fun y => min (u y) M) x = max (u x - M) 0 := by
    intro x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases le_or_gt (u x) M with hle | hgt
    · rw [min_eq_left hle, max_eq_right (by linarith)]; ring
    · rw [min_eq_right hgt.le, max_eq_left (by linarith)]; ring
  have hvmem : MemW0 2 K (fun x => max (u x - M) 0) :=
    (hu.add (hmin.smul (-1))).congr (Eventually.of_forall hpt)
  have hv0 : ∀ x, 0 ≤ max (u x - M) 0 := fun x => le_max_right _ _
  have hwgm : HasWeakGradient (fun x => min (u x) M)
      (fun x => minMul M (u x) • weakGrad u x) :=
    hmin.hasWeakGradient.congr_right hgmin
  have hwgv : HasWeakGradient (fun x => max (u x - M) 0)
      (fun x => (1 - minMul M (u x)) • weakGrad u x) := by
    have h1 := hu.hasWeakGradient.add (hwgm.smul (-1))
    refine (h1.congr_right (Eventually.of_forall fun x => ?_)).congr_left
      (Eventually.of_forall hpt)
    show (weakGrad u + (-1 : ℝ) • fun y => minMul M (u y) • weakGrad u y) x
      = (1 - minMul M (u x)) • weakGrad u x
    simp only [Pi.add_apply, Pi.neg_apply, sub_smul, one_smul, neg_smul]
    abel
  have hvg : weakGrad (fun x => max (u x - M) 0) =ᵐ[volume]
      fun x => (1 - minMul M (u x)) • weakGrad u x := hwgv.weakGrad_ae_eq
  have hz := weakGrad_eq_zero_of_eq_zero hKm hKvol hvmem hv0
  filter_upwards [hz, hvg] with x h1 h2 hux
  have hv : max (u x - M) 0 = 0 := by rw [hux]; simp
  have h3 : (1 - minMul M (u x)) • weakGrad u x = 0 := by rw [← h2]; exact h1 hv
  have hmm : minMul M (u x) = 1 / 2 := by
    rw [minMul, if_neg (by rw [hux]; exact lt_irrefl M), if_pos hux]
  rw [hmm] at h3
  have h4 : (1 - (1 : ℝ) / 2) = 1 / 2 := by norm_num
  rw [h4] at h3
  have h5 : ((1 : ℝ) / 2) ≠ 0 := by norm_num
  simpa [h5] using h3

/-- **The truncation chain rule in clean form**: `∇(min (u, M)) = 1_{u ≤ M} ∇u` a.e. -/
theorem ae_weakGrad_min (hKm : MeasurableSet K) (hKvol : volume K ≠ ⊤) (hu : MemW0 2 K u)
    (hu0 : ∀ x, 0 ≤ u x) {M : ℝ} (hM : 0 < M) :
    ∀ᵐ x, weakGrad (fun y => min (u y) M) x = if u x ≤ M then weakGrad u x else 0 := by
  obtain ⟨-, hgmin⟩ := memW0_min hKm hKvol hu hu0 hM.le
  filter_upwards [hgmin, ae_weakGrad_eq_of_eq_level hKm hKvol hu hu0 hM] with x h1 h2
  rw [h1]
  rcases lt_trichotomy (u x) M with hlt | heq | hgt
  · rw [minMul, if_pos hlt, one_smul, if_pos hlt.le]
  · rw [minMul, if_neg (by rw [heq]; exact lt_irrefl M), if_pos heq, if_pos heq.le, h2 heq]
    simp
  · rw [minMul, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), zero_smul]

end Komlos.Literature.Regularized
