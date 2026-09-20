import Komlos.Literature.Regularized.VariationalEuler

/-!
# Uniqueness of the minimizer

Lane `L1` (`reg/variational`), the frozen lane statement `IsRegMinimizer.ae_eq`
(formerly a named `sorry` in `Interface.lean`, proved here).

## The lattice argument

Let `u`, `v` be two minimizers.  Because the energy density is local, truncating one against
the other rearranges the energy without changing it:

`E_dens(u ∧ v) + E_dens(u ∨ v) = E_dens(u) + E_dens(v)`,  `(u ∧ v)² + (u ∨ v)² = u² + v²`

(using `∇u = ∇v` a.e. on `{u = v}`, a consequence of Stampacchia's lemma applied to
`(u - v)⁺`).  Writing `N₁ = ∫ (u ∧ v)²`, `N₂ = ∫ (u ∨ v)²` (so `N₁ + N₂ = 2`), the rescaling
bound `energy_ge_of_memW0_gen`

`∫ Q(w,∇w) + ∫ P(w) ≥ N m + (κ/4) N log N`

applied to `u ∧ v` and `u ∨ v` and summed gives `(κ/4)(N₁ log N₁ + N₂ log N₂) ≤ 0`, while
`N log N ≥ N - 1` with **strict** inequality for `N ≠ 1` forces `N₁ = N₂ = 1`.  Then
`∫ u² = ∫ (u ∧ v)²` with `u ∧ v ≤ u` gives `u = u ∧ v` a.e., and symmetrically `v = u ∧ v`
a.e., i.e. `u = v` a.e.

The only Sobolev input is the chain rule for the positive part (`var_memW0_posPart`), obtained
from `Komlos.Literature.memW0_comp` and the smooth approximations
`P_ε(t) = t - (H_ε t)/2` of `t ↦ t⁺`, where `H_ε` is `sqrtDefect`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u v : Euc d → ℝ}

/-! ### The chain rule for the positive part -/

/-- The limiting multiplier for `t ↦ t⁺`. -/
noncomputable def posMul (t : ℝ) : ℝ := if 0 < t then 1 else if t = 0 then 1 / 2 else 0

theorem posMul_nonneg (t : ℝ) : 0 ≤ posMul t := by
  rw [posMul]; split_ifs <;> norm_num

theorem abs_posMul_le_one (t : ℝ) : |posMul t| ≤ 1 := by
  rw [posMul]; split_ifs <;> norm_num

/-- The smooth approximation of the positive part. -/
noncomputable def posApprox (ε t : ℝ) : ℝ := t - sqrtDefect ε t / 2

@[simp] theorem posApprox_zero (ε : ℝ) (hε : 0 ≤ ε) : posApprox ε 0 = 0 := by
  simp [posApprox, sqrtDefect_zero hε]

theorem hasDerivAt_posApprox {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (posApprox ε) (1 - (1 - t / Real.sqrt (t ^ 2 + ε ^ 2)) / 2) t :=
  (hasDerivAt_id t).sub ((hasDerivAt_sqrtDefect hε t).div_const 2)

theorem deriv_posApprox {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (posApprox ε) t = 1 - (1 - t / Real.sqrt (t ^ 2 + ε ^ 2)) / 2 :=
  (hasDerivAt_posApprox hε t).deriv

theorem contDiff_posApprox {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (posApprox ε) :=
  contDiff_id.sub ((contDiff_sqrtDefect hε).div_const 2)

theorem abs_deriv_posApprox_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |deriv (posApprox ε) t| ≤ 1 := by
  have hpos : 0 < t ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)
  have hs : 0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.2 hpos
  have hq : |t / Real.sqrt (t ^ 2 + ε ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
      _ ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  rw [deriv_posApprox hε, abs_le]
  rw [abs_le] at hq
  constructor <;> linarith [hq.1, hq.2]

theorem abs_posApprox_sub_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    |posApprox ε t - max t 0| ≤ ε / 2 := by
  have h1 := abs_sqrtDefect_sub_le hε t
  have he : posApprox ε t - max t 0 = -((sqrtDefect ε t - (t - |t|)) / 2) := by
    rw [posApprox, max_def]
    rcases le_or_gt t 0 with hle | hgt
    · rw [if_pos hle, abs_of_nonpos hle]; ring
    · rw [if_neg (by linarith), abs_of_pos hgt]; ring
  rw [he, abs_neg, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  exact h1

theorem tendsto_deriv_posApprox {e : ℕ → ℝ} (he : ∀ n, 0 < e n)
    (he0 : Tendsto e atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => deriv (posApprox (e n)) t) atTop (𝓝 (posMul t)) := by
  have h := ((tendsto_deriv_sqrtDefect' he he0 t).div_const 2).const_sub 1
  have heq : ∀ n, 1 - deriv (sqrtDefect (e n)) t / 2 = deriv (posApprox (e n)) t := by
    intro n
    rw [deriv_posApprox (he n), deriv_sqrtDefect (he n)]
  simp only [heq] at h
  have hval : 1 - (if t < 0 then (2 : ℝ) else if t = 0 then 1 else 0) / 2 = posMul t := by
    rw [posMul]
    rcases lt_trichotomy t 0 with hlt | heqt | hgt
    · rw [if_pos hlt, if_neg (by linarith), if_neg (by linarith)]; norm_num
    · rw [if_neg (by rw [heqt]; norm_num), if_pos heqt, if_neg (by rw [heqt]; norm_num),
        if_pos heqt]
      norm_num
    · rw [if_neg (by linarith), if_neg (by linarith), if_pos hgt]; norm_num
  rwa [hval] at h

/-- **The chain rule for the positive part** in `W₀^{1,2}(K)`. -/
theorem var_memW0_posPart (hKm : MeasurableSet K) (hKvol : volume K ≠ ⊤) {f : Euc d → ℝ}
    (hf : MemW0 2 K f) :
    MemW0 2 K (fun x => max (f x) 0) ∧
      weakGrad (fun x => max (f x) 0) =ᵐ[volume] fun x => posMul (f x) • weakGrad f x := by
  set e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with he_def
  have he : ∀ n, 0 < e n := fun n => Nat.one_div_pos_of_nat
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hchain := fun n => memW0_comp (K := K) (f := f) one_lt_two hf
    (contDiff_posApprox (he n)) (posApprox_zero (e n) (he n).le) (L := 1)
    (fun t => abs_deriv_posApprox_le (he n) t)
  set a : ℕ → Euc d → ℝ := fun n x => deriv (posApprox (e n)) (f x) with ha_def
  set al : Euc d → ℝ := fun x => posMul (f x) with hal_def
  have hwm : AEStronglyMeasurable f volume := hf.memLp.aestronglyMeasurable
  have ham : ∀ n, AEStronglyMeasurable (a n) volume := fun n => by
    have heq : deriv (posApprox (e n)) =
        fun t : ℝ => 1 - (1 - t / Real.sqrt (t ^ 2 + e n ^ 2)) / 2 := by
      funext t
      exact deriv_posApprox (he n) t
    have hc : Continuous (deriv (posApprox (e n))) := by
      rw [heq]
      refine continuous_const.sub (Continuous.div_const ?_ 2)
      refine continuous_const.sub (continuous_id.div
        (Real.continuous_sqrt.comp (((continuous_pow 2)).add continuous_const)) fun t => ?_)
      exact (Real.sqrt_pos.2
        (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (he n) 2))).ne'
    exact hc.comp_aestronglyMeasurable hwm
  have halm : AEStronglyMeasurable al volume := by
    have hmeas : Measurable posMul := by
      have heq : posMul = fun t : ℝ => if 0 < t then (1 : ℝ) else if t = 0 then 1 / 2 else 0 :=
        rfl
      rw [heq]
      refine Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const ?_
      exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
        measurable_const measurable_const
    exact (hmeas.comp_aemeasurable hwm.aemeasurable).aestronglyMeasurable
  have hal1 : ∀ x, |al x| ≤ 1 := fun x => abs_posMul_le_one (f x)
  have hmaxLp : MemLp (fun x => max (f x) 0) (ENNReal.ofReal 2) volume := by
    refine hf.memLp.of_le_mul (c := 1)
      ((hwm.aemeasurable.max aemeasurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_or_gt (f x) 0 with hle | hgt
    · rw [max_eq_right hle]
      simp
    · rw [max_eq_left hgt.le]
  have hgLp : MemLp (fun x => al x • weakGrad f x) (ENNReal.ofReal 2) volume :=
    hf.memLp_weakGrad.of_le_mul (c := 1) (halm.smul hf.memLp_weakGrad.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, one_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hal1 x))
  have hind : MemLp (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) volume :=
    memLp_indicator_const _ hKm _ (Or.inr hKvol)
  have hf0 : Tendsto (fun n => eLpNorm ((fun x => posApprox (e n) (f x))
      - fun x => max (f x) 0) (ENNReal.ofReal 2) volume) atTop (𝓝 0) := by
    have hle : ∀ n, eLpNorm ((fun x => posApprox (e n) (f x)) - fun x => max (f x) 0)
        (ENNReal.ofReal 2) volume ≤ ENNReal.ofReal (e n) *
          eLpNorm (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) volume := by
      intro n
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ _
      filter_upwards [hf.ae_eq_zero] with x hx
      show ‖posApprox (e n) (f x) - max (f x) 0‖ ≤ e n * ‖K.indicator (fun _ => (1 : ℝ)) x‖
      rw [Real.norm_eq_abs]
      by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxK]
        simp only [Real.norm_eq_abs, abs_one, mul_one]
        have := abs_posApprox_sub_le (he n).le (f x)
        linarith [(he n).le]
      · rw [Set.indicator_of_notMem hxK, hx hxK]
        simp [posApprox_zero (e n) (he n).le]
    have hlim : Tendsto (fun n => ENNReal.ofReal (e n) *
        eLpNorm (K.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) volume) atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.mul_const
        ((ENNReal.continuous_ofReal.tendsto 0).comp he0) (Or.inr hind.eLpNorm_ne_top)
      simpa [Function.comp_def] using hc
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle
  have hgrad := tendsto_eLpNorm_smul_sub_smul (μ := volume) (p := 2) one_lt_two
    (a := a) (al := al) (b := fun _ => weakGrad f) (bl := weakGrad f)
    hf.memLp_weakGrad (L := 1) (fun n x => abs_deriv_posApprox_le (he n) (f x))
    hal1 ham halm (fun _ => hf.memLp_weakGrad.aestronglyMeasurable)
    (Eventually.of_forall fun x => tendsto_deriv_posApprox he he0 (f x)) (by simp)
  have hwg : HasWeakGradient (fun x => max (f x) 0) (fun x => al x • weakGrad f x) := by
    refine HasWeakGradient.of_tendsto one_lt_two
      (u := fun n x => posApprox (e n) (f x))
      (G := fun n x => a n x • weakGrad f x) (fun n => ?_) hmaxLp hgLp hf0 hgrad
    exact (hchain n).1.hasWeakGradient.congr_right (hchain n).2
  refine ⟨⟨hmaxLp, ?_, ⟨_, hwg, hgLp⟩⟩, hwg.weakGrad_ae_eq⟩
  filter_upwards [hf.ae_eq_zero] with x hx hxK
  rw [hx hxK]
  simp

/-! ### The lattice decomposition -/

/-- **`min` and `max` of two nonnegative `W₀^{1,2}` functions**, with their weak gradients.
On `{u = v}` the two gradients agree a.e. (Stampacchia applied to `(u - v)⁺`), so the
formulas below are unambiguous. -/
theorem memW0_min_max (hKm : MeasurableSet K) (hKvol : volume K ≠ ⊤)
    (hu : MemW0 2 K u) (hv : MemW0 2 K v) :
    MemW0 2 K (fun x => min (u x) (v x)) ∧ MemW0 2 K (fun x => max (u x) (v x)) ∧
      ∀ᵐ x, weakGrad (fun y => min (u y) (v y)) x
            = (if u x ≤ v x then weakGrad u x else weakGrad v x) ∧
          weakGrad (fun y => max (u y) (v y)) x
            = (if u x ≤ v x then weakGrad v x else weakGrad u x) := by
  set f : Euc d → ℝ := fun x => u x - v x with hfdef
  have hfpt : ∀ x, (u + (-1 : ℝ) • v) x = f x := by
    intro x
    show u x + (-1 : ℝ) * v x = u x - v x
    ring
  have hfmem : MemW0 2 K f := (hu.add (hv.smul (-1))).congr (Eventually.of_forall hfpt)
  have hwgf : HasWeakGradient f (fun x => weakGrad u x - weakGrad v x) := by
    have h1 := hu.hasWeakGradient.add (hv.hasWeakGradient.smul (-1 : ℝ))
    refine (h1.congr_right (Eventually.of_forall fun x => ?_)).congr_left
      (Eventually.of_forall hfpt)
    show (weakGrad u + (-1 : ℝ) • weakGrad v) x = weakGrad u x - weakGrad v x
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [neg_smul, one_smul]
    abel
  have hfg : weakGrad f =ᵐ[volume] fun x => weakGrad u x - weakGrad v x := hwgf.weakGrad_ae_eq
  obtain ⟨hpmem, hpg⟩ := var_memW0_posPart hKm hKvol hfmem
  have hwgp : HasWeakGradient (fun x => max (f x) 0)
      (fun x => posMul (f x) • weakGrad f x) := hpmem.hasWeakGradient.congr_right hpg
  -- pointwise identities
  have hfx : ∀ x, f x = u x - v x := fun _ => rfl
  have hminpt : ∀ x, min (u x) (v x) = u x - max (f x) 0 := by
    intro x
    rcases le_or_gt (u x) (v x) with hle | hgt
    · rw [min_eq_left hle, max_eq_right (by rw [hfx]; linarith), sub_zero]
    · rw [min_eq_right hgt.le, max_eq_left (by rw [hfx]; linarith), hfx]
      ring
  have hmaxpt : ∀ x, max (u x) (v x) = v x + max (f x) 0 := by
    intro x
    rcases le_or_gt (u x) (v x) with hle | hgt
    · rw [max_eq_right hle, max_eq_right (by rw [hfx]; linarith), add_zero]
    · rw [max_eq_left hgt.le, max_eq_left (by rw [hfx]; linarith), hfx]
      ring
  have hminmem : MemW0 2 K (fun x => min (u x) (v x)) :=
    (hu.add (hpmem.smul (-1))).congr (Eventually.of_forall fun x => by
      show u x + (-1 : ℝ) * max (f x) 0 = min (u x) (v x)
      rw [hminpt]; ring)
  have hmaxmem : MemW0 2 K (fun x => max (u x) (v x)) :=
    (hv.add (hpmem.smul 1)).congr (Eventually.of_forall fun x => by
      show v x + (1 : ℝ) * max (f x) 0 = max (u x) (v x)
      rw [hmaxpt]; ring)
  have hwgmin : HasWeakGradient (fun x => min (u x) (v x))
      (fun x => weakGrad u x - posMul (f x) • weakGrad f x) := by
    have h1 := hu.hasWeakGradient.add (hwgp.smul (-1 : ℝ))
    refine (h1.congr_right (Eventually.of_forall fun x => ?_)).congr_left
      (Eventually.of_forall fun x => ?_)
    · show (weakGrad u + (-1 : ℝ) • fun y => posMul (f y) • weakGrad f y) x
        = weakGrad u x - posMul (f x) • weakGrad f x
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [neg_smul, one_smul]
      abel
    · show (u + (-1 : ℝ) • fun y => max (f y) 0) x = min (u x) (v x)
      show u x + (-1 : ℝ) * max (f x) 0 = min (u x) (v x)
      rw [hminpt]; ring
  have hwgmax : HasWeakGradient (fun x => max (u x) (v x))
      (fun x => weakGrad v x + posMul (f x) • weakGrad f x) := by
    have h1 := hv.hasWeakGradient.add (hwgp.smul (1 : ℝ))
    refine (h1.congr_right (Eventually.of_forall fun x => ?_)).congr_left
      (Eventually.of_forall fun x => ?_)
    · show (weakGrad v + (1 : ℝ) • fun y => posMul (f y) • weakGrad f y) x
        = weakGrad v x + posMul (f x) • weakGrad f x
      simp
    · show (v + (1 : ℝ) • fun y => max (f y) 0) x = max (u x) (v x)
      show v x + (1 : ℝ) * max (f x) 0 = max (u x) (v x)
      rw [hmaxpt]; ring
  refine ⟨hminmem, hmaxmem, ?_⟩
  have hstamp := weakGrad_eq_zero_of_eq_zero hKm hKvol hpmem (fun x => le_max_right _ _)
  filter_upwards [hfg, hwgmin.weakGrad_ae_eq, hwgmax.weakGrad_ae_eq, hstamp, hpg]
    with x hfgx hminx hmaxx hstx hpgx
  -- on `{u = v}` the two gradients agree
  have hequal : u x = v x → weakGrad u x = weakGrad v x := by
    intro heq
    have hfx0 : f x = 0 := by rw [hfx]; linarith
    have h0 : max (f x) 0 = 0 := by rw [hfx0]; simp
    have hst := hstx h0
    rw [hpgx, hfx0] at hst
    have hpm : posMul (0 : ℝ) = 1 / 2 := by rw [posMul]; norm_num
    rw [hpm] at hst
    have hz : weakGrad f x = 0 := by
      have h2 : (1 / 2 : ℝ) ≠ 0 := by norm_num
      simpa [h2] using hst
    rw [hfgx] at hz
    exact sub_eq_zero.1 hz
  rcases lt_trichotomy (u x) (v x) with hlt | heq | hgt
  · have hfneg : f x < 0 := by rw [hfdef]; simpa using sub_neg.2 hlt
    have hpm : posMul (f x) = 0 := by
      rw [posMul, if_neg (by linarith), if_neg (by linarith)]
    rw [hminx, hmaxx, hpm, if_pos hlt.le, if_pos hlt.le]
    simp
  · have hg := hequal heq
    have hfx0 : f x = 0 := by rw [hfx]; linarith
    have h0 : max (f x) 0 = 0 := by rw [hfx0]; simp
    have hz : weakGrad f x = 0 := by
      have hst := hstx h0
      rw [hpgx, hfx0] at hst
      have hpm : posMul (0 : ℝ) = 1 / 2 := by rw [posMul]; norm_num
      rw [hpm] at hst
      have h2 : (1 / 2 : ℝ) ≠ 0 := by norm_num
      simpa [h2] using hst
    rw [hminx, hmaxx, hz, if_pos heq.le, if_pos heq.le, smul_zero, sub_zero, add_zero, hg]
    exact ⟨rfl, rfl⟩
  · have hfpos : 0 < f x := by rw [hfdef]; simpa using sub_pos.2 hgt
    have hpm : posMul (f x) = 1 := by rw [posMul, if_pos hfpos]
    rw [hminx, hmaxx, hpm, if_neg (by linarith), if_neg (by linarith), one_smul, hfgx]
    constructor
    · abel
    · abel

/-! ### Uniqueness -/

set_option maxHeartbeats 800000 in
/-- **(L1, `reg/variational`)** Uniqueness of the minimizer of the regularized energy.  This
is the frozen statement `IsRegMinimizer.ae_eq` of the interface. -/
theorem IsRegMinimizer.ae_eq (hκ : 0 < κ) (hΨ : IsRegProfile Ψ) (hK : IsGoodConvex K)
    (hu : IsRegMinimizer 2 κ Ψ K u) (hv : IsRegMinimizer 2 κ Ψ K v) :
    u =ᵐ[volume] v := by
  obtain ⟨c, C, h⟩ := hΨ.exists_isRegProfileWith
  have hKm := hK.measurableSet'
  have hKv := hK.volume_ne_top
  obtain ⟨hminmem, hmaxmem, hgrads⟩ := memW0_min_max hKm hKv hu.memW0 hv.memW0
  have hmin0 : ∀ x, 0 ≤ min (u x) (v x) := fun x => le_min (hu.nonneg x) (hv.nonneg x)
  have hmax0 : ∀ x, 0 ≤ max (u x) (v x) := fun x => le_trans (hu.nonneg x) (le_max_left _ _)
  have hminK : ∀ x, x ∉ K → min (u x) (v x) = 0 := fun x hx => by
    rw [hu.eq_zero_of_notMem x hx, hv.eq_zero_of_notMem x hx, min_self]
  have hmaxK : ∀ x, x ∉ K → max (u x) (v x) = 0 := fun x hx => by
    rw [hu.eq_zero_of_notMem x hx, hv.eq_zero_of_notMem x hx, max_self]
  obtain ⟨hIQ1, hIP1, hineq1⟩ := energy_ge_of_memW0_gen h hκ hK hminmem hmin0 hminK
  obtain ⟨hIQ2, hIP2, hineq2⟩ := energy_ge_of_memW0_gen h hκ hK hmaxmem hmax0 hmaxK
  have hIQu := hu.integrable_kinetic h hK
  have hIPu := hu.integrable_entropy hκ.le hK
  have hIQv := hv.integrable_kinetic h hK
  have hIPv := hv.integrable_entropy hκ.le hK
  -- the squares
  have hsqpt : ∀ x, min (u x) (v x) ^ 2 + max (u x) (v x) ^ 2 = u x ^ 2 + v x ^ 2 := by
    intro x
    rcases le_total (u x) (v x) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle]; ring
  have hminsq : Integrable (fun x => min (u x) (v x) ^ 2) volume := by
    refine Integrable.mono' hu.integrable_sq
      (((hminmem.memLp.aestronglyMeasurable.aemeasurable).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hmin0 x, min_le_left (u x) (v x)]
  have hmaxsq : Integrable (fun x => max (u x) (v x) ^ 2) volume := by
    refine Integrable.mono' (hu.integrable_sq.add hv.integrable_sq)
      (((hmaxmem.memLp.aestronglyMeasurable.aemeasurable).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    show max (u x) (v x) ^ 2 ≤ (fun y => u y ^ 2) x + (fun y => v y ^ 2) x
    have h1 := hsqpt x
    have h2 : (0 : ℝ) ≤ min (u x) (v x) ^ 2 := sq_nonneg _
    linarith
  have hNsum : (∫ x, min (u x) (v x) ^ 2) + ∫ x, max (u x) (v x) ^ 2 = 2 := by
    rw [← integral_add hminsq hmaxsq]
    have h2 : (2 : ℝ) = (∫ x, u x ^ 2) + ∫ x, v x ^ 2 := by
      rw [hu.integral_sq, hv.integral_sq]; norm_num
    rw [h2, ← integral_add hu.integrable_sq hv.integrable_sq]
    exact integral_congr_ae (Eventually.of_forall hsqpt)
  -- the energy splits
  have hQpt : ∀ᵐ x, Korevaar.homogeneousDensity 2 Ψ (min (u x) (v x))
        (weakGrad (fun y => min (u y) (v y)) x)
      + Korevaar.homogeneousDensity 2 Ψ (max (u x) (v x))
        (weakGrad (fun y => max (u y) (v y)) x)
      = Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x)
        + Korevaar.homogeneousDensity 2 Ψ (v x) (weakGrad v x) := by
    filter_upwards [hgrads] with x hx
    rcases le_or_gt (u x) (v x) with hle | hgt
    · rw [hx.1, hx.2, if_pos hle, if_pos hle, min_eq_left hle, max_eq_right hle]
    · rw [hx.1, hx.2, if_neg (not_le.2 hgt), if_neg (not_le.2 hgt), min_eq_right hgt.le,
        max_eq_left hgt.le]
      ring
  have hPpt : ∀ x, Korevaar.entropyPotential 2 κ (min (u x) (v x))
      + Korevaar.entropyPotential 2 κ (max (u x) (v x))
      = Korevaar.entropyPotential 2 κ (u x) + Korevaar.entropyPotential 2 κ (v x) := by
    intro x
    rcases le_total (u x) (v x) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle]; ring
  have hQsum : (∫ x, Korevaar.homogeneousDensity 2 Ψ (min (u x) (v x))
          (weakGrad (fun y => min (u y) (v y)) x))
        + ∫ x, Korevaar.homogeneousDensity 2 Ψ (max (u x) (v x))
          (weakGrad (fun y => max (u y) (v y)) x)
      = (∫ x, Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x))
        + ∫ x, Korevaar.homogeneousDensity 2 Ψ (v x) (weakGrad v x) := by
    rw [← integral_add hIQ1 hIQ2, ← integral_add hIQu hIQv]
    exact integral_congr_ae hQpt
  have hPsum : (∫ x, Korevaar.entropyPotential 2 κ (min (u x) (v x)))
        + ∫ x, Korevaar.entropyPotential 2 κ (max (u x) (v x))
      = (∫ x, Korevaar.entropyPotential 2 κ (u x))
        + ∫ x, Korevaar.entropyPotential 2 κ (v x) := by
    rw [← integral_add hIP1 hIP2, ← integral_add hIPu hIPv]
    exact integral_congr_ae (Eventually.of_forall hPpt)
  have hEu : (∫ x, Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x))
      + ∫ x, Korevaar.entropyPotential 2 κ (u x) = regMin 2 κ Ψ K := hu.energy_eq
  have hEv : (∫ x, Korevaar.homogeneousDensity 2 Ψ (v x) (weakGrad v x))
      + ∫ x, Korevaar.entropyPotential 2 κ (v x) = regMin 2 κ Ψ K := hv.energy_eq
  -- `N₁ = 1`
  have hN1nn : (0 : ℝ) ≤ ∫ x, min (u x) (v x) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hN2nn : (0 : ℝ) ≤ ∫ x, max (u x) (v x) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hN1 : (∫ x, min (u x) (v x) ^ 2) = 1 := by
    by_contra hne
    have hs1 := sub_one_lt_mul_log hN1nn hne
    have hs2 := sub_one_le_mul_log hN2nn
    have hsumE :
        ((∫ x, Korevaar.homogeneousDensity 2 Ψ (min (u x) (v x))
            (weakGrad (fun y => min (u y) (v y)) x))
          + ∫ x, Korevaar.entropyPotential 2 κ (min (u x) (v x)))
        + ((∫ x, Korevaar.homogeneousDensity 2 Ψ (max (u x) (v x))
            (weakGrad (fun y => max (u y) (v y)) x))
          + ∫ x, Korevaar.entropyPotential 2 κ (max (u x) (v x)))
        = 2 * regMin 2 κ Ψ K := by linarith [hQsum, hPsum, hEu, hEv]
    have hNm : (∫ x, min (u x) (v x) ^ 2) * regMin 2 κ Ψ K
        + (∫ x, max (u x) (v x) ^ 2) * regMin 2 κ Ψ K = 2 * regMin 2 κ Ψ K := by
      have hh : ((∫ x, min (u x) (v x) ^ 2) + ∫ x, max (u x) (v x) ^ 2) * regMin 2 κ Ψ K
          = 2 * regMin 2 κ Ψ K := by rw [hNsum]
      linarith [hh]
    have hposS : 0 < (∫ x, min (u x) (v x) ^ 2) * Real.log (∫ x, min (u x) (v x) ^ 2)
        + (∫ x, max (u x) (v x) ^ 2) * Real.log (∫ x, max (u x) (v x) ^ 2) := by
      linarith [hs1, hs2, hNsum]
    have hkey : κ / 4 * ((∫ x, min (u x) (v x) ^ 2) * Real.log (∫ x, min (u x) (v x) ^ 2)
        + (∫ x, max (u x) (v x) ^ 2) * Real.log (∫ x, max (u x) (v x) ^ 2)) ≤ 0 := by
      linarith [hineq1, hineq2, hsumE, hNm]
    have hpos2 : 0 < κ / 4 * ((∫ x, min (u x) (v x) ^ 2) * Real.log (∫ x, min (u x) (v x) ^ 2)
        + (∫ x, max (u x) (v x) ^ 2) * Real.log (∫ x, max (u x) (v x) ^ 2)) :=
      mul_pos (by linarith) hposS
    linarith
  -- conclude
  have hdiffu : ∀ x, 0 ≤ u x ^ 2 - min (u x) (v x) ^ 2 := by
    intro x
    nlinarith [hmin0 x, min_le_left (u x) (v x)]
  have hdiffv : ∀ x, 0 ≤ v x ^ 2 - min (u x) (v x) ^ 2 := by
    intro x
    nlinarith [hmin0 x, min_le_right (u x) (v x)]
  have hzu : (fun x => u x ^ 2 - min (u x) (v x) ^ 2) =ᵐ[volume] 0 := by
    refine (integral_eq_zero_iff_of_nonneg hdiffu (hu.integrable_sq.sub hminsq)).1 ?_
    rw [integral_sub hu.integrable_sq hminsq, hu.integral_sq, hN1]
    ring
  have hzv : (fun x => v x ^ 2 - min (u x) (v x) ^ 2) =ᵐ[volume] 0 := by
    refine (integral_eq_zero_iff_of_nonneg hdiffv (hv.integrable_sq.sub hminsq)).1 ?_
    rw [integral_sub hv.integrable_sq hminsq, hv.integral_sq, hN1]
    ring
  filter_upwards [hzu, hzv] with x hxu hxv
  have hxu' : u x ^ 2 = min (u x) (v x) ^ 2 := by
    have : u x ^ 2 - min (u x) (v x) ^ 2 = 0 := hxu
    linarith
  have hxv' : v x ^ 2 = min (u x) (v x) ^ 2 := by
    have : v x ^ 2 - min (u x) (v x) ^ 2 = 0 := hxv
    linarith
  have h1 : u x = min (u x) (v x) := by
    have := congrArg Real.sqrt hxu'
    rwa [Real.sqrt_sq (hu.nonneg x), Real.sqrt_sq (hmin0 x)] at this
  have h2 : v x = min (u x) (v x) := by
    have := congrArg Real.sqrt hxv'
    rwa [Real.sqrt_sq (hv.nonneg x), Real.sqrt_sq (hmin0 x)] at this
  exact h1.trans h2.symm

end Komlos.Literature.Regularized
