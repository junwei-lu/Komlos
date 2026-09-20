import Komlos.Literature.PLaplacian.RegularityInteriorAux

/-!
# Real-analysis inputs of the Moser iteration

Auxiliary facts for the global boundedness of weak eigensolutions
(`Komlos.Literature.IsWeakEigensolution.exists_ae_le`, Moser iteration; Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, proof of Theorem 8.15), on the way to
Mosconi–Riey–Squassina 2024, Proposition 4.5 (paper Appendix A, *Eigenfunction inputs*).

* `moserDeriv β k s = β min(|s|, k)^{β-1}`, the truncated power `moserPow β k t = ∫₀ᵗ moserDeriv`
  (equal to `t^β` for `0 ≤ t ≤ k`, affine beyond `k`) and the test function
  `moserTest p β k t = ∫₀ᵗ moserDeriv^p`; both are `C¹` with bounded derivative and vanish at `0`,
  so the chain rule `memW0_comp` applies to them.
* `rpow_mul_moserTest_le` — the key pointwise inequality `t^{p-1} G(t) ≤ β^p H(t)^p`.
* `exists_iterate_bound` — the product bound of the iteration: `N_{j+1} ≤ D^{(j+1)κ^{-j}} N_j`
  implies `N_n ≤ B N_0`.
* `ae_le_of_eLpNorm_le` — uniform `L^{q_n}` bounds with `q_n → ∞` give an `L^∞` bound (Chebyshev).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Komlos.Literature

/-! ### Truncated powers -/

/-- The derivative `β min(|s|, k)^{β-1}` of the truncated power `moserPow β k`. -/
noncomputable def moserDeriv (β k s : ℝ) : ℝ := β * min |s| k ^ (β - 1)

/-- The truncated power `H(t) = ∫₀ᵗ β min(|s|, k)^{β-1} ds` of the Moser iteration: `H(t) = t^β`
for `0 ≤ t ≤ k`, and `H` is affine for `t ≥ k`. -/
noncomputable def moserPow (β k t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, moserDeriv β k s

/-- The Moser test function `G(t) = ∫₀ᵗ (H')^p`, so that `G' = (H')^p` and testing the equation
with `G(u)` controls `∫ F(∇H(u))^p`. -/
noncomputable def moserTest (p β k t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, moserDeriv β k s ^ p

variable {β k : ℝ}

theorem continuous_moserDeriv (hβ : 1 ≤ β) : Continuous (moserDeriv β k) :=
  continuous_const.mul
    ((continuous_abs.min continuous_const).rpow_const fun _ => Or.inr (sub_nonneg.2 hβ))

theorem moserDeriv_nonneg (hβ : 1 ≤ β) (hk : 0 ≤ k) (s : ℝ) : 0 ≤ moserDeriv β k s :=
  mul_nonneg (by linarith) (Real.rpow_nonneg (le_min (abs_nonneg s) hk) _)

theorem moserDeriv_le (hβ : 1 ≤ β) (hk : 0 ≤ k) (s : ℝ) : moserDeriv β k s ≤ β * k ^ (β - 1) :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_min (abs_nonneg s) hk) (min_le_right _ _)
    (sub_nonneg.2 hβ)) (by linarith)

theorem moserDeriv_mono (hβ : 1 ≤ β) (hk : 0 ≤ k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    moserDeriv β k s ≤ moserDeriv β k t := by
  unfold moserDeriv
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_min (abs_nonneg s) hk) ?_
    (sub_nonneg.2 hβ)) (by linarith)
  rw [abs_of_nonneg hs, abs_of_nonneg (hs.trans hst)]
  exact min_le_min hst le_rfl

theorem continuous_moserDeriv_rpow (hβ : 1 ≤ β) {p : ℝ} (hp : 0 ≤ p) :
    Continuous fun s => moserDeriv β k s ^ p :=
  (continuous_moserDeriv hβ).rpow_const fun _ => Or.inr hp

theorem hasDerivAt_moserPow (hβ : 1 ≤ β) (t : ℝ) :
    HasDerivAt (moserPow β k) (moserDeriv β k t) t :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_moserDeriv hβ).intervalIntegrable _ _)
    ((continuous_moserDeriv hβ).stronglyMeasurableAtFilter _ _)
    (continuous_moserDeriv hβ).continuousAt

theorem hasDerivAt_moserTest (hβ : 1 ≤ β) {p : ℝ} (hp : 0 ≤ p) (t : ℝ) :
    HasDerivAt (moserTest p β k) (moserDeriv β k t ^ p) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_moserDeriv_rpow hβ hp).intervalIntegrable _ _)
    ((continuous_moserDeriv_rpow hβ hp).stronglyMeasurableAtFilter _ _)
    (continuous_moserDeriv_rpow hβ hp).continuousAt

theorem deriv_moserPow (hβ : 1 ≤ β) : deriv (moserPow β k) = moserDeriv β k :=
  funext fun t => (hasDerivAt_moserPow hβ t).deriv

theorem deriv_moserTest (hβ : 1 ≤ β) {p : ℝ} (hp : 0 ≤ p) :
    deriv (moserTest p β k) = fun s => moserDeriv β k s ^ p :=
  funext fun t => (hasDerivAt_moserTest hβ hp t).deriv

theorem contDiff_moserPow (hβ : 1 ≤ β) : ContDiff ℝ 1 (moserPow β k) :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_moserPow hβ t).differentiableAt, by
    rw [deriv_moserPow hβ]
    exact continuous_moserDeriv hβ⟩

theorem contDiff_moserTest (hβ : 1 ≤ β) {p : ℝ} (hp : 0 ≤ p) : ContDiff ℝ 1 (moserTest p β k) :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_moserTest hβ hp t).differentiableAt, by
    rw [deriv_moserTest hβ hp]
    exact continuous_moserDeriv_rpow hβ hp⟩

theorem moserPow_zero : moserPow β k 0 = 0 := intervalIntegral.integral_same

theorem moserTest_zero {p : ℝ} : moserTest p β k 0 = 0 := intervalIntegral.integral_same

theorem moserPow_nonneg (hβ : 1 ≤ β) (hk : 0 ≤ k) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ moserPow β k t :=
  intervalIntegral.integral_nonneg ht fun s _ => moserDeriv_nonneg hβ hk s

theorem moserTest_nonneg (hβ : 1 ≤ β) (hk : 0 ≤ k) {p : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ moserTest p β k t :=
  intervalIntegral.integral_nonneg ht fun s _ => Real.rpow_nonneg (moserDeriv_nonneg hβ hk s) _

/-- `∫₀ᵗ β s^{β-1} ds = t^β`. -/
theorem integral_mul_rpow_sub_one (hβ : 1 ≤ β) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, β * s ^ (β - 1) = t ^ β := by
  have hβ0 : β ≠ 0 := (zero_lt_one.trans_le hβ).ne'
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow hβ0, sub_zero]
  field_simp

theorem continuous_mul_rpow_sub_one (hβ : 1 ≤ β) : Continuous fun s : ℝ => β * s ^ (β - 1) :=
  continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (sub_nonneg.2 hβ))

/-- The truncated power lies below the power: `H(t) ≤ t^β` for `t ≥ 0`. -/
theorem moserPow_le_rpow (hβ : 1 ≤ β) (hk : 0 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    moserPow β k t ≤ t ^ β := by
  rw [← integral_mul_rpow_sub_one hβ t]
  refine intervalIntegral.integral_mono_on ht ((continuous_moserDeriv hβ).intervalIntegrable _ _)
    ((continuous_mul_rpow_sub_one hβ).intervalIntegrable _ _) fun s hs => ?_
  unfold moserDeriv
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_min (abs_nonneg s) hk) ?_
    (sub_nonneg.2 hβ)) (by linarith)
  rw [abs_of_nonneg hs.1]
  exact min_le_left _ _

/-- The truncated power is the power below the truncation level: `H(t) = t^β` for `0 ≤ t ≤ k`. -/
theorem moserPow_eq_rpow (hβ : 1 ≤ β) {t : ℝ} (ht : 0 ≤ t) (htk : t ≤ k) :
    moserPow β k t = t ^ β := by
  rw [← integral_mul_rpow_sub_one hβ t]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  simp only [moserDeriv, abs_of_nonneg hs.1, min_eq_left (hs.2.trans htk)]

/-- `t H'(t) ≤ β H(t)` for `t ≥ 0` (`min(s, k) ≥ (s/t) min(t, k)` on `[0, t]`). -/
theorem mul_moserDeriv_le (hβ : 1 ≤ β) (hk : 0 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    t * moserDeriv β k t ≤ β * moserPow β k t := by
  rcases ht.eq_or_lt with rfl | ht'
  · simp [moserPow]
  have hβ1 : 0 ≤ β - 1 := sub_nonneg.2 hβ
  have hm0 : 0 ≤ min t k := le_min ht hk
  have key : ∫ s in (0 : ℝ)..t, (min t k / t) ^ (β - 1) * (β * s ^ (β - 1)) ≤
      moserPow β k t := by
    refine intervalIntegral.integral_mono_on ht
      ((continuous_const.mul (continuous_mul_rpow_sub_one hβ)).intervalIntegrable _ _)
      ((continuous_moserDeriv hβ).intervalIntegrable _ _) fun s hs => ?_
    have hs0 : 0 ≤ s := hs.1
    have hmt : 0 ≤ min t k / t := div_nonneg hm0 ht
    have hmin : s * (min t k / t) ≤ min |s| k := by
      rw [abs_of_nonneg hs0]
      rcases le_total s k with hsk | hsk
      · rw [min_eq_left hsk]
        have h1 : min t k / t ≤ 1 := (div_le_one ht').2 (min_le_left _ _)
        calc s * (min t k / t) ≤ s * 1 := mul_le_mul_of_nonneg_left h1 hs0
          _ = s := mul_one s
      · rw [min_eq_right hsk, min_eq_right (hsk.trans hs.2)]
        calc s * (k / t) = k * (s / t) := by ring
          _ ≤ k * 1 := mul_le_mul_of_nonneg_left ((div_le_one ht').2 hs.2) hk
          _ = k := mul_one k
    have h1 : (min t k / t) ^ (β - 1) * (β * s ^ (β - 1)) = β * (s * (min t k / t)) ^ (β - 1) := by
      rw [Real.mul_rpow hs0 hmt]
      ring
    rw [h1]
    unfold moserDeriv
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_nonneg hs0 hmt) hmin hβ1)
      (by linarith)
  rw [intervalIntegral.integral_const_mul, integral_mul_rpow_sub_one hβ t] at key
  have htβ : t ^ β = t ^ (β - 1) * t := by
    rw [← Real.rpow_add_one ht'.ne', sub_add_cancel]
  have htpos : 0 < t ^ (β - 1) := Real.rpow_pos_of_pos ht' _
  have h2 : (min t k / t) ^ (β - 1) * t ^ β = min t k ^ (β - 1) * t := by
    rw [Real.div_rpow hm0 ht, htβ]
    field_simp
  have hder : moserDeriv β k t = β * min t k ^ (β - 1) := by
    simp only [moserDeriv, abs_of_nonneg ht]
  rw [hder]
  calc t * (β * min t k ^ (β - 1)) = β * (min t k ^ (β - 1) * t) := by ring
    _ = β * ((min t k / t) ^ (β - 1) * t ^ β) := by rw [h2]
    _ ≤ β * moserPow β k t := mul_le_mul_of_nonneg_left key (by linarith)

/-- `G(t) ≤ H'(t)^{p-1} H(t)` for `t ≥ 0` (`H'` is nondecreasing on `[0, t]`). -/
theorem moserTest_le (hβ : 1 ≤ β) (hk : 0 ≤ k) {p : ℝ} (hp : 1 ≤ p) {t : ℝ} (ht : 0 ≤ t) :
    moserTest p β k t ≤ moserDeriv β k t ^ (p - 1) * moserPow β k t := by
  unfold moserTest moserPow
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on ht
    ((continuous_moserDeriv_rpow hβ (by linarith)).intervalIntegrable _ _)
    ((continuous_const.mul (continuous_moserDeriv hβ)).intervalIntegrable _ _) fun s hs => ?_
  have h0 := moserDeriv_nonneg hβ hk s
  have h1 : moserDeriv β k s ^ p = moserDeriv β k s ^ (p - 1) * moserDeriv β k s := by
    rw [← Real.rpow_add_one' h0 (ne_of_gt (by linarith)), sub_add_cancel]
  rw [h1]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow h0 (moserDeriv_mono hβ hk hs.1 hs.2) (by linarith)) h0

/-- **The Moser pointwise inequality**: `t^{p-1} G(t) ≤ β^p H(t)^p` for `t ≥ 0`. -/
theorem rpow_mul_moserTest_le (hβ : 1 ≤ β) (hk : 0 ≤ k) {p : ℝ} (hp : 1 ≤ p) {t : ℝ}
    (ht : 0 ≤ t) : t ^ (p - 1) * moserTest p β k t ≤ β ^ p * moserPow β k t ^ p := by
  have hH := moserPow_nonneg hβ hk ht
  have hh := moserDeriv_nonneg hβ hk t
  have hp1 : 0 ≤ p - 1 := by linarith
  calc t ^ (p - 1) * moserTest p β k t
      ≤ t ^ (p - 1) * (moserDeriv β k t ^ (p - 1) * moserPow β k t) :=
        mul_le_mul_of_nonneg_left (moserTest_le hβ hk hp ht) (Real.rpow_nonneg ht _)
    _ = (t * moserDeriv β k t) ^ (p - 1) * moserPow β k t := by
        rw [Real.mul_rpow ht hh]
        ring
    _ ≤ (β * moserPow β k t) ^ (p - 1) * moserPow β k t :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (mul_nonneg ht hh) (mul_moserDeriv_le hβ hk ht) hp1) hH
    _ = β ^ (p - 1) * moserPow β k t ^ p := by
        rw [Real.mul_rpow (by linarith) hH, mul_assoc,
          ← Real.rpow_add_one' hH (ne_of_gt (by linarith)), sub_add_cancel]
    _ ≤ β ^ p * moserPow β k t ^ p :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hβ (by linarith))
          (Real.rpow_nonneg hH _)

/-- As the truncation level `k = n + 1 → ∞`, `H(t) → t^β` (eventually equal). -/
theorem tendsto_moserPow (hβ : 1 ≤ β) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => moserPow β ((n : ℝ) + 1) t) atTop (𝓝 (t ^ β)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈t⌉₊] with n hn
  have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have h2 : (⌈t⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
  exact (moserPow_eq_rpow hβ ht (by linarith)).symm

/-! ### The iteration -/

/-- **The product bound of the Moser iteration**: if `N (j+1) ≤ D^{(j+1) κ^{-j}} N j` with
`D ≥ 1` and `κ > 1`, then `N n ≤ B N 0` for all `n`, with `B = D^{∑ (j+1) κ^{-j}}`. -/
theorem exists_iterate_bound {N : ℕ → ℝ≥0∞} {D κ : ℝ} (hD : 1 ≤ D) (hκ : 1 < κ)
    (hstep : ∀ j : ℕ, N (j + 1) ≤ ENNReal.ofReal (D ^ (((j : ℝ) + 1) * κ⁻¹ ^ j)) * N j) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, N n ≤ ENNReal.ofReal B * N 0 := by
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
  refine ⟨D ^ (∑' j : ℕ, ((j : ℝ) + 1) * κ⁻¹ ^ j), Real.rpow_nonneg hD0.le _, fun n => ?_⟩
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
        _ = ENNReal.ofReal (D ^ (∑ j ∈ Finset.range (n + 1), ((j : ℝ) + 1) * κ⁻¹ ^ j)) * N 0 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD0.le _),
            ← Real.rpow_add hD0, Finset.sum_range_succ,
            add_comm (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * κ⁻¹ ^ j)]
  refine (hpart n).trans ?_
  gcongr
  exact hsum.sum_le_tsum (Finset.range n) fun j _ => mul_nonneg (by positivity) (pow_nonneg hr0 j)

/-- From `N₁^z ≤ D N₀^z` with `z > 0` and `D ≥ 0`, deduce `N₁ ≤ D^{1/z} N₀`. -/
theorem le_ofReal_rpow_inv_mul_of_rpow_le {N₁ N₀ : ℝ≥0∞} {z : ℝ} (hz : 0 < z) {D : ℝ}
    (hD : 0 ≤ D) (h : N₁ ^ z ≤ ENNReal.ofReal D * N₀ ^ z) :
    N₁ ≤ ENNReal.ofReal (D ^ z⁻¹) * N₀ := by
  rw [← ENNReal.rpow_le_rpow_iff hz, ENNReal.mul_rpow_of_nonneg _ _ hz.le,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hD _) hz.le, ← Real.rpow_mul hD,
    inv_mul_cancel₀ hz.ne', Real.rpow_one]
  exact h

/-- **`L^∞` bounds from uniform `L^{q_n}` bounds** (Chebyshev): if `‖u‖_{L^{q_n}} ≤ B` for a
sequence of exponents `q_n → ∞`, then `u ≤ B` almost everywhere. -/
theorem ae_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    (hu : AEStronglyMeasurable u μ) {q : ℕ → ℝ} (hq0 : ∀ n, 0 < q n)
    (hq : Tendsto q atTop atTop) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, eLpNorm u (ENNReal.ofReal (q n)) μ ≤ ENNReal.ofReal B) :
    ∀ᵐ x ∂μ, u x ≤ B := by
  have key : ∀ ε : ℝ, 0 < ε → μ {x | ENNReal.ofReal (B + ε) ≤ ‖u x‖ₑ} = 0 := by
    intro ε hε
    have hBε : 0 < B + ε := by linarith
    have hn : ∀ n, μ {x | ENNReal.ofReal (B + ε) ≤ ‖u x‖ₑ} ≤
        ENNReal.ofReal ((B / (B + ε)) ^ q n) := by
      intro n
      have hq' : ENNReal.ofReal (q n) ≠ 0 := by simpa using hq0 n
      have h1 := mul_meas_ge_le_pow_eLpNorm' μ hq' ENNReal.ofReal_ne_top hu
        (ENNReal.ofReal (B + ε))
      rw [ENNReal.toReal_ofReal (hq0 n).le,
        ENNReal.ofReal_rpow_of_nonneg hBε.le (hq0 n).le] at h1
      have h2 : eLpNorm u (ENNReal.ofReal (q n)) μ ^ q n ≤ ENNReal.ofReal (B ^ q n) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hB (hq0 n).le]
        exact ENNReal.rpow_le_rpow (hbound n) (hq0 n).le
      have hpos : 0 < (B + ε) ^ q n := Real.rpow_pos_of_pos hBε _
      calc μ {x | ENNReal.ofReal (B + ε) ≤ ‖u x‖ₑ}
          = ENNReal.ofReal ((B + ε) ^ q n)⁻¹ *
              (ENNReal.ofReal ((B + ε) ^ q n) * μ {x | ENNReal.ofReal (B + ε) ≤ ‖u x‖ₑ}) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hpos.le),
              inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal ((B + ε) ^ q n)⁻¹ * ENNReal.ofReal (B ^ q n) := by
            gcongr
            exact h1.trans h2
        _ = ENNReal.ofReal ((B / (B + ε)) ^ q n) := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.2 hpos.le), Real.div_rpow hB hBε.le,
              div_eq_inv_mul]
    have hlim : Tendsto (fun n => ENNReal.ofReal ((B / (B + ε)) ^ q n)) atTop (𝓝 0) := by
      have hb1 : B / (B + ε) < 1 := (div_lt_one hBε).2 (by linarith)
      have h1 := (tendsto_rpow_atTop_of_base_lt_one _
        (by linarith [div_nonneg hB hBε.le]) hb1).comp hq
      have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      simpa [Function.comp_def] using h2
    exact le_antisymm (ge_of_tendsto' hlim hn) bot_le
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_)
    (measure_iUnion_null fun n : ℕ => key (1 / ((n : ℝ) + 1)) (by positivity))
  have hlt : B < u x := not_le.1 hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
  refine mem_iUnion.2 ⟨n, ?_⟩
  show ENNReal.ofReal (B + 1 / ((n : ℝ) + 1)) ≤ ‖u x‖ₑ
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  linarith [le_abs_self (u x)]

end Komlos.Literature
