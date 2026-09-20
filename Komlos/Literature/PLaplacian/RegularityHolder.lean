import Komlos.Literature.PLaplacian.RegularityHolderAux
import Komlos.Literature.PLaplacian.RegularityCampanato
import Komlos.Literature.PLaplacian.HolderExcessAux

/-!
# Hölder continuity of bounded weak eigensolutions (De Giorgi–Nash–Moser)

Towards Mosconi–Riey–Squassina 2024, Proposition 4.5 (paper Appendix A, *Eigenfunction inputs*):
a bounded nonnegative weak solution `u ∈ W₀^{1,p}(K)` of `-div a(∇u) = λ u^{p-1}` on an open set
`K` has a representative that is locally Hölder continuous in `K` (Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Theorem 8.22; for the `p`-Laplacian structure
Serrin 1964 and Trudinger 1967).

## Main results

* `holder_solution` — **interior `C^{0,α}`** (proved): a representative of `u` that is continuous
  in `K` and Hölder continuous on every compact subset of `K`.
* `exists_holder_representative` — a bounded measurable function whose oscillation on small
  balls decays like `(r/R₀)^α` has such a representative (limits of ball averages, Lebesgue
  differentiation).

The interior `C^{1,α}` half of this file (`gradExcess`, `holder_gradient_of_continuous`,
`holder_gradient`, `IsWeakEigensolution.campanato_weakGrad` and the excess machinery) belonged
to the degenerate `p`-Laplacian route: it rested on `exists_degiorgi_uniform_flux_energy_bounds`
(`DiffQuotCaccioppoli.lean`), which was never proved. The regularized route of
`REGULARIZED_ROUTE.md` (Revision 2) replaced that route, and lane `L7` deleted the section
together with its dependency cone (`ExcessDecay.lean`, `ReplacementComparison.lean`,
`PHarmonicDecay.lean`, `DiffQuotCaccioppoli.lean`); see
`Komlos/Literature/Regularized/NOTES_integrate.md`. Nothing that survives used it.

## Proof of `holder_solution`

* `measure_mul_lintegral_log_le` — on `closedBall x₀ (2R)`, the Poincaré inequality
  (`MemW0.measure_mul_lintegral_sub_rpow_le`) applied to `log(w + ε)` for a level function
  `w = σ(u - k) ∈ [0, om]` and the logarithmic Caccioppoli estimate at scale `R`
  (`log_caccioppoli_level`) bound `|E| ∫ ((log(a + ε) - log(w + ε))^+)^p`, where `w ≥ a` on `E`,
  by a constant times `R^{d} |B_{2R}|`.
* `exists_level_lower_bound` — if `w ≥ om/2` on a fixed fraction of `ball x₀ R`, then
  `w ≥ c₁ om - (|λ| S^{p-1} R^p)^{1/(p-1)}` a.e. on `ball x₀ R`: the logarithmic bound
  (`lintegral_log_level_le`, `lintegral_W_level_le`) feeds the scale-invariant Moser sup bound
  `moser_level_sup` of `RegularityHolderAux` for `log(2(om + ε)) - log(w + ε)`.
* `exists_osc_decay` — De Giorgi's alternative: the oscillation of `u` on `ball x₀ R` is at most
  `(1 - c₁) om + (|λ| S^{p-1} R^p)^{1/(p-1)}` if it is at most `om` on `closedBall x₀ (3R)`.
* `exists_holder_osc` — iterating on the radii `R₀ 4^{-n}` bounds the oscillation on `ball x₀ r`
  by `C₀ (r/R₀)^α`; `exists_holder_representative` then gives `holder_solution`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Integrals of rescaled cutoffs -/

/-- `∫ η^{m-p} |∇η|^p ≤ g^p |B|` for a cutoff `0 ≤ η ≤ 1` supported in `B` with `|∇η| ≤ g`. -/
theorem integral_cutoff_weight_le {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η)
    {B : Set (Euc d)} (hBm : MeasurableSet B) (hBfin : volume B ≠ ⊤) (hηB : tsupport η ⊆ B)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {g : ℝ} (hg : ∀ x, ‖gradient η x‖ ≤ g) {p : ℝ}
    (hp0 : 0 < p) {m : ℕ} (hmp : p ≤ m) :
    ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p ≤ g ^ p * (volume B).toReal := by
  have hη1' : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hmp' : 0 ≤ (m : ℝ) - p := sub_nonneg.2 hmp
  have hint : Integrable (B.indicator fun _ => g ^ p) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  calc ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p ≤ ∫ x, B.indicator (fun _ => g ^ p) x := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => mul_nonneg
          (Real.rpow_nonneg (hη0 x) _) (Real.rpow_nonneg (norm_nonneg _) _)) hint
          (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ B
        · show η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p ≤ B.indicator (fun _ => g ^ p) x
          rw [indicator_of_mem hx]
          calc η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p ≤ 1 * g ^ p :=
                mul_le_mul (Real.rpow_le_one (hη0 x) (hη1 x) hmp')
                  (Real.rpow_le_rpow (norm_nonneg _) (hg x) hp0.le)
                  (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one
            _ = g ^ p := one_mul _
        · show η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p ≤ B.indicator (fun _ => g ^ p) x
          rw [indicator_of_notMem hx, gradient_eq_zero_of_notMem_tsupport (fun h => hx (hηB h)),
            norm_zero, Real.zero_rpow hp0.ne', mul_zero]
    _ = g ^ p * (volume B).toReal := by
        rw [integral_indicator_const _ hBm, smul_eq_mul, mul_comm, Measure.real]

/-- `∫ η^m ≤ |B|` for a cutoff `0 ≤ η ≤ 1` supported in `B`. -/
theorem integral_cutoff_pow_le {η : Euc d → ℝ} {B : Set (Euc d)} (hBm : MeasurableSet B)
    (hBfin : volume B ≠ ⊤) (hηB : tsupport η ⊆ B) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    {m : ℕ} (hm0 : m ≠ 0) :
    ∫ x, η x ^ m ≤ (volume B).toReal := by
  have hint : Integrable (B.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  calc ∫ x, η x ^ m ≤ ∫ x, B.indicator (fun _ => (1 : ℝ)) x := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => pow_nonneg (hη0 x) m) hint
          (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ B
        · show η x ^ m ≤ B.indicator (fun _ => (1 : ℝ)) x
          rw [indicator_of_mem hx]
          exact pow_le_one₀ (hη0 x) (hη1 x)
        · show η x ^ m ≤ B.indicator (fun _ => (1 : ℝ)) x
          rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hηB h)),
            zero_pow hm0]
    _ = (volume B).toReal := by
        rw [integral_indicator_const _ hBm, smul_eq_mul, mul_one, Measure.real]

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- `|λ| S^{p-1} R^p ≤ ε^{p-1}` gives `|λ| S^{p-1} ε^{1-p} ≤ R^{-p}`. -/
theorem lam_mul_rpow_le_of_le {S R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hΛ : |lam| * S ^ (p - 1) * R ^ p ≤ ε ^ (p - 1)) :
    |lam| * S ^ (p - 1) * ε ^ (1 - p) ≤ (R ^ p)⁻¹ := by
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  have hε1 : ε ^ (p - 1) * ε ^ (1 - p) = 1 := by
    rw [← Real.rpow_add hε, show p - 1 + (1 - p) = (0 : ℝ) by ring, Real.rpow_zero]
  have hεpos : 0 < ε ^ (1 - p) := Real.rpow_pos_of_pos hε _
  have hRp' := hRp.ne'
  calc |lam| * S ^ (p - 1) * ε ^ (1 - p) =
        (|lam| * S ^ (p - 1) * R ^ p) * ε ^ (1 - p) * (R ^ p)⁻¹ := by field_simp
    _ ≤ ε ^ (p - 1) * ε ^ (1 - p) * (R ^ p)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΛ hεpos.le)
          (inv_nonneg.2 hRp.le)
    _ = (R ^ p)⁻¹ := by rw [hε1, one_mul]

/-- **The logarithmic Poincaré bound at scale `R`**: for a level function `w = σ(u - k)` with
values in `[0, om]` a.e. on the support of a cutoff `η` (`η = 1` on `closedBall x₀ (2R)`,
supported in `closedBall x₀ (3R)`, `|∇η| ≤ G₂/R`), `ε > 0` with `|λ| S^{p-1} R^p ≤ ε^{p-1}`, and a
measurable `E ⊆ closedBall x₀ (2R)` on which `w ≥ a ≥ 0`,
`|E| ∫_{B_{2R}} ((log(a + ε) - log(w + ε))^+)^p ≤ 2^d (4R)^p |B_{2R}| (K R^{-p}) |B_{3R}|`,
`K = c^{-p} (p-1)^{-1} (2^p (⌈p⌉ L)^p (p-1)^{1-p} G₂^p + 2)`. -/
theorem measure_mul_lintegral_log_le (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {G₂ : ℝ} (hG₂ : 0 ≤ G₂) {x₀ : Euc d} {R : ℝ} (hR : 0 < R)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (hηB : tsupport η ⊆ Metric.closedBall x₀ (3 * R)) (hη0 : ∀ x, 0 ≤ η x)
    (hη1 : ∀ x, η x ≤ 1) (hηone : ∀ x ∈ Metric.closedBall x₀ (2 * R), η x = 1)
    (hG : ∀ x, ‖gradient η x‖ ≤ G₂ / R) {σ k om ε : ℝ} (hσ : σ = 1 ∨ σ = -1) (hom : 0 ≤ om)
    (hε : 0 < ε) (hΛ : |lam| * S ^ (p - 1) * R ^ p ≤ ε ^ (p - 1))
    (hlevel : ∀ᵐ x, x ∈ tsupport η → σ * (u x - k) ∈ Icc 0 om) {E : Set (Euc d)}
    (hEm : MeasurableSet E) (hEB : E ⊆ Metric.closedBall x₀ (2 * R)) {a : ℝ} (ha : 0 ≤ a)
    (hE : ∀ y ∈ E, σ * (u y - k) ∈ Icc 0 om ∧ a ≤ σ * (u y - k)) :
    volume E * ∫⁻ x in Metric.closedBall x₀ (2 * R),
        ENNReal.ofReal (Real.log (a + ε) - Real.log (levelClamp σ k om (u x) + ε)) ^ p ≤
      2 ^ d * ENNReal.ofReal (4 * R) ^ p * volume (Metric.closedBall x₀ (2 * R)) *
        (ENNReal.ofReal (c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p *
          (p - 1) ^ (1 - p) * G₂ ^ p + 2) * (R ^ p)⁻¹) *
            volume (Metric.closedBall x₀ (3 * R))) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hpos : ∀ t ∈ Icc 0 om, 0 < t + ε := fun t ht => by linarith [ht.1]
  obtain ⟨cl, Gl, hclG, hGlw, hGlg⟩ := memW0_comp_level hp hu.memW0 hσ hom
    (Φ := fun t => Real.log (t + ε)) (φ' := fun t => (t + ε)⁻¹)
    (fun t ht => by
      have h := ((hasDerivAt_id' t).add_const ε).log (hpos t ht).ne'
      rwa [one_div] at h)
    ((continuousOn_id.add continuousOn_const).inv₀ fun t ht => (hpos t ht).ne')
  have hB2m : MeasurableSet (Metric.closedBall x₀ (2 * R)) := measurableSet_closedBall
  have hB2fin : volume (Metric.closedBall x₀ (2 * R)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hdiam : ∀ x ∈ Metric.closedBall x₀ (2 * R), ∀ y ∈ Metric.closedBall x₀ (2 * R),
      ‖y - x‖ ≤ 4 * R := by
    intro x hx y hy
    rw [← dist_eq_norm]
    rw [Metric.mem_closedBall] at hx hy
    calc dist y x ≤ dist y x₀ + dist x₀ x := dist_triangle _ _ _
      _ ≤ 2 * R + 2 * R := add_le_add hy (by rw [dist_comm]; exact hx)
      _ = 4 * R := by ring
  have hPo := hGlw.measure_mul_lintegral_sub_rpow_le hp (convex_closedBall x₀ (2 * R)) hB2m
    hB2fin hdiam hEm hEB (a := Real.log (a + ε) - cl) (fun y hy => by
      obtain ⟨h1, h2⟩ := hE y hy
      show Real.log (a + ε) - cl ≤ Gl (u y)
      have h3 := hclG _ h1
      have h4 : Real.log (a + ε) ≤ Real.log (σ * (u y - k) + ε) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith)
  beta_reduce at hPo
  have hsubB : Metric.closedBall x₀ (2 * R) ⊆ tsupport η := fun x hx =>
    subset_tsupport η (by rw [Function.mem_support, hηone x hx]; exact one_ne_zero)
  have hL1 : ∫⁻ x in Metric.closedBall x₀ (2 * R),
      ENNReal.ofReal (Real.log (a + ε) - cl - Gl (u x)) ^ p =
      ∫⁻ x in Metric.closedBall x₀ (2 * R),
        ENNReal.ofReal (Real.log (a + ε) - Real.log (levelClamp σ k om (u x) + ε)) ^ p := by
    refine setLIntegral_congr_fun_ae hB2m ?_
    filter_upwards [hlevel] with x h3 hxB
    have h4 := h3 (hsubB hxB)
    have h5 := hclG _ h4
    rw [levelClamp_eq h4]
    congr 2
    linarith
  rw [hL1] at hPo
  refine hPo.trans (mul_le_mul_right ?_ _)
  -- the energy of `log(w + ε)` on `closedBall x₀ (2R)`
  have hm : p ≤ (⌈p⌉₊ : ℝ) := Nat.le_ceil p
  have hm1 : (1 : ℝ) < ⌈p⌉₊ := lt_of_lt_of_le hp hm
  have hm0 : ⌈p⌉₊ ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hm1
    norm_num at hm1
  have hlog := hu.log_caccioppoli_level hp hF hS huS hσ hom hε hc hcF hL0 hL hm hη hηs hηK hη0
    hlevel
  have hB3m : MeasurableSet (Metric.closedBall x₀ (3 * R)) := measurableSet_closedBall
  have hB3fin : volume (Metric.closedBall x₀ (3 * R)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hY := integral_cutoff_weight_le hη hB3m hB3fin hηB hη0 hη1 hG hp0 hm
  have hZ := integral_cutoff_pow_le hB3m hB3fin hηB hη0 hη1 hm0
  have hΛε := lam_mul_rpow_le_of_le hR hε hΛ
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  have hK0 : 0 ≤ c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p *
      (p - 1) ^ (1 - p) * G₂ ^ p + 2) * (R ^ p)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      (inv_nonneg.2 hp1.le)) (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg zero_le_two _) (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) _))
          (Real.rpow_nonneg hp1.le _)) (Real.rpow_nonneg hG₂ _)) zero_le_two))
      (inv_nonneg.2 hRp.le)
  have hgradbound : ∫ x, η x ^ ⌈p⌉₊ * ((levelClamp σ k om (u x) + ε) ^ (-p) *
      ‖weakGrad u x‖ ^ p) ≤
      c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1) ^ (1 - p) * G₂ ^ p + 2) *
        (R ^ p)⁻¹ * (volume (Metric.closedBall x₀ (3 * R))).toReal := by
    refine hlog.trans ?_
    rw [Real.div_rpow hG₂ hR.le, div_eq_mul_inv] at hY
    have hV0 : 0 ≤ (volume (Metric.closedBall x₀ (3 * R))).toReal := ENNReal.toReal_nonneg
    have hK1 : 0 ≤ 2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1) ^ (1 - p) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg zero_le_two _)
        (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) _)) (Real.rpow_nonneg hp1.le _)
    have hZ0 : 0 ≤ ∫ x, η x ^ ⌈p⌉₊ := integral_nonneg fun x => pow_nonneg (hη0 x) _
    have hΛ0 : 0 ≤ |lam| * S ^ (p - 1) * ε ^ (1 - p) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hS _)) (Real.rpow_nonneg hε.le _)
    have h1 : 2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1) ^ (1 - p) *
        (∫ x, η x ^ ((⌈p⌉₊ : ℝ) - p) * ‖gradient η x‖ ^ p) ≤
        2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1) ^ (1 - p) *
          (G₂ ^ p * (R ^ p)⁻¹ * (volume (Metric.closedBall x₀ (3 * R))).toReal) :=
      mul_le_mul_of_nonneg_left hY hK1
    have h2 : 2 * (|lam| * S ^ (p - 1)) * ε ^ (1 - p) * ∫ x, η x ^ ⌈p⌉₊ ≤
        2 * (R ^ p)⁻¹ * (volume (Metric.closedBall x₀ (3 * R))).toReal := by
      calc 2 * (|lam| * S ^ (p - 1)) * ε ^ (1 - p) * ∫ x, η x ^ ⌈p⌉₊
          = 2 * (|lam| * S ^ (p - 1) * ε ^ (1 - p)) * ∫ x, η x ^ ⌈p⌉₊ := by ring
        _ ≤ 2 * (R ^ p)⁻¹ * (volume (Metric.closedBall x₀ (3 * R))).toReal :=
            mul_le_mul (mul_le_mul_of_nonneg_left hΛε zero_le_two) hZ hZ0
              (mul_nonneg zero_le_two (inv_nonneg.2 hRp.le))
    have hC0 : 0 ≤ c⁻¹ ^ p * (p - 1)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _) (inv_nonneg.2 hp1.le)
    calc c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1) ^ (1 - p) *
          (∫ x, η x ^ ((⌈p⌉₊ : ℝ) - p) * ‖gradient η x‖ ^ p) +
          2 * (|lam| * S ^ (p - 1)) * ε ^ (1 - p) * ∫ x, η x ^ ⌈p⌉₊)
        ≤ c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1) ^ (1 - p) *
          (G₂ ^ p * (R ^ p)⁻¹ * (volume (Metric.closedBall x₀ (3 * R))).toReal) +
          2 * (R ^ p)⁻¹ * (volume (Metric.closedBall x₀ (3 * R))).toReal) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC0
      _ = c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1) ^ (1 - p) * G₂ ^ p +
          2) * (R ^ p)⁻¹ * (volume (Metric.closedBall x₀ (3 * R))).toReal := by ring
  have hint : Integrable fun x => η x ^ ⌈p⌉₊ * ((levelClamp σ k om (u x) + ε) ^ (-p) *
      ‖weakGrad u x‖ ^ p) := by
    have h1 : Integrable fun x => ‖(σ * (levelClamp σ k om (u x) + ε)⁻¹) • weakGrad u x‖ ^ p :=
      (integrable_norm_rpow_of_memLp hp0 hGlw.memLp_weakGrad).congr
        (hGlg.mono fun x hx => by simp only [hx])
    have hηm : AEStronglyMeasurable (fun x => η x ^ ⌈p⌉₊) volume :=
      (hη.continuous.pow ⌈p⌉₊).aestronglyMeasurable
    have h2 : Integrable fun x => η x ^ ⌈p⌉₊ *
        ‖(σ * (levelClamp σ k om (u x) + ε)⁻¹) • weakGrad u x‖ ^ p :=
      h1.bdd_mul (c := 1) hηm (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hη0 x) _)]
        exact pow_le_one₀ (hη0 x) (hη1 x))
    refine h2.congr (Eventually.of_forall fun x => ?_)
    have hq := hpos _ (levelClamp_mem (σ := σ) (k := k) hom (u x))
    show η x ^ ⌈p⌉₊ * ‖(σ * (levelClamp σ k om (u x) + ε)⁻¹) • weakGrad u x‖ ^ p =
      η x ^ ⌈p⌉₊ * ((levelClamp σ k om (u x) + ε) ^ (-p) * ‖weakGrad u x‖ ^ p)
    rw [norm_smul, norm_mul, Real.norm_eq_abs σ, hσ1, one_mul,
      Real.norm_of_nonneg (inv_nonneg.2 hq.le), Real.mul_rpow (inv_nonneg.2 hq.le)
        (norm_nonneg _), Real.inv_rpow hq.le, Real.rpow_neg hq.le]
  calc ∫⁻ z in Metric.closedBall x₀ (2 * R), ‖weakGrad (fun x => Gl (u x)) z‖ₑ ^ p
      = ∫⁻ z in Metric.closedBall x₀ (2 * R), ENNReal.ofReal (η z ^ ⌈p⌉₊ *
          ((levelClamp σ k om (u z) + ε) ^ (-p) * ‖weakGrad u z‖ ^ p)) := by
        refine setLIntegral_congr_fun_ae hB2m ?_
        filter_upwards [hGlg] with z hz hzB
        have hq := hpos _ (levelClamp_mem (σ := σ) (k := k) hom (u z))
        have e1 : ‖(σ * (levelClamp σ k om (u z) + ε)⁻¹) • weakGrad u z‖ =
            (levelClamp σ k om (u z) + ε)⁻¹ * ‖weakGrad u z‖ := by
          rw [norm_smul, norm_mul, Real.norm_eq_abs σ, hσ1, one_mul,
            Real.norm_of_nonneg (inv_nonneg.2 hq.le)]
        rw [hz, hηone z hzB, one_pow, one_mul, ← ofReal_norm, e1,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (inv_nonneg.2 hq.le) (norm_nonneg _)) hp0.le,
          Real.mul_rpow (inv_nonneg.2 hq.le) (norm_nonneg _), Real.inv_rpow hq.le,
          Real.rpow_neg hq.le]
    _ ≤ ∫⁻ z, ENNReal.ofReal (η z ^ ⌈p⌉₊ *
          ((levelClamp σ k om (u z) + ε) ^ (-p) * ‖weakGrad u z‖ ^ p)) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ z, η z ^ ⌈p⌉₊ *
          ((levelClamp σ k om (u z) + ε) ^ (-p) * ‖weakGrad u z‖ ^ p)) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z =>
          mul_nonneg (pow_nonneg (hη0 z) _) (mul_nonneg (Real.rpow_nonneg
            (hpos _ (levelClamp_mem (σ := σ) (k := k) hom (u z))).le _)
            (Real.rpow_nonneg (norm_nonneg _) _)))).symm
    _ ≤ ENNReal.ofReal (c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p *
          (p - 1) ^ (1 - p) * G₂ ^ p + 2) * (R ^ p)⁻¹ *
            (volume (Metric.closedBall x₀ (3 * R))).toReal) :=
        ENNReal.ofReal_le_ofReal hgradbound
    _ = ENNReal.ofReal (c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p *
          (p - 1) ^ (1 - p) * G₂ ^ p + 2) * (R ^ p)⁻¹) *
            volume (Metric.closedBall x₀ (3 * R)) := by
        rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_toReal hB3fin]

/-- **The logarithmic bound normalized by a density bound**: under the hypotheses of
`measure_mul_lintegral_log_le` and `θ R^d |B₁| ≤ |E|`,
`∫_{B_{2R}} ((log(a + ε) - log(w + ε))^+)^p ≤ θ⁻¹ 2^d 4^p 2^d K 3^d R^d |B₁|`. -/
theorem lintegral_log_level_le (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {G₂ : ℝ} (hG₂ : 0 ≤ G₂) {x₀ : Euc d} {R : ℝ} (hR : 0 < R)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (hηB : tsupport η ⊆ Metric.closedBall x₀ (3 * R)) (hη0 : ∀ x, 0 ≤ η x)
    (hη1 : ∀ x, η x ≤ 1) (hηone : ∀ x ∈ Metric.closedBall x₀ (2 * R), η x = 1)
    (hG : ∀ x, ‖gradient η x‖ ≤ G₂ / R) {σ k om ε : ℝ} (hσ : σ = 1 ∨ σ = -1) (hom : 0 ≤ om)
    (hε : 0 < ε) (hΛ : |lam| * S ^ (p - 1) * R ^ p ≤ ε ^ (p - 1))
    (hlevel : ∀ᵐ x, x ∈ tsupport η → σ * (u x - k) ∈ Icc 0 om) {E : Set (Euc d)}
    (hEm : MeasurableSet E) (hEB : E ⊆ Metric.closedBall x₀ (2 * R)) {a : ℝ} (ha : 0 ≤ a)
    (hE : ∀ y ∈ E, σ * (u y - k) ∈ Icc 0 om ∧ a ≤ σ * (u y - k)) {θ : ℝ} (hθ : 0 < θ)
    (hEθ : ENNReal.ofReal (θ * R ^ d) * volume (Metric.ball (0 : Euc d) 1) ≤ volume E) :
    ∫⁻ x in Metric.closedBall x₀ (2 * R),
        ENNReal.ofReal (Real.log (a + ε) - Real.log (levelClamp σ k om (u x) + ε)) ^ p ≤
      ENNReal.ofReal (θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * (c⁻¹ ^ p * (p - 1)⁻¹ *
        (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p * (p - 1) ^ (1 - p) * G₂ ^ p + 2)) * 3 ^ d * R ^ d) *
        volume (Metric.ball (0 : Euc d) 1) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have h1 := hu.measure_mul_lintegral_log_le hp hF hS huS hc hcF hL0 hL hG₂ hR hη hηs hηK hηB
    hη0 hη1 hηone hG hσ hom hε hΛ hlevel hEm hEB ha hE
  obtain ⟨KL, hKL⟩ : ∃ KL : ℝ, KL = c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p *
      (p - 1) ^ (1 - p) * G₂ ^ p + 2) := ⟨_, rfl⟩
  rw [← hKL] at h1 ⊢
  have hKL0 : 0 ≤ KL := by
    rw [hKL]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      (inv_nonneg.2 hp1.le)) (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg zero_le_two _) (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) _))
          (Real.rpow_nonneg hp1.le _)) (Real.rpow_nonneg hG₂ _)) zero_le_two)
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = volume (Metric.ball (0 : Euc d) 1) := ⟨_, rfl⟩
  rw [← hV] at hEθ ⊢
  have hVtop : V ≠ ⊤ := by
    rw [hV]
    exact measure_ball_lt_top.ne
  have hRd : 0 < R ^ d := pow_pos hR d
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  have hb2 : volume (Metric.closedBall x₀ (2 * R)) = ENNReal.ofReal ((2 * R) ^ d) * V := by
    rw [hV, Measure.addHaar_closedBall volume x₀ (by linarith), finrank_euclideanSpace_fin]
  have hb3 : volume (Metric.closedBall x₀ (3 * R)) = ENNReal.ofReal ((3 * R) ^ d) * V := by
    rw [hV, Measure.addHaar_closedBall volume x₀ (by linarith), finrank_euclideanSpace_fin]
  rw [hb2, hb3] at h1
  obtain ⟨X, hX⟩ : ∃ X : ℝ≥0∞, X = ∫⁻ x in Metric.closedBall x₀ (2 * R),
      ENNReal.ofReal (Real.log (a + ε) - Real.log (levelClamp σ k om (u x) + ε)) ^ p := ⟨_, rfl⟩
  rw [← hX] at h1 ⊢
  have e2 : (2 : ℝ≥0∞) ^ d = ENNReal.ofReal (2 ^ d) := by
    rw [ENNReal.ofReal_pow zero_le_two]
    simp
  have e4 : ENNReal.ofReal (4 * R) ^ p = ENNReal.ofReal ((4 * R) ^ p) :=
    ENNReal.ofReal_rpow_of_nonneg (by linarith) hp0.le
  rw [e2, e4] at h1
  have n1 : (0 : ℝ) ≤ 2 ^ d := pow_nonneg zero_le_two d
  have n2 : 0 ≤ (4 * R) ^ p := Real.rpow_nonneg (by linarith) p
  have n3 : 0 ≤ (2 * R) ^ d := pow_nonneg (by linarith) d
  have n4 : 0 ≤ KL * (R ^ p)⁻¹ := mul_nonneg hKL0 (inv_nonneg.2 hRp.le)
  have hreal : 2 ^ d * (4 * R) ^ p * (2 * R) ^ d * (KL * (R ^ p)⁻¹) * (3 * R) ^ d =
      θ * R ^ d * (θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * KL * 3 ^ d * R ^ d) := by
    have hθ' := hθ.ne'
    have hRp' := hRp.ne'
    rw [Real.mul_rpow (by norm_num) hR.le, mul_pow, mul_pow]
    field_simp
  have hcomb : ENNReal.ofReal (2 ^ d) * ENNReal.ofReal ((4 * R) ^ p) *
      (ENNReal.ofReal ((2 * R) ^ d) * V) *
        (ENNReal.ofReal (KL * (R ^ p)⁻¹) * (ENNReal.ofReal ((3 * R) ^ d) * V)) =
      (ENNReal.ofReal (θ * R ^ d) * V) *
        (ENNReal.ofReal (θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * KL * 3 ^ d * R ^ d) * V) := by
    calc ENNReal.ofReal (2 ^ d) * ENNReal.ofReal ((4 * R) ^ p) *
          (ENNReal.ofReal ((2 * R) ^ d) * V) *
            (ENNReal.ofReal (KL * (R ^ p)⁻¹) * (ENNReal.ofReal ((3 * R) ^ d) * V))
        = ENNReal.ofReal (2 ^ d) * ENNReal.ofReal ((4 * R) ^ p) * ENNReal.ofReal ((2 * R) ^ d) *
            ENNReal.ofReal (KL * (R ^ p)⁻¹) * ENNReal.ofReal ((3 * R) ^ d) * (V * V) := by ring
      _ = ENNReal.ofReal (2 ^ d * (4 * R) ^ p * (2 * R) ^ d * (KL * (R ^ p)⁻¹) * (3 * R) ^ d) *
            (V * V) := by
          rw [← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (mul_nonneg n1 n2),
            ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg n1 n2) n3),
            ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4)]
      _ = ENNReal.ofReal (θ * R ^ d * (θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * KL * 3 ^ d * R ^ d)) *
            (V * V) := by rw [hreal]
      _ = (ENNReal.ofReal (θ * R ^ d) * V) *
            (ENNReal.ofReal (θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * KL * 3 ^ d * R ^ d) * V) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hθ.le hRd.le)]
          ring
  rw [hcomb] at h1
  have hV0 : V ≠ 0 := by
    rw [hV]
    exact (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hA0 : ENNReal.ofReal (θ * R ^ d) * V ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (mul_pos hθ hRd)).ne' hV0
  have hAtop : ENNReal.ofReal (θ * R ^ d) * V ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop
  have h2 : ENNReal.ofReal (θ * R ^ d) * V * X ≤ ENNReal.ofReal (θ * R ^ d) * V *
      (ENNReal.ofReal (θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * KL * 3 ^ d * R ^ d) * V) :=
    (mul_le_mul_left hEθ X).trans h1
  exact (ENNReal.mul_le_mul_iff_right hA0 hAtop).1 h2

/-- **The weighted `L^p` bound for `W = log(2(om + ε)) - log(w + ε)`**: for a cutoff `η` supported
in `closedBall x₀ (2R)`, `N > p`, and a bound `∫_{B_{2R}} ((log(om/2 + ε) - log(w + ε))^+)^p ≤
Z R^d |B₁|`,
`R^{-d} ∫ η^{N-p} W^p ≤ 2^p (Z |B₁| + (log 4)^p 2^d |B₁|)`. -/
theorem lintegral_W_level_le (hp : 1 < p) {x₀ : Euc d}
    {R : ℝ} (hR : 0 < R) {η : Euc d → ℝ} (hηB : tsupport η ⊆ Metric.closedBall x₀ (2 * R))
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {N : ℕ} (hNp : p < N) {σ k om ε : ℝ}
    (hom : 0 ≤ om) (hε : 0 < ε) {Z : ℝ}
    (hX : ∫⁻ x in Metric.closedBall x₀ (2 * R),
        ENNReal.ofReal (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) ^ p ≤
      ENNReal.ofReal (Z * R ^ d) * volume (Metric.ball (0 : Euc d) 1)) :
    ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x, ENNReal.ofReal (η x ^ ((N : ℝ) - p) *
        (Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε)) ^ p) ≤
      ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal Z * volume (Metric.ball (0 : Euc d) 1) +
        ENNReal.ofReal (Real.log 4 ^ p) *
          (ENNReal.ofReal (2 ^ d) * volume (Metric.ball (0 : Euc d) 1))) := by
  have hp0 : 0 < p := by linarith
  have hNp' : 0 < (N : ℝ) - p := sub_pos.2 hNp
  have hRd : 0 < R ^ d := pow_pos hR d
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpt : ∀ x, ENNReal.ofReal (η x ^ ((N : ℝ) - p) *
      (Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε)) ^ p) ≤
      (Metric.closedBall x₀ (2 * R)).indicator (fun x => ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) ^ p +
          ENNReal.ofReal (Real.log 4 ^ p))) x := by
    intro x
    have hw := levelClamp_mem (σ := σ) (k := k) hom (u x)
    have hq : 0 < levelClamp σ k om (u x) + ε := by linarith [hw.1]
    by_cases hx : x ∈ Metric.closedBall x₀ (2 * R)
    · rw [indicator_of_mem hx]
      have hW0 : 0 ≤ Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε) :=
        sub_nonneg.2 (Real.log_le_log hq (by linarith [hw.2]))
      have hB0 : 0 ≤ Real.log (2 * (om + ε)) - Real.log (om / 2 + ε) :=
        sub_nonneg.2 (Real.log_le_log (by linarith) (by linarith))
      have hB4 : Real.log (2 * (om + ε)) - Real.log (om / 2 + ε) ≤ Real.log 4 := by
        rw [← Real.log_div (by linarith) (by linarith)]
        exact Real.log_le_log (div_pos (by linarith) (by linarith))
          (by rw [div_le_iff₀ (by linarith)]; linarith)
      have hA : Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε) ≤
          max (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) 0 +
            (Real.log (2 * (om + ε)) - Real.log (om / 2 + ε)) := by
        have := le_max_left (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) 0
        linarith
      have h1 : η x ^ ((N : ℝ) - p) *
          (Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε)) ^ p ≤
          2 ^ p * (max (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) 0 ^ p +
            Real.log 4 ^ p) := by
        calc η x ^ ((N : ℝ) - p) *
              (Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε)) ^ p
            ≤ 1 * (Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε)) ^ p :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_one (hη0 x) (hη1 x) hNp'.le)
                (Real.rpow_nonneg hW0 _)
          _ = (Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε)) ^ p := one_mul _
          _ ≤ (max (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) 0 +
                (Real.log (2 * (om + ε)) - Real.log (om / 2 + ε))) ^ p :=
              Real.rpow_le_rpow hW0 hA hp0.le
          _ ≤ 2 ^ p * (max (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) 0 ^ p +
                (Real.log (2 * (om + ε)) - Real.log (om / 2 + ε)) ^ p) :=
              add_rpow_le_two_rpow_mul hp0.le (le_max_right _ _) hB0
          _ ≤ 2 ^ p * (max (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) 0 ^ p +
                Real.log 4 ^ p) :=
              mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.rpow_le_rpow hB0 hB4 hp0.le))
                (Real.rpow_nonneg zero_le_two _)
      refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
      have hmax : ENNReal.ofReal (max (Real.log (om / 2 + ε) -
          Real.log (levelClamp σ k om (u x) + ε)) 0) =
          ENNReal.ofReal (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) := by
        rcases le_total (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) 0
          with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two _),
        ENNReal.ofReal_add (Real.rpow_nonneg (le_max_right _ _) _) (Real.rpow_nonneg hlog4 _),
        ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hp0.le, hmax]
    · rw [indicator_of_notMem hx]
      have hx' : x ∉ tsupport η := fun h => hx (hηB h)
      rw [image_eq_zero_of_notMem_tsupport hx', Real.zero_rpow hNp'.ne', zero_mul,
        ENNReal.ofReal_zero]
  have hbound : ∫⁻ x, ENNReal.ofReal (η x ^ ((N : ℝ) - p) *
      (Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε)) ^ p) ≤
      ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (Z * R ^ d) * volume (Metric.ball (0 : Euc d) 1) +
        ENNReal.ofReal (Real.log 4 ^ p) *
          (ENNReal.ofReal ((2 * R) ^ d) * volume (Metric.ball (0 : Euc d) 1))) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_indicator measurableSet_closedBall,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
      setLIntegral_const, Measure.addHaar_closedBall volume x₀ (by linarith),
      finrank_euclideanSpace_fin]
    exact mul_le_mul_right (add_le_add hX le_rfl) _
  have e1 : ENNReal.ofReal ((R ^ d)⁻¹) * ENNReal.ofReal (Z * R ^ d) = ENNReal.ofReal Z := by
    have hRd' := hRd.ne'
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hRd.le)]
    congr 1
    field_simp
  have e2 : ENNReal.ofReal ((R ^ d)⁻¹) * ENNReal.ofReal ((2 * R) ^ d) = ENNReal.ofReal (2 ^ d) := by
    have hRd' := hRd.ne'
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hRd.le), mul_pow]
    congr 1
    field_simp
  calc ENNReal.ofReal ((R ^ d)⁻¹) * ∫⁻ x, ENNReal.ofReal (η x ^ ((N : ℝ) - p) *
        (Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε)) ^ p)
      ≤ ENNReal.ofReal ((R ^ d)⁻¹) * (ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal (Z * R ^ d) * volume (Metric.ball (0 : Euc d) 1) +
            ENNReal.ofReal (Real.log 4 ^ p) *
              (ENNReal.ofReal ((2 * R) ^ d) * volume (Metric.ball (0 : Euc d) 1)))) :=
        mul_le_mul_right hbound _
    _ = ENNReal.ofReal (2 ^ p) * ((ENNReal.ofReal ((R ^ d)⁻¹) * ENNReal.ofReal (Z * R ^ d)) *
          volume (Metric.ball (0 : Euc d) 1) + ENNReal.ofReal (Real.log 4 ^ p) *
            ((ENNReal.ofReal ((R ^ d)⁻¹) * ENNReal.ofReal ((2 * R) ^ d)) *
              volume (Metric.ball (0 : Euc d) 1))) := by ring
    _ = ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal Z * volume (Metric.ball (0 : Euc d) 1) +
          ENNReal.ofReal (Real.log 4 ^ p) *
            (ENNReal.ofReal (2 ^ d) * volume (Metric.ball (0 : Euc d) 1))) := by rw [e1, e2]

/-- **From a density bound to a uniform lower bound (quantitative)**: for `θ > 0` there is
`c₁ ∈ (0, 1]`, depending only on the structural constants and `θ`, such that for every ball with
`closedBall x₀ (3R) ⊆ K` (`R ≤ 1`), every level function `w = σ(u - k)` with values in `[0, om]`
a.e. on `closedBall x₀ (3R)`, if `w ≥ om/2` on a fraction `θ` of `ball x₀ R` then
`w ≥ c₁ om - (|λ| S^{p-1} R^p)^{1/(p-1)}` a.e. on `ball x₀ R` (logarithmic Poincaré bound and the
scale-invariant Moser sup bound for `log(2(om + ε)) - log(w + ε)`, with
`ε = max((|λ| S^{p-1} R^p)^{1/(p-1)}, c₁ om)`). -/
theorem exists_level_lower_bound (hp : 1 < p) (hF : IsSmoothStrictNorm F) (hd : 0 < d)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    (humeas : Measurable u) {θ : ℝ} (hθ : 0 < θ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ (x₀ : Euc d) (R : ℝ), 0 < R → R ≤ 1 →
      Metric.closedBall x₀ (3 * R) ⊆ K → ∀ σ k om : ℝ, (σ = 1 ∨ σ = -1) → 0 < om →
      (∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → σ * (u x - k) ∈ Icc 0 om) →
      ENNReal.ofReal θ * volume (Metric.ball x₀ R) ≤
        volume (Metric.ball x₀ R ∩ {x | om / 2 ≤ σ * (u x - k)}) →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
        c₁ * om - (|lam| * S ^ (p - 1) * R ^ p) ^ (p - 1)⁻¹ ≤ σ * (u x - k) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.1 hd
  obtain ⟨c, hc, hcF⟩ := hF.exists_pos_mul_norm_le'
  obtain ⟨L, hL0, hL⟩ := hF.exists_norm_gradient_le
  obtain ⟨κ, hκ, C, hC, hSob⟩ := exists_sobolev_ball hd hp
  obtain ⟨G₁, hG₁0, hcut₁⟩ := exists_rescaled_cutoff (d := d) one_pos one_lt_two
  obtain ⟨G₂, hG₂0, hcut₂⟩ := exists_rescaled_cutoff (d := d) two_pos (by norm_num : (2 : ℝ) < 3)
  have hNp : p < ((⌈κ * p + p⌉₊ : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil (κ * p + p)
    have h2 : 0 < κ * p := mul_pos (by linarith) hp0
    linarith
  obtain ⟨B, hB0, hBsup⟩ := hu.moser_level_sup hp hF hS huS hc hcF hL0 hL hκ hC hG₁0
    (Nat.le_ceil (κ * p + p))
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = volume (Metric.ball (0 : Euc d) 1) := ⟨_, rfl⟩
  have hVtop : V ≠ ⊤ := by
    rw [hV]
    exact measure_ball_lt_top.ne
  obtain ⟨KL, hKL⟩ : ∃ KL : ℝ, KL = c⁻¹ ^ p * (p - 1)⁻¹ * (2 ^ p * ((⌈p⌉₊ : ℝ) * L) ^ p *
      (p - 1) ^ (1 - p) * G₂ ^ p + 2) := ⟨_, rfl⟩
  have hKL0 : 0 ≤ KL := by
    rw [hKL]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      (inv_nonneg.2 hp1.le)) (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg zero_le_two _) (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) _))
          (Real.rpow_nonneg hp1.le _)) (Real.rpow_nonneg hG₂0 _)) zero_le_two)
  have hZ0 : 0 ≤ θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * KL * 3 ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hθ.le)
      (pow_nonneg zero_le_two d)) (Real.rpow_nonneg (by norm_num) p)) (pow_nonneg zero_le_two d))
      hKL0) (pow_nonneg (by norm_num) d)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ≥0∞, Q = ENNReal.ofReal (2 ^ p) *
      (ENNReal.ofReal (θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * KL * 3 ^ d) * V +
        ENNReal.ofReal (Real.log 4 ^ p) * (ENNReal.ofReal (2 ^ d) * V)) := ⟨_, rfl⟩
  have hQtop : Q ≠ ⊤ := by
    rw [hQ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop)⟩)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ((ENNReal.ofReal B * Q).toReal) ^ p⁻¹ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  refine ⟨Real.exp (-M), Real.exp_pos _, Real.exp_le_one_iff.2 (by linarith),
    fun x₀ R hR hR1 hball σ k om hσ hom hlevel hmeas => ?_⟩
  have hΛ0 : 0 ≤ |lam| * S ^ (p - 1) := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hS _)
  have hΛR0 : 0 ≤ |lam| * S ^ (p - 1) * R ^ p := mul_nonneg hΛ0 (Real.rpow_nonneg hR.le _)
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (|lam| * S ^ (p - 1) * R ^ p) ^ (p - 1)⁻¹ := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by
    rw [he]
    exact Real.rpow_nonneg hΛR0 _
  rw [← he]
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = max e (Real.exp (-M) * om) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    exact lt_max_of_lt_right (mul_pos (Real.exp_pos _) hom)
  have hεe : e ≤ ε := by
    rw [hε]
    exact le_max_left _ _
  have hεsum : ε ≤ e + Real.exp (-M) * om := by
    rw [hε]
    exact max_le (le_add_of_nonneg_right (mul_pos (Real.exp_pos _) hom).le)
      (le_add_of_nonneg_left he0)
  have hΛε : |lam| * S ^ (p - 1) * R ^ p ≤ ε ^ (p - 1) := by
    have h1 : e ^ (p - 1) = |lam| * S ^ (p - 1) * R ^ p := by
      rw [he]
      exact Real.rpow_inv_rpow hΛR0 hp1.ne'
    rw [← h1]
    exact Real.rpow_le_rpow he0 hεe hp1.le
  obtain ⟨η₁, hη₁, hη₁s, hη₁B, hη₁0, hη₁1, hη₁one, hη₁G⟩ := hcut₁ x₀ R hR
  obtain ⟨η₂, hη₂, hη₂s, hη₂B, hη₂0, hη₂1, hη₂one, hη₂G⟩ := hcut₂ x₀ R hR
  have h23 : Metric.closedBall x₀ (2 * R) ⊆ Metric.closedBall x₀ (3 * R) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hR3 : Metric.ball x₀ R ⊆ Metric.closedBall x₀ (3 * R) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hη₁K : tsupport η₁ ⊆ K := hη₁B.trans (h23.trans hball)
  have hη₂K : tsupport η₂ ⊆ K := hη₂B.trans hball
  have hlevel₁ : ∀ᵐ x, x ∈ tsupport η₁ → σ * (u x - k) ∈ Icc 0 om :=
    hlevel.mono fun x hx h => hx (h23 (hη₁B h))
  have hlevel₂ : ∀ᵐ x, x ∈ tsupport η₂ → σ * (u x - k) ∈ Icc 0 om :=
    hlevel.mono fun x hx h => hx (hη₂B h)
  obtain ⟨E, hEdef⟩ : ∃ E : Set (Euc d), E = Metric.ball x₀ R ∩
      {x | om / 2 ≤ σ * (u x - k)} ∩ {x | σ * (u x - k) ∈ Icc 0 om} := ⟨_, rfl⟩
  have hmeasfun : Measurable fun x => σ * (u x - k) :=
    measurable_const.mul (humeas.sub measurable_const)
  have hEm : MeasurableSet E := by
    rw [hEdef]
    exact (measurableSet_ball.inter (measurableSet_le measurable_const hmeasfun)).inter
      (hmeasfun measurableSet_Icc)
  have hEB : E ⊆ Metric.closedBall x₀ (2 * R) := by
    rw [hEdef]
    exact fun x hx => (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith))) hx.1.1
  have hE : ∀ y ∈ E, σ * (u y - k) ∈ Icc 0 om ∧ om / 2 ≤ σ * (u y - k) := by
    rw [hEdef]
    exact fun y hy => ⟨hy.2, hy.1.2⟩
  have hballR : volume (Metric.ball x₀ R) = ENNReal.ofReal (R ^ d) * V := by
    rw [hV, Measure.addHaar_ball volume x₀ hR.le, finrank_euclideanSpace_fin]
  have hEθ : ENNReal.ofReal (θ * R ^ d) * V ≤ volume E := by
    rw [ENNReal.ofReal_mul hθ.le, mul_assoc, ← hballR]
    refine hmeas.trans (measure_mono_ae ?_)
    rw [hEdef]
    filter_upwards [hlevel] with x hx hxE
    exact ⟨hxE, hx (hR3 hxE.1)⟩
  have hX := hu.lintegral_log_level_le hp hF hS huS hc hcF hL0 hL hG₂0 hR hη₂ hη₂s hη₂K hη₂B
    hη₂0 hη₂1 hη₂one hη₂G hσ hom.le hε0 hΛε hlevel₂ hEm hEB (by linarith : (0 : ℝ) ≤ om / 2)
    hE hθ (by rw [← hV]; exact hEθ)
  rw [← hKL] at hX
  have hX' : ∫⁻ x in Metric.closedBall x₀ (2 * R),
      ENNReal.ofReal (Real.log (om / 2 + ε) - Real.log (levelClamp σ k om (u x) + ε)) ^ p ≤
      ENNReal.ofReal ((θ⁻¹ * 2 ^ d * 4 ^ p * 2 ^ d * KL * 3 ^ d) * R ^ d) *
        volume (Metric.ball (0 : Euc d) 1) := hX
  have hWn := lintegral_W_level_le hp hR hη₁B hη₁0 hη₁1 hNp hom.le hε0 hX'
  rw [← hV, ← hQ] at hWn
  have hsup := hBsup x₀ R hR hR1 (hSob x₀ (2 * R) (by linarith)) η₁ hη₁ hη₁s hη₁K hη₁B hη₁0 hη₁1
    hη₁G σ k om ε (2 * (om + ε)) hσ hom.le hε0 le_rfl hΛε hlevel₁
  filter_upwards [ae_restrict_of_ae hsup, ae_restrict_of_ae hlevel,
    ae_restrict_mem measurableSet_ball] with x hx hxl hxB
  have hη₁x : η₁ x = 1 := hη₁one x (by
    rw [one_mul]
    exact Metric.ball_subset_closedBall hxB)
  have hlx := hxl (hR3 hxB)
  have h2 := (hx hη₁x).trans (mul_le_mul_right hWn _)
  have hBQ : ENNReal.ofReal B * Q ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQtop
  have h3 := (ENNReal.ofReal_le_iff_le_toReal hBQ).1 h2
  have hq : 0 < levelClamp σ k om (u x) + ε := by
    linarith [(levelClamp_mem (σ := σ) (k := k) hom.le (u x)).1]
  have hT0 : 0 < 2 * (om + ε) := by linarith
  have hW0 : 0 ≤ Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε) :=
    sub_nonneg.2 (Real.log_le_log hq
      (by linarith [(levelClamp_mem (σ := σ) (k := k) hom.le (u x)).2]))
  have h4 : Real.log (2 * (om + ε)) - Real.log (levelClamp σ k om (u x) + ε) ≤ M := by
    have h5 := Real.rpow_le_rpow (Real.rpow_nonneg hW0 _) h3 (inv_nonneg.2 hp0.le)
    rwa [Real.rpow_rpow_inv hW0 hp0.ne', ← hM] at h5
  have h6 : 2 * (om + ε) * Real.exp (-M) ≤ levelClamp σ k om (u x) + ε := by
    calc 2 * (om + ε) * Real.exp (-M) = Real.exp (Real.log (2 * (om + ε)) - M) := by
          rw [Real.exp_sub, Real.exp_log hT0, Real.exp_neg]
          ring
      _ ≤ Real.exp (Real.log (levelClamp σ k om (u x) + ε)) := Real.exp_le_exp.2 (by linarith)
      _ = levelClamp σ k om (u x) + ε := Real.exp_log hq
  rw [levelClamp_eq hlx] at h6
  have hexp : 0 < Real.exp (-M) := Real.exp_pos _
  nlinarith [mul_pos hexp hε0]

/-- **Oscillation decay** (De Giorgi): there is `c₁ ∈ (0, 1]` such that whenever
`u ∈ [m, m + om]` a.e. on `closedBall x₀ (3R) ⊆ K` (`R ≤ 1`), there is `m'` with
`u ∈ [m', m' + (1 - c₁) om + (|λ| S^{p-1} R^p)^{1/(p-1)}]` a.e. on `ball x₀ R` (one of `u - m` and
`m + om - u` is at least `om/2` on half of `ball x₀ R`; apply `exists_level_lower_bound`). -/
theorem exists_osc_decay (hp : 1 < p) (hF : IsSmoothStrictNorm F) (hd : 0 < d)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    (humeas : Measurable u) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ (x₀ : Euc d) (R : ℝ), 0 < R → R ≤ 1 →
      Metric.closedBall x₀ (3 * R) ⊆ K → ∀ m om : ℝ, 0 ≤ om →
      (∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → u x ∈ Icc m (m + om)) →
      ∃ m' : ℝ, ∀ᵐ x, x ∈ Metric.ball x₀ R →
        u x ∈ Icc m' (m' + ((1 - c₁) * om + (|lam| * S ^ (p - 1) * R ^ p) ^ (p - 1)⁻¹)) := by
  obtain ⟨c₁, hc₁0, hc₁1, hlow⟩ :=
    hu.exists_level_lower_bound hp hF hd hS huS humeas (θ := 1 / 2) (by norm_num)
  refine ⟨c₁, hc₁0, hc₁1, fun x₀ R hR hR1 hball m om hom hosc => ?_⟩
  have he0 : 0 ≤ (|lam| * S ^ (p - 1) * R ^ p) ^ (p - 1)⁻¹ :=
    Real.rpow_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hS _))
      (Real.rpow_nonneg hR.le _)) _
  have hR3 : Metric.ball x₀ R ⊆ Metric.closedBall x₀ (3 * R) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  rcases hom.eq_or_lt with rfl | hom'
  · refine ⟨m, hosc.mono fun x hx hxB => ?_⟩
    obtain ⟨h1, h2⟩ := hx (hR3 hxB)
    exact ⟨h1, by nlinarith⟩
  have hsplit : volume (Metric.ball x₀ R) ≤
      volume (Metric.ball x₀ R ∩ {x | om / 2 ≤ 1 * (u x - m)}) +
        volume (Metric.ball x₀ R ∩ {x | om / 2 ≤ -1 * (u x - (m + om))}) := by
    refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
    by_cases h : om / 2 ≤ 1 * (u x - m)
    · exact Or.inl ⟨hx, h⟩
    · refine Or.inr ⟨hx, ?_⟩
      show om / 2 ≤ -1 * (u x - (m + om))
      linarith
  have hhalf : ENNReal.ofReal (1 / 2) * volume (Metric.ball x₀ R) ≤
      volume (Metric.ball x₀ R ∩ {x | om / 2 ≤ 1 * (u x - m)}) ∨
      ENNReal.ofReal (1 / 2) * volume (Metric.ball x₀ R) ≤
        volume (Metric.ball x₀ R ∩ {x | om / 2 ≤ -1 * (u x - (m + om))}) := by
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    have hsum : ENNReal.ofReal (1 / 2) * volume (Metric.ball x₀ R) +
        ENNReal.ofReal (1 / 2) * volume (Metric.ball x₀ R) = volume (Metric.ball x₀ R) := by
      rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.ofReal_one, one_mul]
    exact absurd (hsplit.trans_lt ((ENNReal.add_lt_add hcon.1 hcon.2).trans_le hsum.le))
      (lt_irrefl _)
  rcases hhalf with h | h
  · have hl := hlow x₀ R hR hR1 hball 1 m om (Or.inl rfl) hom' (hosc.mono fun x hx hxB => by
      obtain ⟨h1, h2⟩ := hx hxB
      exact ⟨by linarith, by linarith⟩) h
    rw [ae_restrict_iff' measurableSet_ball] at hl
    refine ⟨m + (c₁ * om - (|lam| * S ^ (p - 1) * R ^ p) ^ (p - 1)⁻¹), ?_⟩
    filter_upwards [hl, hosc] with x hx1 hx2 hxB
    obtain ⟨h1, h2⟩ := hx2 (hR3 hxB)
    have h3 := hx1 hxB
    constructor <;> linarith
  · have hl := hlow x₀ R hR hR1 hball (-1) (m + om) om (Or.inr rfl) hom'
      (hosc.mono fun x hx hxB => by
        obtain ⟨h1, h2⟩ := hx hxB
        exact ⟨by linarith, by linarith⟩) h
    rw [ae_restrict_iff' measurableSet_ball] at hl
    refine ⟨m, ?_⟩
    filter_upwards [hl, hosc] with x hx1 hx2 hxB
    obtain ⟨h1, h2⟩ := hx2 (hR3 hxB)
    have h3 := hx1 hxB
    constructor <;> linarith

/-- **Hölder decay of the oscillation**: there are `α > 0` and `C₀` such that whenever
`closedBall x₀ (3R₀) ⊆ K` (`R₀ ≤ 1`), for every `r ≤ R₀` there is `m` with
`u ∈ [m, m + C₀ (r/R₀)^α]` a.e. on `ball x₀ r` (iterating `exists_osc_decay` on the radii
`R₀ 4^{-n}`, whose error terms decay geometrically). -/
theorem exists_holder_osc (hp : 1 < p) (hF : IsSmoothStrictNorm F) (hd : 0 < d)
    (hu : IsWeakEigensolution p F K lam u) {S : ℝ} (hS : 0 ≤ S) (huS : ∀ x, u x ∈ Icc 0 S)
    (humeas : Measurable u) :
    ∃ α : ℝ, 0 < α ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (x₀ : Euc d) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 →
      Metric.closedBall x₀ (3 * R₀) ⊆ K → ∀ r : ℝ, 0 < r → r ≤ R₀ →
      ∃ m : ℝ, ∀ᵐ x, x ∈ Metric.ball x₀ r → u x ∈ Icc m (m + C₀ * (r / R₀) ^ α) := by
  have hp1 : 0 < p - 1 := by linarith
  obtain ⟨c₁, hc₁0, hc₁1, hdec⟩ := hu.exists_osc_decay hp hF hd hS huS humeas
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : ℝ, Λ' = (|lam| * S ^ (p - 1)) ^ (p - 1)⁻¹ := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ |lam| * S ^ (p - 1) := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hS _)
  have hΛ'0 : 0 ≤ Λ' := by
    rw [hΛ']
    exact Real.rpow_nonneg hΛ0 _
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = max (1 - c₁) (1 / 4) := ⟨_, rfl⟩
  have hγ1 : γ < 1 := by
    rw [hγ]
    exact max_lt (by linarith) (by norm_num)
  have hγ14 : 1 / 4 ≤ γ := by
    rw [hγ]
    exact le_max_right _ _
  have hγc : 1 - c₁ ≤ γ := by
    rw [hγ]
    exact le_max_left _ _
  obtain ⟨γ', hγ'⟩ : ∃ γ' : ℝ, γ' = (1 + γ) / 2 := ⟨_, rfl⟩
  have hγγ' : γ < γ' := by rw [hγ']; linarith
  have hγ'1 : γ' < 1 := by rw [hγ']; linarith
  have hγ'0 : 0 < γ' := by linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = Real.log γ'⁻¹ / Real.log 4 := ⟨_, rfl⟩
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hαpos : 0 < α := by
    rw [hα]
    exact div_pos (Real.log_pos ((one_lt_inv₀ hγ'0).2 hγ'1)) hlog4
  have h4α : (4 : ℝ) ^ α = γ'⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num), hα,
      show Real.log 4 * (Real.log γ'⁻¹ / Real.log 4) = Real.log γ'⁻¹ by field_simp,
      Real.exp_log (inv_pos.2 hγ'0)]
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = S + Λ' / (γ' - γ) := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by
    rw [hA₀]
    exact add_nonneg hS (div_nonneg hΛ'0 (by linarith))
  refine ⟨α, hαpos, A₀ * 4 ^ α, mul_nonneg hA₀0 (Real.rpow_nonneg (by norm_num) _),
    fun x₀ R₀ hR₀ hR₀1 hball r hr hrR => ?_⟩
  have key : ∀ n : ℕ, ∃ m : ℝ, ∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * (R₀ / 4 ^ n)) →
      u x ∈ Icc m (m + A₀ * γ' ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, Eventually.of_forall fun x _ => ⟨(huS x).1, ?_⟩⟩
      have h1 := (huS x).2
      have h2 : S ≤ A₀ := by
        rw [hA₀]
        exact le_add_of_nonneg_right (div_nonneg hΛ'0 (by linarith))
      simp only [pow_zero, mul_one, zero_add]
      linarith
    | succ n ih =>
      obtain ⟨m, hm⟩ := ih
      have h4n : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
      have hRn : 0 < R₀ / 4 ^ n := div_pos hR₀ h4n
      have hRn1 : R₀ / 4 ^ n ≤ 1 :=
        (div_le_self hR₀.le (one_le_pow₀ (by norm_num))).trans hR₀1
      have hballn : Metric.closedBall x₀ (3 * (R₀ / 4 ^ n)) ⊆ K :=
        (Metric.closedBall_subset_closedBall (by
          have := div_le_self hR₀.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (n := n))
          linarith)).trans hball
      obtain ⟨m', hm'⟩ := hdec x₀ (R₀ / 4 ^ n) hRn hRn1 hballn m (A₀ * γ' ^ n)
        (mul_nonneg hA₀0 (pow_nonneg hγ'0.le n)) hm
      refine ⟨m', hm'.mono fun x hx hxB => ?_⟩
      have hxB' : x ∈ Metric.ball x₀ (R₀ / 4 ^ n) := by
        rw [Metric.mem_closedBall] at hxB
        rw [Metric.mem_ball]
        have e : 3 * (R₀ / 4 ^ (n + 1)) = 3 / 4 * (R₀ / 4 ^ n) := by
          rw [pow_succ]
          field_simp
        rw [e] at hxB
        linarith
      obtain ⟨h1, h2⟩ := hx hxB'
      refine ⟨h1, h2.trans (add_le_add le_rfl ?_)⟩
      -- the error term
      have hbase : (R₀ / 4 ^ n) ^ (p * (p - 1)⁻¹) ≤ (1 / 4) ^ n := by
        have hpp : 1 ≤ p * (p - 1)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hp1]
          linarith
        calc (R₀ / 4 ^ n) ^ (p * (p - 1)⁻¹) ≤ (R₀ / 4 ^ n) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge' hRn.le hRn1 zero_le_one hpp
          _ = R₀ / 4 ^ n := Real.rpow_one _
          _ ≤ 1 / 4 ^ n := div_le_div_of_nonneg_right hR₀1 h4n.le
          _ = (1 / 4) ^ n := by rw [one_div_pow]
      have he : (|lam| * S ^ (p - 1) * (R₀ / 4 ^ n) ^ p) ^ (p - 1)⁻¹ ≤ Λ' * γ ^ n := by
        rw [Real.mul_rpow hΛ0 (Real.rpow_nonneg hRn.le _), ← hΛ', ← Real.rpow_mul hRn.le]
        exact mul_le_mul_of_nonneg_left (hbase.trans (pow_le_pow_left₀ (by norm_num) hγ14 n))
          hΛ'0
      have hγn : γ ^ n ≤ γ' ^ n := pow_le_pow_left₀ (by linarith) hγγ'.le n
      have hA₀γ : Λ' ≤ (γ' - γ) * A₀ := by
        rw [hA₀, mul_add, mul_div_cancel₀ _ (by linarith : γ' - γ ≠ 0)]
        nlinarith
      have hγ'n : 0 ≤ γ' ^ n := pow_nonneg hγ'0.le n
      calc (1 - c₁) * (A₀ * γ' ^ n) + (|lam| * S ^ (p - 1) * (R₀ / 4 ^ n) ^ p) ^ (p - 1)⁻¹
          ≤ γ * (A₀ * γ' ^ n) + Λ' * γ' ^ n :=
            add_le_add (mul_le_mul_of_nonneg_right hγc (mul_nonneg hA₀0 hγ'n))
              (he.trans (mul_le_mul_of_nonneg_left hγn hΛ'0))
        _ ≤ γ * (A₀ * γ' ^ n) + (γ' - γ) * A₀ * γ' ^ n :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hA₀γ hγ'n)
        _ = A₀ * γ' ^ (n + 1) := by ring
  -- choose the scale
  have hRr : 1 ≤ R₀ / r := (one_le_div hr).2 hrR
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hRr (by norm_num : (1 : ℝ) < 4)
  obtain ⟨m, hm⟩ := key n
  refine ⟨m, hm.mono fun x hx hxB => ?_⟩
  have h4n : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
  have hrn : r ≤ R₀ / 4 ^ n := by
    rw [le_div_iff₀ h4n]
    rw [le_div_iff₀ hr] at hn1
    linarith
  have hxB' : x ∈ Metric.closedBall x₀ (3 * (R₀ / 4 ^ n)) := by
    rw [Metric.mem_ball] at hxB
    rw [Metric.mem_closedBall]
    linarith
  obtain ⟨h1, h2⟩ := hx hxB'
  refine ⟨h1, h2.trans ?_⟩
  refine add_le_add le_rfl ?_
  -- `γ'^n ≤ 4^α (r/R₀)^α`
  have hrR0 : 0 < r / R₀ := div_pos hr hR₀
  have hlow : ((4 : ℝ) ^ (n + 1))⁻¹ ≤ r / R₀ := by
    rw [div_lt_iff₀ hr] at hn2
    rw [inv_le_iff_one_le_mul₀ (pow_pos (by norm_num) _), div_mul_eq_mul_div, le_div_iff₀ hR₀]
    linarith
  have hpow : γ' ^ (n + 1) ≤ (r / R₀) ^ α := by
    calc γ' ^ (n + 1) = (((4 : ℝ) ^ (n + 1))⁻¹) ^ α := by
          rw [Real.inv_rpow (pow_nonneg (by norm_num) _), ← Real.rpow_natCast_mul (by norm_num),
            mul_comm, Real.rpow_mul_natCast (by norm_num), h4α, inv_pow, inv_inv]
      _ ≤ (r / R₀) ^ α :=
          Real.rpow_le_rpow (inv_nonneg.2 (pow_nonneg (by norm_num) _)) hlow hαpos.le
  calc A₀ * γ' ^ n = A₀ * (γ'⁻¹ * γ' ^ (n + 1)) := by
        rw [pow_succ]
        field_simp
    _ ≤ A₀ * (γ'⁻¹ * (r / R₀) ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (inv_nonneg.2 hγ'0.le)) hA₀0
    _ = A₀ * 4 ^ α * (r / R₀) ^ α := by rw [h4α]; ring

end IsWeakEigensolution

/-! ### A Hölder representative -/

/-- Averages of a function with values a.e. in `[m, M]` on `s` lie in `[m, M]`. -/
theorem setAverage_mem_Icc_of_ae {s : Set (Euc d)} (hs : MeasurableSet s) (hs0 : volume s ≠ 0)
    (hsfin : volume s ≠ ⊤) {v : Euc d → ℝ} (hvi : IntegrableOn v s) {m M : ℝ}
    (h : ∀ᵐ x, x ∈ s → v x ∈ Icc m M) : ⨍ x in s, v x ∈ Icc m M := by
  have hreal : 0 < (volume s).toReal := ENNReal.toReal_pos hs0 hsfin
  have h' : ∀ᵐ x ∂(volume.restrict s), v x ∈ Icc m M := (ae_restrict_iff' hs).2 h
  have hc : ∀ c : ℝ, IntegrableOn (fun _ => c) s := fun c => integrableOn_const hsfin
  have h1 : (volume s).toReal * m ≤ ∫ x in s, v x := by
    have := integral_mono_ae (hc m) hvi (h'.mono fun x hx => hx.1)
    rwa [setIntegral_const, smul_eq_mul, Measure.real] at this
  have h2 : ∫ x in s, v x ≤ (volume s).toReal * M := by
    have := integral_mono_ae hvi (hc M) (h'.mono fun x hx => hx.2)
    rwa [setIntegral_const, smul_eq_mul, Measure.real] at this
  rw [setAverage_eq, smul_eq_mul, Measure.real]
  constructor
  · rw [le_inv_mul_iff₀ hreal]
    linarith
  · rw [inv_mul_le_iff₀ hreal]
    linarith

/-- **A locally Hölder representative from oscillation bounds** (Campanato-type argument): if a
bounded measurable `v` satisfies `v ∈ [m, m + C₀ (r/R₀)^α]` a.e. on `ball x₀ r` for all
`r ≤ R₀ ≤ 1` whenever `closedBall x₀ (3R₀) ⊆ U`, then the limits of the averages of `v` over
shrinking closed balls define a representative of `v` on `U` (Lebesgue differentiation) that is
continuous on `U` and Hölder continuous on every compact subset of `U`. -/
theorem exists_holder_representative {U : Set (Euc d)} (hU : IsOpen U) {v : Euc d → ℝ}
    (hvm : Measurable v) {S₀ : ℝ} (hv0 : ∀ x, v x ∈ Icc 0 S₀) {α C₀ : ℝ} (hα : 0 < α)
    (hC₀ : 0 ≤ C₀)
    (hosc : ∀ (x₀ : Euc d) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 → Metric.closedBall x₀ (3 * R₀) ⊆ U →
      ∀ r : ℝ, 0 < r → r ≤ R₀ →
        ∃ m : ℝ, ∀ᵐ x, x ∈ Metric.ball x₀ r → v x ∈ Icc m (m + C₀ * (r / R₀) ^ α)) :
    ∃ φ : Euc d → ℝ, φ =ᵐ[volume.restrict U] v ∧ ContinuousOn φ U ∧
      ∀ S : Set (Euc d), IsCompact S → S ⊆ U → ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r φ S := by
  have hS₀ : 0 ≤ S₀ := (hv0 0).1.trans (hv0 0).2
  have hδ : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hint : ∀ s : Set (Euc d), volume s ≠ ⊤ → IntegrableOn v s := fun s hs =>
    Integrable.mono' (integrableOn_const hs (C := S₀)) hvm.aestronglyMeasurable.restrict
      (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hv0 x).1]; exact (hv0 x).2)
  obtain ⟨a, ha⟩ : ∃ a : Euc d → ℕ → ℝ,
      a = fun x (n : ℕ) => ⨍ y in Metric.closedBall x (1 / ((n : ℝ) + 1)), v y := ⟨_, rfl⟩
  have havg : ∀ (z : Euc d) (n : ℕ) (B : Set (Euc d)) (m w : ℝ),
      Metric.closedBall z (1 / ((n : ℝ) + 1)) ⊆ B → (∀ᵐ x, x ∈ B → v x ∈ Icc m (m + w)) →
      a z n ∈ Icc m (m + w) := by
    intro z n B m w hsub hB
    rw [ha]
    exact setAverage_mem_Icc_of_ae measurableSet_closedBall
      (Metric.measure_closedBall_pos volume z (hδ n)).ne' measure_closedBall_lt_top.ne
      (hint _ measure_closedBall_lt_top.ne) (hB.mono fun x hx hxz => hx (hsub hxz))
  have havg0 : ∀ x n, a x n ∈ Icc 0 S₀ := fun x n => by
    have := havg x n univ 0 S₀ (subset_univ _)
      (Eventually.of_forall fun y _ => by rw [zero_add]; exact hv0 y)
    rwa [zero_add] at this
  -- the local interval bound
  have hball_int : ∀ (x₀ : Euc d) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 →
      Metric.closedBall x₀ (3 * R₀) ⊆ U → ∀ t : ℝ, 0 < t → 2 * t ≤ R₀ →
      ∃ m : ℝ, ∀ (z : Euc d) (n : ℕ), dist z x₀ ≤ t → 1 / ((n : ℝ) + 1) < t →
        a z n ∈ Icc m (m + C₀ * (2 * t / R₀) ^ α) := by
    intro x₀ R₀ hR₀ hR₀1 hball t ht htR
    obtain ⟨m, hm⟩ := hosc x₀ R₀ hR₀ hR₀1 hball (2 * t) (by linarith) htR
    refine ⟨m, fun z n hz hn => havg z n (Metric.ball x₀ (2 * t)) m _ (fun w hw => ?_) hm⟩
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith [dist_triangle w z x₀]
  -- choosing small radii
  have hsmall : ∀ R₀ : ℝ, 0 < R₀ → ∀ ε : ℝ, 0 < ε →
      ∃ t : ℝ, 0 < t ∧ 2 * t ≤ R₀ ∧ C₀ * (2 * t / R₀) ^ α < ε := by
    intro R₀ hR₀ ε hε
    have hq : 0 < ε / (2 * (C₀ + 1)) := div_pos hε (by linarith)
    obtain ⟨s', hs'⟩ : ∃ s' : ℝ, s' = min 1 ((ε / (2 * (C₀ + 1))) ^ α⁻¹) := ⟨_, rfl⟩
    have hs0 : 0 < s' := by
      rw [hs']
      exact lt_min one_pos (Real.rpow_pos_of_pos hq _)
    have hs1 : s' ≤ 1 := by
      rw [hs']
      exact min_le_left _ _
    have hsα : s' ^ α ≤ ε / (2 * (C₀ + 1)) := by
      have h1 : s' ≤ (ε / (2 * (C₀ + 1))) ^ α⁻¹ := by
        rw [hs']
        exact min_le_right _ _
      calc s' ^ α ≤ ((ε / (2 * (C₀ + 1))) ^ α⁻¹) ^ α := Real.rpow_le_rpow hs0.le h1 hα.le
        _ = ε / (2 * (C₀ + 1)) := Real.rpow_inv_rpow hq.le hα.ne'
    refine ⟨R₀ * s' / 2, by positivity, by nlinarith, ?_⟩
    have e : 2 * (R₀ * s' / 2) / R₀ = s' := by
      field_simp
    rw [e]
    calc C₀ * s' ^ α ≤ C₀ * (ε / (2 * (C₀ + 1))) := mul_le_mul_of_nonneg_left hsα hC₀
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
  -- convergence of the averages
  have hconv : ∀ x ∈ U, ∃ L, Tendsto (a x) atTop (𝓝 L) := by
    intro x hx
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU x hx
    have hR₀ : 0 < min 1 (ρ / 4) := lt_min one_pos (by linarith)
    have hball : Metric.closedBall x (3 * min 1 (ρ / 4)) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith [min_le_right 1 (ρ / 4)])).trans hρU
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨t, ht0, htR, htε⟩ := hsmall _ hR₀ ε hε
    obtain ⟨m, hm⟩ := hball_int x _ hR₀ (min_le_left _ _) hball t ht0 htR
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt ht0
    refine ⟨N, fun n hn => ?_⟩
    have hnt : 1 / ((n : ℝ) + 1) < t :=
      (Nat.one_div_le_one_div hn).trans_lt hN
    have h1 := hm x n (by rw [dist_self]; exact ht0.le) hnt
    have h2 := hm x N (by rw [dist_self]; exact ht0.le) hN
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨φ, hφ⟩ : ∃ φ : Euc d → ℝ, φ = fun x => limUnder atTop (a x) := ⟨_, rfl⟩
  have hφlim : ∀ x ∈ U, Tendsto (a x) atTop (𝓝 (φ x)) := fun x hx => by
    rw [hφ]
    exact tendsto_nhds_limUnder (hconv x hx)
  have hφ0 : ∀ x ∈ U, φ x ∈ Icc 0 S₀ := fun x hx =>
    isClosed_Icc.mem_of_tendsto (hφlim x hx) (Eventually.of_forall fun n => havg0 x n)
  -- Hölder continuity on compact sets
  have hholder : ∀ S : Set (Euc d), IsCompact S → S ⊆ U →
      ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r φ S := by
    intro S hS hSU
    obtain ⟨δ, hδ0, hδU⟩ := hS.exists_cthickening_subset_open hU hSU
    have hR₀ : 0 < min 1 (δ / 4) := lt_min one_pos (by linarith)
    have hball : ∀ x ∈ S, Metric.closedBall x (3 * min 1 (δ / 4)) ⊆ U := fun x hx =>
      ((Metric.closedBall_subset_closedBall (by linarith [min_le_right 1 (δ / 4)])).trans
        (Metric.closedBall_subset_cthickening hx δ)).trans hδU
    obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = (C₀ + S₀) * (2 / min 1 (δ / 4)) ^ α := ⟨_, rfl⟩
    have hKc0 : 0 ≤ Kc := by
      rw [hKc]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (div_pos two_pos hR₀).le _)
    have hbound : ∀ x ∈ S, ∀ y ∈ S, |φ x - φ y| ≤ Kc * dist x y ^ α := by
      intro x hx y hy
      rcases (dist_nonneg : 0 ≤ dist x y).eq_or_lt with h0 | hpos
      · rw [← h0, Real.zero_rpow hα.ne', mul_zero, (dist_eq_zero.1 h0.symm), sub_self, abs_zero]
      have hfac : (2 * dist x y / min 1 (δ / 4)) ^ α =
          (2 / min 1 (δ / 4)) ^ α * dist x y ^ α := by
        rw [← Real.mul_rpow (div_pos two_pos hR₀).le dist_nonneg]
        congr 1
        field_simp
      rcases le_or_gt (2 * dist x y) (min 1 (δ / 4)) with hle | hgt
      · obtain ⟨m, hm⟩ := hball_int x _ hR₀ (min_le_left _ _) (hball x hx) (dist x y) hpos hle
        have hev : ∀ᶠ n in atTop, |a x n - a y n| ≤ C₀ * (2 * dist x y / min 1 (δ / 4)) ^ α := by
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
          filter_upwards [eventually_ge_atTop N] with n hn
          have hnt : 1 / ((n : ℝ) + 1) < dist x y := (Nat.one_div_le_one_div hn).trans_lt hN
          have h1 := hm x n (by rw [dist_self]; exact dist_nonneg) hnt
          have h2 := hm y n (by rw [dist_comm]) hnt
          rw [abs_le]
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        have hlim := ((hφlim x (hSU hx)).sub (hφlim y (hSU hy))).abs
        refine (le_of_tendsto hlim hev).trans ?_
        rw [hfac, hKc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg
          (Real.rpow_nonneg (div_pos two_pos hR₀).le _) (Real.rpow_nonneg dist_nonneg _))
      · have h1 : 1 ≤ (2 * dist x y / min 1 (δ / 4)) ^ α :=
          Real.one_le_rpow ((one_le_div hR₀).2 hgt.le) hα.le
        have h2 : |φ x - φ y| ≤ S₀ := by
          obtain ⟨hx1, hx2⟩ := hφ0 x (hSU hx)
          obtain ⟨hy1, hy2⟩ := hφ0 y (hSU hy)
          rw [abs_le]
          constructor <;> linarith
        calc |φ x - φ y| ≤ S₀ * 1 := by rw [mul_one]; exact h2
          _ ≤ S₀ * (2 * dist x y / min 1 (δ / 4)) ^ α := mul_le_mul_of_nonneg_left h1 hS₀
          _ = S₀ * ((2 / min 1 (δ / 4)) ^ α * dist x y ^ α) := by rw [hfac]
          _ ≤ Kc * dist x y ^ α := by
              rw [hKc, ← mul_assoc]
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
                (Real.rpow_nonneg (div_pos two_pos hR₀).le _)) (Real.rpow_nonneg dist_nonneg _)
    refine ⟨Real.toNNReal Kc, Real.toNNReal α, Real.toNNReal_pos.2 hα, fun x hx y hy => ?_⟩
    have e1 : ((Real.toNNReal Kc : NNReal) : ℝ≥0∞) = ENNReal.ofReal Kc := rfl
    rw [edist_dist, edist_dist, Real.coe_toNNReal _ hα.le, e1,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le, ← ENNReal.ofReal_mul hKc0]
    exact ENNReal.ofReal_le_ofReal (by rw [Real.dist_eq]; exact hbound x hx y hy)
  have hcont : ContinuousOn φ U := fun x hx => by
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨C, r, hr, hC⟩ := hholder (Metric.closedBall x (ρ / 2)) (isCompact_closedBall x _)
      ((Metric.closedBall_subset_ball (by linarith)).trans hρU)
    exact (((hC.continuousOn hr) x (Metric.mem_closedBall_self (by linarith))).continuousAt
      (Metric.closedBall_mem_nhds x (by linarith))).continuousWithinAt
  refine ⟨φ, ?_, hcont, hholder⟩
  have hloc : LocallyIntegrable v := fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, hint _ measure_ball_lt_top.ne⟩
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average volume hloc 1
  rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards [hleb] with x hx hxU
  have h1 : Tendsto (a x) atTop (𝓝 (v x)) := by
    rw [ha]
    exact hx (fun _ => x) (fun n : ℕ => 1 / ((n : ℝ) + 1))
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall hδ⟩)
      (Eventually.of_forall fun n => Metric.mem_closedBall_self (by
        rw [one_mul]; exact (hδ n).le))
  exact tendsto_nhds_unique (hφlim x hxU) h1

/-- **Hölder continuity of bounded weak eigensolutions** (De Giorgi–Nash–Moser; Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Theorem 8.22; Serrin 1964, Trudinger
1967 for `p`-Laplacian-type structure; towards Mosconi–Riey–Squassina 2024, Proposition 4.5, paper
Appendix A, *Eigenfunction inputs*): a bounded nonnegative weak solution of `-div a(∇u) = λ u^{p-1}`
on an open set `K` has a representative that is continuous on `K` and Hölder continuous on every
compact subset of `K`.

Proof: pass to a measurable representative with values in `[0, S]`; `exists_holder_osc`
(oscillation decay from the logarithmic Poincaré bound and the scale-invariant Moser sup bound for
level functions) gives the oscillation bounds of `exists_holder_representative`. In dimension `0`
the space is a point. -/
theorem holder_solution {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {K : Set (Euc d)} (hK : IsOpen K) {lam : ℝ} {u : Euc d → ℝ}
    (hu : IsWeakEigensolution p F K lam u) (hbdd : ∃ M : ℝ, ∀ᵐ x, u x ≤ M) :
    ∃ φ : Euc d → ℝ, φ =ᵐ[volume.restrict K] u ∧ ContinuousOn φ K ∧
      ∀ S : Set (Euc d), IsCompact S → S ⊆ K →
        ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r φ S := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · have hconst : u = fun _ => u 0 := funext fun x => by rw [Subsingleton.elim x 0]
    refine ⟨u, EventuallyEq.rfl, ?_, fun S _ _ => ⟨0, 1, one_pos, fun x _ y _ => ?_⟩⟩
    · rw [hconst]
      exact continuousOn_const
    · rw [Subsingleton.elim x y]
      simp
  have hd0 : 0 < d := Fin.pos_iff_nonempty.2 hd
  obtain ⟨M, hM⟩ := hbdd
  have hS0 : 0 ≤ max M 0 := le_max_right _ _
  have hmeas := hu.memW0.memLp.aestronglyMeasurable
  obtain ⟨v, hvdef⟩ : ∃ v : Euc d → ℝ, v = fun x => max 0 (min (hmeas.mk u x) (max M 0)) :=
    ⟨_, rfl⟩
  have hvmeas : Measurable v := by
    rw [hvdef]
    exact measurable_const.max (hmeas.stronglyMeasurable_mk.measurable.min measurable_const)
  have hvS : ∀ x, v x ∈ Icc 0 (max M 0) := fun x => by
    rw [hvdef]
    exact clamp_mem hS0 _
  have hvu : v =ᵐ[volume] u := by
    filter_upwards [hmeas.ae_eq_mk, hM] with x h1 h2
    rw [hvdef]
    show max 0 (min (hmeas.mk u x) (max M 0)) = u x
    rw [← h1]
    exact clamp_eq ⟨hu.nonneg x, h2.trans (le_max_left _ _)⟩
  have hv := hu.congr_ae hvu fun x => (hvS x).1
  obtain ⟨α, hα, C₀, hC₀, hosc⟩ := hv.exists_holder_osc hp hF hd0 hS0 hvS hvmeas
  obtain ⟨φ, hφv, hφc, hφH⟩ := exists_holder_representative hK hvmeas hvS hα hC₀ hosc
  exact ⟨φ, hφv.trans (ae_restrict_of_ae hvu), hφc, hφH⟩

end Komlos.Literature
