import Komlos.Literature.Regularized.BoundaryShrink

/-!
# Lane `L2` (`reg/positivity`), step 3: boundary continuity

`REGULARIZED_ROUTE.md`, Revision 2 (ii), boundary half.  The interior representative `φ` of the
minimizer is continuous on `K` (`IsRegMinimizer.exists_interior_continuous_rep`); this file
shows that it tends to `0` at every boundary point, so that `K.indicator φ` is continuous on
all of `ℝ^d`.

## The geometry

`K` is open and convex, so at a boundary point `x₀` there is a supporting functional
(`exists_supporting_functional`, geometric Hahn–Banach): a continuous linear `ℓ` with
`ℓ x < ℓ x₀` for every `x ∈ K`.  Hence `K ⊆ {ℓ < ℓ x₀}`, and the point reflection
`σ(x) = 2x₀ - x` — which preserves Lebesgue measure and every ball centred at `x₀` — exchanges
`{ℓ < ℓ x₀}` with `{ℓ > ℓ x₀}`.  Therefore

`2 |B_r(x₀) ∩ K| ≤ |B_r(x₀)|`  (`measure_inter_le_half_of_supporting`),

i.e. **the complement of `K` occupies at least half of every ball centred at `x₀`**.  This is
exactly the density hypothesis of De Giorgi's boundary lemma.

## The analysis

The zero extension of the minimizer satisfies the `DG⁺` energy inequality on *all* balls of
`ℝ^d` at every level `k ≥ 0` (the competitor `v - η²(v-k)_+` is admissible for the local
problem even when the ball sticks out of `K`, because it still vanishes off `K`).  De Giorgi's
boundary lemma then gives `ess sup_{B_{r/2}} v ≤ θ ess sup_{B_r} v` with `θ < 1` for all small
`r`, hence `ess sup_{B_r} v → 0`.  That is `exists_boundary_sup_decay` — the one named `sorry`
of this file.

## Contents

* `exists_supporting_functional`, `measure_inter_le_half_of_supporting` — the geometry (proved).
* `le_of_ae_le_const_on_open` — from an essential bound to a pointwise bound for a continuous
  representative (proved).
* `exists_boundary_sup_decay` — De Giorgi's boundary lemma (proved, from
  `exists_measure_shrink` and lane `DGN`'s `exists_dg_sup_bound`).
* `tendsto_zero_nhdsWithin_of_sup_decay` — the assembly `φ → 0` at the boundary (proved).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### From essential to pointwise bounds -/

/-- If `φ` is continuous on the open set `U`, agrees a.e. on `U` with `v`, and `v ≤ ε` a.e. on
`U`, then `φ ≤ ε` everywhere on `U`: otherwise `φ > ε` on a ball of positive measure. -/
theorem le_of_ae_le_const_on_open {U : Set (Euc d)} (hU : IsOpen U) {φ v : Euc d → ℝ} {ε : ℝ}
    (hφc : ContinuousOn φ U) (hφv : ∀ᵐ x, x ∈ U → φ x = v x)
    (hv : ∀ᵐ x, x ∈ U → v x ≤ ε) : ∀ x ∈ U, φ x ≤ ε := by
  intro x₀ hx₀
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hev : ∀ᶠ y in 𝓝 x₀, ε < φ y :=
    (hφc.continuousAt (hU.mem_nhds hx₀)).eventually (lt_mem_nhds hcon)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hρ : 0 < min δ r := lt_min hδ hr
  have hnull : volume (Metric.ball x₀ (min δ r)) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hφv, hv] with y h1 h2 hy
    have hyδ : y ∈ Metric.ball x₀ δ := Metric.ball_subset_ball (min_le_left δ r) hy
    have hyU : y ∈ U := hball (Metric.ball_subset_ball (min_le_right δ r) hy)
    have := hδball y hyδ
    rw [h1 hyU] at this
    exact absurd (h2 hyU) (not_le.2 this)
  exact (Metric.measure_ball_pos volume x₀ hρ).ne' hnull

/-- **Nonnegativity of a continuous representative on an open set.** -/
theorem nonneg_of_ae_eq_on_open {U : Set (Euc d)} (hU : IsOpen U) {φ v : Euc d → ℝ}
    (hφc : ContinuousOn φ U) (hφv : ∀ᵐ x, x ∈ U → φ x = v x) (hv0 : ∀ x, 0 ≤ v x) :
    ∀ x ∈ U, 0 ≤ φ x := by
  intro x₀ hx₀
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hev : ∀ᶠ y in 𝓝 x₀, φ y < 0 :=
    (hφc.continuousAt (hU.mem_nhds hx₀)).eventually (gt_mem_nhds hcon)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hρ : 0 < min δ r := lt_min hδ hr
  have hnull : volume (Metric.ball x₀ (min δ r)) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hφv] with y h1 hy
    have hyδ : y ∈ Metric.ball x₀ δ := Metric.ball_subset_ball (min_le_left δ r) hy
    have hyU : y ∈ U := hball (Metric.ball_subset_ball (min_le_right δ r) hy)
    have := hδball y hyδ
    rw [h1 hyU] at this
    exact absurd (hv0 y) (not_le.2 this)
  exact (Metric.measure_ball_pos volume x₀ hρ).ne' hnull

/-! ### De Giorgi's boundary lemma -/

set_option maxHeartbeats 1000000 in
/-- **De Giorgi's boundary lemma for the regularized minimizer**
(`REGULARIZED_ROUTE.md`, Revision 2 (ii); Ladyzhenskaya–Ural'tseva, *Linear and Quasilinear
Elliptic Equations*, Ch. II §7; Giusti, *Direct Methods in the Calculus of Variations*, Thm 7.8):
at a boundary point `x₀` of the convex set `K` the essential supremum of the (zero-extended)
minimizer on `B_ρ(x₀)` tends to `0` as `ρ ↓ 0`.

Proof.  The zero extension of `v` satisfies the `DG⁺` energy inequality

`∫_{B_r ∩ {v > k}} ‖∇v‖² ≤ γ (s-r)⁻² ∫_{B_s} (v-k)_+² + γ χ² |B_s ∩ {v > k}|`

on **every** ball of `ℝ^d` — not only on balls inside `K` — for every level `k ≥ 0`: the
competitor `v - η²(v-k)_+` of `isDG_of_regMinimizer` still vanishes off `K` and is still
nonnegative and bounded, so it is still an `IsRegComp K` competitor, and the comparison of
`regFree` runs verbatim.  (For `k ≥ 0` the truncation `(v - k)_+` vanishes where `v` does, i.e.
off `K`; this is exactly the point at which nonnegativity of the level is used.)

Now `measure_inter_le_half_of_supporting` says `|B_r(x₀) ∖ {v > 0}| ≥ |B_r(x₀) ∖ K| ≥ |B_r|/2`
for every `r`.  De Giorgi's measure-shrinking lemma applied to the levels
`k_j = (1 - 2^{-j}) H`, `H = ess sup_{B_r} v`, converts this fixed density of the zero set into
a small measure of `{v > k_J}` for a `J = J(d, γ)` depending only on the structural constants,
and the local boundedness estimate `exists_dg_sup_bound` at the level `k_J` then gives
`ess sup_{B_{r/2}} v ≤ θ ess sup_{B_r} v + c χ r` with `θ = 1 - 2^{-J} < 1`.  Iterating on
`r_n = 4^{-n} r₀` yields `ess sup_{B_{r_n}} v → 0`.

Formally: `exists_isDGSub_univ` supplies (a), `exists_measure_shrink`
(`Komlos/Literature/Regularized/BoundaryShrink.lean`) supplies the measure-shrinking step,
`exists_dg_sup_bound` (lane `DGN`) turns the resulting smallness of `|B ∩ {v > k_J}|` into the
one-scale contraction `ess sup_{B_R} v ≤ θ ess sup_{B_{4R}} v + C R` with
`θ = 1 - 2^{-J-2} < 1`, and the scale iteration `R_m = 4^{-m} R₀` finishes. -/
theorem exists_boundary_sup_decay (hd : 0 < d) (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) {v : Euc d → ℝ} (hv : IsRegMinimizer 2 κ Ψ K v)
    (hcomp : IsRegComp K v) (hvm : Measurable v) {x₀ : Euc d} (hx₀ : x₀ ∈ frontier K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)), v x ≤ ε := by
  classical
  -- a measurable weak gradient field, and the global `DG⁺` membership
  obtain ⟨G, hGm, hG, hGg⟩ : ∃ G : Euc d → Euc d, Measurable G ∧ HasWeakGradient v G ∧
      G =ᵐ[volume] weakGrad v := by
    refine ⟨hcomp.aestronglyMeasurable_grad.mk (weakGrad v),
      hcomp.aestronglyMeasurable_grad.stronglyMeasurable_mk.measurable, ?_,
      hcomp.aestronglyMeasurable_grad.ae_eq_mk.symm⟩
    exact hcomp.memW0.hasWeakGradient.congr_right
      hcomp.aestronglyMeasurable_grad.ae_eq_mk
  obtain ⟨γ, hγ0, hdg⟩ := exists_isDGSub_univ hκ hΨ hK hv hcomp hG hvm hGm hGg
  obtain ⟨Csup, hCsup0, hsupbd⟩ := exists_dg_sup_bound hd hγ0
  -- the density parameter of the critical-density step
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = 1 / (4 * Csup ^ 2) := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hνdef]; positivity
  have hsqrtν : Real.sqrt ν = 1 / (2 * Csup) := by
    rw [hνdef, show (1 : ℝ) / (4 * Csup ^ 2) = (1 / (2 * Csup)) ^ 2 by field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  obtain ⟨J, hJ0, hshrink⟩ := exists_measure_shrink hd hκ hΨ hK hv hcomp hvm hx₀ hν
  -- the contraction constants
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = 1 - (1 / 2 : ℝ) ^ (J + 2) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂def⟩ : ∃ c₂ : ℝ, c₂ = (1 / 2 : ℝ) ^ (J + 2) := ⟨_, rfl⟩
  have hc₂0 : 0 < c₂ := by rw [hc₂def]; positivity
  have hc₂1 : c₂ ≤ 1 / 4 := by
    rw [hc₂def]
    calc (1 / 2 : ℝ) ^ (J + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hθ0 : 1 / 4 ≤ θ := by rw [hθdef]; linarith
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθnn : 0 ≤ θ := by linarith
  obtain ⟨Cb, hCbdef⟩ : ∃ Cb : ℝ, Cb = 2 * Csup := ⟨_, rfl⟩
  have hCb0 : 0 < Cb := by rw [hCbdef]; linarith
  -- the contraction
  have hcontr : ∀ Rb H : ℝ, 0 < Rb → 0 < H → Rb ≤ c₂ * H →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (4 * Rb))), v x ≤ H) →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ Rb)), v x ≤ θ * H + Cb * Rb := by
    intro Rb H hRb hH hsmall hbnd
    obtain ⟨kJ, hkJdef⟩ : ∃ kJ : ℝ, kJ = H * (1 - (1 / 2 : ℝ) ^ (J + 1)) := ⟨_, rfl⟩
    have hhalfJ : (0 : ℝ) < (1 / 2 : ℝ) ^ (J + 1) := by positivity
    have hhalfJ1 : (1 / 2 : ℝ) ^ (J + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hkJ0 : 0 ≤ kJ := by rw [hkJdef]; nlinarith
    have hHkJ : H - kJ = H * (1 / 2 : ℝ) ^ (J + 1) := by rw [hkJdef]; ring
    have hHkJ0 : 0 ≤ H - kJ := by rw [hHkJ]; positivity
    -- the measure of the top level set is small
    have hRH : (2 : ℝ) ^ (J + 1) * (2 * Rb) ≤ H := by
      have hpow : (2 : ℝ) ^ (J + 1) * 2 * (1 / 2 : ℝ) ^ (J + 2) = 1 := by
        rw [div_pow, one_pow, ← pow_succ]
        field_simp
      have h1 : (2 : ℝ) ^ (J + 1) * (2 * (c₂ * H)) = H := by
        rw [hc₂def]
        calc (2 : ℝ) ^ (J + 1) * (2 * ((1 / 2 : ℝ) ^ (J + 2) * H))
            = ((2 : ℝ) ^ (J + 1) * 2 * (1 / 2 : ℝ) ^ (J + 2)) * H := by ring
          _ = H := by rw [hpow]; ring
      have h2 : (2 : ℝ) ^ (J + 1) * (2 * Rb) ≤ (2 : ℝ) ^ (J + 1) * (2 * (c₂ * H)) := by
        have : (0 : ℝ) < (2 : ℝ) ^ (J + 1) := by positivity
        nlinarith
      linarith
    have hbnd2 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (2 * (2 * Rb)))), v x ≤ H := by
      have he : (2 : ℝ) * (2 * Rb) = 4 * Rb := by ring
      rw [he]
      exact hbnd
    have hmeas := hshrink (2 * Rb) H (by linarith) hH hRH hbnd2
    rw [← hkJdef] at hmeas
    -- the local maximum principle at the level `kJ`
    have hsup := hsupbd 1 (2 * Rb) Set.univ v G zero_le_one (hdg (2 * Rb)) x₀ (2 * Rb)
      (by linarith) le_rfl (Set.subset_univ _) kJ
    have hhalf : (2 * Rb) / 2 = Rb := by ring
    rw [hhalf] at hsup
    -- the average of the truncation is small
    have hBfin : volume (Metric.ball x₀ (2 * Rb)) ≠ ⊤ :=
      (measure_ball_lt_top (x := x₀) (r := 2 * Rb)).ne
    have hBpos : (0 : ℝ) < (volume (Metric.ball x₀ (2 * Rb))).toReal :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ (by linarith)).ne' hBfin
    have hIle : (∫ y in Metric.ball x₀ (2 * Rb), max (v y - kJ) 0 ^ 2) ≤
        (H - kJ) ^ 2 * ((volume (Metric.ball x₀ (2 * Rb) ∩ {x | kJ < v x})).toReal) := by
      have hAm : MeasurableSet {x : Euc d | kJ < v x} := measurableSet_lt measurable_const hvm
      have hind : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ (2 * Rb))),
          max (v y - kJ) 0 ^ 2 ≤
            Set.indicator {x : Euc d | kJ < v x} (fun _ => (H - kJ) ^ 2) y := by
        have hbnd' : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ (2 * Rb))), v y ≤ H := by
          refine (ae_restrict_iff' measurableSet_ball).2 ?_
          have := (ae_restrict_iff' measurableSet_ball).1 hbnd
          filter_upwards [this] with y hy hyb
          exact hy (Metric.ball_subset_ball (by linarith) hyb)
        filter_upwards [hbnd'] with y hy
        by_cases hyA : y ∈ {x : Euc d | kJ < v x}
        · rw [Set.indicator_of_mem hyA]
          have h0 : (0 : ℝ) ≤ max (v y - kJ) 0 := le_max_right _ _
          have h1 : max (v y - kJ) 0 ≤ H - kJ := max_le (by linarith) hHkJ0
          nlinarith
        · rw [Set.indicator_of_notMem hyA]
          have hyk : v y ≤ kJ := not_lt.1 hyA
          rw [max_eq_right (by linarith)]
          simp
      have hint1 : IntegrableOn (fun y => max (v y - kJ) 0 ^ 2)
          (Metric.ball x₀ (2 * Rb)) volume := by
        have hc : Continuous fun t : ℝ => max (t - kJ) 0 :=
          (continuous_id.sub continuous_const).max continuous_const
        obtain ⟨M, hM⟩ := hcomp.exists_le
        refine Integrable.mono'
          (integrableOn_const (μ := volume) (C := (max (M - kJ) 0 + |kJ|) ^ 2) hBfin)
          ((hc.comp_aestronglyMeasurable hcomp.aestronglyMeasurable).pow 2).restrict ?_
        refine ae_restrict_of_ae (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : max (v y - kJ) 0 ≤ max (M - kJ) 0 + |kJ| := by
          have h2 : v y - kJ ≤ M - kJ := by linarith [hM y]
          have h4 : max (v y - kJ) 0 ≤ max (M - kJ) 0 := max_le_max h2 le_rfl
          linarith [abs_nonneg kJ]
        exact sq_le_sq_of_nonneg (le_max_right _ _) h1
      have hint2 : IntegrableOn
          (Set.indicator {x : Euc d | kJ < v x} fun _ => (H - kJ) ^ 2)
          (Metric.ball x₀ (2 * Rb)) volume := by
        refine (integrableOn_const (μ := volume) (C := (H - kJ) ^ 2) hBfin).mono'
          (((aestronglyMeasurable_const).indicator hAm).restrict) ?_
        refine ae_restrict_of_ae (Eventually.of_forall fun y => ?_)
        by_cases hyA : y ∈ {x : Euc d | kJ < v x}
        · rw [Set.indicator_of_mem hyA, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        · rw [Set.indicator_of_notMem hyA, norm_zero]
          positivity
      have hmono := integral_mono_ae hint1 hint2 hind
      rw [setIntegral_indicator hAm, setIntegral_const] at hmono
      simpa [smul_eq_mul, measureReal_def, mul_comm] using hmono
    have havg : (⨍ y in Metric.ball x₀ (2 * Rb), max (v y - kJ) 0 ^ 2) ≤ (H - kJ) ^ 2 * ν := by
      have hstep2 : (∫ y in Metric.ball x₀ (2 * Rb), max (v y - kJ) 0 ^ 2) ≤
          (H - kJ) ^ 2 * ν * (volume (Metric.ball x₀ (2 * Rb))).toReal := by
        refine hIle.trans ?_
        have h := mul_le_mul_of_nonneg_left hmeas (sq_nonneg (H - kJ))
        calc (H - kJ) ^ 2 * (volume (Metric.ball x₀ (2 * Rb) ∩ {x | kJ < v x})).toReal
            ≤ (H - kJ) ^ 2 * (ν * (volume (Metric.ball x₀ (2 * Rb))).toReal) := h
          _ = (H - kJ) ^ 2 * ν * (volume (Metric.ball x₀ (2 * Rb))).toReal := by ring
      rw [setAverage_eq, smul_eq_mul, measureReal_def, inv_mul_le_iff₀ hBpos]
      linarith [hstep2]
    have hsqrt : Real.sqrt (⨍ y in Metric.ball x₀ (2 * Rb), max (v y - kJ) 0 ^ 2) ≤
        (H - kJ) * Real.sqrt ν := by
      refine (Real.sqrt_le_sqrt havg).trans (le_of_eq ?_)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hHkJ0]
    -- conclude the contraction
    filter_upwards [hsup] with x hx
    have hbound : kJ + Csup * ((H - kJ) * Real.sqrt ν + 1 * (2 * Rb)) ≤ θ * H + Cb * Rb := by
      rw [hsqrtν, hCbdef]
      have he : Csup * ((H - kJ) * (1 / (2 * Csup)) + 1 * (2 * Rb)) =
          (H - kJ) / 2 + 2 * Csup * Rb := by
        field_simp
        try ring
      rw [he, hθdef]
      have hpow1 : (1 / 2 : ℝ) ^ (J + 1) = (1 / 2 : ℝ) ^ J * (1 / 2) := pow_succ _ _
      have hpow2 : (1 / 2 : ℝ) ^ (J + 2) = (1 / 2 : ℝ) ^ J * (1 / 4) := by
        rw [pow_succ, pow_succ]; ring
      rw [hkJdef, hpow1, hpow2]
      ring_nf
      try linarith
    refine le_trans hx (le_trans ?_ hbound)
    have hCs : 0 ≤ Csup := hCsup0.le
    have hadd : Real.sqrt (⨍ y in Metric.ball x₀ (2 * Rb), max (v y - kJ) 0 ^ 2) +
        1 * (2 * Rb) ≤ (H - kJ) * Real.sqrt ν + 1 * (2 * Rb) := by linarith [hsqrt]
    have hstep3 := mul_le_mul_of_nonneg_left hadd hCs
    linarith [hstep3]
  -- the scale iteration
  obtain ⟨M, hM⟩ := hcomp.exists_le
  obtain ⟨M₁, hM₁def⟩ : ∃ M₁ : ℝ, M₁ = max M 1 := ⟨_, rfl⟩
  have hM₁0 : 0 < M₁ := by rw [hM₁def]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hvM₁ : ∀ x, v x ≤ M₁ := fun x => by rw [hM₁def]; exact (hM x).trans (le_max_left _ _)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, θ ^ n * M₁ ≤ ε / 2 := by
    have hlim : Filter.Tendsto (fun n : ℕ => θ ^ n * M₁) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθnn hθ1).mul_const M₁
      simpa using this
    have := (hlim.eventually (eventually_le_nhds (by linarith : (0:ℝ) < ε / 2))).exists
    obtain ⟨n, hn⟩ := this
    exact ⟨n, hn⟩
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = min (c₂ * M₁) (ε / (2 * (Cb * n + 1))) := ⟨_, rfl⟩
  have hR₀0 : 0 < R₀ := by
    rw [hR₀def]
    refine lt_min (by positivity) ?_
    have : (0 : ℝ) < 2 * (Cb * n + 1) := by positivity
    positivity
  have hR₀1 : R₀ ≤ c₂ * M₁ := by rw [hR₀def]; exact min_le_left _ _
  have hR₀2 : R₀ ≤ ε / (2 * (Cb * n + 1)) := by rw [hR₀def]; exact min_le_right _ _
  have hiter : ∀ m : ℕ, ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R₀ / 4 ^ m))),
      v x ≤ θ ^ m * M₁ + Cb * R₀ * m := by
    intro m
    induction m with
    | zero =>
      refine Eventually.of_forall fun x => ?_
      simpa using hvM₁ x
    | succ m ih =>
      have hRm : (0 : ℝ) < R₀ / 4 ^ (m + 1) := by positivity
      have hH : (0 : ℝ) < θ ^ m * M₁ + Cb * R₀ * m := by
        have h1 : (0 : ℝ) < θ ^ m := by positivity
        have h2 : (0 : ℝ) ≤ Cb * R₀ * m := by positivity
        nlinarith
      have hsmall : R₀ / 4 ^ (m + 1) ≤ c₂ * (θ ^ m * M₁ + Cb * R₀ * m) := by
        have hq : ((1 : ℝ) / 4) ^ m ≤ θ ^ m :=
          pow_le_pow_left₀ (by norm_num) (by linarith) m
        have hR : R₀ / 4 ^ (m + 1) ≤ (c₂ * M₁) * ((1 / 4 : ℝ) ^ m) := by
          rw [pow_succ]
          rw [div_le_iff₀ (by positivity)]
          have h4 : ((1 : ℝ) / 4) ^ m * (4 ^ m * 4) = 4 := by
            rw [div_pow, one_pow]
            field_simp
          nlinarith [hR₀1, mul_pos (pow_pos (by norm_num : (0:ℝ) < 4) m)
            (by norm_num : (0:ℝ) < 4)]
        have h2 : (c₂ * M₁) * ((1 / 4 : ℝ) ^ m) ≤ c₂ * (θ ^ m * M₁) := by
          have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ c₂ * M₁)
          nlinarith [hc₂0, hM₁0]
        have h3 : (0 : ℝ) ≤ c₂ * (Cb * R₀ * m) := by positivity
        have h4 : c₂ * (θ ^ m * M₁ + Cb * R₀ * m) = c₂ * (θ ^ m * M₁) + c₂ * (Cb * R₀ * m) := by
          ring
        linarith
      have hprev : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (4 * (R₀ / 4 ^ (m + 1))))),
          v x ≤ θ ^ m * M₁ + Cb * R₀ * m := by
        have he : (4 : ℝ) * (R₀ / 4 ^ (m + 1)) = R₀ / 4 ^ m := by
          rw [pow_succ]
          field_simp
          try ring
        rw [he]
        exact ih
      have hstep := hcontr (R₀ / 4 ^ (m + 1)) (θ ^ m * M₁ + Cb * R₀ * m) hRm hH hsmall hprev
      filter_upwards [hstep] with x hx
      refine hx.trans ?_
      have h1 : θ * (θ ^ m * M₁ + Cb * R₀ * m) = θ ^ (m + 1) * M₁ + θ * (Cb * R₀ * m) := by
        rw [pow_succ]; ring
      have h2 : θ * (Cb * R₀ * m) ≤ Cb * R₀ * m := by
        have : (0 : ℝ) ≤ Cb * R₀ * m := by positivity
        nlinarith
      have h3 : Cb * (R₀ / 4 ^ (m + 1)) ≤ Cb * R₀ := by
        have hle : R₀ / 4 ^ (m + 1) ≤ R₀ := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n := m + 1), hR₀0]
        exact mul_le_mul_of_nonneg_left hle hCb0.le
      push_cast
      rw [h1]
      linarith
  refine ⟨R₀ / 4 ^ n, by positivity, ?_⟩
  filter_upwards [hiter n] with x hx
  refine hx.trans ?_
  have h1 : Cb * R₀ * n ≤ ε / 2 := by
    have hden : (0 : ℝ) < 2 * (Cb * n + 1) := by positivity
    have hcn : (0 : ℝ) ≤ Cb * n := by positivity
    have h2 : Cb * R₀ * n ≤ Cb * (ε / (2 * (Cb * n + 1))) * n := by
      linarith [mul_le_mul_of_nonneg_left hR₀2 hcn]
    have h3 : Cb * (ε / (2 * (Cb * n + 1))) * n ≤ ε / 2 := by
      have hkey : Cb * (ε / (2 * (Cb * (n : ℝ) + 1))) * n =
          (Cb * n) * ε / (2 * (Cb * n + 1)) := by
        field_simp
        try ring
      rw [hkey, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
      nlinarith [hε.le, Nat.cast_nonneg (α := ℝ) n, hCb0.le]
    linarith
  linarith

/-! ### The assembly -/

/-- **Zero boundary values of the continuous interior representative.**  Combining
`exists_boundary_sup_decay` (an essential bound `v ≤ ε` on a small ball around the boundary
point) with `le_of_ae_le_const_on_open` (which upgrades it to a pointwise bound for the
continuous representative on the open set `K ∩ B_ρ`) and nonnegativity. -/
theorem tendsto_zero_nhdsWithin_of_sup_decay {φ v : Euc d → ℝ} (hK : IsGoodConvex K)
    (hφc : ContinuousOn φ K) (hφv : φ =ᵐ[volume.restrict K] v) (hv0 : ∀ x, 0 ≤ v x)
    {x₀ : Euc d}
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)), v x ≤ ε) :
    Tendsto φ (𝓝[K] x₀) (𝓝 0) := by
  have hφv' : ∀ᵐ x : Euc d, x ∈ K → φ x = v x := (ae_restrict_iff' hK.isOpen.measurableSet).1 hφv
  have hnn : ∀ x ∈ K, 0 ≤ φ x := nonneg_of_ae_eq_on_open hK.isOpen hφc hφv' hv0
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨ρ, hρ, hball⟩ := hdecay (ε / 2) (by linarith)
  refine ⟨ρ, hρ, fun x hxK hxd => ?_⟩
  have hU : IsOpen (K ∩ Metric.ball x₀ ρ) := hK.isOpen.inter Metric.isOpen_ball
  have hxU : x ∈ K ∩ Metric.ball x₀ ρ := ⟨hxK, Metric.mem_ball.2 hxd⟩
  have hφvU : ∀ᵐ y : Euc d, y ∈ K ∩ Metric.ball x₀ ρ → φ y = v y := by
    filter_upwards [hφv'] with y hy hyU
    exact hy hyU.1
  have hvU : ∀ᵐ y : Euc d, y ∈ K ∩ Metric.ball x₀ ρ → v y ≤ ε / 2 := by
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hball] with y hy hyU
    exact hy hyU.2
  have hle := le_of_ae_le_const_on_open hU (hφc.mono Set.inter_subset_left) hφvU hvU x hxU
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn x hxK)]
  linarith

end Komlos.Literature.Regularized
