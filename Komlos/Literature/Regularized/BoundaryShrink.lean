import Komlos.Literature.Regularized.PositivityDG

/-!
# Lane `L2` (`reg/positivity`): De Giorgi's measure-shrinking lemma at the boundary

The boundary estimate of `REGULARIZED_ROUTE.md`, Revision 2 (ii) needs one ingredient beyond
the level-set energy inequality: **De Giorgi's second (measure-shrinking) lemma**.  Its input is
the project's double-integral Poincaré inequality on a convex set,
`Komlos.Literature.MemW0.measure_mul_lintegral_sub_rpow_le`, at an exponent `p` strictly
between `1` and `2` — the exponent must be `< 2`, otherwise the iteration below does not decay
(the annulus measure that the Hölder/Young step produces is exactly what makes the sum over
levels telescope).

## The scheme

Fix a ball `B` and levels `k_j = H(1 - 2^{-j-1})`, `j = 0, …, J`, with gaps
`δ_j = H 2^{-j-2}`.  Write `a_j = |B ∩ {v > k_j}|` and `m_j = |B ∩ {k_j < v ≤ k_{j+1}}|`.
Applied to the level truncation `T_j = (v-k_j)_+ - (v-k_{j+1})_+` (which is `0` where
`v ≤ k_j` and `δ_j` where `v ≥ k_{j+1}`), the Poincaré inequality gives

`a_{j+1} · |B ∩ {v ≤ k_j}| · δ_j^p ≤ 2^d (2R)^p |B| ∫_{B ∩ ann_j} ‖∇v‖^p`,

and the elementary Young inequality `t^p ≤ λ^{p-2} t² + λ^p` (valid for `1 ≤ p ≤ 2`, `λ > 0`)
turns the right-hand side into `λ^{p-2} E_j + λ^p m_j`.  With `|B ∩ {v ≤ k_j}| ≥ |B|/2`
(the *boundary density*: `v` vanishes on at least half of every ball centred at a boundary
point of the convex set `K`) and `E_j/δ_j² ≤ Q` uniformly in `j` (the Caccioppoli inequality,
`exists_energy_ineq`), the choice `λ = δ_j μ` gives

`a_{j+1} ≤ 2^{d+1}(2R)^p (μ^{p-2} Q + μ^p m_j)`,

and summing over `j < J` (the annuli are disjoint, so `Σ m_j ≤ |B|`) and optimizing in `μ`
yields `a_J ≤ C_d |B| J^{-(2-p)/2}`, which is as small as we please.

## Contents

* `rpow_young_two` — the elementary `t^p ≤ λ^{p-2} t² + λ^p`.
* `levTrunc`, `memW0_levTrunc` — the level truncation `(v-k)_+ - (v-l)_+` and its membership
  in `W₀^{1,2}(K)`, and (at an exponent `p ≤ 2`, using that `K` is bounded)
  `memW0_levTrunc_rpow`.
* `measure_mul_measure_mul_rpow_le` — the packaged consequence of the double-integral Poincaré
  inequality: `|E| |Z| δ^p ≤ 2^d D^p |B| ∫_B ‖∇T‖^p` whenever `T ≥ δ` on `E` and `T = 0` on `Z`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### An elementary Young inequality -/

/-- `t^p ≤ λ^{p-2} t² + λ^p` for `0 ≤ t`, `0 < λ` and `1 ≤ p ≤ 2`: split at `t = λ`. -/
theorem rpow_young_two {p lam t : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hlam : 0 < lam)
    (ht : 0 ≤ t) : t ^ p ≤ lam ^ (p - 2) * t ^ 2 + lam ^ p := by
  have hlam0 : (0 : ℝ) < lam ^ (p - 2) := Real.rpow_pos_of_pos hlam _
  have hlamp : (0 : ℝ) < lam ^ p := Real.rpow_pos_of_pos hlam _
  rcases le_or_gt t lam with h | h
  · have h1 : t ^ p ≤ lam ^ p := Real.rpow_le_rpow ht h (by linarith)
    nlinarith [sq_nonneg t, hlam0.le]
  · have htpos : 0 < t := lt_trans hlam h
    have hsplit : t ^ p = t ^ (2 : ℝ) * t ^ (p - 2) := by
      rw [← Real.rpow_add htpos]
      ring_nf
    have hmono : t ^ (p - 2) ≤ lam ^ (p - 2) :=
      Real.rpow_le_rpow_of_nonpos hlam h.le (by linarith)
    have ht2 : t ^ (2 : ℝ) = t ^ 2 := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hsplit, ht2]
    have := mul_le_mul_of_nonneg_left hmono (sq_nonneg t)
    nlinarith [hlamp.le]

/-! ### The level truncation -/

/-- The level truncation `(u-k)_+ - (u-l)_+ = min((u-k)_+, l-k)`: it vanishes where `u ≤ k`
and equals `l - k` where `u ≥ l`. -/
noncomputable def levTrunc (k l : ℝ) (u : Euc d → ℝ) : Euc d → ℝ :=
  fun x => posTrunc k u x - posTrunc l u x

theorem levTrunc_nonneg {k l : ℝ} (hkl : k ≤ l) (u : Euc d → ℝ) (x : Euc d) :
    0 ≤ levTrunc k l u x := by
  rw [levTrunc, posTrunc, posTrunc, sub_nonneg]
  exact max_le_max (by linarith) le_rfl

theorem levTrunc_eq_zero {k l : ℝ} {u : Euc d → ℝ} {x : Euc d} (hx : u x ≤ k) (hkl : k ≤ l) :
    levTrunc k l u x = 0 := by
  rw [levTrunc, posTrunc, posTrunc, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

theorem levTrunc_eq_sub {k l : ℝ} {u : Euc d → ℝ} {x : Euc d} (hx : l ≤ u x) (hkl : k ≤ l) :
    levTrunc k l u x = l - k := by
  rw [levTrunc, posTrunc, posTrunc, max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

theorem levTrunc_le {k l : ℝ} {u : Euc d → ℝ} (hkl : k ≤ l) (x : Euc d) :
    levTrunc k l u x ≤ l - k := by
  rw [levTrunc, posTrunc, posTrunc]
  rcases le_or_gt (u x) k with h | h
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
  rcases le_or_gt (u x) l with h' | h'
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith

/-- The level truncation lies in `W₀^{1,2}(K)` with weak gradient `1_{k<u≤l} ∇u`. -/
theorem memW0_levTrunc {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) (hu : MemW0 2 K u) :
    MemW0 2 K (levTrunc k l u) ∧
      HasWeakGradient (levTrunc k l u)
        (fun x => (levelInd k u x - levelInd l u x) • weakGrad u x) := by
  obtain ⟨h1m, h1g⟩ := memW0_posTrunc hk hu
  obtain ⟨h2m, h2g⟩ := memW0_posTrunc hl hu
  constructor
  · have hsum := h1m.add (h2m.smul (-1 : ℝ))
    have he : (posTrunc k u + (-1 : ℝ) • posTrunc l u) = levTrunc k l u := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, levTrunc]
      ring
    rwa [he] at hsum
  · have hsum := h1g.add (h2g.smul (-1 : ℝ))
    refine (hsum.congr_left (Eventually.of_forall fun x => ?_)).congr_right
      (Eventually.of_forall fun x => ?_)
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, levTrunc]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply]
      module

/-- At an exponent `p ≤ 2` the level truncation is still in `W₀^{1,p}(K)`, because it and its
weak gradient vanish (a.e.) off the bounded set `K`. -/
theorem memW0_levTrunc_rpow {p : ℝ} (_hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hK : IsGoodConvex K)
    (hcomp : IsRegComp K u) (hum : Measurable u) {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hkl : k ≤ l) :
    MemW0 p K (levTrunc k l u) ∧
      HasWeakGradient (levTrunc k l u)
        (Set.indicator K fun x => (levelInd k u x - levelInd l u x) • weakGrad u x) := by
  classical
  obtain ⟨h2m, h2g⟩ := memW0_levTrunc hk hl hcomp.memW0
  have hKfin : volume K ≠ ⊤ := hK.isBounded.measure_lt_top.ne
  have hsetk : MeasurableSet {x : Euc d | k < u x} := measurableSet_lt measurable_const hum
  have hsetl : MeasurableSet {x : Euc d | l < u x} := measurableSet_lt measurable_const hum
  have hm1 : Measurable fun x => levelInd k u x - levelInd l u x := by
    unfold levelInd
    exact (Measurable.ite hsetk measurable_const measurable_const).sub
      (Measurable.ite hsetl measurable_const measurable_const)
  have hzeroK : ∀ x, x ∉ K → levTrunc k l u x = 0 := fun x hx =>
    levTrunc_eq_zero (by rw [hcomp.eq_zero_of_notMem x hx]; exact hk) hkl
  have hple : ENNReal.ofReal p ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hp2
  -- the gradient vanishes a.e. off `K`
  have hgradK : ∀ᵐ x : Euc d, x ∉ K → weakGrad u x = 0 := by
    filter_upwards [hcomp.weakGrad_eq_zero] with x hx hxK
    exact hx (hcomp.eq_zero_of_notMem x hxK)
  have hindeq : (Set.indicator K fun x => (levelInd k u x - levelInd l u x) • weakGrad u x)
      =ᵐ[volume] fun x => (levelInd k u x - levelInd l u x) • weakGrad u x := by
    filter_upwards [hgradK] with x hx
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
    · rw [Set.indicator_of_notMem hxK, hx hxK, smul_zero]
  have hg : HasWeakGradient (levTrunc k l u)
      (Set.indicator K fun x => (levelInd k u x - levelInd l u x) • weakGrad u x) :=
    h2g.congr_right hindeq.symm
  refine ⟨⟨?_, ?_, ⟨_, hg, ?_⟩⟩, hg⟩
  · -- the function itself
    exact h2m.memLp.mono_exponent_of_measure_support_ne_top (s := K) hzeroK hKfin hple
  · exact Eventually.of_forall hzeroK
  · -- the gradient
    have hbase : MemLp
        (Set.indicator K fun x => (levelInd k u x - levelInd l u x) • weakGrad u x)
        (ENNReal.ofReal 2) volume := by
      refine MemLp.of_le_mul (c := 1) hcomp.memW0.memLp_weakGrad ?_ ?_
      · exact (hm1.aestronglyMeasurable.smul
          hcomp.aestronglyMeasurable_grad).indicator hK.isOpen.measurableSet
      · refine Eventually.of_forall fun x => ?_
        by_cases hxK : x ∈ K
        · rw [Set.indicator_of_mem hxK, norm_smul, Real.norm_eq_abs, one_mul]
          have h1 : |levelInd k u x - levelInd l u x| ≤ 1 := by
            rw [levelInd, levelInd]
            split <;> split <;> simp
          nlinarith [norm_nonneg (weakGrad u x)]
        · rw [Set.indicator_of_notMem hxK, norm_zero, one_mul]
          exact norm_nonneg _
    refine hbase.mono_exponent_of_measure_support_ne_top (s := K) (fun x hx => ?_) hKfin hple
    exact Set.indicator_of_notMem hx _

/-! ### The Poincaré consequence -/

/-- **The two-set form of the double-integral Poincaré inequality.**  If `T ∈ W₀^{1,p}(K)`
satisfies `T ≥ δ` on `E ⊆ B` and `T = 0` on `Z ⊆ B`, then

`|E| |Z| δ^p ≤ 2^d D^p |B| ∫_B ‖∇T‖^p`

for a convex `B` of finite measure and diameter at most `D`.  This is
`Komlos.Literature.MemW0.measure_mul_lintegral_sub_rpow_le` with the left-hand side restricted
to `Z`, where `δ - T = δ`. -/
theorem measure_mul_measure_mul_rpow_le {p : ℝ} (hp : 1 < p) {T : Euc d → ℝ}
    (hT : MemW0 p K T) {B : Set (Euc d)} (hBc : Convex ℝ B) (hBm : MeasurableSet B)
    (hBfin : volume B ≠ ⊤) {D : ℝ} (hBD : ∀ x ∈ B, ∀ y ∈ B, ‖y - x‖ ≤ D)
    {E Z : Set (Euc d)} (hEm : MeasurableSet E) (hZm : MeasurableSet Z)
    (hEB : E ⊆ B) (hZB : Z ⊆ B) {δ : ℝ}
    (hE : ∀ y ∈ E, δ ≤ T y) (hZ : ∀ y ∈ Z, T y = 0) :
    volume E * (volume Z * ENNReal.ofReal δ ^ p) ≤
      2 ^ d * ENNReal.ofReal D ^ p * volume B * ∫⁻ z in B, ‖weakGrad T z‖ₑ ^ p := by
  refine le_trans ?_ (hT.measure_mul_lintegral_sub_rpow_le hp hBc hBm hBfin hBD hEm hEB hE)
  gcongr
  calc volume Z * ENNReal.ofReal δ ^ p = ∫⁻ _ in Z, ENNReal.ofReal δ ^ p := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in Z, ENNReal.ofReal (δ - T x) ^ p := by
        refine setLIntegral_mono' hZm fun x hx => ?_
        rw [hZ x hx, sub_zero]
    _ ≤ ∫⁻ x in B, ENNReal.ofReal (δ - T x) ^ p := lintegral_mono_set hZB

/-! ### One level step of the measure-shrinking iteration -/

/-- **One level step.**  For `0 ≤ k < l` and any measurable `Z ⊆ B = ball x₁ Rb` on which
`u ≤ k`,

`|B ∩ {u>l}| · |Z| · (l-k)^p ≤ 2^d (2R)^p |B| (λ^{p-2} ∫_{B∩{u>k}} ‖∇u‖² + λ^p |ann|)`,

where `ann = (B ∩ {u>k}) ∖ {u>l}` is the annulus between the two levels.  This is
`measure_mul_measure_mul_rpow_le` applied to the level truncation `levTrunc k l u`, combined
with the Young inequality `rpow_young_two` on the gradient integral. -/
theorem measure_level_step {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hK : IsGoodConvex K)
    (hcomp : IsRegComp K u) (hum : Measurable u)
    {x₁ : Euc d} {Rb : ℝ} (hRb : 0 < Rb) {k l : ℝ} (hk : 0 ≤ k) (hkl : k < l)
    {lam : ℝ} (hlam : 0 < lam)
    {Z : Set (Euc d)} (hZm : MeasurableSet Z) (hZB : Z ⊆ Metric.ball x₁ Rb)
    (hZlev : ∀ x ∈ Z, u x ≤ k) :
    (volume (Metric.ball x₁ Rb ∩ {x | l < u x})).toReal * (volume Z).toReal * (l - k) ^ p ≤
      2 ^ d * (2 * Rb) ^ p * (volume (Metric.ball x₁ Rb)).toReal *
        (lam ^ (p - 2) * (∫ x in Metric.ball x₁ Rb ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2) +
          lam ^ p *
            (volume ((Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x})).toReal) := by
  classical
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hδ0 : (0 : ℝ) ≤ l - k := by linarith
  have hkl' : k ≤ l := hkl.le
  have hl0 : (0 : ℝ) ≤ l := le_trans hk hkl'
  have hAkm : MeasurableSet {x : Euc d | k < u x} := measurableSet_lt measurable_const hum
  have hAlm : MeasurableSet {x : Euc d | l < u x} := measurableSet_lt measurable_const hum
  have hBfin : volume (Metric.ball x₁ Rb) ≠ ⊤ := (measure_ball_lt_top (x := x₁) (r := Rb)).ne
  have hEfin : volume (Metric.ball x₁ Rb ∩ {x | l < u x}) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt (measure_ball_lt_top (x := x₁) (r := Rb))).ne
  have hZfin : volume Z ≠ ⊤ :=
    ((measure_mono hZB).trans_lt (measure_ball_lt_top (x := x₁) (r := Rb))).ne
  have hannfin : volume ((Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x}) ≠ ⊤ :=
    ((measure_mono ((Set.sdiff_subset).trans Set.inter_subset_left)).trans_lt
      (measure_ball_lt_top (x := x₁) (r := Rb))).ne
  obtain ⟨hTmem, hTg⟩ := memW0_levTrunc_rpow hp1.le hp2 hK hcomp hum hk hl0 hkl'
  -- the diameter of the ball
  have hdiam : ∀ x ∈ Metric.ball x₁ Rb, ∀ y ∈ Metric.ball x₁ Rb, ‖y - x‖ ≤ 2 * Rb := by
    intro x hx y hy
    rw [Metric.mem_ball, dist_eq_norm] at hx hy
    calc ‖y - x‖ = ‖(y - x₁) - (x - x₁)‖ := by congr 1; abel
      _ ≤ ‖y - x₁‖ + ‖x - x₁‖ := norm_sub_le _ _
      _ ≤ 2 * Rb := by linarith
  -- the Poincaré inequality
  have hpoin := measure_mul_measure_mul_rpow_le (T := levTrunc k l u) hp1 hTmem
    (convex_ball x₁ Rb) measurableSet_ball hBfin hdiam
    (measurableSet_ball.inter hAlm) hZm Set.inter_subset_left hZB
    (fun y hy => le_of_eq (levTrunc_eq_sub hy.2.le hkl').symm)
    (fun y hy => levTrunc_eq_zero (hZlev y hy) hkl')
  -- the pointwise description of the weak gradient of the truncation
  have hGTeq : ∀ x, ‖(Set.indicator K fun y =>
      (levelInd k u y - levelInd l u y) • weakGrad u y) x‖ =
      Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖) x := by
    intro x
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
      simp only [levelInd]
      by_cases hxk : k < u x
      · by_cases hxl : l < u x
        · rw [if_pos hxk, if_pos hxl, Set.indicator_of_notMem (fun hc => hc.2 hxl)]
          simp
        · have hmem : x ∈ {x : Euc d | k < u x} \ {x : Euc d | l < u x} := ⟨hxk, hxl⟩
          rw [if_pos hxk, if_neg hxl, Set.indicator_of_mem hmem]
          simp
      · have hxl : ¬ (l < u x) := fun h => hxk (lt_trans hkl h)
        rw [if_neg hxk, if_neg hxl, Set.indicator_of_notMem (fun hc => hxk hc.1)]
        simp
    · have hxu : u x = 0 := hcomp.eq_zero_of_notMem x hxK
      have hnot : x ∉ {x : Euc d | k < u x} \ {x : Euc d | l < u x} := by
        intro hc
        have : k < u x := hc.1
        rw [hxu] at this
        linarith
      rw [Set.indicator_of_notMem hxK, Set.indicator_of_notMem hnot, norm_zero]
  -- the gradient lintegral, in real form
  have hgradae : (fun z => ‖weakGrad (levTrunc k l u) z‖ₑ ^ p) =ᵐ[volume]
      fun z => ENNReal.ofReal
        (Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖) z ^ p) := by
    filter_upwards [hTg.weakGrad_ae_eq] with z hz
    rw [hz, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0, hGTeq z]
  have hIntp : IntegrableOn (fun z =>
      Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖) z ^ p)
      (Metric.ball x₁ Rb) volume := by
    have hmeas : AEStronglyMeasurable (fun z =>
        Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖) z ^ p)
        volume := by
      refine (Real.continuous_rpow_const hp0).comp_aestronglyMeasurable ?_
      exact (hcomp.aestronglyMeasurable_grad.norm).indicator (hAkm.diff hAlm)
    refine Integrable.mono'
      ((hcomp.integrable_normSq_grad.integrableOn (s := Metric.ball x₁ Rb)).add
        (integrableOn_const (μ := volume) (C := (1 : ℝ)) hBfin)) hmeas.restrict ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun z => ?_)
    have hnn : 0 ≤ Set.indicator ({x | k < u x} \ {x | l < u x})
        (fun y => ‖weakGrad u y‖) z := Set.indicator_nonneg (fun y _ => norm_nonneg _) z
    have hyoung := rpow_young_two hp1.le hp2 (by norm_num : (0:ℝ) < 1) hnn
    have hle : Set.indicator ({x | k < u x} \ {x | l < u x})
        (fun y => ‖weakGrad u y‖) z ^ 2 ≤ ‖weakGrad u z‖ ^ 2 := by
      by_cases hz : z ∈ ({x | k < u x} \ {x | l < u x})
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        simp
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn p)]
    simp only [Real.one_rpow, one_mul] at hyoung
    simp only [Pi.add_apply]
    linarith
  have hlint : (∫⁻ z in Metric.ball x₁ Rb, ‖weakGrad (levTrunc k l u) z‖ₑ ^ p) =
      ENNReal.ofReal (∫ z in Metric.ball x₁ Rb,
        Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖) z ^ p) := by
    rw [lintegral_congr_ae (ae_restrict_of_ae hgradae)]
    exact (ofReal_integral_eq_lintegral_ofReal hIntp
      (ae_restrict_of_ae (Eventually.of_forall fun z =>
        Real.rpow_nonneg (Set.indicator_nonneg (fun y _ => norm_nonneg _) z) p))).symm
  -- the real bound for the gradient integral
  have hannsub : (Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x} ⊆
      Metric.ball x₁ Rb ∩ {x | k < u x} := Set.sdiff_subset
  have hannm : MeasurableSet ((Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x}) :=
    (measurableSet_ball.inter hAkm).diff hAlm
  have hinterdiff : Metric.ball x₁ Rb ∩ ({x | k < u x} \ {x | l < u x}) =
      (Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  have hpow : ∀ z : Euc d,
      Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖) z ^ p =
        Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖ ^ p) z := by
    intro z
    by_cases hz : z ∈ ({x : Euc d | k < u x} \ {x : Euc d | l < u x})
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
        Real.zero_rpow (by linarith)]
  have hIgrad2 : IntegrableOn (fun x => ‖weakGrad u x‖ ^ 2)
      ((Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x}) volume :=
    hcomp.integrable_normSq_grad.integrableOn
  have hIgradp : IntegrableOn (fun x => ‖weakGrad u x‖ ^ p)
      ((Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x}) volume := by
    refine Integrable.mono' (hIgrad2.add (integrableOn_const (μ := volume) (C := (1 : ℝ))
      ((measure_mono (hannsub.trans Set.inter_subset_left)).trans_lt
        (measure_ball_lt_top (x := x₁) (r := Rb))).ne))
      (((Real.continuous_rpow_const hp0).comp_aestronglyMeasurable
        hcomp.aestronglyMeasurable_grad.norm).restrict) ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun z => ?_)
    have hyoung := rpow_young_two hp1.le hp2 (by norm_num : (0:ℝ) < 1) (norm_nonneg (weakGrad u z))
    simp only [Real.one_rpow, one_mul] at hyoung
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
    simp only [Pi.add_apply]
    linarith
  have hrealgrad : (∫ z in Metric.ball x₁ Rb,
      Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖) z ^ p) ≤
      lam ^ (p - 2) * (∫ x in Metric.ball x₁ Rb ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2) +
        lam ^ p *
          (volume ((Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x})).toReal := by
    have he1 : (∫ z in Metric.ball x₁ Rb,
        Set.indicator ({x | k < u x} \ {x | l < u x}) (fun y => ‖weakGrad u y‖) z ^ p) =
        ∫ z in (Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x}, ‖weakGrad u z‖ ^ p := by
      rw [integral_congr_ae (ae_restrict_of_ae (Eventually.of_forall hpow)),
        setIntegral_indicator (hAkm.diff hAlm), hinterdiff]
    rw [he1]
    have hbd : (∫ z in (Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x},
        ‖weakGrad u z‖ ^ p) ≤
        ∫ z in (Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x},
          (lam ^ (p - 2) * ‖weakGrad u z‖ ^ 2 + lam ^ p) := by
      refine integral_mono_ae hIgradp ((hIgrad2.const_mul _).add
        (integrableOn_const (μ := volume) (C := lam ^ p)
          ((measure_mono (hannsub.trans Set.inter_subset_left)).trans_lt
            (measure_ball_lt_top (x := x₁) (r := Rb))).ne)) ?_
      exact ae_restrict_of_ae (Eventually.of_forall fun z =>
        rpow_young_two hp1.le hp2 hlam (norm_nonneg _))
    refine hbd.trans ?_
    rw [integral_add ((hIgrad2.const_mul _)) (integrableOn_const (μ := volume) (C := lam ^ p)
      ((measure_mono (hannsub.trans Set.inter_subset_left)).trans_lt
        (measure_ball_lt_top (x := x₁) (r := Rb))).ne), integral_const_mul, setIntegral_const]
    have hmono : (∫ z in (Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x},
        ‖weakGrad u z‖ ^ 2) ≤ ∫ x in Metric.ball x₁ Rb ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2 := by
      refine setIntegral_mono_set hcomp.integrable_normSq_grad.integrableOn ?_
        (LE.le.eventuallyLE hannsub)
      exact ae_restrict_of_ae (Eventually.of_forall fun z => sq_nonneg _)
    have hlp : (0 : ℝ) ≤ lam ^ (p - 2) := (Real.rpow_pos_of_pos hlam _).le
    have := mul_le_mul_of_nonneg_left hmono hlp
    simp only [smul_eq_mul, measureReal_def]
    linarith
  -- convert the Poincaré inequality to real numbers
  set RG : ℝ := lam ^ (p - 2) * (∫ x in Metric.ball x₁ Rb ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2) +
    lam ^ p * (volume ((Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x})).toReal with hRGdef
  have hRG0 : 0 ≤ RG := by
    rw [hRGdef]
    have h1 : (0 : ℝ) ≤ lam ^ (p - 2) := (Real.rpow_pos_of_pos hlam _).le
    have h2 : (0 : ℝ) ≤ lam ^ p := (Real.rpow_pos_of_pos hlam _).le
    have h3 : (0 : ℝ) ≤ ∫ x in Metric.ball x₁ Rb ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have h4 : (0 : ℝ) ≤ (volume ((Metric.ball x₁ Rb ∩ {x | k < u x}) \ {x | l < u x})).toReal :=
      ENNReal.toReal_nonneg
    positivity
  have hRb2 : (0 : ℝ) ≤ 2 * Rb := by linarith
  have hVnn : (0 : ℝ) ≤ (volume (Metric.ball x₁ Rb)).toReal := ENNReal.toReal_nonneg
  have hLeq : volume (Metric.ball x₁ Rb ∩ {x | l < u x}) *
      (volume Z * ENNReal.ofReal (l - k) ^ p) =
      ENNReal.ofReal ((volume (Metric.ball x₁ Rb ∩ {x | l < u x})).toReal *
        (volume Z).toReal * (l - k) ^ p) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hEfin, ENNReal.ofReal_toReal hZfin,
      ENNReal.ofReal_rpow_of_nonneg hδ0 hp0, mul_assoc]
  have hReq : ENNReal.ofReal (2 ^ d * (2 * Rb) ^ p * (volume (Metric.ball x₁ Rb)).toReal * RG)
      = (2 : ℝ≥0∞) ^ d * ENNReal.ofReal (2 * Rb) ^ p *
        volume (Metric.ball x₁ Rb) * ENNReal.ofReal RG := by
    have e1 : ENNReal.ofReal
          (2 ^ d * (2 * Rb) ^ p * (volume (Metric.ball x₁ Rb)).toReal * RG) =
        ENNReal.ofReal (2 ^ d * (2 * Rb) ^ p * (volume (Metric.ball x₁ Rb)).toReal) *
          ENNReal.ofReal RG :=
      ENNReal.ofReal_mul (by
        have h2 : (0 : ℝ) ≤ (2 * Rb) ^ p := Real.rpow_nonneg hRb2 p
        have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
        exact mul_nonneg (mul_nonneg h1 h2) hVnn)
    have e2 : ENNReal.ofReal (2 ^ d * (2 * Rb) ^ p * (volume (Metric.ball x₁ Rb)).toReal) =
        ENNReal.ofReal (2 ^ d * (2 * Rb) ^ p) *
          ENNReal.ofReal ((volume (Metric.ball x₁ Rb)).toReal) :=
      ENNReal.ofReal_mul (by
        have h2 : (0 : ℝ) ≤ (2 * Rb) ^ p := Real.rpow_nonneg hRb2 p
        have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
        exact mul_nonneg h1 h2)
    have e3 : ENNReal.ofReal ((2 : ℝ) ^ d * (2 * Rb) ^ p) =
        ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal ((2 * Rb) ^ p) :=
      ENNReal.ofReal_mul (by positivity)
    have e4 : ENNReal.ofReal ((2 * Rb) ^ p) = ENNReal.ofReal (2 * Rb) ^ p :=
      (ENNReal.ofReal_rpow_of_nonneg hRb2 hp0).symm
    have e5 : ENNReal.ofReal ((2 : ℝ) ^ d) = (2 : ℝ≥0∞) ^ d := by
      rw [ENNReal.ofReal_pow (by norm_num), dgn_ofReal_two]
    rw [e1, e2, e3, e4, e5, ENNReal.ofReal_toReal hBfin]
  have hchain : ENNReal.ofReal ((volume (Metric.ball x₁ Rb ∩ {x | l < u x})).toReal *
      (volume Z).toReal * (l - k) ^ p) ≤
      ENNReal.ofReal (2 ^ d * (2 * Rb) ^ p * (volume (Metric.ball x₁ Rb)).toReal * RG) := by
    rw [← hLeq, hReq]
    refine hpoin.trans ?_
    rw [hlint]
    gcongr
  have hfin : (0 : ℝ) ≤ 2 ^ d * (2 * Rb) ^ p * (volume (Metric.ball x₁ Rb)).toReal * RG := by
    have h2 : (0 : ℝ) ≤ (2 * Rb) ^ p := Real.rpow_nonneg hRb2 p
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hVnn) hRG0
  exact (ENNReal.ofReal_le_ofReal_iff hfin).1 hchain


/-! ### The supporting half-space at a convex boundary point -/

/-- **Supporting functional at a convex boundary point** (geometric Hahn–Banach): for an open
convex `K` and `x₀ ∈ frontier K` there is a continuous linear functional `ℓ` with `ℓ x < ℓ x₀`
for every `x ∈ K`; the open half-space `{ℓ < ℓ x₀}` contains `K` and has `x₀` on its boundary. -/
theorem exists_supporting_functional (hK : IsGoodConvex K) {x₀ : Euc d}
    (hx₀ : x₀ ∈ frontier K) : ∃ ℓ : Euc d →L[ℝ] ℝ, ∀ x ∈ K, ℓ x < ℓ x₀ := by
  have hx₀K : x₀ ∉ K := by
    rw [hK.isOpen.frontier_eq] at hx₀
    exact hx₀.2
  exact geometric_hahn_banach_open_point hK.convex hK.isOpen hx₀K

/-- **Half-density of the complement at a convex boundary point**: if `K` lies in the open
half-space `{ℓ < ℓ x₀}`, then `K` occupies at most half of every ball centred at `x₀`.

The point reflection `σ(x) = (x₀ + x₀) - x` preserves Lebesgue measure
(`Measure.measurePreserving_sub_left`) and every ball centred at `x₀`, and maps
`{ℓ < ℓ x₀}` onto `{ℓ > ℓ x₀}`; the two traces on the ball are therefore equimeasurable and
disjoint. -/
theorem measure_inter_le_half_of_supporting {x₀ : Euc d} (ℓ : Euc d →L[ℝ] ℝ)
    (hℓ : ∀ x ∈ K, ℓ x < ℓ x₀) (r : ℝ) :
    2 * volume (Metric.ball x₀ r ∩ K) ≤ volume (Metric.ball x₀ r) := by
  classical
  set H : Set (Euc d) := {x | ℓ x < ℓ x₀} with hHdef
  set H' : Set (Euc d) := {x | ℓ x₀ < ℓ x} with hH'def
  set σ : Euc d → Euc d := fun t => (x₀ + x₀) - t with hσdef
  have hdist : ∀ x : Euc d, dist (σ x) x₀ = dist x x₀ := by
    intro x
    rw [hσdef, dist_eq_norm, dist_eq_norm, show x₀ + x₀ - x - x₀ = -(x - x₀) by abel, norm_neg]
  have hell : ∀ x : Euc d, ℓ (σ x) = ℓ x₀ + ℓ x₀ - ℓ x := by
    intro x
    rw [hσdef]
    simp [map_sub, map_add]
  have hmp : MeasurePreserving σ volume volume :=
    Measure.measurePreserving_sub_left volume (x₀ + x₀)
  have hHopen : IsOpen H := isOpen_lt (by fun_prop) continuous_const
  have hH'open : IsOpen H' := isOpen_lt continuous_const (by fun_prop)
  have hpre : σ ⁻¹' (Metric.ball x₀ r ∩ H') = Metric.ball x₀ r ∩ H := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, hHdef, hH'def,
      Set.mem_ofPred_eq, hdist, hell]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  have hmeq : volume (Metric.ball x₀ r ∩ H) = volume (Metric.ball x₀ r ∩ H') := by
    rw [← hpre]
    exact hmp.measure_preimage
      (measurableSet_ball.inter hH'open.measurableSet).nullMeasurableSet
  have hdisj : Disjoint (Metric.ball x₀ r ∩ H) (Metric.ball x₀ r ∩ H') := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ ⟨-, hx'⟩
    simp only [hHdef, hH'def, Set.mem_ofPred_eq] at hx hx'
    linarith
  have hunion : volume (Metric.ball x₀ r ∩ H) + volume (Metric.ball x₀ r ∩ H') ≤
      volume (Metric.ball x₀ r) := by
    rw [← measure_union hdisj (measurableSet_ball.inter hH'open.measurableSet)]
    exact measure_mono (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
  have hsub : Metric.ball x₀ r ∩ K ⊆ Metric.ball x₀ r ∩ H :=
    Set.inter_subset_inter_right _ fun x hx => hℓ x hx
  calc 2 * volume (Metric.ball x₀ r ∩ K)
      ≤ 2 * volume (Metric.ball x₀ r ∩ H) := by gcongr
    _ = volume (Metric.ball x₀ r ∩ H) + volume (Metric.ball x₀ r ∩ H') := by
        rw [← hmeq, two_mul]
    _ ≤ volume (Metric.ball x₀ r) := hunion

/-! ### Volumes of concentric balls -/

/-- Doubling the radius multiplies the volume of a ball by `2^d`. -/
theorem volume_ball_two_mul (hd : 0 < d) (x : Euc d) {r : ℝ} (_hr : 0 ≤ r) :
    volume (Metric.ball x (2 * r)) = ENNReal.ofReal (2 ^ d) * volume (Metric.ball x r) := by
  have : Nontrivial (Euc d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  rw [Measure.addHaar_ball_mul volume x (by norm_num : (0:ℝ) ≤ 2) r,
    ← Measure.addHaar_ball_center volume x r, finrank_euclideanSpace_fin]

/-! ### Summing the annuli -/

/-- The level annuli `(B ∩ {u > k_j}) ∖ {u > k_{j+1}}` are pairwise disjoint subsets of `B`,
so their measures sum to at most `|B|`. -/
theorem sum_measure_annuli_le {B : Set (Euc d)} (hBm : MeasurableSet B) (hum : Measurable u)
    (hBfin : volume B ≠ ⊤) (kk : ℕ → ℝ) (hmono : Monotone kk) (J : ℕ) :
    ∑ j ∈ Finset.range J,
        (volume ((B ∩ {x | kk j < u x}) \ {x | kk (j + 1) < u x})).toReal ≤
      (volume B).toReal := by
  classical
  set ann : ℕ → Set (Euc d) := fun j => (B ∩ {x | kk j < u x}) \ {x | kk (j + 1) < u x}
    with hanndef
  have hannm : ∀ j, MeasurableSet (ann j) := fun j =>
    (hBm.inter (measurableSet_lt measurable_const hum)).diff
      (measurableSet_lt measurable_const hum)
  have hannsub : ∀ j, ann j ⊆ B := fun j x hx => hx.1.1
  have hdisj : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint ann := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · refine Set.disjoint_left.2 fun x hxi hxj => ?_
      have h1 : ¬ (kk (i + 1) < u x) := hxi.2
      have h2 : kk j < u x := hxj.1.2
      have h3 : kk (i + 1) ≤ kk j := hmono h
      exact h1 (lt_of_le_of_lt h3 h2)
    · refine Set.disjoint_left.2 fun x hxi hxj => ?_
      have h1 : ¬ (kk (j + 1) < u x) := hxj.2
      have h2 : kk i < u x := hxi.1.2
      have h3 : kk (j + 1) ≤ kk i := hmono h
      exact h1 (lt_of_le_of_lt h3 h2)
  have hsum : ∑ j ∈ Finset.range J, volume (ann j) = volume (⋃ j ∈ Finset.range J, ann j) :=
    (measure_biUnion_finset hdisj fun j _ => hannm j).symm
  have hle : volume (⋃ j ∈ Finset.range J, ann j) ≤ volume B :=
    measure_mono (Set.iUnion₂_subset fun j _ => hannsub j)
  have hfin : ∀ j, volume (ann j) ≠ ⊤ := fun j =>
    ((measure_mono (hannsub j)).trans_lt hBfin.lt_top).ne
  rw [← ENNReal.toReal_sum (fun j _ => hfin j), hsum]
  exact ENNReal.toReal_mono hBfin hle


/-! ### The boundary density -/

/-- At a boundary point of the convex set `K` the minimizer is `≤ k` on at least half of every
ball, for every level `k ≥ 0`: the set `{u > k}` is contained in `{u > 0} ⊆ K`, which occupies
at most half of the ball (`measure_inter_le_half_of_supporting`). -/
theorem half_measure_below (hcomp : IsRegComp K u) (hum : Measurable u) {x₀ : Euc d}
    {ℓ : Euc d →L[ℝ] ℝ} (hℓ : ∀ x ∈ K, ℓ x < ℓ x₀) (Rb : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    (volume (Metric.ball x₀ Rb)).toReal / 2 ≤
      (volume (Metric.ball x₀ Rb ∩ {x | u x ≤ k})).toReal := by
  classical
  have hAm : MeasurableSet {x : Euc d | k < u x} := measurableSet_lt measurable_const hum
  have hBfin : volume (Metric.ball x₀ Rb) ≠ ⊤ := (measure_ball_lt_top (x := x₀) (r := Rb)).ne
  have hsubK : Metric.ball x₀ Rb ∩ {x : Euc d | k < u x} ⊆ Metric.ball x₀ Rb ∩ K := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hc
    have h1 : k < u x := hx.2
    rw [hcomp.eq_zero_of_notMem x hc] at h1
    linarith
  have hhalf : 2 * volume (Metric.ball x₀ Rb ∩ {x : Euc d | k < u x}) ≤
      volume (Metric.ball x₀ Rb) :=
    le_trans (by gcongr) (measure_inter_le_half_of_supporting ℓ hℓ Rb)
  have hsplit : volume (Metric.ball x₀ Rb ∩ {x : Euc d | u x ≤ k}) +
      volume (Metric.ball x₀ Rb ∩ {x : Euc d | k < u x}) = volume (Metric.ball x₀ Rb) := by
    rw [← measure_union (Set.disjoint_left.2 fun x hx hx' =>
      absurd (hx'.2 : k < u x) (not_lt.2 (hx.2 : u x ≤ k))) (measurableSet_ball.inter hAm)]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases le_or_gt (u x) k with hc | hc
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, hc⟩
  have hfin1 : volume (Metric.ball x₀ Rb ∩ {x : Euc d | u x ≤ k}) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt hBfin.lt_top).ne
  have hfin2 : volume (Metric.ball x₀ Rb ∩ {x : Euc d | k < u x}) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt hBfin.lt_top).ne
  have hsplitR : (volume (Metric.ball x₀ Rb ∩ {x : Euc d | u x ≤ k})).toReal +
      (volume (Metric.ball x₀ Rb ∩ {x : Euc d | k < u x})).toReal =
      (volume (Metric.ball x₀ Rb)).toReal := by
    rw [← ENNReal.toReal_add hfin1 hfin2, hsplit]
  have hhalfR : 2 * (volume (Metric.ball x₀ Rb ∩ {x : Euc d | k < u x})).toReal ≤
      (volume (Metric.ball x₀ Rb)).toReal := by
    have := ENNReal.toReal_mono hBfin hhalf
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
  linarith

/-! ### One level step, in scaled form -/

/-- The level step with the free parameter `λ = (t/R)(l-k)`, after dividing by
`|B| (l-k)^p / 2` and using the boundary density `|B ∩ {u ≤ k}| ≥ |B|/2`.  The hypothesis
`hQ` is the Caccioppoli bound `E_k ≤ Q (l-k)²`. -/
theorem measure_level_step_scaled {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hK : IsGoodConvex K)
    (hcomp : IsRegComp K u) (hum : Measurable u) {x₀ : Euc d}
    {ℓ : Euc d →L[ℝ] ℝ} (hℓ : ∀ x ∈ K, ℓ x < ℓ x₀)
    {Rb : ℝ} (hRb : 0 < Rb) {k l : ℝ} (hk : 0 ≤ k) (hkl : k < l) {t Q : ℝ} (ht : 0 < t)
    (_hQ0 : 0 ≤ Q)
    (hQ : (∫ x in Metric.ball x₀ Rb ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2) ≤ Q * (l - k) ^ 2) :
    (volume (Metric.ball x₀ Rb ∩ {x | l < u x})).toReal ≤
      2 ^ (d + 1) * 2 ^ p * (t ^ (p - 2) * (Rb ^ 2 * Q) + t ^ p *
        (volume ((Metric.ball x₀ Rb ∩ {x | k < u x}) \ {x | l < u x})).toReal) := by
  classical
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hδ : (0 : ℝ) < l - k := by linarith
  have hV : (0 : ℝ) < (volume (Metric.ball x₀ Rb)).toReal := by
    refine ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hRb).ne' ?_
    exact (measure_ball_lt_top (x := x₀) (r := Rb)).ne
  set V : ℝ := (volume (Metric.ball x₀ Rb)).toReal with hVdef
  set m : ℝ := (volume ((Metric.ball x₀ Rb ∩ {x | k < u x}) \ {x | l < u x})).toReal with hmdef
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set lam : ℝ := (t / Rb) * (l - k) with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hZm : MeasurableSet (Metric.ball x₀ Rb ∩ {x : Euc d | u x ≤ k}) :=
    measurableSet_ball.inter (measurableSet_le hum measurable_const)
  have hstep := measure_level_step hp1 hp2 hK hcomp hum hRb hk hkl hlam hZm
    Set.inter_subset_left (fun x hx => hx.2)
  have hz := half_measure_below hcomp hum hℓ Rb hk
  set a : ℝ := (volume (Metric.ball x₀ Rb ∩ {x | l < u x})).toReal with hadef
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  set z : ℝ := (volume (Metric.ball x₀ Rb ∩ {x : Euc d | u x ≤ k})).toReal with hzdef
  set E : ℝ := ∫ x in Metric.ball x₀ Rb ∩ {x | k < u x}, ‖weakGrad u x‖ ^ 2 with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; exact integral_nonneg fun x => sq_nonneg _
  -- rewrite the powers of `lam`
  have hlam1 : lam ^ (p - 2) = (t / Rb) ^ (p - 2) * (l - k) ^ (p - 2) := by
    rw [hlamdef, Real.mul_rpow (by positivity) (by positivity)]
  have hlam2 : lam ^ p = (t / Rb) ^ p * (l - k) ^ p := by
    rw [hlamdef, Real.mul_rpow (by positivity) (by positivity)]
  have hδsq : (l - k) ^ (p - 2) * ((l - k) ^ 2 : ℝ) = (l - k) ^ p := by
    rw [show ((l - k) ^ 2 : ℝ) = (l - k) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_add hδ]
    norm_num
  -- the right-hand side of the level step
  have hRHS : lam ^ (p - 2) * E + lam ^ p * m ≤
      (l - k) ^ p * ((t / Rb) ^ (p - 2) * Q + (t / Rb) ^ p * m) := by
    have h1 : lam ^ (p - 2) * E ≤ (l - k) ^ p * ((t / Rb) ^ (p - 2) * Q) := by
      rw [hlam1, mul_assoc]
      have hq : (l - k) ^ (p - 2) * E ≤ (l - k) ^ (p - 2) * (Q * (l - k) ^ 2) :=
        mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg hδ.le _)
      have he : (l - k) ^ (p - 2) * (Q * (l - k) ^ 2) = (l - k) ^ p * Q := by
        rw [← hδsq]; ring
      rw [he] at hq
      calc (t / Rb) ^ (p - 2) * ((l - k) ^ (p - 2) * E)
          ≤ (t / Rb) ^ (p - 2) * ((l - k) ^ p * Q) :=
            mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg (by positivity) _)
        _ = (l - k) ^ p * ((t / Rb) ^ (p - 2) * Q) := by ring
    have h2 : lam ^ p * m = (l - k) ^ p * ((t / Rb) ^ p * m) := by rw [hlam2]; ring
    rw [h2]
    have := h1
    linarith
  -- divide out
  have hkey : a * (V / 2) * (l - k) ^ p ≤
      2 ^ d * (2 * Rb) ^ p * V * ((l - k) ^ p * ((t / Rb) ^ (p - 2) * Q + (t / Rb) ^ p * m)) := by
    refine le_trans ?_ (le_trans hstep ?_)
    · have : a * (V / 2) ≤ a * z := mul_le_mul_of_nonneg_left hz ha0
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hδ.le _)
    · exact mul_le_mul_of_nonneg_left hRHS (by positivity)
  have hδp : (0 : ℝ) < (l - k) ^ p := Real.rpow_pos_of_pos hδ _
  have hdiv : a * (V / 2) ≤ 2 ^ d * (2 * Rb) ^ p * V *
      ((t / Rb) ^ (p - 2) * Q + (t / Rb) ^ p * m) := by
    have he : 2 ^ d * (2 * Rb) ^ p * V *
        ((l - k) ^ p * ((t / Rb) ^ (p - 2) * Q + (t / Rb) ^ p * m)) =
        (2 ^ d * (2 * Rb) ^ p * V * ((t / Rb) ^ (p - 2) * Q + (t / Rb) ^ p * m)) *
          (l - k) ^ p := by ring
    rw [he] at hkey
    exact le_of_mul_le_mul_right hkey hδp
  -- simplify the powers of `Rb`
  have hRbp : (2 * Rb) ^ p = (2 : ℝ) ^ p * Rb ^ p :=
    Real.mul_rpow (by norm_num) hRb.le
  have htRb1 : (t / Rb) ^ (p - 2) = t ^ (p - 2) * Rb ^ (2 - p) := by
    rw [Real.div_rpow ht.le hRb.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg hRb.le]
    ring_nf
  have htRb2 : (t / Rb) ^ p = t ^ p * (Rb ^ p)⁻¹ := by
    rw [Real.div_rpow ht.le hRb.le, div_eq_mul_inv]
  have hRbcancel : Rb ^ p * Rb ^ (2 - p) = Rb ^ 2 := by
    rw [← Real.rpow_add hRb]
    norm_num
  have hfinal : 2 ^ d * (2 * Rb) ^ p * V * ((t / Rb) ^ (p - 2) * Q + (t / Rb) ^ p * m) =
      (V / 2) * (2 ^ (d + 1) * 2 ^ p * (t ^ (p - 2) * (Rb ^ 2 * Q) + t ^ p * m)) := by
    have hRbne : (Rb ^ p : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hRb p).ne'
    rw [hRbp, htRb1, htRb2]
    have expand : 2 ^ d * (2 ^ p * Rb ^ p) * V *
        (t ^ (p - 2) * Rb ^ (2 - p) * Q + t ^ p * (Rb ^ p)⁻¹ * m) =
        2 ^ d * 2 ^ p * V * t ^ (p - 2) * (Rb ^ p * Rb ^ (2 - p)) * Q +
        2 ^ d * 2 ^ p * V * t ^ p * m * (Rb ^ p * (Rb ^ p)⁻¹) := by ring
    rw [expand, hRbcancel, mul_inv_cancel₀ hRbne]
    ring
  rw [hfinal] at hdiv
  have hVhalf : (0 : ℝ) < V / 2 := by linarith
  rw [mul_comm ((V : ℝ) / 2)] at hdiv
  exact le_of_mul_le_mul_right hdiv hVhalf


variable {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ}

/-! ### The measure-shrinking lemma -/

set_option maxHeartbeats 1000000 in
/-- **De Giorgi's measure-shrinking lemma at a convex boundary point.**

Given `ν > 0` there is a number `J` of levels, depending only on `d`, on the structural
constants of the problem and on `ν`, such that for every radius `R` and every essential bound
`H` for the minimizer on `B_{2R}(x₀)` with `2^{J+1} R ≤ H`,

`|B_R(x₀) ∩ {u > H(1 - 2^{-J-1})}| ≤ ν |B_R(x₀)|`.

The proof runs the level scheme described in the module docstring at the exponent `p = 3/2`:
the scaled level step `measure_level_step_scaled` with the free parameter `t`, the uniform
Caccioppoli bound `E_j ≤ Q δ_j²` coming from `exists_energy_ineq` (this is where
`2^{J+1} R ≤ H` is used: it makes the lower-order term `γ|B_{2R}|` of the Caccioppoli
inequality dominated by its leading term), and the disjointness of the annuli. -/
theorem exists_measure_shrink (hd : 0 < d) (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) (hcomp : IsRegComp K u)
    (hum : Measurable u) {x₀ : Euc d} (hx₀ : x₀ ∈ frontier K) {ν : ℝ} (hν : 0 < ν) :
    ∃ J : ℕ, 0 < J ∧ ∀ (Rb H : ℝ), 0 < Rb → 0 < H → (2 : ℝ) ^ (J + 1) * Rb ≤ H →
      (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (2 * Rb))), u x ≤ H) →
      (volume (Metric.ball x₀ Rb ∩ {x | H * (1 - (1 / 2 : ℝ) ^ (J + 1)) < u x})).toReal ≤
        ν * (volume (Metric.ball x₀ Rb)).toReal := by
  classical
  obtain ⟨γ, hγ0, hen⟩ := exists_energy_ineq hκ hΨ hK hu hcomp hum
  obtain ⟨ℓ, hℓ⟩ := exists_supporting_functional hK hx₀
  set p : ℝ := 3 / 2 with hpdef
  have hp1 : (1 : ℝ) < p := by rw [hpdef]; norm_num
  have hp2 : p ≤ 2 := by rw [hpdef]; norm_num
  have hp2' : (0 : ℝ) < 2 - p := by rw [hpdef]; norm_num
  set Cbig : ℝ := 2 ^ (d + 1) * 2 ^ p with hCbigdef
  have hCbig0 : 0 < Cbig := by
    rw [hCbigdef]
    have : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set Cg : ℝ := Cbig * (8 * γ * 2 ^ d) + 1 with hCgdef
  have hCg0 : 0 < Cg := by
    rw [hCgdef]
    have : (0 : ℝ) ≤ Cbig * (8 * γ * 2 ^ d) := by positivity
    linarith
  -- the free parameter `t`
  set t : ℝ := (2 * Cg / ν) ^ (1 / (2 - p)) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have htp : t ^ (p - 2) = ν / (2 * Cg) := by
    have h1 : t ^ (2 - p) = 2 * Cg / ν := by
      rw [htdef, ← Real.rpow_mul (by positivity)]
      rw [one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    have h2 : p - 2 = -(2 - p) := by ring
    rw [h2, Real.rpow_neg ht0.le, h1]
    rw [inv_div]
  -- the number of levels
  obtain ⟨J, hJ0, hJ⟩ : ∃ J : ℕ, 0 < J ∧ Cbig * t ^ p / (J : ℝ) ≤ ν / 2 := by
    have htp0 : (0 : ℝ) < t ^ p := Real.rpow_pos_of_pos ht0 _
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * Cbig * t ^ p / ν)
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, div_le_iff₀ hn1, div_lt_iff₀ hν] at *
    nlinarith [hν, hn, Nat.cast_nonneg (α := ℝ) n]
  refine ⟨J, hJ0, ?_⟩
  intro Rb H hRb hH hRH hbound
  -- notation
  set V : ℝ := (volume (Metric.ball x₀ Rb)).toReal with hVdef
  have hV0 : 0 < V := by
    rw [hVdef]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hRb).ne'
      (measure_ball_lt_top (x := x₀) (r := Rb)).ne
  have hV2 : (volume (Metric.ball x₀ (2 * Rb))).toReal = 2 ^ d * V := by
    rw [volume_ball_two_mul hd x₀ hRb.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hVdef]
  set kk : ℕ → ℝ := fun j => H * (1 - (1 / 2 : ℝ) ^ (j + 1)) with hkkdef
  have hhalf : ∀ j : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := fun j => by positivity
  have hhalf1 : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := fun j =>
    pow_le_one₀ (by norm_num) (by norm_num)
  have hkk0 : ∀ j, 0 ≤ kk j := fun j => by
    rw [hkkdef]
    have := hhalf1 j
    nlinarith [hH]
  have hkkmono : Monotone kk := by
    intro i j hij
    rw [hkkdef]
    simp only []
    have : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ (i + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    nlinarith [hH]
  have hkkgap : ∀ j : ℕ, kk (j + 1) - kk j = H * (1 / 2 : ℝ) ^ (j + 2) := fun j => by
    have h : (1 / 2 : ℝ) ^ (j + 2) = (1 / 2 : ℝ) ^ (j + 1) * (1 / 2) := pow_succ _ _
    simp only [hkkdef]
    rw [h]
    ring
  have hkklt : ∀ j : ℕ, kk j < kk (j + 1) := fun j => by
    have h := hkkgap j
    have : (0 : ℝ) < H * (1 / 2 : ℝ) ^ (j + 2) := by positivity
    linarith
  have hHkk : ∀ j : ℕ, H - kk j = H * (1 / 2 : ℝ) ^ (j + 1) := fun j => by
    rw [hkkdef]; ring
  -- the uniform Caccioppoli bound
  set Q : ℝ := 8 * γ * 2 ^ d * V / Rb ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
  have hRbQ : Rb ^ 2 * Q = 8 * γ * 2 ^ d * V := by
    rw [hQdef]
    field_simp
  have hEbound : ∀ j : ℕ, j < J →
      (∫ x in Metric.ball x₀ Rb ∩ {x | kk j < u x}, ‖weakGrad u x‖ ^ 2) ≤
        Q * (kk (j + 1) - kk j) ^ 2 := by
    intro j hjJ
    have hen' := hen x₀ Rb (2 * Rb) (kk j) hRb (by linarith) (hkk0 j)
    -- the truncation is bounded by `H - kk j` on the double ball
    have hItrunc : (∫ x in Metric.ball x₀ (2 * Rb), posTrunc (kk j) u x ^ 2) ≤
        (H - kk j) ^ 2 * (2 ^ d * V) := by
      have hint1 : IntegrableOn (fun x => posTrunc (kk j) u x ^ 2)
          (Metric.ball x₀ (2 * Rb)) volume :=
        (hcomp.integrable_posTrunc_sq (hkk0 j)).integrableOn
      have hint2 : IntegrableOn (fun _ : Euc d => (H - kk j) ^ 2)
          (Metric.ball x₀ (2 * Rb)) volume :=
        integrableOn_const (measure_ball_lt_top (x := x₀) (r := 2 * Rb)).ne
      have hmono := integral_mono_ae hint1 hint2 ?_
      · rw [setIntegral_const] at hmono
        simp only [smul_eq_mul, measureReal_def] at hmono
        rw [hV2] at hmono
        linarith
      · filter_upwards [hbound] with x hx
        have h0 : 0 ≤ posTrunc (kk j) u x := posTrunc_nonneg _ _ _
        have hHk : (0:ℝ) ≤ H - kk j := by rw [hHkk j]; positivity
        have h1 : posTrunc (kk j) u x ≤ H - kk j := by
          rw [posTrunc]
          exact max_le (by linarith) hHk
        nlinarith
    have hmeas : (volume (Metric.ball x₀ (2 * Rb) ∩ {x | kk j < u x})).toReal ≤ 2 ^ d * V := by
      rw [← hV2]
      refine ENNReal.toReal_mono (measure_ball_lt_top (x := x₀) (r := 2 * Rb)).ne ?_
      exact measure_mono Set.inter_subset_left
    -- the level gap dominates the radius
    have hgap : 2 * Rb ≤ H - kk j := by
      rw [hHkk j]
      have h1 : (2 : ℝ) ^ (J + 1) * Rb ≤ H := hRH
      have h2 : (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ (j + 1) = 2 ^ (J - j) := by
        rw [div_pow, one_pow]
        rw [eq_div_iff (by positivity)] at *
        field_simp
        rw [← pow_add]
        congr 1
        omega
      have h3 : (2 : ℝ) ≤ 2 ^ (J - j) := by
        have : 1 ≤ J - j := by omega
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (J - j) := pow_le_pow_right₀ (by norm_num) this
      have h4 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := hhalf j
      nlinarith [h1, h2, h3, h4]
    have hsq : (H - kk j) ^ 2 = 4 * (kk (j + 1) - kk j) ^ 2 := by
      rw [hHkk j, hkkgap j, pow_succ]
      ring
    have hRbsq : Rb ^ 2 ≤ (H - kk j) ^ 2 / 4 := by nlinarith [hRb, hgap]
    have hRb2 : (0 : ℝ) < Rb ^ 2 := by positivity
    have hstep : (∫ x in Metric.ball x₀ Rb ∩ {x | kk j < u x}, ‖weakGrad u x‖ ^ 2) ≤
        γ / Rb ^ 2 * ((H - kk j) ^ 2 * (2 ^ d * V)) + γ * (2 ^ d * V) := by
      have hsr : (2 * Rb - Rb) = Rb := by ring
      rw [hsr] at hen'
      have hq1 : γ / Rb ^ 2 * (∫ x in Metric.ball x₀ (2 * Rb), posTrunc (kk j) u x ^ 2) ≤
          γ / Rb ^ 2 * ((H - kk j) ^ 2 * (2 ^ d * V)) :=
        mul_le_mul_of_nonneg_left hItrunc (by positivity)
      have hq2 : γ * (volume (Metric.ball x₀ (2 * Rb) ∩ {x | kk j < u x})).toReal ≤
          γ * (2 ^ d * V) := mul_le_mul_of_nonneg_left hmeas hγ0
      linarith
    have hW0 : (0 : ℝ) ≤ 2 ^ d * V := by positivity
    have hlow : γ * (2 ^ d * V) ≤ γ / Rb ^ 2 * ((H - kk j) ^ 2 * (2 ^ d * V)) / 4 := by
      rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity : (0:ℝ) < Rb ^ 2 * 4)]
      have h4 : 4 * Rb ^ 2 ≤ (H - kk j) ^ 2 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hγ0 hW0)]
    have hS0 : (0 : ℝ) ≤ γ / Rb ^ 2 * ((H - kk j) ^ 2 * (2 ^ d * V)) := by positivity
    have hQe : Q * (kk (j + 1) - kk j) ^ 2 =
        2 * (γ / Rb ^ 2 * ((H - kk j) ^ 2 * (2 ^ d * V))) := by
      have hd2 : (kk (j + 1) - kk j) ^ 2 = (H - kk j) ^ 2 / 4 := by rw [hsq]; ring
      rw [hQdef, hd2]
      field_simp
      ring
    rw [hQe]
    linarith
  -- the per-level bound
  have hlevel : ∀ j : ℕ, j < J →
      (volume (Metric.ball x₀ Rb ∩ {x | kk (j + 1) < u x})).toReal ≤
        Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V) + t ^ p *
          (volume ((Metric.ball x₀ Rb ∩ {x | kk j < u x}) \
            {x | kk (j + 1) < u x})).toReal) := by
    intro j hjJ
    have h := measure_level_step_scaled hp1 hp2 hK hcomp hum hℓ hRb (hkk0 j) (hkklt j)
      ht0 hQ0 (hEbound j hjJ)
    rw [hRbQ] at h
    rw [hCbigdef]
    exact h
  -- sum over the levels
  have hJR : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ0
  have hballfin : volume (Metric.ball x₀ Rb) ≠ ⊤ := (measure_ball_lt_top (x := x₀) (r := Rb)).ne
  have hmonoJ : ∀ j : ℕ, j < J →
      (volume (Metric.ball x₀ Rb ∩ {x | kk J < u x})).toReal ≤
        (volume (Metric.ball x₀ Rb ∩ {x | kk (j + 1) < u x})).toReal := by
    intro j hj
    refine ENNReal.toReal_mono
      ((measure_mono Set.inter_subset_left).trans_lt hballfin.lt_top).ne
      (measure_mono (Set.inter_subset_inter_right _ fun x hx => ?_))
    exact lt_of_le_of_lt (hkkmono (by omega : j + 1 ≤ J)) hx
  have hsum1 : (J : ℝ) * (volume (Metric.ball x₀ Rb ∩ {x | kk J < u x})).toReal ≤
      ∑ j ∈ Finset.range J,
        (volume (Metric.ball x₀ Rb ∩ {x | kk (j + 1) < u x})).toReal := by
    have hle : ∑ _j ∈ Finset.range J,
        (volume (Metric.ball x₀ Rb ∩ {x | kk J < u x})).toReal ≤
        ∑ j ∈ Finset.range J,
          (volume (Metric.ball x₀ Rb ∩ {x | kk (j + 1) < u x})).toReal :=
      Finset.sum_le_sum fun j hj => hmonoJ j (Finset.mem_range.1 hj)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hle
  have hsum2 : ∑ j ∈ Finset.range J,
        (volume (Metric.ball x₀ Rb ∩ {x | kk (j + 1) < u x})).toReal ≤
      ∑ j ∈ Finset.range J, (Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V)) +
        (Cbig * t ^ p) * (volume ((Metric.ball x₀ Rb ∩ {x | kk j < u x}) \
          {x | kk (j + 1) < u x})).toReal) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have h := hlevel j (Finset.mem_range.1 hj)
    have he : Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V) + t ^ p *
        (volume ((Metric.ball x₀ Rb ∩ {x | kk j < u x}) \
          {x | kk (j + 1) < u x})).toReal) =
        Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V)) + (Cbig * t ^ p) *
          (volume ((Metric.ball x₀ Rb ∩ {x | kk j < u x}) \
            {x | kk (j + 1) < u x})).toReal := by ring
    rw [he] at h
    exact h
  have hsum3 : ∑ j ∈ Finset.range J, (Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V)) +
      (Cbig * t ^ p) * (volume ((Metric.ball x₀ Rb ∩ {x | kk j < u x}) \
        {x | kk (j + 1) < u x})).toReal) =
      (J : ℝ) * (Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V))) +
        (Cbig * t ^ p) * ∑ j ∈ Finset.range J,
          (volume ((Metric.ball x₀ Rb ∩ {x | kk j < u x}) \
            {x | kk (j + 1) < u x})).toReal := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
  have hmsum : ∑ j ∈ Finset.range J,
      (volume ((Metric.ball x₀ Rb ∩ {x | kk j < u x}) \
        {x | kk (j + 1) < u x})).toReal ≤ V :=
    sum_measure_annuli_le measurableSet_ball hum hballfin kk hkkmono J
  have hCt0 : (0 : ℝ) ≤ Cbig * t ^ p :=
    mul_nonneg hCbig0.le (Real.rpow_nonneg ht0.le _)
  have hbig : (J : ℝ) * (volume (Metric.ball x₀ Rb ∩ {x | kk J < u x})).toReal ≤
      (J : ℝ) * (Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V))) + (Cbig * t ^ p) * V := by
    have h1 := hsum1.trans hsum2
    rw [hsum3] at h1
    have h2 := mul_le_mul_of_nonneg_left hmsum hCt0
    linarith
  -- the two terms are each at most `(ν/2) V`
  have hterm1 : Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V)) ≤ ν / 2 * V := by
    have hVe : Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V)) =
        (Cbig * (8 * γ * 2 ^ d)) * t ^ (p - 2) * V := by ring
    rw [hVe, htp]
    have hle : Cbig * (8 * γ * 2 ^ d) ≤ Cg := by rw [hCgdef]; linarith
    have hnu : (0 : ℝ) < ν / (2 * Cg) := by positivity
    have h1 : (Cbig * (8 * γ * 2 ^ d)) * (ν / (2 * Cg)) ≤ Cg * (ν / (2 * Cg)) :=
      mul_le_mul_of_nonneg_right hle hnu.le
    have h2 : Cg * (ν / (2 * Cg)) = ν / 2 := by field_simp; try ring
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_right h1 hV0.le
    linarith
  have hterm2 : (Cbig * t ^ p) * V ≤ (J : ℝ) * (ν / 2 * V) := by
    have hJ' : Cbig * t ^ p ≤ ν / 2 * (J : ℝ) := by
      rw [div_le_iff₀ hJR] at hJ
      linarith
    have := mul_le_mul_of_nonneg_right hJ' hV0.le
    linarith
  have hconc : (J : ℝ) * (volume (Metric.ball x₀ Rb ∩ {x | kk J < u x})).toReal ≤
      (J : ℝ) * (ν * V) := by
    have h1 : (J : ℝ) * (Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V))) ≤
        (J : ℝ) * (ν / 2 * V) := mul_le_mul_of_nonneg_left hterm1 hJR.le
    have h3 : (J : ℝ) * (ν / 2 * V) + (J : ℝ) * (ν / 2 * V) = (J : ℝ) * (ν * V) := by ring
    calc (J : ℝ) * (volume (Metric.ball x₀ Rb ∩ {x | kk J < u x})).toReal
        ≤ (J : ℝ) * (Cbig * (t ^ (p - 2) * (8 * γ * 2 ^ d * V))) + Cbig * t ^ p * V := hbig
      _ ≤ (J : ℝ) * (ν / 2 * V) + (J : ℝ) * (ν / 2 * V) := add_le_add h1 hterm2
      _ = (J : ℝ) * (ν * V) := h3
  show (volume (Metric.ball x₀ Rb ∩ {x | kk J < u x})).toReal ≤ ν * V
  exact le_of_mul_le_mul_left hconc hJR


end Komlos.Literature.Regularized
