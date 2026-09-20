import Komlos.Literature.Regularized.DeGiorgiClass

/-!
# De Giorgi's isoperimetric inequality on a ball

Auxiliary material for `Komlos/Literature/Regularized/DeGiorgiOsc.lean`, the oscillation half of
lane `DGN` of `REGULARIZED_ROUTE.md` (Revision 2).

The analytic input of De Giorgi's *second* lemma (measure shrinking) is the **isoperimetric**
(or *De Giorgi–Poincaré*) inequality: for `k < l`,

`|B_ρ ∩ {z ≥ l}| · (l-k)^p · |B_ρ ∩ {z ≤ k}| ≤ 2^d (2ρ)^p |B_ρ| ∫_{B_ρ ∩ {k < z ≤ l}} ‖∇z‖^p`.

It is obtained from the project's double-integral Poincaré inequality
`Komlos.Literature.MemW0.measure_mul_lintegral_sub_rpow_le` (`RegularityPoincare.lean`) applied to
the **clamped level function** `w = min ((z - k)_+) (l - k)`, localized by a cutoff: on `B_ρ` one
has `w = l - k` on `{z ≥ l}`, `w = 0` on `{z ≤ k}` and `∇w = 1_{k < z ≤ l} ∇z`.

The exponent must be taken **strictly below `2`**: in the De Giorgi iteration the gradient enters
through `(∫ ‖∇z‖²)^{p/2} |S|^{1-p/2}` (Hölder), and the factor `|S|^{1-p/2}` with a *positive*
exponent is what makes the measures of the level annuli summable.  The file therefore works at a
general `p ∈ (1, 2)`; the consumer uses `p = 3/2`.

## Main results

* `volume_ball_mul_eq` — `|B_{c r}| = c^d |B_r|`.
* `memW0_mono_exponent` — lowering the exponent of `W₀^{1,q}` for a function supported in a set of
  finite measure.
* `memW0_clampLevel` — the localized clamped level function `min ((η (z - k))_+) (l - k)` lies in
  `W₀^{1,p}` of a ball, with weak gradient `1_{k < z ≤ l} ∇z` on the inner ball.
* `measure_mul_measure_le_lintegral_grad_rpow` — the isoperimetric inequality.
* `lintegral_rpow_le_rpow_lintegral_sq` — the Hölder step `∫_S g^p ≤ (∫_S g²)^{p/2} |S|^{1-p/2}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Volumes of concentric balls -/

/-- `|B(x₀, c r)| = c^d |B(x₀, r)|`. -/
theorem volume_ball_mul_eq (hd : 0 < d) (x₀ : Euc d) {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) :
    volume (Metric.ball x₀ (c * r)) = ENNReal.ofReal (c ^ d) * volume (Metric.ball x₀ r) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.1 hd
  rw [Measure.addHaar_ball volume x₀ (by positivity : (0:ℝ) ≤ c * r),
    Measure.addHaar_ball volume x₀ hr, finrank_euclideanSpace_fin, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_pow]

/-! ### Hölder between the exponents `p` and `2` -/

/-- **Hölder's inequality between the exponents `p` and `2`** for `0 < p < 2`:
`∫_S g^p ≤ (∫_S g²)^{p/2} |S|^{1 - p/2}`. -/
theorem lintegral_rpow_le_rpow_lintegral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Set α) {g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.restrict S)) {p : ℝ}
    (hp0 : 0 < p) (hp2 : p ≤ 2) :
    ∫⁻ x in S, g x ^ p ∂μ ≤ (∫⁻ x in S, g x ^ (2 : ℝ) ∂μ) ^ (p / 2) * μ S ^ (1 - p / 2) := by
  have hkey := ENNReal.lintegral_mul_norm_pow_le (μ := μ.restrict S) (f := fun x => g x ^ (2 : ℝ))
    (g := fun _ => (1 : ℝ≥0∞)) (hg.pow_const _) aemeasurable_const
    (p := p / 2) (q := 1 - p / 2) (by positivity) (by linarith) (by ring)
  simp only [ENNReal.one_rpow, mul_one, one_mul, lintegral_const,
    Measure.restrict_apply_univ] at hkey
  refine le_trans (le_of_eq ?_) hkey
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_mul]
  congr 1
  ring

/-! ### Lowering the Sobolev exponent -/

/-- **Lowering the exponent**: a function of `W₀^{1,q}(K)` which vanishes, together with an
explicit weak gradient, outside a set `K` of finite measure, lies in `W₀^{1,p}(K)` for `p ≤ q`. -/
theorem memW0_mono_exponent {p q : ℝ} (hpq : p ≤ q) {K : Set (Euc d)} (hK : volume K ≠ ⊤)
    {f : Euc d → ℝ} {g : Euc d → Euc d} (hfq : MemW0 q K f) (hg : HasWeakGradient f g)
    (hf0 : ∀ x, x ∉ K → f x = 0) (hg0 : ∀ x, x ∉ K → g x = 0) : MemW0 p K f where
  memLp := hfq.memLp.mono_exponent_of_measure_support_ne_top hf0 hK (ENNReal.ofReal_le_ofReal hpq)
  ae_eq_zero := hfq.ae_eq_zero
  exists_weakGradient :=
    ⟨g, hg, (hfq.memLp_weakGrad.ae_eq hg.weakGrad_ae_eq).mono_exponent_of_measure_support_ne_top
      hg0 hK (ENNReal.ofReal_le_ofReal hpq)⟩

/-! ### The localized clamped level function -/

/-- `t - (t - H)_+ = min t H`. -/
theorem sub_max_sub_eq_min (t H : ℝ) : t - max (t - H) 0 = min t H := by
  rcases le_total t H with h | h
  · rw [max_eq_right (by linarith), sub_zero, min_eq_left h]
  · rw [max_eq_left (by linarith), min_eq_right h]
    ring

/-- **The localized clamped level function.**  For `z` with weak gradient `G`, both locally square
integrable on `closedBall x₀ (3ρ/2)`, and levels `k < l`, there is
`w ∈ W₀^{1,p}(closedBall x₀ (3ρ/2))` which equals the clamp `min ((z-k)_+) (l-k)` on `ball x₀ ρ`
and whose weak gradient is dominated by `1_{k < z ≤ l} ‖G‖` there.

Proof: cut off with a smooth `η` which is `1` on `closedBall x₀ (5ρ/4)` and supported in
`closedBall x₀ (3ρ/2)` (`exists_cutoff_const`), so that `f₀ = η (z - k)` lies in `W₀^{1,2}`
(`memW0_two_mul_cutoff`), hence in `W₀^{1,p}` (`memW0_mono_exponent`); then truncate twice with
`memW0_posPart` — at the level `0` and at the level `l - k` — and subtract. -/
theorem memW0_clampLevel {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {z : Euc d → ℝ} {G : Euc d → Euc d}
    (hzG : HasWeakGradient z G) (hzm : Measurable z) (hGm : Measurable G) {x₀ : Euc d} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hz2 : IntegrableOn (fun x => z x ^ 2) (Metric.closedBall x₀ (3 / 2 * ρ)) volume)
    (hG2 : IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ (3 / 2 * ρ)) volume)
    {k l : ℝ} (hkl : k < l) :
    ∃ w : Euc d → ℝ, MemW0 p (Metric.closedBall x₀ (3 / 2 * ρ)) w ∧
      (∀ x ∈ Metric.ball x₀ ρ, w x = min (max (z x - k) 0) (l - k)) ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ ρ)), ‖weakGrad w x‖ₑ ≤
        (Metric.ball x₀ ρ ∩ {y | k < z y ∧ z y ≤ l}).indicator (fun y => ‖G y‖ₑ) x := by
  have hH : (0 : ℝ) < l - k := by linarith
  obtain ⟨_, _, hcut⟩ := exists_cutoff_const d
  obtain ⟨η, hηC, hηs, hηB, hη0, hη1, hηone, _⟩ :=
    hcut x₀ (5 / 4 * ρ) (3 / 2 * ρ) (by positivity) (by linarith)
  have hη1' : ContDiff ℝ 1 η := hηC.of_le (by simp)
  have hBfin : volume (Metric.closedBall x₀ (3 / 2 * ρ)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hballsub : Metric.ball x₀ ρ ⊆ Metric.ball x₀ (5 / 4 * ρ) :=
    Metric.ball_subset_ball (by linarith)
  have hηval : ∀ x ∈ Metric.ball x₀ (5 / 4 * ρ), η x = 1 := fun x hx =>
    hηone x (Metric.ball_subset_closedBall hx)
  have hηgrad : ∀ x ∈ Metric.ball x₀ (5 / 4 * ρ), gradient η x = 0 := by
    intro x hx
    have he : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) fun y hy => hηval y hy
    rw [he.gradient_eq]
    simp
  set f₀ : Euc d → ℝ := fun x => η x * (z x - k) with hf₀def
  set g₀ : Euc d → Euc d := fun x => η x • G x + (z x - k) • gradient η x with hg₀def
  have e1 : ((fun x => η x * z x) + (-k) • η) = f₀ := by
    funext x
    simp only [hf₀def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hwg₀ : HasWeakGradient f₀ g₀ := by
    have h1 : HasWeakGradient (fun x => η x * z x)
        (fun x => η x • G x + z x • gradient η x) := hzG.contDiff_mul hηC
    have h2 : HasWeakGradient ((-k) • η) ((-k) • gradient η) :=
      (hasWeakGradient_gradient hη1' hηs).smul (-k)
    have h3 := h1.add h2
    have e2 : ((fun x => η x • G x + z x • gradient η x) + (-k) • gradient η) = g₀ := by
      funext x
      simp only [hg₀def, Pi.add_apply, Pi.smul_apply]
      module
    rwa [e1, e2] at h3
  have hηabs : ∀ x, |η x| ≤ 1 := fun x => by rw [abs_of_nonneg (hη0 x)]; exact hη1 x
  have hmul2 := memW0_two_mul_cutoff hzG hzm.aestronglyMeasurable hGm.aestronglyMeasurable
    hz2 hG2 hηC hηs hηB hηabs
  have hconst2 : MemW0 2 (Metric.closedBall x₀ (3 / 2 * ρ)) ((-k) • η) :=
    (memW0_of_contDiff hη1' hηs hηB 2).smul (-k)
  have hf₀2 : MemW0 2 (Metric.closedBall x₀ (3 / 2 * ρ)) f₀ := by
    rw [← e1]
    exact hmul2.1.add hconst2
  have hf₀0 : ∀ x, x ∉ Metric.closedBall x₀ (3 / 2 * ρ) → f₀ x = 0 := fun x hx => by
    have h : η x = 0 := image_eq_zero_of_notMem_tsupport fun hh => hx (hηB hh)
    simp [hf₀def, h]
  have hg₀0 : ∀ x, x ∉ Metric.closedBall x₀ (3 / 2 * ρ) → g₀ x = 0 := fun x hx => by
    have h1 : η x = 0 := image_eq_zero_of_notMem_tsupport fun hh => hx (hηB hh)
    have h2 : gradient η x = 0 := gradient_eq_zero_of_notMem_tsupport fun hh => hx (hηB hh)
    simp [hg₀def, h1, h2]
  have hf₀p : MemW0 p (Metric.closedBall x₀ (3 / 2 * ρ)) f₀ :=
    memW0_mono_exponent hp2 hBfin hf₀2 hwg₀ hf₀0 hg₀0
  -- the two truncations
  obtain ⟨hu₁, hgu₁'⟩ := memW0_posPart hp1 hf₀p 0
  set u₁ : Euc d → ℝ := fun x => posPartShift 0 (f₀ x) with hu₁def
  set G₁ : Euc d → Euc d := fun x => (if (0 : ℝ) < f₀ x then (1 : ℝ) else 0) • g₀ x with hG₁def
  have hgu₁ : HasWeakGradient u₁ G₁ := by
    refine hgu₁'.congr_right ?_
    filter_upwards [hwg₀.weakGrad_ae_eq] with x hx
    simp only [hG₁def, hx]
  obtain ⟨hu₂, hgu₂'⟩ := memW0_posPart hp1 hu₁ (l - k)
  set u₂ : Euc d → ℝ := fun x => posPartShift (l - k) (u₁ x) with hu₂def
  set G₂ : Euc d → Euc d := fun x => (if l - k < u₁ x then (1 : ℝ) else 0) • G₁ x with hG₂def
  have hgu₂ : HasWeakGradient u₂ G₂ := by
    refine hgu₂'.congr_right ?_
    filter_upwards [hgu₁.weakGrad_ae_eq] with x hx
    simp only [hG₂def, hx]
  set w : Euc d → ℝ := fun x => u₁ x - u₂ x with hwdef
  have ew : (u₁ + (-1 : ℝ) • u₂) = w := by
    funext x
    simp only [hwdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eG : (G₁ + (-1 : ℝ) • G₂) = fun x => G₁ x - G₂ x := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply]
    module
  have hwW0 : MemW0 p (Metric.closedBall x₀ (3 / 2 * ρ)) w := by
    rw [← ew]
    exact hu₁.add (hu₂.smul (-1))
  have hgw : HasWeakGradient w (fun x => G₁ x - G₂ x) := by
    have h := hgu₁.add (hgu₂.smul (-1))
    rwa [ew, eG] at h
  -- pointwise identities on the inner ball
  have hpt : ∀ x ∈ Metric.ball x₀ ρ, f₀ x = z x - k ∧ g₀ x = G x ∧ u₁ x = max (z x - k) 0 ∧
      u₂ x = max (max (z x - k) 0 - (l - k)) 0 := by
    intro x hx
    have hxb := hballsub hx
    have hηx : η x = 1 := hηval x hxb
    have hgx : gradient η x = 0 := hηgrad x hxb
    have h1 : f₀ x = z x - k := by simp [hf₀def, hηx]
    have h2 : g₀ x = G x := by simp [hg₀def, hηx, hgx]
    have h3 : u₁ x = max (z x - k) 0 := by simp [hu₁def, posPartShift, h1]
    refine ⟨h1, h2, h3, ?_⟩
    have h4 : max (-(l - k)) 0 = 0 := max_eq_right (by linarith)
    simp only [hu₂def, posPartShift, h4, sub_zero, h3]
  refine ⟨w, hwW0, ?_, ?_⟩
  · intro x hx
    obtain ⟨_, _, h3, h4⟩ := hpt x hx
    rw [hwdef]
    simp only [h3, h4]
    exact sub_max_sub_eq_min _ _
  · filter_upwards [ae_restrict_of_ae hgw.weakGrad_ae_eq, ae_restrict_mem measurableSet_ball]
      with x hx hxb
    rw [hx]
    obtain ⟨h1, h2, h3, _⟩ := hpt x hxb
    by_cases hk : k < z x
    · by_cases hl : z x ≤ l
      · have hmem : x ∈ Metric.ball x₀ ρ ∩ {y | k < z y ∧ z y ≤ l} := ⟨hxb, hk, hl⟩
        rw [Set.indicator_of_mem hmem]
        have hpos : (0 : ℝ) < f₀ x := by rw [h1]; linarith
        have hG₁x : G₁ x = G x := by simp [hG₁def, if_pos hpos, h2]
        have hu : ¬ (l - k < u₁ x) := by
          rw [h3, max_eq_left (by linarith)]
          push Not
          linarith
        have hG₂x : G₂ x = 0 := by simp [hG₂def, if_neg hu]
        rw [hG₁x, hG₂x, sub_zero]
      · have hpos : (0 : ℝ) < f₀ x := by rw [h1]; linarith
        have hu : l - k < u₁ x := by
          rw [h3, max_eq_left (by linarith)]
          linarith [not_le.1 hl]
        have hG₂x : G₂ x = G₁ x := by simp [hG₂def, if_pos hu]
        rw [hG₂x, sub_self]
        simp
    · have hnpos : ¬ ((0 : ℝ) < f₀ x) := by
        rw [h1]
        push Not
        linarith [not_lt.1 hk]
      have hG₁x : G₁ x = 0 := by simp [hG₁def, if_neg hnpos]
      have hG₂x : G₂ x = 0 := by simp [hG₂def, hG₁x]
      rw [hG₁x, hG₂x, sub_self]
      simp

/-! ### The isoperimetric inequality -/

/-- **De Giorgi's isoperimetric inequality on a ball** (De Giorgi 1957; Ladyzhenskaya–Ural'tseva,
*Linear and Quasilinear Elliptic Equations*, Ch. II, Lemma 3.9; Giusti, *Direct Methods in the
Calculus of Variations*, Lemma 7.2): for `k < l` and `1 < p ≤ 2`,

`|B_ρ ∩ {z ≥ l}| · (l-k)^p · |B_ρ ∩ {z ≤ k}| ≤ 2^d (2ρ)^p |B_ρ| ∫_{B_ρ ∩ {k < z ≤ l}} ‖∇z‖^p`.

It is the double-integral Poincaré inequality `MemW0.measure_mul_lintegral_sub_rpow_le` applied to
the clamped level function of `memW0_clampLevel`: that function equals `l - k` on `{z ≥ l}`,
vanishes on `{z ≤ k}` and has gradient `1_{k < z ≤ l} ∇z`. -/
theorem measure_mul_measure_le_lintegral_grad_rpow {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2)
    {z : Euc d → ℝ} {G : Euc d → Euc d} (hzG : HasWeakGradient z G) (hzm : Measurable z)
    (hGm : Measurable G) {x₀ : Euc d} {ρ : ℝ} (hρ : 0 < ρ)
    (hz2 : IntegrableOn (fun x => z x ^ 2) (Metric.closedBall x₀ (3 / 2 * ρ)) volume)
    (hG2 : IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ (3 / 2 * ρ)) volume)
    {k l : ℝ} (hkl : k < l) :
    volume (Metric.ball x₀ ρ ∩ {x | l ≤ z x}) *
        (ENNReal.ofReal (l - k) ^ p * volume (Metric.ball x₀ ρ ∩ {x | z x ≤ k})) ≤
      2 ^ d * ENNReal.ofReal (2 * ρ) ^ p * volume (Metric.ball x₀ ρ) *
        ∫⁻ x in Metric.ball x₀ ρ ∩ {y | k < z y ∧ z y ≤ l}, ‖G x‖ₑ ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hH : (0 : ℝ) < l - k := by linarith
  obtain ⟨w, hw, hwval, hwgrad⟩ := memW0_clampLevel hp1 hp2 hzG hzm hGm hρ hz2 hG2 hkl
  have hEm : MeasurableSet (Metric.ball x₀ ρ ∩ {x | l ≤ z x}) :=
    measurableSet_ball.inter (measurableSet_le measurable_const hzm)
  have hDm : MeasurableSet (Metric.ball x₀ ρ ∩ {x | z x ≤ k}) :=
    measurableSet_ball.inter (measurableSet_le hzm measurable_const)
  have hSm : MeasurableSet (Metric.ball x₀ ρ ∩ {y | k < z y ∧ z y ≤ l}) :=
    measurableSet_ball.inter ((measurableSet_lt measurable_const hzm).inter
      (measurableSet_le hzm measurable_const))
  have hE : ∀ y ∈ Metric.ball x₀ ρ ∩ {x | l ≤ z x}, l - k ≤ w y := by
    intro y hy
    have hy2 : l ≤ z y := hy.2
    rw [hwval y hy.1]
    exact le_min (le_max_of_le_left (by linarith)) le_rfl
  have hBD : ∀ x ∈ Metric.ball x₀ ρ, ∀ y ∈ Metric.ball x₀ ρ, ‖y - x‖ ≤ 2 * ρ := by
    intro x hx y hy
    rw [Metric.mem_ball] at hx hy
    have htri := dist_triangle y x₀ x
    rw [dist_comm x₀ x] at htri
    rw [← dist_eq_norm]
    linarith
  have hkey := hw.measure_mul_lintegral_sub_rpow_le hp1 (convex_ball x₀ ρ) measurableSet_ball
    measure_ball_lt_top.ne hBD hEm inter_subset_left hE
  have hleft : ENNReal.ofReal (l - k) ^ p * volume (Metric.ball x₀ ρ ∩ {x | z x ≤ k}) ≤
      ∫⁻ x in Metric.ball x₀ ρ, ENNReal.ofReal (l - k - w x) ^ p := by
    calc ENNReal.ofReal (l - k) ^ p * volume (Metric.ball x₀ ρ ∩ {x | z x ≤ k})
        = ∫⁻ x in Metric.ball x₀ ρ ∩ {x | z x ≤ k}, ENNReal.ofReal (l - k - w x) ^ p := by
          rw [← setLIntegral_const (Metric.ball x₀ ρ ∩ {x | z x ≤ k})
            (ENNReal.ofReal (l - k) ^ p)]
          refine setLIntegral_congr_fun hDm fun x hx => ?_
          have hx2 : z x ≤ k := hx.2
          have hwx : w x = 0 := by
            rw [hwval x hx.1, max_eq_right (by linarith : z x - k ≤ 0), min_eq_left hH.le]
          rw [hwx, sub_zero]
      _ ≤ ∫⁻ x in Metric.ball x₀ ρ, ENNReal.ofReal (l - k - w x) ^ p :=
          lintegral_mono_set inter_subset_left
  have hright : ∫⁻ x in Metric.ball x₀ ρ, ‖weakGrad w x‖ₑ ^ p ≤
      ∫⁻ x in Metric.ball x₀ ρ ∩ {y | k < z y ∧ z y ≤ l}, ‖G x‖ₑ ^ p := by
    have h1 : ∫⁻ x in Metric.ball x₀ ρ, ‖weakGrad w x‖ₑ ^ p ≤
        ∫⁻ x in Metric.ball x₀ ρ,
          (Metric.ball x₀ ρ ∩ {y | k < z y ∧ z y ≤ l}).indicator
            (fun y => ‖G y‖ₑ ^ p) x := by
      refine lintegral_mono_ae ?_
      filter_upwards [hwgrad] with x hx
      by_cases hmem : x ∈ Metric.ball x₀ ρ ∩ {y | k < z y ∧ z y ≤ l}
      · rw [Set.indicator_of_mem hmem]
        rw [Set.indicator_of_mem hmem] at hx
        exact ENNReal.rpow_le_rpow hx hp0.le
      · rw [Set.indicator_of_notMem hmem]
        rw [Set.indicator_of_notMem hmem] at hx
        have h0 : ‖weakGrad w x‖ₑ = 0 := le_antisymm hx zero_le
        rw [h0, ENNReal.zero_rpow_of_pos hp0]
    refine h1.trans (le_of_eq ?_)
    rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
      Set.inter_eq_left.2 inter_subset_left]
  calc volume (Metric.ball x₀ ρ ∩ {x | l ≤ z x}) *
        (ENNReal.ofReal (l - k) ^ p * volume (Metric.ball x₀ ρ ∩ {x | z x ≤ k}))
      ≤ volume (Metric.ball x₀ ρ ∩ {x | l ≤ z x}) *
          ∫⁻ x in Metric.ball x₀ ρ, ENNReal.ofReal (l - k - w x) ^ p :=
        by gcongr
    _ ≤ 2 ^ d * ENNReal.ofReal (2 * ρ) ^ p * volume (Metric.ball x₀ ρ) *
          ∫⁻ x in Metric.ball x₀ ρ, ‖weakGrad w x‖ₑ ^ p := hkey
    _ ≤ 2 ^ d * ENNReal.ofReal (2 * ρ) ^ p * volume (Metric.ball x₀ ρ) *
          ∫⁻ x in Metric.ball x₀ ρ ∩ {y | k < z y ∧ z y ≤ l}, ‖G x‖ₑ ^ p :=
        by gcongr

end Komlos.Literature.Regularized
