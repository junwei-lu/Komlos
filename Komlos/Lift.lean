import Komlos.Transform

/-!
# The geometric lift and its Steiner symmetral (paper Lemma 4.1)

The lift `B = lift K v = {(y, s) : |s| < 3, y + s v ∈ K}` is a nonempty bounded open convex
subset of `ℝ^d × ℝ`; its vertical fibers `J_y = {s : (y, s) ∈ B}` are open intervals
(`exists_fiber_eq_Ioo`), whose lengths `ℓ = fiberLength K v` are concave on the projection
of `B` (`fiberLength_concave`).  The Steiner symmetral `B⋆ = steiner K v = {(y, s) : |s| < ℓ(y)/2}`
is again nonempty bounded open convex (`isGoodConvex_steiner`), symmetric in `s`
(`steiner_symm`), and its height-one section is the transform `𝒯_v K`
(`sectionAt_steiner_one`, paper (4.3)).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-- Membership in the lift, unfolded. -/
theorem mem_lift_iff {K : Set (Euc d)} {v : Euc d} {p : Euc d × ℝ} :
    p ∈ lift K v ↔ |p.2| < 3 ∧ p.1 + p.2 • v ∈ K :=
  Iff.rfl

/-- The horizontal coordinate of a point of the lift is bounded by `r + 3‖v‖` when
`K ⊆ closedBall 0 r`. -/
theorem norm_fst_le_of_mem_lift {K : Set (Euc d)} {v : Euc d} {r : ℝ}
    (hr : K ⊆ Metric.closedBall 0 r) {p : Euc d × ℝ} (hp : p ∈ lift K v) :
    ‖p.1‖ ≤ r + 3 * ‖v‖ := by
  have h1 : ‖p.1 + p.2 • v‖ ≤ r := mem_closedBall_zero_iff.1 (hr hp.2)
  calc ‖p.1‖ = ‖(p.1 + p.2 • v) - p.2 • v‖ := by simp
    _ ≤ ‖p.1 + p.2 • v‖ + ‖p.2 • v‖ := norm_sub_le _ _
    _ ≤ r + 3 * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        have := mul_le_mul_of_nonneg_right hp.1.le (norm_nonneg v)
        linarith

/-- The lift of a nonempty bounded open convex set is nonempty bounded open convex. -/
theorem isGoodConvex_lift {K : Set (Euc d)} (hK : IsGoodConvex K) (v : Euc d) :
    IsGoodConvex (lift K v) where
  nonempty := by
    obtain ⟨x, hx⟩ := hK.nonempty
    exact ⟨(x, 0), by simp [lift, hx]⟩
  isBounded := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Euc d)).1 hK.isBounded
    have hb : Bornology.IsBounded
        (Metric.closedBall (0 : Euc d) (r + 3 * ‖v‖) ×ˢ Ioo (-3 : ℝ) 3) :=
      Metric.isBounded_closedBall.prod (Metric.isBounded_Ioo _ _)
    refine hb.subset ?_
    intro p hp
    exact ⟨mem_closedBall_zero_iff.2 (norm_fst_le_of_mem_lift hr hp), abs_lt.1 hp.1⟩
  isOpen := by
    have h1 : IsOpen {p : Euc d × ℝ | |p.2| < 3} := isOpen_lt continuous_snd.abs continuous_const
    have h2 : IsOpen {p : Euc d × ℝ | p.1 + p.2 • v ∈ K} :=
      hK.isOpen.preimage (continuous_fst.add (continuous_snd.smul continuous_const))
    exact h1.inter h2
  convex := by
    intro p hp q hq a b ha hb hab
    refine ⟨?_, ?_⟩
    · have := convex_Ioo (-3 : ℝ) 3 (abs_lt.1 hp.1) (abs_lt.1 hq.1) ha hb hab
      exact abs_lt.2 this
    · have := hK.convex hp.2 hq.2 ha hb hab
      convert this using 1
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      module

/-- Vertical fibers of the lift are open intervals (possibly empty). -/
theorem exists_fiber_eq_Ioo {K : Set (Euc d)} (hK : IsGoodConvex K) (v : Euc d) (y : Euc d) :
    ∃ a b : ℝ, {s : ℝ | (y, s) ∈ lift K v} = Ioo a b := by
  set J := {s : ℝ | (y, s) ∈ lift K v} with hJ
  have hL := isGoodConvex_lift hK v
  have hJopen : IsOpen J := hL.isOpen.preimage (Continuous.prodMk_right y)
  have hJconv : Convex ℝ J := by
    intro s hs t ht a b ha hb hab
    have h := hL.convex hs ht ha hb hab
    have h2 : a • (y, s) + b • (y, t) = (y, a • s + b • t) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, ← add_smul, hab, one_smul]
      · simp
    rw [h2] at h
    exact h
  have hsub : J ⊆ Ioo (-3) 3 := fun s hs => abs_lt.1 hs.1
  have hbdd₁ : BddBelow J := bddBelow_Ioo.mono hsub
  have hbdd₂ : BddAbove J := bddAbove_Ioo.mono hsub
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · exact ⟨0, 0, by rw [hJe, Ioo_self]⟩
  refine ⟨sInf J, sSup J, Subset.antisymm ?_ ?_⟩
  · intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJopen s hs
    rw [Real.ball_eq_Ioo] at hball
    constructor
    · calc sInf J ≤ s - ε / 2 := csInf_le hbdd₁ (hball ⟨by linarith, by linarith⟩)
        _ < s := by linarith
    · calc s < s + ε / 2 := by linarith
        _ ≤ sSup J := le_csSup hbdd₂ (hball ⟨by linarith, by linarith⟩)
  · exact IsConnected.Ioo_csInf_csSup_subset ⟨hJne, hJconv.ordConnected.isPreconnected⟩
      hbdd₁ hbdd₂

/-- The fiber length in terms of the endpoints of the fiber. -/
theorem fiberLength_eq_of_eq_Ioo {K : Set (Euc d)} {v : Euc d} {y : Euc d} {a b : ℝ}
    (h : {s : ℝ | (y, s) ∈ lift K v} = Ioo a b) : fiberLength K v y = max (b - a) 0 := by
  rw [fiberLength, h, Real.volume_Ioo, ENNReal.toReal_ofReal']

/-- Fiber lengths are nonnegative. -/
theorem fiberLength_nonneg (K : Set (Euc d)) (v : Euc d) (y : Euc d) :
    0 ≤ fiberLength K v y :=
  ENNReal.toReal_nonneg

/-- Fiber lengths are at most `6` (fibers lie in `(-3, 3)`). -/
theorem fiberLength_le_six (K : Set (Euc d)) (v : Euc d) (y : Euc d) :
    fiberLength K v y ≤ 6 := by
  unfold fiberLength
  have hsub : {s : ℝ | (y, s) ∈ lift K v} ⊆ Ioo (-3) 3 := fun s hs => abs_lt.1 hs.1
  calc (volume {s : ℝ | (y, s) ∈ lift K v}).toReal ≤ (volume (Ioo (-3 : ℝ) 3)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Ioo]) (measure_mono hsub)
    _ = 6 := by rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by norm_num)]; norm_num

/-- Two points `a', b'` of the fiber over `y` force `ℓ(y) > b' − a'` (the fiber is an open
interval containing both). -/
theorem sub_lt_fiberLength_of_mem {K : Set (Euc d)} (hK : IsGoodConvex K) {v : Euc d}
    {y : Euc d} {a' b' : ℝ} (ha : (y, a') ∈ lift K v) (hb : (y, b') ∈ lift K v) :
    b' - a' < fiberLength K v y := by
  obtain ⟨c, e, hce⟩ := exists_fiber_eq_Ioo hK v y
  have ha' : a' ∈ Ioo c e := by rw [← hce]; exact ha
  have hb' : b' ∈ Ioo c e := by rw [← hce]; exact hb
  rw [fiberLength_eq_of_eq_Ioo hce]
  exact lt_max_of_lt_left (by linarith [ha'.1, hb'.2])

/-- Fiber lengths are concave on the projection of the lift:
`(1−θ) J_{y₀} + θ J_{y₁} ⊆ J_{(1−θ)y₀ + θ y₁}`. -/
theorem fiberLength_concave {K : Set (Euc d)} (hK : IsGoodConvex K) (v : Euc d)
    {y₀ y₁ : Euc d} (h₀ : 0 < fiberLength K v y₀) (h₁ : 0 < fiberLength K v y₁) {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) * fiberLength K v y₀ + θ * fiberLength K v y₁ ≤
      fiberLength K v ((1 - θ) • y₀ + θ • y₁) := by
  obtain ⟨a₀, b₀, h₀'⟩ := exists_fiber_eq_Ioo hK v y₀
  obtain ⟨a₁, b₁, h₁'⟩ := exists_fiber_eq_Ioo hK v y₁
  obtain ⟨a, b, h'⟩ := exists_fiber_eq_Ioo hK v ((1 - θ) • y₀ + θ • y₁)
  rw [fiberLength_eq_of_eq_Ioo h₀'] at h₀ ⊢
  rw [fiberLength_eq_of_eq_Ioo h₁'] at h₁ ⊢
  rw [fiberLength_eq_of_eq_Ioo h']
  have hab₀ : a₀ < b₀ := sub_pos.1 ((lt_max_iff.1 h₀).resolve_right (lt_irrefl _))
  have hab₁ : a₁ < b₁ := sub_pos.1 ((lt_max_iff.1 h₁).resolve_right (lt_irrefl _))
  rw [max_eq_left (sub_pos.2 hab₀).le, max_eq_left (sub_pos.2 hab₁).le]
  -- the interval `(lo, hi)` sits inside the fiber over the combination
  have hlohi : (1 - θ) * a₀ + θ * a₁ < (1 - θ) * b₀ + θ * b₁ := by
    rcases eq_or_lt_of_le hθ₀ with rfl | hθ
    · simpa using hab₀
    · nlinarith [mul_nonneg (sub_nonneg.2 hθ₁) (sub_pos.2 hab₀).le, mul_pos hθ (sub_pos.2 hab₁)]
  have key : Ioo ((1 - θ) * a₀ + θ * a₁) ((1 - θ) * b₀ + θ * b₁) ⊆ Ioo a b := by
    rw [← h']
    intro s hs
    obtain ⟨l, hl0, hl1, hsl⟩ : ∃ l : ℝ, 0 < l ∧ l < 1 ∧
        s = (1 - l) * ((1 - θ) * a₀ + θ * a₁) + l * ((1 - θ) * b₀ + θ * b₁) := by
      refine ⟨(s - ((1 - θ) * a₀ + θ * a₁)) / (((1 - θ) * b₀ + θ * b₁) - ((1 - θ) * a₀ + θ * a₁)),
        div_pos (by linarith [hs.1]) (by linarith), (div_lt_one (by linarith)).2 (by linarith [hs.2]),
        ?_⟩
      have hne : ((1 - θ) * b₀ + θ * b₁) - ((1 - θ) * a₀ + θ * a₁) ≠ 0 := (sub_pos.2 hlohi).ne'
      field_simp
      ring
    have hs0 : (1 - l) * a₀ + l * b₀ ∈ {s : ℝ | (y₀, s) ∈ lift K v} := by
      rw [h₀']; exact ⟨by nlinarith, by nlinarith⟩
    have hs1 : (1 - l) * a₁ + l * b₁ ∈ {s : ℝ | (y₁, s) ∈ lift K v} := by
      rw [h₁']; exact ⟨by nlinarith, by nlinarith⟩
    have hmem := (isGoodConvex_lift hK v).convex hs0 hs1 (sub_nonneg.2 hθ₁) hθ₀ (by ring)
    have heq : (1 - θ) • (y₀, (1 - l) * a₀ + l * b₀) + θ • (y₁, (1 - l) * a₁ + l * b₁) =
        ((1 - θ) • y₀ + θ • y₁, s) := by
      ext
      · simp
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [hsl]; ring
    rw [heq] at hmem
    exact hmem
  obtain ⟨hlo, hhi⟩ := (Ioo_subset_Ioo_iff hlohi).1 key
  exact le_max_of_le_left (by linarith)

/-- Paper Lemma 4.1: the Steiner symmetral `B⋆` is nonempty, bounded, open, convex. -/
theorem isGoodConvex_steiner {K : Set (Euc d)} (hK : IsGoodConvex K) (v : Euc d) :
    IsGoodConvex (steiner K v) where
  nonempty := by
    obtain ⟨x, hx⟩ := hK.nonempty
    refine ⟨(x, 0), ?_⟩
    show |(0 : ℝ)| < fiberLength K v x / 2
    have h0 : (x, (0 : ℝ)) ∈ lift K v := ⟨by simp, by simpa using hx⟩
    obtain ⟨a, b, hab⟩ := exists_fiber_eq_Ioo hK v x
    have hmem : (0 : ℝ) ∈ Ioo a b := by rw [← hab]; exact h0
    rw [fiberLength_eq_of_eq_Ioo hab, abs_zero]
    have : 0 < b - a := by linarith [hmem.1, hmem.2]
    rw [max_eq_left this.le]; linarith
  isBounded := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Euc d)).1 hK.isBounded
    have hb : Bornology.IsBounded
        (Metric.closedBall (0 : Euc d) (r + 3 * ‖v‖) ×ˢ Ioo (-3 : ℝ) 3) :=
      Metric.isBounded_closedBall.prod (Metric.isBounded_Ioo _ _)
    refine hb.subset ?_
    rintro ⟨y, s⟩ hp
    change |s| < fiberLength K v y / 2 at hp
    have hpos : 0 < fiberLength K v y := by linarith [abs_nonneg s]
    obtain ⟨a, b, hab⟩ := exists_fiber_eq_Ioo hK v y
    rw [fiberLength_eq_of_eq_Ioo hab] at hpos
    have hab' : a < b := sub_pos.1 ((lt_max_iff.1 hpos).resolve_right (lt_irrefl _))
    have hmem : (y, (a + b) / 2) ∈ lift K v := by
      have : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
      rw [← hab] at this; exact this
    have h1 : ‖y‖ ≤ r + 3 * ‖v‖ := norm_fst_le_of_mem_lift (p := (y, (a + b) / 2)) hr hmem
    refine ⟨mem_closedBall_zero_iff.2 h1, ?_⟩
    have := fiberLength_le_six K v y
    exact abs_lt.1 (by linarith)
  isOpen := by
    rw [isOpen_prod_iff]
    intro y₀ s₀ hp
    change |s₀| < fiberLength K v y₀ / 2 at hp
    obtain ⟨a, b, hab⟩ := exists_fiber_eq_Ioo hK v y₀
    rw [fiberLength_eq_of_eq_Ioo hab] at hp
    have hba : 2 * |s₀| < b - a := by
      have := abs_nonneg s₀
      rcases le_or_gt (b - a) 0 with h | h
      · rw [max_eq_right h] at hp; linarith
      · rw [max_eq_left h.le] at hp; linarith
    obtain ⟨ε, hε0, hεdef⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = (b - a - 2 * |s₀|) / 4 :=
      ⟨_, by linarith, rfl⟩
    have ha' : (y₀, a + ε) ∈ lift K v := by
      have : a + ε ∈ Ioo a b := ⟨by linarith, by linarith [abs_nonneg s₀]⟩
      rw [← hab] at this; exact this
    have hb' : (y₀, b - ε) ∈ lift K v := by
      have : b - ε ∈ Ioo a b := ⟨by linarith [abs_nonneg s₀], by linarith⟩
      rw [← hab] at this; exact this
    have hopen := (isGoodConvex_lift hK v).isOpen
    refine ⟨{y | (y, a + ε) ∈ lift K v} ∩ {y | (y, b - ε) ∈ lift K v},
      Ioo (-(((b - ε) - (a + ε)) / 2)) (((b - ε) - (a + ε)) / 2),
      (hopen.preimage (Continuous.prodMk_left (a + ε))).inter
        (hopen.preimage (Continuous.prodMk_left (b - ε))),
      isOpen_Ioo, ⟨ha', hb'⟩, ?_, ?_⟩
    · exact abs_lt.1 (by linarith)
    · rintro ⟨y, s⟩ ⟨⟨hy1, hy2⟩, hs⟩
      change |s| < fiberLength K v y / 2
      have hs' : |s| < ((b - ε) - (a + ε)) / 2 := abs_lt.2 hs
      have := sub_lt_fiberLength_of_mem hK hy1 hy2
      linarith
  convex := by
    intro p hp q hq a b ha hb hab
    change |p.2| < fiberLength K v p.1 / 2 at hp
    change |q.2| < fiberLength K v q.1 / 2 at hq
    show |(a • p + b • q).2| < fiberLength K v (a • p + b • q).1 / 2
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hp0 : 0 < fiberLength K v p.1 := by linarith [abs_nonneg p.2]
    have hq0 : 0 < fiberLength K v q.1 := by linarith [abs_nonneg q.2]
    have ha' : a = 1 - b := eq_sub_of_add_eq hab
    have hcon := fiberLength_concave hK v hp0 hq0 hb (by linarith)
    rw [← ha'] at hcon
    calc |a * p.2 + b * q.2| ≤ a * |p.2| + b * |q.2| := by
          calc |a * p.2 + b * q.2| ≤ |a * p.2| + |b * q.2| := abs_add_le _ _
            _ = a * |p.2| + b * |q.2| := by
                rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < (a * fiberLength K v p.1 + b * fiberLength K v q.1) / 2 := by
          rcases eq_or_lt_of_le ha with rfl | ha''
          · have hb1 : b = 1 := by linarith
            subst hb1
            simpa using hq
          · nlinarith [mul_lt_mul_of_pos_left hp ha'', mul_le_mul_of_nonneg_left hq.le hb]
      _ ≤ fiberLength K v (a • p.1 + b • q.1) / 2 := by linarith

/-- `B⋆` is symmetric in `s`. -/
theorem steiner_symm {K : Set (Euc d)} (v : Euc d) (p : Euc d × ℝ) (hp : p ∈ steiner K v) :
    (p.1, -p.2) ∈ steiner K v := by
  change |-p.2| < fiberLength K v p.1 / 2
  rwa [abs_neg]

/-- Paper (4.3): the height-one section of `B⋆` is the transform:
`{y : ℓ(y) > 2} = 𝒯_v K`. -/
theorem sectionAt_steiner_one {K : Set (Euc d)} (hK : IsGoodConvex K) (v : Euc d) :
    sectionAt (steiner K v) 1 = transform v K := by
  ext y
  rw [mem_transform_iff]
  change |(1 : ℝ)| < fiberLength K v y / 2 ↔ _
  rw [abs_one]
  obtain ⟨a, b, hab⟩ := exists_fiber_eq_Ioo hK v y
  rw [fiberLength_eq_of_eq_Ioo hab]
  constructor
  · intro h
    have hba : 2 < b - a := by
      rcases le_or_gt (b - a) 0 with h' | h'
      · rw [max_eq_right h'] at h; linarith
      · rw [max_eq_left h'.le] at h; linarith
    have h1 : (y, (a + b) / 2 - 1) ∈ lift K v := by
      have : (a + b) / 2 - 1 ∈ Ioo a b := ⟨by linarith, by linarith⟩
      rw [← hab] at this; exact this
    have h2 : (y, (a + b) / 2 + 1) ∈ lift K v := by
      have : (a + b) / 2 + 1 ∈ Ioo a b := ⟨by linarith, by linarith⟩
      rw [← hab] at this; exact this
    refine ⟨y + ((a + b) / 2) • v, -((a + b) / 2), ?_, ?_, ?_, ?_⟩
    · convert h1.2 using 1
      simp only [sub_smul, one_smul]
      abel
    · convert h2.2 using 1
      simp only [add_smul, one_smul]
      abel
    · rw [abs_neg, abs_lt]
      have := abs_lt.1 h1.1
      have := abs_lt.1 h2.1
      constructor <;> linarith
    · simp [neg_smul]
  · rintro ⟨z, t, hz1, hz2, ht, rfl⟩
    have ht' := abs_lt.1 ht
    have h1 : -t - 1 ∈ {s : ℝ | (z + t • v, s) ∈ lift K v} := by
      refine ⟨?_, ?_⟩
      · rw [abs_lt]; constructor <;> linarith
      · convert hz1 using 1
        simp only [sub_smul, neg_smul, one_smul]
        abel
    have h2 : -t + 1 ∈ {s : ℝ | (z + t • v, s) ∈ lift K v} := by
      refine ⟨?_, ?_⟩
      · rw [abs_lt]; constructor <;> linarith
      · convert hz2 using 1
        simp only [add_smul, neg_smul, one_smul]
        abel
    rw [hab] at h1 h2
    have : 2 < b - a := by linarith [h1.1, h2.2]
    rw [max_eq_left (by linarith)]
    linarith

end Komlos
