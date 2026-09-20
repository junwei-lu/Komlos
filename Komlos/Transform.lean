import Komlos.Defs

/-!
# The transform `𝒯_v K` (paper Lemma 2.1, "Translate containment")
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Membership in the transform: `y = z + t v` with `z ± v ∈ K` and `|t| < 2`. -/
theorem mem_transform_iff {K : Set E} {v y : E} :
    y ∈ transform v K ↔ ∃ (z : E) (t : ℝ), z - v ∈ K ∧ z + v ∈ K ∧ |t| < 2 ∧ y = z + t • v := by
  constructor
  · intro hy
    obtain ⟨x, hx, w, hw, rfl⟩ := Set.mem_add.1 hy
    obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hb'⟩⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hw
    have hb'' : b + v = a - v := hb'
    refine ⟨a - v, t, ?_, ?_, abs_lt.2 ⟨ht.1, ht.2⟩, rfl⟩
    · have : b = a - v - v := by rw [← hb'']; abel
      rw [← this]; exact hb
    · simpa using ha
  · rintro ⟨z, t, hz1, hz2, ht, rfl⟩
    exact Set.mem_add.2
      ⟨z, ⟨⟨z + v, hz2, by simp⟩, ⟨z - v, hz1, by simp⟩⟩, t • v, ⟨t, abs_lt.1 ht, rfl⟩, rfl⟩

/-- Paper (2.11): `𝒯_v K ⊆ (K − v) ∪ (K + v)` for convex `K`. -/
theorem transform_subset_union {K : Set E} (hK : Convex ℝ K) (v : E) :
    transform v K ⊆ (fun x => x - v) '' K ∪ (fun x => x + v) '' K := by
  intro y hy
  obtain ⟨z, t, hz1, hz2, ht, rfl⟩ := mem_transform_iff.1 hy
  rw [abs_lt] at ht
  rcases le_or_gt 0 t with h | h
  · -- `t ≥ 0`: `y - v = z + (t - 1) v` is a convex combination of `z - v` and `z + v`.
    right
    refine ⟨(1 - t / 2) • (z - v) + (t / 2) • (z + v),
      hK hz1 hz2 (by linarith) (by linarith) (by ring), ?_⟩
    dsimp only
    module
  · -- `t < 0`: `y + v = z + (t + 1) v` is a convex combination of `z - v` and `z + v`.
    left
    refine ⟨(-t / 2) • (z - v) + (1 + t / 2) • (z + v),
      hK hz1 hz2 (by linarith) (by linarith) (by ring), ?_⟩
    dsimp only
    module

omit [NormedSpace ℝ E] in
/-- The translate `K - v` of a bounded set is bounded. -/
theorem isBounded_image_sub {K : Set E} (hK : Bornology.IsBounded K) (v : E) :
    Bornology.IsBounded ((fun x => x - v) '' K) := by
  rw [← Set.sub_singleton]
  exact hK.sub Bornology.isBounded_singleton

omit [NormedSpace ℝ E] in
/-- The translate `K + v` of a bounded set is bounded. -/
theorem isBounded_image_add {K : Set E} (hK : Bornology.IsBounded K) (v : E) :
    Bornology.IsBounded ((fun x => x + v) '' K) := by
  rw [← Set.add_singleton]
  exact hK.add Bornology.isBounded_singleton

/-- The segment `{t v : |t| < 2}` is bounded. -/
theorem isBounded_segment_image (v : E) :
    Bornology.IsBounded ((fun t : ℝ => t • v) '' Ioo (-2 : ℝ) 2) := by
  refine isBounded_iff_forall_norm_le.2 ⟨2 * ‖v‖, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_lt.2 ⟨ht.1, ht.2⟩).le (norm_nonneg v)

/-- The segment `{t v : |t| < 2}` is convex. -/
theorem convex_segment_image (v : E) :
    Convex ℝ ((fun t : ℝ => t • v) '' Ioo (-2 : ℝ) 2) :=
  (convex_Ioo (-2 : ℝ) 2).is_linear_image (IsLinearMap.isLinearMap_smul' v)

/-- Paper Lemma 2.1: a nonempty transform of a nonempty bounded open convex set is again
nonempty, bounded, open and convex. -/
theorem isGoodConvex_transform {K : Set E} (hK : IsGoodConvex K) (v : E)
    (hne : (transform v K).Nonempty) : IsGoodConvex (transform v K) := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · -- bounded: Minkowski sum of two bounded sets
    exact ((isBounded_image_sub hK.isBounded v).subset Set.inter_subset_left).add
      (isBounded_segment_image v)
  · -- open: `A + B` is open when `A` is open
    refine IsOpen.add_right (IsOpen.inter ?_ ?_)
    · rw [← Set.sub_singleton]; exact hK.isOpen.sub_right
    · rw [← Set.add_singleton]; exact hK.isOpen.add_right
  · -- convex: Minkowski sum of convex sets
    refine Convex.add (Convex.inter ?_ ?_) (convex_segment_image v)
    · rw [← Set.sub_singleton]; exact hK.convex.sub (convex_singleton v)
    · rw [← Set.add_singleton]; exact hK.convex.add (convex_singleton v)

/-- Paper Lemma 2.1: symmetry `K = −K` is preserved by the transform. -/
theorem transform_neg_eq {K : Set E} (hK : K = -K) (v : E) :
    transform v K = -transform v K := by
  have hmem : ∀ x, x ∈ K → -x ∈ K := fun x hx => by
    rw [hK] at hx; exact Set.mem_neg.1 hx
  have key : ∀ y, y ∈ transform v K → -y ∈ transform v K := by
    intro y hy
    obtain ⟨z, t, hz1, hz2, ht, rfl⟩ := mem_transform_iff.1 hy
    refine mem_transform_iff.2 ⟨-z, -t, ?_, ?_, by rwa [abs_neg], by module⟩
    · convert hmem _ hz2 using 1; abel
    · convert hmem _ hz1 using 1; abel
  ext y
  exact ⟨fun h => Set.mem_neg.2 (key y h), fun h => by simpa using key _ (Set.mem_neg.1 h)⟩

/-- A nonempty convex set with `K = −K` contains the origin (used in Corollary 2.3). -/
theorem zero_mem_of_symm {K : Set E} (hK : Convex ℝ K) (hne : K.Nonempty) (hsymm : K = -K) :
    (0 : E) ∈ K := by
  obtain ⟨x, hx⟩ := hne
  have hx' : -x ∈ K := by rw [hsymm] at hx; exact Set.mem_neg.1 hx
  have := hK hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa using this

end Komlos
