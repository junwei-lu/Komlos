import Komlos.Transform

/-!
# From finite-step stability to full signings (paper Corollary 2.3, abstract form)

`Komlos.exists_signs_sum_mem_of_stable` is Corollary 2.3 with the stability step
(Proposition 2.2) abstracted into a predicate `good` on sets that is preserved by every
transform `𝒯_{v_j}`.  The concrete instance with `good K := HasAdmissible K κ` is
`Komlos.exists_signs_sum_mem` in `Komlos/Main.lean`.

The proof follows the paper: with `K_0 = K` and `K_j = 𝒯_{v_j} K_{j−1}` (here
`Komlos.iterTransform`), every `K_j` is `good` and symmetric, so `0 ∈ K_n`; the signs are
then chosen backwards, `z_{j−1} = z_j + ε_j v_j ∈ K_{j−1}`, using paper (2.11).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The iterated transform `K_n = 𝒯_{v_n} ⋯ 𝒯_{v_1} K` of paper Corollary 2.3 (the vector
`v 0` is applied first). -/
def iterTransform : {n : ℕ} → (Fin n → E) → Set E → Set E
  | 0, _, K => K
  | _ + 1, v, K => iterTransform (Fin.tail v) (transform (v 0) K)

@[simp] theorem iterTransform_zero (v : Fin 0 → E) (K : Set E) : iterTransform v K = K := rfl

@[simp] theorem iterTransform_succ {n : ℕ} (v : Fin (n + 1) → E) (K : Set E) :
    iterTransform v K = iterTransform (Fin.tail v) (transform (v 0) K) := rfl

/-- Symmetry `K = −K` is preserved along the iteration (paper Lemma 2.1, as used in the
proof of Corollary 2.3). -/
theorem iterTransform_neg_eq {n : ℕ} (v : Fin n → E) {K : Set E} (hK : K = -K) :
    iterTransform v K = -iterTransform v K := by
  induction n generalizing K with
  | zero => exact hK
  | succ n ih => exact ih (Fin.tail v) (transform_neg_eq hK (v 0))

/-- A predicate preserved by every transform `𝒯_{v_j}` is preserved along the iteration
(paper Corollary 2.3: "Proposition 2.2 applies at every stage"). -/
theorem good_iterTransform (good : Set E → Prop) {n : ℕ} (v : Fin n → E)
    (hstab : ∀ K, good K → ∀ j, (transform (v j) K).Nonempty ∧ good (transform (v j) K))
    {K : Set E} (hK : good K) : good (iterTransform v K) := by
  induction n generalizing K with
  | zero => exact hK
  | succ n ih => exact ih (Fin.tail v) (fun K hK j => hstab K hK j.succ) (hstab K hK 0).2

/-- The backwards sign selection of paper Corollary 2.3: every point `z` of the iterated
transform `K_n` can be brought back into `K` by adding a signed sum `∑ ε_j v_j`, choosing
`ε_n, …, ε_1` successively via paper (2.11). -/
theorem exists_signs_add_sum_mem_of_mem_iterTransform (good : Set E → Prop)
    (hgood : ∀ K, good K → IsGoodConvex K) {n : ℕ} (v : Fin n → E)
    (hstab : ∀ K, good K → ∀ j, (transform (v j) K).Nonempty ∧ good (transform (v j) K))
    {K : Set E} (hK : good K) {z : E} (hz : z ∈ iterTransform v K) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧ z + ∑ j, ε j • v j ∈ K := by
  induction n generalizing K z with
  | zero => exact ⟨fun _ => 1, fun j => j.elim0, by simpa using hz⟩
  | succ n ih =>
    obtain ⟨ε, hε, hmem⟩ :=
      ih (Fin.tail v) (fun K hK j => hstab K hK j.succ) (hstab K hK 0).2 hz
    have hsum : ∀ c : ℝ,
        z + ∑ j, (Fin.cons c ε : Fin (n + 1) → ℝ) j • v j
          = (z + ∑ j, ε j • Fin.tail v j) + c • v 0 := by
      intro c
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
      abel
    -- paper (2.11): `z + ∑_{j ≥ 1} ε_j v_j ∈ (K − v_0) ∪ (K + v_0)`
    rcases transform_subset_union (hgood K hK).convex (v 0) hmem with
      ⟨x, hx, hxz⟩ | ⟨x, hx, hxz⟩
    · -- `x − v 0 = z + ∑ …`: choose `ε_0 = 1`
      refine ⟨(Fin.cons 1 ε : Fin (n + 1) → ℝ), fun j => ?_, ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) j
        · exact Or.inl (Fin.cons_zero _ _)
        · rw [Fin.cons_succ]; exact hε i
      · rw [hsum, ← hxz, one_smul]
        simpa using hx
    · -- `x + v 0 = z + ∑ …`: choose `ε_0 = −1`
      refine ⟨(Fin.cons (-1) ε : Fin (n + 1) → ℝ), fun j => ?_, ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) j
        · exact Or.inr (Fin.cons_zero _ _)
        · rw [Fin.cons_succ]; exact hε i
      · rw [hsum, ← hxz, neg_one_smul]
        simpa using hx

/-- Paper Corollary 2.3 (abstract form).  If `good` implies "nonempty bounded open convex",
and every transform `𝒯_{v_j}` of a `good` set is nonempty and `good`, then for a symmetric
`good` set `K` there are signs with `∑ ε_j v_j ∈ K`. -/
theorem exists_signs_sum_mem_of_stable (good : Set E → Prop)
    (hgood : ∀ K, good K → IsGoodConvex K)
    {n : ℕ} (v : Fin n → E)
    (hstab : ∀ K, good K → ∀ j, (transform (v j) K).Nonempty ∧ good (transform (v j) K))
    {K : Set E} (hK : good K) (hsymm : K = -K) :
    ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧ ∑ j, ε j • v j ∈ K := by
  -- `K_n` is `good`, hence nonempty and convex, and symmetric, so `0 ∈ K_n`.
  have hgoodn : good (iterTransform v K) := good_iterTransform good v hstab hK
  have h0 : (0 : E) ∈ iterTransform v K :=
    zero_mem_of_symm (hgood _ hgoodn).convex (hgood _ hgoodn).nonempty
      (iterTransform_neg_eq v hsymm)
  obtain ⟨ε, hε, hmem⟩ :=
    exists_signs_add_sum_mem_of_mem_iterTransform good hgood v hstab hK h0
  exact ⟨ε, hε, by rwa [zero_add] at hmem⟩

end Komlos
