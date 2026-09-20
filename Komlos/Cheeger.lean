import Komlos.Variation

/-!
# The Cheeger value of a mixture and its Minkowski convexity (paper §3, Lemma 3.2)

* `cheeger_anti` — domain monotonicity `K ⊆ L → h_H(L) ≤ h_H(K)`;
* `mixtureEnergy_le_of_varBounded` — the cap (2.8) gives `E_H(ρ) ≤ κ`;
* `cheeger_lt_top` — `h_H(K) < ∞` on nonempty open sets.

Paper Lemma 3.2 (Minkowski convexity of `h_H`) is `Komlos.cheeger_minkowski`, in
`Komlos/Eigenvalue.lean`: it goes through the anisotropic `p`-eigenvalue and the limit
`p ↓ 1`, reducing to the single external input `Komlos.eigenvalue_convexity`
(Wang–Xia 2011, Theorem 1.2). See `SORRIES.md`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  {N : ℕ} {α : Fin N → ℝ} {u : Fin N → E}

/-- `𝒫(K) ⊆ 𝒫(L)` when `K ⊆ L`: only the support condition changes. -/
theorem MemP.mono {K L : Set E} (hKL : K ⊆ L) {ρ : E → ℝ} (hρ : MemP K ρ) : MemP L ρ where
  measurable := hρ.measurable
  nonneg := hρ.nonneg
  integrable := hρ.integrable
  integral_eq_one := hρ.integral_eq_one
  ae_zero_outside := hρ.ae_zero_outside.mono fun _ hx hxL => hx fun hxK => hxL (hKL hxK)
  dirVar_ne_top := hρ.dirVar_ne_top

/-- Domain monotonicity of `h_H` (paper, after (3.2)). -/
theorem cheeger_anti {K L : Set E} (hKL : K ⊆ L) : cheeger α u L ≤ cheeger α u K :=
  le_iInf₂ fun ρ hρ => iInf₂_le ρ (hρ.mono hKL)

/-- Under the cap (2.8), every mixture energy is at most `κ`. -/
theorem mixtureEnergy_le_of_varBounded (hmix : IsMixture α u) {κ : ℝ} {ρ : E → ℝ}
    (hρ : VarBounded κ ρ) : mixtureEnergy α u ρ ≤ ENNReal.ofReal κ := by
  unfold mixtureEnergy
  calc ∑ l, ENNReal.ofReal (α l) * dirVar (u l) ρ
      ≤ ∑ l, ENNReal.ofReal (α l) * ENNReal.ofReal κ := by
        refine Finset.sum_le_sum fun l _ => ?_
        gcongr
        simpa [hmix.norm_eq_one l] using hρ (u l)
    _ = ENNReal.ofReal κ := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun l _ => hmix.nonneg l,
          hmix.sum_eq_one, ENNReal.ofReal_one, one_mul]

/-- `h_H(K) ≤ E_H(ρ)` for every `ρ ∈ 𝒫(K)`. -/
theorem cheeger_le_mixtureEnergy {K : Set E} {ρ : E → ℝ} (hρ : MemP K ρ) :
    cheeger α u K ≤ mixtureEnergy α u ρ :=
  iInf₂_le ρ hρ

end General

section Euclidean

variable {d : ℕ} {N : ℕ} {α : Fin N → ℝ} {u : Fin N → Euc d}

/-- `h_H(K) < ∞` for nonempty open `K` (paper Lemma 3.4: "each nonempty section admits a
smooth compactly supported probability density"). -/
theorem cheeger_lt_top (hmix : IsMixture α u) {K : Set (Euc d)} (hK : IsOpen K)
    (hne : K.Nonempty) : cheeger α u K < ⊤ := by
  obtain ⟨ρ, hρ⟩ := exists_memP_of_isOpen hK hne
  refine (cheeger_le_mixtureEnergy hρ).trans_lt ?_
  unfold mixtureEnergy
  rw [ENNReal.sum_lt_top]
  intro l _
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hρ.dirVar_ne_top (u l)).lt_top

-- Paper Lemma 3.2 (Minkowski convexity) is `Komlos.cheeger_minkowski`, proved in
-- `Komlos/Eigenvalue.lean` via the `p ↓ 1` eigenvalue limit (it needs the eigenvalue
-- machinery, which imports this file).

end Euclidean

end Komlos
