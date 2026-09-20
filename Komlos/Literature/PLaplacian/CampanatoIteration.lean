import Mathlib

/-!
# Quantitative Campanato iteration

This elementary iteration depends only on real analysis. Keeping it independent of
`RegularitySchauder` lets the data-dependent freezing argument use it before deriving
any uniform Schauder estimate, avoiding a circular import or theorem dependency.
-/

namespace Komlos.Literature

/-- **Campanato/Giaquinta iteration lemma, with a constant uniform in `Φ`** (Giaquinta–Martinazzi,
*An Introduction to the Regularity Theory for Elliptic Systems*, Lemma 5.13). This is
`campanato_iteration` below with the existential for the constant `c` pulled outside the
quantification over `Φ`: the constant produced by the proof depends only on `a`, `β` and `γ`, and a
Schauder estimate (one constant for a whole family of solutions) needs exactly that uniformity. -/
theorem campanato_iteration_constants {a β γ : ℝ} (ha : 0 ≤ a)
    (hβ : 0 ≤ β) (hβγ : β < γ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (b R₀ : ℝ), 0 ≤ b → 0 < R₀ →
      ∀ Φ : ℝ → ℝ, (∀ r, 0 ≤ Φ r) →
      (∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ → Φ ρ ≤ Φ r) →
      (∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ → Φ ρ ≤ a * (ρ / r) ^ γ * Φ r + b * r ^ β) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ R₀ → Φ ρ ≤ c * (Φ R₀ + b * R₀ ^ β) * (ρ / R₀) ^ β := by
  classical
  -- An intermediate exponent `β < δ < γ`.
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (β + γ) / 2 := ⟨_, rfl⟩
  have hβδ : β < δ := by rw [hδ]; linarith
  have hδγ : δ < γ := by rw [hδ]; linarith
  have hγδ : 0 < γ - δ := by linarith
  -- The contraction ratio `τ ∈ (0, 1)`, chosen so small that `a τ ^ γ ≤ τ ^ δ`.
  have ha1 : (0 : ℝ) < (a + 1)⁻¹ := by positivity
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = min (1 / 2) ((a + 1)⁻¹ ^ (γ - δ)⁻¹) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by
    rw [hτ]; exact lt_min (by norm_num) (Real.rpow_pos_of_pos ha1 _)
  have hτ1 : τ < 1 := by
    rw [hτ]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hτle : τ ≤ (a + 1)⁻¹ ^ (γ - δ)⁻¹ := by rw [hτ]; exact min_le_right _ _
  have hτδ : (0 : ℝ) < τ ^ δ := Real.rpow_pos_of_pos hτ0 _
  have hτβ : (0 : ℝ) < τ ^ β := Real.rpow_pos_of_pos hτ0 _
  have hτcontract : a * τ ^ γ ≤ τ ^ δ := by
    have h1 : τ ^ (γ - δ) ≤ (a + 1)⁻¹ := by
      calc τ ^ (γ - δ) ≤ ((a + 1)⁻¹ ^ (γ - δ)⁻¹) ^ (γ - δ) :=
            Real.rpow_le_rpow hτ0.le hτle hγδ.le
        _ = (a + 1)⁻¹ := Real.rpow_inv_rpow ha1.le hγδ.ne'
    have h4 : a * (a + 1)⁻¹ ≤ 1 := by
      have hpos : (0 : ℝ) < a + 1 := by linarith
      rw [← div_eq_mul_inv, div_le_one hpos]
      linarith
    have h2 : a * τ ^ (γ - δ) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left h1 ha) h4
    have hne : (τ : ℝ) ^ δ ≠ 0 := hτδ.ne'
    have h5 : τ ^ δ * τ ^ (γ - δ) = τ ^ γ := by
      rw [Real.rpow_sub hτ0]; field_simp
    calc a * τ ^ γ = τ ^ δ * (a * τ ^ (γ - δ)) := by rw [← h5]; ring
      _ ≤ τ ^ δ * 1 := mul_le_mul_of_nonneg_left h2 hτδ.le
      _ = τ ^ δ := mul_one _
  -- The geometric gain `τ ^ β - τ ^ δ > 0`, and the modified initial datum `S`.
  have hβδpow : τ ^ δ < τ ^ β := Real.rpow_lt_rpow_of_exponent_gt hτ0 hτ1 hβδ
  have hgap : (0 : ℝ) < τ ^ β - τ ^ δ := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (τ ^ β - τ ^ δ)⁻¹ := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; exact inv_pos.2 hgap
  -- Basic facts about the geometric sequence of radii `τ ^ k R₀`.
  have hτkpos : ∀ k : ℕ, (0 : ℝ) < τ ^ k := fun k => pow_pos hτ0 k
  have hτkle : ∀ k : ℕ, (τ : ℝ) ^ k ≤ 1 := fun _ => pow_le_one₀ hτ0.le hτ1.le
  -- The constant depends only on `a`, `β`, `γ`; fix it before quantifying over `Φ`.
  refine ⟨max 1 K / τ ^ β,
    div_nonneg (le_trans zero_le_one (le_max_left _ _)) hτβ.le, ?_⟩
  intro b R₀ hb hR₀ Φ hΦ0 hmono hdecay
  have hbR : 0 ≤ b * R₀ ^ β := mul_nonneg hb (Real.rpow_nonneg hR₀.le _)
  have hkR : ∀ k : ℕ, (τ : ℝ) ^ k * R₀ ≤ R₀ := fun k => by
    calc (τ : ℝ) ^ k * R₀ ≤ 1 * R₀ := mul_le_mul_of_nonneg_right (hτkle k) hR₀.le
      _ = R₀ := one_mul _
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Φ R₀ + K * (b * R₀ ^ β) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]; linarith [hΦ0 R₀, mul_nonneg hK0.le hbR]
  have hkey : b * R₀ ^ β ≤ (τ ^ β - τ ^ δ) * S := by
    have hne2 : τ ^ β - τ ^ δ ≠ 0 := hgap.ne'
    have hSge : K * (b * R₀ ^ β) ≤ S := by rw [hS]; linarith [hΦ0 R₀]
    have h1 : (τ ^ β - τ ^ δ) * (K * (b * R₀ ^ β)) = b * R₀ ^ β := by
      rw [hK]; field_simp
    calc b * R₀ ^ β = (τ ^ β - τ ^ δ) * (K * (b * R₀ ^ β)) := h1.symm
      _ ≤ (τ ^ β - τ ^ δ) * S := mul_le_mul_of_nonneg_left hSge hgap.le
  -- **The iteration.**
  have hind : ∀ k : ℕ, Φ (τ ^ k * R₀) ≤ (τ ^ k) ^ β * S := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, one_mul, Real.one_rpow]
      rw [hS]
      linarith [mul_nonneg hK0.le hbR]
    | succ k ih =>
      have hrpos : (0 : ℝ) < τ ^ k * R₀ := mul_pos (hτkpos k) hR₀
      have hρpos : (0 : ℝ) < τ ^ (k + 1) * R₀ := mul_pos (hτkpos (k + 1)) hR₀
      have hρr : (τ : ℝ) ^ (k + 1) * R₀ ≤ τ ^ k * R₀ :=
        mul_le_mul_of_nonneg_right (pow_right_anti₀ hτ0.le hτ1.le (Nat.le_succ k)) hR₀.le
      have hden : (τ : ℝ) ^ k * R₀ ≠ 0 := hrpos.ne'
      have hdiv : (τ : ℝ) ^ (k + 1) * R₀ / (τ ^ k * R₀) = τ := by
        rw [div_eq_iff hden]; ring
      have h1 := hdecay _ _ hρpos hρr (hkR k)
      rw [hdiv] at h1
      have h2 : ((τ : ℝ) ^ k * R₀) ^ β = (τ ^ k) ^ β * R₀ ^ β :=
        Real.mul_rpow (hτkpos k).le hR₀.le
      have h3 : ((τ : ℝ) ^ (k + 1)) ^ β = (τ ^ k) ^ β * τ ^ β := by
        rw [pow_succ]
        exact Real.mul_rpow (hτkpos k).le hτ0.le
      have h4 : a * τ ^ γ * Φ (τ ^ k * R₀) ≤ τ ^ δ * ((τ ^ k) ^ β * S) :=
        le_trans (mul_le_mul_of_nonneg_right hτcontract (hΦ0 _))
          (mul_le_mul_of_nonneg_left ih hτδ.le)
      have h5 : ((τ : ℝ) ^ k) ^ β * (τ ^ δ * S + b * R₀ ^ β) ≤ (τ ^ k) ^ β * (τ ^ β * S) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hτkpos k).le _)
        nlinarith [hkey]
      rw [h3]
      calc Φ ((τ : ℝ) ^ (k + 1) * R₀)
          ≤ a * τ ^ γ * Φ (τ ^ k * R₀) + b * ((τ : ℝ) ^ k * R₀) ^ β := h1
        _ ≤ τ ^ δ * ((τ ^ k) ^ β * S) + b * ((τ ^ k) ^ β * R₀ ^ β) := by rw [h2]; linarith
        _ = ((τ : ℝ) ^ k) ^ β * (τ ^ δ * S + b * R₀ ^ β) := by ring
        _ ≤ ((τ : ℝ) ^ k) ^ β * (τ ^ β * S) := h5
        _ = ((τ : ℝ) ^ k) ^ β * τ ^ β * S := by ring
  -- **Interpolation between the geometric radii.**
  intro ρ hρ hρR
  have hSmax : S ≤ max 1 K * (Φ R₀ + b * R₀ ^ β) := by
    have hm1 : (1 : ℝ) ≤ max 1 K := le_max_left _ _
    have h1 : Φ R₀ ≤ max 1 K * Φ R₀ := by nlinarith [hΦ0 R₀, hm1]
    have h2 : K * (b * R₀ ^ β) ≤ max 1 K * (b * R₀ ^ β) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hbR
    rw [hS]; linarith [h1, h2]
  have hex : ∃ n : ℕ, (τ : ℝ) ^ n * R₀ < ρ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hρ hR₀) hτ1
    rw [lt_div_iff₀ hR₀] at hn
    exact ⟨n, hn⟩
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, (τ : ℝ) ^ N * R₀ < ρ ∧
      ∀ m : ℕ, m < N → ¬((τ : ℝ) ^ m * R₀ < ρ) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ hm => Nat.find_min hex hm⟩
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hN1
    linarith
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = k + 1 := by
    cases N with
    | zero => exact absurd rfl hN0
    | succ k => exact ⟨k, rfl⟩
  have hk2 : ρ ≤ (τ : ℝ) ^ k * R₀ := not_lt.1 (hN2 k (by omega))
  have hΦk : Φ ρ ≤ ((τ : ℝ) ^ k) ^ β * S :=
    le_trans (hmono ρ (τ ^ k * R₀) hρ hk2 (hkR k)) (hind k)
  have hlow : ((τ : ℝ) ^ k) ^ β * τ ^ β ≤ (ρ / R₀) ^ β := by
    have h1 : (τ : ℝ) ^ (k + 1) ≤ ρ / R₀ := by
      rw [le_div_iff₀ hR₀]; exact hN1.le
    have h2 : ((τ : ℝ) ^ (k + 1)) ^ β ≤ (ρ / R₀) ^ β :=
      Real.rpow_le_rpow (pow_nonneg hτ0.le _) h1 hβ
    rwa [pow_succ, Real.mul_rpow (pow_nonneg hτ0.le k) hτ0.le] at h2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hτβ]
  calc Φ ρ * τ ^ β ≤ (((τ : ℝ) ^ k) ^ β * S) * τ ^ β :=
        mul_le_mul_of_nonneg_right hΦk hτβ.le
    _ = S * (((τ : ℝ) ^ k) ^ β * τ ^ β) := by ring
    _ ≤ S * (ρ / R₀) ^ β := mul_le_mul_of_nonneg_left hlow hS0
    _ ≤ max 1 K * (Φ R₀ + b * R₀ ^ β) * (ρ / R₀) ^ β :=
        mul_le_mul_of_nonneg_right hSmax (Real.rpow_nonneg (div_pos hρ hR₀).le _)

/-- Campanato iteration for a fixed forcing size and initial radius. The constant
comes from `campanato_iteration_constants`, so it is independent of both parameters. -/
theorem campanato_iteration_uniform {a b β γ R₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hβ : 0 ≤ β) (hβγ : β < γ) (hR₀ : 0 < R₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ Φ : ℝ → ℝ, (∀ r, 0 ≤ Φ r) →
      (∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ → Φ ρ ≤ Φ r) →
      (∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ → Φ ρ ≤ a * (ρ / r) ^ γ * Φ r + b * r ^ β) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ R₀ → Φ ρ ≤ c * (Φ R₀ + b * R₀ ^ β) * (ρ / R₀) ^ β := by
  obtain ⟨c, hc, h⟩ := campanato_iteration_constants ha hβ hβγ
  exact ⟨c, hc, h b R₀ hb hR₀⟩

/-- **Campanato/Giaquinta iteration lemma** (Giaquinta–Martinazzi, *An Introduction to the
Regularity Theory for Elliptic Systems*, Lemma 5.13; Giaquinta, *Multiple Integrals in the Calculus
of Variations*, Ch. III, Lemma 2.1): the elementary hole-filling step of the Campanato method
(Gilbarg–Trudinger, Theorem 8.32, step 3), independent of the elliptic problem. If a nonnegative,
monotone `Φ : ℝ → ℝ` obeys the perturbed decay `Φ ρ ≤ a (ρ / r) ^ γ * Φ r + b * r ^ β` for all
`0 < ρ ≤ r ≤ R₀` with the good exponent `γ` strictly larger than the data exponent `β ≥ 0`, then
`Φ ρ ≤ c (Φ R₀ + b R₀ ^ β) (ρ / R₀) ^ β` on `(0, R₀]`, with `c` depending only on `a, β, γ`. -/
theorem campanato_iteration {a b β γ R₀ : ℝ} (Φ : ℝ → ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hβ : 0 ≤ β) (hβγ : β < γ) (hR₀ : 0 < R₀) (hΦ0 : ∀ r, 0 ≤ Φ r)
    (hmono : ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ → Φ ρ ≤ Φ r)
    (hdecay : ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ → Φ ρ ≤ a * (ρ / r) ^ γ * Φ r + b * r ^ β) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ R₀ →
      Φ ρ ≤ c * (Φ R₀ + b * R₀ ^ β) * (ρ / R₀) ^ β := by
  obtain ⟨c, hc0, hc⟩ := campanato_iteration_uniform ha hb hβ hβγ hR₀
  exact ⟨c, hc0, hc Φ hΦ0 hmono hdecay⟩

end Komlos.Literature
