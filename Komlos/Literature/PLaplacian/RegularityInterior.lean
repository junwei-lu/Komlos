import Komlos.Literature.PLaplacian.RegularityMoserAux
import Komlos.Literature.PLaplacian.RegularitySchauder

/-!
# Interior regularity ladder for the first eigenfunction

Towards Mosconi–Riey–Squassina 2024, Proposition 4.5 (paper Appendix A, *Eigenfunction inputs*:
"Proposition 4.5 of [MRS24] gives positivity and `C^{1,α}` regularity up to the smooth boundary
for this nontrivial minimizer"), this file builds the De Giorgi–Nash–Moser chain for a nonnegative
weak solution `u ∈ W₀^{1,p}(K)` of the eigenvalue equation
`∫ ⟪a(∇u), ∇ψ⟫ = λ ∫ u^{p-1} ψ` (`a = flux p F`, all `ψ ∈ W₀^{1,p}(K)`).

## Main results

* `IsWeakEigensolution p F K λ u` — the hypotheses (a nonnegative `W₀^{1,p}(K)` solution tested
  against all of `W₀^{1,p}(K)`).
* `IsWeakEigensolution.integral_mul_test_eq` — testing with `ψ = ζ u` for smooth `ζ`:
  `∫ ζ F(∇u)^p + ∫ u ⟪a(∇u), ∇ζ⟫ = λ ∫ ζ u^p` (Euler's identity `⟪a(ξ), ξ⟫ = F(ξ)^p`).
* `IsWeakEigensolution.caccioppoli` — **the Caccioppoli energy estimate**: for a smooth compactly
  supported cutoff `η ≥ 0` and an integer `m ≥ p`,
  `∫ η^m F(∇u)^p ≤ 2λ ∫ η^m u^p + 2^p (m L)^p ∫ η^{m-p} ‖∇η‖^p u^p`, where `L` bounds `‖∇F‖`;
  `caccioppoli_norm` is the Euclidean form via `c ‖ξ‖ ≤ F(ξ)`.
* `IsWeakEigensolution.exists_ae_le` — **global boundedness by Moser iteration**, proved from the
  chain rule `memW0_comp` and the Sobolev inequality `sobolev_inequality`: testing with
  `G(u)` for the truncated powers of `RegularityMoserAux` gives the energy bound
  `c^p ∫ ‖∇H(u)‖^p ≤ max λ 1 · β^p ∫ H(u)^p` (`moser_energy`), Sobolev gives
  `‖u^β‖_{κp} ≤ C A β ‖u^β‖_p` (`moser_trunc`, `moser_step`, Fatou as the truncation level
  `→ ∞`), and iterating `β = κ^j` bounds `‖u‖_{p κ^j}` uniformly (`exists_iterate_bound`,
  `ae_le_of_eLpNorm_le`).

## `C²` off the critical set

* `contDiffOn_two_of_gradient_ne_zero` — `C²` off the critical set; its hypotheses are the
  conclusions of `holder_gradient` plus positivity. **Proved** in this file from the machinery of
  `RegularitySchauder` (ellipticity of `Da` away from `0`, the linearized equation of difference
  quotients, weak derivatives from uniformly Hölder difference quotients); the only cited input is
  the linear interior Schauder estimate `schauder_C2` (Gilbarg–Trudinger, Theorem 8.32).

Positivity (`weak_harnack_pos`, the weak Harnack inequality of Trudinger 1967) is **proved** in
`Komlos.Literature.PLaplacian.RegularityHarnack` from the Caccioppoli-type energy inequalities,
the Sobolev inequality and the Poincaré inequality of `RegularityPoincare`. Interior `C^{1,α}`
(`holder_gradient`) is in `Komlos.Literature.PLaplacian.RegularityHolder`: the Hölder continuity
of `u` (`holder_solution`, De Giorgi–Nash–Moser) is proved there and only the gradient step
(`holder_gradient_of_continuous`, DiBenedetto 1983, Tolksdorf 1984) is cited.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Weak eigensolutions -/

/-- A **nonnegative weak solution in `W₀^{1,p}(K)` of the eigenvalue equation**
`-div a(∇u) = λ u^{p-1}` (paper Appendix A, *Eigenfunction inputs*, the weak eigenfunction
equation with `a = flux p F`), tested against every `ψ ∈ W₀^{1,p}(K)`. The weak first
eigenfunction of `Regularity.lean` is one (`IsWeakFirstEigenfunction.isWeakEigensolution`). -/
structure IsWeakEigensolution (p : ℝ) (F : Euc d → ℝ) (K : Set (Euc d)) (lam : ℝ)
    (u : Euc d → ℝ) : Prop where
  /-- `u ∈ W₀^{1,p}(K)`. -/
  memW0 : MemW0 p K u
  /-- `u ≥ 0`. -/
  nonneg : ∀ x, 0 ≤ u x
  /-- The weak equation `∫ ⟪a(∇u), ∇ψ⟫ = λ ∫ u^{p-1} ψ` for all `ψ ∈ W₀^{1,p}(K)`. -/
  weakEq : ∀ ψ : Euc d → ℝ, MemW0 p K ψ →
    ∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ = lam * ∫ x, u x ^ (p - 1) * ψ x

/-! ### Integrability -/

/-- `∫ u^p < ∞` for a nonnegative `u ∈ L^p`. -/
theorem integrable_rpow_of_memLp_nonneg {p : ℝ} (hp0 : 0 < p) {u : Euc d → ℝ}
    (hu : MemLp u (ENNReal.ofReal p)) (hu0 : ∀ x, 0 ≤ u x) : Integrable fun x => u x ^ p := by
  refine (integrable_norm_rpow_of_memLp hp0 hu).congr (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (hu0 x)]

/-- `∫ F(G)^p < ∞` for `G ∈ L^p` (since `F ≤ M ‖·‖`). -/
theorem IsSmoothStrictNorm.integrable_rpow_comp {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    {p : ℝ} (hp0 : 0 < p) {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal p)) :
    Integrable fun x => F (G x) ^ p := by
  obtain ⟨M, hM⟩ := hF.exists_le_mul_norm
  refine ((integrable_norm_rpow_of_memLp hp0 hG).const_mul (max M 0 ^ p)).mono' ?_
    (Eventually.of_forall fun x => norm_rpow_le_of_le_mul_norm hF.nonneg hM hp0 (G x))
  exact (hF.continuous_rpow hp0.le).comp_aestronglyMeasurable hG.aestronglyMeasurable

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- The cross term `u ⟪a(∇u), V⟫` is integrable for bounded measurable `V`. -/
theorem integrable_mul_inner_flux (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {V : Euc d → Euc d}
    (hV : AEStronglyMeasurable V volume) {B : ℝ} (hB : ∀ x, ‖V x‖ ≤ B) :
    Integrable fun x => u x * ⟪flux p F (weakGrad u x), V x⟫ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨L, hL0, hL⟩ := hF.exists_norm_gradient_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hG := hu.memW0.memLp_weakGrad
  have hdom : Integrable fun x => L * B * (F (weakGrad u x) ^ p + u x ^ p) :=
    ((hF.integrable_rpow_comp hp0 hG).add
      (integrable_rpow_of_memLp_nonneg hp0 hu.memW0.memLp hu.nonneg)).const_mul (L * B)
  refine hdom.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact hu.memW0.memLp.aestronglyMeasurable.mul
      (((hF.continuous_flux' hp).comp_aestronglyMeasurable hG.aestronglyMeasurable).inner hV)
  · have h1 := hF.abs_inner_flux_le (p := p) hL (weakGrad u x) (V x)
    have h2 := rpow_sub_one_mul_le_add hp.le (hF.nonneg (weakGrad u x)) (hu.nonneg x)
    have hFp : 0 ≤ F (weakGrad u x) ^ (p - 1) := Real.rpow_nonneg (hF.nonneg _) _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hu.nonneg x)]
    calc u x * |⟪flux p F (weakGrad u x), V x⟫|
        ≤ u x * (L * F (weakGrad u x) ^ (p - 1) * B) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left (hB x)
            (mul_nonneg hL0 hFp))) (hu.nonneg x)
      _ = L * B * (F (weakGrad u x) ^ (p - 1) * u x) := by ring
      _ ≤ L * B * (F (weakGrad u x) ^ p + u x ^ p) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hL0 hB0)

/-- **Testing the eigenvalue equation with `ψ = ζ u`** for a smooth `ζ` with bounded values and
bounded gradient: `∫ ζ F(∇u)^p + ∫ u ⟪a(∇u), ∇ζ⟫ = λ ∫ ζ u^p`. -/
theorem integral_mul_test_eq (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) {A B : ℝ}
    (hA : ∀ x, |ζ x| ≤ A) (hB : ∀ x, ‖gradient ζ x‖ ≤ B) :
    (∫ x, ζ x * F (weakGrad u x) ^ p) + ∫ x, u x * ⟪flux p F (weakGrad u x), gradient ζ x⟫ =
      lam * ∫ x, ζ x * u x ^ p := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hψ, hψg⟩ := hu.memW0.contDiff_mul hζ hA hB
  have h := hu.weakEq _ hψ
  have i1 : Integrable fun x => ζ x * F (weakGrad u x) ^ p :=
    (hF.integrable_rpow_comp hp0 hu.memW0.memLp_weakGrad).bdd_mul
      hζ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hA x)
  have i2 : Integrable fun x => u x * ⟪flux p F (weakGrad u x), gradient ζ x⟫ :=
    hu.integrable_mul_inner_flux hp hF
      (continuous_gradient (hζ.of_le (by simp))).aestronglyMeasurable hB
  have e1 : ∫ x, ⟪flux p F (weakGrad u x), weakGrad (fun x => ζ x * u x) x⟫ =
      (∫ x, ζ x * F (weakGrad u x) ^ p) +
        ∫ x, u x * ⟪flux p F (weakGrad u x), gradient ζ x⟫ := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (hψg.mono fun x hx => ?_)
    simp only [hx, inner_add_right, real_inner_smul_right, hF.inner_flux_self_eq_rpow hp]
  have e2 : ∫ x, u x ^ (p - 1) * (ζ x * u x) = ∫ x, ζ x * u x ^ p := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show u x ^ (p - 1) * (ζ x * u x) = ζ x * u x ^ p
    have h1 : u x ^ (p - 1) * u x = u x ^ p := by
      rw [← Real.rpow_add_one' (hu.nonneg x) (ne_of_gt (by linarith)), sub_add_cancel]
    calc u x ^ (p - 1) * (ζ x * u x) = ζ x * (u x ^ (p - 1) * u x) := by ring
      _ = ζ x * u x ^ p := by rw [h1]
  rw [← e1, h, e2]

end IsWeakEigensolution

/-! ### The Caccioppoli estimate -/

/-- The pointwise inequality behind the Caccioppoli absorption: with `e = η(x)`, `Φ = F(∇u(x))`,
`U = u(x)`, `G = ‖∇η(x)‖` and `|I| ≤ L Φ^{p-1} G` (`I = ⟪a(∇u), ∇η⟫`),
`-U m e^{m-1} I ≤ e^m Φ^p / 2 + 2^{p-1} (m L)^p e^{m-p} G^p U^p` (Young with the splitting
`e^{m-1} = (e^{m/p})^{p-1} e^{m/p - 1}`). -/
theorem caccioppoli_pointwise {p : ℝ} (hp : 1 < p) {m : ℕ} (hm : p ≤ m) {e Φ U G I L : ℝ}
    (he : 0 ≤ e) (hΦ : 0 ≤ Φ) (hU : 0 ≤ U) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hI : |I| ≤ L * Φ ^ (p - 1) * G) :
    -(U * (((m : ℝ) * e ^ (m - 1)) * I)) ≤
      e ^ m * Φ ^ p / 2 +
        2 ^ (p - 1) * ((m : ℝ) * L) ^ p * (e ^ ((m : ℝ) - p) * G ^ p * U ^ p) := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hm1 : (1 : ℝ) < m := lt_of_lt_of_le hp hm
  have hm2 : 2 ≤ m := by
    have : 1 < m := by exact_mod_cast hm1
    omega
  have hmN : 1 ≤ m := by omega
  set s := e ^ ((m : ℝ) / p) with hs
  set c := e ^ ((m : ℝ) / p - 1) with hc
  have hs0 : 0 ≤ s := Real.rpow_nonneg he _
  have hc0 : 0 ≤ c := Real.rpow_nonneg he _
  have h1 : e ^ m = s ^ p := by
    rw [hs, ← Real.rpow_mul he, ← Real.rpow_natCast]
    congr 1
    field_simp
  have hexp : (m : ℝ) / p * (p - 1) + ((m : ℝ) / p - 1) = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmN, Nat.cast_one]
    field_simp
    ring
  have hne : (m : ℝ) / p * (p - 1) + ((m : ℝ) / p - 1) ≠ 0 := by
    rw [hexp]
    exact Nat.cast_ne_zero.2 (by omega)
  have h2 : e ^ (m - 1) = s ^ (p - 1) * c := by
    rw [hs, hc, ← Real.rpow_mul he, ← Real.rpow_add' he hne, hexp, Real.rpow_natCast]
  have h3 : e ^ ((m : ℝ) - p) = c ^ p := by
    rw [hc, ← Real.rpow_mul he]
    congr 1
    field_simp
  have hX : 0 ≤ U * ((m : ℝ) * e ^ (m - 1)) :=
    mul_nonneg hU (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg he _))
  have hmL : 0 ≤ (m : ℝ) * L := mul_nonneg (Nat.cast_nonneg m) hL
  have hmLc : 0 ≤ (m : ℝ) * L * c := mul_nonneg hmL hc0
  have hmLcU : 0 ≤ (m : ℝ) * L * c * U := mul_nonneg hmLc hU
  have hY := rpow_sub_one_mul_le_half_add hp (mul_nonneg hs0 hΦ) (mul_nonneg hmLcU hG)
  calc -(U * (((m : ℝ) * e ^ (m - 1)) * I))
      = U * ((m : ℝ) * e ^ (m - 1)) * (-I) := by ring
    _ ≤ U * ((m : ℝ) * e ^ (m - 1)) * (L * Φ ^ (p - 1) * G) :=
        mul_le_mul_of_nonneg_left ((neg_le_abs I).trans hI) hX
    _ = (s * Φ) ^ (p - 1) * ((m : ℝ) * L * c * U * G) := by
        rw [h2, Real.mul_rpow hs0 hΦ]
        ring
    _ ≤ (s * Φ) ^ p / 2 + 2 ^ (p - 1) * ((m : ℝ) * L * c * U * G) ^ p := hY
    _ = e ^ m * Φ ^ p / 2 +
          2 ^ (p - 1) * ((m : ℝ) * L) ^ p * (e ^ ((m : ℝ) - p) * G ^ p * U ^ p) := by
        rw [h1, h3, Real.mul_rpow hs0 hΦ, Real.mul_rpow hmLcU hG, Real.mul_rpow hmLc hU,
          Real.mul_rpow hmL hc0]
        ring

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- **The Caccioppoli energy estimate** for the eigenvalue equation (the first rung of the
De Giorgi–Nash–Moser ladder behind MRS24, Proposition 4.5; paper Appendix A, *Eigenfunction
inputs*). Let `η ≥ 0` be smooth with compact support, `m ≥ p` an integer and `L` a bound for
`‖∇F‖`. Testing the equation with `ψ = η^m u ∈ W₀^{1,p}(K)` gives
`∫ η^m F(∇u)^p + m ∫ η^{m-1} u ⟪a(∇u), ∇η⟫ = λ ∫ η^m u^p`, and absorbing the cross term by
Young's inequality (`caccioppoli_pointwise`) gives
`∫ η^m F(∇u)^p ≤ 2λ ∫ η^m u^p + 2^p (m L)^p ∫ η^{m-p} ‖∇η‖^p u^p`. -/
theorem caccioppoli (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {m : ℕ} (hm : p ≤ m) {η : Euc d → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) :
    ∫ x, η x ^ m * F (weakGrad u x) ^ p ≤
      2 * lam * (∫ x, η x ^ m * u x ^ p) +
        2 ^ p * ((m : ℝ) * L) ^ p * ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * u x ^ p := by
  have hp0 : 0 < p := by linarith
  have hm1 : (1 : ℝ) < m := lt_of_lt_of_le hp hm
  have hmpos : m ≠ 0 := by
    rintro rfl
    norm_num at hm1
  have hmp : 0 ≤ (m : ℝ) - p := sub_nonneg.2 hm
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hζ : ContDiff ℝ ∞ (fun x => η x ^ m) := hη.pow m
  have hζs : HasCompactSupport (fun x => η x ^ m) := by
    refine hηs.mono fun x hx h0 => hx ?_
    show η x ^ m = 0
    rw [h0, zero_pow hmpos]
  obtain ⟨A, hA⟩ := hζ.continuous.bounded_above_of_compact_support hζs
  obtain ⟨B, hB⟩ := (continuous_gradient (hζ.of_le (by simp))).bounded_above_of_compact_support
    (hasCompactSupport_gradient hζs)
  have hid := hu.integral_mul_test_eq hp hF hζ (A := A) (B := B)
    (fun x => by rw [← Real.norm_eq_abs]; exact hA x) hB
  -- the cross term
  have hcross : ∀ x, u x * ⟪flux p F (weakGrad u x), gradient (fun y => η y ^ m) x⟫ =
      u x * (((m : ℝ) * η x ^ (m - 1)) * ⟪flux p F (weakGrad u x), gradient η x⟫) := by
    intro x
    rw [gradient_pow_apply (hη1.differentiable one_ne_zero x) m, real_inner_smul_right]
  have hpt : ∀ x, -(u x * ⟪flux p F (weakGrad u x), gradient (fun y => η y ^ m) x⟫) ≤
      η x ^ m * F (weakGrad u x) ^ p / 2 + 2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
        (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * u x ^ p) := by
    intro x
    rw [hcross x]
    exact caccioppoli_pointwise hp hm (hη0 x) (hF.nonneg _) (hu.nonneg x) (norm_nonneg _) hL0
      (hF.abs_inner_flux_le hL _ _)
  -- integrability
  obtain ⟨Aη, hAη⟩ := hη.continuous.bounded_above_of_compact_support hηs
  obtain ⟨Bη, hBη⟩ := (continuous_gradient hη1).bounded_above_of_compact_support
    (hasCompactSupport_gradient hηs)
  have hup := integrable_rpow_of_memLp_nonneg hp0 hu.memW0.memLp hu.nonneg
  have i1 : Integrable fun x => η x ^ m * F (weakGrad u x) ^ p :=
    (hF.integrable_rpow_comp hp0 hu.memW0.memLp_weakGrad).bdd_mul
      hζ.continuous.aestronglyMeasurable (Eventually.of_forall hA)
  have i2 : Integrable fun x => u x * ⟪flux p F (weakGrad u x), gradient (fun y => η y ^ m) x⟫ :=
    hu.integrable_mul_inner_flux hp hF
      (continuous_gradient (hζ.of_le (by simp))).aestronglyMeasurable hB
  have i4 : Integrable fun x => η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * u x ^ p := by
    refine hup.bdd_mul (c := max Aη 0 ^ ((m : ℝ) - p) * max Bη 0 ^ p) ?_
      (Eventually.of_forall fun x => ?_)
    · exact ((hη.continuous.rpow_const fun _ => Or.inr hmp).mul
        ((continuous_gradient hη1).norm.rpow_const fun _ => Or.inr hp0.le)).aestronglyMeasurable
    · have ha : η x ≤ max Aη 0 :=
        (le_abs_self _).trans ((Real.norm_eq_abs (η x) ▸ hAη x).trans (le_max_left _ _))
      have hb : ‖gradient η x‖ ≤ max Bη 0 := (hBη x).trans (le_max_left _ _)
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hη0 x) _)
        (Real.rpow_nonneg (norm_nonneg _) _))]
      exact mul_le_mul (Real.rpow_le_rpow (hη0 x) ha hmp)
        (Real.rpow_le_rpow (norm_nonneg _) hb hp0.le) (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (le_max_right _ _) _)
  have hint : ∫ x, -(u x * ⟪flux p F (weakGrad u x), gradient (fun y => η y ^ m) x⟫) ≤
      ∫ x, (η x ^ m * F (weakGrad u x) ^ p / 2 + 2 ^ (p - 1) * ((m : ℝ) * L) ^ p *
        (η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * u x ^ p)) :=
    integral_mono i2.neg ((i1.div_const 2).add (i4.const_mul _)) hpt
  rw [integral_neg, integral_add (i1.div_const 2) (i4.const_mul _), integral_div,
    integral_const_mul] at hint
  have h2p : (2 : ℝ) ^ (p - 1) = 2 ^ p / 2 := Real.rpow_sub_one two_ne_zero p
  rw [h2p] at hint
  nlinarith [hid, hint]

/-- **The Caccioppoli estimate, Euclidean form**: with the ellipticity bound `c ‖ξ‖ ≤ F(ξ)`
(`IsSmoothStrictNorm.exists_pos_mul_norm_le'`),
`c^p ∫ η^m ‖∇u‖^p ≤ 2λ ∫ η^m u^p + 2^p (m L)^p ∫ η^{m-p} ‖∇η‖^p u^p`. -/
theorem caccioppoli_norm (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ ξ, ‖gradient F ξ‖ ≤ L) {m : ℕ} (hm : p ≤ m)
    {η : Euc d → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) :
    c ^ p * ∫ x, η x ^ m * ‖weakGrad u x‖ ^ p ≤
      2 * lam * (∫ x, η x ^ m * u x ^ p) +
        2 ^ p * ((m : ℝ) * L) ^ p * ∫ x, η x ^ ((m : ℝ) - p) * ‖gradient η x‖ ^ p * u x ^ p := by
  have hp0 : 0 < p := by linarith
  refine le_trans ?_ (hu.caccioppoli hp hF hL0 hL hm hη hηs hη0)
  have hζ : ContDiff ℝ ∞ (fun x => η x ^ m) := hη.pow m
  have hmpos : m ≠ 0 := by
    rintro rfl
    have := lt_of_lt_of_le hp hm
    norm_num at this
  have hζs : HasCompactSupport (fun x => η x ^ m) := by
    refine hηs.mono fun x hx h0 => hx ?_
    show η x ^ m = 0
    rw [h0, zero_pow hmpos]
  obtain ⟨A, hA⟩ := hζ.continuous.bounded_above_of_compact_support hζs
  have i1 : Integrable fun x => η x ^ m * F (weakGrad u x) ^ p :=
    (hF.integrable_rpow_comp hp0 hu.memW0.memLp_weakGrad).bdd_mul
      hζ.continuous.aestronglyMeasurable (Eventually.of_forall hA)
  have i0 : Integrable fun x => η x ^ m * ‖weakGrad u x‖ ^ p :=
    (integrable_norm_rpow_of_memLp hp0 hu.memW0.memLp_weakGrad).bdd_mul
      hζ.continuous.aestronglyMeasurable (Eventually.of_forall hA)
  rw [← integral_const_mul]
  refine integral_mono (i0.const_mul _) i1 fun x => ?_
  have hηm : 0 ≤ η x ^ m := pow_nonneg (hη0 x) m
  have h1 : c ^ p * ‖weakGrad u x‖ ^ p ≤ F (weakGrad u x) ^ p := by
    rw [← Real.mul_rpow hc.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (mul_nonneg hc.le (norm_nonneg _)) (hcF _) hp0.le
  calc c ^ p * (η x ^ m * ‖weakGrad u x‖ ^ p) = η x ^ m * (c ^ p * ‖weakGrad u x‖ ^ p) := by ring
    _ ≤ η x ^ m * F (weakGrad u x) ^ p := mul_le_mul_of_nonneg_left h1 hηm

/-! ### Global boundedness (Moser iteration) -/

/-- **The Moser energy bound** at truncation level `k > 0` for `β ≥ 1`: with the truncated power
`H = moserPow β k` and the test function `G = moserTest p β k` (`G' = (H')^p`), testing the
equation with `G(u) ∈ W₀^{1,p}(K)` gives `∫ F(∇H(u))^p = λ ∫ u^{p-1} G(u)`, hence
`c^p ∫ ‖∇H(u)‖^p ≤ max λ 1 · β^p ∫ H(u)^p` (`rpow_mul_moserTest_le`). Also `H(u) ∈ W₀^{1,p}(K)`. -/
theorem moser_energy (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ)
    {β k : ℝ} (hβ : 1 ≤ β) (hk : 0 < k) :
    MemW0 p K (fun x => moserPow β k (u x)) ∧
      c ^ p * ∫ x, ‖weakGrad (fun x => moserPow β k (u x)) x‖ ^ p ≤
        max lam 1 * β ^ p * ∫ x, moserPow β k (u x) ^ p := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hHw, hHg⟩ := memW0_comp hp hu.memW0 (contDiff_moserPow hβ) moserPow_zero
    (L := β * k ^ (β - 1)) fun t => by
      rw [deriv_moserPow hβ, abs_of_nonneg (moserDeriv_nonneg hβ hk.le t)]
      exact moserDeriv_le hβ hk.le t
  obtain ⟨hGw, hGg⟩ := memW0_comp hp hu.memW0 (contDiff_moserTest hβ hp0.le) moserTest_zero
    (L := (β * k ^ (β - 1)) ^ p) fun t => by
      simp only [deriv_moserTest hβ hp0.le]
      rw [abs_of_nonneg (Real.rpow_nonneg (moserDeriv_nonneg hβ hk.le t) _)]
      exact Real.rpow_le_rpow (moserDeriv_nonneg hβ hk.le t) (moserDeriv_le hβ hk.le t) hp0.le
  refine ⟨hHw, ?_⟩
  have hEq := hu.weakEq _ hGw
  have hmeasU := hu.memW0.memLp.aestronglyMeasurable
  have hHp : Integrable fun x => moserPow β k (u x) ^ p :=
    integrable_rpow_of_memLp_nonneg hp0 hHw.memLp fun x => moserPow_nonneg hβ hk.le (hu.nonneg x)
  -- the left-hand side of the tested equation
  have hL : ∫ x, ⟪flux p F (weakGrad u x), weakGrad (fun x => moserTest p β k (u x)) x⟫ =
      ∫ x, moserDeriv β k (u x) ^ p * F (weakGrad u x) ^ p := by
    refine integral_congr_ae (hGg.mono fun x hx => ?_)
    simp only [hx, deriv_moserTest hβ hp0.le, real_inner_smul_right,
      hF.inner_flux_self_eq_rpow hp]
  -- the energy of `H(u)`
  have hE : ∫ x, F (weakGrad (fun x => moserPow β k (u x)) x) ^ p =
      ∫ x, moserDeriv β k (u x) ^ p * F (weakGrad u x) ^ p := by
    refine integral_congr_ae (hHg.mono fun x hx => ?_)
    simp only [hx, deriv_moserPow hβ]
    exact hF.rpow_smul (moserDeriv_nonneg hβ hk.le _) _
  -- the right-hand side
  have hR : lam * ∫ x, u x ^ (p - 1) * moserTest p β k (u x) ≤
      max lam 1 * β ^ p * ∫ x, moserPow β k (u x) ^ p := by
    have hpt : ∀ x, u x ^ (p - 1) * moserTest p β k (u x) ≤ β ^ p * moserPow β k (u x) ^ p :=
      fun x => rpow_mul_moserTest_le hβ hk.le hp.le (hu.nonneg x)
    have hnn : ∀ x, 0 ≤ u x ^ (p - 1) * moserTest p β k (u x) := fun x =>
      mul_nonneg (Real.rpow_nonneg (hu.nonneg x) _) (moserTest_nonneg hβ hk.le (hu.nonneg x))
    have hmeas : AEStronglyMeasurable (fun x => u x ^ (p - 1) * moserTest p β k (u x)) volume :=
      ((continuous_id.rpow_const fun _ => Or.inr (by linarith)).comp_aestronglyMeasurable
        hmeasU).mul ((contDiff_moserTest hβ hp0.le).continuous.comp_aestronglyMeasurable hmeasU)
    have i2 : Integrable fun x => u x ^ (p - 1) * moserTest p β k (u x) :=
      (hHp.const_mul (β ^ p)).mono' hmeas (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hnn x)]
        exact hpt x)
    have h1 : lam * ∫ x, u x ^ (p - 1) * moserTest p β k (u x) ≤
        max lam 1 * ∫ x, u x ^ (p - 1) * moserTest p β k (u x) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg hnn)
    have h2 : ∫ x, u x ^ (p - 1) * moserTest p β k (u x) ≤
        β ^ p * ∫ x, moserPow β k (u x) ^ p := by
      rw [← integral_const_mul]
      exact integral_mono i2 (hHp.const_mul _) hpt
    calc lam * ∫ x, u x ^ (p - 1) * moserTest p β k (u x)
        ≤ max lam 1 * ∫ x, u x ^ (p - 1) * moserTest p β k (u x) := h1
      _ ≤ max lam 1 * (β ^ p * ∫ x, moserPow β k (u x) ^ p) :=
          mul_le_mul_of_nonneg_left h2 (zero_le_one.trans (le_max_right _ _))
      _ = max lam 1 * β ^ p * ∫ x, moserPow β k (u x) ^ p := by ring
  -- ellipticity
  have hcF' : c ^ p * ∫ x, ‖weakGrad (fun x => moserPow β k (u x)) x‖ ^ p ≤
      ∫ x, F (weakGrad (fun x => moserPow β k (u x)) x) ^ p := by
    rw [← integral_const_mul]
    refine integral_mono ((integrable_norm_rpow_of_memLp hp0 hHw.memLp_weakGrad).const_mul _)
      (hF.integrable_rpow_comp hp0 hHw.memLp_weakGrad) fun x => ?_
    show c ^ p * ‖weakGrad (fun x => moserPow β k (u x)) x‖ ^ p ≤
      F (weakGrad (fun x => moserPow β k (u x)) x) ^ p
    rw [← Real.mul_rpow hc.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (mul_nonneg hc.le (norm_nonneg _)) (hcF _) hp0.le
  calc c ^ p * ∫ x, ‖weakGrad (fun x => moserPow β k (u x)) x‖ ^ p
      ≤ ∫ x, F (weakGrad (fun x => moserPow β k (u x)) x) ^ p := hcF'
    _ = ∫ x, moserDeriv β k (u x) ^ p * F (weakGrad u x) ^ p := hE
    _ = lam * ∫ x, u x ^ (p - 1) * moserTest p β k (u x) := by rw [← hL, hEq]
    _ ≤ max lam 1 * β ^ p * ∫ x, moserPow β k (u x) ^ p := hR

/-- **One Moser step at a fixed truncation level**: given a Sobolev inequality
`‖w‖_{κp} ≤ C ‖∇w‖_p` on `W₀^{1,p}(K)`,
`‖H(u)‖_{κp} ≤ C A β ‖u^β‖_p` with `A = (c^{-p} max λ 1)^{1/p}` and `H = moserPow β k`. -/
theorem moser_trunc (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ)
    {κ : ℝ} {C : ℝ≥0∞}
    (hSob : ∀ w : Euc d → ℝ, MemW0 p K w →
      eLpNorm w (ENNReal.ofReal (κ * p)) ≤ C * eLpNorm (weakGrad w) (ENNReal.ofReal p))
    {β k : ℝ} (hβ : 1 ≤ β) (hk : 0 < k) :
    eLpNorm (fun x => moserPow β k (u x)) (ENNReal.ofReal (κ * p)) ≤
      C * ENNReal.ofReal ((c⁻¹ ^ p * max lam 1) ^ p⁻¹ * β) *
        eLpNorm (fun x => u x ^ β) (ENNReal.ofReal p) := by
  have hp0 : 0 < p := by linarith
  have hβ0 : 0 < β := by linarith
  have hY0 : 0 ≤ c⁻¹ ^ p * max lam 1 :=
    mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _) (zero_le_one.trans (le_max_right _ _))
  have hAβ : 0 ≤ (c⁻¹ ^ p * max lam 1) ^ p⁻¹ * β := mul_nonneg (Real.rpow_nonneg hY0 _) hβ0.le
  obtain ⟨hHw, hen⟩ := hu.moser_energy hp hF hc hcF hβ hk
  have hH0 : ∀ x, 0 ≤ moserPow β k (u x) := fun x => moserPow_nonneg hβ hk.le (hu.nonneg x)
  have hI0 : 0 ≤ ∫ x, moserPow β k (u x) ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (hH0 x) _
  have hen' : ∫ x, ‖weakGrad (fun x => moserPow β k (u x)) x‖ ^ p ≤
      c⁻¹ ^ p * max lam 1 * β ^ p * ∫ x, moserPow β k (u x) ^ p := by
    have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc p
    have hinv : c⁻¹ ^ p * c ^ p = 1 := by rw [Real.inv_rpow hc.le, inv_mul_cancel₀ hcp.ne']
    calc ∫ x, ‖weakGrad (fun x => moserPow β k (u x)) x‖ ^ p
        = c⁻¹ ^ p * (c ^ p * ∫ x, ‖weakGrad (fun x => moserPow β k (u x)) x‖ ^ p) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ c⁻¹ ^ p * (max lam 1 * β ^ p * ∫ x, moserPow β k (u x) ^ p) :=
          mul_le_mul_of_nonneg_left hen (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      _ = c⁻¹ ^ p * max lam 1 * β ^ p * ∫ x, moserPow β k (u x) ^ p := by ring
  have hgrad : eLpNorm (weakGrad (fun x => moserPow β k (u x))) (ENNReal.ofReal p) ≤
      ENNReal.ofReal ((c⁻¹ ^ p * max lam 1) ^ p⁻¹ * β) *
        eLpNorm (fun x => moserPow β k (u x)) (ENNReal.ofReal p) := by
    rw [eLpNorm_eq_ofReal_integral hp0 hHw.memLp_weakGrad, eLpNorm_eq_ofReal_integral hp0 hHw.memLp,
      ← ENNReal.ofReal_mul hAβ]
    refine ENNReal.ofReal_le_ofReal ?_
    have hnorm : ∫ x, ‖moserPow β k (u x)‖ ^ p = ∫ x, moserPow β k (u x) ^ p :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hH0 x)])
    rw [hnorm]
    calc (∫ x, ‖weakGrad (fun x => moserPow β k (u x)) x‖ ^ p) ^ p⁻¹
        ≤ (c⁻¹ ^ p * max lam 1 * β ^ p * ∫ x, moserPow β k (u x) ^ p) ^ p⁻¹ :=
          Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) hen'
            (inv_nonneg.2 hp0.le)
      _ = (c⁻¹ ^ p * max lam 1) ^ p⁻¹ * β * (∫ x, moserPow β k (u x) ^ p) ^ p⁻¹ := by
          rw [Real.mul_rpow (mul_nonneg hY0 (Real.rpow_nonneg hβ0.le _)) hI0,
            Real.mul_rpow hY0 (Real.rpow_nonneg hβ0.le _), Real.rpow_rpow_inv hβ0.le hp0.ne']
  have hmono : eLpNorm (fun x => moserPow β k (u x)) (ENNReal.ofReal p) ≤
      eLpNorm (fun x => u x ^ β) (ENNReal.ofReal p) := by
    refine eLpNorm_mono fun x => ?_
    rw [Real.norm_of_nonneg (hH0 x), Real.norm_of_nonneg (Real.rpow_nonneg (hu.nonneg x) _)]
    exact moserPow_le_rpow hβ hk.le (hu.nonneg x)
  refine (hSob _ hHw).trans ?_
  rw [mul_assoc]
  gcongr
  exact hgrad.trans (by gcongr)

/-- **One Moser step**: `‖u^β‖_{κp} ≤ C A β ‖u^β‖_p` for `β ≥ 1` (Fatou as the truncation level
`k = n + 1 → ∞`, `moserPow β k (u) → u^β`). -/
theorem moser_step (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ)
    {κ : ℝ} {C : ℝ≥0∞}
    (hSob : ∀ w : Euc d → ℝ, MemW0 p K w →
      eLpNorm w (ENNReal.ofReal (κ * p)) ≤ C * eLpNorm (weakGrad w) (ENNReal.ofReal p))
    {β : ℝ} (hβ : 1 ≤ β) :
    eLpNorm (fun x => u x ^ β) (ENNReal.ofReal (κ * p)) ≤
      C * ENNReal.ofReal ((c⁻¹ ^ p * max lam 1) ^ p⁻¹ * β) *
        eLpNorm (fun x => u x ^ β) (ENNReal.ofReal p) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x => moserPow β ((n : ℝ) + 1) (u x)) volume :=
    fun n => (contDiff_moserPow hβ).continuous.comp_aestronglyMeasurable
      hu.memW0.memLp.aestronglyMeasurable
  have hlim : ∀ᵐ x, Tendsto (fun n : ℕ => moserPow β ((n : ℝ) + 1) (u x)) atTop
      (𝓝 (u x ^ β)) :=
    Eventually.of_forall fun x => tendsto_moserPow hβ (hu.nonneg x)
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _ hlim).trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall fun n =>
    hu.moser_trunc hp hF hc hcF hSob hβ (by positivity))

end IsWeakEigensolution

/-- `‖u^β‖_{L^q} = ‖u‖_{L^{qβ}}^β` for `u ≥ 0` and `β > 0` (`eLpNorm_norm_rpow`). -/
theorem eLpNorm_rpow_eq_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    (hu0 : ∀ x, 0 ≤ u x) {β : ℝ} (hβ : 0 < β) (q : ℝ≥0∞) :
    eLpNorm (fun x => u x ^ β) q μ = eLpNorm u (q * ENNReal.ofReal β) μ ^ β := by
  have h : (fun x => u x ^ β) = fun x => ‖u x‖ ^ β :=
    funext fun x => by rw [Real.norm_of_nonneg (hu0 x)]
  rw [h]
  exact eLpNorm_norm_rpow u hβ

/-- A finite constant times `A κ^j` is at most `a κ^j` for some `a ≥ 1`. -/
theorem exists_one_le_mul_bound {C : ℝ≥0∞} (hC : C ≠ ⊤) {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ j : ℕ, C * ENNReal.ofReal (A * κ ^ j) ≤ ENNReal.ofReal (a * κ ^ j) := by
  refine ⟨max C.toReal 1 * max A 1,
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (le_max_right _ _), fun j => ?_⟩
  have h1 : C * ENNReal.ofReal (A * κ ^ j) = ENNReal.ofReal (C.toReal * (A * κ ^ j)) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_assoc]
  exact mul_le_mul (le_max_left _ _)
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hκ.le j))
    (mul_nonneg hA (pow_nonneg hκ.le j)) (zero_le_one.trans (le_max_right _ _))

namespace IsWeakEigensolution

variable {p : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {lam : ℝ} {u : Euc d → ℝ}

/-- **One Moser iteration step in exponent form**: with `β = κ^j` in `moser_step`,
`‖u‖_{pκ^{j+1}} ≤ (aκ)^{(j+1)κ^{-j}} ‖u‖_{pκ^j}`. -/
theorem moser_iterate_step (hp : 1 < p) (hF : IsSmoothStrictNorm F)
    (hu : IsWeakEigensolution p F K lam u) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ)
    {κ : ℝ} (hκ : 1 < κ) {C : ℝ≥0∞}
    (hSob : ∀ w : Euc d → ℝ, MemW0 p K w →
      eLpNorm w (ENNReal.ofReal (κ * p)) ≤ C * eLpNorm (weakGrad w) (ENNReal.ofReal p))
    {a : ℝ} (ha1 : 1 ≤ a)
    (haC : ∀ j : ℕ, C * ENNReal.ofReal ((c⁻¹ ^ p * max lam 1) ^ p⁻¹ * κ ^ j) ≤
      ENNReal.ofReal (a * κ ^ j))
    (j : ℕ) :
    eLpNorm u (ENNReal.ofReal (p * κ ^ (j + 1))) ≤
      ENNReal.ofReal ((a * κ) ^ (((j : ℝ) + 1) * κ⁻¹ ^ j)) *
        eLpNorm u (ENNReal.ofReal (p * κ ^ j)) := by
  have hp0 : 0 < p := by linarith
  have hκ0 : 0 < κ := by linarith
  have ha0 : 0 ≤ a := by linarith
  have haκ : 0 ≤ a * κ := mul_nonneg ha0 hκ0.le
  have hβ : (1 : ℝ) ≤ κ ^ j := one_le_pow₀ hκ.le
  have hβ0 : 0 < κ ^ j := pow_pos hκ0 j
  have h1 := hu.moser_step hp hF hc hcF hSob hβ
  have hexp : κ * p * κ ^ j = p * κ ^ (j + 1) := by ring
  have e1 : eLpNorm (fun x => u x ^ κ ^ j) (ENNReal.ofReal (κ * p)) =
      eLpNorm u (ENNReal.ofReal (p * κ ^ (j + 1))) ^ κ ^ j := by
    rw [eLpNorm_rpow_eq_of_nonneg hu.nonneg hβ0, ← ENNReal.ofReal_mul (mul_nonneg hκ0.le hp0.le),
      hexp]
  have e2 : eLpNorm (fun x => u x ^ κ ^ j) (ENNReal.ofReal p) =
      eLpNorm u (ENNReal.ofReal (p * κ ^ j)) ^ κ ^ j := by
    rw [eLpNorm_rpow_eq_of_nonneg hu.nonneg hβ0, ← ENNReal.ofReal_mul hp0.le]
  rw [e1, e2] at h1
  have hconst : C * ENNReal.ofReal ((c⁻¹ ^ p * max lam 1) ^ p⁻¹ * κ ^ j) ≤
      ENNReal.ofReal ((a * κ) ^ (j + 1)) := by
    refine (haC j).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_pow, pow_succ, pow_succ]
    exact mul_le_mul (le_mul_of_one_le_left ha0 (one_le_pow₀ ha1))
      (le_mul_of_one_le_right (pow_nonneg hκ0.le j) hκ.le) (pow_nonneg hκ0.le j)
      (mul_nonneg (pow_nonneg ha0 j) ha0)
  have h2 : eLpNorm u (ENNReal.ofReal (p * κ ^ (j + 1))) ^ κ ^ j ≤
      ENNReal.ofReal ((a * κ) ^ (j + 1)) * eLpNorm u (ENNReal.ofReal (p * κ ^ j)) ^ κ ^ j :=
    h1.trans (mul_le_mul_left hconst _)
  have h3 := le_ofReal_rpow_inv_mul_of_rpow_le hβ0 (pow_nonneg haκ _) h2
  have hpowD : ((a * κ) ^ (j + 1)) ^ (κ ^ j)⁻¹ = (a * κ) ^ (((j : ℝ) + 1) * κ⁻¹ ^ j) := by
    rw [← Real.rpow_natCast (a * κ) (j + 1), ← Real.rpow_mul haκ, ← inv_pow]
    simp only [Nat.cast_add, Nat.cast_one]
  rwa [hpowD] at h3

/-- **Global boundedness of weak eigensolutions** (Moser iteration; Gilbarg–Trudinger, Theorem
8.15; for the `p`-Laplacian eigenproblem e.g. Lindqvist, *A nonlinear eigenvalue problem*): a
nonnegative weak solution `u ∈ W₀^{1,p}(K)` of `-div a(∇u) = λ u^{p-1}` on a bounded set `K` is
essentially bounded. This is the `L^∞` input of `holder_gradient` and `boundary_regularity`.

Proof: `moser_iterate_step` (`moser_step` with `β = κ^j`) gives
`‖u‖_{pκ^{j+1}} ≤ D^{(j+1)κ^{-j}} ‖u‖_{pκ^j}` for a constant `D ≥ 1`; `exists_iterate_bound`
bounds all `‖u‖_{pκ^j}` by `B ‖u‖_p`, and `ae_le_of_eLpNorm_le` concludes. In dimension `0` the
space is a point. -/
theorem exists_ae_le (hp : 1 < p) (hF : IsSmoothStrictNorm F) (hK : Bornology.IsBounded K)
    (hu : IsWeakEigensolution p F K lam u) : ∃ M : ℝ, ∀ᵐ x, u x ≤ M := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨u 0, Eventually.of_forall fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
  have hd0 : 0 < d := Fin.pos_iff_nonempty.2 hd
  have hp0 : 0 < p := by linarith
  obtain ⟨c, hc, hcF⟩ := hF.exists_pos_mul_norm_le'
  obtain ⟨κ, hκ, C, hC, hSob⟩ := sobolev_inequality hd0 hp hK
  have hκ0 : 0 < κ := by linarith
  have hA0 : 0 ≤ (c⁻¹ ^ p * max lam 1) ^ p⁻¹ :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hc.le) _)
      (zero_le_one.trans (le_max_right _ _))) _
  obtain ⟨a, ha1, haC⟩ := exists_one_le_mul_bound hC hA0 hκ0
  -- an opaque name for the sequence of norms (unifying through a lambda here is very slow)
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℝ≥0∞, ∀ j, N j = eLpNorm u (ENNReal.ofReal (p * κ ^ j)) :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ j : ℕ, N (j + 1) ≤
      ENNReal.ofReal ((a * κ) ^ (((j : ℝ) + 1) * κ⁻¹ ^ j)) * N j := fun j => by
    rw [hN, hN]
    exact hu.moser_iterate_step hp hF hc hcF hκ hSob ha1 haC j
  obtain ⟨B, hB0, hB⟩ := exists_iterate_bound (one_le_mul_of_one_le_of_one_le ha1 hκ.le) hκ hstep
  have hN0 : N 0 ≠ ⊤ := by
    rw [hN, pow_zero, mul_one]
    exact hu.memW0.memLp.eLpNorm_ne_top
  have hbound : ∀ n : ℕ, eLpNorm u (ENNReal.ofReal (p * κ ^ n)) ≤
      ENNReal.ofReal (B * (N 0).toReal) := fun n => by
    rw [← hN n, ENNReal.ofReal_mul hB0, ENNReal.ofReal_toReal hN0]
    exact hB n
  exact ⟨B * (N 0).toReal,
    ae_le_of_eLpNorm_le hu.memW0.memLp.aestronglyMeasurable (q := fun n => p * κ ^ n)
      (fun n => mul_pos hp0 (pow_pos hκ0 n))
      ((tendsto_pow_atTop_atTop_of_one_lt hκ).const_mul_atTop hp0)
      (mul_nonneg hB0 ENNReal.toReal_nonneg) hbound⟩

end IsWeakEigensolution

/-! ### `C²` off the critical set -/

/-- **`C²` regularity off the critical set** (paper Appendix A, *Eigenfunction inputs*: "Where
`∇u_i ≠ 0`, the equation is locally uniformly elliptic with smooth coefficients, so local
elliptic regularity gives `u_i ∈ C²`"; Gilbarg–Trudinger, Theorem 8.32 and §8.11 (difference
quotients)): a positive `C^{1,α}` representative of a weak eigensolution is `C²` on the open set
where its gradient does not vanish. The hypotheses `hφ1`, `hφα` are the conclusions of
`holder_gradient` (`RegularityHolder.lean`), which precedes this step in `mrs_regularity_core`.

Proof: `φ` solves `∫ ⟪a(∇φ), ∇ψ⟫ = λ ∫ φ^{p-1} ψ` for smooth `ψ` supported in `K` (the weak
gradient of `u` is `∇φ` a.e. on `K`, `ae_gradient_eq_of_hasWeakGradient`). Near a point with
`∇φ ≠ 0`, the difference quotients of `φ` solve linear uniformly elliptic equations with Hölder
coefficients, and the cited Schauder estimate `schauder_C2` bounds their gradients uniformly in
`C^{0,α}` (`exists_holder_difference_gradient`); hence each partial derivative `∂_jφ` has
uniformly Hölder difference quotients and is `C¹` (`contDiffOn_of_holder_difference`), so `∇φ`
is `C¹` and `φ` is `C²`. -/
theorem contDiffOn_two_of_gradient_ne_zero {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsOpen K) {lam : ℝ} {u : Euc d → ℝ}
    (hu : IsWeakEigensolution p F K lam u) {φ : Euc d → ℝ} (hφu : φ =ᵐ[volume.restrict K] u)
    (hφ1 : ContDiffOn ℝ 1 φ K)
    (hφα : ∀ S : Set (Euc d), IsCompact S → S ⊆ K →
      ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r (gradient φ) S)
    (hφpos : ∀ x ∈ K, 0 < φ x) :
    ContDiffOn ℝ 2 φ (K ∩ {x | gradient φ x ≠ 0}) := by
  classical
  -- the weak equation with the classical gradient of `φ`
  obtain ⟨φ', hφ'⟩ : ∃ φ' : Euc d → ℝ, φ' = K.piecewise φ u := ⟨_, rfl⟩
  have hφ'u : φ' =ᵐ[volume] u := by
    rw [hφ']
    filter_upwards [(ae_restrict_iff' hK.measurableSet).1 hφu] with x hx
    by_cases hxK : x ∈ K
    · rw [piecewise_eq_of_mem _ _ _ hxK]
      exact hx hxK
    · rw [piecewise_eq_of_notMem _ _ _ hxK]
  have hφ'1 : ContDiffOn ℝ 1 φ' K :=
    hφ1.congr fun x hx => by rw [hφ', piecewise_eq_of_mem _ _ _ hx]
  have hgrad' : ∀ x ∈ K, gradient φ' x = gradient φ x := fun x hx => by
    have heq : φ' =ᶠ[𝓝 x] φ := by
      filter_upwards [hK.mem_nhds hx] with y hy
      rw [hφ', piecewise_eq_of_mem _ _ _ hy]
    unfold gradient
    rw [heq.fderiv_eq]
  have hae := ae_gradient_eq_of_hasWeakGradient hu.memW0.hasWeakGradient hφ'u hK hφ'1
  have hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ K →
      ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ = lam * ∫ x, φ x ^ (p - 1) * ψ x := by
    intro ψ hψ hψs hψK
    have h := hu.weakEq ψ (memW0_of_contDiff (hψ.of_le (by simp)) hψs hψK p)
    have e1 : ∫ x, ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ =
        ∫ x, ⟪flux p F (gradient φ x), gradient ψ x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [weakGrad_ae_eq_gradient (hψ.of_le (by simp)) hψs, hae] with x h1 h2
      show ⟪flux p F (weakGrad u x), weakGrad ψ x⟫ = ⟪flux p F (gradient φ x), gradient ψ x⟫
      rw [h1]
      by_cases hxK : x ∈ K
      · rw [← h2 hxK, hgrad' x hxK]
      · rw [gradient_eq_zero_of_notMem_tsupport fun h => hxK (hψK h), inner_zero_right,
          inner_zero_right]
    have e2 : ∫ x, u x ^ (p - 1) * ψ x = ∫ x, φ x ^ (p - 1) * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [(ae_restrict_iff' hK.measurableSet).1 hφu] with x hx
      show u x ^ (p - 1) * ψ x = φ x ^ (p - 1) * ψ x
      by_cases hxK : x ∈ K
      · rw [hx hxK]
      · rw [image_eq_zero_of_notMem_tsupport fun h => hxK (hψK h), mul_zero, mul_zero]
    rw [← e1, ← e2]
    exact h
  -- the partial derivatives of `φ` are `C¹` off the critical set
  have hgc : ContinuousOn (gradient φ) K :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      (hφ1.continuousOn_fderiv_of_isOpen hK le_rfl)
  have hVo : IsOpen (K ∩ {x | gradient φ x ≠ 0}) :=
    hgc.isOpen_inter_preimage hK isOpen_compl_singleton
  have hVK : K ∩ {x | gradient φ x ≠ 0} ⊆ K := inter_subset_left
  have hG : ∀ j : Fin d,
      ContDiffOn ℝ 1 (fun x => gradient φ x j) (K ∩ {x | gradient φ x ≠ 0}) := by
    intro j
    refine contDiffOn_of_holder_difference
      ((PiLp.continuous_apply 2 _ j).comp_continuousOn (hgc.mono hVK)) fun x hx => ?_
    obtain ⟨ρ, C, α, hρ, hα, hρV, hb⟩ := exists_holder_difference_gradient hp hF hVo
      (hφ1.mono hVK) (fun x hx => hφpos x (hVK hx)) (fun S hS hSV => hφα S hS (hSV.trans hVK))
      (fun ψ hψ hψs hψV => hweak ψ hψ hψs (hψV.trans hVK)) hx hx.2
    refine ⟨ρ, C, α, hρ, hα, hρV, fun i s hs hsρ y hy z hz => ?_⟩
    refine le_trans ?_ (hb i s hs hsρ y hy z hz)
    have h := PiLp.norm_apply_le
      ((gradient φ (y + s • EuclideanSpace.single i 1) - gradient φ y) -
        (gradient φ (z + s • EuclideanSpace.single i 1) - gradient φ z)) j
    simpa [Real.norm_eq_abs] using h
  have hgrad1 : ContDiffOn ℝ 1 (gradient φ) (K ∩ {x | gradient φ x ≠ 0}) :=
    contDiffOn_euclidean.2 hG
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ φ) (K ∩ {x | gradient φ x ≠ 0}) :=
    ((InnerProductSpace.toDual ℝ (Euc d)).contDiff.comp_contDiffOn hgrad1).congr
      fun x _ => toDual_gradient.symm
  exact (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hVo).2
    ⟨(hφ1.mono hVK).differentiableOn one_ne_zero, fun h => by simp at h, hfd⟩

end Komlos.Literature
