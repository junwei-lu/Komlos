import Komlos.Literature.Regularized.DeGiorgiNashAux

/-!
# De Giorgi classes at exponent `2`

This is the *abstract* half of lane `DGN` of `REGULARIZED_ROUTE.md` (Revision 2): the
De Giorgi–Nash–Moser theory is run once and for all on a class of functions defined by a
**level-set energy inequality**, and the concrete equations (the linear divergence-form
equation with bounded measurable coefficients of
`Komlos/Literature/Regularized/DeGiorgiNash.lean`, and the quasi-minima of
`∫ w² Ψ(∇w/w) + g(w)` of the regularity lane) only have to be shown to belong to that class.

## The class

`IsDGSub γ χ R₀ Ω z G` (De Giorgi's class `DG⁺(Ω, γ, χ)` at exponent `2`, in the normalization
of Ladyzhenskaya–Ural'tseva, *Linear and Quasilinear Elliptic Equations*, Ch. II §6, and
Giaquinta–Giusti, *On the regularity of the minima of variational integrals*, Acta Math. 148
(1982)) says: `G` is a weak gradient of `z`, both are locally square integrable, and for every
ball `closedBall x₀ s ⊆ Ω` with `s ≤ R₀`, every `0 < r < s` and every level `k ∈ ℝ`,

`∫_{B_r ∩ {z > k}} ‖G‖² ≤ γ (s - r)⁻² ∫_{B_s} ((z - k)_+)² + γ χ² |B_s ∩ {z > k}|`.   (DG)

(All three integrals are ordinary Bochner integrals; they converge because of the local
square-integrability field, and the real-valued form is what both the producers of the class
and the De Giorgi iteration manipulate.)

`IsDG γ χ R₀ Ω z G` requires `(DG)` for `z` and for `-z`.

Two design choices, both deliberate:

* the exponent on the measure term is **`1`**, not the `1 - 2/d + ε` of the
  Ladyzhenskaya–Ural'tseva class `B₂(Ω, M, γ, χ, 1/q, κ)`.  The larger exponent is what one
  gets from an `L^q` forcing term with `q < ∞`; for a **bounded** forcing (`‖f‖_∞ ≤ M`,
  `‖g‖_∞ < ∞`, the case of this lane) the exponent `1` comes out of the Caccioppoli
  computation directly, and it is what the De Giorgi iteration consumes.  Crucially, exponent
  `1` makes the class meaningful and the proofs uniform in **every** dimension `d ≥ 1`: the
  dimensional restriction `d ≥ 3` of the usual statements enters only through the Sobolev
  exponent, and the project's `exists_sobolev_ball` already supplies a Sobolev inequality with
  *some* `κ > 1` for every `d ≥ 1` (for `d = 1` it is the embedding into `L^∞`, for `d = 2` a
  Gagliardo–Nirenberg exponent, for `d ≥ 3` the sharp `κ = d/(d-2)`).  No statement below
  restricts `d`.
* the inequality is required for **all** levels `k`, not only `k ≥ k₀`.  Both the linear
  equation and the quasi-minimum functional satisfy it for all `k`.

The scale parameter `R₀` caps the radii for which `(DG)` is asserted; `χ` carries the size of
the lower-order data.  For the linear equation `-div(A ∇z) = -div f + g` on a ball of radius
`R₀`, one may take `χ = c(d, λ, Λ) (M + ‖g‖_∞ R₀)`, so that `χ R` is the `M R + ‖g‖_∞ R²` of
the target estimates whenever `R = R₀`.

## Main statements

* `exists_dg_step_const` — **one step** of the iteration (Caccioppoli + Sobolev + Hölder).
* `exists_dg_sup_bound` — **local boundedness** (De Giorgi's first lemma plus the iteration):
  `ess sup_{B_{R/2}} (z - k)_+ ≤ C ((⨍_{B_R} (z - k)_+²)^{1/2} + χ R)` with `C = C(d, γ)`.
Both are proved here.  The oscillation-decay half of the theory — `exists_dg_osc_decay`,
`exists_dg_holder_osc` and `IsDG.exists_holder_representative` — was stated here as named
`sorry`s until lane `reg/dgn-osc` proved it; it now lives in `DeGiorgiOsc*.lean`, and this
file no longer contains any placeholder.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### The class -/

/-- **De Giorgi's class `DG⁺(Ω, γ, χ)` at exponent `2` and scale `R₀`.**

`z` has weak gradient `G`, both are locally square integrable on `Ω`, and the level-set energy
inequality
`∫_{B_r ∩ {z > k}} ‖G‖² ≤ γ (s-r)⁻² ∫_{B_s} ((z-k)_+)² + γ χ² |B_s ∩ {z > k}|`
holds for all levels `k` and all concentric balls `B_r ⊂ B_s` with `closedBall x₀ s ⊆ Ω` and
`s ≤ R₀`.  Note `‖∇(z-k)_+‖ = ‖G‖ 1_{z > k}` a.e., so the left-hand side is the Dirichlet
energy of the truncation `(z-k)_+` on `B_r`. -/
structure IsDGSub (γ χ R₀ : ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d) : Prop where
  /-- `G` is a weak gradient of `z`. -/
  hasWeakGradient : HasWeakGradient z G
  /-- `z` is measurable (a representative has been chosen). -/
  measurable : Measurable z
  /-- `G` is measurable. -/
  measurable_grad : Measurable G
  /-- `z` and `G` are locally square integrable on `Ω`. -/
  integrableOn : ∀ (x₀ : Euc d) (s : ℝ), Metric.closedBall x₀ s ⊆ Ω →
    IntegrableOn (fun x => z x ^ 2) (Metric.closedBall x₀ s) volume ∧
      IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ s) volume
  /-- The level-set energy (Caccioppoli) inequality. -/
  energy : ∀ (x₀ : Euc d) (r s k : ℝ), 0 < r → r < s → s ≤ R₀ →
    Metric.closedBall x₀ s ⊆ Ω →
    (∫ x in Metric.ball x₀ r ∩ {x | k < z x}, ‖G x‖ ^ 2) ≤
      γ / (s - r) ^ 2 * (∫ x in Metric.ball x₀ s, max (z x - k) 0 ^ 2) +
        γ * χ ^ 2 * (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal

/-- **De Giorgi's class `DG(Ω, γ, χ)`**: both `z` and `-z` lie in `DG⁺(Ω, γ, χ)`.  Solutions of
a linear divergence-form equation lie in `DG`; sub-solutions lie in `DG⁺` only. -/
structure IsDG (γ χ R₀ : ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d) : Prop where
  /-- `z ∈ DG⁺`. -/
  sub : IsDGSub γ χ R₀ Ω z G
  /-- `-z ∈ DG⁺`. -/
  neg : IsDGSub γ χ R₀ Ω (fun x => -z x) (fun x => -G x)

namespace IsDGSub

variable {γ χ R₀ : ℝ} {Ω : Set (Euc d)} {z : Euc d → ℝ} {G : Euc d → Euc d}

/-- The class is monotone in the constants `γ` and `χ`. -/
theorem mono (h : IsDGSub γ χ R₀ Ω z G) {γ' χ' : ℝ} (hγ : 0 ≤ γ) (hγ' : γ ≤ γ')
    (hχ : 0 ≤ χ) (hχ' : χ ≤ χ') : IsDGSub γ' χ' R₀ Ω z G where
  hasWeakGradient := h.hasWeakGradient
  measurable := h.measurable
  measurable_grad := h.measurable_grad
  integrableOn := h.integrableOn
  energy x₀ r s k hr hrs hsR hball := by
    refine (h.energy x₀ r s k hr hrs hsR hball).trans (add_le_add ?_ ?_)
    · have hpos : (0 : ℝ) < (s - r) ^ 2 := by positivity
      have hI : 0 ≤ ∫ x in Metric.ball x₀ s, max (z x - k) 0 ^ 2 :=
        integral_nonneg fun x => sq_nonneg _
      have : γ / (s - r) ^ 2 ≤ γ' / (s - r) ^ 2 := by gcongr
      exact mul_le_mul_of_nonneg_right this hI
    · have hm : (0 : ℝ) ≤ (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal :=
        ENNReal.toReal_nonneg
      have h1 : γ * χ ^ 2 ≤ γ' * χ ^ 2 := mul_le_mul_of_nonneg_right hγ' (sq_nonneg χ)
      have h2 : χ ^ 2 ≤ χ' ^ 2 := by nlinarith
      have h3 : γ' * χ ^ 2 ≤ γ' * χ' ^ 2 := mul_le_mul_of_nonneg_left h2 (hγ.trans hγ')
      exact mul_le_mul_of_nonneg_right (by linarith) hm

/-- The class only depends on `Ω` through the balls it contains: it is monotone under
shrinking the domain. -/
theorem mono_domain (h : IsDGSub γ χ R₀ Ω z G) {Ω' : Set (Euc d)} (hΩ : Ω' ⊆ Ω) :
    IsDGSub γ χ R₀ Ω' z G where
  hasWeakGradient := h.hasWeakGradient
  measurable := h.measurable
  measurable_grad := h.measurable_grad
  integrableOn x₀ s hs := h.integrableOn x₀ s (hs.trans hΩ)
  energy x₀ r s k hr hrs hsR hball := h.energy x₀ r s k hr hrs hsR (hball.trans hΩ)

/-- The class is monotone in the scale `R₀`. -/
theorem mono_scale (h : IsDGSub γ χ R₀ Ω z G) {R₁ : ℝ} (hR : R₁ ≤ R₀) :
    IsDGSub γ χ R₁ Ω z G where
  hasWeakGradient := h.hasWeakGradient
  measurable := h.measurable
  measurable_grad := h.measurable_grad
  integrableOn := h.integrableOn
  energy x₀ r s k hr hrs hsR hball := h.energy x₀ r s k hr hrs (hsR.trans hR) hball

end IsDGSub

/-! ### One step of the De Giorgi iteration -/

set_option maxHeartbeats 2000000 in
/-- **One step of the De Giorgi iteration for the class `DG⁺`.**  For concentric balls
`B_ρ ⊂ B_σ` well inside `B_R` and any level `k`,

`∫_{B_ρ} (z-k)_+² ≤ C R^{2-dθ} ( (σ-ρ)^{-2} ∫_{B_σ} (z-k)_+² + χ² |A| ) |A|^θ`,

where `A = B_σ ∩ {z > k}` and `θ ∈ (0,1)`, `C` depend only on `d` and `γ`.

Proof: test with `v = η (z-k)_+` (`memW0_cutoff_posPart`); `‖∇v‖² ≤ 2η²1_{z>k}‖G‖² + 2(z-k)_+²‖∇η‖²`,
the first term is controlled by the `(DG)` inequality at the intermediate radius
`ρ'' = ρ + 2(σ-ρ)/3` and the second by `‖∇η‖ ≤ 3C_c/(σ-ρ)`; then `exists_sobolev_holder_ball`
on the set `A`, on which `v` agrees with `(z-k)_+` over `B_ρ`. -/
theorem exists_dg_step_const (hd : 0 < d) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Cst : ℝ, 0 < Cst ∧
      ∀ (χ R₀ : ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
        0 ≤ χ → IsDGSub γ χ R₀ Ω z G →
      ∀ (x₀ : Euc d) (R : ℝ), 0 < R → R ≤ R₀ → Metric.closedBall x₀ R ⊆ Ω →
      ∀ (ρ σ : ℝ), 0 < ρ → ρ < σ → σ ≤ 15 * R / 16 → ∀ k : ℝ,
      (∫ x in Metric.ball x₀ ρ, max (z x - k) 0 ^ 2) ≤
        Cst * R ^ (2 - (d : ℝ) * θ) *
          ((σ - ρ)⁻¹ ^ 2 * (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2) +
            χ ^ 2 * (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal) *
          (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal ^ θ := by
  obtain ⟨θ, hθ0, hθ1, CS, hCS, hSH⟩ := exists_sobolev_holder_ball hd
  obtain ⟨Cc, hCc, hcut⟩ := exists_cutoff_const d
  have hM : (0:ℝ) < 18 * γ + 18 * Cc ^ 2 := by nlinarith [mul_pos hCc hCc]
  refine ⟨θ, hθ0, hθ1, CS * (18 * γ + 18 * Cc ^ 2), mul_pos hCS hM, ?_⟩
  intro χ R₀ Ω z G hχ hz x₀ R hR hRR₀ hball ρ σ hρ hρσ hσ k
  have hsr : (0:ℝ) < σ - ρ := by linarith
  have hσR : σ < R := by linarith
  have hρ'ρ'' : ρ + (σ - ρ) / 3 < ρ + 2 * (σ - ρ) / 3 := by linarith
  have hρρ' : ρ < ρ + (σ - ρ) / 3 := by linarith
  have hρ''σ : ρ + 2 * (σ - ρ) / 3 < σ := by linarith
  have hρ''R : ρ + 2 * (σ - ρ) / 3 < R := by linarith
  have hρ''0 : (0:ℝ) < ρ + 2 * (σ - ρ) / 3 := by linarith
  obtain ⟨η, hηC, hηcs, hηsupp, hη0, hη1, hηone, hηgrad⟩ :=
    hcut x₀ ρ (ρ + (σ - ρ) / 3) hρ hρρ'
  obtain ⟨ζ, hζC, hζcs, hζsupp, hζ0, hζ1, hζone, hζgrad⟩ :=
    hcut x₀ (ρ + 2 * (σ - ρ) / 3) R hρ''0 hρ''R
  have hηg' : ∀ x, ‖gradient η x‖ ≤ 3 * Cc / (σ - ρ) := by
    intro x
    refine (hηgrad x).trans (le_of_eq ?_)
    have he : ρ + (σ - ρ) / 3 - ρ = (σ - ρ) / 3 := by ring
    rw [he, div_div_eq_mul_div]
    ring
  obtain ⟨hz2, hG2⟩ := hz.integrableOn x₀ R hball
  have hzm : AEStronglyMeasurable z volume := hz.measurable.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G volume := hz.measurable_grad.aestronglyMeasurable
  have hζabs : ∀ x, |ζ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hζ0 x], hζ1 x⟩
  obtain ⟨hv, hvg⟩ := memW0_cutoff_posPart hρ'ρ'' hρ''R.le hz.hasWeakGradient hzm hGm hz2 hG2
    hηC hηcs hηsupp hζC hζcs hζsupp hζabs hζone k
  -- measurability and elementary facts
  have hindm : Measurable (fun x => if k < z x then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const hz.measurable) measurable_const
      measurable_const
  have hwm : Measurable (fun x => max (z x - k) 0) :=
    (hz.measurable.sub measurable_const).max measurable_const
  have hηcont : Continuous η := hηC.continuous
  have hη1C : ContDiff ℝ 1 η := hηC.of_le (by simp)
  have hgηcont : Continuous (gradient η) := continuous_gradient hη1C
  have hSm : MeasurableSet (Metric.ball x₀ σ ∩ {x | k < z x}) :=
    measurableSet_ball.inter (measurableSet_lt measurable_const hz.measurable)
  have hS'm : MeasurableSet (Metric.ball x₀ (ρ + 2 * (σ - ρ) / 3) ∩ {x | k < z x}) :=
    measurableSet_ball.inter (measurableSet_lt measurable_const hz.measurable)
  have hSfin : volume (Metric.ball x₀ σ ∩ {x | k < z x}) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top).ne
  have hA0 : (0:ℝ) ≤ (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal := ENNReal.toReal_nonneg
  have hIσ0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hηzero : ∀ x, x ∉ tsupport η → η x = 0 ∧ gradient η x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx, gradient_eq_zero_of_notMem_tsupport hx⟩
  have hηball : tsupport η ⊆ Metric.ball x₀ (ρ + 2 * (σ - ρ) / 3) := by
    intro x hx
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.1 (hηsupp hx)) hρ'ρ''
  have hηballσ : tsupport η ⊆ Metric.ball x₀ σ := fun x hx =>
    Metric.ball_subset_ball hρ''σ.le (hηball hx)
  have hηballR : tsupport η ⊆ Metric.closedBall x₀ R := fun x hx =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) (hηball hx))
  have hw2 : ∀ x, max (z x - k) 0 ^ 2 ≤ 2 * z x ^ 2 + 2 * k ^ 2 := by
    intro x
    have h1 : max (z x - k) 0 ≤ |z x| + |k| := by
      refine max_le ?_ (by positivity)
      have := le_abs_self (z x)
      have := neg_abs_le k
      linarith
    nlinarith [le_max_right (z x - k) (0:ℝ), abs_nonneg (z x), abs_nonneg k, sq_abs (z x),
      sq_abs k, sq_nonneg (|z x| - |k|)]
  have hQ0 : (0:ℝ) ≤ 3 * Cc / (σ - ρ) := by positivity
  -- integrability of the three energy integrands
  have hE1int : Integrable
      (fun x => η x ^ 2 * (if k < z x then (1:ℝ) else 0) * ‖G x‖ ^ 2) volume := by
    refine integrable_of_bound_on_ball hz2 hG2 ?_ 1 0 0 ?_ ?_
    · exact (((hηcont.pow 2).aestronglyMeasurable).mul hindm.aestronglyMeasurable).mul
        (hGm.norm.pow 2)
    · refine Eventually.of_forall fun x _ => ?_
      have hi : (0:ℝ) ≤ (if k < z x then (1:ℝ) else 0) ∧
          (if k < z x then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
      have hnn : (0:ℝ) ≤ η x ^ 2 * (if k < z x then (1:ℝ) else 0) * ‖G x‖ ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hi.1) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hη2 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
      have hprod : η x ^ 2 * (if k < z x then (1:ℝ) else 0) ≤ 1 := by
        nlinarith [hη2, hi.1, hi.2, sq_nonneg (η x)]
      have hprod0 : (0:ℝ) ≤ η x ^ 2 * (if k < z x then (1:ℝ) else 0) :=
        mul_nonneg (sq_nonneg _) hi.1
      nlinarith [hprod, hprod0, sq_nonneg ‖G x‖]
    · intro x hx
      obtain ⟨h1, _⟩ := hηzero x fun h => hx (hηballR h)
      simp [h1]
  have hE2int : Integrable
      (fun x => max (z x - k) 0 ^ 2 * ‖gradient η x‖ ^ 2) volume := by
    refine integrable_of_bound_on_ball hz2 hG2 ?_ 0
      (2 * (3 * Cc / (σ - ρ)) ^ 2) (2 * (3 * Cc / (σ - ρ)) ^ 2 * k ^ 2) ?_ ?_
    · exact ((hwm.pow_const 2).aestronglyMeasurable).mul
        ((hgηcont.norm.pow 2).aestronglyMeasurable)
    · refine Eventually.of_forall fun x _ => ?_
      have hnn : (0:ℝ) ≤ max (z x - k) 0 ^ 2 * ‖gradient η x‖ ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hq2 : ‖gradient η x‖ ^ 2 ≤ (3 * Cc / (σ - ρ)) ^ 2 := by
        nlinarith [hηg' x, norm_nonneg (gradient η x), hQ0]
      nlinarith [hw2 x, sq_nonneg (max (z x - k) 0), sq_nonneg (3 * Cc / (σ - ρ)),
        mul_nonneg (sq_nonneg (max (z x - k) 0)) (sq_nonneg (3 * Cc / (σ - ρ)))]
    · intro x hx
      obtain ⟨_, h2⟩ := hηzero x fun h => hx (hηballR h)
      simp [h2]
  have hvLp : MemLp (fun x => η x * max (z x - k) 0) 2 volume := by
    have h := hv.memLp
    rwa [dgn_ofReal_two] at h
  have hvgLp : MemLp (weakGrad (fun x => η x * max (z x - k) 0)) 2 volume := by
    have h := hv.memLp_weakGrad
    rwa [dgn_ofReal_two] at h
  have hvgint : Integrable
      (fun x => ‖weakGrad (fun y => η y * max (z y - k) 0) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hvgLp.aestronglyMeasurable).1 hvgLp
  -- `‖∇v‖² ≤ 2 η² 1_{z>k} ‖G‖² + 2 (z-k)_+² ‖∇η‖²`
  have hgradbd : ∀ᵐ x, ‖weakGrad (fun y => η y * max (z y - k) 0) x‖ ^ 2 ≤
      2 * (η x ^ 2 * (if k < z x then (1:ℝ) else 0) * ‖G x‖ ^ 2)
        + 2 * (max (z x - k) 0 ^ 2 * ‖gradient η x‖ ^ 2) := by
    filter_upwards [hvg] with x hx
    rw [hx]
    have hind2 : (if k < z x then (1:ℝ) else 0) ^ 2 = (if k < z x then (1:ℝ) else 0) := by
      split <;> norm_num
    have hA1 : ‖(η x * (if k < z x then (1:ℝ) else 0)) • G x‖ ^ 2
        = η x ^ 2 * (if k < z x then (1:ℝ) else 0) * ‖G x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow, hind2]
    have hA2 : ‖max (z x - k) 0 • gradient η x‖ ^ 2
        = max (z x - k) 0 ^ 2 * ‖gradient η x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hn := norm_add_le ((η x * (if k < z x then (1:ℝ) else 0)) • G x)
      (max (z x - k) 0 • gradient η x)
    nlinarith [hn, hA1, hA2,
      norm_nonneg ((η x * (if k < z x then (1:ℝ) else 0)) • G x),
      norm_nonneg (max (z x - k) 0 • gradient η x),
      norm_nonneg ((η x * (if k < z x then (1:ℝ) else 0)) • G x
        + max (z x - k) 0 • gradient η x),
      sq_nonneg (‖(η x * (if k < z x then (1:ℝ) else 0)) • G x‖
        - ‖max (z x - k) 0 • gradient η x‖)]
  have hRint : Integrable
      (fun x => 2 * (η x ^ 2 * (if k < z x then (1:ℝ) else 0) * ‖G x‖ ^ 2)
        + 2 * (max (z x - k) 0 ^ 2 * ‖gradient η x‖ ^ 2)) volume :=
    (hE1int.const_mul 2).add (hE2int.const_mul 2)
  have hEsum : (∫ x, ‖weakGrad (fun y => η y * max (z y - k) 0) x‖ ^ 2) ≤
      2 * (∫ x, η x ^ 2 * (if k < z x then (1:ℝ) else 0) * ‖G x‖ ^ 2)
        + 2 * (∫ x, max (z x - k) 0 ^ 2 * ‖gradient η x‖ ^ 2) := by
    have hsum := integral_mono_ae hvgint hRint hgradbd
    rwa [integral_add (hE1int.const_mul 2) (hE2int.const_mul 2), integral_const_mul,
      integral_const_mul] at hsum
  have hw2int : IntegrableOn (fun x => max (z x - k) 0 ^ 2) (Metric.ball x₀ σ) volume := by
    have hbase : IntegrableOn (fun x => 2 * z x ^ 2 + 2 * k ^ 2) (Metric.ball x₀ σ) volume :=
      ((hz2.mono_set (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall hσR.le))).const_mul 2).add
        (integrableOn_const (C := 2 * k ^ 2) measure_ball_lt_top.ne)
    refine Integrable.mono' hbase ((hwm.pow_const 2).aestronglyMeasurable.restrict)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hw2 x
  -- the `‖G‖²` term via the De Giorgi inequality
  have hE1 : (∫ x, η x ^ 2 * (if k < z x then (1:ℝ) else 0) * ‖G x‖ ^ 2) ≤
      9 * γ / (σ - ρ) ^ 2 * (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2)
        + γ * (χ ^ 2 * (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal) := by
    have hdg := hz.energy x₀ (ρ + 2 * (σ - ρ) / 3) σ k hρ''0 hρ''σ (le_trans hσR.le hRR₀)
      ((Metric.closedBall_subset_closedBall hσR.le).trans hball)
    have he : σ - (ρ + 2 * (σ - ρ) / 3) = (σ - ρ) / 3 := by ring
    rw [he] at hdg
    have hdiv : γ / ((σ - ρ) / 3) ^ 2 = 9 * γ / (σ - ρ) ^ 2 := by
      field_simp
      ring
    rw [hdiv] at hdg
    have hindint : Integrable ((Metric.ball x₀ (ρ + 2 * (σ - ρ) / 3) ∩ {x | k < z x}).indicator
        (fun y => ‖G y‖ ^ 2)) volume := by
      rw [integrable_indicator_iff hS'm]
      exact hG2.mono_set (Set.inter_subset_left.trans (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall (by linarith))))
    have hptw : ∀ x, η x ^ 2 * (if k < z x then (1:ℝ) else 0) * ‖G x‖ ^ 2 ≤
        (Metric.ball x₀ (ρ + 2 * (σ - ρ) / 3) ∩ {x | k < z x}).indicator
          (fun y => ‖G y‖ ^ 2) x := by
      intro x
      by_cases hxη : x ∈ tsupport η
      · by_cases hkz : k < z x
        · have hmem : x ∈ Metric.ball x₀ (ρ + 2 * (σ - ρ) / 3) ∩ {x | k < z x} :=
            ⟨hηball hxη, hkz⟩
          rw [Set.indicator_of_mem hmem, if_pos hkz, mul_one]
          have hη2 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
          nlinarith [sq_nonneg ‖G x‖, sq_nonneg (η x)]
        · rw [if_neg hkz, mul_zero, zero_mul]
          exact Set.indicator_nonneg (fun y _ => sq_nonneg _) x
      · obtain ⟨h1, _⟩ := hηzero x hxη
        rw [h1]
        have h0 : (0:ℝ) ≤ (Metric.ball x₀ (ρ + 2 * (σ - ρ) / 3) ∩ {x | k < z x}).indicator
            (fun y => ‖G y‖ ^ 2) x := Set.indicator_nonneg (fun y _ => sq_nonneg _) x
        simpa using h0
    have h1 := integral_mono_ae hE1int hindint (Eventually.of_forall hptw)
    rw [integral_indicator hS'm] at h1
    linarith [h1, hdg]
  -- the `‖∇η‖²` term
  have hE2 : (∫ x, max (z x - k) 0 ^ 2 * ‖gradient η x‖ ^ 2) ≤
      9 * Cc ^ 2 / (σ - ρ) ^ 2 * (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2) := by
    have hQsq : (3 * Cc / (σ - ρ)) ^ 2 = 9 * Cc ^ 2 / (σ - ρ) ^ 2 := by
      field_simp
      ring
    have hindint : Integrable ((Metric.ball x₀ σ).indicator
        (fun y => (3 * Cc / (σ - ρ)) ^ 2 * max (z y - k) 0 ^ 2)) volume := by
      rw [integrable_indicator_iff measurableSet_ball]
      exact hw2int.const_mul _
    have hptw : ∀ x, max (z x - k) 0 ^ 2 * ‖gradient η x‖ ^ 2 ≤
        (Metric.ball x₀ σ).indicator
          (fun y => (3 * Cc / (σ - ρ)) ^ 2 * max (z y - k) 0 ^ 2) x := by
      intro x
      by_cases hxη : x ∈ tsupport η
      · rw [Set.indicator_of_mem (hηballσ hxη)]
        have hq2 : ‖gradient η x‖ ^ 2 ≤ (3 * Cc / (σ - ρ)) ^ 2 := by
          nlinarith [hηg' x, norm_nonneg (gradient η x), hQ0]
        nlinarith [sq_nonneg (max (z x - k) 0), hq2]
      · obtain ⟨_, h2⟩ := hηzero x hxη
        rw [h2]
        have h0 : (0:ℝ) ≤ (Metric.ball x₀ σ).indicator
            (fun y => (3 * Cc / (σ - ρ)) ^ 2 * max (z y - k) 0 ^ 2) x :=
          Set.indicator_nonneg (fun y _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) x
        simpa using h0
    have h1 := integral_mono_ae hE2int hindint (Eventually.of_forall hptw)
    rw [integral_indicator measurableSet_ball, integral_const_mul, hQsq] at h1
    exact h1
  -- the left-hand side is bounded by the integral of `v²` over `A`
  have hvsq : Integrable (fun x => (η x * max (z x - k) 0) ^ 2) volume :=
    (memLp_two_iff_integrable_sq hvLp.aestronglyMeasurable).1 hvLp
  have hlow : (∫ x in Metric.ball x₀ ρ, max (z x - k) 0 ^ 2) ≤
      ∫ x in Metric.ball x₀ σ ∩ {x | k < z x}, (η x * max (z x - k) 0) ^ 2 := by
    have hlhs : Integrable ((Metric.ball x₀ ρ).indicator
        (fun y => max (z y - k) 0 ^ 2)) volume := by
      rw [integrable_indicator_iff measurableSet_ball]
      exact hw2int.mono_set (Metric.ball_subset_ball hρσ.le)
    have hptw2 : ∀ x, (Metric.ball x₀ ρ).indicator (fun y => max (z y - k) 0 ^ 2) x ≤
        (Metric.ball x₀ σ ∩ {x | k < z x}).indicator
          (fun y => (η y * max (z y - k) 0) ^ 2) x := by
      intro x
      by_cases hxρ : x ∈ Metric.ball x₀ ρ
      · by_cases hkz : k < z x
        · have hmem : x ∈ Metric.ball x₀ σ ∩ {x | k < z x} :=
            ⟨Metric.ball_subset_ball hρσ.le hxρ, hkz⟩
          rw [Set.indicator_of_mem hxρ, Set.indicator_of_mem hmem,
            hηone x (Metric.ball_subset_closedBall hxρ), one_mul]
        · rw [Set.indicator_of_mem hxρ, max_eq_right (by linarith [not_lt.1 hkz])]
          have h0 : (0:ℝ) ≤ (Metric.ball x₀ σ ∩ {x | k < z x}).indicator
              (fun y => (η y * max (z y - k) 0) ^ 2) x :=
            Set.indicator_nonneg (fun y _ => sq_nonneg _) x
          simpa using h0
      · rw [Set.indicator_of_notMem hxρ]
        exact Set.indicator_nonneg (fun y _ => sq_nonneg _) x
    have h2 := integral_mono_ae hlhs (hvsq.indicator hSm) (Eventually.of_forall hptw2)
    rwa [integral_indicator measurableSet_ball, integral_indicator hSm] at h2
  -- assemble
  have hinvsq : (σ - ρ)⁻¹ ^ 2 = 1 / (σ - ρ) ^ 2 := by rw [inv_pow, ← one_div]
  have hT2nn : (0:ℝ) ≤ χ ^ 2 * (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal :=
    mul_nonneg (sq_nonneg _) hA0
  have hgradfin : (∫ x, ‖weakGrad (fun y => η y * max (z y - k) 0) x‖ ^ 2) ≤
      (18 * γ + 18 * Cc ^ 2) * ((σ - ρ)⁻¹ ^ 2 *
        (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2)
          + χ ^ 2 * (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal) := by
    have he1 : 9 * γ / (σ - ρ) ^ 2 * (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2)
        = 9 * γ * ((σ - ρ)⁻¹ ^ 2 *
          (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2)) := by
      rw [hinvsq]; ring
    have he2 : 9 * Cc ^ 2 / (σ - ρ) ^ 2 * (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2)
        = 9 * Cc ^ 2 * ((σ - ρ)⁻¹ ^ 2 *
          (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2)) := by
      rw [hinvsq]; ring
    rw [he1] at hE1
    rw [he2] at hE2
    set T1 : ℝ := (σ - ρ)⁻¹ ^ 2 * (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2) with hT1def
    set T2 : ℝ := χ ^ 2 * (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal with hT2def
    nlinarith [hEsum, hE1, hE2, mul_nonneg hγ hT2nn, mul_nonneg (sq_nonneg Cc) hT2nn]
  have hSHv := hSH x₀ R hR (fun x => η x * max (z x - k) 0) hv
    (Metric.ball x₀ σ ∩ {x | k < z x}) hSm hSfin
  have hRpow : (0:ℝ) ≤ R ^ (2 - (d:ℝ) * θ) := Real.rpow_nonneg hR.le _
  have hAθ : (0:ℝ) ≤ (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal ^ θ :=
    Real.rpow_nonneg hA0 _
  have hfinal : (∫ x in Metric.ball x₀ ρ, max (z x - k) 0 ^ 2) ≤
      CS * R ^ (2 - (d:ℝ) * θ) *
        ((18 * γ + 18 * Cc ^ 2) * ((σ - ρ)⁻¹ ^ 2 *
          (∫ x in Metric.ball x₀ σ, max (z x - k) 0 ^ 2)
            + χ ^ 2 * (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal)) *
        (volume (Metric.ball x₀ σ ∩ {x | k < z x})).toReal ^ θ := by
    refine hlow.trans (hSHv.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgradfin (mul_nonneg hCS.le hRpow)) hAθ
  refine hfinal.trans (le_of_eq ?_)
  ring

/-! ### Local boundedness -/

set_option maxHeartbeats 2000000 in
/-- **Local boundedness in the De Giorgi class** (De Giorgi 1957; Ladyzhenskaya–Ural'tseva,
Ch. II, Theorem 6.1; Giaquinta–Giusti, Theorem 4.1): a function of `DG⁺(Ω, γ, χ)` is
essentially bounded above on the half ball, with

`ess sup_{B_{R/2}} (z - k)_+ ≤ C ((⨍_{B_R} (z - k)_+ ²)^{1/2} + χ R)`,

and a constant `C` depending **only on `d` and `γ`** (uniform in `χ`, `R₀`, `Ω`, `z`, `G`, `k`,
`x₀` and `R`), which is why the quantifiers are ordered as below.

Proof (the De Giorgi iteration): with levels `k_n = k + H(1 - 2^{-n})` and radii
`r_n = R/2 + (R/4) 2^{-n}` (so `r_0 = 3R/4 ↓ R/2`), `exists_dg_step_const` at the pair
`(r_{n+1}, r_n)` and the level `k_{n+1}`, Chebyshev
(`|{z > k_{n+1}} ∩ B_{r_n}| ≤ 4^{n+1} Y_n / H²`, using the level jump `k_{n+1} - k_n = H 2^{-n-1}`)
and `H ≥ χ R` give, for `Y_n = ∫_{B_{r_n}} (z - k_n)_+²`,

`Y_{n+1} ≤ C R^{2-dθ} (68 · 4ⁿ Y_n / R²) (4^{n+1} Y_n / H²)^θ`.

Dividing by `R^d H²` (`dg_rescale_identity`) turns this into
`Ỹ_{n+1} ≤ (68 · 4^θ C) (4^{1+θ})ⁿ Ỹ_n^{1+θ}` for `Ỹ_n = Y_n / (R^d H²)`, whose constant no
longer involves `R` or `H`; `tendsto_zero_of_degiorgi_fast_convergence` then gives `Y_n → 0`
as soon as `Ỹ_0` is below the absolute threshold, which is exactly
`H ≥ c₆ (⨍_{B_R} (z-k)_+²)^{1/2}`.  Taking `H = χ R + c₆ (⨍…)^{1/2} + t` and letting `t ↓ 0`
gives the statement. -/
theorem exists_dg_sup_bound (hd : 0 < d) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ R₀ : ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
      0 ≤ χ → IsDGSub γ χ R₀ Ω z G →
      ∀ (x₀ : Euc d) (R : ℝ), 0 < R → R ≤ R₀ → Metric.closedBall x₀ R ⊆ Ω → ∀ k : ℝ,
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
        z x ≤ k + C * (Real.sqrt (⨍ y in Metric.ball x₀ R, max (z y - k) 0 ^ 2) + χ * R) := by
  obtain ⟨θ, hθ0, hθ1, Cst, hCst, hstepL⟩ := exists_dg_step_const hd hγ
  -- the constants of the iteration
  have hbb1 : (1:ℝ) < (4:ℝ) ^ (1 + θ) :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2 (Or.inl ⟨by norm_num, by linarith⟩)
  have hA₀0 : (0:ℝ) < 68 * 4 ^ θ * Cst := by positivity
  have hc₅0 : (0:ℝ) <
      (68 * 4 ^ θ * Cst) ^ (-θ⁻¹) * ((4:ℝ) ^ (1 + θ)) ^ (-(θ ^ 2)⁻¹) := by positivity
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.1 hd
  have hVd0 : (0:ℝ) < (volume (Metric.ball (0:Euc d) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  refine ⟨max (Real.sqrt ((volume (Metric.ball (0:Euc d) 1)).toReal /
      ((68 * 4 ^ θ * Cst) ^ (-θ⁻¹) * ((4:ℝ) ^ (1 + θ)) ^ (-(θ ^ 2)⁻¹)))) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro χ R₀ Ω z G hχ hz x₀ R hR hRR₀ hball k
  set A₀ : ℝ := 68 * 4 ^ θ * Cst with hA₀def
  set bb : ℝ := (4:ℝ) ^ (1 + θ) with hbbdef
  set c₅ : ℝ := A₀ ^ (-θ⁻¹) * bb ^ (-(θ ^ 2)⁻¹) with hc₅def
  set Vd : ℝ := (volume (Metric.ball (0:Euc d) 1)).toReal with hVddef
  set c₆ : ℝ := Real.sqrt (Vd / c₅) with hc₆def
  have hc₆0 : (0:ℝ) ≤ c₆ := Real.sqrt_nonneg _
  set avg : ℝ := ⨍ y in Metric.ball x₀ R, max (z y - k) 0 ^ 2 with havgdef
  -- integrability of the truncations on balls
  obtain ⟨hz2, hG2⟩ := hz.integrableOn x₀ R hball
  have hwm : Measurable (fun x => z x - k) := hz.measurable.sub measurable_const
  have hwint : ∀ (c s : ℝ), s ≤ R →
      IntegrableOn (fun x => max (z x - c) 0 ^ 2) (Metric.ball x₀ s) volume := by
    intro c s hs
    have hbase : IntegrableOn (fun x => 2 * z x ^ 2 + 2 * c ^ 2) (Metric.ball x₀ s) volume :=
      ((hz2.mono_set (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall hs))).const_mul 2).add
        (integrableOn_const (C := 2 * c ^ 2) measure_ball_lt_top.ne)
    refine Integrable.mono' hbase
      (((((hz.measurable.sub measurable_const).max measurable_const).pow_const
        2).aestronglyMeasurable).restrict) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : max (z x - c) 0 ≤ |z x| + |c| := by
      refine max_le ?_ (by positivity)
      have := le_abs_self (z x)
      have := neg_abs_le c
      linarith
    nlinarith [le_max_right (z x - c) (0:ℝ), abs_nonneg (z x), abs_nonneg c, sq_abs (z x),
      sq_abs c, sq_nonneg (|z x| - |c|)]
  have havg0 : (0:ℝ) ≤ avg := by
    rw [havgdef, setAverage_eq, smul_eq_mul, Measure.real]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x => sq_nonneg _)
  -- `∫_{B_R} (z-k)_+² = avg * R^d * Vd`
  have hvolR : volume.real (Metric.ball x₀ R) = R ^ d * Vd := by
    rw [Measure.real, hVddef, Measure.addHaar_ball volume x₀ hR.le, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hY0up : (∫ x in Metric.ball x₀ R, max (z x - k) 0 ^ 2) = avg * (R ^ d * Vd) := by
    rw [havgdef, setAverage_eq, smul_eq_mul, hvolR]
    have hne : (R ^ d * Vd) ≠ 0 := by positivity
    field_simp
  have hpow4 : ∀ m : ℕ, ((1 / 2 : ℝ) ^ m) ^ 2 * 4 ^ m = 1 := by
    intro m
    rw [← pow_mul, mul_comm m 2, pow_mul, ← mul_pow]
    norm_num
  -- the core estimate: for every admissible height `H`, `z ≤ k + H` a.e. on the half ball
  have hcore : ∀ H : ℝ, 0 < H → χ * R ≤ H → avg * Vd ≤ c₅ * H ^ 2 →
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))), z x ≤ k + H := by
    intro H hH0 hHχ hsmall
    set rr : ℕ → ℝ := fun n => R / 2 + R / 4 * (1 / 2 : ℝ) ^ n with hrrdef
    set kk : ℕ → ℝ := fun n => k + H * (1 - (1 / 2 : ℝ) ^ n) with hkkdef
    set Y : ℕ → ℝ := fun n => ∫ x in Metric.ball x₀ (rr n), max (z x - kk n) 0 ^ 2 with hYdef
    set D : ℝ := R ^ d * H ^ 2 with hDdef
    have hD0 : (0:ℝ) < D := by rw [hDdef]; positivity
    set Yt : ℕ → ℝ := fun n => Y n / D with hYtdef
    have hhalf : ∀ n : ℕ, (0:ℝ) < (1 / 2 : ℝ) ^ n := fun n => by positivity
    have hhalf1 : ∀ n : ℕ, (1 / 2 : ℝ) ^ n ≤ 1 := fun n =>
      pow_le_one₀ (by norm_num) (by norm_num)
    have hrrlb : ∀ n, R / 2 < rr n := fun n => by
      simp only [hrrdef]; nlinarith [hhalf n]
    have hrrub : ∀ n, rr n ≤ 3 * R / 4 := fun n => by
      simp only [hrrdef]; nlinarith [hhalf1 n]
    have hrrdiff : ∀ n : ℕ, rr n - rr (n + 1) = R / 8 * (1 / 2 : ℝ) ^ n := fun n => by
      simp only [hrrdef]; ring
    have hrrdec : ∀ n : ℕ, rr (n + 1) < rr n := fun n => by
      have h := hrrdiff n; nlinarith [hhalf n]
    have hkkdiff : ∀ n : ℕ, kk (n + 1) - kk n = H * (1 / 2 : ℝ) ^ (n + 1) := fun n => by
      simp only [hkkdef]; ring
    have hkkle : ∀ n, kk n ≤ k + H := fun n => by
      simp only [hkkdef]; nlinarith [hhalf n]
    have hkkmono : ∀ n, kk n ≤ kk (n + 1) := fun n => by
      have := hkkdiff n; have := mul_pos hH0 (hhalf (n + 1)); linarith
    have hYnn : ∀ n, 0 ≤ Y n := fun n => integral_nonneg fun x => sq_nonneg _
    have hYtnn : ∀ n, 0 ≤ Yt n := fun n => div_nonneg (hYnn n) hD0.le
    have hYmono : ∀ n, (∫ x in Metric.ball x₀ (rr n), max (z x - kk (n + 1)) 0 ^ 2) ≤ Y n := by
      intro n
      refine integral_mono_ae (hwint (kk (n + 1)) (rr n) (by linarith [hrrub n]))
        (hwint (kk n) (rr n) (by linarith [hrrub n])) (Eventually.of_forall fun x => ?_)
      have hle : max (z x - kk (n + 1)) 0 ≤ max (z x - kk n) 0 :=
        max_le_max (by linarith [hkkmono n]) le_rfl
      nlinarith [le_max_right (z x - kk (n + 1)) (0:ℝ), le_max_right (z x - kk n) (0:ℝ)]
    -- Chebyshev on the level set
    have hcheb : ∀ n : ℕ,
        (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal *
          (kk (n + 1) - kk n) ^ 2 ≤ Y n := by
      intro n
      have hSm : MeasurableSet (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x}) :=
        measurableSet_ball.inter (measurableSet_lt measurable_const hz.measurable)
      have hSfin : volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x}) ≠ ⊤ :=
        (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top).ne
      have hrrR : rr n ≤ R := by linarith [hrrub n]
      have h1 : (∫ _x in Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x},
            (kk (n + 1) - kk n) ^ 2)
          ≤ ∫ x in Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x}, max (z x - kk n) 0 ^ 2 := by
        refine setIntegral_mono_on (integrableOn_const hSfin)
          ((hwint (kk n) (rr n) hrrR).mono_set Set.inter_subset_left) hSm (fun x hx => ?_)
        have hkz : kk (n + 1) < z x := hx.2
        have h2 : kk (n + 1) - kk n ≤ max (z x - kk n) 0 :=
          le_max_of_le_left (by linarith)
        have h3 : (0:ℝ) ≤ kk (n + 1) - kk n := by
          have := hkkdiff n; have := mul_pos hH0 (hhalf (n + 1)); linarith
        nlinarith [h2, h3]
      have h2 : (∫ x in Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x},
            max (z x - kk n) 0 ^ 2) ≤ Y n := by
        refine setIntegral_mono_set (hwint (kk n) (rr n) hrrR)
          (Eventually.of_forall fun x => sq_nonneg _)
          (LE.le.eventuallyLE Set.inter_subset_left)
      rw [setIntegral_const, smul_eq_mul, Measure.real] at h1
      linarith [h1, h2]
    -- the recursion
    have hχ2 : χ ^ 2 ≤ H ^ 2 / R ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < R ^ 2)]
      nlinarith [hHχ, mul_nonneg hχ hR.le]
    have hrec : ∀ n : ℕ, Yt (n + 1) ≤ A₀ * bb ^ (n : ℝ) * Yt n ^ (1 + θ) := by
      intro n
      have hstep := hstepL χ R₀ Ω z G hχ hz x₀ R hR hRR₀ hball (rr (n + 1)) (rr n)
        (by linarith [hrrlb (n + 1)]) (hrrdec n) (by linarith [hrrub n]) (kk (n + 1))
      have hAa0 : (0:ℝ) ≤ (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal :=
        ENNReal.toReal_nonneg
      have hIσ := hYmono n
      have hIσ0 : (0:ℝ) ≤ ∫ x in Metric.ball x₀ (rr n), max (z x - kk (n + 1)) 0 ^ 2 :=
        integral_nonneg fun x => sq_nonneg _
      have hsq : ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 = 1 / 4 ^ (n + 1) := by
        rw [eq_div_iff (by positivity : ((4:ℝ) ^ (n + 1)) ≠ 0)]
        exact hpow4 (n + 1)
      have hAbd : (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal
          ≤ 4 ^ (n + 1) * Y n / H ^ 2 := by
        have h := hcheb n
        rw [hkkdiff n, mul_pow, hsq] at h
        rw [le_div_iff₀ (by positivity : (0:ℝ) < H ^ 2)]
        have h4 : (0:ℝ) < 4 ^ (n + 1) := by positivity
        have h5 := mul_le_mul_of_nonneg_left h h4.le
        have h6 : (4:ℝ) ^ (n + 1) *
            ((volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal *
              (H ^ 2 * (1 / 4 ^ (n + 1))))
            = (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal * H ^ 2 := by
          field_simp
        rw [h6] at h5
        exact h5
      have hgeo : (rr n - rr (n + 1))⁻¹ ^ 2 = 64 * 4 ^ n / R ^ 2 := by
        have hkey : (R / 8 * (1 / 2 : ℝ) ^ n) ^ 2 * (64 * 4 ^ n / R ^ 2) = 1 := by
          have he : (R / 8 * (1 / 2 : ℝ) ^ n) ^ 2 * (64 * 4 ^ n / R ^ 2)
              = ((1 / 2 : ℝ) ^ n) ^ 2 * 4 ^ n := by
            field_simp
            ring
          rw [he]
          exact hpow4 n
        rw [hrrdiff n, inv_pow]
        exact inv_eq_of_mul_eq_one_right hkey
      have hbracket : (rr n - rr (n + 1))⁻¹ ^ 2 *
            (∫ x in Metric.ball x₀ (rr n), max (z x - kk (n + 1)) 0 ^ 2)
          + χ ^ 2 * (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal
          ≤ 68 * 4 ^ n * Y n / R ^ 2 := by
        rw [hgeo]
        have h1 : 64 * 4 ^ n / R ^ 2 *
            (∫ x in Metric.ball x₀ (rr n), max (z x - kk (n + 1)) 0 ^ 2)
            ≤ 64 * 4 ^ n / R ^ 2 * Y n := mul_le_mul_of_nonneg_left hIσ (by positivity)
        have h2 : χ ^ 2 * (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal
            ≤ H ^ 2 / R ^ 2 * ((4:ℝ) ^ (n + 1) * Y n / H ^ 2) :=
          mul_le_mul hχ2 hAbd hAa0 (by positivity)
        have h3 : H ^ 2 / R ^ 2 * ((4:ℝ) ^ (n + 1) * Y n / H ^ 2)
            = 4 * ((4:ℝ) ^ n * Y n) / R ^ 2 := by
          field_simp
          ring
        rw [h3] at h2
        have h4 : 64 * (4:ℝ) ^ n / R ^ 2 * Y n + 4 * ((4:ℝ) ^ n * Y n) / R ^ 2
            = 68 * 4 ^ n * Y n / R ^ 2 := by
          field_simp
          ring
        linarith [h1, h2, h4]
      have hAθ0 : (0:ℝ) ≤
          (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal ^ θ :=
        Real.rpow_nonneg hAa0 _
      have hmain : Y (n + 1) ≤ Cst * R ^ (2 - (d:ℝ) * θ) * (68 * 4 ^ n * Y n / R ^ 2) *
          ((4:ℝ) ^ (n + 1) * Y n / H ^ 2) ^ θ := by
        refine hstep.trans ?_
        have hAθ : (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal ^ θ
            ≤ ((4:ℝ) ^ (n + 1) * Y n / H ^ 2) ^ θ := Real.rpow_le_rpow hAa0 hAbd hθ0.le
        have hc0 : (0:ℝ) ≤ Cst * R ^ (2 - (d:ℝ) * θ) := by positivity
        have hb0 : (0:ℝ) ≤ Cst * R ^ (2 - (d:ℝ) * θ) * (68 * 4 ^ n * Y n / R ^ 2) := by
          have : (0:ℝ) ≤ 68 * 4 ^ n * Y n / R ^ 2 := by positivity
          exact mul_nonneg hc0 this
        calc Cst * R ^ (2 - (d:ℝ) * θ) *
              ((rr n - rr (n + 1))⁻¹ ^ 2 *
                (∫ x in Metric.ball x₀ (rr n), max (z x - kk (n + 1)) 0 ^ 2)
                + χ ^ 2 *
                  (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal) *
              (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal ^ θ
            ≤ Cst * R ^ (2 - (d:ℝ) * θ) * (68 * 4 ^ n * Y n / R ^ 2) *
              (volume (Metric.ball x₀ (rr n) ∩ {x | kk (n + 1) < z x})).toReal ^ θ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbracket hc0) hAθ0
          _ ≤ _ := mul_le_mul_of_nonneg_left hAθ hb0
      rcases eq_or_lt_of_le (hYnn n) with h0 | hpos
      · have hYt0 : Yt n = 0 := by
          show Y n / D = 0
          rw [← h0, zero_div]
        have hYn1 : Y (n + 1) ≤ 0 := by
          refine hmain.trans (le_of_eq ?_)
          rw [← h0]
          simp [Real.zero_rpow hθ0.ne']
        rw [hYt0, Real.zero_rpow (by positivity : (1:ℝ) + θ ≠ 0), mul_zero]
        show Y (n + 1) / D ≤ 0
        exact div_nonpos_of_nonpos_of_nonneg hYn1 hD0.le
      · show Y (n + 1) / D ≤ A₀ * bb ^ (n : ℝ) * (Y n / D) ^ (1 + θ)
        rw [div_le_iff₀ hD0, hA₀def, hbbdef, hDdef,
          ← dg_rescale_identity n d hCst hR hH0 hpos]
        exact hmain
    -- the smallness of the first term
    have hkk00 : kk 0 = k := by simp only [hkkdef]; norm_num
    have hY0le : Y 0 ≤ ∫ x in Metric.ball x₀ R, max (z x - k) 0 ^ 2 := by
      have hsub : Metric.ball x₀ (rr 0) ⊆ Metric.ball x₀ R :=
        Metric.ball_subset_ball (by linarith [hrrub 0])
      have heq : Y 0 = ∫ x in Metric.ball x₀ (rr 0), max (z x - k) 0 ^ 2 := by
        show (∫ x in Metric.ball x₀ (rr 0), max (z x - kk 0) 0 ^ 2)
          = ∫ x in Metric.ball x₀ (rr 0), max (z x - k) 0 ^ 2
        rw [hkk00]
      rw [heq]
      exact setIntegral_mono_set (hwint k R le_rfl) (Eventually.of_forall fun x => sq_nonneg _)
        (LE.le.eventuallyLE hsub)
    have hsmall' : Yt 0 ≤ A₀ ^ (-θ⁻¹) * bb ^ (-(θ ^ 2)⁻¹) := by
      rw [← hc₅def]
      show Y 0 / D ≤ c₅
      rw [div_le_iff₀ hD0, hDdef]
      have h1 : Y 0 ≤ avg * (R ^ d * Vd) := by rw [← hY0up]; exact hY0le
      have h2 := mul_le_mul_of_nonneg_left hsmall (pow_nonneg hR.le d)
      nlinarith [h1, h2]
    have htend : Filter.Tendsto Yt Filter.atTop (nhds 0) :=
      tendsto_zero_of_degiorgi_fast_convergence hA₀0 hbb1 hθ0 hYtnn hrec hsmall'
    have htendY : Filter.Tendsto Y Filter.atTop (nhds 0) := by
      have h := htend.mul_const D
      rw [zero_mul] at h
      refine h.congr fun n => ?_
      show Y n / D * D = Y n
      field_simp
    -- pass to the limit
    have hIle : ∀ n, (∫ x in Metric.ball x₀ (R / 2), max (z x - (k + H)) 0 ^ 2) ≤ Y n := by
      intro n
      have h1 : (∫ x in Metric.ball x₀ (R / 2), max (z x - (k + H)) 0 ^ 2)
          ≤ ∫ x in Metric.ball x₀ (R / 2), max (z x - kk n) 0 ^ 2 := by
        refine integral_mono_ae (hwint (k + H) (R / 2) (by linarith))
          (hwint (kk n) (R / 2) (by linarith)) (Eventually.of_forall fun x => ?_)
        have hle : max (z x - (k + H)) 0 ≤ max (z x - kk n) 0 :=
          max_le_max (by linarith [hkkle n]) le_rfl
        nlinarith [le_max_right (z x - (k + H)) (0:ℝ), le_max_right (z x - kk n) (0:ℝ)]
      have h2 : (∫ x in Metric.ball x₀ (R / 2), max (z x - kk n) 0 ^ 2) ≤ Y n :=
        setIntegral_mono_set (hwint (kk n) (rr n) (by linarith [hrrub n]))
          (Eventually.of_forall fun x => sq_nonneg _)
          (LE.le.eventuallyLE (Metric.ball_subset_ball (hrrlb n).le))
      linarith
    have hIzero : (∫ x in Metric.ball x₀ (R / 2), max (z x - (k + H)) 0 ^ 2) ≤ 0 :=
      ge_of_tendsto htendY (Filter.Eventually.of_forall hIle)
    have hIeq : (∫ x in Metric.ball x₀ (R / 2), max (z x - (k + H)) 0 ^ 2) = 0 :=
      le_antisymm hIzero (integral_nonneg fun x => sq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (hwint (k + H) (R / 2) (by linarith))).1 hIeq
    filter_upwards [hae] with x hx
    have hx0 : max (z x - (k + H)) 0 = 0 := by
      have : max (z x - (k + H)) 0 ^ 2 = 0 := hx
      nlinarith [le_max_right (z x - (k + H)) (0:ℝ), this]
    have hle := le_max_left (z x - (k + H)) (0:ℝ)
    linarith [hx0, hle]
  -- apply the core with a vanishing extra height, then let it go to zero
  have hall : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
      ∀ m : ℕ, z x ≤ k + (χ * R + c₆ * Real.sqrt avg + 1 / ((m:ℝ) + 1)) := by
    rw [ae_all_iff]
    intro m
    have ht0 : (0:ℝ) < 1 / ((m:ℝ) + 1) := by positivity
    have h1 : (0:ℝ) ≤ c₆ * Real.sqrt avg := mul_nonneg hc₆0 (Real.sqrt_nonneg avg)
    have h2 : (0:ℝ) ≤ χ * R := mul_nonneg hχ hR.le
    refine hcore (χ * R + c₆ * Real.sqrt avg + 1 / ((m:ℝ) + 1)) (by linarith) (by linarith) ?_
    have hc₆sq : c₆ ^ 2 = Vd / c₅ := Real.sq_sqrt (by positivity)
    have h3 : (c₆ * Real.sqrt avg) ^ 2
        ≤ (χ * R + c₆ * Real.sqrt avg + 1 / ((m:ℝ) + 1)) ^ 2 := by
      nlinarith [h1, h2, ht0]
    have h4 : (c₆ * Real.sqrt avg) ^ 2 = Vd / c₅ * avg := by
      rw [mul_pow, hc₆sq, Real.sq_sqrt havg0]
    have h5 := mul_le_mul_of_nonneg_left h3 hc₅0.le
    rw [h4] at h5
    have h6 : c₅ * (Vd / c₅ * avg) = avg * Vd := by
      field_simp
      try ring
    linarith [h5, h6]
  filter_upwards [hall] with x hx
  have hlim : z x ≤ k + (χ * R + c₆ * Real.sqrt avg) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    exact (hx m).trans (by linarith)
  have hs0 : (0:ℝ) ≤ Real.sqrt avg := Real.sqrt_nonneg _
  have hχR : (0:ℝ) ≤ χ * R := mul_nonneg hχ hR.le
  have hC1 : c₆ * Real.sqrt avg ≤ max c₆ 1 * Real.sqrt avg :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
  have hC2 : χ * R ≤ max c₆ 1 * (χ * R) := by
    nlinarith [le_max_right c₆ (1:ℝ), hχR]
  linarith [hlim, hC1, hC2]

end Komlos.Literature.Regularized
