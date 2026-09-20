import Komlos.Literature.PLaplacian.FrozenComparison

/-!
# The `L²` frozen Dirichlet replacement by the direct method

This file supplies the *existence* half of the second classical input of the freezing step
(`Komlos.Literature.exists_frozen_replacement_data` in `PLaplacian/SchauderHarmonic.lean`): given
a constant symmetric `μ`-elliptic, `Λ`-bounded matrix `A₀` and an `L²` field `G` (in the
application `G = ∇w`), there is `ψ ∈ W₀^{1,2}(B̄(c,s))` minimising the **frozen Dirichlet energy**

`energy A₀ G ψ = ∫ ⟪A₀ (G - ∇ψ), G - ∇ψ⟫`,

and the minimiser satisfies the Euler–Lagrange equation `∫ ⟪A₀ (G - ∇ψ), ∇ζ⟫ = 0` for every
`ζ ∈ W₀^{1,2}(B̄(c,s))`.  With `G = ∇w` the field `H := G - ∇ψ` is the gradient of the frozen
Dirichlet replacement `h = w - ψ` of `w` on the ball, and `ψ = w - h` is exactly the admissible
test function of `Komlos.Literature.frozen_energy_estimate`.

## Why this file exists

The repo already proves the direct method for the anisotropic `p`-Laplacian
(`exists_dirEnergy_min` / `exists_pharmonic_replacement`, `PLaplacian/HolderExcessAux.lean`), but
that file is *downstream* of `SchauderHarmonic` in the import graph — it needs
`IsSmoothStrictNorm`, `midDefect`, `flux` and `hasDerivAt_integral_rpow_add_smul`, which live in
`EigenfunctionAux`/`Eigenfunction`, themselves downstream of `Rellich`.  For the quadratic case
`p = 2` none of that machinery is needed: uniform convexity is the *parallelogram law* for the
quadratic form `ξ ↦ ⟪A₀ ξ, ξ⟫` (`inner_apply_sub_self_eq_of_mid`), and the Euler–Lagrange
equation is the vanishing of the linear coefficient of a real quadratic
(`euler_lagrange_energy_min`).  Everything below therefore rests only on
`Komlos.Literature.Sobolev.Defs` (`W0_complete`, `MemW0`) and on the ball Poincaré inequality
`MemW0.eLpNorm_le_eLpNorm_weakGrad_closedBall` of `PLaplacian/FrozenComparison.lean`.

## Main results

* `inner_apply_sub_self_eq_of_mid` — the parallelogram law for a quadratic form.
* `integrable_inner_apply` — `x ↦ ⟪A₀ (u x), v x⟫` is integrable for `L²` fields `u`, `v`.
* `exists_energy_min` — the direct method: the frozen energy attains its infimum on
  `W₀^{1,2}(B̄(c,s))`.
* `euler_lagrange_energy_min` — the Euler–Lagrange equation of the minimiser.
* `exists_frozen_replacement_field` — the two combined: the frozen Dirichlet replacement *field*.

## What is still missing for `exists_frozen_replacement_data`

The replacement produced here is a Sobolev object: `H = G - ∇ψ` is an `L²` field, not yet the
gradient of a `C¹` function.  Upgrading it needs **Weyl's lemma** for `div (A₀ ∇h) = 0` — the
same missing input as `exists_constCoeff_gradient_lipschitz`.  See the `TODO(frozen)` comment of
`Komlos.Literature.exists_frozen_replacement_data`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace

open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

namespace FrozenDirichlet

variable {d : ℕ}

/-! ### The quadratic form of a constant coefficient matrix -/

/-- Boundedness of the bilinear form `(ξ, η) ↦ ⟪A₀ ξ, η⟫` attached to `A₀`. -/
theorem abs_inner_apply_le {A₀ : Euc d →L[ℝ] Euc d} {Λ : ℝ} (hA : ‖A₀‖ ≤ Λ) (ξ η : Euc d) :
    |⟪A₀ ξ, η⟫| ≤ Λ * (‖ξ‖ * ‖η‖) := by
  have h1 : |⟪A₀ ξ, η⟫| ≤ ‖A₀ ξ‖ * ‖η‖ := abs_real_inner_le_norm _ _
  have h2 : ‖A₀ ξ‖ ≤ Λ * ‖ξ‖ :=
    (A₀.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg ξ))
  calc |⟪A₀ ξ, η⟫| ≤ ‖A₀ ξ‖ * ‖η‖ := h1
    _ ≤ Λ * ‖ξ‖ * ‖η‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg η)
    _ = Λ * (‖ξ‖ * ‖η‖) := by ring

/-- The quadratic form is bounded above by `Λ ‖ξ‖²`. -/
theorem inner_apply_self_le {A₀ : Euc d →L[ℝ] Euc d} {Λ : ℝ} (hA : ‖A₀‖ ≤ Λ) (ξ : Euc d) :
    ⟪A₀ ξ, ξ⟫ ≤ Λ * ‖ξ‖ ^ 2 := by
  have h := abs_inner_apply_le hA ξ ξ
  have h2 : ‖ξ‖ * ‖ξ‖ = ‖ξ‖ ^ 2 := by ring
  rw [h2] at h
  exact (le_abs_self _).trans h

/-- The symmetry hypothesis of this file, `⟪A₀ ξ, η⟫ = ⟪A₀ η, ξ⟫`, in terms of the self-adjointness
convention `⟪A₀ u, v⟫ = ⟪u, A₀ v⟫` used by `Komlos.Literature.PLaplacian.HarmonicRd`. -/
theorem inner_apply_comm_of_selfAdjoint {A₀ : Euc d →L[ℝ] Euc d}
    (hsymm : ∀ u v : Euc d, ⟪A₀ u, v⟫ = ⟪u, A₀ v⟫) (ξ η : Euc d) : ⟪A₀ ξ, η⟫ = ⟪A₀ η, ξ⟫ := by
  rw [hsymm ξ η]
  exact real_inner_comm (A₀ η) ξ

/-- Expansion of the quadratic form along a sum. -/
theorem inner_apply_add_self (A₀ : Euc d →L[ℝ] Euc d) (a e : Euc d) :
    ⟪A₀ (a + e), a + e⟫ = ⟪A₀ a, a⟫ + ⟪A₀ a, e⟫ + ⟪A₀ e, a⟫ + ⟪A₀ e, e⟫ := by
  simp only [map_add, inner_add_left, inner_add_right]
  ring

/-- Expansion of the quadratic form along a difference. -/
theorem inner_apply_sub_self (A₀ : Euc d →L[ℝ] Euc d) (a e : Euc d) :
    ⟪A₀ (a - e), a - e⟫ = ⟪A₀ a, a⟫ - ⟪A₀ a, e⟫ - ⟪A₀ e, a⟫ + ⟪A₀ e, e⟫ := by
  simp only [map_sub, inner_sub_left, inner_sub_right]
  ring

/-- **The parallelogram law for the quadratic form `ξ ↦ ⟪A₀ ξ, ξ⟫`**: if `m` is the midpoint of
`a` and `b` (in the form `m + m = a + b`, which avoids dividing by two) then
`⟪A₀ (a - b), a - b⟫ = 2 ⟪A₀ a, a⟫ + 2 ⟪A₀ b, b⟫ - 4 ⟪A₀ m, m⟫`.  No symmetry of `A₀` is needed:
the cross terms cancel in pairs.  This is the uniform convexity behind the direct method for
`p = 2`. -/
theorem inner_apply_sub_self_eq_of_mid (A₀ : Euc d →L[ℝ] Euc d) {a b m : Euc d}
    (hm : m + m = a + b) :
    ⟪A₀ (a - b), a - b⟫ = 2 * ⟪A₀ a, a⟫ + 2 * ⟪A₀ b, b⟫ - 4 * ⟪A₀ m, m⟫ := by
  have h1 : ⟪A₀ (a + b), a + b⟫ = 4 * ⟪A₀ m, m⟫ := by
    rw [← hm, inner_apply_add_self A₀ m m]
    ring
  have h2 := inner_apply_add_self A₀ a b
  have h3 := inner_apply_sub_self A₀ a b
  linarith

/-! ### Integrability of the quadratic and bilinear integrands -/

/-- The square of the norm of an `L²` field is integrable. -/
theorem integrable_norm_sq {F : Euc d → Euc d} (hF : MemLp F (ENNReal.ofReal 2)) :
    Integrable fun x => ‖F x‖ ^ 2 := by
  have h0 : (ENNReal.ofReal (2 : ℝ)) ≠ 0 := by simp
  have htop : (ENNReal.ofReal (2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htr : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by
    rw [ENNReal.toReal_ofReal]
    norm_num
  refine (hF.integrable_norm_rpow h0 htop).congr (Eventually.of_forall fun x => ?_)
  show ‖F x‖ ^ ((ENNReal.ofReal (2 : ℝ)).toReal) = ‖F x‖ ^ (2 : ℕ)
  rw [htr, ← Real.rpow_natCast ‖F x‖ 2]
  norm_num

/-- The bilinear pairing of two `L²` fields through `A₀` is integrable. -/
theorem integrable_inner_apply {A₀ : Euc d →L[ℝ] Euc d} {Λ : ℝ} (hA : ‖A₀‖ ≤ Λ)
    {u v : Euc d → Euc d} (hu : MemLp u (ENNReal.ofReal 2)) (hv : MemLp v (ENNReal.ofReal 2)) :
    Integrable fun x => ⟪A₀ (u x), v x⟫ := by
  have hΛ0 : (0 : ℝ) ≤ Λ := (norm_nonneg A₀).trans hA
  have hdom : Integrable fun x => Λ * ((‖u x‖ ^ 2 + ‖v x‖ ^ 2) / 2) :=
    (((integrable_norm_sq hu).add (integrable_norm_sq hv)).div_const 2).const_mul Λ
  refine hdom.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (A₀.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable).inner
      hv.aestronglyMeasurable
  · show ‖⟪A₀ (u x), v x⟫‖ ≤ Λ * ((‖u x‖ ^ 2 + ‖v x‖ ^ 2) / 2)
    rw [Real.norm_eq_abs]
    have h1 : |⟪A₀ (u x), v x⟫| ≤ Λ * (‖u x‖ * ‖v x‖) := abs_inner_apply_le hA _ _
    have h2 : ‖u x‖ * ‖v x‖ ≤ (‖u x‖ ^ 2 + ‖v x‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖u x‖ - ‖v x‖)]
    have h3 : Λ * (‖u x‖ * ‖v x‖) ≤ Λ * ((‖u x‖ ^ 2 + ‖v x‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left h2 hΛ0
    linarith

/-- The competitor field `G - ∇z` of `z ∈ W₀^{1,2}(B)` lies in `L²` when `G` does. -/
theorem memLp_sub_weakGrad {B : Set (Euc d)} {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) {z : Euc d → ℝ} (hz : MemW0 2 B z) :
    MemLp (fun x => G x - weakGrad z x) (ENNReal.ofReal 2) :=
  (hG.sub hz.memLp_weakGrad).ae_eq (Eventually.of_forall fun _ => rfl)

/-! ### Linear combinations in `W₀^{1,2}` -/

/-- `W₀^{1,2}(B)` is closed under differences. -/
theorem memW0_sub {B : Set (Euc d)} {z₁ z₂ : Euc d → ℝ} (h₁ : MemW0 2 B z₁)
    (h₂ : MemW0 2 B z₂) : MemW0 2 B (z₁ - z₂) := by
  have hfun : z₁ - z₂ = z₁ + (-1 : ℝ) • z₂ := by
    funext x
    show z₁ x - z₂ x = z₁ x + (-1 : ℝ) * z₂ x
    ring
  rw [hfun]
  exact h₁.add (h₂.smul (-1))

/-- The weak gradient of a difference. -/
theorem weakGrad_sub_ae {z₁ z₂ : Euc d → ℝ} (h₁ : ∃ g, HasWeakGradient z₁ g)
    (h₂ : ∃ g, HasWeakGradient z₂ g) :
    weakGrad (z₁ - z₂) =ᵐ[volume] weakGrad z₁ - weakGrad z₂ := by
  have hfun : z₁ - z₂ = z₁ + (-1 : ℝ) • z₂ := by
    funext x
    show z₁ x - z₂ x = z₁ x + (-1 : ℝ) * z₂ x
    ring
  have hgfun : weakGrad z₁ + (-1 : ℝ) • weakGrad z₂ =ᵐ[volume] weakGrad z₁ - weakGrad z₂ :=
    Eventually.of_forall fun x => by
      show weakGrad z₁ x + (-1 : ℝ) • weakGrad z₂ x = weakGrad z₁ x - weakGrad z₂ x
      module
  have h : HasWeakGradient (z₁ - z₂) (weakGrad z₁ - weakGrad z₂) := by
    rw [hfun]
    exact ((hasWeakGradient_weakGrad h₁).add
      ((hasWeakGradient_weakGrad h₂).smul (-1))).congr_right hgfun
  exact h.weakGrad_ae_eq

/-- `W₀^{1,2}(B)` is closed under the affine perturbations used by the Euler–Lagrange argument. -/
theorem memW0_add_smul {B : Set (Euc d)} {z ζ : Euc d → ℝ} (hz : MemW0 2 B z)
    (hζ : MemW0 2 B ζ) (t : ℝ) : MemW0 2 B (z + t • ζ) :=
  hz.add (hζ.smul t)

/-- The weak gradient of an affine perturbation. -/
theorem weakGrad_add_smul_ae {z ζ : Euc d → ℝ} (hz : ∃ g, HasWeakGradient z g)
    (hζ : ∃ g, HasWeakGradient ζ g) (t : ℝ) :
    weakGrad (z + t • ζ) =ᵐ[volume] weakGrad z + t • weakGrad ζ :=
  ((hasWeakGradient_weakGrad hz).add ((hasWeakGradient_weakGrad hζ).smul t)).weakGrad_ae_eq


/-! ### Young's inequality for the bilinear form -/

/-- **Young's inequality for the bilinear form**: `⟪A₀ u, e⟫ ≤ (Λ/2)(θ ‖u‖² + θ⁻¹ ‖e‖²)`.  This is
what replaces, in the quadratic case, the `L^p` interpolation of `HolderExcessAux`. -/
theorem inner_apply_le_young {A₀ : Euc d →L[ℝ] Euc d} {Λ : ℝ} (hA : ‖A₀‖ ≤ Λ) {θ : ℝ}
    (hθ : 0 < θ) (u e : Euc d) :
    ⟪A₀ u, e⟫ ≤ Λ / 2 * (θ * ‖u‖ ^ 2 + θ⁻¹ * ‖e‖ ^ 2) := by
  have hΛ0 : (0 : ℝ) ≤ Λ := (norm_nonneg A₀).trans hA
  have hθne : θ ≠ 0 := hθ.ne'
  have hinv : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθne
  have hexp : θ * (θ * ‖u‖ ^ 2 + θ⁻¹ * ‖e‖ ^ 2) = θ ^ 2 * ‖u‖ ^ 2 + ‖e‖ ^ 2 := by
    calc θ * (θ * ‖u‖ ^ 2 + θ⁻¹ * ‖e‖ ^ 2)
        = θ ^ 2 * ‖u‖ ^ 2 + θ * θ⁻¹ * ‖e‖ ^ 2 := by ring
      _ = θ ^ 2 * ‖u‖ ^ 2 + ‖e‖ ^ 2 := by rw [hinv, one_mul]
  have hkey : θ * (2 * (‖u‖ * ‖e‖)) ≤ θ * (θ * ‖u‖ ^ 2 + θ⁻¹ * ‖e‖ ^ 2) := by
    rw [hexp]
    nlinarith [sq_nonneg (θ * ‖u‖ - ‖e‖)]
  have hAM : 2 * (‖u‖ * ‖e‖) ≤ θ * ‖u‖ ^ 2 + θ⁻¹ * ‖e‖ ^ 2 := le_of_mul_le_mul_left hkey hθ
  have h1 : ⟪A₀ u, e⟫ ≤ Λ * (‖u‖ * ‖e‖) := (le_abs_self _).trans (abs_inner_apply_le hA u e)
  nlinarith [hAM, h1, hΛ0]

/-! ### The frozen Dirichlet energy -/

/-- The **frozen Dirichlet energy** of the competitor `z ∈ W₀^{1,2}(B)` relative to the field `G`:
`∫ ⟪A₀ (G - ∇z), G - ∇z⟫`.  With `G = ∇w` this is the `A₀`-energy `∫ ⟪A₀ ∇v, ∇v⟫` of the
competitor `v = w - z`, so that the frozen Dirichlet replacement of `w` on `B` is `w - z` for a
minimiser `z`. -/
noncomputable def energy (A₀ : Euc d →L[ℝ] Euc d) (G : Euc d → Euc d) (z : Euc d → ℝ) : ℝ :=
  ∫ x, ⟪A₀ (G x - weakGrad z x), G x - weakGrad z x⟫

theorem energy_eq (A₀ : Euc d →L[ℝ] Euc d) (G : Euc d → Euc d) (z : Euc d → ℝ) :
    energy A₀ G z = ∫ x, ⟪A₀ (G x - weakGrad z x), G x - weakGrad z x⟫ := rfl

/-- The energy depends on `z` only through the a.e. class of its weak gradient. -/
theorem energy_congr_weakGrad {A₀ : Euc d →L[ℝ] Euc d} {G : Euc d → Euc d} {z : Euc d → ℝ}
    {F : Euc d → Euc d} (h : weakGrad z =ᵐ[volume] F) :
    energy A₀ G z = ∫ x, ⟪A₀ (G x - F x), G x - F x⟫ := by
  rw [energy_eq]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  show ⟪A₀ (G x - weakGrad z x), G x - weakGrad z x⟫ = ⟪A₀ (G x - F x), G x - F x⟫
  rw [hx]

/-- The frozen energy is nonnegative. -/
theorem energy_nonneg {A₀ : Euc d →L[ℝ] Euc d} {μ : ℝ} (hμ : 0 < μ)
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) (G : Euc d → Euc d) (z : Euc d → ℝ) :
    0 ≤ energy A₀ G z := by
  rw [energy_eq]
  refine integral_nonneg fun x => ?_
  show (0 : ℝ) ≤ ⟪A₀ (G x - weakGrad z x), G x - weakGrad z x⟫
  have h0 : (0 : ℝ) ≤ μ * ‖G x - weakGrad z x‖ ^ 2 := mul_nonneg hμ.le (sq_nonneg _)
  have h1 := hell (G x - weakGrad z x)
  linarith

/-- **Ellipticity in integrated form**: the `L²` norm of the competitor field is controlled by the
energy. -/
theorem mul_integral_norm_sq_le_energy {A₀ : Euc d →L[ℝ] Euc d} {μ Λ : ℝ}
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) (hA : ‖A₀‖ ≤ Λ) {B : Set (Euc d)}
    {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal 2)) {z : Euc d → ℝ}
    (hz : MemW0 2 B z) :
    μ * ∫ x, ‖G x - weakGrad z x‖ ^ 2 ≤ energy A₀ G z := by
  have hu : MemLp (fun x => G x - weakGrad z x) (ENNReal.ofReal 2) := memLp_sub_weakGrad hG hz
  rw [energy_eq, ← integral_const_mul]
  refine integral_mono ((integrable_norm_sq hu).const_mul μ) (integrable_inner_apply hA hu hu)
    fun x => ?_
  show μ * ‖G x - weakGrad z x‖ ^ 2 ≤ ⟪A₀ (G x - weakGrad z x), G x - weakGrad z x⟫
  exact hell _

/-- The infimum of the frozen energy over `W₀^{1,2}(B)`: a nonnegative `m` lying below every
energy and approximated by energies. -/
theorem exists_energy_inf {A₀ : Euc d →L[ℝ] Euc d} {μ : ℝ} (hμ : 0 < μ)
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) (B : Set (Euc d)) (G : Euc d → Euc d) :
    ∃ m : ℝ, 0 ≤ m ∧ (∀ z : Euc d → ℝ, MemW0 2 B z → m ≤ energy A₀ G z) ∧
      ∀ δ : ℝ, 0 < δ → ∃ z : Euc d → ℝ, MemW0 2 B z ∧ energy A₀ G z < m + δ := by
  have : Nonempty {z : Euc d → ℝ // MemW0 2 B z} := ⟨⟨0, MemW0.zero⟩⟩
  have hbdd : BddBelow (Set.range fun z : {z : Euc d → ℝ // MemW0 2 B z} =>
      energy A₀ G z.1) := by
    refine ⟨0, ?_⟩
    rintro y ⟨z, rfl⟩
    exact energy_nonneg hμ hell G z.1
  refine ⟨⨅ z : {z : Euc d → ℝ // MemW0 2 B z}, energy A₀ G z.1,
    le_ciInf fun z => energy_nonneg hμ hell G z.1, fun z hz => ciInf_le hbdd ⟨z, hz⟩,
    fun δ hδ => ?_⟩
  obtain ⟨z, hz⟩ := exists_lt_of_ciInf_lt
    (f := fun z : {z : Euc d → ℝ // MemW0 2 B z} => energy A₀ G z.1)
    (lt_add_of_pos_right _ hδ)
  exact ⟨z.1, z.2, hz⟩

/-- **The key estimate of the direct method for `p = 2`**: comparing with the midpoint competitor,
the parallelogram law (`inner_apply_sub_self_eq_of_mid`) bounds the `L²` distance of the gradients
of two competitors by how far their energies lie above the infimum. -/
theorem mul_integral_norm_weakGrad_sub_sq_le {A₀ : Euc d →L[ℝ] Euc d} {μ Λ : ℝ}
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) (hA : ‖A₀‖ ≤ Λ) {B : Set (Euc d)}
    {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal 2)) {m : ℝ}
    (hm : ∀ z : Euc d → ℝ, MemW0 2 B z → m ≤ energy A₀ G z)
    {z₁ z₂ : Euc d → ℝ} (h₁ : MemW0 2 B z₁) (h₂ : MemW0 2 B z₂) :
    μ * ∫ x, ‖weakGrad z₁ x - weakGrad z₂ x‖ ^ 2 ≤
      2 * energy A₀ G z₂ + 2 * energy A₀ G z₁ - 4 * m := by
  -- the midpoint competitor `zm = z₁ + (z₂ - z₁)/2`
  have hwW : MemW0 2 B (z₂ - z₁) := memW0_sub h₂ h₁
  have hzmW : MemW0 2 B (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) := memW0_add_smul h₁ hwW _
  have hgw : weakGrad (z₂ - z₁) =ᵐ[volume] weakGrad z₂ - weakGrad z₁ :=
    weakGrad_sub_ae ⟨_, h₂.hasWeakGradient⟩ ⟨_, h₁.hasWeakGradient⟩
  have hgm : weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) =ᵐ[volume]
      weakGrad z₁ + (2 : ℝ)⁻¹ • weakGrad (z₂ - z₁) :=
    weakGrad_add_smul_ae ⟨_, h₁.hasWeakGradient⟩ ⟨_, hwW.hasWeakGradient⟩ _
  -- the midpoint relation, pointwise a.e.
  have hmid : ∀ᵐ x : Euc d,
      (G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x)
        + (G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x)
      = (G x - weakGrad z₂ x) + (G x - weakGrad z₁ x) := by
    filter_upwards [hgm, hgw] with x hx hy
    have hx' : weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x
        = weakGrad z₁ x + (2 : ℝ)⁻¹ • weakGrad (z₂ - z₁) x := hx
    have hy' : weakGrad (z₂ - z₁) x = weakGrad z₂ x - weakGrad z₁ x := hy
    rw [hx', hy']
    module
  have hsub : ∀ x : Euc d, (G x - weakGrad z₂ x) - (G x - weakGrad z₁ x)
      = weakGrad z₁ x - weakGrad z₂ x := fun x => by module
  have hpt : ∀ᵐ x : Euc d,
      ⟪A₀ (weakGrad z₁ x - weakGrad z₂ x), weakGrad z₁ x - weakGrad z₂ x⟫
        = 2 * ⟪A₀ (G x - weakGrad z₂ x), G x - weakGrad z₂ x⟫
          + 2 * ⟪A₀ (G x - weakGrad z₁ x), G x - weakGrad z₁ x⟫
          - 4 * ⟪A₀ (G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x),
              G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x⟫ := by
    filter_upwards [hmid] with x hx
    have h := inner_apply_sub_self_eq_of_mid A₀ hx
    rwa [hsub x] at h
  -- integrability of the four integrands
  have hmemD : MemLp (fun x => weakGrad z₁ x - weakGrad z₂ x) (ENNReal.ofReal 2) :=
    (h₁.memLp_weakGrad.sub h₂.memLp_weakGrad).ae_eq (Eventually.of_forall fun _ => rfl)
  have hi1 : Integrable fun x => ⟪A₀ (G x - weakGrad z₁ x), G x - weakGrad z₁ x⟫ :=
    integrable_inner_apply hA (memLp_sub_weakGrad hG h₁) (memLp_sub_weakGrad hG h₁)
  have hi2 : Integrable fun x => ⟪A₀ (G x - weakGrad z₂ x), G x - weakGrad z₂ x⟫ :=
    integrable_inner_apply hA (memLp_sub_weakGrad hG h₂) (memLp_sub_weakGrad hG h₂)
  have him : Integrable fun x =>
      ⟪A₀ (G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x),
        G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x⟫ :=
    integrable_inner_apply hA (memLp_sub_weakGrad hG hzmW) (memLp_sub_weakGrad hG hzmW)
  have hiL : Integrable fun x =>
      ⟪A₀ (weakGrad z₁ x - weakGrad z₂ x), weakGrad z₁ x - weakGrad z₂ x⟫ :=
    integrable_inner_apply hA hmemD hmemD
  -- the parallelogram identity, integrated
  have hj2 : Integrable fun x => 2 * ⟪A₀ (G x - weakGrad z₂ x), G x - weakGrad z₂ x⟫ :=
    hi2.const_mul 2
  have hj1 : Integrable fun x => 2 * ⟪A₀ (G x - weakGrad z₁ x), G x - weakGrad z₁ x⟫ :=
    hi1.const_mul 2
  have hjm : Integrable fun x => 4 * ⟪A₀ (G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x),
      G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x⟫ := him.const_mul 4
  have hj12 : Integrable fun x => 2 * ⟪A₀ (G x - weakGrad z₂ x), G x - weakGrad z₂ x⟫
      + 2 * ⟪A₀ (G x - weakGrad z₁ x), G x - weakGrad z₁ x⟫ := hj2.add hj1
  have hint : ∫ x, ⟪A₀ (weakGrad z₁ x - weakGrad z₂ x), weakGrad z₁ x - weakGrad z₂ x⟫
      = 2 * energy A₀ G z₂ + 2 * energy A₀ G z₁
        - 4 * energy A₀ G (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) := by
    rw [integral_congr_ae hpt, energy_eq, energy_eq, energy_eq,
      integral_sub hj12 hjm, integral_add hj2 hj1, integral_const_mul, integral_const_mul,
      integral_const_mul]
  -- ellipticity and minimality of the infimum
  have hlow : μ * ∫ x, ‖weakGrad z₁ x - weakGrad z₂ x‖ ^ 2 ≤
      ∫ x, ⟪A₀ (weakGrad z₁ x - weakGrad z₂ x), weakGrad z₁ x - weakGrad z₂ x⟫ := by
    rw [← integral_const_mul]
    refine integral_mono ((integrable_norm_sq hmemD).const_mul μ) hiL fun x => ?_
    show μ * ‖weakGrad z₁ x - weakGrad z₂ x‖ ^ 2
      ≤ ⟪A₀ (weakGrad z₁ x - weakGrad z₂ x), weakGrad z₁ x - weakGrad z₂ x⟫
    exact hell _
  have hmm : m ≤ energy A₀ G (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) := hm _ hzmW
  linarith

/-! ### The direct method: existence of the minimiser -/

/-- **The direct method for the frozen Dirichlet energy (`p = 2`).**  For a constant symmetric
`μ`-elliptic, `Λ`-bounded `A₀` and an `L²` field `G`, the frozen energy `z ↦ ∫ ⟪A₀ (G - ∇z),
G - ∇z⟫` attains its infimum on `W₀^{1,2}(B̄(c,s))`.

Proof (Giaquinta–Martinazzi, Theorem 4.2; the quadratic case of `exists_dirEnergy_min`): a
minimising sequence `z n` has `∫ ‖G - ∇z n‖²` uniformly bounded by ellipticity; the midpoint
competitor together with the parallelogram law (`mul_integral_norm_weakGrad_sub_sq_le`) makes
`∇z n` Cauchy in `L²`; the ball Poincaré inequality
(`MemW0.eLpNorm_le_eLpNorm_weakGrad_closedBall`) makes `z n` Cauchy in the graph norm, so
`W0_complete` produces the limit `v ∈ W₀^{1,2}`; and the energy passes to the limit because
`E(v) - E(z n)` is controlled by `∫ ‖∇z n - ∇v‖²` through Young's inequality
(`inner_apply_le_young`). -/
theorem exists_energy_min (hd : 0 < d) {A₀ : Euc d →L[ℝ] Euc d} {μ Λ : ℝ} (hμ : 0 < μ)
    (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) (hA : ‖A₀‖ ≤ Λ)
    (hsymm : ∀ ξ η : Euc d, ⟪A₀ ξ, η⟫ = ⟪A₀ η, ξ⟫)
    {c : Euc d} {s : ℝ} (hs : 0 ≤ s) {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal 2)) :
    ∃ v : Euc d → ℝ, MemW0 2 (Metric.closedBall c s) v ∧
      ∀ z : Euc d → ℝ, MemW0 2 (Metric.closedBall c s) z → energy A₀ G v ≤ energy A₀ G z := by
  have hΛ0 : (0 : ℝ) ≤ Λ := (norm_nonneg A₀).trans hA
  obtain ⟨m₀, hm₀0, hmle, hmlt⟩ := exists_energy_inf hμ hell (Metric.closedBall c s) G
  choose z hzW hzJ using fun n : ℕ => hmlt (1 / ((n : ℝ) + 1)) (by positivity)
  have hδ1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  -- (i) a uniform `L²` bound for the competitor fields
  have hCu : ∀ n : ℕ, ∫ x, ‖G x - weakGrad (z n) x‖ ^ 2 ≤ (m₀ + 1) / μ := by
    intro n
    have h1 := mul_integral_norm_sq_le_energy hell hA hG (hzW n)
    have h2 := hzJ n
    have h3 := hδ1 n
    have hcomm : (∫ x, ‖G x - weakGrad (z n) x‖ ^ 2) * μ
        = μ * ∫ x, ‖G x - weakGrad (z n) x‖ ^ 2 := mul_comm _ _
    rw [le_div_iff₀ hμ, hcomm]
    linarith
  -- (ii) the gradients are Cauchy in `L²`
  have hCauchy : ∀ k l : ℕ, μ * ∫ x, ‖weakGrad (z k) x - weakGrad (z l) x‖ ^ 2 ≤
      2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1)) := by
    intro k l
    have h := mul_integral_norm_weakGrad_sub_sq_le hell hA hG hmle (hzW k) (hzW l)
    have h1 := hzJ k
    have h2 := hzJ l
    linarith
  -- (iii) the graph-norm Cauchy condition of `W0_complete`
  have hgradMemLp : ∀ k l : ℕ, MemLp (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) :=
    fun k l => (hzW k).memLp_weakGrad.sub (hzW l).memLp_weakGrad
  have hnorm : ∀ k l : ℕ,
      μ * ((eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume).toReal) ^ 2
        ≤ 2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1)) := by
    intro k l
    rw [← integral_norm_sq_eq_sq_eLpNorm (hgradMemLp k l)]
    exact hCauchy k l
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 2 * s + 1 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hTdef]; linarith
  have hpo : ∀ k l : ℕ, eLpNorm (z k - z l) (ENNReal.ofReal 2) volume
      ≤ ENNReal.ofReal T *
        eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume := by
    intro k l
    have hW : MemW0 2 (Metric.closedBall c s) (z k - z l) := memW0_sub (hzW k) (hzW l)
    have h := hW.eLpNorm_le_eLpNorm_weakGrad_closedBall (T := T) hd one_lt_two hs
      (by rw [hTdef]; linarith)
    have hcg : eLpNorm (weakGrad (z k - z l)) (ENNReal.ofReal 2) volume
        = eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume :=
      eLpNorm_congr_ae
        (weakGrad_sub_ae ⟨_, (hzW k).hasWeakGradient⟩ ⟨_, (hzW l).hasWeakGradient⟩)
    rwa [hcg] at h
  have hcauchyE : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
      eLpNorm (z k - z l) (ENNReal.ofReal 2) volume +
        eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume < ε := by
    intro ε hε
    obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hrpos : 0 < r := by
      by_contra hcon
      push Not at hcon
      rw [ENNReal.ofReal_eq_zero.2 hcon] at hr1
      exact lt_irrefl _ hr1
    obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = r / (2 * (T + 1)) := ⟨_, rfl⟩
    have he0 : 0 < e := by
      rw [hedef]
      exact div_pos hrpos (by linarith)
    have hTe : (T + 1) * e < r := by
      have hid : e * (2 * (T + 1)) = r := by
        rw [hedef]
        exact div_mul_cancel₀ r (ne_of_gt (by linarith : (0 : ℝ) < 2 * (T + 1)))
      linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (μ * e ^ 2))
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h4 : 4 < ((N : ℝ) + 1) * (μ * e ^ 2) := by
      have hNgt : 4 / (μ * e ^ 2) < (N : ℝ) + 1 := by linarith [hN]
      rwa [div_lt_iff₀ (mul_pos hμ (pow_pos he0 2))] at hNgt
    have hlt : 4 * (1 / ((N : ℝ) + 1)) < μ * e ^ 2 := by
      rw [mul_one_div, div_lt_iff₀ hNpos]
      linarith [h4]
    refine ⟨N, fun k l hk hl => ?_⟩
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have hle : ((N : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
        have hc : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
        linarith
      exact one_div_le_one_div_of_le hNpos hle
    have hl1 : 1 / ((l : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have hle : ((N : ℝ) + 1) ≤ ((l : ℝ) + 1) := by
        have hc : (N : ℝ) ≤ (l : ℝ) := Nat.cast_le.2 hl
        linarith
      exact one_div_le_one_div_of_le hNpos hle
    obtain ⟨X, hXdef⟩ : ∃ X : ℝ,
        X = (eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume).toReal :=
      ⟨_, rfl⟩
    have hmu : μ * X ^ 2 ≤ 2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1)) := by
      rw [hXdef]
      exact hnorm k l
    have hsq : X ^ 2 < e ^ 2 := by
      have hmlt : μ * X ^ 2 < μ * e ^ 2 := by linarith
      exact lt_of_mul_lt_mul_left hmlt hμ.le
    have hnn : (0 : ℝ) ≤ X := by
      rw [hXdef]
      exact ENNReal.toReal_nonneg
    have htoReal : X ≤ e := by
      by_contra hcon
      push Not at hcon
      have hpos : (0 : ℝ) < (X - e) * (X + e) := mul_pos (by linarith) (by linarith)
      nlinarith [hpos, hsq]
    have hne : eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume ≠ ⊤ :=
      (hgradMemLp k l).eLpNorm_lt_top.ne
    have hle : eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume
        ≤ ENNReal.ofReal e := by
      rw [← ENNReal.ofReal_toReal hne, ← hXdef]
      exact ENNReal.ofReal_le_ofReal htoReal
    calc eLpNorm (z k - z l) (ENNReal.ofReal 2) volume
          + eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume
        ≤ ENNReal.ofReal T * ENNReal.ofReal e + ENNReal.ofReal e :=
          add_le_add ((hpo k l).trans (mul_le_mul_right hle (ENNReal.ofReal T))) hle
      _ = ENNReal.ofReal ((T + 1) * e) := by
          rw [← ENNReal.ofReal_mul hT0.le,
            ← ENNReal.ofReal_add (mul_nonneg hT0.le he0.le) he0.le]
          congr 1
          ring
      _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hrpos).2 hTe
      _ < ε := hr2
  obtain ⟨v, hvW, hvT⟩ := W0_complete one_lt_two z hzW hcauchyE
  -- (iv) the `L²` distance of the gradients to the limit tends to zero
  have hgradT : Tendsto
      (fun n => eLpNorm (weakGrad (z n) - weakGrad v) (ENNReal.ofReal 2) volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvT
      (fun _ => zero_le) fun _ => le_add_self
  have hmemn : ∀ n : ℕ, MemLp (weakGrad (z n) - weakGrad v) (ENNReal.ofReal 2) :=
    fun n => (hzW n).memLp_weakGrad.sub hvW.memLp_weakGrad
  have hEn : Tendsto (fun n : ℕ => ∫ x, ‖weakGrad (z n) x - weakGrad v x‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ =>
        (eLpNorm (weakGrad (z n) - weakGrad v) (ENNReal.ofReal 2) volume).toReal)
        atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hgradT
      simpa [Function.comp_def] using h
    have h2 : Tendsto (fun n : ℕ =>
        ((eLpNorm (weakGrad (z n) - weakGrad v) (ENNReal.ofReal 2) volume).toReal) ^ 2)
        atTop (𝓝 0) := by
      have h := h1.pow 2
      simpa using h
    refine h2.congr fun n => ?_
    exact (integral_norm_sq_eq_sq_eLpNorm (hmemn n)).symm
  -- (v) the energy expansion around the `n`-th competitor
  have hexpand : ∀ n : ℕ, energy A₀ G v = energy A₀ G (z n)
      + 2 * (∫ x, ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫)
      + ∫ x, ⟪A₀ (weakGrad (z n) x - weakGrad v x), weakGrad (z n) x - weakGrad v x⟫ := by
    intro n
    have hun : MemLp (fun x => G x - weakGrad (z n) x) (ENNReal.ofReal 2) :=
      memLp_sub_weakGrad hG (hzW n)
    have hen : MemLp (fun x => weakGrad (z n) x - weakGrad v x) (ENNReal.ofReal 2) :=
      (hmemn n).ae_eq (Eventually.of_forall fun _ => rfl)
    have hi1 : Integrable fun x => ⟪A₀ (G x - weakGrad (z n) x), G x - weakGrad (z n) x⟫ :=
      integrable_inner_apply hA hun hun
    have hi2 : Integrable fun x =>
        ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫ :=
      integrable_inner_apply hA hun hen
    have hi3 : Integrable fun x =>
        ⟪A₀ (weakGrad (z n) x - weakGrad v x), weakGrad (z n) x - weakGrad v x⟫ :=
      integrable_inner_apply hA hen hen
    have hpt : ∀ x : Euc d, ⟪A₀ (G x - weakGrad v x), G x - weakGrad v x⟫
        = ⟪A₀ (G x - weakGrad (z n) x), G x - weakGrad (z n) x⟫
          + 2 * ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫
          + ⟪A₀ (weakGrad (z n) x - weakGrad v x), weakGrad (z n) x - weakGrad v x⟫ := by
      intro x
      have hsum : G x - weakGrad v x
          = (G x - weakGrad (z n) x) + (weakGrad (z n) x - weakGrad v x) := by module
      rw [hsum, inner_apply_add_self A₀ (G x - weakGrad (z n) x)
        (weakGrad (z n) x - weakGrad v x),
        hsymm (weakGrad (z n) x - weakGrad v x) (G x - weakGrad (z n) x)]
      ring
    have hae : (fun x : Euc d => ⟪A₀ (G x - weakGrad v x), G x - weakGrad v x⟫)
        =ᵐ[volume] fun x : Euc d => ⟪A₀ (G x - weakGrad (z n) x), G x - weakGrad (z n) x⟫
          + 2 * ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫
          + ⟪A₀ (weakGrad (z n) x - weakGrad v x), weakGrad (z n) x - weakGrad v x⟫ :=
      Eventually.of_forall hpt
    have hi2' : Integrable fun x =>
        2 * ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫ := hi2.const_mul 2
    have hi12 : Integrable fun x => ⟪A₀ (G x - weakGrad (z n) x), G x - weakGrad (z n) x⟫
        + 2 * ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫ := hi1.add hi2'
    rw [energy_eq, energy_eq, integral_congr_ae hae,
      integral_add hi12 hi3, integral_add hi1 hi2', integral_const_mul]
  -- (vi) the limit is a minimiser
  have hvmin : energy A₀ G v ≤ m₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = energy A₀ G v - m₀ := ⟨_, rfl⟩
    have hκ0 : 0 < κ := by rw [hκdef]; linarith
    obtain ⟨Cu, hCudef⟩ : ∃ Cu : ℝ, Cu = (m₀ + 1) / μ := ⟨_, rfl⟩
    have hCu0 : 0 ≤ Cu := by
      rw [hCudef]
      exact div_nonneg (by linarith) hμ.le
    have hden : 0 < Λ * Cu + 1 := by
      have := mul_nonneg hΛ0 hCu0
      linarith
    obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = κ / (2 * (Λ * Cu + 1)) := ⟨_, rfl⟩
    have hθ0 : 0 < θ := by
      rw [hθdef]
      exact div_pos hκ0 (by linarith)
    have hstep : θ * (2 * (Λ * Cu + 1)) = κ := by
      rw [hθdef]
      exact div_mul_cancel₀ κ (ne_of_gt (by linarith : (0 : ℝ) < 2 * (Λ * Cu + 1)))
    have hθΛ : Λ * (θ * Cu) ≤ κ / 2 := by
      have h1 : θ * (Λ * Cu) ≤ θ * (Λ * Cu + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hθ0.le
      nlinarith [h1, hstep]
    have htend : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)
        + (Λ * θ⁻¹ + Λ) * ∫ x, ‖weakGrad (z n) x - weakGrad v x‖ ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := hEn.const_mul (Λ * θ⁻¹ + Λ)
      simpa using h1.add h2
    obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds (show (0 : ℝ) < κ / 2 by linarith))).exists
    have hn' : 1 / ((n : ℝ) + 1)
        + (Λ * θ⁻¹ + Λ) * (∫ x, ‖weakGrad (z n) x - weakGrad v x‖ ^ 2) < κ / 2 := hn
    have hun : MemLp (fun x => G x - weakGrad (z n) x) (ENNReal.ofReal 2) :=
      memLp_sub_weakGrad hG (hzW n)
    have hen : MemLp (fun x => weakGrad (z n) x - weakGrad v x) (ENNReal.ofReal 2) :=
      (hmemn n).ae_eq (Eventually.of_forall fun _ => rfl)
    have hb1 : (∫ x, ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫)
        ≤ Λ / 2 * (θ * Cu + θ⁻¹ * ∫ x, ‖weakGrad (z n) x - weakGrad v x‖ ^ 2) := by
      have hiL : Integrable fun x =>
          ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫ :=
        integrable_inner_apply hA hun hen
      have hiR : Integrable fun x => Λ / 2 * (θ * ‖G x - weakGrad (z n) x‖ ^ 2
          + θ⁻¹ * ‖weakGrad (z n) x - weakGrad v x‖ ^ 2) :=
        (((integrable_norm_sq hun).const_mul θ).add
          ((integrable_norm_sq hen).const_mul θ⁻¹)).const_mul (Λ / 2)
      have hmono : (∫ x, ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫)
          ≤ ∫ x, Λ / 2 * (θ * ‖G x - weakGrad (z n) x‖ ^ 2
            + θ⁻¹ * ‖weakGrad (z n) x - weakGrad v x‖ ^ 2) := by
        refine integral_mono hiL hiR fun x => ?_
        show ⟪A₀ (G x - weakGrad (z n) x), weakGrad (z n) x - weakGrad v x⟫
          ≤ Λ / 2 * (θ * ‖G x - weakGrad (z n) x‖ ^ 2
            + θ⁻¹ * ‖weakGrad (z n) x - weakGrad v x‖ ^ 2)
        exact inner_apply_le_young hA hθ0 _ _
      have hsplit : (∫ x, Λ / 2 * (θ * ‖G x - weakGrad (z n) x‖ ^ 2
            + θ⁻¹ * ‖weakGrad (z n) x - weakGrad v x‖ ^ 2))
          = Λ / 2 * (θ * (∫ x, ‖G x - weakGrad (z n) x‖ ^ 2)
            + θ⁻¹ * ∫ x, ‖weakGrad (z n) x - weakGrad v x‖ ^ 2) := by
        have hq1 : Integrable fun x => θ * ‖G x - weakGrad (z n) x‖ ^ 2 :=
          (integrable_norm_sq hun).const_mul θ
        have hq2 : Integrable fun x => θ⁻¹ * ‖weakGrad (z n) x - weakGrad v x‖ ^ 2 :=
          (integrable_norm_sq hen).const_mul θ⁻¹
        rw [integral_const_mul, integral_add hq1 hq2, integral_const_mul, integral_const_mul]
      rw [hsplit] at hmono
      have hCun : (∫ x, ‖G x - weakGrad (z n) x‖ ^ 2) ≤ Cu := by
        rw [hCudef]
        exact hCu n
      have hprod : 0 ≤ Λ / 2 * θ * (Cu - ∫ x, ‖G x - weakGrad (z n) x‖ ^ 2) :=
        mul_nonneg (mul_nonneg (by linarith) hθ0.le) (by linarith)
      nlinarith [hmono, hprod]
    have hb2 : (∫ x, ⟪A₀ (weakGrad (z n) x - weakGrad v x), weakGrad (z n) x - weakGrad v x⟫)
        ≤ Λ * ∫ x, ‖weakGrad (z n) x - weakGrad v x‖ ^ 2 := by
      have hiL : Integrable fun x =>
          ⟪A₀ (weakGrad (z n) x - weakGrad v x), weakGrad (z n) x - weakGrad v x⟫ :=
        integrable_inner_apply hA hen hen
      rw [← integral_const_mul]
      refine integral_mono hiL ((integrable_norm_sq hen).const_mul Λ) fun x => ?_
      show ⟪A₀ (weakGrad (z n) x - weakGrad v x), weakGrad (z n) x - weakGrad v x⟫
        ≤ Λ * ‖weakGrad (z n) x - weakGrad v x‖ ^ 2
      exact inner_apply_self_le hA _
    have hE := hexpand n
    have hJ := hzJ n
    linarith
  exact ⟨v, hvW, fun z' hz' => le_trans hvmin (hmle z' hz')⟩

/-! ### The Euler–Lagrange equation -/

/-- **The Euler–Lagrange equation of the frozen Dirichlet minimiser.**  A minimiser `v` of
`z ↦ ∫ ⟪A₀ (G - ∇z), G - ∇z⟫` over `W₀^{1,2}(B)` satisfies `∫ ⟪A₀ (G - ∇v), ∇ζ⟫ = 0` for every
`ζ ∈ W₀^{1,2}(B)`, i.e. `H = G - ∇v` is a weak solution of the frozen equation `div (A₀ H) = 0`
with `W₀^{1,2}` test functions.

For `p = 2` no differentiation under the integral sign is needed: `t ↦ E(v - t ζ)` is the real
quadratic `E(v) + 2 t L + t² Q` with `L = ∫ ⟪A₀ (G - ∇v), ∇ζ⟫`, and a quadratic with a minimum at
`t = 0` has vanishing linear coefficient. -/
theorem euler_lagrange_energy_min {A₀ : Euc d →L[ℝ] Euc d} {Λ : ℝ} (hA : ‖A₀‖ ≤ Λ)
    (hsymm : ∀ ξ η : Euc d, ⟪A₀ ξ, η⟫ = ⟪A₀ η, ξ⟫) {B : Set (Euc d)} {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) {v : Euc d → ℝ} (hv : MemW0 2 B v)
    (hmin : ∀ z : Euc d → ℝ, MemW0 2 B z → energy A₀ G v ≤ energy A₀ G z)
    {ζ : Euc d → ℝ} (hζ : MemW0 2 B ζ) :
    ∫ x, ⟪A₀ (G x - weakGrad v x), weakGrad ζ x⟫ = 0 := by
  have hu : MemLp (fun x => G x - weakGrad v x) (ENNReal.ofReal 2) := memLp_sub_weakGrad hG hv
  have hgζ : MemLp (weakGrad ζ) (ENNReal.ofReal 2) := hζ.memLp_weakGrad
  have hiu : Integrable fun x => ⟪A₀ (G x - weakGrad v x), G x - weakGrad v x⟫ :=
    integrable_inner_apply hA hu hu
  have hiL : Integrable fun x => ⟪A₀ (G x - weakGrad v x), weakGrad ζ x⟫ :=
    integrable_inner_apply hA hu hgζ
  have hiQ : Integrable fun x => ⟪A₀ (weakGrad ζ x), weakGrad ζ x⟫ :=
    integrable_inner_apply hA hgζ hgζ
  have hsm : ∀ (t : ℝ) (a e : Euc d), ⟪A₀ (a + t • e), a + t • e⟫
      = ⟪A₀ a, a⟫ + 2 * t * ⟪A₀ a, e⟫ + t ^ 2 * ⟪A₀ e, e⟫ := by
    intro t a e
    have h1 : ⟪A₀ a, t • e⟫ = t * ⟪A₀ a, e⟫ := real_inner_smul_right _ _ _
    have h2 : ⟪A₀ (t • e), a⟫ = t * ⟪A₀ a, e⟫ := by rw [hsymm (t • e) a, h1]
    have h3 : ⟪A₀ (t • e), t • e⟫ = t ^ 2 * ⟪A₀ e, e⟫ := by
      rw [real_inner_smul_right (A₀ (t • e)) e t, hsymm (t • e) e,
        real_inner_smul_right (A₀ e) e t]
      ring
    rw [inner_apply_add_self A₀ a (t • e), h1, h2, h3]
    ring
  have hE : ∀ t : ℝ, energy A₀ G (v + (-t) • ζ)
      = energy A₀ G v + 2 * t * (∫ x, ⟪A₀ (G x - weakGrad v x), weakGrad ζ x⟫)
        + t ^ 2 * ∫ x, ⟪A₀ (weakGrad ζ x), weakGrad ζ x⟫ := by
    intro t
    have hgr : weakGrad (v + (-t) • ζ) =ᵐ[volume] weakGrad v + (-t) • weakGrad ζ :=
      weakGrad_add_smul_ae ⟨_, hv.hasWeakGradient⟩ ⟨_, hζ.hasWeakGradient⟩ (-t)
    have hpt : ∀ x : Euc d,
        ⟪A₀ (G x - (weakGrad v + (-t) • weakGrad ζ) x),
            G x - (weakGrad v + (-t) • weakGrad ζ) x⟫
          = ⟪A₀ (G x - weakGrad v x), G x - weakGrad v x⟫
            + 2 * t * ⟪A₀ (G x - weakGrad v x), weakGrad ζ x⟫
            + t ^ 2 * ⟪A₀ (weakGrad ζ x), weakGrad ζ x⟫ := by
      intro x
      have hrw : G x - (weakGrad v + (-t) • weakGrad ζ) x
          = (G x - weakGrad v x) + t • weakGrad ζ x := by
        show G x - (weakGrad v x + (-t) • weakGrad ζ x)
          = (G x - weakGrad v x) + t • weakGrad ζ x
        module
      rw [hrw, hsm t (G x - weakGrad v x) (weakGrad ζ x)]
    have hae : (fun x : Euc d => ⟪A₀ (G x - (weakGrad v + (-t) • weakGrad ζ) x),
          G x - (weakGrad v + (-t) • weakGrad ζ) x⟫)
        =ᵐ[volume] fun x : Euc d => ⟪A₀ (G x - weakGrad v x), G x - weakGrad v x⟫
          + 2 * t * ⟪A₀ (G x - weakGrad v x), weakGrad ζ x⟫
          + t ^ 2 * ⟪A₀ (weakGrad ζ x), weakGrad ζ x⟫ := Eventually.of_forall hpt
    have hiL' : Integrable fun x =>
        2 * t * ⟪A₀ (G x - weakGrad v x), weakGrad ζ x⟫ := hiL.const_mul (2 * t)
    have hiQ' : Integrable fun x =>
        t ^ 2 * ⟪A₀ (weakGrad ζ x), weakGrad ζ x⟫ := hiQ.const_mul (t ^ 2)
    have hiuL : Integrable fun x => ⟪A₀ (G x - weakGrad v x), G x - weakGrad v x⟫
        + 2 * t * ⟪A₀ (G x - weakGrad v x), weakGrad ζ x⟫ := hiu.add hiL'
    rw [energy_congr_weakGrad hgr, integral_congr_ae hae, energy_eq,
      integral_add hiuL hiQ', integral_add hiu hiL', integral_const_mul, integral_const_mul]
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ∫ x, ⟪A₀ (G x - weakGrad v x), weakGrad ζ x⟫ := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = ∫ x, ⟪A₀ (weakGrad ζ x), weakGrad ζ x⟫ := ⟨_, rfl⟩
  have hkey : ∀ t : ℝ, 0 ≤ 2 * t * L + t ^ 2 * Q := by
    intro t
    have h := hmin (v + (-t) • ζ) (memW0_add_smul hv hζ (-t))
    rw [hE t, ← hLdef, ← hQdef] at h
    linarith
  have habs : ∀ ε : ℝ, 0 < ε → 2 * |L| ≤ ε * Q := by
    intro ε hε
    rcases le_or_gt 0 L with hL | hL
    · have h := hkey (-ε)
      rw [abs_of_nonneg hL]
      have hmul : ε * (2 * L) ≤ ε * (ε * Q) := by nlinarith [h]
      exact le_of_mul_le_mul_left hmul hε
    · have h := hkey ε
      rw [abs_of_neg hL]
      have hmul : ε * (2 * -L) ≤ ε * (ε * Q) := by nlinarith [h]
      exact le_of_mul_le_mul_left hmul hε
  rw [← hLdef]
  by_contra hL0
  have hLpos : 0 < |L| := abs_pos.2 hL0
  have hq := habs (|L| / (|Q| + 1)) (div_pos hLpos (by positivity))
  have h1 : |L| / (|Q| + 1) * Q ≤ |L| / (|Q| + 1) * |Q| :=
    mul_le_mul_of_nonneg_left (le_abs_self Q) (by positivity)
  have h2 : |L| / (|Q| + 1) * |Q| < |L| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg Q, hLpos]
  linarith

/-! ### The frozen Dirichlet replacement field -/

/-- **The frozen Dirichlet replacement field.**  For a constant symmetric `μ`-elliptic,
`Λ`-bounded `A₀` and an `L²` field `G` there is `ψ ∈ W₀^{1,2}(B̄(c,s))` such that `H = G - ∇ψ` is
an `L²` weak solution of the frozen equation `div (A₀ H) = 0` tested against `W₀^{1,2}(B̄(c,s))`.

With `G = ∇w` this is exactly the pair `(h, ψ) = (w - ψ, w - h)` needed by
`Komlos.Literature.frozen_energy_estimate`, except that `H` is not yet known to be the *gradient
of a `C¹` function*: that is Weyl's lemma, the outstanding input recorded in the `TODO(frozen)`
of `Komlos.Literature.exists_frozen_replacement_data`. -/
theorem exists_frozen_replacement_field (hd : 0 < d) {A₀ : Euc d →L[ℝ] Euc d} {μ Λ : ℝ}
    (hμ : 0 < μ) (hell : ∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) (hA : ‖A₀‖ ≤ Λ)
    (hsymm : ∀ ξ η : Euc d, ⟪A₀ ξ, η⟫ = ⟪A₀ η, ξ⟫)
    {c : Euc d} {s : ℝ} (hs : 0 ≤ s) {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal 2)) :
    ∃ ψ : Euc d → ℝ, MemW0 2 (Metric.closedBall c s) ψ ∧
      MemLp (fun x => G x - weakGrad ψ x) (ENNReal.ofReal 2) ∧
      ∀ ζ : Euc d → ℝ, MemW0 2 (Metric.closedBall c s) ζ →
        ∫ x, ⟪A₀ (G x - weakGrad ψ x), weakGrad ζ x⟫ = 0 := by
  obtain ⟨v, hvW, hvmin⟩ := exists_energy_min hd hμ hell hA hsymm hs hG
  exact ⟨v, hvW, memLp_sub_weakGrad hG hvW,
    fun ζ hζ => euler_lagrange_energy_min hA hsymm hG hvW hvmin hζ⟩

end FrozenDirichlet

end Komlos.Literature
