import Komlos.Literature.Regularized.InteriorHarmonicAux

/-!
# The `Ψ`-harmonic replacement on a ball (lane `L3b`)

The comparison function of link 6: given an `L²` field `G` (in the application `G = ∇v`) and a
ball `B`, the **`Ψ`-Dirichlet energy**

`regDirEnergy Ψ G z = ∫ (Ψ (G - ∇z) - Ψ 0)`,  `z ∈ W₀^{1,2}(B)`,

attains its infimum, and the minimiser satisfies `∫ ⟪∇Ψ (G - ∇z), ∇ζ⟫ = 0` for every
`ζ ∈ W₀^{1,2}(B)`.  With `G = ∇v` the field `H = G - ∇z` is the gradient field of the
`Ψ`-harmonic replacement `h = v - z` of `v` on `B`.

The file is the `Ψ`-analogue of `Komlos/Literature/PLaplacian/FrozenDirichlet.lean` (the same
argument for the frozen *quadratic* energy `∫ ⟪A₀(G - ∇z), G - ∇z⟫`), and follows it step by
step.  Two things replace the quadratic structure:

* the parallelogram law becomes **strong convexity**, `IsRegProfileWith.two_mul_midpoint_add_le`:
  `2 Ψ((a+b)/2) + (c/4)‖a-b‖² ≤ Ψ a + Ψ b`, a consequence of the quadratic lower Taylor bound
  `IsRegProfileWith.add_inner_add_half_le`;
* the Euler–Lagrange equation is obtained **without differentiating under the integral sign**:
  the two-sided Taylor bound gives
  `E(z + tζ) ≤ E(z) - t ∫ ⟪∇Ψ(G - ∇z), ∇ζ⟫ + (C/2) t² ∫ ‖∇ζ‖²`, and minimality at `t` of both
  signs forces the linear coefficient to vanish.

Normalising by `Ψ 0` is what makes the energy finite: `0 ≤ Ψ q - Ψ 0 ≤ (C/2)‖q‖²`
(`IsRegProfileWith.quadratic_lower`, `quadratic_upper`), so the integrand is dominated by an
integrable function as soon as `G - ∇z ∈ L²`.  Since `Ψ 0` is a constant, subtracting it does not
change the minimisers or the Euler–Lagrange equation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {Ψ : Euc d → ℝ} {c C : ℝ}

/-! ### Strong convexity and the two-sided Taylor bound -/

/-- **Strong convexity of the profile**: `2 Ψ((a+b)/2) + (c/4) ‖a-b‖² ≤ Ψ a + Ψ b`.  This is what
replaces the parallelogram law of the quadratic case. -/
theorem IsRegProfileWith.two_mul_midpoint_add_le (h : IsRegProfileWith Ψ c C) (a b : Euc d) :
    2 * Ψ ((2 : ℝ)⁻¹ • (a + b)) + c / 4 * ‖a - b‖ ^ 2 ≤ Ψ a + Ψ b := by
  set m : Euc d := (2 : ℝ)⁻¹ • (a + b) with hm
  have ha : m + (2 : ℝ)⁻¹ • (a - b) = a := by rw [hm]; module
  have hb : m + (2 : ℝ)⁻¹ • (b - a) = b := by rw [hm]; module
  have h1 := h.add_inner_add_half_le m ((2 : ℝ)⁻¹ • (a - b))
  have h2 := h.add_inner_add_half_le m ((2 : ℝ)⁻¹ • (b - a))
  rw [ha] at h1
  rw [hb] at h2
  have hn1 : ‖(2 : ℝ)⁻¹ • (a - b)‖ ^ 2 = ‖a - b‖ ^ 2 / 4 := by
    rw [norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
    ring
  have hn2 : ‖(2 : ℝ)⁻¹ • (b - a)‖ ^ 2 = ‖a - b‖ ^ 2 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹),
      ← norm_neg (a - b)]
    have : -(a - b) = b - a := by abel
    rw [this]
    ring
  have hinner : ⟪gradient Ψ m, (2 : ℝ)⁻¹ • (a - b)⟫ + ⟪gradient Ψ m, (2 : ℝ)⁻¹ • (b - a)⟫ = 0 := by
    rw [← inner_add_right]
    have : (2 : ℝ)⁻¹ • (a - b) + (2 : ℝ)⁻¹ • (b - a) = 0 := by module
    rw [this, inner_zero_right]
  rw [hn1] at h1
  rw [hn2] at h2
  linarith

/-- **The two-sided Taylor bound**: `|Ψ (q + ξ) - Ψ q - ⟪∇Ψ q, ξ⟫| ≤ (C/2) ‖ξ‖²`. -/
theorem IsRegProfileWith.abs_taylor_le (h : IsRegProfileWith Ψ c C) (q ξ : Euc d) :
    |Ψ (q + ξ) - Ψ q - ⟪gradient Ψ q, ξ⟫| ≤ C / 2 * ‖ξ‖ ^ 2 := by
  have h1 := h.add_inner_add_half_le q ξ
  have h2 := h.le_add_inner_add_half q ξ
  have h3 : 0 ≤ c / 2 * ‖ξ‖ ^ 2 := mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The `Ψ`-Dirichlet energy -/

/-- The **`Ψ`-Dirichlet energy** of the competitor `z ∈ W₀^{1,2}(B)` relative to the field `G`,
normalised by `Ψ 0` so that the integral converges. -/
noncomputable def regDirEnergy (Ψ : Euc d → ℝ) (G : Euc d → Euc d) (z : Euc d → ℝ) : ℝ :=
  ∫ x, (Ψ (G x - weakGrad z x) - Ψ 0)

/-- The normalised profile is nonnegative and dominated by a multiple of the square of the norm. -/
theorem IsRegProfileWith.shifted_bounds (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    0 ≤ Ψ q - Ψ 0 ∧ Ψ q - Ψ 0 ≤ C / 2 * ‖q‖ ^ 2 := by
  have h1 := h.quadratic_lower q
  have h2 := h.quadratic_upper q
  have h3 : 0 ≤ c / 2 * ‖q‖ ^ 2 := mul_nonneg (by linarith [h.c_pos]) (sq_nonneg _)
  exact ⟨by linarith, by linarith⟩

/-- The integrand of `regDirEnergy` is integrable for an `L²` field. -/
theorem integrable_shifted_profile (h : IsRegProfileWith Ψ c C) {F : Euc d → Euc d}
    (hF : MemLp F (ENNReal.ofReal 2)) : Integrable fun x => Ψ (F x) - Ψ 0 := by
  have hdom : Integrable fun x => C / 2 * ‖F x‖ ^ 2 :=
    (Komlos.Literature.FrozenDirichlet.integrable_norm_sq hF).const_mul _
  refine hdom.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((h.toIsRegProfile.contDiff.continuous.comp_aestronglyMeasurable
      hF.aestronglyMeasurable).sub aestronglyMeasurable_const)
  · have hb := h.shifted_bounds (F x)
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2

/-- Lower bound: the energy controls the `L²` norm of the competitor field. -/
theorem mul_integral_le_regDirEnergy (h : IsRegProfileWith Ψ c C) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) {B : Set (Euc d)} {z : Euc d → ℝ} (hz : MemW0 2 B z) :
    c / 2 * (∫ x, ‖G x - weakGrad z x‖ ^ 2) ≤ regDirEnergy Ψ G z := by
  have hu : MemLp (fun x => G x - weakGrad z x) (ENNReal.ofReal 2) :=
    Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG hz
  rw [regDirEnergy, ← integral_const_mul]
  refine integral_mono ((Komlos.Literature.FrozenDirichlet.integrable_norm_sq hu).const_mul _)
    (integrable_shifted_profile h hu) fun x => ?_
  have := h.quadratic_lower (G x - weakGrad z x)
  show c / 2 * ‖G x - weakGrad z x‖ ^ 2 ≤ Ψ (G x - weakGrad z x) - Ψ 0
  linarith

/-- Upper bound: the energy is controlled by the `L²` norm of the competitor field. -/
theorem regDirEnergy_le (h : IsRegProfileWith Ψ c C) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) {B : Set (Euc d)} {z : Euc d → ℝ} (hz : MemW0 2 B z) :
    regDirEnergy Ψ G z ≤ C / 2 * ∫ x, ‖G x - weakGrad z x‖ ^ 2 := by
  have hu : MemLp (fun x => G x - weakGrad z x) (ENNReal.ofReal 2) :=
    Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG hz
  rw [regDirEnergy, ← integral_const_mul]
  refine integral_mono (integrable_shifted_profile h hu)
    ((Komlos.Literature.FrozenDirichlet.integrable_norm_sq hu).const_mul _) fun x => ?_
  exact (h.shifted_bounds (G x - weakGrad z x)).2

/-- The energy is nonnegative. -/
theorem regDirEnergy_nonneg (h : IsRegProfileWith Ψ c C) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) {B : Set (Euc d)} {z : Euc d → ℝ} (hz : MemW0 2 B z) :
    0 ≤ regDirEnergy Ψ G z := by
  refine le_trans ?_ (mul_integral_le_regDirEnergy h hG hz)
  exact mul_nonneg (by linarith [h.c_pos]) (integral_nonneg fun _ => sq_nonneg _)


/-! ### The infimum and the midpoint estimate -/

/-- The infimum of the `Ψ`-Dirichlet energy over `W₀^{1,2}(B)`. -/
theorem exists_regDirEnergy_inf (h : IsRegProfileWith Ψ c C) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) (B : Set (Euc d)) :
    ∃ m : ℝ, 0 ≤ m ∧ (∀ z : Euc d → ℝ, MemW0 2 B z → m ≤ regDirEnergy Ψ G z) ∧
      ∀ δ : ℝ, 0 < δ → ∃ z : Euc d → ℝ, MemW0 2 B z ∧ regDirEnergy Ψ G z < m + δ := by
  have : Nonempty {z : Euc d → ℝ // MemW0 2 B z} := ⟨⟨0, MemW0.zero⟩⟩
  have hbdd : BddBelow (Set.range fun z : {z : Euc d → ℝ // MemW0 2 B z} =>
      regDirEnergy Ψ G z.1) := by
    refine ⟨0, ?_⟩
    rintro y ⟨z, rfl⟩
    exact regDirEnergy_nonneg h hG z.2
  refine ⟨⨅ z : {z : Euc d → ℝ // MemW0 2 B z}, regDirEnergy Ψ G z.1,
    le_ciInf fun z => regDirEnergy_nonneg h hG z.2, fun z hz => ciInf_le hbdd ⟨z, hz⟩,
    fun δ hδ => ?_⟩
  obtain ⟨z, hz⟩ := exists_lt_of_ciInf_lt
    (f := fun z : {z : Euc d → ℝ // MemW0 2 B z} => regDirEnergy Ψ G z.1)
    (lt_add_of_pos_right _ hδ)
  exact ⟨z.1, z.2, hz⟩

/-- **The key estimate of the direct method**: by strong convexity, the `L²` distance of the
gradients of two competitors is controlled by how far their energies lie above the infimum. -/
theorem mul_integral_weakGrad_sub_sq_le (h : IsRegProfileWith Ψ c C) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) {B : Set (Euc d)} {m : ℝ}
    (hm : ∀ z : Euc d → ℝ, MemW0 2 B z → m ≤ regDirEnergy Ψ G z)
    {z₁ z₂ : Euc d → ℝ} (h₁ : MemW0 2 B z₁) (h₂ : MemW0 2 B z₂) :
    c / 2 * (∫ x, ‖weakGrad z₁ x - weakGrad z₂ x‖ ^ 2) ≤
      2 * regDirEnergy Ψ G z₂ + 2 * regDirEnergy Ψ G z₁ - 4 * m := by
  have hwW : MemW0 2 B (z₂ - z₁) := Komlos.Literature.FrozenDirichlet.memW0_sub h₂ h₁
  have hzmW : MemW0 2 B (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) :=
    Komlos.Literature.FrozenDirichlet.memW0_add_smul h₁ hwW _
  have hgw : weakGrad (z₂ - z₁) =ᵐ[volume] weakGrad z₂ - weakGrad z₁ :=
    Komlos.Literature.FrozenDirichlet.weakGrad_sub_ae ⟨_, h₂.hasWeakGradient⟩
      ⟨_, h₁.hasWeakGradient⟩
  have hgm : weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) =ᵐ[volume]
      weakGrad z₁ + (2 : ℝ)⁻¹ • weakGrad (z₂ - z₁) :=
    Komlos.Literature.FrozenDirichlet.weakGrad_add_smul_ae ⟨_, h₁.hasWeakGradient⟩
      ⟨_, hwW.hasWeakGradient⟩ _
  -- the pointwise strong-convexity inequality
  have hpt : ∀ᵐ x : Euc d,
      2 * (Ψ (G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x) - Ψ 0) +
          c / 4 * ‖weakGrad z₁ x - weakGrad z₂ x‖ ^ 2 ≤
        (Ψ (G x - weakGrad z₁ x) - Ψ 0) + (Ψ (G x - weakGrad z₂ x) - Ψ 0) := by
    filter_upwards [hgm, hgw] with x hx hy
    have hx' : weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x
        = weakGrad z₁ x + (2 : ℝ)⁻¹ • weakGrad (z₂ - z₁) x := hx
    have hy' : weakGrad (z₂ - z₁) x = weakGrad z₂ x - weakGrad z₁ x := hy
    have hmid : G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x
        = (2 : ℝ)⁻¹ • ((G x - weakGrad z₁ x) + (G x - weakGrad z₂ x)) := by
      rw [hx', hy']; module
    have hdiff : (G x - weakGrad z₁ x) - (G x - weakGrad z₂ x)
        = weakGrad z₂ x - weakGrad z₁ x := by module
    have hkey := h.two_mul_midpoint_add_le (G x - weakGrad z₁ x) (G x - weakGrad z₂ x)
    rw [← hmid, hdiff] at hkey
    have hnorm : ‖weakGrad z₂ x - weakGrad z₁ x‖ = ‖weakGrad z₁ x - weakGrad z₂ x‖ :=
      norm_sub_rev _ _
    rw [hnorm] at hkey
    linarith
  -- integrability of the two sides
  have hu1 : MemLp (fun x => G x - weakGrad z₁ x) (ENNReal.ofReal 2) :=
    Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG h₁
  have hu2 : MemLp (fun x => G x - weakGrad z₂ x) (ENNReal.ofReal 2) :=
    Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG h₂
  have hum : MemLp (fun x => G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x)
      (ENNReal.ofReal 2) := Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG hzmW
  have hD : MemLp (fun x => weakGrad z₁ x - weakGrad z₂ x) (ENNReal.ofReal 2) :=
    (h₁.memLp_weakGrad.sub h₂.memLp_weakGrad).ae_eq (Eventually.of_forall fun _ => rfl)
  have hiL : Integrable fun x =>
      2 * (Ψ (G x - weakGrad (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) x) - Ψ 0) +
        c / 4 * ‖weakGrad z₁ x - weakGrad z₂ x‖ ^ 2 :=
    ((integrable_shifted_profile h hum).const_mul 2).add
      ((Komlos.Literature.FrozenDirichlet.integrable_norm_sq hD).const_mul _)
  have hiR : Integrable fun x =>
      (Ψ (G x - weakGrad z₁ x) - Ψ 0) + (Ψ (G x - weakGrad z₂ x) - Ψ 0) :=
    (integrable_shifted_profile h hu1).add (integrable_shifted_profile h hu2)
  have hint := integral_mono_ae hiL hiR hpt
  rw [integral_add ((integrable_shifted_profile h hum).const_mul 2)
      ((Komlos.Literature.FrozenDirichlet.integrable_norm_sq hD).const_mul _),
    integral_add (integrable_shifted_profile h hu1) (integrable_shifted_profile h hu2),
    integral_const_mul, integral_const_mul] at hint
  have hmm : m ≤ regDirEnergy Ψ G (z₁ + (2 : ℝ)⁻¹ • (z₂ - z₁)) := hm _ hzmW
  simp only [regDirEnergy] at hint hmm ⊢
  linarith


/-! ### Continuity of the energy along `L²`-convergent gradients -/

/-- `∇Ψ ∘ F` inherits every `L^p` bound of `F`, because `‖∇Ψ q‖ ≤ C ‖q‖`. -/
theorem repl_memLp_gradient_comp (h : IsRegProfileWith Ψ c C) {p : ℝ≥0∞} {F : Euc d → Euc d}
    (hF : MemLp F p) : MemLp (fun x => gradient Ψ (F x)) p := by
  refine (hF.const_smul C).mono ?_ (Eventually.of_forall fun x => ?_)
  · exact h.toIsRegProfile.contDiff_gradient.continuous.comp_aestronglyMeasurable
      hF.aestronglyMeasurable
  · show ‖gradient Ψ (F x)‖ ≤ ‖(C • F) x‖
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h.C_nonneg]
    exact h.norm_gradient_le (F x)

/-- **A quantitative upper semicontinuity of the `Ψ`-Dirichlet energy**: the energy of `w` exceeds
that of `z` by at most a `θ`-weighted Young splitting of the linear term plus the quadratic
remainder.  Letting `∇w → ∇z` in `L²` and then `θ → 0` shows that the energy passes to the limit
in the direct method. -/
theorem regDirEnergy_le_of_close (h : IsRegProfileWith Ψ c C) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) {B : Set (Euc d)} {z w : Euc d → ℝ}
    (hz : MemW0 2 B z) (hw : MemW0 2 B w) {θ : ℝ} (hθ : 0 < θ) :
    regDirEnergy Ψ G w ≤ regDirEnergy Ψ G z
      + θ / 2 * (C ^ 2 * ∫ x, ‖G x - weakGrad z x‖ ^ 2)
      + (1 / (2 * θ) + C / 2) * ∫ x, ‖weakGrad z x - weakGrad w x‖ ^ 2 := by
  have huz : MemLp (fun x => G x - weakGrad z x) (ENNReal.ofReal 2) :=
    Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG hz
  have huw : MemLp (fun x => G x - weakGrad w x) (ENNReal.ofReal 2) :=
    Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG hw
  have hD : MemLp (fun x => weakGrad z x - weakGrad w x) (ENNReal.ofReal 2) :=
    (hz.memLp_weakGrad.sub hw.memLp_weakGrad).ae_eq (Eventually.of_forall fun _ => rfl)
  have hi1 : Integrable fun x => Ψ (G x - weakGrad z x) - Ψ 0 :=
    integrable_shifted_profile h huz
  have hi2 : Integrable fun x => θ / 2 * (C ^ 2 * ‖G x - weakGrad z x‖ ^ 2) :=
    ((Komlos.Literature.FrozenDirichlet.integrable_norm_sq huz).const_mul _).const_mul _
  have hi3 : Integrable fun x => (1 / (2 * θ) + C / 2) * ‖weakGrad z x - weakGrad w x‖ ^ 2 :=
    (Komlos.Literature.FrozenDirichlet.integrable_norm_sq hD).const_mul _
  have hpt : ∀ x : Euc d, Ψ (G x - weakGrad w x) - Ψ 0 ≤
      (Ψ (G x - weakGrad z x) - Ψ 0) + θ / 2 * (C ^ 2 * ‖G x - weakGrad z x‖ ^ 2) +
        (1 / (2 * θ) + C / 2) * ‖weakGrad z x - weakGrad w x‖ ^ 2 := by
    intro x
    set u : Euc d := G x - weakGrad z x with hu
    set e : Euc d := weakGrad z x - weakGrad w x with he
    have hsum : G x - weakGrad w x = u + e := by rw [hu, he]; module
    have htay := h.le_add_inner_add_half u e
    rw [← hsum] at htay
    have hcs : ⟪gradient Ψ u, e⟫ ≤ ‖gradient Ψ u‖ * ‖e‖ := real_inner_le_norm _ _
    have hyoung : ‖gradient Ψ u‖ * ‖e‖ ≤ θ / 2 * ‖gradient Ψ u‖ ^ 2 + 1 / (2 * θ) * ‖e‖ ^ 2 := by
      rw [← sub_nonneg]
      have key : θ / 2 * ‖gradient Ψ u‖ ^ 2 + 1 / (2 * θ) * ‖e‖ ^ 2 - ‖gradient Ψ u‖ * ‖e‖
          = (θ * ‖gradient Ψ u‖ - ‖e‖) ^ 2 / (2 * θ) := by
        field_simp
        ring
      rw [key]
      positivity
    have hgrad : ‖gradient Ψ u‖ ≤ C * ‖u‖ := h.norm_gradient_le u
    have hg0 : 0 ≤ ‖gradient Ψ u‖ := norm_nonneg _
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have hsq2 : ‖gradient Ψ u‖ ^ 2 ≤ C ^ 2 * ‖u‖ ^ 2 := by nlinarith [hgrad, hg0, hu0]
    nlinarith [htay, hcs, hyoung, hsq2, hθ]
  have hi12 : Integrable fun x => (Ψ (G x - weakGrad z x) - Ψ 0) +
      θ / 2 * (C ^ 2 * ‖G x - weakGrad z x‖ ^ 2) := hi1.add hi2
  have hisum : Integrable fun x => (Ψ (G x - weakGrad z x) - Ψ 0) +
      θ / 2 * (C ^ 2 * ‖G x - weakGrad z x‖ ^ 2) +
      (1 / (2 * θ) + C / 2) * ‖weakGrad z x - weakGrad w x‖ ^ 2 := hi12.add hi3
  have hkey := integral_mono (integrable_shifted_profile h huw) hisum hpt
  rw [integral_add hi12 hi3, integral_add hi1 hi2, integral_const_mul,
    integral_const_mul, integral_const_mul] at hkey
  simpa only [regDirEnergy] using hkey


/-! ### The direct method -/

/-- **The direct method for the `Ψ`-Dirichlet energy.**  The energy
`z ↦ ∫ (Ψ (G - ∇z) - Ψ 0)` attains its infimum on `W₀^{1,2}(B̄(cB, s))`.

Proof (the `Ψ`-analogue of `Komlos.Literature.FrozenDirichlet.exists_energy_min`): a minimising
sequence has `∫ ‖G - ∇z n‖²` uniformly bounded by the quadratic lower bound; the midpoint
competitor together with strong convexity (`mul_integral_weakGrad_sub_sq_le`) makes `∇z n` Cauchy
in `L²`; the ball Poincaré inequality makes `z n` Cauchy in the graph norm, so
`Komlos.Literature.W0_complete` produces the limit; and the energy passes to the limit by
`regDirEnergy_le_of_close`, letting first `n → ∞` and then the Young parameter `θ → 0`. -/
theorem exists_regDirEnergy_min (hd : 0 < d) (h : IsRegProfileWith Ψ c C)
    {cB : Euc d} {s : ℝ} (hs : 0 ≤ s) {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal 2)) :
    ∃ v : Euc d → ℝ, MemW0 2 (Metric.closedBall cB s) v ∧
      ∀ z : Euc d → ℝ, MemW0 2 (Metric.closedBall cB s) z →
        regDirEnergy Ψ G v ≤ regDirEnergy Ψ G z := by
  have hc2 : (0 : ℝ) < c / 2 := by linarith [h.c_pos]
  obtain ⟨m₀, hm₀0, hmle, hmlt⟩ := exists_regDirEnergy_inf h hG (Metric.closedBall cB s)
  choose z hzW hzJ using fun n : ℕ => hmlt (1 / ((n : ℝ) + 1)) (by positivity)
  have hδ1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  -- (i) a uniform `L²` bound for the competitor fields
  have hCu : ∀ n : ℕ, ∫ x, ‖G x - weakGrad (z n) x‖ ^ 2 ≤ (m₀ + 1) / (c / 2) := by
    intro n
    have h1 := mul_integral_le_regDirEnergy h hG (hzW n)
    have h2 := hzJ n
    have h3 := hδ1 n
    rw [le_div_iff₀ hc2, mul_comm]
    linarith
  -- (ii) the gradients are Cauchy in `L²`
  have hCauchy : ∀ k l : ℕ, c / 2 * ∫ x, ‖weakGrad (z k) x - weakGrad (z l) x‖ ^ 2 ≤
      2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1)) := by
    intro k l
    have hkey := mul_integral_weakGrad_sub_sq_le h hG hmle (hzW k) (hzW l)
    have h1 := hzJ k
    have h2 := hzJ l
    linarith
  -- (iii) the graph-norm Cauchy condition of `W0_complete`
  have hgradMemLp : ∀ k l : ℕ, MemLp (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) :=
    fun k l => (hzW k).memLp_weakGrad.sub (hzW l).memLp_weakGrad
  have hnorm : ∀ k l : ℕ,
      c / 2 * ((eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume).toReal) ^ 2
        ≤ 2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1)) := by
    intro k l
    rw [← Komlos.Literature.integral_norm_sq_eq_sq_eLpNorm (hgradMemLp k l)]
    exact hCauchy k l
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 2 * s + 1 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hTdef]; linarith
  have hpo : ∀ k l : ℕ, eLpNorm (z k - z l) (ENNReal.ofReal 2) volume
      ≤ ENNReal.ofReal T *
        eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume := by
    intro k l
    have hW : MemW0 2 (Metric.closedBall cB s) (z k - z l) :=
      Komlos.Literature.FrozenDirichlet.memW0_sub (hzW k) (hzW l)
    have hkey := hW.eLpNorm_le_eLpNorm_weakGrad_closedBall (T := T) hd one_lt_two hs
      (by rw [hTdef]; linarith)
    have hcg : eLpNorm (weakGrad (z k - z l)) (ENNReal.ofReal 2) volume
        = eLpNorm (weakGrad (z k) - weakGrad (z l)) (ENNReal.ofReal 2) volume :=
      eLpNorm_congr_ae (Komlos.Literature.FrozenDirichlet.weakGrad_sub_ae
        ⟨_, (hzW k).hasWeakGradient⟩ ⟨_, (hzW l).hasWeakGradient⟩)
    rwa [hcg] at hkey
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
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / ((c / 2) * e ^ 2))
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h4 : 4 < ((N : ℝ) + 1) * ((c / 2) * e ^ 2) := by
      have hNgt : 4 / ((c / 2) * e ^ 2) < (N : ℝ) + 1 := by linarith [hN]
      rwa [div_lt_iff₀ (mul_pos hc2 (pow_pos he0 2))] at hNgt
    have hlt : 4 * (1 / ((N : ℝ) + 1)) < (c / 2) * e ^ 2 := by
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
    have hmu : (c / 2) * X ^ 2 ≤ 2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1)) := by
      rw [hXdef]
      exact hnorm k l
    have hsq : X ^ 2 < e ^ 2 := by
      have hmlt : (c / 2) * X ^ 2 < (c / 2) * e ^ 2 := by linarith
      exact lt_of_mul_lt_mul_left hmlt hc2.le
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
  obtain ⟨v, hvW, hvT⟩ := Komlos.Literature.W0_complete one_lt_two z hzW hcauchyE
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
      have hh := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hgradT
      simpa [Function.comp_def] using hh
    have h2 : Tendsto (fun n : ℕ =>
        ((eLpNorm (weakGrad (z n) - weakGrad v) (ENNReal.ofReal 2) volume).toReal) ^ 2)
        atTop (𝓝 0) := by
      have hh := h1.pow 2
      simpa using hh
    refine h2.congr fun n => ?_
    exact (Komlos.Literature.integral_norm_sq_eq_sq_eLpNorm (hmemn n)).symm
  -- (v) the energy passes to the limit
  have hK0 : (0 : ℝ) ≤ (m₀ + 1) / (c / 2) := by positivity
  have hvle : regDirEnergy Ψ G v ≤ m₀ := by
    refine le_of_forall_sub_le fun ε hε => ?_
    obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ε / (3 * (C ^ 2 * ((m₀ + 1) / (c / 2)) + 1)) := ⟨_, rfl⟩
    have hden : (0 : ℝ) < 3 * (C ^ 2 * ((m₀ + 1) / (c / 2)) + 1) := by positivity
    have hθ : 0 < θ := by rw [hθdef]; exact div_pos hε hden
    have hsmall : θ / 2 * (C ^ 2 * ((m₀ + 1) / (c / 2))) < ε / 3 := by
      have hpos : (0 : ℝ) ≤ C ^ 2 * ((m₀ + 1) / (c / 2)) := by positivity
      have hid : θ * (3 * (C ^ 2 * ((m₀ + 1) / (c / 2)) + 1)) = ε := by
        rw [hθdef]
        exact div_mul_cancel₀ ε hden.ne'
      have hgap : 0 < θ * (C ^ 2 * ((m₀ + 1) / (c / 2)) / 2 + 1) := mul_pos hθ (by linarith)
      linarith [hid, hgap]
    have htend : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) +
        (1 / (2 * θ) + C / 2) * (∫ x, ‖weakGrad (z n) x - weakGrad v x‖ ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := hEn.const_mul (1 / (2 * θ) + C / 2)
      simpa using h1.add h2
    obtain ⟨N, hN⟩ :=
      (htend.eventually (gt_mem_nhds (show (0 : ℝ) < 2 * ε / 3 by linarith))).exists
    have hclose := regDirEnergy_le_of_close h hG (hzW N) hvW hθ
    have hmono : θ / 2 * (C ^ 2 * ∫ x, ‖G x - weakGrad (z N) x‖ ^ 2) ≤
        θ / 2 * (C ^ 2 * ((m₀ + 1) / (c / 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hCu N) (sq_nonneg C))
        (by linarith : (0 : ℝ) ≤ θ / 2)
    have hzN := hzJ N
    linarith
  exact ⟨v, hvW, fun w hw => le_trans hvle (hmle w hw)⟩


/-! ### The Euler–Lagrange equation -/

/-- **The Euler–Lagrange equation of the `Ψ`-Dirichlet minimiser**:
`∫ ⟪∇Ψ (G - ∇v), ∇ζ⟫ = 0` for every `ζ ∈ W₀^{1,2}(B)`.

No differentiation under the integral sign is needed: the two-sided Taylor bound
(`IsRegProfileWith.le_add_inner_add_half`) gives
`E(v + tζ) ≤ E(v) - t ∫ ⟪∇Ψ(G - ∇v), ∇ζ⟫ + (C/2) t² ∫ ‖∇ζ‖²`, and minimality at `t` of both
signs forces the linear coefficient to vanish. -/
theorem euler_lagrange_regDirEnergy_min (h : IsRegProfileWith Ψ c C) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal 2)) {B : Set (Euc d)} {v : Euc d → ℝ} (hv : MemW0 2 B v)
    (hmin : ∀ z : Euc d → ℝ, MemW0 2 B z → regDirEnergy Ψ G v ≤ regDirEnergy Ψ G z)
    {ζ : Euc d → ℝ} (hζ : MemW0 2 B ζ) :
    (∫ x, ⟪gradient Ψ (G x - weakGrad v x), weakGrad ζ x⟫) = 0 := by
  have hidn : ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have huv : MemLp (fun x => G x - weakGrad v x) (ENNReal.ofReal 2) :=
    Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG hv
  have hΦ : MemLp (fun x => gradient Ψ (G x - weakGrad v x)) (ENNReal.ofReal 2) :=
    repl_memLp_gradient_comp h huv
  have hZ : MemLp (weakGrad ζ) (ENNReal.ofReal 2) := hζ.memLp_weakGrad
  have hI : Integrable fun x => ⟪gradient Ψ (G x - weakGrad v x), weakGrad ζ x⟫ := by
    simpa using Komlos.Literature.FrozenDirichlet.integrable_inner_apply hidn hΦ hZ
  have hNi : Integrable fun x => ‖weakGrad ζ x‖ ^ 2 :=
    Komlos.Literature.FrozenDirichlet.integrable_norm_sq hZ
  have hi1 : Integrable fun x => Ψ (G x - weakGrad v x) - Ψ 0 :=
    integrable_shifted_profile h huv
  set I : ℝ := ∫ x, ⟪gradient Ψ (G x - weakGrad v x), weakGrad ζ x⟫ with hIdef
  set N : ℝ := ∫ x, ‖weakGrad ζ x‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun _ => sq_nonneg _
  have hC0 : (0 : ℝ) ≤ C := h.C_nonneg
  -- the variational inequality at the perturbation `v + t ζ`
  have hkey : ∀ t : ℝ, 0 ≤ (-t) * I + (C / 2 * t ^ 2) * N := by
    intro t
    have hzt : MemW0 2 B (v + t • ζ) := Komlos.Literature.FrozenDirichlet.memW0_add_smul hv hζ t
    have hgt : weakGrad (v + t • ζ) =ᵐ[volume] weakGrad v + t • weakGrad ζ :=
      Komlos.Literature.FrozenDirichlet.weakGrad_add_smul_ae ⟨_, hv.hasWeakGradient⟩
        ⟨_, hζ.hasWeakGradient⟩ t
    have hut : MemLp (fun x => G x - weakGrad (v + t • ζ) x) (ENNReal.ofReal 2) :=
      Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hG hzt
    have hi2 : Integrable fun x =>
        (-t) * ⟪gradient Ψ (G x - weakGrad v x), weakGrad ζ x⟫ := hI.const_mul (-t)
    have hi3 : Integrable fun x => (C / 2 * t ^ 2) * ‖weakGrad ζ x‖ ^ 2 := hNi.const_mul _
    have hi12 : Integrable fun x => (Ψ (G x - weakGrad v x) - Ψ 0) +
        (-t) * ⟪gradient Ψ (G x - weakGrad v x), weakGrad ζ x⟫ := hi1.add hi2
    have hisum : Integrable fun x => (Ψ (G x - weakGrad v x) - Ψ 0) +
        (-t) * ⟪gradient Ψ (G x - weakGrad v x), weakGrad ζ x⟫ +
        (C / 2 * t ^ 2) * ‖weakGrad ζ x‖ ^ 2 := hi12.add hi3
    have hpt : ∀ᵐ x : Euc d, Ψ (G x - weakGrad (v + t • ζ) x) - Ψ 0 ≤
        (Ψ (G x - weakGrad v x) - Ψ 0) +
          (-t) * ⟪gradient Ψ (G x - weakGrad v x), weakGrad ζ x⟫ +
          (C / 2 * t ^ 2) * ‖weakGrad ζ x‖ ^ 2 := by
      filter_upwards [hgt] with x hx
      have hx' : weakGrad (v + t • ζ) x = weakGrad v x + t • weakGrad ζ x := hx
      have hsum : G x - weakGrad (v + t • ζ) x
          = (G x - weakGrad v x) + (-t) • weakGrad ζ x := by rw [hx']; module
      have htay := h.le_add_inner_add_half (G x - weakGrad v x) ((-t) • weakGrad ζ x)
      rw [← hsum] at htay
      have hin : ⟪gradient Ψ (G x - weakGrad v x), (-t) • weakGrad ζ x⟫
          = (-t) * ⟪gradient Ψ (G x - weakGrad v x), weakGrad ζ x⟫ := real_inner_smul_right _ _ _
      have hnm : ‖(-t) • weakGrad ζ x‖ ^ 2 = t ^ 2 * ‖weakGrad ζ x‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
      rw [hin, hnm] at htay
      linarith
    have hint := integral_mono_ae (integrable_shifted_profile h hut) hisum hpt
    rw [integral_add hi12 hi3, integral_add hi1 hi2, integral_const_mul,
      integral_const_mul] at hint
    have hmin' := hmin _ hzt
    simp only [regDirEnergy] at hmin' hint
    rw [← hIdef, ← hNdef] at hint
    linarith
  -- both signs of `t` bound `I`
  have hbound : ∀ J : ℝ, (∀ t : ℝ, 0 < t → J ≤ C / 2 * t * N) → J ≤ 0 := by
    intro J hJ
    refine le_of_forall_sub_le fun ε hε => ?_
    have hden : (0 : ℝ) < C / 2 * N + 1 := by positivity
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = ε / (C / 2 * N + 1) := ⟨_, rfl⟩
    have ht : 0 < t := by rw [htdef]; exact div_pos hε hden
    have htD : t * (C / 2 * N + 1) = ε := by rw [htdef]; exact div_mul_cancel₀ ε hden.ne'
    have h1 := hJ t ht
    linarith
  have hIle : I ≤ 0 := by
    refine hbound I fun t ht => ?_
    have hk := hkey t
    nlinarith [hk, ht]
  have hIge : (0 : ℝ) ≤ I := by
    have hneg : -I ≤ 0 := by
      refine hbound (-I) fun t ht => ?_
      have hk := hkey (-t)
      nlinarith [hk, ht]
    linarith
  exact le_antisymm hIle hIge


/-! ### Integrability helpers for the weak formulation -/

/-- A function integrable on a closed set and vanishing off it is integrable. -/
theorem integrable_of_integrableOn_of_zero_outside {F : Euc d → ℝ} {K : Set (Euc d)}
    (hK : IsClosed K) (hF : IntegrableOn F K volume) (h0 : ∀ x ∉ K, F x = 0) : Integrable F := by
  have hc : IntegrableOn F Kᶜ volume :=
    (integrableOn_zero (μ := volume) (s := Kᶜ)).congr_fun (fun x hx => (h0 x hx).symm)
      hK.isOpen_compl.measurableSet
  have hu : IntegrableOn F (K ∪ Kᶜ) volume := integrableOn_union.2 ⟨hF, hc⟩
  rwa [Set.union_compl_self, integrableOn_univ] at hu

/-- `x ↦ ⟪F x, e⟫ ψ x` is integrable when `F` is integrable on the support of the continuous,
compactly supported `ψ`. -/
theorem integrable_inner_mul_of_integrableOn {F : Euc d → Euc d} {ψ : Euc d → ℝ} (e : Euc d)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hF : IntegrableOn F (tsupport ψ) volume) :
    Integrable fun x => ⟪F x, e⟫ * ψ x := by
  have hFe : IntegrableOn (fun x => ⟪F x, e⟫) (tsupport ψ) volume :=
    (hF.const_inner e).congr (Eventually.of_forall fun x => (real_inner_comm e (F x)).symm)
  have hprod : IntegrableOn (fun x => ⟪F x, e⟫ * ψ x) (tsupport ψ) volume :=
    hFe.mul_continuousOn hψc.continuousOn hψs
  refine integrable_of_integrableOn_of_zero_outside (isClosed_tsupport ψ) hprod fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- The directional derivative of a test function is continuous with compact support, and vanishes
off the support of the test function. -/
theorem contDiff_fderiv_apply {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (e : Euc d) : Continuous (fun x => fderiv ℝ ψ x e) ∧
      HasCompactSupport (fun x => fderiv ℝ ψ x e) ∧
      ∀ x ∉ tsupport ψ, fderiv ℝ ψ x e = 0 := by
  have hfd : Continuous (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψ).2.continuous
  have hz : ∀ x ∉ tsupport ψ, fderiv ℝ ψ x e = 0 := by
    intro x hx
    have h0 : fderiv ℝ ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem => hx (tsupport_fderiv_subset ℝ hmem)
    rw [h0]
    rfl
  exact ⟨hfd.clm_apply continuous_const,
    Korevaar.hasCompactSupport_of_zero_outside hψs hz, hz⟩

/-! ### Subtracting a Sobolev function from a local weak gradient -/

/-- **The potential of the replacement.**  If `v` has the local weak gradient `G` on the open set
`U` and `z` is a global Sobolev function with weak gradient `Z`, then `v - z` has the local weak
gradient `G - Z` on `U`. -/
theorem HasWeakGradientOn.sub_hasWeakGradient {U : Set (Euc d)} (hU : IsOpen U)
    {v : Euc d → ℝ} {G : Euc d → Euc d} (hv : HasWeakGradientOn U v G)
    (hvc : ContinuousOn v U) (hGloc : LocallyIntegrableOn G U volume)
    {z : Euc d → ℝ} {Z : Euc d → Euc d} (hz : HasWeakGradient z Z) :
    HasWeakGradientOn U (fun x => v x - z x) (fun x => G x - Z x) := by
  refine ⟨fun ψ hψ hψs hψU e => ?_⟩
  obtain ⟨hgc, hgs, hgz⟩ := contDiff_fderiv_apply hψ hψs e
  have hψc : Continuous ψ := hψ.continuous
  -- the four integrability facts
  have hI1 : Integrable fun x => v x * fderiv ℝ ψ x e :=
    (Korevaar.continuous_mul_of_continuousOn hU hvc hgc (isClosed_tsupport ψ) hψU hgz).integrable_of_hasCompactSupport
      (Korevaar.hasCompactSupport_of_zero_outside hψs fun x hx => by rw [hgz x hx, mul_zero])
  have hI2 : Integrable fun x => z x * fderiv ℝ ψ x e := by
    refine (hz.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hgc hgs).congr
      (Eventually.of_forall fun x => ?_)
    show (fderiv ℝ ψ x e) • z x = z x * fderiv ℝ ψ x e
    rw [smul_eq_mul, mul_comm]
  have hI3 : Integrable fun x => ⟪G x, e⟫ * ψ x :=
    integrable_inner_mul_of_integrableOn e hψc hψs
      (hGloc.integrableOn_compact_subset hψU hψs)
  have hI4 : Integrable fun x => ⟪Z x, e⟫ * ψ x :=
    integrable_inner_mul_of_integrableOn e hψc hψs
      (hz.locallyIntegrable_grad.integrableOn_isCompact hψs)
  -- the identity
  have hsplit : (∫ x, (v x - z x) * fderiv ℝ ψ x e) =
      (∫ x, v x * fderiv ℝ ψ x e) - ∫ x, z x * fderiv ℝ ψ x e := by
    rw [← integral_sub hI1 hI2]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hsplit' : (∫ x, ⟪G x - Z x, e⟫ * ψ x) =
      (∫ x, ⟪G x, e⟫ * ψ x) - ∫ x, ⟪Z x, e⟫ * ψ x := by
    rw [← integral_sub hI3 hI4]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ⟪G x - Z x, e⟫ * ψ x = ⟪G x, e⟫ * ψ x - ⟪Z x, e⟫ * ψ x
    rw [inner_sub_left]
    ring
  rw [hsplit, hsplit', hv.integral_eq ψ hψ hψs hψU e, hz.integral_mul_fderiv ψ hψ hψs e]
  ring



/-! ### The product rule for a smooth cutoff -/

/-- A scalar function continuous on an open set, multiplied by a continuous *vector field*
vanishing outside a closed subset, is globally continuous.  (The vector-valued companion of
`Komlos.Literature.Korevaar.continuous_mul_of_continuousOn`.) -/
theorem repl_continuous_smul_of_continuousOn {Ω : Set (Euc d)} (hΩ : IsOpen Ω) {f : Euc d → ℝ}
    {g : Euc d → Euc d} (hf : ContinuousOn f Ω) (hg : Continuous g) {K : Set (Euc d)}
    (hK : IsClosed K) (hKΩ : K ⊆ Ω) (hgK : ∀ x ∉ K, g x = 0) :
    Continuous fun x => f x • g x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (hf.continuousAt (hΩ.mem_nhds hx)).smul hg.continuousAt
  · have hmem : Kᶜ ∈ 𝓝 x := hK.isOpen_compl.mem_nhds fun h => hx (hKΩ h)
    refine (continuousAt_const (y := (0 : Euc d))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    show f y • g y = 0
    rw [hgK y hy, smul_zero]

/-- `v` times a continuous function supported in a compact subset of `U` is integrable. -/
theorem integrable_mul_of_continuousOn {U : Set (Euc d)} (hU : IsOpen U) {v : Euc d → ℝ}
    (hvc : ContinuousOn v U) {g : Euc d → ℝ} (hgc : Continuous g) {K : Set (Euc d)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hg0 : ∀ y ∉ K, g y = 0) :
    Integrable fun y => v y * g y :=
  (Korevaar.continuous_mul_of_continuousOn hU hvc hgc hK.isClosed hKU
    hg0).integrable_of_hasCompactSupport
    (Korevaar.hasCompactSupport_of_zero_outside hK fun y hy => by rw [hg0 y hy, mul_zero])

/-- **The product rule for a smooth cutoff.**  If `v` has the local weak gradient `G` on the open
set `U` and `ζ` is smooth with compact support inside `U`, then `ζ v` is a *global* Sobolev
function, with weak gradient `ζ ∇v + v ∇ζ`.  This is what turns the (only locally Sobolev)
solution `v` into a `MemW0` function, so that the truncation chain rule
`Komlos.Literature.Regularized.memW0_posPart` applies to it. -/
theorem HasWeakGradientOn.cutoff_mul {U : Set (Euc d)} (hU : IsOpen U)
    {v : Euc d → ℝ} {G : Euc d → Euc d} (hv : HasWeakGradientOn U v G)
    (hvc : ContinuousOn v U) (hGloc : LocallyIntegrableOn G U volume)
    {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U) :
    HasWeakGradient (fun y => ζ y * v y) (fun y => ζ y • G y + v y • gradient ζ y) := by
  have hζc : Continuous ζ := hζ.continuous
  have hζ0 : ∀ y ∉ tsupport ζ, ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hgζc : Continuous (gradient ζ) := continuous_gradient (hζ.of_le (by simp))
  have hgζ0 : ∀ y ∉ tsupport ζ, gradient ζ y = 0 := fun y hy =>
    gradient_eq_zero_of_notMem_tsupport hy
  have hKcpt : IsCompact (tsupport ζ) := hζs
  -- continuity of the two continuous pieces
  have hprodc : Continuous fun y => ζ y * v y := by
    refine (Korevaar.continuous_mul_of_continuousOn hU hvc hζc (isClosed_tsupport ζ) hζU
      hζ0).congr fun y => ?_
    exact mul_comm (v y) (ζ y)
  have hvgζ : Continuous fun y => v y • gradient ζ y :=
    repl_continuous_smul_of_continuousOn hU hvc hgζc (isClosed_tsupport ζ) hζU hgζ0
  -- local integrability of `ζ • G`
  have hζG : LocallyIntegrable (fun y => ζ y • G y) volume := by
    intro y
    by_cases hy : y ∈ tsupport ζ
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU y (hζU hy)
      refine ⟨Metric.closedBall y (r / 2), Metric.closedBall_mem_nhds y (by linarith), ?_⟩
      have hsubU : Metric.closedBall y (r / 2) ⊆ U :=
        (Metric.closedBall_subset_ball (by linarith)).trans hball
      exact (hGloc.integrableOn_compact_subset hsubU
        (isCompact_closedBall y (r / 2))).continuousOn_smul hζc.continuousOn
          (isCompact_closedBall y (r / 2))
    · refine ⟨(tsupport ζ)ᶜ, (isClosed_tsupport ζ).isOpen_compl.mem_nhds hy, ?_⟩
      refine (integrableOn_zero (μ := volume) (s := (tsupport ζ)ᶜ)).congr_fun (fun w hw => ?_)
        (isClosed_tsupport ζ).isOpen_compl.measurableSet
      show (0 : Euc d) = ζ w • G w
      rw [hζ0 w hw, zero_smul]
  refine ⟨hprodc.locallyIntegrable, hζG.add hvgζ.locallyIntegrable, fun ψ hψ hψs e => ?_⟩
  -- the test function `ζ ψ`
  have hψc : Continuous ψ := hψ.continuous
  have hdψc : Continuous fun y => fderiv ℝ ψ y e := by
    have hfd : Continuous (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψ).2.continuous
    exact hfd.clm_apply continuous_const
  have hdζc : Continuous fun y => fderiv ℝ ζ y e := by
    have hfd : Continuous (fderiv ℝ ζ) := (contDiff_infty_iff_fderiv.1 hζ).2.continuous
    exact hfd.clm_apply continuous_const
  have hdζ0 : ∀ y ∉ tsupport ζ, fderiv ℝ ζ y e = 0 := by
    intro y hy
    have h0 : fderiv ℝ ζ y = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem => hy (tsupport_fderiv_subset ℝ hmem)
    rw [h0]; rfl
  set χ : Euc d → ℝ := fun y => ζ y * ψ y with hχdef
  have hχ : ContDiff ℝ ∞ χ := hζ.mul hψ
  have hχ0 : ∀ y ∉ tsupport ζ, χ y = 0 := by
    intro y hy
    show ζ y * ψ y = 0
    rw [hζ0 y hy, zero_mul]
  have hχs : HasCompactSupport χ := Korevaar.hasCompactSupport_of_zero_outside hKcpt hχ0
  have hχU : tsupport χ ⊆ U := by
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport ζ)) hζU
    intro y hy
    by_contra hcon
    exact hy (hχ0 y hcon)
  -- the product rule for `fderiv`
  have hfd : ∀ y, fderiv ℝ χ y e = ζ y * fderiv ℝ ψ y e + ψ y * fderiv ℝ ζ y e := by
    intro y
    have h1 : HasFDerivAt ζ (fderiv ℝ ζ y) y := (hζ.differentiable (by simp) y).hasFDerivAt
    have h2 : HasFDerivAt ψ (fderiv ℝ ψ y) y := (hψ.differentiable (by simp) y).hasFDerivAt
    have h3 : fderiv ℝ χ y = ζ y • fderiv ℝ ψ y + ψ y • fderiv ℝ ζ y := (h1.mul h2).fderiv
    rw [h3]
    simp
  -- integrability of the four pieces
  have hI1 : Integrable fun y => v y * (ζ y * fderiv ℝ ψ y e) :=
    integrable_mul_of_continuousOn hU hvc (hζc.mul hdψc) hKcpt hζU
      fun y hy => by rw [hζ0 y hy, zero_mul]
  have hI2 : Integrable fun y => v y * (ψ y * fderiv ℝ ζ y e) :=
    integrable_mul_of_continuousOn hU hvc (hψc.mul hdζc) hKcpt hζU
      fun y hy => by rw [hdζ0 y hy, mul_zero]
  have hI3 : Integrable fun y => ⟪G y, e⟫ * χ y :=
    integrable_inner_mul_of_integrableOn e hχ.continuous hχs
      (hGloc.integrableOn_compact_subset hχU hχs)
  have hI4 : Integrable fun y => v y * (⟪gradient ζ y, e⟫ * ψ y) :=
    integrable_mul_of_continuousOn hU hvc ((hgζc.inner continuous_const).mul hψc) hKcpt hζU
      fun y hy => by rw [hgζ0 y hy, inner_zero_left, zero_mul]
  -- the computation
  have hkey := hv.integral_eq χ hχ hχs hχU e
  have hsplit : (∫ y, v y * fderiv ℝ χ y e) =
      (∫ y, v y * (ζ y * fderiv ℝ ψ y e)) + ∫ y, v y * (ψ y * fderiv ℝ ζ y e) := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show v y * fderiv ℝ χ y e = v y * (ζ y * fderiv ℝ ψ y e) + v y * (ψ y * fderiv ℝ ζ y e)
    rw [hfd y]
    ring
  rw [hsplit] at hkey
  have hgoalL : (∫ y, (ζ y * v y) * fderiv ℝ ψ y e) = ∫ y, v y * (ζ y * fderiv ℝ ψ y e) :=
    integral_congr_ae (Eventually.of_forall fun y => by ring)
  have hgoalR : (∫ y, ⟪ζ y • G y + v y • gradient ζ y, e⟫ * ψ y) =
      (∫ y, ⟪G y, e⟫ * χ y) + ∫ y, v y * (⟪gradient ζ y, e⟫ * ψ y) := by
    rw [← integral_add hI3 hI4]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ⟪ζ y • G y + v y • gradient ζ y, e⟫ * ψ y =
      ⟪G y, e⟫ * χ y + v y * (⟪gradient ζ y, e⟫ * ψ y)
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hχdef]
    ring
  have hlast : (∫ y, v y * (ψ y * fderiv ℝ ζ y e)) =
      ∫ y, v y * (⟪gradient ζ y, e⟫ * ψ y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show v y * (ψ y * fderiv ℝ ζ y e) = v y * (⟪gradient ζ y, e⟫ * ψ y)
    rw [fderiv_apply_eq_inner_gradient ζ y e]
    ring
  rw [hgoalL, hgoalR, ← hlast]
  linarith [hkey]


/-! ### The maximum principle for the minimiser -/

/-- A smooth function that is constant on a neighbourhood has vanishing gradient there. -/
theorem gradient_eq_zero_of_eventuallyEq_const {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) {y : Euc d}
    {t : ℝ} (hloc : ∀ᶠ w in 𝓝 y, ζ w = t) : gradient ζ y = 0 := by
  have hfd : HasFDerivAt ζ (0 : Euc d →L[ℝ] ℝ) y :=
    (hasFDerivAt_const t y).congr_of_eventuallyEq hloc
  have hzero : ∀ w : Euc d, ⟪gradient ζ y, w⟫ = (0 : ℝ) := by
    intro w
    rw [← fderiv_apply_eq_inner_gradient ζ y w, hfd.fderiv]
    rfl
  exact inner_self_eq_zero.1 (hzero (gradient ζ y))

/-- **The maximum principle for the `Ψ`-Dirichlet minimiser** (one-sided).  If `v ≤ K` on the ball
`B̄(x,s)` and `z` minimises `regDirEnergy Ψ (1_{B̄} G)` over `W₀^{1,2}(B̄)`, then the replacement
`h = v - z` satisfies `h ≤ K` a.e. on `B̄`.

Proof (Giaquinta, *Multiple Integrals in the Calculus of Variations*, Ch. II; Gilbarg–Trudinger,
Theorem 8.1).  Let `ζ` be a cutoff equal to `1` on a neighbourhood of `B̄` and compactly supported
in `U`, and put `vt = ζ v` — a *global* Sobolev function by `HasWeakGradientOn.cutoff_mul` — and
`hh = vt - z`.  The competitor is `z + w` with

`w = (hh - K)_+ - (vt - K)_+`

(the two `(-K)_+` shifts of `posPartShift` cancel).  It lies in `W₀^{1,2}(B̄)` because `z = 0`
off `B̄` makes `hh = vt` there; its weak gradient is `1_{hh>K} ∇hh - 1_{vt>K} ∇vt`, which on `B̄`
— where `ζ = 1`, `∇ζ = 0` and `v ≤ K` — equals `1_{h>K} (G - ∇z)`.  Hence `1_{B̄} G - ∇(z+w)`
vanishes on `B̄ ∩ {h > K}` and equals `1_{B̄} G - ∇z` elsewhere, so the energy does not increase;
minimality forces the integrand difference to vanish a.e., and the quadratic lower bound
`Ψ 0 + (c/2)‖q‖² ≤ Ψ q` then forces `∇w = 0` a.e.  Poincaré on `W₀^{1,2}(B̄)` gives `w = 0`, i.e.
`(hh - K)_+ = (vt - K)_+ = 0` on `B̄`.

Note that the naive competitor "truncate `h` at the level `K`" is *not* admissible here: `h = v`
off `B̄` and `v` is unbounded near `∂U`, so `(h - K)_+` does not vanish off `B̄`.  Subtracting
`(vt - K)_+` is exactly what repairs this. -/
theorem regDirEnergy_min_le (hd : 0 < d) (hP : IsRegProfileWith Ψ c C)
    {U : Set (Euc d)} (hU : IsOpen U) {v : Euc d → ℝ} {G : Euc d → Euc d}
    (hv : HasWeakGradientOn U v G) (hvc : ContinuousOn v U)
    (hGloc : LocallyIntegrableOn G U volume) (hGm : AEStronglyMeasurable G volume)
    {x : Euc d} {s a b : ℝ} (hs : 0 < s) (hsa : s < a) (hab : a < b)
    (hbU : Metric.closedBall x b ⊆ U)
    (hGsq : IntegrableOn (fun y => ‖G y‖ ^ 2) (Metric.closedBall x b) volume)
    {z : Euc d → ℝ} (hz : MemW0 2 (Metric.closedBall x s) z)
    (hmin : ∀ w : Euc d → ℝ, MemW0 2 (Metric.closedBall x s) w →
      regDirEnergy Ψ ((Metric.closedBall x s).indicator G) z ≤
        regDirEnergy Ψ ((Metric.closedBall x s).indicator G) w)
    {K : ℝ} (hK : ∀ y ∈ Metric.closedBall x s, v y ≤ K) :
    ∀ᵐ y, y ∈ Metric.closedBall x s → v y - z y ≤ K := by
  classical
  have h2e : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  set B : Set (Euc d) := Metric.closedBall x s with hB
  set GB : Euc d → Euc d := B.indicator G with hGB
  have hBb : B ⊆ Metric.closedBall x b := Metric.closedBall_subset_closedBall (by linarith)
  have hGBm : MemLp GB (ENNReal.ofReal 2) := by
    rw [hGB, h2e]
    refine (memLp_indicator_iff_restrict measurableSet_closedBall).2 ?_
    exact (memLp_two_iff_integrable_sq_norm hGm.restrict).2 (hGsq.mono_set hBb)
  -- the cutoff
  obtain ⟨Cc, hCc, hcut⟩ := exists_cutoff_const d
  obtain ⟨ζ, hζ, hζcs, hζsupp, hζnn, hζle1, hζone, hζgrad⟩ := hcut x a b (by linarith) hab
  have hζU : tsupport ζ ⊆ U := hζsupp.trans hbU
  have hBa : B ⊆ Metric.closedBall x a := Metric.closedBall_subset_closedBall (by linarith)
  have hBζ : B ⊆ tsupport ζ := by
    refine subset_trans ?_ (subset_tsupport ζ)
    intro y hy
    have h1 : ζ y = 1 := hζone y (hBa hy)
    simp [Function.mem_support, h1]
  have hgζB : ∀ y ∈ Metric.ball x a, gradient ζ y = 0 := by
    intro y hy
    refine gradient_eq_zero_of_eventuallyEq_const hζ (t := 1) ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with w hw
    exact hζone w (Metric.ball_subset_closedBall hw)
  have hBball : B ⊆ Metric.ball x a := Metric.closedBall_subset_ball hsa
  have hζ0 : ∀ y ∉ tsupport ζ, ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hgζ0 : ∀ y ∉ tsupport ζ, gradient ζ y = 0 := fun y hy =>
    gradient_eq_zero_of_notMem_tsupport hy
  -- the localized solution `vt = ζ v`
  set vt : Euc d → ℝ := fun y => ζ y * v y with hvtdef
  have hvtg : HasWeakGradient vt (fun y => ζ y • G y + v y • gradient ζ y) :=
    hv.cutoff_mul hU hvc hGloc hζ hζcs hζU
  have hvtc : Continuous vt := by
    refine (Korevaar.continuous_mul_of_continuousOn hU hvc hζ.continuous (isClosed_tsupport ζ)
      hζU hζ0).congr fun y => ?_
    exact mul_comm (v y) (ζ y)
  have hvgζc : Continuous fun y => v y • gradient ζ y :=
    repl_continuous_smul_of_continuousOn hU hvc (continuous_gradient (hζ.of_le (by simp)))
      (isClosed_tsupport ζ) hζU hgζ0
  have hvtW : MemW0 2 (tsupport ζ) vt := by
    have hvt0 : ∀ y ∉ tsupport ζ, vt y = 0 := by
      intro y hy
      show ζ y * v y = 0
      rw [hζ0 y hy, zero_mul]
    refine ⟨hvtc.memLp_of_hasCompactSupport
        (Korevaar.hasCompactSupport_of_zero_outside hζcs hvt0),
      Eventually.of_forall hvt0, ⟨_, hvtg, ?_⟩⟩
    have hGbig : MemLp ((Metric.closedBall x b).indicator G) (ENNReal.ofReal 2) := by
      rw [h2e]
      refine (memLp_indicator_iff_restrict measurableSet_closedBall).2 ?_
      exact (memLp_two_iff_integrable_sq_norm hGm.restrict).2 hGsq
    have h1 : MemLp (fun y => ζ y • G y) (ENNReal.ofReal 2) := by
      refine hGbig.mono (hζ.continuous.aestronglyMeasurable.smul hGm)
        (Eventually.of_forall fun y => ?_)
      show ‖ζ y • G y‖ ≤ ‖(Metric.closedBall x b).indicator G y‖
      by_cases hy : y ∈ Metric.closedBall x b
      · rw [Set.indicator_of_mem hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζnn y)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hζle1 y)
      · have hyz : ζ y = 0 := hζ0 y fun hmem => hy (hζsupp hmem)
        rw [Set.indicator_of_notMem hy, hyz, zero_smul]
    have h2 : MemLp (fun y => v y • gradient ζ y) (ENNReal.ofReal 2) :=
      hvgζc.memLp_of_hasCompactSupport
        (Korevaar.hasCompactSupport_of_zero_outside hζcs fun y hy => by
          show v y • gradient ζ y = 0
          rw [hgζ0 y hy, smul_zero])
    exact h1.add h2
  have hzT : MemW0 2 (tsupport ζ) z := hz.mono hBζ
  set hh : Euc d → ℝ := fun y => vt y - z y with hhdef
  have hhW : MemW0 2 (tsupport ζ) hh := Komlos.Literature.FrozenDirichlet.memW0_sub hvtW hzT
  -- the competitor
  obtain ⟨hP1W, hP1g⟩ := memW0_posPart (p := 2) one_lt_two hhW K
  obtain ⟨hP2W, hP2g⟩ := memW0_posPart (p := 2) one_lt_two hvtW K
  set w : Euc d → ℝ := fun y => posPartShift K (hh y) - posPartShift K (vt y) with hwdef
  have hwT : MemW0 2 (tsupport ζ) w := Komlos.Literature.FrozenDirichlet.memW0_sub hP1W hP2W
  have hwg : HasWeakGradient w
      (fun y => (if K < hh y then (1 : ℝ) else 0) • weakGrad hh y -
        (if K < vt y then (1 : ℝ) else 0) • weakGrad vt y) := by
    refine ((hP1g.add (hP2g.smul (-1))).congr_left
      (Eventually.of_forall fun y => ?_)).congr_right (Eventually.of_forall fun y => ?_)
    · show posPartShift K (hh y) + (-1 : ℝ) * posPartShift K (vt y) = w y
      show _ = posPartShift K (hh y) - posPartShift K (vt y)
      ring
    · show (if K < hh y then (1 : ℝ) else 0) • weakGrad hh y +
        (-1 : ℝ) • ((if K < vt y then (1 : ℝ) else 0) • weakGrad vt y) = _
      module
  have hw0 : ∀ᵐ y, y ∉ B → w y = 0 := by
    filter_upwards [hz.ae_eq_zero] with y hy hyB
    have hzz : z y = 0 := hy hyB
    show posPartShift K (hh y) - posPartShift K (vt y) = 0
    have hval : hh y = vt y := by show vt y - z y = vt y; rw [hzz, sub_zero]
    rw [hval, sub_self]
  have hwB : MemW0 2 B w := ⟨hwT.memLp, hw0, hwT.exists_weakGradient⟩
  -- the case analysis for the gradient of the competitor
  have hwgae : weakGrad w =ᵐ[volume] fun y => (if K < hh y then (1 : ℝ) else 0) • weakGrad hh y -
      (if K < vt y then (1 : ℝ) else 0) • weakGrad vt y := hwg.weakGrad_ae_eq
  have hhgae : weakGrad hh =ᵐ[volume] weakGrad vt - weakGrad z :=
    Komlos.Literature.FrozenDirichlet.weakGrad_sub_ae ⟨_, hvtW.hasWeakGradient⟩
      ⟨_, hzT.hasWeakGradient⟩
  have hvtgae : weakGrad vt =ᵐ[volume] fun y => ζ y • G y + v y • gradient ζ y :=
    hvtg.weakGrad_ae_eq
  have hw0grad : ∀ᵐ y, y ∉ B → weakGrad w y = 0 :=
    hwB.weakGrad_eq_zero_of_isClosed Metric.isClosed_closedBall
  have hzwg : weakGrad (z + w) =ᵐ[volume] weakGrad z + weakGrad w :=
    (hz.hasWeakGradient.add hwB.hasWeakGradient).weakGrad_ae_eq
  have hcases : ∀ᵐ y, weakGrad w y = 0 ∨
      (GB y - weakGrad z y - weakGrad w y = 0 ∧ weakGrad w y = GB y - weakGrad z y) := by
    filter_upwards [hwgae, hhgae, hvtgae, hw0grad] with y hwy hhy hvty hw0y
    by_cases hyB : y ∈ B
    · have hζ1 : ζ y = 1 := hζone y (hBa hyB)
      have hgζ1 : gradient ζ y = 0 := hgζB y (hBball hyB)
      have hvty' : weakGrad vt y = ζ y • G y + v y • gradient ζ y := hvty
      have hvtG : weakGrad vt y = G y := by rw [hvty', hζ1, hgζ1]; simp
      have hvtv : vt y = v y := by show ζ y * v y = v y; rw [hζ1, one_mul]
      have hnotK : ¬ (K < vt y) := by rw [hvtv]; exact not_lt.2 (hK y hyB)
      have hhy' : weakGrad hh y = weakGrad vt y - weakGrad z y := hhy
      have hGBy : GB y = G y := by rw [hGB]; exact Set.indicator_of_mem hyB G
      have hwy' : weakGrad w y =
          (if K < hh y then (1 : ℝ) else 0) • (GB y - weakGrad z y) := by
        rw [hwy, if_neg hnotK, zero_smul, sub_zero, hhy', hvtG, hGBy]
      by_cases hind : K < hh y
      · right
        rw [hwy', if_pos hind, one_smul]
        exact ⟨by abel, rfl⟩
      · left
        rw [hwy', if_neg hind, zero_smul]
    · exact Or.inl (hw0y hyB)
  -- the energy does not increase
  have hzwW : MemW0 2 B (z + w) := hz.add hwB
  have hint1 : Integrable fun y => Ψ (GB y - weakGrad (z + w) y) - Ψ 0 :=
    integrable_shifted_profile hP (Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hGBm hzwW)
  have hint2 : Integrable fun y => Ψ (GB y - weakGrad z y) - Ψ 0 :=
    integrable_shifted_profile hP (Komlos.Literature.FrozenDirichlet.memLp_sub_weakGrad hGBm hz)
  have hvanish : ∀ᵐ y, weakGrad w y = 0 ∨ GB y - weakGrad (z + w) y = 0 := by
    filter_upwards [hcases, hzwg] with y hy hzwy
    have hzwy' : weakGrad (z + w) y = weakGrad z y + weakGrad w y := hzwy
    rcases hy with h1 | ⟨h2, _⟩
    · exact Or.inl h1
    · refine Or.inr ?_
      rw [hzwy']
      have hvec : GB y - (weakGrad z y + weakGrad w y)
          = GB y - weakGrad z y - weakGrad w y := by abel
      rw [hvec, h2]
  have hle : ∀ᵐ y, Ψ (GB y - weakGrad (z + w) y) - Ψ 0 ≤ Ψ (GB y - weakGrad z y) - Ψ 0 := by
    filter_upwards [hvanish, hzwg] with y hy hzwy
    have hzwy' : weakGrad (z + w) y = weakGrad z y + weakGrad w y := hzwy
    rcases hy with h1 | h2
    · rw [hzwy', h1, add_zero]
    · rw [h2]
      simpa using (hP.shifted_bounds (GB y - weakGrad z y)).1
  have hEeq : regDirEnergy Ψ GB (z + w) = regDirEnergy Ψ GB z :=
    le_antisymm (integral_mono_ae hint1 hint2 hle) (hmin _ hzwW)
  -- the integrand difference vanishes a.e.
  have hdiff0 : ∀ᵐ y, (Ψ (GB y - weakGrad z y) - Ψ 0) -
      (Ψ (GB y - weakGrad (z + w) y) - Ψ 0) = 0 := by
    have hnn : (0 : Euc d → ℝ) ≤ᵐ[volume] fun y => (Ψ (GB y - weakGrad z y) - Ψ 0) -
        (Ψ (GB y - weakGrad (z + w) y) - Ψ 0) := by
      filter_upwards [hle] with y hy
      show (0 : ℝ) ≤ _
      linarith
    have hzero : ∫ y, ((Ψ (GB y - weakGrad z y) - Ψ 0) -
        (Ψ (GB y - weakGrad (z + w) y) - Ψ 0)) = 0 := by
      rw [integral_sub hint2 hint1]
      simp only [regDirEnergy] at hEeq
      linarith
    have hres := (integral_eq_zero_iff_of_nonneg_ae hnn (hint2.sub hint1)).1 hzero
    filter_upwards [hres] with y hy
    exact hy
  -- hence the gradient of `w` vanishes
  have hgrad0 : weakGrad w =ᵐ[volume] 0 := by
    filter_upwards [hcases, hdiff0, hzwg] with y hy hdy hzwy
    have hzwy' : weakGrad (z + w) y = weakGrad z y + weakGrad w y := hzwy
    rcases hy with h1 | ⟨h2, h3⟩
    · exact h1
    · have hvec : GB y - weakGrad (z + w) y = 0 := by
        rw [hzwy']
        have : GB y - (weakGrad z y + weakGrad w y)
            = GB y - weakGrad z y - weakGrad w y := by abel
        rw [this, h2]
      rw [hvec] at hdy
      have hq := hP.quadratic_lower (GB y - weakGrad z y)
      have hnormsq : ‖GB y - weakGrad z y‖ ^ 2 ≤ 0 := by
        nlinarith [hP.c_pos, sq_nonneg ‖GB y - weakGrad z y‖]
      have hzero : GB y - weakGrad z y = 0 := by
        have hnn : ‖GB y - weakGrad z y‖ = 0 := by
          nlinarith [norm_nonneg (GB y - weakGrad z y)]
        exact norm_eq_zero.1 hnn
      rw [h3, hzero]
      rfl
  -- Poincaré: `w = 0`
  have hwnorm := hwB.eLpNorm_le_eLpNorm_weakGrad_closedBall (T := 2 * s + 1) hd one_lt_two hs.le
    (by linarith)
  have hgz : eLpNorm (weakGrad w) (ENNReal.ofReal 2) volume = 0 := by
    rw [eLpNorm_congr_ae hgrad0]
    simp
  have hw00 : w =ᵐ[volume] 0 := by
    have hz0 : eLpNorm w (ENNReal.ofReal 2) volume = 0 := by
      refine le_antisymm ?_ zero_le
      rw [hgz] at hwnorm
      simpa using hwnorm
    exact (eLpNorm_eq_zero_iff hwT.memLp.aestronglyMeasurable (by simp)).1 hz0
  -- conclude
  filter_upwards [hw00] with y hy hyB
  have hζ1 : ζ y = 1 := hζone y (hBa hyB)
  have hvtv : vt y = v y := by show ζ y * v y = v y; rw [hζ1, one_mul]
  have hhv : hh y = v y - z y := by show vt y - z y = v y - z y; rw [hvtv]
  have hwy : posPartShift K (hh y) - posPartShift K (vt y) = 0 := hy
  simp only [posPartShift, hhv, hvtv] at hwy
  have hvK : max (v y - K) 0 = 0 := max_eq_right (by linarith [hK y hyB])
  rw [hvK] at hwy
  have hmz : max (v y - z y - K) 0 = 0 := by linarith
  have := max_eq_right_iff.1 hmz
  linarith


/-! ### The two-sided maximum principle -/

/-- The negation of a local weak gradient. -/
theorem HasWeakGradientOn.neg {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}
    (hv : HasWeakGradientOn U v G) :
    HasWeakGradientOn U (fun y => -v y) (fun y => -G y) := by
  refine ⟨fun ψ hψ hψs hψU e => ?_⟩
  have hkey := hv.integral_eq ψ hψ hψs hψU e
  have h1 : (∫ y, -v y * fderiv ℝ ψ y e) = -∫ y, v y * fderiv ℝ ψ y e := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have h2 : (∫ y, ⟪-G y, e⟫ * ψ y) = -∫ y, ⟪G y, e⟫ * ψ y := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ⟪-G y, e⟫ * ψ y = -(⟪G y, e⟫ * ψ y)
    rw [inner_neg_left]
    ring
  rw [h1, h2, hkey]

/-- The weak gradient of `-z`. -/
theorem weakGrad_neg_ae {z : Euc d → ℝ} (hz : ∃ g, HasWeakGradient z g) :
    weakGrad (fun y => -z y) =ᵐ[volume] fun y => -weakGrad z y := by
  have h := (hasWeakGradient_weakGrad hz).smul (-1)
  have h1 : HasWeakGradient (fun y => -z y) ((-1 : ℝ) • weakGrad z) :=
    h.congr_left (Eventually.of_forall fun y => by
      show ((-1 : ℝ) • z) y = -z y
      show (-1 : ℝ) * z y = -z y
      ring)
  have h2 : HasWeakGradient (fun y => -z y) (fun y => -weakGrad z y) :=
    h1.congr_right (Eventually.of_forall fun y => by
      show ((-1 : ℝ) • weakGrad z) y = -weakGrad z y
      show (-1 : ℝ) • weakGrad z y = -weakGrad z y
      module)
  exact h2.weakGrad_ae_eq

/-- The `Ψ`-Dirichlet energy is invariant under simultaneous negation (`Ψ` is even). -/
theorem regDirEnergy_neg (hΨ : IsRegProfile Ψ) {G : Euc d → Euc d} {z : Euc d → ℝ}
    (hz : ∃ g, HasWeakGradient z g) :
    regDirEnergy Ψ (fun y => -G y) (fun y => -z y) = regDirEnergy Ψ G z := by
  refine integral_congr_ae ?_
  filter_upwards [weakGrad_neg_ae hz] with y hy
  show Ψ (-G y - weakGrad (fun y => -z y) y) - Ψ 0 = Ψ (G y - weakGrad z y) - Ψ 0
  rw [show weakGrad (fun y => -z y) y = -weakGrad z y from hy]
  congr 1
  rw [show -G y - -weakGrad z y = -(G y - weakGrad z y) from by abel, hΨ.even]

/-- **The two-sided maximum principle**: the `Ψ`-Dirichlet minimiser is bounded by the oscillation
of `v` on the ball.  The lower bound is the upper bound applied to `(-v, -G, -z)`, which is
legitimate because `Ψ` is even (`regDirEnergy_neg`). -/
theorem regDirEnergy_min_abs_le (hd : 0 < d) (hP : IsRegProfileWith Ψ c C)
    {U : Set (Euc d)} (hU : IsOpen U) {v : Euc d → ℝ} {G : Euc d → Euc d}
    (hv : HasWeakGradientOn U v G) (hvc : ContinuousOn v U)
    (hGloc : LocallyIntegrableOn G U volume) (hGm : AEStronglyMeasurable G volume)
    {x : Euc d} {s a b : ℝ} (hs : 0 < s) (hsa : s < a) (hab : a < b)
    (hbU : Metric.closedBall x b ⊆ U)
    (hGsq : IntegrableOn (fun y => ‖G y‖ ^ 2) (Metric.closedBall x b) volume)
    {z : Euc d → ℝ} (hz : MemW0 2 (Metric.closedBall x s) z)
    (hmin : ∀ w : Euc d → ℝ, MemW0 2 (Metric.closedBall x s) w →
      regDirEnergy Ψ ((Metric.closedBall x s).indicator G) z ≤
        regDirEnergy Ψ ((Metric.closedBall x s).indicator G) w)
    {k K : ℝ} (hk : ∀ y ∈ Metric.closedBall x s, k ≤ v y)
    (hK : ∀ y ∈ Metric.closedBall x s, v y ≤ K) :
    ∀ᵐ y, |z y| ≤ K - k := by
  have hkK : k ≤ K := le_trans (hk x (Metric.mem_closedBall_self hs.le))
    (hK x (Metric.mem_closedBall_self hs.le))
  have hup := regDirEnergy_min_le hd hP hU hv hvc hGloc hGm hs hsa hab hbU hGsq hz hmin hK
  -- the negated problem
  have hnegind : (Metric.closedBall x s).indicator (fun y => -G y)
      = fun y => -((Metric.closedBall x s).indicator G y) := by
    funext y
    by_cases hy : y ∈ Metric.closedBall x s
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, neg_zero]
  have hznegW : MemW0 2 (Metric.closedBall x s) (fun y => -z y) :=
    (hz.smul (-1)).congr (Eventually.of_forall fun y => by
      show ((-1 : ℝ) • z) y = -z y
      show (-1 : ℝ) * z y = -z y
      ring)
  have hminneg : ∀ w : Euc d → ℝ, MemW0 2 (Metric.closedBall x s) w →
      regDirEnergy Ψ ((Metric.closedBall x s).indicator (fun y => -G y)) (fun y => -z y) ≤
        regDirEnergy Ψ ((Metric.closedBall x s).indicator (fun y => -G y)) w := by
    intro w hw
    have hwneg : MemW0 2 (Metric.closedBall x s) (fun y => -w y) :=
      (hw.smul (-1)).congr (Eventually.of_forall fun y => by
        show ((-1 : ℝ) • w) y = -w y
        show (-1 : ℝ) * w y = -w y
        ring)
    have e1 : regDirEnergy Ψ ((Metric.closedBall x s).indicator (fun y => -G y))
        (fun y => -z y) = regDirEnergy Ψ ((Metric.closedBall x s).indicator G) z := by
      rw [hnegind]
      exact regDirEnergy_neg hP.toIsRegProfile ⟨_, hz.hasWeakGradient⟩
    have e2 : regDirEnergy Ψ ((Metric.closedBall x s).indicator (fun y => -G y)) w =
        regDirEnergy Ψ ((Metric.closedBall x s).indicator G) (fun y => -w y) := by
      rw [hnegind, ← regDirEnergy_neg (Ψ := Ψ)
        (G := (Metric.closedBall x s).indicator G) (z := fun y => -w y)
        hP.toIsRegProfile ⟨_, hwneg.hasWeakGradient⟩]
      refine integral_congr_ae ?_
      filter_upwards [weakGrad_neg_ae (z := fun y => -w y) ⟨_, hwneg.hasWeakGradient⟩,
        weakGrad_neg_ae (z := w) ⟨_, hw.hasWeakGradient⟩] with y hy1 hy2
      show Ψ (-((Metric.closedBall x s).indicator G y) - weakGrad w y) - Ψ 0 =
        Ψ (-((Metric.closedBall x s).indicator G y) -
          weakGrad (fun y => -(fun y => -w y) y) y) - Ψ 0
      congr 3
      have h3 : weakGrad (fun y => -(fun y => -w y) y) y = -weakGrad (fun y => -w y) y := hy1
      rw [h3, show weakGrad (fun y => -w y) y = -weakGrad w y from hy2, neg_neg]
    rw [e1, e2]
    exact hmin _ hwneg
  have hlow := regDirEnergy_min_le hd hP hU hv.neg hvc.neg hGloc.neg hGm.neg hs hsa hab hbU
    (by simpa using hGsq) hznegW hminneg (K := -k)
    (fun y hy => by simpa using neg_le_neg (hk y hy))
  filter_upwards [hup, hlow, hz.ae_eq_zero] with y hyu hyl hy0
  by_cases hyB : y ∈ Metric.closedBall x s
  · have h1 : v y - z y ≤ K := hyu hyB
    have h2 : -v y - -z y ≤ -k := hyl hyB
    have h3 : k ≤ v y := hk y hyB
    have h4 : v y ≤ K := hK y hyB
    rw [abs_le]
    constructor <;> linarith
  · rw [hy0 hyB, abs_zero]
    linarith

/-! ### The replacement as a `Ψ`-harmonic gradient field -/

section Replacement

variable {κ mc : ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-- A local weak gradient transported to an a.e.-equal field. -/
theorem HasWeakGradientOn.congr_grad_ae {U : Set (Euc d)} {v : Euc d → ℝ}
    {G G' : Euc d → Euc d} (h : HasWeakGradientOn U v G) (hGG : ∀ᵐ y, y ∈ U → G y = G' y) :
    HasWeakGradientOn U v G' := by
  refine ⟨fun ψ hψ hψs hψU e => ?_⟩
  rw [h.integral_eq ψ hψ hψs hψU e]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hGG] with y hy
  show ⟪G y, e⟫ * ψ y = ⟪G' y, e⟫ * ψ y
  by_cases hys : y ∈ tsupport ψ
  · rw [hy (hψU hys)]
  · rw [image_eq_zero_of_notMem_tsupport hys, mul_zero, mul_zero]

/-- The gradient field of a weak logarithmic solution is locally integrable on `U`. -/
theorem IsWeakLogSol.locallyIntegrableOn_grad (hsol : IsWeakLogSol κ mc Ψ U v G) :
    LocallyIntegrableOn G U volume := by
  intro y hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hsol.isOpen y hy
  refine ⟨Metric.closedBall y (r / 2),
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds y (by linarith)), ?_⟩
  have hsubU : Metric.closedBall y (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall y (r / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have h2 : MemLp G 2 (volume.restrict (Metric.closedBall y (r / 2))) :=
    (memLp_two_iff_integrable_sq_norm hsol.measurable_grad.aestronglyMeasurable).2
      (hsol.integrableOn_sq y (r / 2) hsubU)
  exact h2.integrable (by norm_num)

/-- **The `Ψ`-harmonic replacement of a weak logarithmic solution on a ball.**

Minimising the `Ψ`-Dirichlet energy relative to `1_{B̄} G` over `W₀^{1,2}(B̄)`
(`exists_regDirEnergy_min`) produces `z` whose Euler–Lagrange equation
(`euler_lagrange_regDirEnergy_min`) says exactly that the field `H = 1_{B̄} G - ∇z` is
`Ψ`-harmonic on the open ball, with potential `v - z` (`HasWeakGradientOn.sub_hasWeakGradient`).
On the ball, `G - H = ∇z`, so the comparison estimate of link 6 is an estimate for `∫ ‖∇z‖²`.

The measurable representatives `z`, `Z` are chosen so that the `Measurable` fields of
`IsRegHarmonicField` are available. -/
theorem IsWeakLogSol.exists_psi_harmonic_replacement (hd : 0 < d) (hP : IsRegProfileWith Ψ c C)
    (hsol : IsWeakLogSol κ mc Ψ U v G) {x : Euc d} {s : ℝ} (hs : 0 < s)
    (hsub : Metric.closedBall x s ⊆ U) :
    ∃ (z : Euc d → ℝ) (Z H : Euc d → Euc d),
      MemW0 2 (Metric.closedBall x s) z ∧ Measurable z ∧ Measurable Z ∧
      weakGrad z =ᵐ[volume] Z ∧ MemLp H (ENNReal.ofReal 2) ∧
      (∀ y, H y = (Metric.closedBall x s).indicator G y - Z y) ∧
      (∀ y ∈ Metric.closedBall x s, G y - H y = Z y) ∧
      (∫ y, ⟪gradient Ψ (H y), weakGrad z y⟫) = 0 ∧
      IsRegHarmonicField Ψ (Metric.ball x s) (fun y => v y - z y) H ∧
      (∀ w : Euc d → ℝ, MemW0 2 (Metric.closedBall x s) w →
        regDirEnergy Ψ ((Metric.closedBall x s).indicator G) z ≤
          regDirEnergy Ψ ((Metric.closedBall x s).indicator G) w) := by
  classical
  have h2e : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  set B : Set (Euc d) := Metric.closedBall x s with hB
  set GB : Euc d → Euc d := B.indicator G with hGB
  -- `1_B G` is globally square integrable
  have hGBm : MemLp GB (ENNReal.ofReal 2) := by
    rw [hGB, h2e]
    refine (memLp_indicator_iff_restrict measurableSet_closedBall).2 ?_
    exact (memLp_two_iff_integrable_sq_norm hsol.measurable_grad.aestronglyMeasurable).2
      (hsol.integrableOn_sq x s hsub)
  -- the minimiser, and a measurable representative of it
  obtain ⟨z₀, hz₀, hmin₀⟩ := exists_regDirEnergy_min hd hP (cB := x) (s := s) hs.le hGBm
  obtain ⟨z, hzsm, hzz⟩ : ∃ z : Euc d → ℝ, StronglyMeasurable z ∧ z₀ =ᵐ[volume] z :=
    ⟨hz₀.memLp.aestronglyMeasurable.mk z₀, hz₀.memLp.aestronglyMeasurable.stronglyMeasurable_mk,
      hz₀.memLp.aestronglyMeasurable.ae_eq_mk⟩
  have hz : MemW0 2 B z := hz₀.congr hzz
  have hzg : weakGrad z =ᵐ[volume] weakGrad z₀ :=
    (hz₀.hasWeakGradient.congr_left hzz).weakGrad_ae_eq
  have hmin : ∀ w : Euc d → ℝ, MemW0 2 B w → regDirEnergy Ψ GB z ≤ regDirEnergy Ψ GB w := by
    intro w hw
    have heq : regDirEnergy Ψ GB z = regDirEnergy Ψ GB z₀ := by
      refine integral_congr_ae ?_
      filter_upwards [hzg] with y hy
      rw [hy]
    rw [heq]
    exact hmin₀ w hw
  -- a measurable representative of the weak gradient
  obtain ⟨Z, hZsm, hZz⟩ : ∃ Z : Euc d → Euc d, StronglyMeasurable Z ∧ weakGrad z =ᵐ[volume] Z :=
    ⟨hz.memLp_weakGrad.aestronglyMeasurable.mk (weakGrad z),
      hz.memLp_weakGrad.aestronglyMeasurable.stronglyMeasurable_mk,
      hz.memLp_weakGrad.aestronglyMeasurable.ae_eq_mk⟩
  set H : Euc d → Euc d := fun y => GB y - Z y with hH
  have hZmem : MemLp Z (ENNReal.ofReal 2) := hz.memLp_weakGrad.ae_eq hZz
  have hHmem : MemLp H (ENNReal.ofReal 2) := hGBm.sub hZmem
  -- the Euler–Lagrange equation, transported to the measurable representative
  have hEL : ∀ ζ : Euc d → ℝ, MemW0 2 B ζ → (∫ y, ⟪gradient Ψ (H y), weakGrad ζ y⟫) = 0 := by
    intro ζ hζ
    have hkey := euler_lagrange_regDirEnergy_min hP hGBm hz hmin hζ
    rw [← hkey]
    refine integral_congr_ae ?_
    filter_upwards [hZz] with y hy
    show ⟪gradient Ψ (GB y - Z y), weakGrad ζ y⟫ = ⟪gradient Ψ (GB y - weakGrad z y), weakGrad ζ y⟫
    rw [hy]
  -- the potential
  have hvz : HasWeakGradientOn U (fun y => v y - z y) (fun y => G y - weakGrad z y) :=
    HasWeakGradientOn.sub_hasWeakGradient hsol.isOpen hsol.hasWeakGradientOn hsol.continuousOn
      hsol.locallyIntegrableOn_grad hz.hasWeakGradient
  have hballsub : Metric.ball x s ⊆ B := Metric.ball_subset_closedBall
  have hballU : Metric.ball x s ⊆ U := hballsub.trans hsub
  have hfield : HasWeakGradientOn (Metric.ball x s) (fun y => v y - z y) H := by
    refine (hvz.mono hballU).congr_grad_ae ?_
    filter_upwards [hZz] with y hy hyB
    show G y - weakGrad z y = GB y - Z y
    rw [hy, hGB, Set.indicator_of_mem (hballsub hyB)]
  refine ⟨z, Z, H, hz, hzsm.measurable, hZsm.measurable, hZz, hHmem, fun y => rfl, ?_,
    hEL z hz, ?_, hmin⟩
  · intro y hy
    show G y - (GB y - Z y) = Z y
    rw [hGB, Set.indicator_of_mem hy]
    abel
  · refine
      { isOpen := Metric.isOpen_ball
        measurable := hsol.measurable.sub hzsm.measurable
        measurable_grad := (hsol.measurable_grad.indicator measurableSet_closedBall).sub
          hZsm.measurable
        hasWeakGradientOn := hfield
        integrableOn_sq := fun y t _ => ?_
        weakEq := fun ψ hψ hψs hψU => ?_ }
    · exact (Komlos.Literature.FrozenDirichlet.integrable_norm_sq hHmem).integrableOn
    · have hψW : MemW0 2 B ψ :=
        Komlos.Literature.memW0_of_contDiff_supported hψ hψs (hψU.trans hballsub) 2
      have hkey := hEL ψ hψW
      rw [← hkey]
      refine integral_congr_ae ?_
      filter_upwards [weakGrad_ae_eq_gradient (hψ.of_le (by simp)) hψs] with y hy
      rw [hy]

end Replacement

end Komlos.Literature.Regularized
