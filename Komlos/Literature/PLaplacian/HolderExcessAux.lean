import Komlos.Literature.PLaplacian.RegularityHolderAux
import Komlos.Literature.PLaplacian.RegularityCampanato

/-!
# The `F`-`p`-harmonic replacement and the gradient excess (DiBenedetto/Tolksdorf inputs)

Auxiliary file for `Komlos.Literature.PLaplacian.RegularityHolder`: it builds the classical
foundations that the two DiBenedetto/Tolksdorf statements of that file rest on.

## Main results

* `MemW0.sub`, `HasWeakGradient.sub`, `weakGrad_sub_ae_eq` — the missing subtraction API for
  `W₀^{1,p}` and weak gradients.
* `integral_norm_sub_rpow_le_memLp` — the **integrated uniform convexity** of `Φ = F^p` for
  `L^p` vector fields (the `L^p` counterpart of `integral_norm_sub_rpow_le_of_continuous` of
  `Eigenfunction.lean`, which is stated for continuous compactly supported fields).
* `exists_pharmonic_replacement` — **the direct method for the Dirichlet problem**: for a
  bounded `B` and any `G ∈ L^p(ℝ^d; ℝ^d)` there is `w ∈ W₀^{1,p}(B)` minimizing
  `w ↦ ∫ F(G - ∇w)^p`, and it satisfies the Euler–Lagrange equation
  `∫ ⟪a(G - ∇w), ∇ψ⟫ = 0` for every `ψ ∈ W₀^{1,p}(B)` (`a = flux p F`). With `G = ∇u` this is
  exactly the `F`-`p`-harmonic replacement `v = u - w` of `u` on `B`.

  No weak compactness is used: exactly as in `exists_minimizer`, uniform convexity of `F^p`
  (`IsSmoothStrictNorm.exists_norm_sub_rpow_le`) makes the gradients of a minimizing sequence
  Cauchy in `L^p`, the Dirichlet–Poincaré inequality
  (`MemW0.eLpNorm_le_eLpNorm_weakGrad`) makes the sequence itself Cauchy in `L^p`, and
  `W0_complete` produces the limit inside `W₀^{1,p}(B)`.
* `fieldExcess` — the Campanato mean-oscillation excess `⨍_{B(x,r)} ‖H - (H)_{x,r}‖` of a vector
  field, with `fieldExcess_le_two_mul` and `exists_fieldExcess_bound` (the uniform-in-`x` top
  bound at a fixed scale, from `‖H‖ ≤ 1 + ‖H‖^p`).
* `excess_power_decay` — the **Giaquinta/Campanato iteration** in normalized form: a nonnegative
  `E` with `E ρ ≤ A (ρ/r)^β E r + Bc r^β` for `0 < ρ ≤ r ≤ R₀` and `E R₀ ≤ M₀` satisfies
  `E r ≤ C r^{β/2}` on `(0, R₀]`, with `C` depending only on `A, Bc, β, R₀, M₀` (hence uniformly
  over the centres of the balls in the application).

These are the ingredients of `IsWeakEigensolution.exists_energy_comparison` and
`IsWeakEigensolution.exists_gradient_campanato_average` in
`Komlos.Literature.PLaplacian.RegularityHolder`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Subtraction in `W₀^{1,p}` and for weak gradients -/

/-- Weak gradients subtract. -/
theorem HasWeakGradient.sub {f f' : Euc d → ℝ} {g g' : Euc d → Euc d}
    (hg : HasWeakGradient f g) (hg' : HasWeakGradient f' g') :
    HasWeakGradient (f - f') (g - g') := by
  have h := hg.add (hg'.smul (-1 : ℝ))
  have e1 : f + (-1 : ℝ) • f' = f - f' := by
    funext x
    show f x + (-1 : ℝ) • f' x = f x - f' x
    rw [neg_one_smul, ← sub_eq_add_neg]
  have e2 : g + (-1 : ℝ) • g' = g - g' := by
    funext x
    show g x + (-1 : ℝ) • g' x = g x - g' x
    rw [neg_one_smul, ← sub_eq_add_neg]
  rwa [e1, e2] at h

/-- `W₀^{1,p}(K)` is closed under subtraction. -/
theorem MemW0.sub {p : ℝ} {K : Set (Euc d)} {f f' : Euc d → ℝ} (hf : MemW0 p K f)
    (hf' : MemW0 p K f') : MemW0 p K (f - f') := by
  have h := hf.add (hf'.smul (-1 : ℝ))
  have e1 : f + (-1 : ℝ) • f' = f - f' := by
    funext x
    show f x + (-1 : ℝ) • f' x = f x - f' x
    rw [neg_one_smul, ← sub_eq_add_neg]
  rwa [e1] at h

/-- The chosen weak gradient of a difference is a.e. the difference of the chosen weak
gradients. -/
theorem weakGrad_sub_ae_eq {f f' : Euc d → ℝ} (hf : ∃ g, HasWeakGradient f g)
    (hf' : ∃ g, HasWeakGradient f' g) :
    weakGrad (f - f') =ᵐ[volume] weakGrad f - weakGrad f' :=
  ((hasWeakGradient_weakGrad hf).sub (hasWeakGradient_weakGrad hf')).weakGrad_ae_eq

/-- The chosen weak gradient of a sum is a.e. the sum of the chosen weak gradients. -/
theorem weakGrad_add_ae_eq {f f' : Euc d → ℝ} (hf : ∃ g, HasWeakGradient f g)
    (hf' : ∃ g, HasWeakGradient f' g) :
    weakGrad (f + f') =ᵐ[volume] weakGrad f + weakGrad f' :=
  ((hasWeakGradient_weakGrad hf).add (hasWeakGradient_weakGrad hf')).weakGrad_ae_eq

/-- The chosen weak gradient of a scalar multiple. -/
theorem weakGrad_smul_ae_eq {f : Euc d → ℝ} (hf : ∃ g, HasWeakGradient f g) (c : ℝ) :
    weakGrad (c • f) =ᵐ[volume] c • weakGrad f :=
  ((hasWeakGradient_weakGrad hf).smul c).weakGrad_ae_eq

/-- `∇(f + t g) = ∇f + t ∇g` a.e. -/
theorem weakGrad_add_smul_ae_eq {f g : Euc d → ℝ} (hf : ∃ G, HasWeakGradient f G)
    (hg : ∃ G, HasWeakGradient g G) (t : ℝ) :
    weakGrad (f + t • g) =ᵐ[volume] weakGrad f + t • weakGrad g :=
  ((hasWeakGradient_weakGrad hf).add ((hasWeakGradient_weakGrad hg).smul t)).weakGrad_ae_eq

/-- `∇((1/2)(f + g)) = (1/2)(∇f + ∇g)` a.e. -/
theorem weakGrad_half_add_ae_eq {f g : Euc d → ℝ} (hf : ∃ G, HasWeakGradient f G)
    (hg : ∃ G, HasWeakGradient g G) :
    weakGrad ((1 / 2 : ℝ) • (f + g)) =ᵐ[volume] (1 / 2 : ℝ) • (weakGrad f + weakGrad g) :=
  (((hasWeakGradient_weakGrad hf).add (hasWeakGradient_weakGrad hg)).smul
    (1 / 2 : ℝ)).weakGrad_ae_eq

/-! ### Integrated uniform convexity for `L^p` vector fields -/

/-- **Integrated uniform convexity of `Φ = F^p` for `L^p` vector fields** — the `L^p`
counterpart of `integral_norm_sub_rpow_le_of_continuous` (which is stated for continuous
compactly supported fields): from the pointwise bound
`‖ξ - η‖^p ≤ C · midDefect p F ξ η + ε (‖ξ‖+‖η‖)^p` (`exists_norm_sub_rpow_le`),
`∫ ‖A − B‖^p ≤ C (∫F(A)^p/2 + ∫F(B)^p/2 − ∫F((A+B)/2)^p) + ε 2^p (∫‖A‖^p + ∫‖B‖^p)`. -/
theorem integral_norm_sub_rpow_le_memLp {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {ε C : ℝ} (hε : 0 < ε)
    (hC : ∀ ξ η : Euc d, ‖ξ - η‖ ^ p ≤ C * midDefect p F ξ η + ε * (‖ξ‖ + ‖η‖) ^ p)
    {A B : Euc d → Euc d} (hA : MemLp A (ENNReal.ofReal p))
    (hB : MemLp B (ENNReal.ofReal p)) :
    ∫ x, ‖A x - B x‖ ^ p ≤
      C * ((∫ x, F (A x) ^ p) / 2 + (∫ x, F (B x) ^ p) / 2 -
        ∫ x, F ((1 / 2 : ℝ) • (A x + B x)) ^ p) +
      ε * (2 ^ p * ((∫ x, ‖A x‖ ^ p) + ∫ x, ‖B x‖ ^ p)) := by
  have hp0 : 0 < p := by linarith
  have hIfp : Integrable fun x => F (A x) ^ p := hF.integrable_rpow_comp hp0 hA
  have hIgp : Integrable fun x => F (B x) ^ p := hF.integrable_rpow_comp hp0 hB
  have hABmem : MemLp (fun x => (1 / 2 : ℝ) • (A x + B x)) (ENNReal.ofReal p) :=
    ((hA.add hB).const_smul (1 / 2 : ℝ)).ae_eq (Eventually.of_forall fun _ => rfl)
  have hImp : Integrable fun x => F ((1 / 2 : ℝ) • (A x + B x)) ^ p :=
    hF.integrable_rpow_comp hp0 hABmem
  have hInf : Integrable fun x => ‖A x‖ ^ p := integrable_norm_rpow_of_memLp hp0 hA
  have hIng : Integrable fun x => ‖B x‖ ^ p := integrable_norm_rpow_of_memLp hp0 hB
  have hIsum : Integrable fun x => (‖A x‖ + ‖B x‖) ^ p := by
    refine (integrable_norm_rpow_of_memLp hp0 (hA.norm.add hB.norm)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg (A x)) (norm_nonneg (B x)))]
  have hIdiff : Integrable fun x => ‖A x - B x‖ ^ p :=
    (integrable_norm_rpow_of_memLp hp0 (hA.sub hB)).congr (Eventually.of_forall fun _ => rfl)
  have hI12 : Integrable fun x => F (A x) ^ p / 2 + F (B x) ^ p / 2 :=
    (hIfp.div_const 2).add (hIgp.div_const 2)
  have hIdef : Integrable fun x => midDefect p F (A x) (B x) := hI12.sub hImp
  have step1 : ∫ x, ‖A x - B x‖ ^ p ≤
      ∫ x, (C * midDefect p F (A x) (B x) + ε * (‖A x‖ + ‖B x‖) ^ p) :=
    integral_mono hIdiff ((hIdef.const_mul C).add (hIsum.const_mul ε)) fun x => hC _ _
  have step2 : ∫ x, (C * midDefect p F (A x) (B x) + ε * (‖A x‖ + ‖B x‖) ^ p) =
      C * (∫ x, midDefect p F (A x) (B x)) + ε * ∫ x, (‖A x‖ + ‖B x‖) ^ p := by
    rw [integral_add (hIdef.const_mul C) (hIsum.const_mul ε), integral_const_mul,
      integral_const_mul]
  have step3 : ∫ x, midDefect p F (A x) (B x) =
      (∫ x, F (A x) ^ p) / 2 + (∫ x, F (B x) ^ p) / 2 -
        ∫ x, F ((1 / 2 : ℝ) • (A x + B x)) ^ p := by
    simp only [midDefect]
    rw [integral_sub hI12 hImp, integral_add (hIfp.div_const 2) (hIgp.div_const 2), integral_div,
      integral_div]
  have step4 : ∫ x, (‖A x‖ + ‖B x‖) ^ p ≤
      2 ^ p * ((∫ x, ‖A x‖ ^ p) + ∫ x, ‖B x‖ ^ p) := by
    rw [← integral_add hInf hIng, ← integral_const_mul]
    exact integral_mono hIsum ((hInf.add hIng).const_mul _) fun x =>
      add_rpow_le_two_rpow_mul hp0.le (norm_nonneg _) (norm_nonneg _)
  rw [step3] at step2
  have h6 := mul_le_mul_of_nonneg_left step4 hε.le
  linarith [step1, step2, h6]

/-! ### The Dirichlet energy relative to a fixed field -/

/-- The **Dirichlet energy of `w` relative to the field `G`**, `∫ F(G - ∇w)^p`. With
`G = ∇u` this is the `F`-`p`-energy `∫ F(∇v)^p` of the competitor `v = u - w`, and the
`F`-`p`-harmonic replacement of `u` on `B` is `u - w` for a minimizer `w` over
`W₀^{1,p}(B)`. -/
noncomputable def dirEnergy (p : ℝ) (F : Euc d → ℝ) (G : Euc d → Euc d) (w : Euc d → ℝ) : ℝ :=
  ∫ x, F (G x - weakGrad w x) ^ p

theorem dirEnergy_eq (p : ℝ) (F : Euc d → ℝ) (G : Euc d → Euc d) (w : Euc d → ℝ) :
    dirEnergy p F G w = ∫ x, F (G x - weakGrad w x) ^ p := rfl

theorem dirEnergy_nonneg {p : ℝ} {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    (G : Euc d → Euc d) (w : Euc d → ℝ) : 0 ≤ dirEnergy p F G w :=
  integral_nonneg fun _ => Real.rpow_nonneg (hF.nonneg _) p

/-- The competitor field `G - ∇w` of `w` lies in `L^p` when `G` does and `w ∈ W₀^{1,p}(B)`. -/
theorem memLp_sub_weakGrad {p : ℝ} {B : Set (Euc d)} {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) {w : Euc d → ℝ} (hw : MemW0 p B w) :
    MemLp (fun x => G x - weakGrad w x) (ENNReal.ofReal p) :=
  (hG.sub hw.memLp_weakGrad).ae_eq (Eventually.of_forall fun _ => rfl)

/-! ### The direct method for the Dirichlet problem -/

/-- The energy controls the `L^p` norm of the competitor field: `c^p ∫ ‖G - ∇w‖^p ≤ ∫ F(G - ∇w)^p`
whenever `c ‖·‖ ≤ F`. -/
theorem mul_integral_norm_sub_weakGrad_rpow_le {p : ℝ} (hp0 : 0 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {c : ℝ} (hc : 0 < c) (hcF : ∀ ξ, c * ‖ξ‖ ≤ F ξ)
    {B : Set (Euc d)} {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal p)) {w : Euc d → ℝ}
    (hw : MemW0 p B w) :
    c ^ p * ∫ x, ‖G x - weakGrad w x‖ ^ p ≤ dirEnergy p F G w := by
  have hmem : MemLp (fun x => G x - weakGrad w x) (ENNReal.ofReal p) :=
    memLp_sub_weakGrad hG hw
  rw [dirEnergy_eq, ← integral_const_mul]
  refine integral_mono ((integrable_norm_rpow_of_memLp hp0 hmem).const_mul _)
    (hF.integrable_rpow_comp hp0 hmem) fun x => ?_
  show c ^ p * ‖G x - weakGrad w x‖ ^ p ≤ F (G x - weakGrad w x) ^ p
  rw [← Real.mul_rpow hc.le (norm_nonneg _)]
  exact Real.rpow_le_rpow (mul_nonneg hc.le (norm_nonneg _)) (hcF _) hp0.le

/-- The infimum of the Dirichlet energy over `W₀^{1,p}(B)`: a nonnegative `m` that lies below every
energy and is approximated by energies. -/
theorem exists_dirEnergy_inf {p : ℝ} {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F)
    (B : Set (Euc d)) (G : Euc d → Euc d) :
    ∃ m : ℝ, 0 ≤ m ∧ (∀ z : Euc d → ℝ, MemW0 p B z → m ≤ dirEnergy p F G z) ∧
      ∀ δ : ℝ, 0 < δ → ∃ z : Euc d → ℝ, MemW0 p B z ∧ dirEnergy p F G z < m + δ := by
  have : Nonempty {z : Euc d → ℝ // MemW0 p B z} := ⟨⟨0, MemW0.zero⟩⟩
  have hbdd : BddBelow (Set.range fun z : {z : Euc d → ℝ // MemW0 p B z} =>
      dirEnergy p F G z.1) := by
    refine ⟨0, ?_⟩
    rintro y ⟨z, rfl⟩
    exact dirEnergy_nonneg hF G z.1
  refine ⟨⨅ z : {z : Euc d → ℝ // MemW0 p B z}, dirEnergy p F G z.1,
    le_ciInf fun z => dirEnergy_nonneg hF G z.1, fun z hz => ciInf_le hbdd ⟨z, hz⟩,
    fun δ hδ => ?_⟩
  obtain ⟨z, hz⟩ := exists_lt_of_ciInf_lt
    (f := fun z : {z : Euc d → ℝ // MemW0 p B z} => dirEnergy p F G z.1)
    (lt_add_of_pos_right _ hδ)
  exact ⟨z.1, z.2, hz⟩

/-- **The key estimate of the direct method for the Dirichlet energy**: if `m` lies below the
energy of every competitor in `W₀^{1,p}(B)` and `‖ξ - η‖^p ≤ C · midDefect + ε (‖ξ‖+‖η‖)^p`
pointwise, then comparing with the midpoint competitor `(w₂ + w₁)/2`,
`∫ ‖∇w₁ - ∇w₂‖^p ≤ C (J(w₁)/2 + J(w₂)/2 - m) + ε 2^p (∫ ‖G - ∇w₂‖^p + ∫ ‖G - ∇w₁‖^p)`. -/
theorem integral_norm_weakGrad_sub_rpow_le {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {B : Set (Euc d)} {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) {m ε C : ℝ} (hε : 0 < ε) (hC0 : 0 ≤ C)
    (hC : ∀ ξ η : Euc d, ‖ξ - η‖ ^ p ≤ C * midDefect p F ξ η + ε * (‖ξ‖ + ‖η‖) ^ p)
    (hmle : ∀ z : Euc d → ℝ, MemW0 p B z → m ≤ dirEnergy p F G z)
    {w₁ w₂ : Euc d → ℝ} (hw₁ : MemW0 p B w₁) (hw₂ : MemW0 p B w₂) :
    ∫ x, ‖weakGrad w₁ x - weakGrad w₂ x‖ ^ p ≤
      C * (dirEnergy p F G w₁ / 2 + dirEnergy p F G w₂ / 2 - m) +
        ε * (2 ^ p * ((∫ x, ‖G x - weakGrad w₂ x‖ ^ p) + ∫ x, ‖G x - weakGrad w₁ x‖ ^ p)) := by
  have hmain : ∫ x, ‖(G x - weakGrad w₂ x) - (G x - weakGrad w₁ x)‖ ^ p ≤
      C * ((∫ x, F (G x - weakGrad w₂ x) ^ p) / 2 + (∫ x, F (G x - weakGrad w₁ x) ^ p) / 2 -
        ∫ x, F ((1 / 2 : ℝ) • ((G x - weakGrad w₂ x) + (G x - weakGrad w₁ x))) ^ p) +
      ε * (2 ^ p * ((∫ x, ‖G x - weakGrad w₂ x‖ ^ p) + ∫ x, ‖G x - weakGrad w₁ x‖ ^ p)) :=
    integral_norm_sub_rpow_le_memLp hp hF hε hC (memLp_sub_weakGrad hG hw₂)
      (memLp_sub_weakGrad hG hw₁)
  have hdiff : ∫ x, ‖(G x - weakGrad w₂ x) - (G x - weakGrad w₁ x)‖ ^ p =
      ∫ x, ‖weakGrad w₁ x - weakGrad w₂ x‖ ^ p := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖(G x - weakGrad w₂ x) - (G x - weakGrad w₁ x)‖ ^ p =
      ‖weakGrad w₁ x - weakGrad w₂ x‖ ^ p
    rw [sub_sub_sub_cancel_left]
  -- the midpoint competitor
  have hzW : MemW0 p B ((1 / 2 : ℝ) • (w₂ + w₁)) := (hw₂.add hw₁).smul (1 / 2 : ℝ)
  have hzE : ∫ x, F ((1 / 2 : ℝ) • ((G x - weakGrad w₂ x) + (G x - weakGrad w₁ x))) ^ p =
      dirEnergy p F G ((1 / 2 : ℝ) • (w₂ + w₁)) := by
    rw [dirEnergy_eq]
    refine integral_congr_ae ?_
    filter_upwards [weakGrad_half_add_ae_eq (f := w₂) (g := w₁) ⟨_, hw₂.hasWeakGradient⟩
      ⟨_, hw₁.hasWeakGradient⟩] with x hx
    simp only [Pi.smul_apply, Pi.add_apply] at hx
    show F ((1 / 2 : ℝ) • ((G x - weakGrad w₂ x) + (G x - weakGrad w₁ x))) ^ p
        = F (G x - weakGrad ((1 / 2 : ℝ) • (w₂ + w₁)) x) ^ p
    rw [hx]
    have e : (1 / 2 : ℝ) • ((G x - weakGrad w₂ x) + (G x - weakGrad w₁ x)) =
        G x - (1 / 2 : ℝ) • (weakGrad w₂ x + weakGrad w₁ x) := by module
    rw [e]
  have hzm : m ≤ ∫ x, F ((1 / 2 : ℝ) • ((G x - weakGrad w₂ x) + (G x - weakGrad w₁ x))) ^ p := by
    rw [hzE]
    exact hmle _ hzW
  have hCterm : C * ((∫ x, F (G x - weakGrad w₂ x) ^ p) / 2 +
        (∫ x, F (G x - weakGrad w₁ x) ^ p) / 2 -
        ∫ x, F ((1 / 2 : ℝ) • ((G x - weakGrad w₂ x) + (G x - weakGrad w₁ x))) ^ p) ≤
      C * (dirEnergy p F G w₁ / 2 + dirEnergy p F G w₂ / 2 - m) := by
    refine mul_le_mul_of_nonneg_left ?_ hC0
    rw [dirEnergy_eq p F G w₁, dirEnergy_eq p F G w₂]
    linarith [hzm]
  linarith [hmain, hCterm, hdiff]

/-- **The gradients of a minimizing sequence of the Dirichlet energy are Cauchy in `L^p`**: if
`w n ∈ W₀^{1,p}(B)` has energies `J(w n) → m`, where `m` lies below every energy, and the
competitor fields `G - ∇w n` are bounded in `L^p`, then `∫ ‖∇w_k - ∇w_l‖^p → 0`. -/
theorem tendsto_integral_norm_weakGrad_sub {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {B : Set (Euc d)} {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) {w : ℕ → Euc d → ℝ} (hwW : ∀ n, MemW0 p B (w n)) {m : ℝ}
    (hmle : ∀ z : Euc d → ℝ, MemW0 p B z → m ≤ dirEnergy p F G z)
    (hJlim : Tendsto (fun n => dirEnergy p F G (w n)) atTop (𝓝 m))
    {Bd : ℝ} (hBd : ∀ n, ∫ x, ‖G x - weakGrad (w n) x‖ ^ p ≤ Bd) :
    Tendsto (fun kl : ℕ × ℕ => ∫ x, ‖weakGrad (w kl.1) x - weakGrad (w kl.2) x‖ ^ p)
      (atTop ×ˢ atTop) (𝓝 0) := by
  have hBd0 : 0 ≤ Bd :=
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p).trans (hBd 0)
  have hD : Tendsto (fun kl : ℕ × ℕ =>
      dirEnergy p F G (w kl.1) / 2 + dirEnergy p F G (w kl.2) / 2 - m)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h := (((hJlim.comp tendsto_fst).div_const 2).add
      ((hJlim.comp tendsto_snd).div_const 2)).sub (tendsto_const_nhds (x := m))
    have e : m / 2 + m / 2 - m = 0 := by ring
    rw [e] at h
    exact h
  rw [Metric.tendsto_nhds]
  intro η hη
  have hX0 : (0 : ℝ) ≤ 2 ^ p * (2 * Bd) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  have hK1 : (0 : ℝ) < 2 * (2 ^ p * (2 * Bd) + 1) := by linarith
  obtain ⟨ε, hε, hεX⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (2 ^ p * (2 * Bd)) < η / 2 :=
    ⟨η / (2 * (2 ^ p * (2 * Bd) + 1)), div_pos hη hK1, by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hK1]
      nlinarith⟩
  obtain ⟨C, hC0, hC⟩ := hF.exists_norm_sub_rpow_le hp hε
  have hev : ∀ᶠ kl : ℕ × ℕ in atTop ×ˢ atTop,
      C * (dirEnergy p F G (w kl.1) / 2 + dirEnergy p F G (w kl.2) / 2 - m) < η / 2 := by
    have h := hD.const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (half_pos hη))
  filter_upwards [hev] with kl hkl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  have h1 := integral_norm_weakGrad_sub_rpow_le hp hF hG hε hC0 hC hmle (hwW kl.1) (hwW kl.2)
  have h2 : ε * (2 ^ p * ((∫ x, ‖G x - weakGrad (w kl.2) x‖ ^ p) +
      ∫ x, ‖G x - weakGrad (w kl.1) x‖ ^ p)) ≤ ε * (2 ^ p * (2 * Bd)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hBd kl.1, hBd kl.2])
      (Real.rpow_nonneg (by norm_num) _)) hε.le
  linarith

/-- `∫ ‖g_k - g_l‖^p → 0` gives `‖g_k - g_l‖_{L^p} → 0` for `L^p` vector fields. -/
theorem tendsto_eLpNorm_sub_of_tendsto_integral {p : ℝ} (hp0 : 0 < p) {g : ℕ → Euc d → Euc d}
    (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p))
    (h : Tendsto (fun kl : ℕ × ℕ => ∫ x, ‖g kl.1 x - g kl.2 x‖ ^ p) (atTop ×ˢ atTop) (𝓝 0)) :
    Tendsto (fun kl : ℕ × ℕ => eLpNorm (g kl.1 - g kl.2) (ENNReal.ofReal p))
      (atTop ×ˢ atTop) (𝓝 0) := by
  have h0 := ((Real.continuous_rpow_const (inv_nonneg.2 hp0.le)).tendsto 0).comp h
  have h1 := (ENNReal.continuous_ofReal.tendsto _).comp h0
  simp only [Function.comp_def, Real.zero_rpow (inv_ne_zero hp0.ne'),
    ENNReal.ofReal_zero] at h1
  refine h1.congr fun kl => ?_
  rw [eLpNorm_eq_ofReal_integral hp0 ((hg kl.1).sub (hg kl.2))]
  simp only [Pi.sub_apply]

/-- **The graph-norm distance in `W₀^{1,p}(B)` is controlled by the gradient distance**
(Dirichlet–Poincaré, `MemW0.eLpNorm_le_eLpNorm_weakGrad`): for `B ⊆ closedBall 0 Rb`,
`‖f - g‖_{L^p} + ‖∇f - ∇g‖_{L^p} ≤ ((2 Rb + 1) + 1) ‖∇f - ∇g‖_{L^p}`. -/
theorem eLpNorm_sub_add_eLpNorm_weakGrad_sub_le {p : ℝ} (hp : 1 < p) (hd : 0 < d)
    {B : Set (Euc d)} {Rb : ℝ} (hRb : 0 ≤ Rb) (hB : B ⊆ Metric.closedBall 0 Rb)
    {f g : Euc d → ℝ} (hf : MemW0 p B f) (hg : MemW0 p B g) :
    eLpNorm (f - g) (ENNReal.ofReal p) + eLpNorm (weakGrad f - weakGrad g) (ENNReal.ofReal p) ≤
      (ENNReal.ofReal (2 * Rb + 1) + 1) *
        eLpNorm (weakGrad f - weakGrad g) (ENNReal.ofReal p) := by
  have hgrad : eLpNorm (weakGrad (f - g)) (ENNReal.ofReal p) =
      eLpNorm (weakGrad f - weakGrad g) (ENNReal.ofReal p) :=
    eLpNorm_congr_ae (weakGrad_sub_ae_eq ⟨_, hf.hasWeakGradient⟩ ⟨_, hg.hasWeakGradient⟩)
  have hpo : eLpNorm (f - g) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (2 * Rb + 1) * eLpNorm (weakGrad (f - g)) (ENNReal.ofReal p) :=
    (hf.sub hg).eLpNorm_le_eLpNorm_weakGrad hd hp hRb hB (show 2 * Rb < 2 * Rb + 1 by linarith)
  rw [hgrad] at hpo
  rw [add_mul, one_mul]
  exact add_le_add hpo le_rfl

/-- **A minimizing sequence of the Dirichlet energy is Cauchy in the graph norm**
`‖·‖_{L^p} + ‖∇·‖_{L^p}` of `W₀^{1,p}(B)` (the hypothesis of `W0_complete`), when `B` is bounded
and the competitor fields `G - ∇w n` are bounded in `L^p`. -/
theorem cauchy_graphNorm_of_dirEnergy_minimizing {p : ℝ} (hp : 1 < p) (hd : 0 < d)
    {F : Euc d → ℝ} (hF : IsSmoothStrictNorm F) {B : Set (Euc d)} {Rb : ℝ} (hRb : 0 ≤ Rb)
    (hB : B ⊆ Metric.closedBall 0 Rb) {G : Euc d → Euc d} (hG : MemLp G (ENNReal.ofReal p))
    {w : ℕ → Euc d → ℝ} (hwW : ∀ n, MemW0 p B (w n)) {m : ℝ}
    (hmle : ∀ z : Euc d → ℝ, MemW0 p B z → m ≤ dirEnergy p F G z)
    (hJlim : Tendsto (fun n => dirEnergy p F G (w n)) atTop (𝓝 m))
    {Bd : ℝ} (hBd : ∀ n, ∫ x, ‖G x - weakGrad (w n) x‖ ^ p ≤ Bd) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
      eLpNorm (w k - w l) (ENNReal.ofReal p) +
        eLpNorm (weakGrad (w k) - weakGrad (w l)) (ENNReal.ofReal p) < ε := by
  have hp0 : 0 < p := by linarith
  have hTg : Tendsto (fun kl : ℕ × ℕ =>
      eLpNorm (weakGrad (w kl.1) - weakGrad (w kl.2)) (ENNReal.ofReal p))
      (atTop ×ˢ atTop) (𝓝 0) :=
    tendsto_eLpNorm_sub_of_tendsto_integral hp0 (g := fun n => weakGrad (w n))
      (fun n => (hwW n).memLp_weakGrad)
      (tendsto_integral_norm_weakGrad_sub hp hF hG hwW hmle hJlim hBd)
  have hconst : Tendsto (fun kl : ℕ × ℕ => (ENNReal.ofReal (2 * Rb + 1) + 1) *
      eLpNorm (weakGrad (w kl.1) - weakGrad (w kl.2)) (ENNReal.ofReal p))
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * Rb + 1) + 1) hTg
      (Or.inr (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩))
    rw [mul_zero] at h
    exact h
  intro ε hε
  have hev := hconst.eventually (gt_mem_nhds hε)
  rw [prod_atTop_atTop_eq] at hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop_prod_self.1 hev
  exact ⟨N, fun k l hk hl => lt_of_le_of_lt
    (eLpNorm_sub_add_eLpNorm_weakGrad_sub_le hp hd hRb hB (hwW k) (hwW l)) (hN k l hk hl)⟩

/-- **Continuity of the Dirichlet energy** along `L^p` convergence of the weak gradients in
`W₀^{1,p}(B)` (continuity of the Nemytskii functional, `tendsto_integral_comp_of_tendsto_eLpNorm`).
-/
theorem tendsto_dirEnergy_of_tendsto {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {B : Set (Euc d)} {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) {w : ℕ → Euc d → ℝ} (hwW : ∀ n, MemW0 p B (w n))
    {wl : Euc d → ℝ} (hwlW : MemW0 p B wl)
    (hT : Tendsto (fun n => eLpNorm (weakGrad (w n) - weakGrad wl) (ENNReal.ofReal p)) atTop
      (𝓝 0)) :
    Tendsto (fun n => dirEnergy p F G (w n)) atTop (𝓝 (dirEnergy p F G wl)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Mf, hMf⟩ := hF.exists_le_mul_norm
  have hξT : Tendsto (fun n => eLpNorm ((fun x => G x - weakGrad (w n) x) -
      fun x => G x - weakGrad wl x) (ENNReal.ofReal p)) atTop (𝓝 0) := by
    refine hT.congr fun n => ?_
    have e : ((fun x => G x - weakGrad (w n) x) - fun x => G x - weakGrad wl x) =
        -(weakGrad (w n) - weakGrad wl) := by
      funext x
      show G x - weakGrad (w n) x - (G x - weakGrad wl x) = -(weakGrad (w n) x - weakGrad wl x)
      abel
    rw [e, eLpNorm_neg]
  have h : Tendsto (fun n => ∫ x, F (G x - weakGrad (w n) x) ^ p) atTop
      (𝓝 (∫ x, F (G x - weakGrad wl x) ^ p)) :=
    tendsto_integral_comp_of_tendsto_eLpNorm hp.le (hF.continuous_rpow hp0.le)
      (norm_rpow_le_of_le_mul_norm hF.nonneg hMf hp0)
      (fun n => memLp_sub_weakGrad hG (hwW n)) (memLp_sub_weakGrad hG hwlW) hξT
  simp only [dirEnergy_eq]
  exact h

/-- **The Dirichlet energy attains its infimum on `W₀^{1,p}(B)`** (the direct method, in the
uniform-convexity form of `exists_minimizer`; no weak compactness is used): for `1 < p`, a
smooth strictly convex norm `F`, a bounded `B ⊆ closedBall 0 Rb` and a field `G ∈ L^p`, there is
`w ∈ W₀^{1,p}(B)` with `∫ F(G - ∇w)^p ≤ ∫ F(G - ∇z)^p` for every `z ∈ W₀^{1,p}(B)`.

Proof: a minimizing sequence `w n` has `∫ ‖G - ∇w n‖^p` uniformly bounded (`c ‖·‖ ≤ F`); since
`(w k + w l)/2 ∈ W₀^{1,p}(B)` is a competitor, the integrated uniform convexity
(`integral_norm_sub_rpow_le_memLp`) makes `∇w n` Cauchy in `L^p`; the Dirichlet–Poincaré
inequality (`MemW0.eLpNorm_le_eLpNorm_weakGrad`) makes `w n` Cauchy in `L^p`; `W0_complete`
gives the limit `w ∈ W₀^{1,p}(B)`, and the energy passes to the limit by continuity of the
Nemytskii functional (`tendsto_integral_comp_of_tendsto_eLpNorm`). -/
theorem exists_dirEnergy_min {p : ℝ} (hp : 1 < p) (hd : 0 < d) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {B : Set (Euc d)} {Rb : ℝ} (hRb : 0 ≤ Rb)
    (hB : B ⊆ Metric.closedBall 0 Rb) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) :
    ∃ w : Euc d → ℝ, MemW0 p B w ∧
      ∀ z : Euc d → ℝ, MemW0 p B z → dirEnergy p F G w ≤ dirEnergy p F G z := by
  have hp0 : 0 < p := by linarith
  obtain ⟨c, hc, hcF⟩ := hF.exists_pos_mul_norm_le'
  have hcp : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
  -- the infimum and a minimizing sequence
  obtain ⟨m, -, hmle, hmlt⟩ := exists_dirEnergy_inf (p := p) hF B G
  choose w hwW hwJ using fun n : ℕ => hmlt (1 / ((n : ℝ) + 1)) (by positivity)
  have hJlim : Tendsto (fun n => dirEnergy p F G (w n)) atTop (𝓝 m) := by
    have h := (tendsto_const_nhds (x := m)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [add_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun n => hmle _ (hwW n)) (fun n => (hwJ n).le)
  -- a uniform `L^p` bound on the competitor fields
  have hξbd : ∀ n, ∫ x, ‖G x - weakGrad (w n) x‖ ^ p ≤ (m + 1) / c ^ p := by
    intro n
    have h1 := mul_integral_norm_sub_weakGrad_rpow_le hp0 hF hc hcF hG (hwW n)
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h3 := hwJ n
    rw [le_div_iff₀ hcp]
    linarith
  -- the limit in `W₀^{1,p}(B)` (Cauchy in the graph norm, `W0_complete`)
  obtain ⟨wl, hwlW, hwlT⟩ := W0_complete hp w hwW
    (cauchy_graphNorm_of_dirEnergy_minimizing hp hd hF hRb hB hG hwW hmle hJlim hξbd)
  have hgradT : Tendsto (fun n => eLpNorm (weakGrad (w n) - weakGrad wl) (ENNReal.ofReal p))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hwlT
      (fun _ => zero_le) fun _ => le_add_self
  -- the energy passes to the limit
  have hEwl : dirEnergy p F G wl = m :=
    tendsto_nhds_unique (tendsto_dirEnergy_of_tendsto hp hF hG hwW hwlW hgradT) hJlim
  refine ⟨wl, hwlW, fun z hz => ?_⟩
  rw [hEwl]
  exact hmle z hz

/-- **The Euler–Lagrange equation of the Dirichlet minimizer**: a minimizer `w` of
`z ↦ ∫ F(G - ∇z)^p` over `W₀^{1,p}(B)` satisfies `∫ ⟪a(G - ∇w), ∇ψ⟫ = 0` for every
`ψ ∈ W₀^{1,p}(B)`, with `a = flux p F`.

Proof: `t ↦ ∫ F((G - ∇w) + t ∇ψ)^p = ∫ F(G - ∇(w - tψ))^p` is minimal at `t = 0` because
`w - tψ ∈ W₀^{1,p}(B)`; its derivative there is `p ∫ ⟪a(G - ∇w), ∇ψ⟫`
(`hasDerivAt_integral_rpow_add_smul`, i.e. `D(F^p)(ξ) = p ⟪a(ξ), ·⟫`). -/
theorem euler_lagrange_dirEnergy_min {p : ℝ} (hp : 1 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {B : Set (Euc d)} {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) {w : Euc d → ℝ} (hw : MemW0 p B w)
    (hmin : ∀ z : Euc d → ℝ, MemW0 p B z → dirEnergy p F G w ≤ dirEnergy p F G z)
    {ψ : Euc d → ℝ} (hψ : MemW0 p B ψ) :
    ∫ x, ⟪flux p F (G x - weakGrad w x), weakGrad ψ x⟫ = 0 := by
  have hp0 : 0 < p := by linarith
  have hcongr : ∀ t : ℝ, ∫ x, F (G x - weakGrad w x + t • weakGrad ψ x) ^ p
      = dirEnergy p F G (w + (-t) • ψ) := by
    intro t
    rw [dirEnergy_eq]
    refine integral_congr_ae ?_
    filter_upwards [weakGrad_add_smul_ae_eq (f := w) (g := ψ) ⟨_, hw.hasWeakGradient⟩
      ⟨_, hψ.hasWeakGradient⟩ (-t)] with x hx
    simp only [Pi.add_apply, Pi.smul_apply] at hx
    show F (G x - weakGrad w x + t • weakGrad ψ x) ^ p
        = F (G x - weakGrad (w + (-t) • ψ) x) ^ p
    rw [hx]
    have e : G x - weakGrad w x + t • weakGrad ψ x
        = G x - (weakGrad w x + (-t) • weakGrad ψ x) := by module
    rw [e]
  have hloc : IsLocalMin (fun t : ℝ =>
      ∫ x, F (G x - weakGrad w x + t • weakGrad ψ x) ^ p) 0 := by
    refine Eventually.of_forall fun t => ?_
    have h0 : ∫ x, F (G x - weakGrad w x + (0 : ℝ) • weakGrad ψ x) ^ p = dirEnergy p F G w := by
      rw [dirEnergy_eq]
      simp only [zero_smul, add_zero]
    have ht : dirEnergy p F G w ≤ ∫ x, F (G x - weakGrad w x + t • weakGrad ψ x) ^ p := by
      rw [hcongr t]
      exact hmin _ (hw.add (hψ.smul (-t)))
    show ∫ x, F (G x - weakGrad w x + (0 : ℝ) • weakGrad ψ x) ^ p ≤
      ∫ x, F (G x - weakGrad w x + t • weakGrad ψ x) ^ p
    rw [h0]
    exact ht
  have hderiv := hasDerivAt_integral_rpow_add_smul (μ := volume) hp hF
    (memLp_sub_weakGrad hG hw) hψ.memLp_weakGrad
  have h0 := hloc.hasDerivAt_eq_zero hderiv
  have h1 : p * ∫ x, ⟪flux p F (G x - weakGrad w x), weakGrad ψ x⟫ = 0 := by
    rw [← integral_const_mul]
    exact h0
  exact (mul_eq_zero.1 h1).resolve_left hp0.ne'

/-- **The `F`-`p`-harmonic replacement with prescribed `W₀^{1,p}` boundary data**
(DiBenedetto 1983; Tolksdorf 1984): for a bounded `B ⊆ closedBall 0 Rb` and `G ∈ L^p` there is
`w ∈ W₀^{1,p}(B)` minimizing `z ↦ ∫ F(G - ∇z)^p` and solving the `F`-`p`-Laplace equation
`∫ ⟪a(G - ∇w), ∇ψ⟫ = 0` for all `ψ ∈ W₀^{1,p}(B)`. With `G = ∇u` the field `G - ∇w` is the
gradient of the `F`-`p`-harmonic replacement `v = u - w` of `u` on `B`. -/
theorem exists_pharmonic_replacement {p : ℝ} (hp : 1 < p) (hd : 0 < d) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {B : Set (Euc d)} {Rb : ℝ} (hRb : 0 ≤ Rb)
    (hB : B ⊆ Metric.closedBall 0 Rb) {G : Euc d → Euc d}
    (hG : MemLp G (ENNReal.ofReal p)) :
    ∃ w : Euc d → ℝ, MemW0 p B w ∧
      ∀ ψ : Euc d → ℝ, MemW0 p B ψ →
        ∫ x, ⟪flux p F (G x - weakGrad w x), weakGrad ψ x⟫ = 0 := by
  obtain ⟨w, hwW, hwmin⟩ := exists_dirEnergy_min hp hd hF hRb hB hG
  exact ⟨w, hwW, fun ψ hψ => euler_lagrange_dirEnergy_min hp hF hG hwW hwmin hψ⟩

/-! ### The mean-oscillation excess of a vector field -/

/-- The **Campanato (mean-oscillation) excess** of a field `H` on `B(x, r)`,
`⨍_{B(x,r)} ‖H - (H)_{x,r}‖`. The gradient excess `gradExcess u` of `RegularityHolder` is
`fieldExcess (weakGrad u)`. -/
noncomputable def fieldExcess (H : Euc d → Euc d) (x : Euc d) (r : ℝ) : ℝ :=
  ⨍ y in Metric.closedBall x r, ‖H y - ⨍ z in Metric.closedBall x r, H z‖

theorem fieldExcess_eq (H : Euc d → Euc d) (x : Euc d) (r : ℝ) :
    fieldExcess H x r =
      ⨍ y in Metric.closedBall x r, ‖H y - ⨍ z in Metric.closedBall x r, H z‖ := rfl

/-- The excess is `|B(x,r)|⁻¹ ∫_{B(x,r)} ‖H - (H)_{x,r}‖`. -/
theorem fieldExcess_eq_inv_mul (H : Euc d → Euc d) (x : Euc d) (r : ℝ) :
    fieldExcess H x r = (volume.real (Metric.closedBall x r))⁻¹ *
      ∫ y in Metric.closedBall x r, ‖H y - ⨍ z in Metric.closedBall x r, H z‖ := by
  rw [fieldExcess_eq, setAverage_eq (volume : Measure (Euc d))
    (fun y => ‖H y - ⨍ z in Metric.closedBall x r, H z‖) (Metric.closedBall x r), smul_eq_mul]

theorem fieldExcess_nonneg (H : Euc d → Euc d) (x : Euc d) (r : ℝ) : 0 ≤ fieldExcess H x r := by
  rw [fieldExcess_eq_inv_mul]
  exact mul_nonneg (inv_nonneg.2 measureReal_nonneg)
    (integral_nonneg fun _ => norm_nonneg _)

/-- The excess is at most twice the average of `‖H‖`. -/
theorem fieldExcess_le_two_mul {H : Euc d → Euc d} (hH : LocallyIntegrable H) (x : Euc d)
    {r : ℝ} (hr : 0 < r) :
    fieldExcess H x r ≤ 2 * ((volume.real (Metric.closedBall x r))⁻¹ *
      ∫ y in Metric.closedBall x r, ‖H y‖) := by
  have hvol : 0 < volume.real (Metric.closedBall x r) := by
    rw [volume_real_closedBall x hr.le]
    exact mul_pos (pow_pos hr d) volume_real_closedBall_pos
  have hHon : IntegrableOn H (Metric.closedBall x r) :=
    hH.integrableOn_isCompact (isCompact_closedBall x r)
  have hmean : ‖⨍ z in Metric.closedBall x r, H z‖ ≤
      (volume.real (Metric.closedBall x r))⁻¹ * ∫ y in Metric.closedBall x r, ‖H y‖ := by
    have h := norm_setAverage_sub_le (s := Metric.closedBall x r) (t := Metric.closedBall x r)
      (Metric.measure_closedBall_pos volume x hr).ne' measure_closedBall_lt_top.ne
      subset_rfl measure_closedBall_lt_top.ne hHon 0
    simpa only [sub_zero] using h
  have hcv : IntegrableOn (fun _ : Euc d => ⨍ z in Metric.closedBall x r, H z)
      (Metric.closedBall x r) := integrableOn_const measure_closedBall_lt_top.ne
  have hcs : IntegrableOn (fun _ : Euc d => ‖⨍ z in Metric.closedBall x r, H z‖)
      (Metric.closedBall x r) := integrableOn_const measure_closedBall_lt_top.ne
  have hint1 : IntegrableOn (fun y => ‖H y - ⨍ z in Metric.closedBall x r, H z‖)
      (Metric.closedBall x r) := (hHon.sub hcv).norm
  have hint2 : IntegrableOn
      (fun y => ‖H y‖ + ‖⨍ z in Metric.closedBall x r, H z‖) (Metric.closedBall x r) :=
    hHon.norm.add hcs
  have hle : ∫ y in Metric.closedBall x r, ‖H y - ⨍ z in Metric.closedBall x r, H z‖ ≤
      (∫ y in Metric.closedBall x r, ‖H y‖) +
        volume.real (Metric.closedBall x r) * ‖⨍ z in Metric.closedBall x r, H z‖ := by
    have h1 : ∫ y in Metric.closedBall x r, ‖H y - ⨍ z in Metric.closedBall x r, H z‖ ≤
        ∫ y in Metric.closedBall x r, (‖H y‖ + ‖⨍ z in Metric.closedBall x r, H z‖) :=
      integral_mono hint1 hint2 fun y => norm_sub_le _ _
    have h2 : ∫ y in Metric.closedBall x r, (‖H y‖ + ‖⨍ z in Metric.closedBall x r, H z‖) =
        (∫ y in Metric.closedBall x r, ‖H y‖) +
          volume.real (Metric.closedBall x r) * ‖⨍ z in Metric.closedBall x r, H z‖ := by
      rw [integral_add hHon.norm hcs, setIntegral_const, smul_eq_mul]
    rwa [h2] at h1
  rw [fieldExcess_eq_inv_mul]
  have hinv : 0 ≤ (volume.real (Metric.closedBall x r))⁻¹ := inv_nonneg.2 hvol.le
  calc (volume.real (Metric.closedBall x r))⁻¹ *
        ∫ y in Metric.closedBall x r, ‖H y - ⨍ z in Metric.closedBall x r, H z‖
      ≤ (volume.real (Metric.closedBall x r))⁻¹ *
        ((∫ y in Metric.closedBall x r, ‖H y‖) +
          volume.real (Metric.closedBall x r) * ‖⨍ z in Metric.closedBall x r, H z‖) :=
        mul_le_mul_of_nonneg_left hle hinv
    _ = (volume.real (Metric.closedBall x r))⁻¹ * (∫ y in Metric.closedBall x r, ‖H y‖) +
          ‖⨍ z in Metric.closedBall x r, H z‖ := by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hvol.ne', one_mul]
    _ ≤ 2 * ((volume.real (Metric.closedBall x r))⁻¹ *
          ∫ y in Metric.closedBall x r, ‖H y‖) := by linarith [hmean]

/-- `t ≤ 1 + t^p` for `t ≥ 0` and `p ≥ 1`. -/
theorem le_one_add_rpow {p t : ℝ} (hp : 1 ≤ p) (ht : 0 ≤ t) : t ≤ 1 + t ^ p := by
  rcases le_total t 1 with h | h
  · linarith [Real.rpow_nonneg ht p]
  · have h1 : t ^ (1 : ℝ) ≤ t ^ p := Real.rpow_le_rpow_of_exponent_le h hp
    rw [Real.rpow_one] at h1
    linarith

/-- **A uniform bound for the excess at a fixed scale**: for `H` locally integrable with
`‖H‖^p ∈ L¹` (`p ≥ 1`) the excess `fieldExcess H x r` is bounded by a constant independent of
the centre `x` (`‖H‖ ≤ 1 + ‖H‖^p` pointwise, plus translation invariance of the volume of
balls). This is the uniform top bound `E(R₀) ≤ M₀` needed by the Giaquinta iteration. -/
theorem exists_fieldExcess_bound {p : ℝ} (hp : 1 ≤ p) {H : Euc d → Euc d}
    (hH : LocallyIntegrable H) (hHp : Integrable fun y => ‖H y‖ ^ p) {r : ℝ} (hr : 0 < r) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ x : Euc d, fieldExcess H x r ≤ M₀ := by
  have hω : 0 < volume.real (Metric.closedBall (0 : Euc d) 1) := volume_real_closedBall_pos
  have hvolpos : 0 < r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) :=
    mul_pos (pow_pos hr d) hω
  have hIp : 0 ≤ ∫ y, ‖H y‖ ^ p := integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) p
  have hinv0 : (0 : ℝ) ≤ (r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))⁻¹ :=
    inv_nonneg.2 hvolpos.le
  refine ⟨2 * ((r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1))⁻¹ *
    (r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) + ∫ y, ‖H y‖ ^ p)), ?_, fun x => ?_⟩
  · have hsum : (0 : ℝ) ≤ r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) +
        ∫ y, ‖H y‖ ^ p := by linarith
    have := mul_nonneg hinv0 hsum
    linarith
  have hvol : volume.real (Metric.closedBall x r) =
      r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) := volume_real_closedBall x hr.le
  have hHon : IntegrableOn H (Metric.closedBall x r) :=
    hH.integrableOn_isCompact (isCompact_closedBall x r)
  have hone : IntegrableOn (fun _ : Euc d => (1 : ℝ)) (Metric.closedBall x r) :=
    integrableOn_const measure_closedBall_lt_top.ne
  have hbd : ∫ y in Metric.closedBall x r, ‖H y‖ ≤
      r ^ d * volume.real (Metric.closedBall (0 : Euc d) 1) + ∫ y, ‖H y‖ ^ p := by
    have h1 : ∫ y in Metric.closedBall x r, ‖H y‖ ≤
        ∫ y in Metric.closedBall x r, (1 + ‖H y‖ ^ p) :=
      integral_mono hHon.norm (hone.add hHp.integrableOn)
        fun y => le_one_add_rpow hp (norm_nonneg _)
    have h2 : ∫ y in Metric.closedBall x r, (1 + ‖H y‖ ^ p) =
        volume.real (Metric.closedBall x r) + ∫ y in Metric.closedBall x r, ‖H y‖ ^ p := by
      rw [integral_add hone hHp.integrableOn, setIntegral_const, smul_eq_mul, mul_one]
    have h3 : ∫ y in Metric.closedBall x r, ‖H y‖ ^ p ≤ ∫ y, ‖H y‖ ^ p :=
      setIntegral_le_integral hHp
        (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) p)
    rw [hvol] at h2
    linarith
  have hkey := fieldExcess_le_two_mul hH x hr
  rw [hvol] at hkey
  refine hkey.trans ?_
  have := mul_le_mul_of_nonneg_left hbd hinv0
  linarith

/-! ### The Giaquinta/Campanato iteration -/

/-- For `A ≥ 0` and `α > 0` there is `τ ∈ (0, 1)` with `A τ^α ≤ 1/2`. -/
theorem exists_pos_lt_one_mul_rpow_le_half {A α : ℝ} (hA : 0 ≤ A) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ A * τ ^ α ≤ 1 / 2 := by
  have hden : (0 : ℝ) < 2 * (A + 1) := by linarith
  have hfrac : (0 : ℝ) < 1 / (2 * (A + 1)) := div_pos one_pos hden
  have hs0 : (0 : ℝ) < (1 / (2 * (A + 1))) ^ α⁻¹ := Real.rpow_pos_of_pos hfrac _
  refine ⟨min (1 / 2) ((1 / (2 * (A + 1))) ^ α⁻¹), lt_min (by norm_num) hs0,
    lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
  have hτ0 : (0 : ℝ) ≤ min (1 / 2) ((1 / (2 * (A + 1))) ^ α⁻¹) :=
    le_of_lt (lt_min (by norm_num) hs0)
  have hpow : (min (1 / 2 : ℝ) ((1 / (2 * (A + 1))) ^ α⁻¹)) ^ α ≤ 1 / (2 * (A + 1)) := by
    calc (min (1 / 2 : ℝ) ((1 / (2 * (A + 1))) ^ α⁻¹)) ^ α
        ≤ ((1 / (2 * (A + 1))) ^ α⁻¹) ^ α :=
          Real.rpow_le_rpow hτ0 (min_le_right _ _) hα.le
      _ = 1 / (2 * (A + 1)) := by
          rw [← Real.rpow_mul hfrac.le, inv_mul_cancel₀ hα.ne', Real.rpow_one]
  calc A * (min (1 / 2 : ℝ) ((1 / (2 * (A + 1))) ^ α⁻¹)) ^ α ≤ A * (1 / (2 * (A + 1))) :=
        mul_le_mul_of_nonneg_left hpow hA
    _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hden]
        linarith

/-- **The Giaquinta/Campanato iteration lemma** (Giaquinta–Martinazzi, *An Introduction to the
Regularity Theory for Elliptic Systems*, Lemma 5.13; Giaquinta, *Multiple Integrals in the
Calculus of Variations*, Ch. III, Lemma 2.1), in the normalized (excess) form used by
DiBenedetto's gradient estimate: a nonnegative `E` with the two-scale decay
`E ρ ≤ A (ρ/r)^β E r + Bc r^β` for `0 < ρ ≤ r ≤ R₀` and the top bound `E R₀ ≤ M₀` obeys the power
decay `E r ≤ C r^α` on `(0, R₀]`, with `α = β/2 > 0` and `C ≥ 0` depending only on
`A, Bc, β, R₀, M₀` — in particular uniformly over all such `E`, hence over the centres of the
balls in the application.

Proof: choose `τ ∈ (0,1)` with `A τ^α ≤ 1/2` and iterate on `r_k = τ^k R₀`. With
`D = M₀ R₀^{-α} + 2 Bc R₀^α τ^{-α}` an induction gives `E r_k ≤ D r_k^α`; for a general
`r ∈ (0, R₀]` pick `k` with `r_{k+1} < r ≤ r_k` and use the decay once more at the pair
`(r, r_k)` together with `r_k < r/τ`. -/
theorem excess_power_decay {A Bc β R₀ M₀ : ℝ} (hA : 0 ≤ A) (hBc : 0 ≤ Bc) (hβ : 0 < β)
    (hR₀ : 0 < R₀) (hM₀ : 0 ≤ M₀) :
    ∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧
      ∀ E : ℝ → ℝ, (∀ r, 0 ≤ E r) → E R₀ ≤ M₀ →
        (∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → r ≤ R₀ → E ρ ≤ A * (ρ / r) ^ β * E r + Bc * r ^ β) →
        ∀ r : ℝ, 0 < r → r ≤ R₀ → E r ≤ C * r ^ α := by
  have hα : (0 : ℝ) < β / 2 := by linarith
  obtain ⟨τ, hτ0, hτ1, hτA⟩ := exists_pos_lt_one_mul_rpow_le_half hA hα
  have hβsum : β / 2 + β / 2 = β := by ring
  have hτα : (0 : ℝ) < τ ^ (β / 2) := Real.rpow_pos_of_pos hτ0 _
  have hR₀α : (0 : ℝ) < R₀ ^ (β / 2) := Real.rpow_pos_of_pos hR₀ _
  have hM₀S : (0 : ℝ) ≤ M₀ * (R₀ ^ (β / 2))⁻¹ := mul_nonneg hM₀ (inv_nonneg.2 hR₀α.le)
  have hcst0 : (0 : ℝ) ≤ Bc * R₀ ^ (β / 2) * (τ ^ (β / 2))⁻¹ :=
    mul_nonneg (mul_nonneg hBc hR₀α.le) (inv_nonneg.2 hτα.le)
  have hD0 : (0 : ℝ) ≤ M₀ * (R₀ ^ (β / 2))⁻¹ + 2 * (Bc * R₀ ^ (β / 2) * (τ ^ (β / 2))⁻¹) := by
    linarith
  refine ⟨β / 2, (A * (M₀ * (R₀ ^ (β / 2))⁻¹ + 2 * (Bc * R₀ ^ (β / 2) * (τ ^ (β / 2))⁻¹)) +
      Bc * R₀ ^ (β / 2)) * (τ ^ (β / 2))⁻¹, hα,
    mul_nonneg (add_nonneg (mul_nonneg hA hD0) (mul_nonneg hBc hR₀α.le))
      (inv_nonneg.2 hτα.le), ?_⟩
  intro E hE0 hEM hdec
  set D : ℝ := M₀ * (R₀ ^ (β / 2))⁻¹ + 2 * (Bc * R₀ ^ (β / 2) * (τ ^ (β / 2))⁻¹) with hD_def
  -- the geometric radii `r_k = τ^k R₀`
  have hrk0 : ∀ k : ℕ, (0 : ℝ) < τ ^ k * R₀ := fun k => mul_pos (pow_pos hτ0 k) hR₀
  have hrkR : ∀ k : ℕ, τ ^ k * R₀ ≤ R₀ := fun k => by
    calc τ ^ k * R₀ ≤ 1 * R₀ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hτ0.le hτ1.le) hR₀.le
      _ = R₀ := one_mul _
  have hrksucc : ∀ k : ℕ, τ ^ (k + 1) * R₀ = τ * (τ ^ k * R₀) := fun k => by
    rw [pow_succ]
    ring
  have hrkmono : ∀ k : ℕ, τ ^ (k + 1) * R₀ ≤ τ ^ k * R₀ := fun k => by
    rw [hrksucc k]
    calc τ * (τ ^ k * R₀) ≤ 1 * (τ ^ k * R₀) :=
          mul_le_mul_of_nonneg_right hτ1.le (hrk0 k).le
      _ = τ ^ k * R₀ := one_mul _
  have hTne : τ ^ (β / 2) ≠ 0 := hτα.ne'
  -- `Bc R₀^{β/2} ≤ (1/2) D τ^{β/2}`
  have hDT : Bc * R₀ ^ (β / 2) ≤ 1 / 2 * D * τ ^ (β / 2) := by
    have h1 : 2 * (Bc * R₀ ^ (β / 2) * (τ ^ (β / 2))⁻¹) ≤ D := by
      rw [hD_def]
      linarith
    have h3 : 2 * (Bc * R₀ ^ (β / 2) * (τ ^ (β / 2))⁻¹) * τ ^ (β / 2) ≤ D * τ ^ (β / 2) :=
      mul_le_mul_of_nonneg_right h1 hτα.le
    have h2 : 2 * (Bc * R₀ ^ (β / 2) * (τ ^ (β / 2))⁻¹) * τ ^ (β / 2) =
        2 * (Bc * R₀ ^ (β / 2)) := by
      rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hTne, mul_one]
    rw [h2] at h3
    linarith
  -- the induction on the geometric radii
  have hind : ∀ k : ℕ, E (τ ^ k * R₀) ≤ D * (τ ^ k * R₀) ^ (β / 2) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, one_mul]
      have hMD : M₀ = M₀ * (R₀ ^ (β / 2))⁻¹ * R₀ ^ (β / 2) := by
        rw [mul_assoc, inv_mul_cancel₀ hR₀α.ne', mul_one]
      have hle : M₀ * (R₀ ^ (β / 2))⁻¹ ≤ D := by
        rw [hD_def]
        linarith
      calc E R₀ ≤ M₀ := hEM
        _ = M₀ * (R₀ ^ (β / 2))⁻¹ * R₀ ^ (β / 2) := hMD
        _ ≤ D * R₀ ^ (β / 2) := mul_le_mul_of_nonneg_right hle hR₀α.le
    | succ k ih =>
      have hratio : τ ^ (k + 1) * R₀ / (τ ^ k * R₀) = τ := by
        rw [hrksucc k, mul_div_cancel_right₀ _ (hrk0 k).ne']
      have hd1 := hdec (τ ^ (k + 1) * R₀) (τ ^ k * R₀) (hrk0 _) (hrkmono k) (hrkR k)
      rw [hratio] at hd1
      have hτβ : τ ^ β = τ ^ (β / 2) * τ ^ (β / 2) := by
        rw [← Real.rpow_add hτ0, hβsum]
      have hrβ : (τ ^ k * R₀) ^ β = (τ ^ k * R₀) ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) := by
        rw [← Real.rpow_add (hrk0 k), hβsum]
      have hrα0 : (0 : ℝ) ≤ (τ ^ k * R₀) ^ (β / 2) := Real.rpow_nonneg (hrk0 k).le _
      have hrαle : (τ ^ k * R₀) ^ (β / 2) ≤ R₀ ^ (β / 2) :=
        Real.rpow_le_rpow (hrk0 k).le (hrkR k) hα.le
      have hsucc : (τ ^ (k + 1) * R₀) ^ (β / 2) = τ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) := by
        rw [hrksucc k, Real.mul_rpow hτ0.le (hrk0 k).le]
      rw [hsucc]
      rw [hτβ, hrβ] at hd1
      have hEk0 : 0 ≤ E (τ ^ k * R₀) := hE0 _
      have hAτ : A * (τ ^ (β / 2) * τ ^ (β / 2)) ≤ 1 / 2 * τ ^ (β / 2) := by
        have h := mul_le_mul_of_nonneg_right hτA hτα.le
        calc A * (τ ^ (β / 2) * τ ^ (β / 2)) = A * τ ^ (β / 2) * τ ^ (β / 2) := by ring
          _ ≤ 1 / 2 * τ ^ (β / 2) := h
      have hhalf : (0 : ℝ) ≤ 1 / 2 * τ ^ (β / 2) := by linarith
      have hstep1 : A * (τ ^ (β / 2) * τ ^ (β / 2)) * E (τ ^ k * R₀) ≤
          1 / 2 * τ ^ (β / 2) * (D * (τ ^ k * R₀) ^ (β / 2)) := by
        have hle1 : A * (τ ^ (β / 2) * τ ^ (β / 2)) * E (τ ^ k * R₀) ≤
            1 / 2 * τ ^ (β / 2) * E (τ ^ k * R₀) :=
          mul_le_mul_of_nonneg_right hAτ hEk0
        have hle2 : 1 / 2 * τ ^ (β / 2) * E (τ ^ k * R₀) ≤
            1 / 2 * τ ^ (β / 2) * (D * (τ ^ k * R₀) ^ (β / 2)) :=
          mul_le_mul_of_nonneg_left ih hhalf
        linarith
      have hmul : (τ ^ k * R₀) ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) ≤
          R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) :=
        mul_le_mul_of_nonneg_right hrαle hrα0
      have hstep2 : Bc * ((τ ^ k * R₀) ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2)) ≤
          1 / 2 * D * τ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) := by
        have hle1 : Bc * ((τ ^ k * R₀) ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2)) ≤
            Bc * R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) := by
          calc Bc * ((τ ^ k * R₀) ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2))
              ≤ Bc * (R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2)) :=
                mul_le_mul_of_nonneg_left hmul hBc
            _ = Bc * R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) := by ring
        have hle2 : Bc * R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) ≤
            1 / 2 * D * τ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) :=
          mul_le_mul_of_nonneg_right hDT hrα0
        linarith
      linarith
  -- general radii
  intro r hr hrR₀
  have hPex : ∃ n : ℕ, τ ^ (n + 1) * R₀ < r := by
    have htend : Tendsto (fun n : ℕ => τ ^ n * R₀) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hτ0.le hτ1).mul_const R₀
      simpa using h
    obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hr)).exists
    exact ⟨n, lt_of_le_of_lt (hrkmono n) hn⟩
  classical
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, τ ^ (k + 1) * R₀ < r ∧ r ≤ τ ^ k * R₀ := by
    refine ⟨Nat.find hPex, Nat.find_spec hPex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hPex) with hk | hk
    · rw [hk]
      simpa using hrR₀
    · have hmin := Nat.find_min hPex (m := Nat.find hPex - 1) (by omega)
      rw [not_lt] at hmin
      have he : Nat.find hPex - 1 + 1 = Nat.find hPex := by omega
      rwa [he] at hmin
  have hdr := hdec r (τ ^ k * R₀) hr hk2 (hrkR k)
  have hratio1 : (r / (τ ^ k * R₀)) ^ β ≤ 1 :=
    Real.rpow_le_one (le_of_lt (div_pos hr (hrk0 k))) ((div_le_one (hrk0 k)).2 hk2) hβ.le
  have hEk0 : 0 ≤ E (τ ^ k * R₀) := hE0 _
  have hAE : (0 : ℝ) ≤ A * E (τ ^ k * R₀) := mul_nonneg hA hEk0
  have hstep1 : E r ≤ A * E (τ ^ k * R₀) + Bc * (τ ^ k * R₀) ^ β := by
    have hq : A * (r / (τ ^ k * R₀)) ^ β * E (τ ^ k * R₀) ≤ A * E (τ ^ k * R₀) := by
      calc A * (r / (τ ^ k * R₀)) ^ β * E (τ ^ k * R₀)
          = A * E (τ ^ k * R₀) * (r / (τ ^ k * R₀)) ^ β := by ring
        _ ≤ A * E (τ ^ k * R₀) * 1 := mul_le_mul_of_nonneg_left hratio1 hAE
        _ = A * E (τ ^ k * R₀) := mul_one _
    linarith
  have hrβ : (τ ^ k * R₀) ^ β = (τ ^ k * R₀) ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) := by
    rw [← Real.rpow_add (hrk0 k), hβsum]
  have hrα0 : (0 : ℝ) ≤ (τ ^ k * R₀) ^ (β / 2) := Real.rpow_nonneg (hrk0 k).le _
  have hrαle : (τ ^ k * R₀) ^ (β / 2) ≤ R₀ ^ (β / 2) :=
    Real.rpow_le_rpow (hrk0 k).le (hrkR k) hα.le
  have hmul : (τ ^ k * R₀) ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) ≤
      R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) :=
    mul_le_mul_of_nonneg_right hrαle hrα0
  have hstep2 : E r ≤ (A * D + Bc * R₀ ^ (β / 2)) * (τ ^ k * R₀) ^ (β / 2) := by
    have h1 : A * E (τ ^ k * R₀) ≤ A * (D * (τ ^ k * R₀) ^ (β / 2)) :=
      mul_le_mul_of_nonneg_left (hind k) hA
    have h2 : Bc * (τ ^ k * R₀) ^ β ≤ Bc * R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) := by
      rw [hrβ]
      calc Bc * ((τ ^ k * R₀) ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2))
          ≤ Bc * (R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2)) :=
            mul_le_mul_of_nonneg_left hmul hBc
        _ = Bc * R₀ ^ (β / 2) * (τ ^ k * R₀) ^ (β / 2) := by ring
    linarith
  have hrklt : τ ^ k * R₀ ≤ r / τ := by
    rw [le_div_iff₀ hτ0]
    have h := hk1
    rw [hrksucc k] at h
    linarith
  have hrkα : (τ ^ k * R₀) ^ (β / 2) ≤ r ^ (β / 2) * (τ ^ (β / 2))⁻¹ := by
    calc (τ ^ k * R₀) ^ (β / 2) ≤ (r / τ) ^ (β / 2) :=
          Real.rpow_le_rpow (hrk0 k).le hrklt hα.le
      _ = r ^ (β / 2) / τ ^ (β / 2) := Real.div_rpow hr.le hτ0.le _
      _ = r ^ (β / 2) * (τ ^ (β / 2))⁻¹ := div_eq_mul_inv _ _
  have hcoef0 : (0 : ℝ) ≤ A * D + Bc * R₀ ^ (β / 2) :=
    add_nonneg (mul_nonneg hA hD0) (mul_nonneg hBc hR₀α.le)
  calc E r ≤ (A * D + Bc * R₀ ^ (β / 2)) * (τ ^ k * R₀) ^ (β / 2) := hstep2
    _ ≤ (A * D + Bc * R₀ ^ (β / 2)) * (r ^ (β / 2) * (τ ^ (β / 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hrkα hcoef0
    _ = (A * D + Bc * R₀ ^ (β / 2)) * (τ ^ (β / 2))⁻¹ * r ^ (β / 2) := by ring

end Komlos.Literature
