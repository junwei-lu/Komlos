import Komlos.Literature.Regularized.DeGiorgiOsc

/-!
# De Giorgi–Nash–Moser for linear equations with measurable coefficients

Lane `DGN` of `REGULARIZED_ROUTE.md` (Revision 2).  On an open set `Ω ⊆ ℝ^d` we consider the
divergence-form equation

`-div (A ∇z) = -div f + g`,

with `A : ℝ^d → (ℝ^d →L ℝ^d)` merely **measurable**, uniformly elliptic and bounded
(`λ‖ξ‖² ≤ ⟪A x ξ, ξ⟫`, `‖A x‖ ≤ Λ` a.e. on `Ω`), and bounded forcing (`‖f‖ ≤ M`, `|g| ≤ N`
a.e. on `Ω`).  The unknown `z` is only assumed to have a weak gradient `G`, with `z` and `G`
square integrable on every closed ball contained in `Ω` — no global Sobolev regularity.

## The weak formulation

`IsDGTest Ω T ψ` collects the admissible test functions: `ψ ∈ W₀^{1,2}(T)` for a compact
`T ⊆ Ω` whose weak gradient vanishes a.e. off `T`.  This is the `W^{1,2}` closure of
`C_c^∞(Ω)`, which is what the Caccioppoli argument needs: the test function `η² (z-k)_+` is
Lipschitz, not smooth.

**DEVIATION** from the lane brief, which asks for the equation tested against *smooth*
compactly supported `ψ`.  Passing from smooth to `W^{1,2}` test functions is a density
statement; the project has it for *equalities*
(`Komlos.Literature.integral_inner_weakGrad_eq_of_memW0_two`, used for solutions), but the
sub-solution inequality additionally needs the approximating sequence to stay nonnegative,
which the existing approximation lemma does not expose.  Rather than weaken the sub-solution
statement, the hypothesis is stated for `W^{1,2}` test functions directly — the same
convention as the project's own `Komlos.Literature.IsWeakEigensolution`, whose `weakEq` field
is likewise quantified over all of `W₀^{1,p}(K)`.

## Main results

* `exists_dgSub_const` — **(1) Caccioppoli on level sets**: a sub-solution lies in the
  De Giorgi class `DG⁺(Ω, γ, M + N R₀)` with `γ = γ(d, λ, Λ)`.
* `exists_dg_const` — solutions lie in `DG(Ω, γ, M + N R₀)`.
* `IsLinearSubsol.exists_essSup_bound` — **(2) local boundedness**
  `ess sup_{B_{R/2}} z_+ ≤ C ((⨍_{B_R} z_+²)^{1/2} + M R + N R²)`.
* `IsLinearSol.exists_osc_decay`, `IsLinearSol.exists_holder_representative` —
  **(3) the interior Hölder estimate** and the Hölder continuous representative.

(2) and (3) are proved here *from* the abstract De Giorgi class theory of
`Komlos/Literature/Regularized/DeGiorgiClass.lean`; only (1) is specific to the equation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Coefficients, data and the weak formulation -/

/-- Uniformly elliptic, bounded, measurable coefficients on `Ω`. -/
structure IsUnifElliptic (lam Lam : ℝ) (Ω : Set (Euc d))
    (A : Euc d → (Euc d →L[ℝ] Euc d)) : Prop where
  /-- Ellipticity: `λ ‖ξ‖² ≤ ⟪A x ξ, ξ⟫`. -/
  elliptic : ∀ᵐ x, x ∈ Ω → ∀ ξ : Euc d, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫
  /-- Boundedness: `‖A x‖ ≤ Λ`. -/
  bddCoeff : ∀ᵐ x, x ∈ Ω → ‖A x‖ ≤ Lam

/-- Admissible Sobolev test functions for the weak formulation on `Ω`: `ψ ∈ W₀^{1,2}(T)` for a
compact `T ⊆ Ω`, with `∇ψ = 0` a.e. off `T`. -/
structure IsDGTest (Ω T : Set (Euc d)) (ψ : Euc d → ℝ) : Prop where
  /-- `T` is compact. -/
  isCompact : IsCompact T
  /-- `T ⊆ Ω`. -/
  subset : T ⊆ Ω
  /-- `ψ ∈ W₀^{1,2}(T)`. -/
  memW0 : MemW0 2 T ψ
  /-- The weak gradient of `ψ` vanishes a.e. off `T`. -/
  grad_eq_zero : ∀ᵐ x, x ∉ T → weakGrad ψ x = 0

/-- A **weak sub-solution** of `-div (A ∇z) ≤ -div f + g` on `Ω`, with bounded measurable
data.  `lam`, `Lam` are the ellipticity constants, `M` bounds `‖f‖` and `N` bounds `|g|`. -/
structure IsLinearSubsol (lam Lam M N : ℝ) (A : Euc d → (Euc d →L[ℝ] Euc d))
    (f : Euc d → Euc d) (g : Euc d → ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ)
    (G : Euc d → Euc d) : Prop where
  /-- The coefficients are uniformly elliptic and bounded. -/
  coeff : IsUnifElliptic lam Lam Ω A
  /-- `G` is a weak gradient of `z`. -/
  hasWeakGradient : HasWeakGradient z G
  /-- `z` is measurable. -/
  measurable : Measurable z
  /-- `G` is measurable. -/
  measurable_grad : Measurable G
  /-- The flux `A ∇z` is measurable. -/
  aesm_flux : AEStronglyMeasurable (fun x => A x (G x)) volume
  /-- `f` is measurable. -/
  aesm_f : AEStronglyMeasurable f volume
  /-- `g` is measurable. -/
  aesm_g : AEStronglyMeasurable g volume
  /-- `z` and `G` are square integrable on closed balls inside `Ω`. -/
  integrableOn : ∀ (x₀ : Euc d) (s : ℝ), Metric.closedBall x₀ s ⊆ Ω →
    IntegrableOn (fun x => z x ^ 2) (Metric.closedBall x₀ s) volume ∧
      IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ s) volume
  /-- `‖f‖ ≤ M` a.e. on `Ω`. -/
  bound_f : ∀ᵐ x, x ∈ Ω → ‖f x‖ ≤ M
  /-- `|g| ≤ N` a.e. on `Ω`. -/
  bound_g : ∀ᵐ x, x ∈ Ω → |g x| ≤ N
  /-- The weak inequality, tested against nonnegative Sobolev test functions. -/
  subeq : ∀ (T : Set (Euc d)) (ψ : Euc d → ℝ), IsDGTest Ω T ψ → (∀ x, 0 ≤ ψ x) →
    (∫ x, ⟪A x (G x), weakGrad ψ x⟫) ≤ ∫ x, (⟪f x, weakGrad ψ x⟫ + g x * ψ x)

/-- A **weak solution** of `-div (A ∇z) = -div f + g` on `Ω`. -/
structure IsLinearSol (lam Lam M N : ℝ) (A : Euc d → (Euc d →L[ℝ] Euc d))
    (f : Euc d → Euc d) (g : Euc d → ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ)
    (G : Euc d → Euc d) : Prop where
  /-- The coefficients are uniformly elliptic and bounded. -/
  coeff : IsUnifElliptic lam Lam Ω A
  /-- `G` is a weak gradient of `z`. -/
  hasWeakGradient : HasWeakGradient z G
  /-- `z` is measurable. -/
  measurable : Measurable z
  /-- `G` is measurable. -/
  measurable_grad : Measurable G
  /-- The flux `A ∇z` is measurable. -/
  aesm_flux : AEStronglyMeasurable (fun x => A x (G x)) volume
  /-- `f` is measurable. -/
  aesm_f : AEStronglyMeasurable f volume
  /-- `g` is measurable. -/
  aesm_g : AEStronglyMeasurable g volume
  /-- `z` and `G` are square integrable on closed balls inside `Ω`. -/
  integrableOn : ∀ (x₀ : Euc d) (s : ℝ), Metric.closedBall x₀ s ⊆ Ω →
    IntegrableOn (fun x => z x ^ 2) (Metric.closedBall x₀ s) volume ∧
      IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ s) volume
  /-- `‖f‖ ≤ M` a.e. on `Ω`. -/
  bound_f : ∀ᵐ x, x ∈ Ω → ‖f x‖ ≤ M
  /-- `|g| ≤ N` a.e. on `Ω`. -/
  bound_g : ∀ᵐ x, x ∈ Ω → |g x| ≤ N
  /-- The weak equation, tested against Sobolev test functions. -/
  weakEq : ∀ (T : Set (Euc d)) (ψ : Euc d → ℝ), IsDGTest Ω T ψ →
    (∫ x, ⟪A x (G x), weakGrad ψ x⟫) = ∫ x, (⟪f x, weakGrad ψ x⟫ + g x * ψ x)

/-! ### (1) Caccioppoli on level sets -/

set_option maxHeartbeats 4000000 in
/-- **Caccioppoli inequality on level sets**: a weak sub-solution of
`-div(A ∇z) ≤ -div f + g` on `Ω` belongs to the De Giorgi class `DG⁺(Ω, γ, M + N R₀)` at
every scale `R₀`, with `γ` depending only on the ellipticity constants `λ, Λ` (and the
absolute cutoff constant of `exists_cutoff_const`).

Proof: test the inequality with `ψ = η² (z - k)_+`, where `η` is a cutoff between the balls
of radii `r` and `r + (s-r)/3` (`exists_cutoff_const`, `‖∇η‖ ≤ 3C/(s-r)`).  That `ψ` is an
admissible test function is `memW0_two_mul_cutoff` (localization of `z` by a second cutoff
`ζ ≡ 1` near `supp η`), `memW0_posPart` (the truncation chain rule) and
`MemW0.contDiff_mul_const_add` (multiplication by `η²`, restoring the constant `(-k)_+`
subtracted in `posPartShift`).  Expanding
`∇ψ = η² 1_{z>k} G + 2 η (z-k)_+ ∇η`, ellipticity on the first term and Young's inequality on
the others give the inequality with `γ χ² = (2/λ)(M²/λ + M² + N²(s-r)²/2)`, which
`χ = M + N R₀` and a large enough `γ` dominate. -/
theorem exists_dgSub_const {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 ≤ Lam) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (M N R₀ : ℝ) (A : Euc d → (Euc d →L[ℝ] Euc d)) (f : Euc d → Euc d)
      (g : Euc d → ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
      0 ≤ M → 0 ≤ N → 0 ≤ R₀ → IsLinearSubsol lam Lam M N A f g Ω z G →
      IsDGSub γ (M + N * R₀) R₀ Ω z G := by
  obtain ⟨C, hC, hcut⟩ := exists_cutoff_const d
  refine ⟨max ((2 / lam) * ((4 * Lam ^ 2 / lam + 1) * (3 * C) ^ 2 + 1 / 2))
      ((2 / lam) * (1 / lam + 1)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
  intro M N R₀ A f g Ω z G hM hN hR₀ hz
  set γ : ℝ := max ((2 / lam) * ((4 * Lam ^ 2 / lam + 1) * (3 * C) ^ 2 + 1 / 2))
    ((2 / lam) * (1 / lam + 1)) with hγdef
  refine { hasWeakGradient := hz.hasWeakGradient, measurable := hz.measurable
           measurable_grad := hz.measurable_grad, integrableOn := hz.integrableOn
           energy := ?_ }
  intro x₀ r s k hr hrs hsR hball
  -- radii and cutoffs
  have hsr : (0 : ℝ) < s - r := by linarith
  set ρ₁ := r + (s - r) / 3 with hρ₁def
  set ρ₂ := r + 2 * (s - r) / 3 with hρ₂def
  have hrρ₁ : r < ρ₁ := by simp only [hρ₁def]; linarith
  have hρ₁ρ₂ : ρ₁ < ρ₂ := by simp only [hρ₁def, hρ₂def]; linarith
  have hρ₂s : ρ₂ < s := by simp only [hρ₂def]; linarith
  obtain ⟨η, hηC, hηcs, hηsupp, hη0, hη1, hηone, hηgrad⟩ := hcut x₀ r ρ₁ hr hrρ₁
  obtain ⟨ζ, hζC, hζcs, hζsupp, hζ0, hζ1, hζone, hζgrad⟩ :=
    hcut x₀ ρ₂ s (by linarith) hρ₂s
  have hηg' : ∀ x, ‖gradient η x‖ ≤ 3 * C / (s - r) := by
    intro x
    refine (hηgrad x).trans (le_of_eq ?_)
    have he : ρ₁ - r = (s - r) / 3 := by rw [hρ₁def]; ring
    rw [he, div_div_eq_mul_div]
    ring
  obtain ⟨hz2, hG2⟩ := hz.integrableOn x₀ s hball
  have hzm : AEStronglyMeasurable z volume := hz.measurable.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G volume := hz.measurable_grad.aestronglyMeasurable
  have hζabs : ∀ x, |ζ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hζ0 x], hζ1 x⟩
  -- the localized function and its truncation
  obtain ⟨hZ, hZg⟩ := memW0_two_mul_cutoff hz.hasWeakGradient hzm hGm hz2 hG2 hζC hζcs
    hζsupp hζabs
  obtain ⟨hW, hWg⟩ := memW0_posPart (p := 2) one_lt_two hZ k
  -- the test function `ψ = η² (z - k)_+`
  have hη2C : ContDiff ℝ ∞ (fun x => η x ^ 2) := hηC.pow 2
  have hη2cs : HasCompactSupport (fun x => η x ^ 2) := by
    have h := hηcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    simpa only [Function.comp_def] using h
  have hη2supp : tsupport (fun x => η x ^ 2) ⊆ Metric.closedBall x₀ s := by
    have hsupp : Function.support (fun x => η x ^ 2) = Function.support η := by
      ext x
      simp [Function.mem_support]
    show closure (Function.support (fun x => η x ^ 2)) ⊆ Metric.closedBall x₀ s
    rw [hsupp]
    exact hηsupp.trans (Metric.closedBall_subset_closedBall (by linarith))
  obtain ⟨hψ, hψg⟩ := hW.contDiff_mul_const_add hη2C hη2cs hη2supp (max (-k) 0)
  -- notation
  set w : Euc d → ℝ := fun x => max (z x - k) 0 with hwdef
  set ind : Euc d → ℝ := fun x => if k < z x then (1 : ℝ) else 0 with hinddef
  set Φ : Euc d → Euc d :=
    fun x => (η x ^ 2 * ind x) • G x + (2 * η x * w x) • gradient η x with hΦdef
  -- behaviour off the support of `η`, and near it
  have hηzero : ∀ x, x ∉ tsupport η → η x = 0 ∧ gradient η x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx, gradient_eq_zero_of_notMem_tsupport hx⟩
  have hζat : ∀ x ∈ tsupport η, ζ x = 1 ∧ gradient ζ x = 0 := by
    intro x hx
    have hx1 : x ∈ Metric.closedBall x₀ ρ₁ := hηsupp hx
    refine ⟨hζone x (Metric.closedBall_subset_closedBall hρ₁ρ₂.le hx1), ?_⟩
    have hxb : x ∈ Metric.ball x₀ ρ₂ := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.1 hx1) hρ₁ρ₂
    have hev : ζ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with y hy
      exact hζone y (Metric.ball_subset_closedBall hy)
    have hfd : fderiv ℝ ζ x = 0 := by rw [hev.fderiv_eq]; simp
    refine ext_inner_right ℝ fun v => ?_
    rw [← fderiv_apply_eq_inner_gradient, hfd]
    simp
  have hη1C : ContDiff ℝ 1 η := hηC.of_le (by simp)
  have hηd : ∀ x, DifferentiableAt ℝ η x := fun x => hη1C.differentiable one_ne_zero x
  have hgη2 : ∀ x, gradient (fun y => η y ^ 2) x = (2 * η x) • gradient η x := by
    intro x
    rw [gradient_pow_apply (hηd x) 2]
    norm_num
  -- the test function is `η² (z - k)_+`
  have hψval : ∀ x, η x ^ 2 * (max (-k) 0 + posPartShift k (ζ x * z x)) = η x ^ 2 * w x := by
    intro x
    by_cases hx : x ∈ tsupport η
    · rw [(hζat x hx).1, one_mul]
      simp only [posPartShift, hwdef]
      ring
    · rw [(hηzero x hx).1]
      simp
  have hψnonneg : ∀ x, 0 ≤ η x ^ 2 * (max (-k) 0 + posPartShift k (ζ x * z x)) := by
    intro x
    have : max (-k) 0 + posPartShift k (ζ x * z x) = max (ζ x * z x - k) 0 := by
      simp only [posPartShift]; ring
    rw [this]
    positivity
  have hΦeq : weakGrad (fun x => η x ^ 2 * (max (-k) 0 + posPartShift k (ζ x * z x)))
      =ᵐ[volume] Φ := by
    filter_upwards [hψg, hW.hasWeakGradient.weakGrad_ae_eq.symm.trans
      (hWg.weakGrad_ae_eq), hZg] with x hx hxW hxZ
    rw [hx, hgη2 x]
    by_cases hxη : x ∈ tsupport η
    · obtain ⟨hζ1x, hζg0⟩ := hζat x hxη
      have hZx : ζ x * z x = z x := by rw [hζ1x, one_mul]
      have hWgx : weakGrad (fun y => posPartShift k (ζ y * z y)) x = ind x • G x := by
        rw [hxW]
        simp only [hZx, hinddef]
        rw [hxZ, hζ1x, hζg0, one_smul, smul_zero, add_zero]
      rw [hWgx]
      have hval : max (-k) 0 + posPartShift k (ζ x * z x) = w x := by
        rw [hZx]
        simp only [posPartShift, hwdef]
        ring
      rw [hval, hΦdef]
      module
    · obtain ⟨hη0x, hηg0⟩ := hηzero x hxη
      rw [hΦdef]
      simp [hη0x, hηg0]
  -- the weak inequality on this test function
  set ψ0 : Euc d → ℝ := fun x => η x ^ 2 * (max (-k) 0 + posPartShift k (ζ x * z x))
    with hψ0def
  have hψ0val : ∀ x, ψ0 x = η x ^ 2 * w x := fun x => hψval x
  have hsubTsupp : tsupport η ⊆ Metric.closedBall x₀ s :=
    hηsupp.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hsuppBall : tsupport η ⊆ Metric.ball x₀ s := by
    intro x hx
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.1 (hηsupp hx)) (by linarith)
  have hΦ0 : ∀ x, x ∉ tsupport η → Φ x = 0 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hηzero x hx
    rw [hΦdef]
    simp [h1, h2]
  have hψtest : IsDGTest Ω (Metric.closedBall x₀ s) ψ0 := by
    refine ⟨isCompact_closedBall x₀ s, hball, hψ, ?_⟩
    filter_upwards [hΦeq] with x hx hxB
    rw [hx]
    exact hΦ0 x fun h => hxB (hsubTsupp h)
  have hkey : (∫ x, ⟪A x (G x), Φ x⟫) ≤ ∫ x, (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x)) := by
    have hsubeq := hz.subeq _ _ hψtest hψnonneg
    have h1 : (∫ x, ⟪A x (G x), Φ x⟫) = ∫ x, ⟪A x (G x), weakGrad ψ0 x⟫ :=
      integral_congr_ae (hΦeq.mono fun x hx => by
        show ⟪A x (G x), Φ x⟫ = ⟪A x (G x), weakGrad ψ0 x⟫
        rw [hx])
    have h2 : (∫ x, (⟪f x, weakGrad ψ0 x⟫ + g x * ψ0 x)) =
        ∫ x, (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x)) :=
      integral_congr_ae (hΦeq.mono fun x hx => by
        show ⟪f x, weakGrad ψ0 x⟫ + g x * ψ0 x = ⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x)
        rw [hx, hψ0val x])
    rw [h1, ← h2]
    exact hsubeq
  -- elementary pointwise bounds
  set Q : ℝ := 3 * C / (s - r) with hQdef
  have hQ0 : (0 : ℝ) ≤ Q := by rw [hQdef]; exact div_nonneg (by positivity) hsr.le
  have hw0 : ∀ x, 0 ≤ w x := fun x => le_max_right _ _
  have hwzero : ∀ x, ¬ (k < z x) → w x = 0 := fun x hx => by
    rw [hwdef]; exact max_eq_right (by linarith [not_lt.1 hx])
  have hind1 : ∀ x, k < z x → ind x = 1 := fun x hx => by rw [hinddef]; simp [hx]
  have hind0 : ∀ x, ¬ (k < z x) → ind x = 0 := fun x hx => by rw [hinddef]; simp [hx]
  have hindnn : ∀ x, 0 ≤ ind x ∧ ind x ≤ 1 := by
    intro x
    by_cases hx : k < z x
    · rw [hind1 x hx]; norm_num
    · rw [hind0 x hx]; norm_num
  have hw2 : ∀ x, w x ^ 2 ≤ 2 * z x ^ 2 + 2 * k ^ 2 := by
    intro x
    have h1 : w x ≤ |z x| + |k| := by
      rw [hwdef]
      refine max_le ?_ (by positivity)
      have := le_abs_self (z x)
      have := neg_abs_le k
      linarith
    nlinarith [hw0 x, abs_nonneg (z x), abs_nonneg k, sq_abs (z x), sq_abs k,
      sq_nonneg (|z x| - |k|)]
  have hΦbd : ∀ x, ‖Φ x‖ ≤ ‖G x‖ + 2 * Q * w x := by
    intro x
    have hηx0 : 0 ≤ η x := hη0 x
    have hηx1 : η x ≤ 1 := hη1 x
    have hwx0 : 0 ≤ w x := hw0 x
    have hix := hindnn x
    rw [hΦdef]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      have hnn : (0 : ℝ) ≤ η x ^ 2 * ind x := mul_nonneg (sq_nonneg _) hix.1
      have h1 : |η x ^ 2 * ind x| ≤ 1 := by
        rw [abs_of_nonneg hnn]
        nlinarith [hix.1, hix.2, sq_nonneg (η x)]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    · rw [norm_smul, Real.norm_eq_abs]
      have hnn : (0 : ℝ) ≤ 2 * η x * w x := by positivity
      rw [abs_of_nonneg hnn]
      have h3 : 2 * η x * w x * ‖gradient η x‖ ≤ 2 * η x * w x * Q :=
        mul_le_mul_of_nonneg_left (hηg' x) hnn
      nlinarith [h3, hwx0, hQ0, hηx1,
        mul_nonneg (mul_nonneg hQ0 hwx0) (sub_nonneg.2 hηx1)]
  -- measurability
  have hindm : Measurable ind := by
    rw [hinddef]
    exact Measurable.ite (measurableSet_lt measurable_const hz.measurable)
      measurable_const measurable_const
  have hwm : Measurable w := by
    rw [hwdef]
    exact (hz.measurable.sub measurable_const).max measurable_const
  have hηcont : Continuous η := hηC.continuous
  have hgηcont : Continuous (gradient η) := continuous_gradient hη1C
  have hΦm : AEStronglyMeasurable Φ volume := by
    rw [hΦdef]
    exact ((((hηcont.pow 2).aestronglyMeasurable).mul hindm.aestronglyMeasurable).smul hGm).add
      (((continuous_const.mul hηcont).aestronglyMeasurable.mul
        hwm.aestronglyMeasurable).smul hgηcont.aestronglyMeasurable)
  -- the four integrands
  set Bconst : ℝ := M ^ 2 / lam + M ^ 2 + N ^ 2 * (s - r) ^ 2 / 2 with hBconstdef
  set K : ℝ := (4 * Lam ^ 2 / lam + 1) * Q ^ 2 + 1 / (2 * (s - r) ^ 2) with hKdef
  set Main : Euc d → ℝ := fun x => η x ^ 2 * ind x * ‖G x‖ ^ 2 with hMaindef
  set Bnd : Euc d → ℝ := fun x =>
      (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
        (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst) with hBnddef
  have hBconst0 : 0 ≤ Bconst := by rw [hBconstdef]; positivity
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have : (0 : ℝ) < 2 * (s - r) ^ 2 := by positivity
    have h1 : (0 : ℝ) ≤ 4 * Lam ^ 2 / lam := by positivity
    have h2 : (0 : ℝ) ≤ Q ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ 1 / (2 * (s - r) ^ 2) := by positivity
    nlinarith
  have hMain0 : ∀ x, 0 ≤ Main x := fun x => by
    rw [hMaindef]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hindnn x).1) (sq_nonneg _)
  have hBnd0 : ∀ x, 0 ≤ Bnd x := fun x => by
    rw [hBnddef]
    have h1 : (0 : ℝ) ≤ 4 * Lam ^ 2 / lam + 1 := by positivity
    have h2 : (0 : ℝ) ≤ w x ^ 2 / (2 * (s - r) ^ 2) := by positivity
    have h3 : (0 : ℝ) ≤ η x ^ 2 * ind x := mul_nonneg (sq_nonneg _) (hindnn x).1
    have := hBconst0
    nlinarith [sq_nonneg (w x), sq_nonneg ‖gradient η x‖, mul_nonneg (sq_nonneg (w x))
      (sq_nonneg ‖gradient η x‖)]
  -- vanishing outside the ball
  have hvanish : ∀ x, x ∉ Metric.closedBall x₀ s → x ∉ tsupport η := fun x hx h =>
    hx (hsubTsupp h)
  -- integrability
  have hMainInt : Integrable Main volume := by
    refine integrable_of_bound_on_ball hz2 hG2 ?_ 1 0 0 ?_ ?_
    · rw [hMaindef]
      exact ((hηcont.pow 2).aestronglyMeasurable.mul hindm.aestronglyMeasurable).mul
        (hGm.norm.pow 2)
    · refine Eventually.of_forall fun x _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hMain0 x), hMaindef]
      have h1 : η x ^ 2 * ind x ≤ 1 := by
        nlinarith [hη0 x, hη1 x, (hindnn x).1, (hindnn x).2, sq_nonneg (η x)]
      nlinarith [sq_nonneg ‖G x‖, mul_nonneg (sq_nonneg (η x)) (hindnn x).1]
    · intro x hx
      obtain ⟨h1, _⟩ := hηzero x (hvanish x hx)
      rw [hMaindef]
      simp [h1]
  have hLHInt : Integrable (fun x => ⟪A x (G x), Φ x⟫) volume := by
    refine integrable_of_bound_on_ball hz2 hG2 (hz.aesm_flux.inner hΦm)
      (Lam + Lam * Q) (2 * Lam * Q) (2 * Lam * Q * k ^ 2) ?_ ?_
    · filter_upwards [hz.coeff.bddCoeff] with x hbA hxB
      have hxΩ : x ∈ Ω := hball hxB
      have hAG : ‖A x (G x)‖ ≤ Lam * ‖G x‖ :=
        (A x).le_opNorm (G x) |>.trans (mul_le_mul_of_nonneg_right (hbA hxΩ) (norm_nonneg _))
      have h1 : |⟪A x (G x), Φ x⟫| ≤ ‖A x (G x)‖ * ‖Φ x‖ := abs_real_inner_le_norm _ _
      have h2 := hΦbd x
      have h3 := hw2 x
      have h4 : ‖A x (G x)‖ * ‖Φ x‖ ≤ Lam * ‖G x‖ * (‖G x‖ + 2 * Q * w x) := by
        refine mul_le_mul hAG h2 (norm_nonneg _) (by positivity)
      rw [Real.norm_eq_abs]
      have h5 : 2 * ‖G x‖ * w x ≤ ‖G x‖ ^ 2 + w x ^ 2 := by
        nlinarith [sq_nonneg (‖G x‖ - w x)]
      nlinarith [norm_nonneg (G x), hw0 x, hQ0, hLam, mul_nonneg hLam hQ0]
    · intro x hx
      rw [hΦ0 x (hvanish x hx), inner_zero_right]
  have hRHInt : Integrable (fun x => ⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x)) volume := by
    refine integrable_of_bound_on_ball hz2 hG2
      ((hz.aesm_f.inner hΦm).add (hz.aesm_g.mul
        ((hηcont.pow 2).aestronglyMeasurable.mul hwm.aestronglyMeasurable)))
      M (2 * M * Q + N) (M + (2 * M * Q + N) * k ^ 2 + M * Q + N) ?_ ?_
    · filter_upwards [hz.bound_f, hz.bound_g] with x hbf hbg hxB
      have hxΩ : x ∈ Ω := hball hxB
      have h1 : |⟪f x, Φ x⟫| ≤ ‖f x‖ * ‖Φ x‖ := abs_real_inner_le_norm _ _
      have h2 := hΦbd x
      have h3 := hw2 x
      have hηw : 0 ≤ η x ^ 2 * w x := mul_nonneg (sq_nonneg _) (hw0 x)
      have hη2 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
      have h4 : |g x * (η x ^ 2 * w x)| ≤ N * w x := by
        rw [abs_mul, abs_of_nonneg hηw]
        calc |g x| * (η x ^ 2 * w x) ≤ N * (η x ^ 2 * w x) :=
              mul_le_mul_of_nonneg_right (hbg hxΩ) hηw
          _ ≤ N * w x := by
                nlinarith [hw0 x, hN, hη2,
                  mul_nonneg (mul_nonneg hN (hw0 x)) (sub_nonneg.2 hη2)]
      have h5 : ‖f x‖ * ‖Φ x‖ ≤ M * (‖G x‖ + 2 * Q * w x) :=
        mul_le_mul (hbf hxΩ) h2 (norm_nonneg _) hM
      have h6 : 2 * ‖G x‖ ≤ ‖G x‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖G x‖ - 1)]
      have h7 : 2 * w x ≤ w x ^ 2 + 1 := by nlinarith [sq_nonneg (w x - 1)]
      rw [Real.norm_eq_abs]
      have h8 : |⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x)| ≤ |⟪f x, Φ x⟫| +
        |g x * (η x ^ 2 * w x)| := abs_add_le _ _
      nlinarith [norm_nonneg (G x), hw0 x, hQ0, hM, hN, mul_nonneg hM hQ0]
    · intro x hx
      obtain ⟨h1, _⟩ := hηzero x (hvanish x hx)
      rw [hΦ0 x (hvanish x hx), inner_zero_right, h1]
      simp
  have hBndInt : Integrable Bnd volume := by
    refine integrable_of_bound_on_ball hz2 hG2 ?_ 0 (2 * K) (2 * K * k ^ 2 + Bconst) ?_ ?_
    · rw [hBnddef]
      exact ((((hwm.pow_const 2).aestronglyMeasurable).mul
          (hgηcont.norm.pow 2).aestronglyMeasurable).const_mul _).add
        (((hηcont.pow 2).aestronglyMeasurable.mul hindm.aestronglyMeasurable).mul
          (((((hwm.pow_const 2).div_const (2 * (s - r) ^ 2)).aestronglyMeasurable)).add
            aestronglyMeasurable_const))
    · refine Eventually.of_forall fun x _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hBnd0 x), hBnddef]
      have hq := hηg' x
      have hq0 : 0 ≤ ‖gradient η x‖ := norm_nonneg _
      have hq2 : ‖gradient η x‖ ^ 2 ≤ Q ^ 2 := by nlinarith
      have h1 : (0 : ℝ) ≤ 4 * Lam ^ 2 / lam + 1 := by positivity
      have h2 : η x ^ 2 * ind x ≤ 1 := by
        nlinarith [hη0 x, hη1 x, (hindnn x).1, (hindnn x).2, sq_nonneg (η x)]
      have h3 : (0 : ℝ) ≤ η x ^ 2 * ind x := mul_nonneg (sq_nonneg _) (hindnn x).1
      have h4 : (0 : ℝ) ≤ w x ^ 2 / (2 * (s - r) ^ 2) := by positivity
      have h5 := hw2 x
      have hKval : K = (4 * Lam ^ 2 / lam + 1) * Q ^ 2 + 1 / (2 * (s - r) ^ 2) := hKdef
      show (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
          (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst) ≤
        0 * ‖G x‖ ^ 2 + 2 * K * z x ^ 2 + (2 * K * k ^ 2 + Bconst)
      calc (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
            (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst)
          ≤ (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * Q ^ 2) +
            1 * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst) := by gcongr
        _ = K * w x ^ 2 + Bconst := by rw [hKval]; ring
        _ ≤ K * (2 * z x ^ 2 + 2 * k ^ 2) + Bconst := by nlinarith [hK0, h5]
        _ = 0 * ‖G x‖ ^ 2 + 2 * K * z x ^ 2 + (2 * K * k ^ 2 + Bconst) := by ring
    · intro x hx
      obtain ⟨h1, h2⟩ := hηzero x (hvanish x hx)
      rw [hBnddef]
      simp [h1, h2]
  -- the pointwise Young inequality
  have hpt : ∀ᵐ x, lam / 2 * Main x ≤
      (⟪A x (G x), Φ x⟫ - (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x))) + Bnd x := by
    have hBc : Bconst = M ^ 2 / lam + M ^ 2 + N ^ 2 * (s - r) ^ 2 / 2 := hBconstdef
    filter_upwards [hz.coeff.elliptic, hz.coeff.bddCoeff, hz.bound_f, hz.bound_g]
      with x hell hbA hbf hbg
    have hΦx : Φ x = (η x ^ 2 * ind x) • G x + (2 * η x * w x) • gradient η x := by rw [hΦdef]
    by_cases hxη : x ∈ tsupport η
    · have hxΩ : x ∈ Ω := hball (hsubTsupp hxη)
      have e1 : ⟪A x (G x), Φ x⟫ = (η x ^ 2 * ind x) * ⟪A x (G x), G x⟫
          + (2 * η x * w x) * ⟪A x (G x), gradient η x⟫ := by
        rw [hΦx, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have e2 : ⟪f x, Φ x⟫ = (η x ^ 2 * ind x) * ⟪f x, G x⟫
          + (2 * η x * w x) * ⟪f x, gradient η x⟫ := by
        rw [hΦx, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      by_cases hkz : k < z x
      · have hi1 : ind x = 1 := hind1 x hkz
        have hAG : ‖A x (G x)‖ ≤ Lam * ‖G x‖ :=
          ((A x).le_opNorm (G x)).trans (mul_le_mul_of_nonneg_right (hbA hxΩ) (norm_nonneg _))
        have hAGG : lam * ‖G x‖ ^ 2 ≤ ⟪A x (G x), G x⟫ := hell hxΩ (G x)
        have hAGη : |⟪A x (G x), gradient η x⟫| ≤ Lam * ‖G x‖ * ‖gradient η x‖ :=
          (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right hAG (norm_nonneg _))
        have hfG : |⟪f x, G x⟫| ≤ M * ‖G x‖ :=
          (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hbf hxΩ) (norm_nonneg _))
        have hfη : |⟪f x, gradient η x⟫| ≤ M * ‖gradient η x‖ :=
          (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hbf hxΩ) (norm_nonneg _))
        have hgx : |g x| ≤ N := hbg hxΩ
        have hηw : 0 ≤ 2 * η x * w x := by
          have := hη0 x; have := hw0 x; positivity
        have hLHbd : η x ^ 2 * lam * ‖G x‖ ^ 2 -
            2 * η x * w x * Lam * ‖G x‖ * ‖gradient η x‖ ≤ ⟪A x (G x), Φ x⟫ := by
          rw [e1, hi1, mul_one]
          have t1 : η x ^ 2 * (lam * ‖G x‖ ^ 2) ≤ η x ^ 2 * ⟪A x (G x), G x⟫ :=
            mul_le_mul_of_nonneg_left hAGG (sq_nonneg _)
          have t2 : -(Lam * ‖G x‖ * ‖gradient η x‖) ≤ ⟪A x (G x), gradient η x⟫ := by
            have := (abs_le.1 hAGη).1
            linarith
          have t3 : (2 * η x * w x) * (-(Lam * ‖G x‖ * ‖gradient η x‖)) ≤
              (2 * η x * w x) * ⟪A x (G x), gradient η x⟫ :=
            mul_le_mul_of_nonneg_left t2 hηw
          nlinarith [t1, t3]
        have hRHbd : ⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x) ≤
            η x ^ 2 * M * ‖G x‖ + 2 * η x * w x * M * ‖gradient η x‖ +
              N * η x ^ 2 * w x := by
          rw [e2, hi1, mul_one]
          have t1 : η x ^ 2 * ⟪f x, G x⟫ ≤ η x ^ 2 * (M * ‖G x‖) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans hfG) (sq_nonneg _)
          have t2 : (2 * η x * w x) * ⟪f x, gradient η x⟫ ≤
              (2 * η x * w x) * (M * ‖gradient η x‖) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans hfη) hηw
          have hηw2 : 0 ≤ η x ^ 2 * w x := mul_nonneg (sq_nonneg _) (hw0 x)
          have t3 : g x * (η x ^ 2 * w x) ≤ N * (η x ^ 2 * w x) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hgx) hηw2
          nlinarith [t1, t2, t3]
        have hcp := caccioppoli_pointwise hlam hLam hM hN (hη0 x) (norm_nonneg (G x))
          (hw0 x) (norm_nonneg (gradient η x)) hsr hLHbd hRHbd
        show lam / 2 * (η x ^ 2 * ind x * ‖G x‖ ^ 2) ≤
          (⟪A x (G x), Φ x⟫ - (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x))) +
            ((4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
              (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst))
        rw [hi1, hBc]
        nlinarith [hcp]
      · have hi0 : ind x = 0 := hind0 x hkz
        have hwx : w x = 0 := hwzero x hkz
        have hΦ0x : Φ x = 0 := by rw [hΦx, hi0, hwx]; simp
        show lam / 2 * (η x ^ 2 * ind x * ‖G x‖ ^ 2) ≤
          (⟪A x (G x), Φ x⟫ - (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x))) +
            ((4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
              (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst))
        rw [hi0, hwx, hΦ0x]
        simp
    · obtain ⟨h1, h2⟩ := hηzero x hxη
      show lam / 2 * (η x ^ 2 * ind x * ‖G x‖ ^ 2) ≤
        (⟪A x (G x), Φ x⟫ - (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x))) +
          ((4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
            (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst))
      rw [hΦ0 x hxη, h1, h2]
      simp
  -- integrate
  have hdiffInt : Integrable (fun x => ⟪A x (G x), Φ x⟫ -
      (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x))) volume := hLHInt.sub hRHInt
  have hcombInt : Integrable (fun x => (⟪A x (G x), Φ x⟫ -
      (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x))) + Bnd x) volume := hdiffInt.add hBndInt
  have hstep : lam / 2 * (∫ x, Main x) ≤ ∫ x, Bnd x := by
    have h1 := integral_mono_ae (hMainInt.const_mul (lam / 2)) hcombInt hpt
    have h2 : (∫ x, ((⟪A x (G x), Φ x⟫ - (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x))) + Bnd x))
        = ((∫ x, ⟪A x (G x), Φ x⟫) - ∫ x, (⟪f x, Φ x⟫ + g x * (η x ^ 2 * w x)))
          + ∫ x, Bnd x := by
      rw [integral_add hdiffInt hBndInt, integral_sub hLHInt hRHInt]
    rw [integral_const_mul, h2] at h1
    linarith [hkey]
  -- lower bound for `∫ Main`
  have hSmeas : MeasurableSet (Metric.ball x₀ r ∩ {x | k < z x}) :=
    measurableSet_ball.inter (measurableSet_lt measurable_const hz.measurable)
  have hS2meas : MeasurableSet (Metric.ball x₀ s ∩ {x | k < z x}) :=
    measurableSet_ball.inter (measurableSet_lt measurable_const hz.measurable)
  have hSind : ∀ x, (Metric.ball x₀ r ∩ {x | k < z x}).indicator (fun y => ‖G y‖ ^ 2) x
      ≤ Main x := by
    intro x
    by_cases hx : x ∈ Metric.ball x₀ r ∩ {x | k < z x}
    · rw [Set.indicator_of_mem hx]
      have h1 : η x = 1 := hηone x (Metric.ball_subset_closedBall hx.1)
      have h2 : ind x = 1 := hind1 x hx.2
      show ‖G x‖ ^ 2 ≤ η x ^ 2 * ind x * ‖G x‖ ^ 2
      rw [h1, h2]
      simp
    · rw [Set.indicator_of_notMem hx]
      exact hMain0 x
  have hSInt : Integrable ((Metric.ball x₀ r ∩ {x | k < z x}).indicator
      (fun y => ‖G y‖ ^ 2)) volume := by
    refine Integrable.mono' hMainInt ((hGm.norm.pow 2).indicator hSmeas)
      (Eventually.of_forall fun x => ?_)
    have hnn : 0 ≤ (Metric.ball x₀ r ∩ {x | k < z x}).indicator (fun y => ‖G y‖ ^ 2) x :=
      Set.indicator_nonneg (fun y _ => sq_nonneg _) x
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hSind x
  have hlow : (∫ x in Metric.ball x₀ r ∩ {x | k < z x}, ‖G x‖ ^ 2) ≤ ∫ x, Main x := by
    rw [← integral_indicator hSmeas]
    exact integral_mono_ae hSInt hMainInt (Eventually.of_forall hSind)
  -- upper bound for `∫ Bnd`
  have hw2Int : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ s) volume := by
    have hbase : IntegrableOn (fun x => 2 * z x ^ 2 + 2 * k ^ 2) (Metric.ball x₀ s) volume :=
      ((hz2.mono_set Metric.ball_subset_closedBall).const_mul 2).add
        (integrableOn_const (C := 2 * k ^ 2) measure_ball_lt_top.ne)
    refine Integrable.mono' hbase ((hwm.pow_const 2).aestronglyMeasurable.restrict)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hw2 x
  have hI1 : Integrable ((Metric.ball x₀ s).indicator (fun y => K * w y ^ 2)) volume := by
    rw [integrable_indicator_iff measurableSet_ball]
    exact hw2Int.const_mul K
  have hI2 : Integrable ((Metric.ball x₀ s ∩ {x | k < z x}).indicator
      (fun _ : Euc d => Bconst)) volume := by
    rw [integrable_indicator_iff hS2meas]
    exact integrableOn_const (C := Bconst)
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top).ne
  have hBndUp : ∀ x, Bnd x ≤ (Metric.ball x₀ s).indicator (fun y => K * w y ^ 2) x
      + (Metric.ball x₀ s ∩ {x | k < z x}).indicator (fun _ => Bconst) x := by
    intro x
    have hq := hηg' x
    have hq0 : 0 ≤ ‖gradient η x‖ := norm_nonneg _
    have hq2 : ‖gradient η x‖ ^ 2 ≤ Q ^ 2 := by nlinarith
    have h1 : (0 : ℝ) ≤ 4 * Lam ^ 2 / lam + 1 := by positivity
    have hKval : K = (4 * Lam ^ 2 / lam + 1) * Q ^ 2 + 1 / (2 * (s - r) ^ 2) := hKdef
    have hi2 := hindnn x
    have hη2 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
    by_cases hxη : x ∈ tsupport η
    · have hxs : x ∈ Metric.ball x₀ s := hsuppBall hxη
      by_cases hkz : k < z x
      · have hi1 : ind x = 1 := hind1 x hkz
        have hmem : x ∈ Metric.ball x₀ s ∩ {x | k < z x} := ⟨hxs, hkz⟩
        rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hmem]
        show (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
            (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst) ≤
          K * w x ^ 2 + Bconst
        rw [hi1, mul_one, hKval]
        have hd : w x ^ 2 / (2 * (s - r) ^ 2) = 1 / (2 * (s - r) ^ 2) * w x ^ 2 := by ring
        rw [hd]
        have hb : (0 : ℝ) ≤ 1 / (2 * (s - r) ^ 2) * w x ^ 2 := by positivity
        have hA : (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2)
            ≤ (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * Q ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq2 (sq_nonneg (w x))) h1
        have hB : η x ^ 2 * (1 / (2 * (s - r) ^ 2) * w x ^ 2 + Bconst)
            ≤ 1 * (1 / (2 * (s - r) ^ 2) * w x ^ 2 + Bconst) :=
          mul_le_mul_of_nonneg_right hη2 (by linarith [hBconst0, hb])
        have hEq : (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * Q ^ 2)
            + 1 * (1 / (2 * (s - r) ^ 2) * w x ^ 2 + Bconst)
            = ((4 * Lam ^ 2 / lam + 1) * Q ^ 2 + 1 / (2 * (s - r) ^ 2)) * w x ^ 2
              + Bconst := by ring
        linarith [hA, hB, hEq]
      · have hi0 : ind x = 0 := hind0 x hkz
        have hwx : w x = 0 := hwzero x hkz
        have hrhs : 0 ≤ (Metric.ball x₀ s).indicator (fun y => K * w y ^ 2) x
            + (Metric.ball x₀ s ∩ {x | k < z x}).indicator (fun _ => Bconst) x :=
          add_nonneg (Set.indicator_nonneg (fun y _ => mul_nonneg hK0 (sq_nonneg _)) x)
            (Set.indicator_nonneg (fun _ _ => hBconst0) x)
        refine le_trans (le_of_eq ?_) hrhs
        show (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
            (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst) = 0
        rw [hi0, hwx]
        simp
    · obtain ⟨hz1, hz3⟩ := hηzero x hxη
      have hrhs : 0 ≤ (Metric.ball x₀ s).indicator (fun y => K * w y ^ 2) x
          + (Metric.ball x₀ s ∩ {x | k < z x}).indicator (fun _ => Bconst) x :=
        add_nonneg (Set.indicator_nonneg (fun y _ => mul_nonneg hK0 (sq_nonneg _)) x)
          (Set.indicator_nonneg (fun _ _ => hBconst0) x)
      refine le_trans (le_of_eq ?_) hrhs
      show (4 * Lam ^ 2 / lam + 1) * (w x ^ 2 * ‖gradient η x‖ ^ 2) +
          (η x ^ 2 * ind x) * (w x ^ 2 / (2 * (s - r) ^ 2) + Bconst) = 0
      rw [hz1, hz3]
      simp
  have hupp : (∫ x, Bnd x) ≤ K * (∫ x in Metric.ball x₀ s, w x ^ 2)
      + Bconst * (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal := by
    have hI12 : Integrable (fun x => (Metric.ball x₀ s).indicator (fun y => K * w y ^ 2) x
        + (Metric.ball x₀ s ∩ {x | k < z x}).indicator (fun _ => Bconst) x) volume :=
      hI1.add hI2
    have h1 := integral_mono_ae hBndInt hI12 (Eventually.of_forall hBndUp)
    have e1 : (∫ x, (Metric.ball x₀ s).indicator (fun y => K * w y ^ 2) x)
        = K * ∫ x in Metric.ball x₀ s, w x ^ 2 := by
      rw [integral_indicator measurableSet_ball, integral_const_mul]
    have e2 : (∫ x, (Metric.ball x₀ s ∩ {x | k < z x}).indicator (fun _ : Euc d => Bconst) x)
        = (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal * Bconst := by
      rw [integral_indicator hS2meas, setIntegral_const, smul_eq_mul]
      try rfl
    have h2 : (∫ x, ((Metric.ball x₀ s).indicator (fun y => K * w y ^ 2) x
        + (Metric.ball x₀ s ∩ {x | k < z x}).indicator (fun _ => Bconst) x))
        = K * (∫ x in Metric.ball x₀ s, w x ^ 2)
          + (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal * Bconst := by
      rw [integral_add hI1 hI2, e1, e2]
    rw [h2] at h1
    linarith [h1]
  -- conclusion
  have hIw0 : (0 : ℝ) ≤ ∫ x in Metric.ball x₀ s, w x ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hV0 : (0 : ℝ) ≤ (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal :=
    ENNReal.toReal_nonneg
  have h2lam : (0 : ℝ) < 2 / lam := by positivity
  have hMn : (∫ x, Main x) ≤ 2 / lam * (K * (∫ x in Metric.ball x₀ s, w x ^ 2)
      + Bconst * (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal) := by
    have hcomb := hstep.trans hupp
    have hid : (∫ x, Main x) = 2 / lam * (lam / 2 * (∫ x, Main x)) := by field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_left hcomb h2lam.le
  -- the two constant comparisons
  have hγ1 : 2 / lam * ((4 * Lam ^ 2 / lam + 1) * (3 * C) ^ 2 + 1 / 2) ≤ γ := by
    rw [hγdef]; exact le_max_left _ _
  have hγ2 : 2 / lam * (1 / lam + 1) ≤ γ := by rw [hγdef]; exact le_max_right _ _
  have hKeq : 2 / lam * K =
      (2 / lam * ((4 * Lam ^ 2 / lam + 1) * (3 * C) ^ 2 + 1 / 2)) / (s - r) ^ 2 := by
    rw [hKdef, hQdef, div_pow]
    field_simp
    try ring
  have hsq : M ^ 2 + N ^ 2 * (s - r) ^ 2 ≤ (M + N * R₀) ^ 2 := by
    have h1 : (s - r) ^ 2 ≤ R₀ ^ 2 := by nlinarith [hsr, hsR, hr, hR₀]
    nlinarith [mul_nonneg (mul_nonneg hM hN) hR₀, sq_nonneg N, hN, sq_nonneg (s - r)]
  have hBcUp : 2 / lam * Bconst ≤ γ * (M + N * R₀) ^ 2 := by
    have hinv : (0 : ℝ) < 1 / lam := by positivity
    have hid : 2 / lam * (1 / lam + 1) * (M ^ 2 + N ^ 2 * (s - r) ^ 2)
        - 2 / lam * (M ^ 2 / lam + M ^ 2 + N ^ 2 * (s - r) ^ 2 / 2)
        = 2 / lam * ((1 / lam + 1 / 2) * (N ^ 2 * (s - r) ^ 2)) := by field_simp; ring
    have h0 : (0 : ℝ) ≤ 2 / lam * ((1 / lam + 1 / 2) * (N ^ 2 * (s - r) ^ 2)) := by positivity
    have hstep1 : 2 / lam * Bconst ≤ 2 / lam * (1 / lam + 1) * (M ^ 2 + N ^ 2 * (s - r) ^ 2) := by
      rw [hBconstdef]
      linarith [hid, h0]
    have h3 : (0 : ℝ) ≤ M ^ 2 + N ^ 2 * (s - r) ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ 2 / lam * (1 / lam + 1) := by positivity
    nlinarith [hstep1, hγ2, hsq, h3, h4]
  refine hlow.trans (hMn.trans ?_)
  have hd : (0 : ℝ) < (s - r) ^ 2 := by positivity
  have hKle : 2 / lam * K ≤ γ / (s - r) ^ 2 := by
    rw [hKeq]
    exact div_le_div_of_nonneg_right hγ1 hd.le
  have hexp : 2 / lam * (K * (∫ x in Metric.ball x₀ s, w x ^ 2)
      + Bconst * (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal)
      = (2 / lam * K) * (∫ x in Metric.ball x₀ s, w x ^ 2)
        + (2 / lam * Bconst) * (volume (Metric.ball x₀ s ∩ {x | k < z x})).toReal := by ring
  rw [hexp]
  exact add_le_add (mul_le_mul_of_nonneg_right hKle hIw0)
    (mul_le_mul_of_nonneg_right hBcUp hV0)

/-- A solution is a sub-solution. -/
theorem IsLinearSol.isLinearSubsol {lam Lam M N : ℝ} {A : Euc d → (Euc d →L[ℝ] Euc d)}
    {f : Euc d → Euc d} {g : Euc d → ℝ} {Ω : Set (Euc d)} {z : Euc d → ℝ} {G : Euc d → Euc d}
    (hz : IsLinearSol lam Lam M N A f g Ω z G) : IsLinearSubsol lam Lam M N A f g Ω z G where
  coeff := hz.coeff
  hasWeakGradient := hz.hasWeakGradient
  measurable := hz.measurable
  measurable_grad := hz.measurable_grad
  aesm_flux := hz.aesm_flux
  aesm_f := hz.aesm_f
  aesm_g := hz.aesm_g
  integrableOn := hz.integrableOn
  bound_f := hz.bound_f
  bound_g := hz.bound_g
  subeq T ψ hψ _ := le_of_eq (hz.weakEq T ψ hψ)

/-- `-z` solves the same equation with data `-f`, `-g`. -/
theorem IsLinearSol.neg {lam Lam M N : ℝ} {A : Euc d → (Euc d →L[ℝ] Euc d)}
    {f : Euc d → Euc d} {g : Euc d → ℝ} {Ω : Set (Euc d)} {z : Euc d → ℝ} {G : Euc d → Euc d}
    (hz : IsLinearSol lam Lam M N A f g Ω z G) :
    IsLinearSol lam Lam M N A (fun x => -f x) (fun x => -g x) Ω (fun x => -z x)
      (fun x => -G x) where
  coeff := hz.coeff
  hasWeakGradient := by
    have h := hz.hasWeakGradient.smul (-1)
    refine h.congr_left (Eventually.of_forall fun x => ?_) |>.congr_right
      (Eventually.of_forall fun x => ?_) <;> simp [Pi.smul_apply]
  measurable := hz.measurable.neg
  measurable_grad := hz.measurable_grad.neg
  aesm_flux := by
    refine (hz.aesm_flux.neg).congr (Eventually.of_forall fun x => ?_)
    simp
  aesm_f := hz.aesm_f.neg
  aesm_g := hz.aesm_g.neg
  integrableOn x₀ s hs := by
    obtain ⟨h1, h2⟩ := hz.integrableOn x₀ s hs
    exact ⟨h1.congr_fun (fun x _ => by ring) measurableSet_closedBall,
      h2.congr_fun (fun x _ => by rw [norm_neg]) measurableSet_closedBall⟩
  bound_f := hz.bound_f.mono fun x hx hxΩ => by rw [norm_neg]; exact hx hxΩ
  bound_g := hz.bound_g.mono fun x hx hxΩ => by rw [abs_neg]; exact hx hxΩ
  weakEq T ψ hψ := by
    have h := hz.weakEq T ψ hψ
    have e1 : ∀ x, ⟪A x (-G x), weakGrad ψ x⟫ = -⟪A x (G x), weakGrad ψ x⟫ := by
      intro x; rw [map_neg, inner_neg_left]
    have e2 : ∀ x, (⟪-f x, weakGrad ψ x⟫ + (-g x) * ψ x) =
        -(⟪f x, weakGrad ψ x⟫ + g x * ψ x) := by
      intro x; rw [inner_neg_left]; ring
    simp only [e1, e2, integral_neg, h]

/-- **Solutions lie in the De Giorgi class `DG`**: apply `exists_dgSub_const` to `z` and to
`-z` (which solves the same equation with data `-f`, `-g`). -/
theorem exists_dg_const {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 ≤ Lam) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (M N R₀ : ℝ) (A : Euc d → (Euc d →L[ℝ] Euc d)) (f : Euc d → Euc d)
      (g : Euc d → ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
      0 ≤ M → 0 ≤ N → 0 ≤ R₀ → IsLinearSol lam Lam M N A f g Ω z G →
      IsDG γ (M + N * R₀) R₀ Ω z G := by
  obtain ⟨γ, hγ, hsub⟩ := exists_dgSub_const (d := d) hlam hLam
  refine ⟨γ, hγ, fun M N R₀ A f g Ω z G hM hN hR₀ hz => ⟨?_, ?_⟩⟩
  · exact hsub M N R₀ A f g Ω z G hM hN hR₀ hz.isLinearSubsol
  · exact hsub M N R₀ A (fun x => -f x) (fun x => -g x) Ω (fun x => -z x) (fun x => -G x)
      hM hN hR₀ hz.neg.isLinearSubsol

/-! ### (2) Local boundedness -/

/-- **Interior local boundedness for sub-solutions** (De Giorgi): with `C = C(d, λ, Λ)`,

`ess sup_{B_{R/2}} (z - k)_+ ≤ C ((⨍_{B_R} (z - k)_+²)^{1/2} + M R + N R²)`

for every level `k` and every ball `closedBall x₀ R ⊆ Ω`.  Taking `k = 0` gives the form of
the lane brief.  Proof: `exists_dgSub_const` at the scale `R₀ = R` (so that the De Giorgi
parameter `χ R = (M + N R) R = M R + N R²`) and `exists_dg_sup_bound`. -/
theorem exists_essSup_bound {lam Lam : ℝ} (hd : 0 < d) (hlam : 0 < lam) (hLam : 0 ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N : ℝ) (A : Euc d → (Euc d →L[ℝ] Euc d)) (f : Euc d → Euc d)
      (g : Euc d → ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
      0 ≤ M → 0 ≤ N → IsLinearSubsol lam Lam M N A f g Ω z G →
      ∀ (x₀ : Euc d) (R : ℝ), 0 < R → Metric.closedBall x₀ R ⊆ Ω → ∀ k : ℝ,
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))),
        z x ≤ k + C * (Real.sqrt (⨍ y in Metric.ball x₀ R, max (z y - k) 0 ^ 2) +
          (M * R + N * R ^ 2)) := by
  obtain ⟨γ, hγ, hsub⟩ := exists_dgSub_const (d := d) hlam hLam
  obtain ⟨C, hC, hbound⟩ := exists_dg_sup_bound (d := d) hd hγ.le
  refine ⟨C, hC, fun M N A f g Ω z G hM hN hz x₀ R hR hball k => ?_⟩
  have hdg : IsDGSub γ (M + N * R) R Ω z G :=
    hsub M N R A f g Ω z G hM hN hR.le hz
  have h := hbound (M + N * R) R Ω z G (by positivity) hdg x₀ R hR le_rfl hball k
  refine h.mono fun x hx => ?_
  refine hx.trans (by nlinarith [Real.sqrt_nonneg (⨍ y in Metric.ball x₀ R,
    max (z y - k) 0 ^ 2), hC.le])

/-! ### (3) The interior Hölder estimate -/

/-- **Interior oscillation decay for solutions** (De Giorgi–Nash): with `α ∈ (0,1)` and
`C₀ = C₀(d, λ, Λ)`,
`osc_{B_r} z ≤ C₀ (r/R)^α (osc_{B_{3R}} z + M R + N R²)` for `0 < r ≤ R`. -/
theorem exists_osc_decay {lam Lam : ℝ} (hd : 0 < d) (hlam : 0 < lam) (hLam : 0 ≤ Lam) :
    ∃ α : ℝ, 0 < α ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (M N : ℝ) (A : Euc d → (Euc d →L[ℝ] Euc d))
      (f : Euc d → Euc d) (g : Euc d → ℝ) (Ω : Set (Euc d)) (z : Euc d → ℝ) (G : Euc d → Euc d),
      0 ≤ M → 0 ≤ N → IsLinearSol lam Lam M N A f g Ω z G →
      ∀ (x₀ : Euc d) (R : ℝ), 0 < R → Metric.closedBall x₀ (3 * R) ⊆ Ω →
      ∀ m om : ℝ, 0 ≤ om →
      (∀ᵐ x, x ∈ Metric.closedBall x₀ (3 * R) → z x ∈ Icc m (m + om)) →
      ∀ r : ℝ, 0 < r → r ≤ R →
      ∃ m' : ℝ, ∀ᵐ x, x ∈ Metric.ball x₀ r →
        z x ∈ Icc m' (m' + C₀ * (r / R) ^ α * (om + (M * R + N * (3 * R) * R))) := by
  obtain ⟨γ, hγ, hdgc⟩ := exists_dg_const (d := d) hlam hLam
  obtain ⟨α, hα, C₀, hC₀, hosc⟩ := exists_dg_holder_osc (d := d) hd hγ.le
  refine ⟨α, hα, C₀, hC₀, fun M N A f g Ω z G hM hN hz x₀ R hR hball m om hom hz3 r hr hrR => ?_⟩
  have h3R : (0 : ℝ) ≤ 3 * R := by linarith
  have hdg : IsDG γ (M + N * (3 * R)) (3 * R) Ω z G :=
    hdgc M N (3 * R) A f g Ω z G hM hN h3R hz
  obtain ⟨m', hm'⟩ := hosc (M + N * (3 * R)) (3 * R) Ω z G (by positivity) hdg x₀ R hR le_rfl
    hball m om hom hz3 r hr hrR
  exact ⟨m', hm'.mono fun x hx hxr => by
    have := hx hxr
    have he : (M + N * (3 * R)) * R = M * R + N * (3 * R) * R := by ring
    rwa [he] at this⟩

/-- **A locally Hölder continuous representative** (De Giorgi–Nash): a bounded weak solution on
an open `Ω` has a representative that is continuous on `Ω` and Hölder continuous on every
compact subset of `Ω`. -/
theorem IsLinearSol.exists_holder_representative {lam Lam M N : ℝ}
    {A : Euc d → (Euc d →L[ℝ] Euc d)} {f : Euc d → Euc d} {g : Euc d → ℝ} {Ω : Set (Euc d)}
    {z : Euc d → ℝ} {G : Euc d → Euc d} (hd : 0 < d) (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hΩ : IsOpen Ω) (hR₀ : (0 : ℝ) < 1)
    (hz : IsLinearSol lam Lam M N A f g Ω z G) {S : ℝ} (hS : ∀ x, |z x| ≤ S) :
    ∃ φ : Euc d → ℝ, φ =ᵐ[volume.restrict Ω] z ∧ ContinuousOn φ Ω ∧
      ∀ T : Set (Euc d), IsCompact T → T ⊆ Ω → ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r φ T := by
  obtain ⟨γ, hγ, hdgc⟩ := exists_dg_const (d := d) hlam hLam
  have hdg : IsDG γ (M + N * 1) 1 Ω z G := hdgc M N 1 A f g Ω z G hM hN zero_le_one hz
  exact IsDG.exists_holder_representative hd hγ.le (by positivity) hR₀ hΩ hdg hS

end Komlos.Literature.Regularized
