import Komlos.Literature.PLaplacian.HarmonicMVP

/-!
# Weakly harmonic functions on `ℝ^d` and the constant-coefficient energy decay

Mathlib's harmonic-function theory is two-dimensional: `InnerProductSpace.HarmonicOnNhd` is
defined on any real inner product space, but the only mean value property available
(`HarmonicOnNhd.circleAverage_eq`) goes through complex analysis and lives on `ℂ`.  The
Campanato/Schauder method (Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Theorem 8.32) needs instead the `ℝ^d` theory of the **constant-coefficient** equation
`div (A₀ ∇h) = 0` with `A₀` symmetric positive definite: interior derivative estimates and the
resulting Morrey decay of the gradient energy oscillation.  This file builds that theory and uses
it for the perturbed (freezing) decay behind the interior Schauder estimate.

## Main definitions

* `IsWeakConstSolutionOn A₀ U w`: `w` solves `div (A₀ ∇w) = 0` weakly on `U`, i.e.
  `∫ ⟪A₀ ∇w, ∇ψ⟫ = 0` for every `ψ ∈ C_c^∞(U)`.  This mirrors the encoding of the weak equation
  used by `IsWeakEigensolution` and by `schauder_perturbed_energy_decay`.
* `IsWeaklyHarmonicOn U w`: the case `A₀ = 1`, i.e. `∫ ⟪∇w, ∇ψ⟫ = 0` for `ψ ∈ C_c^∞(U)`.
* `sqExcess G x r = ∫_{B(x,r)} ‖G - (G)_{B(x,r)}‖²`, the `L²` Campanato excess of a vector
  field `G`; the gradient energy oscillation of Gilbarg–Trudinger Theorem 8.32 is
  `sqExcess (gradient w) x r`.

## Main results

* `integral_inner_const_gradient_eq_zero`: constant vector fields are weakly divergence free,
  `∫ ⟪c, ∇ψ⟫ = 0`; hence `isWeakConstSolutionOn_affine`, affine functions solve every
  constant-coefficient equation.
* `gradient_comp_selfAdjoint`, `isWeaklyHarmonicOn_comp_of_isWeakConstSolutionOn`: the **linear
  change of variables** `y = L x` with `L` self-adjoint and `L ∘ L = A₀` turns a weak solution of
  `div (A₀ ∇·) = 0` into a weakly harmonic function.  This is the reduction of the
  constant-coefficient theory to the Laplacian.
* `sqExcess_le_of_lipschitz`, `sqExcess_decay_of_lipschitz`: an interior Lipschitz estimate for
  the gradient upgrades to the Morrey decay `Φ(ρ) ≲ (ρ/r)^{d+2} Φ(r)`.
* `exists_constCoeff_sqExcess_decay` — the constant-coefficient Morrey decay — is **proved**
  here from `exists_constCoeff_gradient_lipschitz`, the `ℝ^d` interior derivative estimate, which
  is itself proved in `Komlos.Literature.PLaplacian.HarmonicMVP` (the `ℝ^d` mean value property
  for `div (A₀ ∇·) = 0`, built there without any divergence theorem).
The data-dependent freezing estimate is proved in `SchauderFreezing`, and the uniform
comparison is assembled in `SchauderHarmonic` after the independent interpolation bootstrap.
Keeping this constant-coefficient theory separate prevents circular imports through the
uniform gradient estimate.

-/

open MeasureTheory Set Filter Topology InnerProductSpace

open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature

variable {d : ℕ}

/-! ### Weak solutions of a constant-coefficient equation -/

/-- `w` is a **weak solution of `div (A₀ ∇w) = 0` on `U`**: `∫ ⟪A₀ ∇w, ∇ψ⟫ = 0` for every smooth
compactly supported `ψ` with `tsupport ψ ⊆ U`.  The encoding mirrors the weak equation of
`IsWeakEigensolution` and of `schauder_perturbed_energy_decay` (Gilbarg–Trudinger, (8.2)). -/
def IsWeakConstSolutionOn (A₀ : Euc d →L[ℝ] Euc d) (U : Set (Euc d)) (w : Euc d → ℝ) : Prop :=
  ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ x, ⟪A₀ (gradient w x), gradient ψ x⟫ = 0

/-- `w` is **weakly harmonic on `U`**: `∫ ⟪∇w, ∇ψ⟫ = 0` for every `ψ ∈ C_c^∞(U)`.  This is the
`ℝ^d` notion behind `InnerProductSpace.HarmonicOnNhd` before any regularity is known; the
equivalence with `Δ w = 0` for `C²` functions is Weyl's lemma. -/
def IsWeaklyHarmonicOn (U : Set (Euc d)) (w : Euc d → ℝ) : Prop :=
  ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ x, ⟪gradient w x, gradient ψ x⟫ = 0

/-- Weak harmonicity is the constant-coefficient equation with `A₀ = 1`. -/
theorem isWeaklyHarmonicOn_iff_id {U : Set (Euc d)} {w : Euc d → ℝ} :
    IsWeaklyHarmonicOn U w ↔ IsWeakConstSolutionOn (ContinuousLinearMap.id ℝ (Euc d)) U w :=
  Iff.rfl

/-- A weak solution on `U` is a weak solution on every subset of `U`. -/
theorem IsWeakConstSolutionOn.mono {A₀ : Euc d →L[ℝ] Euc d} {U V : Set (Euc d)} {w : Euc d → ℝ}
    (hw : IsWeakConstSolutionOn A₀ U w) (hVU : V ⊆ U) : IsWeakConstSolutionOn A₀ V w :=
  fun ψ hψ hψs hψV => hw ψ hψ hψs (hψV.trans hVU)

/-! ### Elementary calculus on `Euc d` -/

/-- Two vectors with the same inner products against everything are equal. -/
theorem eq_of_forall_inner_eq {u v : Euc d} (h : ∀ z : Euc d, ⟪u, z⟫ = ⟪v, z⟫) : u = v := by
  have h0 : ⟪u - v, u - v⟫ = (0 : ℝ) := by
    rw [inner_sub_left, h (u - v), sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

/-- The gradient of a `C¹` function is continuous on any open set where the function is `C¹`. -/
theorem continuousOn_gradient {U : Set (Euc d)} (hU : IsOpen U) {w : Euc d → ℝ}
    (hw : ContDiffOn ℝ 1 w U) : ContinuousOn (gradient w) U :=
  (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
    (hw.continuousOn_fderiv_of_isOpen hU le_rfl)

/-- The gradient of `y ↦ ⟪c, y⟫ + b` is the constant field `c`. -/
theorem gradient_inner_const_add (c : Euc d) (b : ℝ) (x : Euc d) :
    gradient (fun y : Euc d => ⟪c, y⟫ + b) x = c := by
  have h1 : HasFDerivAt (fun y : Euc d => ⟪c, y⟫) (innerSL ℝ c) x := by
    simpa using (innerSL ℝ c).hasFDerivAt
  have hd : HasFDerivAt (fun y : Euc d => ⟪c, y⟫ + b) (innerSL ℝ c) x := by
    simpa using h1.add_const b
  refine eq_of_forall_inner_eq fun z => ?_
  have := fderiv_apply_eq_inner_gradient (fun y : Euc d => ⟪c, y⟫ + b) x z
  rw [hd.fderiv] at this
  simpa using this.symm

/-- **Constant vector fields are weakly divergence free**: `∫ ⟪c, ∇ψ⟫ = 0` for every `C¹`
compactly supported `ψ`.  (Integration by parts against the constant function `1`.) -/
theorem integral_inner_const_gradient_eq_zero (c : Euc d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψs : HasCompactSupport ψ) : ∫ x, ⟪c, gradient ψ x⟫ = (0 : ℝ) := by
  have h := integral_mul_fderiv_eq_neg_of_contDiffOn (U := (Set.univ : Set (Euc d))) isOpen_univ
    (φ := fun _ : Euc d => (1 : ℝ)) contDiff_const.contDiffOn hψ hψs (subset_univ _) c
  have e : (fun x : Euc d => ⟪c, gradient ψ x⟫) = fun x : Euc d => (1 : ℝ) * fderiv ℝ ψ x c := by
    funext x
    rw [one_mul]
    exact (real_inner_comm (gradient ψ x) c).trans
      (fderiv_apply_eq_inner_gradient ψ x c).symm
  have e' : (fun x : Euc d => fderiv ℝ (fun _ : Euc d => (1 : ℝ)) x c * ψ x) =
      fun _ : Euc d => (0 : ℝ) := by
    funext x
    simp
  rw [e, h, e', integral_zero, neg_zero]

/-- **Affine functions solve every constant-coefficient equation.** -/
theorem isWeakConstSolutionOn_affine (A₀ : Euc d →L[ℝ] Euc d) (U : Set (Euc d)) (c : Euc d)
    (b : ℝ) : IsWeakConstSolutionOn A₀ U (fun y => ⟪c, y⟫ + b) := by
  intro ψ hψ hψs _
  have e : (fun x : Euc d => ⟪A₀ (gradient (fun y : Euc d => ⟪c, y⟫ + b) x), gradient ψ x⟫) =
      fun x : Euc d => ⟪A₀ c, gradient ψ x⟫ := by
    funext x
    rw [gradient_inner_const_add]
  rw [e]
  exact integral_inner_const_gradient_eq_zero (A₀ c) (hψ.of_le (by simp)) hψs

/-! ### The linear change of variables `y = A₀^{1/2} x`

A constant symmetric positive definite `A₀` factors as `A₀ = L ∘ L` with `L = A₀^{1/2}`
self-adjoint and invertible.  Substituting `y = L x` turns `div (A₀ ∇·) = 0` into the Laplace
equation: this is the classical reduction of the constant-coefficient theory to harmonic
functions (Gilbarg–Trudinger, Theorem 8.32, step 1).  -/

/-- The gradient is measurable for every function (the Fréchet derivative is). -/
theorem measurable_gradient (w : Euc d → ℝ) : Measurable (gradient w) :=
  (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ w)

/-- **Chain rule for the gradient under a self-adjoint linear change of variables**:
`∇(w ∘ L) y = L (∇w (L y))` when `L` is self-adjoint. -/
theorem gradient_comp_selfAdjoint {L : Euc d ≃L[ℝ] Euc d}
    (hL : ∀ u v : Euc d, ⟪L u, v⟫ = ⟪u, L v⟫) {w : Euc d → ℝ} {y : Euc d}
    (hw : DifferentiableAt ℝ w (L y)) :
    gradient (fun z : Euc d => w (L z)) y = L (gradient w (L y)) := by
  have hcomp : HasFDerivAt (fun z : Euc d => w (L z))
      ((fderiv ℝ w (L y)).comp (L : Euc d →L[ℝ] Euc d)) y :=
    hw.hasFDerivAt.comp y L.hasFDerivAt
  refine eq_of_forall_inner_eq fun z => ?_
  have h1 := fderiv_apply_eq_inner_gradient (fun z : Euc d => w (L z)) y z
  rw [hcomp.fderiv] at h1
  have h2 : ((fderiv ℝ w (L y)).comp (L : Euc d →L[ℝ] Euc d)) z =
      ⟪L (gradient w (L y)), z⟫ := by
    show fderiv ℝ w (L y) (L z) = _
    rw [fderiv_apply_eq_inner_gradient, hL]
  rw [h2] at h1
  exact h1.symm

/-- **Linear change of variables in a Lebesgue integral on `ℝ^d`.** -/
theorem integral_comp_continuousLinearEquiv (L : Euc d ≃L[ℝ] Euc d) {f : Euc d → ℝ}
    (hf : StronglyMeasurable f) :
    ∫ y, f (L y) = |LinearMap.det (L.symm : Euc d →ₗ[ℝ] Euc d)| * ∫ x, f x := by
  have hmap : Measure.map (L : Euc d → Euc d) (volume : Measure (Euc d)) =
      ENNReal.ofReal |LinearMap.det (L.symm : Euc d →ₗ[ℝ] Euc d)| • volume := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply L.continuous.measurable hs, Measure.smul_apply, smul_eq_mul,
      Measure.addHaar_preimage_continuousLinearEquiv]
  have h1 : ∫ x, f x ∂(Measure.map (L : Euc d → Euc d) volume) = ∫ y, f (L y) :=
    integral_map L.continuous.measurable.aemeasurable hf.aestronglyMeasurable
  rw [← h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

/-- A vanishing integral stays vanishing under a linear change of variables. -/
theorem integral_comp_eq_zero (L : Euc d ≃L[ℝ] Euc d) {f : Euc d → ℝ} (hf : StronglyMeasurable f)
    (h : ∫ x, f x = (0 : ℝ)) : ∫ y, f (L y) = (0 : ℝ) := by
  rw [integral_comp_continuousLinearEquiv L hf, h, mul_zero]

/-- **Reduction of the constant-coefficient equation to the Laplace equation.**  If `L` is a
self-adjoint linear isomorphism with `L ∘ L = A₀` (i.e. `L = A₀^{1/2}`) and `w` solves
`div (A₀ ∇w) = 0` weakly on `U`, then `w ∘ L` is weakly harmonic on `L⁻¹(U)`. -/
theorem isWeaklyHarmonicOn_comp_of_isWeakConstSolutionOn {A₀ : Euc d →L[ℝ] Euc d}
    {L : Euc d ≃L[ℝ] Euc d} (hL : ∀ u v : Euc d, ⟪L u, v⟫ = ⟪u, L v⟫)
    (hLL : ∀ v : Euc d, L (L v) = A₀ v) {U : Set (Euc d)} (hU : IsOpen U) {w : Euc d → ℝ}
    (hwd : ContDiffOn ℝ 1 w U) (hw : IsWeakConstSolutionOn A₀ U w) :
    IsWeaklyHarmonicOn ((L : Euc d → Euc d) ⁻¹' U) (fun z => w (L z)) := by
  intro ψ hψ hψs hψV
  obtain ⟨φ, hφdef⟩ : ∃ φ : Euc d → ℝ, φ = fun x => ψ (L.symm x) := ⟨_, rfl⟩
  have hφapp : ∀ x : Euc d, φ x = ψ (L.symm x) := fun x => by simp only [hφdef]
  have hφ : ContDiff ℝ ∞ φ := by
    rw [hφdef]
    exact hψ.comp (L.symm : Euc d →L[ℝ] Euc d).contDiff
  have hcpt : IsCompact (tsupport ψ) := hψs
  have hsupp : Function.support φ ⊆ (L : Euc d → Euc d) '' tsupport ψ := by
    intro x hx
    have hx' : ψ (L.symm x) ≠ 0 := by
      rw [← hφapp x]
      exact hx
    exact ⟨L.symm x, subset_tsupport ψ hx', by simp⟩
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro (hcpt.image L.continuous) fun x hx => by
      by_contra hne
      exact hx (hsupp hne)
  have hφsupp : tsupport φ ⊆ U := by
    have himg : (L : Euc d → Euc d) '' tsupport ψ ⊆ U := by
      rintro _ ⟨y, hy, rfl⟩
      exact hψV hy
    refine le_trans ?_ himg
    show closure (Function.support φ) ⊆ (L : Euc d → Euc d) '' tsupport ψ
    exact closure_minimal hsupp (hcpt.image L.continuous).isClosed
  have hψeq : ψ = fun y : Euc d => φ (L y) := by
    funext y
    rw [hφapp, ContinuousLinearEquiv.symm_apply_apply]
  -- the two integrands agree pointwise
  have hpt : ∀ y : Euc d, ⟪gradient (fun z : Euc d => w (L z)) y, gradient ψ y⟫ =
      ⟪A₀ (gradient w (L y)), gradient φ (L y)⟫ := by
    intro y
    by_cases hy : L y ∈ U
    · have hwd' : DifferentiableAt ℝ w (L y) :=
        (hwd.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hy)
      have e1 : gradient (fun z : Euc d => w (L z)) y = L (gradient w (L y)) :=
        gradient_comp_selfAdjoint hL hwd'
      have e2 : gradient ψ y = L (gradient φ (L y)) := by
        rw [hψeq]
        exact gradient_comp_selfAdjoint hL
          ((hφ.of_le (by simp)).differentiable one_ne_zero).differentiableAt
      rw [e1, e2, ← hL, hLL]
    · have hyψ : y ∉ tsupport ψ := fun hmem => hy (hψV hmem)
      have hyφ : L y ∉ tsupport φ := fun hmem => hy (hφsupp hmem)
      rw [gradient_eq_zero_of_notMem_tsupport hyψ,
        gradient_eq_zero_of_notMem_tsupport hyφ, inner_zero_right, inner_zero_right]
  have hmeas : StronglyMeasurable fun x : Euc d => ⟪A₀ (gradient w x), gradient φ x⟫ :=
    ((A₀.continuous.measurable.comp (measurable_gradient w)).inner
      (measurable_gradient φ)).stronglyMeasurable
  have hzero : ∫ x, ⟪A₀ (gradient w x), gradient φ x⟫ = (0 : ℝ) := hw φ hφ hφs hφsupp
  calc ∫ y, ⟪gradient (fun z : Euc d => w (L z)) y, gradient ψ y⟫
      = ∫ y, ⟪A₀ (gradient w (L y)), gradient φ (L y)⟫ :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = 0 := integral_comp_eq_zero L hmeas hzero

/-! ### The `L²` Campanato excess of a vector field -/

/-- `sqExcess G x r = ∫_{B(x,r)} ‖G - (G)_{B(x,r)}‖²`.  With `G = ∇w` this is the gradient energy
oscillation `Φ(x, r)` of the Campanato method (Gilbarg–Trudinger, Theorem 8.32). -/
noncomputable def sqExcess (G : Euc d → Euc d) (x : Euc d) (r : ℝ) : ℝ :=
  ∫ y in Metric.closedBall x r, ‖G y - ⨍ z in Metric.closedBall x r, G z‖ ^ 2

theorem sqExcess_eq (G : Euc d → Euc d) (x : Euc d) (r : ℝ) :
    sqExcess G x r =
      ∫ y in Metric.closedBall x r, ‖G y - ⨍ z in Metric.closedBall x r, G z‖ ^ 2 := rfl

theorem sqExcess_nonneg (G : Euc d → Euc d) (x : Euc d) (r : ℝ) : 0 ≤ sqExcess G x r :=
  integral_nonneg fun _ => sq_nonneg _

/-- The average minimizes the quadratic deviation. -/
theorem sqExcess_le_const {G : Euc d → Euc d} {x : Euc d} {r : ℝ} (hr : 0 < r)
    (hG : ContinuousOn G (Metric.closedBall x r)) (c : Euc d) :
    sqExcess G x r ≤ ∫ y in Metric.closedBall x r, ‖G y - c‖ ^ 2 :=
  integral_norm_sub_setAverage_sq_le_const hr hG c

/-- The excess is monotone in the radius. -/
theorem sqExcess_mono {G : Euc d → Euc d} {x : Euc d} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hG : ContinuousOn G (Metric.closedBall x r)) : sqExcess G x ρ ≤ sqExcess G x r :=
  integral_norm_sub_setAverage_sq_mono hρ hρr hG

/-- `t ^ (d + 2) = t ^ d * t ^ 2` for the real power. -/
theorem rpow_natCast_add_two {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ ((n : ℝ) + 2) = t ^ n * t ^ 2 := by
  have h2 : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.rpow_add ht, Real.rpow_natCast, h2]

/-- **The excess of a Lipschitz field on a small ball.**  Combined with an interior derivative
estimate this is step (4) of the harmonic decay: `∫_{B_ρ}‖G - (G)_ρ‖² ≤ ω_d K² ρ^{d+2}`. -/
theorem sqExcess_le_of_lipschitz {G : Euc d → Euc d} {x : Euc d} {ρ K : ℝ} (hρ : 0 < ρ)
    (hG : ContinuousOn G (Metric.closedBall x ρ)) (hK : 0 ≤ K)
    (hlip : ∀ y ∈ Metric.closedBall x ρ, ∀ z ∈ Metric.closedBall x ρ,
      ‖G y - G z‖ ≤ K * dist y z) :
    sqExcess G x ρ ≤
      volume.real (Metric.closedBall (0 : Euc d) 1) * (K ^ 2 * ρ ^ ((d : ℝ) + 2)) := by
  have hbd : ∀ y ∈ Metric.closedBall x ρ, ‖G y - G x‖ ≤ K * ρ := by
    intro y hy
    refine (hlip y hy x (Metric.mem_closedBall_self hρ.le)).trans ?_
    exact mul_le_mul_of_nonneg_left (Metric.mem_closedBall.1 hy) hK
  have h1 : sqExcess G x ρ ≤ (K * ρ) ^ 2 * volume.real (Metric.closedBall x ρ) :=
    (sqExcess_le_const hρ hG (G x)).trans (setIntegral_norm_sub_sq_le hG hbd)
  rw [volume_real_closedBall x hρ.le] at h1
  refine h1.trans_eq ?_
  rw [rpow_natCast_add_two hρ d]
  ring

/-- **Morrey decay of the gradient energy from an interior Lipschitz estimate** (step (3) ⇒ (4)
of the harmonic theory).  If the field `G` is `K`-Lipschitz on `B(x, r/2)` with
`K² r^{d+2} ≤ C · sqExcess G x r`, then the excess decays at the Morrey rate `(ρ/r)^{d+2}`. -/
theorem sqExcess_decay_of_lipschitz {G : Euc d → Euc d} {x : Euc d} {r K C : ℝ} (hr : 0 < r)
    (hG : ContinuousOn G (Metric.closedBall x r)) (hK : 0 ≤ K)
    (hlip : ∀ y ∈ Metric.closedBall x (r / 2), ∀ z ∈ Metric.closedBall x (r / 2),
      ‖G y - G z‖ ≤ K * dist y z)
    (hKC : K ^ 2 * r ^ ((d : ℝ) + 2) ≤ C * sqExcess G x r) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ ≤ r / 2) :
    sqExcess G x ρ ≤ volume.real (Metric.closedBall (0 : Euc d) 1) * C *
      ((ρ / r) ^ ((d : ℝ) + 2) * sqExcess G x r) := by
  have hω : (0 : ℝ) ≤ volume.real (Metric.closedBall (0 : Euc d) 1) :=
    volume_real_closedBall_pos.le
  have hsub : Metric.closedBall x ρ ⊆ Metric.closedBall x (r / 2) :=
    Metric.closedBall_subset_closedBall hρr
  have hsub' : Metric.closedBall x ρ ⊆ Metric.closedBall x r :=
    Metric.closedBall_subset_closedBall (by linarith)
  have h1 := sqExcess_le_of_lipschitz (G := G) (x := x) (ρ := ρ) (K := K) hρ (hG.mono hsub') hK
    fun y hy z hz => hlip y (hsub hy) z (hsub hz)
  have hrne : r ≠ 0 := hr.ne'
  have hsplit : ρ ^ ((d : ℝ) + 2) = (ρ / r) ^ ((d : ℝ) + 2) * r ^ ((d : ℝ) + 2) := by
    rw [← Real.mul_rpow (div_nonneg hρ.le hr.le) hr.le]
    congr 1
    field_simp
  have hq : (0 : ℝ) ≤ (ρ / r) ^ ((d : ℝ) + 2) :=
    Real.rpow_nonneg (div_nonneg hρ.le hr.le) _
  refine h1.trans ?_
  rw [hsplit]
  have h2 : K ^ 2 * ((ρ / r) ^ ((d : ℝ) + 2) * r ^ ((d : ℝ) + 2)) =
      (ρ / r) ^ ((d : ℝ) + 2) * (K ^ 2 * r ^ ((d : ℝ) + 2)) := by ring
  rw [h2]
  have h3 : (ρ / r) ^ ((d : ℝ) + 2) * (K ^ 2 * r ^ ((d : ℝ) + 2)) ≤
      (ρ / r) ^ ((d : ℝ) + 2) * (C * sqExcess G x r) :=
    mul_le_mul_of_nonneg_left hKC hq
  calc volume.real (Metric.closedBall (0 : Euc d) 1) *
        ((ρ / r) ^ ((d : ℝ) + 2) * (K ^ 2 * r ^ ((d : ℝ) + 2)))
      ≤ volume.real (Metric.closedBall (0 : Euc d) 1) *
        ((ρ / r) ^ ((d : ℝ) + 2) * (C * sqExcess G x r)) := by
        exact mul_le_mul_of_nonneg_left h3 hω
    _ = volume.real (Metric.closedBall (0 : Euc d) 1) * C *
        ((ρ / r) ^ ((d : ℝ) + 2) * sqExcess G x r) := by ring

/-! ### Comparing two fields in the `L²` excess -/

/-- The elementary triangle inequality in squared form. -/
theorem norm_sub_sq_le_two_add {E : Type*} [NormedAddCommGroup E] (a b c : E) :
    ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have h : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    have e : a - c = (a - b) + (b - c) := by abel
    rw [e]
    exact norm_add_le _ _
  nlinarith [norm_nonneg (a - b), norm_nonneg (b - c), norm_nonneg (a - c),
    sq_nonneg (‖a - b‖ - ‖b - c‖)]

/-- The integrated triangle inequality: the `L²` deviation of `G` from a constant is controlled by
the `L²` distance from `G` to `H` plus the `L²` deviation of `H`. -/
theorem setIntegral_norm_sub_sq_le_two_add {G H : Euc d → Euc d} {x : Euc d} {r : ℝ}
    (hG : ContinuousOn G (Metric.closedBall x r)) (hH : ContinuousOn H (Metric.closedBall x r))
    (c : Euc d) :
    (∫ y in Metric.closedBall x r, ‖G y - c‖ ^ 2) ≤
      2 * (∫ y in Metric.closedBall x r, ‖G y - H y‖ ^ 2) +
        2 * ∫ y in Metric.closedBall x r, ‖H y - c‖ ^ 2 := by
  have hcpt : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  have i1 : IntegrableOn (fun y => ‖G y - c‖ ^ 2) (Metric.closedBall x r) :=
    ((hG.sub continuousOn_const).norm.pow 2).integrableOn_compact hcpt
  have i2 : IntegrableOn (fun y => ‖G y - H y‖ ^ 2) (Metric.closedBall x r) :=
    ((hG.sub hH).norm.pow 2).integrableOn_compact hcpt
  have i3 : IntegrableOn (fun y => ‖H y - c‖ ^ 2) (Metric.closedBall x r) :=
    ((hH.sub continuousOn_const).norm.pow 2).integrableOn_compact hcpt
  have hmono : (∫ y in Metric.closedBall x r, ‖G y - c‖ ^ 2) ≤
      ∫ y in Metric.closedBall x r, (2 * ‖G y - H y‖ ^ 2 + 2 * ‖H y - c‖ ^ 2) :=
    integral_mono i1 ((i2.const_mul 2).add (i3.const_mul 2))
      (fun y => norm_sub_sq_le_two_add (G y) (H y) c)
  rwa [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul, integral_const_mul]
    at hmono

/-- Monotonicity in the domain of a nonnegative squared integrand. -/
theorem setIntegral_norm_sub_sq_mono {G H : Euc d → Euc d} {x : Euc d} {ρ r : ℝ} (hρr : ρ ≤ r)
    (hG : ContinuousOn G (Metric.closedBall x r)) (hH : ContinuousOn H (Metric.closedBall x r)) :
    (∫ y in Metric.closedBall x ρ, ‖G y - H y‖ ^ 2) ≤
      ∫ y in Metric.closedBall x r, ‖G y - H y‖ ^ 2 := by
  have hsub : Metric.closedBall x ρ ⊆ Metric.closedBall x r :=
    Metric.closedBall_subset_closedBall hρr
  exact setIntegral_mono_set
    (((hG.sub hH).norm.pow 2).integrableOn_compact (isCompact_closedBall x r))
    (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE

/-! ### The interior derivative estimate and the freezing comparison

`exists_constCoeff_gradient_lipschitz` is the `ℝ^d` interior derivative estimate; it is now
proved, in `Komlos.Literature.PLaplacian.HarmonicMVP`, from the mean value property built there.
`exists_frozen_comparison` below is the remaining classical input of this file. -/

/-- **Interior derivative estimate for a constant-coefficient elliptic equation**
(Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 8.32,
step 1; Giaquinta–Martinazzi, Theorem 5.14): if `A₀` is a constant `μ`-elliptic, `Λ`-bounded
matrix and `h` solves `div (A₀ ∇h) = 0` weakly on `B(x, 2r)`, then `∇h` is Lipschitz on the half
ball `B(x, r/2)` with a Lipschitz constant `K` obeying the scale-invariant bound
`K² r^{d+2} ≤ C ∫_{B(x,r)} ‖∇h - (∇h)_{B(x,r)}‖²`, where `C = C(d, μ, Λ)`.

Fed into `sqExcess_decay_of_lipschitz` (proved above) it yields the Morrey decay
`exists_constCoeff_sqExcess_decay`, which is derived from it below.

The proof is `Komlos.Literature.exists_constCoeff_gradient_lipschitz_aux` of
`Komlos/Literature/PLaplacian/HarmonicMVP.lean`, which builds the missing `ℝ^d` theory: the
antisymmetric part of the constant `A₀` drops out of the weak equation already for `C¹`
solutions, and for the symmetric part `A` the **mean value property**
`(∫ χ) h x = ∫ χ(w) h (x + s w) dw` is obtained by testing the weak equation against the
rescaled bump `W((y - x)/s)` with `W = θ(⟪A⁻¹ ·, ·⟫)` — the identity `∇W(w) = χ(w) • A⁻¹ w`
replaces the divergence theorem, which Mathlib has only for boxes.  Comparing the resulting mean
value property for the gradient at two nearby base points gives the Lipschitz bound with
`K ≲ r^{-(d+2)/2} ‖∇h - (∇h)_r‖_{L²(B(x,r))}`, which is the statement below. -/
theorem exists_constCoeff_gradient_lipschitz (d : ℕ) {μ Λ : ℝ} (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A₀ : Euc d →L[ℝ] Euc d) (h : Euc d → ℝ) (x : Euc d) (r : ℝ), 0 < r →
        (∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) → ‖A₀‖ ≤ Λ →
        ContDiffOn ℝ 1 h (Metric.ball x (2 * r)) →
        IsWeakConstSolutionOn A₀ (Metric.ball x (2 * r)) h →
        ∃ K : ℝ, 0 ≤ K ∧
          K ^ 2 * r ^ ((d : ℝ) + 2) ≤ C * sqExcess (gradient h) x r ∧
          ∀ y ∈ Metric.closedBall x (r / 2), ∀ z ∈ Metric.closedBall x (r / 2),
            ‖gradient h y - gradient h z‖ ≤ K * dist y z := by
  -- The `ℝ^d` mean value property and the interior derivative estimate are built in
  -- `Komlos.Literature.PLaplacian.HarmonicMVP`; `exists_constCoeff_gradient_lipschitz_aux` is the
  -- same statement with `r ^ ((d : ℝ) + 2)` written as the natural power `r ^ d * r ^ 2` and with
  -- `IsWeakConstSolutionOn` and `sqExcess` unfolded.
  obtain ⟨C, hC0, hest⟩ := exists_constCoeff_gradient_lipschitz_aux d (μ := μ) (Λ := Λ) hμ
  refine ⟨C, hC0, ?_⟩
  intro A₀ h x r hr hell hbdd hh hsol
  obtain ⟨K, hK0, hKC, hlip⟩ := hest A₀ h x r hr hell hbdd hh hsol
  refine ⟨K, hK0, ?_, hlip⟩
  rw [rpow_natCast_add_two hr d, sqExcess_eq]
  exact hKC

/-- **Interior Morrey decay of the gradient energy for a constant-coefficient elliptic equation**
(Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 8.32,
step 1; Giaquinta–Martinazzi, Theorem 5.14): if `A₀` is a constant `μ`-elliptic, `Λ`-bounded
matrix and `h` solves `div (A₀ ∇h) = 0` weakly on `B(x, 2r)`, then the gradient energy
oscillation obeys `Φ_h(ρ) ≤ C (ρ/r)^{d+2} Φ_h(r)`, with `C = C(d, μ, Λ)`.

The proof splits the range of `ρ` at `r/2`.  For `ρ ≤ r/2` this is the interior derivative
estimate `exists_constCoeff_gradient_lipschitz` fed into `sqExcess_decay_of_lipschitz`.  For
`r/2 < ρ ≤ r` no equation is needed: the excess is monotone in the radius
(`sqExcess_mono`) and `(ρ/r)^{d+2} ≥ 2^{-(d+2)}`, so the constant `2^{d+2}` suffices. -/
theorem exists_constCoeff_sqExcess_decay (d : ℕ) {μ Λ : ℝ} (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A₀ : Euc d →L[ℝ] Euc d) (h : Euc d → ℝ) (x : Euc d) (r : ℝ), 0 < r →
        (∀ ζ : Euc d, μ * ‖ζ‖ ^ 2 ≤ ⟪A₀ ζ, ζ⟫) → ‖A₀‖ ≤ Λ →
        ContDiffOn ℝ 1 h (Metric.ball x (2 * r)) →
        IsWeakConstSolutionOn A₀ (Metric.ball x (2 * r)) h →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
          sqExcess (gradient h) x ρ ≤
            C * ((ρ / r) ^ ((d : ℝ) + 2) * sqExcess (gradient h) x r) := by
  obtain ⟨C₀, hC₀, hest⟩ := exists_constCoeff_gradient_lipschitz d (μ := μ) (Λ := Λ) hμ
  have hω : (0 : ℝ) ≤ volume.real (Metric.closedBall (0 : Euc d) 1) :=
    (volume_real_closedBall_pos (d := d)).le
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) + 2) := Real.rpow_nonneg (by norm_num) _
  refine ⟨volume.real (Metric.closedBall (0 : Euc d) 1) * C₀ + (2 : ℝ) ^ ((d : ℝ) + 2),
    add_nonneg (mul_nonneg hω hC₀) h2d, ?_⟩
  intro A₀ h x r hr hell hbdd hh hsol ρ hρ hρr
  have hsub : Metric.closedBall x r ⊆ Metric.ball x (2 * r) := fun y hy =>
    Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (by linarith))
  have hGc : ContinuousOn (gradient h) (Metric.closedBall x r) :=
    (continuousOn_gradient Metric.isOpen_ball hh).mono hsub
  have hq0 : (0 : ℝ) ≤ (ρ / r) ^ ((d : ℝ) + 2) :=
    Real.rpow_nonneg (div_nonneg hρ.le hr.le) _
  have hS0 : (0 : ℝ) ≤ sqExcess (gradient h) x r := sqExcess_nonneg _ _ _
  rcases le_or_gt ρ (r / 2) with hsmall | hbig
  · -- the interior derivative estimate plus `sqExcess_decay_of_lipschitz`
    obtain ⟨K, hK0, hKC, hlip⟩ := hest A₀ h x r hr hell hbdd hh hsol
    have hdecay : sqExcess (gradient h) x ρ ≤
        volume.real (Metric.closedBall (0 : Euc d) 1) * C₀ *
          ((ρ / r) ^ ((d : ℝ) + 2) * sqExcess (gradient h) x r) :=
      sqExcess_decay_of_lipschitz hr hGc hK0 hlip hKC hρ hsmall
    refine hdecay.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hq0 hS0))
    linarith
  · -- the range `r/2 < ρ ≤ r`: monotonicity of the excess suffices
    have hmono : sqExcess (gradient h) x ρ ≤ sqExcess (gradient h) x r :=
      sqExcess_mono hρ hρr hGc
    have hhalf : (1 : ℝ) / 2 ≤ ρ / r := by
      rw [le_div_iff₀ hr]
      linarith
    have hqle : ((1 : ℝ) / 2) ^ ((d : ℝ) + 2) ≤ (ρ / r) ^ ((d : ℝ) + 2) :=
      Real.rpow_le_rpow (by norm_num) hhalf (by positivity)
    have hinv : (2 : ℝ) ^ ((d : ℝ) + 2) * ((1 : ℝ) / 2) ^ ((d : ℝ) + 2) = 1 := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 2),
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.one_rpow]
    calc sqExcess (gradient h) x ρ
        ≤ sqExcess (gradient h) x r := hmono
      _ = (2 : ℝ) ^ ((d : ℝ) + 2) *
            (((1 : ℝ) / 2) ^ ((d : ℝ) + 2) * sqExcess (gradient h) x r) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ (2 : ℝ) ^ ((d : ℝ) + 2) *
            ((ρ / r) ^ ((d : ℝ) + 2) * sqExcess (gradient h) x r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqle hS0) h2d
      _ ≤ (volume.real (Metric.closedBall (0 : Euc d) 1) * C₀ + (2 : ℝ) ^ ((d : ℝ) + 2)) *
            ((ρ / r) ^ ((d : ℝ) + 2) * sqExcess (gradient h) x r) :=
          mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hω hC₀])
            (mul_nonneg hq0 hS0)


end Komlos.Literature
