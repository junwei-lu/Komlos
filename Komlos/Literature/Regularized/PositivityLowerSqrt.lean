import Komlos.Literature.Regularized.PositivityDG
import Komlos.Literature.PLaplacian.RegularityHarnack

/-!
# Lane `L2p` (`reg/pos-lower`), step 1: the square-root competitor `√(v² + g²)`

`REGULARIZED_ROUTE.md`, Revision 2 (iii): the local positive lower bound for the regularized
minimizer rests on the *convexity of the energy in the density* `ρ̃ = w²`, and the only
competitors that see that convexity are those obtained by **adding mass to the density**,
`ρ̃ ↦ ρ̃ + g²`.  In the variable `w` that is the competitor

`w = √(v² + g²)`,  `g` smooth, nonnegative, compactly supported in `K`.

A competitor of the form `v + τ ψ` is useless here: it perturbs the density by
`2 τ v ψ + τ² ψ²`, a quantity that vanishes exactly where `v` does, i.e. exactly where the
information is needed.

This file builds that competitor.  Its two non-trivial ingredients are:

* **the weak gradient** `∇w = w⁻¹ (v ∇v + g ∇g)` (`IsRegComp.hasWeakGradient_sqrtAdd`).  The map
  `t ↦ √t` is not Lipschitz at `0`, so the one-variable chain rule `memW0_comp` does not apply
  directly; instead `√(U + ε) - √ε` (`U = v² + g²`) *is* a legitimate `C¹` composition with
  bounded derivative (`memW0_comp_sub_of_hasDerivAt`), and the family is passed to the limit
  `ε ↓ 0` with `HasWeakGradient.of_tendsto`.  The pointwise domination
  `‖∇√(U+ε)‖ ≤ √(‖∇v‖² + ‖∇g‖²)` is Cauchy–Schwarz in `ℝ²` and is uniform in `ε`;
* **subadditivity of the kinetic density** (`homogeneousDensity_two_add_le`):
  `D(√(a²+b²), ·) ≤ D(a, ξ) + D(b, η)` for the perspective-type density `D(s, ξ) = s² Ψ(ξ/s)`.
  In the density variable this is exactly the joint convexity of the perspective of `Ψ`, and it
  is the reason the whole argument is run in `ρ̃ = w²`: the density `D` itself is *not* jointly
  convex in `(s, ξ)` for a general convex `Ψ`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {K : Set (Euc d)}

/-! ### Elementary square-root inequalities -/

/-- Subadditivity of `Real.sqrt`. -/
theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- **Cauchy–Schwarz in `ℝ²`**: `a c + b e ≤ √(a² + b²) √(c² + e²)`. -/
theorem mul_add_mul_le_sqrt_mul_sqrt {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) :
    a * c + b * e ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + e ^ 2) := by
  have hnn : 0 ≤ a * c + b * e := by positivity
  have hsq : (a * c + b * e) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + e ^ 2) := by
    nlinarith [sq_nonneg (a * e - b * c)]
  calc a * c + b * e = Real.sqrt ((a * c + b * e) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + e ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + e ^ 2) := Real.sqrt_mul (by positivity) _

/-! ### Convexity of the perspective -/

/-- **Joint convexity of the perspective of `Ψ`**, in the form used below:
`(a² + b²) Ψ((a ξ + b η)/(a² + b²)) ≤ a² Ψ(ξ/a) + b² Ψ(η/b)`.

With `ρ₁ = a²`, `ρ₂ = b²`, `m_i = ∇ρ_i`, this is
`D̃(ρ₁ + ρ₂, m₁ + m₂) ≤ D̃(ρ₁, m₁) + D̃(ρ₂, m₂)` for the perspective `D̃(ρ, m) = ρ Ψ(m/(2ρ))`,
i.e. convexity of `Ψ` plus `1`-homogeneity of the perspective. -/
theorem convex_perspective_two {Ψ : Euc d → ℝ} (hΨ : ConvexOn ℝ (Set.univ : Set (Euc d)) Ψ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ξ η : Euc d) :
    (a ^ 2 + b ^ 2) * Ψ ((a ^ 2 + b ^ 2)⁻¹ • (a • ξ + b • η)) ≤
      a ^ 2 * Ψ (a⁻¹ • ξ) + b ^ 2 * Ψ (b⁻¹ • η) := by
  rcases ha.eq_or_lt with rfl | hapos
  · rcases hb.eq_or_lt with rfl | hbpos
    · norm_num
    · have h1 : ((0 : ℝ) ^ 2 + b ^ 2)⁻¹ • ((0 : ℝ) • ξ + b • η) = b⁻¹ • η := by
        rw [zero_pow two_ne_zero, zero_add, zero_smul, zero_add, smul_smul]
        congr 1
        field_simp
      rw [h1]
      norm_num
  · rcases hb.eq_or_lt with rfl | hbpos
    · have h1 : (a ^ 2 + (0 : ℝ) ^ 2)⁻¹ • (a • ξ + (0 : ℝ) • η) = a⁻¹ • ξ := by
        rw [zero_pow two_ne_zero, add_zero, zero_smul, add_zero, smul_smul]
        congr 1
        field_simp
      rw [h1]
      norm_num
    · have hS0 : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
      have hs0 : (0 : ℝ) ≤ a ^ 2 / (a ^ 2 + b ^ 2) := by positivity
      have ht0 : (0 : ℝ) ≤ b ^ 2 / (a ^ 2 + b ^ 2) := by positivity
      have hst : a ^ 2 / (a ^ 2 + b ^ 2) + b ^ 2 / (a ^ 2 + b ^ 2) = 1 := by
        field_simp
      have hcomb : (a ^ 2 / (a ^ 2 + b ^ 2)) • (a⁻¹ • ξ) + (b ^ 2 / (a ^ 2 + b ^ 2)) • (b⁻¹ • η)
          = (a ^ 2 + b ^ 2)⁻¹ • (a • ξ + b • η) := by
        rw [smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
        congr 1
        · congr 1
          field_simp
          try ring
        · congr 1
          field_simp
          try ring
      have h := hΨ.2 (mem_univ (a⁻¹ • ξ)) (mem_univ (b⁻¹ • η)) hs0 ht0 hst
      rw [hcomb] at h
      have h2 : (a ^ 2 + b ^ 2) * Ψ ((a ^ 2 + b ^ 2)⁻¹ • (a • ξ + b • η)) ≤
          (a ^ 2 + b ^ 2) * ((a ^ 2 / (a ^ 2 + b ^ 2)) * Ψ (a⁻¹ • ξ) +
            (b ^ 2 / (a ^ 2 + b ^ 2)) * Ψ (b⁻¹ • η)) := by
        simpa using mul_le_mul_of_nonneg_left h hS0.le
      have h3 : (a ^ 2 + b ^ 2) * ((a ^ 2 / (a ^ 2 + b ^ 2)) * Ψ (a⁻¹ • ξ) +
            (b ^ 2 / (a ^ 2 + b ^ 2)) * Ψ (b⁻¹ • η)) =
          a ^ 2 * Ψ (a⁻¹ • ξ) + b ^ 2 * Ψ (b⁻¹ • η) := by
        field_simp
      linarith [h2, h3.le, h3.ge]

/-- **Subadditivity of the kinetic density** `D(s, ξ) = s² Ψ(ξ/s)` along the density variable:
`D(√(a²+b²), (a ξ + b η)/√(a²+b²)) ≤ D(a, ξ) + D(b, η)`.  This is `convex_perspective_two`. -/
theorem homogeneousDensity_two_add_le {Ψ : Euc d → ℝ}
    (hΨ : ConvexOn ℝ (Set.univ : Set (Euc d)) Ψ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ξ η : Euc d) :
    Korevaar.homogeneousDensity 2 Ψ (Real.sqrt (a ^ 2 + b ^ 2))
        ((Real.sqrt (a ^ 2 + b ^ 2))⁻¹ • (a • ξ + b • η)) ≤
      Korevaar.homogeneousDensity 2 Ψ a ξ + Korevaar.homogeneousDensity 2 Ψ b η := by
  have hsum : (0 : ℝ) ≤ a ^ 2 + b ^ 2 := by positivity
  have hcsq : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hsum
  rw [pos_homogeneousDensity_two, pos_homogeneousDensity_two, pos_homogeneousDensity_two, hcsq]
  have hinner : (Real.sqrt (a ^ 2 + b ^ 2))⁻¹ •
      ((Real.sqrt (a ^ 2 + b ^ 2))⁻¹ • (a • ξ + b • η)) =
      (a ^ 2 + b ^ 2)⁻¹ • (a • ξ + b • η) := by
    rw [smul_smul, ← mul_inv, ← sq, hcsq]
  rw [hinner]
  exact convex_perspective_two hΨ ha hb ξ η

/-! ### `L²` membership for bounded functions supported in `K` -/

/-- A bounded a.e.-measurable function vanishing off the bounded open set `K` lies in `L²`. -/
theorem memLp_two_of_bounded_of_support (hK : IsGoodConvex K) {f : Euc d → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hB : ∀ x, |f x| ≤ B)
    (hsupp : ∀ x, x ∉ K → f x = 0) : MemLp f (ENNReal.ofReal 2) := by
  have hsq : Integrable (fun x => f x ^ 2) volume := by
    refine integrable_of_bounded_of_support (B := B ^ 2) hK (hf.pow 2) (fun x => ?_)
      (fun x hx => by rw [hsupp x hx]; ring)
    have h0 : (0 : ℝ) ≤ |f x| := abs_nonneg _
    have h1 : |f x ^ 2| = |f x| ^ 2 := by rw [abs_pow]
    rw [h1]
    nlinarith [hB x]
  rw [dgn_ofReal_two]
  exact (memLp_two_iff_integrable_sq hf).2 hsq

/-! ### The square-root competitor -/

/-- The perturbed density `U = v² + g²`. -/
noncomputable def sqrtAddSq (v g : Euc d → ℝ) : Euc d → ℝ := fun x => v x ^ 2 + g x ^ 2

/-- The weak gradient of `sqrtAddSq v g`, namely `2 v ∇v + 2 g ∇g`. -/
noncomputable def sqrtAddSqGrad (v g : Euc d → ℝ) : Euc d → Euc d :=
  fun x => (2 * v x) • weakGrad v x + (2 * g x) • gradient g x

/-- The square-root competitor `w = √(v² + g²)`. -/
noncomputable def sqrtAdd (v g : Euc d → ℝ) : Euc d → ℝ :=
  fun x => Real.sqrt (sqrtAddSq v g x)

/-- The weak gradient of `sqrtAdd v g`, namely `w⁻¹ (v ∇v + g ∇g)`, with the junk value `0`
where `w = 0` (which is correct there, because `v = g = 0`). -/
noncomputable def sqrtAddGrad (v g : Euc d → ℝ) : Euc d → Euc d :=
  fun x => (sqrtAdd v g x)⁻¹ • (v x • weakGrad v x + g x • gradient g x)

variable {v g : Euc d → ℝ}

theorem sqrtAddSq_nonneg (v g : Euc d → ℝ) (x : Euc d) : 0 ≤ sqrtAddSq v g x := by
  rw [sqrtAddSq]; positivity

theorem sqrtAdd_nonneg (v g : Euc d → ℝ) (x : Euc d) : 0 ≤ sqrtAdd v g x := Real.sqrt_nonneg _

theorem sqrtAdd_sq (v g : Euc d → ℝ) (x : Euc d) : sqrtAdd v g x ^ 2 = v x ^ 2 + g x ^ 2 :=
  Real.sq_sqrt (sqrtAddSq_nonneg v g x)

/-- A pointwise bound for a normalized combination, `‖r⁻¹ (a ξ + b η)‖ ≤ √(‖ξ‖² + ‖η‖²)` whenever
`√(a² + b²) ≤ r`: Cauchy–Schwarz in `ℝ²`.  It is what makes the approximating gradients below
uniformly dominated. -/
theorem norm_inv_smul_pair_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ξ η : Euc d)
    (hr : Real.sqrt (a ^ 2 + b ^ 2) ≤ r) :
    ‖r⁻¹ • (a • ξ + b • η)‖ ≤ Real.sqrt (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
  have hr0 : (0 : ℝ) ≤ r := le_trans (Real.sqrt_nonneg _) hr
  have hz : ‖a • ξ + b • η‖ ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg hb]
    exact mul_add_mul_le_sqrt_mul_sqrt ha hb (norm_nonneg _) (norm_nonneg _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hr0)]
  rcases eq_or_lt_of_le hr0 with h | hrpos
  · simp [← h]
  · have h1 : r⁻¹ * ‖a • ξ + b • η‖ ≤
        r⁻¹ * (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    have hone : r⁻¹ * Real.sqrt (a ^ 2 + b ^ 2) ≤ 1 := by
      rw [inv_mul_eq_div]
      exact (div_le_one hrpos).2 hr
    have h2 : r⁻¹ * (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (‖ξ‖ ^ 2 + ‖η‖ ^ 2)) ≤
        Real.sqrt (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
      rw [← mul_assoc]
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _) hone
    linarith

/-- `v² ∈ W₀^{1,2}(K)` with weak gradient `2 v ∇v`, for a bounded competitor `v`. -/
theorem IsRegComp.memW0_sq (hv : IsRegComp K v) :
    MemW0 2 K (fun x => v x ^ 2) ∧
      weakGrad (fun x => v x ^ 2) =ᵐ[volume] fun x => (2 * v x) • weakGrad v x := by
  obtain ⟨M₀, hM₀⟩ := hv.exists_le
  have hMnn : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have h := memW0_comp_sub_of_hasDerivAt (p := 2) one_lt_two hv.memW0 hMnn
      (fun x => ⟨hv.nonneg x, (hM₀ x).trans (le_max_left _ _)⟩)
      (Ψ := fun t => t ^ 2) (ψ' := fun t => 2 * t)
      (fun t _ => by simpa using hasDerivAt_pow 2 t) (by fun_prop)
  simpa using h

/-- `√(U + ε) - √ε ∈ W₀^{1,2}(K)` for `U ∈ W₀^{1,2}(K)` with values in `[0, S]`: the map
`t ↦ √(t + ε)` is `C¹` with bounded derivative there. -/
theorem memW0_sqrt_add_const {U : Euc d → ℝ} (hU : MemW0 2 K U) {S : ℝ} (hS : 0 ≤ S)
    (hUS : ∀ x, U x ∈ Icc 0 S) {ε : ℝ} (hε : 0 < ε) :
    MemW0 2 K (fun x => Real.sqrt (U x + ε) - Real.sqrt ε) ∧
      weakGrad (fun x => Real.sqrt (U x + ε) - Real.sqrt ε) =ᵐ[volume]
        fun x => (2 * Real.sqrt (U x + ε))⁻¹ • weakGrad U x := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivAt (fun s : ℝ => Real.sqrt (s + ε)) ((2 * Real.sqrt (t + ε))⁻¹) t := by
    intro t ht
    have hpos : (0 : ℝ) < t + ε := by linarith [ht.1]
    have h1 : HasDerivAt (fun s : ℝ => s + ε) 1 t := (hasDerivAt_id t).add_const ε
    have h3 := h1.sqrt hpos.ne'
    simpa [one_div] using h3
  have hcont : ContinuousOn (fun t : ℝ => (2 * Real.sqrt (t + ε))⁻¹) (Icc 0 S) := by
    refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) (fun t ht => ?_)
    have hpos : (0 : ℝ) < Real.sqrt (t + ε) := Real.sqrt_pos.2 (by linarith [ht.1])
    positivity
  have h := memW0_comp_sub_of_hasDerivAt (p := 2) one_lt_two hU hS hUS hderiv hcont
  simpa using h

/-! ### The competitor: weak gradient and membership in the competitor class -/

/-- `|√(U+ε) - √ε - √U| ≤ √ε`: the error of the regularized square root, uniformly in `U ≥ 0`. -/
theorem abs_sqrt_add_sub_sqrt_le {U ε : ℝ} (hU : 0 ≤ U) (hε : 0 ≤ ε) :
    |Real.sqrt (U + ε) - Real.sqrt ε - Real.sqrt U| ≤ Real.sqrt ε := by
  have h1 : Real.sqrt U ≤ Real.sqrt (U + ε) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (U + ε) ≤ Real.sqrt U + Real.sqrt ε := sqrt_add_le_add_sqrt hU hε
  rw [abs_le]
  constructor <;> linarith

/-- `(2s)⁻¹ (2a ξ + 2b η) = s⁻¹ (a ξ + b η)`, also at `s = 0`. -/
theorem inv_two_mul_smul_pair (s a b : ℝ) (ξ η : Euc d) :
    (2 * s)⁻¹ • ((2 * a) • ξ + (2 * b) • η) = s⁻¹ • (a • ξ + b • η) := by
  have h1 : (2 * s)⁻¹ * (2 * a) = s⁻¹ * a := by rw [mul_inv]; ring
  have h2 : (2 * s)⁻¹ * (2 * b) = s⁻¹ * b := by rw [mul_inv]; ring
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, h1, h2]

/-- **The square-root competitor** (`REGULARIZED_ROUTE.md`, Revision 2 (iii)).  For a bounded
nonnegative `v ∈ W₀^{1,2}(K)` and a smooth nonnegative `g` compactly supported in `K`, the
function `w = √(v² + g²)` is again a competitor of the local problem, with weak gradient
`w⁻¹ (v ∇v + g ∇g)`.

Proof: `U = v² + g²` lies in `W₀^{1,2}(K)` with `∇U = 2 v ∇v + 2 g ∇g` (the one-variable chain
rule at the `C¹` profile `t ↦ t²`, `IsRegComp.memW0_sq`, plus smoothness of `g`) and takes values
in `[0, S]`.  The square root is not Lipschitz at `0`, so `w` is obtained as an `L²` limit of
`w_ε = √(U + ε) - √ε`, each of which *is* a `C¹` composition with bounded derivative
(`memW0_sqrt_add_const`).  The gradients `∇w_ε = ∇U/(2√(U+ε))` are dominated, uniformly in `ε`,
by `√(‖∇v‖² + ‖∇g‖²) ∈ L²` (Cauchy–Schwarz in `ℝ²`, `norm_inv_smul_pair_le`), and converge
pointwise to `∇U/(2√U)`: where `U = 0` both `v` and `g` vanish, so the numerator vanishes too and
the junk value `0` is correct.  `HasWeakGradient.of_tendsto` concludes. -/
theorem IsRegComp.sqrtAdd_spec (hK : IsGoodConvex K) (hv : IsRegComp K v)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) (hgK : tsupport g ⊆ K)
    (hg0 : ∀ x, 0 ≤ g x) :
    HasWeakGradient (sqrtAdd v g) (sqrtAddGrad v g) ∧ IsRegComp K (sqrtAdd v g) := by
  classical
  -- pointwise bounds
  obtain ⟨M₀, hM₀⟩ := hv.exists_le
  obtain ⟨A₀, hA₀⟩ := hg.continuous.bounded_above_of_compact_support hgs
  have hMnn : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have hAnn : (0 : ℝ) ≤ max A₀ 0 := le_max_right _ _
  have hM : ∀ x, v x ≤ max M₀ 0 := fun x => (hM₀ x).trans (le_max_left _ _)
  have hA : ∀ x, g x ≤ max A₀ 0 := fun x => by
    refine le_trans (le_trans (le_abs_self _) ?_) (le_max_left _ _)
    rw [← Real.norm_eq_abs]; exact hA₀ x
  have hgzero : ∀ x, x ∉ K → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hgK h)
  -- smoothness data for `g`
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hgsq1 : ContDiff ℝ 1 (fun x => g x ^ 2) := (hg.pow 2).of_le (by exact_mod_cast le_top)
  have hgsqs : HasCompactSupport (fun x => g x ^ 2) := by
    rw [HasCompactSupport, tsupport_sq]; exact hgs
  have hgradsq : ∀ x, gradient (fun y => g y ^ 2) x = (2 * g x) • gradient g x := by
    intro x
    refine gradient_eq_smul_of_hasFDerivAt ?_
    have h := ((hg1.differentiable one_ne_zero) x).hasFDerivAt.pow 2
    simpa using h
  -- the perturbed density `U = v² + g²`
  obtain ⟨hvsq, hvsqg⟩ := hv.memW0_sq
  have hg2w : HasWeakGradient (fun x => g x ^ 2) (fun x => (2 * g x) • gradient g x) :=
    (hasWeakGradient_gradient hgsq1 hgsqs).congr_right (Eventually.of_forall hgradsq)
  have hv2w : HasWeakGradient (fun x => v x ^ 2) (fun x => (2 * v x) • weakGrad v x) :=
    hvsq.hasWeakGradient.congr_right hvsqg
  have hUw : HasWeakGradient (sqrtAddSq v g) (sqrtAddSqGrad v g) := by
    refine ((hv2w.add hg2w).congr_left (Eventually.of_forall fun x => ?_)).congr_right
      (Eventually.of_forall fun x => ?_) <;> rfl
  have hUmem : MemW0 2 K (sqrtAddSq v g) := by
    have h := hvsq.add (memW0_of_contDiff hgsq1 hgsqs (by rw [tsupport_sq]; exact hgK) 2)
    exact h.congr (Eventually.of_forall fun x => rfl)
  have hUnn : ∀ x, 0 ≤ sqrtAddSq v g x := sqrtAddSq_nonneg v g
  have hSnn : (0 : ℝ) ≤ (max M₀ 0) ^ 2 + (max A₀ 0) ^ 2 := by positivity
  have hUS : ∀ x, sqrtAddSq v g x ∈ Icc 0 ((max M₀ 0) ^ 2 + (max A₀ 0) ^ 2) := by
    intro x
    refine ⟨hUnn x, ?_⟩
    have h1 : v x ^ 2 ≤ (max M₀ 0) ^ 2 := by nlinarith [hv.nonneg x, hM x]
    have h2 : g x ^ 2 ≤ (max A₀ 0) ^ 2 := by nlinarith [hg0 x, hA x]
    show v x ^ 2 + g x ^ 2 ≤ _
    linarith
  have hUzero : ∀ x, x ∉ K → sqrtAddSq v g x = 0 := by
    intro x hx
    show v x ^ 2 + g x ^ 2 = 0
    rw [hv.eq_zero_of_notMem x hx, hgzero x hx]
    ring
  have hUmeas : AEStronglyMeasurable (sqrtAddSq v g) volume := hUmem.memLp.aestronglyMeasurable
  -- where `U` vanishes, so does the numerator of the gradient
  have hz0 : ∀ x, sqrtAddSq v g x = 0 → v x • weakGrad v x + g x • gradient g x = 0 := by
    intro x hx
    have hsum : v x ^ 2 + g x ^ 2 = 0 := hx
    have hv2 : v x ^ 2 = 0 := by nlinarith [sq_nonneg (v x), sq_nonneg (g x)]
    have hg2 : g x ^ 2 = 0 := by nlinarith [sq_nonneg (v x), sq_nonneg (g x)]
    rw [pow_eq_zero_iff two_ne_zero |>.1 hv2, pow_eq_zero_iff two_ne_zero |>.1 hg2,
      zero_smul, zero_smul, add_zero]
  -- the dominating function
  have hQnn : ∀ x, (0 : ℝ) ≤ Real.sqrt (‖weakGrad v x‖ ^ 2 + ‖gradient g x‖ ^ 2) := fun x =>
    Real.sqrt_nonneg _
  have hQmeas : AEStronglyMeasurable
      (fun x => Real.sqrt (‖weakGrad v x‖ ^ 2 + ‖gradient g x‖ ^ 2)) volume := by
    have h1 : AEStronglyMeasurable (fun x => ‖weakGrad v x‖ ^ 2) volume :=
      (hv.aestronglyMeasurable_grad.norm).pow 2
    have h2 : Continuous fun x => ‖gradient g x‖ ^ 2 := ((continuous_gradient hg1).norm).pow 2
    exact Real.continuous_sqrt.comp_aestronglyMeasurable (h1.add h2.aestronglyMeasurable)
  have hFmem : MemLp (fun x => ‖weakGrad v x‖ + ‖gradient g x‖) (ENNReal.ofReal 2) := by
    refine (hv.memW0.memLp_weakGrad.norm).add ?_
    exact ((continuous_gradient hg1).memLp_of_hasCompactSupport
      (hasCompactSupport_gradient hgs)).norm
  have hQmem : MemLp (fun x => Real.sqrt (‖weakGrad v x‖ ^ 2 + ‖gradient g x‖ ^ 2))
      (ENNReal.ofReal 2) := by
    refine hFmem.of_le hQmeas (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hQnn x),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖weakGrad v x‖ + ‖gradient g x‖)]
    refine le_trans (sqrt_add_le_add_sqrt (by positivity) (by positivity)) ?_
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- the approximating sequence
  obtain ⟨eps, hepsdef⟩ : ∃ e : ℕ → ℝ, e = fun n : ℕ => 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hepspos : ∀ n, 0 < eps n := fun n => by rw [hepsdef]; positivity
  have hepsle : ∀ n, eps n ≤ 1 := fun n => by
    rw [hepsdef]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by linarith)]
    linarith
  have hepslim : Tendsto eps atTop (𝓝 0) := by
    rw [hepsdef]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hsqrtepslim : Tendsto (fun n => Real.sqrt (eps n)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hepslim
    simpa [Function.comp_def] using h
  obtain ⟨wn, hwndef⟩ : ∃ w : ℕ → Euc d → ℝ,
      w = fun n x => Real.sqrt (sqrtAddSq v g x + eps n) - Real.sqrt (eps n) := ⟨_, rfl⟩
  obtain ⟨Gn, hGndef⟩ : ∃ G : ℕ → Euc d → Euc d,
      G = fun n x => (Real.sqrt (sqrtAddSq v g x + eps n))⁻¹ •
        (v x • weakGrad v x + g x • gradient g x) := ⟨_, rfl⟩
  have happrox : ∀ n, MemW0 2 K (wn n) ∧ HasWeakGradient (wn n) (Gn n) := by
    intro n
    obtain ⟨h1, h2⟩ := memW0_sqrt_add_const hUmem hSnn hUS (hepspos n)
    rw [hwndef]
    refine ⟨h1, ?_⟩
    have h3 : HasWeakGradient (fun x => Real.sqrt (sqrtAddSq v g x + eps n) - Real.sqrt (eps n))
        (fun x => (2 * Real.sqrt (sqrtAddSq v g x + eps n))⁻¹ • weakGrad (sqrtAddSq v g) x) :=
      h1.hasWeakGradient.congr_right h2
    refine h3.congr_right ?_
    filter_upwards [hUw.weakGrad_ae_eq] with x hx
    rw [hx, hGndef]
    exact inv_two_mul_smul_pair _ _ _ _ _
  -- `L²` membership of the limits
  have hwmeas : AEStronglyMeasurable (sqrtAdd v g) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hUmeas
  have hwmem : MemLp (sqrtAdd v g) (ENNReal.ofReal 2) := by
    refine memLp_two_of_bounded_of_support
      (B := Real.sqrt ((max M₀ 0) ^ 2 + (max A₀ 0) ^ 2)) hK hwmeas (fun x => ?_)
      (fun x hx => by rw [sqrtAdd, hUzero x hx, Real.sqrt_zero])
    rw [abs_of_nonneg (sqrtAdd_nonneg v g x)]
    exact Real.sqrt_le_sqrt (hUS x).2
  have hGwbd : ∀ x, ‖sqrtAddGrad v g x‖ ≤
      Real.sqrt (‖weakGrad v x‖ ^ 2 + ‖gradient g x‖ ^ 2) :=
    fun x => norm_inv_smul_pair_le (hv.nonneg x) (hg0 x) _ _ le_rfl
  have hGwmeas : AEStronglyMeasurable (sqrtAddGrad v g) volume := by
    have h1 : AEMeasurable (fun x => v x • weakGrad v x) volume :=
      hv.aestronglyMeasurable.aemeasurable.smul hv.aestronglyMeasurable_grad.aemeasurable
    have h2 : AEMeasurable (fun x => g x • gradient g x) volume :=
      hg.continuous.measurable.aemeasurable.smul
        (continuous_gradient hg1).measurable.aemeasurable
    exact ((hwmeas.aemeasurable.inv).smul (h1.add h2)).aestronglyMeasurable
  have hGwmem : MemLp (sqrtAddGrad v g) (ENNReal.ofReal 2) := by
    refine hQmem.of_le hGwmeas (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hQnn x)]
    exact hGwbd x
  have hGnbd : ∀ n x, ‖Gn n x‖ ≤ Real.sqrt (‖weakGrad v x‖ ^ 2 + ‖gradient g x‖ ^ 2) := by
    intro n x
    rw [hGndef]
    refine norm_inv_smul_pair_le (hv.nonneg x) (hg0 x) _ _ ?_
    have hUeq : sqrtAddSq v g x = v x ^ 2 + g x ^ 2 := rfl
    exact Real.sqrt_le_sqrt (by rw [hUeq] at *; linarith [(hepspos n).le])
  have hGnmeas : ∀ n, AEStronglyMeasurable (Gn n) volume := fun n =>
    (happrox n).2.locallyIntegrable_grad.aestronglyMeasurable
  -- the two `L²` limits
  have hlim1 : Tendsto (fun n => eLpNorm (wn n - sqrtAdd v g) (ENNReal.ofReal 2) volume)
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_of_dominated (p := 2) (by norm_num)
      (F := K.indicator fun _ => (1 : ℝ)) ?_ (fun n => ((happrox n).1.memLp.1).sub hwmeas)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · refine memLp_two_of_bounded_of_support (B := 1) hK
        (measurable_const.indicator hK.isOpen.measurableSet).aestronglyMeasurable
        (fun x => ?_) (fun x hx => Set.indicator_of_notMem hx _)
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]; norm_num
      · rw [Set.indicator_of_notMem hx]; norm_num
    · by_cases hx : x ∈ K
      · rw [Pi.sub_apply, hwndef, Real.norm_eq_abs, Real.norm_eq_abs,
          Set.indicator_of_mem hx, abs_one]
        refine le_trans ?_ (Real.sqrt_le_one.2 (hepsle n))
        exact abs_sqrt_add_sub_sqrt_le (hUnn x) (hepspos n).le
      · have hU0 : sqrtAddSq v g x = 0 := hUzero x hx
        have hw0 : sqrtAdd v g x = 0 := by rw [sqrtAdd, hU0, Real.sqrt_zero]
        rw [Pi.sub_apply, hwndef, hw0, Set.indicator_of_notMem hx]
        simp [hU0]
    · refine squeeze_zero_norm (fun n => ?_) hsqrtepslim
      rw [Pi.sub_apply, hwndef, Real.norm_eq_abs]
      exact abs_sqrt_add_sub_sqrt_le (hUnn x) (hepspos n).le
  have hlim2 : Tendsto (fun n => eLpNorm (Gn n - sqrtAddGrad v g) (ENNReal.ofReal 2) volume)
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_of_dominated (p := 2) (by norm_num)
      (F := fun x => 2 * Real.sqrt (‖weakGrad v x‖ ^ 2 + ‖gradient g x‖ ^ 2))
      (hQmem.const_mul 2) (fun n => (hGnmeas n).sub hGwmeas)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Pi.sub_apply, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (‖weakGrad v x‖ ^ 2 +
          ‖gradient g x‖ ^ 2))]
      refine le_trans (norm_sub_le _ _) ?_
      linarith [hGnbd n x, hGwbd x]
    · by_cases hx : sqrtAddSq v g x = 0
      · have hz := hz0 x hx
        have h1 : ∀ n, Gn n x = 0 := by
          intro n; rw [hGndef]; simp [hz]
        have h2 : sqrtAddGrad v g x = 0 := by rw [sqrtAddGrad]; simp [hz]
        simp [Pi.sub_apply, h1, h2]
      · have hUpos : 0 < sqrtAddSq v g x := lt_of_le_of_ne (hUnn x) (Ne.symm hx)
        have hsq : 0 < Real.sqrt (sqrtAddSq v g x) := Real.sqrt_pos.2 hUpos
        have h1 : Tendsto (fun n => sqrtAddSq v g x + eps n) atTop
            (𝓝 (sqrtAddSq v g x)) := by simpa using tendsto_const_nhds.add hepslim
        have h2 : Tendsto (fun n => Real.sqrt (sqrtAddSq v g x + eps n)) atTop
            (𝓝 (Real.sqrt (sqrtAddSq v g x))) := by
          simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto _).comp h1
        have h3 := (h2.inv₀ hsq.ne').smul_const (v x • weakGrad v x + g x • gradient g x)
        have h4 : Tendsto (fun n => Gn n x) atTop (𝓝 (sqrtAddGrad v g x)) := by
          rw [hGndef]
          exact h3
        simpa [Pi.sub_apply] using h4.sub_const (sqrtAddGrad v g x)
  have hmain : HasWeakGradient (sqrtAdd v g) (sqrtAddGrad v g) :=
    HasWeakGradient.of_tendsto (p := 2) one_lt_two (fun n => (happrox n).2) hwmem hGwmem
      hlim1 hlim2
  refine ⟨hmain, ⟨⟨hwmem, Eventually.of_forall fun x hx => ?_,
    ⟨sqrtAddGrad v g, hmain, hGwmem⟩⟩, sqrtAdd_nonneg v g, fun x hx => ?_,
    ⟨Real.sqrt ((max M₀ 0) ^ 2 + (max A₀ 0) ^ 2), fun x => Real.sqrt_le_sqrt (hUS x).2⟩⟩⟩
  · rw [sqrtAdd, hUzero x hx, Real.sqrt_zero]
  · rw [sqrtAdd, hUzero x hx, Real.sqrt_zero]

/-- The chosen weak gradient of the square-root competitor. -/
theorem weakGrad_sqrtAdd (hK : IsGoodConvex K) (hv : IsRegComp K v)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) (hgK : tsupport g ⊆ K)
    (hg0 : ∀ x, 0 ≤ g x) :
    weakGrad (sqrtAdd v g) =ᵐ[volume] sqrtAddGrad v g :=
  (hv.sqrtAdd_spec hK hg hgs hgK hg0).1.weakGrad_ae_eq

end Komlos.Literature.Regularized
