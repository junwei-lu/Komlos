import Komlos.Literature.Regularized.PositivityLocal
import Komlos.Literature.Regularized.DeGiorgiNash

/-!
# Lane `L2` (`reg/positivity`): the Caccioppoli toolkit

The ingredients of the De Giorgi class membership `isDG_of_regMinimizer`
(`Komlos/Literature/Regularized/PositivityDG.lean`), separated out because they are the
reusable half of that argument and because the boundary lemma
(`exists_boundary_sup_decay`) uses exactly the same competitor.

## Contents

* `posTrunc k u = (u - k)_+`, `levelInd k u = 1_{u > k}` and `memW0_posTrunc`: the truncation
  chain rule at a **nonnegative** level, where `memW0_posPart`'s shift `(-k)_+` vanishes, so
  that `(u-k)_+` itself (and not only a shifted version) lies in `W₀^{1,2}(K)`.
* `IsRegComp.truncCompetitor`: **the De Giorgi competitor** `w = u - η² (u-k)_+` for a smooth
  cutoff `η` with `0 ≤ η ≤ 1` supported in `K`.  It is again an `IsRegComp K` competitor —
  nonnegative because `u - (u-k)_+ = min(u, k) ≥ 0`, bounded by `u`, and supported in `K` —
  and its weak gradient is `(1 - η² 1_{u>k}) ∇u - (u-k)_+ ∇(η²)`.
* `setIntegral_le_of_integral_le_of_eq_off`: the localization of an inequality between two
  integrals to the set where the integrands differ.
* `le_of_holefilling`: the elementary **hole-filling iteration lemma** (Giaquinta,
  *Multiple Integrals in the Calculus of Variations*, Ch. V, Lemma 3.1; Giusti, *Direct
  Methods*, Lemma 6.1): if `f ρ ≤ θ f r + A (r - ρ)^{-2} + B` for all `ρ < r` in `[ρ₀, R]` with
  `θ < 1`, then `f ρ₀ ≤ c(θ) (A (R - ρ₀)^{-2} + B)`.  This is what removes the term
  `θ ∫_{B_s} ‖∇u‖²` that the Caccioppoli comparison leaves on the right-hand side.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### Truncation at a nonnegative level -/

/-- The truncation `(u - k)_+`. -/
noncomputable def posTrunc (k : ℝ) (u : Euc d → ℝ) : Euc d → ℝ := fun x => max (u x - k) 0

/-- The level indicator `1_{u > k}`, the factor appearing in `∇(u-k)_+ = 1_{u>k} ∇u`. -/
noncomputable def levelInd (k : ℝ) (u : Euc d → ℝ) : Euc d → ℝ :=
  fun x => if k < u x then (1 : ℝ) else 0

theorem posTrunc_nonneg (k : ℝ) (u : Euc d → ℝ) (x : Euc d) : 0 ≤ posTrunc k u x :=
  le_max_right _ _

theorem levelInd_nonneg (k : ℝ) (u : Euc d → ℝ) (x : Euc d) : 0 ≤ levelInd k u x := by
  rw [levelInd]; split <;> norm_num

theorem levelInd_le_one (k : ℝ) (u : Euc d → ℝ) (x : Euc d) : levelInd k u x ≤ 1 := by
  rw [levelInd]; split <;> norm_num

/-- At a nonnegative level the shift in `posPartShift` vanishes. -/
theorem posPartShift_eq_posTrunc {k : ℝ} (hk : 0 ≤ k) (u : Euc d → ℝ) (x : Euc d) :
    posPartShift k (u x) = posTrunc k u x := by
  rw [posPartShift, posTrunc, max_eq_right (neg_nonpos.2 hk), sub_zero]

/-- **The truncation chain rule at a nonnegative level**: `(u-k)_+ ∈ W₀^{1,2}(K)` with weak
gradient `1_{u>k} ∇u`. -/
theorem memW0_posTrunc {k : ℝ} (hk : 0 ≤ k) (hu : MemW0 2 K u) :
    MemW0 2 K (posTrunc k u) ∧
      HasWeakGradient (posTrunc k u) (fun x => levelInd k u x • weakGrad u x) := by
  obtain ⟨h1, h2⟩ := memW0_posPart (p := 2) one_lt_two hu k
  have heq : (fun x => posPartShift k (u x)) = posTrunc k u :=
    funext fun x => posPartShift_eq_posTrunc hk u x
  rw [heq] at h1 h2
  exact ⟨h1, h2⟩

/-! ### Squares of cutoffs -/

theorem tsupport_sq (η : Euc d → ℝ) : tsupport (fun x => η x ^ 2) = tsupport η := by
  have hs : (Function.support fun x => η x ^ 2) = Function.support η := by
    ext x
    simp [Function.mem_support]
  rw [tsupport, tsupport, hs]

/-! ### The De Giorgi competitor -/

/-- **The De Giorgi competitor** `w = u - ζ (u-k)_+` at a nonnegative level `k`, for a smooth
compactly supported cutoff `0 ≤ ζ ≤ 1`.

`w` lies again in the local competitor class `IsRegComp K`: it is nonnegative because
`ζ ≤ 1` and `u - (u-k)_+ = min(u,k) ≥ 0`, it is bounded above by `u`, and it vanishes off `K`
because both `u` and `(u-k)_+` do (here `k ≥ 0` is used — this is the only place the sign of the
level enters).  Its weak gradient is `∇u - ζ 1_{u>k} ∇u - (u-k)_+ ∇ζ`.

**No support condition on `ζ` is needed**: the product `ζ (u-k)_+` vanishes off `K` because
`(u-k)_+` does, so `MemW0.contDiff_mul` applies even when `tsupport ζ ⊄ K`.  This is what makes
the *boundary* Caccioppoli inequality (`BoundaryPositivity.lean`) available on balls that stick
out of `K`. -/
theorem IsRegComp.truncCompetitor (hcomp : IsRegComp K u) {k : ℝ} (hk : 0 ≤ k)
    {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ)
    (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) :
    IsRegComp K (fun x => u x - ζ x * posTrunc k u x) ∧
      weakGrad (fun x => u x - ζ x * posTrunc k u x) =ᵐ[volume]
        fun x => weakGrad u x - (ζ x * levelInd k u x) • weakGrad u x
          - posTrunc k u x • gradient ζ x := by
  classical
  obtain ⟨hT, hTg⟩ := memW0_posTrunc hk hcomp.memW0
  obtain ⟨Bg, hBg⟩ := (continuous_gradient (hζ.of_le (by simp))).bounded_above_of_compact_support
    (hasCompactSupport_gradient hζs)
  obtain ⟨hP, hPg⟩ := hT.contDiff_mul hζ (A := 1) (B := Bg)
    (fun x => by rw [abs_of_nonneg (hζ0 x)]; exact hζ1 x) hBg
  -- the weak gradient of `ζ (u-k)_+`
  have hPweak : HasWeakGradient (fun x => ζ x * posTrunc k u x)
      (fun x => ζ x • (levelInd k u x • weakGrad u x) +
        posTrunc k u x • gradient ζ x) := by
    refine (hP.hasWeakGradient.congr_right ?_)
    filter_upwards [hPg, hTg.weakGrad_ae_eq] with x h1 h2
    rw [h1, h2]
  -- the competitor itself
  have hmem : MemW0 2 K (fun x => u x - ζ x * posTrunc k u x) := by
    have hsum := hcomp.memW0.add (hP.smul (-1 : ℝ))
    have heq : (u + (-1 : ℝ) • fun x => ζ x * posTrunc k u x) =
        fun x => u x - ζ x * posTrunc k u x := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rwa [heq] at hsum
  have hweak : HasWeakGradient (fun x => u x - ζ x * posTrunc k u x)
      (fun x => weakGrad u x - (ζ x * levelInd k u x) • weakGrad u x
        - posTrunc k u x • gradient ζ x) := by
    have hsum := hcomp.memW0.hasWeakGradient.add (hPweak.smul (-1 : ℝ))
    refine (hsum.congr_left (Eventually.of_forall fun x => ?_)).congr_right
      (Eventually.of_forall fun x => ?_)
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_smul]
      rw [smul_add]
      module
  -- the pointwise bounds
  have hTle : ∀ x, ζ x * posTrunc k u x ≤ posTrunc k u x := by
    intro x
    nlinarith [posTrunc_nonneg k u x, hζ0 x, hζ1 x]
  have hTnn : ∀ x, 0 ≤ ζ x * posTrunc k u x := fun x =>
    mul_nonneg (hζ0 x) (posTrunc_nonneg k u x)
  have hnn : ∀ x, 0 ≤ u x - ζ x * posTrunc k u x := by
    intro x
    have hsub : 0 ≤ u x - posTrunc k u x := by
      rcases le_or_gt (u x) k with h | h
      · rw [posTrunc, max_eq_right (by linarith)]
        simpa using hcomp.nonneg x
      · rw [posTrunc, max_eq_left (by linarith)]
        linarith
    linarith [hTle x]
  obtain ⟨M, hM⟩ := hcomp.exists_le
  refine ⟨⟨hmem, hnn, fun x hx => ?_, ⟨M, fun x => ?_⟩⟩, hweak.weakGrad_ae_eq⟩
  · have hu0 : u x = 0 := hcomp.eq_zero_of_notMem x hx
    rw [hu0, posTrunc, hu0, max_eq_right (by linarith)]
    ring
  · linarith [hTnn x, hM x]

/-! ### Truncation from above and the super competitor -/

/-- The truncation from above, `(l - u)_+`. -/
noncomputable def negTrunc (l : ℝ) (u : Euc d → ℝ) : Euc d → ℝ := fun x => max (l - u x) 0

/-- The level indicator `1_{u < l}`, the factor in `∇(l-u)_+ = -1_{u<l} ∇u`. -/
noncomputable def levelIndLt (l : ℝ) (u : Euc d → ℝ) : Euc d → ℝ :=
  fun x => if u x < l then (1 : ℝ) else 0

theorem negTrunc_nonneg (l : ℝ) (u : Euc d → ℝ) (x : Euc d) : 0 ≤ negTrunc l u x :=
  le_max_right _ _

theorem levelIndLt_nonneg (l : ℝ) (u : Euc d → ℝ) (x : Euc d) : 0 ≤ levelIndLt l u x := by
  rw [levelIndLt]; split <;> norm_num

theorem levelIndLt_le_one (l : ℝ) (u : Euc d → ℝ) (x : Euc d) : levelIndLt l u x ≤ 1 := by
  rw [levelIndLt]; split <;> norm_num

/-- **The truncation chain rule from above**: `(l-u)_+ - l ∈ W₀^{1,2}(K)` (the shift by the
constant `l` is what makes it vanish off `K`) with weak gradient `-1_{u<l} ∇u`. -/
theorem memW0_negTrunc {l : ℝ} (hl : 0 ≤ l) (hu : MemW0 2 K u) :
    MemW0 2 K (fun x => negTrunc l u x - l) ∧
      HasWeakGradient (fun x => negTrunc l u x - l)
        (fun x => -(levelIndLt l u x • weakGrad u x)) := by
  classical
  have heneg : ((-1 : ℝ) • u) = fun x => -u x := by funext x; simp
  have hneg : MemW0 2 K (fun x => -u x) := by
    have h := hu.smul (-1 : ℝ)
    rwa [heneg] at h
  obtain ⟨h1, h2⟩ := memW0_posPart (p := 2) one_lt_two hneg (-l)
  have heqf : (fun x => posPartShift (-l) (-u x)) = fun x => negTrunc l u x - l := by
    funext x
    rw [posPartShift, negTrunc, neg_neg, max_eq_left hl]
    ring_nf
  have hgneg : weakGrad (fun x => -u x) =ᵐ[volume] fun x => -weakGrad u x := by
    have h := weakGrad_const_mul ⟨weakGrad u, hu.hasWeakGradient⟩ (-1 : ℝ)
    have he2 : (fun x => (-1 : ℝ) * u x) = fun x => -u x := by funext x; ring
    rw [he2] at h
    filter_upwards [h] with x hx
    rw [hx]
    module
  rw [heqf] at h1 h2
  refine ⟨h1, h2.congr_right ?_⟩
  filter_upwards [hgneg] with x hx
  rw [hx, levelIndLt]
  by_cases hlt : u x < l
  · rw [if_pos hlt, if_pos (by simpa using hlt)]
    module
  · rw [if_neg hlt, if_neg (by simpa using hlt)]
    module

/-- **The super competitor** `w = u + ζ (l-u)_+` at a nonnegative level `l`, for a smooth cutoff
`0 ≤ ζ ≤ 1` compactly supported **inside `K`**.

Unlike the sub competitor, the support condition `tsupport ζ ⊆ K` is essential here: `(l-u)_+`
equals the constant `l` off `K`, so `ζ (l-u)_+` only vanishes off `K` when `ζ` does.  `w` is
nonnegative, bounded by `max (u, l)`, vanishes off `K`, and has weak gradient
`∇u - ζ 1_{u<l} ∇u + (l-u)_+ ∇ζ`. -/
theorem IsRegComp.truncCompetitorSuper (hcomp : IsRegComp K u) {l : ℝ} (hl : 0 ≤ l)
    {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ) (hζK : tsupport ζ ⊆ K)
    (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) :
    IsRegComp K (fun x => u x + ζ x * negTrunc l u x) ∧
      weakGrad (fun x => u x + ζ x * negTrunc l u x) =ᵐ[volume]
        fun x => weakGrad u x - (ζ x * levelIndLt l u x) • weakGrad u x
          + negTrunc l u x • gradient ζ x := by
  classical
  obtain ⟨hT, hTg⟩ := memW0_negTrunc hl hcomp.memW0
  obtain ⟨hP, hPg⟩ := hT.contDiff_mul_const_add hζ hζs hζK l
  have hfun : (fun x => ζ x * (l + (negTrunc l u x - l))) =
      fun x => ζ x * negTrunc l u x := by
    funext x; ring_nf
  rw [hfun] at hP hPg
  have hPweak : HasWeakGradient (fun x => ζ x * negTrunc l u x)
      (fun x => -(ζ x • (levelIndLt l u x • weakGrad u x)) +
        negTrunc l u x • gradient ζ x) := by
    refine (hP.hasWeakGradient.congr_right ?_)
    filter_upwards [hPg, hTg.weakGrad_ae_eq] with x h1 h2
    rw [h1, h2]
    have : l + (negTrunc l u x - l) = negTrunc l u x := by ring
    rw [this, smul_neg]
  have hmem : MemW0 2 K (fun x => u x + ζ x * negTrunc l u x) := by
    have hsum := hcomp.memW0.add hP
    have heq : (u + fun x => ζ x * negTrunc l u x) =
        fun x => u x + ζ x * negTrunc l u x := by
      funext x; simp only [Pi.add_apply]
    rwa [heq] at hsum
  have hweak : HasWeakGradient (fun x => u x + ζ x * negTrunc l u x)
      (fun x => weakGrad u x - (ζ x * levelIndLt l u x) • weakGrad u x
        + negTrunc l u x • gradient ζ x) := by
    have hsum := hcomp.memW0.hasWeakGradient.add hPweak
    refine (hsum.congr_left (Eventually.of_forall fun x => ?_)).congr_right
      (Eventually.of_forall fun x => ?_)
    · simp only [Pi.add_apply]
    · simp only [Pi.add_apply, smul_smul]
      module
  -- the pointwise bounds
  have hTnn : ∀ x, 0 ≤ ζ x * negTrunc l u x := fun x =>
    mul_nonneg (hζ0 x) (negTrunc_nonneg l u x)
  have hnn : ∀ x, 0 ≤ u x + ζ x * negTrunc l u x := fun x => by
    linarith [hcomp.nonneg x, hTnn x]
  obtain ⟨M, hM⟩ := hcomp.exists_le
  refine ⟨⟨hmem, hnn, fun x hx => ?_, ⟨max M l, fun x => ?_⟩⟩, hweak.weakGrad_ae_eq⟩
  · have hζ0' : ζ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hζK h)
    rw [hcomp.eq_zero_of_notMem x hx, hζ0']
    ring
  · have h1 : ζ x * negTrunc l u x ≤ negTrunc l u x := by
      nlinarith [negTrunc_nonneg l u x, hζ0 x, hζ1 x]
    have h2 : u x + negTrunc l u x ≤ max M l := by
      rcases le_or_gt (u x) l with h | h
      · rw [negTrunc, max_eq_left (by linarith)]
        have : u x + (l - u x) = l := by ring
        rw [this]
        exact le_max_right _ _
      · rw [negTrunc, max_eq_right (by linarith)]
        have : u x + 0 = u x := by ring
        rw [this]
        exact (hM x).trans (le_max_left _ _)
    linarith

/-! ### Localizing an integral inequality -/

/-- If `∫ f ≤ ∫ g` and the two integrands agree off a measurable set `A`, then
`∫_A f ≤ ∫_A g`. -/
theorem setIntegral_le_of_integral_le_of_eq_off {A : Set (Euc d)} (hA : MeasurableSet A)
    {f g : Euc d → ℝ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hle : (∫ x, f x) ≤ ∫ x, g x) (hoff : ∀ᵐ x, x ∉ A → f x = g x) :
    (∫ x in A, f x) ≤ ∫ x in A, g x := by
  have h1 : ((∫ x in A, f x) + ∫ x in Aᶜ, f x) = ∫ x, f x := integral_add_compl hA hf
  have h2 : ((∫ x in A, g x) + ∫ x in Aᶜ, g x) = ∫ x, g x := integral_add_compl hA hg
  have h3 : (∫ x in Aᶜ, f x) = ∫ x in Aᶜ, g x := by
    refine setIntegral_congr_ae hA.compl ?_
    filter_upwards [hoff] with x hx hxA
    exact hx hxA
  linarith

/-! ### The energy comparison on a level set -/

/-- The lower-order part of the local energy density,
`L(s) = Ψ(0) s² + (κ/2) s² log s - Λ s²`.  The quadratic growth of the kinetic density
(`IsRegProfileWith.le_homogeneousDensity`, `.homogeneousDensity_le`) says exactly that the full
density is `L(s)` plus something between `(c/2)‖ξ‖²` and `(C/2)‖ξ‖²`. -/
noncomputable def regLow (κ Λ : ℝ) (Ψ : Euc d → ℝ) (s : ℝ) : ℝ :=
  Ψ 0 * s ^ 2 + Korevaar.entropyPotential 2 κ s - Λ * s ^ 2

theorem abs_regLow_le {κ Λ : ℝ} {Ψ : Euc d → ℝ} {Mbig s : ℝ} (hMbig : 1 ≤ Mbig)
    (hs0 : 0 ≤ s) (hsM : s ≤ Mbig) :
    |regLow κ Λ Ψ s| ≤ |Ψ 0| * Mbig ^ 2 +
      |κ| / 2 * (Mbig ^ 2 * Real.log Mbig + 1) + |Λ| * Mbig ^ 2 := by
  have hs2 : s ^ 2 ≤ Mbig ^ 2 := by nlinarith
  have h1 : |Ψ 0 * s ^ 2| ≤ |Ψ 0| * Mbig ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    exact mul_le_mul_of_nonneg_left hs2 (abs_nonneg _)
  have h2 : |Korevaar.entropyPotential 2 κ s| ≤ |κ| / 2 * (Mbig ^ 2 * Real.log Mbig + 1) := by
    rw [pos_entropyPotential_two, abs_mul]
    have habs2 : |κ / 2| = |κ| / 2 := by rw [abs_div]; norm_num
    rw [habs2]
    exact mul_le_mul_of_nonneg_left (pos_abs_sq_mul_log_le hs0 hsM hMbig) (by positivity)
  have h3 : |Λ * s ^ 2| ≤ |Λ| * Mbig ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    exact mul_le_mul_of_nonneg_left hs2 (abs_nonneg _)
  rw [regLow]
  calc |Ψ 0 * s ^ 2 + Korevaar.entropyPotential 2 κ s - Λ * s ^ 2|
      ≤ |Ψ 0 * s ^ 2 + Korevaar.entropyPotential 2 κ s| + |Λ * s ^ 2| := abs_sub _ _
    _ ≤ (|Ψ 0 * s ^ 2| + |Korevaar.entropyPotential 2 κ s|) + |Λ * s ^ 2| :=
        add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by linarith

/-- **The Caccioppoli comparison, in its raw form.**  If `w` is any competitor of the local
problem that agrees with the minimizer `u` (together with its gradient) off a set `S` of finite
measure, then the Dirichlet energies of `u` and `w` on `S` are comparable, with an additive error
proportional to `|S|`.

This is the only place where minimality is used in the De Giorgi class estimates: the value
`regFree κ Λ Ψ u ≤ regFree κ Λ Ψ w` (`IsRegMinimizer.regFree_le`) is localized to `S`
(`setIntegral_le_of_integral_le_of_eq_off`) and the two-sided quadratic growth of the density
converts it into an inequality between Dirichlet energies. -/
theorem exists_caccioppoli_core {κ : ℝ} (hκ : 0 < κ) {Ψ : Euc d → ℝ} {c C : ℝ}
    (hΨ : IsRegProfileWith Ψ c C) (hK : IsGoodConvex K)
    (hu : IsRegMinimizer 2 κ Ψ K u) (hucomp : IsRegComp K u) {Mbig : ℝ} (hMbig : 1 ≤ Mbig)
    (huM : ∀ x, u x ≤ Mbig) :
    ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∀ w : Euc d → ℝ, IsRegComp K w → (∀ x, w x ≤ Mbig) →
      ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
      (∀ᵐ x, x ∉ S → u x = w x) → (∀ᵐ x, x ∉ S → weakGrad u x = weakGrad w x) →
      c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
        C / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + B₁ * (volume S).toReal := by
  classical
  set Λ : ℝ := regMin 2 κ Ψ K + κ / 4 with hΛ
  set B₀ : ℝ := |Ψ 0| * Mbig ^ 2 + |κ| / 2 * (Mbig ^ 2 * Real.log Mbig + 1) + |Λ| * Mbig ^ 2
    with hB₀
  have hB₀0 : 0 ≤ B₀ := by
    have : (0:ℝ) ≤ Real.log Mbig := Real.log_nonneg hMbig
    have h1 : (0:ℝ) ≤ |Ψ 0| * Mbig ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ |κ| / 2 * (Mbig ^ 2 * Real.log Mbig + 1) := by positivity
    have h3 : (0:ℝ) ≤ |Λ| * Mbig ^ 2 := by positivity
    rw [hB₀]; linarith
  refine ⟨2 * B₀, by linarith, fun w hw hwM S hS hSfin hoffv hoffg => ?_⟩
  -- the two local energy densities
  set Fu : Euc d → ℝ := fun x => Korevaar.homogeneousDensity 2 Ψ (u x) (weakGrad u x) +
    Korevaar.entropyPotential 2 κ (u x) - Λ * u x ^ 2 with hFu
  set Fw : Euc d → ℝ := fun x => Korevaar.homogeneousDensity 2 Ψ (w x) (weakGrad w x) +
    Korevaar.entropyPotential 2 κ (w x) - Λ * w x ^ 2 with hFw
  have hFuInt : Integrable Fu volume :=
    ((hucomp.integrable_density hΨ).add (hucomp.integrable_entropy hK κ)).sub
      (hucomp.integrable_sq.const_mul Λ)
  have hFwInt : Integrable Fw volume :=
    ((hw.integrable_density hΨ).add (hw.integrable_entropy hK κ)).sub
      (hw.integrable_sq.const_mul Λ)
  -- the localized comparison
  have hle : (∫ x, Fu x) ≤ ∫ x, Fw x := hu.regFree_le hκ hΨ hK hucomp hw
  have hoffF : ∀ᵐ x, x ∉ S → Fu x = Fw x := by
    filter_upwards [hoffv, hoffg] with x h1 h2 hx
    rw [hFu, hFw]
    simp only []
    rw [h1 hx, h2 hx]
  have hlocal : (∫ x in S, Fu x) ≤ ∫ x in S, Fw x :=
    setIntegral_le_of_integral_le_of_eq_off hS hFuInt hFwInt hle hoffF
  -- the lower-order part is globally integrable and bounded on `S`
  have hLu : Integrable (fun x => regLow κ Λ Ψ (u x)) volume :=
    ((hucomp.integrable_sq.const_mul (Ψ 0)).add (hucomp.integrable_entropy hK κ)).sub
      (hucomp.integrable_sq.const_mul Λ)
  have hLw : Integrable (fun x => regLow κ Λ Ψ (w x)) volume :=
    ((hw.integrable_sq.const_mul (Ψ 0)).add (hw.integrable_entropy hK κ)).sub
      (hw.integrable_sq.const_mul Λ)
  have hcstInt : IntegrableOn (fun _ : Euc d => B₀) S volume := integrableOn_const hSfin
  have hcstInt' : IntegrableOn (fun _ : Euc d => -B₀) S volume := integrableOn_const hSfin
  -- the Dirichlet energies are integrable
  have hDu : IntegrableOn (fun x => ‖weakGrad u x‖ ^ 2) S volume :=
    hucomp.integrable_normSq_grad.integrableOn
  have hDw : IntegrableOn (fun x => ‖weakGrad w x‖ ^ 2) S volume :=
    hw.integrable_normSq_grad.integrableOn
  -- lower bound for `∫_S Fu`
  have hlow : c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) + (∫ x in S, regLow κ Λ Ψ (u x)) ≤
      ∫ x in S, Fu x := by
    have hptw : ∀ᵐ x ∂(volume.restrict S),
        c / 2 * ‖weakGrad u x‖ ^ 2 + regLow κ Λ Ψ (u x) ≤ Fu x := by
      refine ae_restrict_of_ae ?_
      filter_upwards [hucomp.weakGrad_eq_zero] with x hx
      have h := hΨ.le_homogeneousDensity (hucomp.nonneg x) hx
      rw [hFu, regLow]
      simp only []
      linarith
    have hIl : IntegrableOn (fun x => c / 2 * ‖weakGrad u x‖ ^ 2 + regLow κ Λ Ψ (u x))
        S volume := (hDu.const_mul _).add hLu.integrableOn
    have := integral_mono_ae hIl hFuInt.integrableOn hptw
    rwa [integral_add (hDu.const_mul _) hLu.integrableOn, integral_const_mul] at this
  -- upper bound for `∫_S Fw`
  have hup : (∫ x in S, Fw x) ≤
      C / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + ∫ x in S, regLow κ Λ Ψ (w x) := by
    have hptw : ∀ᵐ x ∂(volume.restrict S),
        Fw x ≤ C / 2 * ‖weakGrad w x‖ ^ 2 + regLow κ Λ Ψ (w x) := by
      refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
      have h := hΨ.homogeneousDensity_le (hw.nonneg x) (weakGrad w x)
      rw [hFw, regLow]
      simp only []
      linarith
    have hIu : IntegrableOn (fun x => C / 2 * ‖weakGrad w x‖ ^ 2 + regLow κ Λ Ψ (w x))
        S volume := (hDw.const_mul _).add hLw.integrableOn
    have := integral_mono_ae hFwInt.integrableOn hIu hptw
    rwa [integral_add (hDw.const_mul _) hLw.integrableOn, integral_const_mul] at this
  -- the bounds on the lower-order integrals
  have hLuS : -(B₀ * (volume S).toReal) ≤ ∫ x in S, regLow κ Λ Ψ (u x) := by
    have := integral_mono_ae hcstInt' hLu.integrableOn
      (ae_restrict_of_ae (Eventually.of_forall fun x =>
        neg_le_of_abs_le (abs_regLow_le hMbig (hucomp.nonneg x) (huM x))))
    rw [setIntegral_const] at this
    simpa [measureReal_def, neg_mul, mul_comm] using this
  have hLwS : (∫ x in S, regLow κ Λ Ψ (w x)) ≤ B₀ * (volume S).toReal := by
    have := integral_mono_ae hLw.integrableOn hcstInt
      (ae_restrict_of_ae (Eventually.of_forall fun x =>
        le_of_abs_le (abs_regLow_le hMbig (hw.nonneg x) (hwM x))))
    rw [setIntegral_const] at this
    simpa [measureReal_def, mul_comm] using this
  linarith


/-! ### The hole-filling iteration lemma -/

/-- **The hole-filling iteration lemma** (Giaquinta, *Multiple Integrals in the Calculus of
Variations*, Ch. V, Lemma 3.1; Giusti, *Direct Methods in the Calculus of Variations*,
Lemma 6.1).  If a bounded nonnegative `f` satisfies

`f ρ ≤ θ f r + A (r - ρ)⁻² + B`  for all `ρ₀ ≤ ρ < r ≤ R`

with `0 ≤ θ < 1`, then the term `θ f r` can be absorbed:

`f ρ₀ ≤ c(θ) (A (R - ρ₀)⁻² + B)`.

This is the step that turns the Caccioppoli comparison of `isDG_of_regMinimizer` — which, after
Young's inequality, only bounds `∫_{B_ρ} ‖∇u‖²` by `θ ∫_{B_r} ‖∇u‖²` plus the data — into the
De Giorgi class inequality, where no Dirichlet energy appears on the right.

Proof: iterate on the radii `t_i = ρ₀ + (1 - τ^i)(R - ρ₀)`, whose gaps are
`t_{i+1} - t_i = τ^i (1-τ)(R-ρ₀)`, with `τ = √((1+θ)/2)`, so that `q = θ/τ² = 2θ/(1+θ) < 1`.
Induction gives
`f ρ₀ ≤ θ^n f(t_n) + (∑_{i<n} q^i) A (1-τ)^{-2}(R-ρ₀)^{-2} + (∑_{i<n} θ^i) B`,
and `n → ∞` kills the first term (`f` is bounded) and sums the two geometric series. -/
theorem exists_holefilling_const {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ cc : ℝ, 0 ≤ cc ∧ ∀ (f : ℝ → ℝ) (ρ₀ R A B Mf : ℝ), ρ₀ < R → 0 ≤ A → 0 ≤ B →
      (∀ r, 0 ≤ f r) → (∀ r, f r ≤ Mf) →
      (∀ ρ r : ℝ, ρ₀ ≤ ρ → ρ < r → r ≤ R → f ρ ≤ θ * f r + A / (r - ρ) ^ 2 + B) →
      f ρ₀ ≤ cc * (A / (R - ρ₀) ^ 2 + B) := by
  -- the ratio `τ` with `θ < τ² < 1`
  set τ : ℝ := Real.sqrt ((1 + θ) / 2) with hτdef
  have hhalf : (0 : ℝ) < (1 + θ) / 2 := by linarith
  have hτpos : 0 < τ := Real.sqrt_pos.2 hhalf
  have hτsq : τ ^ 2 = (1 + θ) / 2 := Real.sq_sqrt hhalf.le
  have hτ1 : τ < 1 := by nlinarith [hτsq, hτpos]
  set q : ℝ := θ / τ ^ 2 with hqdef
  have hq0 : 0 ≤ q := div_nonneg hθ0 (by positivity)
  have hq1 : q < 1 := by
    rw [hqdef, hτsq, div_lt_one (by linarith)]
    linarith
  refine ⟨max (((1 - τ) ^ 2 * (1 - q))⁻¹) ((1 - θ)⁻¹), le_max_of_le_right (by positivity),
    fun f ρ₀ R A B Mf hρR hA hB hf0 hfM hstep => ?_⟩
  have hRρ : 0 < R - ρ₀ := by linarith
  have hτ1' : 0 < 1 - τ := by linarith
  set P : ℝ := A / ((1 - τ) ^ 2 * (R - ρ₀) ^ 2) with hPdef
  have hP0 : 0 ≤ P := by positivity
  -- the radii
  set t : ℕ → ℝ := fun i => ρ₀ + (1 - τ ^ i) * (R - ρ₀) with htdef
  have hτi0 : ∀ i : ℕ, 0 < τ ^ i := fun i => pow_pos hτpos i
  have hτi1 : ∀ i : ℕ, τ ^ i ≤ 1 := fun i => pow_le_one₀ hτpos.le hτ1.le
  have ht0 : t 0 = ρ₀ := by simp [htdef]
  have htlow : ∀ i, ρ₀ ≤ t i := fun i => by
    have := hτi1 i
    have : 0 ≤ (1 - τ ^ i) * (R - ρ₀) := mul_nonneg (by linarith) hRρ.le
    simp only [htdef]
    linarith
  have hthigh : ∀ i, t i ≤ R := fun i => by
    have h1 : 0 < τ ^ i := hτi0 i
    have : (1 - τ ^ i) * (R - ρ₀) ≤ R - ρ₀ := by nlinarith
    simp only [htdef]
    linarith
  have htgap : ∀ i, t (i + 1) - t i = τ ^ i * ((1 - τ) * (R - ρ₀)) := fun i => by
    simp only [htdef, pow_succ]
    ring
  have htlt : ∀ i, t i < t (i + 1) := fun i => by
    have h := htgap i
    have : 0 < τ ^ i * ((1 - τ) * (R - ρ₀)) := by positivity
    linarith
  -- the iteration
  have hiter : ∀ n : ℕ, f ρ₀ ≤ θ ^ n * f (t n) +
      (∑ i ∈ Finset.range n, q ^ i) * P + (∑ i ∈ Finset.range n, θ ^ i) * B := by
    intro n
    induction n with
    | zero => simp [ht0]
    | succ n ih =>
      have hstepn := hstep (t n) (t (n + 1)) (htlow n) (htlt n) (hthigh (n + 1))
      have hpow : (t (n + 1) - t n) ^ 2 =
          ((1 - τ) ^ 2 * (R - ρ₀) ^ 2) * (τ ^ 2) ^ n := by
        rw [htgap n]; ring
      have hgap : A / (t (n + 1) - t n) ^ 2 = ((τ ^ 2) ^ n)⁻¹ * P := by
        rw [hpow, hPdef, inv_mul_eq_div, div_div]
      have hθn : (0 : ℝ) ≤ θ ^ n := pow_nonneg hθ0 n
      have hmul : θ ^ n * f (t n) ≤
          θ ^ n * (θ * f (t (n + 1)) + A / (t (n + 1) - t n) ^ 2 + B) :=
        mul_le_mul_of_nonneg_left hstepn hθn
      have hqn : θ ^ n * (((τ ^ 2) ^ n)⁻¹ * P) = q ^ n * P := by
        rw [hqdef, div_pow, div_eq_mul_inv, mul_assoc]
      rw [hgap] at hmul
      have hsum1 : (∑ i ∈ Finset.range (n + 1), q ^ i) =
          (∑ i ∈ Finset.range n, q ^ i) + q ^ n := Finset.sum_range_succ _ _
      have hsum2 : (∑ i ∈ Finset.range (n + 1), θ ^ i) =
          (∑ i ∈ Finset.range n, θ ^ i) + θ ^ n := Finset.sum_range_succ _ _
      rw [hsum1, hsum2]
      have hexp : θ ^ n * (θ * f (t (n + 1)) + ((τ ^ 2) ^ n)⁻¹ * P + B) =
          θ ^ (n + 1) * f (t (n + 1)) + q ^ n * P + θ ^ n * B := by
        rw [← hqn]
        ring
      rw [hexp] at hmul
      nlinarith [ih, hmul]
  -- pass to the limit
  have hlim1 : Tendsto (fun n : ℕ => θ ^ n * Mf) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const Mf
    simpa using this
  have hlim2 : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, q ^ i) * P) atTop
      (𝓝 ((1 - q)⁻¹ * P)) :=
    ((hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat).mul_const P
  have hlim3 : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, θ ^ i) * B) atTop
      (𝓝 ((1 - θ)⁻¹ * B)) :=
    ((hasSum_geometric_of_lt_one hθ0 hθ1).tendsto_sum_nat).mul_const B
  have hlim : Tendsto (fun n : ℕ => θ ^ n * Mf +
      (∑ i ∈ Finset.range n, q ^ i) * P + (∑ i ∈ Finset.range n, θ ^ i) * B) atTop
      (𝓝 (0 + (1 - q)⁻¹ * P + (1 - θ)⁻¹ * B)) :=
    (hlim1.add hlim2).add hlim3
  have hkey : ∀ n : ℕ, f ρ₀ ≤ θ ^ n * Mf +
      (∑ i ∈ Finset.range n, q ^ i) * P + (∑ i ∈ Finset.range n, θ ^ i) * B := by
    intro n
    have hb : θ ^ n * f (t n) ≤ θ ^ n * Mf :=
      mul_le_mul_of_nonneg_left (hfM (t n)) (pow_nonneg hθ0 n)
    linarith [hiter n]
  have hbound : f ρ₀ ≤ (1 - q)⁻¹ * P + (1 - θ)⁻¹ * B := by
    have h := ge_of_tendsto hlim (Eventually.of_forall hkey)
    simpa using h
  -- and compare with the claimed constant
  have hPeq : (1 - q)⁻¹ * P = ((1 - τ) ^ 2 * (1 - q))⁻¹ * (A / (R - ρ₀) ^ 2) := by
    rw [hPdef]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have h1 : ((1 - τ) ^ 2 * (1 - q))⁻¹ ≤
      max (((1 - τ) ^ 2 * (1 - q))⁻¹) ((1 - θ)⁻¹) := le_max_left _ _
  have h2 : (1 - θ)⁻¹ ≤ max (((1 - τ) ^ 2 * (1 - q))⁻¹) ((1 - θ)⁻¹) := le_max_right _ _
  have hAq : 0 ≤ A / (R - ρ₀) ^ 2 := by positivity
  have hstep1 := mul_le_mul_of_nonneg_right h1 hAq
  have hstep2 := mul_le_mul_of_nonneg_right h2 hB
  calc f ρ₀ ≤ (1 - q)⁻¹ * P + (1 - θ)⁻¹ * B := hbound
    _ = ((1 - τ) ^ 2 * (1 - q))⁻¹ * (A / (R - ρ₀) ^ 2) + (1 - θ)⁻¹ * B := by rw [hPeq]
    _ ≤ max (((1 - τ) ^ 2 * (1 - q))⁻¹) ((1 - θ)⁻¹) * (A / (R - ρ₀) ^ 2) +
        max (((1 - τ) ^ 2 * (1 - q))⁻¹) ((1 - θ)⁻¹) * B := by linarith
    _ = max (((1 - τ) ^ 2 * (1 - q))⁻¹) ((1 - θ)⁻¹) * (A / (R - ρ₀) ^ 2 + B) := by ring


end Komlos.Literature.Regularized
