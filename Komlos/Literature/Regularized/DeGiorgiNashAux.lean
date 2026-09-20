import Komlos.Literature.PLaplacian.RegularityHolder

/-!
# Toolkit for the De Giorgi–Nash–Moser theory: truncations and cutoffs

Auxiliary material for `Komlos/Literature/Regularized/DeGiorgiClass.lean` (which imports this
file, so that the De Giorgi class estimates can be proved with this toolkit) and for
`Komlos/Literature/Regularized/DeGiorgiNash.lean`.

## Contents

* `softPos` — the `C^∞` approximation `softPos δ s = (s + √(s² + δ²))/2` of `max s 0`, and its
  calculus.  It is the device that produces the **truncation chain rule** without any
  fine-level-set theory: the repository's `memW0_comp` needs a `C¹` profile with bounded
  derivative, and `max (· - k) 0` is not `C¹`.
* `memW0_posPart` — **the truncation chain rule**: for `f ∈ W₀^{1,p}(K)` and a level `k`, the
  function `(f - k)_+ - (-k)_+` lies in `W₀^{1,p}(K)` with weak gradient `1_{f > k} ∇f`.  The
  shift by the constant `(-k)_+` is what makes the truncation vanish where `f` does, hence lie
  in `L^p`; consumers recover `(f - k)_+` by adding the constant back on a cutoff
  (`MemW0.contDiff_mul_const_add`).
  The approximation is `softPos δ (· - k - √δ)`, whose derivative tends to `1_{· > k}`
  *pointwise everywhere* — the shift `√δ ≫ δ` is what makes the limit of the derivative
  vanish, rather than equal `1/2`, at the level `· = k`.
* `exists_cutoff_const` — a smooth radial cutoff between two concentric balls of **arbitrary**
  radii `a < b`, with `‖∇η‖ ≤ C/(b-a)` for an absolute `C`.  The project's
  `exists_rescaled_cutoff` only produces cutoffs of a fixed radius *ratio*, which is not enough
  for the De Giorgi iteration (where the ratio tends to `1`).
* `memW0_two_mul_cutoff`, `integrable_of_bound_on_ball` — localization of a merely *locally*
  Sobolev function, and the integrability bookkeeping that goes with it.
* `caccioppoli_pointwise` — the four Young inequalities of the level-set Caccioppoli estimate.
* `degiorgi_fast_convergence`, `tendsto_zero_of_degiorgi_fast_convergence` — the kernel of the
  De Giorgi iteration: `Y (n+1) ≤ C bⁿ (Y n)^{1+α}` and `Y 0` small give `Y n → 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### Dominated convergence for `eLpNorm` -/

/-- **Dominated convergence in `L^p`**: if `‖h n‖ ≤ ‖F‖` with `F ∈ L^p` and `h n → 0` a.e., then
`‖h n‖_{L^p} → 0`.  (Mathlib's `tendsto_Lp_finite_of_tendsto_ae` assumes a finite measure.) -/
theorem tendsto_eLpNorm_of_dominated {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ} (hp0 : 0 < p) {h : ℕ → α → E} {F : α → ℝ}
    (hF : MemLp F (ENNReal.ofReal p) μ) (hhm : ∀ n, AEStronglyMeasurable (h n) μ)
    (hbd : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ ≤ ‖F x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (h n) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hfin : ∫⁻ x, ‖F x‖ₑ ^ p ∂μ ≠ ⊤ := by
    rw [lintegral_enorm_rpow_eq_eLpNorm_rpow hp0]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le hF.eLpNorm_ne_top
  have hdom : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ₑ ^ p ≤ ‖F x‖ₑ ^ p := by
    intro n
    filter_upwards [hbd n] with x hx
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx
  have hint : Tendsto (fun n => ∫⁻ x, ‖h n x‖ₑ ^ p ∂μ) atTop (𝓝 0) := by
    have h0 := tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0)
      (fun x => ‖F x‖ₑ ^ p) (fun n => ((hhm n).enorm.pow_const p)) hdom hfin ?_
    · simpa using h0
    · filter_upwards [hlim] with x hx
      have h2 : Tendsto (fun n => ‖h n x‖ₑ) atTop (𝓝 0) := by
        have h := (continuous_enorm.tendsto (0 : E)).comp hx
        rw [enorm_zero] at h
        exact h
      have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp0] using h3
  have h1 : Tendsto (fun n => (∫⁻ x, ‖h n x‖ₑ ^ p ∂μ) ^ (1 / p)) atTop (𝓝 0) := by
    have h2 := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0 |>.comp hint
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h2
  refine h1.congr fun n => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]

/-! ### The smoothed positive part -/

/-- `softPos δ s = (s + √(s² + δ²))/2`, a `C^∞` function with `0 ≤ (softPos δ)' ≤ 1` that
approximates `max s 0` uniformly to within `δ/2`. -/
noncomputable def softPos (δ s : ℝ) : ℝ := (s + Real.sqrt (s ^ 2 + δ ^ 2)) / 2

theorem abs_le_sqrt_sq_add_sq (δ s : ℝ) : |s| ≤ Real.sqrt (s ^ 2 + δ ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])

theorem sqrt_sq_add_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (s : ℝ) :
    Real.sqrt (s ^ 2 + δ ^ 2) ≤ |s| + δ := by
  have h : Real.sqrt (s ^ 2 + δ ^ 2) ≤ Real.sqrt ((|s| + δ) ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [abs_nonneg s, sq_abs s])
  rwa [Real.sqrt_sq (by positivity)] at h

theorem sqrt_sq_add_sq_pos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : 0 < Real.sqrt (s ^ 2 + δ ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

/-- The derivative of `softPos δ`. -/
theorem hasDerivAt_softPos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    HasDerivAt (softPos δ) ((1 + s / Real.sqrt (s ^ 2 + δ ^ 2)) / 2) s := by
  have hpos : (0 : ℝ) < s ^ 2 + δ ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + δ ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (δ ^ 2)
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + δ ^ 2))
      (2 * s / (2 * Real.sqrt (s ^ 2 + δ ^ 2))) s := h1.sqrt hpos.ne'
  have h3 : HasDerivAt (softPos δ) ((1 + 2 * s / (2 * Real.sqrt (s ^ 2 + δ ^ 2))) / 2) s :=
    ((hasDerivAt_id s).add h2).div_const 2
  have he : (1 : ℝ) + 2 * s / (2 * Real.sqrt (s ^ 2 + δ ^ 2)) =
      1 + s / Real.sqrt (s ^ 2 + δ ^ 2) := by
    rw [mul_div_mul_left _ _ (two_ne_zero)]
  rwa [he] at h3

theorem contDiff_softPos {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ 1 (softPos δ) := by
  have hsq : ContDiff ℝ 1 fun t : ℝ => t ^ 2 + δ ^ 2 :=
    (contDiff_id.pow 2).add contDiff_const
  have hs : ContDiff ℝ 1 fun t : ℝ => Real.sqrt (t ^ 2 + δ ^ 2) :=
    contDiff_iff_contDiffAt.2 fun t => hsq.contDiffAt.sqrt (by positivity)
  have h : ContDiff ℝ 1 (softPos δ) := (contDiff_id.add hs).div_const 2
  exact h

theorem deriv_softPos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    deriv (softPos δ) s = (1 + s / Real.sqrt (s ^ 2 + δ ^ 2)) / 2 :=
  (hasDerivAt_softPos hδ s).deriv

theorem deriv_softPos_mem {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    deriv (softPos δ) s ∈ Icc (0 : ℝ) 1 := by
  rw [deriv_softPos hδ]
  have h0 : 0 < Real.sqrt (s ^ 2 + δ ^ 2) := sqrt_sq_add_sq_pos hδ s
  have h1 : |s / Real.sqrt (s ^ 2 + δ ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos h0, div_le_one h0]
    exact abs_le_sqrt_sq_add_sq δ s
  rw [abs_le] at h1
  constructor <;> [linarith [h1.1]; linarith [h1.2]]

theorem abs_deriv_softPos_le {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : |deriv (softPos δ) s| ≤ 1 := by
  have h := deriv_softPos_mem hδ s
  rw [abs_le]
  exact ⟨by linarith [h.1], h.2⟩

/-- `softPos δ` approximates `max · 0` uniformly. -/
theorem abs_softPos_sub_max_le {δ : ℝ} (hδ : 0 ≤ δ) (s : ℝ) :
    |softPos δ s - max s 0| ≤ δ / 2 := by
  have hmax : max s 0 = (s + |s|) / 2 := by
    rcases le_total 0 s with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  have h1 := abs_le_sqrt_sq_add_sq δ s
  have h2 := sqrt_sq_add_sq_le hδ s
  rw [hmax, softPos, abs_le]
  constructor <;> [linarith; linarith]

/-- `softPos δ` is `1`-Lipschitz. -/
theorem abs_softPos_sub_softPos_le {δ : ℝ} (hδ : 0 < δ) (s t : ℝ) :
    |softPos δ s - softPos δ t| ≤ |s - t| := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := softPos δ) (fun x _ => (hasDerivAt_softPos hδ x).differentiableAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact abs_deriv_softPos_le hδ x)
    (mem_univ t) (mem_univ s)
  simpa only [Real.norm_eq_abs, one_mul] using h


/-- For `s < 0` the derivative of `softPos δ` is at most `δ/(2|s|)` — it tends to `0` away from
the origin, at a rate controlled by the distance to the origin. -/
theorem deriv_softPos_le_of_neg {δ s : ℝ} (hδ : 0 < δ) (hs : s < 0) :
    deriv (softPos δ) s ≤ δ / (2 * |s|) := by
  have h0 : 0 < Real.sqrt (s ^ 2 + δ ^ 2) := sqrt_sq_add_sq_pos hδ s
  have h1 : |s| ≤ Real.sqrt (s ^ 2 + δ ^ 2) := abs_le_sqrt_sq_add_sq δ s
  have h2 : Real.sqrt (s ^ 2 + δ ^ 2) ≤ |s| + δ := sqrt_sq_add_sq_le hδ.le s
  have habs : |s| = -s := abs_of_neg hs
  have hpos : 0 < |s| := abs_pos.2 hs.ne
  have key : (1 + s / Real.sqrt (s ^ 2 + δ ^ 2)) / 2 =
      (Real.sqrt (s ^ 2 + δ ^ 2) + s) / (2 * Real.sqrt (s ^ 2 + δ ^ 2)) := by
    field_simp
  rw [deriv_softPos hδ, key, div_le_div_iff₀ (by positivity) (by positivity)]
  have hA : Real.sqrt (s ^ 2 + δ ^ 2) + s ≤ δ := by rw [habs] at h2; linarith
  have hA0 : 0 ≤ Real.sqrt (s ^ 2 + δ ^ 2) + s := by rw [habs] at h1; linarith
  calc (Real.sqrt (s ^ 2 + δ ^ 2) + s) * (2 * |s|) ≤ δ * (2 * |s|) := by nlinarith
    _ ≤ δ * (2 * Real.sqrt (s ^ 2 + δ ^ 2)) := by nlinarith

/-- For `s > 0` the derivative of `softPos δ` is at least `1 - δ/(2 s)`. -/
theorem one_sub_deriv_softPos_le_of_pos {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    1 - deriv (softPos δ) s ≤ δ / (2 * s) := by
  have h0 : 0 < Real.sqrt (s ^ 2 + δ ^ 2) := sqrt_sq_add_sq_pos hδ s
  have h1 : |s| ≤ Real.sqrt (s ^ 2 + δ ^ 2) := abs_le_sqrt_sq_add_sq δ s
  have h2 : Real.sqrt (s ^ 2 + δ ^ 2) ≤ |s| + δ := sqrt_sq_add_sq_le hδ.le s
  have habs : |s| = s := abs_of_pos hs
  rw [habs] at h1 h2
  have key : 1 - (1 + s / Real.sqrt (s ^ 2 + δ ^ 2)) / 2 =
      (Real.sqrt (s ^ 2 + δ ^ 2) - s) / (2 * Real.sqrt (s ^ 2 + δ ^ 2)) := by
    field_simp
    ring
  rw [deriv_softPos hδ, key, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (Real.sqrt (s ^ 2 + δ ^ 2) - s) * (2 * s) ≤ δ * (2 * s) := by nlinarith
    _ ≤ δ * (2 * Real.sqrt (s ^ 2 + δ ^ 2)) := by nlinarith

/-! ### The truncation profile -/

/-- The shifted positive part `posPartShift k t = (t - k)_+ - (-k)_+`, normalized so that it
vanishes at `t = 0` (hence maps `L^p` functions to `L^p` functions). -/
noncomputable def posPartShift (k t : ℝ) : ℝ := max (t - k) 0 - max (-k) 0

/-- The `C^∞` approximation of `posPartShift k`: `softPos δ` at the *shifted* level
`k + √δ`.  The shift `√δ`, large compared with the smoothing width `δ`, is what makes the
derivative converge to `1_{t > k}` at *every* point, including `t = k` (where the unshifted
approximation would converge to `1/2`). -/
noncomputable def softPosShift (δ k t : ℝ) : ℝ :=
  softPos δ (t - (k + Real.sqrt δ)) - softPos δ (-(k + Real.sqrt δ))

theorem posPartShift_zero (k : ℝ) : posPartShift k 0 = 0 := by simp [posPartShift]

theorem abs_posPartShift_le (k t : ℝ) : |posPartShift k t| ≤ |t| := by
  have h := abs_max_sub_max_le_abs (t - k) (-k) 0
  simpa only [posPartShift, sub_neg_eq_add, sub_add_cancel] using h

theorem softPosShift_zero (δ k : ℝ) : softPosShift δ k 0 = 0 := by
  simp [softPosShift]

theorem contDiff_softPosShift {δ : ℝ} (hδ : 0 < δ) (k : ℝ) : ContDiff ℝ 1 (softPosShift δ k) :=
  ((contDiff_softPos hδ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const

theorem hasDerivAt_softPosShift {δ : ℝ} (hδ : 0 < δ) (k t : ℝ) :
    HasDerivAt (softPosShift δ k) (deriv (softPos δ) (t - (k + Real.sqrt δ))) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - (k + Real.sqrt δ)) 1 t :=
    (hasDerivAt_id t).sub_const _
  have h2 := (hasDerivAt_softPos hδ (t - (k + Real.sqrt δ))).comp t h1
  rw [mul_one] at h2
  have h3 : HasDerivAt (fun x : ℝ => softPos δ (x - (k + Real.sqrt δ)))
      (deriv (softPos δ) (t - (k + Real.sqrt δ))) t := by
    rw [deriv_softPos hδ]
    simpa only [Function.comp_def] using h2
  have h4 : HasDerivAt (softPosShift δ k) (deriv (softPos δ) (t - (k + Real.sqrt δ))) t :=
    h3.sub_const _
  exact h4

theorem deriv_softPosShift {δ : ℝ} (hδ : 0 < δ) (k t : ℝ) :
    deriv (softPosShift δ k) t = deriv (softPos δ) (t - (k + Real.sqrt δ)) :=
  (hasDerivAt_softPosShift hδ k t).deriv

theorem abs_deriv_softPosShift_le {δ : ℝ} (hδ : 0 < δ) (k t : ℝ) :
    |deriv (softPosShift δ k) t| ≤ 1 := by
  rw [deriv_softPosShift hδ]
  exact abs_deriv_softPos_le hδ _

theorem abs_softPosShift_le {δ : ℝ} (hδ : 0 < δ) (k t : ℝ) : |softPosShift δ k t| ≤ |t| := by
  have h := abs_softPos_sub_softPos_le hδ (t - (k + Real.sqrt δ)) (-(k + Real.sqrt δ))
  simpa only [softPosShift, sub_neg_eq_add, sub_add_cancel] using h

/-- The approximation error is uniform in `t`. -/
theorem abs_softPosShift_sub_posPartShift_le {δ : ℝ} (hδ : 0 < δ) (k t : ℝ) :
    |softPosShift δ k t - posPartShift k t| ≤ δ + 2 * Real.sqrt δ := by
  have ha : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have e1 := abs_softPos_sub_max_le hδ.le (t - (k + Real.sqrt δ))
  have e2 := abs_softPos_sub_max_le hδ.le (-(k + Real.sqrt δ))
  have e3 : |max (t - (k + Real.sqrt δ)) 0 - max (t - k) 0| ≤ Real.sqrt δ := by
    have h := abs_max_sub_max_le_abs (t - (k + Real.sqrt δ)) (t - k) 0
    refine h.trans (le_of_eq ?_)
    rw [show t - (k + Real.sqrt δ) - (t - k) = -Real.sqrt δ by ring, abs_neg, abs_of_nonneg ha]
  have e4 : |max (-(k + Real.sqrt δ)) 0 - max (-k) 0| ≤ Real.sqrt δ := by
    have h := abs_max_sub_max_le_abs (-(k + Real.sqrt δ)) (-k) 0
    refine h.trans (le_of_eq ?_)
    rw [show -(k + Real.sqrt δ) - -k = -Real.sqrt δ by ring, abs_neg, abs_of_nonneg ha]
  have key : softPosShift δ k t - posPartShift k t =
      (softPos δ (t - (k + Real.sqrt δ)) - max (t - (k + Real.sqrt δ)) 0) -
        (softPos δ (-(k + Real.sqrt δ)) - max (-(k + Real.sqrt δ)) 0) +
        ((max (t - (k + Real.sqrt δ)) 0 - max (t - k) 0) -
          (max (-(k + Real.sqrt δ)) 0 - max (-k) 0)) := by
    simp only [softPosShift, posPartShift]; ring
  rw [key]
  calc |_| ≤ |(softPos δ (t - (k + Real.sqrt δ)) - max (t - (k + Real.sqrt δ)) 0) -
        (softPos δ (-(k + Real.sqrt δ)) - max (-(k + Real.sqrt δ)) 0)| +
      |(max (t - (k + Real.sqrt δ)) 0 - max (t - k) 0) -
        (max (-(k + Real.sqrt δ)) 0 - max (-k) 0)| := abs_add_le _ _
    _ ≤ (δ / 2 + δ / 2) + (Real.sqrt δ + Real.sqrt δ) := by
        gcongr <;> [skip; skip] <;>
          exact (abs_sub _ _).trans (by first | exact add_le_add e1 e2 | exact add_le_add e3 e4)
    _ = δ + 2 * Real.sqrt δ := by ring


theorem continuous_posPartShift (k : ℝ) : Continuous (posPartShift k) :=
  ((continuous_id.sub continuous_const).max continuous_const).sub continuous_const

theorem continuous_deriv_softPosShift {δ : ℝ} (hδ : 0 < δ) (k : ℝ) :
    Continuous (deriv (softPosShift δ k)) :=
  (contDiff_softPosShift hδ k).continuous_deriv le_rfl

/-- The derivatives of the approximations converge to `1_{t > k}` at **every** point. -/
theorem tendsto_deriv_softPosShift {δ : ℕ → ℝ} (hδpos : ∀ n, 0 < δ n)
    (hδlim : Tendsto δ atTop (𝓝 0)) (k t : ℝ) :
    Tendsto (fun n => deriv (softPosShift (δ n) k) t) atTop
      (𝓝 (if k < t then (1 : ℝ) else 0)) := by
  have hsqlim : Tendsto (fun n => Real.sqrt (δ n)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hδlim
    simpa [Function.comp_def] using h
  have hsqpos : ∀ n, 0 < Real.sqrt (δ n) := fun n => Real.sqrt_pos.2 (hδpos n)
  simp only [deriv_softPosShift (hδpos _) k]
  by_cases hk : k < t
  · rw [if_pos hk]
    have he : 0 < t - k := by linarith
    -- eventually `t - (k + √δₙ) ≥ (t-k)/2 > 0`
    have hev : ∀ᶠ n in atTop, Real.sqrt (δ n) < (t - k) / 2 := by
      have := hsqlim.eventually (eventually_lt_nhds (by linarith : (0:ℝ) < (t - k) / 2))
      exact this
    have hupper : ∀ n, deriv (softPos (δ n)) (t - (k + Real.sqrt (δ n))) ≤ 1 :=
      fun n => (deriv_softPos_mem (hδpos n) _).2
    have hlower : ∀ᶠ n in atTop, 1 - δ n / (t - k) ≤
        deriv (softPos (δ n)) (t - (k + Real.sqrt (δ n))) := by
      filter_upwards [hev] with n hn
      have hs : (t - k) / 2 < t - (k + Real.sqrt (δ n)) := by linarith
      have hs0 : 0 < t - (k + Real.sqrt (δ n)) := by linarith
      have h1 := one_sub_deriv_softPos_le_of_pos (hδpos n) hs0
      have h2 : δ n / (2 * (t - (k + Real.sqrt (δ n)))) ≤ δ n / (t - k) := by
        apply div_le_div_of_nonneg_left (hδpos n).le he
        linarith
      linarith
    have hlim0 : Tendsto (fun n => 1 - δ n / (t - k)) atTop (𝓝 1) := by
      have := (hδlim.div_const (t - k)).const_sub (1 : ℝ)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim0 tendsto_const_nhds hlower
      (Eventually.of_forall hupper)
  · rw [if_neg hk]
    have ht : t ≤ k := not_lt.1 hk
    have hlower : ∀ n, (0 : ℝ) ≤ deriv (softPos (δ n)) (t - (k + Real.sqrt (δ n))) :=
      fun n => (deriv_softPos_mem (hδpos n) _).1
    have hupper : ∀ n, deriv (softPos (δ n)) (t - (k + Real.sqrt (δ n))) ≤
        Real.sqrt (δ n) / 2 := by
      intro n
      have hs : t - (k + Real.sqrt (δ n)) < 0 := by linarith [hsqpos n]
      have habs : Real.sqrt (δ n) ≤ |t - (k + Real.sqrt (δ n))| := by
        rw [abs_of_neg hs]
        linarith
      have h1 := deriv_softPos_le_of_neg (hδpos n) hs
      have h2 : δ n / (2 * |t - (k + Real.sqrt (δ n))|) ≤ δ n / (2 * Real.sqrt (δ n)) := by
        refine div_le_div_of_nonneg_left (hδpos n).le (by linarith [hsqpos n]) ?_
        linarith
      have h3 : δ n / (2 * Real.sqrt (δ n)) = Real.sqrt (δ n) / 2 := by
        rw [div_eq_div_iff (by linarith [hsqpos n] : (0:ℝ) < 2 * Real.sqrt (δ n)).ne'
          (two_ne_zero)]
        nlinarith [Real.mul_self_sqrt (hδpos n).le]
      rw [h3] at h2
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hsqlim.div_const 2) (fun n => hlower n) (fun n => hupper n)

/-! ### The truncation chain rule -/

/-- **Truncation chain rule in `W₀^{1,p}(K)`** (Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Lemma 7.6; Ziemer, *Weakly Differentiable Functions*, Theorem 2.1.11):
for `f ∈ W₀^{1,p}(K)` and a level `k`, the shifted truncation `(f - k)_+ - (-k)_+` lies in
`W₀^{1,p}(K)` and has weak gradient `1_{f > k} ∇f`.

Proof: `memW0_comp` applied to the `C^∞` profiles `softPosShift δ k`, whose derivatives converge
to `1_{· > k}` pointwise everywhere and whose values converge to `posPartShift k` uniformly, then
dominated convergence in `L^p` (`tendsto_eLpNorm_of_dominated`,
`tendsto_eLpNorm_smul_of_tendsto_ae`) and `HasWeakGradient.of_tendsto`. -/
theorem memW0_posPart {p : ℝ} (hp : 1 < p) {K : Set (Euc d)} {f : Euc d → ℝ} (hf : MemW0 p K f)
    (k : ℝ) :
    MemW0 p K (fun x => posPartShift k (f x)) ∧
      HasWeakGradient (fun x => posPartShift k (f x))
        (fun x => (if k < f x then (1 : ℝ) else 0) • weakGrad f x) := by
  have hp0 : 0 < p := by linarith
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsqlim : Tendsto (fun n => Real.sqrt (δ n)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hδlim
    simpa [Function.comp_def] using h
  set u : ℕ → Euc d → ℝ := fun n x => softPosShift (δ n) k (f x) with hudef
  set P : Euc d → ℝ := fun x => posPartShift k (f x) with hPdef
  set ind : Euc d → ℝ := fun x => if k < f x then (1 : ℝ) else 0 with hinddef
  set c : ℕ → Euc d → ℝ := fun n x => deriv (softPosShift (δ n) k) (f x) with hcdef
  have hfm : AEStronglyMeasurable f volume := hf.memLp.aestronglyMeasurable
  -- the approximations
  have hcomp : ∀ n, MemW0 p K (u n) ∧
      weakGrad (u n) =ᵐ[volume] fun x => c n x • weakGrad f x := fun n =>
    memW0_comp hp hf (contDiff_softPosShift (hδpos n) k) (softPosShift_zero _ _)
      (fun t => abs_deriv_softPosShift_le (hδpos n) k t)
  have hweak : ∀ n, HasWeakGradient (u n) (fun x => c n x • weakGrad f x) := fun n =>
    (hcomp n).1.hasWeakGradient.congr_right (hcomp n).2
  -- measurability
  have hum : ∀ n, AEStronglyMeasurable (u n) volume := fun n =>
    ((contDiff_softPosShift (hδpos n) k).continuous).comp_aestronglyMeasurable hfm
  have hcm : ∀ n, AEStronglyMeasurable (c n) volume := fun n =>
    (continuous_deriv_softPosShift (hδpos n) k).comp_aestronglyMeasurable hfm
  have hPm : AEStronglyMeasurable P volume :=
    (continuous_posPartShift k).comp_aestronglyMeasurable hfm
  -- pointwise limits
  have hcind : ∀ x, Tendsto (fun n => c n x) atTop (𝓝 (ind x)) := fun x =>
    tendsto_deriv_softPosShift hδpos hδlim k (f x)
  have hindm : AEStronglyMeasurable ind volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hcm (Eventually.of_forall hcind)
  have hval : ∀ x, Tendsto (fun n => u n x - P x) atTop (𝓝 0) := by
    intro x
    have hb : Tendsto (fun n => δ n + 2 * Real.sqrt (δ n)) atTop (𝓝 0) := by
      simpa using hδlim.add (hsqlim.const_mul 2)
    have hb' : Tendsto (fun n => -(δ n + 2 * Real.sqrt (δ n))) atTop (𝓝 0) := by
      simpa using hb.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hb' hb (fun n => ?_) (fun n => ?_)
    · have h := abs_softPosShift_sub_posPartShift_le (hδpos n) k (f x)
      rw [abs_le] at h
      exact h.1
    · have h := abs_softPosShift_sub_posPartShift_le (hδpos n) k (f x)
      rw [abs_le] at h
      exact h.2
  -- `L^p` bounds and limits
  have habs2 : ∀ n x, |u n x - P x| ≤ ‖2 * f x‖ := by
    intro n x
    have h1 := abs_softPosShift_le (hδpos n) k (f x)
    have h2 := abs_posPartShift_le k (f x)
    have : |u n x - P x| ≤ |u n x| + |P x| := abs_sub _ _
    rw [Real.norm_eq_abs, abs_mul]
    simp only [abs_two]
    linarith
  have hPmem : MemLp P (ENNReal.ofReal p) volume :=
    hf.memLp.of_le hPm (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact abs_posPartShift_le k (f x))
  have hgmem : MemLp (fun x => ind x • weakGrad f x) (ENNReal.ofReal p) volume := by
    refine hf.memLp_weakGrad.of_le (hindm.smul hf.memLp_weakGrad.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have : |ind x| ≤ 1 := by
      simp only [hinddef]
      split <;> simp
    calc |ind x| * ‖weakGrad f x‖ ≤ 1 * ‖weakGrad f x‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖weakGrad f x‖ := one_mul _
  have hvalLp : Tendsto (fun n => eLpNorm (u n - P) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_of_dominated hp0 (F := fun x => 2 * f x)
      (hf.memLp.const_mul 2) (fun n => (hum n).sub hPm) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => hval x)
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using habs2 n x
  have hgradLp : Tendsto (fun n => eLpNorm ((fun x => c n x • weakGrad f x) -
      fun x => ind x • weakGrad f x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    have hb : ∀ n x, |c n x - ind x| ≤ 2 := by
      intro n x
      have h1 : |c n x| ≤ 1 := abs_deriv_softPosShift_le (hδpos n) k (f x)
      have h2 : |ind x| ≤ 1 := by simp only [hinddef]; split <;> simp
      calc |c n x - ind x| ≤ |c n x| + |ind x| := abs_sub _ _
        _ ≤ 2 := by linarith
    have h := tendsto_eLpNorm_smul_of_tendsto_ae hp0 hf.memLp_weakGrad (L := 2)
      (h := fun n x => c n x - ind x) hb (fun n => (hcm n).sub hindm)
      (Eventually.of_forall fun x => by simpa using (hcind x).sub_const (ind x))
    refine h.congr fun n => ?_
    refine eLpNorm_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, sub_smul]
  have hG : HasWeakGradient P (fun x => ind x • weakGrad f x) :=
    HasWeakGradient.of_tendsto hp hweak hPmem hgmem hvalLp hgradLp
  refine ⟨⟨hPmem, ?_, ⟨_, hG, hgmem⟩⟩, hG⟩
  filter_upwards [hf.ae_eq_zero] with x hx hxK
  simp only [hPdef, hx hxK, posPartShift_zero]


/-! ### Smooth radial cutoffs between balls of arbitrary radii -/

theorem deriv_smoothTransition_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos hs.le
  rw [h.deriv_eq]
  simp

theorem deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le hs.le
  rw [h.deriv_eq]
  simp

/-- `Real.smoothTransition` has a globally bounded derivative. -/
theorem exists_bound_deriv_smoothTransition :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).continuousOn
  refine ⟨max C₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun t => ?_⟩
  have h1 : (0 : ℝ) ≤ max C₀ 1 := le_trans zero_le_one (le_max_right _ _)
  by_cases ht0 : t < 0
  · rw [deriv_smoothTransition_eq_zero_of_neg ht0, abs_zero]; exact h1
  by_cases ht1 : 1 < t
  · rw [deriv_smoothTransition_eq_zero_of_one_lt ht1, abs_zero]; exact h1
  · have h := hC₀ t ⟨not_lt.1 ht0, not_lt.1 ht1⟩
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)

theorem gradient_normSq (z : Euc d) : gradient (fun y : Euc d => ‖y‖ ^ 2) z = (2 : ℝ) • z := by
  refine ext_inner_right ℝ fun v => ?_
  rw [← fderiv_apply_eq_inner_gradient, fderiv_norm_sq_apply]
  simp [real_inner_smul_left]

theorem gradient_normSq_sub_const (x₀ x : Euc d) :
    gradient (fun y : Euc d => ‖y - x₀‖ ^ 2) x = (2 : ℝ) • (x - x₀) := by
  rw [gradient_comp_sub_const (f := fun y : Euc d => ‖y‖ ^ 2)
    ((contDiff_norm_sq (n := 1) ℝ).differentiable one_ne_zero) x₀ x, gradient_normSq]

/-- **A smooth radial cutoff between two concentric balls of arbitrary radii**: for every
`0 < a < b` there is `η ∈ C_c^∞` with `0 ≤ η ≤ 1`, `η = 1` on `closedBall x₀ a`,
`tsupport η ⊆ closedBall x₀ b` and `‖∇η‖ ≤ C/(b - a)` with an **absolute** constant `C`.

The project's `exists_rescaled_cutoff` only produces cutoffs whose two radii have a fixed
*ratio*; the De Giorgi iteration needs ratios tending to `1`.  The construction here is
`η = smoothTransition ((b² - ‖x - x₀‖²)/(b² - a²))`: the square of the distance is smooth
everywhere (no issue at the centre), and `b/(a + b) ≤ 1` converts the gradient bound
`2 b C₀/(b² - a²)` into `2 C₀/(b - a)`. -/
theorem exists_cutoff_const (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : Euc d) (a b : ℝ), 0 < a → a < b →
      ∃ η : Euc d → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
        tsupport η ⊆ Metric.closedBall x₀ b ∧ (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
        (∀ x ∈ Metric.closedBall x₀ a, η x = 1) ∧ ∀ x, ‖gradient η x‖ ≤ C / (b - a) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_bound_deriv_smoothTransition
  refine ⟨2 * C₀, by positivity, fun x₀ a b ha hab => ?_⟩
  have hb : 0 < b := ha.trans hab
  have hden : 0 < b ^ 2 - a ^ 2 := by nlinarith
  set q : Euc d → ℝ := fun y => ‖y - x₀‖ ^ 2 with hqdef
  set w : Euc d → ℝ := fun y => (b ^ 2 - a ^ 2)⁻¹ * (b ^ 2 - q y) with hwdef
  have hqC : ContDiff ℝ ∞ q := (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hwC : ContDiff ℝ ∞ w := by
    have h2 : ContDiff ℝ ∞ (fun y : Euc d => b ^ 2 - q y) := contDiff_const.sub hqC
    have h3 : ContDiff ℝ ∞ (fun y : Euc d => (b ^ 2 - a ^ 2)⁻¹ * (b ^ 2 - q y)) := by
      simpa only [smul_eq_mul] using h2.const_smul ((b ^ 2 - a ^ 2)⁻¹)
    exact h3
  have hq1 : ContDiff ℝ 1 q := hqC.of_le (by simp)
  have hqd : ∀ x, DifferentiableAt ℝ q x := fun x => hq1.differentiable one_ne_zero x
  have hw1 : ContDiff ℝ 1 w := hwC.of_le (by simp)
  have hwd : ∀ x, DifferentiableAt ℝ w x := fun x => hw1.differentiable one_ne_zero x
  set η : Euc d → ℝ := fun x => Real.smoothTransition (w x) with hηdef
  have hηC : ContDiff ℝ ∞ η := Real.smoothTransition.contDiff.comp hwC
  -- values
  have hη0 : ∀ x, 0 ≤ η x := fun x => Real.smoothTransition.nonneg _
  have hη1 : ∀ x, η x ≤ 1 := fun x => Real.smoothTransition.le_one _
  have hwneg : ∀ x, b < ‖x - x₀‖ → w x < 0 := by
    intro x hx
    have h1 : b ^ 2 < ‖x - x₀‖ ^ 2 := by nlinarith [norm_nonneg (x - x₀)]
    have : b ^ 2 - q x < 0 := by simp only [hqdef]; linarith
    simp only [hwdef]
    exact mul_neg_of_pos_of_neg (by positivity) this
  have hηone : ∀ x ∈ Metric.closedBall x₀ a, η x = 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    refine Real.smoothTransition.one_of_one_le ?_
    have h1 : ‖x - x₀‖ ^ 2 ≤ a ^ 2 := by nlinarith [norm_nonneg (x - x₀)]
    have h2 : b ^ 2 - a ^ 2 ≤ b ^ 2 - q x := by simp only [hqdef]; linarith
    simp only [hwdef]
    rw [inv_mul_eq_div, le_div_iff₀ hden, one_mul]
    linarith
  have hsupp : Function.support η ⊆ Metric.ball x₀ b := by
    intro x hx
    by_contra hb'
    rw [Metric.mem_ball, not_lt, dist_eq_norm] at hb'
    refine hx ?_
    show Real.smoothTransition (w x) = 0
    refine Real.smoothTransition.zero_of_nonpos ?_
    have h1 : b ^ 2 ≤ ‖x - x₀‖ ^ 2 := by nlinarith [norm_nonneg (x - x₀)]
    have h2 : b ^ 2 - q x ≤ 0 := by simp only [hqdef]; linarith
    simp only [hwdef]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h2
  have htsupp : tsupport η ⊆ Metric.closedBall x₀ b :=
    closure_minimal (hsupp.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  have hηs : HasCompactSupport η :=
    (isCompact_closedBall x₀ b).of_isClosed_subset (isClosed_tsupport _) htsupp
  -- the gradient
  have hgradw : ∀ x, gradient w x = (-(b ^ 2 - a ^ 2)⁻¹) • ((2 : ℝ) • (x - x₀)) := by
    intro x
    have h1 : HasFDerivAt w ((-(b ^ 2 - a ^ 2)⁻¹) • fderiv ℝ q x) x := by
      have h2 := ((hqd x).hasFDerivAt.const_sub (b ^ 2)).const_mul ((b ^ 2 - a ^ 2)⁻¹)
      rw [smul_neg, ← neg_smul] at h2
      exact h2
    rw [gradient_eq_smul_of_hasFDerivAt h1, gradient_normSq_sub_const]
  have hgrad : ∀ x, ‖gradient η x‖ ≤ 2 * C₀ / (b - a) := by
    intro x
    have hcomp : gradient η x = deriv Real.smoothTransition (w x) • gradient w x :=
      gradient_comp_apply
        ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero) (hwd x)
    have hnw : ‖gradient w x‖ = 2 * ‖x - x₀‖ / (b ^ 2 - a ^ 2) := by
      rw [hgradw x, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (b ^ 2 - a ^ 2)⁻¹)]
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      field_simp
    rw [hcomp, norm_smul, Real.norm_eq_abs, hnw]
    by_cases hx : b < ‖x - x₀‖
    · rw [deriv_smoothTransition_eq_zero_of_neg (hwneg x hx), abs_zero, zero_mul]
      positivity
    · have hxb : ‖x - x₀‖ ≤ b := not_lt.1 hx
      have hfac : 2 * ‖x - x₀‖ / (b ^ 2 - a ^ 2) ≤ 2 / (b - a) := by
        rw [div_le_div_iff₀ hden (by linarith)]
        nlinarith [norm_nonneg (x - x₀)]
      calc |deriv Real.smoothTransition (w x)| * (2 * ‖x - x₀‖ / (b ^ 2 - a ^ 2))
          ≤ C₀ * (2 / (b - a)) :=
            mul_le_mul (hC₀ _) hfac (by positivity) hC₀pos.le
        _ = 2 * C₀ / (b - a) := by ring
  exact ⟨η, hηC, hηs, htsupp, hη0, hη1, hηone, hgrad⟩


/-! ### Localization -/

theorem dgn_ofReal_two : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num

/-- `MemLp _ 2` from square-integrability on a set outside which the function vanishes. -/
theorem memLp_two_of_integrableOn_sq_norm {E : Type*} [NormedAddCommGroup E] {B : Set (Euc d)}
    {h : Euc d → E} (hm : AEStronglyMeasurable h volume)
    (hB : IntegrableOn (fun x => ‖h x‖ ^ 2) B volume) (hsupp : ∀ x, x ∉ B → h x = 0) :
    MemLp h (ENNReal.ofReal (2 : ℝ)) volume := by
  rw [dgn_ofReal_two]
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine hB.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  rw [hsupp x hx, norm_zero]
  norm_num

/-- **Localization**: if `G` is a weak gradient of `z` and both are square integrable on a set
`B`, then multiplying by a smooth cutoff `ζ` with `|ζ| ≤ 1` supported in `B` produces an element
of `W₀^{1,2}(B)` with the product-rule weak gradient. -/
theorem memW0_two_mul_cutoff {B : Set (Euc d)} {z : Euc d → ℝ} {G : Euc d → Euc d}
    (hzG : HasWeakGradient z G) (hzm : AEStronglyMeasurable z volume)
    (hGm : AEStronglyMeasurable G volume)
    (hz2 : IntegrableOn (fun x => z x ^ 2) B volume)
    (hG2 : IntegrableOn (fun x => ‖G x‖ ^ 2) B volume)
    {ζ : Euc d → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ) (hζB : tsupport ζ ⊆ B)
    (hζ1 : ∀ x, |ζ x| ≤ 1) :
    MemW0 2 B (fun x => ζ x * z x) ∧
      weakGrad (fun x => ζ x * z x) =ᵐ[volume]
        fun x => ζ x • G x + z x • gradient ζ x := by
  have hζ1' : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have hgζc : Continuous (gradient ζ) := continuous_gradient hζ1'
  obtain ⟨Bg, hBg⟩ := hgζc.bounded_above_of_compact_support (hasCompactSupport_gradient hζs)
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0)
  have hwg : HasWeakGradient (fun x => ζ x * z x)
      (fun x => ζ x • G x + z x • gradient ζ x) := hzG.contDiff_mul hζ
  have hζ0 : ∀ x, x ∉ B → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hζB h)
  have hgζ0 : ∀ x, x ∉ B → gradient ζ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport fun h => hx (hζB h)
  -- the function
  have hfm : AEStronglyMeasurable (fun x => ζ x * z x) volume :=
    hζ.continuous.aestronglyMeasurable.mul hzm
  have hf2 : IntegrableOn (fun x => ‖ζ x * z x‖ ^ 2) B volume := by
    refine Integrable.mono' hz2 ((hfm.norm.pow 2).restrict) (Eventually.of_forall fun x => ?_)
    have hz1 : ζ x ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hζ1 x)
    have h1 : ‖ζ x * z x‖ ^ 2 ≤ z x ^ 2 := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]
      nlinarith [sq_nonneg (z x)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h1
  have hfLp : MemLp (fun x => ζ x * z x) (ENNReal.ofReal (2 : ℝ)) volume :=
    memLp_two_of_integrableOn_sq_norm hfm hf2 fun x hx => by rw [hζ0 x hx, zero_mul]
  -- the gradient
  have hgm : AEStronglyMeasurable (fun x => ζ x • G x + z x • gradient ζ x) volume :=
    (hζ.continuous.aestronglyMeasurable.smul hGm).add
      (hzm.smul hgζc.aestronglyMeasurable)
  have hg2 : IntegrableOn (fun x => ‖ζ x • G x + z x • gradient ζ x‖ ^ 2) B volume := by
    refine Integrable.mono' ((hG2.const_mul 2).add (hz2.const_mul (2 * Bg ^ 2)))
      ((hgm.norm.pow 2).restrict) (Eventually.of_forall fun x => ?_)
    have h1 : ‖ζ x • G x + z x • gradient ζ x‖ ≤ ‖G x‖ + Bg * |z x| := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hζ1 x)
      · rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hBg x) (abs_nonneg _)
    have h2 : (‖G x‖ + Bg * |z x|) ^ 2 ≤ 2 * ‖G x‖ ^ 2 + 2 * Bg ^ 2 * z x ^ 2 := by
      nlinarith [sq_nonneg (‖G x‖ - Bg * |z x|), sq_abs (z x)]
    have h3 : ‖ζ x • G x + z x • gradient ζ x‖ ^ 2 ≤ (‖G x‖ + Bg * |z x|) ^ 2 := by
      nlinarith [norm_nonneg (ζ x • G x + z x • gradient ζ x), h1]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h3.trans h2
  have hgLp : MemLp (fun x => ζ x • G x + z x • gradient ζ x) (ENNReal.ofReal (2 : ℝ)) volume :=
    memLp_two_of_integrableOn_sq_norm hgm hg2 fun x hx => by
      rw [hζ0 x hx, hgζ0 x hx, zero_smul, smul_zero, add_zero]
  exact ⟨⟨hfLp, Eventually.of_forall fun x hx => by rw [hζ0 x hx, zero_mul], ⟨_, hwg, hgLp⟩⟩,
    hwg.weakGrad_ae_eq⟩


/-! ### The pointwise Young inequality of the Caccioppoli estimate -/

/-- **The arithmetic core of the level-set Caccioppoli estimate.**  With
`a = η(x) ∈ [0,1]`, `u = ‖G(x)‖`, `v = (z(x)-k)_+`, `q = ‖∇η(x)‖` and `t = s - r`, and with
`LHv`, `RHv` the two integrands of the weak inequality at a point where `z > k`, four
applications of Young's inequality give
`(λ/2) a²u² ≤ LHv - RHv + (4Λ²/λ + 1) v²q² + a²(v²/(2t²) + M²/λ + M² + N²t²/2)`. -/
theorem caccioppoli_pointwise {lam Lam M N a u v q t LHv RHv : ℝ}
    (hlam : 0 < lam) (_hLam : 0 ≤ Lam) (_hM : 0 ≤ M) (_hN : 0 ≤ N)
    (_ha0 : 0 ≤ a) (_hu : 0 ≤ u) (_hv : 0 ≤ v) (_hq : 0 ≤ q) (ht : 0 < t)
    (hLH : a ^ 2 * lam * u ^ 2 - 2 * a * v * Lam * u * q ≤ LHv)
    (hRH : RHv ≤ a ^ 2 * M * u + 2 * a * v * M * q + N * a ^ 2 * v) :
    lam / 2 * (a ^ 2 * u ^ 2) ≤ LHv - RHv +
      ((4 * Lam ^ 2 / lam + 1) * (v ^ 2 * q ^ 2) +
        a ^ 2 * (v ^ 2 / (2 * t ^ 2) + (M ^ 2 / lam + M ^ 2 + N ^ 2 * t ^ 2 / 2))) := by
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  -- (i) the ellipticity/flux cross term
  have y1 : 2 * a * v * Lam * u * q ≤
      lam / 4 * (a ^ 2 * u ^ 2) + 4 * Lam ^ 2 / lam * (v ^ 2 * q ^ 2) := by
    rw [← sub_nonneg]
    have key : lam / 4 * (a ^ 2 * u ^ 2) + 4 * Lam ^ 2 / lam * (v ^ 2 * q ^ 2) -
        2 * a * v * Lam * u * q = (lam / 2 * (a * u) - 2 * (Lam * v * q)) ^ 2 / lam := by
      field_simp
      ring
    rw [key]
    positivity
  -- (ii) the `f`-term against the gradient
  have y2 : a ^ 2 * M * u ≤ lam / 4 * (a ^ 2 * u ^ 2) + M ^ 2 / lam * a ^ 2 := by
    rw [← sub_nonneg]
    have key : lam / 4 * (a ^ 2 * u ^ 2) + M ^ 2 / lam * a ^ 2 - a ^ 2 * M * u =
        a ^ 2 * (lam / 2 * u - M) ^ 2 / lam := by
      field_simp
      ring
    rw [key]
    positivity
  -- (iii) the `f`-term against the cutoff gradient
  have y3 : 2 * a * v * M * q ≤ v ^ 2 * q ^ 2 + M ^ 2 * a ^ 2 := by
    nlinarith [sq_nonneg (v * q - M * a)]
  -- (iv) the `g`-term
  have y4 : N * a ^ 2 * v ≤ a ^ 2 * (v ^ 2 / (2 * t ^ 2)) + a ^ 2 * (N ^ 2 * t ^ 2 / 2) := by
    rw [← sub_nonneg]
    have key : a ^ 2 * (v ^ 2 / (2 * t ^ 2)) + a ^ 2 * (N ^ 2 * t ^ 2 / 2) - N * a ^ 2 * v =
        a ^ 2 * (v - N * t ^ 2) ^ 2 / (2 * t ^ 2) := by
      field_simp
      ring
    rw [key]
    positivity
  nlinarith [y1, y2, y3, y4, hLH, hRH]


/-- Integrability of a function supported in a ball and bounded there by
`c₁‖G‖² + c₂ z² + c₃`. -/
theorem integrable_of_bound_on_ball {x₀ : Euc d} {s : ℝ} {z : Euc d → ℝ} {G : Euc d → Euc d}
    (hz2 : IntegrableOn (fun x => z x ^ 2) (Metric.closedBall x₀ s) volume)
    (hG2 : IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ s) volume)
    {h : Euc d → ℝ} (hm : AEStronglyMeasurable h volume) (c₁ c₂ c₃ : ℝ)
    (hb : ∀ᵐ x, x ∈ Metric.closedBall x₀ s → ‖h x‖ ≤ c₁ * ‖G x‖ ^ 2 + c₂ * z x ^ 2 + c₃)
    (h0 : ∀ x, x ∉ Metric.closedBall x₀ s → h x = 0) : Integrable h volume := by
  have hconst : IntegrableOn (fun _ : Euc d => c₃) (Metric.closedBall x₀ s) volume :=
    integrableOn_const (C := c₃) measure_closedBall_lt_top.ne
  refine Integrable.mono' (g := (Metric.closedBall x₀ s).indicator
    (fun x => c₁ * ‖G x‖ ^ 2 + c₂ * z x ^ 2 + c₃)) ?_ hm ?_
  · rw [integrable_indicator_iff measurableSet_closedBall]
    exact ((hG2.const_mul c₁).add (hz2.const_mul c₂)).add hconst
  · filter_upwards [hb] with x hx
    by_cases hxB : x ∈ Metric.closedBall x₀ s
    · rw [Set.indicator_of_mem hxB]
      exact hx hxB
    · rw [Set.indicator_of_notMem hxB, h0 x hxB, norm_zero]


/-! ### De Giorgi's fast geometric convergence lemma -/

/-- **De Giorgi's fast geometric convergence lemma** (Ladyzhenskaya–Ural'tseva, Ch. II,
Lemma 4.7; Giusti, *Direct Methods in the Calculus of Variations*, Lemma 7.1): if a
nonnegative sequence satisfies `Y (n+1) ≤ C bⁿ (Y n)^{1+α}` with `C > 0`, `b > 1`, `α > 0`, and
the first term is small enough, `Y 0 ≤ C^{-1/α} b^{-1/α²}`, then `Y n ≤ Y 0 b^{-n/α}`, so
`Y n → 0`.

This is the kernel of the De Giorgi iteration: `Y n` is the energy `∫_{B_{r_n}} (z - k_n)_+²`
at the `n`-th level/radius pair, the smallness of `Y 0` is what fixes the height `H` of the
level ladder, and `Y n → 0` says `z ≤ k + H` a.e. on the inner ball. -/
theorem degiorgi_fast_convergence {Y : ℕ → ℝ} {Cst b α : ℝ}
    (hC : 0 < Cst) (hb : 1 < b) (hα : 0 < α) (hY : ∀ n, 0 ≤ Y n)
    (hstep : ∀ n : ℕ, Y (n + 1) ≤ Cst * b ^ (n : ℝ) * Y n ^ (1 + α))
    (hsmall : Y 0 ≤ Cst ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)) :
    ∀ n : ℕ, Y n ≤ Y 0 * b ^ (-(n : ℝ) / α) := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hne : α ≠ 0 := hα.ne'
  -- the smallness hypothesis in the form used by the induction
  have hkey : Cst * Y 0 ^ α ≤ b ^ (-α⁻¹) := by
    have h1 : Y 0 ^ α ≤ (Cst ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)) ^ α :=
      Real.rpow_le_rpow (hY 0) hsmall hα.le
    have h2 : (Cst ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)) ^ α = Cst⁻¹ * b ^ (-α⁻¹) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) (Real.rpow_nonneg hb0.le _),
        ← Real.rpow_mul hC.le, ← Real.rpow_mul hb0.le]
      have e1 : -α⁻¹ * α = -1 := by field_simp
      have e2 : -(α ^ 2)⁻¹ * α = -α⁻¹ := by field_simp; try ring
      rw [e1, e2, Real.rpow_neg_one]
    rw [h2] at h1
    calc Cst * Y 0 ^ α ≤ Cst * (Cst⁻¹ * b ^ (-α⁻¹)) := mul_le_mul_of_nonneg_left h1 hC.le
      _ = b ^ (-α⁻¹) := by field_simp
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : (0 : ℝ) < b ^ (-(n : ℝ) / α) := Real.rpow_pos_of_pos hb0 _
    have hY0n : 0 ≤ Y 0 * b ^ (-(n : ℝ) / α) := mul_nonneg (hY 0) hbn.le
    have h1 : Y n ^ (1 + α) ≤ (Y 0 * b ^ (-(n : ℝ) / α)) ^ (1 + α) :=
      Real.rpow_le_rpow (hY n) ih (by linarith)
    have h2 : (Y 0 * b ^ (-(n : ℝ) / α)) ^ (1 + α)
        = Y 0 ^ α * Y 0 * b ^ (-(n : ℝ) / α * (1 + α)) := by
      rw [Real.mul_rpow (hY 0) hbn.le, ← Real.rpow_mul hb0.le,
        Real.rpow_add' (hY 0) (by positivity), Real.rpow_one]
      ring
    have hpow : b ^ (n : ℝ) * b ^ (-(n : ℝ) / α * (1 + α)) = b ^ (-(n : ℝ) / α) := by
      rw [← Real.rpow_add hb0]
      congr 1
      field_simp
      try ring
    have h3 : Cst * b ^ (n : ℝ) * (Y 0 ^ α * Y 0 * b ^ (-(n : ℝ) / α * (1 + α)))
        = (Cst * Y 0 ^ α) * (Y 0 * (b ^ (n : ℝ) * b ^ (-(n : ℝ) / α * (1 + α)))) := by ring
    have h4 : Y (n + 1) ≤ (Cst * Y 0 ^ α) * (Y 0 * b ^ (-(n : ℝ) / α)) := by
      refine (hstep n).trans ?_
      have hmono : Cst * b ^ (n : ℝ) * Y n ^ (1 + α)
          ≤ Cst * b ^ (n : ℝ) * (Y 0 ^ α * Y 0 * b ^ (-(n : ℝ) / α * (1 + α))) :=
        mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2))
          (by positivity)
      rw [h3, hpow] at hmono
      exact hmono
    have hb1 : b ^ (-α⁻¹) * (Y 0 * b ^ (-(n : ℝ) / α))
        = Y 0 * (b ^ (-α⁻¹) * b ^ (-(n : ℝ) / α)) := by ring
    have hb2 : b ^ (-α⁻¹) * b ^ (-(n : ℝ) / α) = b ^ (-((n : ℝ) + 1) / α) := by
      rw [← Real.rpow_add hb0]
      congr 1
      field_simp
      try ring
    calc Y (n + 1) ≤ (Cst * Y 0 ^ α) * (Y 0 * b ^ (-(n : ℝ) / α)) := h4
      _ ≤ b ^ (-α⁻¹) * (Y 0 * b ^ (-(n : ℝ) / α)) := mul_le_mul_of_nonneg_right hkey hY0n
      _ = Y 0 * b ^ (-((n : ℝ) + 1) / α) := by rw [hb1, hb2]
      _ = Y 0 * b ^ (-((n + 1 : ℕ) : ℝ) / α) := by norm_num

/-- The conclusion of `degiorgi_fast_convergence` in the form actually used: `Y n → 0`. -/
theorem tendsto_zero_of_degiorgi_fast_convergence {Y : ℕ → ℝ} {Cst b α : ℝ}
    (hC : 0 < Cst) (hb : 1 < b) (hα : 0 < α) (hY : ∀ n, 0 ≤ Y n)
    (hstep : ∀ n : ℕ, Y (n + 1) ≤ Cst * b ^ (n : ℝ) * Y n ^ (1 + α))
    (hsmall : Y 0 ≤ Cst ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)) :
    Tendsto Y atTop (𝓝 0) := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hbound := degiorgi_fast_convergence hC hb hα hY hstep hsmall
  have hgeom : Tendsto (fun n : ℕ => Y 0 * b ^ (-(n : ℝ) / α)) atTop (𝓝 0) := by
    have hbi : |b ^ (-α⁻¹)| < 1 := by
      rw [abs_of_pos (Real.rpow_pos_of_pos hb0 _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg hb (by simp [hα])
    have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbi).const_mul (Y 0)
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    congr 1
    rw [← Real.rpow_natCast (b ^ (-α⁻¹)) n, ← Real.rpow_mul hb0.le]
    congr 1
    field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom
    (fun n => hY n) hbound


/-! ### Sobolev and Hölder on a ball -/

theorem enorm_rpow_two {E : Type*} [NormedAddCommGroup E] (a : E) :
    ‖a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖a‖ ^ 2) := by
  rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ← ofReal_norm,
    ENNReal.ofReal_pow (norm_nonneg a)]

theorem enorm_rpow_two_real (y : ℝ) : ‖y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (y ^ 2) := by
  rw [enorm_rpow_two, Real.norm_eq_abs, sq_abs]

/-- **Sobolev combined with Hölder on a ball**: with `κ > 1` the Sobolev exponent of
`Komlos.Literature.exists_sobolev_ball` at `p = 2` and `θ = 1 - 1/κ ∈ (0,1)`, for every
`v ∈ W₀^{1,2}(closedBall x₀ R)` and every set `S` of finite measure

`∫_S v² ≤ C R^{2 - dθ} (∫ ‖∇v‖²) |S|^θ`,

with `C` depending only on `d`.  This is exactly the combination the De Giorgi iteration
consumes: Sobolev raises the integrability exponent from `2` to `2κ`, Hölder brings it back
down on the (small) set `S` where the truncation lives, and the powers of `R` are the ones
that make the final bound scale-invariant. -/
theorem exists_sobolev_holder_ball (hd : 0 < d) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ CS : ℝ, 0 < CS ∧
      ∀ (x₀ : Euc d) (R : ℝ), 0 < R → ∀ v : Euc d → ℝ,
        MemW0 2 (Metric.closedBall x₀ R) v →
        ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
        (∫ x in S, v x ^ 2) ≤ CS * R ^ (2 - (d : ℝ) * θ) *
          (∫ x, ‖weakGrad v x‖ ^ 2) * (volume S).toReal ^ θ := by
  obtain ⟨κ, hκ, C, hC, hSob⟩ := exists_sobolev_ball hd (by norm_num : (1:ℝ) < 2)
  have hpq : Real.HolderConjugate κ (Real.conjExponent κ) :=
    Real.HolderConjugate.conjExponent hκ
  have hκ0 : (0:ℝ) < κ := by linarith
  have hq0 : (0:ℝ) < Real.conjExponent κ := hpq.symm.pos
  have hκi : (0:ℝ) < κ⁻¹ := by positivity
  refine ⟨(Real.conjExponent κ)⁻¹, by positivity, by
    have h := hpq.one_sub_inv; linarith, max ((C ^ κ⁻¹).toReal) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro x₀ R hR v hv S hSm hSfin
  set θ : ℝ := (Real.conjExponent κ)⁻¹ with hθdef
  have hθ0 : (0:ℝ) < θ := by rw [hθdef]; positivity
  have hθeq : θ = 1 - κ⁻¹ := hpq.one_sub_inv.symm
  have hR0 : (0:ℝ) ≤ R := hR.le
  set J : ℝ≥0∞ := ∫⁻ x, ‖weakGrad v x‖ₑ ^ (2:ℝ) with hJdef
  have hJtop : J ≠ ⊤ := by
    rw [hJdef, lintegral_enorm_rpow_eq_eLpNorm_rpow (by norm_num : (0:ℝ) < 2)]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hv.memLp_weakGrad.eLpNorm_ne_top
  have hvm : AEStronglyMeasurable v volume := hv.memLp.aestronglyMeasurable
  have hGm : AEStronglyMeasurable (weakGrad v) volume := hv.memLp_weakGrad.aestronglyMeasurable
  -- Hölder against the indicator of `S`
  have hfm : AEMeasurable (fun x => ‖v x‖ₑ ^ (2:ℝ)) volume := hvm.enorm.pow_const _
  have hgm : AEMeasurable (S.indicator (fun _ : Euc d => (1:ℝ≥0∞))) volume :=
    aemeasurable_const.indicator hSm
  have hmul : (fun x => ‖v x‖ₑ ^ (2:ℝ)) * S.indicator (fun _ : Euc d => (1:ℝ≥0∞))
      = S.indicator (fun x => ‖v x‖ₑ ^ (2:ℝ)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hfm hgm
  rw [hmul, lintegral_indicator hSm] at hholder
  have hgq : ∫⁻ x, (S.indicator (fun _ : Euc d => (1:ℝ≥0∞)) x) ^ Real.conjExponent κ
      = volume S := by
    have hpt : ∀ x, (S.indicator (fun _ : Euc d => (1:ℝ≥0∞)) x) ^ Real.conjExponent κ
        = S.indicator (fun _ : Euc d => (1:ℝ≥0∞)) x := by
      intro x
      by_cases hx : x ∈ S
      · simp [hx]
      · simp [hx, ENNReal.zero_rpow_of_pos hq0]
    rw [lintegral_congr hpt, lintegral_indicator hSm]
    simp
  rw [hgq] at hholder
  have hfκ : ∫⁻ x, (‖v x‖ₑ ^ (2:ℝ)) ^ κ = ∫⁻ x, ‖v x‖ₑ ^ (κ * 2) := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_mul, mul_comm]
  rw [hfκ] at hholder
  -- Sobolev
  have hbase : (0:ℝ) ≤ R ^ d * (R ^ (2:ℝ) * (R ^ d)⁻¹) ^ κ :=
    mul_nonneg (pow_nonneg hR0 d) (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hR0 2)
      (inv_nonneg.2 (pow_nonneg hR0 d))) κ)
  have hpow : (R ^ d * (R ^ (2:ℝ) * (R ^ d)⁻¹) ^ κ) ^ κ⁻¹ = R ^ (2 - (d:ℝ) * θ) := by
    rw [show R ^ d = R ^ ((d:ℕ) : ℝ) from (Real.rpow_natCast R d).symm,
      ← Real.rpow_neg hR0, ← Real.rpow_add hR, ← Real.rpow_mul hR0, ← Real.rpow_add hR,
      ← Real.rpow_mul hR0]
    congr 1
    rw [hθeq]
    field_simp
    ring
  have hconst : (C * ENNReal.ofReal (R ^ d * (R ^ (2:ℝ) * (R ^ d)⁻¹) ^ κ)) ^ κ⁻¹
      = C ^ κ⁻¹ * ENNReal.ofReal (R ^ (2 - (d:ℝ) * θ)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hκi.le,
      ENNReal.ofReal_rpow_of_nonneg hbase hκi.le, hpow]
  have hstep : (∫⁻ x, ‖v x‖ₑ ^ (κ * 2)) ^ (1 / κ) ≤
      C ^ κ⁻¹ * ENNReal.ofReal (R ^ (2 - (d:ℝ) * θ)) * J := by
    have h1 : (∫⁻ x, ‖v x‖ₑ ^ (κ * 2)) ^ (1 / κ) ≤
        (C * ENNReal.ofReal (R ^ d * (R ^ (2:ℝ) * (R ^ d)⁻¹) ^ κ) * J ^ κ) ^ (1 / κ) :=
      ENNReal.rpow_le_rpow (hSob x₀ R hR v hv) (by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / κ),
      ← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hκ0.ne', ENNReal.rpow_one, hconst]
  have hfinal : (∫⁻ x in S, ‖v x‖ₑ ^ (2:ℝ)) ≤
      C ^ κ⁻¹ * ENNReal.ofReal (R ^ (2 - (d:ℝ) * θ)) * J * volume S ^ θ := by
    have hvol : volume S ^ (1 / Real.conjExponent κ) = volume S ^ θ := by
      rw [hθdef, one_div]
    rw [hvol] at hholder
    exact hholder.trans (mul_le_mul' hstep le_rfl)
  -- transfer to real integrals
  have hXtop : C ^ κ⁻¹ * ENNReal.ofReal (R ^ (2 - (d:ℝ) * θ)) * J * volume S ^ θ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top)
      hJtop) (ENNReal.rpow_ne_top_of_nonneg hθ0.le hSfin)
    exact ENNReal.rpow_ne_top_of_nonneg hκi.le hC
  have hSint : (∫ x in S, v x ^ 2) = (∫⁻ x in S, ‖v x‖ₑ ^ (2:ℝ)).toReal := by
    rw [lintegral_congr fun x => enorm_rpow_two_real (v x)]
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      ((hvm.pow 2).restrict)
  have hGint : (∫ x, ‖weakGrad v x‖ ^ 2) = J.toReal := by
    rw [hJdef, lintegral_congr fun x => enorm_rpow_two (weakGrad v x)]
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      (hGm.norm.pow 2)
  rw [hSint, hGint]
  have htr := ENNReal.toReal_mono hXtop hfinal
  have hval : (C ^ κ⁻¹ * ENNReal.ofReal (R ^ (2 - (d:ℝ) * θ)) * J * volume S ^ θ).toReal
      = (C ^ κ⁻¹).toReal * R ^ (2 - (d:ℝ) * θ) * J.toReal * (volume S).toReal ^ θ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hR0 _), ENNReal.toReal_rpow]
  rw [hval] at htr
  refine htr.trans ?_
  have h1 : (0:ℝ) ≤ R ^ (2 - (d:ℝ) * θ) := Real.rpow_nonneg hR0 _
  have h2 : (0:ℝ) ≤ J.toReal := ENNReal.toReal_nonneg
  have h3 : (0:ℝ) ≤ (volume S).toReal ^ θ := Real.rpow_nonneg ENNReal.toReal_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) h1) h2) h3


/-! ### The truncation `η (z - k)_+` as a Sobolev test function -/

/-- **The De Giorgi test function.**  For `z` with weak gradient `G`, square integrable on
`closedBall x₀ R`, a cutoff `η` supported in `closedBall x₀ a` and a second cutoff `ζ` that is
`1` on `closedBall x₀ b` (`a < b ≤ R`) and supported in `closedBall x₀ R`, the truncation
`η (z - k)_+` lies in `W₀^{1,2}(closedBall x₀ R)` with weak gradient
`η 1_{z > k} G + (z-k)_+ ∇η`.

The second cutoff is what turns the merely *locally* Sobolev `z` into a global one
(`memW0_two_mul_cutoff`); it is invisible in the conclusion because `ζ ≡ 1` on a neighbourhood
of `tsupport η`. -/
theorem memW0_cutoff_posPart {x₀ : Euc d} {R a b : ℝ} (hab : a < b) (hbR : b ≤ R)
    {z : Euc d → ℝ} {G : Euc d → Euc d} (hzG : HasWeakGradient z G)
    (hzm : AEStronglyMeasurable z volume) (hGm : AEStronglyMeasurable G volume)
    (hz2 : IntegrableOn (fun x => z x ^ 2) (Metric.closedBall x₀ R) volume)
    (hG2 : IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall x₀ R) volume)
    {η ζ : Euc d → ℝ} (hηC : ContDiff ℝ ∞ η) (hηcs : HasCompactSupport η)
    (hηsupp : tsupport η ⊆ Metric.closedBall x₀ a)
    (hζC : ContDiff ℝ ∞ ζ) (hζcs : HasCompactSupport ζ)
    (hζsupp : tsupport ζ ⊆ Metric.closedBall x₀ R) (hζabs : ∀ x, |ζ x| ≤ 1)
    (hζone : ∀ x ∈ Metric.closedBall x₀ b, ζ x = 1) (k : ℝ) :
    MemW0 2 (Metric.closedBall x₀ R) (fun x => η x * max (z x - k) 0) ∧
      weakGrad (fun x => η x * max (z x - k) 0) =ᵐ[volume] fun x =>
        (η x * (if k < z x then (1:ℝ) else 0)) • G x + max (z x - k) 0 • gradient η x := by
  have haR : a ≤ R := le_trans hab.le hbR
  have hηR : tsupport η ⊆ Metric.closedBall x₀ R :=
    hηsupp.trans (Metric.closedBall_subset_closedBall haR)
  -- the localized function and its truncation
  obtain ⟨hZ, hZg⟩ := memW0_two_mul_cutoff hzG hzm hGm hz2 hG2 hζC hζcs hζsupp hζabs
  obtain ⟨hW, hWg⟩ := memW0_posPart (p := 2) one_lt_two hZ k
  obtain ⟨hψ, hψg⟩ := hW.contDiff_mul_const_add hηC hηcs hηR (max (-k) 0)
  -- behaviour on and off the support of `η`
  have hηzero : ∀ x, x ∉ tsupport η → η x = 0 ∧ gradient η x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx, gradient_eq_zero_of_notMem_tsupport hx⟩
  have hζat : ∀ x ∈ tsupport η, ζ x = 1 ∧ gradient ζ x = 0 := by
    intro x hx
    have hx1 : x ∈ Metric.closedBall x₀ a := hηsupp hx
    refine ⟨hζone x (Metric.closedBall_subset_closedBall hab.le hx1), ?_⟩
    have hxb : x ∈ Metric.ball x₀ b := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.1 hx1) hab
    have hev : ζ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with y hy
      exact hζone y (Metric.ball_subset_closedBall hy)
    have hfd : fderiv ℝ ζ x = 0 := by rw [hev.fderiv_eq]; simp
    refine ext_inner_right ℝ fun w => ?_
    rw [← fderiv_apply_eq_inner_gradient, hfd]
    simp
  -- the test function is `η (z-k)_+`
  have hval : (fun x => η x * (max (-k) 0 + posPartShift k (ζ x * z x)))
      = fun x => η x * max (z x - k) 0 := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [(hζat x hx).1, one_mul]
      simp only [posPartShift]
      ring
    · rw [(hηzero x hx).1]
      simp
  rw [hval] at hψ hψg
  refine ⟨hψ, ?_⟩
  filter_upwards [hψg, hW.hasWeakGradient.weakGrad_ae_eq.symm.trans hWg.weakGrad_ae_eq, hZg]
    with x hx hxW hxZ
  rw [hx]
  by_cases hxη : x ∈ tsupport η
  · obtain ⟨hζ1x, hζg0⟩ := hζat x hxη
    have hZx : ζ x * z x = z x := by rw [hζ1x, one_mul]
    have hWgx : weakGrad (fun y => posPartShift k (ζ y * z y)) x
        = (if k < z x then (1:ℝ) else 0) • G x := by
      rw [hxW, hZx, hxZ, hζ1x, hζg0, one_smul, smul_zero, add_zero]
    have hvalx : max (-k) 0 + posPartShift k (ζ x * z x) = max (z x - k) 0 := by
      rw [hZx]
      simp only [posPartShift]
      ring
    rw [hWgx, hvalx, smul_smul]
  · obtain ⟨hη0x, hηg0⟩ := hηzero x hxη
    simp [hη0x, hηg0]


/-- The algebraic identity that rescales the De Giorgi recursion: dividing by `R^m H²` turns
the step estimate into one with a constant free of `R` and `H`.  (Both sides are written as
products of powers of positive numbers, so the identity is checked by substituting
`x = exp (log x)` and comparing exponents.) -/
theorem dg_rescale_identity (n m : ℕ) {θ Cst R H Y : ℝ}
    (hCst : 0 < Cst) (hR : 0 < R) (hH : 0 < H) (hY : 0 < Y) :
    Cst * R ^ (2 - (m : ℝ) * θ) * (68 * 4 ^ n * Y / R ^ 2) *
        ((4:ℝ) ^ (n + 1) * Y / H ^ 2) ^ θ
      = 68 * 4 ^ θ * Cst * ((4:ℝ) ^ (1 + θ)) ^ (n : ℝ) *
        (Y / (R ^ m * H ^ 2)) ^ (1 + θ) * (R ^ m * H ^ 2) := by
  obtain ⟨r, rfl⟩ : ∃ r, R = Real.exp r := ⟨Real.log R, (Real.exp_log hR).symm⟩
  obtain ⟨h, rfl⟩ : ∃ h, H = Real.exp h := ⟨Real.log H, (Real.exp_log hH).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, Y = Real.exp y := ⟨Real.log Y, (Real.exp_log hY).symm⟩
  obtain ⟨c, rfl⟩ : ∃ c, Cst = Real.exp c := ⟨Real.log Cst, (Real.exp_log hCst).symm⟩
  rw [show (4:ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm,
    show (68:ℝ) = Real.exp (Real.log 68) from (Real.exp_log (by norm_num)).symm]
  simp only [div_eq_mul_inv, ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_neg,
    ← Real.exp_add]
  rw [Real.exp_eq_exp]
  push_cast
  ring

end Komlos.Literature.Regularized
