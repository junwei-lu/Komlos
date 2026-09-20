import Komlos.Literature.Regularized.DeGiorgiClass
import Komlos.Literature.Regularized.InteriorMorreyAux

/-!
# The De Giorgi class of the logarithmic solution (lane `L3a`, link 4)

The Stampacchia step of link 4: a continuous weak solution `v` of
`div ∇Ψ(∇v) = κ v + 2 m + B(∇v)` on `U` belongs, after being cut off so as to become globally
Sobolev and globally bounded, to a De Giorgi class `IsDG` of
`Komlos/Literature/Regularized/DeGiorgiClass.lean`.

The obstruction is the *natural growth* `|B(q)| ≤ 2 C ‖q‖² + 2 |Ψ 0|` of the right-hand side:
testing the equation with `η² (z - k)_+` produces a term `2 C ∫ η² ‖∇z‖² (z-k)_+` which cannot
be absorbed, because `(z-k)_+` is not small.  Stampacchia's device is to test instead with

`η² Q((z - k)_+)`,   `Q(t) = (e^{λ t} - 1)/λ`,   `λ = 4 C / c`,

so that the same term becomes `(2C/λ) ∫ η² e^{λ(z-k)_+} ‖∇z‖² = (c/2) ∫ η² Q'((z-k)_+) ‖∇z‖²`,
which *is* half of the principal part.

## Contents

* `exists_exp_profile` — the `C¹` profile with globally bounded derivative that agrees with the
  shifted exponential on the range of `posPartShift k ∘ z`.  As in
  `Komlos/Literature/Regularized/InteriorWeakEqLog.lean`, it is built as a primitive of a
  continuous bounded function, so no smooth gluing is needed.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {c C : ℝ} {Ψ : Euc d → ℝ}

/-! ### The truncated exponential profile -/

/-- **The Stampacchia profile.**  For `0 ≤ a ≤ T` there is a `C¹` function `R` with `R 0 = 0`
and `|R'| ≤ e^{λT}` globally, such that on the interval `[-a, T - a]`

* `R' t = e^{λ (t + a)}`, and
* `R t + (e^{λ a} - 1)/λ = (e^{λ (t+a)} - 1)/λ`.

It is applied with `t = posPartShift k (z x) = (z x - k)_+ - (-k)_+` and `a = (-k)_+`, so that
`R t + (e^{λa}-1)/λ = Q((z x - k)_+)` with `Q(u) = (e^{λ u} - 1)/λ`.  `R` is the primitive of
`s ↦ exp (λ · clamp (s + a))`, `clamp u = min (max u 0) T`. -/
theorem exists_exp_profile {lam a T : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (haT : a ≤ T) :
    ∃ R : ℝ → ℝ, ContDiff ℝ 1 R ∧ R 0 = 0 ∧
      (∀ t, |deriv R t| ≤ Real.exp (lam * T)) ∧
      (∀ t, -a ≤ t → t ≤ T - a → deriv R t = Real.exp (lam * (t + a))) ∧
      (∀ t, -a ≤ t → t ≤ T - a →
        R t + (Real.exp (lam * a) - 1) / lam = (Real.exp (lam * (t + a)) - 1) / lam) := by
  have hT : 0 ≤ T := ha.trans haT
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → ℝ, γ = fun s => Real.exp (lam * min (max (s + a) 0) T) := ⟨_, rfl⟩
  have hγc : Continuous γ := by
    rw [hγ]
    exact Real.continuous_exp.comp
      (continuous_const.mul (((continuous_id.add continuous_const).max
        continuous_const).min continuous_const))
  have hclamp : ∀ s : ℝ, min (max (s + a) 0) T ≤ T := fun s => min_le_right _ _
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = fun t => ∫ s in (0 : ℝ)..t, γ s := ⟨_, rfl⟩
  have hRd : ∀ t, HasDerivAt R (γ t) t := fun t => by
    rw [hR]
    exact intervalIntegral.integral_hasDerivAt_right (hγc.intervalIntegrable _ _)
      (hγc.stronglyMeasurableAtFilter _ _) hγc.continuousAt
  have hderiv : deriv R = γ := funext fun t => (hRd t).deriv
  have hRC : ContDiff ℝ 1 R :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hRd t).differentiableAt, by rw [hderiv]; exact hγc⟩
  have hR0 : R 0 = 0 := by rw [hR]; simp
  have hbound : ∀ t, |deriv R t| ≤ Real.exp (lam * T) := by
    intro t
    rw [hderiv, hγ]
    show |Real.exp (lam * min (max (t + a) 0) T)| ≤ Real.exp (lam * T)
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hclamp t) hlam.le)
  have hdv : ∀ t, -a ≤ t → t ≤ T - a → deriv R t = Real.exp (lam * (t + a)) := by
    intro t h1 h2
    rw [hderiv, hγ]
    show Real.exp (lam * min (max (t + a) 0) T) = Real.exp (lam * (t + a))
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  refine ⟨R, hRC, hR0, hbound, hdv, ?_⟩
  intro t h1 h2
  have hmem : ∀ s ∈ Set.uIcc (0 : ℝ) t, -a ≤ s ∧ s ≤ T - a := by
    intro s hs
    rcases le_total (0 : ℝ) t with ht | ht
    · rw [Set.uIcc_of_le ht] at hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · rw [Set.uIcc_of_ge ht] at hs
      exact ⟨by linarith [hs.1], by linarith [hs.2, haT, hT]⟩
  have hfd : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun u => Real.exp (lam * (u + a)) / lam) (Real.exp (lam * (s + a))) s := by
    intro s _
    have h : HasDerivAt (fun u : ℝ => lam * (u + a)) lam s := by
      simpa using ((hasDerivAt_id s).add_const a).const_mul lam
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (lam * (u + a)))
        (Real.exp (lam * (s + a)) * lam) s := (Real.hasDerivAt_exp _).comp s h
    have h3 := h2.div_const lam
    have h4 : Real.exp (lam * (s + a)) * lam / lam = Real.exp (lam * (s + a)) := by
      field_simp
    rwa [h4] at h3
  have hint : (∫ s in (0 : ℝ)..t, Real.exp (lam * (s + a))) =
      Real.exp (lam * (t + a)) / lam - Real.exp (lam * (0 + a)) / lam :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hfd
      ((Real.continuous_exp.comp (continuous_const.mul
        (continuous_id.add continuous_const))).intervalIntegrable _ _)
  have hcongr : (∫ s in (0 : ℝ)..t, γ s) = ∫ s in (0 : ℝ)..t, Real.exp (lam * (s + a)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := hmem s hs
    show γ s = Real.exp (lam * (s + a))
    rw [hγ]
    show Real.exp (lam * min (max (s + a) 0) T) = Real.exp (lam * (s + a))
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  have hRt : R t = Real.exp (lam * (t + a)) / lam - Real.exp (lam * a) / lam := by
    rw [hR]
    show (∫ s in (0 : ℝ)..t, γ s) = _
    rw [hcongr, hint]
    norm_num
  rw [hRt]
  field_simp
  try ring

/-! ### The Stampacchia test function -/

/-- **`η² Q((z-k)_+)` is a bounded `W₀^{1,2}` test function**, `Q u = (e^{λu} - 1)/λ`, with weak
gradient `η² Q'((z-k)_+) 1_{z>k} ∇z + Q((z-k)_+) ∇(η²)`.

The construction never leaves the repository's chain rules: `memW0_posPart` produces
`(z-k)_+` (up to the constant `(-k)_+`), `memW0_comp` composes with the `C¹` profile
`exists_exp_profile` (whose derivative is globally bounded, which is what `memW0_comp` needs),
and `MemW0.contDiff_mul_const_add` multiplies by the cutoff and restores the constant. -/
theorem exists_dg_testfn {lam : ℝ} (hlam : 0 < lam) {z : Euc d → ℝ} {K₀ : Set (Euc d)}
    (hzW : MemW0 2 K₀ z) {S : ℝ} (hS : ∀ x, |z x| ≤ S) {k : ℝ} (hk : -S - 1 ≤ k)
    {ζ : Euc d → ℝ} (hζC : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ) (hζK : tsupport ζ ⊆ K₀) :
    ∃ w : Euc d → ℝ,
      MemW0 2 K₀ w ∧
      (∀ x, w x = ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam)) ∧
      weakGrad w =ᵐ[volume] fun x =>
        (ζ x * (Real.exp (lam * max (z x - k) 0) *
          (if k < z x then (1 : ℝ) else 0))) • weakGrad z x +
          ((Real.exp (lam * max (z x - k) 0) - 1) / lam) • gradient ζ x := by
  have hS0 : 0 ≤ S := (abs_nonneg (z 0)).trans (hS 0)
  obtain ⟨a, hadef⟩ : ∃ t : ℝ, t = max (-k) 0 := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ t : ℝ, t = 2 * S + 1 := ⟨_, rfl⟩
  have ha : 0 ≤ a := by rw [hadef]; exact le_max_right _ _
  have haT : a ≤ T := by
    rw [hadef, hTdef]
    refine max_le ?_ (by linarith)
    linarith
  obtain ⟨R, hRC, hR0, hRb, hRdv, hRval⟩ := exists_exp_profile hlam ha haT
  obtain ⟨hhW, hhg⟩ := _root_.Komlos.Literature.Regularized.memW0_posPart one_lt_two hzW k
  obtain ⟨hRW, hRg⟩ := Komlos.Literature.memW0_comp one_lt_two hhW hRC hR0 hRb
  obtain ⟨cQ, hcQ⟩ : ∃ t : ℝ, t = (Real.exp (lam * a) - 1) / lam := ⟨_, rfl⟩
  obtain ⟨hwW, hwg⟩ := hRW.contDiff_mul_const_add hζC hζs hζK cQ
  -- the range of `posPartShift k ∘ z`
  have hrange : ∀ x, -a ≤ posPartShift k (z x) ∧
      posPartShift k (z x) ≤ T - a := by
    intro x
    have hzx := hS x
    rw [abs_le] at hzx
    have hpp : posPartShift k (z x) = max (z x - k) 0 - a := by
      rw [posPartShift, hadef]
    have h1 : (0 : ℝ) ≤ max (z x - k) 0 := le_max_right _ _
    have h2 : max (z x - k) 0 ≤ T := by
      rw [hTdef]
      refine max_le ?_ (by linarith)
      have : -k ≤ S + 1 := by linarith
      linarith [hzx.2]
    rw [hpp]
    constructor <;> linarith
  have hplus : ∀ x, posPartShift k (z x) + a = max (z x - k) 0 := by
    intro x
    rw [posPartShift, hadef]
    ring
  -- the value identity
  have hval : ∀ x, ζ x * (cQ + R (posPartShift k (z x))) =
      ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam) := by
    intro x
    obtain ⟨h1, h2⟩ := hrange x
    have h := hRval _ h1 h2
    rw [hplus x] at h
    rw [hcQ]
    congr 1
    linarith
  refine ⟨fun x => ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam), ?_, fun _ => rfl, ?_⟩
  · have heq : (fun x => ζ x * (cQ + R (posPartShift k (z x)))) =
        fun x => ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam) := funext hval
    exact heq ▸ hwW
  · have heq : (fun x => ζ x * (cQ + R (posPartShift k (z x)))) =
        fun x => ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam) := funext hval
    rw [← heq]
    filter_upwards [hwg, hRg, hhg.weakGrad_ae_eq] with x h1 h2 h3
    rw [h1, h2, h3]
    obtain ⟨hr1, hr2⟩ := hrange x
    rw [hRdv _ hr1 hr2, hplus x]
    have hvx : cQ + R (posPartShift k (z x)) =
        (Real.exp (lam * max (z x - k) 0) - 1) / lam := by
      have h := hRval _ hr1 hr2
      rw [hplus x] at h
      rw [hcQ]
      linarith
    rw [hvx]
    module


/-! ### The pointwise Stampacchia inequality -/

/-- **The pointwise inequality behind the Stampacchia–Caccioppoli estimate**, at a point where
`z > k`.  Here `ηx = η x`, `ex = e^{λ(z-k)_+}`, `qx = Q((z-k)_+)`, `tx = (z-k)_+`,
`nx = ∇(η²) x`, `Hx = ∇z x` and `fx` is the right-hand side.

The three terms of the tested equation are bounded below by ellipticity, by Young's inequality
(using `Q(t) ≤ t e^{λ T}`), and — this is Stampacchia's point — by the *exponential* absorption
`2 C Q(t) ≤ (2C/λ) e^{λ t} ≤ (c/2) e^{λ t}`, which is what turns the natural growth into half of
the principal part. -/
theorem dg_pointwise (hΨ : IsRegProfile Ψ) (hCΨ : IsRegProfileWith Ψ c C)
    {lam E Eprime A Kg ηx ex qx tx fx : ℝ} {Hx nx : Euc d}
    (hlam : 0 < lam) (hlamC : 4 * C ≤ lam * c) (hKg : 0 ≤ Kg)
    (hη0 : 0 ≤ ηx) (hη1 : ηx ≤ 1) (he1 : 1 ≤ ex) (hq0 : 0 ≤ qx) (hqE : qx ≤ Eprime)
    (hqt : qx ≤ tx * E) (hqlam : lam * qx ≤ ex) (_ht0 : 0 ≤ tx) (hA0 : 0 ≤ A) (_hE0 : 0 ≤ E)
    (hf : |fx| ≤ A + 2 * C * ‖Hx‖ ^ 2) (hn : ‖nx‖ ≤ 2 * ηx * Kg) :
    c / 4 * (ηx ^ 2 * ex * ‖Hx‖ ^ 2) - 4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 * tx ^ 2 - A * Eprime ≤
      ηx ^ 2 * ex * ⟪gradient Ψ Hx, Hx⟫ + qx * ⟪gradient Ψ Hx, nx⟫ + fx * (ηx ^ 2 * qx) := by
  have hc : 0 < c := hCΨ.c_pos
  have hC0 : 0 ≤ C := hCΨ.C_nonneg
  have hHn : (0:ℝ) ≤ ‖Hx‖ := norm_nonneg _
  have hex0 : (0:ℝ) ≤ ex := by linarith
  have hη2 : (0:ℝ) ≤ ηx ^ 2 := sq_nonneg _
  have hη2le : ηx ^ 2 ≤ 1 := by nlinarith [hη0, hη1]
  -- the principal part
  have hell : c * ‖Hx‖ ^ 2 ≤ ⟪gradient Ψ Hx, Hx⟫ := by
    have h := hCΨ.inner_gradient_sub Hx 0
    rw [hΨ.gradient_zero, sub_zero, sub_zero] at h
    exact h
  have hT1 : ηx ^ 2 * ex * (c * ‖Hx‖ ^ 2) ≤ ηx ^ 2 * ex * ⟪gradient Ψ Hx, Hx⟫ :=
    mul_le_mul_of_nonneg_left hell (by positivity)
  -- the cutoff term
  have hgrad : ‖gradient Ψ Hx‖ ≤ C * ‖Hx‖ := hCΨ.norm_gradient_le Hx
  have hcs : |⟪gradient Ψ Hx, nx⟫| ≤ ‖gradient Ψ Hx‖ * ‖nx‖ := abs_real_inner_le_norm _ _
  have hT2abs : |qx * ⟪gradient Ψ Hx, nx⟫| ≤ 2 * (ηx * ‖Hx‖) * (C * Kg * E * tx) := by
    rw [abs_mul, abs_of_nonneg hq0]
    calc qx * |⟪gradient Ψ Hx, nx⟫| ≤ qx * (C * ‖Hx‖ * (2 * ηx * Kg)) := by
          refine mul_le_mul_of_nonneg_left (hcs.trans ?_) hq0
          exact mul_le_mul hgrad hn (norm_nonneg _) (by positivity)
      _ ≤ (tx * E) * (C * ‖Hx‖ * (2 * ηx * Kg)) := by
          refine mul_le_mul_of_nonneg_right hqt ?_
          positivity
      _ = 2 * (ηx * ‖Hx‖) * (C * Kg * E * tx) := by ring
  have hyoung : 2 * (ηx * ‖Hx‖) * (C * Kg * E * tx) ≤
      c / 4 * (ηx * ‖Hx‖) ^ 2 + 4 / c * (C * Kg * E * tx) ^ 2 := by
    have hid : c / 4 * (ηx * ‖Hx‖) ^ 2 + 4 / c * (C * Kg * E * tx) ^ 2
        - 2 * (ηx * ‖Hx‖) * (C * Kg * E * tx)
        = (c * (ηx * ‖Hx‖) - 4 * (C * Kg * E * tx)) ^ 2 / (4 * c) := by
      field_simp
      ring
    have hnn : 0 ≤ (c * (ηx * ‖Hx‖) - 4 * (C * Kg * E * tx)) ^ 2 / (4 * c) :=
      div_nonneg (sq_nonneg _) (by linarith)
    linarith
  have hT2 : -(c / 4 * (ηx ^ 2 * ex * ‖Hx‖ ^ 2) +
      4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 * tx ^ 2) ≤ qx * ⟪gradient Ψ Hx, nx⟫ := by
    have habs := neg_abs_le (qx * ⟪gradient Ψ Hx, nx⟫)
    have hsq : c / 4 * (ηx * ‖Hx‖) ^ 2 ≤ c / 4 * (ηx ^ 2 * ex * ‖Hx‖ ^ 2) := by
      have h1 : (ηx * ‖Hx‖) ^ 2 = ηx ^ 2 * ‖Hx‖ ^ 2 := by ring
      have h2 : ηx ^ 2 * ‖Hx‖ ^ 2 ≤ ηx ^ 2 * ex * ‖Hx‖ ^ 2 := by
        have h3 : 0 ≤ ηx ^ 2 * ‖Hx‖ ^ 2 * (ex - 1) :=
          mul_nonneg (mul_nonneg hη2 (sq_nonneg _)) (by linarith)
        linarith
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
    have hE2 : 4 / c * (C * Kg * E * tx) ^ 2 = 4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 * tx ^ 2 := by
      ring
    linarith
  -- the natural-growth term
  have hAterm : A * (ηx ^ 2 * qx) ≤ A * Eprime := by
    refine mul_le_mul_of_nonneg_left ?_ hA0
    calc ηx ^ 2 * qx ≤ 1 * qx := mul_le_mul_of_nonneg_right hη2le hq0
      _ = qx := one_mul _
      _ ≤ Eprime := hqE
  have habs2 : 2 * C * qx ≤ c / 2 * ex := by
    rcases eq_or_lt_of_le hC0 with h0 | hCpos
    · rw [← h0]
      have : (0:ℝ) ≤ c / 2 * ex := by positivity
      linarith
    · have h1 : qx ≤ ex / lam := by
        rw [le_div_iff₀ hlam]
        linarith [hqlam]
      have h2 : 2 * C * qx ≤ 2 * C * (ex / lam) := by
        refine mul_le_mul_of_nonneg_left h1 (by linarith)
      have h3 : 2 * C * (ex / lam) ≤ c / 2 * ex := by
        rw [mul_div_assoc', div_le_iff₀ hlam]
        have h4 : 0 ≤ (lam * c - 4 * C) * ex := mul_nonneg (by linarith) hex0
        linarith
      linarith
  have hT3 : -(A * Eprime + c / 2 * (ηx ^ 2 * ex * ‖Hx‖ ^ 2)) ≤ fx * (ηx ^ 2 * qx) := by
    have habs := neg_abs_le (fx * (ηx ^ 2 * qx))
    have hbd : |fx * (ηx ^ 2 * qx)| ≤ A * Eprime + c / 2 * (ηx ^ 2 * ex * ‖Hx‖ ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ηx ^ 2 * qx)]
      have hstep : |fx| * (ηx ^ 2 * qx) ≤ (A + 2 * C * ‖Hx‖ ^ 2) * (ηx ^ 2 * qx) :=
        mul_le_mul_of_nonneg_right hf (by positivity)
      have hsplit : (A + 2 * C * ‖Hx‖ ^ 2) * (ηx ^ 2 * qx) =
          A * (ηx ^ 2 * qx) + (2 * C * qx) * (ηx ^ 2 * ‖Hx‖ ^ 2) := by ring
      have hlast : (2 * C * qx) * (ηx ^ 2 * ‖Hx‖ ^ 2) ≤
          c / 2 * (ηx ^ 2 * ex * ‖Hx‖ ^ 2) := by
        have h1 : (2 * C * qx) * (ηx ^ 2 * ‖Hx‖ ^ 2) ≤ (c / 2 * ex) * (ηx ^ 2 * ‖Hx‖ ^ 2) :=
          mul_le_mul_of_nonneg_right habs2 (by positivity)
        linarith [h1]
      linarith
    linarith
  linarith [hT1, hT2, hT3]


/-! ### The Stampacchia–Caccioppoli step -/

set_option maxHeartbeats 1000000 in
/-- **The Stampacchia–Caccioppoli estimate.**  Testing the weak equation with
`η² Q((z-k)_+)` and integrating the pointwise inequality `dg_pointwise` gives

`(c/4) ∫ η² e^{λ(z-k)_+} 1_{z>k} ‖∇z‖² ≤ (4/c) C² K² E² ∫_{B_s} ((z-k)_+)²
    + A ((E-1)/λ) |B_s ∩ {z > k}|`,

which is the level-set energy inequality of `IsDGSub`. -/
theorem dg_energy_step (hΨ : IsRegProfile Ψ) (hCΨ : IsRegProfileWith Ψ c C)
    {z : Euc d → ℝ} {H : Euc d → Euc d} {f : Euc d → ℝ} {K₀ : Set (Euc d)}
    (hzW : MemW0 2 K₀ z) (hzm : Measurable z) (hzH : weakGrad z =ᵐ[volume] H)
    (hHm : Measurable H) (hfm : Measurable f)
    {S : ℝ} (hS : ∀ x, |z x| ≤ S) {A : ℝ} (hA0 : 0 ≤ A)
    (hfbd : ∀ x, |f x| ≤ A + 2 * C * ‖H x‖ ^ 2)
    {lam Tb E Ep : ℝ} (hlam : 0 < lam) (hlamC : 4 * C ≤ lam * c)
    (hTbdef : Tb = 2 * S + 1) (hEdef : E = Real.exp (lam * Tb)) (hEpdef : Ep = (E - 1) / lam)
    {y : Euc d} {r s k : ℝ} (_hr : 0 < r) (hrs : r < s) (hk : -S - 1 ≤ k)
    {η : Euc d → ℝ} (hηC : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηsub : tsupport η ⊆ Metric.closedBall y ((r + s) / 2))
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hηone : ∀ x ∈ Metric.closedBall y r, η x = 1)
    {Kg : ℝ} (hKg0 : 0 ≤ Kg) (hηg : ∀ x, ‖gradient η x‖ ≤ Kg)
    (hTball : Metric.closedBall y s ⊆ K₀)
    (hH2 : IntegrableOn (fun x => ‖H x‖ ^ 2) (Metric.closedBall y s) volume)
    (hweak : ∀ w : Euc d → ℝ, MemW0 2 (Metric.closedBall y s) w →
      (∀ᵐ x, x ∉ Metric.closedBall y s → weakGrad w x = 0) →
      ∀ Mw : ℝ, (∀ x, |w x| ≤ Mw) →
      (∫ x, ⟪gradient Ψ (H x), weakGrad w x⟫) = -∫ x, f x * w x) :
    (∫ x in Metric.ball y r ∩ {x | k < z x}, ‖H x‖ ^ 2) ≤
      4 / c * (4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
          (∫ x in Metric.ball y s, max (z x - k) 0 ^ 2) +
        A * Ep * (volume (Metric.ball y s ∩ {x | k < z x})).toReal) := by
  have hc : 0 < c := hCΨ.c_pos
  have hC0 : 0 ≤ C := hCΨ.C_nonneg
  have hS0 : 0 ≤ S := (abs_nonneg (z 0)).trans (hS 0)
  have hTb0 : 0 ≤ Tb := by rw [hTbdef]; linarith
  have hE1 : 1 ≤ E := by rw [hEdef]; exact Real.one_le_exp (by positivity)
  have hE0 : (0:ℝ) ≤ E := by linarith
  have hEp0 : 0 ≤ Ep := by rw [hEpdef]; exact div_nonneg (by linarith) hlam.le
  have hη1' : ContDiff ℝ 1 η := hηC.of_le (by simp)
  -- ### elementary facts about the profile values
  have ht0 : ∀ x, (0:ℝ) ≤ max (z x - k) 0 := fun x => le_max_right _ _
  have htTb : ∀ x, max (z x - k) 0 ≤ Tb := by
    intro x
    have h1 := hS x
    rw [abs_le] at h1
    rw [hTbdef]
    exact max_le (by linarith) (by linarith)
  have hEx1 : ∀ x, 1 ≤ Real.exp (lam * max (z x - k) 0) := fun x =>
    Real.one_le_exp (mul_nonneg hlam.le (ht0 x))
  have hExE : ∀ x, Real.exp (lam * max (z x - k) 0) ≤ E := by
    intro x
    rw [hEdef]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (htTb x) hlam.le)
  have hQ0 : ∀ x, (0:ℝ) ≤ (Real.exp (lam * max (z x - k) 0) - 1) / lam := fun x =>
    div_nonneg (by linarith [hEx1 x]) hlam.le
  have hQEp : ∀ x, (Real.exp (lam * max (z x - k) 0) - 1) / lam ≤ Ep := by
    intro x
    have h := hExE x
    rw [hEpdef, div_le_div_iff_of_pos_right hlam]
    linarith
  have hexp_le : ∀ u : ℝ, 0 ≤ u → Real.exp u - 1 ≤ u * Real.exp u := by
    intro u hu
    have h1 : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
    have h3 : 0 < Real.exp u := Real.exp_pos u
    rw [Real.exp_neg u] at h1
    have h4 := mul_le_mul_of_nonneg_right h1 h3.le
    rw [inv_mul_cancel₀ h3.ne'] at h4
    nlinarith [h4]
  have hQt : ∀ x, (Real.exp (lam * max (z x - k) 0) - 1) / lam ≤ max (z x - k) 0 * E := by
    intro x
    have hu : (0:ℝ) ≤ lam * max (z x - k) 0 := mul_nonneg hlam.le (ht0 x)
    have h := hexp_le _ hu
    have hEE := hExE x
    have ht := ht0 x
    rw [div_le_iff₀ hlam]
    nlinarith [mul_nonneg (mul_nonneg hlam.le ht) (by linarith : (0:ℝ) ≤ E -
      Real.exp (lam * max (z x - k) 0))]
  have hqlam : ∀ x, lam * ((Real.exp (lam * max (z x - k) 0) - 1) / lam) ≤
      Real.exp (lam * max (z x - k) 0) := by
    intro x
    have hid : lam * ((Real.exp (lam * max (z x - k) 0) - 1) / lam) =
        Real.exp (lam * max (z x - k) 0) - 1 := by field_simp
    rw [hid]
    linarith
  -- ### the cutoff `ζ = η²`
  obtain ⟨ζ, hζdef⟩ : ∃ g : Euc d → ℝ, g = fun x => η x ^ 2 := ⟨_, rfl⟩
  have hζval : ∀ x, ζ x = η x ^ 2 := fun x => by rw [hζdef]
  have hζC : ContDiff ℝ ∞ ζ := by rw [hζdef]; exact hηC.pow 2
  have hζsupp : Function.support ζ ⊆ tsupport η := fun x hx =>
    subset_closure (show η x ≠ 0 from fun h => hx (by rw [hζval x, h]; norm_num))
  have hζs : HasCompactSupport ζ := HasCompactSupport.of_support_subset_isCompact hηs hζsupp
  have hζts : tsupport ζ ⊆ Metric.closedBall y ((r + s) / 2) :=
    (closure_minimal hζsupp (isClosed_tsupport η)).trans hηsub
  have hballs : Metric.closedBall y ((r + s) / 2) ⊆ Metric.ball y s := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    linarith
  have hζball : tsupport ζ ⊆ Metric.ball y s := hζts.trans hballs
  have hζK : tsupport ζ ⊆ K₀ :=
    hζball.trans (Metric.ball_subset_closedBall.trans hTball)
  have hζ0 : ∀ x, 0 ≤ ζ x := fun x => by rw [hζval x]; exact sq_nonneg _
  have hζ1 : ∀ x, ζ x ≤ 1 := fun x => by rw [hζval x]; nlinarith [hη0 x, hη1 x]
  have hζzero : ∀ x, x ∉ Metric.ball y s → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hζball h)
  have hgζ : ∀ x, gradient ζ x = (2 * η x) • gradient η x := by
    intro x; rw [hζdef]; exact gradient_sq hη1' x
  have hgζzero : ∀ x, x ∉ Metric.ball y s → gradient ζ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport fun h => hx (hζball h)
  have hgζnorm : ∀ x, ‖gradient ζ x‖ ≤ 2 * η x * Kg := by
    intro x
    rw [hgζ x, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hη0 x] : (0:ℝ) ≤ 2 * η x)]
    have h1 : ‖gradient η x‖ ≤ Kg := hηg x
    nlinarith [norm_nonneg (gradient η x), hη0 x]
  -- ### the test function
  obtain ⟨w, hwW, hwval, hwgrad⟩ := exists_dg_testfn hlam hzW hS hk hζC hζs hζK
  have hw0 : ∀ x, x ∉ Metric.ball y s → w x = 0 := by
    intro x hx
    rw [hwval x, hζzero x hx, zero_mul]
  have hwT : MemW0 2 (Metric.closedBall y s) w :=
    ⟨hwW.memLp, Eventually.of_forall fun x hx =>
      hw0 x fun h => hx (Metric.ball_subset_closedBall h), hwW.exists_weakGradient⟩
  have hwg0 : ∀ᵐ x, x ∉ Metric.closedBall y s → weakGrad w x = 0 := by
    filter_upwards [hwgrad] with x hx hxn
    have hxb : x ∉ Metric.ball y s := fun h => hxn (Metric.ball_subset_closedBall h)
    rw [hx, hζzero x hxb, hgζzero x hxb]
    simp
  have hwb : ∀ x, |w x| ≤ Ep := by
    intro x
    rw [hwval x, abs_mul, abs_of_nonneg (hζ0 x),
      abs_of_nonneg (hQ0 x)]
    calc ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam) ≤ 1 * Ep :=
        mul_le_mul (hζ1 x) (hQEp x) (hQ0 x) zero_le_one
      _ = Ep := one_mul _
  have key := hweak w hwT hwg0 Ep hwb
  -- ### rewriting the tested identity
  have e1 : (∫ x, ⟪gradient Ψ (H x), weakGrad w x⟫) =
      ∫ x, (ζ x * (Real.exp (lam * max (z x - k) 0) * (if k < z x then (1:ℝ) else 0)) *
          ⟪gradient Ψ (H x), H x⟫ +
        ((Real.exp (lam * max (z x - k) 0) - 1) / lam) * ⟪gradient Ψ (H x), gradient ζ x⟫) := by
    refine integral_congr_ae ?_
    filter_upwards [hwgrad, hzH] with x h1 h2
    show ⟪gradient Ψ (H x), weakGrad w x⟫ = _
    rw [h1, inner_add_right, real_inner_smul_right, real_inner_smul_right, h2]
  have e2 : (∫ x, f x * w x) =
      ∫ x, f x * (ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam)) :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [hwval x])
  rw [e1, e2] at key
  -- ### measurability
  have hmind : Measurable fun x => if k < z x then (1:ℝ) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const hzm) measurable_const measurable_const
  have hmEx : Measurable fun x => Real.exp (lam * max (z x - k) 0) :=
    Real.measurable_exp.comp (measurable_const.mul ((hzm.sub measurable_const).max
      measurable_const))
  have hmQ : Measurable fun x => (Real.exp (lam * max (z x - k) 0) - 1) / lam :=
    (hmEx.sub measurable_const).div measurable_const
  have hmΨH : Measurable fun x => gradient Ψ (H x) :=
    hΨ.contDiff_gradient.continuous.measurable.comp hHm
  have hmgζ : Continuous fun x => gradient ζ x := continuous_gradient (hζC.of_le (by simp))
  have hmSet : MeasurableSet (Metric.ball y s ∩ {x | k < z x}) :=
    Metric.isOpen_ball.measurableSet.inter (measurableSet_lt measurable_const hzm)
  -- `‖H‖` is integrable on the ball
  have hH1 : IntegrableOn (fun x => ‖H x‖) (Metric.closedBall y s) volume := by
    have hdom : IntegrableOn (fun x => 2⁻¹ * (‖H x‖ ^ 2 + 1)) (Metric.closedBall y s) volume :=
      ((hH2).add (integrableOn_const (isCompact_closedBall y s).measure_lt_top.ne)).const_mul _
    refine Integrable.mono' hdom (hHm.norm.aestronglyMeasurable).restrict
      (Eventually.of_forall fun x => ?_)
    have h1 : ‖H x‖ ≤ 2⁻¹ * (‖H x‖ ^ 2 + 1) := by
      nlinarith [sq_nonneg (‖H x‖ - 1), norm_nonneg (H x)]
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (H x))] using h1
  have hballsub : Metric.ball y s ⊆ Metric.closedBall y s := Metric.ball_subset_closedBall
  have hfinCB : volume (Metric.closedBall y s) ≠ ⊤ := (isCompact_closedBall y s).measure_lt_top.ne
  have hfinB : volume (Metric.ball y s) ≠ ⊤ := measure_ball_lt_top.ne
  -- ### integrability of the three terms
  have iA : Integrable (fun x => ζ x * (Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0)) * ⟪gradient Ψ (H x), H x⟫) volume := by
    refine integrable_of_bound_on_set (S := Metric.closedBall y s) measurableSet_closedBall
      (((hζC.continuous.measurable.mul (hmEx.mul hmind)).mul
        (hmΨH.inner hHm)).aestronglyMeasurable)
      (b := fun x => E * (C * ‖H x‖ ^ 2)) ((hH2.const_mul C).const_mul E) ?_ ?_
    · intro x _
      have h1 : |⟪gradient Ψ (H x), H x⟫| ≤ C * ‖H x‖ ^ 2 := by
        have ha : |⟪gradient Ψ (H x), H x⟫| ≤ ‖gradient Ψ (H x)‖ * ‖H x‖ :=
          abs_real_inner_le_norm _ _
        have hb : ‖gradient Ψ (H x)‖ ≤ C * ‖H x‖ := hCΨ.norm_gradient_le (H x)
        nlinarith [norm_nonneg (H x), norm_nonneg (gradient Ψ (H x))]
      have h2 : |ζ x * (Real.exp (lam * max (z x - k) 0) *
          (if k < z x then (1:ℝ) else 0))| ≤ E := by
        rw [abs_mul, abs_of_nonneg (hζ0 x), abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        have hi : |(if k < z x then (1:ℝ) else 0)| ≤ 1 := by
          split <;> norm_num
        have hb : ζ x * (Real.exp (lam * max (z x - k) 0) *
            |(if k < z x then (1:ℝ) else 0)|) ≤ 1 * (E * 1) := by
          refine mul_le_mul (hζ1 x) ?_ (by positivity) zero_le_one
          exact mul_le_mul (hExE x) hi (abs_nonneg _) hE0
        linarith [hb]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h2 h1 (abs_nonneg _) hE0
    · intro x hx
      rw [hζzero x fun h => hx (hballsub h), zero_mul, zero_mul]
  have iB : Integrable (fun x => ((Real.exp (lam * max (z x - k) 0) - 1) / lam) *
      ⟪gradient Ψ (H x), gradient ζ x⟫) volume := by
    refine integrable_of_bound_on_set (S := Metric.closedBall y s) measurableSet_closedBall
      ((hmQ.mul (hmΨH.inner hmgζ.measurable)).aestronglyMeasurable)
      (b := fun x => Ep * (C * (2 * Kg) * ‖H x‖))
      ((hH1.const_mul (C * (2 * Kg))).const_mul Ep) ?_ ?_
    · intro x _
      have h1 : |⟪gradient Ψ (H x), gradient ζ x⟫| ≤ C * (2 * Kg) * ‖H x‖ := by
        have ha : |⟪gradient Ψ (H x), gradient ζ x⟫| ≤ ‖gradient Ψ (H x)‖ * ‖gradient ζ x‖ :=
          abs_real_inner_le_norm _ _
        have hb : ‖gradient Ψ (H x)‖ ≤ C * ‖H x‖ := hCΨ.norm_gradient_le (H x)
        have hd : ‖gradient ζ x‖ ≤ 2 * Kg := by
          have hgz := hgζnorm x
          nlinarith [hη0 x, hη1 x, hKg0]
        nlinarith [norm_nonneg (H x), norm_nonneg (gradient ζ x),
          norm_nonneg (gradient Ψ (H x))]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQ0 x)]
      have hnn : (0:ℝ) ≤ C * (2 * Kg) * ‖H x‖ := by positivity
      exact mul_le_mul (hQEp x) h1 (abs_nonneg _) hEp0
    · intro x hx
      rw [hgζzero x fun h => hx (hballsub h), inner_zero_right, mul_zero]
  have iC : Integrable (fun x => f x * (ζ x *
      ((Real.exp (lam * max (z x - k) 0) - 1) / lam))) volume := by
    have hdom : IntegrableOn (fun x => A * Ep + 2 * C * Ep * ‖H x‖ ^ 2)
        (Metric.closedBall y s) volume :=
      (integrableOn_const hfinCB).add (hH2.const_mul (2 * C * Ep))
    refine integrable_of_bound_on_set (S := Metric.closedBall y s) measurableSet_closedBall
      ((hfm.mul (hζC.continuous.measurable.mul hmQ)).aestronglyMeasurable)
      (b := fun x => A * Ep + 2 * C * Ep * ‖H x‖ ^ 2) hdom ?_ ?_
    · intro x _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hζ0 x),
        abs_of_nonneg (hQ0 x)]
      have hnn : (0:ℝ) ≤ A + 2 * C * ‖H x‖ ^ 2 := by positivity
      have h2 : ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam) ≤ Ep := by
        have hstep : ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam) ≤ 1 * Ep :=
          mul_le_mul (hζ1 x) (hQEp x) (hQ0 x) zero_le_one
        linarith
      have h3 : |f x| * (ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam)) ≤
          (A + 2 * C * ‖H x‖ ^ 2) * Ep :=
        mul_le_mul (hfbd x) h2 (mul_nonneg (hζ0 x) (hQ0 x)) hnn
      nlinarith [h3]
    · intro x hx
      rw [hζzero x fun h => hx (hballsub h), zero_mul, mul_zero]
  have iD : Integrable (fun x => ζ x * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) volume := by
    refine integrable_of_bound_on_set (S := Metric.closedBall y s) measurableSet_closedBall
      ((((hζC.continuous.measurable.mul hmEx).mul hmind).mul
        (hHm.norm.pow_const 2)).aestronglyMeasurable)
      (b := fun x => E * ‖H x‖ ^ 2) (hH2.const_mul E) ?_ ?_
    · intro x _
      have hi0 : (0:ℝ) ≤ (if k < z x then (1:ℝ) else 0) := by split <;> norm_num
      have hi1 : (if k < z x then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
      have hζe0 : (0:ℝ) ≤ ζ x * Real.exp (lam * max (z x - k) 0) :=
        mul_nonneg (hζ0 x) (Real.exp_nonneg _)
      have hnn : (0:ℝ) ≤ ζ x * Real.exp (lam * max (z x - k) 0) *
          (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2 :=
        mul_nonneg (mul_nonneg hζe0 hi0) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have h1 : ζ x * Real.exp (lam * max (z x - k) 0) ≤ E := by
        have h := mul_le_mul (hζ1 x) (hExE x) (Real.exp_nonneg _) zero_le_one
        linarith
      have hstep : ζ x * Real.exp (lam * max (z x - k) 0) *
          (if k < z x then (1:ℝ) else 0) ≤ E := by nlinarith
      exact mul_le_mul_of_nonneg_right hstep (sq_nonneg _)
    · intro x hx
      rw [hζzero x fun h => hx (hballsub h), zero_mul, zero_mul, zero_mul]
  have iE : Integrable (fun x => max (z x - k) 0 ^ 2 *
      (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) volume := by
    have heq : (fun x => max (z x - k) 0 ^ 2 *
        (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) =
        (Metric.ball y s).indicator (fun x => max (z x - k) 0 ^ 2) := by
      funext x
      by_cases hx : x ∈ Metric.ball y s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    rw [heq, integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    have hdom : IntegrableOn (fun _ : Euc d => Tb ^ 2) (Metric.ball y s) volume :=
      integrableOn_const hfinB
    refine Integrable.mono' hdom
      (((hzm.sub measurable_const).max measurable_const).pow_const
        2).aestronglyMeasurable.restrict (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [ht0 x, htTb x]
  have iF : Integrable ((Metric.ball y s ∩ {x | k < z x}).indicator
      fun _ => (1:ℝ)) volume := by
    rw [integrable_indicator_iff hmSet]
    exact integrableOn_const
      (((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top).ne)
  -- ### the tested identity has vanishing integral
  have hPint : Integrable (fun x => ζ x * (Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0)) * ⟪gradient Ψ (H x), H x⟫ +
      ((Real.exp (lam * max (z x - k) 0) - 1) / lam) *
        ⟪gradient Ψ (H x), gradient ζ x⟫ +
      f x * (ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam))) volume := (iA.add iB).add iC
  have hABint : Integrable (fun x => ζ x * (Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0)) * ⟪gradient Ψ (H x), H x⟫ +
      ((Real.exp (lam * max (z x - k) 0) - 1) / lam) *
        ⟪gradient Ψ (H x), gradient ζ x⟫) volume := iA.add iB
  have hPzero : (∫ x, (ζ x * (Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0)) * ⟪gradient Ψ (H x), H x⟫ +
      ((Real.exp (lam * max (z x - k) 0) - 1) / lam) *
        ⟪gradient Ψ (H x), gradient ζ x⟫ +
      f x * (ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam)))) = 0 := by
    have hsplit : (∫ x, (ζ x * (Real.exp (lam * max (z x - k) 0) *
        (if k < z x then (1:ℝ) else 0)) * ⟪gradient Ψ (H x), H x⟫ +
        ((Real.exp (lam * max (z x - k) 0) - 1) / lam) *
          ⟪gradient Ψ (H x), gradient ζ x⟫ +
        f x * (ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam)))) =
        (∫ x, (ζ x * (Real.exp (lam * max (z x - k) 0) *
          (if k < z x then (1:ℝ) else 0)) * ⟪gradient Ψ (H x), H x⟫ +
          ((Real.exp (lam * max (z x - k) 0) - 1) / lam) *
            ⟪gradient Ψ (H x), gradient ζ x⟫)) +
          ∫ x, f x * (ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam)) :=
      integral_add hABint iC
    rw [hsplit, key]
    ring
  -- ### the pointwise bound
  have hpt : ∀ x, c / 4 * (ζ x * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) -
      4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
        (max (z x - k) 0 ^ 2 * (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) -
      A * Ep * (Metric.ball y s ∩ {x | k < z x}).indicator (fun _ => (1:ℝ)) x ≤
      ζ x * (Real.exp (lam * max (z x - k) 0) * (if k < z x then (1:ℝ) else 0)) *
        ⟪gradient Ψ (H x), H x⟫ +
      ((Real.exp (lam * max (z x - k) 0) - 1) / lam) *
        ⟪gradient Ψ (H x), gradient ζ x⟫ +
      f x * (ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam)) := by
    intro x
    by_cases hx : x ∈ Metric.ball y s
    · by_cases hk' : k < z x
      · have hmem : x ∈ Metric.ball y s ∩ {x | k < z x} := ⟨hx, hk'⟩
        have hmain := dg_pointwise hΨ hCΨ (lam := lam) (E := E) (Eprime := Ep) (A := A)
          (Kg := Kg) (ηx := η x) (ex := Real.exp (lam * max (z x - k) 0))
          (qx := (Real.exp (lam * max (z x - k) 0) - 1) / lam) (tx := max (z x - k) 0)
          (fx := f x) (Hx := H x) (nx := gradient ζ x)
          hlam hlamC hKg0 (hη0 x) (hη1 x) (hEx1 x) (hQ0 x) (hQEp x) (hQt x) (hqlam x)
          (ht0 x) hA0 hE0 (hfbd x) (hgζnorm x)
        simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hmem, if_pos hk',
          hζval x, mul_one]
        linarith [hmain]
      · have hzk : z x - k ≤ 0 := by linarith [not_lt.1 hk']
        have ht : max (z x - k) 0 = 0 := max_eq_right hzk
        have hnm : x ∉ Metric.ball y s ∩ {x | k < z x} := fun h => hk' h.2
        simp only [if_neg hk', ht, Set.indicator_of_notMem hnm, mul_zero, zero_mul,
          mul_one, Real.exp_zero]
        norm_num
    · have hnm : x ∉ Metric.ball y s ∩ {x | k < z x} := fun h => hx h.1
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hnm, hζzero x hx,
        hgζzero x hx, mul_zero, zero_mul, inner_zero_right]
      norm_num
  -- ### integrate
  have hLBint : Integrable (fun x => c / 4 * (ζ x * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) -
      4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
        (max (z x - k) 0 ^ 2 * (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) -
      A * Ep * (Metric.ball y s ∩ {x | k < z x}).indicator (fun _ => (1:ℝ)) x) volume :=
    ((iD.const_mul _).sub (iE.const_mul _)).sub (iF.const_mul _)
  have hmono : (∫ x, (c / 4 * (ζ x * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) -
      4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
        (max (z x - k) 0 ^ 2 * (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) -
      A * Ep * (Metric.ball y s ∩ {x | k < z x}).indicator (fun _ => (1:ℝ)) x)) ≤
      ∫ x, (ζ x * (Real.exp (lam * max (z x - k) 0) *
        (if k < z x then (1:ℝ) else 0)) * ⟪gradient Ψ (H x), H x⟫ +
        ((Real.exp (lam * max (z x - k) 0) - 1) / lam) *
          ⟪gradient Ψ (H x), gradient ζ x⟫ +
        f x * (ζ x * ((Real.exp (lam * max (z x - k) 0) - 1) / lam))) :=
    integral_mono hLBint hPint hpt
  rw [hPzero] at hmono
  -- ### evaluate the three integrals of the lower bound
  have hsub1 : (∫ x, (c / 4 * (ζ x * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) -
      4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
        (max (z x - k) 0 ^ 2 * (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) -
      A * Ep * (Metric.ball y s ∩ {x | k < z x}).indicator (fun _ => (1:ℝ)) x)) =
      (∫ x, (c / 4 * (ζ x * Real.exp (lam * max (z x - k) 0) *
        (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) -
        4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
          (max (z x - k) 0 ^ 2 * (Metric.ball y s).indicator (fun _ => (1:ℝ)) x))) -
        ∫ x, A * Ep * (Metric.ball y s ∩ {x | k < z x}).indicator (fun _ => (1:ℝ)) x :=
    integral_sub ((iD.const_mul _).sub (iE.const_mul _)) (iF.const_mul _)
  have hsub2 : (∫ x, (c / 4 * (ζ x * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) -
      4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
        (max (z x - k) 0 ^ 2 * (Metric.ball y s).indicator (fun _ => (1:ℝ)) x))) =
      (∫ x, c / 4 * (ζ x * Real.exp (lam * max (z x - k) 0) *
        (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2)) -
        ∫ x, 4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
          (max (z x - k) 0 ^ 2 * (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) :=
    integral_sub (iD.const_mul _) (iE.const_mul _)
  have hEint : (∫ x, max (z x - k) 0 ^ 2 *
      (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) =
      ∫ x in Metric.ball y s, max (z x - k) 0 ^ 2 := by
    have heq : (fun x => max (z x - k) 0 ^ 2 *
        (Metric.ball y s).indicator (fun _ => (1:ℝ)) x) =
        (Metric.ball y s).indicator (fun x => max (z x - k) 0 ^ 2) := by
      funext x
      by_cases hx : x ∈ Metric.ball y s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    rw [heq]
    exact integral_indicator Metric.isOpen_ball.measurableSet
  have hFint : (∫ x, (Metric.ball y s ∩ {x | k < z x}).indicator (fun _ => (1:ℝ)) x) =
      (volume (Metric.ball y s ∩ {x | k < z x})).toReal := by
    rw [integral_indicator_const (1:ℝ) hmSet]
    simp
    rfl
  rw [hsub1, hsub2, integral_const_mul, integral_const_mul, integral_const_mul, hEint,
    hFint] at hmono
  have hζη : (∫ x, ζ x * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) =
      ∫ x, η x ^ 2 * Real.exp (lam * max (z x - k) 0) *
        (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [hζval x])
  rw [hζη] at hmono
  -- ### the left-hand side dominates the level-set energy on `B_r`
  have hmeasS : MeasurableSet (Metric.ball y r ∩ {x | k < z x}) :=
    Metric.isOpen_ball.measurableSet.inter (measurableSet_lt measurable_const hzm)
  have hsubr : Metric.ball y r ∩ {x | k < z x} ⊆ Metric.closedBall y s := fun x hx =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball hrs.le hx.1)
  have hnnint : ∀ x, (0:ℝ) ≤ η x ^ 2 * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2 := by
    intro x
    have hi0 : (0:ℝ) ≤ (if k < z x then (1:ℝ) else 0) := by split <;> norm_num
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) hi0)
      (sq_nonneg _)
  have hiD' : Integrable (fun x => η x ^ 2 * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) volume := by
    refine iD.congr (Eventually.of_forall fun x => ?_)
    simp only [hζval x]
  have h1 : (∫ x in Metric.ball y r ∩ {x | k < z x}, ‖H x‖ ^ 2) ≤
      ∫ x in Metric.ball y r ∩ {x | k < z x}, η x ^ 2 *
        Real.exp (lam * max (z x - k) 0) * (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2 := by
    refine setIntegral_mono_on (hH2.mono_set hsubr) (hiD'.restrict) hmeasS ?_
    intro x hx
    have hηx : η x = 1 := hηone x (Metric.ball_subset_closedBall hx.1)
    have hk' : k < z x := hx.2
    rw [hηx, if_pos hk']
    have he := hEx1 x
    nlinarith [sq_nonneg ‖H x‖]
  have h2 : (∫ x in Metric.ball y r ∩ {x | k < z x}, η x ^ 2 *
      Real.exp (lam * max (z x - k) 0) * (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) ≤
      ∫ x, η x ^ 2 * Real.exp (lam * max (z x - k) 0) *
        (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2 :=
    setIntegral_le_integral hiD' (Eventually.of_forall hnnint)
  have hcpos : (0:ℝ) < c / 4 := by linarith
  have hkey : c / 4 * (∫ x, η x ^ 2 * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2) ≤
      4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 * (∫ x in Metric.ball y s, max (z x - k) 0 ^ 2) +
        A * Ep * (volume (Metric.ball y s ∩ {x | k < z x})).toReal := by linarith
  have hid : 4 / c * (c / 4 * (∫ x, η x ^ 2 * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2)) =
      ∫ x, η x ^ 2 * Real.exp (lam * max (z x - k) 0) *
        (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2 := by
    field_simp
  have h4c : (0:ℝ) < 4 / c := by positivity
  have hmul : 4 / c * (c / 4 * (∫ x, η x ^ 2 * Real.exp (lam * max (z x - k) 0) *
      (if k < z x then (1:ℝ) else 0) * ‖H x‖ ^ 2)) ≤
      4 / c * (4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
          (∫ x in Metric.ball y s, max (z x - k) 0 ^ 2) +
        A * Ep * (volume (Metric.ball y s ∩ {x | k < z x})).toReal) :=
    mul_le_mul_of_nonneg_left hkey h4c.le
  rw [hid] at hmul
  linarith

/-! ### The De Giorgi class of a bounded natural-growth solution -/

set_option maxHeartbeats 1000000 in
/-- **A bounded weak solution with natural growth lies in a De Giorgi class.**  The level-set
energy inequality is `dg_energy_step` at the level `max k (-S-1)`; for `k < -S-1` the set
`{z > k}` is everything (because `|z| ≤ S`), so the inequality at the level `-S-1` — where the
Stampacchia constants are still uniform — implies the one at `k` by monotonicity. -/
theorem exists_isDGSub_of_weak (hΨ : IsRegProfile Ψ) (hCΨ : IsRegProfileWith Ψ c C)
    {x₀ : Euc d} {ρ : ℝ} {K₀ : Set (Euc d)} (hballK : Metric.ball x₀ ρ ⊆ K₀)
    {z : Euc d → ℝ} {H : Euc d → Euc d} {f : Euc d → ℝ}
    (hzW : MemW0 2 K₀ z) (hzm : Measurable z) (hzHw : HasWeakGradient z H)
    (hHm : Measurable H) (hfm : Measurable f)
    {S : ℝ} (hS : ∀ x, |z x| ≤ S) {A : ℝ} (hA0 : 0 ≤ A)
    (hfbd : ∀ x, |f x| ≤ A + 2 * C * ‖H x‖ ^ 2)
    (hH2 : ∀ (y : Euc d) (s : ℝ), Metric.closedBall y s ⊆ Metric.ball x₀ ρ →
      IntegrableOn (fun x => ‖H x‖ ^ 2) (Metric.closedBall y s) volume)
    (hweak : ∀ (y : Euc d) (s : ℝ), Metric.closedBall y s ⊆ Metric.ball x₀ ρ →
      ∀ w : Euc d → ℝ, MemW0 2 (Metric.closedBall y s) w →
      (∀ᵐ x, x ∉ Metric.closedBall y s → weakGrad w x = 0) →
      ∀ Mw : ℝ, (∀ x, |w x| ≤ Mw) →
      (∫ x, ⟪gradient Ψ (H x), weakGrad w x⟫) = -∫ x, f x * w x) :
    ∃ γ χ : ℝ, 0 ≤ γ ∧ 0 ≤ χ ∧ IsDGSub γ χ ρ (Metric.ball x₀ ρ) z H := by
  obtain ⟨Ccut, hCcut, hcut⟩ := exists_cutoff_const d
  have hc : 0 < c := hCΨ.c_pos
  have hcne : c ≠ 0 := ne_of_gt hc
  have hC0 : 0 ≤ C := hCΨ.C_nonneg
  have hS0 : 0 ≤ S := (abs_nonneg (z 0)).trans (hS 0)
  have hzH : weakGrad z =ᵐ[volume] H := hzHw.weakGrad_ae_eq
  obtain ⟨lam, hlamdef⟩ : ∃ t : ℝ, t = 4 * C / c + 1 := ⟨_, rfl⟩
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hlamC : 4 * C ≤ lam * c := by
    rw [hlamdef]
    have h : (4 * C / c + 1) * c = 4 * C + c := by field_simp
    rw [h]
    linarith
  obtain ⟨Tb, hTbdef⟩ : ∃ t : ℝ, t = 2 * S + 1 := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ t : ℝ, t = Real.exp (lam * Tb) := ⟨_, rfl⟩
  have hTb0 : 0 ≤ Tb := by rw [hTbdef]; linarith
  have hE1 : 1 ≤ E := by rw [hEdef]; exact Real.one_le_exp (by positivity)
  obtain ⟨Ep, hEpdef⟩ : ∃ t : ℝ, t = (E - 1) / lam := ⟨_, rfl⟩
  have hEp0 : 0 ≤ Ep := by rw [hEpdef]; exact div_nonneg (by linarith) hlam.le
  obtain ⟨γ, hγdef⟩ : ∃ t : ℝ, t = max (64 * C ^ 2 * Ccut ^ 2 * E ^ 2 / c ^ 2) 1 := ⟨_, rfl⟩
  have hγ1 : 1 ≤ γ := by rw [hγdef]; exact le_max_right _ _
  have hγ0 : 0 ≤ γ := by linarith
  have hγge : 64 * C ^ 2 * Ccut ^ 2 * E ^ 2 / c ^ 2 ≤ γ := by rw [hγdef]; exact le_max_left _ _
  obtain ⟨χ, hχdef⟩ : ∃ t : ℝ, t = Real.sqrt (4 * A * Ep / c / γ) := ⟨_, rfl⟩
  have hχ0 : 0 ≤ χ := by rw [hχdef]; exact Real.sqrt_nonneg _
  have hγne : γ ≠ 0 := by linarith
  have hχsq : γ * χ ^ 2 = 4 * A * Ep / c := by
    rw [hχdef, Real.sq_sqrt (by positivity)]
    field_simp
  -- integrability of `(z-k)_+²` on balls
  have hIint : ∀ (y : Euc d) (s k' : ℝ), IntegrableOn (fun x => max (z x - k') 0 ^ 2)
      (Metric.ball y s) volume := by
    intro y s k'
    have hb : IntegrableOn (fun _ : Euc d => (|k'| + S) ^ 2) (Metric.ball y s) volume :=
      integrableOn_const measure_ball_lt_top.ne
    refine Integrable.mono' hb
      (((hzm.sub measurable_const).max
        measurable_const).pow_const 2).aestronglyMeasurable.restrict
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := hS x
    rw [abs_le] at h1
    have h2 : max (z x - k') 0 ≤ |k'| + S := by
      refine max_le ?_ (by positivity)
      have h3 := le_abs_self k'
      have h4 := neg_abs_le k'
      linarith [h1.2]
    nlinarith [le_max_right (z x - k') 0, abs_nonneg k']
  refine ⟨γ, χ, hγ0, hχ0, ⟨hzHw, hzm, hHm, ?_, ?_⟩⟩
  · intro y s hs
    refine ⟨?_, hH2 y s hs⟩
    have hb : IntegrableOn (fun _ : Euc d => S ^ 2) (Metric.closedBall y s) volume :=
      integrableOn_const (isCompact_closedBall y s).measure_lt_top.ne
    refine Integrable.mono' hb ((hzm.pow_const 2).aestronglyMeasurable).restrict
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hS x, abs_nonneg (z x), sq_abs (z x)]
  · intro y r s k hr hrs hsρ hball
    have hsr : 0 < s - r := by linarith
    obtain ⟨η, hηC, hηs, hηsub, hη0, hη1, hηone, hηg⟩ := hcut y r ((r + s) / 2) hr (by linarith)
    obtain ⟨Kg, hKgdef⟩ : ∃ t : ℝ, t = 2 * Ccut / (s - r) := ⟨_, rfl⟩
    have hKg0 : 0 ≤ Kg := by rw [hKgdef]; positivity
    have hηgKg : ∀ x, ‖gradient η x‖ ≤ Kg := by
      intro x
      have h := hηg x
      have heq : Ccut / ((r + s) / 2 - r) = Kg := by
        rw [hKgdef, show (r + s) / 2 - r = (s - r) / 2 from by ring, div_div_eq_mul_div]
        ring
      rwa [heq] at h
    have hTball : Metric.closedBall y s ⊆ K₀ := hball.trans hballK
    -- the arithmetic turning the Caccioppoli constants into `γ`, `χ`
    have harith : ∀ I M : ℝ, 0 ≤ I → 0 ≤ M →
        4 / c * (4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 * I + A * Ep * M) ≤
          γ / (s - r) ^ 2 * I + γ * χ ^ 2 * M := by
      intro I M hI hM
      have hKgsq : Kg ^ 2 = 4 * Ccut ^ 2 / (s - r) ^ 2 := by
        rw [hKgdef, div_pow]
        ring
      have hco : 4 / c * (4 / c * C ^ 2 * Kg ^ 2 * E ^ 2) =
          64 * C ^ 2 * Ccut ^ 2 * E ^ 2 / c ^ 2 / (s - r) ^ 2 := by
        rw [hKgsq]
        ring
      have hMeq : 4 / c * (A * Ep) = γ * χ ^ 2 := by
        rw [hχsq]
        ring
      have hpos : (0:ℝ) < (s - r) ^ 2 := by positivity
      have hdiv : 64 * C ^ 2 * Ccut ^ 2 * E ^ 2 / c ^ 2 / (s - r) ^ 2 ≤ γ / (s - r) ^ 2 := by
        gcongr
      have hfin : 64 * C ^ 2 * Ccut ^ 2 * E ^ 2 / c ^ 2 / (s - r) ^ 2 * I ≤
          γ / (s - r) ^ 2 * I := mul_le_mul_of_nonneg_right hdiv hI
      have hexp : 4 / c * (4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 * I + A * Ep * M) =
          (4 / c * (4 / c * C ^ 2 * Kg ^ 2 * E ^ 2)) * I + (4 / c * (A * Ep)) * M := by ring
      rw [hexp, hco, hMeq]
      linarith
    have hM0 : (0:ℝ) ≤ (volume (Metric.ball y s ∩ {x | k < z x})).toReal :=
      ENNReal.toReal_nonneg
    have hI0 : (0:ℝ) ≤ ∫ x in Metric.ball y s, max (z x - k) 0 ^ 2 :=
      setIntegral_nonneg measurableSet_ball fun x _ => sq_nonneg _
    by_cases hk' : -S - 1 ≤ k
    · have hstep := dg_energy_step hΨ hCΨ hzW hzm hzH hHm hfm hS hA0 hfbd hlam hlamC
        hTbdef hEdef hEpdef hr hrs hk' hηC hηs hηsub hη0 hη1 hηone hKg0 hηgKg hTball
        (hH2 y s hball) (hweak y s hball)
      exact hstep.trans (harith _ _ hI0 hM0)
    · have hkS : k < -S - 1 := not_le.1 hk'
      have hzk : ∀ x, k < z x := by
        intro x
        have h1 := hS x
        rw [abs_le] at h1
        linarith [h1.1]
      have hzkt : ∀ x, -S - 1 < z x := by
        intro x
        have h1 := hS x
        rw [abs_le] at h1
        linarith [h1.1]
      have hset1 : Metric.ball y r ∩ {x | k < z x} = Metric.ball y r := by
        ext x; simp [hzk x]
      have hset2 : Metric.ball y r ∩ {x | -S - 1 < z x} = Metric.ball y r := by
        ext x; simp [hzkt x]
      have hset3 : Metric.ball y s ∩ {x | -S - 1 < z x} = Metric.ball y s ∩ {x | k < z x} := by
        ext x; simp [hzkt x, hzk x]
      have hstep := dg_energy_step hΨ hCΨ hzW hzm hzH hHm hfm hS hA0 hfbd hlam hlamC
        hTbdef hEdef hEpdef hr hrs (le_refl (-S - 1)) hηC hηs hηsub hη0 hη1 hηone hKg0 hηgKg
        hTball (hH2 y s hball) (hweak y s hball)
      rw [hset2, hset3] at hstep
      rw [hset1]
      have hmonoI : (∫ x in Metric.ball y s, max (z x - (-S - 1)) 0 ^ 2) ≤
          ∫ x in Metric.ball y s, max (z x - k) 0 ^ 2 := by
        refine setIntegral_mono_on (hIint y s _) (hIint y s _) measurableSet_ball ?_
        intro x _
        have h1 : max (z x - (-S - 1)) 0 ≤ max (z x - k) 0 :=
          max_le_max (by linarith) le_rfl
        nlinarith [le_max_right (z x - (-S - 1)) 0, le_max_right (z x - k) 0]
      have hstep2 : (∫ x in Metric.ball y r, ‖H x‖ ^ 2) ≤
          4 / c * (4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
              (∫ x in Metric.ball y s, max (z x - k) 0 ^ 2) +
            A * Ep * (volume (Metric.ball y s ∩ {x | k < z x})).toReal) := by
        refine hstep.trans ?_
        have hnn : (0:ℝ) ≤ 4 / c := by positivity
        have hnn2 : (0:ℝ) ≤ 4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 := by positivity
        have h1 : 4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
            (∫ x in Metric.ball y s, max (z x - (-S - 1)) 0 ^ 2) ≤
            4 / c * C ^ 2 * Kg ^ 2 * E ^ 2 *
              (∫ x in Metric.ball y s, max (z x - k) 0 ^ 2) :=
          mul_le_mul_of_nonneg_left hmonoI hnn2
        exact mul_le_mul_of_nonneg_left (by linarith) hnn
      exact hstep2.trans (harith _ _ hI0 hM0)

end Komlos.Literature.Regularized
