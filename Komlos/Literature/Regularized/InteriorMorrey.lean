import Komlos.Literature.Regularized.InteriorMorreyHolder

/-!
# The Morrey/Caccioppoli bound for `∇v` (lane `L3a`, link 5)

Link 5 of lane `L3` (`reg/c2`) of `REGULARIZED_ROUTE.md`, Revision 2 (v):
`IsWeakLogSol.exists_morrey`, proved here as
`IsWeakLogSol.exists_morrey`.

## The Caccioppoli inequality with absorbed natural growth

`caccioppoli_core` is the quantitative heart.  Testing
`div ∇Ψ(∇v) = κ v + 2 m + B(∇v)` with `η² (v - v̄)` — legitimate by link 3
(`IsWeakLogSol.weakEq_memW0`), since `η² (v - v̄)` is a *bounded* element of `W₀^{1,2}` — gives

`∫ ⟪∇Ψ(∇v), η² ∇v⟫ + ∫ (v - v̄) ⟪∇Ψ(∇v), ∇(η²)⟫ + ∫ f η² (v - v̄) = 0`.

Ellipticity bounds the first term below by `c ∫ η² ‖∇v‖²`.  The second is
`2 ∫ (v - v̄) η ⟪∇Ψ(∇v), ∇η⟫`, which Young's inequality bounds by
`(c/4) ∫ η²‖∇v‖² + (4/c) (C K_∇η osc)² |B|`.  The third is bounded using
`|f| ≤ |κ| Mv + 2|m| + 2 C ‖∇v‖² + 2 |Ψ 0|` (`abs_regNatGrowth_le`) by
`osc · K · |B| + 2 C osc ∫ η² ‖∇v‖²`, and the last term is absorbed as soon as the oscillation
is small, `8 C osc ≤ c`.  What is left is

`(c/2) ∫ η² ‖∇v‖² ≤ ((4/c)(C K_∇η osc)² + osc K) |B_{2s}|`.

The whole computation is done as **one** pointwise inequality integrated once: the integrand
`⟪∇Ψ(G), ∇(η²(v-v̄))⟫ + f η²(v-v̄)`, whose integral vanishes, is bounded below pointwise by
`(c/2) η² ‖G‖² - D 1_{B_{2s}}`.

## From the Caccioppoli inequality to the Morrey bound

`exists_morrey` feeds `caccioppoli_core` with `v̄ = v y` and
`osc = Ch (2s)^α` coming from the local Hölder estimate of link 4
(`IsWeakLogSol.exists_local_holder`, `InteriorMorreyHolder.lean`); the smallness `8 C osc ≤ c`
holds on all small balls because `α > 0`, and `|B_{2s}| = c_d (2s)^d`, so the right-hand side is
`C (s^{2α-2} + s^{α}) s^d ≤ C s^{d-2+2α}` for `s ≤ 1`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ m c C : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ}
  {G : Euc d → Euc d}

/-! ### The pointwise inequality behind the Caccioppoli estimate -/

/-- **The pointwise Caccioppoli inequality.**  With `t = η x ∈ [0,1]`, `N = ∇η x`,
`w = v x - v̄`, `g = ∇v x` and `f` the right-hand side of the equation, the integrand of the
tested weak equation is bounded below by `(c/2) t² ‖g‖²` minus a constant:

* ellipticity gives `⟪∇Ψ g, g⟫ ≥ c ‖g‖²` (strong monotonicity at `q' = 0`, `∇Ψ 0 = 0`);
* Young's inequality absorbs `2 w t ⟪∇Ψ g, N⟫` into `(c/4) t²‖g‖² + (4/c)(C K_g osc)²`;
* the natural-growth bound `|f| ≤ Kc + 2C‖g‖²` and `8 C osc ≤ c` absorb `f t² w` into
  `osc Kc + (c/4) t²‖g‖²`.

Extracted as a separate declaration: inlining it into `IsWeakLogSol.caccioppoli_core` exhausts
the heartbeat budget. -/
theorem logSol_caccioppoli_pointwise (hΨ : IsRegProfile Ψ) (hCΨ : IsRegProfileWith Ψ c C)
    {g N : Euc d} {t w f Kg osc Kc : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hKg0 : 0 ≤ Kg)
    (hN : ‖N‖ ≤ Kg) (hosc0 : 0 ≤ osc) (hw : |w| ≤ osc) (hKc0 : 0 ≤ Kc)
    (hf : |f| ≤ Kc + 2 * C * ‖g‖ ^ 2) (hsmall : 8 * C * osc ≤ c) :
    c / 2 * (t ^ 2 * ‖g‖ ^ 2) - (4 / c * (C * Kg * osc) ^ 2 + osc * Kc) ≤
      ⟪gradient Ψ g, (t ^ 2) • g + w • ((2 * t) • N)⟫ + f * (t ^ 2 * w) := by
  have hc : 0 < c := hCΨ.c_pos
  have hC0 : 0 ≤ C := hCΨ.C_nonneg
  have hgn : (0:ℝ) ≤ ‖g‖ := norm_nonneg _
  have ht2 : (0:ℝ) ≤ t ^ 2 := sq_nonneg _
  -- the principal part
  have ha : c * ‖g‖ ^ 2 ≤ ⟪gradient Ψ g, g⟫ := by
    have h := hCΨ.inner_gradient_sub g 0
    rw [hΨ.gradient_zero, sub_zero, sub_zero] at h
    exact h
  have ha' : t ^ 2 * (c * ‖g‖ ^ 2) ≤ t ^ 2 * ⟪gradient Ψ g, g⟫ :=
    mul_le_mul_of_nonneg_left ha ht2
  have hsplit : ⟪gradient Ψ g, (t ^ 2) • g + w • ((2 * t) • N)⟫ =
      t ^ 2 * ⟪gradient Ψ g, g⟫ + 2 * w * t * ⟪gradient Ψ g, N⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right]
    ring
  -- the cutoff term
  have hIbd : |⟪gradient Ψ g, N⟫| ≤ C * ‖g‖ * Kg := by
    have h1 : |⟪gradient Ψ g, N⟫| ≤ ‖gradient Ψ g‖ * ‖N‖ := abs_real_inner_le_norm _ _
    have h2 : ‖gradient Ψ g‖ ≤ C * ‖g‖ := hCΨ.norm_gradient_le g
    nlinarith [norm_nonneg (gradient Ψ g), norm_nonneg N]
  have hchain : 2 * |w| * t * |⟪gradient Ψ g, N⟫| ≤ 2 * (t * ‖g‖) * (C * Kg * osc) := by
    calc 2 * |w| * t * |⟪gradient Ψ g, N⟫|
        = (2 * t * |⟪gradient Ψ g, N⟫|) * |w| := by ring
      _ ≤ (2 * t * |⟪gradient Ψ g, N⟫|) * osc :=
          mul_le_mul_of_nonneg_left hw
            (mul_nonneg (mul_nonneg (by norm_num) ht0) (abs_nonneg _))
      _ = (2 * t * osc) * |⟪gradient Ψ g, N⟫| := by ring
      _ ≤ (2 * t * osc) * (C * ‖g‖ * Kg) :=
          mul_le_mul_of_nonneg_left hIbd
            (mul_nonneg (mul_nonneg (by norm_num) ht0) hosc0)
      _ = 2 * (t * ‖g‖) * (C * Kg * osc) := by ring
  have habs : -(2 * (t * ‖g‖) * (C * Kg * osc)) ≤ 2 * w * t * ⟪gradient Ψ g, N⟫ := by
    have h1 : |2 * w * t * ⟪gradient Ψ g, N⟫| = 2 * |w| * t * |⟪gradient Ψ g, N⟫| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ht0]
      norm_num
    have h3 := neg_abs_le (2 * w * t * ⟪gradient Ψ g, N⟫)
    rw [h1] at h3
    linarith
  have hyoung : 2 * (t * ‖g‖) * (C * Kg * osc) ≤
      c / 4 * (t * ‖g‖) ^ 2 + 4 / c * (C * Kg * osc) ^ 2 := by
    have hid : c / 4 * (t * ‖g‖) ^ 2 + 4 / c * (C * Kg * osc) ^ 2
        - 2 * (t * ‖g‖) * (C * Kg * osc)
        = (c * (t * ‖g‖) - 4 * (C * Kg * osc)) ^ 2 / (4 * c) := by
      field_simp
      ring
    have hnn : 0 ≤ (c * (t * ‖g‖) - 4 * (C * Kg * osc)) ^ 2 / (4 * c) :=
      div_nonneg (sq_nonneg _) (by linarith)
    linarith
  -- the natural-growth term
  have hg2 : 0 ≤ t ^ 2 * ‖g‖ ^ 2 := mul_nonneg ht2 (sq_nonneg _)
  have hprod : |f * (t ^ 2 * w)| ≤ osc * Kc + c / 4 * (t ^ 2 * ‖g‖ ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht2]
    have hstep : |f| * (t ^ 2 * |w|) ≤ (Kc + 2 * C * ‖g‖ ^ 2) * (t ^ 2 * osc) := by
      refine mul_le_mul hf ?_ (mul_nonneg ht2 (abs_nonneg _)) (by nlinarith)
      exact mul_le_mul_of_nonneg_left hw ht2
    have h1 : 0 ≤ Kc * osc * (1 - t ^ 2) := by
      have : t ^ 2 ≤ 1 := by nlinarith
      exact mul_nonneg (mul_nonneg hKc0 hosc0) (by linarith)
    have h2 : 0 ≤ (c / 4 - 2 * C * osc) * (t ^ 2 * ‖g‖ ^ 2) :=
      mul_nonneg (by linarith) hg2
    nlinarith
  have hprod' : -(osc * Kc + c / 4 * (t ^ 2 * ‖g‖ ^ 2)) ≤ f * (t ^ 2 * w) := by
    have := neg_abs_le (f * (t ^ 2 * w))
    linarith
  have heq : (t * ‖g‖) ^ 2 = t ^ 2 * ‖g‖ ^ 2 := by ring
  rw [hsplit]
  linarith

/-! ### The Caccioppoli test function -/

/-- **`ζ (v - v̄)` is a `W₀^{1,2}` test function with the expected weak gradient.**  Here `ζ` is
any smooth cutoff supported in `B_{2s}` and `closedBall y (3s) ⊆ U`.

`v` itself is only *locally* weakly differentiable (`HasWeakGradientOn`), so the statement is
obtained by first globalizing `v` with a second cutoff `ζ₀`, equal to `1` on `B_{5s/2}` and
supported in `B_{3s}` (`IsWeakLogSol.memW0_mul_cutoff`), and then multiplying by `ζ` and
subtracting the constant (`Komlos.Literature.MemW0.contDiff_mul_const_add`).  On `B_{2s}` one has
`ζ₀ = 1` and `∇ζ₀ = 0`, so the auxiliary cutoff leaves no trace. -/
theorem IsWeakLogSol.memW0_cutoff_sub_const (hsol : IsWeakLogSol κ m Ψ U v G)
    {y : Euc d} {s : ℝ} (hspos : 0 < s) (hbs : Metric.closedBall y (3 * s) ⊆ U)
    {ζ : Euc d → ℝ} (hζC : ContDiff ℝ ∞ ζ) (hζs : HasCompactSupport ζ)
    (hζsub : tsupport ζ ⊆ Metric.closedBall y (2 * s)) (vb : ℝ) :
    MemW0 2 (Metric.closedBall y (2 * s)) (fun x => ζ x * (v x - vb)) ∧
      weakGrad (fun x => ζ x * (v x - vb)) =ᵐ[volume]
        fun x => ζ x • G x + (v x - vb) • gradient ζ x := by
  have hζzero : ∀ x, x ∉ Metric.closedBall y (2 * s) → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hζsub h)
  have hgζzero : ∀ x, x ∉ Metric.closedBall y (2 * s) → gradient ζ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport fun h => hx (hζsub h)
  obtain ⟨Ccut, _, hcut⟩ := exists_cutoff_const d
  obtain ⟨ζ₀, hζ₀C, hζ₀s, hζ₀ts, _, _, hζ₀one, _⟩ :=
    hcut y (5 * s / 2) (3 * s) (by linarith) (by linarith)
  obtain ⟨hvtw, hvtg⟩ := hsol.memW0_mul_cutoff hζ₀C hζ₀s (hζ₀ts.trans hbs) hbs hζ₀ts
  have hball25 : Metric.closedBall y (2 * s) ⊆ Metric.ball y (5 * s / 2) := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    linarith
  have hζK : tsupport ζ ⊆ tsupport ζ₀ := by
    refine hζsub.trans fun x hx => subset_closure (show ζ₀ x ≠ 0 from ?_)
    rw [hζ₀one x (Metric.closedBall_subset_closedBall (by linarith) hx)]
    norm_num
  obtain ⟨hφw, hφg⟩ := hvtw.contDiff_mul_const_add hζC hζs hζK (-vb)
  have hφval : ∀ x, ζ x * (-vb + ζ₀ x * v x) = ζ x * (v x - vb) := by
    intro x
    by_cases hx : x ∈ Metric.closedBall y (2 * s)
    · rw [hζ₀one x (Metric.closedBall_subset_closedBall (by linarith) hx)]; ring
    · rw [hζzero x hx]; ring
  have hfuneq : (fun x => ζ x * (-vb + ζ₀ x * v x)) = fun x => ζ x * (v x - vb) :=
    funext hφval
  rw [hfuneq] at hφw hφg
  have hgζ₀0 : ∀ x ∈ Metric.ball y (5 * s / 2), gradient ζ₀ x = 0 := by
    intro x hx
    have hev : ζ₀ =ᶠ[𝓝 x] fun _ : Euc d => (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
      exact hζ₀one z (Metric.ball_subset_closedBall hz)
    exact (hasGradientAt_const (x := x) (c := (1 : ℝ))).congr_of_eventuallyEq hev |>.gradient
  have hgrad : weakGrad (fun x => ζ x * (v x - vb)) =ᵐ[volume]
      fun x => ζ x • G x + (v x - vb) • gradient ζ x := by
    filter_upwards [hφg, hvtg.weakGrad_ae_eq] with x h1 h2
    rw [h1, h2]
    by_cases hx : x ∈ Metric.closedBall y (2 * s)
    · rw [hgζ₀0 x (hball25 hx),
        hζ₀one x (Metric.closedBall_subset_closedBall (by linarith) hx),
        smul_zero, add_zero, one_smul, show -vb + 1 * v x = v x - vb from by ring]
    · rw [hζzero x hx, hgζzero x hx]
      simp
  refine ⟨⟨hφw.memLp, Eventually.of_forall fun x hx => ?_, hφw.exists_weakGradient⟩, hgrad⟩
  show ζ x * (v x - vb) = 0
  rw [hζzero x hx, zero_mul]

/-! ### The Caccioppoli inequality -/

/-- **The Caccioppoli inequality for `v` with the natural-growth term absorbed.**  All the
geometric data are hypotheses: `η` is a cutoff, `1` on `B_s` and supported in `B_{2s}`, with
`‖∇η‖ ≤ Kg`; `Mv` bounds `|v|` on `B_{3s}`; `osc` bounds `|v - v̄|` on `B_{2s}`.  The absorption
of the natural-growth term needs the smallness `8 C osc ≤ c`.

The proof tests the equation with `η² (v - v̄)` through link 3
(`IsWeakLogSol.weakEq_memW0`; the test function is bounded, which is what that link requires),
and integrates the single pointwise inequality `logSol_caccioppoli_pointwise`. -/
theorem IsWeakLogSol.caccioppoli_core (hΨ : IsRegProfile Ψ) (hCΨ : IsRegProfileWith Ψ c C)
    (hsol : IsWeakLogSol κ m Ψ U v G)
    {y : Euc d} {s : ℝ} (hspos : 0 < s) (hbs : Metric.closedBall y (3 * s) ⊆ U)
    {η : Euc d → ℝ} (hηC : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηsub : tsupport η ⊆ Metric.closedBall y (2 * s))
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hηone : ∀ x ∈ Metric.closedBall y s, η x = 1)
    {Kg : ℝ} (hKg0 : 0 ≤ Kg) (hKg : ∀ x, ‖gradient η x‖ ≤ Kg)
    {Mv : ℝ} (hMv : ∀ x ∈ Metric.closedBall y (3 * s), |v x| ≤ Mv)
    {vb osc : ℝ} (hosc0 : 0 ≤ osc)
    (hosc : ∀ x ∈ Metric.closedBall y (2 * s), |v x - vb| ≤ osc)
    (hsmall : 8 * C * osc ≤ c) :
    (∫ x in Metric.ball y s, ‖G x‖ ^ 2) ≤
      2 / c * (4 / c * (C * Kg * osc) ^ 2 + osc * (|κ| * Mv + 2 * |m| + 2 * |Ψ 0|)) *
        (volume (Metric.closedBall y (2 * s))).toReal := by
  have hc : 0 < c := hCΨ.c_pos
  have hC0 : 0 ≤ C := hCΨ.C_nonneg
  have hMv0 : 0 ≤ Mv := (abs_nonneg (v y)).trans (hMv y (by simp; linarith))
  obtain ⟨Kc, hKcdef⟩ : ∃ t : ℝ, t = |κ| * Mv + 2 * |m| + 2 * |Ψ 0| := ⟨_, rfl⟩
  obtain ⟨Dcon, hDdef⟩ : ∃ t : ℝ, t = 4 / c * (C * Kg * osc) ^ 2 + osc * Kc := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by
    rw [hKcdef]
    have h1 : 0 ≤ |κ| * Mv := mul_nonneg (abs_nonneg _) hMv0
    linarith [abs_nonneg m, abs_nonneg (Ψ 0)]
  have hD0 : 0 ≤ Dcon := by
    rw [hDdef]
    have h1 : (0:ℝ) ≤ 4 / c * (C * Kg * osc) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    have h2 : (0:ℝ) ≤ osc * Kc := mul_nonneg hosc0 hKc0
    linarith
  rw [← hKcdef, ← hDdef]
  -- ### the cutoff `ζ = η²`
  obtain ⟨ζ, hζdef⟩ : ∃ f : Euc d → ℝ, f = fun x => η x ^ 2 := ⟨_, rfl⟩
  have hζval : ∀ x, ζ x = η x ^ 2 := fun x => by rw [hζdef]
  have hζC : ContDiff ℝ ∞ ζ := by rw [hζdef]; exact hηC.pow 2
  have hζsupp : Function.support ζ ⊆ tsupport η := fun x hx =>
    subset_closure (show η x ≠ 0 from fun h => hx (by rw [hζval x, h]; norm_num))
  have hζs : HasCompactSupport ζ := HasCompactSupport.of_support_subset_isCompact hηs hζsupp
  have hζsub : tsupport ζ ⊆ Metric.closedBall y (2 * s) :=
    (closure_minimal hζsupp (isClosed_tsupport η)).trans hηsub
  have hζ0 : ∀ x, 0 ≤ ζ x := fun x => by rw [hζval x]; exact sq_nonneg _
  have hζ1 : ∀ x, ζ x ≤ 1 := fun x => by
    rw [hζval x]; nlinarith [hη0 x, hη1 x]
  have hζzero : ∀ x, x ∉ Metric.closedBall y (2 * s) → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hζsub h)
  have hgζ : ∀ x, gradient ζ x = (2 * η x) • gradient η x := by
    intro x; rw [hζdef]; exact gradient_sq (hηC.of_le (by simp)) x
  have hgζzero : ∀ x, x ∉ Metric.closedBall y (2 * s) → gradient ζ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport fun h => hx (hζsub h)
  have hgζnorm : ∀ x, ‖gradient ζ x‖ ≤ 2 * Kg := by
    intro x
    rw [hgζ x, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hη0 x] : (0:ℝ) ≤ 2 * η x)]
    nlinarith [hKg x, norm_nonneg (gradient η x), hη0 x, hη1 x]
  -- ### the tested identity
  obtain ⟨hφw, hφgrad⟩ := hsol.memW0_cutoff_sub_const hspos hbs hζC hζs hζsub vb
  have hTc : IsCompact (Metric.closedBall y (2 * s)) := isCompact_closedBall _ _
  have hTsub : Metric.closedBall y (2 * s) ⊆ Metric.ball y (3 * s) := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    linarith
  have hφg0 : ∀ᵐ x, x ∉ Metric.closedBall y (2 * s) →
      weakGrad (fun x => ζ x * (v x - vb)) x = 0 := by
    filter_upwards [hφgrad] with x hx hxn
    rw [hx, hζzero x hxn, hgζzero x hxn]
    simp
  have hφb : ∀ x, |ζ x * (v x - vb)| ≤ osc := by
    intro x
    rw [abs_mul, abs_of_nonneg (hζ0 x)]
    by_cases hx : x ∈ Metric.closedBall y (2 * s)
    · calc ζ x * |v x - vb| ≤ 1 * osc :=
          mul_le_mul (hζ1 x) (hosc x hx) (abs_nonneg _) zero_le_one
        _ = osc := one_mul _
    · rw [hζzero x hx, zero_mul]; exact hosc0
  have key := hsol.weakEq_memW0 hΨ hbs hTc hTsub hφw hφg0 hφb
  have e1 : (∫ x, ⟪gradient Ψ (G x), weakGrad (fun z => ζ z * (v z - vb)) x⟫) =
      ∫ x, ⟪gradient Ψ (G x), ζ x • G x + (v x - vb) • gradient ζ x⟫ :=
    integral_congr_ae (hφgrad.mono fun x hx => by simp only [hx])
  rw [e1] at key
  -- ### integrability
  have hG2 : IntegrableOn (fun x => ‖G x‖ ^ 2) (Metric.closedBall y (2 * s)) volume :=
    (hsol.integrableOn_sq y (3 * s) hbs).mono_set
      (Metric.closedBall_subset_closedBall (by linarith))
  have hG1 : IntegrableOn G (Metric.closedBall y (2 * s)) volume :=
    integrableOn_of_integrableOn_sq_norm (isCompact_closedBall y (2 * s)).measure_lt_top.ne
      hsol.measurable_grad.aestronglyMeasurable.restrict hG2
  have hGn : IntegrableOn (fun x => ‖G x‖) (Metric.closedBall y (2 * s)) volume := hG1.norm
  have hf1 : IntegrableOn (regLogRhs κ m Ψ v G) (Metric.closedBall y (2 * s)) volume :=
    (hsol.integrableOn_rhs hΨ hbs).mono_set (Metric.closedBall_subset_closedBall (by linarith))
  have hmeasG : AEStronglyMeasurable (fun x => gradient Ψ (G x)) volume :=
    (hΨ.contDiff_gradient.continuous.measurable.comp hsol.measurable_grad).aestronglyMeasurable
  have hmeasW : AEStronglyMeasurable
      (fun x => ζ x • G x + (v x - vb) • gradient ζ x) volume :=
    ((hζC.continuous.measurable.smul hsol.measurable_grad).add
      ((hsol.measurable.sub measurable_const).smul
        (continuous_gradient (hζC.of_le (by simp))).measurable)).aestronglyMeasurable
  have iP1 : Integrable
      (fun x => ⟪gradient Ψ (G x), ζ x • G x + (v x - vb) • gradient ζ x⟫) volume := by
    refine integrable_of_bound_on_set (S := Metric.closedBall y (2 * s))
      measurableSet_closedBall (hmeasG.inner hmeasW)
      (b := fun x => C * ‖G x‖ ^ 2 + 2 * C * Kg * osc * ‖G x‖) ?_ ?_ ?_
    · exact (hG2.const_mul C).add (hGn.const_mul (2 * C * Kg * osc))
    · intro x hx
      have hb1 : ‖gradient Ψ (G x)‖ ≤ C * ‖G x‖ := hCΨ.norm_gradient_le (G x)
      have hb2 : ‖ζ x • G x + (v x - vb) • gradient ζ x‖ ≤ ‖G x‖ + osc * (2 * Kg) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζ0 x)]
          exact mul_le_of_le_one_left (norm_nonneg _) (hζ1 x)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hosc x hx) (hgζnorm x) (norm_nonneg _) hosc0
      have hcs : ‖⟪gradient Ψ (G x), ζ x • G x + (v x - vb) • gradient ζ x⟫‖ ≤
          ‖gradient Ψ (G x)‖ * ‖ζ x • G x + (v x - vb) • gradient ζ x‖ := by
        rw [Real.norm_eq_abs]
        exact abs_real_inner_le_norm _ _
      nlinarith [norm_nonneg (gradient Ψ (G x)), norm_nonneg (G x),
        norm_nonneg (ζ x • G x + (v x - vb) • gradient ζ x)]
    · intro x hx
      rw [hζzero x hx, hgζzero x hx, zero_smul, smul_zero, add_zero, inner_zero_right]
  have iP2 : Integrable (fun x => regLogRhs κ m Ψ v G x * (ζ x * (v x - vb))) volume := by
    refine integrable_of_bound_on_set (S := Metric.closedBall y (2 * s))
      measurableSet_closedBall
      ((hsol.measurable_rhs hΨ).aestronglyMeasurable.mul
        (hζC.continuous.aestronglyMeasurable.mul
          (hsol.measurable.sub measurable_const).aestronglyMeasurable))
      (b := fun x => osc * |regLogRhs κ m Ψ v G x|) ?_ ?_ ?_
    · exact hf1.abs.const_mul osc
    · intro x hx
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hζ0 x)]
      have h1 : ζ x * |v x - vb| ≤ osc := by
        calc ζ x * |v x - vb| ≤ 1 * osc :=
              mul_le_mul (hζ1 x) (hosc x hx) (abs_nonneg _) zero_le_one
          _ = osc := one_mul _
      nlinarith [abs_nonneg (regLogRhs κ m Ψ v G x)]
    · intro x hx
      rw [hζzero x hx, zero_mul, mul_zero]
  have hsum : (∫ x, (⟪gradient Ψ (G x), ζ x • G x + (v x - vb) • gradient ζ x⟫ +
      regLogRhs κ m Ψ v G x * (ζ x * (v x - vb)))) = 0 := by
    rw [integral_add iP1 iP2, key]
    ring
  -- ### the pointwise bound
  have hfbd : ∀ x ∈ Metric.closedBall y (2 * s),
      |regLogRhs κ m Ψ v G x| ≤ Kc + 2 * C * ‖G x‖ ^ 2 := by
    intro x hx
    have h1 : |v x| ≤ Mv := hMv x (Metric.closedBall_subset_closedBall (by linarith) hx)
    have h2 := abs_regNatGrowth_le hCΨ (G x)
    have h3 : |κ * v x + 2 * m + regNatGrowth Ψ (G x)| ≤
        |κ * v x + 2 * m| + |regNatGrowth Ψ (G x)| := abs_add_le _ _
    have h3' : |κ * v x + 2 * m| ≤ |κ * v x| + |2 * m| := abs_add_le _ _
    have h4 : |κ * v x| ≤ |κ| * Mv := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h5 : |2 * m| = 2 * |m| := by rw [abs_mul]; norm_num
    rw [hKcdef]
    simp only [regLogRhs]
    linarith
  have hpt : ∀ x, c / 2 * (ζ x * ‖G x‖ ^ 2) -
      Dcon * (Metric.closedBall y (2 * s)).indicator (fun _ => (1 : ℝ)) x ≤
      ⟪gradient Ψ (G x), ζ x • G x + (v x - vb) • gradient ζ x⟫ +
        regLogRhs κ m Ψ v G x * (ζ x * (v x - vb)) := by
    intro x
    by_cases hx : x ∈ Metric.closedBall y (2 * s)
    · rw [Set.indicator_of_mem hx, mul_one, hDdef, hζval x, hgζ x]
      exact logSol_caccioppoli_pointwise hΨ hCΨ (hη0 x) (hη1 x) hKg0 (hKg x) hosc0 (hosc x hx) hKc0
        (hfbd x hx) hsmall
    · rw [Set.indicator_of_notMem hx, mul_zero, hζzero x hx, hgζzero x hx]
      simp
  -- ### integrate
  have hζG : Integrable (fun x => ζ x * ‖G x‖ ^ 2) volume := by
    refine integrable_of_bound_on_set (S := Metric.closedBall y (2 * s))
      measurableSet_closedBall
      ((hζC.continuous.measurable.mul
        (hsol.measurable_grad.norm.pow_const 2)).aestronglyMeasurable)
      (b := fun x => ‖G x‖ ^ 2) hG2 ?_ ?_
    · intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hζ0 x) (sq_nonneg _))]
      nlinarith [hζ1 x, hζ0 x, sq_nonneg ‖G x‖]
    · intro x hx
      rw [hζzero x hx, zero_mul]
  have hind : Integrable
      (fun x => Dcon * (Metric.closedBall y (2 * s)).indicator (fun _ => (1 : ℝ)) x) volume := by
    refine Integrable.const_mul ?_ Dcon
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (isCompact_closedBall y (2 * s)).measure_lt_top.ne
  have hInt1 : Integrable (fun x => c / 2 * (ζ x * ‖G x‖ ^ 2) -
      Dcon * (Metric.closedBall y (2 * s)).indicator (fun _ => (1 : ℝ)) x) volume :=
    (hζG.const_mul (c / 2)).sub hind
  have hInt2 : Integrable (fun x => ⟪gradient Ψ (G x), ζ x • G x + (v x - vb) • gradient ζ x⟫ +
      regLogRhs κ m Ψ v G x * (ζ x * (v x - vb))) volume := iP1.add iP2
  have hmono : (∫ x, (c / 2 * (ζ x * ‖G x‖ ^ 2) -
      Dcon * (Metric.closedBall y (2 * s)).indicator (fun _ => (1 : ℝ)) x)) ≤
      ∫ x, (⟪gradient Ψ (G x), ζ x • G x + (v x - vb) • gradient ζ x⟫ +
        regLogRhs κ m Ψ v G x * (ζ x * (v x - vb))) := integral_mono hInt1 hInt2 hpt
  rw [hsum] at hmono
  have hRHSval : (∫ x, (c / 2 * (ζ x * ‖G x‖ ^ 2) -
      Dcon * (Metric.closedBall y (2 * s)).indicator (fun _ => (1 : ℝ)) x)) =
      c / 2 * (∫ x, ζ x * ‖G x‖ ^ 2) -
        Dcon * (volume (Metric.closedBall y (2 * s))).toReal := by
    rw [integral_sub (hζG.const_mul (c / 2)) hind, integral_const_mul, integral_const_mul,
      integral_indicator_const (1 : ℝ) measurableSet_closedBall]
    simp
    exact Or.inl rfl
  rw [hRHSval] at hmono
  -- ### conclude
  have hfin : (∫ x in Metric.ball y s, ‖G x‖ ^ 2) ≤ ∫ x, ζ x * ‖G x‖ ^ 2 := by
    have h1 : (∫ x in Metric.ball y s, ‖G x‖ ^ 2) = ∫ x in Metric.ball y s, ζ x * ‖G x‖ ^ 2 := by
      refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
      rw [hζval x, hηone x (Metric.ball_subset_closedBall hx)]
      norm_num
    rw [h1]
    exact setIntegral_le_integral hζG
      (Eventually.of_forall fun x => mul_nonneg (hζ0 x) (sq_nonneg _))
  have h2c : (0:ℝ) < 2 / c := by positivity
  have hid : 2 / c * (c / 2 * (∫ x, ζ x * ‖G x‖ ^ 2)) = ∫ x, ζ x * ‖G x‖ ^ 2 := by
    field_simp
  have hXle : (∫ x, ζ x * ‖G x‖ ^ 2) ≤
      2 / c * (Dcon * (volume (Metric.closedBall y (2 * s))).toReal) := by
    calc (∫ x, ζ x * ‖G x‖ ^ 2) = 2 / c * (c / 2 * (∫ x, ζ x * ‖G x‖ ^ 2)) := hid.symm
      _ ≤ 2 / c * (Dcon * (volume (Metric.closedBall y (2 * s))).toReal) :=
          mul_le_mul_of_nonneg_left (by linarith) h2c.le
  calc (∫ x in Metric.ball y s, ‖G x‖ ^ 2) ≤ ∫ x, ζ x * ‖G x‖ ^ 2 := hfin
    _ ≤ 2 / c * (Dcon * (volume (Metric.closedBall y (2 * s))).toReal) := hXle
    _ = 2 / c * Dcon * (volume (Metric.closedBall y (2 * s))).toReal := by ring

/-! ### Power bookkeeping -/

/-- `(s^α)² s^d / s² = s^{d-2+2α}`. -/
theorem rpow_morrey_identity {s α : ℝ} (hs : 0 < s) (d : ℕ) :
    (s ^ α) ^ 2 * s ^ d / s ^ 2 = s ^ ((d : ℝ) - 2 + 2 * α) := by
  have hs0 : (0:ℝ) ≤ s := hs.le
  have e1 : (s ^ α) ^ 2 = s ^ (2 * α) := by
    rw [← Real.rpow_natCast (s ^ α) 2, ← Real.rpow_mul hs0]
    congr 1
    push_cast
    ring
  have e2 : s ^ d = s ^ ((d : ℝ)) := (Real.rpow_natCast s d).symm
  have e3 : s ^ (2 : ℕ) = s ^ ((2 : ℝ)) := by
    rw [← Real.rpow_natCast s 2]
    norm_num
  rw [e1, e2, e3, ← Real.rpow_add hs, ← Real.rpow_sub hs]
  congr 1
  ring

/-- `s^α s^d ≤ s^{d-2+2α}` for `0 < s ≤ 1` and `α ≤ 2`. -/
theorem rpow_morrey_le {s α : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hα : α ≤ 2) (d : ℕ) :
    s ^ α * s ^ d ≤ s ^ ((d : ℝ) - 2 + 2 * α) := by
  have e2 : s ^ d = s ^ ((d : ℝ)) := (Real.rpow_natCast s d).symm
  rw [e2, ← Real.rpow_add hs]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)

/-- The volume of a closed ball of `Euc d`, as a real number. -/
theorem volume_closedBall_toReal (y : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall y r)).toReal =
      r ^ d * (volume (Metric.closedBall (0 : Euc d) 1)).toReal := by
  rw [Measure.addHaar_closedBall' volume y hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-! ### The Morrey bound -/

/-- **(5) The Morrey/Caccioppoli bound** `∫_{B_s} ‖∇v‖² ≤ C s^{d-2+2α}`.  This is the frozen
statement `Komlos.Literature.Regularized.IsWeakLogSol.exists_morrey` of
`InteriorRegularity.lean`, verbatim.

The Hölder estimate of link 4 (`IsWeakLogSol.exists_local_holder`) supplies both the smallness
of the oscillation that `caccioppoli_core` needs for the absorption of the natural-growth term,
and the rate `osc ≤ Ch (2s)^α` that turns the Caccioppoli inequality into the Morrey bound. -/
theorem IsWeakLogSol.exists_morrey (hΨ : IsRegProfile Ψ) (hsol : IsWeakLogSol κ m Ψ U v G)
    {x₀ : Euc d} (hx₀ : x₀ ∈ U) :
    ∃ r Cm α : ℝ, 0 < r ∧ 0 < α ∧ α < 1 ∧ Metric.closedBall x₀ r ⊆ U ∧
      ∀ y ∈ Metric.ball x₀ (r / 2), ∀ s : ℝ, 0 < s → s ≤ r / 2 →
        (∫ x in Metric.ball y s, ‖G x‖ ^ 2) ≤ Cm * s ^ ((d : ℝ) - 2 + 2 * α) := by
  obtain ⟨c, C, hCΨ⟩ := hΨ.exists_isRegProfileWith
  have hc : 0 < c := hCΨ.c_pos
  have hC0 : 0 ≤ C := hCΨ.C_nonneg
  obtain ⟨r₀, Ch, α, hr₀, hα0, hα1, hr₀U, hHol⟩ := hsol.exists_local_holder hΨ hx₀
  obtain ⟨Ch', hCh'0, hHol'⟩ : ∃ t : ℝ, 0 ≤ t ∧ ∀ y ∈ Metric.closedBall x₀ r₀,
      ∀ z ∈ Metric.closedBall x₀ r₀, |v y - v z| ≤ t * dist y z ^ α :=
    ⟨max Ch 0, le_max_right _ _, fun y hy z hz => (hHol y hy z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg α))⟩
  obtain ⟨Ccut, hCcut0, hcut⟩ := exists_cutoff_const d
  obtain ⟨Mv, hMv⟩ : ∃ M : ℝ, ∀ x ∈ Metric.closedBall x₀ r₀, |v x| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ r₀).exists_bound_of_continuousOn
      (hsol.continuousOn.mono hr₀U)
    exact ⟨M, fun x hx => by rw [← Real.norm_eq_abs]; exact hM x hx⟩
  have hMv0 : 0 ≤ Mv := (abs_nonneg (v x₀)).trans (hMv x₀ (Metric.mem_closedBall_self hr₀.le))
  obtain ⟨Kv, hKvdef⟩ : ∃ t : ℝ, t = |κ| * Mv + 2 * |m| + 2 * |Ψ 0| := ⟨_, rfl⟩
  have hKv0 : 0 ≤ Kv := by
    rw [hKvdef]
    have h1 : 0 ≤ |κ| * Mv := mul_nonneg (abs_nonneg _) hMv0
    linarith [abs_nonneg m, abs_nonneg (Ψ 0)]
  -- the radius
  obtain ⟨Bc, hBcdef⟩ : ∃ t : ℝ, t = 8 * C * Ch' + 1 := ⟨_, rfl⟩
  have hBc1 : 1 ≤ Bc := by rw [hBcdef]; nlinarith
  have hBc0 : 0 < Bc := by linarith
  obtain ⟨ρ, hρdef⟩ : ∃ t : ℝ, t = (c / Bc) ^ (1 / α) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hρα : ρ ^ α = c / Bc := by
    rw [hρdef, ← Real.rpow_mul (by positivity), one_div,
      inv_mul_cancel₀ (ne_of_gt hα0), Real.rpow_one]
  obtain ⟨r, hrdef⟩ : ∃ t : ℝ, t = min (min (r₀ / 2) 1) ρ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact lt_min (lt_min (by linarith) one_pos) hρ0
  have hrr₀ : r ≤ r₀ / 2 := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrρ : r ≤ ρ := by rw [hrdef]; exact min_le_right _ _
  have hV1 : (0:ℝ) ≤ (volume (Metric.closedBall (0 : Euc d) 1)).toReal := ENNReal.toReal_nonneg
  refine ⟨r, 2 / c * (volume (Metric.closedBall (0 : Euc d) 1)).toReal *
      (4 / c * ((C * Ccut * Ch') ^ 2 * ((2:ℝ) ^ α) ^ 2 * (2:ℝ) ^ d) +
        Kv * (Ch' * (2:ℝ) ^ α * (2:ℝ) ^ d)), α, hr0, hα0, hα1,
    (Metric.closedBall_subset_closedBall (by linarith)).trans hr₀U, ?_⟩
  intro y hy s hs hsr
  have hdy : dist y x₀ < r / 2 := Metric.mem_ball.1 hy
  have hb3 : Metric.closedBall y (3 * s) ⊆ Metric.closedBall x₀ r₀ := by
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    have ht := dist_triangle x y x₀
    linarith
  have hbs : Metric.closedBall y (3 * s) ⊆ U := hb3.trans hr₀U
  have hb2 : Metric.closedBall y (2 * s) ⊆ Metric.closedBall x₀ r₀ :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hb3
  obtain ⟨η, hηC, hηs, hηsub, hη0, hη1, hηone, hηg⟩ := hcut y s (2 * s) hs (by linarith)
  have hηg' : ∀ x, ‖gradient η x‖ ≤ Ccut / s := by
    intro x
    have h := hηg x
    rwa [show 2 * s - s = s from by ring] at h
  have hoscdef : ∀ x ∈ Metric.closedBall y (2 * s), |v x - v y| ≤ Ch' * (2 * s) ^ α := by
    intro x hx
    refine (hHol' x (hb2 hx) y (hb2 (Metric.mem_closedBall_self (by linarith)))).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCh'0
    exact Real.rpow_le_rpow dist_nonneg (Metric.mem_closedBall.1 hx) hα0.le
  have hsmall : 8 * C * (Ch' * (2 * s) ^ α) ≤ c := by
    have h1 : (2 * s) ^ α ≤ ρ ^ α :=
      Real.rpow_le_rpow (by linarith) (by linarith) hα0.le
    rw [hρα] at h1
    have h2 : (0:ℝ) ≤ 8 * C * Ch' := by positivity
    have h3 : 8 * C * Ch' / Bc ≤ 1 := (div_le_one hBc0).2 (by rw [hBcdef]; linarith)
    calc 8 * C * (Ch' * (2 * s) ^ α) = 8 * C * Ch' * (2 * s) ^ α := by ring
      _ ≤ 8 * C * Ch' * (c / Bc) := mul_le_mul_of_nonneg_left h1 h2
      _ = c * (8 * C * Ch' / Bc) := by ring
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left h3 hc.le
      _ = c := mul_one c
  have hcore := hsol.caccioppoli_core hΨ hCΨ hs hbs hηC hηs hηsub hη0 hη1 hηone
    (Kg := Ccut / s) (by positivity) hηg' (Mv := Mv) (fun x hx => hMv x (hb3 hx))
    (vb := v y) (osc := Ch' * (2 * s) ^ α)
    (mul_nonneg hCh'0 (Real.rpow_nonneg (by linarith) α)) hoscdef hsmall
  refine hcore.trans ?_
  rw [volume_closedBall_toReal y (by linarith : (0:ℝ) ≤ 2 * s), ← hKvdef]
  -- power bookkeeping
  have hmul : (2 * s) ^ α = (2:ℝ) ^ α * s ^ α := Real.mul_rpow (by norm_num) hs.le
  have hnat : (2 * s) ^ d = (2:ℝ) ^ d * s ^ d := mul_pow 2 s d
  have hid := rpow_morrey_identity (α := α) hs d
  have hle := rpow_morrey_le (α := α) hs (by linarith) (by linarith) d
  have hX : (C * (Ccut / s) * (Ch' * (2 * s) ^ α)) ^ 2 * (2 * s) ^ d =
      ((C * Ccut * Ch') ^ 2 * ((2:ℝ) ^ α) ^ 2 * (2:ℝ) ^ d) * s ^ ((d : ℝ) - 2 + 2 * α) := by
    rw [hmul, hnat, ← hid]
    field_simp
    try ring
  have hA2 : (0:ℝ) ≤ Ch' * (2:ℝ) ^ α * (2:ℝ) ^ d :=
    mul_nonneg (mul_nonneg hCh'0 (Real.rpow_nonneg (by norm_num) α)) (by positivity)
  have hY : (Ch' * (2 * s) ^ α) * (2 * s) ^ d ≤
      (Ch' * (2:ℝ) ^ α * (2:ℝ) ^ d) * s ^ ((d : ℝ) - 2 + 2 * α) := by
    rw [hmul, hnat, show Ch' * ((2:ℝ) ^ α * s ^ α) * ((2:ℝ) ^ d * s ^ d)
      = (Ch' * (2:ℝ) ^ α * (2:ℝ) ^ d) * (s ^ α * s ^ d) from by ring]
    exact mul_le_mul_of_nonneg_left hle hA2
  have hpre : (0:ℝ) ≤ 2 / c * (volume (Metric.closedBall (0 : Euc d) 1)).toReal := by positivity
  calc 2 / c * (4 / c * (C * (Ccut / s) * (Ch' * (2 * s) ^ α)) ^ 2 +
        Ch' * (2 * s) ^ α * Kv) *
        ((2 * s) ^ d * (volume (Metric.closedBall (0 : Euc d) 1)).toReal)
      = 2 / c * (volume (Metric.closedBall (0 : Euc d) 1)).toReal *
          (4 / c * ((C * (Ccut / s) * (Ch' * (2 * s) ^ α)) ^ 2 * (2 * s) ^ d) +
            Kv * ((Ch' * (2 * s) ^ α) * (2 * s) ^ d)) := by ring
    _ ≤ 2 / c * (volume (Metric.closedBall (0 : Euc d) 1)).toReal *
          (4 / c * (((C * Ccut * Ch') ^ 2 * ((2:ℝ) ^ α) ^ 2 * (2:ℝ) ^ d) *
              s ^ ((d : ℝ) - 2 + 2 * α)) +
            Kv * ((Ch' * (2:ℝ) ^ α * (2:ℝ) ^ d) * s ^ ((d : ℝ) - 2 + 2 * α))) := by
        refine mul_le_mul_of_nonneg_left ?_ hpre
        rw [hX]
        have h2 : Kv * ((Ch' * (2 * s) ^ α) * (2 * s) ^ d) ≤
            Kv * ((Ch' * (2:ℝ) ^ α * (2:ℝ) ^ d) * s ^ ((d : ℝ) - 2 + 2 * α)) :=
          mul_le_mul_of_nonneg_left hY hKv0
        linarith
    _ = 2 / c * (volume (Metric.closedBall (0 : Euc d) 1)).toReal *
          (4 / c * ((C * Ccut * Ch') ^ 2 * ((2:ℝ) ^ α) ^ 2 * (2:ℝ) ^ d) +
            Kv * (Ch' * (2:ℝ) ^ α * (2:ℝ) ^ d)) * s ^ ((d : ℝ) - 2 + 2 * α) := by ring

end Komlos.Literature.Regularized
