import Komlos.Literature.Regularized.InteriorMorreyDG
import Komlos.Literature.Regularized.DeGiorgiOsc

/-!
# Local Hölder continuity of `v` (lane `L3a`, link 4)

Link 4 of lane `L3` (`reg/c2`) of `REGULARIZED_ROUTE.md`, Revision 2 (v):
`IsWeakLogSol.exists_local_holder`, proved here as
`IsWeakLogSol.exists_local_holder`.

## The route, and why the shortcut is unavailable

The obvious shortcut is to read the Hölder continuity of `v = -log φ` off that of `φ`: lane `L2`
proves that a positive continuous minimizer is locally Hölder and locally bounded below by a
positive constant (`IsDG.exists_holder_representative` applied to the De Giorgi class of the
*minimization problem*), and `log` is Lipschitz on `[δ, M]`.

That shortcut is **not available from the hypotheses of this link**.  `IsWeakLogSol` records only
that `v` is a continuous weak solution of
`div ∇Ψ(∇v) = κ v + 2 m + B(∇v)` on `U`; it carries no minimality, and no function `φ` at all.
Deriving Hölder continuity therefore has to be done from the equation, by the Stampacchia route
described in the docstring of the frozen statement.

Note moreover that simply *adding* "`φ = e^{-v}` is locally Hölder" as a hypothesis would be
circular: `IsWeakLogSol` already gives `v` continuous on `U`, so `φ = e^{-v}` is automatically
continuous and locally bounded between two positive constants on every compact subset of `U`,
and on such a set `log` and `exp` are bi-Lipschitz — the hypothesis would therefore be
*equivalent* to the conclusion.  The only non-circular strengthening is to replace the
hypothesis `IsWeakLogSol κ m Ψ U v G` by the *minimality* datum from which lane `L2` derives the
De Giorgi class (e.g. `IsDG γ χ R₀ U (fun x => Real.exp (-v x)) H` for some admissible
constants).  That would propagate to `IsWeakLogSol.contDiffOn_two` and hence to the whole chain,
so the frozen statements are left unchanged and the Stampacchia route is taken instead; this is
**not** a deviation.

## What is missing

The Stampacchia substitution: on a ball `B ⋐ U`, `v` is bounded (it is continuous on `U`), say
`|v| ≤ S`.  Testing the equation with `η² (e^{λ (v-k)_+} - 1)`, `λ = 2 C / c` with `c, C` the
ellipticity constants of `Ψ`, absorbs the natural-growth term `B(∇v)` — `|B(q)| ≤ 2C‖q‖² + 2|Ψ0|`
(`abs_regNatGrowth_le`) — into the principal part, and produces the level-set energy inequality

`∫_{B_r ∩ {v > k}} ‖∇v‖² ≤ γ (s-r)⁻² ∫_{B_s} ((v-k)_+)² + γ χ² |B_s ∩ {v > k}|`

with `γ = γ(c, C, e^{2λS})` and `χ = χ(κ S, |m|, |Ψ 0|, c)`, i.e. membership of the De Giorgi
class `IsDGSub` of `Komlos/Literature/Regularized/DeGiorgiClass.lean`.  Since `∇Ψ` is odd and
`B` is even, `-v` solves the equation with `m ↦ -m` and the same bound on the natural-growth
term, so the same computation gives `IsDGSub` for `-v`, i.e. `IsDG`.  The De Giorgi class is
then converted to a Hölder estimate by `IsDG.exists_holder_representative` (lane `DGN`).

Both steps need the globalization of `InteriorMorreyAux.lean` (`IsDGSub` is stated with a global
weak gradient and `IsDG.exists_holder_representative` with a global sup bound), and the test
functions are bounded elements of `W₀^{1,2}`, so the weak equation is used through
`IsWeakLogSol.weakEq_memW0` (link 3, `InteriorWeakEq.lean`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ m : ℝ} {Ψ : Euc d → ℝ} {U : Set (Euc d)} {v : Euc d → ℝ} {G : Euc d → Euc d}

/-! ### An elementary `rpow` comparison -/

/-- On `[0, M]` with `M ≥ 1`, a larger Hölder exponent is stronger:
`t^b ≤ M^{b-a} t^a` for `0 < a ≤ b`. -/
theorem rpow_le_rpow_exponent_swap {t M a b : ℝ} (ht : 0 ≤ t) (_hM : 1 ≤ M) (htM : t ≤ M)
    (ha : 0 < a) (hab : a ≤ b) : t ^ b ≤ M ^ (b - a) * t ^ a := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, Real.zero_rpow (by linarith : b ≠ 0), Real.zero_rpow ha.ne', mul_zero]
  · have hb : t ^ b = t ^ a * t ^ (b - a) := by
      rw [← Real.rpow_add h]
      congr 1
      ring
    rw [hb, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht a)
    exact Real.rpow_le_rpow h.le htM (by linarith)

/-! ### The De Giorgi class membership of `v` -/

/-- **The Stampacchia step.**  Near any point of `U`, the solution `v` — after being cut off so
as to become globally Sobolev and globally bounded — belongs to a De Giorgi class
`IsDG γ χ ρ (ball x₀ ρ)` of `Komlos/Literature/Regularized/DeGiorgiClass.lean`.

This is the only genuinely missing ingredient of link 4; see the module docstring for the
Stampacchia exponential substitution that produces it. -/
theorem IsWeakLogSol.exists_isDG (hΨ : IsRegProfile Ψ) (hsol : IsWeakLogSol κ m Ψ U v G)
    {x₀ : Euc d} (hx₀ : x₀ ∈ U) :
    ∃ (ρ γ χ S : ℝ) (z : Euc d → ℝ) (H : Euc d → Euc d),
      0 < ρ ∧ 0 ≤ γ ∧ 0 ≤ χ ∧ Metric.closedBall x₀ ρ ⊆ U ∧
      (∀ x ∈ Metric.ball x₀ ρ, z x = v x) ∧ (∀ x, |z x| ≤ S) ∧
      IsDG γ χ ρ (Metric.ball x₀ ρ) z H := by
  obtain ⟨c, C, hCΨ⟩ := hΨ.exists_isRegProfileWith
  -- ### the geometry
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hsol.isOpen x₀ hx₀
  obtain ⟨R, hRdef⟩ : ∃ t : ℝ, t = ε / 2 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; linarith
  have hRU : Metric.closedBall x₀ R ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hεU
    rw [hRdef]; linarith
  obtain ⟨Ccut, _, hcut⟩ := exists_cutoff_const d
  obtain ⟨ζ₀, hζ₀C, hζ₀s, hζ₀ts, _, _, hζ₀one, _⟩ :=
    hcut x₀ (2 * R / 3) R (by linarith) (by linarith)
  have hζ₀U : tsupport ζ₀ ⊆ U := hζ₀ts.trans hRU
  obtain ⟨ρ, hρdef⟩ : ∃ t : ℝ, t = R / 3 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρU : Metric.closedBall x₀ ρ ⊆ U :=
    (Metric.closedBall_subset_closedBall (by rw [hρdef]; linarith)).trans hRU
  have hballsub : Metric.ball x₀ ρ ⊆ Metric.ball x₀ (2 * R / 3) :=
    Metric.ball_subset_ball (by rw [hρdef]; linarith)
  -- ### the globalized solution
  obtain ⟨hzW, hzHw⟩ := hsol.memW0_mul_cutoff hζ₀C hζ₀s hζ₀U hRU hζ₀ts
  have hζ₀1 : ∀ x ∈ Metric.ball x₀ ρ, ζ₀ x = 1 := fun x hx =>
    hζ₀one x (Metric.ball_subset_closedBall (hballsub hx))
  have hgζ₀0 : ∀ x ∈ Metric.ball x₀ (2 * R / 3), gradient ζ₀ x = 0 := by
    intro x hx
    have hev : ζ₀ =ᶠ[𝓝 x] fun _ : Euc d => (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with w hw
      exact hζ₀one w (Metric.ball_subset_closedBall hw)
    exact (hasGradientAt_const (x := x) (c := (1 : ℝ))).congr_of_eventuallyEq hev |>.gradient
  have hzv : ∀ x ∈ Metric.ball x₀ ρ, ζ₀ x * v x = v x := fun x hx => by
    rw [hζ₀1 x hx, one_mul]
  have hHG : ∀ x ∈ Metric.ball x₀ ρ,
      ζ₀ x • G x + v x • gradient ζ₀ x = G x := fun x hx => by
    rw [hζ₀1 x hx, hgζ₀0 x (hballsub hx), one_smul, smul_zero, add_zero]
  have hballK : Metric.ball x₀ ρ ⊆ tsupport ζ₀ := fun x hx =>
    subset_closure (show ζ₀ x ≠ 0 by rw [hζ₀1 x hx]; norm_num)
  -- ### `z` is bounded
  have hζ₀zero : ∀ x, x ∉ tsupport ζ₀ → ζ₀ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx
  have hzc : Continuous fun x => ζ₀ x * v x := by
    have h := Komlos.Literature.Korevaar.continuous_mul_of_continuousOn hsol.isOpen
      hsol.continuousOn hζ₀C.continuous (isClosed_tsupport ζ₀) hζ₀U hζ₀zero
    exact h.congr fun x => mul_comm (v x) (ζ₀ x)
  have hzs : HasCompactSupport fun x => ζ₀ x * v x := hζ₀s.mul_right
  obtain ⟨S, hSbd⟩ := hzc.bounded_above_of_compact_support hzs
  have hS : ∀ x, |ζ₀ x * v x| ≤ S := fun x => by
    rw [← Real.norm_eq_abs]; exact hSbd x
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS x₀)
  -- ### measurability
  have hzm : Measurable fun x => ζ₀ x * v x := hζ₀C.continuous.measurable.mul hsol.measurable
  have hHm : Measurable fun x => ζ₀ x • G x + v x • gradient ζ₀ x :=
    (hζ₀C.continuous.measurable.smul hsol.measurable_grad).add
      (hsol.measurable.smul (continuous_gradient (hζ₀C.of_le (by simp))).measurable)
  -- ### the right-hand side
  obtain ⟨A, hAdef⟩ : ∃ t : ℝ, t = |κ| * S + 2 * |m| + 2 * |Ψ 0| := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have : 0 ≤ |κ| * S := mul_nonneg (abs_nonneg _) hS0
    linarith [abs_nonneg m, abs_nonneg (Ψ 0)]
  have hfbd : ∀ x, |κ * (ζ₀ x * v x) + 2 * m +
      regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x)| ≤
      A + 2 * C * ‖ζ₀ x • G x + v x • gradient ζ₀ x‖ ^ 2 := by
    intro x
    have h1 : |κ * (ζ₀ x * v x)| ≤ |κ| * S := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hS x) (abs_nonneg _)
    have h2 := abs_regNatGrowth_le hCΨ (ζ₀ x • G x + v x • gradient ζ₀ x)
    have h3 : |2 * m| = 2 * |m| := by rw [abs_mul]; norm_num
    have ha := abs_add_le (κ * (ζ₀ x * v x) + 2 * m)
      (regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x))
    have hb := abs_add_le (κ * (ζ₀ x * v x)) (2 * m)
    rw [hAdef]
    linarith
  have hfm : Measurable fun x => κ * (ζ₀ x * v x) + 2 * m +
      regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x) :=
    ((measurable_const.mul hzm).add measurable_const).add
      ((continuous_regNatGrowth hΨ).measurable.comp hHm)
  -- ### the hypotheses of `exists_isDGSub_of_weak`
  have hH2 : ∀ (y : Euc d) (s : ℝ), Metric.closedBall y s ⊆ Metric.ball x₀ ρ →
      IntegrableOn (fun x => ‖ζ₀ x • G x + v x • gradient ζ₀ x‖ ^ 2)
        (Metric.closedBall y s) volume := by
    intro y s hs
    have hsU : Metric.closedBall y s ⊆ U :=
      hs.trans (Metric.ball_subset_closedBall.trans hρU)
    refine ((hsol.integrableOn_sq y s hsU).congr_fun ?_ measurableSet_closedBall)
    intro x hx
    show ‖G x‖ ^ 2 = ‖ζ₀ x • G x + v x • gradient ζ₀ x‖ ^ 2
    rw [hHG x (hs hx)]
  have hweak : ∀ (y : Euc d) (s : ℝ), Metric.closedBall y s ⊆ Metric.ball x₀ ρ →
      ∀ w : Euc d → ℝ, MemW0 2 (Metric.closedBall y s) w →
      (∀ᵐ x, x ∉ Metric.closedBall y s → weakGrad w x = 0) →
      ∀ Mw : ℝ, (∀ x, |w x| ≤ Mw) →
      (∫ x, ⟪gradient Ψ (ζ₀ x • G x + v x • gradient ζ₀ x), weakGrad w x⟫) =
        -∫ x, (κ * (ζ₀ x * v x) + 2 * m +
          regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x)) * w x := by
    intro y s hs w hw hwg Mw hwb
    have h1 : (∫ x, ⟪gradient Ψ (ζ₀ x • G x + v x • gradient ζ₀ x), weakGrad w x⟫) =
        ∫ x, ⟪gradient Ψ (G x), weakGrad w x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [hwg] with x hx
      show ⟪gradient Ψ (ζ₀ x • G x + v x • gradient ζ₀ x), weakGrad w x⟫ =
        ⟪gradient Ψ (G x), weakGrad w x⟫
      by_cases hb : x ∈ Metric.closedBall y s
      · rw [hHG x (hs hb)]
      · rw [hx hb, inner_zero_right, inner_zero_right]
    have h2 := hsol.weakEq_memW0 hΨ hρU (isCompact_closedBall y s) hs hw hwg hwb
    have h3 : (∫ x, regLogRhs κ m Ψ v G x * w x) =
        ∫ x, (κ * (ζ₀ x * v x) + 2 * m +
          regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x)) * w x := by
      refine integral_congr_ae ?_
      filter_upwards [hw.ae_eq_zero] with x hx
      show regLogRhs κ m Ψ v G x * w x = _
      by_cases hb : x ∈ Metric.closedBall y s
      · simp only [regLogRhs]
        rw [hHG x (hs hb), hzv x (hs hb)]
      · rw [hx hb, mul_zero, mul_zero]
    rw [h1, h2, h3]
  -- ### the De Giorgi class for `z` and for `-z`
  obtain ⟨γ₁, χ₁, hγ₁, hχ₁, hDG₁⟩ := exists_isDGSub_of_weak hΨ hCΨ hballK hzW hzm hzHw hHm
    hfm hS hA0 hfbd hH2 hweak
  have hnegz : ((-1:ℝ) • fun x => ζ₀ x * v x) = fun x => -(ζ₀ x * v x) := by
    funext x; simp
  have hnegH : ((-1:ℝ) • fun x => ζ₀ x • G x + v x • gradient ζ₀ x) =
      fun x => -(ζ₀ x • G x + v x • gradient ζ₀ x) := by
    funext x
    show (-1:ℝ) • (ζ₀ x • G x + v x • gradient ζ₀ x) =
      -(ζ₀ x • G x + v x • gradient ζ₀ x)
    rw [neg_one_smul]
  have hzWn : MemW0 2 (tsupport ζ₀) (fun x => -(ζ₀ x * v x)) := hnegz ▸ (hzW.smul (-1))
  have hzHwn : HasWeakGradient (fun x => -(ζ₀ x * v x))
      (fun x => -(ζ₀ x • G x + v x • gradient ζ₀ x)) := by
    have h := hzHw.smul (-1)
    rw [hnegz, hnegH] at h
    exact h
  have hSn : ∀ x, |-(ζ₀ x * v x)| ≤ S := fun x => by rw [abs_neg]; exact hS x
  have hfbdn : ∀ x, |-(κ * (ζ₀ x * v x) + 2 * m +
      regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x))| ≤
      A + 2 * C * ‖-(ζ₀ x • G x + v x • gradient ζ₀ x)‖ ^ 2 := by
    intro x
    rw [abs_neg, norm_neg]
    exact hfbd x
  have hH2n : ∀ (y : Euc d) (s : ℝ), Metric.closedBall y s ⊆ Metric.ball x₀ ρ →
      IntegrableOn (fun x => ‖-(ζ₀ x • G x + v x • gradient ζ₀ x)‖ ^ 2)
        (Metric.closedBall y s) volume := by
    intro y s hs
    refine ((hH2 y s hs).congr_fun ?_ measurableSet_closedBall)
    intro x _
    show ‖ζ₀ x • G x + v x • gradient ζ₀ x‖ ^ 2 =
      ‖-(ζ₀ x • G x + v x • gradient ζ₀ x)‖ ^ 2
    rw [norm_neg]
  have hweakn : ∀ (y : Euc d) (s : ℝ), Metric.closedBall y s ⊆ Metric.ball x₀ ρ →
      ∀ w : Euc d → ℝ, MemW0 2 (Metric.closedBall y s) w →
      (∀ᵐ x, x ∉ Metric.closedBall y s → weakGrad w x = 0) →
      ∀ Mw : ℝ, (∀ x, |w x| ≤ Mw) →
      (∫ x, ⟪gradient Ψ (-(ζ₀ x • G x + v x • gradient ζ₀ x)), weakGrad w x⟫) =
        -∫ x, (-(κ * (ζ₀ x * v x) + 2 * m +
          regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x))) * w x := by
    intro y s hs w hw hwg Mw hwb
    have h1 : (∫ x, ⟪gradient Ψ (-(ζ₀ x • G x + v x • gradient ζ₀ x)), weakGrad w x⟫) =
        -∫ x, ⟪gradient Ψ (ζ₀ x • G x + v x • gradient ζ₀ x), weakGrad w x⟫ := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ⟪gradient Ψ (-(ζ₀ x • G x + v x • gradient ζ₀ x)), weakGrad w x⟫ = _
      rw [hΨ.gradient_neg, inner_neg_left]
    have h2 := hweak y s hs w hw hwg Mw hwb
    have h3 : (∫ x, (-(κ * (ζ₀ x * v x) + 2 * m +
        regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x))) * w x) =
        -∫ x, (κ * (ζ₀ x * v x) + 2 * m +
          regNatGrowth Ψ (ζ₀ x • G x + v x • gradient ζ₀ x)) * w x := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      ring
    rw [h1, h2, h3]
    try ring
  obtain ⟨γ₂, χ₂, hγ₂, hχ₂, hDG₂⟩ := exists_isDGSub_of_weak hΨ hCΨ hballK hzWn hzm.neg hzHwn
    hHm.neg hfm.neg hSn hA0 hfbdn hH2n hweakn
  refine ⟨ρ, max γ₁ γ₂, max χ₁ χ₂, S, (fun x => ζ₀ x * v x),
    (fun x => ζ₀ x • G x + v x • gradient ζ₀ x), hρ,
    le_trans hγ₁ (le_max_left _ _), le_trans hχ₁ (le_max_left _ _), hρU, hzv, hS,
    ⟨hDG₁.mono hγ₁ (le_max_left _ _) hχ₁ (le_max_left _ _),
      hDG₂.mono hγ₂ (le_max_right _ _) hχ₂ (le_max_right _ _)⟩⟩

/-! ### The frozen statement -/

/-- **(4) `v` is locally Hölder continuous on `U`.**  This is the frozen statement
`Komlos.Literature.Regularized.IsWeakLogSol.exists_local_holder` of `InteriorRegularity.lean`,
verbatim.

See the module docstring: the proof is the Stampacchia exponential substitution, which places
`v` in the De Giorgi class `IsDG` of `Komlos/Literature/Regularized/DeGiorgiClass.lean`, followed
by `IsDG.exists_holder_representative`. -/
-- TODO(reg/c2a): the Stampacchia substitution.  Concretely: (i) globalize `v` on a ball
-- `B(x₀, 3ρ) ⊆ U` with `IsWeakLogSol.memW0_mul_cutoff`; (ii) test the equation
-- (`IsWeakLogSol.weakEq_memW0`) with `η² (e^{λ (v-k)_+} - 1)`, `λ = 2C/c`, and collect the
-- level-set energy inequality, i.e. `IsDGSub γ χ ρ (ball x₀ ρ) ṽ G̃` and the same for `-ṽ`;
-- (iii) apply `IsDG.exists_holder_representative` and identify its representative with `v`
-- (two functions continuous on an open set and a.e. equal there are equal).
theorem IsWeakLogSol.exists_local_holder (hΨ : IsRegProfile Ψ) (hsol : IsWeakLogSol κ m Ψ U v G)
    {x₀ : Euc d} (hx₀ : x₀ ∈ U) :
    ∃ r Ch α : ℝ, 0 < r ∧ 0 < α ∧ α < 1 ∧ Metric.closedBall x₀ r ⊆ U ∧
      ∀ y ∈ Metric.closedBall x₀ r, ∀ z ∈ Metric.closedBall x₀ r,
        |v y - v z| ≤ Ch * dist y z ^ α := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- `Euc 0` is a single point, so every statement of this shape is vacuous
    subst hd0
    obtain ⟨t, ht, htU⟩ := Metric.isOpen_iff.1 hsol.isOpen x₀ hx₀
    refine ⟨t / 2, 0, 1 / 2, by linarith, by norm_num, by norm_num,
      (Metric.closedBall_subset_ball (by linarith)).trans htU, fun y _ z _ => ?_⟩
    have hyz : y = z := Subsingleton.elim y z
    rw [hyz]
    simp
  obtain ⟨ρ, γ, χ, S, z, H, hρ, hγ, hχ, hρU, hzv, hzS, hDG⟩ := hsol.exists_isDG hΨ hx₀
  obtain ⟨ϕ, hϕae, hϕc, hϕH⟩ :=
    hDG.exists_holder_representative hd hγ hχ hρ Metric.isOpen_ball hzS
  -- the representative is `v` itself on the ball
  have hvc : ContinuousOn v (Metric.ball x₀ ρ) :=
    hsol.continuousOn.mono (Metric.ball_subset_closedBall.trans hρU)
  have hzc : ContinuousOn z (Metric.ball x₀ ρ) := hvc.congr fun x hx => hzv x hx
  have hϕz : Set.EqOn ϕ z (Metric.ball x₀ ρ) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hϕae Metric.isOpen_ball hϕc hzc
  have hϕv : ∀ x ∈ Metric.ball x₀ ρ, ϕ x = v x := fun x hx => (hϕz hx).trans (hzv x hx)
  -- the Hölder estimate on the half ball
  have hTsub : Metric.closedBall x₀ (ρ / 2) ⊆ Metric.ball x₀ ρ :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨Cn, rn, hrn0, hHol⟩ :=
    hϕH (Metric.closedBall x₀ (ρ / 2)) (isCompact_closedBall _ _) hTsub
  have hrn : (0:ℝ) < (rn : ℝ) := by exact_mod_cast hrn0
  obtain ⟨α, hαdef⟩ : ∃ t : ℝ, t = min (rn : ℝ) (1 / 2) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; exact lt_min hrn (by norm_num)
  have hα1 : α < 1 := by
    rw [hαdef]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hαr : α ≤ (rn : ℝ) := by rw [hαdef]; exact min_le_left _ _
  obtain ⟨M, hMdef⟩ : ∃ t : ℝ, t = max ρ 1 := ⟨_, rfl⟩
  have hM1 : (1:ℝ) ≤ M := by rw [hMdef]; exact le_max_right _ _
  refine ⟨ρ / 2, (Cn : ℝ) * M ^ ((rn : ℝ) - α), α, by linarith, hα0, hα1,
    (Metric.closedBall_subset_closedBall (by linarith)).trans hρU, fun y hy w hw => ?_⟩
  have hdyw : dist y w ≤ M := by
    have h1 := Metric.mem_closedBall.1 hy
    have h2 := Metric.mem_closedBall.1 hw
    have h3 : dist y w ≤ dist y x₀ + dist x₀ w := dist_triangle y x₀ w
    rw [dist_comm x₀ w] at h3
    have h4 : dist y w ≤ ρ := by linarith
    rw [hMdef]
    exact h4.trans (le_max_left _ _)
  have hdist := hHol.dist_le hy hw
  rw [Real.dist_eq, hϕv y (hTsub hy), hϕv w (hTsub hw)] at hdist
  have hswap : dist y w ^ ((rn : ℝ)) ≤ M ^ ((rn : ℝ) - α) * dist y w ^ α :=
    rpow_le_rpow_exponent_swap dist_nonneg hM1 hdyw hα0 hαr
  calc |v y - v w| ≤ (Cn : ℝ) * dist y w ^ ((rn : ℝ)) := hdist
    _ ≤ (Cn : ℝ) * (M ^ ((rn : ℝ) - α) * dist y w ^ α) :=
        mul_le_mul_of_nonneg_left hswap Cn.coe_nonneg
    _ = (Cn : ℝ) * M ^ ((rn : ℝ) - α) * dist y w ^ α := by ring

end Komlos.Literature.Regularized
