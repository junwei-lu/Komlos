import Komlos.Literature.Regularized.PositivityLowerPos

/-!
# Lane `L2p` (`reg/pos-lower`), step 4: the local positive lower bound

`REGULARIZED_ROUTE.md`, Revision 2 (iii).  This file proves `exists_local_lower_bound`, the
frozen statement `exists_local_lower_bound` of
`Komlos/Literature/Regularized/Positivity.lean` verbatim: on a ball around every interior point
the minimizer is bounded below by a positive constant.

## The proof

The lane's original plan ran the De Giorgi machinery on the **shifted logarithm**
`Z_δ = log δ - log(v + δ)`; the `W₀^{1,2}` facts about `Z_δ` that were proved for that route are
kept below (`memW0_shiftedLog`, `abs_shiftedLog_le`), but the route itself has been **replaced**
by the shorter and logarithm-free argument of
`Komlos/Literature/Regularized/PositivityLowerPos.lean`:

* the **rescaled level function** `w_l = -min(v,l)/l` lies in `DG⁻(γ, 1)` with constants
  independent of the level `l` (`exists_isDGSub_levelScaled`).  The point is the *sign* of the
  entropy: the super competitor `u + ζ(l-u)₊` raises the minimizer, and `s ↦ s² log s` is
  decreasing on `(0, e^{-1/2})`, so the entropy difference can be dropped outright and the
  lower-order error of the level energy inequality is `(|Ψ 0| + |Λ|) l²` — homogeneous of
  degree two, with **no** `log(1/l)` factor (`exists_energy_ineq_super_sharp`);
* the `δ`-uniform `L¹` bound for `(-log(v+δ))₊` (`exists_neg_log_shift_bound`, entropy
  comparison with the square-root competitor) applied at `δ = l` gives
  `log(1/(2l)) · |B_R ∩ {v < l}| ≤ A`, so the sublevel sets have arbitrarily small measure;
* hence `⨍_{B_R} (w_l + 1)²` is arbitrarily small, and the De Giorgi sup bound at the level
  `k = -1` gives `w_l ≤ -1/2` a.e. on `B_{R/2}`, i.e. `v ≥ l/2` there.

No expansion of positivity and no chain of balls are needed.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ : ℝ} {Ψ : Euc d → ℝ} {c C : ℝ} {K : Set (Euc d)}

/-! ### The shifted logarithm as a Sobolev function -/

section ShiftedLog

variable {v : Euc d → ℝ}

/-- **The shifted logarithm `Z_δ = log δ - log(v + δ)` lies in `W₀^{1,2}(K)`**, with weak gradient
`-(v + δ)⁻¹ ∇v`.

This is the reason the whole De Giorgi argument is run on `Z_δ` rather than on `-log v`: the
profile `t ↦ log δ - log(t + δ)` is `C¹` with derivative bounded by `δ⁻¹` on the range `[0, M]`
of `v`, and it vanishes at `t = 0`, so `Z_δ` vanishes off `K` and the chain rule
`memW0_comp_sub_of_hasDerivAt` applies verbatim.  Neither `-log v` (which is `+∞` on `{v = 0}`)
nor any truncation of it (which jumps across `∂K`) has a global weak gradient. -/
theorem memW0_shiftedLog (hcomp : IsRegComp K v) {δ : ℝ} (hδ0 : 0 < δ) :
    MemW0 2 K (fun x => Real.log δ - Real.log (v x + δ)) ∧
      weakGrad (fun x => Real.log δ - Real.log (v x + δ)) =ᵐ[volume]
        fun x => -((v x + δ)⁻¹ • weakGrad v x) := by
  obtain ⟨M₀, hM₀⟩ := hcomp.exists_le
  have hS : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have hfS : ∀ x, v x ∈ Icc (0 : ℝ) (max M₀ 0) :=
    fun x => ⟨hcomp.nonneg x, (hM₀ x).trans (le_max_left _ _)⟩
  have hderiv : ∀ t ∈ Icc (0 : ℝ) (max M₀ 0),
      HasDerivAt (fun s : ℝ => Real.log δ - Real.log (s + δ)) (-(t + δ)⁻¹) t := by
    intro t ht
    have hpos : (0 : ℝ) < t + δ := by linarith [ht.1]
    have h1 : HasDerivAt (fun s : ℝ => s + δ) 1 t := (hasDerivAt_id t).add_const δ
    have h2 := (h1.log hpos.ne').const_sub (Real.log δ)
    simpa using h2
  have hcont : ContinuousOn (fun t : ℝ => -(t + δ)⁻¹) (Icc 0 (max M₀ 0)) := by
    refine ContinuousOn.neg (ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop))
      (fun t ht => ?_))
    have hpos : (0 : ℝ) < t + δ := by linarith [ht.1]
    exact hpos.ne'
  have h := memW0_comp_sub_of_hasDerivAt (p := 2) one_lt_two hcomp.memW0 hS hfS hderiv hcont
  simpa using h

/-- The pointwise bounds on `Z_δ`: it is nonpositive and bounded below by `log δ - log(M + 1)`. -/
theorem abs_shiftedLog_le (hcomp : IsRegComp K v) {M : ℝ} (hM : ∀ x, v x ≤ M)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (x : Euc d) :
    |Real.log δ - Real.log (v x + δ)| ≤ |Real.log δ| + |Real.log (max M 0 + 1)| := by
  have hpos : (0 : ℝ) < v x + δ := by linarith [hcomp.nonneg x]
  have h1 : Real.log δ ≤ Real.log (v x + δ) :=
    Real.log_le_log hδ0 (by linarith [hcomp.nonneg x])
  have h2 : Real.log (v x + δ) ≤ Real.log (max M 0 + 1) := by
    refine Real.log_le_log hpos ?_
    have : v x ≤ max M 0 := (hM x).trans (le_max_left _ _)
    linarith
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le (Real.log δ), le_abs_self (Real.log (max M 0 + 1)),
      abs_nonneg (Real.log δ), abs_nonneg (Real.log (max M 0 + 1))]
  · nlinarith [le_abs_self (Real.log δ), neg_abs_le (Real.log (max M 0 + 1)),
      abs_nonneg (Real.log δ), abs_nonneg (Real.log (max M 0 + 1))]

end ShiftedLog

/-! ### The local positive lower bound -/

/-- **Local positive lower bound for the regularized minimizer**
(`REGULARIZED_ROUTE.md`, Revision 2 (iii)): on a ball around every point of `K` the minimizer is
bounded below by a positive constant.

This is the frozen lane statement `exists_local_lower_bound`, verbatim.

Proved in `PositivityLowerPos.lean` as `exists_local_lower_bound'`; see the module docstring. -/
theorem exists_local_lower_bound (hd : 0 < d) (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) {v : Euc d → ℝ} (hv : IsRegMinimizer 2 κ Ψ K v)
    (hcomp : IsRegComp K v) (hvm : Measurable v) {x₀ : Euc d} (hx₀ : x₀ ∈ K) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧ Metric.ball x₀ r ⊆ K ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), ε ≤ v x :=
  exists_local_lower_bound' hd hκ hΨ hK hv hcomp hvm hx₀

end Komlos.Literature.Regularized
