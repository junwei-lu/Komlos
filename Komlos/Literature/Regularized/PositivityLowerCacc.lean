import Komlos.Literature.Regularized.PositivityLowerProfile

/-!
# Lane `L2p` (`reg/pos-lower`), step 4d: the pointwise estimates of the Caccioppoli terms

The master logarithmic Caccioppoli inequality (`IsRegMinimizer.log_caccioppoli_master`) applied
to the profile `Φ = shiftLogProfile (levelFun k ε) δ a L` has exactly one term whose sign is not
automatic,

`(C/L) ∫ η² f(Z_δ) smoothStep'(h) ‖q‖²`,  `h = (log v − log a)/L`,

and this file provides its pointwise split: **absorbed** into the good term where
`h ≥ 12C/(cL)`, and **bounded by the Dirichlet energy on the layer** `{a < v < a e^{12C/c}}`
otherwise.  The split is what makes the estimate uniform in `a`: the layer has bounded
logarithmic width, and its Dirichlet energy is `O(a²(1 + κ log(1/a)))` by the
level-dependent De Giorgi inequality `exists_energy_ineq_super_level`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {c C : ℝ} {Ψ : Euc d → ℝ}

/-- **The absorption/layer split of the bad term.**  With `F ≥ 0` standing for `f(Z_δ)`,
`Q ≥ 0` for `‖q‖²` and `G` for `‖∇v‖²` (so that `Q t² ≤ G`),

`(C/L) F smoothStep'(h) Q ≤ (c/2) F H_a(t) Q + 1_{t < a e^{12C/c}} · (72C²/(cL²)) F G / a²`.

The first term is absorbed by the good term `c ∫ η² F H_a ‖q‖²` of the master inequality; the
second lives on a layer of bounded logarithmic width and carries the factor `1/L²`. -/
theorem badTerm_le (hΨ : IsRegProfileWith Ψ c C) {a L F G Q t : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hF : 0 ≤ F) (hQ : 0 ≤ Q) (ht : 0 < t) (hQG : Q * t ^ 2 ≤ G) :
    C / L * F * smoothStepDeriv ((Real.log t - Real.log a) / L) * Q ≤
      c / 2 * (F * logSwitch a L t) * Q +
        (if t < a * Real.exp (12 * C / c) then 72 * C ^ 2 / (c * L ^ 2) * F * G / a ^ 2
          else 0) := by
  have hc0 : (0 : ℝ) < c := hΨ.c_pos
  have hC0 : (0 : ℝ) ≤ C := hΨ.C_nonneg
  obtain ⟨h, hhdef⟩ : ∃ h : ℝ, h = (Real.log t - Real.log a) / L := ⟨_, rfl⟩
  have hgood0 : 0 ≤ c / 2 * (F * logSwitch a L t) * Q := by
    have := logSwitch_nonneg a L t
    positivity
  have hifnn : (0 : ℝ) ≤ (if t < a * Real.exp (12 * C / c) then
      72 * C ^ 2 / (c * L ^ 2) * F * G / a ^ 2 else 0) := by
    split
    · have hG0 : 0 ≤ G := le_trans (by positivity) hQG
      positivity
    · exact le_rfl
  rcases le_or_gt h 0 with hh0 | hh0
  · rw [← hhdef, smoothStepDeriv_of_nonpos hh0]
    simp only [mul_zero, zero_mul]
    linarith
  -- `h > 0` forces `t > a`
  have hh0' : 0 < (Real.log t - Real.log a) / L := by rw [← hhdef]; exact hh0
  have hnum : 0 < Real.log t - Real.log a := by
    have h2 : 0 < (Real.log t - Real.log a) / L * L := mul_pos hh0' hL
    rwa [div_mul_cancel₀ _ hL.ne'] at h2
  have hta : a < t := (Real.log_lt_log_iff ha ht).1 (by linarith)
  have hQle : Q ≤ G / a ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hsq : a ^ 2 ≤ t ^ 2 := by nlinarith [ha.le, hta.le]
    nlinarith [mul_le_mul_of_nonneg_left hsq hQ, hQG]
  rcases le_or_gt 1 h with hh1 | hh1
  · rw [← hhdef, smoothStepDeriv_of_one_le hh1]
    simp only [mul_zero, zero_mul]
    linarith
  -- now `0 < h < 1`
  have hσd : smoothStepDeriv h ≤ 6 * h := by
    have := smoothStepDeriv_le h
    rwa [max_eq_left hh0.le] at this
  have hσ : h ^ 2 ≤ logSwitch a L t := by
    rw [logSwitch, ← hhdef]
    exact sq_le_smoothStep hh0.le hh1.le
  rcases le_or_gt (12 * C / (c * L)) h with habs | hlay
  · -- absorption
    refine le_trans ?_ (le_add_of_nonneg_right hifnn)
    rw [← hhdef]
    have hkey : C / L * smoothStepDeriv h ≤ c / 2 * logSwitch a L t := by
      have h1 : C / L * smoothStepDeriv h ≤ C / L * (6 * h) :=
        mul_le_mul_of_nonneg_left hσd (by positivity)
      have h2 : C / L * (6 * h) ≤ c / 2 * h ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at habs
        have hCL : C / L * (6 * h) = 6 * C * h / L := by field_simp; try ring
        rw [hCL, div_le_iff₀ hL]
        nlinarith [habs, hh0.le, hc0.le, hL.le]
      have h3 : c / 2 * h ^ 2 ≤ c / 2 * logSwitch a L t :=
        mul_le_mul_of_nonneg_left hσ (by positivity)
      linarith
    calc C / L * F * smoothStepDeriv h * Q = (C / L * smoothStepDeriv h) * (F * Q) := by ring
      _ ≤ (c / 2 * logSwitch a L t) * (F * Q) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = c / 2 * (F * logSwitch a L t) * Q := by ring
  · -- the layer
    have hlayer : t < a * Real.exp (12 * C / c) := by
      have hLh : Real.log t - Real.log a < 12 * C / c := by
        rw [hhdef, div_lt_iff₀ hL] at hlay
        have hrw : 12 * C / (c * L) * L = 12 * C / c := by field_simp
        rw [hrw] at hlay
        exact hlay
      have hlt : Real.log t < Real.log a + 12 * C / c := by linarith
      have hexp : Real.log (a * Real.exp (12 * C / c)) = Real.log a + 12 * C / c := by
        rw [Real.log_mul ha.ne' (Real.exp_ne_zero _), Real.log_exp]
      rw [← hexp] at hlt
      exact (Real.log_lt_log_iff ht (by positivity)).1 hlt
    rw [if_pos hlayer, ← hhdef]
    refine le_trans ?_ (le_add_of_nonneg_left hgood0)
    have hG0 : 0 ≤ G := le_trans (by positivity) hQG
    have hbound : C / L * F * smoothStepDeriv h * Q ≤
        C / L * F * (6 * (12 * C / (c * L))) * (G / a ^ 2) := by
      have h1 : smoothStepDeriv h ≤ 6 * (12 * C / (c * L)) := by
        have : 6 * h ≤ 6 * (12 * C / (c * L)) := by linarith
        linarith [hσd]
      have hcoef : (0 : ℝ) ≤ C / L * F := by positivity
      calc C / L * F * smoothStepDeriv h * Q ≤ C / L * F * (6 * (12 * C / (c * L))) * Q := by
            nlinarith [mul_le_mul_of_nonneg_left h1 hcoef, hQ]
        _ ≤ C / L * F * (6 * (12 * C / (c * L))) * (G / a ^ 2) := by
            refine mul_le_mul_of_nonneg_left hQle ?_
            positivity
    refine le_trans hbound (le_of_eq ?_)
    field_simp
    ring

/-! ### Two-sided bounds for `⟪∇Ψ q, q⟫` -/

/-- `⟪∇Ψ q, q⟫ ≤ C ‖q‖²`, from `‖∇Ψ q‖ ≤ C ‖q‖`. -/
theorem inner_gradient_self_le (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    ⟪gradient Ψ q, q⟫ ≤ C * ‖q‖ ^ 2 := by
  calc ⟪gradient Ψ q, q⟫ ≤ ‖gradient Ψ q‖ * ‖q‖ := real_inner_le_norm _ _
    _ ≤ (C * ‖q‖) * ‖q‖ := mul_le_mul_of_nonneg_right (h.norm_gradient_le q) (norm_nonneg _)
    _ = C * ‖q‖ ^ 2 := by ring

/-- `c ‖q‖² ≤ ⟪∇Ψ q, q⟫`, from strong monotonicity of `∇Ψ` against `q' = 0`. -/
theorem le_inner_gradient_self (h : IsRegProfileWith Ψ c C) (q : Euc d) :
    c * ‖q‖ ^ 2 ≤ ⟪gradient Ψ q, q⟫ := by
  have hm := h.inner_gradient_sub q 0
  simp only [h.toIsRegProfile.gradient_zero, sub_zero] at hm
  exact hm

/-! ### The pointwise majorant of the Caccioppoli right-hand side -/

set_option maxHeartbeats 1000000 in
/-- **The pointwise estimate of the right-hand side of `log_caccioppoli_master`** for the
profile `Φ = shiftLogProfile f δ a L`.  Writing `Z = log δ − log(t+δ)`, `H = H_a(t)` and
`q = t⁻¹ • g`, the four terms are bounded by

* the *good* term `c e² f(Z) H ‖q‖²` (which cancels the left-hand side of the master
  inequality),
* minus the *second good* term `c e² f'(Z) (t/(t+δ)) H ‖q‖²` (which becomes
  `c ∫ ‖∇Z_δ‖²`),
* the *layer* term, supported in `{t < a e^{12C/c}}`,
* the `∇η` term and the zeroth-order term, both carrying the factor `f(Z) H`. -/
theorem caccioppoli_rhs_pointwise (hΨ : IsRegProfileWith Ψ c C) {κ Λ S δ a L W e t : ℝ}
    {g Gη : Euc d} {f fd : ℝ → ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (ha : 0 < a) (hL : 0 < L)
    (ht0 : 0 ≤ t) (htS : t ≤ S) (hf : ∀ z, 0 ≤ f z) (hfd : ∀ z, 0 ≤ fd z)
    (_hW : 0 ≤ W) (hGη : ‖Gη‖ ≤ 2 * |e| * W) :
    2 * Ψ 0 * (e ^ 2 * (t * shiftLogProfile f δ a L t))
        + e ^ 2 * (t * shiftLogProfile f δ a L t
            + t ^ 2 * shiftLogProfileDeriv f fd δ a L t) *
            ⟪gradient Ψ (t⁻¹ • g), t⁻¹ • g⟫
        + t * ⟪gradient Ψ (t⁻¹ • g), shiftLogProfile f δ a L t • Gη⟫
        + e ^ 2 * (t * shiftLogProfile f δ a L t) * (κ * Real.log t + κ / 2 - 2 * Λ) ≤
      c * (e ^ 2 * (f (Real.log δ - Real.log (t + δ)) * logSwitch a L t) * ‖t⁻¹ • g‖ ^ 2)
        - c * (e ^ 2 * (fd (Real.log δ - Real.log (t + δ)) * (t / (t + δ)) *
            logSwitch a L t) * ‖t⁻¹ • g‖ ^ 2)
        + (if t < a * Real.exp (12 * C / c) then
            72 * C ^ 2 / (c * L ^ 2) * (e ^ 2 * f (Real.log δ - Real.log (t + δ))) *
              ‖g‖ ^ 2 / a ^ 2
          else 0)
        + 2 * C ^ 2 / c * (f (Real.log δ - Real.log (t + δ)) * logSwitch a L t) * W ^ 2
        + (2 * |Ψ 0| + κ * Real.log (max S 1) + κ / 2 + 2 * |Λ|) *
            (e ^ 2 * (f (Real.log δ - Real.log (t + δ)) * logSwitch a L t)) := by
  have hc0 : (0 : ℝ) < c := hΨ.c_pos
  have hC0 : (0 : ℝ) ≤ C := hΨ.C_nonneg
  set Z : ℝ := Real.log δ - Real.log (t + δ) with hZ
  set H : ℝ := logSwitch a L t with hH
  set q : Euc d := t⁻¹ • g with hq
  set Q : ℝ := ‖q‖ ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := sq_nonneg _
  have hH0 : 0 ≤ H := logSwitch_nonneg a L t
  have hfZ : 0 ≤ f Z := hf Z
  have hfdZ : 0 ≤ fd Z := hfd Z
  have hcoef : 0 ≤ e ^ 2 * (f Z * H) := by positivity
  have hifnn : (0 : ℝ) ≤ (if t < a * Real.exp (12 * C / c) then
      72 * C ^ 2 / (c * L ^ 2) * (e ^ 2 * f Z) * ‖g‖ ^ 2 / a ^ 2 else 0) := by
    split
    · positivity
    · exact le_rfl
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · -- `t = 0`: every term on the left vanishes and the right-hand side is nonnegative.
    have htz : t = 0 := h0.symm
    have hΦ0 : shiftLogProfile f δ a L t = 0 := shiftLogProfile_of_le ha hL (by linarith)
    have hΦ'0 : shiftLogProfileDeriv f fd δ a L t = 0 :=
      shiftLogProfileDeriv_of_le ha hL (by linarith)
    have hQz : Q = 0 := by rw [hQdef, hq, htz]; simp
    have hA : (0 : ℝ) ≤ 2 * C ^ 2 / c * (f Z * H) * W ^ 2 :=
      mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hfZ hH0)) (sq_nonneg W)
    have hK0 : (0 : ℝ) ≤ 2 * |Ψ 0| + κ * Real.log (max S 1) + κ / 2 + 2 * |Λ| := by
      have hlog : 0 ≤ Real.log (max S 1) := Real.log_nonneg (le_max_right _ _)
      nlinarith [abs_nonneg (Ψ 0), abs_nonneg Λ, hκ.le, hlog]
    have hB : (0 : ℝ) ≤ (2 * |Ψ 0| + κ * Real.log (max S 1) + κ / 2 + 2 * |Λ|) *
        (e ^ 2 * (f Z * H)) := mul_nonneg hK0 hcoef
    rw [hΦ0, hΦ'0, hQz]
    simp only [mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_smul,
      inner_zero_right]
    linarith
  · -- `t > 0`
    have htδ : (0 : ℝ) < t + δ := by linarith
    have hΦ : t * shiftLogProfile f δ a L t = f Z * H := mul_shiftLogProfile ha hL h0
    have hΦ2 : t * shiftLogProfile f δ a L t + t ^ 2 * shiftLogProfileDeriv f fd δ a L t =
        f Z * (smoothStepDeriv ((Real.log t - Real.log a) / L) / L)
          - fd Z * (t / (t + δ)) * H := mul_shiftLogProfile_add_sq_mul_deriv hδ ha hL h0
    set IP : ℝ := ⟪gradient Ψ q, q⟫ with hIP
    have hIPup : IP ≤ C * Q := inner_gradient_self_le hΨ q
    have hIPlo : c * Q ≤ IP := le_inner_gradient_self hΨ q
    set σ' : ℝ := smoothStepDeriv ((Real.log t - Real.log a) / L) with hσ'
    have hσ'0 : 0 ≤ σ' := smoothStepDeriv_nonneg _
    -- term 1
    have hT1 : 2 * Ψ 0 * (e ^ 2 * (t * shiftLogProfile f δ a L t)) ≤
        2 * |Ψ 0| * (e ^ 2 * (f Z * H)) := by
      rw [hΦ]
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (Ψ 0)]) hcoef
    -- term 2
    have hT2 : e ^ 2 * (t * shiftLogProfile f δ a L t
          + t ^ 2 * shiftLogProfileDeriv f fd δ a L t) * IP ≤
        C / L * (e ^ 2 * f Z) * σ' * Q - c * (e ^ 2 * (fd Z * (t / (t + δ)) * H) * Q) := by
      rw [hΦ2]
      have hpos : 0 ≤ e ^ 2 * (f Z * (σ' / L)) := by positivity
      have hneg : 0 ≤ e ^ 2 * (fd Z * (t / (t + δ)) * H) := by positivity
      have hsplit : e ^ 2 * (f Z * (σ' / L) - fd Z * (t / (t + δ)) * H) * IP =
          (e ^ 2 * (f Z * (σ' / L))) * IP - (e ^ 2 * (fd Z * (t / (t + δ)) * H)) * IP := by
        ring
      rw [hsplit]
      have h1 : (e ^ 2 * (f Z * (σ' / L))) * IP ≤ (e ^ 2 * (f Z * (σ' / L))) * (C * Q) :=
        mul_le_mul_of_nonneg_left hIPup hpos
      have h2 : (e ^ 2 * (fd Z * (t / (t + δ)) * H)) * (c * Q) ≤
          (e ^ 2 * (fd Z * (t / (t + δ)) * H)) * IP := mul_le_mul_of_nonneg_left hIPlo hneg
      have h3 : (e ^ 2 * (f Z * (σ' / L))) * (C * Q) = C / L * (e ^ 2 * f Z) * σ' * Q := by
        field_simp
        try ring
      linarith
    -- term 3
    have hT3 : t * ⟪gradient Ψ q, shiftLogProfile f δ a L t • Gη⟫ ≤
        c / 2 * (e ^ 2 * (f Z * H)) * Q + 2 * C ^ 2 / c * (f Z * H) * W ^ 2 := by
      have hsm : t * ⟪gradient Ψ q, shiftLogProfile f δ a L t • Gη⟫ =
          (f Z * H) * ⟪gradient Ψ q, Gη⟫ := by
        rw [real_inner_smul_right, ← hΦ]; ring
      rw [hsm]
      have hinner : ⟪gradient Ψ q, Gη⟫ ≤ C * ‖q‖ * (2 * |e| * W) := by
        calc ⟪gradient Ψ q, Gη⟫ ≤ ‖gradient Ψ q‖ * ‖Gη‖ := real_inner_le_norm _ _
          _ ≤ (C * ‖q‖) * (2 * |e| * W) :=
              mul_le_mul (hΨ.norm_gradient_le q) hGη (norm_nonneg _) (by positivity)
      have hyoung : C * ‖q‖ * (2 * |e| * W) ≤ c / 2 * (e ^ 2 * Q) + 2 * C ^ 2 / c * W ^ 2 := by
        have habs : |e| ^ 2 = e ^ 2 := sq_abs e
        rw [hQdef, ← sub_nonneg]
        have hexp : c / 2 * (e ^ 2 * ‖q‖ ^ 2) + 2 * C ^ 2 / c * W ^ 2
            - C * ‖q‖ * (2 * |e| * W)
            = (c * (|e| * ‖q‖) - 2 * C * W) ^ 2 / (2 * c) := by
          rw [← habs]
          field_simp
          try ring
        rw [hexp]
        positivity
      have hfin := mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ f Z * H)
      have hfin2 := mul_le_mul_of_nonneg_left hyoung (by positivity : (0 : ℝ) ≤ f Z * H)
      linarith [hfin, hfin2]
    -- term 4
    have hT4 : e ^ 2 * (t * shiftLogProfile f δ a L t) * (κ * Real.log t + κ / 2 - 2 * Λ) ≤
        (κ * Real.log (max S 1) + κ / 2 + 2 * |Λ|) * (e ^ 2 * (f Z * H)) := by
      rw [hΦ]
      have hlt : Real.log t ≤ Real.log (max S 1) :=
        Real.log_le_log h0 (le_trans htS (le_max_left _ _))
      have hb : κ * Real.log t + κ / 2 - 2 * Λ ≤
          κ * Real.log (max S 1) + κ / 2 + 2 * |Λ| := by
        have h1 : κ * Real.log t ≤ κ * Real.log (max S 1) :=
          mul_le_mul_of_nonneg_left hlt hκ.le
        have h2 : -Λ ≤ |Λ| := by rw [← abs_neg]; exact le_abs_self _
        linarith
      calc e ^ 2 * (f Z * H) * (κ * Real.log t + κ / 2 - 2 * Λ)
          ≤ e ^ 2 * (f Z * H) * (κ * Real.log (max S 1) + κ / 2 + 2 * |Λ|) :=
            mul_le_mul_of_nonneg_left hb hcoef
        _ = (κ * Real.log (max S 1) + κ / 2 + 2 * |Λ|) * (e ^ 2 * (f Z * H)) := by ring
    -- the bad term
    have hbad := badTerm_le (Ψ := Ψ) hΨ (a := a) (L := L) (F := e ^ 2 * f Z) (G := ‖g‖ ^ 2)
      (Q := Q) (t := t) ha hL (by positivity) hQ0 h0 (by
        have hnorm : Q = ‖g‖ ^ 2 / t ^ 2 := by
          rw [hQdef, hq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h0, mul_pow,
            inv_pow]
          ring
        have hcanc : ‖g‖ ^ 2 / t ^ 2 * t ^ 2 = ‖g‖ ^ 2 :=
          div_mul_cancel₀ _ (pow_ne_zero 2 h0.ne')
        rw [hnorm, hcanc])
    have hbad' : C / L * (e ^ 2 * f Z) * σ' * Q ≤
        c / 2 * (e ^ 2 * (f Z * H)) * Q +
          (if t < a * Real.exp (12 * C / c) then
            72 * C ^ 2 / (c * L ^ 2) * (e ^ 2 * f Z) * ‖g‖ ^ 2 / a ^ 2 else 0) := by
      refine le_trans hbad (add_le_add ?_ ?_)
      · rw [hH]; apply le_of_eq; ring
      · split
        · apply le_of_eq; ring
        · exact le_rfl
    linarith

end Komlos.Literature.Regularized
