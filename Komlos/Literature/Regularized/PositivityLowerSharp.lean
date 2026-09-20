import Komlos.Literature.Regularized.PositivityLowerLevel

/-!
# Lane `L2p` (`reg/pos-lower`), step 5: the *sharp* level-dependent De Giorgi inequality

`exists_energy_ineq_super_level` bounds the lower-order term by
`γ l² (log(1/l) + 1) |B_s ∩ {u < l}|`, because it estimates the entropy density by its
*absolute value*.  That logarithm is fatal for the expansion of positivity: after the rescaling
`z = (l − u)₊ / l` (which is what turns a De Giorgi class statement into a statement about the
level `l`) it leaves a De Giorgi constant `χ² ≍ log(1/l) → ∞`.

The logarithm is an artifact.  On the super side the competitor **raises** the minimizer,
`w = u + ζ (l − u)₊ ≥ u`, and both stay in `[0, l]`; and `s ↦ s² log s` is *decreasing* on
`(0, e^{-1/2})`.  Hence for levels `l ≤ e^{-1/2}` the entropy difference
`∫ (κ/2)(w² log w − u² log u)` is `≤ 0` and can simply be dropped from
`regFree(u) ≤ regFree(w)`.  What is left of the lower-order part is `(Ψ 0 − Λ)(w² − u²)`,
bounded by `(|Ψ 0| + |Λ|) l²` — homogeneous of degree two in the level, with **no logarithm**.

Consequently `z = (l − u)₊ / l` lies in `IsDGSub γ 1 …` with constants independent of `l`, and
the De Giorgi sup bound applies to it uniformly.  This is the key to `exists_local_lower_bound'`
(see `PositivityLowerPos.lean`).

Credit: this observation (use the *sign* of the entropy, not its absolute value) is due to the
coordinator; it replaces the logarithmic route of `PositivityLowerVar.lean` /
`PositivityLowerProfile.lean`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff

namespace Komlos.Literature.Regularized

variable {d : ℕ} {κ c C : ℝ} {Ψ : Euc d → ℝ} {K : Set (Euc d)} {u : Euc d → ℝ}

/-! ### `s ↦ s² log s` is decreasing below `e^{-1/2}` -/

/-- The derivative of `s ↦ s² log s` on `s > 0`. -/
theorem hasDerivAt_sq_mul_log {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ 2 * Real.log y) (2 * x * Real.log x + x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  refine (h1.mul h2).congr_deriv ?_
  field_simp
  try ring

/-- **`s ↦ s² log s` is nonincreasing on `[0, e^{-1/2}]`**: the derivative
`s (2 log s + 1)` is nonpositive there.  This is the sign that removes the logarithm from the
lower-order term of the super-side energy inequality. -/
theorem sq_mul_log_le_of_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ Real.exp (-(1 / 2 : ℝ))) : t ^ 2 * Real.log t ≤ s ^ 2 * Real.log s := by
  have hexp1 : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  rcases hs.eq_or_lt with hs0 | hs0
  · -- `s = 0`
    rw [← hs0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    rcases (le_trans hs hst).eq_or_lt with ht0 | ht0
    · rw [← ht0]; simp
    · have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le (le_of_lt (lt_of_le_of_lt ht hexp1))
      nlinarith [sq_nonneg t]
  · -- `0 < s`
    have hmono : AntitoneOn (fun y : ℝ => y ^ 2 * Real.log y) (Set.Icc s t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc s t) ?_ ?_ ?_
      · exact fun x hx =>
          ((hasDerivAt_sq_mul_log (lt_of_lt_of_le hs0 hx.1)).continuousAt).continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact ((hasDerivAt_sq_mul_log (lt_trans hs0 hx.1)).differentiableAt).differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := lt_trans hs0 hx.1
        rw [(hasDerivAt_sq_mul_log hx0).deriv]
        have hlx : Real.log x ≤ -(1 / 2 : ℝ) := by
          have hxe : x ≤ Real.exp (-(1 / 2 : ℝ)) := le_trans hx.2.le ht
          calc Real.log x ≤ Real.log (Real.exp (-(1 / 2 : ℝ))) := Real.log_le_log hx0 hxe
            _ = -(1 / 2 : ℝ) := Real.log_exp _
        nlinarith [hx0, hlx]
    exact hmono (Set.left_mem_Icc.2 hst) (Set.right_mem_Icc.2 hst) hst

/-- **The sharp bound on the lower-order density difference.**  If `0 ≤ s ≤ t ≤ l ≤ e^{-1/2}`,
the entropy part of `regLow κ Λ Ψ t - regLow κ Λ Ψ s` is nonpositive, so the difference is
bounded by `(|Ψ 0| + |Λ|) l²` — with **no** logarithmic factor. -/
theorem regLow_sub_le_sharp {Λ l s t : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s) (hst : s ≤ t)
    (htl : t ≤ l) (hl : l ≤ Real.exp (-(1 / 2 : ℝ))) :
    regLow κ Λ Ψ t - regLow κ Λ Ψ s ≤ (|Ψ 0| + |Λ|) * l ^ 2 := by
  have ht0 : 0 ≤ t := le_trans hs hst
  have hl0 : 0 ≤ l := le_trans ht0 htl
  have hent : t ^ 2 * Real.log t ≤ s ^ 2 * Real.log s :=
    sq_mul_log_le_of_le hs hst (le_trans htl hl)
  have hsq0 : 0 ≤ t ^ 2 - s ^ 2 := by nlinarith
  have hsq : t ^ 2 - s ^ 2 ≤ l ^ 2 := by nlinarith
  rw [regLow, regLow, entropyPotential_two κ ht0, entropyPotential_two κ hs]
  have h1 : Ψ 0 * t ^ 2 - Ψ 0 * s ^ 2 ≤ |Ψ 0| * l ^ 2 := by
    have hx : Ψ 0 * (t ^ 2 - s ^ 2) ≤ |Ψ 0| * (t ^ 2 - s ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hsq0
    nlinarith [mul_le_mul_of_nonneg_left hsq (abs_nonneg (Ψ 0))]
  have h2 : -(Λ * t ^ 2) + Λ * s ^ 2 ≤ |Λ| * l ^ 2 := by
    have hx : -(Λ * (t ^ 2 - s ^ 2)) ≤ |Λ| * (t ^ 2 - s ^ 2) := by
      have := neg_abs_le Λ
      nlinarith [hsq0]
    nlinarith [mul_le_mul_of_nonneg_left hsq (abs_nonneg Λ)]
  have h3 : κ / 2 * (t ^ 2 * Real.log t) - κ / 2 * (s ^ 2 * Real.log s) ≤ 0 := by
    nlinarith [hent, hκ]
  linarith

/-! ### The Caccioppoli comparison with the sharp lower-order error -/

set_option maxHeartbeats 1000000 in
/-- **The Caccioppoli comparison, sharp level-aware form.**  Same as
`exists_caccioppoli_core_level`, but the lower-order error is `B₁ l² |S|` with **no logarithm**:
on the super side the competitor satisfies `u ≤ w ≤ l` on `S`, and for `l ≤ e^{-1/2}` the
entropy difference `w² log w - u² log u` is nonpositive (`sq_mul_log_le_of_le`), so only
`(Ψ 0 - Λ)(w² - u²)` survives. -/
theorem exists_caccioppoli_core_sharp (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) (hucomp : IsRegComp K u) :
    ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∀ l : ℝ, 0 < l → l ≤ Real.exp (-(1 / 2 : ℝ)) →
      ∀ w : Euc d → ℝ, IsRegComp K w →
      ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
      (∀ x ∈ S, u x ≤ l) → (∀ x ∈ S, w x ≤ l) → (∀ x ∈ S, u x ≤ w x) →
      (∀ᵐ x, x ∉ S → u x = w x) → (∀ᵐ x, x ∉ S → weakGrad u x = weakGrad w x) →
      c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
        C / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + B₁ * l ^ 2 * (volume S).toReal := by
  classical
  set Λ : ℝ := regMin 2 κ Ψ K + κ / 4 with hΛ
  refine ⟨|Ψ 0| + |Λ|, by positivity, ?_⟩
  intro l hl0 hl1 w hw S hS hSfin huS hwS huwS hoffv hoffg
  set B₀ : ℝ := (|Ψ 0| + |Λ|) * l ^ 2 with hB₀
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; positivity
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
  have hle : (∫ x, Fu x) ≤ ∫ x, Fw x := hu.regFree_le hκ hΨ hK hucomp hw
  have hoffF : ∀ᵐ x, x ∉ S → Fu x = Fw x := by
    filter_upwards [hoffv, hoffg] with x h1 h2 hx
    rw [hFu, hFw]
    simp only []
    rw [h1 hx, h2 hx]
  have hlocal : (∫ x in S, Fu x) ≤ ∫ x in S, Fw x :=
    setIntegral_le_of_integral_le_of_eq_off hS hFuInt hFwInt hle hoffF
  have hLu : Integrable (fun x => regLow κ Λ Ψ (u x)) volume :=
    ((hucomp.integrable_sq.const_mul (Ψ 0)).add (hucomp.integrable_entropy hK κ)).sub
      (hucomp.integrable_sq.const_mul Λ)
  have hLw : Integrable (fun x => regLow κ Λ Ψ (w x)) volume :=
    ((hw.integrable_sq.const_mul (Ψ 0)).add (hw.integrable_entropy hK κ)).sub
      (hw.integrable_sq.const_mul Λ)
  have hcstInt : IntegrableOn (fun _ : Euc d => B₀) S volume := integrableOn_const hSfin
  have hDu : IntegrableOn (fun x => ‖weakGrad u x‖ ^ 2) S volume :=
    hucomp.integrable_normSq_grad.integrableOn
  have hDw : IntegrableOn (fun x => ‖weakGrad w x‖ ^ 2) S volume :=
    hw.integrable_normSq_grad.integrableOn
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
  have hdiff : (∫ x in S, regLow κ Λ Ψ (w x)) - (∫ x in S, regLow κ Λ Ψ (u x)) ≤
      B₀ * (volume S).toReal := by
    have hptw : ∀ᵐ x ∂(volume.restrict S),
        regLow κ Λ Ψ (w x) - regLow κ Λ Ψ (u x) ≤ B₀ := by
      rw [ae_restrict_iff' hS]
      refine Eventually.of_forall fun x hx => ?_
      rw [hB₀]
      exact regLow_sub_le_sharp (Λ := Λ) (Ψ := Ψ) hκ (hucomp.nonneg x) (huwS x hx)
        (hwS x hx) hl1
    have hsubint : IntegrableOn (fun x => regLow κ Λ Ψ (w x) - regLow κ Λ Ψ (u x)) S volume :=
      hLw.integrableOn.sub hLu.integrableOn
    have hmono := integral_mono_ae hsubint hcstInt hptw
    rw [integral_sub hLw.integrableOn hLu.integrableOn, setIntegral_const] at hmono
    simpa [measureReal_def, mul_comm] using hmono
  show c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
      C / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + B₀ * (volume S).toReal
  linarith [hlocal, hlow, hup, hdiff]

/-! ### The assembled sharp level-dependent energy inequality -/

set_option maxHeartbeats 1000000 in
/-- **The sharp level-dependent De Giorgi (super-side) inequality.**  For every ball
`closedBall x₁ s ⊆ K`, every `0 < r < s` and every level `0 < l ≤ e^{-1/2}`,

`∫_{B_r ∩ {u<l}} ‖∇u‖² ≤ γ(s−r)^{-2} ∫_{B_s}(l−u)₊² + γ l² |B_s ∩ {u<l}|`.

Both terms are homogeneous of degree two in the level, so after the rescaling
`z = (l − u)₊ / l` the constants become **independent of `l`** — see `isDGSub_levelScaled`. -/
theorem exists_energy_ineq_super_sharp (hκ : 0 < κ) (hΨ : IsRegProfileWith Ψ c C)
    (hK : IsGoodConvex K) (hu : IsRegMinimizer 2 κ Ψ K u) (hcomp : IsRegComp K u)
    (hum : Measurable u) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ (x₁ : Euc d) (r s l : ℝ), 0 < r → r < s → 0 < l →
      l ≤ Real.exp (-(1 / 2 : ℝ)) → Metric.closedBall x₁ s ⊆ K →
      (∫ x in Metric.ball x₁ r ∩ {x | u x < l}, ‖weakGrad u x‖ ^ 2) ≤
        γ / (s - r) ^ 2 * (∫ x in Metric.ball x₁ s, negTrunc l u x ^ 2) +
          γ * l ^ 2 * (volume (Metric.ball x₁ s ∩ {x | u x < l})).toReal := by
  classical
  obtain ⟨B₁, hB₁0, hcore0⟩ := exists_caccioppoli_core_sharp hκ hΨ.add_c hK hu hcomp
  obtain ⟨c₀, hc₀pos, hcut⟩ := exists_cutoff_const d
  have hC'pos : (0 : ℝ) < C + c := by linarith [hΨ.C_nonneg, hΨ.c_pos]
  have hθ0 : (0 : ℝ) ≤ 1 - c / (2 * (C + c)) := by
    have h : c / (2 * (C + c)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith [hΨ.C_nonneg, hΨ.c_pos]
    linarith
  have hθ1 : (1 : ℝ) - c / (2 * (C + c)) < 1 := by
    have h : 0 < c / (2 * (C + c)) := div_pos hΨ.c_pos (by linarith)
    linarith
  obtain ⟨cc, hcc0, hhf⟩ := exists_holefilling_const hθ0 hθ1
  have hγ0 : (0 : ℝ) ≤ 4 * cc * c₀ ^ 2 := mul_nonneg (by linarith) (sq_nonneg c₀)
  refine ⟨max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))), le_max_of_le_left hγ0, ?_⟩
  intro x₁ r s l hr hrs hl0 hl1 hKball
  have hl : (0 : ℝ) ≤ l := hl0.le
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = l ^ 2 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hcore : ∀ w : Euc d → ℝ, IsRegComp K w →
      ∀ S : Set (Euc d), MeasurableSet S → volume S ≠ ⊤ →
      (∀ x ∈ S, u x ≤ l) → (∀ x ∈ S, w x ≤ l) → (∀ x ∈ S, u x ≤ w x) →
      (∀ᵐ x, x ∉ S → u x = w x) → (∀ᵐ x, x ∉ S → weakGrad u x = weakGrad w x) →
      c / 2 * (∫ x in S, ‖weakGrad u x‖ ^ 2) ≤
        (C + c) / 2 * (∫ x in S, ‖weakGrad w x‖ ^ 2) + (B₁ * L) * (volume S).toReal := by
    intro w hw S hS hSfin huS hwS huwS h1 h2
    have := hcore0 l hl0 hl1 w hw S hS hSfin huS hwS huwS h1 h2
    rw [hLdef]
    linarith [this]
  have hAmeas : MeasurableSet {x : Euc d | u x < l} := measurableSet_lt hum measurable_const
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ x in Metric.ball x₁ s, negTrunc l u x ^ 2 := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ,
      m = (volume (Metric.ball x₁ s ∩ {x : Euc d | u x < l})).toReal := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hIdef]; exact integral_nonneg fun x => sq_nonneg _
  have hm0 : 0 ≤ m := by rw [hmdef]; exact ENNReal.toReal_nonneg
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun tt =>
      ∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l}, ‖weakGrad u x‖ ^ 2 := ⟨_, rfl⟩
  have hf0 : ∀ tt, 0 ≤ f tt := fun tt => by
    rw [hfdef]; exact integral_nonneg fun x => sq_nonneg _
  have hfM : ∀ tt, f tt ≤ ∫ x, ‖weakGrad u x‖ ^ 2 := fun tt => by
    rw [hfdef]
    exact setIntegral_le_integral hcomp.integrable_normSq_grad
      (Eventually.of_forall fun x => sq_nonneg _)
  obtain ⟨s', hs'def⟩ : ∃ s' : ℝ, s' = (r + s) / 2 := ⟨_, rfl⟩
  have hrs' : r < s' := by rw [hs'def]; linarith
  have hs's : s' < s := by rw [hs'def]; linarith
  have hITint : Integrable (fun x => negTrunc l u x ^ 2)
      (volume.restrict (Metric.ball x₁ s)) := by
    refine Integrable.mono'
      (integrableOn_const (μ := volume) (C := l ^ 2)
        (measure_ball_lt_top (x := x₁) (r := s)).ne)
      ((hcomp.aesm_negTrunc l).pow 2).restrict ?_
    refine ae_restrict_of_ae (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq_of_nonneg (negTrunc_nonneg l u x) (hcomp.negTrunc_le hl x)
  have hstep : ∀ ρ tt : ℝ, r ≤ ρ → ρ < tt → tt ≤ s' →
      f ρ ≤ (1 - c / (2 * (C + c))) * f tt + (c₀ ^ 2 * I) / (tt - ρ) ^ 2 +
        ((B₁ * L) / (C + c)) * m := by
    intro ρ tt hrρ hρt htts
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr hrρ
    have hgap : (0 : ℝ) < tt - ρ := by linarith
    have hcgap : (0 : ℝ) < (tt - ρ) ^ 2 := by positivity
    obtain ⟨ζ, hζsm, hζcs, hζts, hζ0, hζ1, hζone, hζgrad⟩ := hcut x₁ ρ tt hρ0 hρt
    have hζK : tsupport ζ ⊆ K :=
      hζts.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hKball)
    have hone := caccioppoli_one_scale_super_level hΨ hcomp hum
      (by positivity : (0:ℝ) ≤ B₁ * L) hl hcore hζsm hζcs hζK hζ0 hζ1 hζgrad hζts
    have hIζglob : Integrable (fun x => ζ x * ‖weakGrad u x‖ ^ 2) volume := by
      refine Integrable.mono' hcomp.integrable_normSq_grad
        (hζsm.continuous.aestronglyMeasurable.mul
          (hcomp.aestronglyMeasurable_grad.norm.pow 2))
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hζ0 x), abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg ‖weakGrad u x‖, hζ0 x, hζ1 x]
    have hfρ : f ρ ≤
        ∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l},
          ζ x * ‖weakGrad u x‖ ^ 2 := by
      have hsub : Metric.closedBall x₁ ρ ∩ {x : Euc d | u x < l} ⊆
          Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l} :=
        Set.inter_subset_inter_left _ (Metric.closedBall_subset_closedBall hρt.le)
      have heq : f ρ =
          ∫ x in Metric.closedBall x₁ ρ ∩ {x : Euc d | u x < l},
            ζ x * ‖weakGrad u x‖ ^ 2 := by
        rw [hfdef]
        refine setIntegral_congr_fun (measurableSet_closedBall.inter hAmeas) fun x hx => ?_
        rw [hζone x hx.1, one_mul]
      rw [heq]
      refine setIntegral_mono_set hIζglob.integrableOn ?_ (LE.le.eventuallyLE hsub)
      exact ae_restrict_of_ae (Eventually.of_forall fun x => mul_nonneg (hζ0 x) (sq_nonneg _))
    have hsubs : Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l} ⊆ Metric.ball x₁ s :=
      fun x hx => Metric.closedBall_subset_ball (by linarith) hx.1
    have hITle : (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l},
        negTrunc l u x ^ 2) ≤ I := by
      rw [hIdef]
      refine setIntegral_mono_set hITint ?_ (LE.le.eventuallyLE hsubs)
      exact ae_restrict_of_ae (Eventually.of_forall fun x => sq_nonneg _)
    have hSm : (volume (Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l})).toReal ≤ m := by
      rw [hmdef]
      refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_left _
        (Metric.closedBall_subset_ball (by linarith))))
      exact ((measure_mono Set.inter_subset_left).trans_lt
        (measure_ball_lt_top (x := x₁) (r := s))).ne
    have hVb : (c₀ / (tt - ρ)) ^ 2 *
        (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l}, negTrunc l u x ^ 2) ≤
        (c₀ ^ 2 * I) / (tt - ρ) ^ 2 := by
      rw [div_pow, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hITle (sq_nonneg c₀)) hcgap.le
    have hBm : ((B₁ * L) / (C + c)) *
        (volume (Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l})).toReal ≤
        ((B₁ * L) / (C + c)) * m :=
      mul_le_mul_of_nonneg_left hSm (by positivity)
    have hfe : (∫ x in Metric.closedBall x₁ tt ∩ {x : Euc d | u x < l},
        ‖weakGrad u x‖ ^ 2) = f tt := by rw [hfdef]
    rw [hfe] at hone
    linarith [hfρ, hone, hVb, hBm]
  have hA0 : 0 ≤ c₀ ^ 2 * I := by positivity
  have hB0 : 0 ≤ ((B₁ * L) / (C + c)) * m := mul_nonneg (by positivity) hm0
  have hhole := hhf f r s' (c₀ ^ 2 * I) (((B₁ * L) / (C + c)) * m) (∫ x, ‖weakGrad u x‖ ^ 2)
    hrs' hA0 hB0 hf0 hfM hstep
  have hball : (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l},
      ‖weakGrad u x‖ ^ 2) ≤ f r := by
    rw [hfdef]
    refine setIntegral_mono_set hcomp.integrable_normSq_grad.integrableOn ?_
      (LE.le.eventuallyLE (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall))
    exact ae_restrict_of_ae (Eventually.of_forall fun x => sq_nonneg _)
  have hsr : s' - r = (s - r) / 2 := by rw [hs'def]; ring
  have hsr0 : (0 : ℝ) < (s - r) ^ 2 := by
    have h : 0 < s - r := by linarith
    positivity
  have hexpand : cc * ((c₀ ^ 2 * I) / (s' - r) ^ 2 + ((B₁ * L) / (C + c)) * m) =
      (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I + (cc * (B₁ / (C + c))) * (L * m) := by
    rw [hsr]
    field_simp
    try ring
  have h1 : (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 * I :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_left _ _) hsr0.le) hI0
  have h2 : (cc * (B₁ / (C + c))) * (L * m) ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * (L * m) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hL0 hm0)
  have hfinal : (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l}, ‖weakGrad u x‖ ^ 2) ≤
      max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 * I +
        max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * (L * m) := by
    calc (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l}, ‖weakGrad u x‖ ^ 2)
        ≤ f r := hball
      _ ≤ cc * ((c₀ ^ 2 * I) / (s' - r) ^ 2 + ((B₁ * L) / (C + c)) * m) := hhole
      _ = (4 * cc * c₀ ^ 2) / (s - r) ^ 2 * I + (cc * (B₁ / (C + c))) * (L * m) := hexpand
      _ ≤ _ := by linarith
  rw [hIdef, hmdef, hLdef] at hfinal
  calc (∫ x in Metric.ball x₁ r ∩ {x : Euc d | u x < l}, ‖weakGrad u x‖ ^ 2)
      ≤ _ := hfinal
    _ = max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) / (s - r) ^ 2 *
          (∫ x in Metric.ball x₁ s, negTrunc l u x ^ 2) +
        max (4 * cc * c₀ ^ 2) (cc * (B₁ / (C + c))) * l ^ 2 *
          (volume (Metric.ball x₁ s ∩ {x : Euc d | u x < l})).toReal := by ring

end Komlos.Literature.Regularized
