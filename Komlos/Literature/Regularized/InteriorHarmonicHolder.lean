import Komlos.Literature.Regularized.InteriorHarmonicHolderDecay

/-!
# Link 2 for gradient fields, from the Campanato decay (lane `L3h`)

`exists_reg_excess_decay` (`InteriorHarmonicHolderDecay.lean`) gives the decay of the `L²` excess
of a `Ψ`-harmonic gradient field `H`.  This file turns it into the statement that lane `L3b`
consumes, `exists_regHarmonic_campanato_field'`: `H` has a representative `W` continuous on the
ball, and the decay holds for `W`.

Continuity comes from **Campanato's criterion**
(`Komlos.Literature.exists_holder_of_campanato`).  Its hypothesis is an `L¹` mean-oscillation
bound `∫_{B(x,t)} ‖H - m‖ ≤ C t^{d+α}`, which follows from the `L²` decay by the elementary
inequality `a ≤ a²/(2ε) + ε/2` at `ε = t^β` — no Cauchy–Schwarz needed.  The criterion also
demands *global* local integrability of the field, which `H` need not have up to `∂(ball x₀ r)`;
it is therefore applied on the balls `ball x₀ R` with `R < r` (where `H` is genuinely `L¹`), and
the resulting continuous representatives are glued: two continuous functions that agree a.e. on
an open set agree everywhere on it, so the representatives at different radii are compatible.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

set_option linter.unusedSectionVars false

variable {d : ℕ} {Ψ : Euc d → ℝ}

/-! ### Elementary facts -/

/-- A `Ψ`-harmonic gradient field on `U` is one on any smaller open subset. -/
theorem IsRegHarmonicField.mono {U U' : Set (Euc d)} {h : Euc d → ℝ} {H : Euc d → Euc d}
    (hH : IsRegHarmonicField Ψ U h H) (hU' : IsOpen U') (hsub : U' ⊆ U) :
    IsRegHarmonicField Ψ U' h H where
  isOpen := hU'
  measurable := hH.measurable
  measurable_grad := hH.measurable_grad
  hasWeakGradientOn := hH.hasWeakGradientOn.mono hsub
  integrableOn_sq y t ht := hH.integrableOn_sq y t (ht.trans hsub)
  weakEq ψ hψ hψs hψU := hH.weakEq ψ hψ hψs (hψU.trans hsub)

/-- The `L²` excess only depends on the field up to a null set. -/
theorem sqExcess_congr_ae {W W' : Euc d → Euc d} {x₀ : Euc d} {ρ : ℝ}
    (hWW : ∀ᵐ x ∂(volume.restrict (Metric.closedBall x₀ ρ)), W x = W' x) :
    Komlos.Literature.sqExcess W x₀ ρ = Komlos.Literature.sqExcess W' x₀ ρ := by
  have hWW' : ∀ᵐ x, x ∈ Metric.closedBall x₀ ρ → W x = W' x :=
    (ae_restrict_iff' measurableSet_closedBall).1 hWW
  rw [Komlos.Literature.sqExcess_eq, Komlos.Literature.sqExcess_eq, setAverage_congr_fun
    measurableSet_closedBall hWW']
  refine setIntegral_congr_ae measurableSet_closedBall ?_
  filter_upwards [hWW'] with x hx hxb
  rw [hx hxb]

/-- Two functions continuous on an open set and agreeing a.e. there agree everywhere there. -/
theorem eqOn_of_ae_eq_of_continuousOn {E : Type*} [NormedAddCommGroup E] {V : Set (Euc d)}
    (hV : IsOpen V) {f g : Euc d → E} (hf : ContinuousOn f V) (hg : ContinuousOn g V)
    (hae : ∀ᵐ x ∂(volume.restrict V), f x = g x) : Set.EqOn f g V := by
  by_contra hcon
  obtain ⟨x, hxV, hxne⟩ : ∃ x, x ∈ V ∧ f x ≠ g x := by
    simpa only [Set.EqOn, not_forall, exists_prop] using hcon
  set D : Set (Euc d) := V ∩ (fun y => f y - g y) ⁻¹' {(0 : E)}ᶜ with hDdef
  have hDopen : IsOpen D :=
    (hf.sub hg).isOpen_inter_preimage hV isOpen_compl_singleton
  have hxD : x ∈ D := ⟨hxV, by simpa [sub_eq_zero] using hxne⟩
  have hDnull : volume D = 0 := by
    have hsub : D ⊆ {y | y ∈ V ∧ f y ≠ g y} := by
      intro y hy
      exact ⟨hy.1, by simpa [sub_eq_zero] using hy.2⟩
    have h0 : volume {y | y ∈ V ∧ f y ≠ g y} = 0 := by
      have := (ae_restrict_iff' hV.measurableSet).1 hae
      have hnull : volume {y | ¬ (y ∈ V → f y = g y)} = 0 := this
      refine measure_mono_null (fun y hy => ?_) hnull
      exact fun hcon2 => hy.2 (hcon2 hy.1)
    exact measure_mono_null hsub h0
  exact absurd hDnull (hDopen.measure_pos volume ⟨x, hxD⟩).ne'

/-! ### The continuous representative on a ball with compact closure in the domain -/

section Representative

variable {x₀ : Euc d} {r : ℝ} {h : Euc d → ℝ} {H : Euc d → Euc d}

/-- A `Ψ`-harmonic gradient field is integrable on every closed ball inside its domain. -/
theorem IsRegHarmonicField.integrableOn {U : Set (Euc d)}
    (hH : IsRegHarmonicField Ψ U h H) {y : Euc d} {t : ℝ} (ht : Metric.closedBall y t ⊆ U) :
    IntegrableOn H (Metric.closedBall y t) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall y t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have h2 : MemLp H 2 (volume.restrict (Metric.closedBall y t)) :=
    (memLp_two_iff_integrable_sq_norm hH.measurable_grad.aestronglyMeasurable).2
      (hH.integrableOn_sq y t ht)
  exact h2.integrable (by norm_num)

set_option maxHeartbeats 1000000 in
/-- **A continuous representative on a ball whose closure lies in the domain.**  Campanato's
criterion applied to `1_{B̄(x₀,R)} H`; the `L¹` mean-oscillation hypothesis comes from the `L²`
excess decay through `a ≤ a²/(2ε) + ε/2` at `ε = t^β`. -/
theorem exists_cont_rep_ball (hΨ : IsRegProfile Ψ) (hr : 0 < r)
    (hH : IsRegHarmonicField Ψ (Metric.ball x₀ r) h H)
    (hL2 : IsLocSqIntegrableOn (Metric.ball x₀ r) h) {R : ℝ} (hR : 0 < R)
    (hRr : Metric.closedBall x₀ R ⊆ Metric.ball x₀ r) :
    ∃ W : Euc d → Euc d, ContinuousOn W (Metric.ball x₀ R) ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)), H x = W x := by
  obtain ⟨Cdec, β, hCdec, hβ, hβ1, hdec⟩ := exists_reg_excess_decay hΨ
  set g : Euc d → Euc d := (Metric.closedBall x₀ R).indicator H with hgdef
  have hgH : ∀ x ∈ Metric.closedBall x₀ R, g x = H x := fun x hx => Set.indicator_of_mem hx H
  have hgloc : LocallyIntegrable g volume :=
    ((integrable_indicator_iff measurableSet_closedBall).2 (hH.integrableOn hRr)).locallyIntegrable
  have hballR : Metric.ball x₀ R ⊆ Metric.ball x₀ r :=
    Metric.ball_subset_closedBall.trans hRr
  -- the Campanato hypothesis
  have hcamp : ∀ S : Set (Euc d), IsCompact S → S ⊆ Metric.ball x₀ R →
      ∃ α C R₀ : ℝ, 0 < α ∧ 0 < R₀ ∧ ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ R₀ →
        ∃ m : Euc d, (∫ y in Metric.closedBall x t, ‖g y - m‖) ≤ C * t ^ ((d : ℝ) + α) := by
    intro S hS hSR
    obtain ⟨δ, hδ, hδS⟩ := hS.exists_cthickening_subset_open Metric.isOpen_ball hSR
    have hballs : ∀ x ∈ S, Metric.closedBall x δ ⊆ Metric.ball x₀ R := fun x hx =>
      (Metric.closedBall_subset_cthickening hx δ).trans hδS
    set vol1 : ℝ := volume.real (Metric.closedBall (0 : Euc d) 1) with hvol1def
    have hvol1 : 0 < vol1 := Komlos.Literature.volume_real_closedBall_pos
    set E₀ : ℝ := ∫ y in Metric.closedBall x₀ R, ‖H y‖ ^ 2 with hE₀def
    have hE₀ : 0 ≤ E₀ := integral_nonneg fun _ => sq_nonneg _
    set K : ℝ := Cdec * (2 / δ) ^ ((d : ℝ) + 2 * β) * E₀ with hKdef
    have hK : 0 ≤ K := by
      refine mul_nonneg (mul_nonneg hCdec ?_) hE₀
      exact Real.rpow_nonneg (by positivity) _
    refine ⟨β, (K + vol1) / 2, δ / 2, hβ, by positivity, ?_⟩
    intro x hxS t ht htR
    refine ⟨⨍ y in Metric.closedBall x t, H y, ?_⟩
    have hbx : Metric.closedBall x δ ⊆ Metric.ball x₀ R := hballs x hxS
    have hbxr : Metric.ball x δ ⊆ Metric.ball x₀ r :=
      (Metric.ball_subset_closedBall.trans hbx).trans hballR
    have hHx : IsRegHarmonicField Ψ (Metric.ball x δ) h H := hH.mono Metric.isOpen_ball hbxr
    have hL2x : IsLocSqIntegrableOn (Metric.ball x δ) h := fun y u hu => hL2 y u (hu.trans hbxr)
    have htδ : t ≤ δ / 2 := htR
    have hdecx := hdec x δ hδ h H hHx hL2x t ht htδ
    -- the excess at the scale `δ/2` is bounded by the energy on the big ball
    have hsub2 : Metric.closedBall x (δ / 2) ⊆ Metric.closedBall x₀ R :=
      ((Metric.closedBall_subset_closedBall (by linarith)).trans hbx).trans
        Metric.ball_subset_closedBall
    have hsubt : Metric.closedBall x t ⊆ Metric.closedBall x₀ R :=
      (Metric.closedBall_subset_closedBall (by linarith)).trans hsub2
    have hexc2 : Komlos.Literature.sqExcess H x (δ / 2) ≤ E₀ := by
      have h1 : Komlos.Literature.sqExcess H x (δ / 2) ≤
          ∫ y in Metric.closedBall x (δ / 2), ‖H y - 0‖ ^ 2 :=
        integral_norm_sub_setAverage_sq_le_const' measurableSet_closedBall
          measure_closedBall_lt_top.ne (hH.integrableOn (hsub2.trans hRr))
          (hH.integrableOn_sq x (δ / 2) (hsub2.trans hRr)) 0
      refine h1.trans ?_
      simp only [sub_zero]
      refine setIntegral_mono_set (hH.integrableOn_sq x₀ R hRr)
        (Eventually.of_forall fun y => sq_nonneg _) (Eventually.of_forall hsub2)
    -- hence the `L²` excess decays like `t^{d+2β}`
    have hpow : (2 * t / δ) ^ ((d : ℝ) + 2 * β) = (2 / δ) ^ ((d : ℝ) + 2 * β) *
        t ^ ((d : ℝ) + 2 * β) := by
      rw [← Real.mul_rpow (by positivity) ht.le]
      congr 1
      field_simp
    have hexct : Komlos.Literature.sqExcess H x t ≤ K * t ^ ((d : ℝ) + 2 * β) := by
      refine hdecx.trans ?_
      rw [hpow, hKdef]
      have hcc : 0 ≤ Cdec * (2 / δ) ^ ((d : ℝ) + 2 * β) * t ^ ((d : ℝ) + 2 * β) := by
        refine mul_nonneg (mul_nonneg hCdec (Real.rpow_nonneg (by positivity) _)) ?_
        exact Real.rpow_nonneg ht.le _
      calc Cdec * ((2 / δ) ^ ((d : ℝ) + 2 * β) * t ^ ((d : ℝ) + 2 * β)) *
            Komlos.Literature.sqExcess H x (δ / 2)
          = Cdec * (2 / δ) ^ ((d : ℝ) + 2 * β) * t ^ ((d : ℝ) + 2 * β) *
              Komlos.Literature.sqExcess H x (δ / 2) := by ring
        _ ≤ Cdec * (2 / δ) ^ ((d : ℝ) + 2 * β) * t ^ ((d : ℝ) + 2 * β) * E₀ :=
            mul_le_mul_of_nonneg_left hexc2 hcc
        _ = Cdec * (2 / δ) ^ ((d : ℝ) + 2 * β) * E₀ * t ^ ((d : ℝ) + 2 * β) := by ring
    -- the `L¹` bound, by `a ≤ a²/(2ε) + ε/2` at `ε = t^β`
    set m : Euc d := ⨍ y in Metric.closedBall x t, H y with hmdef
    set ε : ℝ := t ^ β with hεdef
    have hε : 0 < ε := Real.rpow_pos_of_pos ht _
    have hHt : IntegrableOn H (Metric.closedBall x t) volume := hH.integrableOn (hsubt.trans hRr)
    have hHt2 : IntegrableOn (fun y => ‖H y‖ ^ 2) (Metric.closedBall x t) volume :=
      hH.integrableOn_sq x t (hsubt.trans hRr)
    have hnm : IntegrableOn (fun y => ‖H y - m‖) (Metric.closedBall x t) volume :=
      (hHt.sub (integrableOn_const measure_closedBall_lt_top.ne)).norm
    have hnm2 : IntegrableOn (fun y => ‖H y - m‖ ^ 2) (Metric.closedBall x t) volume := by
      have : IsFiniteMeasure (volume.restrict (Metric.closedBall x t)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
      have h2 : MemLp (fun y => H y - m) 2 (volume.restrict (Metric.closedBall x t)) :=
        ((memLp_two_iff_integrable_sq_norm hH.measurable_grad.aestronglyMeasurable).2
          hHt2).sub (memLp_const m)
      exact (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).1 h2
    have hptw : ∀ y : Euc d, ‖H y - m‖ ≤ ‖H y - m‖ ^ 2 / (2 * ε) + ε / 2 := by
      intro y
      have ha : (0 : ℝ) ≤ ‖H y - m‖ := norm_nonneg _
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖H y - m‖ - ε)]
    have hint : (∫ y in Metric.closedBall x t, ‖H y - m‖) ≤
        (∫ y in Metric.closedBall x t, ‖H y - m‖ ^ 2) / (2 * ε) +
          ε / 2 * volume.real (Metric.closedBall x t) := by
      have hb : IntegrableOn
          (fun y => ‖H y - m‖ ^ 2 / (2 * ε) + ε / 2) (Metric.closedBall x t) volume :=
        (hnm2.div_const (2 * ε)).add (integrableOn_const measure_closedBall_lt_top.ne)
      have h1 := setIntegral_mono_on hnm hb measurableSet_closedBall (fun y _ => hptw y)
      have h2 : (∫ y in Metric.closedBall x t, (‖H y - m‖ ^ 2 / (2 * ε) + ε / 2)) =
          (∫ y in Metric.closedBall x t, ‖H y - m‖ ^ 2) / (2 * ε) +
            ε / 2 * volume.real (Metric.closedBall x t) := by
        rw [integral_add (hnm2.div_const (2 * ε))
          (integrableOn_const measure_closedBall_lt_top.ne), integral_div, setIntegral_const,
          smul_eq_mul]
        ring
      rw [h2] at h1
      exact h1
    -- arithmetic
    have hvol : volume.real (Metric.closedBall x t) = t ^ d * vol1 :=
      Komlos.Literature.volume_real_closedBall x ht.le
    have hsq : (∫ y in Metric.closedBall x t, ‖H y - m‖ ^ 2) = Komlos.Literature.sqExcess H x t :=
      rfl
    have htβ : (0 : ℝ) < t ^ β := Real.rpow_pos_of_pos ht β
    have ht1 : t ^ ((d : ℝ) + 2 * β) / (2 * ε) = t ^ ((d : ℝ) + β) / 2 := by
      have hsplit : t ^ ((d : ℝ) + 2 * β) = t ^ ((d : ℝ) + β) * t ^ β := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      rw [hεdef, hsplit]
      field_simp
    have ht2 : ε / 2 * (t ^ d * vol1) = vol1 / 2 * t ^ ((d : ℝ) + β) := by
      have hsplit : t ^ ((d : ℝ) + β) = t ^ ((d : ℝ)) * t ^ β := Real.rpow_add ht _ _
      rw [hεdef, hsplit, Real.rpow_natCast t d]
      ring
    have hfinal : (∫ y in Metric.closedBall x t, ‖g y - m‖) =
        ∫ y in Metric.closedBall x t, ‖H y - m‖ :=
      setIntegral_congr_fun measurableSet_closedBall fun y hy => by rw [hgH y (hsubt hy)]
    rw [hfinal]
    refine hint.trans ?_
    rw [hsq, hvol, ht2]
    have hstep : Komlos.Literature.sqExcess H x t / (2 * ε) ≤
        K * t ^ ((d : ℝ) + 2 * β) / (2 * ε) := by
      exact div_le_div_of_nonneg_right hexct (by positivity)
    have hK2 : K * t ^ ((d : ℝ) + 2 * β) / (2 * ε) = K / 2 * t ^ ((d : ℝ) + β) := by
      rw [mul_div_assoc, ht1]
      ring
    rw [hK2] at hstep
    have : K / 2 * t ^ ((d : ℝ) + β) + vol1 / 2 * t ^ ((d : ℝ) + β) =
        (K + vol1) / 2 * t ^ ((d : ℝ) + β) := by ring
    linarith [hstep]
  obtain ⟨W, hWg, hWc, -⟩ :=
    Komlos.Literature.exists_holder_of_campanato Metric.isOpen_ball hgloc hcamp
  refine ⟨W, hWc, ?_⟩
  filter_upwards [hWg, self_mem_ae_restrict Metric.isOpen_ball.measurableSet] with x hx hxb
  rw [hx]
  exact (hgH x (Metric.ball_subset_closedBall hxb)).symm

set_option maxHeartbeats 1000000 in
/-- **A continuous representative on the whole ball.**  The representatives of
`exists_cont_rep_ball` on the exhausting balls `ball x₀ (r - r/(n+2))` are compatible (two
continuous functions agreeing a.e. on an open set agree there), so they glue. -/
theorem exists_cont_rep (hΨ : IsRegProfile Ψ) (hr : 0 < r)
    (hH : IsRegHarmonicField Ψ (Metric.ball x₀ r) h H)
    (hL2 : IsLocSqIntegrableOn (Metric.ball x₀ r) h) :
    ∃ W : Euc d → Euc d, ContinuousOn W (Metric.ball x₀ r) ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), H x = W x := by
  classical
  set R : ℕ → ℝ := fun n => r - r / ((n : ℝ) + 2) with hRdef
  have hRlt : ∀ n, R n < r := fun n => by
    have : 0 < r / ((n : ℝ) + 2) := by positivity
    simp only [hRdef]
    linarith
  have hRpos : ∀ n, 0 < R n := fun n => by
    have h2 : r / ((n : ℝ) + 2) ≤ r / 2 := by
      refine div_le_div_of_nonneg_left hr.le (by norm_num) ?_
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    simp only [hRdef]
    linarith
  have hRmono : Monotone R := by
    intro m n hmn
    have hm : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
      have := Nat.cast_le (α := ℝ) |>.2 hmn
      linarith
    have : r / ((n : ℝ) + 2) ≤ r / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr.le (by positivity) hm
    simp only [hRdef]
    linarith
  have hRsub : ∀ n, Metric.closedBall x₀ (R n) ⊆ Metric.ball x₀ r := fun n =>
    Metric.closedBall_subset_ball (hRlt n)
  have hcover : ∀ x ∈ Metric.ball x₀ r, ∃ n, x ∈ Metric.ball x₀ (R n) := by
    intro x hx
    have hd : dist x x₀ < r := Metric.mem_ball.1 hx
    set c : ℝ := r - dist x x₀ with hcdef
    have hc : 0 < c := by simp only [hcdef]; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (r / c)
    refine ⟨n, Metric.mem_ball.2 ?_⟩
    have h2 : r / c < (n : ℝ) + 2 := by linarith
    have h3 : r / ((n : ℝ) + 2) < c := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hc] at h2
      linarith
    simp only [hRdef, hcdef] at h3 ⊢
    linarith
  choose W hW using fun n => exists_cont_rep_ball hΨ hr hH hL2 (hRpos n) (hRsub n)
  -- the representatives are compatible
  have hcompat : ∀ m n : ℕ, m ≤ n → Set.EqOn (W m) (W n) (Metric.ball x₀ (R m)) := by
    intro m n hmn
    refine eqOn_of_ae_eq_of_continuousOn Metric.isOpen_ball (hW m).1
      (((hW n).1).mono (Metric.ball_subset_ball (hRmono hmn))) ?_
    have h1 := (hW m).2
    have h2 : ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R m))), H x = W n x :=
      ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (hRmono hmn)) (hW n).2
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← hx1, hx2]
  set V : Euc d → Euc d :=
    fun x => if hx : ∃ n, x ∈ Metric.ball x₀ (R n) then W (Nat.find hx) x else 0 with hVdef
  have hV : ∀ (n : ℕ) (x : Euc d), x ∈ Metric.ball x₀ (R n) → V x = W n x := by
    intro n x hx
    have hex : ∃ k, x ∈ Metric.ball x₀ (R k) := ⟨n, hx⟩
    have hfind : x ∈ Metric.ball x₀ (R (Nat.find hex)) := Nat.find_spec hex
    have hle : Nat.find hex ≤ n := Nat.find_le hx
    simp only [hVdef, dif_pos hex]
    exact hcompat (Nat.find hex) n hle hfind
  refine ⟨V, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := hcover x hx
    have hnbhd : Metric.ball x₀ (R n) ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hn
    have hWn : ContinuousAt (W n) x := ((hW n).1).continuousAt hnbhd
    have heq : V =ᶠ[𝓝 x] W n := by
      filter_upwards [hnbhd] with y hy using hV n y hy
    exact (hWn.congr heq.symm).continuousWithinAt
  · rw [ae_restrict_iff' Metric.isOpen_ball.measurableSet]
    have hnull : ∀ n : ℕ, ∀ᵐ x, x ∈ Metric.ball x₀ (R n) → H x = V x := by
      intro n
      have h1 := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).1 (hW n).2
      filter_upwards [h1] with x hx hxb
      rw [hx hxb, hV n x hxb]
    have hall : ∀ᵐ x, ∀ n : ℕ, x ∈ Metric.ball x₀ (R n) → H x = V x := ae_all_iff.2 hnull
    filter_upwards [hall] with x hx hxb
    obtain ⟨n, hn⟩ := hcover x hxb
    exact hx n hn

end Representative

/-! ### Link 2 for gradient fields, in the shape lane `L3b` consumes -/

/-- **(link 2, field form) The Campanato decay of a `Ψ`-harmonic gradient field.**

This is `Komlos.Literature.Regularized.exists_regHarmonic_campanato_field` of
`InteriorHarmonic.lean` (lane `L3b`), verbatim except for the extra hypothesis
`IsLocSqIntegrableOn (ball x₀ r) h` (see the DEVIATION recorded at `IsLocSqIntegrableOn`).

**DEVIATION.**  Lane `L3b` derives its version from the named `sorry`
`exists_regHarmonic_holder_field`, which is **false** as stated: it asks for a sup bound on
`closedBall x₀ (r/2)` controlled by the `L²` excess on the *same* ball, and points of the boundary
sphere have no interior room inside the data ball.  Counterexample for `Ψ = ‖·‖²/2`, `d = 2`,
`x₀ = 0`, `r = 1`: `H_n = ∇ Re (z^{n+1}/((n+1) 2^{-n})) = (Re (2z)^n, -Im (2z)^n)` is harmonic on
`B_1` with `(H_n)_{B_{1/2}} = H_n(0) = 0` and `⨍_{B_{1/2}} ‖H_n‖² = 1/(n+1) → 0`, while for odd `n`
`‖H_n(1/2) - H_n(-1/2)‖² = 4` at distance `1 = r`.  The present theorem proves instead the
*consequence* that lane `L3b` and the rest of the chain actually use, so that the false lemma
becomes dead code. -/
theorem exists_regHarmonic_campanato_field' (hΨ : IsRegProfile Ψ) :
    ∃ Cdec β : ℝ, 0 ≤ Cdec ∧ 0 < β ∧ β < 1 ∧
      ∀ (x₀ : Euc d) (r : ℝ), 0 < r → ∀ (h : Euc d → ℝ) (H : Euc d → Euc d),
        IsRegHarmonicField Ψ (Metric.ball x₀ r) h H →
        IsLocSqIntegrableOn (Metric.ball x₀ r) h →
        ∃ W : Euc d → Euc d, ContinuousOn W (Metric.ball x₀ r) ∧
          (∀ᵐ x ∂(volume.restrict (Metric.ball x₀ r)), H x = W x) ∧
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 2 →
            Komlos.Literature.sqExcess W x₀ ρ ≤
              Cdec * (2 * ρ / r) ^ ((d : ℝ) + 2 * β) *
                Komlos.Literature.sqExcess W x₀ (r / 2) := by
  obtain ⟨Cdec, β, hCdec, hβ, hβ1, hdec⟩ := exists_reg_excess_decay hΨ
  refine ⟨Cdec, β, hCdec, hβ, hβ1, fun x₀ r hr h H hH hL2 => ?_⟩
  obtain ⟨W, hWc, hWae⟩ := exists_cont_rep hΨ hr hH hL2
  refine ⟨W, hWc, hWae, fun ρ hρ hρr => ?_⟩
  have hsubρ : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r :=
    Metric.closedBall_subset_ball (by linarith)
  have hsub2 : Metric.closedBall x₀ (r / 2) ⊆ Metric.ball x₀ r :=
    Metric.closedBall_subset_ball (by linarith)
  have e1 : Komlos.Literature.sqExcess W x₀ ρ = Komlos.Literature.sqExcess H x₀ ρ :=
    sqExcess_congr_ae
      ((ae_restrict_of_ae_restrict_of_subset hsubρ hWae).mono fun x hx => hx.symm)
  have e2 : Komlos.Literature.sqExcess W x₀ (r / 2) = Komlos.Literature.sqExcess H x₀ (r / 2) :=
    sqExcess_congr_ae
      ((ae_restrict_of_ae_restrict_of_subset hsub2 hWae).mono fun x hx => hx.symm)
  rw [e1, e2]
  exact hdec x₀ r hr h H hH hL2 ρ hρ hρr

end Komlos.Literature.Regularized
