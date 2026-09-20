import Komlos.Literature.Regularized.ScalarLimitGtTwoAux

/-!
# From truncated kinetic bounds to `λ_{p,F}(K)/p`, for `p > 2`

`REGULARIZED_ROUTE.md`, Revision 2, *Scalar limits*, lower half, case `2 < p`: the last two
steps of the argument, for a *fixed* admissible competitor `v`.

## The two steps

* **Monotone convergence in the truncation level.**  For every `q` the truncated profile
  `Θ_R(q) = h_R((2/p) F q)` is eventually (in `R`) equal to `Λ(q) = ((2/p) F q)^p / p`, so the
  kinetic densities converge pointwise.  Fatou's lemma (`lintegral_liminf_le'`) upgrades the
  uniform bound `∫ D_{Θ_R}(v, ∇v) ≤ E` to integrability of `D_Λ(v, ∇v)` together with
  `∫ D_Λ(v, ∇v) ≤ E` (`integral_limitProfile_le`).
* **The chain rule for the concave power.**  With `β = 1/p < 1/2` the shifted power
  `powShift β τ` has a *bounded* derivative (this is where `p > 2` is used: `2β - 1 < 0`, so the
  truncation from above of the `p ≤ 2` case is unnecessary and the shift `τ` alone suffices), so
  `u_τ = powShift β τ ∘ v ∈ W₀^{1,p}(K)`, and `∫ F(∇u_τ)^p ≤ p ∫ D_Λ(v, ∇v)` pointwise.  Letting
  `τ ↓ 0` in `lambdaSob_mul_le` gives `λ_{p,F}(K) ≤ p E`
  (`lambdaSob_le_of_integral_limitProfile`).

The combination is `lambdaGen_div_le_of_truncDensity_le`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ}

/-! ### `L^q` membership -/

/-- `L^q` membership from integrability of `|f|^q` (the `ScalarLimitGtTwo*` copy of
`memLp_ofReal_of_integrable_rpow`, which lives downstream in `ScalarLimitLower.lean`). -/
theorem memLp_ofReal_of_rpow_abs_integrable {q : ℝ} (hq : 0 < q) {f : Euc d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hint : Integrable fun x => |f x| ^ q) :
    MemLp f (ENNReal.ofReal q) volume := by
  refine (integrable_norm_rpow_iff hf
    (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq) ENNReal.ofReal_ne_top).1 ?_
  rw [ENNReal.toReal_ofReal hq.le]
  simpa only [Real.norm_eq_abs] using hint

/-! ### The limiting profile is continuous -/

section LimitProfile

variable {p : ℝ} {F : Euc d → ℝ}

theorem continuous_limitProfile (hp : 1 < p) (hF : IsSmoothStrictNorm F) :
    Continuous (limitProfile p F) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hrc : Continuous fun y : ℝ => y ^ p :=
    continuous_iff_continuousAt.2 fun y => Real.continuousAt_rpow_const y p (Or.inr hp0.le)
  exact (hrc.comp (continuous_const.mul hF.continuous)).div_const p

end LimitProfile

/-! ### Step 1: Fatou in the truncation level -/

/-- **The `R → ∞` limit of the truncated kinetic bounds.**  If the kinetic integrals of the
truncated profiles `Θ_R` at a fixed admissible `v` are bounded by `E` for every `R > 0`, then the
kinetic integrand of the limiting profile `Λ` is integrable with integral at most `E`. -/
theorem integral_limitProfile_le {p : ℝ} (hp : 1 < p) (hp2 : 2 ≤ p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} {v : Euc d → ℝ}
    (hv : IsRegAdmissible 2 K v) {E : ℝ}
    (hb : ∀ R : ℝ, 0 < R →
      (∫ x, Korevaar.homogeneousDensity 2 (truncDensity p F R) (v x) (weakGrad v x)) ≤ E) :
    (Integrable fun x =>
        Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x)) ∧
      (∫ x, Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x)) ≤ E := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_isMollifier (d := d) (ε := 1) one_pos
  set f : ℕ → Euc d → ℝ := fun n x =>
    Korevaar.homogeneousDensity 2 (truncDensity p F ((n : ℝ) + 1)) (v x) (weakGrad v x) with hf
  set g : Euc d → ℝ := fun x =>
    Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x) with hg
  have hRn : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  -- measurability
  have hfm : ∀ n, AEStronglyMeasurable (f n) volume := fun n =>
    aestronglyMeasurable_kinetic (continuous_truncDensity hp hF) hv.aestronglyMeasurable
      hv.aestronglyMeasurable_weakGrad
  have hgm : AEStronglyMeasurable g volume :=
    aestronglyMeasurable_kinetic (continuous_limitProfile hp hF) hv.aestronglyMeasurable
      hv.aestronglyMeasurable_weakGrad
  -- nonnegativity
  have hf0 : ∀ n x, 0 ≤ f n x := fun n x =>
    homogeneousDensity_two_nonneg
      (fun q => truncDensity_nonneg hp (hRn n).le hF q) _ _
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    homogeneousDensity_two_nonneg (fun q => limitProfile_nonneg hp hF q) _ _
  -- integrability of the truncated densities, by comparison with a genuine regularized profile
  have hfi : ∀ n, Integrable (f n) volume := by
    intro n
    have hΨ := isRegProfile_regProfile (p := p) (R := (n : ℝ) + 1) (F := F) (ρ := ρ₀) hp
      (hRn n) hF hρ₀
    obtain ⟨c, C, hW⟩ := hΨ.exists_isRegProfileWith
    refine Integrable.mono' (integrable_kinetic hW hv.memW0 hv.nonneg) (hfm n)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 n x)]
    exact homogeneousDensity_two_mono
      (fun q => truncDensity_le_regProfile hp hp2 hF (hRn n) le_rfl hρ₀ q) _ _
  -- pointwise convergence
  have hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    intro x
    refine tendsto_const_nhds.congr' ?_
    have hev := eventually_truncDensity_eq hp hF ((v x)⁻¹ • weakGrad v x)
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually hev] with n hn
    show g x = f n x
    simp only [hf, hg, Korevaar.homogeneousDensity, hn]
  -- Fatou
  have hE0 : 0 ≤ E :=
    le_trans (integral_nonneg (hf0 0)) (hb (((0 : ℕ) : ℝ) + 1) (hRn 0))
  have hlint : ∫⁻ x, ENNReal.ofReal (g x) ≤ ENNReal.ofReal E := by
    have hcong : (fun x => ENNReal.ofReal (g x)) =
        fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop := by
      funext x
      have h := (ENNReal.continuous_ofReal.tendsto (g x)).comp (hlim x)
      exact ((h.liminf_eq).symm).trans rfl
    rw [hcong]
    refine le_trans (lintegral_liminf_le' fun n =>
      (ENNReal.measurable_ofReal.comp_aemeasurable (hfm n).aemeasurable)) ?_
    refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (Eventually.of_forall (hf0 n))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hb ((n : ℝ) + 1) (hRn n)
    simpa [hf] using this
  have hgi : Integrable g volume := by
    refine ⟨hgm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg0)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨hgi, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0)
  rw [← this] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff hE0).1 hlint

/-! ### Step 2: the chain rule for the concave power `t ↦ t^{2/p}` -/

section Chain

variable {p β τ : ℝ}

/-- The derivative of `powShift β τ` is bounded by `2 β τ^{β - 1/2}` when `β ≤ 1/2`: this is
where `p ≥ 2` enters (for `p < 2` the derivative is *not* bounded and the `lowPow` truncation
from above of `ScalarLimitLower.lean` is needed instead). -/
theorem abs_deriv_powShift_le (hβ0 : 0 < β) (hβ : β ≤ 1 / 2) (hτ : 0 < τ) (t : ℝ) :
    |deriv (powShift β τ) t| ≤ 2 * β * τ ^ (β - 1 / 2) := by
  have hbase : (0 : ℝ) < t ^ 2 + τ := by positivity
  rw [deriv_powShift hτ]
  have habs : |2 * β * t * (t ^ 2 + τ) ^ (β - 1)| = 2 * β * |t| * (t ^ 2 + τ) ^ (β - 1) := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hbase _),
      abs_of_pos (by linarith : (0:ℝ) < 2 * β)]
  rw [habs]
  have h1 : |t| ≤ (t ^ 2 + τ) ^ ((1 : ℝ) / 2) := by
    have habs2 : |t| = (t ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
    rw [habs2]
    exact Real.rpow_le_rpow (sq_nonneg t) (by linarith) (by norm_num)
  have h2 : (t ^ 2 + τ) ^ ((1 : ℝ) / 2) * (t ^ 2 + τ) ^ (β - 1) = (t ^ 2 + τ) ^ (β - 1 / 2) := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  have h3 : (t ^ 2 + τ) ^ (β - 1 / 2) ≤ τ ^ (β - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hτ (by nlinarith [sq_nonneg t]) (by linarith)
  have h4 : |t| * (t ^ 2 + τ) ^ (β - 1) ≤ (t ^ 2 + τ) ^ (β - 1 / 2) := by
    calc |t| * (t ^ 2 + τ) ^ (β - 1)
        ≤ (t ^ 2 + τ) ^ ((1 : ℝ) / 2) * (t ^ 2 + τ) ^ (β - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hbase.le _)
      _ = (t ^ 2 + τ) ^ (β - 1 / 2) := h2
  calc 2 * β * |t| * (t ^ 2 + τ) ^ (β - 1) = 2 * β * (|t| * (t ^ 2 + τ) ^ (β - 1)) := by ring
    _ ≤ 2 * β * (t ^ 2 + τ) ^ (β - 1 / 2) :=
        mul_le_mul_of_nonneg_left h4 (by linarith)
    _ ≤ 2 * β * τ ^ (β - 1 / 2) := mul_le_mul_of_nonneg_left h3 (by linarith)

/-- The derivative of the shifted power is bounded by the derivative of the untruncated power,
`2 β t^{2β-1}`, at every `t > 0`. -/
theorem deriv_powShift_le_rpow (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hτ : 0 < τ) {t : ℝ} (ht : 0 < t) :
    deriv (powShift β τ) t ≤ 2 * β * t ^ (2 * β - 1) := by
  have hsq : (0 : ℝ) < t ^ 2 := by positivity
  rw [deriv_powShift hτ]
  have h1 : (t ^ 2 + τ) ^ (β - 1) ≤ (t ^ 2) ^ (β - 1) :=
    Real.rpow_le_rpow_of_nonpos hsq (by linarith) (by linarith)
  have h2 : (t ^ 2) ^ (β - 1) = t ^ (2 * β - 2) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring
  have h3 : t * t ^ (2 * β - 2) = t ^ (2 * β - 1) := by
    rw [show (2 * β - 1 : ℝ) = 1 + (2 * β - 2) by ring, Real.rpow_add ht, Real.rpow_one]
  calc 2 * β * t * (t ^ 2 + τ) ^ (β - 1) = 2 * β * (t * (t ^ 2 + τ) ^ (β - 1)) := by ring
    _ ≤ 2 * β * (t * t ^ (2 * β - 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ht.le) (by linarith)
        rw [← h2]; exact h1
    _ = 2 * β * t ^ (2 * β - 1) := by rw [h3]

theorem deriv_powShift_nonneg (hβ0 : 0 < β) (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ deriv (powShift β τ) t := by
  rw [deriv_powShift hτ]
  have : (0 : ℝ) < t ^ 2 + τ := by positivity
  exact mul_nonneg (mul_nonneg (by linarith) ht) (Real.rpow_nonneg this.le _)

@[simp] theorem powShift_zero_arg : powShift β τ 0 = 0 := by
  simp [powShift]

/-- `powShift β τ t → t^{2β}` as `τ ↓ 0`, along `τ = 1/(n+1)`. -/
theorem tendsto_powShift_rpow (hβ0 : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => powShift β (1 / ((n : ℝ) + 1)) t) atTop (𝓝 (t ^ (2 * β))) := by
  have hτlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrc : Continuous fun x : ℝ => x ^ β :=
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x β (Or.inr hβ0.le)
  have h1 : Tendsto (fun n : ℕ => (t ^ 2 + 1 / ((n : ℝ) + 1)) ^ β) atTop (𝓝 ((t ^ 2) ^ β)) :=
    (hrc.tendsto _).comp (by simpa using tendsto_const_nhds.add hτlim)
  have h2 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ β) atTop (𝓝 0) := by
    have h := (hrc.tendsto (0 : ℝ)).comp hτlim
    rwa [Real.zero_rpow hβ0.ne'] at h
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  have h4 : (t ^ 2) ^ β = t ^ (2 * β) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
    norm_num
  rw [← h4]
  simpa only [powShift] using h3

end Chain

/-! ### The pointwise bound and the competitor -/

section Competitor

variable {p β τ : ℝ} {F : Euc d → ℝ} {K : Set (Euc d)} {v : Euc d → ℝ}

/-- `powShift β τ t ^ p ≤ t²` for `β = 1/p`. -/
theorem powShift_rpow_le_sq (hp : 1 < p) (hβ : β = 1 / p) (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) :
    powShift β τ t ^ p ≤ t ^ 2 := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one hp0]; linarith
  have h2βp : 2 * β * p = 2 := by rw [hβ]; field_simp
  have h0 : 0 ≤ powShift β τ t := powShift_nonneg hβ0.le hτ t
  have h1 : powShift β τ t ≤ t ^ (2 * β) := by
    have h := powShift_le_abs_rpow hβ0.le hβ1 hτ t
    rwa [abs_of_nonneg ht] at h
  calc powShift β τ t ^ p ≤ (t ^ (2 * β)) ^ p := Real.rpow_le_rpow h0 h1 hp0.le
    _ = t ^ (2 * β * p) := by rw [← Real.rpow_mul ht]
    _ = t ^ 2 := by rw [h2βp, rpow_two_eq_sq]

/-- **The pointwise kinetic bound for `p ≥ 2`**: `(powShift')^p F(ξ)^p ≤ p D_Λ(t, ξ)`.  The two
sides are in fact equal up to the inequality `powShift' t ≤ 2β t^{2β-1}`. -/
theorem rpow_deriv_powShift_mul_le (hp : 1 < p) (hβ : β = 1 / p) (hF : IsSmoothStrictNorm F)
    (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) (ξ : Euc d) :
    deriv (powShift β τ) t ^ p * F ξ ^ p ≤
      p * Korevaar.homogeneousDensity 2 (limitProfile p F) t ξ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one hp0]; linarith
  have h2βeq : 2 * β = 2 / p := by rw [hβ]; ring
  have hFξ : 0 ≤ F ξ := hF.nonneg ξ
  rcases ht.eq_or_lt with rfl | htpos
  · rw [deriv_powShift hτ]
    have h1 : 2 * β * (0 : ℝ) * ((0 : ℝ) ^ 2 + τ) ^ (β - 1) = 0 := by ring
    rw [h1, Real.zero_rpow hpne, zero_mul, homogeneousDensity_two_zero, mul_zero]
  · have h2βm : (2 * β - 1) * p = 2 - p := by rw [hβ]; field_simp
    have hd0 : 0 ≤ deriv (powShift β τ) t := deriv_powShift_nonneg hβ0 hτ htpos.le
    have hd : deriv (powShift β τ) t ≤ 2 * β * t ^ (2 * β - 1) :=
      deriv_powShift_le_rpow hβ0 hβ1 hτ htpos
    have hq : F (t⁻¹ • ξ) = t⁻¹ * F ξ := by
      rw [hF.homog, abs_of_pos (inv_pos.2 htpos)]
    have hinv : (t⁻¹ : ℝ) ^ p = (t ^ p)⁻¹ := Real.inv_rpow htpos.le p
    have hexp : t ^ (2 : ℝ) * (t ^ p)⁻¹ = t ^ (2 - p) := by
      rw [← Real.rpow_neg htpos.le, ← Real.rpow_add htpos]
      congr 1
      try ring
    have hbase : 2 / p * F (t⁻¹ • ξ) = 2 / p * t⁻¹ * F ξ := by rw [hq]; ring
    have hRw : p * Korevaar.homogeneousDensity 2 (limitProfile p F) t ξ
        = t ^ (2 : ℝ) * (2 / p * t⁻¹ * F ξ) ^ p := by
      simp only [Korevaar.homogeneousDensity, limitProfile, hbase]
      field_simp
    have heq : t ^ (2 : ℝ) * (2 / p * t⁻¹ * F ξ) ^ p =
        (2 * β) ^ p * (t ^ (2 - p) * F ξ ^ p) := by
      rw [Real.mul_rpow (by positivity) hFξ,
        Real.mul_rpow (by positivity) (inv_nonneg.2 htpos.le), hinv, h2βeq, ← hexp]
      ring
    have hL : deriv (powShift β τ) t ^ p * F ξ ^ p ≤ (2 * β) ^ p * (t ^ (2 - p) * F ξ ^ p) := by
      have h1 : deriv (powShift β τ) t ^ p ≤ (2 * β * t ^ (2 * β - 1)) ^ p :=
        Real.rpow_le_rpow hd0 hd hp0.le
      have h2 : (2 * β * t ^ (2 * β - 1)) ^ p = (2 * β) ^ p * t ^ (2 - p) := by
        rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg htpos.le _),
          ← Real.rpow_mul htpos.le, h2βm]
      calc deriv (powShift β τ) t ^ p * F ξ ^ p ≤ ((2 * β) ^ p * t ^ (2 - p)) * F ξ ^ p := by
            rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hFξ _)
        _ = (2 * β) ^ p * (t ^ (2 - p) * F ξ ^ p) := by ring
    rw [hRw, heq]
    exact hL

/-- The derivative of `powShift β τ` is continuous. -/
theorem continuous_deriv_powShift (hτ : 0 < τ) (β : ℝ) : Continuous (deriv (powShift β τ)) := by
  have hrw : deriv (powShift β τ) = fun s : ℝ => 2 * β * s * (s ^ 2 + τ) ^ (β - 1) :=
    funext (deriv_powShift hτ β)
  rw [hrw]
  have hb : Continuous fun s : ℝ => s ^ 2 + τ := (continuous_pow 2).add continuous_const
  have hpos : ∀ s : ℝ, (0 : ℝ) < s ^ 2 + τ := fun s => by positivity
  exact (continuous_const.mul continuous_id).mul (hb.rpow_const fun s => Or.inl (hpos s).ne')

/-- **The competitor `u_τ = powShift (1/p) τ ∘ v` lies in `W₀^{1,p}(K)`.**  The `L^p` bounds for
the function and its gradient come from `powShift_rpow_le_sq` and from the pointwise kinetic
bound `rpow_deriv_powShift_mul_le` together with `c_F ‖ξ‖ ≤ F ξ`; the chain rule itself is
`memW0_comp` at exponent `2`, where `v` lives. -/
theorem memW0_powShift_comp (hp2 : 2 < p) (hβ : β = 1 / p) (hF : IsSmoothStrictNorm F)
    (hv : IsRegAdmissible 2 K v)
    (hgi : Integrable (fun x =>
      Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x)) volume)
    (hτ : 0 < τ) :
    MemW0 p K (fun x => powShift β τ (v x)) ∧
      weakGrad (fun x => powShift β τ (v x)) =ᵐ[volume]
        fun x => deriv (powShift β τ) (v x) • weakGrad v x := by
  have hp : 1 < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one hp0]; linarith
  have hβhalf : β ≤ 1 / 2 := by
    rw [hβ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  obtain ⟨cF, hcF0, hcF⟩ := exists_pos_mul_norm_le' hF
  have hv2 : MemLp v 2 volume := by
    have h := hv.memW0.memLp; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at h
  have hg2 : MemLp (weakGrad v) 2 volume := by
    have h := hv.memW0.memLp_weakGrad; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at h
  have hi1 : Integrable fun x => v x ^ 2 := hv.integrable_sq
  -- the chain rule at exponent `2`
  obtain ⟨hu2, hug⟩ := memW0_comp (p := 2) (K := K) (f := v) (by norm_num) hv.memW0
    (G := powShift β τ) ((contDiff_powShift hτ β).of_le (by norm_cast)) powShift_zero_arg
    (L := 2 * β * τ ^ (β - 1 / 2)) (fun t => abs_deriv_powShift_le hβ0 hβhalf hτ t)
  refine ⟨?_, hug⟩
  have hum : AEStronglyMeasurable (fun x => powShift β τ (v x)) volume :=
    (contDiff_powShift hτ β).continuous.comp_aestronglyMeasurable hv2.1
  -- `u ∈ L^p`
  have hmeas_abs : AEStronglyMeasurable (fun x => |powShift β τ (v x)| ^ p) volume := by
    have hc : Continuous fun y : ℝ => |y| ^ p :=
      (continuous_iff_continuousAt.2 fun y =>
        Real.continuousAt_rpow_const y p (Or.inr hp0.le)).comp continuous_abs
    exact hc.comp_aestronglyMeasurable hum
  have huint : Integrable fun x => |powShift β τ (v x)| ^ p := by
    refine Integrable.mono' hi1 hmeas_abs (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (powShift_nonneg hβ0.le hτ _)]
    exact powShift_rpow_le_sq hp hβ hτ (hv.nonneg x)
  -- the gradient in `L^p`
  have hgm : AEStronglyMeasurable (fun x => deriv (powShift β τ) (v x) • weakGrad v x) volume :=
    ((continuous_deriv_powShift hτ β).comp_aestronglyMeasurable hv2.1).smul hg2.1
  have hgle : ∀ x, ‖deriv (powShift β τ) (v x) • weakGrad v x‖ ^ p ≤
      cF⁻¹ ^ p *
        (p * Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x)) := by
    intro x
    have hd0 : 0 ≤ deriv (powShift β τ) (v x) := deriv_powShift_nonneg hβ0 hτ (hv.nonneg x)
    have hn : ‖weakGrad v x‖ ≤ cF⁻¹ * F (weakGrad v x) := by
      have h := hcF (weakGrad v x)
      rw [inv_mul_eq_div, le_div_iff₀ hcF0]
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0]
    have h1 : (deriv (powShift β τ) (v x) * ‖weakGrad v x‖) ^ p ≤
        (deriv (powShift β τ) (v x) * (cF⁻¹ * F (weakGrad v x))) ^ p :=
      Real.rpow_le_rpow (mul_nonneg hd0 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hn hd0) hp0.le
    have h2 : (deriv (powShift β τ) (v x) * (cF⁻¹ * F (weakGrad v x))) ^ p
        = cF⁻¹ ^ p * (deriv (powShift β τ) (v x) ^ p * F (weakGrad v x) ^ p) := by
      rw [show deriv (powShift β τ) (v x) * (cF⁻¹ * F (weakGrad v x))
            = cF⁻¹ * (deriv (powShift β τ) (v x) * F (weakGrad v x)) by ring,
        Real.mul_rpow (by positivity) (mul_nonneg hd0 (hF.nonneg _)),
        Real.mul_rpow hd0 (hF.nonneg _)]
    have h3 := rpow_deriv_powShift_mul_le hp hβ hF hτ (hv.nonneg x) (weakGrad v x)
    have h4 : (0 : ℝ) ≤ cF⁻¹ ^ p := Real.rpow_nonneg (by positivity) _
    calc (deriv (powShift β τ) (v x) * ‖weakGrad v x‖) ^ p
        ≤ cF⁻¹ ^ p * (deriv (powShift β τ) (v x) ^ p * F (weakGrad v x) ^ p) := by
          rw [← h2]; exact h1
      _ ≤ cF⁻¹ ^ p *
            (p * Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x)) :=
          mul_le_mul_of_nonneg_left h3 h4
  have hgint : Integrable fun x => ‖deriv (powShift β τ) (v x) • weakGrad v x‖ ^ p := by
    have hc : Continuous fun y : ℝ => y ^ p :=
      continuous_iff_continuousAt.2 fun y => Real.continuousAt_rpow_const y p (Or.inr hp0.le)
    refine Integrable.mono' ((hgi.const_mul p).const_mul (cF⁻¹ ^ p))
      (hc.comp_aestronglyMeasurable hgm.norm) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hgle x
  have hgmem : MemLp (fun x => deriv (powShift β τ) (v x) • weakGrad v x)
      (ENNReal.ofReal p) volume := by
    refine (integrable_norm_rpow_iff hgm
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0)
      ENNReal.ofReal_ne_top).1 ?_
    rw [ENNReal.toReal_ofReal hp0.le]
    exact hgint
  exact
    { memLp := memLp_ofReal_of_rpow_abs_integrable hp0 hum huint
      ae_eq_zero := Eventually.of_forall fun x hx => by
        rw [hv.eq_zero_of_notMem x hx, powShift_zero_arg]
      exists_weakGradient :=
        ⟨fun x => deriv (powShift β τ) (v x) • weakGrad v x,
          hu2.hasWeakGradient.congr_right hug, hgmem⟩ }

end Competitor

/-! ### Step 2: `λ_{p,F}(K) ≤ p E` -/

/-- **The chain-rule step.**  If the kinetic integrand of the limiting profile is integrable with
integral at most `E`, then `λ_{p,F}(K) ≤ p E`: apply `lambdaSob_mul_le` to the competitor
`u_τ = powShift (1/p) τ ∘ v` and let `τ ↓ 0`, where `∫ u_τ^p → ∫ v² = 1`. -/
theorem lambdaSob_le_of_integral_limitProfile {p : ℝ} (hp2 : 2 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} {v : Euc d → ℝ}
    (hv : IsRegAdmissible 2 K v) {E : ℝ}
    (hgi : Integrable (fun x =>
      Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x)) volume)
    (hgb : (∫ x, Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x)) ≤ E) :
    lambdaSob p F K ≤ p * E := by
  have hp : 1 < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  set β : ℝ := 1 / p with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβ1 : β ≤ 1 := by rw [hβdef, div_le_one hp0]; linarith
  have h2βp : 2 * β * p = 2 := by rw [hβdef]; field_simp
  have hv2 : MemLp v 2 volume := by
    have h := hv.memW0.memLp; rwa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] at h
  have hi1 : Integrable fun x => v x ^ 2 := hv.integrable_sq
  have hrc : Continuous fun y : ℝ => y ^ p :=
    continuous_iff_continuousAt.2 fun y => Real.continuousAt_rpow_const y p (Or.inr hp0.le)
  have hkey : ∀ n : ℕ,
      lambdaSob p F K * (∫ x, powShift β (1 / ((n : ℝ) + 1)) (v x) ^ p) ≤ p * E := by
    intro n
    have hτ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨hu, hug⟩ := memW0_powShift_comp hp2 hβdef hF hv hgi hτ
    have hlam := lambdaSob_mul_le hp0 hF.nonneg hu
    have habs : (∫ x, |powShift β (1 / ((n : ℝ) + 1)) (v x)| ^ p) =
        ∫ x, powShift β (1 / ((n : ℝ) + 1)) (v x) ^ p :=
      integral_congr_ae (Eventually.of_forall fun x => by
        show |powShift β (1 / ((n : ℝ) + 1)) (v x)| ^ p
          = powShift β (1 / ((n : ℝ) + 1)) (v x) ^ p
        rw [abs_of_nonneg (powShift_nonneg hβ0.le hτ _)])
    rw [habs] at hlam
    refine hlam.trans ?_
    have hcongr :
        (fun x => F (weakGrad (fun y => powShift β (1 / ((n : ℝ) + 1)) (v y)) x) ^ p)
          =ᵐ[volume] fun x =>
            deriv (powShift β (1 / ((n : ℝ) + 1))) (v x) ^ p * F (weakGrad v x) ^ p := by
      filter_upwards [hug] with x hx
      rw [hx, hF.homog, abs_of_nonneg (deriv_powShift_nonneg hβ0 hτ (hv.nonneg x)),
        Real.mul_rpow (deriv_powShift_nonneg hβ0 hτ (hv.nonneg x)) (hF.nonneg _)]
    rw [integral_congr_ae hcongr]
    have hptw : ∀ x, deriv (powShift β (1 / ((n : ℝ) + 1))) (v x) ^ p * F (weakGrad v x) ^ p ≤
        p * Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x) :=
      fun x => rpow_deriv_powShift_mul_le hp hβdef hF hτ (hv.nonneg x) _
    have hint : Integrable fun x =>
        deriv (powShift β (1 / ((n : ℝ) + 1))) (v x) ^ p * F (weakGrad v x) ^ p := by
      refine Integrable.mono' (hgi.const_mul p) ?_ (Eventually.of_forall fun x => ?_)
      · exact (hrc.comp_aestronglyMeasurable
          ((continuous_deriv_powShift hτ β).comp_aestronglyMeasurable hv2.1)).mul
          (hrc.comp_aestronglyMeasurable (hF.continuous.comp_aestronglyMeasurable
            hv.aestronglyMeasurable_weakGrad))
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (Real.rpow_nonneg (deriv_powShift_nonneg hβ0 hτ (hv.nonneg x)) _)
          (Real.rpow_nonneg (hF.nonneg _) _))]
        exact hptw x
    calc (∫ x, deriv (powShift β (1 / ((n : ℝ) + 1))) (v x) ^ p * F (weakGrad v x) ^ p)
        ≤ ∫ x, p * Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x) :=
          integral_mono hint (hgi.const_mul p) hptw
      _ = p * ∫ x, Korevaar.homogeneousDensity 2 (limitProfile p F) (v x) (weakGrad v x) := by
          rw [integral_const_mul]
      _ ≤ p * E := mul_le_mul_of_nonneg_left hgb hp0.le
  have hlim : Tendsto (fun n : ℕ => ∫ x, powShift β (1 / ((n : ℝ) + 1)) (v x) ^ p) atTop (𝓝 1) := by
    have hlim0 : Tendsto (fun n : ℕ => ∫ x, powShift β (1 / ((n : ℝ) + 1)) (v x) ^ p) atTop
        (𝓝 (∫ x, v x ^ 2)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => v x ^ 2) ?_ ?_ hi1 ?_
      · refine Eventually.of_forall fun n => ?_
        exact hrc.comp_aestronglyMeasurable
          ((contDiff_powShift (by positivity : (0:ℝ) < 1 / ((n : ℝ) + 1))
            β).continuous.comp_aestronglyMeasurable hv2.1)
      · refine Eventually.of_forall fun n => Eventually.of_forall fun x => ?_
        have hτ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (powShift_nonneg hβ0.le hτ _) _)]
        exact powShift_rpow_le_sq hp hβdef hτ (hv.nonneg x)
      · refine Eventually.of_forall fun x => ?_
        have h := (hrc.tendsto (v x ^ (2 * β))).comp (tendsto_powShift_rpow hβ0 (hv.nonneg x))
        have h3 : (v x ^ (2 * β)) ^ p = v x ^ 2 := by
          rw [← Real.rpow_mul (hv.nonneg x), h2βp, rpow_two_eq_sq]
        rw [h3] at h
        simpa only [Function.comp_def] using h
    rwa [hv.integral_sq] at hlim0
  have hfinal : lambdaSob p F K * 1 ≤ p * E :=
    le_of_tendsto (hlim.const_mul (lambdaSob p F K)) (Eventually.of_forall hkey)
  linarith [hfinal]

/-! ### The combination -/

/-- **From the truncated kinetic bounds to the eigenvalue.**  If a fixed admissible competitor
`v` has `∫ D_{Θ_R}(v, ∇v) ≤ E` for every truncation level `R > 0`, then
`λ_{p,F}(K)/p ≤ E`. -/
theorem lambdaGen_div_le_of_truncDensity_le {p : ℝ} (hp2 : 2 < p) {F : Euc d → ℝ}
    (hF : IsSmoothStrictNorm F) {K : Set (Euc d)} (hK : IsGoodConvex K) {v : Euc d → ℝ}
    (hv : IsRegAdmissible 2 K v) {E : ℝ}
    (hb : ∀ R : ℝ, 0 < R →
      (∫ x, Korevaar.homogeneousDensity 2 (truncDensity p F R) (v x) (weakGrad v x)) ≤ E) :
    lambdaGen p F K / p ≤ E := by
  have hp : 1 < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨hgi, hgb⟩ := integral_limitProfile_le hp hp2.le hF hv hb
  have h := lambdaSob_le_of_integral_limitProfile hp2 hF hv hgi hgb
  obtain ⟨CF, hCF⟩ := hF.exists_le_mul_norm
  have hlamEq : lambdaSob p F K = lambdaGen p F K :=
    lambdaSob_eq_lambdaGen hp hF.continuous hF.nonneg hCF hK
  rw [hlamEq] at h
  rw [div_le_iff₀ hp0]
  linarith [h]

end Komlos.Literature.Regularized
