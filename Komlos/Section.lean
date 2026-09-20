import Komlos.CommonDensity
import Komlos.EigenvalueLimit

/-!
# Prescribed sections (paper Lemma 3.4)

For a nonempty bounded open convex `B ⊆ ℝ^d × ℝ` symmetric under `(y,s) ↦ (y,−s)`, a
probability density `R` on `B` with horizontal variations `V_{(u,0)} R ≤ κ` for all unit
`u`, and `a ≥ 0` with `∫ |s| R ≥ a`: the section `D_a` is nonempty and admits an
admissible density with the same `κ`.

Paper proof: the sections are nested and Minkowski-convex in the height; by
`cheeger_anti` and `cheeger_minkowski`, `t ↦ h_H(D_t)` is nondecreasing and convex on
`[0,b)`.  Slicing (`lintegral_dirVar_slice_le`, via `dirVar_tendsto` + Fatou + Fubini)
gives `∫ q(s) h_H(D_{|s|}) ds ≤ ∑ α_ℓ ∫ V_{u_ℓ}(R_s) ds ≤ κ`; Jensen at the mean absolute
height `M ≥ a` and monotonicity give `h_H(D_a) ≤ κ` for every mixture; conclude with
`hasAdmissible_of_cheeger_le`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

variable {d : ℕ}

/-- Sections of a reflection-symmetric convex set are nested: `D_t ⊆ D_s` for `0 ≤ s ≤ t`. -/
theorem sectionAt_antitone {B : Set (Euc d × ℝ)} (hB : Convex ℝ B)
    (hsymm : ∀ p ∈ B, (p.1, -p.2) ∈ B) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    sectionAt B t ⊆ sectionAt B s := by
  intro y hy
  have hyt : (y, t) ∈ B := hy
  have hynt : (y, -t) ∈ B := hsymm _ hyt
  rcases eq_or_lt_of_le (hs.trans hst) with ht | ht
  · have hs0 : s = 0 := le_antisymm (hst.trans ht.symm.le) hs
    subst hs0
    subst ht
    exact hy
  · have hcomb := hB hyt hynt (a := (t + s) / (2 * t)) (b := (t - s) / (2 * t))
      (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith))
      (by field_simp; ring)
    show (y, s) ∈ B
    convert hcomb using 1
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, ← add_smul]
      rw [show (t + s) / (2 * t) + (t - s) / (2 * t) = 1 by field_simp; ring, one_smul]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      ring

/-- Sections of a convex set are Minkowski-convex in the height. -/
theorem smul_sectionAt_add_subset {B : Set (Euc d × ℝ)} (hB : Convex ℝ B) {s t θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) • sectionAt B s + θ • sectionAt B t ⊆ sectionAt B ((1 - θ) * s + θ * t) := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
  have hcomb := hB (x := (y, s)) (y := (z, t)) hy hz (a := 1 - θ) (b := θ) (by linarith) hθ₀
    (by ring)
  show ((1 - θ) • y + θ • z, (1 - θ) * s + θ * t) ∈ B
  convert hcomb using 1
  ext <;> simp

/-- Nonempty sections of a nonempty bounded open convex set are nonempty bounded open
convex. -/
theorem isGoodConvex_sectionAt {B : Set (Euc d × ℝ)} (hB : IsGoodConvex B) {t : ℝ}
    (hne : (sectionAt B t).Nonempty) : IsGoodConvex (sectionAt B t) where
  nonempty := hne
  isBounded := by
    obtain ⟨C, hC⟩ := hB.isBounded.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨C, fun y hy => ?_⟩
    exact (norm_fst_le (y, t)).trans (hC _ hy)
  isOpen := hB.isOpen.preimage (continuous_id.prodMk continuous_const)
  convex := by
    intro y hy z hz a b ha hb hab
    have hcomb := hB.convex (x := (y, t)) (y := (z, t)) hy hz ha hb hab
    show (a • y + b • z, t) ∈ B
    convert hcomb using 1
    ext
    · simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, ← add_mul, hab, one_mul]

/-- Slicing helper: the directional variation of the slices `R_s = R(·, s)` is, for a.e. `s`,
the `liminf` of a sequence of measurable difference quotients `Q n s`, each of which
integrates (in `s`) to at most `V_{(u,0)} R`. -/
theorem exists_sliceQuot (R : Euc d × ℝ → ℝ) (hR : Measurable R) (hint : Integrable R)
    (u : Euc d) :
    ∃ Q : ℕ → ℝ → ℝ≥0∞, (∀ n, Measurable (Q n)) ∧
      (∀ n, ∫⁻ s, Q n s ≤ dirVar ((u, (0 : ℝ)) : Euc d × ℝ) R) ∧
      ∀ᵐ s, dirVar u (fun y => R (y, s)) = liminf (fun n => Q n s) atTop := by
  set h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hh
  have hpos : ∀ n, 0 < h n := fun n => by simp only [hh]; positivity
  have hlim : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hpos⟩
  refine ⟨fun n s => (∫⁻ y, ‖R (y + h n • u, s) - R (y, s)‖ₑ) / ENNReal.ofReal (h n),
    fun n => ?_, fun n => ?_, ?_⟩
  · have hm : Measurable fun p : Euc d × ℝ => ‖R (p.1 + h n • u, p.2) - R p‖ₑ := by
      fun_prop
    exact (Measurable.lintegral_prod_left' hm).div_const _
  · have hm : Measurable fun p : Euc d × ℝ => ‖R (p + h n • (u, 0)) - R p‖ₑ := by fun_prop
    have : ∫⁻ s, (∫⁻ y, ‖R (y + h n • u, s) - R (y, s)‖ₑ) / ENNReal.ofReal (h n) =
        (∫⁻ p, ‖R (p + h n • (u, (0 : ℝ))) - R p‖ₑ) / ENNReal.ofReal (h n) := by
      simp only [div_eq_mul_inv]
      rw [lintegral_mul_const' _ _ (by simp [hpos n])]
      congr 1
      rw [Measure.volume_eq_prod, lintegral_prod_symm' _ hm]
      simp
    rw [this]
    exact le_iSup₂ (f := fun (h : ℝ) (_ : 0 < h) =>
      (∫⁻ x, ‖R (x + h • ((u, (0 : ℝ)) : Euc d × ℝ)) - R x‖ₑ) / ENNReal.ofReal h) (h n) (hpos n)
  · have hae : ∀ᵐ s : ℝ, Integrable (fun y => R (y, s)) := hint.prod_left_ae
    filter_upwards [hae] with s hs
    exact ((dirVar_tendsto u _ hs).comp hlim).liminf_eq.symm

/-- The slice variation `s ↦ V_u(R_s)` is a.e.-measurable. -/
theorem aemeasurable_dirVar_slice (R : Euc d × ℝ → ℝ) (hR : Measurable R)
    (hint : Integrable R) (u : Euc d) :
    AEMeasurable (fun s => dirVar u (fun y => R (y, s))) := by
  obtain ⟨Q, hQm, -, hQ⟩ := exists_sliceQuot R hR hint u
  exact (Measurable.liminf hQm).aemeasurable.congr (hQ.mono fun s hs => hs.symm)

/-- Paper (3.4) (horizontal slicing): `∫ V_u(R_s) ds ≤ V_{(u,0)} R`. -/
theorem lintegral_dirVar_slice_le (R : Euc d × ℝ → ℝ) (hR : Measurable R)
    (hint : Integrable R) (u : Euc d) :
    ∫⁻ s, dirVar u (fun y => R (y, s)) ≤ dirVar ((u, (0 : ℝ)) : Euc d × ℝ) R := by
  obtain ⟨Q, hQm, hQle, hQ⟩ := exists_sliceQuot R hR hint u
  calc ∫⁻ s, dirVar u (fun y => R (y, s)) = ∫⁻ s, liminf (fun n => Q n s) atTop :=
        lintegral_congr_ae hQ
    _ ≤ liminf (fun n => ∫⁻ s, Q n s) atTop := lintegral_liminf_le hQm
    _ ≤ liminf (fun _ : ℕ => dirVar ((u, (0 : ℝ)) : Euc d × ℝ) R) atTop :=
        liminf_le_liminf (Eventually.of_forall hQle)
    _ = _ := liminf_const _

/-- Paper Lemma 3.4 (prescribed sections). -/
theorem prescribed_section {B : Set (Euc d × ℝ)} (hB : IsGoodConvex B)
    (hsymm : ∀ p ∈ B, (p.1, -p.2) ∈ B) {κ : ℝ} (hκ : 0 ≤ κ) {R : Euc d × ℝ → ℝ}
    (hR : IsProbDensityOn B R)
    (hvar : ∀ u : Euc d, ‖u‖ = 1 → dirVar ((u, (0 : ℝ)) : Euc d × ℝ) R ≤ ENNReal.ofReal κ)
    {a : ℝ} (ha : 0 ≤ a) (hheight : a ≤ ∫ p, |p.2| * R p) :
    (sectionAt B a).Nonempty ∧ HasAdmissible (sectionAt B a) κ := by
  /- Step 0: reflection symmetry in the height. -/
  have hmemabs : ∀ (y : Euc d) (s : ℝ), (y, |s|) ∈ B ↔ (y, s) ∈ B := by
    intro y s
    rcases abs_choice s with h | h <;> rw [h]
    exact ⟨fun h' => by simpa using hsymm _ h', fun h' => hsymm _ h'⟩
  have hsec_abs : ∀ s : ℝ, sectionAt B |s| = sectionAt B s := fun s =>
    Set.ext fun y => hmemabs y s
  /- Step 1: the set `S = {t ≥ 0 : D_t ≠ ∅}` of admissible heights is convex and contains
  `0`. -/
  set S : Set ℝ := {t | 0 ≤ t ∧ (sectionAt B t).Nonempty} with hS
  have hS_conv : Convex ℝ S := by
    intro s hs t ht β γ hβ hγ hβγ
    refine ⟨add_nonneg (mul_nonneg hβ hs.1) (mul_nonneg hγ ht.1), ?_⟩
    obtain ⟨y, hy⟩ := hs.2
    obtain ⟨z, hz⟩ := ht.2
    have hβ' : β = 1 - γ := by linarith
    subst hβ'
    exact ⟨(1 - γ) • y + γ • z, smul_sectionAt_add_subset hB.convex hγ (by linarith)
      (Set.add_mem_add (Set.smul_mem_smul_set hy) (Set.smul_mem_smul_set hz))⟩
  have h0S : (0 : ℝ) ∈ S := by
    obtain ⟨p, hp⟩ := hB.nonempty
    refine ⟨le_rfl, p.1, sectionAt_antitone hB.convex hsymm le_rfl (abs_nonneg p.2) ?_⟩
    exact (hmemabs p.1 p.2).2 hp
  have hIcc : ∀ t ∈ S, Icc 0 t ⊆ S := fun t ht => hS_conv.ordConnected.out h0S ht
  /- Step 2: slices, the marginal `q`, and the mean absolute height `M`. -/
  have hRs_meas : ∀ s : ℝ, Measurable (fun y => R (y, s)) := fun s =>
    hR.measurable.comp measurable_prodMk_right
  set q : ℝ → ℝ := fun s => ∫ y, R (y, s) with hq
  have hq_nonneg : ∀ s, 0 ≤ q s := fun s => integral_nonneg fun y => hR.nonneg _
  have hq_meas : Measurable q :=
    (hR.measurable.stronglyMeasurable.integral_prod_left').measurable
  have hq_int : Integrable q := hR.integrable.integral_prod_right
  have hq_one : ∫ s, q s = 1 := by
    rw [← hR.integral_eq_one, Measure.volume_eq_prod, integral_prod_symm _ hR.integrable]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ p ∈ B, |p.2| ≤ C := by
    obtain ⟨C, hC⟩ := hB.isBounded.exists_norm_le
    exact ⟨C, fun p hp => (norm_snd_le p).trans (hC p hp)⟩
  have hM_int : Integrable (fun p : Euc d × ℝ => |p.2| * R p) := by
    refine (hR.integrable.const_mul C).mono' ?_ ?_
    · have := hR.measurable
      exact (by fun_prop : Measurable fun p : Euc d × ℝ => |p.2| * R p).aestronglyMeasurable
    · filter_upwards [hR.ae_zero_outside] with p hp
      by_cases hpB : p ∈ B
      · rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hR.nonneg p)]
        exact mul_le_mul_of_nonneg_right (hC p hpB) (hR.nonneg p)
      · simp [hp hpB]
  set M : ℝ := ∫ p, |p.2| * R p with hM
  have hMq_int : Integrable (fun s : ℝ => |s| * q s) := by
    have := hM_int.integral_prod_right
    simpa [integral_const_mul] using this
  have hM_eq : M = ∫ s, |s| * q s := by
    rw [hM, Measure.volume_eq_prod, integral_prod_symm _ hM_int]
    simp [integral_const_mul, hq]
  have hMa : a ≤ M := hheight
  /- Step 3: a.e. properties of the slices `R_s`. -/
  have hslice_supp : ∀ᵐ s : ℝ, ∀ᵐ y : Euc d, (y, s) ∉ B → R (y, s) = 0 := by
    have h1 := hR.ae_zero_outside
    rw [Measure.volume_eq_prod] at h1
    have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Euc d)))).quasiMeasurePreserving.ae h1
    exact Measure.ae_ae_of_ae_prod h2
  have hslice_int : ∀ᵐ s : ℝ, Integrable (fun y => R (y, s)) := hR.integrable.prod_left_ae
  have hslice_var : ∀ᵐ s : ℝ, ∀ i : Fin d,
      dirVar (EuclideanSpace.single i 1) (fun y => R (y, s)) < ⊤ := by
    rw [ae_all_iff]
    intro i
    refine ae_lt_top' (aemeasurable_dirVar_slice R hR.measurable hR.integrable _) ?_
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := κ)) ?_
    exact (lintegral_dirVar_slice_le R hR.measurable hR.integrable _).trans (hvar _ (by simp))
  /- Step 4: `q(s) > 0` forces `D_{|s|} ≠ ∅`. -/
  have hqS : ∀ᵐ s : ℝ, 0 < q s → |s| ∈ S := by
    filter_upwards [hslice_supp] with s hs hqs
    refine ⟨abs_nonneg s, ?_⟩
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, hsec_abs] at hemp
    have : q s = 0 := by
      simp only [hq]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hs] with y hy
      exact hy fun h => Set.eq_empty_iff_forall_notMem.1 hemp y h
    exact hqs.ne' this
  /- Step 5: a null-set argument used twice: if `f ≥ 0` on `{q > 0}`, `f ≠ 0` a.e. and
  `∫ f q = 0`, then `q = 0` a.e., contradicting `∫ q = 1`. -/
  have hcontra : ∀ f : ℝ → ℝ, (∀ᵐ s, 0 < q s → 0 ≤ f s) → (∀ᵐ s, f s ≠ 0) →
      Integrable (fun s => f s * q s) → ∫ s, f s * q s = 0 → False := by
    intro f hf hf0 hfi hint0
    have hnn : 0 ≤ᵐ[volume] fun s => f s * q s := by
      filter_upwards [hf] with s hs
      rcases (hq_nonneg s).lt_or_eq with h | h
      · exact mul_nonneg (hs h) (hq_nonneg s)
      · simp [← h]
    have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hfi).1 hint0
    have hq0 : q =ᵐ[volume] 0 := by
      filter_upwards [h0, hf0] with s hs hs0
      simp only [Pi.zero_apply] at hs ⊢
      rcases mul_eq_zero.1 hs with h | h
      · exact absurd h hs0
      · exact h
    have : ∫ s, q s = 0 := integral_eq_zero_of_ae hq0
    linarith [hq_one]
  have hM_nonneg : 0 ≤ M := hM_eq ▸ integral_nonneg fun s => mul_nonneg (abs_nonneg s) (hq_nonneg s)
  have hM_pos : 0 < M := by
    rcases hM_nonneg.lt_or_eq with h | h
    · exact h
    · exfalso
      have hint0 : ∫ s, |s| * q s = 0 := by rw [← hM_eq, ← h]
      refine hcontra (fun s => |s|) (Eventually.of_forall fun s _ => abs_nonneg s) ?_ hMq_int hint0
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with s hs
      exact abs_ne_zero.2 hs
  have hM_lt : ∃ t₀ ∈ S, M < t₀ := by
    by_contra hcon
    push Not at hcon
    have hL_int : Integrable (fun s => (M - |s|) * q s) := by
      refine ((hq_int.const_mul M).sub hMq_int).congr (Eventually.of_forall fun s => ?_)
      simp only [Pi.sub_apply]
      ring
    have hL0 : ∫ s, (M - |s|) * q s = 0 := by
      have : (fun s => (M - |s|) * q s) = fun s => M * q s - |s| * q s := funext fun s => by ring
      rw [this, integral_sub (hq_int.const_mul M) hMq_int, integral_const_mul, hq_one, ← hM_eq]
      ring
    refine hcontra (fun s => M - |s|) ?_ ?_ hL_int hL0
    · filter_upwards [hqS] with s hs hqs
      exact sub_nonneg.2 (hcon _ (hs hqs))
    · have hcount : ({M, -M} : Set ℝ).Countable := ((Set.finite_singleton (-M)).insert M).countable
      filter_upwards [hcount.ae_notMem volume] with s hs
      intro h
      apply hs
      rcases (abs_eq hM_nonneg).1 (by linarith : |s| = M) with h' | h' <;> simp [h']
  obtain ⟨t₀, ht₀S, hMt₀⟩ := hM_lt
  have hM_int' : M ∈ interior S :=
    interior_mono (hIcc t₀ ht₀S) (by rw [interior_Icc]; exact ⟨hM_pos, hMt₀⟩)
  have hMS : M ∈ S := interior_subset hM_int'
  have haS : a ∈ S := hIcc M hMS ⟨ha, hMa⟩
  refine ⟨haS.2, hasAdmissible_of_cheeger_le (isGoodConvex_sectionAt hB haS.2) hκ ?_⟩
  /- Step 6: fix a mixture; `g(t) = h_H(D_t)` is finite, nondecreasing and convex on `S`. -/
  intro N α w hmix
  set G : ℝ → ℝ≥0∞ := fun t => cheeger α w (sectionAt B t) with hG
  have hG_mono : ∀ s t, 0 ≤ s → s ≤ t → G s ≤ G t := fun s t hs hst =>
    cheeger_anti (sectionAt_antitone hB.convex hsymm hs hst)
  have hG_fin : ∀ t ∈ S, G t ≠ ⊤ := fun t ht =>
    (cheeger_lt_top hmix (isGoodConvex_sectionAt hB ht.2).isOpen ht.2).ne
  have hG_meas : Measurable fun s : ℝ => G |s| := by
    have hmono : Monotone fun t : ℝ => G (max t 0) := fun s t hst =>
      hG_mono _ _ (le_max_right _ _) (max_le_max_right 0 hst)
    have : (fun s : ℝ => G |s|) = (fun t : ℝ => G (max t 0)) ∘ abs := by
      funext s; simp
    rw [this]
    exact hmono.measurable.comp continuous_abs.measurable
  set g : ℝ → ℝ := fun t => (G t).toReal with hg
  have hg_conv : ConvexOn ℝ S g := by
    refine ⟨hS_conv, fun s hs t ht β γ hβ hγ hβγ => ?_⟩
    have hβ' : β = 1 - γ := by linarith
    subst hβ'
    have h1 : G ((1 - γ) * s + γ * t) ≤ ENNReal.ofReal (1 - γ) * G s + ENNReal.ofReal γ * G t :=
      (cheeger_anti (smul_sectionAt_add_subset hB.convex hγ (by linarith))).trans
        (cheeger_minkowski hmix (isGoodConvex_sectionAt hB hs.2) (isGoodConvex_sectionAt hB ht.2)
          hγ (by linarith))
    have hs' := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 1 - γ)) (hG_fin s hs)
    have ht' := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := γ)) (hG_fin t ht)
    simp only [smul_eq_mul, hg]
    calc (G ((1 - γ) * s + γ * t)).toReal
        ≤ (ENNReal.ofReal (1 - γ) * G s + ENNReal.ofReal γ * G t).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hs', ht'⟩) h1
      _ = (1 - γ) * (G s).toReal + γ * (G t).toReal := by
          rw [ENNReal.toReal_add hs' ht', ENNReal.toReal_mul, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal hβ, ENNReal.toReal_ofReal hγ]
  /- Step 7: a supporting line of `g` at the interior point `M`. -/
  set k : ℝ := derivWithin g (Ioi M) M with hk
  have hline : ∀ t ∈ S, g M + k * (t - M) ≤ g t := by
    intro t ht
    rcases lt_trichotomy t M with h | h | h
    · have h1 := hg_conv.slope_le_leftDeriv_of_mem_interior ht hM_int' h
      have h2 := hg_conv.leftDeriv_le_rightDeriv_of_mem_interior hM_int'
      rw [slope_def_field] at h1
      have h3 := h1.trans h2
      rw [div_le_iff₀ (by linarith)] at h3
      linarith [show k * (t - M) = -(k * (M - t)) by ring]
    · subst h; simp
    · have h1 := hg_conv.rightDeriv_le_slope_of_mem_interior hM_int' ht h
      rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
      linarith
  /- Step 8: the weighted energy bound `q(s) h_H(D_{|s|}) ≤ E_H(R_s)` a.e. -/
  have hkey : ∀ᵐ s : ℝ,
      ENNReal.ofReal (q s) * G |s| ≤ mixtureEnergy α w (fun y => R (y, s)) := by
    filter_upwards [hslice_supp, hslice_int, hslice_var] with s hs_supp hs_int hs_var
    rcases (hq_nonneg s).lt_or_eq with hqs | hqs
    · set ρ : Euc d → ℝ := (q s)⁻¹ • fun y => R (y, s) with hρ
      have hRs_fin : ∀ v : Euc d, dirVar v (fun y => R (y, s)) ≠ ⊤ := by
        intro v
        refine ne_top_of_le_ne_top ?_ (dirVar_le_sum_coord _ (hRs_meas s) v)
        exact (ENNReal.sum_lt_top.2 fun i _ =>
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hs_var i)).ne
      have hρP : MemP (sectionAt B |s|) ρ :=
        { measurable := (hRs_meas s).const_smul _
          nonneg := fun y => by
            simp only [hρ, Pi.smul_apply, smul_eq_mul]
            exact mul_nonneg (inv_nonneg.2 (hq_nonneg s)) (hR.nonneg _)
          integrable := hs_int.smul _
          integral_eq_one := by
            simp only [hρ, Pi.smul_apply]
            rw [integral_smul, smul_eq_mul]
            exact inv_mul_cancel₀ hqs.ne'
          ae_zero_outside := by
            filter_upwards [hs_supp] with y hy hyD
            simp only [hρ, Pi.smul_apply, smul_eq_mul]
            rw [hy fun h => hyD ((hmemabs y s).2 h), mul_zero]
          dirVar_ne_top := fun v => by
            rw [hρ, dirVar_const_smul_fun]
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hRs_fin v) }
      have h1 : G |s| ≤ mixtureEnergy α w ρ := cheeger_le_mixtureEnergy hρP
      have h2 : mixtureEnergy α w ρ =
          ENNReal.ofReal (q s)⁻¹ * mixtureEnergy α w (fun y => R (y, s)) := by
        simp only [mixtureEnergy, hρ, dirVar_const_smul_fun, Finset.mul_sum,
          abs_of_pos (inv_pos.2 hqs)]
        exact Finset.sum_congr rfl fun l _ => by ring
      calc ENNReal.ofReal (q s) * G |s|
          ≤ ENNReal.ofReal (q s) *
              (ENNReal.ofReal (q s)⁻¹ * mixtureEnergy α w (fun y => R (y, s))) := by
            rw [← h2]; gcongr
        _ = _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (hq_nonneg s), mul_inv_cancel₀ hqs.ne',
              ENNReal.ofReal_one, one_mul]
    · simp [← hqs]
  /- Step 9: integrate, using the slicing inequality (3.4). -/
  have hlint : ∫⁻ s, ENNReal.ofReal (q s) * G |s| ≤ ENNReal.ofReal κ := by
    calc ∫⁻ s, ENNReal.ofReal (q s) * G |s|
        ≤ ∫⁻ s, mixtureEnergy α w (fun y => R (y, s)) := lintegral_mono_ae hkey
      _ = ∑ l, ENNReal.ofReal (α l) * ∫⁻ s, dirVar (w l) (fun y => R (y, s)) := by
          simp only [mixtureEnergy]
          rw [lintegral_finsetSum' _ fun l _ =>
            (aemeasurable_dirVar_slice R hR.measurable hR.integrable _).const_mul _]
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∑ l, ENNReal.ofReal (α l) * ENNReal.ofReal κ := by
          refine Finset.sum_le_sum fun l _ => ?_
          gcongr
          exact (lintegral_dirVar_slice_le R hR.measurable hR.integrable _).trans
            (hvar _ (hmix.norm_eq_one l))
      _ = ENNReal.ofReal κ := by
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun l _ => hmix.nonneg l,
            hmix.sum_eq_one, ENNReal.ofReal_one, one_mul]
  /- Step 10: the real-valued integrand `F(s) = q(s) g(|s|)` is integrable with `∫ F ≤ κ`. -/
  set F : ℝ → ℝ := fun s => q s * g |s| with hF
  have hF_nonneg : ∀ s, 0 ≤ F s := fun s => mul_nonneg (hq_nonneg s) ENNReal.toReal_nonneg
  have hF_meas : Measurable F := hq_meas.mul hG_meas.ennreal_toReal
  have hF_lint : ∫⁻ s, ENNReal.ofReal (F s) ≤ ENNReal.ofReal κ := by
    refine (lintegral_mono fun s => ?_).trans hlint
    simp only [hF, hg]
    rw [ENNReal.ofReal_mul (hq_nonneg s)]
    gcongr
    exact ENNReal.ofReal_toReal_le
  have hF_int : Integrable F :=
    ⟨hF_meas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF_nonneg)).2
      (hF_lint.trans_lt ENNReal.ofReal_lt_top)⟩
  have hF_le : ∫ s, F s ≤ κ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF_nonneg)
      hF_meas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hκ hF_lint
  /- Step 11: Jensen via the supporting line, then monotonicity. -/
  have hJ : g M ≤ ∫ s, F s := by
    have hL_int : Integrable (fun s => (g M - k * M) * q s + k * (|s| * q s)) :=
      (hq_int.const_mul _).add (hMq_int.const_mul _)
    have hL_eq : ∫ s, ((g M - k * M) * q s + k * (|s| * q s)) = g M := by
      rw [integral_add (hq_int.const_mul _) (hMq_int.const_mul _), integral_const_mul,
        integral_const_mul, hq_one, ← hM_eq]
      ring
    rw [← hL_eq]
    refine integral_mono_ae hL_int hF_int ?_
    filter_upwards [hqS] with s hs
    simp only [hF]
    rcases (hq_nonneg s).lt_or_eq with hqs | hqs
    · have : (g M - k * M) * q s + k * (|s| * q s) = q s * (g M + k * (|s| - M)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (hline _ (hs hqs)) (hq_nonneg s)
    · rw [← hqs]; simp
  have hgM : g M ≤ κ := hJ.trans hF_le
  have hga : g a ≤ g M := ENNReal.toReal_mono (hG_fin M hMS) (hG_mono a M ha hMa)
  calc cheeger α w (sectionAt B a) = ENNReal.ofReal (g a) :=
        (ENNReal.ofReal_toReal (hG_fin a haS)).symm
    _ ≤ ENNReal.ofReal κ := ENNReal.ofReal_le_ofReal (hga.trans hgM)

end Komlos
