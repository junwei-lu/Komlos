import Komlos.Cheeger
import Komlos.Compactness

/-!
# A common density (paper Lemma 3.3)

If `h_H(K) ≤ κ` for every mixture `H`, then some `ρ ∈ 𝒫(K)` satisfies the cap (2.8).

Paper proof: (1) for a finite list of unit directions containing the coordinate basis,
convex separation (`geometric_hahn_banach_open`) between the upward-closed convex set
`S = {z : ∃ ρ ∈ 𝒫(K), z_ℓ ≥ V_{u_ℓ} ρ}` and the open orthant `(−∞, a)^N` shows
`inf_ρ max_ℓ V_{u_ℓ} ρ ≤ κ`; (2) compactness (`exists_subseq_tendsto_L1`) and lower
semicontinuity (`dirVar_le_liminf`) give attainment; (3) a countable dense set of
directions, another compactness step, and `dirVar_le_dirVar_add` extend the bound to all
directions.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace Komlos

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]

/-- `V_0 f = 0`: translating by `0` does nothing. -/
theorem dirVar_zero (f : E → ℝ) : dirVar (0 : E) f = 0 := by
  simp [dirVar]

variable [BorelSpace E] [SecondCountableTopology E] [(volume : Measure E).IsAddHaarMeasure]

/-- Convexity of `V_u` in the function (paper Lemma 3.1):
`V_u (p ρ₁ + q ρ₂) ≤ p V_u ρ₁ + q V_u ρ₂` for `p, q ≥ 0`. -/
theorem dirVar_convexComb_le (v : E) (ρ₁ ρ₂ : E → ℝ) (hρ₁ : Measurable ρ₁) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    dirVar v (p • ρ₁ + q • ρ₂) ≤
      ENNReal.ofReal p * dirVar v ρ₁ + ENNReal.ofReal q * dirVar v ρ₂ := by
  calc dirVar v (p • ρ₁ + q • ρ₂) ≤ dirVar v (p • ρ₁) + dirVar v (q • ρ₂) :=
        dirVar_add_fun_le v _ _ (hρ₁.const_smul p)
    _ = ENNReal.ofReal p * dirVar v ρ₁ + ENNReal.ofReal q * dirVar v ρ₂ := by
        rw [dirVar_const_smul_fun, dirVar_const_smul_fun, abs_of_nonneg hp, abs_of_nonneg hq]

/-- `𝒫(K)` is convex (paper Lemma 3.3: "`S` is convex"). -/
theorem memP_convexComb {K : Set E} {ρ₁ ρ₂ : E → ℝ} (h₁ : MemP K ρ₁) (h₂ : MemP K ρ₂)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) : MemP K (p • ρ₁ + q • ρ₂) where
  measurable := (h₁.measurable.const_smul p).add (h₂.measurable.const_smul q)
  nonneg := fun x => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hp (h₁.nonneg x)) (mul_nonneg hq (h₂.nonneg x))
  integrable := (h₁.integrable.smul p).add (h₂.integrable.smul q)
  integral_eq_one := by
    show ∫ x, (p • ρ₁) x + (q • ρ₂) x = 1
    rw [integral_add (h₁.integrable.smul p) (h₂.integrable.smul q)]
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_smul, h₁.integral_eq_one, h₂.integral_eq_one]
    simpa using hpq
  ae_zero_outside := by
    filter_upwards [h₁.ae_zero_outside, h₂.ae_zero_outside] with x hx₁ hx₂ hx
    simp [hx₁ hx, hx₂ hx]
  dirVar_ne_top := fun v =>
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h₁.dirVar_ne_top v),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h₂.dirVar_ne_top v)⟩)
      (dirVar_convexComb_le v ρ₁ ρ₂ h₁.measurable hp hq)

end General

variable {d : ℕ}

/-- A probability density with bounded coordinate variations lies in `𝒫(K)`
(paper Lemma 3.3: "the coordinate bounds also give `ρ ∈ BV(ℝ^d)`"). -/
theorem memP_of_coord_le {K : Set (Euc d)} {ρ : Euc d → ℝ} (hρ : IsProbDensityOn K ρ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hvar : ∀ i, dirVar (EuclideanSpace.single i 1) ρ ≤ M) :
    MemP K ρ :=
  { hρ with
    dirVar_ne_top := fun v => by
      refine ne_top_of_le_ne_top ?_ (dirVar_le_sum_coord ρ hρ.measurable v)
      exact (ENNReal.sum_lt_top.2 fun i _ =>
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((hvar i).trans_lt hM.lt_top)).ne }

/-- The set `S` of paper Lemma 3.3 is convex. -/
theorem convex_setOf_memP_le {K : Set (Euc d)} {N : ℕ} (u : Fin N → Euc d) :
    Convex ℝ {z : Fin N → ℝ | ∃ ρ, MemP K ρ ∧ ∀ l, (dirVar (u l) ρ).toReal ≤ z l} := by
  rintro z₁ ⟨ρ₁, hρ₁, hz₁⟩ z₂ ⟨ρ₂, hρ₂, hz₂⟩ p q hp hq hpq
  refine ⟨p • ρ₁ + q • ρ₂, memP_convexComb hρ₁ hρ₂ hp hq hpq, fun l => ?_⟩
  have h₁ : ENNReal.ofReal p * dirVar (u l) ρ₁ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hρ₁.dirVar_ne_top _)
  have h₂ : ENNReal.ofReal q * dirVar (u l) ρ₂ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hρ₂.dirVar_ne_top _)
  calc (dirVar (u l) (p • ρ₁ + q • ρ₂)).toReal
      ≤ (ENNReal.ofReal p * dirVar (u l) ρ₁ + ENNReal.ofReal q * dirVar (u l) ρ₂).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h₁, h₂⟩)
          (dirVar_convexComb_le (u l) ρ₁ ρ₂ hρ₁.measurable hp hq)
    _ = p * (dirVar (u l) ρ₁).toReal + q * (dirVar (u l) ρ₂).toReal := by
        rw [ENNReal.toReal_add h₁ h₂, ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]
    _ ≤ p * z₁ l + q * z₂ l := by gcongr <;> [exact hz₁ l; exact hz₂ l]
    _ = (p • z₁ + q • z₂) l := by simp

/-- Step (1) of paper Lemma 3.3 (separation): if every weighted infimum is `≤ κ`, then for
every `a > κ` some `ρ ∈ 𝒫(K)` has all the listed variations `≤ a`. -/
theorem exists_memP_le_of_cheeger_le {K : Set (Euc d)} (hK : IsGoodConvex K) {κ : ℝ}
    (hκ : 0 ≤ κ) {N : ℕ} (u : Fin N → Euc d) (hu : ∀ l, ‖u l‖ = 1)
    (h : ∀ α : Fin N → ℝ, IsMixture α u → cheeger α u K ≤ ENNReal.ofReal κ)
    {a : ℝ} (ha : κ < a) :
    ∃ ρ, MemP K ρ ∧ ∀ l, dirVar (u l) ρ ≤ ENNReal.ofReal a := by
  have ha0 : 0 ≤ a := hκ.trans ha.le
  by_contra hcon
  push Not at hcon
  obtain ⟨ρ₀, hρ₀⟩ := exists_memP_of_isOpen hK.isOpen hK.nonempty
  -- the open orthant `Q = (-∞, a)^N` and the convex set `S`
  have hQc : Convex ℝ (Set.pi univ fun _ : Fin N => Iio a) := convex_pi fun _ _ => convex_Iio a
  have hQo : IsOpen (Set.pi univ fun _ : Fin N => Iio a) :=
    isOpen_set_pi finite_univ fun _ _ => isOpen_Iio
  have hdisj : Disjoint (Set.pi univ fun _ : Fin N => Iio a)
      {z : Fin N → ℝ | ∃ ρ, MemP K ρ ∧ ∀ l, (dirVar (u l) ρ).toReal ≤ z l} := by
    rw [Set.disjoint_left]
    rintro z hzQ ⟨ρ, hρ, hz⟩
    obtain ⟨l, hl⟩ := hcon ρ hρ
    have hzl : z l < a := Set.mem_univ_pi.1 hzQ l
    exact hl.not_ge ((ENNReal.le_ofReal_iff_toReal_le (hρ.dirVar_ne_top _) ha0).2
      ((hz l).trans hzl.le))
  obtain ⟨f, s₀, hfQ, hfS⟩ := geometric_hahn_banach_open hQc hQo (convex_setOf_memP_le u) hdisj
  -- the coordinates of `f`
  obtain ⟨e, he⟩ : ∃ e : Fin N → Fin N → ℝ, e = fun i j => if i = j then 1 else 0 := ⟨_, rfl⟩
  have hf_eq : ∀ x, f x = ∑ i, x i * f (e i) := fun x => by
    conv_lhs => rw [pi_eq_sum_univ x, map_sum]
    simp_rw [map_smul, smul_eq_mul, he]
  have hz₀S : (fun l => (dirVar (u l) ρ₀).toReal) ∈
      {z : Fin N → ℝ | ∃ ρ, MemP K ρ ∧ ∀ l, (dirVar (u l) ρ).toReal ≤ z l} :=
    ⟨ρ₀, hρ₀, fun l => le_rfl⟩
  -- `S` is upward closed
  have hup : ∀ l (τ : ℝ), 0 ≤ τ → (fun l => (dirVar (u l) ρ₀).toReal) + τ • e l ∈
      {z : Fin N → ℝ | ∃ ρ, MemP K ρ ∧ ∀ l, (dirVar (u l) ρ).toReal ≤ z l} := by
    intro l τ hτ
    refine ⟨ρ₀, hρ₀, fun j => ?_⟩
    simp only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : 0 ≤ τ * (if l = j then (1 : ℝ) else 0) := by split_ifs <;> simp [hτ]
    linarith
  -- hence the coefficients of `f` are nonnegative
  have hb_nonneg : ∀ l, 0 ≤ f (e l) := by
    intro l
    by_contra hneg
    push Not at hneg
    have hs := hfS _ hz₀S
    have hτ0 : 0 ≤ (f (fun l => (dirVar (u l) ρ₀).toReal) - s₀ + 1) / (-f (e l)) :=
      div_nonneg (by linarith) (by linarith)
    have hτmul : ((f fun l => (dirVar (u l) ρ₀).toReal) - s₀ + 1) / (-f (e l)) * f (e l) =
        -((f fun l => (dirVar (u l) ρ₀).toReal) - s₀ + 1) := by
      rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hneg.ne, mul_one]
    have := hfS _ (hup l _ hτ0)
    rw [map_add, map_smul, smul_eq_mul, hτmul] at this
    linarith
  -- and their sum is positive
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ l, f (e l) := ⟨_, rfl⟩
  have hB_nonneg : 0 ≤ B := hB ▸ Finset.sum_nonneg fun l _ => hb_nonneg l
  have hf_const : ∀ c : ℝ, f (fun _ => c) = c * B := fun c => by
    rw [hf_eq, hB, Finset.mul_sum]
  have hB_pos : 0 < B := by
    rcases hB_nonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hall : ∀ l, f (e l) = 0 := fun l =>
        (Finset.sum_eq_zero_iff_of_nonneg fun l _ => hb_nonneg l).1 (hB.symm.trans heq.symm) l
          (Finset.mem_univ _)
      have hf0 : ∀ x, f x = 0 := fun x => by rw [hf_eq]; simp [hall]
      have hq : (fun _ => a - 1 : Fin N → ℝ) ∈ Set.pi univ fun _ : Fin N => Iio a :=
        Set.mem_univ_pi.2 fun _ => by simp
      have h1 := hfQ _ hq
      have h2 := hfS _ hz₀S
      rw [hf0] at h1 h2
      linarith
  -- the supremum over `Q` is `a B`
  have haB : a * B ≤ s₀ := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hq : (fun _ => a - ε / B : Fin N → ℝ) ∈ Set.pi univ fun _ : Fin N => Iio a :=
      Set.mem_univ_pi.2 fun _ => by simp [div_pos hε hB_pos]
    have h1 := hfQ _ hq
    rw [hf_const, sub_mul, div_mul_cancel₀ _ hB_pos.ne'] at h1
    linarith
  -- the normalised weights form a mixture with energy `≥ a` on `𝒫(K)`
  have hmix : IsMixture (fun l => f (e l) / B) u :=
    ⟨fun l => div_nonneg (hb_nonneg l) hB_nonneg,
      by rw [← Finset.sum_div, ← hB, div_self hB_pos.ne'], hu⟩
  have hE : ∀ ρ, MemP K ρ → ENNReal.ofReal a ≤ mixtureEnergy (fun l => f (e l) / B) u ρ := by
    intro ρ hρ
    have h1 := hfS _ (⟨ρ, hρ, fun l => le_rfl⟩ :
      (fun l => (dirVar (u l) ρ).toReal) ∈
        {z : Fin N → ℝ | ∃ ρ, MemP K ρ ∧ ∀ l, (dirVar (u l) ρ).toReal ≤ z l})
    rw [hf_eq] at h1
    have h2 : a ≤ ∑ l, f (e l) / B * (dirVar (u l) ρ).toReal := by
      have : ∑ l, f (e l) / B * (dirVar (u l) ρ).toReal =
          (∑ i, (dirVar (u i) ρ).toReal * f (e i)) / B := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [this, le_div_iff₀ hB_pos]
      linarith
    calc ENNReal.ofReal a ≤ ENNReal.ofReal (∑ l, f (e l) / B * (dirVar (u l) ρ).toReal) :=
          ENNReal.ofReal_le_ofReal h2
      _ = ∑ l, ENNReal.ofReal (f (e l) / B) * dirVar (u l) ρ := by
          rw [ENNReal.ofReal_sum_of_nonneg fun l _ =>
            mul_nonneg (hmix.nonneg l) ENNReal.toReal_nonneg]
          exact Finset.sum_congr rfl fun l _ => by
            rw [ENNReal.ofReal_mul (hmix.nonneg l), ENNReal.ofReal_toReal (hρ.dirVar_ne_top _)]
  have hle : ENNReal.ofReal a ≤ cheeger (fun l => f (e l) / B) u K :=
    le_iInf fun ρ => le_iInf fun hρ => hE ρ hρ
  have := hle.trans (h _ hmix)
  rw [ENNReal.ofReal_le_ofReal_iff hκ] at this
  exact absurd this (not_le.2 ha)

/-- Step (1)+(2) of paper Lemma 3.3: for finitely many unit directions containing the
coordinate basis, if every weighted infimum is `≤ κ` then the finite maximum is attained
at level `≤ κ` by some `ρ ∈ 𝒫(K)`. -/
theorem exists_memP_finite_directions {K : Set (Euc d)} (hK : IsGoodConvex K) {κ : ℝ}
    (hκ : 0 ≤ κ) {N : ℕ} (u : Fin N → Euc d) (hu : ∀ l, ‖u l‖ = 1)
    (hbasis : ∀ i : Fin d, ∃ l, u l = EuclideanSpace.single i 1)
    (h : ∀ α : Fin N → ℝ, IsMixture α u → cheeger α u K ≤ ENNReal.ofReal κ) :
    ∃ ρ, MemP K ρ ∧ ∀ l, dirVar (u l) ρ ≤ ENNReal.ofReal κ := by
  -- a minimising sequence
  have hstep : ∀ n : ℕ, ∃ ρ, MemP K ρ ∧
      ∀ l, dirVar (u l) ρ ≤ ENNReal.ofReal (κ + 1 / ((n : ℝ) + 1)) := fun n =>
    exists_memP_le_of_cheeger_le hK hκ u hu h (lt_add_of_pos_right κ (by positivity))
  choose ρ hρ hρvar using hstep
  have hvar : ∀ n i, dirVar (EuclideanSpace.single i 1) (ρ n) ≤ ENNReal.ofReal (κ + 1) := by
    intro n i
    obtain ⟨l, hl⟩ := hbasis i
    rw [← hl]
    refine (hρvar n l).trans (ENNReal.ofReal_le_ofReal ?_)
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  -- compactness
  obtain ⟨φ, ρ', hφ, hρ', hlim⟩ := exists_subseq_tendsto_L1 hK.isBounded ENNReal.ofReal_ne_top ρ
    (fun n => (hρ n).toIsProbDensityOn) hvar
  -- lower semicontinuity
  have hρ'var : ∀ l, dirVar (u l) ρ' ≤ ENNReal.ofReal κ := by
    intro l
    refine (dirVar_le_liminf (u l) (fun k => ρ (φ k)) ρ' (fun k => (hρ (φ k)).measurable)
      hρ'.measurable hlim).trans ?_
    calc liminf (fun k => dirVar (u l) (ρ (φ k))) atTop
        ≤ liminf (fun k : ℕ => ENNReal.ofReal (κ + 1 / ((k : ℝ) + 1))) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
          refine (hρvar (φ k) l).trans (ENNReal.ofReal_le_ofReal ?_)
          have hk : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.le_apply
          gcongr
      _ = ENNReal.ofReal κ := by
          refine Tendsto.liminf_eq (ENNReal.tendsto_ofReal ?_)
          simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨ρ', memP_of_coord_le hρ' (M := ENNReal.ofReal κ) ENNReal.ofReal_ne_top fun i => ?_,
    hρ'var⟩
  obtain ⟨l, hl⟩ := hbasis i
  rw [← hl]
  exact hρ'var l

/-- Step (3) of paper Lemma 3.3 (countable dense directions and compactness): some
`ρ ∈ 𝒫(K)` has `V_u ρ ≤ κ` for every unit direction `u`. -/
theorem exists_memP_unit_directions {K : Set (Euc d)} (hK : IsGoodConvex K) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (h : ∀ (N : ℕ) (α : Fin N → ℝ) (u : Fin N → Euc d), IsMixture α u →
      cheeger α u K ≤ ENNReal.ofReal κ) :
    ∃ ρ, MemP K ρ ∧ ∀ v : Euc d, ‖v‖ = 1 → dirVar v ρ ≤ ENNReal.ofReal κ := by
  by_cases hex : ∃ u₀ : Euc d, ‖u₀‖ = 1
  swap
  · push Not at hex
    obtain ⟨ρ, hρ⟩ := exists_memP_of_isOpen hK.isOpen hK.nonempty
    exact ⟨ρ, hρ, fun v hv => absurd hv (hex v)⟩
  obtain ⟨u₀, hu₀⟩ := hex
  -- a countable dense set of unit directions
  have : Nonempty (Metric.sphere (0 : Euc d) 1) :=
    ⟨⟨u₀, by simpa [mem_sphere_zero_iff_norm] using hu₀⟩⟩
  obtain ⟨w, hw⟩ := TopologicalSpace.exists_dense_seq (Metric.sphere (0 : Euc d) 1)
  have hwn : ∀ k, ‖(w k : Euc d)‖ = 1 := fun k => mem_sphere_zero_iff_norm.1 (w k).2
  -- the finite lists: the coordinate basis followed by `w 0, …, w n`
  obtain ⟨U, hU1, hU2⟩ : ∃ U : ∀ n : ℕ, Fin (d + (n + 1)) → Euc d,
      (∀ n (i : Fin d), U n (Fin.castAdd (n + 1) i) = EuclideanSpace.single i 1) ∧
      (∀ n (k : Fin (n + 1)), U n (Fin.natAdd d k) = w k) :=
    ⟨fun n => Fin.append (fun i => EuclideanSpace.single i (1 : ℝ))
        (fun k : Fin (n + 1) => (w k : Euc d)),
      fun n i => Fin.append_left _ _ i, fun n k => Fin.append_right _ _ k⟩
  have hU : ∀ n l, ‖U n l‖ = 1 := fun n l => by
    refine Fin.addCases (fun i => ?_) (fun k => ?_) l
    · rw [hU1]; simp [PiLp.norm_single]
    · rw [hU2]; exact hwn k
  have hUb : ∀ n (i : Fin d), ∃ l, U n l = EuclideanSpace.single i 1 :=
    fun n i => ⟨Fin.castAdd _ i, hU1 n i⟩
  have hstep : ∀ n, ∃ ρ, MemP K ρ ∧ ∀ l, dirVar (U n l) ρ ≤ ENNReal.ofReal κ := fun n =>
    exists_memP_finite_directions hK hκ (U n) (hU n) (hUb n) fun α hα => h _ α (U n) hα
  choose ρ hρ hρvar using hstep
  have hvar : ∀ n i, dirVar (EuclideanSpace.single i 1) (ρ n) ≤ ENNReal.ofReal κ := fun n i => by
    have := hρvar n (Fin.castAdd _ i)
    rwa [hU1] at this
  have hvarw : ∀ n k, k ≤ n → dirVar (w k : Euc d) (ρ n) ≤ ENNReal.ofReal κ := fun n k hk => by
    have := hρvar n (Fin.natAdd d ⟨k, by omega⟩)
    rwa [hU2] at this
  -- compactness
  obtain ⟨φ, ρ', hφ, hρ', hlim⟩ := exists_subseq_tendsto_L1 hK.isBounded ENNReal.ofReal_ne_top ρ
    (fun n => (hρ n).toIsProbDensityOn) hvar
  -- lower semicontinuity along the subsequence
  have hρ'e : ∀ i, dirVar (EuclideanSpace.single i 1) ρ' ≤ ENNReal.ofReal κ := fun i =>
    (dirVar_le_liminf _ (fun j => ρ (φ j)) ρ' (fun j => (hρ (φ j)).measurable) hρ'.measurable
      hlim).trans
      (liminf_le_of_frequently_le' (Eventually.of_forall fun j => hvar (φ j) i).frequently)
  have hρ'w : ∀ k, dirVar (w k : Euc d) ρ' ≤ ENNReal.ofReal κ := fun k =>
    (dirVar_le_liminf _ (fun j => ρ (φ j)) ρ' (fun j => (hρ (φ j)).measurable) hρ'.measurable
      hlim).trans
      (liminf_le_of_frequently_le' ((eventually_ge_atTop k).mono fun j hj =>
        hvarw (φ j) k (hj.trans hφ.le_apply)).frequently)
  refine ⟨ρ', memP_of_coord_le hρ' ENNReal.ofReal_ne_top hρ'e, fun v hv => ?_⟩
  -- extend to all unit directions by density
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (Real.sqrt d * κ + 1) := ⟨_, rfl⟩
  have hδpos : 0 < δ := hδ ▸ div_pos hε (by positivity)
  obtain ⟨k, hk⟩ := hw.exists_dist_lt ⟨v, by simpa [mem_sphere_zero_iff_norm] using hv⟩ hδpos
  rw [Subtype.dist_eq, dist_eq_norm] at hk
  calc dirVar v ρ'
      ≤ dirVar (w k : Euc d) ρ' + ENNReal.ofReal (Real.sqrt d * ‖v - w k‖) * ENNReal.ofReal κ :=
        dirVar_le_dirVar_add ρ' hρ'.measurable v (w k : Euc d) hρ'e
    _ ≤ ENNReal.ofReal κ + ε := by
        gcongr
        · exact hρ'w k
        · rw [← ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
          calc ENNReal.ofReal (Real.sqrt d * ‖v - w k‖ * κ) ≤ ENNReal.ofReal ε := by
                refine ENNReal.ofReal_le_ofReal ?_
                calc Real.sqrt d * ‖v - w k‖ * κ ≤ Real.sqrt d * δ * κ := by gcongr
                  _ = ε * ((Real.sqrt d * κ) / (Real.sqrt d * κ + 1)) := by
                      rw [hδ]; field_simp
                  _ ≤ ε * 1 := by
                      gcongr
                      exact div_le_one_of_le₀ (by linarith) (by positivity)
                  _ = ε := mul_one _
            _ = ε := ENNReal.ofReal_coe_nnreal

/-- Homogeneity (paper Lemma 3.3, last line): the cap on unit directions gives (2.8). -/
theorem varBounded_of_unit {ρ : Euc d → ℝ} (hρ : Measurable ρ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hunit : ∀ v : Euc d, ‖v‖ = 1 → dirVar v ρ ≤ ENNReal.ofReal κ) : VarBounded κ ρ := by
  intro v
  by_cases hv : v = 0
  · subst hv
    simp [dirVar_zero]
  · have hv' : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul]
    calc dirVar v ρ = dirVar (‖v‖ • (‖v‖⁻¹ • v)) ρ := by rw [← hv']
      _ = ENNReal.ofReal |‖v‖| * dirVar (‖v‖⁻¹ • v) ρ := dirVar_smul _ _ _ hρ
      _ ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal κ := by
          rw [abs_norm]
          gcongr
          exact hunit _ (norm_smul_inv_norm (𝕜 := ℝ) hv)
      _ = ENNReal.ofReal (κ * ‖v‖) := by rw [ENNReal.ofReal_mul hκ, mul_comm]

/-- Paper Lemma 3.3: if `h_H(K) ≤ κ` for every mixture `H`, then `K` admits a density
satisfying the cap (2.8). -/
theorem hasAdmissible_of_cheeger_le {K : Set (Euc d)} (hK : IsGoodConvex K) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (h : ∀ (N : ℕ) (α : Fin N → ℝ) (u : Fin N → Euc d), IsMixture α u →
      cheeger α u K ≤ ENNReal.ofReal κ) :
    HasAdmissible K κ := by
  obtain ⟨ρ, hρ, hunit⟩ := exists_memP_unit_directions hK hκ h
  exact ⟨ρ, hρ, varBounded_of_unit hρ.measurable hκ hunit⟩

end Komlos
