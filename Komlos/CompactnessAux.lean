import Komlos.Variation

/-!
# Auxiliary material for the `L¹`-compactness lemma (paper Lemma 3.1)

The compactness half of paper Lemma 3.1 is proved by approximating every member of the family
by its averages on the cubes of a fixed grid.  This file sets up

* the grid cubes `Komlos.gridCube δ k = ∏ [δ k_i, δ (k_i + 1))` of mesh `δ`, their volumes and
  the index map `Komlos.cubeIdx`;
* the cube-averaging operator `Komlos.cubeAvg`, and the `L¹` error bound
  `‖A_δ f − f‖₁ ≤ 2^d d δ ∑_i V_{e_i} f` obtained from the uniform translation modulus
  (`Komlos.lintegral_translate_sub_le_sum_coord`);
* the step-function map `Komlos.stepLp` into `L¹(ℝ^d)` and the total-boundedness statement
  `Komlos.totallyBounded_range_toLp` for a family of densities with bounded support and
  uniformly bounded coordinate variations.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Komlos

/-- A set that is uniformly approximable by totally bounded sets is totally bounded. -/
theorem totallyBounded_of_approx {X : Type*} [PseudoMetricSpace X] {s : Set X}
    (h : ∀ ε > 0, ∃ T : Set X, TotallyBounded T ∧ ∀ x ∈ s, ∃ y ∈ T, dist x y ≤ ε) :
    TotallyBounded s := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨T, hT, hsT⟩ := h (ε / 3) (by positivity)
  obtain ⟨t, htfin, hTt⟩ := Metric.totallyBounded_iff.1 hT (ε / 3) (by positivity)
  refine ⟨t, htfin, fun x hx => ?_⟩
  obtain ⟨y, hyT, hxy⟩ := hsT x hx
  obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.1 (hTt hyT)
  refine Set.mem_iUnion₂.2 ⟨z, hzt, ?_⟩
  rw [Metric.mem_ball] at hyz ⊢
  linarith [dist_triangle x y z]

variable {d : ℕ}

section Grid

/-- The index `(⌊x_i / δ⌋)_i` of the grid cube of mesh `δ` containing `x`. -/
noncomputable def cubeIdx (δ : ℝ) (x : Euc d) : Fin d → ℤ := fun i => ⌊x i / δ⌋

/-- The half-open grid cube `∏_i [δ k_i, δ (k_i + 1))` of mesh `δ` with index `k`. -/
def gridCube (δ : ℝ) (k : Fin d → ℤ) : Set (Euc d) :=
  {x | ∀ i, δ * k i ≤ x i ∧ x i < δ * (k i + 1)}

/-- The open box `∏_i (-δ, δ)`. -/
def box (δ : ℝ) : Set (Euc d) := {y | ∀ i, |y i| < δ}

theorem mem_gridCube_iff_cubeIdx_eq {δ : ℝ} (hδ : 0 < δ) {k : Fin d → ℤ} {x : Euc d} :
    x ∈ gridCube δ k ↔ cubeIdx δ x = k := by
  change (∀ i, δ * k i ≤ x i ∧ x i < δ * (k i + 1)) ↔ _
  simp only [cubeIdx, funext_iff, Int.floor_eq_iff]
  refine forall_congr' fun i => ?_
  rw [le_div_iff₀ hδ, div_lt_iff₀ hδ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem self_mem_gridCube {δ : ℝ} (hδ : 0 < δ) (x : Euc d) : x ∈ gridCube δ (cubeIdx δ x) :=
  (mem_gridCube_iff_cubeIdx_eq hδ).2 rfl

theorem abs_sub_lt_of_mem_gridCube {δ : ℝ} {k : Fin d → ℤ} {x z : Euc d} (hx : x ∈ gridCube δ k)
    (hz : z ∈ gridCube δ k) (i : Fin d) : |z i - x i| < δ := by
  obtain ⟨hx1, hx2⟩ := hx i
  obtain ⟨hz1, hz2⟩ := hz i
  rw [abs_sub_lt_iff]
  constructor <;> linarith

theorem gridCube_eq_preimage (δ : ℝ) (k : Fin d → ℤ) :
    gridCube δ k = (WithLp.ofLp : Euc d → Fin d → ℝ) ⁻¹'
      (Set.pi univ fun i => Ico (δ * k i) (δ * (k i + 1))) := by
  ext x
  simp [gridCube, Set.mem_pi]

theorem box_eq_preimage (δ : ℝ) :
    box δ = (WithLp.ofLp : Euc d → Fin d → ℝ) ⁻¹' (Set.pi univ fun _ => Ioo (-δ) δ) := by
  ext x
  simp [box, Set.mem_pi, abs_lt]

theorem measurableSet_gridCube (δ : ℝ) (k : Fin d → ℤ) : MeasurableSet (gridCube δ k) := by
  rw [gridCube_eq_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin d)).measurable
    (MeasurableSet.univ_pi fun i => measurableSet_Ico)

theorem measurableSet_box (δ : ℝ) : MeasurableSet (box (d := d) δ) := by
  rw [box_eq_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin d)).measurable
    (MeasurableSet.univ_pi fun i => measurableSet_Ioo)

theorem volume_gridCube (δ : ℝ) (k : Fin d → ℤ) :
    volume (gridCube δ k) = ENNReal.ofReal δ ^ d := by
  rw [gridCube_eq_preimage, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  simp [mul_add]

theorem volume_box (δ : ℝ) :
    volume (box (d := d) δ) = ENNReal.ofReal (2 * δ) ^ d := by
  rw [box_eq_preimage, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
  simp [two_mul]

theorem volume_gridCube_ne_top (δ : ℝ) (k : Fin d → ℤ) : volume (gridCube δ k) ≠ ⊤ := by
  rw [volume_gridCube]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

end Grid

section Averaging

/-- The average `δ^{-d} ∫_{Q_k} f` of `f` on the cube with index `k`. -/
noncomputable def cubeCoef (δ : ℝ) (f : Euc d → ℝ) (k : Fin d → ℤ) : ℝ :=
  (δ ^ d)⁻¹ * ∫ z in gridCube δ k, f z

/-- The cube-averaging operator `A_δ f (x) = δ^{-d} ∫_{Q(x)} f`, `Q(x)` the grid cube of mesh `δ`
containing `x`. -/
noncomputable def cubeAvg (δ : ℝ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  cubeCoef δ f (cubeIdx δ x)

/-- Pointwise bound: `|A_δ f (x) − f (x)| ≤ δ^{-d} ∫_{(-δ,δ)^d} |f (x + y) − f (x)| dy`. -/
theorem enorm_cubeAvg_sub_le {δ : ℝ} (hδ : 0 < δ) {f : Euc d → ℝ} (hfm : Measurable f)
    (hf : Integrable f) (x : Euc d) :
    ‖cubeAvg δ f x - f x‖ₑ ≤
      (ENNReal.ofReal δ ^ d)⁻¹ * ∫⁻ y in box δ, ‖f (x + y) - f x‖ₑ := by
  set Q := gridCube δ (cubeIdx δ x) with hQ
  have hQfin : volume Q ≠ ⊤ := volume_gridCube_ne_top δ _
  have hδd : (0 : ℝ) < δ ^ d := pow_pos hδ d
  have h1 : cubeAvg δ f x - f x = (δ ^ d)⁻¹ * ∫ z in Q, (f z - f x) := by
    rw [integral_sub hf.integrableOn (integrableOn_const hQfin), setIntegral_const,
      measureReal_def, volume_gridCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ.le,
      smul_eq_mul]
    simp only [cubeAvg, cubeCoef, ← hQ]
    field_simp
  rw [h1, enorm_mul, Real.enorm_of_nonneg (inv_nonneg.2 hδd.le), ENNReal.ofReal_inv_of_pos hδd,
    ENNReal.ofReal_pow hδ.le]
  gcongr
  have hG : Measurable fun z => ‖f z - f x‖ₑ := (hfm.sub measurable_const).enorm
  calc ‖∫ z in Q, (f z - f x)‖ₑ ≤ ∫⁻ z in Q, ‖f z - f x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z in (fun z => z - x) ⁻¹' box δ, ‖f z - f x‖ₑ := by
        refine lintegral_mono_set fun z hz i => ?_
        simpa using abs_sub_lt_of_mem_gridCube (self_mem_gridCube hδ x) hz i
    _ = ∫⁻ y in (fun y : Euc d => x + y) ⁻¹' ((fun z => z - x) ⁻¹' box δ),
          ‖f (x + y) - f x‖ₑ :=
        ((measurePreserving_add_left volume x).setLIntegral_comp_preimage
          ((measurable_sub_const x) (measurableSet_box δ)) hG).symm
    _ = ∫⁻ y in box δ, ‖f (x + y) - f x‖ₑ := by
        have hpre : (fun y : Euc d => x + y) ⁻¹' ((fun z => z - x) ⁻¹' box δ) = box δ := by
          ext y; simp
        rw [hpre]

/-- Integrated bound: `‖A_δ f − f‖₁ ≤ δ^{-d} ∫_{(-δ,δ)^d} ‖f (· + y) − f‖₁ dy`. -/
theorem lintegral_cubeAvg_sub_le {δ : ℝ} (hδ : 0 < δ) {f : Euc d → ℝ} (hfm : Measurable f)
    (hf : Integrable f) :
    ∫⁻ x, ‖cubeAvg δ f x - f x‖ₑ ≤
      (ENNReal.ofReal δ ^ d)⁻¹ * ∫⁻ y in box δ, ∫⁻ x, ‖f (x + y) - f x‖ₑ := by
  have hne : (ENNReal.ofReal δ ^ d)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hδ).ne')
  calc ∫⁻ x, ‖cubeAvg δ f x - f x‖ₑ
      ≤ ∫⁻ x, (ENNReal.ofReal δ ^ d)⁻¹ * ∫⁻ y in box δ, ‖f (x + y) - f x‖ₑ :=
        lintegral_mono fun x => enorm_cubeAvg_sub_le hδ hfm hf x
    _ = (ENNReal.ofReal δ ^ d)⁻¹ * ∫⁻ x, ∫⁻ y in box δ, ‖f (x + y) - f x‖ₑ :=
        lintegral_const_mul' _ _ hne
    _ = (ENNReal.ofReal δ ^ d)⁻¹ * ∫⁻ y in box δ, ∫⁻ x, ‖f (x + y) - f x‖ₑ := by
        congr 1
        refine lintegral_lintegral_swap ?_
        exact (((hfm.comp (measurable_fst.add measurable_snd)).sub
          (hfm.comp measurable_fst)).enorm).aemeasurable

/-- The `L¹` error of cube averaging is controlled by the coordinate variations
(paper Lemma 3.1): `‖A_δ f − f‖₁ ≤ 2^d d δ M` when `V_{e_i} f ≤ M` for all `i`. -/
theorem lintegral_cubeAvg_sub_le_of_dirVar {δ : ℝ} (hδ : 0 < δ) {f : Euc d → ℝ}
    (hfm : Measurable f) (hf : Integrable f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, dirVar (EuclideanSpace.single i 1) f ≤ ENNReal.ofReal M) :
    ∫⁻ x, ‖cubeAvg δ f x - f x‖ₑ ≤ ENNReal.ofReal (2 ^ d * d * δ * M) := by
  refine (lintegral_cubeAvg_sub_le hδ hfm hf).trans ?_
  have hinner : ∀ y ∈ box δ,
      ∫⁻ x, ‖f (x + y) - f x‖ₑ ≤ ENNReal.ofReal (d * (δ * M)) := by
    intro y hy
    refine (lintegral_translate_sub_le_sum_coord f hfm y).trans ?_
    calc ∑ i, ENNReal.ofReal |y i| * dirVar (EuclideanSpace.single i 1) f
        ≤ ∑ _i : Fin d, ENNReal.ofReal δ * ENNReal.ofReal M :=
          Finset.sum_le_sum fun i _ => mul_le_mul' (ENNReal.ofReal_le_ofReal (hy i).le) (hM i)
      _ = ENNReal.ofReal (d * (δ * M)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d), ENNReal.ofReal_mul hδ.le,
            ENNReal.ofReal_natCast]
  have hδd : (0 : ℝ) < δ ^ d := pow_pos hδ d
  calc (ENNReal.ofReal δ ^ d)⁻¹ * ∫⁻ y in box δ, ∫⁻ x, ‖f (x + y) - f x‖ₑ
      ≤ (ENNReal.ofReal δ ^ d)⁻¹ * ∫⁻ _y in box δ, ENNReal.ofReal (d * (δ * M)) :=
        mul_le_mul' le_rfl (setLIntegral_mono' (measurableSet_box δ) hinner)
    _ = ENNReal.ofReal ((δ ^ d)⁻¹) *
          (ENNReal.ofReal (d * (δ * M)) * ENNReal.ofReal ((2 * δ) ^ d)) := by
        rw [setLIntegral_const, volume_box, ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_inv_of_pos hδd, ENNReal.ofReal_pow hδ.le]
    _ = ENNReal.ofReal ((δ ^ d)⁻¹ * (d * (δ * M) * (2 * δ) ^ d)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (2 ^ d * d * δ * M) := by
        congr 1
        rw [mul_pow]
        field_simp

end Averaging

section Support

/-- The finite set of indices of the grid cubes of mesh `δ` that can meet the ball of
radius `R`. -/
noncomputable def cubeIndices (δ R : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(⌈R / δ⌉ + 1)) (⌈R / δ⌉ + 1)

theorem cubeIdx_mem_cubeIndices {δ R : ℝ} (hδ : 0 < δ) {x : Euc d} (hx : ‖x‖ ≤ R) :
    cubeIdx δ x ∈ cubeIndices δ R := by
  rw [cubeIndices, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hxi : |x i| ≤ R := by
    have := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at this
    exact this.trans hx
  have h1 : (⌊x i / δ⌋ : ℝ) ≤ x i / δ := Int.floor_le _
  have h2 : x i / δ < ⌊x i / δ⌋ + 1 := Int.lt_floor_add_one _
  have h3 : R / δ ≤ (⌈R / δ⌉ : ℝ) := Int.le_ceil _
  have h4 : |x i / δ| ≤ R / δ := by
    rw [abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right hxi hδ.le
  obtain ⟨h5, h6⟩ := abs_le.1 h4
  constructor
  · have : (-(⌈R / δ⌉ + 1) : ℝ) < ⌊x i / δ⌋ := by linarith
    exact_mod_cast this.le
  · have : (⌊x i / δ⌋ : ℝ) ≤ ⌈R / δ⌉ + 1 := by linarith
    exact_mod_cast this

/-- On a cube whose index is not in `cubeIndices δ R`, a function vanishing a.e. outside the
ball of radius `R` has zero average. -/
theorem cubeCoef_eq_zero {δ R : ℝ} (hδ : 0 < δ) {K : Set (Euc d)} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {f : Euc d → ℝ} (hf : ∀ᵐ x, x ∉ K → f x = 0) {k : Fin d → ℤ} (hk : k ∉ cubeIndices δ R) :
    cubeCoef δ f k = 0 := by
  unfold cubeCoef
  rw [integral_eq_zero_of_ae, mul_zero]
  filter_upwards [ae_restrict_mem (measurableSet_gridCube δ k), ae_restrict_of_ae hf] with z hz hfz
  refine hfz fun hzK => hk ?_
  rw [← (mem_gridCube_iff_cubeIdx_eq hδ).1 hz]
  exact cubeIdx_mem_cubeIndices hδ (hKR z hzK)

/-- For `f` vanishing a.e. outside the ball of radius `R`, `A_δ f` is the step function
`∑_{k ∈ cubeIndices δ R} (δ^{-d} ∫_{Q_k} f) 𝟙_{Q_k}`. -/
theorem cubeAvg_eq_sum {δ R : ℝ} (hδ : 0 < δ) {K : Set (Euc d)} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {f : Euc d → ℝ} (hf : ∀ᵐ x, x ∉ K → f x = 0) (x : Euc d) :
    cubeAvg δ f x =
      ∑ k ∈ cubeIndices δ R, cubeCoef δ f k * (gridCube δ k).indicator (fun _ => (1 : ℝ)) x := by
  have hne : ∀ k, k ≠ cubeIdx δ x → x ∉ gridCube δ k := fun k hk h =>
    hk ((mem_gridCube_iff_cubeIdx_eq hδ).1 h).symm
  by_cases hx : cubeIdx δ x ∈ cubeIndices δ R
  · rw [Finset.sum_eq_single (cubeIdx δ x)]
    · simp [cubeAvg, self_mem_gridCube hδ x]
    · intro k _ hk
      simp [hne k hk]
    · intro h
      exact absurd hx h
  · rw [Finset.sum_eq_zero]
    · exact cubeCoef_eq_zero hδ hKR hf hx
    · intro k hk
      have : k ≠ cubeIdx δ x := fun h => hx (h ▸ hk)
      simp [hne k this]

/-- The averages of a nonnegative function of mass at most one are bounded by `δ^{-d}`. -/
theorem cubeCoef_mem_Icc {δ : ℝ} (hδ : 0 < δ) {f : Euc d → ℝ} (hf : Integrable f)
    (hnn : ∀ x, 0 ≤ f x) (hmass : ∫ x, f x ≤ 1) (k : Fin d → ℤ) :
    cubeCoef δ f k ∈ Icc (-(δ ^ d)⁻¹) (δ ^ d)⁻¹ := by
  have hδd : (0 : ℝ) < δ ^ d := pow_pos hδ d
  have h0 : 0 ≤ ∫ z in gridCube δ k, f z :=
    setIntegral_nonneg (measurableSet_gridCube δ k) fun z _ => hnn z
  have h1 : ∫ z in gridCube δ k, f z ≤ 1 :=
    (setIntegral_le_integral hf (Eventually.of_forall hnn)).trans hmass
  unfold cubeCoef
  constructor
  · have : 0 ≤ (δ ^ d)⁻¹ * ∫ z in gridCube δ k, f z := by positivity
    linarith [inv_pos.2 hδd]
  · calc (δ ^ d)⁻¹ * ∫ z in gridCube δ k, f z ≤ (δ ^ d)⁻¹ * 1 := by gcongr
      _ = (δ ^ d)⁻¹ := mul_one _

end Support

section LpStep

/-- The indicator `𝟙_{Q_k}` of a grid cube as an element of `L¹(ℝ^d)`. -/
noncomputable def cubeIndicatorLp (δ : ℝ) (k : Fin d → ℤ) :
    Lp ℝ 1 (volume : Measure (Euc d)) :=
  indicatorConstLp 1 (measurableSet_gridCube δ k) (volume_gridCube_ne_top δ k) (1 : ℝ)

theorem coeFn_cubeIndicatorLp (δ : ℝ) (k : Fin d → ℤ) :
    ⇑(cubeIndicatorLp δ k) =ᵐ[volume] (gridCube δ k).indicator fun _ => (1 : ℝ) :=
  indicatorConstLp_coeFn

/-- The step-function map `c ↦ ∑_{k ∈ F} c_k 𝟙_{Q_k}` into `L¹(ℝ^d)`. -/
noncomputable def stepLp (δ : ℝ) (F : Finset (Fin d → ℤ))
    (c : (Fin d → ℤ) → ℝ) : Lp ℝ 1 (volume : Measure (Euc d)) :=
  ∑ k ∈ F, c k • cubeIndicatorLp δ k

theorem continuous_stepLp (δ : ℝ) (F : Finset (Fin d → ℤ)) :
    Continuous (stepLp (d := d) δ F) :=
  continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const

/-- A finite sum in `Lp` is a.e. the pointwise sum of representatives. -/
theorem coeFn_finset_sum_Lp {ι : Type*} (s : Finset ι)
    (g : ι → Lp ℝ 1 (volume : Measure (Euc d))) :
    ⇑(∑ k ∈ s, g k) =ᵐ[volume] fun x => ∑ k ∈ s, g k x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero (E := ℝ) (p := 1) (μ := volume)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a) (∑ k ∈ s, g k), ih] with x hx hx'
    rw [hx, Pi.add_apply, hx', Finset.sum_insert ha]

theorem coeFn_stepLp (δ : ℝ) (F : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) :
    ⇑(stepLp δ F c) =ᵐ[volume]
      fun x => ∑ k ∈ F, c k * (gridCube δ k).indicator (fun _ => (1 : ℝ)) x := by
  have h1 : ∀ᵐ x ∂volume, ∀ k ∈ F,
      (c k • cubeIndicatorLp δ k) x = c k * (gridCube δ k).indicator (fun _ => (1 : ℝ)) x := by
    rw [eventually_all_finset]
    intro k _
    filter_upwards [Lp.coeFn_smul (c k) (cubeIndicatorLp δ k), coeFn_cubeIndicatorLp δ k]
      with x hx hx'
    rw [hx, Pi.smul_apply, hx', smul_eq_mul]
  filter_upwards [coeFn_finset_sum_Lp F (fun k => c k • cubeIndicatorLp δ k), h1] with x hx hx'
  rw [stepLp, hx]
  exact Finset.sum_congr rfl fun k hk => hx' k hk

/-- The `L¹` distance from `f` to its step-function approximation is `‖A_δ f − f‖₁`. -/
theorem dist_toLp_stepLp {δ R : ℝ} (hδ : 0 < δ) {K : Set (Euc d)} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {f : Euc d → ℝ} (hf : Integrable f) (hK : ∀ᵐ x, x ∉ K → f x = 0) :
    dist ((memLp_one_iff_integrable.2 hf).toLp f) (stepLp δ (cubeIndices δ R) (cubeCoef δ f))
      = (∫⁻ x, ‖cubeAvg δ f x - f x‖ₑ).toReal := by
  rw [Lp.dist_def, eLpNorm_one_eq_lintegral_enorm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_one_iff_integrable.2 hf),
    coeFn_stepLp δ (cubeIndices δ R) (cubeCoef δ f)] with x hx hx'
  rw [Pi.sub_apply, hx, hx', ← cubeAvg_eq_sum hδ hKR hK x, enorm_sub_rev]

/-- Paper Lemma 3.1 (compactness), total-boundedness form: the `L¹` classes of densities
supported in a bounded set with uniformly bounded coordinate variations form a totally bounded
subset of `L¹(ℝ^d)`. -/
theorem totallyBounded_range_toLp {K : Set (Euc d)} (hK : Bornology.IsBounded K) {M : ℝ≥0∞}
    (hM : M ≠ ⊤) (ρ : ℕ → Euc d → ℝ) (hρ : ∀ n, IsProbDensityOn K (ρ n))
    (hvar : ∀ n i, dirVar (EuclideanSpace.single i 1) (ρ n) ≤ M) :
    TotallyBounded
      (Set.range fun n => (memLp_one_iff_integrable.2 (hρ n).integrable).toLp (ρ n)) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK
  apply totallyBounded_of_approx
  intro ε hε
  set m : ℝ := M.toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set C : ℝ := 2 ^ d * d * m + 1 with hC
  have hC0 : 0 < C := by positivity
  set δ : ℝ := ε / C with hδdef
  have hδ : 0 < δ := div_pos hε hC0
  refine ⟨stepLp δ (cubeIndices δ R) '' (Set.pi univ fun _ => Icc (-(δ ^ d)⁻¹) (δ ^ d)⁻¹),
    ((isCompact_univ_pi fun _ => isCompact_Icc).image (continuous_stepLp δ _)).totallyBounded,
    ?_⟩
  rintro _ ⟨n, rfl⟩
  refine ⟨_, ⟨cubeCoef δ (ρ n), fun k _ => ?_, rfl⟩, ?_⟩
  · exact cubeCoef_mem_Icc hδ (hρ n).integrable (hρ n).nonneg (hρ n).integral_eq_one.le k
  · rw [dist_toLp_stepLp hδ hR (hρ n).integrable (hρ n).ae_zero_outside]
    have hbound := lintegral_cubeAvg_sub_le_of_dirVar hδ (hρ n).measurable (hρ n).integrable hm0
      (fun i => by rw [hm, ENNReal.ofReal_toReal hM]; exact hvar n i)
    refine ENNReal.toReal_le_of_le_ofReal hε.le (hbound.trans (ENNReal.ofReal_le_ofReal ?_))
    calc 2 ^ d * d * δ * m = ε * ((2 ^ d * d * m) / C) := by rw [hδdef]; ring
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one hC0, hC]
          linarith
      _ = ε := mul_one ε

end LpStep

end Komlos
