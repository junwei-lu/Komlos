import Komlos.Literature.Regularized.Interface
import Komlos.Literature.Sobolev.Density

/-!
# Inner domains for the Korevaar limit

Step 1 of the `L4` lane of `REGULARIZED_ROUTE.md` ("Korevaar with two functions"): the
exhaustion of a bounded open convex `K` by the dilated bodies

  `dilateSet x₀ s K = x₀ + s • (K - x₀)`,  `x₀ ∈ K`, `0 < s < 1`,

which are again `IsGoodConvex`, satisfy `closure (dilateSet x₀ s K) ⊆ K`, increase with `s`,
and exhaust `K` as `s ↑ 1`.  The concrete exhausting sequence used downstream is
`innerDomain x₀ K n = dilateSet x₀ (innerRatio n) K` with `innerRatio n = 1 - 1/(n+2)`.

## Main results

* `dilateSet_mem_iff` — `x ∈ dilateSet x₀ s K ↔ x₀ + s⁻¹ • (x - x₀) ∈ K` (for `s ≠ 0`);
* `isGoodConvex_dilateSet` — the dilate of a good convex body is a good convex body;
* `closure_dilateSet_subset` — `closure (dilateSet x₀ s K) ⊆ K` for `x₀ ∈ K`, `0 < s < 1`;
* `dilateSet_mono` — monotonicity in the ratio `s` (uses `x₀ ∈ K` and convexity);
* `exists_mem_dilateSet` — every `x ∈ K` lies in `dilateSet x₀ s K` for `s` close enough to `1`;
* `innerDomain`, `monotone_innerDomain`, `iUnion_innerDomain`, `tendsto_innerRatio` — the
  exhausting sequence and its ratios.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise ContDiff RealInnerProductSpace

namespace Komlos.Literature.Regularized

variable {d : ℕ} {K : Set (Euc d)}

/-! ### The dilated body -/

/-- The dilate `x₀ + s • (K - x₀)` of `K` towards the centre `x₀` by the ratio `s`. -/
def dilateSet (x₀ : Euc d) (s : ℝ) (K : Set (Euc d)) : Set (Euc d) :=
  (fun y => x₀ + s • (y - x₀)) '' K

/-- Membership in the dilate is membership of the inverse dilate in `K`. -/
theorem dilateSet_mem_iff {x₀ : Euc d} {s : ℝ} (hs : s ≠ 0) {x : Euc d} :
    x ∈ dilateSet x₀ s K ↔ x₀ + s⁻¹ • (x - x₀) ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs, one_smul, add_sub_cancel]
  · intro h
    refine ⟨_, h, ?_⟩
    show x₀ + s • (x₀ + s⁻¹ • (x - x₀) - x₀) = x
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hs, one_smul, add_sub_cancel]

/-- The inverse dilation maps `dilateSet x₀ s K` into `K`. -/
theorem dilate_inv_mem {x₀ : Euc d} {s : ℝ} (hs : s ≠ 0) {x : Euc d}
    (hx : x ∈ dilateSet x₀ s K) : x₀ + s⁻¹ • (x - x₀) ∈ K :=
  (dilateSet_mem_iff hs).1 hx

/-- The contrapositive form, used to transport "vanishing off the domain". -/
theorem notMem_dilateSet {x₀ : Euc d} {s : ℝ} (hs : s ≠ 0) {x : Euc d}
    (hx : x₀ + s⁻¹ • (x - x₀) ∉ K) : x ∉ dilateSet x₀ s K := fun h => hx (dilate_inv_mem hs h)

/-- For `0 ≤ s ≤ 1` and a centre in `K`, the dilate is contained in `K`. -/
theorem dilateSet_subset (hK : Convex ℝ K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : dilateSet x₀ s K ⊆ K := by
  rintro _ ⟨y, hy, rfl⟩
  have key := hK hx₀ hy (by linarith : (0:ℝ) ≤ 1 - s) hs0 (by ring)
  have heq : (1 - s) • x₀ + s • y = x₀ + s • (y - x₀) := by module
  rwa [heq] at key

/-- The dilate of a good convex body (towards one of its points, by a ratio in `(0, 1]`) is a
good convex body. -/
theorem isGoodConvex_dilateSet (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) : IsGoodConvex (dilateSet x₀ s K) where
  nonempty := hK.nonempty.image _
  isBounded := hK.isBounded.subset (dilateSet_subset hK.convex hx₀ hs0.le hs1)
  isOpen := by
    have hpre : dilateSet x₀ s K = (fun x : Euc d => x₀ + s⁻¹ • (x - x₀)) ⁻¹' K := by
      ext x; exact dilateSet_mem_iff hs0.ne'
    rw [hpre]
    exact hK.isOpen.preimage (by fun_prop)
  convex := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ u v hu hv huv
    refine ⟨u • a + v • b, hK.convex ha hb hu hv huv, ?_⟩
    have hv' : v = 1 - u := by linarith
    subst hv'
    module

/-- **The inner domain is compactly contained in `K`**: `closure (x₀ + s (K - x₀)) ⊆ K` for
`x₀ ∈ K` and `0 < s < 1` (`Komlos.dilate_closure_add_ball_subset`). -/
theorem closure_dilateSet_subset (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) : closure (dilateSet x₀ s K) ⊆ K := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hK.isOpen x₀ hx₀
  have hcont : Continuous fun y : Euc d => x₀ + s • (y - x₀) := by fun_prop
  have hL : IsCompact ((fun y => x₀ + s • (y - x₀)) '' closure K) :=
    hK.isBounded.isCompact_closure.image hcont
  have hsub : closure (dilateSet x₀ s K) ⊆ (fun y => x₀ + s • (y - x₀)) '' closure K :=
    closure_minimal (Set.image_mono subset_closure) hL.isClosed
  refine hsub.trans fun y hy => ?_
  exact dilate_closure_add_ball_subset hK.convex hK.isOpen hball hs0.le hs1
    (mul_pos (by linarith) hδ) ⟨y, hy, 0, Metric.mem_closedBall_self le_rfl, add_zero y⟩

/-- The dilates increase with the ratio. -/
theorem dilateSet_mono (hK : Convex ℝ K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) : dilateSet x₀ s K ⊆ dilateSet x₀ t K := by
  have ht0 : 0 < t := lt_of_lt_of_le hs hst
  rintro _ ⟨y, hy, rfl⟩
  have hr0 : 0 ≤ s / t := by positivity
  have hr1 : s / t ≤ 1 := (div_le_one ht0).2 hst
  have heq : x₀ + t⁻¹ • (x₀ + s • (y - x₀) - x₀) = (1 - s / t) • x₀ + (s / t) • y := by
    rw [add_sub_cancel_left, smul_smul, show t⁻¹ * s = s / t by ring]
    module
  rw [dilateSet_mem_iff ht0.ne', heq]
  exact hK hx₀ hy (by linarith) hr0 (by ring)

/-- Every point of the open set `K` belongs to a dilate with ratio arbitrarily close to `1`. -/
theorem exists_mem_dilateSet (hK : IsOpen K) (x₀ : Euc d) {x : Euc d} (hx : x ∈ K) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x ∈ dilateSet x₀ s K := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK x hx
  set M : ℝ := ‖x - x₀‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  set ε : ℝ := min (1 / 2) (r / (2 * (M + 1))) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  refine ⟨1 / (1 + ε), by positivity, by
    rw [div_lt_one (by linarith)]; linarith, ?_⟩
  rw [dilateSet_mem_iff (by positivity)]
  refine hball ?_
  rw [Metric.mem_ball, dist_eq_norm]
  have hinv : (1 / (1 + ε) : ℝ)⁻¹ = 1 + ε := by
    rw [one_div, inv_inv]
  have hnorm : ‖x₀ + (1 / (1 + ε) : ℝ)⁻¹ • (x - x₀) - x‖ = ε * M := by
    rw [hinv]
    have : x₀ + (1 + ε) • (x - x₀) - x = ε • (x - x₀) := by module
    rw [this, norm_smul, Real.norm_of_nonneg hε0.le]
  rw [hnorm]
  have h1 : ε ≤ r / (2 * (M + 1)) := min_le_right _ _
  have h2 : ε * M ≤ r / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right h1 hM0
  have h3 : r / (2 * (M + 1)) * M < r := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### The exhausting sequence -/

/-- The ratios `1 - 1/(n+2)` of the exhausting sequence of inner domains. -/
noncomputable def innerRatio (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

theorem innerRatio_pos (n : ℕ) : 0 < innerRatio n := by
  have h : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  simp only [innerRatio]; linarith

theorem innerRatio_lt_one (n : ℕ) : innerRatio n < 1 := by
  have : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  simp only [innerRatio]; linarith

theorem monotone_innerRatio : Monotone innerRatio := by
  intro m n hmn
  have hm : (0:ℝ) < (m : ℝ) + 2 := by positivity
  have hle : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
    have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
    linarith
  have := one_div_le_one_div_of_le hm hle
  simp only [innerRatio]; linarith

theorem tendsto_innerRatio : Tendsto innerRatio atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    exact one_div_le_one_div_of_le h1 (by linarith)
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h0
  rw [sub_zero] at h1
  exact h1

/-- The exhausting sequence of inner domains of `K` centred at `x₀`. -/
noncomputable def innerDomain (x₀ : Euc d) (K : Set (Euc d)) (n : ℕ) : Set (Euc d) :=
  dilateSet x₀ (innerRatio n) K

theorem isGoodConvex_innerDomain (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) (n : ℕ) :
    IsGoodConvex (innerDomain x₀ K n) :=
  isGoodConvex_dilateSet hK hx₀ (innerRatio_pos n) (innerRatio_lt_one n).le

theorem closure_innerDomain_subset (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) (n : ℕ) :
    closure (innerDomain x₀ K n) ⊆ K :=
  closure_dilateSet_subset hK hx₀ (innerRatio_pos n) (innerRatio_lt_one n)

theorem innerDomain_subset (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) (n : ℕ) :
    innerDomain x₀ K n ⊆ K :=
  subset_closure.trans (closure_innerDomain_subset hK hx₀ n)

theorem monotone_innerDomain (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) :
    Monotone (innerDomain x₀ K) := fun m _n hmn =>
  dilateSet_mono hK.convex hx₀ (innerRatio_pos m) (monotone_innerRatio hmn)

theorem iUnion_innerDomain (hK : IsGoodConvex K) {x₀ : Euc d} (hx₀ : x₀ ∈ K) :
    ⋃ n, innerDomain x₀ K n = K := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun n => innerDomain_subset hK hx₀ n) fun x hx => ?_
  obtain ⟨s, hs0, hs1, hxs⟩ := exists_mem_dilateSet hK.isOpen x₀ hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s ≤ innerRatio n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - s))
    refine ⟨n, ?_⟩
    have h1s : 0 < 1 - s := by linarith
    have hn0 : (0:ℝ) < (n : ℝ) + 2 := by positivity
    have hlt : 1 / (1 - s) < (n : ℝ) + 2 := by linarith
    have : 1 / ((n : ℝ) + 2) < 1 - s := by
      rw [div_lt_iff₀ hn0]
      rw [div_lt_iff₀ h1s] at hlt
      nlinarith
    simp only [innerRatio]; linarith
  exact Set.mem_iUnion.2 ⟨n, dilateSet_mono hK.convex hx₀ hs0 hn hxs⟩

end Komlos.Literature.Regularized
