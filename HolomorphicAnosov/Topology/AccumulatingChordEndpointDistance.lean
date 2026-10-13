import HolomorphicAnosov.Topology.AccumulatingChordArcClassification
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

namespace HolomorphicAnosov
open Set Filter MeasureTheory
open scoped Topology _root_.Topology

/-- Endpoint pairs of pairwise distinct disjoint open circle arcs form a null
family under any continuous map into a metric space.

Source: de Carvalho, *Pruning fronts and the formation of horseshoes*,
arXiv:math/9701217v1, Definition 4.3 and Lemma 4.4, pp.29--30, the null-family
estimate used in the attached-skeleton continuity argument; Cairns (1951),
§3(E)--§4(A), pp.863--864, countable-chord omission expansion.

Proof: orient each arc by the existing circle-arc classification and represent
it as exp of an interval in (-π,3π). The lifted intervals are pairwise disjoint,
so their lengths are summable for Lebesgue measure restricted to [-π,3π]. Hence
the lengths tend to zero. Uniform continuity of the continuous map composed
with exp on this compact interval makes the image endpoint distances tend to
zero. Reversing an arc's orientation does not change that distance. -/
theorem accumulatingChord_endpoint_distance_tendsto_zero
    {E : Type*} [PseudoMetricSpace E] {ι : Type*}
    (σ : Circle → E) (hσ : Continuous σ)
    (arcs : ι → Set Circle) (u v : ι → Circle)
    (hOpen : ∀ i, IsOpen (arcs i))
    (hConnected : ∀ i, IsConnected (arcs i))
    (hEndpoints : ∀ i, frontier (arcs i) = {u i, v i})
    (hDistinct : ∀ i, u i ≠ v i)
    (hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j))
    (i : ℕ → ι) (hi : Pairwise fun n m ↦ i n ≠ i m) :
    Tendsto (fun n ↦ dist (σ (u (i n))) (σ (v (i n)))) atTop (𝓝 0) := by
  classical
  have hsegImage {a b : ℝ} (hab : a < b) :
      (Path.segment a b) '' Ioo 0 1 = Ioo a b := by
    simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ioo 0 1)]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add,
      image_subtype_val_Ioo, Icc.coe_zero, Icc.coe_one]
    convert image_affine_Ioo (sub_pos_of_lt hab) a 0 1 using 2 <;>
      simp [AffineMap.lineMap_apply_module, smul_eq_mul]
    ring
  have horient (n : ℕ) : ∃ p q : Circle, p ≠ q ∧
      arcs (i n) = Circle.path p q '' Ioo 0 1 ∧
      dist (σ (u (i n))) (σ (v (i n))) = dist (σ p) (σ q) := by
    rcases circle_arc_subset_directed_path (arcs (i n)) (u (i n)) (v (i n))
      (hOpen _) (hConnected _) (hEndpoints _) (hDistinct _) with hf | hb
    · exact ⟨u (i n), v (i n), hDistinct _,
        circle_arc_eq_directed_path _ _ _ (hOpen _) (hConnected _) (hEndpoints _)
          (hDistinct _) hf, rfl⟩
    · refine ⟨v (i n), u (i n), (hDistinct _).symm, ?_, dist_comm ..⟩
      apply circle_arc_eq_directed_path _ _ _ (hOpen _) (hConnected _)
        (by simpa only [pair_comm] using hEndpoints (i n)) (hDistinct _).symm hb
  choose p q hpq harc hseg using horient
  let a : ℕ → ℝ := fun n ↦ (p n : ℂ).arg
  let b : ℕ → ℝ := fun n ↦ Circle.angleDiff (p n) (q n) + a n
  have hab (n) : a n < b n := by
    dsimp only [b]
    linarith [Circle.angleDiff_pos (hpq n)]
  have ha (n) : -Real.pi < a n := Complex.neg_pi_lt_arg _
  have hb (n) : b n < 3 * Real.pi := by
    dsimp only [b, a]
    linarith [Circle.angleDiff_lt_two_pi (p n) (q n), Complex.arg_le_pi (p n : ℂ)]
  have hpa (n) : Circle.exp (a n) = p n := Circle.exp_arg _
  have hqb (n) : Circle.exp (b n) = q n := by
    dsimp only [b]
    rw [Circle.exp_add, hpa]
    exact Circle.exp_angleDiff_mul
  have himage (n) : Circle.exp '' Ioo (a n) (b n) = arcs (i n) := by
    rw [harc n, Circle.coe_path, image_comp, hsegImage (hab n)]
  have hdisj : Pairwise (fun n m ↦ Disjoint (Ioo (a n) (b n)) (Ioo (a m) (b m))) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro t htn htm
    exact Set.disjoint_left.mp (hArcsDisjoint (hi hnm))
      (himage n ▸ mem_image_of_mem Circle.exp htn)
      (himage m ▸ mem_image_of_mem Circle.exp htm)
  let K : Set ℝ := Icc (-Real.pi) (3 * Real.pi)
  have hsub (n) : Ioo (a n) (b n) ⊆ K := by
    intro t ht
    exact ⟨(ha n).le.trans ht.1.le, ht.2.le.trans (hb n).le⟩
  let μ : Measure ℝ := volume.restrict K
  have hm (n) : μ.real (Ioo (a n) (b n)) = b n - a n := by
    dsimp only [μ, Measure.real]
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr (hsub n)]
    exact Real.volume_real_Ioo_of_le (hab n).le
  have hsum : Summable (fun n ↦ b n - a n) := by
    have hs := summable_measure_toReal (μ := μ) (fun n ↦ measurableSet_Ioo) hdisj
    simpa only [hm] using hs
  have hlength := hsum.tendsto_atTop_zero
  have huc : UniformContinuousOn (fun t ↦ σ (Circle.exp t)) K :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (hσ.comp Circle.exp.continuous).continuousOn
  have hap (n) : a n ∈ K := ⟨(ha n).le, (hab n).le.trans (hb n).le⟩
  have hbp (n) : b n ∈ K := ⟨(ha n).le.trans (hab n).le, (hb n).le⟩
  have hend : Tendsto (fun n ↦ dist (σ (p n)) (σ (q n))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδspec⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    filter_upwards [hlength.eventually_lt_const hδ] with n hn
    have hd : dist (a n) (b n) < δ := by
      simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hab n).le), neg_sub] using hn
    have he := hδspec (a n) (hap n) (b n) (hbp n) hd
    simpa only [hpa, hqb, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using he
  exact hend.congr (fun n ↦ (hseg n).symm)


end HolomorphicAnosov
