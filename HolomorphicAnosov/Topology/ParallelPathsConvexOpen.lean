import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Module

/-!
# Disjoint parallel paths in an open convex set

An elementary affine-geometric lemma used in the Markov-free argument for
Ghys, *Holomorphic Anosov systems*, Proposition 4.1, pp.596–597.
This precise formulation and its continuous-family refinement are agent-written.
DAG node: `topo.parallel_paths_convex_open_g17`.
-/

open Set Metric
open scoped Topology
namespace HolomorphicAnosov

/-- In an open convex subset of a real normed space of dimension at least two,
any neighborhoods of two distinct points can be joined by arbitrarily many
pairwise disjoint compact segment paths.

Choose a vector linearly independent of the endpoint difference. Translate
the original segment by distinct sufficiently small positive multiples of
this vector. Both translated endpoints stay in their specified neighborhoods
and in the convex domain, so the whole segment stays in the domain. Equality
of points on two translated segments forces equality of both coefficients
by linear independence, hence equality of their translation labels. This is
the parallel-path step of the Markov-free Ghys Proposition 4.1 argument. -/
theorem parallel_paths_convex_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 1 < Module.finrank ℝ E)
    (U N₀ N₁ : Set E) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁)
    (a b : E) (hab : a ≠ b) (ha : a ∈ U ∩ N₀) (hb : b ∈ U ∩ N₁)
    (n : ℕ) :
    ∃ (x y : Fin n → E) (γ : ∀ i, Path (x i) (y i)),
      (∀ i, x i ∈ N₀ ∧ y i ∈ N₁ ∧ Set.range (γ i) ⊆ U) ∧
      Pairwise (fun i j ↦ Disjoint (Set.range (γ i)) (Set.range (γ j))) := by
  classical
  obtain ⟨v, hv⟩ := exists_linearIndependent_pair_of_one_lt_finrank hdim
    (show b - a ≠ 0 from sub_ne_zero.mpr hab.symm)
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp (hU.inter hN₀) a ha
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp (hU.inter hN₁) b hb
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  let δ := ε / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let r : Fin n → ℝ := fun i ↦ δ * ((i.val : ℝ) + 1) / ((n : ℝ) + 1)
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hr (i : Fin n) : 0 < r i ∧ r i < δ := by
    have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
    constructor
    · exact div_pos (mul_pos hδ (by positivity)) hn
    · apply (div_lt_iff₀ hn).mpr
      nlinarith
  have hshift (i : Fin n) : ‖r i • v‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hr i).1]
    have hδv : δ * (‖v‖ + 1) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith [norm_nonneg v, (hr i).1, (hr i).2]
  have ha' (i : Fin n) : a + r i • v ∈ U ∩ N₀ := by
    apply hball₀
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hshift i).trans_le (min_le_left _ _)
  have hb' (i : Fin n) : b + r i • v ∈ U ∩ N₁ := by
    apply hball₁
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hshift i).trans_le (min_le_right _ _)
  refine ⟨fun i ↦ a + r i • v, fun i ↦ b + r i • v,
    fun i ↦ Path.segment (a + r i • v) (b + r i • v), ?_, ?_⟩
  · intro i
    exact ⟨(ha' i).2, (hb' i).2, by
      rw [Path.range_segment]
      exact hconv.segment_subset (ha' i).1 (hb' i).1⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro z ⟨t, ht⟩ ⟨u, hu⟩
    have heq := ht.trans hu.symm
    have hformula (i : Fin n) (t : unitInterval) :
        Path.segment (a + r i • v) (b + r i • v) t =
          a + (t : ℝ) • (b-a) + r i • v := by
      simp only [Path.segment_apply, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [hformula, hformula] at heq
    have heq' : (t : ℝ) • (b-a) + r i • v = (u : ℝ) • (b-a) + r j • v := by
      apply add_left_cancel (a := a)
      simpa only [add_assoc] using heq
    have hrEq := (hv.eq_of_pair heq').2
    apply hij
    apply Fin.ext
    have : (i.val : ℝ) = j.val := by
      dsimp [r] at hrEq
      have := (div_left_inj' hn.ne').mp hrEq
      nlinarith
    exact_mod_cast this

/-- A nonzero difference in a continuous family persists on a closed base
ball and on arbitrarily many disjoint parallel paths in the stable parameter.
The base radius and positive endpoint gap are chosen before the path count,
so the eventual integral contradiction has one fixed positive-area base.

Source: agent-written refinement for the same Ghys Proposition 4.1 argument.
Continuity of the distance of the two evaluations gives an open product
neighborhood on which it exceeds half its initial value. Choose a positive
closed base ball in the first factor and endpoint neighborhoods in the other
two factors. The preceding theorem gives any requested number of disjoint
segments between these endpoint neighborhoods; the uniform half-gap holds
on the same base ball for every member of every such finite family. -/
theorem continuous_family_parallel_paths_uniform_gap
    {X E Y : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [PseudoMetricSpace Y] (hdim : 1 < Module.finrank ℝ E)
    (V : Set X) (U : Set E) (hV : IsOpen V) (hU : IsOpen U) (hconv : Convex ℝ U)
    (S : X × E → Y) (hS : ContinuousOn S (V ×ˢ U))
    (z₀ : X) (hz₀ : z₀ ∈ V) (a b : E) (ha : a ∈ U) (hb : b ∈ U)
    (hgap : 0 < dist (S (z₀,a)) (S (z₀,b))) :
    ∃ r η : ℝ, 0 < r ∧ closedBall z₀ r ⊆ V ∧ 0 < η ∧
      ∀ n : ℕ, ∃ (x y : Fin n → E) (γ : ∀ i, Path (x i) (y i)),
        (∀ i, range (γ i) ⊆ U) ∧
        Pairwise (fun i j ↦ Disjoint (range (γ i)) (range (γ j))) ∧
        ∀ z ∈ closedBall z₀ r, ∀ i,
          η ≤ dist (S (z,x i)) (S (z,y i)) := by
  let Ω : Set (X × (E × E)) := V ×ˢ (U ×ˢ U)
  let G : X × (E × E) → ℝ := fun p ↦ dist (S (p.1,p.2.1)) (S (p.1,p.2.2))
  have hSa : ContinuousOn (fun p : X × (E × E) ↦ S (p.1,p.2.1)) Ω :=
    hS.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
      (fun p hp ↦ ⟨hp.1,hp.2.1⟩)
  have hSb : ContinuousOn (fun p : X × (E × E) ↦ S (p.1,p.2.2)) Ω :=
    hS.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
      (fun p hp ↦ ⟨hp.1,hp.2.2⟩)
  have hG : ContinuousOn G Ω := continuous_dist.comp_continuousOn (hSa.prodMk hSb)
  let η := dist (S (z₀,a)) (S (z₀,b)) / 2
  have hη : 0 < η := half_pos hgap
  let W : Set (X × (E × E)) := Ω ∩ G ⁻¹' Ioi η
  have hW : IsOpen W := hG.isOpen_inter_preimage (hV.prod (hU.prod hU)) isOpen_Ioi
  have hpW : (z₀,(a,b)) ∈ W := ⟨⟨hz₀,ha,hb⟩,half_lt_self hgap⟩
  obtain ⟨Z,N,hZ,hN,hzZ,habN,hZN⟩ := isOpen_prod_iff.mp hW z₀ (a,b) hpW
  obtain ⟨N₀,N₁,hN₀,hN₁,haN,hbN,hNN⟩ := isOpen_prod_iff.mp hN a b habN
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hZ z₀ hzZ
  have hclosed : closedBall z₀ (R/2) ⊆ Z :=
    (closedBall_subset_ball (half_lt_self hR)).trans hball
  refine ⟨R/2,η,half_pos hR,?_,hη,?_⟩
  · intro z hz
    exact (hZN (show (z,(a,b)) ∈ Z ×ˢ N from ⟨hclosed hz,habN⟩)).1.1
  · intro n
    have hab : a ≠ b := by
      intro he
      subst b
      simp at hgap
    obtain ⟨x,y,γ,hends,hdis⟩ := parallel_paths_convex_open hdim U N₀ N₁ hU hconv
      hN₀ hN₁ a b hab ⟨ha,haN⟩ ⟨hb,hbN⟩ n
    refine ⟨x,y,γ,fun i ↦ (hends i).2.2,hdis,?_⟩
    intro z hz i
    exact ((hZN (show (z,(x i,y i)) ∈ Z ×ˢ N from
      ⟨hclosed hz,hNN ⟨(hends i).1,(hends i).2.1⟩⟩)).2 :
      η < dist (S (z,x i)) (S (z,y i))).le

end HolomorphicAnosov
