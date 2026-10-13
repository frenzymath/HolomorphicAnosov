import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Polygon.Basic

/-!
# Finite simple polygon cycle data

This packages vertex injectivity and the common-endpoint edge-intersection
condition used in Cairns (1951), preliminary §2(B), p.860. Nondegeneracy follows
from injectivity once the cycle has at least two vertices. The remaining lemmas
convert equivalent endpoint formulations and change the cyclic enumeration.
-/

namespace HolomorphicAnosov
open Set

/-- The vertex and edge separation properties used in the finite cycle construction. -/
structure PolygonCycleData {n : ℕ} (p : Polygon ℂ n) : Prop where
  injective : Function.Injective p.vertices
  simple : ∀ i j : Fin n, i ≠ j → p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
    ({p i, p (finRotate n i)} : Set ℂ) ∩ {p j, p (finRotate n j)}

lemma PolygonCycleData.vertex_mem_edge {n : ℕ} {p : Polygon ℂ n}
    (h : PolygonCycleData p) (i j : Fin n) :
    p i ∈ p.edgeSet ℝ j ↔ i = j ∨ i = finRotate n j := by
  constructor
  · intro hi
    by_cases hij : i = j
    · exact Or.inl hij
    have hj := (h.simple i j hij ⟨left_mem_affineSegment ℝ _ _, hi⟩).2
    simpa only [mem_insert_iff, mem_singleton_iff, h.injective.eq_iff] using hj
  · rintro (rfl | rfl)
    · exact left_mem_affineSegment ℝ _ _
    · exact right_mem_affineSegment ℝ _ _

lemma PolygonCycleData.nondegenerate {n : ℕ} {p : Polygon ℂ (n + 2)}
    (h : PolygonCycleData p) : p.HasNondegenerateEdges := by
  intro i he
  have hi := congrArg Fin.val (h.injective he)
  rw [coe_finRotate] at hi
  split_ifs at hi with hil
  · subst i
    simp only [Fin.val_last] at hi
    omega
  · omega

lemma PolygonCycleData.indexed_simple {n : ℕ} {p : Polygon ℂ n}
    (h : PolygonCycleData p) (i j : Fin n) (hij : i ≠ j) :
    p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
      p.vertices '' ({i, finRotate n i} ∩ {j, finRotate n j}) := by
  simpa only [image_inter h.injective, image_pair] using h.simple i j hij

lemma PolygonCycleData.of_indexed {n : ℕ} {p : Polygon ℂ n}
    (hinj : Function.Injective p.vertices)
    (hs : ∀ i j : Fin n, i ≠ j → p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
      p.vertices '' ({i, finRotate n i} ∩ {j, finRotate n j})) : PolygonCycleData p := by
  refine ⟨hinj, ?_⟩
  intro i j hij
  simpa only [image_inter hinj, image_pair] using hs i j hij

lemma PolygonCycleData.reindex {n : ℕ} {p : Polygon ℂ n} (h : PolygonCycleData p)
    (e f : Equiv.Perm (Fin n))
    (he : ∀ i, (e i = f i ∧ e (finRotate n i) = finRotate n (f i)) ∨
      (e i = finRotate n (f i) ∧ e (finRotate n i) = f i)) :
    let q : Polygon ℂ n := ⟨p.vertices ∘ e⟩
    PolygonCycleData q ∧ q.boundary ℝ = p.boundary ℝ := by
  intro q
  have hends (i : Fin n) : ({q i, q (finRotate n i)} : Set ℂ) =
      {p (f i), p (finRotate n (f i))} := by
    rcases he i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp only [q, Function.comp_apply, h₁, h₂]
    exact pair_comm _ _
  have hedge (i : Fin n) : q.edgeSet ℝ i = p.edgeSet ℝ (f i) := by
    rcases he i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp only [Polygon.edgeSet, affineSegment_eq_segment, q, Function.comp_apply, h₁, h₂]
    exact segment_symm ℝ _ _
  refine ⟨⟨h.injective.comp e.injective, ?_⟩, ?_⟩
  · intro i j hij
    simpa only [hedge, hends] using h.simple (f i) (f j) (f.injective.ne hij)
  · ext x
    simp only [Polygon.boundary, mem_iUnion, hedge]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨f i, hi⟩,
      fun ⟨i, hi⟩ ↦ ⟨f.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩⟩

end HolomorphicAnosov
