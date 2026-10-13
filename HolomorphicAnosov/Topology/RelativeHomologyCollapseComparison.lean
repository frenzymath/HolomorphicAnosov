import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence

/-!
# Comparing relative homology by closed-subspace collapse

DAG node: `topo.relative_homology_closed_embedding_collapse_g20`.
Source: Hatcher, *Algebraic Topology*, Proposition 2.22 p.124, applied
naturally to a closed embedding covering the complement of the collapsed set.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- Collapsing a closed subset is a closed map: the saturation of a closed
set is either itself or its union with the collapsed subset. -/
theorem isClosedMap_collapse_of_isClosed {X : Type} [TopologicalSpace X]
    (A : Set X) (hA : IsClosed A) : IsClosedMap (GoodPair.collapse A) := by
  intro S hS
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  change IsClosed (GoodPair.collapse A ⁻¹' (GoodPair.collapse A '' S))
  by_cases h : ∃ x ∈ S, x ∈ A
  · have he : GoodPair.collapse A ⁻¹' (GoodPair.collapse A '' S) = S ∪ A := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        rcases Quotient.exact hyx with he | ⟨_, hx⟩
        · exact Or.inl (he ▸ hy)
        · exact Or.inr hx
      · rintro (hx | hx)
        · exact ⟨x, hx, rfl⟩
        · obtain ⟨a, ha, haA⟩ := h
          exact ⟨a, ha, Quotient.sound (Or.inr ⟨haA, hx⟩)⟩
    rw [he]
    exact hS.union hA
  · have he : GoodPair.collapse A ⁻¹' (GoodPair.collapse A '' S) = S := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        rcases Quotient.exact hyx with he | ⟨hyA, _⟩
        · exact he ▸ hy
        · exact False.elim (h ⟨y, hy, hyA⟩)
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [he]
    exact hS

/-- A map of pairs induces the literal map between their collapsed spaces. -/
def subspaceCollapseMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) :
    GoodPair.Collapsed A → GoodPair.Collapsed B :=
  Quotient.map f (by
    intro x y h
    rcases h with rfl | ⟨hx, hy⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hf hx, hf hy⟩)

lemma subspaceCollapseMap_continuous {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) :
    Continuous (subspaceCollapseMap f A B hf) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact (GoodPair.collapse B).continuous.comp f.continuous

/-- A closed embedding covering the target outside its collapsed subset
identifies the quotient pairs. This is the topological comparison used when
one facet remains after the other facets have been collapsed. -/
theorem subspaceCollapseMap_isHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B)
    (he : Topology.IsClosedEmbedding f) (hA : A.Nonempty) (hB : IsClosed B)
    (hpre : ∀ x, f x ∈ B → x ∈ A) (hcover : ∀ y, y ∈ B ∨ y ∈ Set.range f) :
    IsHomeomorph (subspaceCollapseMap f A B hf) := by
  have hs : Function.Surjective (GoodPair.collapse B ∘ f) := by
    intro z
    induction z using Quotient.inductionOn with | h y =>
      rcases hcover y with hy | ⟨x, rfl⟩
      · obtain ⟨a, ha⟩ := hA
        exact ⟨a, Quotient.sound (Or.inr ⟨hf ha, hy⟩)⟩
      · exact ⟨x, rfl⟩
  have hq : Topology.IsQuotientMap (GoodPair.collapse B ∘ f) :=
    ((isClosedMap_collapse_of_isClosed B hB).comp he.isClosedMap).isQuotientMap
      ((GoodPair.collapse B).continuous.comp f.continuous) hs
  apply isHomeomorph_iff_isQuotientMap_injective.mpr
  refine ⟨isQuotientMap_quotient_mk'.of_comp_isQuotientMap hq, ?_⟩
  intro z w
  induction z using Quotient.inductionOn with | h x =>
    induction w using Quotient.inductionOn with | h y =>
      intro h
      apply Quotient.sound
      rcases Quotient.exact h with heq | ⟨hx, hy⟩
      · exact Or.inl (he.injective heq)
      · exact Or.inr ⟨hpre x hx, hpre y hy⟩

lemma subspaceCollapseMap_mem_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B)
    (hpre : ∀ x, f x ∈ B → x ∈ A) (z : GoodPair.Collapsed A) :
    subspaceCollapseMap f A B hf z ∈ GoodPair.collapsedPart B ↔
      z ∈ GoodPair.collapsedPart A := by
  induction z using Quotient.inductionOn with | h x =>
    constructor
    · rintro ⟨y, hy, he⟩
      have hx : f x ∈ B := by
        rcases Quotient.exact he with h | ⟨_, h⟩
        · exact h ▸ hy
        · exact h
      exact ⟨x, hpre x hx, rfl⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨f a, hf ha, congrArg (subspaceCollapseMap f A B hf) he⟩

/-- The closed-embedding quotient comparison, combined with the two good-pair
collapse isomorphisms, identifies the actual relative inclusion map. -/
theorem relative_homology_isIso_of_collapse_comparison
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B)
    (he : Topology.IsClosedEmbedding f) (hA : A.Nonempty) (hB : IsClosed B)
    (hpre : ∀ x, f x ∈ B → x ∈ A) (hcover : ∀ y, y ∈ B ∨ y ∈ Set.range f)
    (R : ModuleCat ℤ) (k : ℕ)
    [IsIso (SSetPair.homologyMap (GoodPair.collapseSingularPairMap (TopCat.of X) A) R k)]
    [IsIso (SSetPair.homologyMap (GoodPair.collapseSingularPairMap (TopCat.of Y) B) R k)] :
    IsIso (SSetPair.homologyMap (singularSubspacePairMap (TopCat.ofHom f) A B hf) R k) := by
  let q := subspaceCollapseMap f A B hf
  let e := (subspaceCollapseMap_isHomeomorph f A B hf he hA hB hpre hcover).homeomorph q
  have hq : Set.MapsTo e (GoodPair.collapsedPart A) (GoodPair.collapsedPart B) := by
    intro z hz
    exact (subspaceCollapseMap_mem_iff f A B hf hpre z).mpr hz
  have hqi : Set.MapsTo e.symm (GoodPair.collapsedPart B) (GoodPair.collapsedPart A) := by
    intro z hz
    apply (subspaceCollapseMap_mem_iff f A B hf hpre (e.symm z)).mp
    change e (e.symm z) ∈ GoodPair.collapsedPart B
    simpa using hz
  let F := singularSubspacePairMap (TopCat.ofHom f) A B hf
  let G := GoodPair.complementPairMap e (GoodPair.collapsedPart A) (GoodPair.collapsedPart B) hq
  have hG : IsIso (SSetPair.homologyMap G R k) :=
    GoodPair.complementPairMap_homology_isIso e _ _ hq hqi R k
  have hcomm : F ≫ GoodPair.collapseSingularPairMap (TopCat.of Y) B =
      GoodPair.collapseSingularPairMap (TopCat.of X) A ≫ G := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
  have hcomp : IsIso (SSetPair.homologyMap F R k ≫
      SSetPair.homologyMap (GoodPair.collapseSingularPairMap (TopCat.of Y) B) R k) := by
    rw [← SSetPair.homologyMap_comp, hcomm, SSetPair.homologyMap_comp]
    infer_instance
  exact (isIso_comp_right_iff _
    (SSetPair.homologyMap (GoodPair.collapseSingularPairMap (TopCat.of Y) B) R k)).mp hcomp

end HolomorphicAnosov
