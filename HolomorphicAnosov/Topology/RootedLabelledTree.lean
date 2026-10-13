import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph SimpleGraph.Walk

namespace HolomorphicAnosov

/-- A rooted simple labelled tree has one parent edge for every nonroot vertex.
The depth is the length of the unique finite path to the root. No cardinality
hypothesis is imposed. Source: the explicit first-dart bijection proof in
Mathlib `SimpleGraph.IsTree.card_edgeFinset`, Acyclic.lean, with its surrounding
finite-cardinality calculation removed; Hatcher Proposition 1A.1, p.84, uses
these parent edges to form rooted layers. The proof retains original edge
labels through `Graph.Simple.eq_of_isLink` and original vertices throughout. -/
theorem rooted_labelled_tree_data
    {V E : Type*} (G : Graph V E) [G.Simple]
    (hG : G.toSimpleGraph.IsTree) (r : G.vertexSet) :
    ∃ (d : G.vertexSet → ℕ)
      (parent : {v : G.vertexSet // v ≠ r} → G.vertexSet)
      (edge : {v : G.vertexSet // v ≠ r} ≃ G.edgeSet),
      d r = 0 ∧
      (∀ v, d (parent v) + 1 = d v.val) ∧
      (∀ v, G.IsLink (edge v).val (parent v).val v.val.val) := by
  classical
  let H := G.toSimpleGraph
  choose f hf hu using (hG.existsUnique_path · r)
  let parent := fun v : {v : G.vertexSet // v ≠ r} => (f v.val).snd
  have hn : ∀ v : {v : G.vertexSet // v ≠ r}, ¬ (f v.val).Nil :=
    fun v => not_nil_of_ne v.property
  have hd : ∀ v : {v : G.vertexSet // v ≠ r},
      (f (parent v)).length + 1 = (f v.val).length := by
    intro v
    have heq := hu (parent v) (f v.val).tail (hf v.val).tail
    rw [← heq]
    exact length_tail_add_one (hn v)
  have links : ∀ v : {v : G.vertexSet // v ≠ r},
      ∃ e, G.IsLink e v.val.val (parent v).val := by
    intro v
    exact (G.toSimpleGraph_adj_iff v.val (parent v)).mp ((f v.val).adj_snd (hn v))
  choose edge hlink using links
  let chosen : {v : G.vertexSet // v ≠ r} → G.edgeSet :=
    fun v => ⟨edge v, (hlink v).edge_mem⟩
  have hinj : Function.Injective chosen := by
    intro a b hab
    have he : edge a = edge b := congrArg Subtype.val hab
    have hablink := (hlink a).eq_and_eq_or_eq_and_eq (he ▸ hlink b)
    rcases hablink with ⟨hab, _⟩ | ⟨hap, hpb⟩
    · exact Subtype.ext (Subtype.ext hab)
    · have hap' : a.val = parent b := Subtype.ext hap
      have hpb' : parent a = b.val := Subtype.ext hpb
      have ha := hd a
      have hb := hd b
      rw [hpb'] at ha
      rw [← hap'] at hb
      omega
  have hsurj : Function.Surjective chosen := by
    intro e
    obtain ⟨x, y, he⟩ := G.exists_isLink_of_mem_edgeSet e.property
    let a : G.vertexSet := ⟨x, he.left_mem⟩
    let b : G.vertexSet := ⟨y, he.right_mem⟩
    have hab : H.Adj a b := (G.toSimpleGraph_adj_iff a b).mpr he.adj
    suffices ∀ (a b : G.vertexSet), H.Adj a b →
        (f a).length ≤ (f b).length →
        ∃ (hb : b ≠ r), parent ⟨b, hb⟩ = a by
      rcases le_total (f a).length (f b).length with hablen | hbalen
      · obtain ⟨hb, hp⟩ := this a b hab hablen
        refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
        exact (hlink ⟨b, hb⟩).eq (by simpa only [hp] using he.symm)
      · obtain ⟨ha, hp⟩ := this b a hab.symm hbalen
        refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
        exact (hlink ⟨a, ha⟩).eq (by simpa only [hp] using he)
    intro x y h hlen
    have hyr : y ≠ r := by
      intro hroot
      subst y
      rw [← hu r nil IsPath.nil, length_nil,
        ← hu x (.cons h .nil) (IsPath.nil.cons (by simpa using h.ne)),
        length_cons, length_nil] at hlen
      omega
    have hpath : (Walk.cons h.symm (f x)).IsPath := by
      refine (cons_isPath_iff _ _).2 ⟨hf x, ?_⟩
      intro hy
      have htake : (f x).takeUntil y hy = .cons h .nil := by
        apply (hG.existsUnique_path x y).unique ((hf x).takeUntil hy)
        simp [h.ne]
      rw [← take_spec _ hy] at hlen
      simp [htake, hu y _ ((hf x).dropUntil hy)] at hlen
    refine ⟨hyr, ?_⟩
    change (f y).snd = x
    rw [← hu y (.cons h.symm (f x)) hpath]
    simp
  refine ⟨fun v => (f v).length, parent, Equiv.ofBijective chosen ⟨hinj, hsurj⟩,
    ?_, hd, ?_⟩
  · change (f r).length = 0
    rw [← hu r nil IsPath.nil]
    rfl
  · intro v
    exact (hlink v).symm

end HolomorphicAnosov
