import HolomorphicAnosov.Geometry.IdealTriangleReflectionData
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace HolomorphicAnosov.IdealDiskTriangle

/-- Prefixing a list preserves deletion of an immediate backtrack. -/
lemma reducesItinerary_cons (A : Finset ℂ) {L K : List (Finset ℂ)}
    (h : reducesItinerary L K) : reducesItinerary (A :: L) (A :: K) := by
  induction h with
  | refl => exact .refl
  | @tail L K h hLK ih =>
    apply ih.tail
    obtain ⟨P, Q, B, C, rfl, rfl⟩ := hLK
    exact ⟨A :: P, Q, B, C, rfl, rfl⟩

/-- An acyclic graph walk reduces to a simple path by deleting immediate backtracks, with the same deletion process on any list of physical labels. (Epstein–Petronio, Def. 4.2) -/
theorem acyclic_walk_reduces_physical_itinerary
    {α : Type*} {G : SimpleGraph α} (hG : G.IsAcyclic) (f : α → Finset ℂ)
    {a b : α} (p : G.Walk a b) :
    ∃ q : G.Walk a b, q.IsPath ∧
      reducesItinerary (p.support.map f) (q.support.map f) := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp, .refl⟩
  | @cons a b c hab p ih =>
    obtain ⟨q, hq, hr⟩ := ih
    have hprefix := reducesItinerary_cons (f a) hr
    by_cases ha : a ∈ q.support
    · have heq := hG.eq_snd_of_adj_start hq hab.symm ha
      cases q with
      | nil => exact (hab.ne (by simpa using heq)).elim
      | @cons b d c hbd q =>
        have had : a = d := by simpa using heq
        subst d
        refine ⟨q, hq.of_cons, hprefix.trans ?_⟩
        apply Relation.ReflTransGen.single
        refine ⟨[], (q.support.map f).tail, f a, f b, ?_, ?_⟩
        · cases q <;> simp
        · cases q <;> simp
    · exact ⟨.cons hab q, hq.cons ha, hprefix⟩

/-- Every literal reflection itinerary lifts to a graph walk once orbit preservation and equality between reflection steps and geometric adjacency have been established. -/
lemma itinerary_lifts_to_walk (V : VertexTriple)
    (hpreserve : ∀ W : Finset ℂ, reachable V.val W → W.card = 3 ∧ ∀ p ∈ W, ‖p‖ = 1)
    (hstep : ∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B)
    {A B : ReachedTriangle V} {L : List (Finset ℂ)}
    (hL : isItinerary A.val.val B.val.val L) :
    ∃ p : (dualGraph V).Walk A B, p.support.map (fun A ↦ A.val.val) = L := by
  classical
  induction L generalizing A with
  | nil => exact (hL.1 rfl).elim
  | cons X L ih =>
    have hX : X = A.val.val := by simpa using hL.2.1
    subst X
    cases L with
    | nil =>
      have hAB : A = B := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using hL.2.2.1
      subst B
      exact ⟨.nil, rfl⟩
    | cons Y L =>
      have hAY : reflectionStep A.val.val Y := hL.2.2.2.rel
      have hreach : reachable V.val Y := A.property.tail hAY
      let C : ReachedTriangle V := ⟨⟨Y, hpreserve Y hreach⟩, hreach⟩
      have htail : isItinerary C.val.val B.val.val (Y :: L) := by
        refine ⟨List.cons_ne_nil _ _, rfl, ?_, hL.2.2.2.of_cons⟩
        simpa using hL.2.2.1
      obtain ⟨p, hp⟩ := ih htail
      exact ⟨.cons ((hstep A C).mp hAY) p, by simpa using congrArg (A.val.val :: ·) hp⟩

/-- A graph walk lists a literal reflection itinerary when graph adjacency is identified with a reflection step. -/
lemma walk_support_isItinerary (V : VertexTriple)
    (hstep : ∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B)
    {A B : ReachedTriangle V} (p : (dualGraph V).Walk A B) :
    isItinerary A.val.val B.val.val (p.support.map (fun A ↦ A.val.val)) := by
  induction p with
  | nil => simp [isItinerary]
  | @cons A B C h p ih =>
    refine ⟨by simp, by simp, ?_, ?_⟩
    · cases p with
      | nil => simp
      | cons h' p => simpa using ih.2.2.1
    · cases p with
      | nil => simpa using (hstep A B).mpr h
      | cons h' p =>
        simpa only [SimpleGraph.Walk.support_cons, List.map_cons, List.isChain_cons_cons] using
          And.intro ((hstep A B).mpr h) ih.2.2.2

/-- Tree adjacency and orbit preservation imply the unique simple itinerary and the immediate-backtrack normal form of every itinerary. -/
theorem reflection_itinerary_normal_form_of_tree (V : VertexTriple)
    (hpreserve : ∀ W : Finset ℂ, reachable V.val W → W.card = 3 ∧ ∀ p ∈ W, ‖p‖ = 1)
    (hstep : ∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B)
    (htree : (dualGraph V).IsTree) (W : ReachedTriangle V) :
    (∃! P : (dualGraph V).Walk (initialTriangle V) W, P.IsPath) ∧
      ∃ L : List (Finset ℂ), isSimpleItinerary V.val W.val.val L ∧
        (∀ K : List (Finset ℂ), isSimpleItinerary V.val W.val.val K → K = L) ∧
        (∀ K : List (Finset ℂ), isItinerary V.val W.val.val K → reducesItinerary K L) ∧
        ∀ P : (dualGraph V).Walk (initialTriangle V) W, P.IsPath →
          P.support.map (fun A ↦ A.val.val) = L := by
  classical
  have hpath := htree.existsUnique_path (initialTriangle V) W
  obtain ⟨p, hp, huniq⟩ := hpath
  have hinj : Function.Injective (fun A : ReachedTriangle V ↦ A.val.val) := by
    intro A B h
    exact Subtype.ext (Subtype.ext h)
  refine ⟨⟨p, hp, huniq⟩, p.support.map (fun A : ReachedTriangle V ↦ A.val.val),
    ⟨walk_support_isItinerary V hstep p, ?_⟩, ?_, ?_, ?_⟩
  · exact (List.nodup_map_iff hinj).mpr (p.isPath_def.mp hp)
  · intro K hK
    obtain ⟨q, hq⟩ := itinerary_lifts_to_walk V hpreserve hstep (A := initialTriangle V) (B := W) hK.1
    have hqpath : q.IsPath := q.isPath_def.mpr
      ((List.nodup_map_iff hinj).mp (hq.symm ▸ hK.2))
    exact hq.symm.trans (congrArg (fun q ↦ q.support.map (fun A ↦ A.val.val)) (huniq q hqpath))
  · intro K hK
    obtain ⟨q, hq⟩ := itinerary_lifts_to_walk V hpreserve hstep (A := initialTriangle V) (B := W) hK
    obtain ⟨r, hr, hred⟩ := acyclic_walk_reduces_physical_itinerary htree.2
      (fun A ↦ A.val.val) q
    rwa [huniq r hr, hq] at hred
  · intro q hq
    exact congrArg (fun q ↦ q.support.map (fun A ↦ A.val.val)) (huniq q hq)

end HolomorphicAnosov.IdealDiskTriangle
