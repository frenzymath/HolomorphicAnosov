import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Compactness.Compact

/-!
Hatcher's finite compact convex union induction. (Hatcher, Lemma 3.27)
-/

namespace HolomorphicAnosov

/-- A property true on compact convex sets and closed under the three-input union rule extends to every finite union of compact convex sets. (Hatcher, Lemma 3.27) -/
theorem finite_compact_convex_union_induction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Set E → Prop)
    (hconvex : ∀ A, IsCompact A → Convex ℝ A → P A)
    (hunion : ∀ A B, IsCompact A → IsCompact B → P A → P B → P (A ∩ B) → P (A ∪ B))
    {ι : Type*} (s : Finset ι) (F : ι → Set E)
    (hc : ∀ i ∈ s, IsCompact (F i)) (hv : ∀ i ∈ s, Convex ℝ (F i)) :
    P (⋃ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty =>
    simpa using hconvex ∅ isCompact_empty (convex_empty : Convex ℝ (∅ : Set E))
  | @insert a s ha ih =>
    have hcA := hc a (Finset.mem_insert_self a s)
    have hvA := hv a (Finset.mem_insert_self a s)
    have hcS (i) (hi : i ∈ s) := hc i (Finset.mem_insert_of_mem hi)
    have hvS (i) (hi : i ∈ s) := hv i (Finset.mem_insert_of_mem hi)
    have hrest := ih F hcS hvS
    have hinter : P (F a ∩ ⋃ i ∈ s, F i) := by
      have h := ih (fun i ↦ F a ∩ F i)
        (fun i hi ↦ hcA.inter_right (hcS i hi).isClosed)
        (fun i hi ↦ hvA.inter (hvS i hi))
      simpa only [Set.inter_iUnion] using h
    have hcRest : IsCompact (⋃ i ∈ s, F i) := s.isCompact_biUnion hcS
    simpa only [Finset.set_biUnion_insert] using
      hunion (F a) (⋃ i ∈ s, F i) hcA hcRest (hconvex (F a) hcA hvA) hrest hinter

end HolomorphicAnosov

