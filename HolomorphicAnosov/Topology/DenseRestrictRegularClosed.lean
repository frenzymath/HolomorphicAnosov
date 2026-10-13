import Mathlib.Topology.Constructions

/-!
# Restricting a dense subset to a regular closed set

An explicit topological step in Bowen, *Markov Partitions and Minimal Sets for
Axiom A Diffeomorphisms* (1970), Lemma 2, pp. 908–909: avoidance in a full plaque
restricts densely to a regular closed rectangle slice. The proof below is an
agent-written expansion of this restriction, using only Mathlib topology.
-/

namespace HolomorphicAnosov

open Set

/-- Any dense subset restricts densely to a regular closed set, with its inherited topology.

Source: agent expansion of the regular-closed slice restriction in Bowen (1970b),
Lemma 2, pp. 908–909. Given a nonempty relatively open W in A, choose its ambient
open representative O and a point z in W. Since A is the closure of its interior,
O meets interior A. This is a nonempty ambient open intersection, so density of V
gives a point in O, interior A, and V. It therefore belongs to W and the pullback
of V. The argument includes empty A and requires neither separation nor compactness. -/
theorem dense_restrict_regular_closed
    {X : Type*} [TopologicalSpace X] (A V : Set X)
    (hA : A = closure (interior A)) (hV : Dense V) :
    Dense ((Subtype.val : A → X) ⁻¹' V) := by
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  obtain ⟨z, hz⟩ := hWne
  have hzO : z.val ∈ O := by
    change z ∈ Subtype.val ⁻¹' O
    rwa [hOW]
  have hzA : z.val ∈ closure (interior A) := hA ▸ z.property
  obtain ⟨y, hyO, hyA⟩ := mem_closure_iff.mp hzA O hO hzO
  obtain ⟨t, ⟨htO, htA⟩, htV⟩ := hV.inter_open_nonempty
    (O ∩ interior A) (hO.inter isOpen_interior) ⟨y, hyO, hyA⟩
  refine ⟨⟨t, interior_subset htA⟩, ?_, htV⟩
  rw [← hOW]
  exact htO

end HolomorphicAnosov

