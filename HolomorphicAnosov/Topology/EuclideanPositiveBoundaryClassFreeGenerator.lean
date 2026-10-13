import HolomorphicAnosov.Topology.EuclideanPositiveBoundaryClassCoefficientComparison
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Freeness of the explicit punctured boundary class

This helper isolates the only postponed positive-dimensional step in the
specified Euclidean local-coordinate construction.  The connecting theorem
already identifies the fixed local class with the explicit alternating face
cycle.  What remains is the source calculation that this cycle is primitive
in reduced integral homology of the punctured Euclidean space.
-/

noncomputable section

namespace HolomorphicAnosov

/-- The explicit alternating boundary class is a free integral generator.

Source: Hatcher, *Algebraic Topology*, Corollary 2.14 p.114, the relative
long exact sequence pp.115--118, and the local-orientation convention
pp.233--234; the ordered simplex convention is p.269.

Proof plan: the prescribed simplex has edge matrix `I + 11ᵀ`, hence positive
determinant `n+1`, and its faces avoid the origin.  Excision and the relative
connecting isomorphism identify its local class with the displayed alternating
boundary cycle in the punctured space.  Radial deformation identifies the
punctured space with the sphere; reduced sphere homology is infinite cyclic in
degree `n`, and the simplicial boundary calculation on the ordered simplex
shows that the alternating face cycle has coefficient `1` in that copy of
`ℤ`.  Equivalently, the face-cycle equations force every coefficient to be the
same signed integer, so no nontrivial integer divides this cycle.  Thus scalar
multiplication by this exact class is injective and surjective.  The case
`n = 0` is the reduced `H₀` of the two-point punctured line and uses the
augmentation-kernel generator.  This theorem intentionally keeps the exact
class supplied by `euclideanPositiveBoundaryClass`; it does not choose an
unrelated generator or add an orientation hypothesis.
-/
theorem euclideanPositiveBoundaryClass_free_generator (n : ℕ) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ _
      (euclideanPositiveBoundaryClass n)) := by
  obtain ⟨e, he⟩ := euclideanPositiveBoundaryClass_coefficient_equiv n
  exact euclideanPositiveBoundaryClass_bijective_of_coefficient_equiv n e he

end HolomorphicAnosov
