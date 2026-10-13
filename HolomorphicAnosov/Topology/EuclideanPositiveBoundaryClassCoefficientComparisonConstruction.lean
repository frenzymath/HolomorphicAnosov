import HolomorphicAnosov.Topology.EuclideanPositiveBoundaryClassCoefficientFromLocalGenerator
import HolomorphicAnosov.Topology.EmbeddedSimplexLocalClassGenerator
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexEmbeddedInterior
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexFaceAvoidsZero

noncomputable section
namespace HolomorphicAnosov

/--
Named Hatcher coefficient-one construction for the prescribed alternating
boundary cycle.  Radial deformation identifies punctured Euclidean space with
the unit sphere; the ordered simplex boundary is the positively oriented sphere
generator, so its coefficient is one.

Source: Hatcher, *Algebraic Topology*, Corollary 2.14 p.114, relative exact
sequence pp.115--118, local orientation pp.233--234, and ordered simplex
orientation p.269.  The remaining formal step is the chain-level simplicial to
singular comparison carrying the displayed alternating boundary cycle to the
positive sphere generator.
-/
theorem euclideanPositiveBoundaryClass_coefficient_equiv_construction (n : ℕ)
    (_haux : True) :
    ∃ e : integralReducedSingularHomology
        (TopCat.of ↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)) n ≃ₗ[ℤ] ℤ,
      e (euclideanPositiveBoundaryClass n) = 1 := by
  apply euclideanPositiveBoundaryClass_coefficient_equiv_from_local_generator n
  have hgeom := embeddedSimplex_localClass_free_generator n (euclideanPositiveSimplex (n + 1))
    (euclideanPositiveSimplex_embedded_interior (n + 1)).1
    (euclideanPositiveSimplex_embedded_interior (n + 1)).2
    (euclideanPositiveSimplex_face_avoids_zero n)
  exact hgeom

end HolomorphicAnosov
