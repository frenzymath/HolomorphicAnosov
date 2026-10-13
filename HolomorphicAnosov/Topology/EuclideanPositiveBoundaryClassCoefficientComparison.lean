import HolomorphicAnosov.Topology.EuclideanPositiveLocalConnecting
import HolomorphicAnosov.Topology.EuclideanPositiveBoundaryClassCoefficientComparisonConstruction
import Mathlib.Algebra.Module.Submodule.Equiv

noncomputable section
namespace HolomorphicAnosov

/-- The algebraic transport step once the source orientation comparison is known.

The source calculation is Hatcher, *Algebraic Topology*, Corollary 2.14 p.114,
the relative connecting sequence pp.115--118, and the local orientation
convention pp.233--234 (with the ordered simplex convention p.269). Radial
deformation gives an integral reduced homology group isomorphic to `ℤ`, while
the connecting map sends the coefficient-one affine simplex to its
alternating face chain. The ordered simplicial boundary equations say that
this chain has coefficient exactly `1` in that copy of `ℤ`; `n = 0` is the
augmentation-kernel calculation for the two-point sphere. Given the resulting
equivalence `e`, the present theorem is an integer-module argument. -/
theorem euclideanPositiveBoundaryClass_bijective_of_coefficient_equiv
    (n : ℕ)
    (e : integralReducedSingularHomology
        (TopCat.of ↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)) n ≃ₗ[ℤ] ℤ)
    (he : e (euclideanPositiveBoundaryClass n) = 1) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ _
      (euclideanPositiveBoundaryClass n)) := by
  let g := LinearMap.toSpanSingleton ℤ _ (euclideanPositiveBoundaryClass n)
  have hinj : Function.Injective g := by
    intro a b hab
    simpa [g, LinearMap.toSpanSingleton_apply, map_zsmul, he] using congrArg e hab
  have hsurj : Function.Surjective g := by
    intro y
    refine ⟨e y, ?_⟩
    apply e.injective
    simp [g, LinearMap.toSpanSingleton_apply, he]
  exact ⟨hinj, hsurj⟩

/-- The source-backed orientation comparison for the explicit boundary cycle.

This is the remaining formalization obligation from Hatcher's local
orientation construction (Corollary 2.14 p.114; relative connecting maps
pp.115--118; local orientations pp.233--234). For positive `n`, identify the
punctured Euclidean space with a sphere by radial deformation and use the long
exact sequence of the point pair. The ordered affine simplex has edge matrix
`I + 11ᵀ`, with positive determinant `n+1`, so its coefficient-one relative
class is positively oriented. The connecting map is the alternating signed
face chain already defined in `euclideanPositiveBoundaryClass`; the
simplicial cycle equations force coefficient `1`. The canonical
simplicial-to-singular comparison then gives an integral linear equivalence
to `ℤ` taking this exact class to `1`. In dimension zero, the same conclusion
is the explicit augmentation-kernel calculation for the two points of the
punctured line. The Lean development has the radial/sphere concentration and
the connecting-chain identity, but not this final normalization calculation,
so this theorem records the source obligation rather than choosing an
unrelated generator. -/
theorem euclideanPositiveBoundaryClass_coefficient_equiv (n : ℕ) :
    ∃ e : integralReducedSingularHomology
        (TopCat.of ↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)) n ≃ₗ[ℤ] ℤ,
      e (euclideanPositiveBoundaryClass n) = 1 := by
  exact euclideanPositiveBoundaryClass_coefficient_equiv_construction n trivial

end HolomorphicAnosov
