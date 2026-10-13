import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Trace

open CategoryTheory
open scoped BigOperators
noncomputable section
universe u
namespace HolomorphicAnosov

/-- An additive endomorphism of the finite winding lattice has a unique integer
 column matrix. Source: the integer-coordinate expansion in Hatcher pp.166–168;
 `toMatrix'` is the actual coordinate map, with no basis assumed as input. -/
theorem winding_endomorphism_matrix (n : ℕ)
    (f : Multiplicative (Fin n → ℤ) →* Multiplicative (Fin n → ℤ)) :
    ∃! A : Matrix (Fin n) (Fin n) ℤ,
      ∀ z : Fin n → ℤ, (f (Multiplicative.ofAdd z)).toAdd = A.mulVec z := by
  let L : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) := f.toAdditiveRight.toIntLinearMap
  refine ⟨L.toMatrix', ?_, ?_⟩
  · intro z
    exact (L.toMatrix'_mulVec z).symm
  · intro B hB
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro z
    exact (hB z).symm.trans (L.toMatrix'_mulVec z).symm


end HolomorphicAnosov
