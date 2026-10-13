import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition
import HolomorphicAnosov.Topology.EuclideanSupportOrientationNaturality

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- Source: Dold (1965), §§1.1–1.3, p.1.
The restriction of a continuous map on an open Euclidean domain U to an open subset V is its composition with the inclusion of V into U.
Proof:  -/
def restrictedMap {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n)))
    (V : Opens (EuclideanSpace ℝ (Fin n))) (hVU : V ≤ U) :
    C(V, EuclideanSpace ℝ (Fin n)) :=
  ⟨fun x ↦ f ⟨x.1, hVU x.2⟩,
   f.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

end HolomorphicAnosov
