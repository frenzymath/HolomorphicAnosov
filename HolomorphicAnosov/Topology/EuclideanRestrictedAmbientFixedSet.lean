import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition
import HolomorphicAnosov.Topology.EuclideanSupportOrientationNaturality
import HolomorphicAnosov.Topology.EuclideanRestrictedMap

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- Source: Dold (1965), §§1.1–1.3, p.1.
Dold restriction/empty-support calculation. The pair square commutes and supported orientations are natural under inclusion; the empty class maps to zero. -/
theorem restricted_ambient_fixedSet_eq
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n)))
    (V : Opens (EuclideanSpace ℝ (Fin n))) (hVU : V ≤ U)
    (hV : ∀ x ∈ euclideanFixedSet f, x.1 ∈ V) :
    euclideanAmbientFixedSet (restrictedMap f V hVU) = euclideanAmbientFixedSet f := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, hVU x.2⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, hV x hx⟩, hx, rfl⟩

end HolomorphicAnosov
