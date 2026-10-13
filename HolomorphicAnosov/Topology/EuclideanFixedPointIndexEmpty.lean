import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition
import HolomorphicAnosov.Topology.EuclideanSupportOrientationNaturality

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- Source: Dold (1965), §§1.1–1.3, p.1.
Dold restriction/empty-support calculation. The pair square commutes and supported orientations are natural under inclusion; the empty class maps to zero. -/
theorem fixed_index_zero_of_empty
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact (euclideanFixedSet f))
    (hEmpty : euclideanFixedSet f = ∅) :
    euclideanFixedPointIndex f hK = 0 := by
  have hA : euclideanAmbientFixedSet f = (∅ : Set (EuclideanSpace ℝ (Fin n))) := by
    simp [euclideanAmbientFixedSet, hEmpty]
  have hcompact : IsCompact (euclideanAmbientFixedSet f) := hK.image continuous_subtype_val
  have hcontained : euclideanAmbientFixedSet f ⊆ (U : Set _) := by
    rintro x ⟨u, hu, rfl⟩
    exact u.property
  have ho := (show ∀ (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
      (K : Set (EuclideanSpace ℝ (Fin n))), K = ∅ →
      ∀ (hc : IsCompact K) (hs : K ⊆ W),
        euclideanSupportOrientation n W K hW hc hs = 0 from by
      intro W hW K h hc hs
      subst K
      exact euclideanSupportOrientation_empty n W hW)
      (U : Set _) U.isOpen (euclideanAmbientFixedSet f) hA hcompact hcontained
  unfold euclideanFixedPointIndex
  dsimp only
  rw [ho]
  simp only [map_zero]

end HolomorphicAnosov
