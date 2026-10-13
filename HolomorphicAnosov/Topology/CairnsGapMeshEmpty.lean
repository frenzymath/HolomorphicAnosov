import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap

/-!
# Empty residual-gap mesh

Source: Cairns (1951), §4(C), pp.864–865. The recurrence declares the mesh
zero when no residual arc exists. This helper records that convention directly
from the literal `CairnsCircleGap.mesh` definition, including arbitrary sets and
empty residual families.
-/
namespace HolomorphicAnosov.Topology.Plane
open Set CairnsCircleGap

/-- If a retained contact set has no residual circular gap, its normalized mesh
is exactly zero. This is the finite-termination branch of Cairns's mesh estimate. -/
theorem cairns_gap_mesh_eq_zero_of_no_gap {S : Set Circle}
    (hgap : ¬ ∃ g : CairnsCircleGap, g.IsGapOf S) :
    CairnsCircleGap.mesh S = 0 := by
  unfold CairnsCircleGap.mesh
  have hset : CairnsCircleGap.normalizedLength ''
      {g : CairnsCircleGap | g.IsGapOf S} = (∅ : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact False.elim (hgap ⟨g, hg⟩)
    · intro hx
      simp at hx
  rw [hset]
  simp

end HolomorphicAnosov.Topology.Plane
