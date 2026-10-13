import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionSideG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionTriangleTransportVertexG6

noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- Reflection carries an actual ideal triangle carrier to its reflected carrier. (Lyubich, Ex. 2.49(i); Epstein–Petronio, Def. 2.1) -/
theorem idealDiskSideReflection_triangle_image_g6 (V : VertexTriple)
    {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (hpV : p ∈ V.val) (hqV : q ∈ V.val) :
    idealDiskSideReflection p q '' triangle V.val =
      triangle (reflectedVertices V.val p q) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (idealDiskSideReflection_triangle_transport_vertex_g6 V hp hq hpq hpV hqV w).1 hw
  · intro hz
    have hz' := (idealDiskSideReflection_triangle_transport_vertex_g6 V hp hq hpq hpV hqV z).2 hz
    exact ⟨idealDiskSideReflection p q z,
      hz',
      idealDiskSideReflection_involutive_disk_g6 hp hq hpq z hz.1⟩

end HolomorphicAnosov.IdealDiskTriangle
