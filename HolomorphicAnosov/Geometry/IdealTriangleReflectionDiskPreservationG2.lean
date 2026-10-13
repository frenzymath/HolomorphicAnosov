import HolomorphicAnosov.Geometry.IdealTriangleReflectionInvolutionG6

noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- The explicit anti-Möbius side reflection preserves the open disk. (Lyubich, Ex. 2.49(i)) -/
theorem idealDiskSideReflection_mem_disk_g2 {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    ∀ z ∈ disk, idealDiskSideReflection p q z ∈ disk := by
  intro z hz
  exact idealDiskSideReflection_mem_disk_g6 hp hq hpq hz

end HolomorphicAnosov.IdealDiskTriangle
