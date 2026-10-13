import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.Connected.PathConnected

open Set
open scoped Manifold ENNReal
namespace HolomorphicAnosov

/-- Points at finite Riemannian extended distance lie in the same connected component. -/
theorem mem_connectedComponent_of_riemannianEDist_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)]
    {x y : M} (hxy : Manifold.riemannianEDist I x y ≠ ⊤) :
    y ∈ connectedComponent x := by
  have hlt := lt_top_iff_ne_top.mpr hxy
  simp only [Manifold.riemannianEDist, iInf_lt_iff] at hlt
  obtain ⟨γ, _, _⟩ := hlt
  exact pathComponent_subset_component x ⟨γ⟩

end HolomorphicAnosov
