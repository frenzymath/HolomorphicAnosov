import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Closedness of finite cubical subcomplex carriers

Source: Hatcher, *Algebraic Topology*, Appendix A.2, p.521: a finite subcomplex
is a finite union of closed characteristic-cell images.
-/

namespace HolomorphicAnosov.Cubical

/-- The carrier of a cubical subcomplex is closed in the ambient Euclidean space.
The selected cells form a finite subset of the subdivision cells, and each cell
carrier is a closed coordinate interval product.
Source: Hatcher Appendix A.2, p.521. -/
theorem CubicalSubcomplex.carrier_isClosed {N : ℕ} {K : FiniteRectilinearSubdivision N}
    (D : CubicalSubcomplex K) : IsClosed D.carrier := by
  rw [CubicalSubcomplex.carrier]
  apply (K.finite_cells.subset D.subset_cells).isClosed_biUnion
  intro c hc
  exact isClosed_Icc


end HolomorphicAnosov.Cubical
