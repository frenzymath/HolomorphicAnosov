import HolomorphicAnosov.Geometry.IdealDiskTriangle
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Geometry.LyubichMarkedTriangleTopologyProviders

/-! The file establishes the topology of the marked ideal-triangle domain. (Lyubich, §2.4.4 and §2.4.13) -/

namespace HolomorphicAnosov

/-- The literal marked ideal-triangle interior is a bounded Jordan domain with the advertised filled carrier as its closure. -/
theorem markedIdealDiskTriangle_interior_domain (T : MarkedIdealDiskTriangle) :
    T.interiorSet.Nonempty ∧
      IsOpen T.interiorSet ∧
      Bornology.IsBounded T.interiorSet ∧
      IsSimplyConnected T.interiorSet ∧
      Analysis.MarkedRectangle.HasJordanBoundary T.interiorSet ∧
      closure T.interiorSet = T.closedSet := by
  exact ⟨markedIdealDiskTriangle_interior_nonempty T,
    markedIdealDiskTriangle_interior_isOpen T,
    markedIdealDiskTriangle_interior_isBounded T,
    markedIdealDiskTriangle_interior_isSimplyConnected T,
    markedIdealDiskTriangle_interior_hasJordanBoundary T,
    markedIdealDiskTriangle_closure_interior_eq_closedSet T⟩

end HolomorphicAnosov
