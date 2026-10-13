import HolomorphicAnosov.Ghys.LeafJetComplexManifold

/-! The base point of a curve germ represented by `g` is `g 0`. (Ghys, §3 p.591) -/

namespace HolomorphicAnosov.Ghys

universe u

variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]

omit [TopologicalSpace L] [ChartedSpace ℂ L] in
/-- The base point of the germ represented by `g` equals `g 0`. (Ghys, §3 p.591) -/
theorem base_coe (g : ℂ → L) : curveGermBase L (g : CurveGerm L) = g 0 := by
  rfl

#check base_coe

end HolomorphicAnosov.Ghys
