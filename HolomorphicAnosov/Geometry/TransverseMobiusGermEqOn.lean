import HolomorphicAnosov.Geometry.TransverseMobiusLocalForm

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- Equality on an open neighborhood implies equality of germs at its base point. -/
theorem transverse_mobius_germ_eqOn
    {Y : Type*} [TopologicalSpace Y]
    {T : Type*} [TopologicalSpace T]
    {f g : Y → T} {y : Y} {U : Set Y}
    (hU : IsOpen U) (hy : y ∈ U) (hfg : EqOn f g U) :
    (Filter.Germ.ofFun f : Filter.Germ (𝓝 y) T) = Filter.Germ.ofFun g := by
  apply Filter.EventuallyEq.germ_eq
  filter_upwards [hU.mem_nhds hy] with x hx
  exact hfg hx

end HolomorphicAnosov.Ghys
