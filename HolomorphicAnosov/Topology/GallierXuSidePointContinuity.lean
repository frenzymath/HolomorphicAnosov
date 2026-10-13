import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- Each parameterized face side is a continuous path in the unit circle. -/
lemma continuous_sidePoint {P : Presentation} (f : Fin P.length)
    (i : Fin (P.get f).length) :
    Continuous (fun t : ℝ => sidePoint P f i t) := by
  unfold sidePoint
  cases hsign : ((P.get f).get i).2 <;> simp
  · fun_prop
  · fun_prop

end HolomorphicAnosov.Topology.GallierXu
