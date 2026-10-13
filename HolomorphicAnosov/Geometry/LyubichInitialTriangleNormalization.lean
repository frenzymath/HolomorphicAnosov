import HolomorphicAnosov.Geometry.LyubichMarkedTriangleTopology
import HolomorphicAnosov.Analysis.Complex.BoundedRiemannMap
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import Mathlib.Topology.Compactification.OnePoint.Basic
import HolomorphicAnosov.Geometry.LyubichCayleyNormalization

/-! The file constructs the normalized map on the initial ideal triangle. (Lyubich, §2.4.13, Exercise 2.49(i)) -/

namespace HolomorphicAnosov

/-- The marked ideal-triangle interior admits the normalized biholomorphism to the upper half-plane, with its sphere-valued extension at the three marked vertices. (Lyubich, §2.4.13, Exercise 2.49(i)) -/
theorem markedIdealDiskTriangle_normalized_initial_map
    (T : MarkedIdealDiskTriangle) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ,
      F.source = T.interiorSet ∧
      F.target = {w : ℂ | 0 < w.im} ∧
      DifferentiableOn ℂ F F.source ∧
      DifferentiableOn ℂ F.symm F.target ∧
      (∃ b : ℂ → OnePoint ℂ,
        ContinuousOn b T.closedSet ∧
        Set.EqOn b (fun z : ℂ ↦ (F z : OnePoint ℂ)) T.interiorSet ∧
        b (T.vertex 0) = (0 : ℂ) ∧
        b (T.vertex 1) = (1 : ℂ) ∧
        b (T.vertex 2) = OnePoint.infty) := by
  classical
  obtain ⟨hne, hopen, hbounded, hsimply, hjordan, hclosure⟩ :=
    markedIdealDiskTriangle_interior_domain T
  obtain ⟨z₀, hz₀⟩ := hne
  let : SimplyConnectedSpace T.interiorSet := hsimply
  obtain ⟨φ, ψ, hφ, hψ, hbij, hψmap, hleft, hright, hcenter, hreal, hpos⟩ :=
    bounded_riemann_map T.interiorSet ⟨z₀, hz₀⟩ hbounded hopen z₀ hz₀
  have hDisk : Analysis.MarkedRectangle.unitDisk = Metric.ball (0 : ℂ) 1 := by
    ext z
    simp [Analysis.MarkedRectangle.unitDisk, Metric.mem_ball, dist_zero_right]
  obtain ⟨Φ, hext, hunique, hboundary, hmarks⟩ :=
    Analysis.MarkedRectangle.caratheodory_same_map T.interiorSet ⟨z₀, hz₀⟩
      hopen hbounded hsimply hjordan φ (hDisk.symm ▸ hφ) (hDisk.symm ▸ hbij)
  exact markedIdealDiskTriangle_cayley_normalization T φ Φ (hDisk.symm ▸ hφ)
      (hDisk.symm ▸ hbij) hext hboundary

end HolomorphicAnosov
