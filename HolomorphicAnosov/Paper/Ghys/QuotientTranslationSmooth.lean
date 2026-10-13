import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Algebra.Group.Units.Equiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LinearMap
import HolomorphicAnosov.Paper.Zhang.Anosov
import Mathlib.LinearAlgebra.Eigenspace.Basic
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Paper.Ghys.TorusChartInverse
import HolomorphicAnosov.Paper.Ghys.QuotientProjectionSmooth

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem quotient_translation_smooth {d : ℕ} (L : FullComplexLattice d)
    (c : ComplexModel d) :
    ContMDiff (complexModel d) (complexModel d) ∞
      (fun x : ComplexTorus L ↦ x - QuotientAddGroup.mk c) := by
  let _ := complexTorus_isManifold L
  intro x
  let e := chartAt (ComplexModel d) x
  have hx : x ∈ e.source := mem_chart_source _ _
  have hchart : ContMDiffAt (complexModel d) 𝓘(ℂ, ComplexModel d) ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx
  have hshift : ContDiff ℂ ∞ (fun z : ComplexModel d ↦ z - c) :=
    contDiff_id.sub contDiff_const
  have hsub : ContMDiffAt (complexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (fun y ↦ e y - c) x := (hshift.contMDiff.contMDiffAt.comp x hchart)
  have hc : ContMDiffAt (complexModel d) (complexModel d) ∞
      (fun y ↦ QuotientAddGroup.mk (e y - c)) x :=
    (quotient_projection_smooth L).contMDiffAt.comp x hsub
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  have hq : (QuotientAddGroup.mk (e y) : ComplexTorus L) = y := by
    rw [← torus_chart_inverse L e (chart_mem_atlas _ _)]
    exact e.left_inv hy
  simp only [QuotientAddGroup.mk_sub, hq]

end HolomorphicAnosov
