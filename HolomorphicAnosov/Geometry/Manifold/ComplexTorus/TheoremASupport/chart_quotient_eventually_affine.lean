import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Paper.Zhang.CodimensionOne
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.TorusModel
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactness.Compact
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.chart_symm_eq_mk

namespace HolomorphicAnosov.TheoremAProof.QuotientCalculus
open Filter _root_.Topology
noncomputable section

/-- Near the quotient origin, the chart expression of the induced automorphism is `z ↦ A.linear z +
(c - A.linear c)`, where `c` is the chart representative of the origin. -/
theorem chart_quotient_eventually_affine {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) :
    let e := chartAt (ComplexModel d) (0 : ComplexTorus L)
    let c := e (0 : ComplexTorus L)
    (fun z : ComplexModel d => e (quotientLinearEquiv A (e.symm z)))
      =ᶠ[𝓝 c] (fun z => A.linear z + (c - A.linear c)) := by
  let e := chartAt (ComplexModel d) (0 : ComplexTorus L)
  let c := e (0 : ComplexTorus L)
  let q := (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L)
  have hc : q c = 0 := by
    change (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L) c = 0
    rw [← chart_symm_eq_mk L 0]
    exact e.left_inv (mem_chart_source _ _)
  have hAc : q (A.linear c) = 0 := by
    change (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L) (A.linear c) = 0
    change quotientLinearEquiv A (q c) = 0
    rw [hc]
    exact map_zero _
  have hshift : q (c - A.linear c) = 0 := by
    change (QuotientAddGroup.mk' L.lattice.toAddSubgroup) (c - A.linear c) = 0
    rw [map_sub]
    change q c - q (A.linear c) = 0
    rw [hc, hAc, sub_self]
  have hctarget : c ∈ e.target := e.map_source (mem_chart_source _ _)
  have hlin : Continuous (fun z : ComplexModel d => A.linear z + (c - A.linear c)) :=
    A.linear.toContinuousLinearEquiv.continuous.add continuous_const
  have hcenter : A.linear c + (c - A.linear c) = c := by abel
  have hball : ∀ᶠ z in 𝓝 c, A.linear z + (c - A.linear c) ∈ e.target := by
    have hb : e.target ∈ 𝓝 (A.linear c + (c - A.linear c)) := by
      rw [hcenter]
      exact e.open_target.mem_nhds hctarget
    exact hlin.continuousAt.preimage_mem_nhds hb
  filter_upwards [hball] with z hz
  change e (quotientLinearEquiv A (e.symm z)) = A.linear z + (c - A.linear c)
  rw [chart_symm_eq_mk L 0]
  have hqshift : q (A.linear z + (c - A.linear c)) = q (A.linear z) := by
    change (QuotientAddGroup.mk' L.lattice.toAddSubgroup) (_ + _) = _
    rw [map_add]
    change q (A.linear z) + q (c - A.linear c) = q (A.linear z)
    rw [hshift, add_zero]
  change e (q (A.linear z)) = A.linear z + (c - A.linear c)
  rw [← hqshift]
  change e ((QuotientAddGroup.mk : ComplexModel d → ComplexTorus L) _) = _
  rw [← chart_symm_eq_mk L 0]
  exact e.right_inv hz



end
end HolomorphicAnosov.TheoremAProof.QuotientCalculus
