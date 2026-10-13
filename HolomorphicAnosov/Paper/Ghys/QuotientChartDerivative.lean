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

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem quotient_chart_derivative {d : ℕ} (L : FullComplexLattice d)
    (e : OpenPartialHomeomorph (ComplexTorus L) (ComplexModel d))
    (he : e ∈ atlas (ComplexModel d) (ComplexTorus L)) (z : ComplexModel d)
    (hz : (QuotientAddGroup.mk z : ComplexTorus L) ∈ e.source) :
    HasFDerivAt (fun w : ComplexModel d ↦ e (QuotientAddGroup.mk w))
      (ContinuousLinearMap.id ℝ (ComplexModel d)) z := by
  let q := (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L)
  have hq : Continuous q := QuotientAddGroup.continuous_mk
  let O := q ⁻¹' e.source
  have hO : IsOpen O := e.open_source.preimage hq
  have hz : z ∈ O := hz
  have hm : ∀ w ∈ O, e (q w) - w ∈ L.lattice := by
    intro w hw
    have hew : (QuotientAddGroup.mk (e (q w)) : ComplexTorus L) = q w := by
      rw [← torus_chart_inverse L e he]
      exact e.left_inv hw
    exact QuotientAddGroup.eq_iff_sub_mem.mp hew
  let D : O → L.lattice := fun w ↦ ⟨e (q w) - w, hm w w.property⟩
  have heq : ContinuousOn (fun w ↦ e (q w)) O :=
    e.continuousOn.comp hq.continuousOn (fun _ hw ↦ hw)
  have hD : Continuous D :=
    (heq.domRestrict.sub continuous_subtype_val).subtype_mk _
  let : DiscreteTopology L.lattice := L.discrete
  have hlc : IsLocallyConstant D := (IsLocallyConstant.iff_continuous D).2 hD
  let p : O := ⟨z, hz⟩
  obtain ⟨V, hV, hp, hconst⟩ := hlc.exists_open p
  have hU : IsOpen (Subtype.val '' V : Set (ComplexModel d)) :=
    hO.isOpenMap_subtype_val V hV
  have hzU : z ∈ (Subtype.val '' V : Set (ComplexModel d)) := ⟨p, hp, rfl⟩
  have hEq : (fun w ↦ e (q w)) =ᶠ[nhds z] (fun w ↦ w + (D p : ComplexModel d)) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have h := congrArg Subtype.val (hconst v hv)
    exact ((sub_eq_iff_eq_add).mp h).trans (add_comm _ _)
  exact ((hasFDerivAt_id z).add_const (D p : ComplexModel d)).congr_of_eventuallyEq hEq

end HolomorphicAnosov
