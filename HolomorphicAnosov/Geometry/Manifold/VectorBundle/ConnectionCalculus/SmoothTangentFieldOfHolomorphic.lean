import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! This file proves real smoothness of holomorphic tangent fields under canonical realification.
(Demailly, I §3.B–C, pp.22–24 and V §14, (14.1), p.273; Zhang, §2.1, (2), p.4) -/

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- A holomorphic tangent field on an open set is smooth under canonical realification. (Demailly, I
§3.C, pp.22–24; Zhang, §2.1, p.4) -/
theorem smoothTangentField_of_holomorphic
    {U : Set X} (hU : IsOpen U)
    {T : (x : X) → TangentSpace (complexModel d) x}
    (hT : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun x ↦ (⟨x, T x⟩ : TangentBundle (complexModel d) X)) U) :
    QuotientLineConnection.IsSmoothTangentField U T := by
  intro x hx
  let ec := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let er := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x
  have hc := (ec.contMDiffAt_section_iff
    (FiberBundle.mem_baseSet_trivializationAt' x)).mp
    (hT.contMDiffAt (hU.mem_nhds hx))
  have hr : ContMDiffAt (realModel d) (realModel d) ∞
      (fun y ↦ (ec (⟨y, T y⟩ : TangentBundle (complexModel d) X)).2) x := by
    obtain ⟨hcont, hdiff⟩ := contMDiffAt_iff.mp hc
    exact contMDiffAt_iff.mpr ⟨hcont, hdiff.restrict_scalars ℝ⟩
  apply ContMDiffAt.contMDiffWithinAt
  apply (er.contMDiffAt_section_iff
    (FiberBundle.mem_baseSet_trivializationAt' x)).mpr
  apply hr.congr_of_eventuallyEq
  filter_upwards [(chartAt (ComplexModel d) x).open_source.mem_nhds
    (mem_chart_source (ComplexModel d) x)] with y hy
  exact complexTangentToReal_coordinates x ⟨y, T y⟩ hy

end HolomorphicAnosov.ConnectionCalculus
