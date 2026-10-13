import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Set Filter Bundle
open scoped Manifold ContDiff Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov

/-- Holomorphic tangent fields are smooth as original real tangent fields. (Zhang, §2.1) -/
theorem holomorphic_tangent_field_smooth
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {V : Set X} {Y : (x : X) → TangentSpace (complexModel d) x}
    (hY : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun x ↦ (⟨x, Y x⟩ : TangentBundle (complexModel d) X)) V) :
    QuotientLineConnection.IsSmoothTangentField V Y := by
  intro x hx
  apply Bundle.contMDiffWithinAt_section.mpr
  have hc := Bundle.contMDiffWithinAt_section.mp (hY x hx)
  obtain ⟨hc₀, hc₁⟩ := contMDiffWithinAt_iff.mp hc
  have hr : ContMDiffWithinAt (realModel d) (realModel d) ∞
      (fun y ↦ (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
        ⟨y, Y y⟩).2) V x :=
    contMDiffWithinAt_iff.mpr ⟨hc₀, hc₁.restrict_scalars ℝ⟩
  apply hr.congr_of_eventuallyEq
  · filter_upwards [nhdsWithin_le_nhds ((chartAt (ComplexModel d) x).open_source.mem_nhds
      (mem_chart_source (ComplexModel d) x))] with y hy
    exact complexTangentToReal_coordinates x ⟨y, Y y⟩ hy
  · exact complexTangentToReal_coordinates x ⟨x, Y x⟩ (mem_chart_source _ _)

end HolomorphicAnosov
