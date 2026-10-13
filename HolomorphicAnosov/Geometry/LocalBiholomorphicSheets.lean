import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! Local biholomorphic sheets and local diffeomorphisms. -/

open Set Topology _root_.Topology
open scoped Manifold ContDiff

namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly

noncomputable section
universe u v

theorem locally_biholomorphic_of_sheets
    {d : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    (p : Y → X)
    (hsheets : ∀ y : Y, ∃ s : OpenPartialHomeomorph Y X,
      y ∈ s.source ∧ EqOn s p s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s s.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ s.symm s.target) :
    IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p := by
  intro y
  obtain ⟨s,hy,he,hf,hi⟩ := hsheets y
  exact ⟨{ toPartialEquiv := s.toPartialEquiv
           open_source := s.open_source
           open_target := s.open_target
           contMDiffOn_toFun := hf
           contMDiffOn_invFun := hi },hy,he.symm⟩

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly
