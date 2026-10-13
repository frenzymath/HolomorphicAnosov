import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.QuotientDynamics

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- The supplied quotient conjugacy also holds for the ORIGINAL inverse map and A inverse. -/
theorem covering_conjugacy_inverse_conjugacy_g15
    {d : ℕ} {X V : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Γ : Submodule ℤ V) (f : Biholomorph d d X X)
    (A : V ≃L[ℝ] V) (h : X ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = QuotientAddGroup.mk (A v)) :
    ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f.symm x) = QuotientAddGroup.mk (A.symm v) := by
  obtain ⟨α, hA, hf⟩ := covering_conjugacy_quotient_dynamics_g15 Γ f A h hc
  intro x v hv
  apply α.injective
  have hleft : α (h (f.symm x)) = h x := by
    simpa only [Function.comp_apply, f.apply_symm_apply] using
      (congrFun hf (f.symm x)).symm
  have hright : α (QuotientAddGroup.mk (A.symm v)) = QuotientAddGroup.mk v := by
    simpa only [Function.comp_apply, A.apply_symm_apply] using
      (congrFun hA (A.symm v)).symm
  rw [hleft, hright, hv]


end HolomorphicAnosov
