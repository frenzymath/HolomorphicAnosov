import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- C0 on the given normalized conjugacy: conjugate the original homeomorphism `f` by `h`. -/
theorem covering_conjugacy_quotient_dynamics_g15
    {d : ℕ} {X V : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Γ : Submodule ℤ V) (f : Biholomorph d d X X)
    (A : V ≃L[ℝ] V) (h : X ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = QuotientAddGroup.mk (A v)) :
    ∃ α : (V ⧸ Γ.toAddSubgroup) ≃ₜ (V ⧸ Γ.toAddSubgroup),
      (QuotientAddGroup.mk : V → V ⧸ Γ.toAddSubgroup) ∘ A = α ∘ QuotientAddGroup.mk ∧
        h ∘ f = α ∘ h := by
  let α := (h.symm.trans f.toHomeomorph).trans h
  refine ⟨α, ?_, ?_⟩
  · funext v
    exact (hc (h.symm (QuotientAddGroup.mk v)) v (by simp)).symm
  · funext x
    simp [α]


end HolomorphicAnosov
