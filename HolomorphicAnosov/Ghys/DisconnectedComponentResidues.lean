import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticIterateIffOfCompact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-! This file proves the finite component-permutation reduction and the corresponding asymptoticity equivalence for disconnected systems. (Ghys, Prop. 3.1) -/

noncomputable section
open scoped Topology
open Filter Set _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u

/-- For a compact locally connected space and a homeomorphism, a positive iterate preserves every connected component, and asymptoticity is equivalent to asymptoticity sampled along that iterate. (Ghys, Prop. 3.1) -/
private def component_perm
    {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) : Equiv.Perm (ConnectedComponents X) where
  toFun := f.continuous.connectedComponentsMap
  invFun := f.symm.continuous.connectedComponentsMap
  left_inv := by
    intro q
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    simp only [Continuous.connectedComponentsMap_mk, f.symm_apply_apply]
  right_inv := by
    intro q
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    simp only [Continuous.connectedComponentsMap_mk, f.apply_symm_apply]

theorem disconnected_component_residue_bridge
    {M : Type u} [MetricSpace M] [CompactSpace M]
    [LocallyConnectedSpace M] (f : M ≃ₜ M) :
    ∃ N : ℕ, 0 < N ∧
      (∀ x : M,
        connectedComponent (((f : M → M)^[N]) x) = connectedComponent x) ∧
      (∀ x y : M,
        ForwardAsymptotic (((f : M → M)^[N])) x y ↔
          ForwardAsymptotic (f : M → M) x y) ∧
      (∀ x y : M,
        ForwardAsymptotic (((f.symm : M → M)^[N])) x y ↔
          ForwardAsymptotic (f.symm : M → M) x y) := by
  let e := component_perm f
  obtain ⟨N, hN, hpow⟩ := (isOfFinOrder_of_finite e).exists_pow_eq_one
  have hcomponents : ∀ x : M,
      connectedComponent (((f : M → M)^[N]) x) = connectedComponent x := by
    intro x
    apply ConnectedComponents.coe_eq_coe.mp
    have hsem : Function.Semiconj ConnectedComponents.mk (f : M → M) e := fun _ ↦ rfl
    calc
      ConnectedComponents.mk (((f : M → M)^[N]) x) =
          (e^[N]) (ConnectedComponents.mk x) := hsem.iterate_right N x
      _ = ConnectedComponents.mk x := by rw [← Equiv.Perm.coe_pow, hpow]; rfl
  refine ⟨N, hN, hcomponents, ?_, ?_⟩
  · intro x y
    exact StableFoliationsSupport.forwardAsymptotic_iterate_iff_of_compact
      f.continuous hN x y
  · intro x y
    exact StableFoliationsSupport.forwardAsymptotic_iterate_iff_of_compact
      f.symm.continuous hN x y

end HolomorphicAnosov.Ghys
