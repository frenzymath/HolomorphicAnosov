import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Covering.Basic

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

/-- A covering with simply connected total space supplies the required local
loop condition. Lift a loop contained in a single covering chart by its inverse,
contract the lifted loop in the total space, and map that endpoint-fixed homotopy
back down. The contraction need not stay inside the covering chart. -/
theorem covering_local_loops_null
    {X : Type*} [TopologicalSpace X] {E : Type*} [TopologicalSpace E]
    [SimplyConnectedSpace E] (p : E → X) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) :
    ∀ x : X, ∃ V : Set X, x ∈ V ∧ IsOpen V ∧
      ∀ γ : Path x x, (∀ t, γ t ∈ V) → γ.Homotopic (Path.refl x) := by
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨e, hy, he⟩ := hp.isLocalHomeomorph y
  have hpy : p y ∈ e.target := by rw [he]; exact e.map_source hy
  refine ⟨e.target, hpy, e.open_target, ?_⟩
  intro γ hγ
  let δ : Path y y :=
    { toFun := fun t ↦ e.symm (γ t)
      continuous_toFun := e.continuousOn_invFun.comp_continuous γ.continuous hγ
      source' := by simp only [γ.source]; rw [he]; exact e.left_inv hy
      target' := by simp only [γ.target]; rw [he]; exact e.left_inv hy }
  have hd := (SimplyConnectedSpace.paths_homotopic δ (Path.refl y)).map ⟨p, hp.continuous⟩
  have hmap : δ.map hp.continuous = γ := by
    ext t
    change p (e.symm (γ t)) = γ t
    exact (congrFun he _).trans (e.right_inv (hγ t))
  have hrefl : (Path.refl y).map hp.continuous = Path.refl (p y) := by ext; rfl
  simpa only [hmap, hrefl] using hd

end HolomorphicAnosov
