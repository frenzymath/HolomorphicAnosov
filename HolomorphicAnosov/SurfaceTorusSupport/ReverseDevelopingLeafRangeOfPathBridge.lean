import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRangeOfCovering
import Mathlib.Topology.Homotopy.Lifting

open Set

namespace HolomorphicAnosov

/-- A set lies in the lifted leaf range if each of its points is joined to the marked lift by a path
projecting to an intrinsic leaf path. (Hatcher, Prop. 1.34, p. 62; Ghys, §5, pp. 598–599) -/
theorem reverse_developing_leaf_range_of_path_bridge
    {L U S : Type*} [TopologicalSpace L] [TopologicalSpace U] [TopologicalSpace S]
    [PathConnectedSpace L]
    (π : U → S) (inc : L → S) (lift : L → U)
    (hπ : IsCoveringMap π) (hlift : Continuous lift)
    (hproj : ∀ z, π (lift z) = inc z)
    (z₀ : L) (u : U) (hu : lift z₀ = u) (C : Set U)
    (bridge : ∀ y, y ∈ C →
      ∃ (z : L) (γ : Path z₀ z) (η : Path u y),
        ∀ t, π (η t) = inc (γ t)) :
    C ⊆ Set.range lift := by
  intro y hy
  obtain ⟨z, γ, η, hη⟩ := bridge y hy
  have heq : (fun t ↦ lift (γ t)) = η := hπ.eq_of_comp_eq
    (hlift.comp γ.continuous) η.continuous (by
      funext t
      exact (hproj (γ t)).trans (hη t).symm)
    0 (by simpa only [Path.source] using hu)
  exact ⟨z, by simpa only [Path.target] using congrFun heq 1⟩


end HolomorphicAnosov
