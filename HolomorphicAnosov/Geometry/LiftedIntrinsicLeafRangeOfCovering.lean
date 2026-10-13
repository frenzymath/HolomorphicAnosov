import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRange
import Mathlib.Topology.Homotopy.Lifting

/-! The range of a lifted leaf under a covering projection. -/

noncomputable section
universe u v w
namespace HolomorphicAnosov

/-- Once the actual intrinsic projection of a constructed lifted leaf is a covering, its entire inclusion range is the marked path-lift range. -/
theorem liftedIntrinsicLeafRange_eq_of_leaf_covering
    {X : Type u} {Y : Type v} {L : Type w} {T : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    [TopologicalSpace T] [PathConnectedSpace T]
    (p : Y → X) (j : L → X) (k : T → L) (i : T → Y)
    (hp : IsCoveringMap p) (hk : IsCoveringMap k) (hi : Continuous i)
    (hcomm : ∀ t, p (i t) = j (k t)) (t₀ : T) :
    liftedIntrinsicLeafRange p j (k t₀) (i t₀) = Set.range i := by
  ext z
  constructor
  · rintro ⟨b, γ, η, hη⟩
    obtain ⟨Γ, hΓ, hΓ₀⟩ := hk.exists_path_lifts γ.toContinuousMap t₀ γ.source
    have heq : (fun t ↦ i (Γ t)) = η := hp.eq_of_comp_eq
      (hi.comp Γ.continuous) η.continuous (by
        funext t
        exact (hcomm (Γ t)).trans
          ((congrArg j (congrFun hΓ t)).trans (hη t).symm))
      0 (by simp only [hΓ₀, Path.source])
    exact ⟨Γ 1, (congrFun heq 1).trans η.target⟩
  · rintro ⟨t, rfl⟩
    let ξ := PathConnectedSpace.somePath t₀ t
    exact ⟨k t, ξ.map hk.continuous, ξ.map hi, fun s ↦ hcomm (ξ s)⟩


end HolomorphicAnosov
