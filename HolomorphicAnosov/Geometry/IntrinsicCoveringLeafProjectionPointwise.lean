import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf

/-! Pointwise properties of pullback leaf projections. -/

namespace HolomorphicAnosov

universe u v w

variable {S : Type u} {X : Type v} {B : Type w}
variable [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace B]

omit [TopologicalSpace S] in
/-- The pullback first projection is the unique map over an injective leaf inclusion. -/
theorem intrinsicCoveringLeafProjection_pointwise
    (i : B → S) (π : X → S) (a : B) (x : X) (h : i a = π x)
    (hi : Function.Injective i) :
    let L := IntrinsicCoveringPullbackLeaf i π a x h
    let q := intrinsicCoveringLeafProjection i π a x h
    let ℓ := intrinsicCoveringLeafInclusion i π a x h
    Continuous q ∧ Function.Injective ℓ ∧
      (∀ z : L, i (q z) = π (ℓ z)) ∧
      (∀ r : L → B, (∀ z, i (r z) = π (ℓ z)) → r = q) := by
  dsimp only
  refine ⟨(intrinsicCoveringLeafProjection i π a x h).continuous, ?_, ?_, ?_⟩
  · intro z z' hz
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply hi
      calc
        i z.val.val.1 = π z.val.val.2 := z.val.property
        _ = π z'.val.val.2 := congrArg π hz
        _ = i z'.val.val.1 := z'.val.property.symm
    · exact hz
  · intro z
    exact z.val.property
  · intro r hr
    funext z
    apply hi
    exact (hr z).trans z.val.property.symm

end HolomorphicAnosov

