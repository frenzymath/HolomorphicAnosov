import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf
import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRange

/-! Endpoint ranges in pointed pullback leaves. -/

namespace HolomorphicAnosov

universe u v w

variable {S : Type u} {X : Type v} {B : Type w}
variable [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace B]

/-- The second pullback projection has exactly the compatible path endpoints. -/
theorem intrinsicCoveringLeafInclusion_range
    (i : B → S) (π : X → S) (a : B) (x : X) (h : i a = π x) :
    Set.range (intrinsicCoveringLeafInclusion i π a x h) =
      liftedIntrinsicLeafRange π i a x := by
  ext z
  constructor
  · rintro ⟨l, rfl⟩
    obtain ⟨δ⟩ := l.property
    let hγ : Path a l.val.val.1 := {
      toFun := fun t => (δ t).val.1
      continuous_toFun := continuous_fst.comp (continuous_subtype_val.comp δ.continuous)
      source' := by
        simpa [intrinsicCoveringPullbackPoint] using
          congrArg (fun p : IntrinsicCoveringPullback i π => p.val.1) δ.source
      target' := by simp }
    let hη : Path x l.val.val.2 := {
      toFun := fun t => (δ t).val.2
      continuous_toFun := continuous_snd.comp (continuous_subtype_val.comp δ.continuous)
      source' := by
        simpa [intrinsicCoveringPullbackPoint] using
          congrArg (fun p : IntrinsicCoveringPullback i π => p.val.2) δ.source
      target' := by simp }
    refine ⟨l.val.val.1, hγ, hη, ?_⟩
    intro t
    exact (δ t).property.symm
  · rintro ⟨b, γ, η, heq⟩
    have hend : i b = π z := by simpa using (heq 1).symm
    let p : IntrinsicCoveringPullback i π := ⟨(b, z), hend⟩
    have δ : Path (intrinsicCoveringPullbackPoint i π a x h) p := {
      toFun := fun t => ⟨(γ t, η t), (heq t).symm⟩
      continuous_toFun := Continuous.subtype_mk (γ.continuous.prodMk η.continuous) _
      source' := by
        apply Subtype.ext
        exact Prod.ext γ.source η.source
      target' := by
        apply Subtype.ext
        exact Prod.ext γ.target η.target }
    exact ⟨⟨p, ⟨δ⟩⟩, rfl⟩

end HolomorphicAnosov

