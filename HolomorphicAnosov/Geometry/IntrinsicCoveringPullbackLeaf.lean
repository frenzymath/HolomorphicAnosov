import Mathlib.Topology.Connected.PathConnected

/-! The pointed intrinsic leaf in a covering pullback. -/

namespace HolomorphicAnosov

universe u v w

variable {S : Type u} {X : Type v} {B : Type w}
variable [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace B]

/-- The literal pullback of the original leaf inclusion and covering projection (Bredon II§14 pp.111–112).-/
abbrev IntrinsicCoveringPullback (i : B → S) (π : X → S) :=
  {z : B × X // i z.1 = π z.2}

/-- The marked pair in the literal pullback (the pointed covering path-lifting construction of Hatcher pp.60–62).-/
def intrinsicCoveringPullbackPoint (i : B → S) (π : X → S)
    (a : B) (x : X) (h : i a = π x) : IntrinsicCoveringPullback i π :=
  ⟨(a, x), h⟩

/-- The intrinsic lifted leaf through a compatible marked pair, as the native path-component subtype in the pullback (Bredon II§14 pp.111–112 and Hatcher pp.60–62, retaining the original intrinsic leaf topology of HPS §7).-/
abbrev IntrinsicCoveringPullbackLeaf (i : B → S) (π : X → S)
    (a : B) (x : X) (h : i a = π x) :=
  ↥(pathComponent (intrinsicCoveringPullbackPoint i π a x h))

/-- Projection to the original intrinsic base leaf, with its supplied topology (Bredon II§14, the pullback first projection).-/
def intrinsicCoveringLeafProjection (i : B → S) (π : X → S)
    (a : B) (x : X) (h : i a = π x) :
    C(IntrinsicCoveringPullbackLeaf i π a x h, B) :=
  ⟨fun z ↦ z.val.val.1,
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- The actual map of the lifted intrinsic leaf into the covering space (Bredon II§14, the pullback second projection, restricted to the marked path component).-/
def intrinsicCoveringLeafInclusion (i : B → S) (π : X → S)
    (a : B) (x : X) (h : i a = π x) :
    C(IntrinsicCoveringPullbackLeaf i π a x h, X) :=
  ⟨fun z ↦ z.val.val.2,
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

end HolomorphicAnosov
