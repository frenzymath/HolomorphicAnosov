import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace HolomorphicAnosov

open Set

/-- Paths contained in one simply connected open-cover member are homotopic in
the ambient space. Source: Hatcher Lemma 1.15, p.35. Lift both paths to the
member's subtype, use simple connectedness there, and include the homotopy. -/
theorem sphere_paths_homotopic_in_member
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsSimplyConnected U)
    {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U) :
    p.Homotopic q := by
  have hx : x ∈ U := by simpa using hp 0
  have hy : y ∈ U := by simpa using hp 1
  let P : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let Q : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have : SimplyConnectedSpace U := hU
  exact (SimplyConnectedSpace.paths_homotopic P Q).map ⟨Subtype.val, continuous_subtype_val⟩

end HolomorphicAnosov

