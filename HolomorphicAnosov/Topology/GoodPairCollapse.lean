import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Basic

/-! Collapsing a subspace to its image point. -/

namespace HolomorphicAnosov.GoodPair

universe u

variable {X : Type u}

/-- The equivalence relation identifies all points of `A` and leaves other points distinct. (Hatcher, Prop. 2.22) -/
def collapseSetoid (A : Set X) : Setoid X where
  r x y := x = y ∨ x ∈ A ∧ y ∈ A
  iseqv := ⟨fun _ ↦ Or.inl rfl,
    fun h ↦ h.elim (fun hxy ↦ Or.inl hxy.symm) (fun hxy ↦ Or.inr hxy.symm),
    fun hxy hyz ↦ by
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact hyz
      · rcases hyz with rfl | ⟨_, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩⟩

/-- The quotient `X/A` identifies two points exactly when they are equal or both belong to `A`, with the quotient topology. (Hatcher, Prop. 2.22) -/
abbrev Collapsed (A : Set X) := Quotient (collapseSetoid A)

variable [TopologicalSpace X]

/-- The canonical continuous quotient projection `X → X/A`. (Hatcher, Prop. 2.22) -/
def collapse (A : Set X) : C(X, Collapsed A) :=
  ⟨Quotient.mk (collapseSetoid A), continuous_quotient_mk'⟩

/-- The subset `A/A` is the image of `A` under the quotient projection. It is empty if `A` is empty; it is a singleton when a point of `A` exists. (Hatcher, Prop. 2.22) -/
def collapsedPart (A : Set X) : Set (Collapsed A) := collapse A '' A

end HolomorphicAnosov.GoodPair
