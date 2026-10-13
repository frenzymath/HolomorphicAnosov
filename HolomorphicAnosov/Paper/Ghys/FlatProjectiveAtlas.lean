import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! This file defines the effective Möbius group with its discrete topology and flat transverse
projective atlases on topological flowboxes. (Ghys, Prop. 4.1 and §5, p. 597) -/

noncomputable section

namespace HolomorphicAnosov.Ghys

/-- The effective Möbius group is the image of the `GL(2, ℂ)` action in the permutation group of
`OnePoint ℂ`. (Ghys, p. 597) -/
def MobiusGroup : Type :=
  (MulAction.toPermHom (GL (Fin 2) ℂ) (OnePoint ℂ)).range

instance : Group MobiusGroup :=
  inferInstanceAs (Group (MulAction.toPermHom (GL (Fin 2) ℂ) (OnePoint ℂ)).range)

/-- The discrete topology on the effective Möbius group. -/
instance : TopologicalSpace MobiusGroup := ⊥

instance : DiscreteTopology MobiusGroup := ⟨rfl⟩

/-- Evaluation of an effective Möbius transformation on `OnePoint ℂ`. -/
def MobiusGroup.apply (g : MobiusGroup) (z : OnePoint ℂ) : OnePoint ℂ :=
  g.val z

/-- A flat transverse projective atlas consists of flowbox charts into `L × ℂ`, a covering selector,
and transition functions into the discrete Möbius group satisfying the cocycle and
transverse-coordinate identities on overlaps. (Ghys, p. 597) -/
structure FlatProjectiveAtlas (X L ι : Type*)
    [TopologicalSpace X] [TopologicalSpace L] where
  chart : ι → OpenPartialHomeomorph X (L × ℂ)
  indexAt : X → ι
  mem_source : ∀ x, x ∈ (chart (indexAt x)).source
  transition : ι → ι → X → MobiusGroup
  transition_continuous : ∀ i j,
    ContinuousOn (transition i j) ((chart i).source ∩ (chart j).source)
  transition_self : ∀ i x, x ∈ (chart i).source → transition i i x = 1
  transition_comp : ∀ i j k x,
    x ∈ (chart i).source ∩ (chart j).source ∩ (chart k).source →
      transition i k x = transition j k x * transition i j x
  transition_agrees : ∀ i j x, x ∈ (chart i).source ∩ (chart j).source →
    ((chart j x).2 : OnePoint ℂ) = (transition i j x).apply ((chart i x).2 : OnePoint ℂ)

end HolomorphicAnosov.Ghys
