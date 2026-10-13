import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith

/-! Explicit strip collapse for Hatcher, Algebraic Topology, Proposition 1.26,
pp.50–51. The coordinate formula and its verification expand the source's
assertion that the added strip deformation retracts onto its attached edges.
This formula and its verification are agent-written; Hatcher asserts the
deformation but does not print these coordinates. -/

noncomputable section
open unitInterval Set
namespace HolomorphicAnosov

/-- The bottom and right edges along which the auxiliary strip is attached. -/
def attachedStripEdges : Set (I × I) := {p | p.2 = 0 ∨ p.1 = 1}

/-- Explicit retraction of the square to its attached edges. For k=u(1+s),
the image is (min(k,1), max(k-1,0)). Source: coordinate expansion of Hatcher
Proposition 1.26, p.50, strip deformation. -/
def attachedStripRetraction : C(I × I, I × I) where
  toFun p :=
    (⟨min ((p.1 : ℝ) * (1 + p.2)) 1, by
       constructor
       · exact le_min (mul_nonneg p.1.2.1 (by linarith [p.2.2.1])) zero_le_one
       · exact min_le_right _ _⟩,
     ⟨max ((p.1 : ℝ) * (1 + p.2) - 1) 0, by
       constructor
       · exact le_max_right _ _
       · apply max_le _ zero_le_one
         nlinarith [p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2]⟩)
  continuous_toFun := by fun_prop

/-- The endpoint lies on the bottom or right edge: split at k=1. -/
theorem attachedStripRetraction_mem (p : I × I) :
    attachedStripRetraction p ∈ attachedStripEdges := by
  by_cases h : (p.1 : ℝ) * (1 + p.2) ≤ 1
  · left
    apply Subtype.ext
    exact max_eq_right (sub_nonpos.mpr h)
  · right
    apply Subtype.ext
    exact min_eq_right (le_of_not_ge h)

/-- The coordinate formula fixes both attached edges, including their common corner. -/
theorem attachedStripRetraction_fixed (p : I × I) (hp : p ∈ attachedStripEdges) :
    attachedStripRetraction p = p := by
  rcases hp with h | h
  · rcases p with ⟨u,s⟩
    dsimp at h
    subst s
    apply Prod.ext <;> apply Subtype.ext
    · simpa [attachedStripRetraction] using min_eq_left u.2.2
    · simp [attachedStripRetraction, max_eq_right (sub_nonpos.mpr u.2.2)]
  · rcases p with ⟨u,s⟩
    dsimp at h
    subst u
    apply Prod.ext <;> apply Subtype.ext
    · simp [attachedStripRetraction, min_eq_right (by linarith [s.2.1] : (1 : ℝ) ≤ 1 + s)]
    · simp [attachedStripRetraction, max_eq_left s.2.1]

/-- Straight interpolation from the identity to the strip retraction fixes the
attached edges at every time. Convex combinations stay in the interval; their
joint continuity gives the homotopy. The endpoints and fixed-edge equations
follow from the corresponding convex-combination identities. This is the
explicit square homotopy underlying Hatcher Proposition 1.26, p.50. -/
def attachedStripHomotopy :
    (ContinuousMap.id (I × I)).HomotopyRel attachedStripRetraction attachedStripEdges where
  toFun z := (Icc.convexComb z.2.1 (attachedStripRetraction z.2).1 z.1,
    Icc.convexComb z.2.2 (attachedStripRetraction z.2).2 z.1)
  continuous_toFun := by fun_prop
  map_zero_left := by intro p; simp
  map_one_left := by intro p; simp
  prop' := by
    intro t p hp
    change (Icc.convexComb p.1 (attachedStripRetraction p).1 t,
      Icc.convexComb p.2 (attachedStripRetraction p).2 t) = p
    rw [attachedStripRetraction_fixed p hp]
    simp

/-- The square strongly deformation retracts to its bottom and right edges.
Use the explicit retraction and the straight homotopy constructed above. -/
theorem attachedStrip_deformation_retraction :
    ∃ r : C(I × I, I × I),
      (∀ p, r p ∈ attachedStripEdges) ∧
      Nonempty ((ContinuousMap.id (I × I)).HomotopyRel r attachedStripEdges) :=
  ⟨attachedStripRetraction, attachedStripRetraction_mem, ⟨attachedStripHomotopy⟩⟩

end HolomorphicAnosov
