import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Basic

open _root_.Topology
open scoped unitInterval

namespace HolomorphicAnosov

/-- Compatible homotopy formulas on a quotient presentation descend to a
homotopy relative to a subset when they fix its entire preimage. Hatcher's
Proposition 1.26, pp.50--51 uses this descent for the attached auxiliary
strips; Appendix A.17, pp.532--533 supplies interval-product quotient descent.
The endpoints and fixed-set equations follow by choosing representatives
under the surjective quotient map. -/
theorem exists_quotient_relative_homotopy
    {X Z Y : Type*} [TopologicalSpace X] [TopologicalSpace Z] [TopologicalSpace Y]
    (q : X → Z) (hq : IsQuotientMap q) (f g : C(Z, Y)) (S : Set Z)
    (H : C(I × X, Y))
    (hzero : ∀ x, H (0, x) = f (q x))
    (hone : ∀ x, H (1, x) = g (q x))
    (hcompat : ∀ t x₁ x₂, q x₁ = q x₂ → H (t, x₁) = H (t, x₂))
    (hfixed : ∀ t x, q x ∈ S → H (t, x) = f (q x)) :
    ∃ G : f.HomotopyRel g S, ∀ t x, G (t, q x) = H (t, x) := by
  let s : Z → X := fun z ↦ Classical.choose (hq.surjective z)
  have hs (z : Z) : q (s z) = z := Classical.choose_spec (hq.surjective z)
  let G : I × Z → Y := fun p ↦ H (p.1, s p.2)
  have heq : ∀ t x, G (t, q x) = H (t, x) := by
    intro t x
    exact hcompat t (s (q x)) x (hs (q x))
  have hcomp : Continuous (fun p : I × X ↦ G (p.1, q p.2)) := by
    have : (fun p : I × X ↦ G (p.1, q p.2)) = H := by
      funext p
      exact heq p.1 p.2
    rw [this]
    exact H.continuous
  have hG : Continuous G := hq.continuous_lift_prod_right hcomp
  refine ⟨{ toFun := G
            continuous_toFun := hG
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }, heq⟩
  · intro z
    obtain ⟨x, rfl⟩ := hq.surjective z
    exact (heq 0 x).trans (hzero x)
  · intro z
    obtain ⟨x, rfl⟩ := hq.surjective z
    exact (heq 1 x).trans (hone x)
  · intro t z hz
    obtain ⟨x, rfl⟩ := hq.surjective z
    exact (heq t x).trans (hfixed t x hz)

end HolomorphicAnosov
