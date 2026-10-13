import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Basic

open _root_.Topology
open scoped unitInterval

namespace HolomorphicAnosov.CWCharacteristic

/-- A homotopy on the source of a quotient map descends continuously through
that quotient when it is constant on every source fibre. The proof uses a
classical section only to define the descended function; continuity follows
from Mathlib's locally-compact product quotient theorem. -/
theorem exists_continuous_product_quotient_lift
    {X Z Y : Type*} [TopologicalSpace X] [TopologicalSpace Z] [TopologicalSpace Y]
    (q : X → Z) (hq : IsQuotientMap q) (H : I × X → Y) (hH : Continuous H)
    (hcompat : ∀ t x₁ x₂, q x₁ = q x₂ → H (t, x₁) = H (t, x₂)) :
    ∃ G : I × Z → Y, Continuous G ∧ ∀ t x, G (t, q x) = H (t, x) := by
  let s : Z → X := fun z ↦ Classical.choose (hq.surjective z)
  have hs (z : Z) : q (s z) = z := Classical.choose_spec (hq.surjective z)
  let G : I × Z → Y := fun p ↦ H (p.1, s p.2)
  have hcomp : Continuous (fun p : I × X ↦ G (p.1, q p.2)) := by
    have heq : (fun p : I × X ↦ G (p.1, q p.2)) = H := by
      funext p
      exact hcompat p.1 (s (q p.2)) p.2 (hs (q p.2))
    rw [heq]
    exact hH
  refine ⟨G, hq.continuous_lift_prod_right hcomp, ?_⟩
  intro t x
  exact hcompat t (s (q x)) x (hs (q x))

end HolomorphicAnosov.CWCharacteristic
