import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.EpiMono

/-!
# Linear-equivalence carrier for an isomorphic mod-two support restriction

Source: Hatcher, *Algebraic Topology*, pp.115–118 and pp.233–235.  The
support restriction is the actual map of singular relative chain complexes;
this interface exposes its categorical isomorphism as the concrete linear
equivalence needed by local-profile statements.
-/

namespace HolomorphicAnosov.Topology.Homology

open CategoryTheory
universe u
noncomputable section

/-- An isomorphic literal support restriction yields a concrete linear
 equivalence between the two `ZMod 2` relative-homology carriers.

Proof plan: obtain the inverse of the `ModuleCat` isomorphism supplied by the
`IsIso` instance and use its underlying linear maps as the forward and inverse
maps.  The two inverse equations are the categorical `IsIso.hom_inv_id` and
`IsIso.inv_hom_id` equations after forgetting to concrete modules.

Source obligation: Hatcher pp.115–118 and pp.233–235.  The statement keeps the
actual support-pair map and the lifted coefficient object; no abstract homology
carrier is substituted.
-/
theorem modTwo_support_restriction_linear_equiv
    (M : Type u) [TopologicalSpace M] (A B : Set M) (h : B ⊆ A) (k : ℕ)
    [IsIso (modTwoSupportRestriction M A B h k)] :
    Nonempty (modTwoSupportHomology M A k ≃ₗ[ZMod 2]
      modTwoSupportHomology M B k) := by
  let g := ConcreteCategory.hom (modTwoSupportRestriction M A B h k)
  have hbij : Function.Bijective g := ConcreteCategory.bijective_of_isIso _
  exact ⟨LinearEquiv.ofBijective g hbij⟩


end
end HolomorphicAnosov.Topology.Homology
