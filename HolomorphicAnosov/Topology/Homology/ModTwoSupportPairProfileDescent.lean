import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.ModTwoSupportRestrictionLinearEquiv
import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.EpiMono

/-!
# Descent of a point profile along a support-pair isomorphism

Source: Hatcher, *Algebraic Topology*, pp.115–118 and pp.233–235.  The
restriction map of support pairs is an actual relative singular-homology map;
its isomorphism transports the point profile without changing coefficients.
-/

namespace HolomorphicAnosov.Topology.Homology

open CategoryTheory

universe u
noncomputable section

/-- A point profile descends to a larger support through an isomorphic support
restriction.  The statement is coefficient-explicit and applies to arbitrary
universe `u`.

Proof plan: obtain the inverse of each `IsIso` restriction map in
`ModuleCat (ZMod 2)`.  Compose the point degree-`n` linear equivalence with the
inverse restriction; transport `Subsingleton` through the same inverse map in
every other degree.  The source support pair is the literal pair
`(M,M\A)`, so no abstract replacement of the homology carrier occurs.

Source obligation: Hatcher pp.115–118 and pp.233–235.  The remaining formal
work is the cross-universe conversion from the categorical `IsIso` witness to
the displayed `LinearEquiv` and its off-degree `Subsingleton` transport.
-/
theorem modTwo_support_pair_profile_descent
    (n : ℕ) (M : Type u) [TopologicalSpace M] (A : Set M) (x : A)
    (hres : ∀ k : ℕ, IsIso (modTwoSupportRestriction M A {x.val}
      (Set.singleton_subset_iff.mpr x.property) k))
    (hpoint :
      Nonempty (modTwoSupportHomology M {x.val} n ≃ₗ[ZMod 2] ZMod 2) ∧
        ∀ k : ℕ, k ≠ n → Subsingleton
          (modTwoSupportHomology M {x.val} k)) :
    Nonempty (modTwoSupportHomology M A n ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ k : ℕ, k ≠ n → Subsingleton (modTwoSupportHomology M A k) := by
  have hpoint_n := hpoint.1
  obtain ⟨e_n⟩ := hpoint_n
  let : IsIso (modTwoSupportRestriction M A {x.val}
      (Set.singleton_subset_iff.mpr x.property) n) := hres n
  obtain ⟨r_n⟩ := modTwo_support_restriction_linear_equiv M A {x.val}
    (Set.singleton_subset_iff.mpr x.property) n
  refine ⟨⟨r_n.trans e_n⟩, ?_⟩
  intro k hk
  let : IsIso (modTwoSupportRestriction M A {x.val}
      (Set.singleton_subset_iff.mpr x.property) k) := hres k
  obtain ⟨r_k⟩ := modTwo_support_restriction_linear_equiv M A {x.val}
    (Set.singleton_subset_iff.mpr x.property) k
  exact (r_k.toEquiv.subsingleton_congr).mpr (hpoint.2 k hk)


end
end HolomorphicAnosov.Topology.Homology
