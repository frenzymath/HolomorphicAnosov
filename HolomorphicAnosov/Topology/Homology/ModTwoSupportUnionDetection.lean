import HolomorphicAnosov.Topology.Homology.ModTwoSupportMayerVietoris

noncomputable section
open Set
namespace HolomorphicAnosov.HatcherCompactSupport
universe u

/-- The two restriction maps out of a compact support union are jointly injective
when the next-degree intersection support is subsingleton.  This is the kernel part of
Hatcher's support Mayer–Vietoris sequence, specialized to mod-two supports. -/
theorem modTwo_support_union_restriction_injective
    (M : Type u) [TopologicalSpace M] [T2Space M]
    (A B : Set M) (hA : IsCompact A) (hB : IsCompact B) (n : ℕ)
    (hnext : Subsingleton (SupportHomology (A ∩ B) (n + 1))) :
    Function.Injective (modTwoSupportMVPhi M A B n) := by
  obtain ⟨δ, hseq, _⟩ := modTwo_compact_support_mayer_vietoris M A B hA hB
  intro x y hxy
  have hzero : modTwoSupportMVPhi M A B n (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (hseq n).1 (x - y) |>.mp hzero
  have hz0 : z = 0 := hnext.elim _ _
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- A mod-two support class on a compact union is zero when its restrictions to both
pieces vanish and the next-degree intersection support is subsingleton. -/
theorem modTwo_support_union_zero_of_restrictions
    (M : Type u) [TopologicalSpace M] [T2Space M]
    (A B : Set M) (hA : IsCompact A) (hB : IsCompact B) (n : ℕ)
    (hnext : Subsingleton (SupportHomology (A ∩ B) (n + 1)))
    (c : SupportHomology (A ∪ B) n)
    (hleft : supportRestriction (M := M) (A := A ∪ B) (B := A)
      Set.subset_union_left n c = 0)
    (hright : supportRestriction (M := M) (A := A ∪ B) (B := B)
      Set.subset_union_right n c = 0) :
    c = 0 := by
  apply (modTwo_support_union_restriction_injective M A B hA hB n hnext)
  rw [map_zero]
  change (supportRestriction (M := M) (A := A ∪ B) (B := A)
      Set.subset_union_left n c,
    -(supportRestriction (M := M) (A := A ∪ B) (B := B)
      Set.subset_union_right n c)) = (0, 0)
  rw [hleft, hright]
  simp

/-- Above the manifold dimension, subsingleton support homology propagates through a
compact union when it already holds on both pieces and their intersection. -/
theorem modTwo_support_union_above_dimension
    (M : Type u) [TopologicalSpace M] [T2Space M]
    (A B : Set M) (hA : IsCompact A) (hB : IsCompact B) (n : ℕ)
    (hleft : ∀ i : ℕ, n < i → Subsingleton (SupportHomology A i))
    (hright : ∀ i : ℕ, n < i → Subsingleton (SupportHomology B i))
    (hinter : ∀ i : ℕ, n < i → Subsingleton (SupportHomology (A ∩ B) i)) :
    ∀ i : ℕ, n < i → Subsingleton (SupportHomology (A ∪ B) i) := by
  intro i hi
  refine ⟨fun x y ↦ ?_⟩
  apply modTwo_support_union_restriction_injective M A B hA hB i
    (hinter (i + 1) (lt_trans hi (Nat.lt_succ_self i)))
  apply Prod.ext
  · exact hleft i hi |>.elim _ _
  · exact hright i hi |>.elim _ _


end HolomorphicAnosov.HatcherCompactSupport
