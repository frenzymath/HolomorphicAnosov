import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductLeibniz
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductBilinear

/-!
# Singular cup products of cocycles

Source: Hatcher, *Algebraic Topology*, p.207, first paragraph after Lemma3.6.
DAG node: `topo.singular_cochain_cup_product_cocycles_g6`.
-/

open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- The actual cup cochain of two cocycles is again a cocycle.

Source: Hatcher, *Algebraic Topology*, p.207. Both input coboundaries vanish.
Lemma3.6 expresses the product coboundary as the sum of two products each
having a zero factor. Bilinearity makes both terms zero. The native outgoing
kernel defining cycles agrees with the next-degree differential kernel, since
its degree comparison map is an isomorphism. All degrees, spaces and rings,
including zero degrees, empty spaces and the zero ring, are covered. -/
theorem cupCochain_mem_cycles (R : Type u) [CommRing R]
    (X : TopCat.{u}) {p q : ℕ}
    (a : cycles R (complex R X) p) (b : cycles R (complex R X) q) :
    cupCochain R X a.val b.val ∈ cycles R (complex R X) (p+q) := by
  have hcycle (n : ℕ) (c : cochains R X n) :
      c ∈ cycles R (complex R X) n ↔ coboundary R X n c = 0 := by
    change (complex R X).dFrom n c = 0 ↔ _
    rw [(complex R X).dFrom_eq (j := n+1) (by simp [ComplexShape.up, ComplexShape.up'])]
    change ((complex R X).xNextIso _).inv (coboundary R X n c) = 0 ↔ _
    exact (ModuleCat.mono_iff_injective ((complex R X).xNextIso _).inv).mp
      inferInstance |>.eq_iff' (map_zero _)
  rw [hcycle, cochain_cup_leibniz, (hcycle p a.val).mp a.property,
    (hcycle q b.val).mp b.property]
  obtain ⟨left, hleft⟩ := cupCochain_bilinear R X (p+1) q
  obtain ⟨right, hright⟩ := cupCochain_bilinear R X p (q+1)
  rw [← hleft, ← hright]
  simp

end HolomorphicAnosov.SingularCochain
