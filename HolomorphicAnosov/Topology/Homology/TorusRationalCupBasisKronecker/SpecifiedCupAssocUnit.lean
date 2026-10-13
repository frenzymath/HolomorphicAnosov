import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CupEqOfRepresentatives
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.OneEqOfRepresentatives
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupLeftUnit
import HolomorphicAnosov.AlgebraicTopology.SingularCupProductLaws

open CategoryTheory

noncomputable section

namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- For a topological space X, a rational cohomology product defined on every cocycle pair by the Alexander–Whitney formula is associative, with the degree casts, and the class of the constant-one cocycle is a two-sided unit.

Source: Hatcher, Algebraic Topology, §3.2 pp206–207, cup cochain formula, associativity and unit.

Identify the product with the singular cup product by surjectivity of cocycle classes: on each cocycle pair both operations equal the class of its Alexander–Whitney product.
Identify the proposed unit with the constant-one class using its representative equation. Apply the source associativity and left/right unit laws, retaining heterogeneous equality for different degree expressions. -/
theorem specified_cup_assoc_unit (X : TopCat)
    (cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ]
        SingularCochain.cohomology ℚ X (p + q))
    (one : SingularCochain.cohomology ℚ X 0)
    (hrep : ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        cup p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩)
    (hunit : ∃ hu : SingularCochain.oneCochain ℚ X ∈
        SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) 0,
      one = SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0
        ⟨SingularCochain.oneCochain ℚ X, hu⟩) :
    (∀ p q r (a : SingularCochain.cohomology ℚ X p)
        (b : SingularCochain.cohomology ℚ X q)
        (c : SingularCochain.cohomology ℚ X r),
      HEq (cup (p + q) r (cup p q a b) c)
        (cup p (q + r) a (cup q r b c))) ∧
    (∀ p (a : SingularCochain.cohomology ℚ X p),
      HEq (cup 0 p one a) a ∧ HEq (cup p 0 a one) a) := by
  obtain ⟨μ, _, hμ, hassoc, hone, _⟩ :=
    SingularCochain.singular_cup_product_laws ℚ
  have hcup : cup = fun p q ↦ μ X ∅ false false p q := by
    funext p q
    apply cup_eq_of_representatives X p q _ _ (hrep p q)
    intro b c
    obtain ⟨d, hd, he⟩ := hμ X ∅ false false p q b c
    change d.val = SingularCochain.cupCochain ℚ X b.val c.val at hd
    refine ⟨hd ▸ d.property, ?_⟩
    exact he.trans (congrArg
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q))
      (Subtype.ext hd))
  obtain ⟨u, hu, hulaw⟩ := hone X
  have ho : one =
      SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0 u := by
    apply one_eq_of_representatives X _ _ hunit
    refine ⟨hu ▸ u.property, ?_⟩
    exact congrArg
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0)
      (Subtype.ext hu)
  have hleft := specified_cup_left_unit cup one hrep hunit
  rw [hcup, ho] at hleft
  rw [hcup, ho]
  exact ⟨hassoc X ∅ false false false, by
    intro p a
    exact ⟨hleft p a, (hulaw ∅ false p a).2⟩⟩


end HolomorphicAnosov.TorusRationalCupBasisKronecker
