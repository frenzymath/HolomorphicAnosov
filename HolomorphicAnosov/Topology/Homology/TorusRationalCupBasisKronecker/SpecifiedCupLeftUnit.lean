import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductUnit
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CupEqOfRepresentatives
open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker
set_option backward.isDefEq.respectTransparency false in
/-- For a product defined on cocycle representatives by the Alexander–Whitney cup
cochain, the constant-one class is a left unit. The proof transports the cochain
unit equality through the degree identification `0 + p = p` and quotient class.
Source: Hatcher, Algebraic Topology, §3.2 p207. -/
theorem specified_cup_left_unit
    {X : TopCat}
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
    ∀ p (a : SingularCochain.cohomology ℚ X p), HEq (cup 0 p one a) a := by
  obtain ⟨hu, hone⟩ := hunit
  intro p a
  obtain ⟨ar, rfl⟩ := (show Function.Surjective
    (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p) from
      Submodule.mkQ_surjective _) a
  obtain ⟨hl, hel⟩ := hrep 0 p ⟨_, hu⟩ ar
  have harg := congrArg (fun z => cup 0 p z
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p ar)) hone.symm
  have hleft : HEq
      (cup 0 p one (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p ar))
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p ar) := by
    rw [← harg]
    rw [hel]
    have hc := (SingularCochain.cupCochain_unit ℚ X ar.val).2
    have htransport {m n : ℕ} (h : m = n)
        (x : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) m)
        (y : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) n)
        (he : ((SingularCochain.complex ℚ X).XIsoOfEq h).hom x.val = y.val) :
        HEq (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) m x)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) n y) := by
      subst n
      have hv : x.val = y.val := he
      exact heq_of_eq (congrArg _ (Subtype.ext hv))
    exact htransport (Nat.zero_add p) ⟨_, hl⟩ ar hc
  exact hleft
end HolomorphicAnosov.TorusRationalCupBasisKronecker
