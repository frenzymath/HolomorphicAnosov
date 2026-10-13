import HolomorphicAnosov.Algebra.Homology.FieldChainKroneckerEvaluation
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductNaturality
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative

open CategoryTheory

noncomputable section

namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- Pullback preserves every rational singular cup product specified by the cocycle formula.

Source: Hatcher, Algebraic Topology, Proposition 3.10 p210. Choose cocycle
representatives of both input classes using quotient surjectivity. Pullback
maps them to cocycles, and the quotient-map representative identity computes
their cohomology classes. The two representative hypotheses identify the cup
products with cup cochains. Naturality on cochains and the same quotient-map
identity then identify the two resulting classes. -/
theorem specified_cup_naturality
    {X Y : TopCat} (f : X ⟶ Y)
    (cupX : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ]
        SingularCochain.cohomology ℚ X (p + q))
    (cupY : ∀ p q : ℕ, SingularCochain.cohomology ℚ Y p →ₗ[ℚ]
      SingularCochain.cohomology ℚ Y q →ₗ[ℚ]
        SingularCochain.cohomology ℚ Y (p + q))
    (hrepX : ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        cupX p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩)
    (hrepY : ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ Y) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ Y) q),
      ∃ hc : SingularCochain.cupCochain ℚ Y b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ Y) (p + q),
        cupY p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) (p + q)
            ⟨SingularCochain.cupCochain ℚ Y b.val c.val, hc⟩) :
    ∀ p q (a : SingularCochain.cohomology ℚ Y p)
      (b : SingularCochain.cohomology ℚ Y q),
      (SingularCochain.cohomologyPullback ℚ f (p + q))
          (cupY p q a b) =
        cupX p q ((SingularCochain.cohomologyPullback ℚ f p) a)
          ((SingularCochain.cohomologyPullback ℚ f q) b) := by
  intro p q a b
  obtain ⟨a', rfl⟩ := (show Function.Surjective
    (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) p) from
    Submodule.mkQ_surjective _) a
  obtain ⟨b', rfl⟩ := (show Function.Surjective
    (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) q) from
    Submodule.mkQ_surjective _) b
  let F := SingularCochain.pullback ℚ f
  let af : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p :=
    ⟨(F.f p).hom a'.val, FieldChainKronecker.map_cycle_mem F p a'⟩
  let bf : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q :=
    ⟨(F.f q).hom b'.val, FieldChainKronecker.map_cycle_mem F q b'⟩
  have ha := quotient_map_representative F p a' af rfl
  have hb := quotient_map_representative F q b' bf rfl
  change (SingularCochain.cohomologyPullback ℚ f p)
    (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) p a') =
    SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p af at ha
  change (SingularCochain.cohomologyPullback ℚ f q)
    (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) q b') =
    SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q bf at hb
  rw [ha, hb]
  obtain ⟨hY, heY⟩ := hrepY p q a' b'
  obtain ⟨hX, heX⟩ := hrepX p q af bf
  rw [heY, heX]
  exact quotient_map_representative F (p + q) ⟨_, hY⟩ ⟨_, hX⟩
    (SingularCochain.pullback_cupCochain ℚ f a'.val b'.val)


end HolomorphicAnosov.TorusRationalCupBasisKronecker
