import HolomorphicAnosov.Algebra.Homology.FieldChainKroneckerEvaluation
import HolomorphicAnosov.AlgebraicTopology.FiniteCWCohomologyCrossProductKunneth
import HolomorphicAnosov.AlgebraicTopology.SingularCupProductLaws
import HolomorphicAnosov.Topology.CircleSingularCohomologyWinding
import HolomorphicAnosov.Topology.RealTorusCoordinateCWStructure
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finset.Sort

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The native cup-law provider gives absolute products with their universal original
cocycle formula, a constant-one representative and the degree-one sign law. -/
theorem absolute_cup_data (X : TopCat) :
    ∃ (cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
          SingularCochain.cohomology ℚ X q →ₗ[ℚ]
            SingularCochain.cohomology ℚ X (p + q))
      (one : SingularCochain.cohomology ℚ X 0),
      (∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
          (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
        ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
            SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
          cup p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
              (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
            SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
              ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩) ∧
      (∃ hu : SingularCochain.oneCochain ℚ X ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) 0,
        one = SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0
          ⟨SingularCochain.oneCochain ℚ X, hu⟩) ∧
      (∀ a b : SingularCochain.cohomology ℚ X 1,
        cup 1 1 a b = -cup 1 1 b a) ∧
      (∀ (f : X ⟶ X) p q (a : SingularCochain.cohomology ℚ X p)
          (b : SingularCochain.cohomology ℚ X q),
        (SingularCochain.cohomologyPullback ℚ f (p + q)) (cup p q a b) =
          cup p q ((SingularCochain.cohomologyPullback ℚ f p) a)
            ((SingularCochain.cohomologyPullback ℚ f q) b)) ∧
      (∀ a : SingularCochain.cohomology ℚ X 1, cup 1 0 a one = a) := by
  obtain ⟨μ, pb, hrep, hassoc, hunit, hpbsq, hnat, hcomm⟩ :=
    SingularCochain.singular_cup_product_laws ℚ
  let cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ]
        SingularCochain.cohomology ℚ X (p + q) := fun p q ↦ μ X ∅ false false p q
  obtain ⟨u, hu, hulaw⟩ := hunit X
  refine ⟨cup, SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0 u,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro p q b c
    obtain ⟨d, hd, he⟩ := hrep X ∅ false false p q b c
    change d.val = SingularCochain.cupCochain ℚ X b.val c.val at hd
    have hdmem : SingularCochain.cupCochain ℚ X b.val c.val ∈
        SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q) := hd ▸ d.property
    refine ⟨hdmem, ?_⟩
    exact he.trans (congrArg
      (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q))
      (show d = ⟨SingularCochain.cupCochain ℚ X b.val c.val, hdmem⟩ from Subtype.ext hd))
  · refine ⟨hu ▸ u.property, ?_⟩
    congr 1
    exact Subtype.ext hu
  · intro a b
    have he := hcomm X ∅ false 1 1 a b
    have hh : cup 1 1 a b = (-1 : ℚ) • cup 1 1 b a := eq_of_heq he
    simpa only [neg_one_smul] using hh

  · intro f p q a b
    have hpb : pb f ∅ ∅ (by simp) false = SingularCochain.pullback ℚ f := by
      have he := hpbsq f ∅ ∅ (by simp) false
      change pb f ∅ ∅ (by simp) false ≫ 𝟙 _ = 𝟙 _ ≫ SingularCochain.pullback ℚ f at he
      simpa only [Category.comp_id, Category.id_comp] using he
    have he := hnat f ∅ ∅ (by simp) false false p q a b
    change (SingularCochain.quotientMap ℚ (pb f ∅ ∅ (by simp) false) (p + q))
      (cup p q a b) = cup p q
        ((SingularCochain.quotientMap ℚ (pb f ∅ ∅ (by simp) false) p) a)
        ((SingularCochain.quotientMap ℚ (pb f ∅ ∅ (by simp) false) q) b) at he
    rw [hpb] at he
    exact he
  · intro a
    exact eq_of_heq (hulaw ∅ false 1 a).2


end HolomorphicAnosov.TorusRationalCupBasisKronecker

