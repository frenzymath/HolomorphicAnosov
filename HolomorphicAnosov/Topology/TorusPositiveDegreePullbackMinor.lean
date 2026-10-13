import HolomorphicAnosov.Algebra.GradedRingOfBilinearProduct
import HolomorphicAnosov.AlgebraicTopology.GradedAlgebraOfBilinear
import HolomorphicAnosov.Algebra.ExteriorCupMinorG3
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupAssocUnit
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupNaturality
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AbsoluteCupData
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.OddSquareZero
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.PullbackOneCochain

open CategoryTheory
open scoped BigOperators DirectSum
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HolomorphicAnosov
open TorusRationalCupBasisKronecker

/-- Generic exterior-power coefficient calculation used by the native cup bridge. -/
theorem exterior_power_principal_minor_adapter_g3
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (n k : ℕ) (b : Module.Basis (Fin n) ℚ W)
    (g : W →ₗ[ℚ] W) (S : Set.powersetCard (Fin n) k) :
    (b.exteriorPower k).repr (exteriorPower.map k g (b.exteriorPower k S)) S =
      ((LinearMap.toMatrix b b g).submatrix
        (Subtype.val : S.val → Fin n) (Subtype.val : S.val → Fin n)).det := by
  exact exterior_power_minor_diagonal n k b g S

/-- Native singular pullback has the principal-minor coefficient in the ordered
cup basis, provided its action on the degree-one generators is the stated matrix.

Source: Hatcher, Example 3.13 p.213 and Theorem 3.15 pp.216–218; Manning (1974),
p.424. The old arbitrary-linear-map statement was false: for n=k=1, B=1 and
f=0 its conclusion was 0=1. This corrected statement specifies the native
pullback, the actual Alexander–Whitney cup product, the ordered cup basis, and
the necessary degree-one compatibility. The torus Lefschetz caller proves that
compatibility from positive winding and rational singular loop naturality.

The specified cochain formula identifies the cup product with the native one,
so it is associative and has its constant-one unit. Graded commutativity over
ℚ makes all degree-one squares vanish. Form the graded direct sum and extend
the degree-one inclusion to the exterior algebra. Pullback preserves its unit
and products by the cochain formulas, hence acts on the ordered basis by the
exterior power of the transpose of B. The exterior coefficient formula gives
the principal minor, unchanged by transposition. The proof also covers k=0. -/
theorem torus_positive_degree_pullback_principal_minor
    (n : ℕ) (B : Matrix (Fin n) (Fin n) ℚ)
    (X : TopCat) (u : X ⟶ X)
    (cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ]
        SingularCochain.cohomology ℚ X (p + q))
    (one : SingularCochain.cohomology ℚ X 0)
    (α : Fin n → SingularCochain.cohomology ℚ X 1)
    (b : ∀ k, Module.Basis (Set.powersetCard (Fin n) k) ℚ
      (SingularCochain.cohomology ℚ X k))
    (hrep : ∀ p q (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (d : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X c.val d.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        cup p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p c)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q d) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X c.val d.val, hc⟩)
    (hunit : ∃ hu : SingularCochain.oneCochain ℚ X ∈
        SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) 0,
      one = SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0
        ⟨SingularCochain.oneCochain ℚ X, hu⟩)
    (hb : let H := fun d ↦ (SingularCochain.cohomology ℚ X d : Type)
      let monomial : ∀ l : List (Fin n), H l.length := fun l ↦
        List.rec (motive := fun l ↦ H l.length) one
          (fun i l v ↦ cast (congrArg H (Nat.add_comm 1 l.length))
            (cup 1 l.length (α i) v)) l
      ∀ k S, b k S = cast (congrArg H
        ((S.val.length_sort (· ≤ ·)).trans S.property)) (monomial (S.val.sort (· ≤ ·))))
    (hα : ∀ i, (SingularCochain.cohomologyPullback ℚ u 1) (α i) =
      ∑ j, B i j • α j)
    (k : ℕ) (S : Set.powersetCard (Fin n) k) :
    (b k).repr ((SingularCochain.cohomologyPullback ℚ u k) (b k S)) S =
      (B.submatrix (Subtype.val : S.val → Fin n) (Subtype.val : S.val → Fin n)).det := by
  classical
  let H := fun d ↦ (SingularCochain.cohomology ℚ X d : Type)
  obtain ⟨hassoc, hlaws⟩ := specified_cup_assoc_unit X cup one hrep hunit
  let := gradedRingOfBilinearProduct ℚ H cup one
    (fun p x ↦ (hlaws p x).1) (fun p x ↦ (hlaws p x).2) hassoc
  have hG (p q : ℕ) (x : H p) (y : H q) :
      GradedMonoid.GMul.mul x y = cup p q x y := rfl
  have hGone : (GradedMonoid.GOne.one : H 0) = one := rfl
  let := (AlgebraicTopology.graded_algebra_of_bilinear ℚ H cup hG).some
  have hsq : ∀ x : H 1, GradedMonoid.GMul.mul x x = 0 := by
    intro x
    rw [hG]
    obtain ⟨μ, _, hμ, _, hcomm, _⟩ := absolute_cup_data X
    have he := cup_eq_of_representatives X 1 1 (cup 1 1) (μ 1 1) (hrep 1 1) (hμ 1 1)
    rw [he]
    exact odd_square_zero (μ 1 1) hcomm x
  have hprod (d : ℕ) (U : Set.powersetCard (Fin n) d) :
      DirectSum.lof ℚ ℕ H d (b d U) =
        ((U.val.sort (· ≤ ·)).map (fun i ↦ DirectSum.lof ℚ ℕ H 1 (α i))).prod := by
    rw [hb d U]
    have hc {p q : ℕ} (h : p = q) (x : H p) :
        DirectSum.lof ℚ ℕ H q (cast (congrArg H h) x) = DirectSum.lof ℚ ℕ H p x := by
      subst q
      rfl
    rw [hc ((U.val.length_sort (· ≤ ·)).trans U.property)]
    exact graded_monomial_product_g3 H cup one hG hGone α _
  let f := fun d ↦ (SingularCochain.cohomologyPullback ℚ u d).hom
  have hf0 : f 0 (GradedMonoid.GOne.one : H 0) = (GradedMonoid.GOne.one : H 0) := by
    rw [hGone]
    obtain ⟨hu, heq⟩ := hunit
    rw [heq]
    exact quotient_map_representative (SingularCochain.pullback ℚ u) 0
      ⟨_, hu⟩ ⟨_, hu⟩ (pullback_oneCochain u)
  apply graded_cup_basis_minor_g3 H n k α (b k) hsq (hprod k) f hf0 ?_ B hα S
  intro p q x y
  simp only [hG]
  exact specified_cup_naturality u cup cup hrep hrep p q x y

end HolomorphicAnosov
