import HolomorphicAnosov.AlgebraicTopology.SingularMixedCupProduct
import HolomorphicAnosov.AlgebraicTopology.SingularCochainReversalCup
import HolomorphicAnosov.AlgebraicTopology.SingularCochainReversalCohomology

/-!
# Ordinary and relative singular cup-product laws

Source: Hatcher, *Algebraic Topology*, cup formula and Lemma 3.6,
pp. 206–207; associativity, distributivity and unit p. 207; same-subspace
relative products pp. 209–210; Proposition 3.10 p. 210; Theorem 3.11 and
its full vertex-reversal/prism proof pp. 210–212.

All modules below are the genuine singular cochain kernel/image quotients.
A Boolean tag false denotes ordinary cohomology and true denotes cohomology
relative to A. The target tag i || j says that a relative factor makes the
product relative. Dependent equalities in associativity, units and graded
commutativity only identify equal natural-number degrees and Boolean tags.
The relative pullback is specified by its commutative square with the
canonical inclusions into the ordinary cochain complex. No new cohomology
model, topology on R, excision assumption or independent graded algebra is used.
-/

open CategoryTheory CategoryTheory.Limits

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
open MixedCup

set_option backward.isDefEq.respectTransparency false in
/-- The front/back singular cochain formula descends to bilinear ordinary,
mixed and same-subspace relative cup products, with their associativity,
unit, pullback naturality and graded commutativity.

Source: Hatcher, *Algebraic Topology*, pp. 206–212, specifically Lemma 3.6,
Proposition 3.10 and Theorem 3.11. The existentially quantified products act
on the literal kernel/image quotients; their representative clause fixes them
to the concrete cochain formula. The pullback clause fixes the relative
cochain maps by the universal property of the existing restriction kernels.

Natural-language proof:

1. Leibniz and descent. Expand δ(a∪b) on each (p+q+1)-simplex. The omitted vertices before the shared vertex give δa∪b; the omitted vertices after it give (−1)^p a∪δb. The last face of the first sum and first face of the second have the same restrictions and opposite signs, hence cancel. Thus δ(a∪b)=δa∪b+(−1)^p a∪δb. Cocycles multiply to cocycles; replacing either factor by a coboundary changes the product by a coboundary, by this identity. If either factor vanishes on chains in A, so does its product on an A-simplex. This proves descent and the mixed relative variants.

2. Associativity, bilinearity, unit and pullback. For three cochains, both associations evaluate on σ as the product of evaluations on consecutive faces [0,…,p], [p,…,p+q] and [p+q,…,p+q+r]; ring associativity proves equality. Distributivity and scalar linearity follow in the same formula. The constant0-cochain1 is a cocycle and its front/back face value is1, giving both units. Postcomposition fσ commutes with every face restriction, so (f^♯a∪f^♯b)(σ)=(a∪b)(fσ), including the relative case.

3. Reversal chain map. For an m-simplex σ let rev σ reverse its ordered vertices and ε_m=(−1)^(m(m+1)/2). Define ρ_mσ=ε_m rev σ. Reversing an omitted vertex changes its face index i to m−i. The equality ε_m=(−1)^m ε_(m−1) therefore gives ∂ρ=ρ∂ term by term.

4. Explicit chain homotopy. In Δ^m×I denote bottom vertices v_i and top vertices w_i, and let π be projection to Δ^m. Set P_mσ=Σ_(i=0)^m(−1)^i ε_(m−i)(σπ)|[v_0,…,v_i,w_m,…,w_i]. Expand ∂P: the faces obtained by omitting v_i or w_i cancel with the matching adjacent prism face; reindexing i to i−1 uses ε_(m−i+1)=(−1)^(m−i+1)ε_(m−i). The two uncancelled end faces are ε_m[ w_m,…,w_0 ] and −[v_0,…,v_m], hence ρσ−σ. Faces omitting v_j with j<i cancel the corresponding P∂ terms with signs (−1)^(i+j) versus (−1)^(i−1+j). Faces omitting w_j with j>i cancel the corresponding P∂ terms using ε_(m−i)=(−1)^(m−i)ε_(m−i−1). Therefore ∂P+P∂=ρ−id. For m=0 both endpoint projections coincide, giving the same identity; no degree−1 operator is required. All simplices in P of a chain in A still map into A. Dualizing the identity gives a cochain homotopy, so ρ^* is identity on absolute and relative cohomology.

5. Graded sign. The front/back evaluations in the reversed simplex give ρ^*a∪ρ^*b=(−1)^(pq)ρ^*(b∪a): commute the two R-valued factors and use ε_(p+q)=(−1)^(pq)ε_pε_q. Since ρ^* induces identity, the equation becomes the asserted graded commutativity. This does not infer an odd square is zero over arbitrary R merely from twice that square being zero.

The quotient projections are surjective, so the representative formulas
uniquely determine the descended products. For a map of pairs, restriction
commutes with pullback because both are precomposition by the same continuous
map on singular simplices. The ordinary pullback therefore restricts to the
relative kernels, giving the displayed cochain square. Applying the literal
quotient map gives the stated naturality. Degree zero uses the unaugmented
complex, so its incoming boundary is zero. Empty spaces, A empty or all of X,
the zero coefficient ring, and degrees p or q zero require no exceptions.
-/
theorem singular_cup_product_laws (R : Type u) [CommRing R] :
    ∃ μ : ∀ (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ),
      cupCohomology R X A i p →ₗ[R]
        cupCohomology R X A j q →ₗ[R] cupCohomology R X A (i || j) (p + q),
    ∃ pb : ∀ {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Set X) (B : Set Y),
      Set.MapsTo f A B → ∀ i : Bool, cupComplex R Y B i ⟶ cupComplex R X A i,
      (∀ (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ)
          (a : cycles R (cupComplex R X A i) p)
          (b : cycles R (cupComplex R X A j) q),
        ∃ c : cycles R (cupComplex R X A (i || j)) (p + q),
          (cupInclusion R X A (i || j)).f (p + q) c.val =
            cupCochain R X ((cupInclusion R X A i).f p a.val)
              ((cupInclusion R X A j).f q b.val) ∧
          μ X A i j p q (cocycleClass R (cupComplex R X A i) p a)
            (cocycleClass R (cupComplex R X A j) q b) =
              cocycleClass R (cupComplex R X A (i || j)) (p + q) c) ∧
      (∀ (X : TopCat.{u}) (A : Set X) (i j k : Bool) (p q r : ℕ)
          (a : cupCohomology R X A i p) (b : cupCohomology R X A j q)
          (c : cupCohomology R X A k r),
        HEq (μ X A (i || j) k (p + q) r (μ X A i j p q a b) c)
          (μ X A i (j || k) p (q + r) a (μ X A j k q r b c))) ∧
      (∀ X : TopCat.{u}, ∃ one : cycles R (complex R X) 0,
        one.val = oneCochain R X ∧
        ∀ (A : Set X) (i : Bool) (p : ℕ) (a : cupCohomology R X A i p),
          HEq (μ X A false i 0 p (cocycleClass R (complex R X) 0 one) a) a ∧
          HEq (μ X A i false p 0 a (cocycleClass R (complex R X) 0 one)) a) ∧
      (∀ {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Set X) (B : Set Y)
          (hf : Set.MapsTo f A B) (i : Bool),
        pb f A B hf i ≫ cupInclusion R X A i =
          cupInclusion R Y B i ≫ pullback R f) ∧
      (∀ {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Set X) (B : Set Y)
          (hf : Set.MapsTo f A B) (i j : Bool) (p q : ℕ)
          (a : cupCohomology R Y B i p) (b : cupCohomology R Y B j q),
        quotientMap R (pb f A B hf (i || j)) (p + q) (μ Y B i j p q a b) =
          μ X A i j p q (quotientMap R (pb f A B hf i) p a)
            (quotientMap R (pb f A B hf j) q b)) ∧
      (∀ (X : TopCat.{u}) (A : Set X) (i : Bool) (p q : ℕ)
          (a : cupCohomology R X A i p) (b : cupCohomology R X A i q),
        HEq (μ X A i i p q a b) (((-1 : R) ^ (p * q)) • μ X A i i q p b a)) := by
  refine ⟨descended_cup R, tagged_pullback R, ?_, descended_cup_assoc R, ?_,
    tagged_pullback_square R, descended_cup_naturality R, ?_⟩
  · intro X A i j p q a b
    refine ⟨tagged_cup_linear R X A i j p q a b, ?_, ?_⟩
    · exact tagged_cochain_cup_inclusion R X A i j p q a.val b.val
    · exact descended_cup_representatives R X A i j p q a b
  · intro X
    refine ⟨unit_cocycle R X, rfl, ?_⟩
    intro A i p a
    obtain ⟨a, rfl⟩ := cocycleClass_surjective R _ p a
    exact ⟨tagged_cup_unit_left R X A i p a, tagged_cup_unit_right R X A i p a⟩
  · intro X A i p q a b
    obtain ⟨a, rfl⟩ := cocycleClass_surjective R _ p a
    obtain ⟨b, rfl⟩ := cocycleClass_surjective R _ q b
    obtain ⟨ar, har, hclassa⟩ := exists_reverse_cocycle R X A i p a
    obtain ⟨br, hbr, hclassb⟩ := exists_reverse_cocycle R X A i q b
    let d := tagged_cup_linear R X A i i q p b a
    obtain ⟨dr, hdr, hclassd⟩ := exists_reverse_cocycle R X A (i || i) (q+p) d
    have hleft : descended_cup R X A i i p q (cocycleClass R _ p a)
        (cocycleClass R _ q b) =
        cocycleClass R _ (p+q) (tagged_cup_linear R X A i i p q ar br) := by
      rw [← hclassa, ← hclassb, descended_cup_representatives]
    rw [hleft, descended_cup_representatives]
    change HEq _ (((-1:R)^(p*q)) • cocycleClass R _ (q+p) d)
    rw [← hclassd, ← map_smul]
    apply class_heq_of_inclusion_cast R X A rfl (Nat.add_comm p q)
    change ((complex R X).XIsoOfEq (Nat.add_comm p q)).hom
        ((cupInclusion R X A (i || i)).f (p+q)
          (tagged_cochain_cup R X A i i p q ar.val br.val)) =
      (cupInclusion R X A (i || i)).f (q+p) ((((-1:R)^(p*q)) • dr).val)
    simp only [Submodule.coe_smul, map_smul, tagged_cochain_cup_inclusion, har, hbr, hdr]
    change ((complex R X).XIsoOfEq (Nat.add_comm p q)).hom
        (cupCochain R X
          (reverseCochain R X p ((cupInclusion R X A i).f p a.val))
          (reverseCochain R X q ((cupInclusion R X A i).f q b.val))) =
      (-1:R)^(p*q) • reverseCochain R X (q+p)
        ((cupInclusion R X A (i || i)).f (q+p)
          (tagged_cochain_cup R X A i i q p b.val a.val))
    rw [tagged_cochain_cup_inclusion]
    exact reverseCochain_cup R X p q _ _

end HolomorphicAnosov.SingularCochain
