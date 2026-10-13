import HolomorphicAnosov.Topology.SignedSingularCrossProduct

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- The boundary of the explicit signed staircase simplex product before pairing
interior faces. Source: Hatcher, *Algebraic Topology*, §3.B, pp.277--278.
The native singular face differential distributes over the finite staircase sum,
leaving the alternating sum of the faces of each product simplex. -/
lemma simplexProduct_boundary_expansion {X Y : TopCat.{u}} {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y (q + 1)) :
    (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
      (ModuleCat.of ℤ (ULift.{u} ℤ))).d (p + (q + 1)) (p + q)).hom
        (simplexProduct X Y σ τ) =
      ∑ w ∈ staircases p (q + 1), orientation w •
        ∑ i : Fin (p + q + 2), (-1 : ℤ) ^ i.val •
          ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
            (R := (ModuleCat.of ℤ (ULift.{u} ℤ)))
            ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i
              (productSimplex (p := p) (q := q + 1) X Y w σ τ))).hom (ULift.up 1) := by
  simp only [simplexProduct, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  change (((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
      (R := (ModuleCat.of ℤ (ULift.{u} ℤ))) (productSimplex X Y w σ τ)) ≫
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
        (ModuleCat.of ℤ (ULift.{u} ℤ))).d (p + q + 1) (p + q)).hom (ULift.up 1) = _
  rw [SSet.ιChainComplex_d (n := p + q)]
  simp

end HolomorphicAnosov.SignedSingularCrossProduct
