import HolomorphicAnosov.Topology.Homology.RationalScalarTransport

/-!
# Naturality of rational scalar transport

The coefficient and chain comparisons commute with simplicial maps, and conjugating
a natural bilinear chain operation by these comparisons preserves naturality.
This is the explicit scalar-comparison step in Bredon, *Topology and Geometry*,
VI §1, pp.316–318. The universe-lift adapter itself is a Lean-specific argument,
proved here from Mathlib's natural scalar comparison and tensor universal property.
DAG node: `algebra.rational_scalar_transport_naturality_g7`.
-/

noncomputable section
open CategoryTheory
open scoped TensorProduct
universe u

namespace HolomorphicAnosov.RationalScalarTransport

/-- Scalar transport retains the value of a bilinear operation on pure tensors.
Proof: the compatible-scalar tensor equivalence fixes pure tensors, and restriction
of scalars retains the underlying additive map. -/
theorem tensorMapTransport_tmul (M N P : ModuleCat.{u} ℚ)
    (f : M ⊗[ℚ] N →ₗ[ℚ] P) (a : scalarFunctor.obj M) (b : scalarFunctor.obj N) :
    tensorMapTransport M N P f (a ⊗ₜ[LiftQ.{u}] b) = f (a ⊗ₜ[ℚ] b) := by
  rfl

/-- The native chain comparison is natural in the simplicial set.
Proof: compose the natural scalar-change comparison with the natural coefficient
isomorphism and take its naturality square. -/
theorem nativeChainComparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    (scalarFunctor.mapHomologicalComplex (.down ℕ)).map
        (SSet.chainComplexMap f qCoefficients) ≫ (nativeChainComparison Y).hom =
      (nativeChainComparison X).hom ≫
        SSet.chainComplexMap f (ModuleCat.of LiftQ.{u} LiftQ.{u}) := by
  exact ((SSet.chainComplexFunctorObjCompMapIso.{u} scalarFunctor qCoefficients) ≪≫
    (SSet.chainComplexFunctor (ModuleCat.{u} LiftQ.{u})).mapIso
      coefficientComparison).hom.naturality f

/-- The inverse comparison is natural as well, by inverse-isomorphism naturality. -/
theorem nativeChainComparison_inv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.chainComplexMap f (ModuleCat.of LiftQ.{u} LiftQ.{u}) ≫
        (nativeChainComparison Y).inv =
      (nativeChainComparison X).inv ≫
        (scalarFunctor.mapHomologicalComplex (.down ℕ)).map
          (SSet.chainComplexMap f qCoefficients) := by
  exact ((SSet.chainComplexFunctorObjCompMapIso.{u} scalarFunctor qCoefficients) ≪≫
    (SSet.chainComplexFunctor (ModuleCat.{u} LiftQ.{u})).mapIso
      coefficientComparison).inv.naturality f

/-- The transported component evaluated on a pure tensor is the original component
between the inverse and forward native comparisons. Proof: evaluate the tensor map
on the pure tensor and use preservation of pure tensors under scalar transport. -/
theorem nativeShuffleComponent_tmul (X Y Z : SSet.{u}) (p q : ℕ)
    (sh : (X.chainComplex qCoefficients).X p ⊗[ℚ]
      (Y.chainComplex qCoefficients).X q →ₗ[ℚ]
      (Z.chainComplex qCoefficients).X (p + q))
    (a : (X.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X p)
    (b : (Y.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X q) :
    nativeShuffleComponent X Y Z p q sh (a ⊗ₜ[LiftQ.{u}] b) =
      ((nativeChainComparison Z).hom.f (p + q)).hom
        (sh (((nativeChainComparison X).inv.f p).hom a ⊗ₜ[ℚ]
          ((nativeChainComparison Y).inv.f q).hom b)) := by
  rfl

/-- Conjugating a natural rational bilinear chain operation by the native scalar
comparisons preserves naturality. Proof: on a pure tensor, move each source map
through its inverse comparison; apply rational naturality; then move the output
map through the forward comparison. No injectivity or nonemptiness is needed. -/
theorem nativeShuffleComponent_naturality
    {X Y Z X' Y' Z' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
    (p q : ℕ)
    (sh : (X.chainComplex qCoefficients).X p ⊗[ℚ]
      (Y.chainComplex qCoefficients).X q →ₗ[ℚ]
      (Z.chainComplex qCoefficients).X (p + q))
    (sh' : (X'.chainComplex qCoefficients).X p ⊗[ℚ]
      (Y'.chainComplex qCoefficients).X q →ₗ[ℚ]
      (Z'.chainComplex qCoefficients).X (p + q))
    (hnat : ∀ a b,
      (SSet.chainComplexMap h qCoefficients).f (p + q) (sh (a ⊗ₜ[ℚ] b)) =
        sh' ((SSet.chainComplexMap f qCoefficients).f p a ⊗ₜ[ℚ]
          (SSet.chainComplexMap g qCoefficients).f q b))
    (a : (X.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X p)
    (b : (Y.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X q) :
    (SSet.chainComplexMap h (ModuleCat.of LiftQ.{u} LiftQ.{u})).f (p + q)
        (nativeShuffleComponent X Y Z p q sh (a ⊗ₜ[LiftQ.{u}] b)) =
      nativeShuffleComponent X' Y' Z' p q sh'
        ((SSet.chainComplexMap f (ModuleCat.of LiftQ.{u} LiftQ.{u})).f p a ⊗ₜ[LiftQ.{u}]
          (SSet.chainComplexMap g (ModuleCat.of LiftQ.{u} LiftQ.{u})).f q b) := by
  have hf := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.f p) (nativeChainComparison_inv_naturality f)) a
  have hg := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.f q) (nativeChainComparison_inv_naturality g)) b
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.f (p + q)) (nativeChainComparison_naturality h))
    (sh (((nativeChainComparison X).inv.f p).hom a ⊗ₜ[ℚ]
      ((nativeChainComparison Y).inv.f q).hom b))
  simp only [nativeShuffleComponent_tmul]
  change ((nativeChainComparison X').inv.f p).hom
    ((SSet.chainComplexMap f (ModuleCat.of LiftQ.{u} LiftQ.{u})).f p a) =
    (SSet.chainComplexMap f qCoefficients).f p
      (((nativeChainComparison X).inv.f p).hom a) at hf
  change ((nativeChainComparison Y').inv.f q).hom
    ((SSet.chainComplexMap g (ModuleCat.of LiftQ.{u} LiftQ.{u})).f q b) =
    (SSet.chainComplexMap g qCoefficients).f q
      (((nativeChainComparison Y).inv.f q).hom b) at hg
  rw [hf, hg]
  exact hh.symm.trans (congrArg ((nativeChainComparison Z').hom.f (p + q)).hom (hnat _ _))

end HolomorphicAnosov.RationalScalarTransport


