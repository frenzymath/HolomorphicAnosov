import HolomorphicAnosov.Topology.Homology.RationalRelativeTensorComparison

/-!
# Rational relative tensor representatives

Source: Bredon VI pp.318–320; Hatcher pp.277–278. The canonical scalar
comparisons preserve the prescribed shuffle on every projected pure tensor.
DAG node: `topo.rational_relative_tensor_representative_g1`.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe u
namespace HolomorphicAnosov.RationalRelativeTensorComparison
open RationalScalarTransport NativeRelativeShuffleComparison SingularEilenbergZilber
set_option backward.isDefEq.respectTransparency false

private theorem tensorHom_entry
    {C D C' D' : ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (p q : ℕ) (a : C.X p) (b : D.X q) :
    (HomologicalComplex.tensorHom f g).f (p + q)
      ((HomologicalComplex.ιTensorObj C D p q (p+q) rfl) (a ⊗ₜ[LiftQ.{u}] b)) =
    (HomologicalComplex.ιTensorObj C' D' p q (p+q) rfl)
      ((f.f p a) ⊗ₜ[LiftQ.{u}] (g.f q b)) := by
  change (HomologicalComplex.ιTensorObj C D p q (p+q) rfl ≫
    (HomologicalComplex.tensorHom f g).f (p+q)) (a ⊗ₜ[LiftQ.{u}] b) = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rfl

private theorem comparison_projection_apply (X : TopCat.{u}) (B : Set X)
    (p : ℕ) (a : (rationalAbsolute X).X p) :
    (nativeRelativeChainComparison (nativePair X B)).hom.f p
      (((nativePair X B).chainComplexπ qCoefficients).f p a) =
    ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u})).f p
      ((nativeChainComparison (TopCat.toSSet.obj X)).hom.f p a) := by
  exact congrArg (fun f ↦ f.f p a)
    (nativeRelativeChainComparison_projection (nativePair X B))

/-- The transported relative shuffle takes a projected pure tensor to the projected
prescribed rational shuffle. Source: Bredon VI pp.318–320. Move the tensor factors
through the canonical native comparisons, apply the relative projection square and
the native shuffle's pure-tensor formula, and cancel the target comparison. -/
theorem transportNativeEquivalence_projected_tensor (X Y : TopCat.{u}) (B : Set X)
    (e : HomotopyEquiv
      (HomologicalComplex.tensorObj (relativeComplex X B) (chainFunctor.obj Y))
      (relativeComplex (TopCat.of (X × Y)) (productSupport X Y B)))
    (he : HomologicalComplex.tensorHom
      ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}))
      (𝟙 (chainFunctor.obj Y)) ≫ e.hom =
      shuffleChainMap X Y ≫
        (nativePair (TopCat.of (X × Y)) (productSupport X Y B)).chainComplexπ
          (ModuleCat.of LiftQ.{u} LiftQ.{u}))
    (p q : ℕ) (a : (rationalAbsolute X).X p) (b : (rationalAbsolute Y).X q) :
    (transportNativeEquivalence X Y B e).hom.f (p+q)
      (FieldTensorHomologyKunneth.ArbitraryUniverse.tensorChain
        (rationalRelative X B) (rationalAbsolute Y) p q (p+q) rfl
        (((nativePair X B).chainComplexπ qCoefficients).f p a) b) =
    ((nativePair (TopCat.of (X × Y)) (productSupport X Y B)).chainComplexπ
      qCoefficients).f (p+q) (SignedShuffle.shuffleBilinear X Y p q a b) := by
  let r := nativeRelativeChainComparison (nativePair X B)
  let s := nativeChainComparison (TopCat.toSSet.obj Y)
  let t := nativeRelativeChainComparison
    (nativePair (TopCat.of (X × Y)) (productSupport X Y B))
  let A := (nativeChainComparison (TopCat.toSSet.obj X)).hom.f p a
  let C := s.hom.f q b
  have hp := comparison_projection_apply X B p a
  have he' := congrArg (fun f ↦ f.f (p+q)
    ((HomologicalComplex.ιTensorObj (chainFunctor.obj X) (chainFunctor.obj Y)
      p q (p+q) rfl) (A ⊗ₜ[LiftQ.{u}] C))) he
  change e.hom.f (p+q) ((HomologicalComplex.tensorHom
    ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}))
    (𝟙 (chainFunctor.obj Y))).f (p+q) _) = _ at he'
  have hentry := tensorHom_entry
    ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}))
    (𝟙 (chainFunctor.obj Y)) p q A C
  erw [hentry] at he'
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at he'
  change t.inv.f (p+q) (e.hom.f (p+q)
    ((HomologicalComplex.tensorHom r.hom s.hom).f (p+q)
      ((HomologicalComplex.ιTensorObj
        ((scalarFunctor.mapHomologicalComplex (.down ℕ)).obj (rationalRelative X B))
        (transportedChains (TopCat.toSSet.obj Y)) p q (p+q) rfl)
        ((((nativePair X B).chainComplexπ qCoefficients).f p a) ⊗ₜ[LiftQ.{u}] b)))) = _
  erw [tensorHom_entry r.hom s.hom p q _ b]
  change t.inv.f (p+q) (e.hom.f (p+q)
    ((HomologicalComplex.ιTensorObj (relativeComplex X B) (chainFunctor.obj Y)
      p q (p+q) rfl)
      ((r.hom.f p _) ⊗ₜ[LiftQ.{u}] C))) = _
  rw [hp, he']
  change t.inv.f (p+q) (((nativePair (TopCat.of (X × Y))
    (productSupport X Y B)).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u})).f (p+q)
      ((shuffle.app (X,Y)).f (p+q) _)) = _
  rw [shuffle_pure_tensor]
  change t.inv.f (p+q) (((nativePair (TopCat.of (X × Y))
    (productSupport X Y B)).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u})).f (p+q)
      (nativeShuffleComponent _ _ _ p q _ (A ⊗ₜ[LiftQ.{u}] C))) = _
  rw [nativeShuffleComponent_tmul]
  have ha : (nativeChainComparison (TopCat.toSSet.obj X)).inv.f p A = a := by
    exact congrArg (fun f ↦ f.f p a)
      (nativeChainComparison (TopCat.toSSet.obj X)).hom_inv_id
  have hb : (nativeChainComparison (TopCat.toSSet.obj Y)).inv.f q C = b := by
    exact congrArg (fun f ↦ f.f q b) s.hom_inv_id
  rw [ha, hb]
  change t.inv.f (p+q) (((nativePair (TopCat.of (X × Y))
    (productSupport X Y B)).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u})).f (p+q)
      ((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f (p+q)
        (SignedShuffle.shuffleBilinear X Y p q a b))) = _
  rw [← comparison_projection_apply (TopCat.of (X × Y)) (productSupport X Y B)]
  exact congrArg (fun f ↦ f.f (p+q)
    (((nativePair (TopCat.of (X × Y)) (productSupport X Y B)).chainComplexπ
      qCoefficients).f (p+q) (SignedShuffle.shuffleBilinear X Y p q a b))) t.hom_inv_id

end HolomorphicAnosov.RationalRelativeTensorComparison

