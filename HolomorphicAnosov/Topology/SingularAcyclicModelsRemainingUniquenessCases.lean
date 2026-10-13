import HolomorphicAnosov.Topology.SingularAcyclicModelsBAUniqueness

/-!
# The remaining natural singular acyclic-model uniqueness cases

Source: Barr, *Acyclic Models*, Chapter 5 §5, Proposition 5.5, printed p. 116;
Eilenberg–Zilber, *On Products of Complexes*, §2 pp. 202–203 and §3 p. 203.
This is statement node `topo.singular_acyclic_models_remaining_uniqueness_cases_g2`.

All chain complexes, signed tensor totalizations and homotopies below are Mathlib objects.
The let-bound expressions only select these objects and spell out naturality and normalization.
`R = ULift ℚ` is the rational field transported to the universe of the spaces; scalar
transport by `ULift.down` gives exactly rational chains and rational-linear maps.
No topology, finiteness or separation condition is imposed on the spaces.
The singular complexes are unnormalized, including those of singleton spaces.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HolomorphicAnosov.Topology

/-- Natural chain homotopies in the three remaining ordered acyclic-model cases.

The two generator maps send the coefficient 1 respectively to the unique point-pair
0-simplex and the tensor of the two unique point 0-simplices. Requiring the chain maps
to carry these generators to the displayed target generator is precisely the canonical
point identification, since the degree-zero modules at the singleton pair are free of rank 1.
The native `Homotopy` equation is `Φ = ∂H + H∂ + Ψ`; the explicit naturality equation
makes every degree of H a natural transformation, and its `(0,1)` component is H₀.

Source:
Barr, Acyclic Models (AMS CRM Monograph Series17, 2002; acquired author corrected2017 text),
Chapter5 §5 Proposition5.5, full written comparison/homotopy induction printed p116 (local
literature/Barr-Acyclic-Models-2002.pdf PDFp128), and Chapter1 §6 Lemma6.2 Yoneda with written
inverse printed p20 (PDFp32). The free-module basis/Hom identification is also written in Barr
Chapter2 §5.1 printed pp64–65 (PDFpp76–77), read in full. Model-generator representations and
augmentation are Eilenberg–Zilber, On Products of Complexes (1953), §2 printed pp202–203 and
singular application §3 p203 (local literature/Eilenberg-Zilber-On-Products-of-Complexes-1953.pdf
PDFpp4–5). The actual topological convex-model fillings are Bredon IV15.5 pp219–220 and VI1.1 p316
through topo.singular_convex_cone_tensor_contraction_g2. Bredon VI1.3 pp317–318 and Problem4 p320
state but omit the three cases; Barr supplies their written general induction. Primary page images
and complete pertinent text read; no reliance on an exercise as proof.

Complete natural-language proof:

U1. Use R = ULift Q at the universe of the spaces. The ring equivalence down identifies these chains, tensor products and linear maps with rational ones. A degree n is free on singular simplices into X×Y, represented by the diagonal simplex in (Δⁿ,Δⁿ); B degree n is the sum over p+q=n of tensors of the two free singular modules, represented by the identity simplex pair in (Δᵖ,Δᑫ). Every generator is the image of its model generator under its pair of simplex maps. The already proved product and tensor extension lemmas extend chosen maps on these generators linearly, by the singular coproducts and total coproduct, and naturally by postcomposition. Equality on model generators therefore proves equality of the resulting natural maps.

U2. Every degree-zero generator comes from the pair of singleton spaces by its pair of point inclusions. Naturality and the common normalization imply that Φ and Ψ agree on every such generator, hence on degree zero. For B, cancel the invertible coefficient unitor in the normalized point-generator equation before applying tensor-generator extensionality. For an empty space the free modules have no generators, so the same argument applies without any nonemptiness assumption.

U3. For A→A and a natural residual r in degree n+1 with rd=0, evaluate on the diagonal generator of (Δⁿ⁺¹,Δⁿ⁺¹). Evaluation preserves rd=0. The product of these standard simplices is convex, and its cone contraction fills the evaluated positive cycle. The implemented product-model filler transports this contraction across the canonical homeomorphism from the product of lifted simplices to the lift of their product. Extend the filling using the product-source extension theorem. Its boundary is r because this is true on the diagonal model generator and hence on every generator.

U4. For B→B, evaluate r separately on the identity generator of (Δᵖ,Δᑫ) for every p+q=n+1. Each value is a cycle. The tensor cone contraction on the two lifted standard simplices fills that cycle: the contraction identity is id minus the tensor point projection, and the latter vanishes in positive total degree. Extend each filling along pairs of simplex maps and through the tensor and total coproducts. The tensor-source extension theorem proves naturality and the boundary equation on the generators, hence everywhere. The case n=0 uses positive degree one and needs no augmentation-zero side condition; either simplex may have dimension zero.

U5. For A→A and B→B apply the natural relative Barr induction to degree-zero equality and the preceding residual fillers. Set H₀=0. Given the lower components, rₖ=Φₖ−Ψₖ−Hₖ₋₁d is a cycle by the chain-map identities, the preceding homotopy equation, and d²=0. Fill it naturally to obtain Hₖ, establishing dHₖ+Hₖ₋₁d=Φₖ−Ψₖ. The induction produces the native objectwise homotopies with natural components and H₀=0. For B→A apply the already proved BA uniqueness theorem, which uses the same induction and product-model filling for paired generators. These are precisely the three claimed cases, with no restriction on the spaces.

-/
theorem singular_acyclic_models_remaining_uniqueness_cases :
    let R := ULift.{u} ℚ
    let coefficient : ModuleCat.{u} R := ModuleCat.of R R
    let C : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj coefficient
    let A : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      tensor TopCat.{u} ⋙ C
    let B : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
      (C.prod C) ⋙ tensor (ChainComplex (ModuleCat.{u} R) ℕ)
    let point : TopCat.{u} := TopCat.of PUnit.{u + 1}
    let pointPair := (point, point)
    let g : coefficient ⟶ (C.obj point).X 0 :=
      (TopCat.toSSet.obj point).ιChainComplex
        ((TopCat.toSSetObjEquiv point (Opposite.op ⦋0⦌)).symm
          (ContinuousMap.const _ PUnit.unit))
    let gA : coefficient ⟶ (A.obj pointPair).X 0 :=
      (TopCat.toSSet.obj (point ⊗ point)).ιChainComplex
        ((TopCat.toSSetObjEquiv (point ⊗ point) (Opposite.op ⦋0⦌)).symm
          (ContinuousMap.const _ (PUnit.unit, PUnit.unit)))
    let gB : coefficient ⟶ (B.obj pointPair).X 0 :=
      (λ_ coefficient).inv ≫ (g ⊗ₘ g) ≫
        HomologicalComplex.ιTensorObj (C.obj point) (C.obj point) 0 0 0 rfl
    let naturalHomotopy := fun
      (S T : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ)
      (Φ Ψ : S ⟶ T) ↦
        ∃ H : ∀ X, _root_.Homotopy (Φ.app X) (Ψ.app X),
          (∀ X Y (f : X ⟶ Y) (i j : ℕ),
            (S.map f).f i ≫ (H Y).hom i j = (H X).hom i j ≫ (T.map f).f j) ∧
          (∀ X, (H X).hom 0 1 = 0)
    (∀ (Φ Ψ : A ⟶ A),
      gA ≫ (Φ.app pointPair).f 0 = gA →
      gA ≫ (Ψ.app pointPair).f 0 = gA → naturalHomotopy A A Φ Ψ) ∧
    (∀ (Φ Ψ : B ⟶ B),
      gB ≫ (Φ.app pointPair).f 0 = gB →
      gB ≫ (Ψ.app pointPair).f 0 = gB → naturalHomotopy B B Φ Ψ) ∧
    (∀ (Φ Ψ : B ⟶ A),
      gB ≫ (Φ.app pointPair).f 0 = gA →
      gB ≫ (Ψ.app pointPair).f 0 = gA → naturalHomotopy B A Φ Ψ) := by
  dsimp only
  refine ⟨?_, ?_, singular_acyclic_models_BA_case⟩
  · intro Φ Ψ hΦ hΨ
    apply barr_natural_relative_homotopy
    · intro X
      exact NatTrans.congr_app (SingularProductGenerator.zero_eq_of_point (ULift.{u} ℚ) _
        ((chainMapOfNaturalTransformation Φ).f 0)
        ((chainMapOfNaturalTransformation Ψ).f 0) (hΦ.trans hΨ.symm)) X
    · intro n r hr
      refine SingularProductGenerator.lift_natural (ULift.{u} ℚ) (n + 1) _ _
        ((chainComplexOfFunctor (SingularProductGenerator.productChains (ULift.{u} ℚ))).d
          (n + 2) (n + 1)) r ?_
      let M := SingularProductGenerator.model.{u} (n + 1)
      let v := (TopCat.toSSet.obj (M.1 ⊗ M.2)).ιChainComplex
        (R := SingularProductGenerator.coeff (ULift.{u} ℚ))
        (SingularProductGenerator.diagonal (n + 1)) ≫ r.app M
      have hv : v ≫ ((SingularProductGenerator.productChains (ULift.{u} ℚ)).obj M).d
          (n + 1) n = 0 := by
        have h := NatTrans.congr_app hr M
        dsimp only [NatTrans.comp_app, zero_app, chainComplexOfFunctor] at h
        dsimp only [v]
        erw [Category.assoc, h, comp_zero]
      exact SingularTensorGenerator.product_model_fill (ULift.{u} ℚ)
        (n + 1) (n + 1) n v hv
  · intro Φ Ψ hΦ hΨ
    apply barr_natural_relative_homotopy
    · intro X
      apply NatTrans.congr_app (SingularTensorGenerator.zero_eq_of_point (ULift.{u} ℚ) _
        ((chainMapOfNaturalTransformation Φ).f 0)
        ((chainMapOfNaturalTransformation Ψ).f 0) ?_) X
      apply (cancel_epi (λ_ (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ))).inv).1
      have hh := hΦ.trans hΨ.symm
      simp only [Category.assoc] at hh
      dsimp only [SingularTensorGenerator.generator]
      simp only [Category.assoc]
      exact hh
    · intro n r hr
      refine SingularTensorGenerator.lift_natural (ULift.{u} ℚ) (n + 1) _ _
        ((chainComplexOfFunctor (SingularTensorGenerator.tensorChains (ULift.{u} ℚ))).d
          (n + 2) (n + 1)) r ?_
      intro p q hpq
      let M := SingularTensorGenerator.model.{u} p q
      let v := SingularTensorGenerator.generator (ULift.{u} ℚ) M p q (n + 1) hpq
        (ULift.up (𝟙 _)) (ULift.up (𝟙 _)) ≫ r.app M
      have hv : v ≫ ((SingularTensorGenerator.tensorChains (ULift.{u} ℚ)).obj M).d
          (n + 1) n = 0 := by
        have h := NatTrans.congr_app hr M
        dsimp only [NatTrans.comp_app, zero_app, chainComplexOfFunctor] at h
        dsimp only [v]
        erw [Category.assoc, h, comp_zero]
      exact ⟨v ≫ (LiftedSingularCone.tensorContraction (ULift.{u} ℚ) (.simplex p) (.simplex q)
          (SingularProductTensor.modelPoint p) (SingularProductTensor.modelPoint q)).hom
            (n + 1) (n + 2),
        LiftedSingularCone.tensor_fill_positive (ULift.{u} ℚ) (.simplex p) (.simplex q)
          (SingularProductTensor.modelPoint p) (SingularProductTensor.modelPoint q) n v hv⟩

end HolomorphicAnosov.Topology

