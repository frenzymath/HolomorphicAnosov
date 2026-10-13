import HolomorphicAnosov.Topology.SingularChainBoundary
import HolomorphicAnosov.Topology.SingularChainMap
import Mathlib.Topology.Category.TopPair
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Singular simplicial subcomplexes of topological subspaces

Source: Hatcher, *Algebraic Topology*, §2.1, pp.108, 110–111, 115, 118–119, 124.
DAG node: `topo.singular_subspace_subcomplex_adapter`.
The carrier, arrows and complexes below are the actual Mathlib singular functor,
simplicial subcomplexes, pairs, and integral chain and homology functors.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace HolomorphicAnosov

/-- Singular sets of actual embedded topological pairs, with both original component maps.
Source: Hatcher §2.1, pp.110–111, 118; Mathlib's `TopPair` and `SSetPair` constructors.
-/
noncomputable def singularPairFunctor : TopPair.{u} ⥤ SSetPair.{u} where
  obj P := by
    letI : Mono P.map := (TopCat.mono_iff_injective _).2 P.isEmbedding_map.injective
    exact SSetPair.of (TopCat.toSSet.map P.map)
  map f := SSetPair.homMk (TopCat.toSSet.map (TopPair.Hom.snd f))
    (TopCat.toSSet.map (TopPair.Hom.fst f)) (by
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp, ← Functor.map_comp, TopPair.Hom.w])
  map_id P := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map (𝟙 P.snd) = 𝟙 _
      exact TopCat.toSSet.map_id _
    · change TopCat.toSSet.map (𝟙 P.fst) = 𝟙 _
      exact TopCat.toSSet.map_id _
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map (TopPair.Hom.snd f ≫ TopPair.Hom.snd g) = _
      exact TopCat.toSSet.map_comp _ _
    · change TopCat.toSSet.map (TopPair.Hom.fst f ≫ TopPair.Hom.fst g) = _
      exact TopCat.toSSet.map_comp _ _

/-- The continuous inclusion of a subset, with its subspace topology.
Source: Hatcher §2.1 p.110; Mathlib `continuous_subtype_val` and `TopCat.ofHom`. -/
def singularSubspaceInclusion (X : TopCat.{u}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual simplicial image of the inclusion of a topological subspace.
Source: Hatcher §2.1 pp.110–111; Mathlib `SSet.Subcomplex.range`. -/
noncomputable def singularSubspace (X : TopCat.{u}) (A : Set X) :
    (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (singularSubspaceInclusion X A))

/-- The singular pair of a space and its subspace, using the actual inclusion.
Source: Hatcher §2.1 p.118; Mathlib `SSetPair.of` and preservation of monomorphisms. -/
noncomputable def singularSubspacePair (X : TopCat.{u}) (A : Set X) : SSetPair.{u} := by
  letI : Mono (singularSubspaceInclusion X A) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  exact SSetPair.of (TopCat.toSSet.map (singularSubspaceInclusion X A))

/-- Restriction of a continuous map to a specified map of subspaces.
Source: Hatcher §2.1 p.118; Mathlib `Continuous.subtype_mk`. -/
def singularSubspaceMap {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Set X) (D : Set Y)
    (hf : Set.MapsTo f A D) : TopCat.of A ⟶ TopCat.of D :=
  TopCat.ofHom ⟨fun a ↦ ⟨f a.val, hf a.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The pair corresponding to the intersection subcomplex inside the second subcomplex.
Source: Hatcher §2.1 pp.119,124; Mathlib `SSet.Subcomplex.homOfLE` and `SSetPair.of`. -/
noncomputable def singularIntersectionPair (X : TopCat.{u}) (A B : Set X) : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE
    (show singularSubspace X A ⊓ singularSubspace X B ≤ singularSubspace X B from inf_le_right))

/-- The actual map of singular pairs induced by a continuous map of topological pairs.
Source: Hatcher §2.1 p.118; Mathlib `SSetPair.homMk` and `TopCat.toSSet`. -/
noncomputable def singularSubspacePairMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : Set X) (D : Set Y) (hf : Set.MapsTo f A D) :
    singularSubspacePair X A ⟶ singularSubspacePair Y D :=
  SSetPair.homMk (TopCat.toSSet.map (singularSubspaceMap f A D hf))
    (TopCat.toSSet.map f) (by
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

/-- The actual inclusion of the intersection pair into the ambient subspace pair.
Source: Hatcher §2.1 pp.119,124; Mathlib `SSet.Subcomplex.homOfLE` and `SSetPair.homMk`. -/
noncomputable def singularIntersectionInclusion (X : TopCat.{u}) (A B : Set X) :
    singularIntersectionPair X A B ⟶ (singularSubspace X A).pair :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE inf_le_left) (singularSubspace X B).ι (by
    ext n s
    rfl)


/-- The common-universe integral coefficient object used by singular chains.
Source: Hatcher §2.1 p.108; Mathlib `ModuleCat.of` and the standard lifted integer module. -/
abbrev singularIntegralCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- Topological subspaces identify with their actual singular simplicial subcomplexes,
including natural pairs, integral chains, relative quotients and homology.

Source: Hatcher, *Algebraic Topology*, §2.1, pp.108, 110–111, 115, 118–119 and 124.
DAG node: `topo.singular_subspace_subcomplex_adapter`.

Complete natural-language proof:

Use the singular-set functor and continuous-map model of its simplices. If σ(Δ^n)⊆A and α:[m]→[n] is a simplex-category map, then σ(α_*t)∈A for every t∈Δ^m. Thus the degreewise sets S_A are closed under every face, degeneracy and composite. Restricting the ambient simplicial operators gives a subfunctor; its identities and composition laws follow by restriction of those of Sing(X). This constructs S_A as a genuine SSet.Subcomplex, with induced simplicial subset topology unchanged because simplicial sets have set-valued degrees.

For each n define e_A(σ)=i_A∘σ. Conversely, from an ambient simplex τ with membership witness h(t)∈A form τ_A(t)=(τ(t),h(t)). Continuous.subtype_mk makes τ_A continuous for the induced topology. Subtype extensionality shows these maps are inverse. At every t, applying a simplicial operator before or after either map gives the same underlying value τ(α_*t). They therefore commute with all simplicial maps, including degree-zero faces from degree one and all degeneracies. Hence they give a simplicial isomorphism e_A and the equality e_A followed by S_A inclusion = Sing(i_A).

An ambient simplex lies in S_{A∩B} exactly when all its values lie in both A and B. This is equivalent to membership in S_A and membership in S_B, degreewise, proving literal equality S_{A∩B}=S_A∩S_B. A⊆B gives S_A⊆S_B by the pointwise containment. The canonical subcomplex inclusions leave the ambient simplex unchanged, and their composite with the ambient inclusion is the direct inclusion, by homOfLE_ι. These equations and S2 prove naturality for subset inclusions.

For N={b:B | b.val∈A}, a simplex into N forgets both subtype layers to an ambient simplex supported in A and B. Conversely, take τ supported in both and form t↦((τ(t),h_B(t)),h_A(t)). Two applications of Continuous.subtype_mk prove continuity into B and then into N. These maps are inverse by subtype extensionality and commute with every precomposition. They identify Sing(N) with S_A∩S_B; the square to Sing(B) and S_B commutes since each route forgets the A-membership witness.

The topological inclusions i_A and N→B are injective, hence monomorphisms in TopCat; the singular functor preserves these monos. Thus their singular arrows form SSetPairs. The subcomplex arrows are degreewise subtype inclusions and are also monomorphisms. Use SSetPair.of and homMk with e_A and the identity of Sing(X) to give inverse pair maps; S2 is their commuting square. Use the S4 isomorphism on N and e_B on B for the intersection pair. The componentwise inverse equations imply pair-isomorphism inverse equations.

For continuous f:X→Y with f(A)⊆D, define f_A:A→D by a↦(f(a),hf(a)). Its continuity is Continuous.subtype_mk applied to f∘i_A. Define S_A→S_D by (τ,h)↦(f∘τ,t↦hf(h(t))); associativity proves simplicial naturality. The inclusion square commutes pointwise and defines a map of SSetPairs. The identity e_D Sing(f_A)=the restricted postcomposition map e_A holds at every simplex value. Together with Sing(f) on ambient simplices this proves the pair-isomorphism naturality square. No good-pair, open or closed subset assumption is used.

Specialize S6 to the pair inclusion (B,N)→(X,A). Its ambient map is i_B and its restricted map forgets the B-membership proof into A. Under S4 and S2, these are respectively S_B↪Sing(X) and S_A∩S_B↪S_A. Both pair-map squares follow by equality of ambient simplex values. This is exactly the inclusion used in Hatcher Theorem2.20 p.119 and proof p.124; taking B=X∖Z gives N=A∖Z with its nested subspace topology.

Fix a universe containing all simplex index sets and take coefficient module R=ULift ℤ in ModuleCat ℤ in that universe. ModuleCat has the required coproducts and is abelian with homology. For any simplicial set L used here, SSet.isColimitChainComplexXCofan gives a coproduct of R indexed by L_n. ModuleCat.finsuppCoconeIsColimit gives the same coproduct as L_n→₀R. The colimit-point comparison isomorphism identifies every summand with its finitely supported single-coordinate generator. Finsupp.sum_single expresses every element as its finite sum of such generators. For L=Sing(X), use the actual singular-simplex equivalence to relabel indices and ULift.down on coefficients: this is precisely Hatcher’s free abelian singular-chain group, rather than a chosen unrelated complex.

The generator map formula sends the generator of σ to the generator of its simplicial image; for topological maps this is postcomposition. The boundary formula sends an n-simplex generator to Σ_{i=0}^n(-1)^i times its i-th face for n>0, matching Hatcher p.108 under the continuous-map face model. In degree zero the Nat-indexed chain differential to a negative degree is zero. Thus S8 comparisons commute with differentials and all relevant maps on each generator, and then on finite sums. For the S_A→Sing(X) inclusion the indexing function is injective, so its free-chain map is injective: each source coefficient is recovered at that same ambient simplex. Its image is exactly the subgroup generated by simplices supported in A. Consequently it identifies C_*(A) with the subchain complex described by Hatcher, and intersection identifies C_*(A∩B) with the intersection of these basis subgroups.

For each simplicial pair P, let q_P be the actual canonical projection to P.chainComplex R. The registered degreewise cokernel property makes its degree-n target a cokernel of the actual inclusion chain map. The concrete ModuleCat range quotient C_n(P.right)/range C_n(P.hom) with its mkQ projection is another cokernel of this same map. CokernelCofork.mapIsoOfIsColimit compares them with defining equation α_n(q_P c)=[c]. By S9, for a topological pair this quotient is exactly Hatcher C_n(X)/C_n(A). Its differential is well-defined because faces preserve A. Both composites of α with differentials agree after precomposition by the surjective projection q_P, using the chain-map equation of q_P, so α commutes with the differential. The inverse isomorphisms commute as well. This gives a chain-complex isomorphism preserving the original quotient projections, not just an abstract isomorphism of groups.

Apply the chain functor to e_A, the intersection identification and their pair isomorphisms. Functoriality maps their inverse equations to inverse chain maps. For a pair map u, projection naturality is q_P then Q(u)=C(u.right) then q_Q. Under S10 it says Q(u)[c]=[u.right#c], the map defined by Hatcher p.118. If c is changed by a chain from the left subspace, its image changes by a chain from the target left subspace because the pair square commutes; hence this is precisely the induced quotient map. Precomposition with the epimorphic q_P proves naturality of all quotient comparison maps. In S7 the resulting map is [c]↦[i_B#c].

Apply the fixed-degree homology functor to these chain isomorphisms and commuting squares. Functor.mapIso preserves their inverse equations; homologyFunctor preserves the map equalities. Its relative specialization is the actual SSetPair.homologyFunctor. Since S9 and S10 identify all chain objects, differentials and projection maps with the ordinary integral singular chains, their homology and induced inclusion map are the homology of those exact chains, cycles modulo boundaries. This proves the asserted natural homology identifications for every n≥0, including n=0. If X or A or B is empty, the positive-dimensional and degree-zero standard simplices are still nonempty, so there are no simplices into an empty subspace and the corresponding free chains are zero; the same arguments apply to A=∅, A=X, disjoint A,B, or B=∅.

The degreewise free-module comparisons below identify every generator, and the
boundary formula identifies the actual differential with the alternating face boundary.
The relative comparisons use the concrete range quotients of those same native chain
modules and preserve their quotient projections. Thus neither absolute nor relative
ordinary singular chains are replaced by an unspecified homology theory.
-/
theorem singular_subspace_subcomplex_adapter :
    ∃ e : ∀ (X : TopCat.{u}) (A : Set X),
        TopCat.toSSet.obj (TopCat.of A) ≅ (singularSubspace X A : SSet.{u}),
      (∀ (X : TopCat.{u}) (A : Set X) (n : SimplexCategoryᵒᵖ)
        (σ : (TopCat.toSSet.obj X).obj n),
        σ ∈ (singularSubspace X A).obj n ↔
          ∀ t, X.toSSetObjEquiv n σ t ∈ A) ∧
      (∀ (X : TopCat.{u}) (A : Set X),
        (e X A).hom ≫ (singularSubspace X A).ι =
          TopCat.toSSet.map (singularSubspaceInclusion X A)) ∧
      (∀ (X : TopCat.{u}) (A B : Set X),
        singularSubspace X (A ∩ B) = singularSubspace X A ⊓ singularSubspace X B) ∧
      (∀ (X : TopCat.{u}), Monotone (singularSubspace X)) ∧
      (∀ (X Y : TopCat.{u}) (f : X ⟶ Y) (A : Set X) (D : Set Y)
        (hf : Set.MapsTo f A D),
        ∃ F : (singularSubspace X A : SSet.{u}) ⟶ (singularSubspace Y D : SSet.{u}),
          F ≫ (singularSubspace Y D).ι =
            (singularSubspace X A).ι ≫ TopCat.toSSet.map f ∧
          (e X A).hom ≫ F =
            TopCat.toSSet.map (singularSubspaceMap f A D hf) ≫ (e Y D).hom) ∧
      ∃ ep : ∀ (X : TopCat.{u}) (A : Set X),
          singularSubspacePair X A ≅ (singularSubspace X A).pair,
        (∀ (X : TopCat.{u}) (A : Set X),
          (ep X A).hom.hom.left = (e X A).hom ∧
          (ep X A).hom.hom.right = 𝟙 (TopCat.toSSet.obj X)) ∧
        ∃ ei : ∀ (X : TopCat.{u}) (A B : Set X),
            singularSubspacePair (TopCat.of B) {b | b.val ∈ A} ≅
              singularIntersectionPair X A B,
          (∀ (X : TopCat.{u}) (A B : Set X),
            (ei X A B).hom.hom.right = (e X B).hom ∧
            (ei X A B).hom ≫ singularIntersectionInclusion X A B =
              singularSubspacePairMap (singularSubspaceInclusion X B)
                {b | b.val ∈ A} A (fun _ hb ↦ hb) ≫ (ep X A).hom) ∧
          ∃ c : ∀ (X : TopCat.{u}) (n : ℕ),
              ((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).X n ≅
                ModuleCat.of ℤ (C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) →₀ ULift.{u} ℤ),
            (∀ (X : TopCat.{u}) (n : ℕ),
              (∀ (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : ULift.{u} ℤ),
                (c X n).hom (((TopCat.toSSet.obj X).ιChainComplex
                  (R := singularIntegralCoefficients) σ) a) =
                    Finsupp.single (X.toSSetObjEquiv _ σ) a) ∧
              (∀ (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) (a : ULift.{u} ℤ),
                (c X n).hom (((TopCat.toSSet.obj X).chainComplex
                  singularIntegralCoefficients).d (n + 1) n
                    (((TopCat.toSSet.obj X).ιChainComplex
                      (R := singularIntegralCoefficients) σ) a)) =
                    ∑ i : Fin (n + 2),
                      (-1 : ℤ) ^ i.val • Finsupp.single
                        (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)) a)) ∧
            (∀ (X Y : TopCat.{u}) (f : X ⟶ Y) (n : ℕ)
              (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : ULift.{u} ℤ),
              (c Y n).hom ((SSet.chainComplexMap (TopCat.toSSet.map f)
                singularIntegralCoefficients).f n
                  (((TopCat.toSSet.obj X).ιChainComplex
                    (R := singularIntegralCoefficients) σ) a)) =
                Finsupp.single (f.hom.comp (X.toSSetObjEquiv _ σ)) a) ∧
          (∀ (X : TopCat.{u}) (A : Set X),
            let c := ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
              singularIntegralCoefficients).mapIso (e X A)
            let r := ((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
              singularIntegralCoefficients).mapIso (ep X A)
            c.hom = SSet.chainComplexMap (e X A).hom singularIntegralCoefficients ∧
              r.hom = SSetPair.chainComplexMap (ep X A).hom singularIntegralCoefficients ∧
              (singularSubspacePair X A).chainComplexπ singularIntegralCoefficients ≫ r.hom =
                (singularSubspace X A).pair.chainComplexπ singularIntegralCoefficients ∧
              ∀ n : ℕ,
                let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ)
                  (ComplexShape.down ℕ) n
                (H.mapIso c).hom =
                  SSet.homologyMap (e X A).hom singularIntegralCoefficients n ∧
                (H.mapIso r).hom =
                  SSetPair.homologyMap (ep X A).hom singularIntegralCoefficients n) ∧
          (∀ (X Y : TopCat.{u}) (f : X ⟶ Y) (A : Set X) (D : Set Y)
            (hf : Set.MapsTo f A D),
            ∃ F : (singularSubspace X A : SSet.{u}) ⟶ (singularSubspace Y D : SSet.{u}),
            ∃ hF : F ≫ (singularSubspace Y D).ι =
                (singularSubspace X A).ι ≫ TopCat.toSSet.map f,
            let G : (singularSubspace X A).pair ⟶ (singularSubspace Y D).pair :=
              SSetPair.homMk F (TopCat.toSSet.map f) hF
            (ep X A).hom ≫ G = singularSubspacePairMap f A D hf ≫ (ep Y D).hom ∧
            ∀ n : ℕ,
              let cx := ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
                singularIntegralCoefficients).mapIso (e X A)
              let cy := ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
                singularIntegralCoefficients).mapIso (e Y D)
              let rx := ((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
                singularIntegralCoefficients).mapIso (ep X A)
              let ry := ((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
                singularIntegralCoefficients).mapIso (ep Y D)
              let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ)
                (ComplexShape.down ℕ) n
              SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceMap f A D hf))
                  singularIntegralCoefficients ≫ cy.hom =
                cx.hom ≫ SSet.chainComplexMap F singularIntegralCoefficients ∧
              SSetPair.chainComplexMap (singularSubspacePairMap f A D hf)
                  singularIntegralCoefficients ≫ ry.hom =
                rx.hom ≫ SSetPair.chainComplexMap G singularIntegralCoefficients ∧
              SSet.homologyMap (TopCat.toSSet.map (singularSubspaceMap f A D hf))
                  singularIntegralCoefficients n ≫ (H.mapIso cy).hom =
                (H.mapIso cx).hom ≫ SSet.homologyMap F singularIntegralCoefficients n ∧
              SSetPair.homologyMap (singularSubspacePairMap f A D hf)
                  singularIntegralCoefficients n ≫ (H.mapIso ry).hom =
                (H.mapIso rx).hom ≫ SSetPair.homologyMap G singularIntegralCoefficients n) ∧
          ∃ q : ∀ (P : SSetPair.{u}) (n : ℕ),
              (P.chainComplex singularIntegralCoefficients).X n ≅
                ModuleCat.of ℤ (((P.right.chainComplex singularIntegralCoefficients).X n) ⧸
                  LinearMap.range ((SSet.chainComplexMap P.hom singularIntegralCoefficients).f n).hom),
            (∀ (P : SSetPair.{u}) (n : ℕ)
              (c : (P.right.chainComplex singularIntegralCoefficients).X n),
              (q P n).hom ((P.chainComplexπ singularIntegralCoefficients).f n c) =
                (LinearMap.range
                  ((SSet.chainComplexMap P.hom singularIntegralCoefficients).f n).hom).mkQ c) ∧
            (∀ (P : SSetPair.{u}) (n : ℕ)
              (c : (P.right.chainComplex singularIntegralCoefficients).X (n + 1)),
              (q P n).hom ((P.chainComplex singularIntegralCoefficients).d (n + 1) n
                ((P.chainComplexπ singularIntegralCoefficients).f (n + 1) c)) =
                  (LinearMap.range
                    ((SSet.chainComplexMap P.hom singularIntegralCoefficients).f n).hom).mkQ
                    ((P.right.chainComplex singularIntegralCoefficients).d (n + 1) n c)) ∧
            (∀ (P Q : SSetPair.{u}) (f : P ⟶ Q) (n : ℕ)
              (c : (P.right.chainComplex singularIntegralCoefficients).X n),
              (q Q n).hom ((SSetPair.chainComplexMap f singularIntegralCoefficients).f n
                ((P.chainComplexπ singularIntegralCoefficients).f n c)) =
                  (LinearMap.range
                    ((SSet.chainComplexMap Q.hom singularIntegralCoefficients).f n).hom).mkQ
                    ((SSet.chainComplexMap f.hom.right singularIntegralCoefficients).f n c)) ∧
            (∀ (X : TopCat.{u}) (A B : Set X) (n : ℕ),
              SSetPair.homologyMap
                (singularSubspacePairMap (singularSubspaceInclusion X B)
                  {b | b.val ∈ A} A (fun _ hb ↦ hb)) singularIntegralCoefficients n ≫
                  SSetPair.homologyMap (ep X A).hom singularIntegralCoefficients n =
                SSetPair.homologyMap (ei X A B).hom singularIntegralCoefficients n ≫
                  SSetPair.homologyMap (singularIntersectionInclusion X A B)
                    singularIntegralCoefficients n) := by
  classical
  let e (X : TopCat.{u}) (A : Set X) :
      TopCat.toSSet.obj (TopCat.of A) ≅ (singularSubspace X A : SSet.{u}) := by
    letI : Mono (singularSubspaceInclusion X A) :=
      (TopCat.mono_iff_injective _).2 Subtype.val_injective
    let f := TopCat.toSSet.map (singularSubspaceInclusion X A)
    let t : TopCat.toSSet.obj (TopCat.of A) ⟶ (singularSubspace X A : SSet.{u}) :=
      SSet.Subcomplex.toRange f
    haveI : Mono f := by dsimp [f]; infer_instance
    haveI : Mono t := mono_of_mono_fac (SSet.Subcomplex.toRange_ι f)
    haveI : Epi t := by
      rw [NatTrans.epi_iff_epi_app]
      intro n
      rw [epi_iff_surjective]
      rintro ⟨σ, τ, hτ⟩
      exact ⟨τ, Subtype.ext hτ⟩
    haveI : IsIso t := isIso_of_mono_of_epi t
    exact asIso t
  have hmem (X : TopCat.{u}) (A : Set X) (n : SimplexCategoryᵒᵖ)
      (σ : (TopCat.toSSet.obj X).obj n) :
      σ ∈ (singularSubspace X A).obj n ↔ ∀ t, X.toSSetObjEquiv n σ t ∈ A := by
    rw [singularSubspace, Subfunctor.range_obj]
    constructor
    · rintro ⟨τ, hτ⟩
      intro t
      have heq := congrArg (fun s ↦ X.toSSetObjEquiv n s t) hτ
      rw [← heq]
      exact (((TopCat.of A).toSSetObjEquiv n τ).toFun t).property
    · intro h
      let f : C(Convexity.StdSimplex ℝ (Fin ((unop n).len + 1)), A) :=
        ⟨fun t ↦ ⟨X.toSSetObjEquiv n σ t, h t⟩,
          (X.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
      refine ⟨((TopCat.of A).toSSetObjEquiv n).symm f, ?_⟩
      apply (X.toSSetObjEquiv n).injective
      ext t
      rfl
  have he (X : TopCat.{u}) (A : Set X) :
      (e X A).hom ≫ (singularSubspace X A).ι =
        TopCat.toSSet.map (singularSubspaceInclusion X A) := rfl
  have hinter (X : TopCat.{u}) (A B : Set X) :
      singularSubspace X (A ∩ B) = singularSubspace X A ⊓ singularSubspace X B := by
    ext n σ
    change (σ ∈ (singularSubspace X (A ∩ B)).obj n) ↔
      σ ∈ (singularSubspace X A).obj n ∧ σ ∈ (singularSubspace X B).obj n
    simp only [hmem, Set.mem_inter_iff, forall_and]
  have hmono (X : TopCat.{u}) : Monotone (singularSubspace X) := by
    intro A B hAB n σ hσ
    rw [hmem] at hσ ⊢
    exact fun t ↦ hAB (hσ t)
  refine ⟨e, hmem, he, hinter, hmono, ?_, ?_⟩
  · intro X Y f A D hf
    let F := (e X A).inv ≫ TopCat.toSSet.map (singularSubspaceMap f A D hf) ≫ (e Y D).hom
    refine ⟨F, ?_, ?_⟩
    · dsimp [F]
      rw [Category.assoc, Category.assoc, he, ← Functor.map_comp]
      have hsq : singularSubspaceMap f A D hf ≫ singularSubspaceInclusion Y D =
          singularSubspaceInclusion X A ≫ f := rfl
      rw [hsq, Functor.map_comp, ← Category.assoc, ← he, Iso.inv_hom_id_assoc]
    · simp [F]
  · let ep (X : TopCat.{u}) (A : Set X) :
        singularSubspacePair X A ≅ (singularSubspace X A).pair :=
      MorphismProperty.Comma.isoMk (e X A) (Iso.refl _) (by
        change (e X A).hom ≫ _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact he X A)
    refine ⟨ep, ?_, ?_⟩
    · intro X A
      exact ⟨rfl, rfl⟩
    · have hex (X : TopCat.{u}) (A B : Set X) :
          ∃ ei : singularSubspacePair (TopCat.of B) {b | b.val ∈ A} ≅
              singularIntersectionPair X A B,
            ei.hom.hom.right = (e X B).hom ∧
            ei.hom ≫ singularIntersectionInclusion X A B =
              singularSubspacePairMap (singularSubspaceInclusion X B)
                {b | b.val ∈ A} A (fun _ hb ↦ hb) ≫ (ep X A).hom := by
        let N : Set B := {x | (x : X) ∈ A}
        let j : TopCat.of N ⟶ X :=
          singularSubspaceInclusion (TopCat.of B) N ≫ singularSubspaceInclusion X B
        have hj : Mono j := by
          have : Mono (singularSubspaceInclusion (TopCat.of B) N) :=
            (TopCat.mono_iff_injective _).mpr Subtype.val_injective
          have : Mono (singularSubspaceInclusion X B) :=
            (TopCat.mono_iff_injective _).mpr Subtype.val_injective
          dsimp [j]
          infer_instance
        have hr : SSet.Subcomplex.range (TopCat.toSSet.map j) ≤
            singularSubspace X A ⊓ singularSubspace X B := by
          intro n τ hτ
          obtain ⟨σ, rfl⟩ := hτ
          constructor
          · apply (hmem X A n _).mpr
            intro t
            exact (((TopCat.of N).toSSetObjEquiv n σ) t).property
          · apply (hmem X B n _).mpr
            intro t
            exact (((TopCat.of N).toSSetObjEquiv n σ) t).val.property
        let m := SSet.Subcomplex.lift (TopCat.toSSet.map j) hr
        have hm : Mono m := mono_of_mono_fac (SSet.Subcomplex.lift_ι _ hr)
        have hsurj (n : SimplexCategoryᵒᵖ) : Function.Surjective (m.app n) := by
          intro τ
          have hA := (hmem X A n τ.val).mp τ.property.1
          have hB := (hmem X B n τ.val).mp τ.property.2
          let f : C(Convexity.StdSimplex ℝ (Fin ((unop n).len + 1)), N) :=
            ⟨fun t ↦ ⟨⟨X.toSSetObjEquiv n τ.val t, hB t⟩, hA t⟩,
              ((X.toSSetObjEquiv n τ.val).continuous.subtype_mk _).subtype_mk _⟩
          refine ⟨((TopCat.of N).toSSetObjEquiv n).symm f, ?_⟩
          apply Subtype.ext
          apply (X.toSSetObjEquiv n).injective
          ext t
          rfl
        have : IsIso m := by
          apply (NatTrans.isIso_iff_isIso_app m).mpr
          intro n
          exact (isIso_iff_bijective _).mpr
            ⟨(CategoryTheory.mono_iff_injective _).mp inferInstance, hsurj n⟩
        let ei : singularSubspacePair (TopCat.of B) N ≅ singularIntersectionPair X A B :=
          MorphismProperty.Comma.isoMk (asIso m) (e X B) (by
            ext n σ
            apply Subtype.ext
            rfl)
        refine ⟨ei, rfl, ?_⟩
        apply MorphismProperty.Arrow.Hom.ext
        · ext n σ
          apply Subtype.ext
          rfl
        · rfl
      let ei (X : TopCat.{u}) (A B : Set X) := (hex X A B).choose
      have hei (X : TopCat.{u}) (A B : Set X) := (hex X A B).choose_spec
      refine ⟨ei, hei, singularChainGeneratorIso, ?_, ?_, ?_⟩
      · intro X n
        exact ⟨singularChainGeneratorIso_hom_generator X n,
          singularChainGeneratorIso_hom_boundary X n⟩
      · intro X Y f n
        exact singularChainGeneratorIso_hom_map_generator f n
      · refine ⟨?_, ?_, ?_⟩
        · intro X A
          refine ⟨rfl, rfl, ?_, fun n ↦ ⟨rfl, rfl⟩⟩
          have hp := (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app
            singularIntegralCoefficients).naturality (ep X A).hom).symm
          change (singularSubspacePair X A).chainComplexπ singularIntegralCoefficients ≫
            SSetPair.chainComplexMap (ep X A).hom singularIntegralCoefficients =
            SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj X)) singularIntegralCoefficients ≫
              (singularSubspace X A).pair.chainComplexπ singularIntegralCoefficients at hp
          have hid : SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj X))
              (singularIntegralCoefficients : ModuleCat.{u} ℤ) = 𝟙 _ :=
            ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj singularIntegralCoefficients).map_id _
          rw [hid, Category.id_comp] at hp
          exact hp
        · intro X Y f A D hf
          let F := (e X A).inv ≫ TopCat.toSSet.map (singularSubspaceMap f A D hf) ≫ (e Y D).hom
          have hF : F ≫ (singularSubspace Y D).ι =
              (singularSubspace X A).ι ≫ TopCat.toSSet.map f := by
            dsimp [F]
            rw [Category.assoc, Category.assoc, he, ← Functor.map_comp]
            have hsq : singularSubspaceMap f A D hf ≫ singularSubspaceInclusion Y D =
                singularSubspaceInclusion X A ≫ f := rfl
            rw [hsq, Functor.map_comp, ← Category.assoc, ← he, Iso.inv_hom_id_assoc]
          let G : (singularSubspace X A).pair ⟶ (singularSubspace Y D).pair :=
            SSetPair.homMk F (TopCat.toSSet.map f) hF
          have hF' : (e X A).hom ≫ F =
              TopCat.toSSet.map (singularSubspaceMap f A D hf) ≫ (e Y D).hom := by
            simp [F]
          have hG : (ep X A).hom ≫ G = singularSubspacePairMap f A D hf ≫ (ep Y D).hom := by
            apply MorphismProperty.Arrow.Hom.ext
            · exact hF'
            · simp [G, ep, singularSubspacePairMap]
          refine ⟨F, hF, hG, ?_⟩
          intro n
          have hc := congrArg
            (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj singularIntegralCoefficients).map) hF'
          have hr := congrArg
            (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj singularIntegralCoefficients).map) hG
          simp only [Functor.map_comp] at hc hr
          refine ⟨hc.symm, hr.symm, ?_, ?_⟩
          · have hh := congrArg
              ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).map)
              hc.symm
            simpa only [Functor.map_comp, SSet.homologyMap, SSetPair.homologyMap,
              Functor.mapIso_hom, HomologicalComplex.homologyFunctor] using hh
          · have hh := congrArg
              ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).map)
              hr.symm
            simpa only [Functor.map_comp, SSet.homologyMap, SSetPair.homologyMap,
              Functor.mapIso_hom, HomologicalComplex.homologyFunctor] using hh
        · let q (P : SSetPair.{u}) (n : ℕ) :
              (P.chainComplex singularIntegralCoefficients).X n ≅
                ModuleCat.of ℤ (((P.right.chainComplex singularIntegralCoefficients).X n) ⧸
                  LinearMap.range ((SSet.chainComplexMap P.hom singularIntegralCoefficients).f n).hom) := by
            let R := singularIntegralCoefficients
            have hh := (P.isColimitCokernelCoforkChainComplexX R n).coconePointUniqueUpToIso
              (ModuleCat.cokernelIsColimit ((SSet.chainComplexMap P.hom R).f n))
            dsimp [SSetPair.cokernelCoforkChainComplexX, ModuleCat.cokernelCocone] at hh
            refine hh ≪≫ ModuleCat.isoMk (Iso.refl _) ?_
            intro k
            ext x
            exact (int_smul_eq_zsmul (AddCommGroup.toIntModule _) k x).trans
              (int_smul_eq_zsmul (Submodule.Quotient.module
                (LinearMap.range ((SSet.chainComplexMap P.hom R).f n).hom)) k x).symm
          have hq (P : SSetPair.{u}) (n : ℕ)
              (c : (P.right.chainComplex singularIntegralCoefficients).X n) :
              (q P n).hom ((P.chainComplexπ singularIntegralCoefficients).f n c) =
                (LinearMap.range
                  ((SSet.chainComplexMap P.hom singularIntegralCoefficients).f n).hom).mkQ c := by
            have hh := (P.isColimitCokernelCoforkChainComplexX singularIntegralCoefficients n).comp_coconePointUniqueUpToIso_hom (ModuleCat.cokernelIsColimit
                ((SSet.chainComplexMap P.hom singularIntegralCoefficients).f n))
                  WalkingParallelPair.one
            exact congrArg (fun k ↦ k.hom c) hh
          refine ⟨q, hq, ?_, ?_, ?_⟩
          · intro P n c
            have hh := ((P.chainComplexπ singularIntegralCoefficients).comm (n + 1) n).symm
            have hv := congrArg (fun k ↦ k.hom c) hh
            change (P.chainComplexπ singularIntegralCoefficients).f n
                ((P.right.chainComplex singularIntegralCoefficients).d (n + 1) n c) =
              (P.chainComplex singularIntegralCoefficients).d (n + 1) n
                ((P.chainComplexπ singularIntegralCoefficients).f (n + 1) c) at hv
            rw [← hv, hq]
          · intro P Q f n c
            have hn := (((SSetPair.chainComplexFunctorπ.{u} (ModuleCat ℤ)).app
              singularIntegralCoefficients).naturality f).symm
            have hv := congrArg (fun k ↦ (k.f n).hom c) hn
            change (SSetPair.chainComplexMap f singularIntegralCoefficients).f n
                ((P.chainComplexπ singularIntegralCoefficients).f n c) =
              (Q.chainComplexπ singularIntegralCoefficients).f n
                ((SSet.chainComplexMap f.hom.right singularIntegralCoefficients).f n c) at hv
            rw [hv, hq]
          · intro X A B n
            rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp]
            rw [(hei X A B).2]

end HolomorphicAnosov
