import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietorisData
import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietorisConnecting
import HolomorphicAnosov.Topology.Homology.SmallChainInclusionEquivalence
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Exact.Basic

/-!
# Hatcher's compact-support relative homology sequence

Hatcher, *Algebraic Topology*, relative Mayer–Vietoris, pp.152–153;
coefficient chains, p.153; Lemma3.27 step(1), p.237.
Here support on K means the relative theory H_k(X, X \\ K; G), not cohomology
with compact supports and not the compact image of an ordinary singular chain.
The relative chains are Mathlib's actual cokernel chain complexes of singular
simplicial subspace inclusions, with an arbitrary abelian coefficient group.
-/

noncomputable section

namespace HolomorphicAnosov.Topology

open CategoryTheory

universe u

/-- Singular pair maps preserve composition.
Source: Hatcher, *Algebraic Topology*, relative chains, pp.152–153.
The restricted map on complement subspaces sends `x` to `g (f x)` in either
construction. Postcomposition of each singular simplex therefore gives equal
left components. The ambient components agree by the same calculation.
Extensionality of morphisms of simplicial pairs gives the asserted equality. -/
theorem supportSingularPairMap_comp
    {X Y Z : TopCat.{u}} (K : Set X) (L : Set Y) (M : Set Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Set.MapsTo f Kᶜ Lᶜ) (hg : Set.MapsTo g Lᶜ Mᶜ) :
    supportSingularPairMap K M (f ≫ g) (fun _ hx ↦ hg (hf hx)) =
      supportSingularPairMap K L f hf ≫ supportSingularPairMap L M g hg := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext n s
    rfl
  · ext n s
    rfl

private theorem supportMap_comp
    {X Y Z : TopCat.{u}} (K : Set X) (L : Set Y) (M : Set Z)
    {G G' G'' : ModuleCat.{u} ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Set.MapsTo f Kᶜ Lᶜ) (hg : Set.MapsTo g Lᶜ Mᶜ)
    (γ : G ⟶ G') (η : G' ⟶ G'') (k : ℕ) :
    supportSingularHomologyMap K M (f ≫ g) (fun _ hx ↦ hg (hf hx)) (γ ≫ η) k =
      (supportSingularHomologyMap L M g hg η k).comp
        (supportSingularHomologyMap K L f hf γ k) := by
  unfold supportSingularHomologyMap
  have hc :
      ((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map (γ ≫ η)).app
        (supportSingularPair X K) ≫
        SSetPair.chainComplexMap (supportSingularPairMap K M (f ≫ g)
          (fun _ hx ↦ hg (hf hx))) G'' =
      (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map γ).app
        (supportSingularPair X K) ≫
        SSetPair.chainComplexMap (supportSingularPairMap K L f hf) G') ≫
      (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map η).app
        (supportSingularPair Y L) ≫
        SSetPair.chainComplexMap (supportSingularPairMap L M g hg) G'') := by
    simp only [supportSingularPairMap_comp, SSetPair.chainComplexMap, Functor.map_comp,
      NatTrans.comp_app, Category.assoc, NatTrans.naturality_assoc]
  rw [hc, HomologicalComplex.homologyMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_naturality
    {X Y : TopCat.{u}} {K K' : Set X} {L L' : Set Y}
    (hK : K' ⊆ K) (hL : L' ⊆ L) {G G' : ModuleCat.{u} ℤ}
    (f : X ⟶ Y) (hf : Set.MapsTo f Kᶜ Lᶜ) (hf' : Set.MapsTo f K'ᶜ L'ᶜ)
    (γ : G ⟶ G') (k : ℕ) :
    (supportSingularHomologyRestrict Y G' hL k).comp
        (supportSingularHomologyMap K L f hf γ k) =
      (supportSingularHomologyMap K' L' f hf' γ k).comp
        (supportSingularHomologyRestrict X G hK k) := by
  unfold supportSingularHomologyRestrict
  have h₁ := supportMap_comp K L L' f (𝟙 Y) hf
    (fun _ hx h ↦ hx (hL h)) γ (𝟙 G') k
  have h₂ := supportMap_comp K K' L' (𝟙 X) f
    (fun _ hx h ↦ hx (hK h)) hf' (𝟙 G) γ k
  simpa using (h₁.symm.trans (by simpa using h₂))

/- A reusable small-chain excision comparison for the complement of two compact
   supports.  Compactness plus Hausdorffness makes the two complement pieces
   open, and they cover the complement of the support intersection. -/
theorem compact_support_small_chain_inclusion_equivalence
    (D : CompactSupportMVData.{u}) :
    let Y := TopCat.of ↥((D.left ∩ D.right)ᶜ)
    let U : Set Y := {x | x.val ∉ D.left}
    let V : Set Y := {x | x.val ∉ D.right}
    ∃ e : HomotopyEquiv
      ((singularSubspace Y U ⊔ singularSubspace Y V).toSSet.chainComplex D.coefficients)
      ((TopCat.toSSet.obj Y).chainComplex D.coefficients),
      e.hom = SSet.chainComplexMap
        (singularSubspace Y U ⊔ singularSubspace Y V).ι D.coefficients := by
  let : T2Space D.space := D.hausdorff
  let Y := TopCat.of ↥((D.left ∩ D.right)ᶜ)
  let U : Set Y := {x | x.val ∉ D.left}
  let V : Set Y := {x | x.val ∉ D.right}
  have hU : IsOpen U := D.compact_left.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hV : IsOpen V := D.compact_right.isClosed.isOpen_compl.preimage continuous_subtype_val
  apply small_chain_inclusion_homotopy_equivalence Y U V _ D.coefficients
  rw [hU.interior_eq, hV.interior_eq]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x.val ∈ D.left
  · exact Or.inr (fun hright ↦ x.property ⟨hx, hright⟩)
  · exact Or.inl hx

set_option backward.isDefEq.respectTransparency false in
/-- Hatcher's natural long exact sequence for homology supported on two compact sets.

Source: Hatcher, Algebraic Topology, relative Mayer-Vietoris pp.152-153, coefficient chains p.153;
compact-support sequence in Lemma 3.27 step (1), p.237.

The quantified family of connecting homomorphisms is a conclusion, not an assumed
Mayer–Vietoris oracle. Its naturality holds for continuous maps of the actual
complement pairs and arbitrary coefficient homomorphisms. At every degree the
three exactness assertions cover every position in the long sequence. Surjectivity
of Ψ in degree zero is its ordinary terminal H_0 → 0 assertion.

Complete saved natural-language proof:

Step 1. Set U=M\A and V=M\B. Compactness and Hausdorffness make U,V open. In singular chains over G,
the support-subcomplexes satisfy C(U) intersection C(V)=C(U intersection V); sums mean sums of
subgroups, rather than all chains of a union. The maps c -> (c,-c) and (a,b) -> a+b give a
degreewise short exact sequence 0 -> C(M)/C(U intersection V) -> C(M)/C(U) direct_sum C(M)/C(V) ->
C(M)/(C(U)+C(V)) -> 0. Injectivity, exactness and surjectivity follow by choosing representatives
and the subgroup intersection identity. They commute with boundaries.

Step 2. The inclusion C(U)+C(V) -> C(U union V) induces a homology isomorphism. To see this directly
from excision, quotient both by C(V): the first quotient is C(U)/C(U intersection V), while the
second is C(U union V)/C(V). Excision for the open cover U,V identifies the homology of these two
quotients. Apply the long exact sequences of the two short exact chain sequences with first term
C(V); their comparison is identity on that term and excision on the last term, so the five-lemma
diagram chase gives the asserted middle homology isomorphism.

Step 3. Compare the short exact sequences with first terms C(U)+C(V) and C(U union V), the common
middle term C(M), and last terms their quotient complexes. The preceding homology isomorphism and
the identity on C(M), by the same exact-sequence diagram chase, identify the homology of
C(M)/(C(U)+C(V)) with H_*(M,M\(A intersection B);G). The first quotient in step 1 is already
H_*(M,M\(A union B);G). Taking the long exact sequence of step 1 gives the stated support sequence,
its signs and its natural maps. Everything uses the same coefficient group throughout.

Step 4. For G=F2 the minus sign equals plus, but the signed formulas remain the convention before
specialization. If either support is empty its relative chain quotient is zero; the formulas and
exactness still apply. In degree zero use the terminating H0 -> 0 portion of the nonnegative
chain-complex sequence, not an unintroduced negative-degree group.
-/
theorem hatcher_compact_support_mayer_vietoris :
    ∃ δ : ∀ (D : CompactSupportMVData.{u}) (k : ℕ),
        supportSingularHomology D.space (D.left ∩ D.right) D.coefficients (k + 1) →+
          supportSingularHomology D.space (D.left ∪ D.right) D.coefficients k,
      (∀ D : CompactSupportMVData.{u},
        (∀ k : ℕ,
          Function.Exact (δ D k)
            (supportMayerVietorisPhi D.space D.coefficients D.left D.right k) ∧
          Function.Exact
            (supportMayerVietorisPhi D.space D.coefficients D.left D.right k)
            (supportMayerVietorisPsi D.space D.coefficients D.left D.right k) ∧
          Function.Exact
            (supportMayerVietorisPsi D.space D.coefficients D.left D.right (k + 1))
            (δ D k)) ∧
        Function.Surjective
          (supportMayerVietorisPsi D.space D.coefficients D.left D.right 0)) ∧
      (∀ (D E : CompactSupportMVData.{u}) (F : CompactSupportMVMap D E) (k : ℕ),
        (F.unionMap k).comp (δ D k) = (δ E k).comp (F.interMap (k + 1)) ∧
        (F.middleMap k).comp
            (supportMayerVietorisPhi D.space D.coefficients D.left D.right k) =
          (supportMayerVietorisPhi E.space E.coefficients E.left E.right k).comp
            (F.unionMap k) ∧
        (F.interMap k).comp
            (supportMayerVietorisPsi D.space D.coefficients D.left D.right k) =
          (supportMayerVietorisPsi E.space E.coefficients E.left E.right k).comp
            (F.middleMap k)) := by
  have hzeroRestrict (X : TopCat.{u}) (G : ModuleCat.{u} ℤ)
      {K L : Set X} (h : L ⊆ K) :
      Function.Surjective (supportSingularHomologyRestrict X G h 0) := by
    let P := supportSingularPair X K
    let Q := supportSingularPair X L
    let f : P ⟶ Q := supportSingularPairMap K L (𝟙 X) (fun _ hx hL ↦ hx (h hL))
    have hπ : P.chainComplexπ G ≫ SSetPair.chainComplexMap f G = Q.chainComplexπ G := by
      have hn := (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app G).naturality f).symm
      change P.chainComplexπ G ≫ SSetPair.chainComplexMap f G =
        SSet.chainComplexMap (TopCat.toSSet.map (𝟙 X)) G ≫ Q.chainComplexπ G at hn
      simpa using hn
    have hπH : P.homologyπ G 0 ≫ SSetPair.homologyMap f G 0 = Q.homologyπ G 0 := by
      simpa only [SSetPair.homologyπ, SSetPair.homologyMap,
        HomologicalComplex.homologyMap_comp] using
          congrArg (fun k ↦ HomologicalComplex.homologyMap k 0) hπ
    have hepi : Epi (SSetPair.homologyMap f G 0) := by
      have : Epi (P.homologyπ G 0 ≫ SSetPair.homologyMap f G 0) := by
        rw [hπH]
        exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
          (Q.chainComplexπ G) 0 (by simp)
      exact epi_of_epi (P.homologyπ G 0) (SSetPair.homologyMap f G 0)
    have hsurj := (ModuleCat.epi_iff_surjective (SSetPair.homologyMap f G 0)).mp hepi
    simpa [supportSingularHomologyRestrict, supportSingularHomologyMap, f] using hsurj
  have hterminal (D : CompactSupportMVData.{u}) :
      Function.Surjective (supportMayerVietorisPsi D.space D.coefficients D.left D.right 0) := by
    intro x
    obtain ⟨a, ha⟩ := hzeroRestrict D.space D.coefficients
      (Set.inter_subset_left : D.left ∩ D.right ⊆ D.left) x
    refine ⟨(a, 0), ?_⟩
    simpa [supportMayerVietorisPsi] using ha
  have hsmall (D : CompactSupportMVData.{u}) :=
    compact_support_small_chain_inclusion_equivalence D
  obtain ⟨δ, hexact, hnatural⟩ := compact_support_mayer_vietoris_connecting
  refine ⟨δ, fun D ↦ ⟨hexact D, hterminal D⟩, ?_⟩
  intro D E F k
  refine ⟨hnatural D E F k, ?_, ?_⟩
  · have hl := restrict_naturality (Set.subset_union_left : D.left ⊆ D.left ∪ D.right)
      (Set.subset_union_left : E.left ⊆ E.left ∪ E.right)
      F.ambient F.unionComplement F.left_complement F.coefficients k
    have hr := restrict_naturality (Set.subset_union_right : D.right ⊆ D.left ∪ D.right)
      (Set.subset_union_right : E.right ⊆ E.left ∪ E.right)
      F.ambient F.unionComplement F.right_complement F.coefficients k
    ext x
    · exact (DFunLike.congr_fun hl x).symm
    · simpa [CompactSupportMVMap.middleMap, CompactSupportMVMap.unionMap,
        supportMayerVietorisPhi] using congrArg Neg.neg (DFunLike.congr_fun hr x).symm
  · have hl := restrict_naturality (Set.inter_subset_left : D.left ∩ D.right ⊆ D.left)
      (Set.inter_subset_left : E.left ∩ E.right ⊆ E.left)
      F.ambient F.left_complement F.interComplement F.coefficients k
    have hr := restrict_naturality (Set.inter_subset_right : D.left ∩ D.right ⊆ D.right)
      (Set.inter_subset_right : E.left ∩ E.right ⊆ E.right)
      F.ambient F.right_complement F.interComplement F.coefficients k
    ext x
    simpa [CompactSupportMVMap.middleMap, CompactSupportMVMap.interMap,
      supportMayerVietorisPsi, map_add] using
        congrArg₂ (· + ·) (DFunLike.congr_fun hl x.1).symm (DFunLike.congr_fun hr x.2).symm


end HolomorphicAnosov.Topology

