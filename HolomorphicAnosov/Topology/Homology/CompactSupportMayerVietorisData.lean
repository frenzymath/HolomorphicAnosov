import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Compact support singular pairs and Mayer–Vietoris maps

This module contains the concrete relative singular pair, support homology maps,
and compact-support data structures used by the Hatcher Mayer–Vietoris theorem.
Sources: Hatcher, *Algebraic Topology*, pp.152–153 and Lemma 3.27 p.237.
-/

noncomputable section

namespace HolomorphicAnosov.Topology

open CategoryTheory

universe u

/-- The actual singular simplicial pair (X \\ K) → X.
Source: Hatcher, pp.153 and237, H_k(X||K;G)=H_k(X,X\\K;G).
The subspace has its induced topology, and its inclusion is a monomorphism;
applying the singular simplicial-set functor gives a genuine simplicial pair. -/
def supportSingularPair (X : TopCat.{u}) (K : Set X) : SSetPair.{u} := by
  let i : TopCat.of ↥(Kᶜ) ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  haveI : Mono i := (TopCat.mono_iff_injective i).2 Subtype.val_injective
  exact SSetPair.of (TopCat.toSSet.map i)

/-- Singular chains relative to the complement of K, with coefficients in G.
Source: Hatcher, p.153: C_n(X,X\\K;G)=C_n(X;G)/C_n(X\\K;G).
`SSetPair.chainComplex` is the categorical cokernel, and its evaluation in
each degree is also the cokernel; the differential is induced by the usual
alternating face maps. No excision or Mayer–Vietoris assumption enters this definition. -/
abbrev supportSingularChainComplex (X : TopCat.{u}) (K : Set X)
    (G : ModuleCat.{u} ℤ) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (supportSingularPair X K).chainComplex G

/-- H_k(X||K;G), the ordinary relative singular homology of (X,X\\K).
Source: Hatcher, pp.153 and237. An abelian group is used as its canonical
integer module. Degrees are natural numbers, so this is unreduced homology. -/
abbrev supportSingularHomology (X : TopCat.{u}) (K : Set X)
    (G : ModuleCat.{u} ℤ) (k : ℕ) : ModuleCat.{u} ℤ :=
  (supportSingularChainComplex X K G).homology k

/-- The singular pair map induced by a continuous map carrying the complement
of K into the complement of L. Source: Hatcher, functorial relative chains,
p.153. The left map is the restriction of the given ambient map; the square
with the subspace inclusions commutes literally. -/
def supportSingularPairMap {X Y : TopCat.{u}} (K : Set X) (L : Set Y)
    (f : X ⟶ Y) (hf : Set.MapsTo f Kᶜ Lᶜ) :
    supportSingularPair X K ⟶ supportSingularPair Y L := by
  let left : TopCat.of ↥(Kᶜ) ⟶ TopCat.of ↥(Lᶜ) := TopCat.ofHom
    ⟨fun x ↦ ⟨f x, hf x.property⟩,
      Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val) _⟩
  refine SSetPair.homMk (TopCat.toSSet.map left) (TopCat.toSSet.map f) ?_
  change TopCat.toSSet.map left ≫ TopCat.toSSet.map _ =
    TopCat.toSSet.map _ ≫ TopCat.toSSet.map f
  rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
  congr 1

/-- The genuine induced relative homology map, allowing both an ambient map
of pairs and a coefficient homomorphism. Source: Hatcher, p.153.
First apply the coefficient morphism to the actual relative chain complex,
then the singular pair map; take homology of their composite. -/
def supportSingularHomologyMap {X Y : TopCat.{u}} (K : Set X) (L : Set Y)
    {G G' : ModuleCat.{u} ℤ} (f : X ⟶ Y) (hf : Set.MapsTo f Kᶜ Lᶜ)
    (γ : G ⟶ G') (k : ℕ) :
    supportSingularHomology X K G k →+ supportSingularHomology Y L G' k :=
  (HomologicalComplex.homologyMap
    (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map γ).app
      (supportSingularPair X K) ≫
      SSetPair.chainComplexMap (supportSingularPairMap K L f hf) G') k).hom.toAddMonoidHom

/-- The restriction H_k(X||K;G) → H_k(X||L;G) for L⊆K.
Source: Hatcher, Lemma3.27 step(1), p.237. It is induced by the identity
ambient map and the inclusion X\\K ⊆ X\\L, not an independently supplied map. -/
def supportSingularHomologyRestrict (X : TopCat.{u}) (G : ModuleCat.{u} ℤ)
    {K L : Set X} (h : L ⊆ K) (k : ℕ) :
    supportSingularHomology X K G k →+ supportSingularHomology X L G k :=
  supportSingularHomologyMap K L (𝟙 X) (fun _ hx hL ↦ hx (h hL)) (𝟙 G) k

/-- The signed union restriction c ↦ (c|A,-c|B).
Source: Hatcher, Lemma3.27 step(1), p.237. The finite direct sum of the two
abelian groups is their product, with its canonical integer-module structure. -/
def supportMayerVietorisPhi (X : TopCat.{u}) (G : ModuleCat.{u} ℤ)
    (A B : Set X) (k : ℕ) :
    supportSingularHomology X (A ∪ B) G k →+
      (supportSingularHomology X A G k × supportSingularHomology X B G k) :=
  (supportSingularHomologyRestrict X G (K := A ∪ B) (L := A) Set.subset_union_left k).prod
    (-supportSingularHomologyRestrict X G (K := A ∪ B) (L := B) Set.subset_union_right k)

/-- The intersection restriction sum (a,b) ↦ a|A∩B+b|A∩B.
Source: Hatcher, Lemma3.27 step(1), p.237. -/
def supportMayerVietorisPsi (X : TopCat.{u}) (G : ModuleCat.{u} ℤ)
    (A B : Set X) (k : ℕ) :
    (supportSingularHomology X A G k × supportSingularHomology X B G k) →+
      supportSingularHomology X (A ∩ B) G k :=
  (supportSingularHomologyRestrict X G (K := A) (L := A ∩ B) Set.inter_subset_left k).coprod
    (supportSingularHomologyRestrict X G (K := B) (L := A ∩ B) Set.inter_subset_right k)


/-- The data of one compact-support sequence: a Hausdorff space, two compact
subsets, and an arbitrary abelian coefficient group. Source: Hatcher, relative
Mayer–Vietoris, pp.152–153, and the support specialization on p.237.
No nonemptiness, manifold, local compactness, or coefficient-freeness is imposed. -/
structure CompactSupportMVData where
  space : TopCat.{u}
  hausdorff : T2Space space
  left : Set space
  right : Set space
  compact_left : IsCompact left
  compact_right : IsCompact right
  coefficients : ModuleCat.{u} ℤ

/-- A map of support data, including a coefficient homomorphism.
Source: Hatcher, naturality of relative chains and Mayer–Vietoris, pp.152–153.
The actual pair condition is that each complement maps into its corresponding
complement. This includes restriction to smaller supports under the identity
ambient map. No condition on the images of the supports themselves is assumed. -/
structure CompactSupportMVMap (D E : CompactSupportMVData.{u}) where
  ambient : D.space ⟶ E.space
  coefficients : D.coefficients ⟶ E.coefficients
  left_complement : Set.MapsTo ambient D.leftᶜ E.leftᶜ
  right_complement : Set.MapsTo ambient D.rightᶜ E.rightᶜ

/-- The complement-of-union pair condition induced by a map of the two pairs.
Source: Hatcher, the natural relative-chain diagram, pp.152–153;
(X\\(A∪B))=(X\\A)∩(X\\B). -/
theorem CompactSupportMVMap.unionComplement {D E : CompactSupportMVData.{u}}
    (F : CompactSupportMVMap D E) :
    Set.MapsTo F.ambient (D.left ∪ D.right)ᶜ (E.left ∪ E.right)ᶜ := by
  intro x hx h
  rcases h with h | h
  · exact F.left_complement (fun hxA ↦ hx (Or.inl hxA)) h
  · exact F.right_complement (fun hxB ↦ hx (Or.inr hxB)) h

/-- The complement-of-intersection pair condition induced by a map of the two pairs.
Source: Hatcher, the natural relative-chain diagram, pp.152–153;
(X\\(A∩B))=(X\\A)∪(X\\B). -/
theorem CompactSupportMVMap.interComplement {D E : CompactSupportMVData.{u}}
    (F : CompactSupportMVMap D E) :
    Set.MapsTo F.ambient (D.left ∩ D.right)ᶜ (E.left ∩ E.right)ᶜ := by
  classical
  intro x hx h
  by_cases hxA : x ∈ D.left
  · exact F.right_complement (fun hxB ↦ hx ⟨hxA, hxB⟩) h.2
  · exact F.left_complement hxA h.1

/-- The induced map on the union-support homology term.
Source: Hatcher, pp.152–153 and237, induced relative homology maps. -/
def CompactSupportMVMap.unionMap {D E : CompactSupportMVData.{u}}
    (F : CompactSupportMVMap D E) (k : ℕ) :=
  supportSingularHomologyMap (D.left ∪ D.right) (E.left ∪ E.right)
    F.ambient F.unionComplement F.coefficients k

/-- The induced map on the intersection-support homology term.
Source: Hatcher, pp.152–153 and237, induced relative homology maps. -/
def CompactSupportMVMap.interMap {D E : CompactSupportMVData.{u}}
    (F : CompactSupportMVMap D E) (k : ℕ) :=
  supportSingularHomologyMap (D.left ∩ D.right) (E.left ∩ E.right)
    F.ambient F.interComplement F.coefficients k

/-- The direct-sum map induced on the two separate support terms.
Source: Hatcher, pp.152–153 and237. Finite direct sums of two abelian groups
are their actual products, and both components use the same coefficient map. -/
def CompactSupportMVMap.middleMap {D E : CompactSupportMVData.{u}}
    (F : CompactSupportMVMap D E) (k : ℕ) :=
  AddMonoidHom.prodMap
    (supportSingularHomologyMap D.left E.left F.ambient F.left_complement F.coefficients k)
    (supportSingularHomologyMap D.right E.right F.ambient F.right_complement F.coefficients k)

end HolomorphicAnosov.Topology
