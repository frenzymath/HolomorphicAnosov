import HolomorphicAnosov.Topology.SignedSingularCrossProduct
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex



noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- Integral relative chains of the original subspace pair; Bredon IV §16, p.222. -/
abbrev RelativeComplex (X : TopCat.{u}) (A : Set X) :=
  (singularSubspacePair X A).chainComplex singularIntegralCoefficients

/-- Ordinary integral relative homology; Bredon IV §16, p.222. -/
abbrev RelativeHomology (X : TopCat.{u}) (A : Set X) (n : ℕ) :=
  (RelativeComplex X A).homology n

/-- The union of the two product subspaces; Bredon IV §16, Proposition 16.3. -/
def ProductSubspace {X Y : TopCat.{u}} (A : Set X) (B : Set Y) : Set (X × Y) :=
  A ×ˢ Set.univ ∪ Set.univ ×ˢ B

/-- The continuous product of the two original maps; Hatcher p.277. -/
def productMap {X Y X' Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    TopCat.of (X × Y) ⟶ TopCat.of (X' × Y') :=
  TopCat.ofHom (f.hom.prodMap g.hom)

/-- The native map on integral singular chains; Bredon IV §16, p.220. -/
abbrev chainMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (SSet.chainComplexMap (TopCat.toSSet.map f) singularIntegralCoefficients).f n

/-- The native ambient-to-relative chain projection; Bredon IV §16, p.222. -/
abbrev relativeProjection (X : TopCat.{u}) (A : Set X) (n : ℕ) :=
  ((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).f n

/-- The induced relative homology map of a map of subspaces; Bredon p.222. -/
abbrev relativeMap {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :=
  SSetPair.homologyMap (singularSubspacePairMap f A B hf) singularIntegralCoefficients n

/-- Change only the written degree using its equality; no chain is changed. -/
def castChain (X : TopCat.{u}) {m n : ℕ} (h : m = n) (a : Chain X m) : Chain X n :=
  h ▸ a

/-- Change only the written relative-homology degree using its equality. -/
def castRelativeHomology (X : TopCat.{u}) (A : Set X) {m n : ℕ} (h : m = n)
    (a : RelativeHomology X A m) : RelativeHomology X A n :=
  h ▸ a

/-- The positive unit-coefficient point generator; Bredon IV §16, p.220. -/
def pointChain (X : TopCat.{u}) (x : X) : Chain X 0 :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := singularIntegralCoefficients)
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌)).symm
      (ContinuousMap.const _ x))).hom (ULift.up 1)

/-- Insertion of the fixed first coordinate; Bredon IV §16, p.220. -/
def insertLeft (X Y : TopCat.{u}) (x : X) : Y ⟶ TopCat.of (X × Y) :=
  TopCat.ofHom ⟨fun y ↦ (x, y), continuous_const.prodMk continuous_id⟩

/-- Insertion of the fixed second coordinate; Bredon IV §16, p.220. -/
def insertRight (X Y : TopCat.{u}) (y : Y) : X ⟶ TopCat.of (X × Y) :=
  TopCat.ofHom ⟨fun x ↦ (x, y), continuous_id.prodMk continuous_const⟩


end HolomorphicAnosov.Topology
