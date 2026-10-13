import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.EuclideanSupportOrientation
import HolomorphicAnosov.Topology.EuclideanPositiveLocalCoordinate

/-!
# Euclidean fixed-point index from the displacement-induced homology map

DAG node: `topo.euclidean_fixed_point_index_definition_g10`.
Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §1.1 and Definition 1.2, printed p.1;
Hatcher, *Algebraic Topology*, ordinary relative singular homology pp.115–118,
positive local orientation pp.233–234 and ordered-coordinate orientation p.269.

For an open U and a continuous f : U → ℝⁿ with compact fixed set, the index is
κₙ((x ↦ x − f(x))₊ o(U,K)). All classes and maps are the actual published
ordinary singular homology constructions. The input contains neither an orientation
choice nor an index law. Compactness is only the admissibility proof needed to form
the canonical supported class. In dimension zero the target is ordinary point-relative
H₀, with the positive point coefficient; no reduced H₀ convention is substituted.
-/

noncomputable section
namespace HolomorphicAnosov

open CategoryTheory Set TopologicalSpace

/-- The fixed set in the actual source subspace U.
Source: Dold Definition 1.2 p.1. The value of f is in ℝⁿ, and is compared with
this point's original ambient inclusion; f need not have values in U. -/
def euclideanFixedSet {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) : Set U :=
  {u | f u = u.val}

/-- The same fixed set as an ambient subset, used by the canonical support pair.
Source: Dold §1.1 and Definition 1.2 p.1. Subtype inclusion is injective and
its inverse image of this image is exactly `euclideanFixedSet f`. -/
def euclideanAmbientFixedSet {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  (Subtype.val : U → EuclideanSpace ℝ (Fin n)) '' euclideanFixedSet f

/-- The actual continuous displacement x − f(x), with Dold's sign convention.
Source: Dold Definition 1.2 p.1. Continuity is continuous subtraction applied to
the original subtype inclusion and f. -/
def euclideanDisplacement {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) : C(U, EuclideanSpace ℝ (Fin n)) :=
  ⟨fun u ↦ u.val - f u, continuous_subtype_val.sub f.continuous⟩

/-- The displacement as a genuine map of the support pair to punctured Euclidean space.
Source: Dold Definition 1.2 p.1; Hatcher induced relative maps p.118.

The source is literally `euclideanSupportPair n U (euclideanAmbientFixedSet f)`.
For u outside the ambient fixed set, u − f(u) cannot be zero: otherwise f(u)=u,
so u itself witnesses membership of its ambient point in the fixed-set image.
Thus the restriction sends the complement into ℝⁿ minus {0}. All pair-map data
and this containment proof are constructed here, with no postponed theorem.
-/
def euclideanDisplacementPairMap {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) :
    euclideanSupportPair n (U : Set _) (euclideanAmbientFixedSet f) ⟶
      singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ :=
  singularSubspacePairMap (TopCat.ofHom (euclideanDisplacement f))
    {u | (u : EuclideanSpace ℝ (Fin n)) ∉ euclideanAmbientFixedSet f}
    ({0} : Set _)ᶜ (by
      intro u hu hz
      have heq : u.val - f u = 0 := Set.mem_singleton_iff.mp hz
      exact hu ⟨u, (sub_eq_zero.mp heq).symm, rfl⟩)

/-- The ordinary integral relative homology map induced by the actual displacement.
Source: Dold Definition 1.2 p.1; Hatcher pp.115–118. Its target is exactly the
published positive-coordinate local homology object, including in dimension zero. -/
def euclideanDisplacementHomologyMap {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) :
    (euclideanSupportPair n (U : Set _) (euclideanAmbientFixedSet f)).homology
        reducedSingularIntegralCoefficients n ⟶ EuclideanLocalIntegralHomology n :=
  SSetPair.homologyMap (euclideanDisplacementPairMap f)
    reducedSingularIntegralCoefficients n

/-- The Euclidean fixed-point index I(f,U)=κₙ((d_f)₊o(U,K)).

Source: Dold §1.1 and Definition 1.2 p.1; Hatcher pp.115–118,233–234,269.
The compact native fixed set has compact ambient image by continuous subtype
inclusion; its image lies in U by each witness's subtype membership. These two
proofs permit the canonical support orientation construction on the SAME native
U pair. Apply the actual displacement homology map and then the canonical positive
local coordinate. No arbitrary homology equivalence, orientation or index data
are inputs. Restriction, additivity, homotopy, product and normalization laws are
not assumed by the definition.

For n=0 the same formula uses ordinary H₀(point,empty;ℤ) and its positive point
coordinate. Empty U and empty fixed set are allowed: the supported class for
empty support is zero. No connectedness or self-map-of-U hypothesis is imposed.
-/
def euclideanFixedPointIndex {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) (hK : IsCompact (euclideanFixedSet f)) : ℤ :=
  let K : Set (EuclideanSpace ℝ (Fin n)) := euclideanAmbientFixedSet f
  have hcompact : IsCompact K := hK.image
    (show Continuous (Subtype.val : U → EuclideanSpace ℝ (Fin n)) from continuous_subtype_val)
  have hcontained : K ⊆ (U : Set (EuclideanSpace ℝ (Fin n))) := by
    rintro x ⟨u, hu, rfl⟩
    exact u.property
  let o := euclideanSupportOrientation n (U : Set (EuclideanSpace ℝ (Fin n))) K
    U.isOpen hcompact hcontained
  euclideanPositiveLocalCoordinate n ((euclideanDisplacementHomologyMap f).hom o)

end HolomorphicAnosov
