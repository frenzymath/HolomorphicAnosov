import HolomorphicAnosov.Topology.EuclideanPositiveLocalClassZeroFreeGenerator
import HolomorphicAnosov.Topology.EuclideanPositiveLocalConnecting
import HolomorphicAnosov.Topology.EuclideanPositiveBoundaryClassFreeGenerator
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexCoordinateRecovery
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexEdgeDeterminant
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexFaceAvoidsZero
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexFaceRelativeZero
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexEmbeddedInterior
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.EuclideanPositiveLocalClass
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The standard positive coordinate on Euclidean local integral homology

Source: Hatcher, *Algebraic Topology*, Corollary 2.14 p.114, the relative
exact sequence pp.115–118, excision pp.119–124, local orientations
pp.233–234, and the ordered-simplex orientation convention p.269;
Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §1.1 p.1. DAG node:
`topo.euclidean_positive_local_coordinate_g10`.

The specified positive class is reused literally. Scalar multiplication
by it defines an actual integer-linear map. A named free-generation
certificate permits inversion of that map, fixing the coordinate without
an arbitrary choice of orientation, basis, or unrelated homology group.
Every homology object here is unaugmented point-relative singular homology;
in dimension zero it is ordinary `H₀(point, empty; ℤ)`.
-/

noncomputable section

namespace HolomorphicAnosov

/-- The actual integral homology object of the Euclidean point-relative pair.

Source: Hatcher pp.115–118,233–234. This abbreviation denotes exactly the
native relative homology used by `euclideanPositiveLocalClass`, with the
same `ULift ℤ` coefficient object. It introduces no abstract homology
carrier or augmentation, including when `n = 0`.
-/
abbrev EuclideanLocalIntegralHomology (n : ℕ) : ModuleCat ℤ :=
  (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
    ({0} : Set _)ᶜ).homology (C := ModuleCat ℤ) reducedSingularIntegralCoefficients n

/-- The integer-linear map `k ↦ k • ωₙ` for the specified positive local class.

Source: Hatcher pp.233–234,269. `LinearMap.toSpanSingleton` applies scalar
multiplication to this exact class; no freeness or nonzero-class assumption
is needed to construct the map itself. The following certificate concerns
this fixed map, rather than supplying a different generator.
-/
def euclideanPositiveLocalCoefficientMap (n : ℕ) :
    ℤ →ₗ[ℤ] EuclideanLocalIntegralHomology n :=
  LinearMap.toSpanSingleton ℤ _ (euclideanPositiveLocalClass n)

/-- The specified positive class freely generates Euclidean local integral homology.

Source: Hatcher Corollary 2.14 p.114, the relative exact sequence
pp.115–118, excision pp.119–124, local orientations pp.233–234 and the
ordered-simplex convention p.269. This is the free-generation construction
certificate of `topo.euclidean_positive_local_coordinate_g10`.

Complete natural-language proof:

The prescribed affine simplex has vertices `(-1,…,-1), e₁,…,eₙ`.
Its edge matrix is `I + 11ᵀ`, with determinant `n+1 > 0`. Its unique
zero preimage has all barycentric weights `1/(n+1)`, so zero is in its
interior. The simplex is consequently an embedded closed disk containing
zero in its interior, oriented positively by the ordered edge basis.
Its faces avoid zero, as certified in the construction of the fixed local
class. The relative class is precisely that of its coefficient-one chain.

For `n > 0`, excision identifies local homology at zero with the corresponding
local homology of this simplex. The pair of the simplex and its punctured
interior point has the same homology as the simplex and its boundary:
the punctured simplex deformation retracts radially from that point onto
the boundary, and the relative exact sequence and homotopy invariance give
the comparison isomorphism. The connecting homomorphism takes the class of
the ordered simplex to its alternating oriented boundary cycle. The simplex
is contractible; its boundary is an `(n-1)`-sphere. Hatcher's sphere
calculation identifies its reduced top homology with the integers and the
coefficient-one oriented boundary with a generator. One can see the latter
directly in the boundary simplicial complex: the cycle equations force the
coefficients on adjacent faces to agree with their alternating orientation
signs, leaving exactly one freely chosen integer. The canonical simplicial
to singular comparison carries this boundary cycle to the singular one,
and hence the connecting isomorphism carries the specified local simplex
class to a free generator. Thus its integer multiples exhaust local homology
and no two distinct multiples coincide.

For `n = 1`, the boundary is `S⁰`; the exact sequence uses the augmentation
kernel of `H₀(S⁰; ℤ) = ℤ ⊕ ℤ`. The alternating endpoint difference freely
generates this kernel. It does not generate the whole ordinary zero-degree
group. For `n = 0`, Euclidean space is a singleton and its punctured
subspace is empty. Ordinary point homology in degree zero is the integer
coefficient module, and the fixed simplex class has coefficient one.
Integer multiplication on that class is therefore bijective as well.

All comparisons use the actual singular subspace pair and integral
coefficients. The universe lift of the coefficients preserves the integer
module. The edge-basis convention fixes the positive sign; neither a
caller-chosen local orientation nor a freeness hypothesis is an input.
-/
theorem euclideanPositiveLocalClass_free_generator (n : ℕ) :
    Function.Bijective (euclideanPositiveLocalCoefficientMap n) := by
  cases n with
  | zero => exact euclideanPositiveLocalClass_zero_free_generator
  | succ n =>
    apply (euclideanPositiveLocalClass_free_generator_iff_boundary n).mpr
    exact euclideanPositiveBoundaryClass_free_generator n

/-- The standard positive local coordinate `κₙ`, inverse to `k ↦ k • ωₙ`.

Source: Hatcher pp.233–234,269 and Dold §1.1 p.1. Its data are the inverse
of the actual scalar-multiplication map, using only the named bijectivity
certificate. Thus `κₙ(a)` is the unique integer coefficient of the SAME
specified positive class. In dimension zero this is the ordinary
coefficient of the positive point class. No orientation choice is supplied
with a map, and no data are replaced by a postponed proof.
-/
def euclideanPositiveLocalCoordinate (n : ℕ) :
    EuclideanLocalIntegralHomology n ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective (euclideanPositiveLocalCoefficientMap n)
    (euclideanPositiveLocalClass_free_generator n)).symm

/-- Normalization, reconstruction, and uniqueness of the fixed positive coordinate.

Source: Hatcher's local-orientation convention pp.233–234,269 and Dold
§1.1 p.1; this is the algebraic characterization in the current node.

Complete natural-language proof: The coefficient map sends `1` to `ωₙ`
by `one_smul`. Its inverse therefore sends `ωₙ` to `1`. Applying the
coefficient map after its inverse gives `(κₙ(a)) • ωₙ = a` for every
class `a`. If an integer-linear equivalence `e` also sends `ωₙ` to `1`,
write `a = (κₙ(a)) • ωₙ` using this reconstruction. Linearity gives
`e(a) = κₙ(a) • e(ωₙ) = κₙ(a) • 1 = κₙ(a)`. Extensionality of linear
equivalences gives `e = κₙ`. This argument applies unchanged in degree
zero, using the ordinary point class and the already certified inverse.
-/
theorem euclideanPositiveLocalCoordinate_characterization (n : ℕ) :
    euclideanPositiveLocalCoordinate n (euclideanPositiveLocalClass n) = 1 ∧
    (∀ a : EuclideanLocalIntegralHomology n,
      euclideanPositiveLocalCoordinate n a • euclideanPositiveLocalClass n = a) ∧
    (∀ e : EuclideanLocalIntegralHomology n ≃ₗ[ℤ] ℤ,
      e (euclideanPositiveLocalClass n) = 1 → e = euclideanPositiveLocalCoordinate n) := by
  let L := LinearEquiv.ofBijective (euclideanPositiveLocalCoefficientMap n)
    (euclideanPositiveLocalClass_free_generator n)
  have hnorm : euclideanPositiveLocalCoordinate n (euclideanPositiveLocalClass n) = 1 := by
    change L.symm (euclideanPositiveLocalClass n) = 1
    simpa [L, euclideanPositiveLocalCoefficientMap] using L.symm_apply_apply (1 : ℤ)
  have hreconstruct : ∀ a : EuclideanLocalIntegralHomology n,
      euclideanPositiveLocalCoordinate n a • euclideanPositiveLocalClass n = a := by
    intro a
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (EuclideanLocalIntegralHomology n))]
    exact L.apply_symm_apply a
  refine ⟨hnorm, hreconstruct, ?_⟩
  intro e he
  ext a
  calc
    e a = e (euclideanPositiveLocalCoordinate n a • euclideanPositiveLocalClass n) :=
      congrArg e (hreconstruct a).symm
    _ = euclideanPositiveLocalCoordinate n a := by rw [map_zsmul, he]; simp

end HolomorphicAnosov

