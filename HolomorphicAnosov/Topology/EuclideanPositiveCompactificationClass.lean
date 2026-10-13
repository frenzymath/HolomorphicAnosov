import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.EuclideanPositiveLocalClass
import HolomorphicAnosov.Topology.ContractibleSubspaceHomologyProjection
import HolomorphicAnosov.Topology.EuclideanPuncturedCompactification

/-!
# The positively normalized Euclidean compactification homology class

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §1.1 p.1; Hatcher, *Algebraic Topology*, sphere homology
p.114, pair exact sequence pp.115–118, excision pp.119–124, local orientation
pp.233–234 and ordered-simplex orientation p.269.
DAG node: `topo.euclidean_positive_compactification_class_g10`.

These are ORDINARY, unaugmented integral singular homology classes. The existing
coefficient object is `ULift ℤ`, with its canonical integral module structure;
its name mentioning reduced homology does not augment the complexes below.
The positive local class is the published specified affine-simplex class. In
positive dimension unique normalization constructs the compactification class.
Dimension zero uses the actual coefficient-one finite-point zero-simplex class,
not uniqueness in ordinary H₀ of the two-point compactification.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HolomorphicAnosov
open CategoryTheory CategoryTheory.Limits Set
open scoped Simplicial

/-- The native one-point compactification of the ordinary Euclidean L2 model.
Source: Dold §1.1 p.1 and Mathlib `OnePoint`; dimension zero is the two-point space. -/
abbrev EuclideanCompactification (n : ℕ) := OnePoint (EuclideanSpace ℝ (Fin n))

/-- Ordinary integral singular homology of that SAME compactification.
Source: Dold §1.1 and Hatcher pp.108–114. No augmentation or reduced H₀ is used. -/
abbrev EuclideanCompactificationHomology (n : ℕ) : ModuleCat ℤ :=
  (TopCat.toSSet.obj (TopCat.of (EuclideanCompactification n))).homology
    reducedSingularIntegralCoefficients n

/-- The actual pair supporting the finite-origin local homology class.
Source: Hatcher pp.115–118; Dold §1.1. -/
def euclideanCompactificationOriginPair (n : ℕ) : SSetPair :=
  singularSubspacePair (TopCat.of (EuclideanCompactification n))
    ({OnePoint.some (0 : EuclideanSpace ℝ (Fin n))} : Set _)ᶜ

/-- The ordinary relative projection q₀ induced by the actual relative chain quotient.
Source: Hatcher pp.115–118; Mathlib `SSetPair.homologyπ`. -/
def euclideanCompactificationOriginProjection (n : ℕ) :
    EuclideanCompactificationHomology n ⟶
      (euclideanCompactificationOriginPair n).homology
        reducedSingularIntegralCoefficients n :=
  (euclideanCompactificationOriginPair n).homologyπ
    reducedSingularIntegralCoefficients n

/-- The literal finite-point inclusion, with the native compactification topology.
Source: Dold §1.1 and Mathlib `OnePoint.continuous_coe`. -/
def euclideanCompactificationFiniteInclusion (n : ℕ) :
    TopCat.of (EuclideanSpace ℝ (Fin n)) ⟶ TopCat.of (EuclideanCompactification n) :=
  TopCat.ofHom ⟨OnePoint.some, OnePoint.continuous_coe⟩

/-- Finite inclusion takes punctured Euclidean space into the complement of the
finite origin, making it an actual map of topological pairs.

Source: Hatcher p.118, maps of pairs. If a finite point x mapped to the finite
origin, injectivity of the native `OnePoint.some` constructor gives x=0. This
contradicts membership in the punctured source. No infinity is in the image of
finite inclusion; no dimension or nonemptiness assumption is needed.
-/
theorem euclideanCompactificationFiniteInclusion_mapsPunctured (n : ℕ) :
    MapsTo (euclideanCompactificationFiniteInclusion n)
      ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ
      ({OnePoint.some (0 : EuclideanSpace ℝ (Fin n))} :
        Set (EuclideanCompactification n))ᶜ := by
  intro x hx hzero
  exact hx (OnePoint.coe_injective hzero)

/-- The actual finite inclusion-induced relative homology map j₀.
Source: Hatcher pp.118–124 and Dold §1.1. This is the homology map of the original
singular pair arrow; it is not a selected group isomorphism or normalization axiom. -/
def euclideanCompactificationLocalInclusion (n : ℕ) :
    (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0} : Set _)ᶜ).homology reducedSingularIntegralCoefficients n ⟶
    (euclideanCompactificationOriginPair n).homology
      reducedSingularIntegralCoefficients n :=
  SSetPair.homologyMap
    (singularSubspacePairMap (euclideanCompactificationFiniteInclusion n)
      ({0} : Set _)ᶜ ({OnePoint.some (0 : EuclideanSpace ℝ (Fin n))} : Set _)ᶜ
      (euclideanCompactificationFiniteInclusion_mapsPunctured n))
    reducedSingularIntegralCoefficients n

/-- Positive-dimensional existence and uniqueness of the normalized class.

Source: Dold §1.1 p.1; the complete source-composite proof is the current DAG
node's step S1, from Hatcher pp.114–124,233–234,269:

Write S=ℝⁿ∪{∞} with its native one-point compactification topology. For n>0,
stereographic coordinates identify S with the unit n-sphere: x maps to
(2x/(‖x‖²+1),(‖x‖²−1)/(‖x‖²+1)), and infinity maps to the north pole. The
inverse away from that pole is z/(1−s). The formula has unit norm, the maps are
inverse, and the limit at infinity is the north pole; continuity and the
compact-to-Hausdorff bijection criterion give the compactification homeomorphism.
Stereographic coordinates based at the finite origin instead show S minus that
point is homeomorphic to ℝⁿ and contractible. For n>1 the outside groups in the
relevant pair exact sequence vanish, giving an isomorphism
q₀:Hₙ(S)→Hₙ(S,S minus {0}). For n=1 the degree-zero map from the connected
complement to the connected sphere is the canonical H₀ isomorphism; exactness
yields the same top projection isomorphism. Excision identifies the finite-origin
pair with (ℝⁿ,ℝⁿ minus zero) by finite inclusion, since the closed removed
infinity lies in the open complement of the finite origin. The map j₀ below is
that actual induced pair map. The specified positive affine-simplex local class
ωₙ fixes the orientation. The unique inverse image q₀⁻¹(j₀ωₙ) exists and is
unique. This proves precisely the displayed construction certificate, without
assuming a generator or replacing the pair map with an arbitrary isomorphism.

Dimension zero is deliberately excluded from this assertion: H₀(S⁰)=ℤ⊕ℤ,
and q₀ kills the infinity summand. Its finite-point class is defined separately
below. All Euclidean models and compactifications are actual nonempty carriers;
no extra nonemptiness, connectedness or orientation premise is supplied.
-/
theorem euclideanPositiveCompactificationClass_unique (n : ℕ) (hn : 0 < n) :
    ∃! μ : EuclideanCompactificationHomology n,
      (euclideanCompactificationOriginProjection n).hom μ =
        (euclideanCompactificationLocalInclusion n).hom (euclideanPositiveLocalClass n) := by
  have : ContractibleSpace
      ↥(({OnePoint.some (0 : EuclideanSpace ℝ (Fin n))} :
        Set (EuclideanCompactification n))ᶜ) :=
    euclideanPuncturedCompactification_contractible n _
  have : IsIso (euclideanCompactificationOriginProjection n) :=
    contractible_subspace_homology_projection_isIso
      (TopCat.of (EuclideanCompactification n)) _ reducedSingularIntegralCoefficients n hn
  let q := euclideanCompactificationOriginProjection n
  let y := (euclideanCompactificationLocalInclusion n).hom (euclideanPositiveLocalClass n)
  refine ⟨(inv q).hom y, ?_, ?_⟩
  · change (inv q ≫ q).hom y = y
    simp
  · intro μ hμ
    have h := congrArg (fun z ↦ (inv q).hom z) hμ
    change (q ≫ inv q).hom μ = (inv q).hom y at h
    simpa using h

/-- The coefficient-one finite-point singular zero-chain, before passing to homology.
Source: Hatcher p.108; Dold §1.1. The singular simplex is literally constant at
finite zero, never at infinity, and its coefficient is the lifted integer one. -/
def euclideanCompactificationFiniteZeroChain :
    ((TopCat.toSSet.obj (TopCat.of (EuclideanCompactification 0))).chainComplex
      reducedSingularIntegralCoefficients).X 0 :=
  ((TopCat.toSSet.obj (TopCat.of (EuclideanCompactification 0))).ιChainComplex
    (R := reducedSingularIntegralCoefficients)
    (((TopCat.of (EuclideanCompactification 0)).toSSetObjEquiv _).symm
      (⟨fun _ ↦ OnePoint.some (0 : EuclideanSpace ℝ (Fin 0)),
        continuous_const⟩ : C(Convexity.StdSimplex ℝ (Fin 1), EuclideanCompactification 0))))
    (ULift.up 1)

/-- The ordinary finite-point zero-chain has zero outgoing boundary.

Source: Hatcher pp.108–110, the ordinary natural-number-indexed singular complex.
There is no negative chain degree. Its degree-zero short complex therefore has
zero outgoing map, so the actual coefficient-one zero-chain is a cycle. This
assertion is about that ordinary chain complex, not an augmented complex, whose
coefficient-sum differential would send it to one.
-/
theorem euclideanCompactificationFiniteZeroChain_cycle :
    let K := (TopCat.toSSet.obj (TopCat.of (EuclideanCompactification 0))).chainComplex
      reducedSingularIntegralCoefficients
    (K.sc 0).g.hom euclideanCompactificationFiniteZeroChain = 0 := by
  rfl

/-- The actual ordinary H₀ class of the coefficient-one finite point.
Source: Hatcher pp.108–110 and Dold §1.1. The native kernel/image quotient and its
canonical homology comparison insert that specified cycle, with no arbitrary
sphere generator or reduced-class substitution. -/
def euclideanCompactificationFiniteZeroClass : EuclideanCompactificationHomology 0 :=
  let K := (TopCat.toSSet.obj (TopCat.of (EuclideanCompactification 0))).chainComplex
    reducedSingularIntegralCoefficients
  (K.sc 0).moduleCatHomologyIso.inv
    ((K.sc 0).moduleCatLeftHomologyData.π
      ⟨euclideanCompactificationFiniteZeroChain,
        euclideanCompactificationFiniteZeroChain_cycle⟩)

/-- The standard positively normalized compactification class μₙ.

Source: Dold §1.1 p.1. For positive n its data are selected from the named UNIQUE
existence certificate for the actual q₀ and j₀ and specified ωₙ. For n=0 its data
are the ordinary coefficient-one finite-point class in the two-point space. No
unnamed admitted data, caller-chosen orientation or arbitrary sphere class occurs.
-/
def euclideanPositiveCompactificationClass (n : ℕ) : EuclideanCompactificationHomology n :=
  if h : n = 0 then
    h.symm ▸ euclideanCompactificationFiniteZeroClass
  else
    (euclideanPositiveCompactificationClass_unique n (Nat.pos_of_ne_zero h)).exists.choose

/-- The constructed class has the required positive local normalization, the
positive-dimensional uniqueness property, and the specified ordinary finite H₀ class.

Source: Dold §1.1 p.1; the current node's complete source-composite proof follows
Hatcher pp.114–124,233–234,269. Stereographic compactification identifies the
positive-dimensional one-point space with the sphere, and its complement of the
finite origin with contractible Euclidean space. The pair exact sequence makes
q₀ an isomorphism: for n>1 use vanishing in the adjoining positive degrees; for
n=1 use the actual H₀ isomorphism from the connected complement to the connected
sphere. Finite inclusion induces the excision isomorphism j₀ on the origin pair.
The prescribed positively oriented affine-simplex class ωₙ fixes the sign, so
q₀⁻¹(j₀ωₙ) is the unique normalized class. The definition chooses precisely
that unique witness; its choice property gives the first two clauses for n>0.
For n=0, the finite and infinite points are separate components. The definition
is the cycle class of the coefficient-one finite-point zero-simplex, with zero
outgoing ordinary boundary. The relative chain projection kills the infinity
point summand and preserves this finite-point chain. The specified local
zero-simplex class is also coefficient one at its unique Euclidean point, and
the actual finite inclusion sends that simplex to the specified finite-point
simplex. Projection and induced pair-map naturality therefore give the same
normalization equation in degree zero. Finally the zero branch of the displayed
definition is exactly the finite-point class. No ordinary degree-zero uniqueness
is asserted: adding an infinity-point class leaves its relative projection
unchanged. This handles every n, including zero, without a reduced H₀ convention.
-/
theorem euclidean_positive_compactification_class :
    (∀ n : ℕ, (euclideanCompactificationOriginProjection n).hom
      (euclideanPositiveCompactificationClass n) =
        (euclideanCompactificationLocalInclusion n).hom (euclideanPositiveLocalClass n)) ∧
    (∀ (n : ℕ), 0 < n → ∀ ν : EuclideanCompactificationHomology n,
      (euclideanCompactificationOriginProjection n).hom ν =
        (euclideanCompactificationLocalInclusion n).hom (euclideanPositiveLocalClass n) →
          ν = euclideanPositiveCompactificationClass n) ∧
    euclideanPositiveCompactificationClass 0 = euclideanCompactificationFiniteZeroClass := by
  have hzero : (euclideanCompactificationOriginProjection 0).hom
      euclideanCompactificationFiniteZeroClass =
        (euclideanCompactificationLocalInclusion 0).hom (euclideanPositiveLocalClass 0) := by
    let R := reducedSingularIntegralCoefficients
    let P := singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin 0))) ({0} : Set _)ᶜ
    let Q := euclideanCompactificationOriginPair 0
    let f := singularSubspacePairMap (euclideanCompactificationFiniteInclusion 0)
      ({0} : Set _)ᶜ ({OnePoint.some (0 : EuclideanSpace ℝ (Fin 0))} : Set _)ᶜ
      (euclideanCompactificationFiniteInclusion_mapsPunctured 0)
    let z := euclideanCompactificationFiniteZeroChain
    let w := (Q.chainComplexπ R).f 0 z
    have hw : ((Q.chainComplex R).sc 0).g.hom w = 0 := by
      simp [HomologicalComplex.sc, HomologicalComplex.shape]
    have hleft := GoodPair.shortComplex_homologyMap_cycle
      ((HomologicalComplex.shortComplexFunctor _ _ 0).map (Q.chainComplexπ R))
      ⟨z, euclideanCompactificationFiniteZeroChain_cycle⟩ ⟨w, hw⟩ rfl
    have hchain : (SSetPair.chainComplexMap f R).f 0 (euclideanPositiveLocalChain 0) = w := by
      change ((P.chainComplexπ R).f 0 ≫ (SSetPair.chainComplexMap f R).f 0) _ = _
      rw [pair_projection_naturality]
      change ((Q.chainComplexπ R).f 0)
        (((SSet.chainComplexMap f.hom.right R).f 0)
          (((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 0))))).ιChainComplex
            (R := R) (((TopCat.of (EuclideanSpace ℝ (Fin 0))).toSSetObjEquiv _).symm
              (euclideanPositiveSimplex 0)) (ULift.up 1))) =
        ((Q.chainComplexπ R).f 0) z
      apply congrArg ((Q.chainComplexπ R).f 0)
      change (((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 0))))).ιChainComplex
          (R := R) (((TopCat.of (EuclideanSpace ℝ (Fin 0))).toSSetObjEquiv _).symm
            (euclideanPositiveSimplex 0)) ≫ (SSet.chainComplexMap f.hom.right R).f 0)
          (ULift.up 1) = z
      rw [SSet.ι_chainComplexMap_f]
      congr 2
      congr 1
      apply ((TopCat.of (EuclideanCompactification 0)).toSSetObjEquiv _).injective
      ext t
      apply congrArg OnePoint.some
      exact Subsingleton.elim _ _
    have hright := GoodPair.shortComplex_homologyMap_cycle
      ((HomologicalComplex.shortComplexFunctor _ _ 0).map (SSetPair.chainComplexMap f R))
      ⟨euclideanPositiveLocalChain 0, euclideanPositiveLocalChain_cycle 0⟩ ⟨w, hw⟩ hchain
    exact hleft.trans hright.symm
  refine ⟨?_, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      simpa [euclideanPositiveCompactificationClass] using hzero
    · simpa [euclideanPositiveCompactificationClass, hn] using
        (euclideanPositiveCompactificationClass_unique n (Nat.pos_of_ne_zero hn)).exists.choose_spec
  · intro n hn ν hν
    simpa [euclideanPositiveCompactificationClass, Nat.ne_of_gt hn] using
      (euclideanPositiveCompactificationClass_unique n hn).unique hν
        (euclideanPositiveCompactificationClass_unique n hn).exists.choose_spec
  · simp [euclideanPositiveCompactificationClass]


end HolomorphicAnosov

