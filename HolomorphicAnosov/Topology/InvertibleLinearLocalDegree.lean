import HolomorphicAnosov.Topology.EuclideanPositiveLocalCoordinate
import HolomorphicAnosov.Topology.InvertibleLinearLocalHomologyAction
import HolomorphicAnosov.Topology.SingularSubspaceHomeomorphHomology

/-!
# Local integral homological degree of an invertible real linear map

Sources: Hatcher, *Algebraic Topology*, pp. 118, 125, 134, 136, 233;
Hatcher, *Vector Bundles and K-Theory*, Version 2.2 (2017), pp. 23–24.
The local group is the actual integral singular homology of the punctured Euclidean pair.
The statements assert the scalar action on every class and its coefficient in every genuine
integral generator coordinate. No positive generator or computed degree is an input.
-/

noncomputable section

open CategoryTheory

namespace HolomorphicAnosov

/-- An invertible finite-dimensional real linear map has nonzero determinant.
This is the algebraic input needed before assigning its local orientation degree. -/
theorem linearEquiv_det_ne_zero (n : ℕ)
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    LinearMap.det L.toLinearMap ≠ 0 := by
  intro hdet
  have hker : LinearMap.ker L.toLinearMap ≠ ⊥ := by
    rw [← LinearMap.det_eq_zero_iff_ker_ne_bot]
    exact hdet
  exact hker (by simp)

/-- The equivalence produced from a nonzero determinant has the original linear map
as its underlying function. This is the literal displacement identification used
when applying the local-degree theorem to `I - B`. -/
theorem equivOfDetNeZero_apply
    {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : LinearMap.det L ≠ 0) (x : EuclideanSpace ℝ (Fin n)) :
    L.equivOfDetNeZero hL x = L x := by
  rfl

/-- In dimension zero the determinant of every endomorphism is the empty determinant one.
This is the zero-dimensional normalization used by the local-degree statement. -/
theorem zero_dimensional_equiv_det_one
    {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hn : n = 0) : LinearMap.det L.toLinearMap = 1 := by
  subst n
  apply LinearMap.det_eq_one_of_finrank_eq_zero
  simp

/-- The local group is infinite cyclic, and every invertible linear map acts by its determinant
sign, independently of the generator. The zero-dimensional map is explicitly the identity.

The determinant is the determinant of the original real linear map on the original Euclidean
model. The integer cast of `SignType.sign` is `-1`, `0`, or `1`; invertibility excludes `0`.
The existence of a linear equivalence with `ℤ` asserts infinite cyclicity without assuming a
chosen generator. The scalar equality asserts the induced automorphism on all homology classes,
and the coefficient equality states independence of every possible generator coordinate.

Node: `topo.invertible_real_linear_local_degree_g9`.
Source: Hatcher, Algebraic Topology, ordinary relative singular-chain triple sequence p.118;
Example2.23 p.125 (written primitive singular-simplex and two-hemisphere singular-cycle proof);
§2.2 Degree p.134(a),(c),(d),(e); local-degree excision/relative diagram p.136; Orientations and
Homology p.233 (natural punctured-space connecting comparison and reflection action). Hatcher,
Vector Bundles and K-Theory, Version2.2 November2017, §1.2 pp.23–24 (written elementary
row-operation paths and the two determinant-sign components of GL(n,R)). Local
literature/hatcher-at.pdf and literature/hatcher-vbkt-2017.pdf. Bredon, Topology and Geometry
(1993), IV Theorem6.6 pp.185–186, Proposition6.10 p.187 and Proposition7.1 pp.190–191, supplies a
separately verified written alternative by natural hemisphere induction and elementary matrices;
it is not needed for the proof below. Franks1969 Lemma1.2 p.118 uses this normalization for I−g.

Complete natural-language proof:

1. Actual local group and natural connecting map
For n>0, R^n contracts by v↦(1−t)v. Its punctured space retracts onto S^(n−1) by v↦v/‖v‖, with
punctured homotopy ((1−t)+t/‖v‖)v. Apply the short exact ordinary singular chain sequence of the
pair and its homology exact sequence. In degrees n≥2 the vanishing positive homology of the
ambient contractible space makes the connecting map H_n(R^n,R^n\{0})→H_(n−1)(R^n\{0}) an
isomorphism. At n=1 its image is instead ker(H_0(R\{0})→H_0(R))=reduced H_0(R\{0}); the map to
H_0(R)=Z is augmentation. The sphere homology theorem therefore gives Z in both cases. Connecting
naturality follows on a relative cycle c from δ[c]=[∂c] and ∂(L#c)=L#∂c. The contractions prove
ambient homology vanishing by relative homotopy invariance at empty subspaces and the constant-map
factorization through a point, whose chains have alternating zero/identity differentials. These
are the exact natural local-group comparisons used by Hatcher p233.

2. Explicit determinant-component paths
Follow Hatcher VBKT pp23–24. Adding t times a scalar multiple of row j to distinct row i is left
multiplication by I+t a E_ij, invertible with inverse I−t a E_ij and determinant1. Gaussian
elimination can be performed using only such additions: if a pivot is zero, add a row having a
nonzero entry in that pivot column; nonsingularity of the remaining block guarantees such a row.
Eliminate entries below the pivot, then above, obtaining a diagonal matrix with nonzero diagonal
entries. Each operation gives a path inside GL(n,R). Interpolate each diagonal entry d to sign(d)
through (1−t)d+t sign(d), which never vanishes. If det L>0 there are an even number of negative
entries. Pair them: the diagonal −I on each corresponding two-dimensional plane is connected to I
by the rotation through angle (1−t)π on that plane, with all other coordinates fixed. Concatenate
these finitely many paths to obtain L_t from L to I. If det L<0, let R=diag(−1,1,…,1). The
positive case applied to RL, followed by multiplication on the left by R, gives a path from L to
R. Dimension1 uses positive scalar interpolation, or the negative coset; no plane rotation is
needed. These paths require no spectral or smooth manifold theorem.

3. Published primitive singular-simplex proof and reflection action
Every GL path in Step2 is a jointly continuous homotopy of (R^n,R^n\{0}), so relative homotopy
invariance makes L_* equal to identity or the coordinate reflection R_*. The identity acts as1 by
functoriality. For n=1, the natural connecting comparison in Step1 identifies H_1(R,R\{0}) with
the augmentation kernel in H_0(R\{0}); its generator is [positive component]−[negative component].
Reflection swaps the two components and therefore acts as−1. For n≥2 write k=n−1>0. The natural
connecting map followed by radial retraction is equivariant for coordinate reflection and
identifies its local action with its action on H_k(S^k). Follow the actual proof cited by Hatcher
p.134(e), Example2.23 p.125, rather than constructing cones on an arbitrary equatorial cycle.
First the identity singular simplex i_j:Delta^j→Delta^j represents a primitive generator of
H_j(Delta^j,boundary Delta^j), by induction on j. For j=0 this is the one-point H0 class. For j>0
let Lambda be all boundary faces except one face F. Delta^j strongly deformation retracts onto
Lambda, so H_*(Delta^j,Lambda)=0 by relative homotopy invariance. The triple connecting map
H_j(Delta^j,boundary Delta^j)→H_(j−1)(boundary Delta^j,Lambda) is an isomorphism. Precisely, the
triple chain sequence is 0→C_*(boundary
Delta^j)/C_*(Lambda)→C_*(Delta^j)/C_*(Lambda)→C_*(Delta^j)/C_*(boundary Delta^j)→0, exact
degreewise by the nested subgroup quotients; its differential is induced by singular boundary and
its connecting map is [c]↦[boundary c]. Use the named degreewise relative cokernel and generic
homology-sequence exactness here, not the pair short-exact lemma as a triple theorem. Inclusion of
the omitted face induces H_(j−1)(F,boundary F)→H_(j−1)(boundary Delta^j,Lambda), an isomorphism:
at j=1 it is the literal zero-chain relative identification; at j>1 both collapsed subspaces are
nonempty good subspaces and the inclusion induces a homeomorphism F/boundary F→boundary
Delta^j/Lambda, so the named good-pair quotient comparison gives the isomorphism. The triple
connecting map sends [i_j] to the alternating face sum, which modulo Lambda is ±[i_(j−1)]. Thus
the source's induction really proves primitivity in ordinary integral relative singular homology.
Next parameterize the two closed hemispheres of S^k by singular k-simplices sigma_+,sigma_- with
identical ordered boundary maps, taking sigma_-=R∘sigma_+; R fixes their common equator. Hatcher
explicitly regards z=sigma_+−sigma_- as a SINGULAR chain on p.125. Its boundary is zero. The
reduced pair sequence for the contractible lower hemisphere gives Htilde_k(S^k)→H_k(S^k,lower
hemisphere) an isomorphism. Inclusion of the upper hemisphere gives H_k(upper
hemisphere,equator)→H_k(S^k,lower hemisphere) an isomorphism, since both are nonempty good pairs
and their quotient spaces are homeomorphic. Under these literal maps [z] corresponds to [sigma_+],
the primitive relative simplex class just proved. Hence [z] is a primitive sphere generator.
Reflection interchanges sigma_+ and sigma_- and sends z exactly to −z, so its sphere action, and
consequently its local relative action by Step1 naturality, is multiplication by−1. This is the
printed p.125/p.134(e) proof and uses no unregistered simplicial-to-singular theorem, coned-z
extension, or compactification action comparison.

4. Zero dimension and normalization
When n=0, R^0 is a point, its punctured subspace is empty, and every linear endomorphism is the
unique map. Its determinant is the empty determinant1. The singular chain complex is Z in each
nonnegative degree, with differential zero in odd positive degree and identity in even positive
degree, so ordinary H_0=Z and the induced map is identity. For n>0 the two preceding steps
identify the action as sign(det L). Replacing a generator by its negative changes both source and
target coordinates together and leaves the integer unchanged. Put L=I−B for the final assertion;
the displacement is exactly this linear map.
-/
theorem invertible_real_linear_local_degree (n : ℕ)
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let X := TopCat.of (EuclideanSpace ℝ (Fin n))
    let A : Set X := {x | x ≠ 0}
    let P := singularSubspacePair X A
    let H := P.homology singularIntegralCoefficients n
    let f : X ⟶ X := TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv)
    let F := SSetPair.homologyMap
      (singularSubspacePairMap f A A
        (fun _x hx h ↦ hx (L.injective (h.trans L.map_zero.symm))))
      singularIntegralCoefficients n
    Nonempty (H ≃ₗ[ℤ] ℤ) ∧ Function.Bijective F.hom ∧
    (∀ c : H, F.hom c = (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) • c) ∧
    (∀ e : H ≃ₗ[ℤ] ℤ,
      e (F.hom (e.symm 1)) = (SignType.sign (LinearMap.det L.toLinearMap) : ℤ)) ∧
    (n = 0 → LinearMap.det L.toLinearMap = 1 ∧ ∀ c : H, F.hom c = c) := by
  dsimp only
  let H := (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
    {x | x ≠ 0}).homology singularIntegralCoefficients n
  let f := TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv)
  let F := SSetPair.homologyMap
    (singularSubspacePairMap f {x | x ≠ 0} {x | x ≠ 0}
      (fun x hx h ↦ hx (L.injective (h.trans L.map_zero.symm))))
    singularIntegralCoefficients n
  have ha := invertible_real_linear_local_homology_action n L
  dsimp only at ha
  change ∀ c : H, F.hom c = (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) • c at ha
  have hb : Function.Bijective F.hom := by
    have hh : ∀ x, L.toContinuousLinearEquiv.toHomeomorph x ≠ 0 ↔ x ≠ 0 := by
      intro x
      exact L.map_ne_zero_iff
    have hb := singular_subspace_homeomorph_homology_bijective
      (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
      L.toContinuousLinearEquiv.toHomeomorph {x | x ≠ 0} {x | x ≠ 0}
      hh singularIntegralCoefficients n
    exact hb
  refine ⟨⟨euclideanPositiveLocalCoordinate n⟩, hb, ha, ?_, ?_⟩
  · intro e
    let k : ℤ := SignType.sign (LinearMap.det L.toLinearMap)
    calc
      e (F.hom (e.symm 1)) = e (k • e.symm 1) := congrArg e (ha (e.symm 1))
      _ = k • e (e.symm 1) := map_zsmul e.toAddEquiv k (e.symm 1)
      _ = k := by simp
  · intro hn
    have hd := zero_dimensional_equiv_det_one L hn
    refine ⟨hd, ?_⟩
    intro c
    rw [ha, hd]
    simp [sign_pos (show (0 : ℝ) < 1 from zero_lt_one)]

/-- The local homological degree of the original displacement `v ↦ v − B v` is the sign of
`det (I − B)` whenever that linear displacement is invertible.

Source: Hatcher, local-degree diagram p. 136 and orientations p. 233; Franks (1969), Lemma 1.2,
p. 118. In finite real dimension nonzero determinant is exactly invertibility. Set
`L = (I − B).equivOfDetNeZero hB`; its underlying map is literally the original displacement.
Apply `invertible_real_linear_local_degree` to this `L`. It gives a genuine primitive integral
coordinate and computes the coefficient in every such coordinate as the determinant sign.
The point zero is the unique zero of this invertible displacement, so the same actual punctured
pair is its local-degree pair. This includes dimension zero, where the pair is point/empty and
the determinant and degree are both one. No fixed-point-index normalization is an input.
-/
theorem linear_displacement_local_degree (n : ℕ)
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hB : LinearMap.det (LinearMap.id - B) ≠ 0) :
    let L := (LinearMap.id - B).equivOfDetNeZero hB
    let X := TopCat.of (EuclideanSpace ℝ (Fin n))
    let A : Set X := {x | x ≠ 0}
    let H := (singularSubspacePair X A).homology singularIntegralCoefficients n
    let f : X ⟶ X := TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv)
    let F := SSetPair.homologyMap
      (singularSubspacePairMap f A A
        (fun _x hx h ↦ hx (L.injective (h.trans L.map_zero.symm))))
      singularIntegralCoefficients n
    ∀ e : H ≃ₗ[ℤ] ℤ,
      e (F.hom (e.symm 1)) = (SignType.sign (LinearMap.det (LinearMap.id - B)) : ℤ) := by
  dsimp only
  have h := invertible_real_linear_local_degree n
    ((LinearMap.id - B).equivOfDetNeZero hB)
  dsimp only at h
  exact h.2.2.2.1

end HolomorphicAnosov
