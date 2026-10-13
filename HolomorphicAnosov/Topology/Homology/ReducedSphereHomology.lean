import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible

import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AugmentedIntegralSingularChainsHomotopy
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.IntegralReducedSingularHomologyMap_homotopy
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.IntegralReducedHomologyIsoOfHomotopyEquiv
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.SphereScale
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ReducedHomologyHomeomorphIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.SphereScale_profile
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ConnectingIsoOfZeroNeighbors
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroOfSurjectiveFromZero
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.GoodPair_shift_of_acyclic
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.SphereProfile_induction
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.RadialCollar_norm
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundaryCollarRetract
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundary_goodPair_guards
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundary_nonempty
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundarySphereHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_finite
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_discrete
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.IntegralReducedPositiveOrdinaryIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_positive
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Disconnected_first_boundary_zero
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Disconnected_reducedH0Kernel
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiscreteZeroChainsIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiscreteZeroChainsIso_augmentation
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiscreteReducedH0SumKernel
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.BoolCoproductIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.BoolCoproductIso_sum
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.SumPairKernelIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.BoolSumKernelIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphereBoolHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphere_degreeZeroIso
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclidean
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclidean_norm_sq
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap_norm
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclideanLinear
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap_continuous
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap_fiber
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Unique_reduced_zero
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Disk_reduced_zero
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap_surjective
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.DiskBoundaryCollapseSphereHomeomorph
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.UnitSphere_successor
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.UnitSphere_profile

/-!
# Reduced integral homology of Euclidean spheres

Source: Hatcher, *Algebraic Topology*, Corollary 2.14 and Theorem 2.13, printed p.114;
Propositions 2.6–2.8 pp.109–110, augmented singular homology and homotopy invariance
pp.110–113, and the disk-boundary quotient Example 0.3 p.6.
DAG node: `topo.reduced_sphere_homology`.

The ambient space is the genuine Euclidean L² space `EuclideanSpace ℝ (Fin (k+1))`.
Both sphere types have their native subspace topologies. The coefficient and reduced homology
objects are exactly the existing integral augmented singular-chain construction, including its
index shift: mathematical reduced degree q is augmented chain index q+1.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The unit k-sphere has reduced integral homology the integer coefficient module in degree k
and zero in every other nonnegative degree. Every positive-radius sphere has the same profile,
and the comparison is the reduced homology map of the literal radial scaling homeomorphism.
No negative-dimensional or zero-radius sphere is included. The case k=0 is the two-point sphere,
whose reduced degree-zero group is one copy of the integers, not two copies.

Source: Hatcher, Corollary 2.14 and Theorem 2.13 p.114; Propositions 2.6–2.8 pp.109–110;
homotopy invariance and the reduced extension pp.110–113; Example 0.3 p.6.

Natural-language proof:

1. Let k be a nonnegative integer and S^k={x∈ℝ^{k+1}:‖x‖=1}, with Euclidean norm and its subspace
topology. Throughout, H̃_n means the augmented integral singular homology in the stated
definition. A homeomorphism induces a reduced homology isomorphism: the chain maps of it and its
inverse have identity composites on all generators and on the added ℤ, so the identity and
composition laws on homology give two-sided inverses. No basepoint or coefficient change is used.

2. For k=0, ‖x‖=|x| in ℝ, so S^0 consists exactly of +1 and −1. These two singleton subsets are
open in S^0, so it is the discrete two-point space. Every simplex has path-connected domain and
hence maps to exactly one of the two points. Thus C_n(S^0)=ℤ⊕ℤ in every n. For n>0 its
differential is zero when n is odd and identity when n is even: each generator has n+1 faces at
the same point and the alternating sum is zero or one. The augmentation in degree zero is
(a,b)↦a+b. In reduced degree zero, ∂_1=0 and ker ε={(a,−a):a∈ℤ}≃ℤ. In positive degrees, at odd n
the following differential is identity, while at even n the current differential is identity, so
every reduced homology group is zero. This gives both conclusions for S^0 directly from the actual
chains. Swapping the two point labels changes the chosen isomorphism to ℤ by a sign but not its
existence; no one-point base is mistaken for S^0.

3. For each m>0, put D^m={x∈ℝ^m:‖x‖≤1} and A=∂D^m={x:‖x‖=1}. The coordinate unit vector shows A≠∅,
and continuity of norm shows A is closed. The relatively open neighborhood V={x∈D^m:1/2<‖x‖}
strongly deformation retracts to A by H(t,x)=((1−t)+t/‖x‖)x, 0≤t≤1. Its norm is (1−t)‖x‖+t,
between ‖x‖>1/2 and 1, so every stage lies in V. At t=0 it is x, at t=1 it lies in A, and it fixes
each point of A. Continuity follows from the positive denominator, scalar multiplication and norm
continuity. Consequently this is a good pair satisfying the precise hypotheses of the cited
reduced exact sequence.

4. Write Q=D^m/A. A concrete homeomorphism Q→S^m⊂ℝ^m×ℝ is induced by F(x)=(sin(πr)x/r,cos(πr)) for
r=‖x‖>0 and F(0)=(0,1). Its norm is one by sin²+cos²=1. At r=1 it is the constant south pole
(0,−1); at r=0 it is the north pole. The first component has norm |sin(πr)|→0 at the center, so F
is continuous there, and away from the center continuity is by the formula. Hence it factors
continuously through the boundary collapse. Every sphere point (z,t) other than the south pole has
a unique r∈[0,1) with cos(πr)=t; for r>0 its preimage is x=r z/sin(πr), and for r=0 the sphere
equation gives z=0. The south pole has precisely the boundary as preimage. Therefore the descended
map is bijective. The closed disk is compact in finite-dimensional Euclidean space, so its
quotient is compact; S^m is Hausdorff as a Euclidean subspace. The compact-to-Hausdorff
continuous-equivalence provider makes this bijection a homeomorphism. This proof includes m=1; it
never uses D^0/∂D^0 as a two-point sphere.

Reindex the orthogonal Euclidean product ℝ^m × ℝ by Fin(m+1): retain the first m coordinates
and use the last coordinate for the final real factor. The sum-of-squares norm identity makes
this coordinate bijection a linear isometry with its evident inverse, hence it restricts to
the exact native EuclideanSpace sphere occurring in the formal statement.

5. Every reduced homology group of D^m vanishes. The homotopy (t,x)↦(1−t)x stays in the disk and
goes from its identity to the constant map at zero. The actual topological-to-singular homotopy
and singular-chain prism providers give a chain homotopy between the induced maps; extend the
prism by zero on the added degree −1 group. The chain-homotopy identity at degree zero is the
ordinary prism identity, and at degree −1 both endpoint chain maps are id_ℤ, so their difference
is zero. It therefore induces equality on reduced homology by the homotopy-map theorem. The
constant map factors through a point. The reduced complex of a point has augmentation id_ℤ and
positive boundaries alternating zero and identity, hence is acyclic in every degree. Thus the
constant map is zero on reduced homology; the homotopy and identity-map law give id_{H̃_n(D^m)}=0.
Every element then equals zero. This proves the actual vanishing needed by the exact sequence,
rather than inserting contractibility as an extra homology assumption.

6. Apply the good-pair exact sequence to (D^m,A) and transport Q to S^m by step 4. For every n≥1
its segment 0=H̃_n(D^m)→H̃_n(S^m)→H̃_{n−1}(S^{m−1})→H̃_{n−1}(D^m)=0 makes the connecting map an
isomorphism: exactness gives zero kernel and full image. Its degree-zero tail is
0=H̃_0(D^m)→H̃_0(S^m)→0, so H̃_0(S^m)=0. The latter tail relies on A≠∅; its augmentation is onto
since a point has coefficient sum one. It is not an application of the positive-degree shift with
n=0, and no natural-number predecessor or negative-degree sphere appears.

7. Induct on k, generalizing the degree n. For the top group, the k=0 calculation gives
H̃_0(S^0)≃ℤ. At k+1, the connecting isomorphism with n=k+1 identifies H̃_{k+1}(S^{k+1}) with
H̃_k(S^k), so composition with the induction isomorphism gives ℤ. For an off-top degree n≠k+1 in
the successor case, n=0 vanishes by step 6. If n=q+1>0, then q≠k, and step 6 identifies
H̃_n(S^{k+1}) with H̃_q(S^k), which vanishes by the induction hypothesis. At k=0, every off-top
degree is positive and step 2 gives vanishing. These cases prove the profile for every nonnegative
degree, including degrees larger than the sphere dimension.

8. For R>0 in the same ambient ℝ^{k+1}, scalar multiplication x↦Rx sends the unit sphere to the
radius-R sphere, since ‖Rx‖=R‖x‖. Its inverse y↦R^{-1}y is well-defined because R≠0 and has unit
norm. Both maps are continuous on their subspaces and the composites are identity by
multiplication of scalars. They are therefore a homeomorphism; step 1 transports the complete
reduced homology profile through its induced inverse maps. This includes k=0, where the radius-R
sphere is {−R,+R}. R=0 is excluded: its sphere is a singleton with zero reduced homology. The
empty sphere in ambient ℝ^0 with positive radius is also outside the statement, since k≥0 makes
the ambient dimension k+1≥1.

The formal coefficient object is `reducedSingularIntegralCoefficients`, namely the actual integer
module on ULift ℤ; universe lifting does not change its integral coefficients. `IsZero` is the
zero-module assertion and a categorical isomorphism is an actual integer-linear isomorphism.
The exported comparison has hom and inv equal to the induced reduced singular homology maps of
the specified scaling homeomorphism and its inverse. Therefore the radius transport uses the
original singular map and augmentation identity, with no tensoring or unrelated chosen group.
-/
theorem reduced_sphere_homology (k : ℕ) :
    let S1 := {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ = 1}
    Nonempty (integralReducedSingularHomology (TopCat.of S1) k ≅
      reducedSingularIntegralCoefficients) ∧
    (∀ q : ℕ, q ≠ k → IsZero (integralReducedSingularHomology (TopCat.of S1) q)) ∧
    ∀ (r : ℝ), 0 < r →
      let Sr := {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ = r}
      Nonempty (integralReducedSingularHomology (TopCat.of Sr) k ≅
        reducedSingularIntegralCoefficients) ∧
      (∀ q : ℕ, q ≠ k → IsZero (integralReducedSingularHomology (TopCat.of Sr) q)) ∧
      ∃ e : S1 ≃ₜ Sr,
        (∀ x : S1, (e x).val = r • x.val) ∧
        (∀ y : Sr, (e.symm y).val = r⁻¹ • y.val) ∧
        ∀ q : ℕ, ∃ ι : integralReducedSingularHomology (TopCat.of S1) q ≅
            integralReducedSingularHomology (TopCat.of Sr) q,
          ι.hom = integralReducedSingularHomologyMap
            (TopCat.ofHom ⟨e, e.continuous⟩) q ∧
          ι.inv = integralReducedSingularHomologyMap
            (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) q := by
  obtain ⟨htop, hoff⟩ := unitSphere_profile k
  exact ⟨htop, hoff, fun r hr ↦ sphereScale_profile k htop hoff r hr⟩










































end HolomorphicAnosov.Topology.Homology
