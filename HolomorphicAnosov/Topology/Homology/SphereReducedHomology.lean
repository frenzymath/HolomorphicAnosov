import HolomorphicAnosov.Topology.Homology.ModTwoPositiveUnitSphereProfile
import HolomorphicAnosov.Topology.Homology.ModTwoZeroSphereProfile
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.SphereScale
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedHomeomorphism

/-!
# Reduced homology of Euclidean spheres over the fixed modulus-two coefficient object

Source: Hatcher, *Algebraic Topology*, Corollary2.14 and Theorem2.13 printed p.114,
reduced augmentation pp.109–110, relative chains and exact sequence pp.115–118,
good-pair/excision comparison pp.119–124, and coefficient extension p.153.
The underlying sphere is the native EuclideanSpace L² sphere with its subtype topology.
All chain objects use exactly ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2)).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace HolomorphicAnosov

/-- Every positive-radius m-sphere has reduced modulus-two homology equal to the fixed coefficient
object in degree m and zero in every other natural degree, with comparison induced by radial scaling.

Source: Hatcher, *Algebraic Topology*, Corollary2.14 and Theorem2.13 p.114, augmentation
pp.109–110, homotopy invariance pp.112–113, relative/excision/good-pair proofs pp.115–124,
and p.153's explicit coefficient extension. Complete natural-language proof of
`topo.closed_manifold_mod2_sphere_profile`:

1. Throughout fix F=ZMod 2, C=ModuleCat.{0} F and the literal coefficient object R0=ModuleCat.of F
(ULift.{0} F). For a Type-0 space X let K_X=(TopCat.toSSet.obj (TopCat.of X)).chainComplex R0. Its
degree-n object is the direct sum of copies of R0 indexed by singular n-simplices. Define
epsilon_X:K_X,0→R0 as the coproduct map equal to id_R0 on every zero-simplex summand. The signed
boundary of any one-simplex is its endpoint-one inclusion minus its endpoint-zero inclusion, so
d_1 followed by epsilon_X is zero. Form A_X=ChainComplex.augment K_X epsilon_X: degree0 is R0,
degree(n+1) is K_X,n, d_1=epsilon_X, and the higher differentials are shifted singular
differentials. Reduced degree q≥0 means H_(q+1)(A_X). This constructs exactly the augmentation
stipulated in the statement. ModuleCat colimits, abelian and homology instances exist with this
fixed ring and universe. Every subsequent quotient, boundary, exact sequence and map keeps R0
unchanged. No integral homology premise or tensor exactness is used.

2. For a continuous f:X→Y, postcomposition sends each zero-simplex summand to the f-image summand,
so its degree-zero chain map k_f satisfies epsilon_Y∘k_f,0=epsilon_X. Its augmented map a_f has
component0=id_R0 and component(n+1)=k_f,n. The augmentation identity is its first chain square;
all remaining squares are those of k_f. On simplex generators identity and composition give
a_id=id and a_(g∘f)=a_g∘a_f. Their induced homology maps inherit these laws. A topological
homotopy gives the ordinary singular-chain homotopy from the recorded Mathlib prism. Extend its
components by zero on augmented degree0 and shift the other components by one. At degree0 both
endpoint maps are id_R0, so their difference is zero. At degree1 the term through the augmented
degree0 homotopy is zero, leaving the ordinary degree-zero prism equation; higher degrees give the
ordinary equation. Thus this is a homotopy of augmented maps, and Homotopy.homologyMap_eq proves
reduced homotopy invariance with R0.

3. A point has exactly one singular simplex in each degree, hence coefficient object R0 in every
ordinary degree. In positive degree n the boundary is sum_(j=0)^n(-1)^j id_R0: zero for odd n and
identity for even n>0. Its augmentation is identity. These maps make the augmented point complex
acyclic: at reduced degree0 the augmentation kernel is zero; at each positive odd degree the next
differential is identity; at each positive even degree the current differential is identity. For
S_0(1)⊂R^1 the norm is absolute value, so its two points are +1 and -1. Both singleton sets are
open by coordinate sign, and any singular simplex is constant at one point because its convex
nonempty domain is connected. Hence each ordinary chain object is R0⊕R0 with the same alternating
zero/identity differentials in each coordinate and augmentation (a,b)↦a+b. Its reduced degree-zero
kernel is {(a,-a):a∈R0}, and a↦(a,-a) with inverse first-coordinate projection gives an F-linear
isomorphism R0 to that kernel; d_1=0, so no quotient changes it. The same alternating calculation
gives zero in all positive degrees. In characteristic two -a=a but the positive even differentials
remain identity, not zero. This proves the complete S0 profile on the literal ULift coefficient;
no choice of an element of F replaces that coefficient object.

4. If a nonempty X contracts to a point x0, the contraction identifies the induced augmented
identity and constant maps on reduced homology by step2. The constant map factors through the
point; its induced map is zero since the point has zero reduced groups by step3. The identity map
on each reduced group is therefore zero, forcing every element to be zero. In particular
D^d={x∈R^d:||x||≤1} contracts by H(x,t)=(1-t)x. Its norm is (1-t)||x||≤1, its endpoints are
identity and zero, and it is continuous, so every reduced homology group of D^d is zero. This
conclusion is established directly over R0.

5. For an inclusion A⊆X, the map on singular simplices is injective; the chains supported in A
therefore form a direct-sum summand in each degree of K_X, with one copy of R0 on each A-simplex
and no coefficient flatness condition. Its quotient is the chain group C_n(X,A;R0) on all
remaining ambient simplices. The literal categorical degreewise cokernel agrees with this range
quotient by the two cokernel universal properties, via
mathlib.modulecat_range_quotient_is_cokernel_g10 and
mathlib.cokernel_cofork_map_iso_of_colimits_g8. Augment the A and X complexes; the inclusion in
augmented degree0 is id_R0, so the quotient has zero in degree0 and the relative chain group
C_n(X,A;R0) in degree(n+1). These objects form a degreewise short exact sequence of chain
complexes. The generic degreewise short exactness and homology-sequence leaves give the long exact
sequence. Its connecting map sends a relative cycle represented by c to [d c] in the augmented A
complex. At ordinary degree1 its target is reduced H0(A), since the boundary of a one-chain has
total coefficient zero. If A is nonempty, its augmentation is onto: the coefficient a on any
chosen zero-simplex gives sum a, without choosing a nonzero coefficient. Thus reduced H_(-1)(A)=0
and the tail is reduced H0(X)→H0(X,A;R0)→0.

6. Suppose A is nonempty and closed in X and V is a neighborhood strongly deforming onto A, and
write Q=X/A, *=q(A). For A⊆V⊆X, the degreewise chain sequence 0→C(V,A;R0)→C(X,A;R0)→C(X,V;R0)→0 is
short exact: it is the direct-sum decomposition by A-simplex, V-simplex outside A, and X-simplex
outside V indices. The homology sequence and relative deformation acyclicity imply
H_n(X,A;R0)→H_n(X,V;R0) is an isomorphism for every n≥0. The quotient deformation and
neighborhood-image homeomorphism give the analogous isomorphism H_n(Q,*;R0)→H_n(Q,q(V);R0).
Excision removes A from (X,V) and removes * from (Q,q(V)), since the removed sets are closed and
lie in the relevant interiors. The quotient complement homeomorphism identifies (X minus A,V minus
A) with (Q minus *,q(V) minus *). All arrows commute as literal inclusion/quotient chain maps; the
two triple isomorphisms, two excision isomorphisms and complement homeomorphism show that
q_*:H_n(X,A;R0)→H_n(Q,*;R0) itself is an isomorphism. Finally the augmented complex of the
singleton * is acyclic by step3; the augmented-pair sequence of (*⊆Q) identifies H_n(Q,*;R0) with
reduced H_n(Q;R0). These are the same maps and comparison used by Hatcher Proposition 2.22. Every
source input here applies to the fixed arbitrary coefficient object R0, not only integers. No
lifting of individual quotient simplices is asserted.

7. For d>0 take X=D^d and A=S^(d-1). The coordinate unit vector shows A nonempty, and A is closed
by continuity of norm. Its relatively open neighborhood V={x∈D^d:||x||>1/2} strongly retracts onto
A by H(x,t)=((1-t)+t/||x||)x. The norm is (1-t)||x||+t, lying in (1/2,1]; endpoints and the
fixed-A law follow directly, and the denominator is positive, so H is continuous. Identify Q=D^d/A
with S^d⊂R^d×R using F(x)=(sin(pi r)x/r,cos(pi r)) for r=||x||>0, and F(0)=(0,1). Norm one follows
from sin²+cos²=1; the boundary maps to the south pole, and the center to the north pole. At zero
the norm of the first component is |sin(pi r)|→0, establishing continuity there. For every sphere
point (z,t) except the south pole, cos(pi r)=t determines a unique r∈[0,1); when r>0 its unique
preimage is x=r z/sin(pi r), and when r=0 it is zero. The south-pole preimage is exactly A. Thus F
descends to a continuous bijection Q→S^d. D^d is compact by its Euclidean proper-space instance
and mathlib.isCompact_closedBall, its quotient is compact, and S^d is Hausdorff. The
compact-to-Hausdorff equivalence leaf gives the displayed homeomorphism. Reindex R^d×R as
EuclideanSpace Real (Fin(d+1)); the coordinate split is a linear isometry and fixes the Euclidean
sphere. This geometric argument includes d=1, but never uses d=0 or a nonexistent boundary S^(-1).

8. Apply steps5–7 at the disk pair with d>0. For every q≥1 the exact segment reduced
H_q(D^d;R0)→H_q(D^d,A;R0)→reduced H_(q-1)(A;R0)→reduced H_(q-1)(D^d;R0) has zero outside groups by
step4. Hence its actual connecting map is injective and surjective. Compose its source with the
inverse of the quotient-induced comparison and quotient-sphere homeomorphism to obtain an
isomorphism reduced H_q(S^d;R0)→reduced H_(q-1)(S^(d-1);R0). The degree-zero tail has outside
groups reduced H0(D^d;R0)=0 and reduced H_(-1)(A;R0)=0, so H0(D^d,A;R0)=0 and therefore reduced
H0(S^d;R0)=0. At d=q=1 the connecting map lands in the actual reduced H0(S0;R0), computed as the
augmentation kernel in step3, not in ordinary H0(S0)=R0⊕R0. The quotient comparison and disk
contraction precede the sphere profile, so this construction does not use a disk-boundary consumer
that depends back on the present node.

9. Induct on sphere dimension m, generalizing q. Step3 proves reduced H0(S0) isomorphic to R0 and
all positive degrees zero. At dimension m+1, the connecting isomorphism with q=m+1 identifies its
top group with reduced H_m(S^m), so compose with the induction isomorphism to obtain R0. If q
differs from m+1, its zero-degree case vanishes by step8. Otherwise q=p+1 and p differs from m;
the same connecting map identifies its group with reduced H_p(S^m), zero by induction. This covers
degrees above and below the sphere dimension, with no natural predecessor at zero. Isomorphisms
transport zero objects via the recorded IsZero/isomorphism leaf.

10. For r>0 define e:S_m(1)→S_m(r) by x↦r*x and e_inverse:y↦r^(-1)*y. mathlib.norm_smul gives
||r*x||=r and ||r^(-1)*y||=1, since r and r^(-1) are positive. The scalar identities give both
inverse equations, and constant scalar multiplication followed by the subtype lift is continuous
on each sphere, so these maps form the explicit homeomorphism in the statement. Its augmented maps
have component0=id_R0 and the genuine singular maps in all higher components. Step2 functoriality
therefore makes the induced maps inverse on the actual augmented homology groups, including
reduced degree0. Transport the top isomorphism and every off-top zero object along these maps. At
r=1 these are identity maps; from radius r to s>0 the same comparison is multiplication by s/r, so
its induced map is the composite of the displayed comparisons.

11. For m=0 and r>0 the actual sphere has two points ±r and reduced H0 is R0; for m>0 reduced H0
is zero. Every stated sphere is nonempty because the ambient dimension is m+1>=1. Radius0 is a
singleton and would have zero reduced homology, so its exclusion is essential; no empty-space or
negative-dimensional sphere convention is used. All chain computations are F-linear and use the
fixed ULift coefficient object; they never obtain mod-2 homology by tensoring the integral
homology result. The name of this node does not assert a manifold top class, orientability or a
homotopy equivalence of an arbitrary manifold to a sphere. Those are separate statements, and no
such premise has entered this proof.

The literal coproduct augmentation is fixed by the two `Sigma.desc` expressions. Its boundary-zero
witnesses are conclusions, not assumptions or data filled with `sorry`. The two augmented chain
complexes insert the same coefficient object at index0. Reduced degree q is their native homology
at q+1. The chain isomorphism in the conclusion has coefficient identity at index0 and the actual
singular chain map of the explicitly specified scaling homeomorphism at every higher index.
Consequently its image under HomologicalComplex.homologyFunctor is the induced reduced-homology
comparison, rather than an unrelated abstract isomorphism. Dimension m=0 is included; radius0 is
excluded. No alternative reduced-homology carrier or integral-to-modulus-two tensor argument is used.
-/
theorem closed_manifold_mod2_sphere_profile (m : ℕ) (r : ℝ) (hr : 0 < r) :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let S1 := {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1}
    let Sr := {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = r}
    let L1 := TopCat.toSSet.obj (TopCat.of S1)
    let Lr := TopCat.toSSet.obj (TopCat.of Sr)
    let K1 := L1.chainComplex R0
    let Kr := Lr.chainComplex R0
    let ε1 : K1.X 0 ⟶ R0 := Sigma.desc (fun _ : L1 _⦋0⦌ ↦ 𝟙 R0)
    let εr : Kr.X 0 ⟶ R0 := Sigma.desc (fun _ : Lr _⦋0⦌ ↦ 𝟙 R0)
    ∃ (w1 : K1.d 1 0 ≫ ε1 = 0) (wr : Kr.d 1 0 ≫ εr = 0),
      let A1 := ChainComplex.augment K1 ε1 w1
      let Ar := ChainComplex.augment Kr εr wr
      Nonempty ((HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2))
        (ComplexShape.down ℕ) (m + 1)).obj Ar ≅ R0) ∧
      (∀ q : ℕ, q ≠ m → IsZero
        ((HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2))
          (ComplexShape.down ℕ) (q + 1)).obj Ar)) ∧
      ∃ e : S1 ≃ₜ Sr,
        (∀ x, (e x).val = r • x.val) ∧
        (∀ y, (e.symm y).val = r⁻¹ • y.val) ∧
        ∃ a : A1 ≅ Ar,
          a.hom.f 0 = 𝟙 R0 ∧
          ∀ q : ℕ, a.hom.f (q + 1) =
            (SSet.chainComplexMap (TopCat.toSSet.map
              (TopCat.ofHom ⟨e, e.continuous_toFun⟩)) R0).f q := by
  dsimp only
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let S1 := {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = 1}
  let Sr := {x : EuclideanSpace ℝ (Fin (m + 1)) // ‖x‖ = r}
  let e : S1 ≃ₜ Sr := Topology.Homology.sphereScale r hr
  obtain ⟨w1, wr, a, ha0, has⟩ := modTwoAugmentedHomeomorphism (TopCat.of S1) (TopCat.of Sr) e
  refine ⟨w1, wr, ?_, ?_, e, (fun _ ↦ rfl), (fun _ ↦ rfl), a, ha0, has⟩
  · have hunit : Nonempty ((ChainComplex.augment
        ((TopCat.toSSet.obj (TopCat.of S1)).chainComplex R0)
        (Sigma.desc (fun _ ↦ 𝟙 R0)) w1).homology (m + 1) ≅ R0) := by
      cases m with
      | zero => exact (modTwoZeroSphereProfile w1).1
      | succ k => exact (modTwoPositiveUnitSphereProfile k w1).1
    obtain ⟨h⟩ := hunit
    exact ⟨((HomologicalComplex.homologyFunctor (ModuleCat (ZMod 2))
      (ComplexShape.down ℕ) (m + 1)).mapIso a).symm ≪≫ h⟩
  · intro q hq
    have hunit : IsZero ((ChainComplex.augment
        ((TopCat.toSSet.obj (TopCat.of S1)).chainComplex R0)
        (Sigma.desc (fun _ ↦ 𝟙 R0)) w1).homology (q + 1)) := by
      cases m with
      | zero =>
        cases q with
        | zero => exact (hq rfl).elim
        | succ n => exact (modTwoZeroSphereProfile w1).2 n
      | succ k => exact (modTwoPositiveUnitSphereProfile k w1).2 q hq
    exact IsZero.of_iso hunit ((HomologicalComplex.homologyFunctor (ModuleCat (ZMod 2))
      (ComplexShape.down ℕ) (q + 1)).mapIso a).symm

end HolomorphicAnosov
