import HolomorphicAnosov.Topology.Homology.EmptySingularChainComplex
import HolomorphicAnosov.Topology.DoldGradedTraceContraction
import HolomorphicAnosov.Topology.FiniteFixedPointIndexSum
import HolomorphicAnosov.Topology.FunctorialTraceConjugacy
import HolomorphicAnosov.Topology.ENRSectionImageModel
import HolomorphicAnosov.Topology.Cubical.SkeletonHomologyNeighborhoods
import HolomorphicAnosov.Topology.ENRRetractionRepresentation
import HolomorphicAnosov.Topology.EuclideanFixedPointIndex
import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition
import HolomorphicAnosov.Topology.Homology.RationalRelativeKunneth
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.ENRLocalFixedPointIndexConjugacy
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Trace
import HolomorphicAnosov.Topology.TraceSubsingleton
import HolomorphicAnosov.Topology.DoldCompactENRGeometricTrace

/-!
# The compact ENR Lefschetz number as the sum of isolated local indices

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood retracts*,
Topology 4 (1965), (1.1)–(1.5) pp.1–2, (2.1),(2.3) p.3, (3.2)–(3.4) pp.4–5,
Theorem (4.1) and its written proof pp.5–6, Lemma (4.2) and §5 pp.6–8.
DAG node: `topo.compact_enr_lefschetz_local_index_sum_g7`.

The ordinary rational singular homology functor and its linear endomorphism are the actual
Mathlib constructions. The integer on each finite isolating domain is the standard-positive
homological displacement index, through the given ENR retraction. No index function,
orientation coordinate, derivative, or additional isolating-neighborhood hypothesis is supplied.
-/

noncomputable section

open CategoryTheory TopologicalSpace TensorProduct
open scoped TensorProduct

namespace HolomorphicAnosov.FixedPointIndexInterface

universe u

/-- The exact ordinary rational Lefschetz formula for a compact metrizable ENR.

Source: Dold (4.1), p.5, written proof pp.5–6 and support-operator Lemma (4.2)
with its six written reductions in §5 pp.6–8; finite local decomposition is (1.5)
and retraction is (2.3). Rational coefficient transport is Hatcher §3.A pp.261–266.

Complete natural-language proof:

1. Use the supplied ENR and literal displacement index
Since r∘s=id_X, s is a homeomorphism from X onto its compact image C=s(X)⊆V, with inverse r|C. Set g=s∘f∘r:V→V; its image lies in C, and g|C is conjugate to f. If g(v)=v, then v=s(r(v)) and r(v) is fixed by f; conversely g(s(x))=s(x) when f(x)=x. Thus Fix(g)=s(K). By Dold (2.3), the ENR index is exactly the Euclidean index of g. Write o_C for the positively oriented integral support class in H_N(V,V\C;Z) from (1.1). Since Fix(g)⊆C, (1.3) says (id−g)_*(o_C)=I(g,V) in H_N(R^N,R^N\{0};Z)=Z. The support restriction sends o_C to o_Fix(g), so this uses precisely the current id−g index, with no dimension-dependent sign change. Passing to rational coefficients makes this equation its integer cast in Q.

2. Explicit source-supported rational coefficient change and concentration
Hatcher §3.A p.261 identifies C_j(A,B;G) with C_j(A,B;Z)⊗_Z G for every pair: the relative integral group is free on the singular j-simplices not contained in B, and σ⊗a maps to aσ. Its boundary is ∂⊗id and this identification commutes with postcomposition, since each simplex and each alternating face has the same coefficient. The named singular-subspace adapter supplies precisely these integral quotient chains. Take G=Q. Q is the fraction localization of Z and is flat by mathlib.localization_flat; scalar extension preserves finite limits by the named flat-extension theorem and finite colimits by its scalar-extension adjunction. Additivity and preservation of zero follow directly from (u+v)⊗q=u⊗q+v⊗q. Thus it is an exact functor, and the named homology-comparison theorem applies degreewise. Concretely, if Z_j=ker ∂ and B_j=im ∂, exactness preserves 0→Z_j→C_j→B_(j−1)→0 and 0→B_j→Z_j→H_j→0. Hence rational cycles and boundaries are Z_j⊗Q and B_j⊗Q, and their quotient is naturally H_j(A,B;Z)⊗Q. This is exactly the rational case of the written Hatcher universal-coefficient argument pp.261–264, Corollary 3A.4 p.264 and Corollary 3A.6(a) p.266; no finite-generation assumption is needed. The same calculation applies to the augmented free complex for reduced homology, including its degree-zero augmentation kernel. Therefore the integral reduced-sphere concentration becomes the identical rational concentration. For m>0, contracting R^m and radially retracting R^m\{0} onto S^(m−1), the pair-chain short exact sequence and its named exact homology sequence give H_j(R^m,R^m\{0};Z)=0 for j≠m and Z for j=m; when m=1 the degree-zero map is the augmentation Z⊕Z→Z, whose kernel is Z. Rationalization gives Q in degree m and zero elsewhere. For m=0 the pair is (point,empty), so ordinary H_0 is Q and higher groups vanish directly. The rational generator is exactly ω_m,Z⊗1, and any equation d_*(o)=aω_m,Z becomes d_*(o_Q)=(a cast to Q)ω_m,Q by the natural coefficient map. This explicitly justifies every rational sphere/local-target group and the index cast used below.

3. The source signed trace convention
For the finite graded rational vector space M=H_*(C;Q), put M*_i=Hom_Q(M_(−i),Q). Dold (3.2) defines θ(φ⊗z)(m)=(−1)^(|m||z|)φ(m)z and (3.4) defines e(φ⊗z)=φ(z). On a homogeneous basis b_(k,j) of M_k, θ^−1(T)=Σ_(k,j)(−1)^k b*_(k,j)⊗T(b_(k,j)) for any degree-zero endomorphism T: the only nonzero evaluation has |m|=|z|=k and k²≡k mod2. Applying e gives Σ_k(−1)^k tr(T|M_k). All sums are finite by the exact finite-dimensional/high-degree-zero hypotheses of the statement. Thus Dold’s trace equals the required ordinary rational alternating trace, including unreduced H_0.

4. Define the diagonal-difference operator of Lemma 4.2
For any compact A⊆O with O open in R^N, let o_A now denote the rational image of the integral support class. For k∈H_q(A;Q), define Φ(A,O)(k) by o_A×k, then the relative diagonal Δ(v)=(v,v) on the O factor, then transposition of the middle O and A factors, then the difference d(v,a)=v−a on the first relative-O and A factors, and finally inverse product with the positive generator ω_N∈H_N(R^N,R^N\{0};Q). The difference is a pair map because v∉A implies v≠a for every a∈A. The named relative product theorem supplies the natural tensor identifications and inverse ω_N×−. This is the exact operator in (4.2), not an index defined by a trace. Functoriality of product maps, naturality of the support class under enlarging domains or restricting supports, and inclusion composition give Φ(A,O′)=i_(O,O′)Φ(A,O) and Φ(A′,O)=Φ(A,O)i_(A′,A) whenever A′⊆A⊆O⊆O′. These are (5.1),(5.1′).

5. Dold §5 Steps 1–2: point and degree zero
If A={p}, restrict to a small convex ball O_0 about p. The homotopy (v,t)↦(v,(1−t)p+tv) of its relative diagonal preserves the first relative factor, so Δ_*(o_p)=o_p⊗[p]. The difference v−p preserves the positive local generator, and Φ sends [p] to the same point class. Domain naturality restores O. Every ordinary singular H_0 class is a finite linear combination of point classes, since zero-chains are finite sums of singular vertices. Support naturality from {p}⊆A therefore proves Φ_0(A,O)=i_* for arbitrary compact A, without assuming it is connected. This fills the point calculation left to the reader and spells out source Step 2; it does not use reduced H_0.

6. Dold §5 Step 3: sphere collar and the exact signs
Use the rational sphere and Euclidean relative concentration obtained in D1Q from the integral providers by exact coefficient change. For 1≤q<N let A=S^q×{0} in O=S^q×B^(N−q), with a flattened orthogonal local tangent/normal patch as in the source. Choose generators σ∈H_q(S^q;Q) and ν∈H_(N−q)(B,B\{0};Q) with σ×ν=o_A. The sphere diagonal is σ×1+1×σ, and the ball relative diagonal is ν×1. Thus Δ_*(o_A)=o_A×1+(−1)^(q(N−q))(1×ν)×(σ×1). After multiplying by σ, the first term has difference image in H_(N+q)(R^N,R^N\{0};Q)=0. For the second, the middle-factor transposition contributes (−1)^(q²). Excision to the flattened patch identifies the difference on normal and tangent coordinates with identity on the N−q normal coordinates and −identity on q tangent coordinates, contributing (−1)^q; putting normal before tangent contributes (−1)^(q(N−q)). The total exponent is 2q(N−q)+q²+q, which is even. Consequently Φ(σ×1)=σ×1 with positive sign, exactly the calculation (5.6) pp.7–8. Other nonzero degrees are degree zero, already handled, so Φ equals inclusion on the collar.

7. Dold §5 Steps 4–5: cubical skeleton and its subcomplex
Fix a finite rectilinear subdivision of a full cube C_0. For q>0 let A=C_0^q. The named cubical foundation states that H_q(A;Q) is generated by oriented boundaries S of (q+1)-cells. Each S has its prescribed sphere collar inside any open O containing A; D5 and domain naturality give Φ(S,O)=i_*. Support naturality gives (Φ(A,O)−i_*)i_(S,A)=0; generation makes Φ(A,O)=i_*. If q=N the group is zero; q=0 was D4. For a subcomplex D⊆C_0^q choose the named nested neighborhoods U,W with U deformation retracting onto C_0^q and W⊆O∩U deformation retracting onto D. The injectivity H_q(D)→H_q(C_0^q) implies H_q(W)→H_q(U) is injective, through these retractions and their inclusion square. Support naturality from the full skeleton gives Φ(D,U)=i_*. Domain naturality then gives i_(W,U)(Φ(D,W)−i_*)=0, so injectivity gives Φ(D,W)=i_*, and enlarging W to O proves the assertion for D. These are exactly source (5.2)–(5.5) and Steps 4–5, using the named one-level complete finite-cubical provider, whose lower singular-homology/Mathlib obligations remain separate.

8. Dold §5 Step 6: arbitrary compact support
Given compact A⊆O⊆R^N, choose a full cube containing A in its interior. Compactness and openness give δ>0 such that the δ-neighborhood of A lies in O. Subdivide the cube finitely into cells of diameter <δ and let P be the union of all closed cells meeting A, with all their faces. Then P is a finite cubical subcomplex and A⊆P⊆O. For q>N, H_q(P;Q)=0 by the named cubical foundation. For 0≤q≤N its q-skeleton P^q lies in the q-skeleton of the full cube; D6 gives Φ(P^q,O)=i_*. Naturality makes (Φ(P,O)−i_*) vanish on the image H_q(P^q)→H_q(P). That map is surjective by the named cubical foundation, so Φ(P,O)=i_* in every degree. Restricting support from P to A by (5.1′) proves Φ(A,O)=i_*. This is the written Step 6; the grid and union are finite, and no homological finite-type assumption on O or arbitrary compact A is made.

9. Dold (4.3): evaluation gives the displacement index
Return to A=C=s(X), O=V. Define D:H_*(V,V\C;Q)→M* by D(v)(k)=the ω_N coefficient of d_*(v×k), where d(v,c)=v−c. Put a_g=(D⊗g_*)Δ_*(o_C)∈M*⊗M, viewing g as a map V→C. The rational product theorem makes these literal natural homology maps; the tensor a_g is a finite sum. The composite e(D⊗g_*)Δ_* is the map induced by v↦v−g(v), because the relative diagonal first sends v to (v,v) and the second factor is then sent to g(v) before taking the difference. Therefore e(a_g)=(I(g,V) cast to Q), by D1. This is the first commuting diagram on p.6 and identity (4.3).

10. Dold (4.4): its associated endomorphism is g on the compact retract
For k∈M_q write Δ_*(o_C)=Σv_a⊗w_b with a+b=N, using the rational product theorem. In Φ(C,V)(k), only terms with a+q=N survive the relative Euclidean target, hence b=q. Swapping w_b and k contributes (−1)^(bq)=(−1)^(q²), so Φ(C,V)(k)=Σ_(b=q)(−1)^(q²)D(v_a)(k)w_b. Applying g_* gives exactly θ(a_g)(k) by Dold’s θ convention in D2. Lemma 4.2, proved through D3–D7, says Φ(C,V)=inclusion; hence θ(a_g)=g_*∘i_*=(g|C)_*. The second diagram on p.6 is precisely this equality, including the Koszul sign. D2 and D8 now give (I(g,V) cast to Q)=Σ_k(−1)^k tr((g|C)_*|H_k(C;Q)). The homology maps of s:X→C and its inverse conjugate (g|C)_* to f_*, so their finite traces agree. This is Dold (4.1) with its compact containing set equal to the whole ENR X; there is no Leray quotient or assertion that H_*(V) is finite type.

11. Finite isolated localization and boundary cases
A finite subset of the Hausdorff space X is discrete. Choose disjoint open neighborhoods O_x of its finitely many fixed points x; their union contains K and each has only that fixed point. By the fixed-set calculation in D1, the retracted local maps on r^−1(O_x) have exactly the single fixed point s(x); they are disjoint open domains in V. Dold (1.3),(1.5) and (2.3), or their current named G9 formulations, identify I(g,V)=Σ_x i_X(f,x). Apply the ring homomorphism Z→Q to this finite sum and combine with D9. Empty K gives index0 directly from the zero supported relative group. If X is empty, its homology and the sum are zero. If N=0 and X is nonempty, r∘s=id forces X to be a singleton; the constant/point index is1 and ordinary H_0 is Q, so both sides equal1, bypassing the positive-dimensional compactification/collar argument. All integral fundamental classes and the target generator use the same orientation before rationalization; arbitrary ENR representation changes do not reverse the index by the named representation-independence result.

The displayed local-domain data removes exactly the other fixed points. The marked fixed
point belongs to that domain; every fixed point there equals it. Its fixed set is therefore
a singleton (or empty for an unmarked point) and the displayed finite-set compactness proof
certifies the input to the existing ENR index. Excision identifies these canonical local
indices with the disjoint neighborhoods in step D10. Finite-dimensionality is assumed for
all ordinary rational H_k, and the stated vanishing above d discards every later trace term.
No conclusion about a different homology theory or a different index definition is used.
-/
theorem compact_enr_lefschetz_local_index_sum
    (X : Type u) [TopologicalSpace X] [MetrizableSpace X] [CompactSpace X]
    (e : ENRRepresentation X) (f : C(X, X)) (d : ℕ)
    (hfinite : {x : X | f x = x}.Finite) :
    let H : ℕ → TopCat.{u} ⥤ ModuleCat.{u} ℚ := fun k ↦
      (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj
        (ModuleCat.of ℚ (ULift.{u} ℚ))
    ∀ hH : ∀ k, FiniteDimensional ℚ ((H k).obj (TopCat.of X) : Type u),
      (∀ k, d < k → Subsingleton ((H k).obj (TopCat.of X) : Type u)) →
      (∑ k ∈ Finset.range (d + 1),
        letI := hH k
        (-1 : ℚ) ^ k * LinearMap.trace ℚ ((H k).obj (TopCat.of X) : Type u)
          ((H k).map (TopCat.ofHom f)).hom) =
      ∑ x ∈ hfinite.toFinset, (finiteFixedPointLocalIndex e f hfinite x : ℚ) := by
  dsimp only
  intro hH hvanish
  classical
  -- The empty-space case needs no index or diagonal-difference comparison:
  -- there are no singular generators, hence all homology and both sums vanish.
  by_cases hX : IsEmpty X
  · let := hX
    have hzchain : CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℚ)).obj
          (ModuleCat.of ℚ (ULift.{u} ℚ))).obj (TopCat.of X)) :=
      HolomorphicAnosov.singular_chain_isZero_of_isEmpty
        (TopCat.of X) (ModuleCat.of ℚ (ULift.{u} ℚ))
    have hzero (k : ℕ) : Subsingleton
        ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj
          (ModuleCat.of ℚ (ULift.{u} ℚ))).obj (TopCat.of X)) : Type u) :=
      ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℚ)
          (ComplexShape.down ℕ) k).map_isZero hzchain)
    have hf : hfinite.toFinset = ∅ := Finset.eq_empty_of_isEmpty _
    rw [hf, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro k hk
    let := hH k
    rw [linearMap_trace_eq_zero_of_subsingleton (hzero k), mul_zero]
  have hlocal := enr_local_fixed_point_index_eq_target_sum e f hfinite
  have hlocalQ := congrArg (fun n : ℤ ↦ (n : ℚ)) hlocal
  simp only [Int.cast_sum] at hlocalQ
  rw [← hlocalQ]
  -- Transport ordinary homology to the actual compact section image. The lift
  -- only puts this Euclidean subspace in the same universe as X.
  let Y := ULift.{u} e.sectionImage
  let E : X ≃ₜ Y := e.sectionImageHomeomorph.trans Homeomorph.ulift.symm
  let g : C(Y, Y) :=
    (⟨E, E.continuous⟩ : C(X, Y)).comp
      (f.comp ⟨E.symm, E.symm.continuous⟩)
  let H : ℕ → TopCat.{u} ⥤ ModuleCat.{u} ℚ := fun k ↦
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj
      (ModuleCat.of ℚ (ULift.{u} ℚ))
  let I : TopCat.of X ≅ TopCat.of Y := TopCat.isoOfHomeo E
  have hHY : ∀ k, FiniteDimensional ℚ ((H k).obj (TopCat.of Y) : Type u) := by
    intro k
    have := hH k
    let T := ((H k).mapIso I).toLinearEquiv
    exact FiniteDimensional.of_injective T.symm.toLinearMap T.symm.injective
  have hvanishY : ∀ k, d < k →
      Subsingleton ((H k).obj (TopCat.of Y) : Type u) := by
    intro k hk
    have := hvanish k hk
    exact ((H k).mapIso I).toLinearEquiv.symm.injective.subsingleton
  have hconj : TopCat.ofHom f ≫ (TopCat.isoOfHomeo E).hom =
      (TopCat.isoOfHomeo E).hom ≫ TopCat.ofHom g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change E (f x) = E (f (E.symm (E x)))
    rw [E.symm_apply_apply]
  have htrace := functor_alternating_trace_eq_of_conjugacy H
    (TopCat.isoOfHomeo E) (TopCat.ofHom f) (TopCat.ofHom g) hconj
    (Finset.range (d + 1))
  change (∑ k ∈ Finset.range (d + 1),
    (-1 : ℚ) ^ k * LinearMap.trace ℚ ((H k).obj (TopCat.of X))
      ((H k).map (TopCat.ofHom f)).hom) = _
  rw [← htrace]
  -- Dold's signed tensor convention in each actual homology degree.
  let V : ℕ → Type u := fun k ↦ (H k).obj (TopCat.of Y)
  let _ : ∀ k, FiniteDimensional ℚ (V k) := hHY
  let T (k : ℕ) : V k →ₗ[ℚ] V k := ((H k).map (TopCat.ofHom g)).hom
  let a (k : ℕ) : Module.Dual ℚ (V k) ⊗[ℚ] V k :=
    (-1 : ℚ)^(k*k) • (dualTensorHomEquiv ℚ (V k) (V k)).symm (T k)
  have hT (k : ℕ) : T k = (-1 : ℚ)^(k*k) •
      dualTensorHom ℚ (V k) (V k) (a k) := by
    dsimp only [a]
    rw [map_smul]
    change T k = (-1 : ℚ)^(k*k) •
      ((-1 : ℚ)^(k*k) •
        (dualTensorHomEquiv ℚ (V k) (V k))
          ((dualTensorHomEquiv ℚ (V k) (V k)).symm (T k)))
    rw [LinearEquiv.apply_symm_apply, smul_smul, ← pow_add]
    have heven : Even (k*k + k*k) := Even.add_self _
    rw [heven.neg_one_pow, one_smul]
  change (∑ k ∈ Finset.range (d + 1), (-1 : ℚ)^k * LinearMap.trace ℚ (V k) (T k)) = _
  rw [dold_alternating_trace_eq_contraction_sum V (Finset.range (d + 1)) a T
    (fun k _ ↦ hT k)]
  rw [hlocalQ]
  -- Remaining geometric identity: Dold (4.3)--(4.4), isolated as a named
  -- source-backed helper so its exact support-operator proof can be completed
  -- independently without changing this theorem's interface.
  simpa [V] using
    (dold_compact_enr_geometric_trace_step X e f d hfinite Y E H rfl g hconj hHY
      hvanishY a (fun k ↦ by
        dsimp only [a]))

end HolomorphicAnosov.FixedPointIndexInterface
