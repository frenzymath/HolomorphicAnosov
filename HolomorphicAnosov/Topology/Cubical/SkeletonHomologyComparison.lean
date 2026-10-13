import HolomorphicAnosov.Topology.Homology.IntegralCompactSupportOrientation
import HolomorphicAnosov.Topology.Cubical.ZeroSkeletonFinite
import HolomorphicAnosov.Topology.Cubical.TopSkeletonHomology
import HolomorphicAnosov.Topology.Cubical.RationalSingularHomologyInclusion
import Mathlib.Topology.CompactOpen
import HolomorphicAnosov.Topology.Cubical.RationalSingularHomology
import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision
import HolomorphicAnosov.Topology.Cubical.SkeletonCarrierSubset
import HolomorphicAnosov.Topology.Cubical.CellCarrierSubsetSkeleton
import HolomorphicAnosov.Topology.Cubical.CellBoundarySubsetSkeleton
import HolomorphicAnosov.Topology.Cubical.ZeroVertexSpan
import HolomorphicAnosov.Topology.Cubical.SubcomplexSkeletonHomologySurjective
import HolomorphicAnosov.Topology.Cubical.PositiveSkeletonSubcomplexInjective
import HolomorphicAnosov.Topology.Cubical.PositiveBoundarySpan
import HolomorphicAnosov.Topology.Cubical.SubcomplexHighDegreeHomology
import HolomorphicAnosov.Topology.Homology.ContractibleSingularHomology
import HolomorphicAnosov.Topology.Homology.EmptySingularHomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homotopy.Basic

/-!
# Rational homology comparisons for finite cubical skeleta

Source: Hatcher, *Algebraic Topology*, Lemma 2.34, pp. 137–139;
Theorem 2.35 and cellular boundary formula, pp. 139–141; coefficient
chains, p. 153 and §3.A; Appendix A.2 and A.5, pp. 521–523.
DAG node: `topo.cubical_skeleton_homology_comparison_g12`.
-/

noncomputable section

open CategoryTheory

namespace HolomorphicAnosov.Cubical

/-- Rational homology comparisons for the original finite cubical skeleta.
Source: Hatcher, Algebraic Topology, Lemma 2.34 printed pp.137–139 (finite-dimensional written proof), Theorem 2.35 pp.139–140 (natural exact-sequence cellular comparison), cellular boundary formula pp.140–141; relative quotient/sphere/wedge comparison Proposition 2.22 pp.124–125 and Corollary 2.25 p.126; coefficient chains p.153 and §3.A pp.261–266. Hatcher Appendix pp.521–523: characteristic-map criterion A.2, explicit Nε(A) construction p.522, disjoint-closed-set shrinking argument A.3 p.522, radial collar deformation A.4 p.522 and subcomplex neighborhood deformation A.5 p.523. Bredon, Topology and Geometry, GTM139 (1993), Chapter I §16 Propositions16.2–16.3 and Theorem16.4 printed pp.56–57 (PDF38): written homogeneous radial homeomorphism of compact convex bodies. Its literal restriction to a radial annulus in a doubled cell cube and product with the remaining normal coordinates gives the stated boundary-sphere collar. Local acquired literature/hatcher-at.pdf/.txt and Bredon-Topology-and-Geometry-1993.pdf/.txt. Dold (1965), §5 Steps4–6 printed p.8 is the consumer, not the proof of these foundations.

Complete natural-language proof:

Each closed original rectilinear cell is a coordinate box in its affine coordinate span. Apply the source radial disk/cube homeomorphism, followed by its positive coordinate affine rescaling, to give a characteristic disk homeomorphism onto that box. It maps the disk interior to the relative box interior and the sphere to the union of proper faces. The relative interiors of the original finite cells, including all their faces, partition C; distinct open cells are disjoint. Their closed cells are compact, hence closed in the original Hausdorff Euclidean topology. A set meeting each of this finite family of closed cells in a closed subset is closed by finite union, so the characteristic weak topology is exactly that original topology. This is the characteristic-map criterion Hatcher A.2 p.521. Thus the original subdivision, its skeleta and all its subcomplexes are finite CW spaces in their given topologies, with the literal stated cell dimensions. Empty subcomplexes have no cells and zero singular chains. Refinement is not used to replace any of these homology objects.

Use Hatcher p.153 and §3.A p.261: the integral relative singular chain group is free on simplices outside the relative subspace, and its tensor with Q is identified with the rational relative chain group by σ⊗a↦aσ, with boundary ∂⊗id. Q is the fraction localization of Z and is flat; scalar extension preserves finite limits by the named flat-extension result and finite colimits by its left adjoint. Additivity follows from the tensor relations. Exactness therefore preserves the cycle/boundary sequences 0→Z_j→C_j→B_(j−1)→0 and 0→B_j→Z_j→H_j→0. Consequently H_j(pair;Q) is naturally H_j(pair;Z)⊗Q, as in Hatcher Corollary3A.4 p.264/Corollary3A.6(a)p.266 and the named homology-comparison theorem. The same argument applies to the augmented free chain complex for reduced homology. Thus the named integral sphere groups give reduced rational sphere homology Q in the sphere degree and zero otherwise, and the chosen integral orientation generator maps to its rational generator. No finite generation or integral-as-rational shortcut is used.

For a finite cubical CW space Y and m>0, apply Hatcher Appendix A.5 p.523 intrinsically in the CW space Y^m to its subcomplex Y^(m−1). In each m-cell take a radial collar of its attaching boundary, and fix the lower skeleton. Sliding each collar radially outward gives a deformation of this open neighborhood onto Y^(m−1) inside Y^m. The characteristic quotient maps and their products with the interval give joint continuity. Thus (Y^m,Y^(m−1)) is a good pair. Collapsing Y^(m−1) produces a finite wedge of m-spheres, one for each original m-cell. The good-pair quotient comparison identifies H_j(Y^m,Y^(m−1);Q) with the reduced homology of that wedge. Follow Hatcher Corollary2.25 p.126: apply the quotient comparison to the disjoint union of the spheres relative to the disjoint union of their basepoints; its quotient is the same wedge. Singular chains on a disjoint union split componentwise because each simplex has connected image, so its reduced relative homology is the direct sum of the sphere groups. Each sphere/basepoint pair is good by a small ball contraction. Q2 therefore makes the adjacent-skeleton relative group zero for j≠m and a direct sum of Q generators for j=m, naturally indexed by the original cells and their chosen orientations. For m=0 use the actual discrete vertex set: its H_0 is the direct sum of Q over the vertices and its positive-degree homology is zero. Empty skeleta give zero groups. This is exactly the written Lemma2.34(a) proof pp.137–138, including its degree-zero case.

The actual relative chain short exact sequence yields the named exact homology sequence for each pair (Y^m,Y^(m−1)). The segment H_(j+1)(Y^m,Y^(m−1))→H_j(Y^(m−1))→H_j(Y^m)→H_j(Y^m,Y^(m−1)) and Q3 show that the middle map is surjective for j≠m and injective for j≠m−1. Starting from the discrete zero-skeleton, induction proves H_j(Y^m)=0 for j>m. For a fixed q, the inclusion H_q(Y^q)→H_q(Y^(q+1)) is surjective; all subsequent skeleton inclusions on H_q are isomorphisms. Since these particular spaces have finitely many cells and dimension at most N, the sequence stops at a finite skeleton equal to Y. Hence H_q(Y^q)→H_q(Y) is surjective and H_k(Y)=0 for k>N. No infinite-grid chain argument is applied to the original finite spaces. This is the first, finite-dimensional written proof of Lemma2.34 pp.137–138; its separate infinite-dimensional arguments are unnecessary.

Let L_m=H_m(Y^m,Y^(m−1);Q), with the cell basis from Q3; use L_0=H_0(Y^0;Q). The source defines d_m=j_(m−1)δ_m, where δ_m is the pair connecting homomorphism and j_(m−1) relativizes to L_(m−1). Exactness gives d_(m−1)d_m=0. The same exact-sequence diagram as Hatcher pp.139–140 makes j_m:H_m(Y^m)→L_m injective with image ker d_m, and makes H_m(Y)=H_m(Y^m)/im δ_(m+1). Consequently j_m induces the isomorphism H_m(Y)≅ker d_m/im d_(m+1). In degree zero take the map to degree −1 to be zero, so the same quotient is H_0(Y). All maps in this comparison come from inclusions and connecting maps of the actual pairs. They commute with inclusion of subcomplexes, by the naturality of the pair-chain short exact sequence and its connecting maps: both inclusion paths postcompose the same singular simplices, and a connecting class is the boundary of the same relative-cycle representative. Thus this identifies the literal singular groups naturally, rather than defining them as cellular groups. The connecting map of an oriented cell sends its relative fundamental class to the fundamental class of its attaching boundary sphere, followed by inclusion; this is Hatcher’s cellular boundary formula pp.140–141.

For D⊆C^q there are no (q+1)-cells in either space. Q5 therefore identifies H_q(D) and H_q(C^q) with the kernels of their cellular d_q without quotienting by any nonzero (q+1)-boundary group. The cell-basis inclusion L_q(D)→L_q(C^q) is injective and commutes with d_q, so it is injective on those kernels. This proves the stated singular inclusion injectivity, including q=0 where D is a subset of the vertices. The full cube C is contractible by its straight-line contraction, hence H_q(C)=0 for q>0. Q5 then gives ker d_q(C)=im d_(q+1)(C). The q-cycles of C^q are exactly this same kernel. Therefore H_q(C^q) is generated by the boundary images of its (q+1)-cell relative generators; by the last part of Q5 these are the included oriented fundamental classes of their boundary spheres. For q=N there are no (N+1)-cells, so the group is zero. For q=0 the ordinary vertex classes, not edge boundaries, are the generators. Q4 applied to any original subcomplex M supplies the remaining skeleton-surjection and high-degree-zero conclusions. Choices of orientations can change individual generator signs but not their span or any claimed inclusion map.
-/
theorem cubical_skeleton_homology_comparison
    (N : ℕ) (hN : 1 ≤ N) (K : FiniteRectilinearSubdivision N)
    (q : ℕ) (hq : q ≤ N) (D : CubicalSubcomplex K)
    (hD : D.carrier ⊆ K.skeleton q) :
    let S := K.skeleton q
    let boundary := fun c : ClosedCoordinateCell N ↦
      {x : Fin N → ℝ | x ∈ c.carrier ∧ ∃ i : Fin N,
        c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)}
    Function.Injective (rationalSingularHomologyInclusion hD q) ∧
      (0 < q → ∃ hboundary : ∀ c ∈ K.cells, c.dimension = q + 1 → boundary c ⊆ S,
        Submodule.span ℚ
          (⋃ c, ⋃ hc : c ∈ K.cells, ⋃ hd : c.dimension = q + 1,
            Set.range (rationalSingularHomologyInclusion (hboundary c hc hd) q)) = ⊤) ∧
      (q = 0 → ∃ hvertices : ∀ c ∈ K.cells, c.dimension = 0 → c.carrier ⊆ S,
        Submodule.span ℚ
          (⋃ c, ⋃ hc : c ∈ K.cells, ⋃ hd : c.dimension = 0,
            Set.range (rationalSingularHomologyInclusion (hvertices c hc hd) 0)) = ⊤) ∧
      (∀ M : CubicalSubcomplex K,
        (∃ hM : M.skeleton q ⊆ M.carrier,
          Function.Surjective (rationalSingularHomologyInclusion hM q)) ∧
          ∀ k : ℕ, N < k → Subsingleton (rationalSingularHomology M.carrier k)) := by
  classical
  dsimp only
  have hboundary_local : ∀ c ∈ K.cells, c.dimension = q + 1 →
      {x : Fin N → ℝ | x ∈ c.carrier ∧ ∃ i : Fin N,
        c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)} ⊆ K.skeleton q := by
    intro c hc hd
    exact cell_boundary_subset_skeleton K q c hc hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hqzero : q = 0
    · subst q
      let : Finite (K.skeleton 0) := (zeroSkeleton_finite K).to_subtype
      let : DiscreteTopology (K.skeleton 0) := inferInstance
      by_cases hnonempty : D.carrier.Nonempty
      · let B : TopCat := TopCat.of (K.skeleton 0)
        let A : Set B := {y | y.val ∈ D.carrier}
        have hA : A.Nonempty := by
          obtain ⟨x, hx⟩ := hnonempty
          exact ⟨⟨x, hD hx⟩, hx⟩
        let e : TopCat.of D.carrier ≅ TopCat.of A := {
          hom := TopCat.ofHom ⟨fun x ↦ ⟨⟨x.val, hD x.property⟩, x.property⟩,
            (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
          inv := TopCat.ofHom ⟨fun x ↦ ⟨x.val.val, x.property⟩,
            (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
        let j : TopCat.of A ⟶ B := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
        let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 0).obj
          (ModuleCat.of ℚ ℚ)
        have hj : Function.Injective (F.map j) :=
          IntegralCompactSupportOrientation.discrete_subspace_homology_injective
            (R₀ := ℚ) B A hA (ModuleCat.of ℚ ℚ) 0
        have : IsIso (F.map e.hom) := (F.mapIso e).isIso_hom
        have he : Function.Injective (F.map e.hom) :=
          ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
        have heq : rationalSingularHomologyInclusion hD 0 = F.map e.hom ≫ F.map j := by
          rw [← F.map_comp]
          rfl
        rw [heq]
        exact hj.comp he
      · let : IsEmpty D.carrier := ⟨fun x ↦ hnonempty ⟨x.val, x.property⟩⟩
        let := ModuleCat.subsingleton_of_isZero
          (HolomorphicAnosov.singular_homology_isZero_of_isEmpty
            (TopCat.of D.carrier) (ModuleCat.of ℚ ℚ) 0)
        exact Function.injective_of_subsingleton _
    · exact cubical_positive_skeleton_subcomplex_injective N hN K q hq
        (by omega) D hD
  · intro hqpos
    refine ⟨hboundary_local, ?_⟩
    by_cases htop : q = N
    · subst q
      let := top_skeleton_homology_subsingleton hN K
      exact Subsingleton.elim _ _
    · exact cubical_positive_boundary_span N hN K q hq hqpos htop
  · intro hqzero
    subst q
    refine ⟨?_, ?_⟩
    · intro c hc hd
      exact cell_carrier_subset_skeleton K 0 c hc (by omega)
    · exact cubical_zero_vertex_span K
  · intro M
    refine ⟨cubical_subcomplex_skeleton_homology_surjective K M q, ?_⟩
    intro k hk
    exact cubical_subcomplex_high_degree_homology_subsingleton K M k hk

end HolomorphicAnosov.Cubical
