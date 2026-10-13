import HolomorphicAnosov.Topology.HatcherPlanarDiskImageComponent

/-!
# Open image of a continuous injection of a planar open set

Source: Allen Hatcher, *Algebraic Topology*, Theorem 2B.3 and proof,
printed p.172 (PDF p.181), specialized to dimension two. The supporting
Proposition 2B.1(a,b), pp.169–170, is expanded in the theorem's proof docstring.

The real plane is Mathlib's `EuclideanSpace ℝ (Fin 2)`. The domain is the
subtype of the specified open set with its induced topology. The full image
of that subtype map is `Set.range f`. No domain point or nonemptiness is chosen
in the statement, so the empty-domain case is included.
-/

namespace HolomorphicAnosov

/-- A continuous injection from an open subset of the real Euclidean plane has open image.

Source: Allen Hatcher, *Algebraic Topology*, Theorem 2B.3 and proof,
printed p.172 (PDF p.181); Proposition 2B.1(a,b), pp.169–170;
Mayer–Vietoris chain proof, pp.149–150; reduced homology, p.110;
and H₀ path-component calculation, pp.109–110.
Local source: `literature/hatcher-at.pdf` and `literature/hatcher-at.txt`.

Complete natural-language proof, relative to the named DAG providers:

I1. Use integral singular chains and the augmented complex defining reduced homology, including
degree −1. For a nonempty space the augmentation is onto because a point maps to 1, so reduced
H_(−1)=0. Ordinary H₀ is free on path components, with augmentation the sum of the coefficients.
Thus for nonempty X, reduced H₀=0 implies one path component; reduced H₀≅ℤ implies exactly two path
components. For the latter implication at least two components are necessary; three distinct
components would give two independent augmentation-kernel generators [x₁]−[x₀], [x₂]−[x₀], so a free
augmentation kernel isomorphic to ℤ permits exactly two. This applies even before local path
connectedness is asserted.
Providers: topo.integral_reduced_singular_homology, mathlib.singular_homology_zero_component_iso_g8.

I2. Derive the reduced open-cover Mayer–Vietoris sequence in Hatcher pp.149–150 rather than treating
a sheaf Mayer–Vietoris square as singular homology. For open A,B with X=A∪B, identify their chains
with supported ambient subcomplexes and put K=C(A)+C(B). In each ordinary degree,
0→C(A∩B)→C(A)⊕C(B)→K→0 has maps c↦(c,−c), (a,b)↦a+b. Injectivity and surjectivity are immediate from
the subgroup inclusions and sum; if a+b=0, then a=−b belongs to the intersection, which the adapter
identifies with C(A∩B). Boundaries commute with both maps. Augment K by restricting the ambient
coefficient-sum map. In mathematical degree −1 the sequence is 0→ℤ→ℤ⊕ℤ→ℤ→0 with the same formulas,
so it is also exact there, including when the intersection is empty. The generic augmentation and
degreewise short-exact results give an actual short exact sequence of augmented chain complexes.
Inclusion K→C(X) induces a homology isomorphism in positive degrees and degree zero: compare the
short exact sequences with first term C(B), middle terms K and C(X), and last terms C(A)/C(A∩B) and
C(X)/C(B). Excision gives the last comparison isomorphism, and the first is identity. Exact-sequence
chasing makes the middle comparison an isomorphism (for injectivity lift an element with zero image
to the first term, and for surjectivity lift its last-term image then correct the residual first-
term element). For reduced degree zero, the ordinary H₀ isomorphism commutes with augmentation and
hence restricts to an isomorphism of its kernel. In degree −1 it identifies augmentation cokernels,
since K and C(X) contain precisely the same points. The homology sequence therefore gives the
reduced Mayer–Vietoris sequence with these inclusion components in all the degrees needed below.
This supplies the signs and the augmented low-degree terms from genuine chain maps.
Providers: topo.singular_subspace_subcomplex_adapter, topo.singular_homology_excision_barycentric_subdivision, mathlib.chain_complex_augmentation_constructor_g8, mathlib.homological_complex_short_exact_of_degreewise, mathlib.homology_sequence_five_arrow_exact.

I3. View ℝ² inside S² using a stereographic chart, with omitted point ∞. Establish Proposition
2B.1(a) for the compact disk images needed here, equivalently embedded cubes I^k→ℝ² for k=0,1,2. The
radial disk–cube homeomorphism gives the equivalence of domain models. For k=0 the sphere minus the
one image point is ℝ² by stereographic projection; the straight contraction gives zero reduced
homology. In positive degrees use ordinary homotopy invariance; in degree zero use the
component/augmentation description. The usual singular prism homotopy preserves augmentation, so
this is also the augmented reduced statement. Every complement used in the induction is nonempty
because the cube image lies in ℝ² and misses ∞.
Providers: mathlib.sphere_stereographic_chart_g8, topo.euclidean_closed_disk_unit_cube_homeomorphism, topo.relative_singular_homotopy_invariance, mathlib.singular_homology_zero_component_iso_g8.

I4. Assume the embedded-(k−1)-cube assertion and suppose a reduced i-cycle α in S²\g(I^k) is not a
boundary, i≥0. Write the cube as I^(k−1)×I and split its last coordinate into two equal closed
intervals. The complements A and B of the two compact half-cube images are open; A∩B is the
complement of the full cube, and A∪B is the complement of their common embedded (k−1)-cube. The last
complement has zero reduced homology by induction. The reduced Mayer–Vietoris sequence therefore
makes (inclusion_*,−inclusion_*) an isomorphism from reduced H_i(A∩B) to reduced H_i(A)⊕reduced
H_i(B). The nonzero class of α remains nonzero in at least one half-cube complement. Rescale that
last-coordinate interval and repeat. Choose nested closed intervals J_m of lengths 2^(−m) such that
α is not a boundary in V_m=S²\g(I^(k−1)×J_m). All images are compact, their complements open and
increasing, and the induction applies to the slice at their unique common point t_*.
Providers: mathlib.isCompact_range, mathlib.isCompact_isClosed, mathlib.homology_sequence_five_arrow_exact.

I5. In the complement of g(I^(k−1)×{t_*}), induction says α=∂β for a finite singular chain β; for
i=0 this means an augmented zero-cycle and an ordinary one-chain boundary. Its support, the finite
union of its simplex images, is compact by the existing chain-support result. The union of the
increasing open V_m is exactly that slice complement: the intersection of the compact nested cube
images is the slice image, because injectivity of g forces any point lying in every image to have
one preimage whose last coordinate belongs to every J_m. The directed compact-cover theorem puts the
whole support of β in one V_m. The subspace adapter corestricts each supported simplex to that V_m;
face maps and boundaries commute with inclusion, so the same equality α=∂β holds there,
contradicting the choice of J_m. This proves reduced acyclicity for k=1, then k=2, directly from
Hatcher’s shrinking-interval proof on p.170.
Providers: topo.singular_chain_compact_support_image_compactness, mathlib.isCompact_elim_directed_cover_g10, topo.singular_subspace_subcomplex_adapter.

I6. For a planar embedded circle g:S¹→ℝ², divide its parameter circle into two closed semicircles
D₊¹,D₋¹ meeting in S⁰. In S² let A=S²\g(D₊¹), B=S²\g(D₋¹). They are open, nonempty and reduced-
acyclic by the embedded-interval assertion. Their union is S² minus the two distinct endpoint
images. Its reduced H₁ is ℤ: stereographically remove one endpoint, obtaining ℝ² with one finite
point removed; translate that point to zero and retract radially to S¹ by H(t,z)=((1−t)+t/|z|)z. The
positive multiplier never reaches zero and fixes the unit circle. Homotopy invariance and the
existing S¹ homology calculation give reduced H₁≅ℤ. Mayer–Vietoris gives reduced H₀(A∩B)≅reduced
H₁(A∪B)≅ℤ, since the surrounding reduced H₁ and H₀ of A and B vanish. Thus S²\g(S¹) has exactly two
path components by I1. This is the planar specialization of Proposition 2B.1(b), independent of any
Jordan–Schoenflies assertion.
Providers: mathlib.sphere_stereographic_chart_g8, topo.relative_singular_homotopy_invariance, topo.reduced_sphere_homology, mathlib.homology_sequence_five_arrow_exact, mathlib.singular_homology_zero_component_iso_g8.

I7. Let U⊂ℝ² be open and f:U→ℝ² continuous and injective. For x∈U choose a positive radius r with
the closed Euclidean disk K=closedBall(x,r)⊂U. Its restriction is a continuous injection on a
compact space into a Hausdorff space and hence, after corestricting to its image, a homeomorphism.
The same holds on its boundary circle. In S² minus f(frontier K), two disjoint nonempty path-
connected sets partition the space: f(ball(x,r)) and S²\f(K). The first is homeomorphic to the
ordinary open disk; the second has reduced H₀=0 by the embedded-two-disk assertion and contains ∞,
hence is path connected. The circle-complement calculation gives exactly two path components, so
these two sets are precisely them. This identification uses both disk and circle assertions, not
merely nonempty connected images.
Providers: mathlib.continuous_homeoOfEquivCompactToT2_g8, mathlib.singular_homology_zero_component_iso_g8.

I8. The circle image is compact and therefore closed, so its sphere complement is open and locally
path connected. Local path connectedness follows from the usual convex-ball basis in each
stereographic sphere chart, restricted to this open subset. Thus its path components equal connected
components. Connected components are closed in their space; since there are precisely two, each
component is also open, being the complement of the other closed component. Therefore f(ball(x,r))
is open in the sphere complement, hence in S², hence in the original ℝ² chart. It contains f(x). The
union of these open images over x∈U is f(U), proving it open. Empty U has empty open image and needs
no selected point. Applying the same assertion to every open subset of U shows the continuous
injection is an open map onto its image. This is exactly Hatcher Theorem 2B.3 in dimension two; its
compact-manifold Corollary 2B.4 is unnecessary.
Providers: mathlib.isCompact_isClosed, mathlib.pathComponent_eq_connectedComponent_g10.

Edge cases: for U=∅, the subtype domain is empty and the range is the open
empty set. No connectedness of U is required. The proof uses compact closed
disks locally, without imposing properness on f, differentiability, boundary
regularity, or a previously established local homeomorphism.
-/
theorem hatcher_planar_embedding_open_image
    (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : IsOpen U)
    (f : U → EuclideanSpace ℝ (Fin 2))
    (hf : Continuous f) (hinj : Function.Injective f) :
    IsOpen (Set.range f) := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds x.property)
  let D := Metric.closedBall x.val r
  let inc : D → U := fun z ↦ ⟨z.val, hball z.property⟩
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  let g : D → EuclideanSpace ℝ (Fin 2) := f ∘ inc
  have hg : Continuous g := hf.comp hinc
  have hginj : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (congrArg (Subtype.val : U → EuclideanSpace ℝ (Fin 2)) (hinj hab))
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall x.val r)
  let B : Set D := {z | z.val ∈ Metric.ball x.val r}
  have hxD : x.val ∈ D := by
    change dist x.val x.val ≤ r
    simpa only [dist_self] using hr.le
  have hxB : (⟨x.val, hxD⟩ : D) ∈ B := by
    change dist x.val x.val < r
    simpa only [dist_self] using hr
  have hxg : g ⟨x.val, hxD⟩ = f x := rfl
  have hopen : IsOpen (g '' B) := by
    have hBopen : IsOpen B := Metric.isOpen_ball.preimage continuous_subtype_val
    have hboundary : IsClosed (g '' Bᶜ) :=
      (hBopen.isClosed_compl.isCompact.image hg).isClosed
    have hcomponent : g '' B = connectedComponentIn (g '' Bᶜ)ᶜ (f x) := by
      exact hatcher_planar_disk_image_component x.val r hr g hg hginj
    rw [hcomponent]
    exact hboundary.isOpen_compl.connectedComponentIn
  have hmem : f x ∈ g '' B := ⟨⟨x.val, hxD⟩, hxB, hxg⟩
  apply Filter.mem_of_superset (hopen.mem_nhds hmem)
  rintro z ⟨a, _, rfl⟩
  exact ⟨inc a, rfl⟩

end HolomorphicAnosov
