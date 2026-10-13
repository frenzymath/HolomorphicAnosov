import HolomorphicAnosov.Topology.HatcherPlanarDiskSphericalSeparation
import HolomorphicAnosov.Topology.OnePointCompactComplement
import HolomorphicAnosov.Topology.ComponentOfDisconnectedPreconnectedUnion
import Mathlib.Analysis.Normed.Module.Connected
import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology
import HolomorphicAnosov.Topology.Homology.SingularChainCompactSupport
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The interior of an embedded planar disk is a complementary component

Source: Hatcher, Algebraic Topology, Theorem 2B.3 proof, p.172,
using Proposition 2B.1(a,b), pp.169–170.
DAG node: `topo.hatcher_planar_disk_image_component_g7`.
-/
namespace HolomorphicAnosov
open Set

/-- The image of the open interior of a continuously embedded closed planar disk
is the component, through the center image, of the complement of its boundary image.
The radius is positive; no smoothness, local flatness, or preexisting openness of
this image is assumed.

Source: Hatcher, Algebraic Topology, proof of Theorem 2B.3, printed p.172;
Proposition 2B.1(a,b), pp.169–170. Local source: literature/hatcher-at.pdf/.txt.

Complete proof relative to the named lower homology providers:

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


The positive-radius closed disk is homeomorphic to the standard disk by translation
and positive rescaling. Compactness and injectivity make g a homeomorphism onto
its image. Place its image in the stereographic plane of S². Proposition 2B.1(b)
says the boundary-circle complement has exactly two path components. The image
of the disk interior is nonempty and path connected. Its complementary part in
that sphere complement is S² minus the whole disk image; this contains infinity
and is path connected by Proposition 2B.1(a) and the reduced-H0 calculation.
These two disjoint sets partition the boundary complement. Since each lies in a
path component and precisely two components exist, they must be exactly those
two components. The boundary complement is open in the locally path connected
sphere, so path components equal connected components.

Under the finite stereographic chart, the interior image lies in the component
of the boundary complement through g(center): it is connected and avoids the
boundary. Conversely any connected subset of that planar complement containing
g(center) remains connected in the sphere complement and therefore lies in its
interior-image component. Thus the planar connected component is exactly the
interior image. The set of disk points outside the open ball is precisely the
boundary sphere because the radius is positive. This proves the displayed
identity with the original Euclidean metric and the given map g.

For the finite-plane formulation used by the final component lemma, the complement
of the whole disk image remains path connected after removing infinity. Indeed it
is an open path-connected subset of the two-sphere; a path that encounters infinity
can be rerouted in a small coordinate disk, disjoint from the compact disk image,
along the connected punctured coordinate disk. The boundary complement in the
plane is not connected: the spherical interior-image and exterior components give
a separation on removing infinity, and the exterior still contains finite points
because the disk image is compact. This finite-plane comparison is now proved in Lean using the existing
`onePoint_complex_complement_component`: spherical preconnectedness puts any two
finite points in the same sphere component, hence in the same plane component.
Conversely the finite part is dense in the open sphere complement, so plane
preconnectedness extends to that sphere complement. A real-linear isometric
homeomorphism transports the original Euclidean plane to the complex plane.
Compactness is proved for the full disk image and its boundary image separately.
Only the two spherical homological assertions remain in `hsepS`.
The elementary component identification then uses the public
`component_of_disconnected_preconnected_union` theorem.
-/
theorem hatcher_planar_disk_image_component
    (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (g : Metric.closedBall x r → EuclideanSpace ℝ (Fin 2))
    (hg : Continuous g) (hinj : Function.Injective g) :
    let B : Set (Metric.closedBall x r) := {z | z.val ∈ Metric.ball x r}
    g '' B = connectedComponentIn (g '' Bᶜ)ᶜ
      (g ⟨x, Metric.mem_closedBall_self hr.le⟩) := by
  let B : Set (Metric.closedBall x r) := {z | z.val ∈ Metric.ball x r}
  change g '' B = connectedComponentIn (g '' Bᶜ)ᶜ _
  have hBconnected : IsPreconnected B := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have himage : (Subtype.val : Metric.closedBall x r → EuclideanSpace ℝ (Fin 2)) '' B =
        Metric.ball x r := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, Metric.ball_subset_closedBall hz⟩, hz, rfl⟩
    rw [himage]
    exact (convex_ball x r).isPreconnected
  have hdisjoint : g '' B ⊆ (g '' Bᶜ)ᶜ := by
    rintro z ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    exact hb ((hinj heq).symm ▸ ha)
  have hxB : (⟨x, Metric.mem_closedBall_self hr.le⟩ : Metric.closedBall x r) ∈ B := by
    change dist x x < r
    simpa only [dist_self] using hr
  have hforward : g '' B ⊆ connectedComponentIn (g '' Bᶜ)ᶜ (g ⟨x, Metric.mem_closedBall_self hr.le⟩) :=
    (hBconnected.image g hg.continuousOn).subset_connectedComponentIn
      ⟨⟨x, Metric.mem_closedBall_self hr.le⟩, hxB, rfl⟩ hdisjoint
  apply le_antisymm hforward
  have hparts : g '' B ∪ (range g)ᶜ = (g '' Bᶜ)ᶜ := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact hdisjoint hy
      · rintro ⟨z, _, rfl⟩
        exact hy ⟨z, rfl⟩
    · intro hy
      by_cases hgy : y ∈ range g
      · obtain ⟨z, rfl⟩ := hgy
        have hz : z ∈ B := by
          by_contra hz
          exact hy ⟨z, hz, rfl⟩
        exact Or.inl ⟨z, hz, rfl⟩
      · exact Or.inr hgy
  -- Compact-complement comparison discharges the passage from the sphere to the plane.
  have hchart {K : Set ℂ} (hK : IsCompact K) :
      IsPreconnected (OnePoint.some '' K)ᶜ ↔ IsPreconnected Kᶜ := by
    let S : Set (OnePoint ℂ) := (OnePoint.some '' K)ᶜ
    have hfinite : S ∩ range (OnePoint.some : ℂ → OnePoint ℂ) =
        OnePoint.some '' Kᶜ := by
      ext z
      constructor
      · rintro ⟨hz, x, rfl⟩
        exact ⟨x, fun hx ↦ hz ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨by simpa [S] using hx, ⟨x, rfl⟩⟩
    have hopen : IsOpen S := (hK.image OnePoint.continuous_coe).isClosed.isOpen_compl
    constructor
    · intro h
      apply isPreconnected_of_forall_pair
      intro x hx y hy
      have hxy : OnePoint.some y ∈ connectedComponentIn S (OnePoint.some x) :=
        h.subset_connectedComponentIn (by simpa [S] using hx) subset_rfl
          (by simpa [S] using hy)
      exact ⟨connectedComponentIn Kᶜ x, connectedComponentIn_subset _ _,
        mem_connectedComponentIn hx, HolomorphicAnosov.Topology.onePoint_complex_complement_component hK hx hy hxy,
        isPreconnected_connectedComponentIn⟩
    · intro h
      apply (h.image OnePoint.some OnePoint.continuous_coe.continuousOn).subset_closure
      · rw [← hfinite]
        exact inter_subset_left
      · change S ⊆ closure (OnePoint.some '' Kᶜ)
        rw [← hfinite]
        intro z hz
        exact hopen.inter_closure ⟨hz, OnePoint.denseRange_coe z⟩
  let e := Complex.orthonormalBasisOneI.repr.symm.toHomeomorph
  let gc : Metric.closedBall x r → ℂ := e ∘ g
  have hgc : Continuous gc := e.continuous.comp hg
  let : CompactSpace (Metric.closedBall x r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall x r)
  have hfull : IsCompact (range gc) := isCompact_range hgc
  have hboundary : IsCompact (gc '' Bᶜ) := by
    have hBopen : IsOpen B := Metric.isOpen_ball.preimage continuous_subtype_val
    exact hBopen.isClosed_compl.isCompact.image hgc
  have he (s : Set (EuclideanSpace ℝ (Fin 2))) :
      IsPreconnected (e '' s)ᶜ ↔ IsPreconnected sᶜ := by
    rw [← e.image_compl]
    exact e.isEmbedding.isInducing.isPreconnected_image
  have hgc_inj : Function.Injective gc := by
    intro a b hab
    apply hinj
    exact e.injective hab
  -- Hatcher 2B.1(a,b): the only remaining obligation is the two spherical assertions.
  have hsepS : IsPreconnected (OnePoint.some '' range gc)ᶜ ∧
      ¬ IsPreconnected (OnePoint.some '' (gc '' Bᶜ))ᶜ := by
    simpa [B] using
      Topology.hatcher_planar_disk_spherical_separation x r hr gc hgc hgc_inj
  have hsep : IsPreconnected (range g)ᶜ ∧ ¬ IsPreconnected (g '' Bᶜ)ᶜ := by
    constructor
    · apply (he (range g)).mp
      simpa only [gc, range_comp] using (hchart hfull).mp hsepS.1
    · intro h
      apply hsepS.2
      apply (hchart hboundary).mpr
      simpa only [gc, image_comp] using (he (g '' Bᶜ)).mpr h
  have hcomponent := component_of_disconnected_preconnected_union
    (hBconnected.image g hg.continuousOn) hsep.1
    (show ¬ IsPreconnected (g '' B ∪ (range g)ᶜ) by simpa only [hparts] using hsep.2)
    (show g ⟨x, Metric.mem_closedBall_self hr.le⟩ ∈ g '' B from
      ⟨⟨x, Metric.mem_closedBall_self hr.le⟩, hxB, rfl⟩)
  rw [hparts] at hcomponent
  exact hcomponent.le

end HolomorphicAnosov
