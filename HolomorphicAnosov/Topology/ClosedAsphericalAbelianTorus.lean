import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.ClosedAsphericalAbelianTorusSomeRank
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.ClosedManifoldDimensionEqOfHomotopyEquiv
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusChartedSpace
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusIsManifold
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjectionSurjective
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjectionLocalHomeomorph

/-!
# Homotopy torus recognition for closed aspherical abelian manifolds

Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, printed p.598;
the full source expansion is recorded in `topo.closed_aspherical_abelian_torus`.
This is only homotopy equivalence with the genuine quotient/product real torus.
It does not assert homeomorphism, an orientation, or smooth conjugacy.

All input notions below are Mathlib data on their original topology: an actual Euclidean
smooth atlas, a surjective covering map from a contractible space, and the fundamental group
at a chosen point. No replacement carrier package or classification hypothesis is introduced.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

/-- A nonempty closed connected smooth real `n`-manifold whose connected universal cover is
contractible and whose fundamental group is abelian and torsion-free is homotopy equivalent
to the actual product `UnitAddTorus (Fin n)`, including `n = 0`.

The whole-space Euclidean model makes the manifold boundaryless; `CompactSpace` expresses
closedness in the closed-manifold convention. Hausdorffness and second countability are the
standard manifold separation/countability conditions. All atlas and topological structures
are selected once on `M` and are the ones used by the maps in the conclusion.

The input `p` is an actual surjective covering map. `ContractibleSpace U` supplies an actual
homotopy equivalence with a point; in particular `U` is nonempty, connected and simply
connected, so this is a connected universal cover. No cover is defined using an admitted proof.
The choice `x₀` only names a basepoint in the nonempty manifold. The group hypotheses use
its actual `FundamentalGroup M x₀`: commutativity and the absence of nonidentity elements
with a positive natural power equal to one. No identification with `ℤ^n` is a premise.

The conclusion contains continuous maps in both directions and actual jointly continuous
interval homotopies of their composites to the identity maps, as specified by Mathlib's
`ContinuousMap.HomotopyEquiv`. There is no homeomorphism or rigidity conclusion.

Source: Ghys, Theorem B proof, printed p.598. Expansion: Hatcher, *Algebraic Topology*,
Theorem A.7 pp.525–527, Corollaries A.8–A.9 p.527, Proposition A.11 pp.528–529,
Corollary A.12 p.529; Proposition 1A.2 pp.84–85, Proposition 1.26 pp.50–52;
K(G,1) definition p.87, Example 1B.5 p.88, Theorem 1B.8/Proposition 1B.9 pp.90–91;
Theorem 2.10/Corollary 2.11 pp.111–113, Theorem 3.26/Lemma 3.27 pp.236–238.
Finite torsion-free module algebra: `Module.basisOfFiniteTypeTorsionFree'`.

Full natural-language proof of `topo.closed_aspherical_abelian_torus`:

1. If n=0, each point has an open neighborhood homeomorphic to R^0, a singleton, so M is discrete.
Connectedness and nonemptiness make M a singleton. T^0 is the singleton empty product; the unique
maps in both directions are continuous and their composites are identities, with constant jointly
continuous homotopies. Hence the n=0 case is proved independently. In the remaining proof fix x0 in
M; all ranks below still allow r=0.

Inputs: topo.def_real_torus, topo.def_homotopy_equivalence.

2. Apply topo.closed_manifold_finite_simplicial_retract_pi1_fg to the given closed connected smooth
M. It derives the compact-manifold ENR and finite simplicial-retraction input from coordinate local
contractibility and the HatcherA.7–A.9 construction; the parent does not assume an ENR or a
triangulation of M.

Inputs: topo.closed_manifold_finite_simplicial_retract_pi1_fg.

3. Retain from topo.closed_manifold_finite_simplicial_retract_pi1_fg the literal finite connected
simplicial realization P0, its finite CW structure, and continuous j:M→P0,q:P0→M with qj=id_M. These
maps establish CW domination of M and preserve the original M topology.

Inputs: topo.closed_manifold_finite_simplicial_retract_pi1_fg.

4. For the chosen x0∈M, topo.closed_manifold_finite_simplicial_retract_pi1_fg supplies a finite
generating set of the actual π1(M,x0); its source proof obtains this via the finite one-skeleton and
the retraction-induced surjection. No lattice embedding or finite universal cover is used.

Inputs: topo.closed_manifold_finite_simplicial_retract_pi1_fg.

5. Apply topo.cw_domination_homotopy_model to the finite connected CW realization P0 and the
continuous maps j,q supplied by topo.closed_manifold_finite_simplicial_retract_pi1_fg. The equation
qj=id_M supplies the constant jointly continuous domination homotopy. The source theorem returns a
connected Hausdorff CW K and actual continuous a_M:M→K,b_M:K→M with jointly continuous H_M:b_M
a_M≃id_M and H_K:a_M b_M≃id_K. These exact maps and homotopies witness CW homotopy type; no finite-
CW claim or recognition of M from homology is used.

Inputs: topo.closed_manifold_finite_simplicial_retract_pi1_fg, topo.cw_domination_homotopy_model,
topo.def_homotopy_equivalence.

6. Put G=π1(M,x0) with its given operations and commutativity. Regard Additive G as a Z-module via
integer multiples. If g1,...,gm generate G, every group word equals an integer linear combination
since G is abelian, so their Z-span is the whole module and it is finite. If a≠0 and a z=0, group
torsion-freeness forces z=0 (replace a by |a| if negative); this is the module torsion-free
hypothesis. Specialize Module.basisOfFiniteTypeTorsionFree' with R=Z and M=Additive G. It returns a
natural r and an actual basis b:Basis(Fin r) Z (Additive G). The coordinate map b.repr gives G≅Z^r
after identifying finitely supported functions on finite Fin r with all functions. Its inverse sends
coordinates c to the finite sum Σ_i c_i b_i; the basis expansion and linear independence prove both
inverse equations. Rank r may be zero. No embedding into C, discreteness or lattice assumption is
used.

Inputs: mathlib.module_basis_of_finite_type_torsion_free,
topo.closed_manifold_finite_simplicial_retract_pi1_fg.

7. Coordinate balls show M is locally path-connected and semilocally simply connected; connectedness
then makes it path-connected. Apply topo.aspherical_torus_recognition to the actual contractible
universal cover from the hypotheses, the constructed CW homotopy model, and the coordinate group
equivalence. Hatcher1B.9 realizes a group isomorphism and its inverse by based continuous maps on CW
K and T^r; uniqueness makes their composites homotopic to identities. The bank recognition proof
transports the cover to K and transports back to M, preserving actual continuous maps
u:M→T^r,v:T^r→M and both jointly continuous inverse homotopies. Use precisely that conclusion;
equality of fundamental groups alone is not the homotopy equivalence.

Inputs: topo.aspherical_torus_recognition, topo.def_homotopy_equivalence.

8. T^r is the same product of r copies of R/Z specified in topo.def_real_torus. For each coordinate
choose an interval of length1 whose omitted quotient point avoids the chosen torus point. The
quotient map is an open partial homeomorphism on that interval; invert it and take finite products
to obtain real r-dimensional charts. On overlaps two lifts differ by an integer, locally constant,
so chart transitions are locally translations and hence smooth. Finite products of the compact
AddCircle factors are compact and Hausdorff; the torus is nonempty and connected since the
continuous coordinate quotient R^r→T^r is surjective and R^r is connected. Thus this literal T^r is
a nonempty closed connected smooth real r-manifold. For r=0 it is a point with its empty-coordinate
chart. Discreteness here is only that of the known subgroup Z⊂R defining the target circle; it is
not an added hypothesis on π1(M) or any translation representation.

Inputs: topo.def_real_torus, mathlib.add_circle_open_partial_homeomorph_coe_g8,
mathlib.add_circle_compactSpace_g2, mathlib.add_circle_continuous_mk_g8,
mathlib.open_quotient_map_pi_g8, mathlib.pi_t2_space_g8.

9. Take coefficient category ModuleCat(ZMod2) and its coefficient object ZMod2, using compatible
universe lifts if needed. Apply mathlib.topcat_homotopy_to_sset_g8 to the two actual continuous
inverse homotopies. Their singular simplicial homotopies give chain homotopies by
mathlib.sset_homotopy_chain_complex_map_g8. Then mathlib.homotopy_homology_map_eq_g8 equates the
homology maps of each composite and its identity endpoint. The singular-chain functor and homology
composition/identity leaves identify those maps with H_k(v)H_k(u) and H_k(u)H_k(v). These equal
identities in every k≥0, so the actual induced maps are mutually inverse and give
H_k(M;ZMod2)≅H_k(T^r;ZMod2). This explicitly supplies the topological-to-chain bridge; a chain-
complex homotopy equivalence alone would not.

Inputs: mathlib.topcat_homotopy_to_sset_g8, mathlib.sset_homotopy_chain_complex_map_g8,
mathlib.homotopy_homology_map_eq_g8, mathlib.sset_chain_complex_functor_g8,
mathlib.singular_homology_functor_g8, mathlib.homological_complex_homology_map_comp,
mathlib.homological_complex_homology_map_id.

10. Apply topo.closed_manifold_mod2_top_homology to M and the constructed smooth T^r. It gives
nonzero H_n(M;ZMod2) and H_r(T^r;ZMod2), with all homology above their respective dimensions zero.
If n>r, the degree-n homology isomorphism identifies a nonzero group with zero. If r>n, the degree-r
isomorphism does the same in the reverse direction. Hence neither strict inequality holds and n=r.
Hatcher3.26 states H_top(-;Z2)=Z2 regardless of orientability, so no orientation premise is
inserted. This also allows r=0.

Inputs: topo.closed_manifold_mod2_top_homology.

11. Replace the finite coordinate index Fin r by Fin n using r=n, transporting only the target type
of the same maps u,v and their two actual homotopies. Their continuity and endpoint equations are
preserved under this index identification; equivalently compose with the coordinate-reindexing
homeomorphism and its inverse. This yields exactly v u≃id_M and u v≃id_(T^n) with jointly continuous
homotopies. The proof constructs a homotopy equivalence only; no homeomorphism rigidity result
enters.

Inputs: topo.def_real_torus, topo.def_homotopy_equivalence.

The formal proof below follows this decomposition. It uses a universe-lifted copy of
exactly the quotient/product torus for the mod-two comparison, with an explicitly
constructed smooth atlas. The uniform argument also covers dimension zero, without
a separate singleton reduction. The ENR/finite-generation theorem, CW-model theorem,
aspherical recognition and mod-two top-homology theorem remain lower mathematical
inputs with their own proof obligations; completing this local proof does not close them.
-/
theorem closed_aspherical_abelian_torus (n : ℕ) (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    {U : Type v} [TopologicalSpace U] [ContractibleSpace U]
    (p : U → M) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (x₀ : M)
    (habelian : ∀ a b : FundamentalGroup M x₀, a * b = b * a)
    (htorsion : ∀ a : FundamentalGroup M x₀, ∀ k : ℕ, 0 < k → a ^ k = 1 → a = 1) :
    Nonempty (ContinuousMap.HomotopyEquiv M (UnitAddTorus (Fin n))) := by
  obtain ⟨r, ⟨e⟩⟩ := closed_aspherical_abelian_torus_some_rank n M p hp hsurj x₀
    habelian htorsion
  let P := ULift.{u} (UnitAddTorus (Fin r))
  let : ChartedSpace (EuclideanSpace ℝ (Fin r)) P := liftedTorusChartedSpace r
  have : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin r))) ∞ P :=
    liftedTorus_isManifold r
  have : ConnectedSpace P :=
    (liftedTorusProjection_surjective.{u} r).connectedSpace
      (liftedTorusProjection_localHomeomorph.{u} r).continuous
  let e' : ContinuousMap.HomotopyEquiv M P :=
    e.trans Homeomorph.ulift.symm.toHomotopyEquiv
  have hnr : n = r := closed_manifold_dimension_eq_of_homotopyEquiv n r M P e'
  subst r
  exact ⟨e⟩


end HolomorphicAnosov
