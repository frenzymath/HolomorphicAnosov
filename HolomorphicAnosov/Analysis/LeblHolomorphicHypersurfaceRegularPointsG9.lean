import HolomorphicAnosov.Analysis.Lebl.leblCoordinatePolydisc
import HolomorphicAnosov.Analysis.Lebl.leblUnpermuteGraphCoordinates
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicZeroSet
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicZeroSetGraphAt
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicHypersurfaceRegularPoints
import HolomorphicAnosov.Analysis.Lebl.isOpen_leblCoordinatePolydisc
import HolomorphicAnosov.Analysis.Lebl.lebl_regularPoints_isOpen
import HolomorphicAnosov.Analysis.Lebl.lebl_analyticOnNhd
import HolomorphicAnosov.Analysis.Lebl.lebl_exists_nonzero_jet
import HolomorphicAnosov.Analysis.Lebl.lebl_minimal_derivative
import HolomorphicAnosov.Analysis.Lebl.lebl_product_implicit
import HolomorphicAnosov.Analysis.Lebl.lebl_nonzero_coordinate_graph
import HolomorphicAnosov.Analysis.Lebl.lebl_unpermute_linear
import HolomorphicAnosov.Analysis.Lebl.lebl_unpermute_point
import HolomorphicAnosov.Analysis.Lebl.lebl_disk_zero_persistence
import HolomorphicAnosov.Analysis.Lebl.lebl_graph_transfer

/-!
# Regular graph points of a holomorphic zero set

Source: Jiří Lebl, *Tasty Bits of Several Complex Variables*, version 3.4 (2020),
§1.6, Theorem 1.6.2 and its proof on printed p. 36; the multiplicity example is on p. 37.
DAG node: `analysis.lebl_holomorphic_hypersurface_regular_points_g9`.

The proof follows the minimal-derivative, implicit-graph and boundary-winding source route. The
local graph predicate uses genuine coordinate
permutations, open polydiscs, complex differentiability and equality of the underlying zero set
with a graph. It has no gradient, multiplicity-one or squarefree condition. Ambient dimension
is written as `n + 1`, covering exactly the positive dimensions in the source. Functions are
ordinary totalizations; their hypotheses concern only the specified open domains.
-/

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- The regular graph points of a nonzero holomorphic function on a domain are open and dense
in its underlying zero set.

Source: Lebl, *Tasty Bits of Several Complex Variables*, version 3.4, Theorem 1.6.2,
printed p. 36; the example on p. 37 excludes replacing zero-set regularity by a nonzero
original gradient. The disk zero-persistence step also follows the written straight-line
Rouché argument in McMullen, *Advanced Complex Analysis*, Corollary 1.23, p. 12.

The parameter `n` is one less than the positive ambient dimension. In particular `n = 0`
is the one-variable case and the parameter polydisc is the singleton complex zero space.
Only complex differentiability on `U` is assumed; no regularity of a totalization outside
`U` is required. Nonidentity with zero is the explicit witness `∃ z ∈ U, a z ≠ 0`.

Natural-language proof (the full one-level proof of the matching DAG node):

R1. A graph witness remains a witness at every graph point in its product neighborhood: the
coordinate projections pull the parameter polydisc and solved-variable disk back to relatively open
neighborhoods in N. Reuse the SAME witness; no unnecessary shrinking is required by the graph
predicate. For density let S be a nonempty relatively open subset of N and write S as the inverse
image of an ambient open W. The polydisc Cauchy provider gives analytic germs on U. If all
coordinate jets vanished at any p in U, the derivative provider would give a zero germ, and the
analytic identity theorem on connected U would force a identically zero, contradicting the given
nonzero value. It suffices to construct a graph point in N intersect W. Empty N is vacuous. The same
algorithm includes ambient complex dimension one, where the parameter space is C^0.
Dependencies: analysis.polydisc_cauchy_power_series, analysis.analytic_identity_open_domain.

R2. Consider all finite ordered lists J of coordinate derivatives for which the ordered derivative
is nonzero at some p in N intersect W. The preceding zero-germ argument makes this set nonempty. Its
least list length k is positive because the empty-list derivative is a, which vanishes on N. Choose
a minimal list J=L followed by coordinate j and such a point p. The ordered derivative h along L is
holomorphic and complex C-infinity on U by the named derivative provider. Minimality implies h
vanishes at every point of N intersect W. By the actual recursive ordered-derivative definition, its
j-coordinate derivative at p is the nonzero derivative along J. This predecessor identity uses no
unproved mixed-derivative commutation. Restrict to the open O=U intersect W and permute j to the
last coordinate. The original defining function may have zero gradient everywhere on N.
Dependencies: analysis.lebl_polydisc_holomorphic_coordinate_derivatives_g1,
analysis.analytic_identity_open_domain.

R3. The derivative source child gives h complex C-infinity on the open O=U intersect W, hence
complex C1 at p. Split the permuted coordinates as E1=C^(n-1) and E2=C, with target F=C. They are
Banach complex spaces, including E1=C^0 when n=1. Under this fixed continuous complex-linear
coordinate identification, the solved-variable partial Frechet derivative of h at p is
multiplication by c=P_n h(p)≠0. Its inverse is multiplication by1/c, so it is the required
continuous complex-linear equivalence. Use an arbitrary ambient totalization of h outside O; the
open product neighborhood of p fixes its C1 derivative and all local equations. Apply the existing
COMPLEX implicit-function theorem at finite order1. It gives an implicit map g with g(p prime)=p_n,
a local uniqueness equation h(z prime,z_n)=0 iff z_n=g(z prime), and ContDiffAt C1 g at p prime. The
new exact finite-C1 neighborhood leaf supplies a neighborhood on which THIS g is ContDiffOn C1.
Restrict to an open polydisc V in it; at every point of V this gives ContDiffAt C1 and the named
conversion gives complex differentiability, hence holomorphy throughout V. No common C-infinity
neighborhood is inferred from C-infinity at a single point. Intersect the implicit-equation
neighborhood with O and choose product V×D around p inside it. By continuity of g and g(p
prime)=p_n, shrink V so g(V)⊂D. Thus the h-zero set in this product is exactly the holomorphic
graph. Since a=0 implies h=0 there, N∩(V×D) lies in that graph.
Dependencies: analysis.lebl_polydisc_holomorphic_coordinate_derivatives_g1,
mathlib.contDiffAt_implicitFunction, mathlib.contDiffAt_one_contDiffOn_nhds_g1,
mathlib.contDiffAt_differentiableAt.

R4. Use the h-graph product V times D inside O and set b(w)=a(p prime,w). Since every a-zero in the
product is an h-zero, b(w)=0 already implies w=g(p prime)=p_n. Thus the center is the ONLY zero of b
in D, without an extra factorization theorem. Choose R>0 with the closed disk around p_n of radius R
contained in D. Every slice a_y is analytic on a neighborhood of this closed disk by complex
differentiability on the original open domain and the continuous complex-linear coordinate
embedding. On its boundary b is nonzero. Joint continuity and compactness of the boundary give a
SINGLE parameter neighborhood on which |a_y(w)-b(w)|<|b(w)| at EVERY boundary point; the compact
eventually-forall theorem packages the finite neighborhood intersection. Follow McMullen
Corollary1.23 p12: b+t(a_y-b) is a jointly continuous boundary homotopy avoiding zero, since the
perturbation norm is at most |a_y-b|<|b|. The existing winding theorem equates endpoint windings.
Its holomorphic disk zero-count formula gives positive winding for b because the center is a zero of
positive order and all zero orders are positive. The same formula gives at least one interior zero
of every a_y. The h-graph uniqueness forces this zero to equal g(y). Hence a(y,g(y))=0 and g(y)
belongs to the inner disk throughout a smaller parameter polydisc. Conversely every original zero
there belongs to the h-graph. This proves the exact original a-zero graph in an open product inside
W. The parameter space C^0 uses precisely the same construction; no separate isolated-zero provider
is needed.
Dependencies: mathlib.differentiableOn_analyticOnNhd_complex_g5,
analysis.lyubich_winding_holomorphic_zero_count.

R5. R1 proves relative openness and R2–R4 construct a graph point in every nonempty relatively
open portion of N, hence density. This conclusion concerns the underlying zero set. For
a(z)=(z1^2−z2^2)^2, the gradient of a can vanish along all of N although the two branches away
from their intersection are regular as zero-set graphs; Lebl’s p37 example demonstrates why
replacing this result by da(p)≠0 would be false. Dependencies: elementary.
-/
theorem lebl_holomorphic_hypersurface_regular_points_g9 (n : ℕ)
    {U : Set (Fin (n + 1) → ℂ)} {a : (Fin (n + 1) → ℂ) → ℂ}
    (hU : IsOpen U) (hconnected : IsConnected U)
    (ha : DifferentiableOn ℂ a U) (hnonzero : ∃ z ∈ U, a z ≠ 0) :
    IsOpen (leblHolomorphicHypersurfaceRegularPoints U a) ∧
      Dense (leblHolomorphicHypersurfaceRegularPoints U a) := by
  refine ⟨lebl_regularPoints_isOpen U a, ?_⟩
  apply dense_iff_inter_open.mpr
  intro S hS hSne
  obtain ⟨W, hW, hWS⟩ := isOpen_induced_iff.mp hS
  obtain ⟨p₀, hp₀⟩ := hSne
  have hp₀W : p₀.val ∈ W := by rw [← hWS] at hp₀; exact hp₀
  obtain ⟨h, j, p, hp, hap, hh, hhd, hzero, hj⟩ :=
    lebl_minimal_derivative (Nat.succ_le_succ (Nat.zero_le n)) hU hconnected ha hnonzero
      ⟨p₀.val, ⟨p₀.property.1, hp₀W⟩, p₀.property.2⟩
  have hO := hU.inter hW
  have hgraph := lebl_nonzero_coordinate_graph hO
    (hh.mono inter_subset_left) hp (hzero p hp hap) j hj
  have hactual := lebl_graph_transfer hO (ha.mono inter_subset_left) hzero hap hgraph
  have hactualU : leblHolomorphicZeroSetGraphAt U a p := by
    obtain ⟨hp', σ, c, r, d, s, g, hr, hs, hpy, hpw, hg, hmaps, hdom, heq⟩ := hactual
    exact ⟨⟨hp'.1.1, hap⟩, σ, c, r, d, s, g, hr, hs, hpy, hpw, hg, hmaps,
      fun y hy w hw ↦ (hdom y hy w hw).1, heq⟩
  refine ⟨⟨p, hp.1, hap⟩, ?_, hactualU⟩
  rw [← hWS]
  exact hp.2

end HolomorphicAnosov.Analysis


