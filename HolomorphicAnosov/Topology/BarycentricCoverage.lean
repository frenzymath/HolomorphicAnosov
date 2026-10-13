import HolomorphicAnosov.Topology.Barycentric.centroid_mem_convexHull_range
import HolomorphicAnosov.Topology.Barycentric.child_convexHull_subset
import HolomorphicAnosov.Topology.Barycentric.mem_convexHull_range_iff_weights
import HolomorphicAnosov.Topology.Barycentric.exists_antitone_permutation
import HolomorphicAnosov.Topology.Barycentric.prefix_centroid_eq_smul_sum
import HolomorphicAnosov.Topology.Barycentric.sum_range_smul_eq_sum_drops
import HolomorphicAnosov.Topology.Barycentric.sum_drop_weights
import HolomorphicAnosov.Topology.Barycentric.weighted_sum_eq_drop_centroids
import HolomorphicAnosov.Topology.Barycentric.sum_Iic_eq_range_of_fin
import HolomorphicAnosov.Topology.Barycentric.convexHull_subset_union_children
import HolomorphicAnosov.Topology.Barycentric.one_step_coverage
import HolomorphicAnosov.Topology.Barycentric.foldl_cover_of_one_step
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module

/-!
# Coverage by finite barycentric subdivisions

Source: Allen Hatcher, *Algebraic Topology*, proof of Proposition 2.21(1),
pp.119–121; Exercise 24, p.133, for the ordered-coordinate chambers.
DAG node: `topo.barycentric_subdivision_coverage`.

The ambient space is an arbitrary real vector space, not necessarily normed
or finite-dimensional. Mathlib's `convexHull` and indexed `Finset.centroid`
are used directly. Prefixes are sets of indices, so repeated vertex values
retain multiplicity. The child operation is a local binding in the theorem;
finite-depth children use Mathlib's `List.foldl`, with no separate or hollow
subdivision object. The statement includes the empty vertex tuple.
-/

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- Every finite real vertex tuple is covered by its permutation-prefix
barycentric cells, and by all its finite-depth descendants. Both assertions
also hold for every injectively indexed face tuple.

Source: Hatcher, *Algebraic Topology*, Proposition 2.21 proof part (1),
pp.119–121, and Exercise 24, p.133. The generic and degenerate tuple scope
is obtained by the explicit affine image calculation in the proof below.

For a permutation σ and prefix position k, `child l w σ k` is exactly the
average of the k.val+1 indexed vertices w(σ(0)),...,w(σ(k)). The index
prefix is nonempty whenever k exists, including l=1. At l=0 there is no k,
so the child is the empty tuple and no empty centroid is evaluated. A list
of r permutations specifies exactly r successive children, in list order.
The union indexed by lists of length r is therefore the full subdivision
at depth r; depth zero has only the empty list. The face clause restricts
the ORIGINAL tuple along the given embedding before forming any children.
It asserts coverage of that face tuple, not a geometric-intersection
identity that could fail for degenerate tuples.

Complete natural-language proof (formalized below by sorting nonnegative barycentric weights,
prefix-centroid decomposition, finite iteration, and face-tuple specialization):

BC0. Let E be the ambient real vector space and v:Fin m→E the finite tuple; when m≥1 write m=n+1.
For σ∈Perm(Fin m), define the child tuple b^σ:Fin m→E by b^σ_k=(1/(k+1))Σ_{j=0}^k v_{σ(j)}. Let
C_σ(v)=convexHull_ℝ(range b^σ). Prefixes are nonempty index sets and barycenters average indexed
entries, retaining multiplicity even if vertex values repeat. For m=0 there is an empty child
tuple and C_σ(v)=convexHull∅=∅. Define depth0 as the single original tuple, and depth(r+1) as all
prefix children of depth-r tuples; the represented set is the union of their convex hulls.

BC1. For x∈convexHull(range v), apply the exact finite-set hull leaf to the finite set u of
distinct vertex values. Obtain nonnegative a(y) on u with Σ_{y∈u}a(y)=1 and Σ_{y∈u}a(y)y=x. For
each y∈u choose one index i_y with v(i_y)=y; distinct y have distinct chosen indices. Put
t(i_y)=a(y) and t(i)=0 on all remaining indices. Reindexing the finite sums yields t_i≥0, Σ_i
t_i=1 and Σ_i t_i v_i=x. Thus repeated vertex values cause no problem, and x comes from the
standard simplex point t under the linear map L:ℝ^m→E, L(t)=Σ_i t_i v_i. When m=0 there is no x in
the empty hull, so this step is only used for m≥1.

BC2. Apply Tuple.sort to i↦−t_i. The named sort leaf supplies a permutation σ whose reordered t
values are weakly decreasing. For m=n+1≥1 put a_j=t_(σ(j)) for 0≤j<m and put a_m=0 as a separate
terminal scalar, not evaluation at an out-of-range Fin m index. Define c_k=(k+1)(a_k−a_(k+1)) for
0≤k<m. Weak decrease and the nonnegative terminal level give c_k≥0. Expanding and shifting these
finite sums gives Σ_(k=0)^(m−1)c_k=Σ_(k=0)^(m−1)(k+1)a_k−Σ_(j=1)^m j
a_j=a_0+Σ_(j=1)^(m−1)((j+1)−j)a_j−m a_m=Σ_(j=0)^(m−1)a_j=Σ_i t_i=1. For each 0≤j<m, the
coefficient of e_(σ(j)) in Σ_k c_k β^σ_k is
Σ_(k=j)^(m−1)c_k/(k+1)=Σ_(k=j)^(m−1)(a_k−a_(k+1))=a_j−a_m=a_j; the last equality is finite
cancellation of adjacent terms. Here β^σ_k=(1/(k+1))Σ_(l=0)^k e_(σ(l)), and every divisor k+1 is
positive. Thus t=Σ_k c_k β^σ_k by equality at all m coordinates. The finite algebra is proved
here, with no separate prerequisite. Ties a_k=a_(k+1) and zero terminal levels give c_k=0 and
preserve all identities. When n=0, m=1, a_0=1,a_1=0,c_0=1; the shifted and tail sums contain
exactly the indicated terms. For m=0 no normalized t exists and the empty-hull case in BC0–BC1
applies instead. Under the linear map L(t)=Σ_i t_i v_i the same indexed identity retains all
multiplicities of an arbitrary tuple v; no injectivity of its values is used.

BC3. Apply the actual linear map L from BC1 to the coordinate identity of BC2. Finite linearity
gives L(β^σ_k)=b^σ_k and x=Σ_k c_k b^σ_k. The finite convex-combination membership leaf now places
x in C_σ(v). For the converse, the same leaf puts every b^σ_k in convexHull(range v), because the
k+1 prefix coefficients all equal1/(k+1) and sum to1. Convexity of that hull gives
C_σ(v)⊆convexHull(range v). Therefore the union over σ is exactly the parent hull. Neither
direction uses affine independence, unique coordinates of x in E, or a metric.

BC4. Identify these explicit children with Hatcher’s recursive coning by induction on m. For m=1
the unique prefix barycenter is v₀, matching Hatcher’s n=0 identity construction. For m≥2, a
permutation σ determines the omitted vertex a=σ(m−1). The first m−1 entries form an ordering of
the opposite face indexed by Fin m minus a; their prefixes are precisely a child of that face by
the induction hypothesis. The final prefix barycenter b^σ_{m−1} is the full barycenter. Thus the
prefix child is the cone from the full barycenter on that opposite-face child. Conversely, an
omitted index a together with a permutation of its m−1 remaining indices determines exactly one
full ordering by appending a. The order of the cone vertices differs from Hatcher’s
[b,w₀,...,w_{n−1}] by moving b to the end, which does not change their convex hull. This is an
explicit deletion/append correspondence; no removed recursive-adapter node is invoked. Each child
has m=n+1 indexed vertices; only for affinely independent original vertices are these genuine
geometric n-simplices.

BC5. Induct on depth r. Depth0 has the original hull. If the depth-r union equals that hull,
replace each depth-r hull by the union of its one-step prefix child hulls using BC3. Taking the
finite unions gives the same hull at depth(r+1). All indexing families are finite (permutations of
a finite type at each of finitely many depths), so this equality applies to every actual tuple and
does not select inconsistent children. Equivalently a point chooses one child at each step and a
path of length r; reverse containment follows from the one-step containment at every step. By BC4
these are Hatcher’s recursively coned subdivision hulls. The induction also covers an empty tuple
and all degenerate child tuples.

BC6. For an injective face embedding α:Fin ℓ→Fin m, use the restricted tuple v∘α. Its barycenters
are the averages of the same chosen original entries α(j); normalized coordinate weights are
extended by zero on indices outside the face. Apply BC1–BC5 with ℓ in place of m to obtain the
identical one-step and finite-depth coverage statements on that face tuple. When ℓ=0 the hull and
all child hulls are empty; when ℓ=1 the hull and its subdivisions are the same singleton. For the
standard simplex, a full child intersects the coordinate face supported on F=range α in the hull
of just those prefix barycenters whose prefix lies in F: writing a point as Σ_k c_k β^σ_k with
c_k≥0, every outside coordinate is a sum of nonnegative c_k/(k+1), so it vanishes exactly when
every coefficient with an outside-containing prefix vanishes. Face orderings extend to full
orderings by appending the complementary indices. This explains the source boundary restriction on
the standard simplex, where faces have their stated dimensions. For degenerate v the asserted
conclusion is the coverage of v∘α; it does not identify geometric intersections with hull(v∘α),
which need not hold under a noninjective affine image.

BC7. Tied sorted coordinates have zero corresponding drop coefficient, so boundaries between
permutation chambers remain covered with no strict sorting requirement; terminal zero coordinates
behave the same way. If m=1, t₀=1, c₀=1 and the unique child is [v₀] at every depth. If vertex
values repeat or their affine span has dimension less than m−1, the same normalized sums and
affine image proof give hull coverage, but the cells may have lower affine dimension and
overlapping interiors. There is no rank or nondegeneracy assumption hidden in the hull equality.
-/
theorem barycentric_subdivision_coverage
    {E : Type u} [AddCommGroup E] [Module ℝ E] (m : ℕ) (v : Fin m → E) :
    let child : ∀ l : ℕ, (Fin l → E) → Equiv.Perm (Fin l) → Fin l → E :=
      fun l w σ k ↦ (Finset.univ.filter (fun j : Fin l ↦ j ≤ k)).centroid ℝ (w ∘ σ)
    (convexHull ℝ (range v) =
      ⋃ σ : Equiv.Perm (Fin m), convexHull ℝ (range (child m v σ))) ∧
    (∀ r : ℕ, convexHull ℝ (range v) =
      ⋃ p : {p : List (Equiv.Perm (Fin m)) // p.length = r},
        convexHull ℝ (range (p.val.foldl (child m) v))) ∧
    (∀ (l : ℕ) (a : Fin l ↪ Fin m),
      (convexHull ℝ (range (v ∘ a)) =
        ⋃ σ : Equiv.Perm (Fin l), convexHull ℝ (range (child l (v ∘ a) σ))) ∧
      (∀ r : ℕ, convexHull ℝ (range (v ∘ a)) =
        ⋃ p : {p : List (Equiv.Perm (Fin l)) // p.length = r},
          convexHull ℝ (range (p.val.foldl (child l) (v ∘ a))))) := by
  let child : ∀ l : ℕ, (Fin l → E) → Equiv.Perm (Fin l) → Fin l → E :=
    fun l w σ k ↦ (Finset.univ.filter (fun j : Fin l ↦ j ≤ k)).centroid ℝ (w ∘ σ)
  have hstep (l : ℕ) (w : Fin l → E) :
      convexHull ℝ (range w) =
        ⋃ σ : Equiv.Perm (Fin l), convexHull ℝ (range (child l w σ)) :=
    one_step_coverage l w
  have hdepth (l : ℕ) (w : Fin l → E) (r : ℕ) :
      convexHull ℝ (range w) =
        ⋃ p : {p : List (Equiv.Perm (Fin l)) // p.length = r},
          convexHull ℝ (range (p.val.foldl (child l) w)) :=
    foldl_cover_of_one_step (fun t : Fin l → E ↦ convexHull ℝ (range t))
      (child l) (hstep l) w r
  exact ⟨hstep m v, hdepth m v, fun l a ↦ ⟨hstep l (v ∘ a), hdepth l (v ∘ a)⟩⟩

end HolomorphicAnosov.BarycentricGeometry
