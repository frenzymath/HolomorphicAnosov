import HolomorphicAnosov.Topology.BarycentricIteratedMeshDefs
import HolomorphicAnosov.Topology.BarycentricNestedPrefixContraction
import HolomorphicAnosov.Topology.BarycentricHullDiameter
import Mathlib.Analysis.Convex.Combination

/-!
# Iterated affine barycentric mesh contraction

Source: Hatcher, *Algebraic Topology*, Proposition 2.21 proof (1), printed pp.119–121.
The proof uses finite centroid averages, affine hull containment, and list induction.
-/

noncomputable section

namespace HolomorphicAnosov.BarycentricMesh

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- Let n∈ℕ, let V be a real normed vector space, and let E be a nonempty normed affine space over
V, with distance dist(a,b)=||a−ᵥb||. Let v:Fin(n+1)→E be a vertex tuple, allowing repetitions. For a
permutation σ of Fin(n+1) define childVertices(v,σ)(k) to be the barycenter (1/(k+1))∑_{j=0}^k
v(σ(j)) of its first k+1 vertices, interpreted as an affine combination. For a finite list p of such
permutations define I(v,[]) = v and I(v,σ::p) = I(childVertices(v,σ),p). Write H(w) for the real
convex hull of the range of a tuple w and q=n/(n+1)∈ℝ. Every child hull H(childVertices(w,σ)) lies
in H(w), and H(I(v,p)) lies in H(v). If D∈ℝ satisfies dist(v(i),v(j))≤D for all i,j, then for every
list p and every i,j, dist(I(v,p)(i),I(v,p)(j))≤q^{length(p)}D, and diam(H(I(v,p)))≤q^{length(p)}D.
For n=0 every child tuple is unchanged and every hull is a singleton of diameter zero. The empty
path gives the original tuple and uses q^0=1, including n=0. No affine-independence, distinctness,
finite-dimensionality or completeness assumption is required.

Source: Hatcher, Algebraic Topology, Proposition 2.21 proof part (1), printed pp.119–121: recursive
coning definition pp.119–120, convex-combination diameter inequality and n/(n+1) estimate p.120,
shape-independent iteration p.121. The same finite norm and affine-combination calculations give the
stated real normed-affine-space generality.

Natural-language proof:

Choose an origin a∈E, for example v(0), and identify E isometrically with V by x↦x−ᵥa. A barycenter
of m≥1 indexed points has coordinate m^{-1}Σ_i(x_i−ᵥa); normalization of the centroid weights makes
this independent of the chosen origin. Thus prove the estimates in V and translate back. Every
prefix has k+1≥1 indices; its equal weights are nonnegative and sum to one. The index set, rather
than the set of distinct positions, defines the barycenter, so repeated positions keep their
multiplicities. To apply the finite physical-vertex weighted-sum theorem, group the equal positions
and add their weights; their total weight remains one.

Each prefix barycenter is a convex combination of points of range(w), hence is in H(w) by the
weighted-sum characterization. H(w) is convex and contains the entire child vertex range, so
convexHull_min gives H(childVertices(w,σ))⊆H(w). Induction on a list, composing this one-step
inclusion with the tail inclusion, gives H(I(v,p))⊆H(v). No subdivision-coverage or geometric
independence theorem is used.

Since Fin(n+1) is nonempty, use i=j=0 in the given pairwise bound to obtain 0≤D. Whenever original
vertices are bounded pairwise by D, convexHull_exists_dist_ge2 with both sets equal to their range
bounds the distance between any two points of their hull by the distance between two original
vertices, hence by D. The norm calculation behind this primitive is precisely Hatcher p.120: for
normalized nonnegative weights t_i, ||x−Σt_i v_i||=||Σt_i(x−v_i)||≤Σt_i||x−v_i||≤max_i||x−v_i||.
Thus hull points are compared with vertices, not identified with vertices.

For the one-step vertex bound use `child_vertices_dist_le_ratio`. For two prefixes,
order their indices i≤j. Every vertex of the i-prefix occurs in the j-prefix. Apply
the centroid average inequality to the j-prefix against each such vertex. The matching
index contributes distance zero; the other card(j-prefix)−1 terms contribute at most D
each. Apply the centroid average inequality again over the i-prefix. This bounds the
two centroid distance by ((card(j-prefix)−1)/card(j-prefix))D, at most (n/(n+1))D
since the prefix has between 1 and n+1 indices and D≥0. Symmetry handles the other
index order. This finite normalized-combination calculation includes n=0 directly.

Fix n and induct on p while generalizing the parent tuple and its bound D. For p=[] the tuple is
unchanged and q^0D=D. For σ::p, the public one-step bound gives every child vertex pair the bound qD, which is
nonnegative since q≥0 and D≥0. Apply the tail induction hypothesis to that exact child tuple and
bound qD, obtaining q^{length(p)}(qD)=q^{length(p)+1}D by natural-power multiplication. The length
of σ::p is length(p)+1. The fixed n, hence the same q, is retained throughout the shape changes.
This proves the vertex-pair estimate for every path.

Set w=I(v,p) and C=q^{length(p)}D≥0. Given x,y∈H(w), convexHull_exists_dist_ge2 chooses actual
entries w(i),w(j) with dist(x,y)≤dist(w(i),w(j)); M7 bounds the latter by C. Apply
Metric.diam_le_of_forall_dist_le with this nonnegative C to obtain diam(H(w))≤C. The statement uses
no assertion that hull points are vertices and no unsupported finite-diameter convention. For n=0
all iterates are the original singleton: the empty path has bound D and positive-length paths have
bound zero; 0^0=1 in the empty case. Zero D and repeated vertices cause no division by D and require
no extra nondegeneracy assumptions. -/
theorem iterated_mesh_contraction (n : ℕ) (v : Fin (n + 1) → E) :
    (∀ (w : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))),
      hull (childVertices w σ) ⊆ hull w) ∧
    (∀ p : List (Equiv.Perm (Fin (n + 1))), hull (iteratedVertices v p) ⊆ hull v) ∧
    (∀ D : ℝ, (∀ i j : Fin (n + 1), dist (v i) (v j) ≤ D) →
      ∀ p : List (Equiv.Perm (Fin (n + 1))),
        (∀ i j : Fin (n + 1),
          dist (iteratedVertices v p i) (iteratedVertices v p j) ≤
            ((n : ℝ) / ((n : ℝ) + 1)) ^ p.length * D) ∧
        Metric.diam (hull (iteratedVertices v p)) ≤
          ((n : ℝ) / ((n : ℝ) + 1)) ^ p.length * D) ∧
    (n = 0 →
      (∀ σ : Equiv.Perm (Fin (n + 1)), childVertices v σ = v) ∧
      (∀ p : List (Equiv.Perm (Fin (n + 1))),
        iteratedVertices v p = v ∧
        hull (iteratedVertices v p) = {v 0} ∧
        Metric.diam (hull (iteratedVertices v p)) = 0)) ∧
    (iteratedVertices v [] = v ∧ ((n : ℝ) / ((n : ℝ) + 1)) ^ (0 : ℕ) = 1) := by
  have hchild : ∀ (w : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))),
      hull (childVertices w σ) ⊆ hull w := by
    intro w σ x hx
    let s (k : Fin (n+1)) : Finset (Fin (n+1)) :=
      Finset.univ.filter (fun j ↦ j ≤ k)
    have hs (k : Fin (n+1)) : (s k).Nonempty := by
      exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩⟩
    let fp : V →ᵃ[ℝ] E :=
      AffineMap.mk' (fun z ↦ z +ᵥ w 0) LinearMap.id 0 (by intro z; simp)
    let c0 : E := childVertices w σ 0
    let fc : V →ᵃ[ℝ] E :=
      AffineMap.mk' (fun z ↦ z +ᵥ c0) LinearMap.id 0 (by intro z; simp)
    let g : V →ᵃ[ℝ] V :=
      AffineMap.mk' (fun z ↦ z + (c0 -ᵥ w 0)) LinearMap.id 0 (by intro z; simp)
    rcases hx with ⟨z, hz, rfl⟩
    change fc z ∈ hull w
    have hfg : (fc : V → E) = (fp : V → E) ∘ (g : V → V) := by
      funext z
      change z +ᵥ c0 = (z + (c0 -ᵥ w 0)) +ᵥ w 0
      rw [show c0 = (c0 -ᵥ w 0) +ᵥ w 0 by simp, ← vadd_vadd]
      simp
    rw [show fc z = fp (g z) by rw [hfg]; rfl]
    refine ⟨g z, ?_, rfl⟩
    have hz' : g z ∈ g '' convexHull ℝ (Set.range
        (fun i ↦ childVertices w σ i -ᵥ c0)) := ⟨z, hz, rfl⟩
    rw [g.image_convexHull] at hz'
    have hsub : g '' Set.range (fun i ↦ childVertices w σ i -ᵥ c0) ⊆
        convexHull ℝ (Set.range (fun i ↦ w i -ᵥ w 0)) := by
      intro y hy
      rcases hy with ⟨u, ⟨i, rfl⟩, rfl⟩
      change (childVertices w σ i -ᵥ c0) + (c0 -ᵥ w 0) ∈ _
      rw [vsub_add_vsub_cancel]
      change (s i).centroid ℝ (fun j ↦ w (σ j)) -ᵥ w 0 ∈ _
      rw [Finset.centroid_vsub_const ℝ (s i) (hs i)]
      rw [(s i).centroid_eq_centerMass (hs i)]
      apply Finset.centerMass_mem_convexHull
      · intro j hj
        simp [Finset.centroidWeights_apply]
      · rw [(s i).sum_centroidWeights_eq_one_of_nonempty ℝ (hs i)]
        norm_num
      · intro j hj
        exact ⟨σ j, rfl⟩
    exact (convexHull_min hsub (convex_convexHull ℝ _)) hz'
  have hiter : ∀ p : List (Equiv.Perm (Fin (n + 1))),
      hull (iteratedVertices v p) ⊆ hull v := by
    intro p
    induction p generalizing v with
    | nil => simp [iteratedVertices]
    | cons σ p ih =>
        rw [iteratedVertices]
        exact (ih (v := childVertices v σ)).trans (hchild v σ)
  refine ⟨hchild, hiter, ?_, ?_, ?_⟩
  · intro D hD p
    have hpair : ∀ (w : Fin (n + 1) → E) (D : ℝ),
        (∀ i j, dist (w i) (w j) ≤ D) →
        ∀ p : List (Equiv.Perm (Fin (n + 1))),
          ∀ i j, dist (iteratedVertices w p i) (iteratedVertices w p j) ≤
            ((n : ℝ) / ((n : ℝ) + 1)) ^ p.length * D := by
      intro w D hD p
      induction p generalizing w D with
      | nil =>
          intro i j
          simpa [iteratedVertices] using hD i j
      | cons σ p ih =>
          have hc := child_vertices_dist_le_ratio w σ D hD
          have hchildD : ∀ i j,
              dist (childVertices w σ i) (childVertices w σ j) ≤
                ((n : ℝ) / ((n : ℝ) + 1)) * D := hc
          have htail := ih (w := childVertices w σ)
            (D := ((n : ℝ) / ((n : ℝ) + 1)) * D) hchildD
          intro i j
          simpa [iteratedVertices, pow_succ, mul_assoc, mul_left_comm,
            mul_comm] using htail i j
    refine ⟨hpair v D hD p, ?_⟩
    exact hull_diam_le_of_vertex_dist (iteratedVertices v p)
      (((n : ℝ) / ((n : ℝ) + 1)) ^ p.length * D)
      (hpair v D hD p)
  · intro hn
    subst n
    constructor
    · intro σ
      funext k
      have hk : k = 0 := Fin.eq_zero k
      subst k
      rw [childVertices]
      simp [Finset.centroid_singleton, Fin.eq_zero (σ 0)]
    · intro p
      have hp : iteratedVertices v p = v := by
        induction p with
        | nil => rfl
        | cons σ p ih =>
            simp only [iteratedVertices]
            rw [show childVertices v σ = v by
              funext k
              have hk : k = 0 := Fin.eq_zero k
              subst k
              rw [childVertices]
              simp [Finset.centroid_singleton, Fin.eq_zero (σ 0)]]
            exact ih
      refine ⟨hp, ?_, ?_⟩
      · rw [hp]
        rw [hull]
        have hv : Set.range (fun i : Fin (0 + 1) ↦ v i -ᵥ v 0) = {0} := by
          ext z
          constructor
          · rintro ⟨i, rfl⟩
            simp [Fin.eq_zero i]
          · intro hz
            simp only [Set.mem_singleton_iff] at hz
            subst z
            exact ⟨0, by simp⟩
        rw [hv]
        simp
      · rw [hull]
        have hv : Set.range (fun i : Fin (0 + 1) ↦ v i -ᵥ v 0) = {0} := by
          ext z
          constructor
          · rintro ⟨i, rfl⟩
            simp [Fin.eq_zero i]
          · intro hz
            simp only [Set.mem_singleton_iff] at hz
            subst z
            exact ⟨0, by simp⟩
        rw [show iteratedVertices v p = v by exact hp]
        rw [hv]
        simp
  · simp [iteratedVertices]

end HolomorphicAnosov.BarycentricMesh
