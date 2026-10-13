import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic

noncomputable section
open Set

namespace HolomorphicAnosov

/-- Two geometric simplicial complexes whose overlap is covered by a common
subcomplex have compatible cross-complex faces. Source: Schultz, Mathematics
205B, §IV.2 Lemma 6 and its written proof, printed p.51.

For a point in the intersection of two face hulls, choose a face of the common
subcomplex containing it. Intersect that face with each of the original faces,
using the intersection axiom in the respective complexes. Both resulting vertex
sets lie in the chosen common face and are therefore affinely independent
together. Their hull intersection is the hull of their common vertices. These
vertices belong to both original faces, giving the desired inclusion. This is
the convex-combination argument in Schultz's proof, with an explicit common
face chosen for each point. Empty overlap and empty common subcomplex are
allowed: in those cases the point assumption is impossible. No finiteness of
the whole complexes or ambient dimension is needed by this proof. -/
theorem common_subcomplex_convexHull_inter_subset {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K L J : Geometry.SimplicialComplex ℝ E)
    (hJK : J.faces ⊆ K.faces) (hJL : J.faces ⊆ L.faces)
    (hcover : K.space ∩ L.space ⊆ J.space)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ t) := by
  classical
  intro x hx
  obtain ⟨u, hu, hxu⟩ := Geometry.SimplicialComplex.mem_space_iff.mp
    (hcover ⟨Geometry.SimplicialComplex.convexHull_subset_space hs hx.1,
      Geometry.SimplicialComplex.convexHull_subset_space ht hx.2⟩)
  have hxs := K.inter_subset_convexHull hs (hJK hu) ⟨hx.1, hxu⟩
  have hxt := L.inter_subset_convexHull ht (hJL hu) ⟨hx.2, hxu⟩
  have hi := (J.indep hu).convexHull_inter
    (Finset.inter_subset_right : s ∩ u ⊆ u)
    (Finset.inter_subset_right : t ∩ u ⊆ u)
  have hxcommon : x ∈ convexHull ℝ
      (((s ∩ u : Finset E) : Set E) ∩ ((t ∩ u : Finset E) : Set E)) := by
    rw [hi]
    simpa only [Finset.coe_inter, Set.mem_inter_iff] using And.intro hxs hxt
  have hsub : (((s ∩ u : Finset E) : Set E) ∩ ((t ∩ u : Finset E) : Set E)) ⊆
      ((s : Set E) ∩ t) := fun _ hy ↦
    ⟨(Finset.mem_inter.mp hy.1).1, (Finset.mem_inter.mp hy.2).1⟩
  exact convexHull_mono hsub hxcommon

end HolomorphicAnosov

