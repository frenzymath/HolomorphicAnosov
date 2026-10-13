import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.CharacteristicDiskSkeletalApproximation
import HolomorphicAnosov.Topology.CWComplex.GlueBoundaryFixedCellHomotopies
import HolomorphicAnosov.Topology.CWComplex.SubcomplexUnion

namespace HolomorphicAnosov

/-- One cellular skeletal deformation on A union the n-skeleton, stationary
on A and the lower skeleton. Source: Hatcher Theorem 4.8, p.349. Form the union
subcomplex. Deform its n-cells by relative characteristic-disk approximation,
fixing the preimage of A and the lower skeleton; leave all other cells constant.
Every characteristic frontier lies in that fixed set. The cell deformations
therefore respect all attaching identifications and glue jointly continuously.
On lower cells the old cellularity applies, and on cells selected by A the
prescribed cellularity on A applies. Hence the endpoint is cellular on the
n-skeleton, including intersections with higher-dimensional cells of A. -/
theorem cw_cellular_skeletal_homotopy
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (q : C(X, Y))
    (hA : Set.MapsTo q ((A : Set X) ∩
      (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X))
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y))
    (hbelow : ∀ m : ℕ, m < n → Set.MapsTo q
      (Topology.CWComplex.skeleton (Set.univ : Set X) (m : ℕ∞) : Set X)
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (m : ℕ∞) : Set Y)) :
    ∃ B : Topology.CWComplex.Subcomplex (Set.univ : Set X),
      (B : Set X) = (A : Set X) ∪
        (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) ∧
      ∃ H : C(unitInterval × (B : Set X), Y),
        (∀ x, H (0, x) = q x.val) ∧
        (∀ t x, x.val ∈ (A : Set X) ∪
          (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) →
          H (t, x) = q x.val) ∧
        ∀ x, x.val ∈
          (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) →
          H (1, x) ∈
          (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y) := by
  classical
  let S := Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)
  let L := Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞)
  let T := (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)
  let F : Set X := (A : Set X) ∪ (L : Set X)
  obtain ⟨B, hB, hBI⟩ := cw_subcomplex_union (Set.univ : Set X) A S
  have hdim (m : ℕ) (i : B.I m) (hi : i.val ∉ A.I m) : m ≤ n := by
    have hs := (hBI m i.val).mp i.property |>.resolve_left hi
    have hs' : (m : ℕ∞) < (n : ℕ∞) + 1 := by
      simpa only [S, Topology.RelCWComplex.skeleton,
        Topology.RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] using hs
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt] at hs'
    exact Nat.lt_succ_iff.mp hs'
  have hlower : Set.MapsTo q (L : Set X) T := by
    intro x hx
    obtain ⟨m, hm, i, hi⟩ := Topology.CWComplex.mem_skeletonLT_iff.mp hx
    have hmn : m < n := by exact_mod_cast hm
    exact Topology.CWComplex.skeleton_mono (by exact_mod_cast hmn.le)
      (hbelow m hmn (Topology.CWComplex.openCell_subset_skeleton m i hi))
  have hfront (m : ℕ) (i : Topology.RelCWComplex.cell (B : Set X) m) :
      Topology.CWComplex.cellFrontier m i ⊆ F := by
    intro x hx
    by_cases hi : i.val ∈ A.I m
    · exact Or.inl (A.cellFrontier_subset_of_mem hi hx)
    · exact Or.inr (Topology.CWComplex.skeletonLT_mono
        (by exact_mod_cast hdim m i hi)
        (Topology.CWComplex.cellFrontier_subset_skeletonLT m i.val hx))
  have data (m : ℕ) (i : Topology.RelCWComplex.cell (B : Set X) m) :
      ∃ P : C(unitInterval × Metric.closedBall (0 : Fin m → ℝ) 1, Y),
        (∀ z, P (0, z) = q (Topology.RelCWComplex.map m i z.val)) ∧
        (∀ t z, Topology.RelCWComplex.map m i z.val ∈ F →
          P (t, z) = q (Topology.RelCWComplex.map m i z.val)) ∧
        ∀ z, Topology.RelCWComplex.map m i z.val ∈ (S : Set X) → P (1, z) ∈ T := by
    let f : C(Metric.closedBall (0 : Fin m → ℝ) 1, Y) :=
      ⟨fun z ↦ q (Topology.RelCWComplex.map m i z.val),
        q.continuous.comp (Topology.RelCWComplex.continuousOn m i).domRestrict⟩
    by_cases hmn : m = n
    · subst m
      obtain ⟨r, hr, ⟨H⟩⟩ := cw_characteristic_disk_skeletal_approximation n
        {z | Topology.RelCWComplex.map n i z.val ∈ F} f (by
          intro z hz
          rcases hz with hz | hz
          · exact hA ⟨hz, Topology.CWComplex.closedCell_subset_skeleton n i.val
              ⟨z.val, z.property, rfl⟩⟩
          · exact hlower hz)
      exact ⟨H.toContinuousMap, H.map_zero_left,
        fun t z hz ↦ H.eq_fst t hz, fun z _ ↦ by change H.toFun (1, z) ∈ T; rw [H.map_one_left]; exact hr ⟨z, rfl⟩⟩
    · refine ⟨⟨fun z ↦ f z.2, f.continuous.comp continuous_snd⟩,
        fun _ ↦ rfl, fun _ _ _ ↦ rfl, ?_⟩
      intro z hz
      by_cases hi : i.val ∈ A.I m
      · exact hA ⟨A.closedCell_subset_of_mem hi ⟨z.val, z.property, rfl⟩, hz⟩
      · have hmn' : m < n := lt_of_le_of_ne (hdim m i hi) hmn
        exact Topology.CWComplex.skeleton_mono (by exact_mod_cast hmn'.le)
          (hbelow m hmn' (Topology.CWComplex.closedCell_subset_skeleton m i.val
            ⟨z.val, z.property, rfl⟩))
  choose P hzero hfix hend using data
  obtain ⟨H, hzero, hfixed, hend⟩ := cw_glue_boundary_fixed_cell_homotopies
    (B : Set X) F (S : Set X) T q hfront P hzero hfix hend
  exact ⟨B, hB, H, hzero, hfixed, hend⟩

end HolomorphicAnosov
