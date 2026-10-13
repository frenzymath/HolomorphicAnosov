import HolomorphicAnosov.Topology.PathsHomotopicInSimplyConnectedMember
import Mathlib.Topology.Subpath

namespace HolomorphicAnosov

open Set

/-- The finite path-decomposition argument in Hatcher Lemma 1.15, p.35.
Choose paths from one common point to every point, lying in each cover member
which contains that endpoint. Subdivide any loop by the open cover. In each
member its subpath class is the inverse of the first connector followed by the
second connector; consecutive connectors cancel. The whole loop class is the
identity. The connectors also give path connectedness. -/
theorem sphere_simply_connected_of_cover_connectors
    {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUsc : ∀ i, IsSimplyConnected (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (b : X) (r : ∀ x, Path b x)
    (hr : ∀ i x, x ∈ U i → ∀ t, r x t ∈ U i) :
    SimplyConnectedSpace X := by
  classical
  let Q := @Path.Homotopic.Quotient.mk X _
  have hstep {i : ι} {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i) :
      (Q p) = (Q (r x)).symm.trans (Q (r y)) := by
    have hx : x ∈ U i := by simpa using hp 0
    have hy : y ∈ U i := by simpa using hp 1
    have hpath : ((r x).trans p).Homotopic (r y) :=
      sphere_paths_homotopic_in_member (hUsc i) _ _ (fun t ↦ by
        have ht : ((r x).trans p) t ∈ Set.range (r x) ∪ Set.range p := by
          rw [← Path.trans_range]
          exact mem_range_self t
        rcases ht with ⟨s, he⟩ | ⟨s, he⟩
        · exact he ▸ hr i x hx s
        · exact he ▸ hp s) (hr i y hy)
    have heq : (Q (r x)).trans (Q p) = Q (r y) := Path.Homotopic.Quotient.eq.mpr hpath
    calc
      Q p = (Q (r x)).symm.trans ((Q (r x)).trans (Q p)) := by
        simp [← Path.Homotopic.Quotient.trans_assoc]
      _ = (Q (r x)).symm.trans (Q (r y)) := by rw [heq]
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨⟨⟨b⟩, fun x y ↦ ⟨(r x).symm.trans (r y)⟩⟩, ?_⟩
  intro x γ
  obtain ⟨s, hs0, hsmono, ⟨N, hsN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i ↦ (hUopen i).preimage γ.continuous)
      (fun t _ ↦ mem_iUnion.mpr (hcover (γ t)))
  have hpart : ∀ k, Q (γ.subpath (s 0) (s k)) =
      (Q (r (γ (s 0)))).symm.trans (Q (r (γ (s k)))) := by
    intro k
    induction k with
    | zero => simp [Q]
    | succ k ih =>
        obtain ⟨i, hi⟩ := hsub k
        have hp : ∀ t, γ.subpath (s k) (s (k + 1)) t ∈ U i := by
          intro t
          have ht : γ.subpath (s k) (s (k + 1)) t ∈
              γ '' Icc (s k) (s (k + 1)) := by
            rw [← γ.range_subpath_of_le _ _ (hsmono (Nat.le_succ k))]
            exact mem_range_self t
          rcases ht with ⟨a, ha, he⟩
          exact he ▸ hi ha
        change Q (γ.subpath (s 0) (s (k + 1))) = _
        calc
          Q (γ.subpath (s 0) (s (k + 1))) =
              (Q (γ.subpath (s 0) (s k))).trans (Q (γ.subpath (s k) (s (k + 1)))) :=
            (Path.Homotopic.mk_subpath_trans_mk_subpath γ _ _ _).symm
          _ = _ := by
            rw [ih, hstep _ hp]
            simp [Path.Homotopic.Quotient.trans_assoc,
              ← Path.Homotopic.Quotient.trans_assoc (Q (r (γ (s k))))]
  have hfinal := hpart N
  rw [hs0, hsN N le_rfl, Path.subpath_zero_one] at hfinal
  have hcast : (γ.cast γ.source γ.target).Homotopic
      ((Path.refl x).cast γ.source γ.target) := by
    apply Path.Homotopic.Quotient.eq.mp
    have hdiag (a c : X) (ha : a = x) (hc : c = x) :
        (Q (r a)).symm.trans (Q (r c)) = Q ((Path.refl x).cast ha hc) := by
      subst a c
      simp [Q]
    exact hfinal.trans (hdiag _ _ γ.source γ.target)
  convert hcast.pathCast γ.source.symm γ.target.symm using 1 <;> ext t <;> rfl

end HolomorphicAnosov

