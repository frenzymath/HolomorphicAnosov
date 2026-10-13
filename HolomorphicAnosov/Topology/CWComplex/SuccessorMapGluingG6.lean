import HolomorphicAnosov.Topology.BasedHomotopyUniqueness

namespace HolomorphicAnosov
universe u v

/-- Continuous maps on the new characteristic disks, agreeing with a lower-skeleton
map on the attaching identifications, extend it to the successor skeleton.

Source: Hatcher, Algebraic Topology, Proposition 1B.9 p.91 and Appendix A.2
pp.520–523. The lower skeleton and the new closed cells cover the successor.
Choose representatives in their disjoint union. Two representatives in the lower
skeleton give the prescribed lower value; off that skeleton they lie in a unique
open cell and have a unique characteristic coordinate. Thus all overlaps agree,
even for nonregular attaching maps. Inherited characteristic-map continuity gives
a continuous descended map. Empty cell families and infinite families are allowed.
The proof uses the existing successor-prism compatibility calculation with constant
time parameter. -/
theorem cw_successor_map_gluing_g6
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] (n : ℕ)
    (h : C((Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (B : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1) →
      C(Metric.closedBall (0 : Fin (n + 1) → ℝ) 1, Y))
    (hB : ∀ i z (hx : Topology.RelCWComplex.map (n + 1) i z.val ∈
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
      B i z = h ⟨Topology.RelCWComplex.map (n + 1) i z.val, hx⟩) :
    ∃ h' : C((Topology.CWComplex.skeleton (Set.univ : Set K)
      ((n + 1 : ℕ) : ℕ∞) : Set K), Y),
      ∀ x : (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K),
        h' ⟨x.val, Topology.CWComplex.skeleton_mono
          (by exact_mod_cast Nat.le_succ n) x.property⟩ = h x := by
  classical
  let H : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y) :=
    ⟨fun x ↦ h x.2, h.continuous.comp continuous_snd⟩
  let P (i : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1)) :
      C(unitInterval × Metric.closedBall (0 : Fin (n + 1) → ℝ) 1, Y) :=
    ⟨fun x ↦ B i x.2, (B i).continuous.comp continuous_snd⟩
  have hP : ∀ i t z (hx : Topology.RelCWComplex.map (n + 1) i z.val ∈
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
      P i (t, z) = H (t, ⟨Topology.RelCWComplex.map (n + 1) i z.val, hx⟩) :=
    fun i _ z hx ↦ hB i z hx
  let S : Set K := Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞)
  let S' : Set K := Topology.CWComplex.skeleton (Set.univ : Set K) ((n + 1 : ℕ) : ℕ∞)
  have hSS : S ⊆ S' := Topology.CWComplex.skeleton_mono (by exact_mod_cast Nat.le_succ n)
  let Rep := S ⊕ (Σ i : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1),
    Metric.closedBall (0 : Fin (n + 1) → ℝ) 1)
  let eval : Rep → S' := Sum.elim
    (fun x ↦ ⟨x.val, hSS x.property⟩)
    (fun q ↦ ⟨Topology.RelCWComplex.map (n + 1) q.1 q.2.val,
      Topology.CWComplex.closedCell_subset_skeleton (n + 1) q.1
        ⟨q.2.val, q.2.property, rfl⟩⟩)
  let values : Rep → unitInterval → Y := Sum.elim (fun x t ↦ H (t, x))
    (fun q t ↦ P q.1 (t, q.2))
  have hsurj : Function.Surjective eval := by
    intro x
    have hx : x.val ∈ S ∪ ⋃ i : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1),
        Topology.CWComplex.closedCell (n + 1) i := by
      rw [Topology.CWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ]
      exact x.property
    rcases hx with hx | hx
    · exact ⟨Sum.inl ⟨x.val, hx⟩, Subtype.ext rfl⟩
    · obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
      exact ⟨Sum.inr ⟨i, ⟨z, hz⟩⟩, Subtype.ext hzx⟩
  have hcompat : ∀ r s : Rep, eval r = eval s → ∀ t, values r t = values s t := by
    intro r s heq t
    have he := congrArg Subtype.val heq
    cases r with
    | inl x =>
      cases s with
      | inl y =>
        have hxy : x = y := Subtype.ext he
        rw [hxy]
      | inr q =>
        have hx : Topology.RelCWComplex.map (n + 1) q.1 q.2.val ∈ S := by
          change x.val = Topology.RelCWComplex.map (n + 1) q.1 q.2.val at he
          rw [← he]
          exact x.property
        change H (t, x) = P q.1 (t, q.2)
        rw [hP _ _ _ hx]
        apply congrArg (fun x ↦ H (t, x))
        exact Subtype.ext he
    | inr q =>
      cases s with
      | inl x =>
        have hx : Topology.RelCWComplex.map (n + 1) q.1 q.2.val ∈ S := by
          change Topology.RelCWComplex.map (n + 1) q.1 q.2.val = x.val at he
          rw [he]
          exact x.property
        change P q.1 (t, q.2) = H (t, x)
        rw [hP _ _ _ hx]
        apply congrArg (fun x ↦ H (t, x))
        exact Subtype.ext he
      | inr q' => exact cw_successor_prisms_compatible n H P hP q.1 q'.1 t q.2 q'.2 he
  let choose : S' → Rep := fun x ↦ (hsurj x).choose
  let U : unitInterval × S' → Y := fun q ↦ values (choose q.2) q.1
  have hagree : ∀ r t, U (t, eval r) = values r t := by
    intro r t
    exact hcompat _ _ (hsurj (eval r)).choose_spec t
  have hcont : Continuous U := by
    apply cw_subtype_prism_continuous_of_characteristic S'
    intro m i
    have hi := i.property
    have hi' : (m : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) + 1 := by
      simpa only [Topology.RelCWComplex.skeleton, Topology.RelCWComplex.skeletonLT,
        Topology.RelCWComplex.Subcomplex.mk', Set.mem_ofPred_eq] using hi
    have hm : m < n + 2 := by exact_mod_cast hi'
    by_cases hmn : m ≤ n
    · let χ : C(Metric.closedBall (0 : Fin m → ℝ) 1, S) :=
        ⟨fun z ↦ ⟨Topology.RelCWComplex.map (C := Set.univ) m i.val z.val,
          Topology.CWComplex.skeleton_mono (by exact_mod_cast hmn)
            (Topology.CWComplex.closedCell_subset_skeleton m i.val
              ⟨z.val, z.property, rfl⟩)⟩,
          by
            apply Continuous.subtype_mk
            exact (Topology.RelCWComplex.continuousOn m i.val).domRestrict⟩
      convert H.continuous.comp (continuous_fst.prodMk (χ.continuous.comp continuous_snd)) using 1
      funext q
      exact hagree (Sum.inl (χ q.2)) q.1
    · have hm1 : m = n + 1 := by omega
      subst m
      convert (P i.val).continuous using 1
      funext q
      exact hagree (Sum.inr ⟨i.val, q.2⟩) q.1
  refine ⟨⟨fun x ↦ U (0, x),
    hcont.comp (continuous_const.prodMk continuous_id)⟩, ?_⟩
  intro x
  exact hagree (Sum.inl x) 0

end HolomorphicAnosov
