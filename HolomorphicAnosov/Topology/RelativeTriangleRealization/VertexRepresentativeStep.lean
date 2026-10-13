import HolomorphicAnosov.Topology.RelativeTriangleRealization.FaceBoundaryVertex

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-- A paired-face generator preserves the property of being represented by a
triangle vertex. If a point `(i, single v)` is identified with a point on a
paired face `(o.1, face o.2 t)`, then that face parameter is an endpoint of the
ordered edge, so the paired point is again a triangle vertex.

Source: Hatcher, Algebraic Topology, pp.103--104 and p.167. The source uses
this endpoint-stratum fact implicitly when passing from face identifications
to the vertex classes. -/
theorem vertex_representative_step {m : ℕ}
    (pair : Occurrence m → Occurrence m)
    {a b : Fin m × Simplex 2}
    (hab : pointRelation pair a b)
    (ha : ∃ w : Fin m × Fin 3,
      a = (w.1, Convexity.StdSimplex.single w.2)) :
    ∃ w : Fin m × Fin 3,
      b = (w.1, Convexity.StdSimplex.single w.2) := by
  obtain ⟨o, t, haeq, hbeq⟩ := hab
  obtain ⟨w, haw⟩ := ha
  have hface : face o.2 t = Convexity.StdSimplex.single w.2 := by
    have hs := congrArg Prod.snd (haeq.symm.trans haw)
    exact hs
  have hnot : ¬ t ∈ interior 1 := by
    intro ht
    have hz : (face o.2 t).weights o.2 = 0 := by
      change t.weights.mapDomain o.2.succAbove o.2 = 0
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨a, ha⟩
      exact o.2.succAbove_ne a ha
    have hwne : w.2 ≠ o.2 := by
      intro hwo
      have hwo' : w.2 = o.2 := hwo
      have hh := congrArg (fun z : Simplex 2 => z.weights o.2) hface
      rw [hz] at hh
      have : (0 : ℝ) = 1 := by simp [hwo'] at hh
      linarith
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hwne
    fin_cases k
    · have hh := congrArg (fun z : Simplex 2 => z.weights (o.2.succAbove 1)) hface
      have hp := ht 1
      rw [← hk] at hh
      change t.weights.mapDomain o.2.succAbove _ = _ at hh
      rw [Finsupp.mapDomain_apply_of_injective o.2.succAbove_right_injective] at hh
      simp at hh
      linarith
    · have hh := congrArg (fun z : Simplex 2 => z.weights (o.2.succAbove 0)) hface
      have hp := ht 0
      rw [← hk] at hh
      change t.weights.mapDomain o.2.succAbove _ = _ at hh
      rw [Finsupp.mapDomain_apply_of_injective o.2.succAbove_right_injective] at hh
      simp at hh
      linarith
  obtain ⟨w', hw'⟩ := face_boundary_vertex (j := o.2) hnot
  have hwne : w' ≠ o.2 := by
    intro hwo
    subst w'
    have hz : (face o.2 t).weights o.2 = 0 := by
      change t.weights.mapDomain o.2.succAbove o.2 = 0
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨a, ha⟩
      exact o.2.succAbove_ne a ha
    have hh := congrArg (fun z : Simplex 2 => z.weights o.2) hw'
    rw [hz] at hh
    simp at hh
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hwne
  have hinj (u v : Simplex 1) (h : face o.2 u = face o.2 v) : u = v := by
    apply Convexity.StdSimplex.ext
    have hh := congrArg Convexity.StdSimplex.weights h
    exact Finsupp.mapDomain_injective o.2.succAbove_right_injective hh
  have ht : t = Convexity.StdSimplex.single k := by
    apply hinj
    have hwface : face o.2 (Convexity.StdSimplex.single k) =
        Convexity.StdSimplex.single w' := by
      change Convexity.StdSimplex.map o.2.succAbove (Convexity.StdSimplex.single k) = _
      rw [Convexity.StdSimplex.map_single, hk]
    have hww : w.2 = w' := Convexity.StdSimplex.single_injective
      (hface.symm.trans hw')
    rw [← hww] at hwface
    exact hface.trans hwface.symm
  refine ⟨((pair o).1, (pair o).2.succAbove k), ?_⟩
  rw [hbeq, ht]
  apply Prod.ext
  · rfl
  · change Convexity.StdSimplex.map (pair o).2.succAbove
      (Convexity.StdSimplex.single k) = _
    rw [Convexity.StdSimplex.map_single]


end HolomorphicAnosov.RelativeTriangleRealization
