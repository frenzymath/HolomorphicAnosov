import HolomorphicAnosov.Topology.Franks.NativePointedSemiconjugacy

namespace HolomorphicAnosov.Topology

/-- The bounded centered correction on the original pullback gives a bounded
uncentered real-coordinate lift. Compose with the explicit inverse coordinate
parametrization and enlarge the bound by the norm of the fixed basepoint.
This is the elementary coordinate step in Franks (1970), Proposition (2.1),
pp. 70–71. -/
theorem bounded_coordinate_lift_of_pullback
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (u0 : OriginalTorusPullback q)
    (k : C(M, UnitAddTorus (Fin n)))
    (H : C(OriginalTorusPullback q, Fin n → ℝ))
    (hproj : ∀ x, coordinateProjection n (H x) = k x.val.1)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖(x.val.2 - u0.val.2) - H x‖ ≤ B) :
    ∃ G : C((Fin n → ℝ), (Fin n → ℝ)),
      (∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖v - G v‖ ≤ K) ∧
      (∀ v, coordinateProjection n (G v) =
        k (q.symm (coordinateProjection n v))) := by
  let P : C((Fin n → ℝ), OriginalTorusPullback q) :=
    ⟨fun v ↦ ⟨(q.symm (originalTorusProjection n v), v), q.apply_symm_apply _⟩,
      ((q.symm.continuous.comp (originalTorusProjection n).continuous).prodMk
        continuous_id).subtype_mk _⟩
  obtain ⟨B, hB, hb⟩ := hbound
  refine ⟨H.comp P, ⟨B + ‖u0.val.2‖, add_nonneg hB (norm_nonneg _), ?_⟩, ?_⟩
  · intro v
    change ‖v - H (P v)‖ ≤ B + ‖u0.val.2‖
    have heq : v - H (P v) = ((v - u0.val.2) - H (P v)) + u0.val.2 := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (hb (P v)) le_rfl)
  · intro v
    exact hproj (P v)

end HolomorphicAnosov.Topology
