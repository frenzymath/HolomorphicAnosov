import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- Every time slice of a continuous Euclidean homotopy whose total fixed locus is compact has compact fixed set.
Source: Dold (1965), §1.7, pp.1–2.
Proof: Intersect the compact total fixed locus with the closed time slice, then project to the domain. This image equals the fixed set of the slice map, by the defining fixed point equality. -/
theorem homotopy_slice_fixedSet_compact
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (H : C(U × unitInterval, EuclideanSpace ℝ (Fin n)))
    (hH : IsCompact (Set.ofPred (fun p : U × unitInterval ↦ H p = p.1.1)))
    (t : unitInterval) :
    IsCompact (euclideanFixedSet
      (H.comp ⟨fun x ↦ (x, t), continuous_id.prodMk continuous_const⟩)) := by
  have hc := (hH.inter_right
    (isClosed_eq continuous_snd
      (continuous_const : Continuous (fun _ : U × unitInterval ↦ t)))).image
    (continuous_fst : Continuous (Prod.fst : U × unitInterval → U))
  have he : Prod.fst ''
      (Set.ofPred (fun p : U × unitInterval ↦ H p = p.1.1) ∩
        {p : U × unitInterval | p.2 = t}) =
      euclideanFixedSet
        (H.comp ⟨fun x ↦ (x, t), continuous_id.prodMk continuous_const⟩) := by
    ext x
    constructor
    · rintro ⟨⟨y, u⟩, ⟨hfix, hu⟩, rfl⟩
      change u = t at hu
      subst u
      exact hfix
    · intro hx
      exact ⟨(x, t), ⟨hx, rfl⟩, rfl⟩
  rw [he] at hc
  exact hc

end HolomorphicAnosov
