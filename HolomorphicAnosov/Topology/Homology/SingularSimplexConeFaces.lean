import HolomorphicAnosov.Topology.Homology.SingularSimplexCone

/-!
# Faces of the literal singular simplex cone

Source: Bredon, Topology and Geometry (1993), IV15.5, pp.219–220.
The cone's zeroth face is the original simplex; a positive face is the cone
of the corresponding face. The formulas include the apex and dimension zero.
-/

noncomputable section
open Convexity
namespace HolomorphicAnosov.SingularConvexCone

/-- The zeroth face of Bredon's cone is the original simplex.
Source: Bredon IV15.5 p.219. Inserting zero as the first coordinate sets the
apex coefficient to zero. The normalized remainder equals the original weights,
so the convex combination is the original simplex value. -/
theorem simplexConeRaw_face_zero {n r : ℕ} (o : Simplex r) (σ : C(Simplex n, Simplex r))
    (z : Simplex n) :
    simplexConeRaw o σ
      (Convexity.StdSimplex.map (Fin.succAbove (0 : Fin (n + 2))) z) = σ z := by
  have hzero :
      (Convexity.StdSimplex.map (Fin.succAbove (0 : Fin (n + 2))) z).weights 0 = 0 := by
    simp [Convexity.StdSimplex.map, Finsupp.mapDomain]
  rw [simplexConeRaw]
  have hlt : (Convexity.StdSimplex.map (Fin.succAbove (0 : Fin (n + 2))) z).weights 0 < 1 := by
    rw [hzero]
    norm_num
  rw [dite_eq_left hlt]
  have hrest : normalizedRest
      (Convexity.StdSimplex.map (Fin.succAbove (0 : Fin (n + 2))) z) hlt = z := by
    apply Convexity.StdSimplex.weights_inj.mp
    ext i
    classical
    simp [normalizedRest, Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply]
    by_cases hi : z.weights i = 0 <;> simp [hi]
  rw [hrest]
  apply Convexity.StdSimplex.ext
  ext i
  simp [Finsupp.mapDomain]

/-- A positive face of Bredon's cone is the cone of the preceding face.
Source: Bredon IV15.5 pp.219–220. Inserting zero at vertex i+1 preserves the
zeroth weight. Off the apex, normalization commutes with this insertion:
the omitted coordinate is zero on both sides, and every other coordinate is
the same original weight divided by 1-t₀. At the apex both formulas return o.
Substitution into the literal convex combination proves the identity. -/
theorem simplexConeRaw_face_succ {n r : ℕ} (o : Simplex r)
    (σ : C(Simplex (n + 1), Simplex r)) (i : Fin (n + 2)) (t : Simplex (n + 1)) :
    simplexConeRaw o σ (StdSimplex.map i.succ.succAbove t) =
      simplexConeRaw o
        (σ.comp ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩) t := by
  have h0 : (StdSimplex.map i.succ.succAbove t).weights 0 = t.weights 0 := by
    rw [StdSimplex.weights_map]
    have h0 : i.succ.succAbove 0 = 0 := by simp
    rw [← h0, Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]
  by_cases ht : t.weights 0 < 1
  · have hf : (StdSimplex.map i.succ.succAbove t).weights 0 < 1 := by rwa [h0]
    have hrest : normalizedRest (StdSimplex.map i.succ.succAbove t) hf =
        StdSimplex.map i.succAbove (normalizedRest t ht) := by
      apply StdSimplex.ext
      ext j
      induction j using Fin.succAboveCases i with
      | p j =>
        change (t.weights.mapDomain i.succ.succAbove) (i.succAbove j).succ /
          (1 - (StdSimplex.map i.succ.succAbove t).weights 0) =
          ((normalizedRest t ht).weights.mapDomain i.succAbove) (i.succAbove j)
        rw [← Fin.succ_succAbove_succ, h0,
          Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective,
          Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]
        rfl
      | x =>
        change (t.weights.mapDomain i.succ.succAbove) i.succ /
          (1 - (StdSimplex.map i.succ.succAbove t).weights 0) =
          ((normalizedRest t ht).weights.mapDomain i.succAbove) i
        rw [Finsupp.mapDomain_of_notMem_range _ _ (by
          rintro ⟨a, ha⟩; exact Fin.succAbove_ne _ _ ha),
          Finsupp.mapDomain_of_notMem_range _ _ (by
          rintro ⟨a, ha⟩; exact Fin.succAbove_ne _ _ ha), zero_div]
    
    simp only [simplexConeRaw, dite_eq_left hf, dite_eq_left ht,
      ContinuousMap.comp_apply]
    rw [hrest]
    congr 1; simp only [h0]
  · have hf : ¬ (StdSimplex.map i.succ.succAbove t).weights 0 < 1 := by rwa [h0]
    simp only [simplexConeRaw, dite_eq_right hf, dite_eq_right ht]

end HolomorphicAnosov.SingularConvexCone

