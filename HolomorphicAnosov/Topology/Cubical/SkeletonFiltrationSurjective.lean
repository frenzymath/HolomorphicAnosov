import HolomorphicAnosov.Topology.Cubical.RationalSingularHomologyInclusion
import HolomorphicAnosov.Topology.Cubical.SkeletonCarrierSubset

noncomputable section
open CategoryTheory
namespace HolomorphicAnosov.Cubical

lemma subcomplex_skeleton_monotone {N : ℕ} {K : FiniteRectilinearSubdivision N}
    (M : CubicalSubcomplex K) : Monotone M.skeleton := by
  intro a b hab x hx
  simp only [CubicalSubcomplex.skeleton, Set.mem_iUnion] at hx ⊢
  obtain ⟨c, hc, hd, hx⟩ := hx
  exact ⟨c, hc, hd.trans hab, hx⟩

lemma rationalSingularHomologyInclusion_comp {N : ℕ}
    {A B C : Set (Fin N → ℝ)} (hAB : A ⊆ B) (hBC : B ⊆ C) (q : ℕ) :
    rationalSingularHomologyInclusion hAB q ≫ rationalSingularHomologyInclusion hBC q =
      rationalSingularHomologyInclusion (hAB.trans hBC) q := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
    (ModuleCat.of ℚ ℚ)
  change F.map _ ≫ F.map _ = F.map _
  rw [← F.map_comp]
  rfl

lemma rationalSingularHomologyInclusion_self {N : ℕ}
    (A : Set (Fin N → ℝ)) (q : ℕ) (h : A ⊆ A) :
    rationalSingularHomologyInclusion h q = 𝟙 _ := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
    (ModuleCat.of ℚ ℚ)
  change F.map _ = 𝟙 _
  convert F.map_id (TopCat.of A) using 1
  congr 1

/-- Hatcher, Algebraic Topology, Lemma 2.34(b), pp.137–139: compose the
surjections induced by the successive skeleton inclusions. Induction on the
upper skeleton index starts at the identity and composes the next given
surjection with the preceding composite. Functoriality identifies that composite
with the literal inclusion. This finite filtration argument uses no topology
beyond the skeleton inclusions. -/
theorem subcomplex_skeleton_homology_surjective_of_steps {N : ℕ}
    {K : FiniteRectilinearSubdivision N} (M : CubicalSubcomplex K) (q n : ℕ)
    (hqn : q ≤ n)
    (hstep : ∀ m, q ≤ m → m < n → Function.Surjective
      (rationalSingularHomologyInclusion
        (subcomplex_skeleton_monotone M (Nat.le_succ m)) q)) :
    Function.Surjective (rationalSingularHomologyInclusion
      (subcomplex_skeleton_monotone M hqn) q) := by
  induction n, hqn using Nat.le_induction with
  | base =>
    rw [rationalSingularHomologyInclusion_self]
    exact Function.surjective_id
  | succ n hn ih =>
    have hprev := ih (fun m hm hmn ↦ hstep m hm (Nat.lt_succ_of_lt hmn))
    have hnext := hstep n hn (Nat.lt_succ_self n)
    have heq := rationalSingularHomologyInclusion_comp
      (subcomplex_skeleton_monotone M hn)
      (subcomplex_skeleton_monotone M (Nat.le_succ n)) q
    rw [← heq]
    exact hnext.comp hprev

end HolomorphicAnosov.Cubical
