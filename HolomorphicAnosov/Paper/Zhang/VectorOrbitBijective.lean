import HolomorphicAnosov.Geometry.Biholomorph

/-! Bijectivity of orbit maps for free transitive vector actions. (Zhang, p. 13) -/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

/-- The orbit map of a free transitive vector action is bijective. (Zhang, Thm 3.3, p. 13) -/
theorem vector_orbit_bijective
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (A : V → Biholomorph d d M M)
    (hzero : ∀ x : M, A 0 x = x)
    (hadd : ∀ (a b : V) (x : M), A (a + b) x = A a (A b x))
    (hfree : ∀ (a : V) (x : M), A a x = x → a = 0)
    (htransitive : ∀ x y : M, ∃ a : V, A a x = y) (x0 : M) :
    Function.Bijective (fun a : V ↦ A a x0) := by
  constructor
  · intro a b hab
    have hx : A (a - b) x0 = x0 := by
      calc
        A (a - b) x0 = A (-b) (A a x0) := by rw [sub_eq_add_neg, add_comm, hadd]
        _ = A (-b) (A b x0) := congrArg (A (-b)) hab
        _ = x0 := by rw [← hadd, neg_add_cancel, hzero]
    exact sub_eq_zero.mp (hfree (a - b) x0 hx)
  · exact htransitive x0


end HolomorphicAnosov
