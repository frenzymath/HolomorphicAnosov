import Mathlib.Topology.TietzeExtension

namespace HolomorphicAnosov

/-- Continuous real-valued maps on closed subsets of a normal space extend to the ambient
space. This is the exact Tietze extension input used in the closed-adjunction normality
argument.

Source: Mathlib `ContinuousMap.exists_restrict_eq_forall_mem_of_closed`, implementing the
Tietze extension theorem; Fritsch--Piccinini, *Cellular Structures in Topology* (1990),
Appendix A.4, pp.260--261.
-/
theorem exists_continuous_real_extension_of_closed
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    (s : Set X) (hs : IsClosed s) (f : C(s, ℝ)) :
    ∃ g : C(X, ℝ), g.restrict s = f := by
  simpa using
    (ContinuousMap.exists_restrict_eq_forall_mem_of_closed f
      (t := Set.univ) (fun _ => Set.mem_univ _) Set.univ_nonempty hs)

end HolomorphicAnosov
