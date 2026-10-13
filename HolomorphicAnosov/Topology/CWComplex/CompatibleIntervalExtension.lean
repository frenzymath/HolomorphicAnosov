import Mathlib.Analysis.Complex.Tietze

/-!
# Simultaneous extension of compatible interval maps

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Appendix A.4.8(iv),
pp. 260–261, and A.5.1(iv), p. 274. The closed-union prescription is the
successor step in the compatible extensions on the skeleta.
-/

namespace HolomorphicAnosov.Topology

universe u

/-- Compatible continuous interval maps on two closed subsets of a normal space
have a common continuous extension.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Appendix A.4.8(iv),
pp. 260–261, and A.5.1(iv), p. 274, use this closed-union prescription before
applying Tietze extension.

Proof: define a function on the ambient space by the first prescribed map on `S`,
the second on `T \ S`, and zero elsewhere. Agreement on the overlap makes its
restrictions to both closed sets equal to the prescribed continuous maps.
Closed-set pasting therefore makes its restriction to `S ∪ T` continuous.
The union is closed, so interval-valued Tietze extension extends this restriction
to the whole normal space. Evaluating the restriction equality at points of `S`
and `T` gives both conclusions. This also covers empty sets and an empty ambient
space, without separation assumptions beyond normality. -/
theorem exists_compatible_unitInterval_extension
    {X : Type u} [TopologicalSpace X] [NormalSpace X]
    (S T : Set X) (hS : IsClosed S) (hT : IsClosed T)
    (f : C(S, unitInterval)) (g : C(T, unitInterval))
    (hfg : ∀ (x : X) (hs : x ∈ S) (ht : x ∈ T), f ⟨x, hs⟩ = g ⟨x, ht⟩) :
    ∃ F : C(X, unitInterval),
      (∀ x : S, F x = f x) ∧ (∀ x : T, F x = g x) := by
  classical
  let h : X → unitInterval := fun x ↦
    if hs : x ∈ S then f ⟨x, hs⟩ else if ht : x ∈ T then g ⟨x, ht⟩ else 0
  have hfs : ∀ x : S, h x = f x := by
    intro x
    simp [h, x.property]
  have hgt : ∀ x : T, h x = g x := by
    intro x
    by_cases hs : (x : X) ∈ S
    · simpa [h, hs] using hfg x hs x.property
    · simp [h, hs, x.property]
  have hcontS : ContinuousOn h S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (show Continuous (fun x : S ↦ f x) from f.continuous).congr
      (fun x ↦ (hfs x).symm)
  have hcontT : ContinuousOn h T := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (show Continuous (fun x : T ↦ g x) from g.continuous).congr
      (fun x ↦ (hgt x).symm)
  let k : C(↥(S ∪ T), unitInterval) :=
    ⟨(S ∪ T).domRestrict h,
      (hcontS.union_of_isClosed hcontT hS hT).domRestrict⟩
  obtain ⟨F, hF⟩ := k.exists_restrict_eq (hS.union hT)
  refine ⟨F, ?_, ?_⟩
  · intro x
    have he := congrArg (fun q : C(↥(S ∪ T), unitInterval) ↦ q ⟨x, Or.inl x.property⟩) hF
    exact he.trans (hfs x)
  · intro x
    have he := congrArg (fun q : C(↥(S ∪ T), unitInterval) ↦ q ⟨x, Or.inr x.property⟩) hF
    exact he.trans (hgt x)

end HolomorphicAnosov.Topology

