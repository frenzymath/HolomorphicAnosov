import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleBasisIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleTensorIndex

noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- In positive total degree, the nonempty circle tensor indices are exactly the
two branches with circle degree zero and one. Hatcher p.216. No index is discarded
on a dimension assumption: the higher-degree branch is eliminated by its empty
circle index, and overlarge coordinate subsets remain empty automatically. -/
def successorCircleTensorIndex (n k : ℕ) :
    ({S : Finset (Fin n) // S.card = k + 1} ⊕
      {S : Finset (Fin n) // S.card = k}) ≃ circleTensorIndex n (k + 1) := by
  let f : ({S : Finset (Fin n) // S.card = k + 1} ⊕
      {S : Finset (Fin n) // S.card = k}) → circleTensorIndex n (k + 1) :=
    Sum.elim (fun S => ⟨⟨(k + 1, 0), by omega⟩, S, ()⟩)
      (fun S => ⟨⟨(k, 1), rfl⟩, S, ()⟩)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro s t h
    cases s with
    | inl s =>
      cases t with
      | inl t =>
        have hs : s = t := Subtype.ext
          (congrArg (fun z : circleTensorIndex n (k + 1) => z.2.1.val) h)
        exact congrArg Sum.inl hs
      | inr t =>
        have hq := congrArg (fun z : circleTensorIndex n (k + 1) => z.1.val.2) h
        simp [f] at hq
    | inr s =>
      cases t with
      | inl t =>
        have hq := congrArg (fun z : circleTensorIndex n (k + 1) => z.1.val.2) h
        simp [f] at hq
      | inr t =>
        have hs : s = t := Subtype.ext
          (congrArg (fun z : circleTensorIndex n (k + 1) => z.2.1.val) h)
        exact congrArg Sum.inr hs
  · rintro ⟨⟨⟨p, q⟩, hpq⟩, S, j⟩
    cases q with
    | zero =>
      have hp : p = k + 1 := by simpa using hpq
      subst p
      refine ⟨Sum.inl S, ?_⟩
      cases j
      rfl
    | succ q =>
      cases q with
      | zero =>
        have hp : p = k := by omega
        subst p
        refine ⟨Sum.inr S, ?_⟩
        cases j
        rfl
      | succ q =>
        have hj : Empty := by
          simpa [circleBasisIndex, show ¬ q + 2 ≤ 1 by omega] using j
        exact hj.elim

end HolomorphicAnosov.TorusRationalCupBasisKronecker
