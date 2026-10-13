import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleTensorIndex

noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- In total degree zero the only tensor summand is (0,0); this includes the
empty coordinate subset and avoids introducing a spurious degree-minus-one term.
Source: Hatcher's unreduced Künneth formula, pp.215–217. -/
def zeroCircleTensorIndex (n : ℕ) :
    {S : Finset (Fin n) // S.card = 0} ≃ circleTensorIndex n 0 := by
  let f : {S : Finset (Fin n) // S.card = 0} → circleTensorIndex n 0 :=
    fun S => ⟨⟨(0, 0), rfl⟩, S, ()⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro s t h
    exact Subtype.ext (congrArg (fun z : circleTensorIndex n 0 => z.2.1.val) h)
  · rintro ⟨⟨⟨p, q⟩, hpq⟩, S, j⟩
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    refine ⟨S, ?_⟩
    cases j
    rfl

end HolomorphicAnosov.TorusRationalCupBasisKronecker
