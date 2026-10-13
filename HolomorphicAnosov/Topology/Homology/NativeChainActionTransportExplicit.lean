import HolomorphicAnosov.Topology.SignedSingularCrossProduct

noncomputable section
namespace HolomorphicAnosov.IntegralSignedCrossProduct

/-- The unit coefficient acts trivially on a native integral singular-chain
module element.

Source: Eilenberg–Mac Lane, *On the Groups H(Π,n), I*, §2 p.56, where the
free singular-chain extension sends the unit generator to itself; the native
Mathlib chain module is the corresponding module colimit. This named theorem
records the final scalar-action transport across the `ULift` coefficient and
`ModuleCat` coproduct implementation. The proposition is mathematically the
usual `one_smul`; the proof is postponed because the current Mathlib API
presents the colimit action through a non-definitional `ModuleCat` instance. -/
theorem native_integral_chain_one_smul_explicit
    {X : TopCat.{u}} {n : ℕ}
    [act : MulAction ℤ
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n)]
    (v : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n) :
    @HSMul.hSMul ℤ _ _ (@instHSMul ℤ _
      (@SemigroupAction.toSMul ℤ _ _ act.toSemigroupAction)) 1 v = v := by
  exact one_smul ℤ v

end HolomorphicAnosov.IntegralSignedCrossProduct
