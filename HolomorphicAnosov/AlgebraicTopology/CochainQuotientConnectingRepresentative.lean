import HolomorphicAnosov.AlgebraicTopology.CochainQuotientConnectingDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition
import Mathlib.Algebra.Homology.ConcreteCategory
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- The connecting map sends the class of a cocycle to the class of the
coboundary of any lift, expressed in the first term of the short exact row.
Source: Hatcher, *Algebraic Topology*, pp.199–200; Mathlib
`ShortComplex.ShortExact.δ_apply`.
Identify concrete kernel elements with abstract cycles through the canonical
module cycle isomorphisms. Apply the elementwise snake-lemma formula to the
lift and its coboundary, then use the cycle-projection compatibility of the
module homology isomorphism to obtain the equality in the explicit quotient. -/
theorem cochain_quotient_connecting_representative (R : Type u) [CommRing R]
    {S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (hS : S.ShortExact) (n : ℕ)
    (α : cycles R S.X₃ n) (b : S.X₂.X n) (hb : S.g.f n b = α.val)
    (β : cycles R S.X₁ (n+1)) (hβ : S.f.f (n+1) β.val = S.X₂.d n (n+1) b) :
    quotientConnecting R hS n (cocycleClass R S.X₃ n α) =
      cocycleClass R S.X₁ (n+1) β := by
  have hα : S.X₃.d n (n+1) α.val = 0 := by
    have h := α.property
    change S.X₃.d n ((ComplexShape.up ℕ).next n) α.val = 0 at h
    exact (congrArg (fun j => S.X₃.d n j α.val = 0) (CochainComplex.next ℕ n)).mp h
  have hh := hS.δ_apply n (n+1) rfl α.val hα b hb β.val hβ (n+2) (CochainComplex.next ℕ (n+1))
  have ha : S.X₃.cyclesMk α.val (n+1) (CochainComplex.next ℕ n) hα = (S.X₃.sc n).moduleCatCyclesIso.inv α := by
    apply (ModuleCat.mono_iff_injective (S.X₃.iCycles n)).mp inferInstance
    change ((forget₂ (ModuleCat R) Ab).map (S.X₃.iCycles n))
      (S.X₃.cyclesMk α.val (n+1) _ hα) = _
    rw [HomologicalComplex.i_cyclesMk]
    change α.val = ((S.X₃.sc n).moduleCatCyclesIso.inv ≫ (S.X₃.sc n).iCycles) α
    rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  have hβzero : S.X₁.d (n+1) (n+2) β.val = 0 := by
    have h := β.property
    change S.X₁.d (n+1) ((ComplexShape.up ℕ).next (n+1)) β.val = 0 at h
    exact (congrArg (fun j => S.X₁.d (n+1) j β.val = 0)
      (CochainComplex.next ℕ (n+1))).mp h
  have hbb : S.X₁.cyclesMk β.val (n+2) (CochainComplex.next ℕ (n+1)) hβzero =
      (S.X₁.sc (n+1)).moduleCatCyclesIso.inv β := by
    apply (ModuleCat.mono_iff_injective (S.X₁.iCycles (n+1))).mp inferInstance
    change ((forget₂ (ModuleCat R) Ab).map (S.X₁.iCycles (n+1)))
      (S.X₁.cyclesMk β.val (n+2) _ hβzero) = _
    rw [HomologicalComplex.i_cyclesMk]
    change β.val = ((S.X₁.sc (n+1)).moduleCatCyclesIso.inv ≫ (S.X₁.sc (n+1)).iCycles) β
    rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  rw [ha, hbb] at hh
  have hc := congrArg (fun x => (S.X₁.sc (n+1)).moduleCatHomologyIso.hom x) hh
  change ((S.X₃.sc n).moduleCatCyclesIso.inv ≫ (S.X₃.sc n).homologyπ ≫
      hS.δ n (n+1) rfl ≫ (S.X₁.sc (n+1)).moduleCatHomologyIso.hom) α =
    ((S.X₁.sc (n+1)).moduleCatCyclesIso.inv ≫ (S.X₁.sc (n+1)).homologyπ ≫
      (S.X₁.sc (n+1)).moduleCatHomologyIso.hom) β at hc
  simp only [← Category.assoc, ShortComplex.moduleCatCyclesIso_inv_π] at hc
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc
  exact hc
end HolomorphicAnosov.SingularCochain

