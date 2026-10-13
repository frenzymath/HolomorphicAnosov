import HolomorphicAnosov.Ghys.CurveContactScalarCoefficients
import HolomorphicAnosov.Ghys.CurvePostcomposeJetEquivalences
import HolomorphicAnosov.Ghys.CurveScalarGermChainRule



namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped Manifold ContDiff
universe u v
variable {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
  [IsManifold 𝓘(ℂ) ∞ L]
variable {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
  [IsManifold 𝓘(ℂ) ∞ L']

/-- The scalar first coefficient of a postcomposed one-jet equals that of its postcomposed
representative. (Ghys, p.591) -/
theorem curveJet1_postcompose_scalar
    (T : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) L L' ∞) (E : CurveJet1 L ≃ CurveJet1 L')
    (hE : ∀ γ, E (curveJet1Class L γ) = curveJet1Class L' (curveParamGermPostcompose T γ))
    (j : CurveJet1 L) (φ : L' → ℂ)
    (hφ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (T (curveJet1Base L j))) :
    curveJet1Base L' (E j) = T (curveJet1Base L j) ∧
      germFirst ((E j).out.val.map φ) = germFirst (j.out.val.map (φ ∘ T)) := by
  have hc : CurveContact1 L' (curveParamGermPostcompose T j.out) (E j).out := by
    apply Quotient.exact (s := curveContactSetoid1 L')
    change curveJet1Class L' (curveParamGermPostcompose T j.out) = _
    rw [← hE]
    change E ⟦j.out⟧ = ⟦(E j).out⟧
    rw [Quotient.out_eq, Quotient.out_eq]
  have hb : curveGermBase L' (curveParamGermPostcompose T j.out).val =
      T (curveJet1Base L j) := by
    change curveGermBase L' (j.out.val.map T) = T (curveGermBase L j.out.val)
    induction j.out.val using Germ.inductionOn with
    | h g => rfl
  have hp := curveContact1_scalar_coefficient (curveParamGermPostcompose T j.out)
    (E j).out hc φ (hb.symm ▸ hφ)
  refine ⟨hc.1.symm.trans hb, ?_⟩
  rw [← hp]
  congr 1
  change (j.out.val.map T).map φ = j.out.val.map (φ ∘ T)
  induction j.out.val using Germ.inductionOn with
  | h g => rfl

/-- The scalar first and second coefficients of a postcomposed two-jet equal those of its
postcomposed representative. (Ghys, p.591) -/
theorem curveJet2_postcompose_scalar
    (T : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) L L' ∞) (E : CurveJet2 L ≃ CurveJet2 L')
    (hE : ∀ γ, E (curveJet2Class L γ) = curveJet2Class L' (curveParamGermPostcompose T γ))
    (j : CurveJet2 L) (φ : L' → ℂ)
    (hφ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (T (curveJet2Base L j))) :
    curveJet2Base L' (E j) = T (curveJet2Base L j) ∧
      germFirst ((E j).out.val.map φ) = germFirst (j.out.val.map (φ ∘ T)) ∧
      germSecond ((E j).out.val.map φ) = germSecond (j.out.val.map (φ ∘ T)) := by
  have hc : CurveContact2 L' (curveParamGermPostcompose T j.out) (E j).out := by
    apply Quotient.exact (s := curveContactSetoid2 L')
    change curveJet2Class L' (curveParamGermPostcompose T j.out) = _
    rw [← hE]
    change E ⟦j.out⟧ = ⟦(E j).out⟧
    rw [Quotient.out_eq, Quotient.out_eq]
  have hb : curveGermBase L' (curveParamGermPostcompose T j.out).val =
      T (curveJet2Base L j) := by
    change curveGermBase L' (j.out.val.map T) = T (curveGermBase L j.out.val)
    induction j.out.val using Germ.inductionOn with
    | h g => rfl
  have hp := curveContact2_scalar_coefficients L'
    (curveParamGermPostcompose T j.out) (E j).out hc φ (hb.symm ▸ hφ)
  have hm : (curveParamGermPostcompose T j.out).val.map φ = j.out.val.map (φ ∘ T) := by
    change (j.out.val.map T).map φ = _
    induction j.out.val using Germ.inductionOn with
    | h g => rfl
  exact ⟨hc.1.symm.trans hb, hp.1.symm.trans (congrArg germFirst hm),
    hp.2.symm.trans (congrArg germSecond hm)⟩

end HolomorphicAnosov.Ghys
