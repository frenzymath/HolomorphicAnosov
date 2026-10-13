import HolomorphicAnosov.Ghys.CurveContactScalarCoefficients
import HolomorphicAnosov.Ghys.CurveJetReparametrization

/-! Rational reparametrization formulas in smooth scalar coordinates. (Ghys, §3 p.591) -/
noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped Manifold ContDiff
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
variable [IsManifold 𝓘(ℂ) ∞ L]

/-- In any scalar function holomorphic at the jet base, rational reparametrization sends the
coefficients `(a,b)` to `(omega*a,omega²*b-omega*mu*a)`. (Ghys, §3 p.591; Michor, §§1.3–1.6 pp.2–3)
-/
theorem curveJet2_scalar_reparam_coefficients
    (p : CurveJetReparametrization) (j : CurveJet2 L) (φ : L → ℂ)
    (hφ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (curveJet2Base L j)) :
    germFirst ((curveJet2Reparametrize L p j).out.1.map φ) =
        (p.omega : ℂ) * germFirst (j.out.1.map φ) ∧
    germSecond ((curveJet2Reparametrize L p j).out.1.map φ) =
        (p.omega : ℂ) ^ 2 * germSecond (j.out.1.map φ) -
          (p.omega : ℂ) * p.mu * germFirst (j.out.1.map φ) := by
  have hr : CurveContact2 L (curveJet2Reparametrize L p j).out
      (curveParamGermReparametrize L p j.out) :=
    Quotient.exact ((Quotient.out_eq _).trans
      (congrArg (curveJet2Reparametrize L p) (Quotient.out_eq j)).symm)
  have hb : curveGermBase L (curveJet2Reparametrize L p j).out.1 =
      curveJet2Base L j := hr.1.trans (base_reparam L p j.out.1)
  have heq := curveContact2_scalar_coefficients L _ _ hr φ (hb.symm ▸ hφ)
  rw [heq.1, heq.2]
  obtain ⟨g, hg0, hg, _, hge⟩ := j.out.2
  have hbg : curveJet2Base L j = g 0 := by
    change curveGermBase L j.out.1 = g 0
    rw [← hge]
    rfl
  have hf : ContDiffAt ℂ 2 (φ ∘ g) 0 :=
    ((hbg ▸ hφ).comp 0 (hg.contMDiffAt (g.open_source.mem_nhds hg0))).contDiffAt.of_le
      (by simp)
  have hgm : j.out.1.map φ = ((φ ∘ g : ℂ → ℂ) : ScalarGerm) := by
    simpa using congrArg (fun z : CurveGerm L ↦ z.map φ) hge.symm
  have hcomp : (curveParamGermReparametrize L p j.out).1.map φ =
      (((φ ∘ g : ℂ → ℂ) : ScalarGerm).compTendsto p.apply p.tendsto_zero) := by
    change (curveGermReparametrize L p j.out.1).map φ = _
    rw [curveGermReparametrize, map_reparam, hgm]
  rw [hcomp, scalar_first_reparam p _ hf, scalar_second_reparam p _ hf, hgm]
  have hd : deriv p.apply 0 = (p.omega : ℂ) := by
    have h := ((hasDerivAt_id (0 : ℂ)).const_mul (p.omega : ℂ)).div
      ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add
        ((hasDerivAt_id (0 : ℂ)).const_mul p.mu)) (by simp)
    convert h.deriv using 1 <;> simp
    rfl
  rw [hd]
  change deriv (φ ∘ g) 0 * (p.omega : ℂ) = _ * deriv (φ ∘ g) 0 ∧
    (iteratedDeriv 2 (φ ∘ g) 0 * (p.omega : ℂ) ^ 2 +
      deriv (φ ∘ g) 0 * iteratedDeriv 2 p.apply 0) / 2 =
      (p.omega : ℂ) ^ 2 * (iteratedDeriv 2 (φ ∘ g) 0 / 2) -
        (p.omega : ℂ) * p.mu * deriv (φ ∘ g) 0
  constructor
  · ring
  · have hp := reparam_second_coeff p
    linear_combination deriv (φ ∘ g) 0 * hp

end HolomorphicAnosov.Ghys
