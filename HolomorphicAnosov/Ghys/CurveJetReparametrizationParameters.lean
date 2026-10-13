import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.Complex.Basic

/-! Parameters, composition, and inversion for rational source coordinate changes near zero. (Ghys,
§3 p.591) -/

noncomputable section
namespace HolomorphicAnosov.Ghys

/-- The parameters `(omega, mu) ∈ ℂˣ × ℂ` of a rational source reparametrization. (Ghys, p.591) -/
structure CurveJetReparametrization where
  omega : ℂˣ
  mu : ℂ

/-- The rational source map `z ↦ omega*z/(1+mu*z)`. (Ghys, p.591) -/
def CurveJetReparametrization.apply (p : CurveJetReparametrization) (z : ℂ) : ℂ :=
  (p.omega : ℂ) * z / (1 + p.mu * z)

/-- The parameters of the pure source scaling `z ↦ omega*z`. (Ghys, p.591) -/
def CurveJetReparametrization.scale (omega : ℂˣ) : CurveJetReparametrization := ⟨omega, 0⟩

/-- The parameters of `q.apply ∘ p.apply` near zero, corresponding to first applying `q` and then
`p` to a germ. (Ghys, p.591) -/
def CurveJetReparametrization.compose (p q : CurveJetReparametrization) :
    CurveJetReparametrization :=
  ⟨q.omega * p.omega, p.mu + q.mu * (p.omega : ℂ)⟩

/-- The inverse reparametrization, whose source map near zero is `z ↦ z/(omega-mu*z)`. (Ghys, p.591)
-/
def CurveJetReparametrization.inverse (p : CurveJetReparametrization) :
    CurveJetReparametrization :=
  ⟨p.omega⁻¹, -p.mu / (p.omega : ℂ)⟩


end HolomorphicAnosov.Ghys
