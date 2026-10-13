import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Setoid.Basic
import Mathlib.Analysis.Complex.Basic

/-! Scalar one- and two-jets of analytic germs. Source: Ghys §3 p.591. -/

open Filter
open scoped Topology _root_.Topology

noncomputable section

namespace HolomorphicAnosov.Ghys

/-- Germs of scalar maps at zero; equality is equality on a neighborhood of zero. Source: Ghys §3 p.591. -/
abbrev ScalarGerm := Filter.Germ (𝓝 (0 : ℂ)) ℂ

/-- Evaluation at zero respects the neighborhood-germ relation. Source: Ghys §3 p.591. -/
theorem germ_base_respects {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 (0 : ℂ)] g) : f 0 = g 0 := by
  exact h.eq_of_nhds

/-- The first derivative respects the neighborhood-germ relation. Source: Ghys §3 p.591. -/
theorem germ_first_respects {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 (0 : ℂ)] g) :
    deriv f 0 = deriv g 0 := by
  exact h.deriv_eq

/-- The quadratic Taylor coefficient respects the neighborhood-germ relation. Source: Ghys §3 p.591. -/
theorem germ_second_respects {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 (0 : ℂ)] g) :
    iteratedDeriv 2 f 0 / 2 = iteratedDeriv 2 g 0 / 2 := by
  exact congrArg (fun z : ℂ ↦ z / 2) (h.iteratedDeriv_eq 2)

/-- Analyticity and a nonzero first derivative are germ properties. Source: Ghys §3 p.591. -/
theorem germ_admissible_respects {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 (0 : ℂ)] g) :
    (AnalyticAt ℂ f 0 ∧ deriv f 0 ≠ 0) ↔ (AnalyticAt ℂ g 0 ∧ deriv g 0 ≠ 0) := by
  exact and_congr (analyticAt_congr h) (by rw [h.deriv_eq])

/-- The base coefficient of a scalar germ, by quotient descent. Source: Ghys §3 p.591. -/
def germBase (γ : ScalarGerm) : ℂ :=
  γ.liftOn (fun f ↦ f 0) (fun _ _ h ↦ germ_base_respects h)

/-- The first coefficient of a scalar germ. Source: Ghys §3 p.591. -/
def germFirst (γ : ScalarGerm) : ℂ :=
  γ.liftOn (fun f ↦ deriv f 0) (fun _ _ h ↦ germ_first_respects h)

/-- The quadratic coefficient is the second derivative divided by two. Source: Ghys §3 p.591. -/
def germSecond (γ : ScalarGerm) : ℂ :=
  γ.liftOn (fun f ↦ iteratedDeriv 2 f 0 / 2) (fun _ _ h ↦ germ_second_respects h)

/-- Germs admitting an analytic representative with nonzero first derivative. Source: Ghys §3 p.591. -/
def GermAdmissible (γ : ScalarGerm) : Prop :=
  γ.liftOn (fun f ↦ AnalyticAt ℂ f 0 ∧ deriv f 0 ≠ 0)
    (fun _ _ h ↦ propext (germ_admissible_respects h))

/-- The admissible scalar-germ carrier. Source: Ghys §3 p.591. -/
abbrev AdmissibleScalarGerm := {γ : ScalarGerm // GermAdmissible γ}

/-- Base and first coefficients used for first-order contact. Source: Ghys §3 p.591. -/
def firstJetData (γ : AdmissibleScalarGerm) : ℂ × ℂ :=
  (germBase γ.1, germFirst γ.1)

/-- Base, first and quadratic coefficients used for second-order contact. Source: Ghys §3 p.591. -/
def secondJetData (γ : AdmissibleScalarGerm) : (ℂ × ℂ) × ℂ :=
  (firstJetData γ, germSecond γ.1)

/-- First-order contact is equality of the base and first coefficients. Source: Ghys §3 p.591. -/
def firstJetContact : Setoid AdmissibleScalarGerm := Setoid.ker firstJetData

/-- Second-order contact adds equality of the quadratic coefficient. Source: Ghys §3 p.591. -/
def secondJetContact : Setoid AdmissibleScalarGerm := Setoid.ker secondJetData

/-- The scalar one-jet quotient. Source: Ghys §3 p.591. -/
abbrev ScalarJet1 := Quotient firstJetContact

/-- The scalar two-jet quotient. Source: Ghys §3 p.591. -/
abbrev ScalarJet2 := Quotient secondJetContact

/-- The class of an admissible germ in the one-jet quotient. Source: Ghys §3 p.591. -/
def jet1Class (γ : AdmissibleScalarGerm) : ScalarJet1 := Quotient.mk firstJetContact γ

/-- The class of an admissible germ in the two-jet quotient. Source: Ghys §3 p.591. -/
def jet2Class (γ : AdmissibleScalarGerm) : ScalarJet2 := Quotient.mk secondJetContact γ

/-- Coefficients descend to one-jets through the kernel quotient. Source: Ghys §3 p.591. -/
def jet1Data : ScalarJet1 → ℂ × ℂ := Setoid.kerLift firstJetData

/-- Coefficients descend to two-jets through the kernel quotient. Source: Ghys §3 p.591. -/
def jet2Data : ScalarJet2 → (ℂ × ℂ) × ℂ := Setoid.kerLift secondJetData

/-- The base map on one-jets. Source: Ghys §3 p.591. -/
def jet1Base (j : ScalarJet1) : ℂ := (jet1Data j).1

/-- The first-coefficient map on one-jets. Source: Ghys §3 p.591. -/
def jet1First (j : ScalarJet1) : ℂ := (jet1Data j).2

/-- The base map on two-jets. Source: Ghys §3 p.591. -/
def jet2Base (j : ScalarJet2) : ℂ := (jet2Data j).1.1

/-- The first-coefficient map on two-jets. Source: Ghys §3 p.591. -/
def jet2First (j : ScalarJet2) : ℂ := (jet2Data j).1.2

/-- The quadratic-coefficient map on two-jets. Source: Ghys §3 p.591. -/
def jet2Second (j : ScalarJet2) : ℂ := (jet2Data j).2

/-- Second-order contact implies first-order contact. Source: Ghys §3 p.591. -/
theorem secondJetContact_implies_first {γ δ : AdmissibleScalarGerm}
    (h : secondJetContact.r γ δ) : firstJetContact.r γ δ := by
  exact congrArg Prod.fst h

/-- Forgetting the quadratic coefficient defines truncation from two-jets to one-jets. Source: Ghys §3 p.591. -/
def jetTruncation : ScalarJet2 → ScalarJet1 :=
  Quotient.map id (fun _ _ h ↦ secondJetContact_implies_first h)

/-- Scalar-germ coefficients, admissibility, contact relations, quotient coefficients and truncation. Source: Ghys §3 p. -/
theorem scalar_jet_germ_quotient :
    (∀ f : ℂ → ℂ,
      germBase (f : ScalarGerm) = f 0 ∧
      germFirst (f : ScalarGerm) = deriv f 0 ∧
      germSecond (f : ScalarGerm) = iteratedDeriv 2 f 0 / 2 ∧
      (GermAdmissible (f : ScalarGerm) ↔ AnalyticAt ℂ f 0 ∧ deriv f 0 ≠ 0)) ∧
    (∀ γ δ : AdmissibleScalarGerm,
      (firstJetContact.r γ δ ↔ germBase γ.1 = germBase δ.1 ∧
        germFirst γ.1 = germFirst δ.1) ∧
      (secondJetContact.r γ δ ↔ firstJetContact.r γ δ ∧
        germSecond γ.1 = germSecond δ.1)) ∧
    (∀ γ : AdmissibleScalarGerm,
      jet1Base (jet1Class γ) = germBase γ.1 ∧
      jet1First (jet1Class γ) = germFirst γ.1 ∧
      jet2Base (jet2Class γ) = germBase γ.1 ∧
      jet2First (jet2Class γ) = germFirst γ.1 ∧
      jet2Second (jet2Class γ) = germSecond γ.1 ∧
      jetTruncation (jet2Class γ) = jet1Class γ) ∧
    (∀ j : ScalarJet1, jet1First j ≠ 0) ∧
    (∀ j : ScalarJet2, jet2First j ≠ 0) ∧
    jet1Base ∘ jetTruncation = jet2Base ∧
    jet1First ∘ jetTruncation = jet2First := by
  have hne : ∀ γ : AdmissibleScalarGerm, germFirst γ.1 ≠ 0 := by
    rintro ⟨γ, hγ⟩
    induction γ using Filter.Germ.inductionOn with
    | h f => exact hγ.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact ⟨rfl, rfl, rfl, Iff.rfl⟩
  · intro γ δ
    constructor
    · change (germBase γ.1, germFirst γ.1) = (germBase δ.1, germFirst δ.1) ↔ _
      exact Prod.ext_iff
    · change (firstJetData γ, germSecond γ.1) =
        (firstJetData δ, germSecond δ.1) ↔ firstJetData γ = firstJetData δ ∧ _
      exact Prod.ext_iff
  · intro γ
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro j
    induction j using Quotient.inductionOn with
    | h γ => exact hne γ
  · intro j
    induction j using Quotient.inductionOn with
    | h γ => exact hne γ
  · funext j
    induction j using Quotient.inductionOn with
    | h γ => rfl
  · funext j
    induction j using Quotient.inductionOn with
    | h γ => rfl


end HolomorphicAnosov.Ghys
