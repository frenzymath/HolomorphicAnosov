import HolomorphicAnosov.Geometry.TransverseMobiusUniqueness
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- A locally projective map is constant along a connected parametrized lifted plaque.
(Thurston, §4.8, p. 63) -/
theorem transverse_projective_constant_on_plaque
    {X Y L ι K : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    [TopologicalSpace K] [PreconnectedSpace K]
    (A : FlatProjectiveAtlas X L ι) (p : Y → X) (hp : Continuous p)
    (D : Y → ComplexProjectiveLine)
    (hD : ∀ y, ∃ i, ∃ a : ComplexMobiusTransformation, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
        EqOn D (fun w ↦ a.apply (complexProjectiveLineFinite ((A.chart i (p w)).2))) U)
    (α : K → Y) (hα : Continuous α) (i : ι) (t₀ : K)
    (hin : ∀ t, p (α t) ∈ (A.chart i).source)
    (hcoord : ∀ t, (A.chart i (p (α t))).2 = (A.chart i (p (α t₀))).2) :
    ∀ t, D (α t) = D (α t₀) := by
  have hlc : IsLocallyConstant (D ∘ α) := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro t
    obtain ⟨j, g, U, hU, htU, hUsub, hEq⟩ := hD (α t)
    have hij : p (α t) ∈ (A.chart i).source ∩ (A.chart j).source :=
      ⟨hin t, hUsub htU⟩
    have htransAt : ContinuousAt (A.transition i j) (p (α t)) :=
      (A.transition_continuous i j).continuousAt
        (((A.chart i).open_source.inter (A.chart j).open_source).mem_nhds hij)
    have ht : ∀ᶠ x in 𝓝 (p (α t)), A.transition i j x = A.transition i j (p (α t)) :=
      htransAt.eventually ((isOpen_discrete {A.transition i j (p (α t))}).mem_nhds rfl)
    have htα : ∀ᶠ s in 𝓝 t, A.transition i j (p (α s)) =
        A.transition i j (p (α t)) := (hp.comp hα).continuousAt ht
    have hUα : ∀ᶠ s in 𝓝 t, α s ∈ U := hα.continuousAt (hU.mem_nhds htU)
    filter_upwards [htα, hUα] with s hsT hsU
    have hc : ((A.chart j (p (α s))).2 : OnePoint ℂ) =
        ((A.chart j (p (α t))).2 : OnePoint ℂ) := by
      rw [A.transition_agrees i j (p (α s)) ⟨hin s, hUsub hsU⟩,
        A.transition_agrees i j (p (α t)) hij, hsT, hcoord s, hcoord t]
    have hc' : complexProjectiveLineFinite ((A.chart j (p (α s))).2) =
        complexProjectiveLineFinite ((A.chart j (p (α t))).2) := by
      apply (OnePoint.equivProjectivization ℂ).symm.injective
      simpa only [complexProjectiveLineFinite_to_onePoint] using hc
    exact (hEq hsU).trans ((congrArg g.apply hc').trans (hEq htU).symm)
  exact fun t ↦ hlc.apply_eq_of_preconnectedSpace t t₀

end HolomorphicAnosov.Ghys
