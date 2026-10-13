import HolomorphicAnosov.Topology.GoodPairCollapse
import Mathlib.Topology.Homeomorph.Defs

/-! Complement homeomorphism for a closed-subspace collapse. -/

namespace HolomorphicAnosov.GoodPair

/-- The quotient projection is a homeomorphism off the collapsed closed subset, compatibly with every distinguished subspace containing it and the two inclusion squares. (Hatcher, Prop. 2.22) -/
theorem good_pair_complement_homeomorphism
    {X : Type*} [TopologicalSpace X] (A : Set X) (hA : IsClosed A) :
    ∃ e : ↥Aᶜ ≃ₜ ↥(collapsedPart A)ᶜ,
      (∀ x : ↥Aᶜ, (e x).val = collapse A x.val) ∧
      ∀ (V : Set X) (hAV : A ⊆ V),
        let VC : Set ↥Aᶜ := {x | x.val ∈ V}
        let QVC : Set ↥(collapsedPart A)ᶜ := {y | y.val ∈ collapse A '' V}
        let qV : V → ↥(collapse A '' V) :=
          fun x ↦ ⟨collapse A x.val, ⟨x.val, x.property, rfl⟩⟩
        let qA : A → ↥(collapsedPart A) :=
          fun x ↦ ⟨collapse A x.val, ⟨x.val, x.property, rfl⟩⟩
        let jV : VC → V := fun x ↦ ⟨x.val.val, x.property⟩
        let jQV : QVC → ↥(collapse A '' V) := fun y ↦ ⟨y.val.val, y.property⟩
        let i : A → V := fun x ↦ ⟨x.val, hAV x.property⟩
        let iQ : ↥(collapsedPart A) → ↥(collapse A '' V) := fun y ↦
          ⟨y.val, Set.image_mono hAV y.property⟩
        ∃ eV : VC ≃ₜ QVC,
          (∀ x : VC, (eV x).val = e x.val) ∧
          ((Subtype.val : ↥(collapsedPart A)ᶜ → Collapsed A) ∘ e =
            (collapse A : X → Collapsed A) ∘ (Subtype.val : ↥Aᶜ → X)) ∧
          (jQV ∘ eV = qV ∘ jV) ∧
          (iQ ∘ qA = qV ∘ i) := by
  classical
  have hrel {x y : X} (h : collapse A x = collapse A y) :
      x = y ∨ x ∈ A ∧ y ∈ A := Quotient.exact h
  have hpre : (collapse A) ⁻¹' collapsedPart A = A := by
    ext x
    constructor
    · rintro ⟨a, ha, he⟩
      rcases hrel he with rfl | h
      · exact ha
      · exact h.2
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hquot : Topology.IsQuotientMap (collapse A) := isQuotientMap_quotient_mk'
  have hB : IsClosed (collapsedPart A) := hquot.isCoinducing.isClosed_preimage.mp
    (hpre.symm ▸ hA)
  have hcomp : Aᶜ = (collapse A) ⁻¹' (collapsedPart A)ᶜ := by
    rw [Set.preimage_compl, hpre]
  let transport : ↥Aᶜ ≃ₜ ↥((collapse A) ⁻¹' (collapsedPart A)ᶜ) :=
    { toEquiv := Set.equivOfEq hcomp
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  let c : ↥Aᶜ → ↥(collapsedPart A)ᶜ :=
    ((collapsedPart A)ᶜ.restrictPreimage (collapse A)) ∘ transport
  have hc : Topology.IsQuotientMap c :=
    (hquot.restrictPreimage_isOpen hB.isOpen_compl).comp transport.isQuotientMap
  have hcval (x : ↥Aᶜ) : (c x).val = collapse A x.val := rfl
  have hci : Function.Injective c := by
    intro x y hxy
    have hh : collapse A x.val = collapse A y.val := congrArg Subtype.val hxy
    rcases hrel hh with hh | hh
    · exact Subtype.ext hh
    · exact (x.property hh.1).elim
  let ec := Equiv.ofBijective c ⟨hci, hc.surjective⟩
  let e : ↥Aᶜ ≃ₜ ↥(collapsedPart A)ᶜ :=
    { toEquiv := ec
      continuous_toFun := hc.continuous
      continuous_invFun := hc.continuous_iff.mpr (by
        change Continuous (fun x => ec.invFun (c x))
        have heq : (fun x => ec.invFun (c x)) = id := funext ec.symm_apply_apply
        rw [heq]
        exact continuous_id) }
  have heval (x : ↥Aᶜ) : (e x).val = collapse A x.val := hcval x
  refine ⟨e, heval, ?_⟩
  intro V hAV
  dsimp only
  have hiff (x : ↥Aᶜ) : x.val ∈ V ↔ (e x).val ∈ collapse A '' V := by
    rw [heval]
    constructor
    · intro hx
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨v, hv, heq⟩
      rcases hrel heq with heq | hh
      · exact heq ▸ hv
      · exact (x.property hh.2).elim
  let eV : {x : ↥Aᶜ | x.val ∈ V} ≃ₜ
      {y : ↥(collapsedPart A)ᶜ | y.val ∈ collapse A '' V} :=
    { toEquiv := e.toEquiv.subtypeEquiv hiff
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨eV, (fun _ ↦ rfl), funext heval, ?_, ?_⟩
  · funext x
    exact Subtype.ext (heval x.val)
  · rfl

end HolomorphicAnosov.GoodPair
