import HolomorphicAnosov.Ghys.CurveJetReparametrization
import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import HolomorphicAnosov.Ghys.CurvePostcomposeJetEquivalences
import HolomorphicAnosov.Ghys.CurvePostcomposeReparametrize

namespace HolomorphicAnosov.Ghys

open Set Topology
open scoped Topology Manifold ContDiff

universe u v w

variable {M : Type u} {Q : Type v} {L : Q → Type v}
variable [∀ q, TopologicalSpace (L q)] [∀ q, ChartedSpace ℂ (L q)]
  [∀ q, IsManifold 𝓘(ℂ) ∞ (L q)]
abbrev FamilyJet1 := (q : Q) × CurveJet1 (L q)
abbrev FamilyJet2 := (q : Q) × CurveJet2 (L q)
/-- First-jet postcomposition assembled over the permutation of leaves. Source: Ghys p.591. -/
noncomputable def familyJet1Equiv (σ : Q ≃ Q)
    (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞) :
    FamilyJet1 (L := L) ≃ FamilyJet1 (L := L) :=
  Equiv.sigmaCongr σ (fun q ↦ (curve_postcompose_jet_equivalences (F q)).choose)

/-- Second-jet postcomposition over the same leaf permutation. Source: Ghys p.591. -/
noncomputable def familyJet2Equiv (σ : Q ≃ Q)
    (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞) :
    FamilyJet2 (L := L) ≃ FamilyJet2 (L := L) :=
  Equiv.sigmaCongr σ (fun q ↦
    (curve_postcompose_jet_equivalences (F q)).choose_spec.choose)

/-- Representative formula for the assembled first-jet equivalence. -/
theorem familyJet1Equiv_class (σ : Q ≃ Q)
    (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞)
    (q : Q) (γ : CurveParamGerm (L q)) :
    familyJet1Equiv σ F ⟨q, curveJet1Class (L q) γ⟩ =
      ⟨σ q, curveJet1Class (L (σ q)) (curveParamGermPostcompose (F q) γ)⟩ := by
  change Sigma.mk _ _ = Sigma.mk _ _
  congr 1
  exact (curve_postcompose_jet_equivalences (F q)).choose_spec.choose_spec.1 γ

/-- Representative formula for the assembled second-jet equivalence. -/
theorem familyJet2Equiv_class (σ : Q ≃ Q)
    (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞)
    (q : Q) (γ : CurveParamGerm (L q)) :
    familyJet2Equiv σ F ⟨q, curveJet2Class (L q) γ⟩ =
      ⟨σ q, curveJet2Class (L (σ q)) (curveParamGermPostcompose (F q) γ)⟩ := by
  change Sigma.mk _ _ = Sigma.mk _ _
  congr 1
  exact (curve_postcompose_jet_equivalences (F q)).choose_spec.choose_spec.2 γ

omit [∀ q, IsManifold 𝓘(ℂ) ∞ (L q)] in
/-- Pointwise inverse leaf transports act inversely on admissible germs. -/
theorem familyParamGerm_postcompose_inverse (σ : Q ≃ Q)
    (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞)
    (G : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ.symm q)) ∞)
    (hG : ∀ q z,
      (⟨σ (σ.symm q), F (σ.symm q) (G q z)⟩ : (q : Q) × L q) = ⟨q, z⟩)
    (q : Q) (γ : CurveParamGerm (L q)) :
    (⟨σ (σ.symm q), curveParamGermPostcompose (F (σ.symm q))
      (curveParamGermPostcompose (G q) γ)⟩ : (q : Q) × CurveParamGerm (L q)) = ⟨q, γ⟩ := by
  have lift_inverse (q r : Q) (H : L q → L r)
      (h : ∀ z, (⟨r, H z⟩ : (q : Q) × L q) = ⟨q, z⟩)
      (γ : CurveParamGerm (L q)) (δ : CurveParamGerm (L r))
      (hδ : δ.val = γ.val.map H) :
      (⟨r, δ⟩ : (q : Q) × CurveParamGerm (L q)) = ⟨q, γ⟩ := by
    have hr : r = q := congrArg Sigma.fst (h (curveGermBase (L q) γ.val))
    subst r
    apply congrArg (Sigma.mk q)
    apply Subtype.ext
    rw [hδ]
    have he : H = id := by
      funext z
      exact eq_of_heq (Sigma.mk.inj (h z)).2
    simp [he]
  apply lift_inverse q (σ (σ.symm q)) (fun z ↦ F (σ.symm q) (G q z)) (hG q)
  change (γ.val.map (G q)).map (F (σ.symm q)) = _
  induction γ.val using Filter.Germ.inductionOn with
  | h g => rfl

/-- The quotient equivalence induced by the inverse leaf transport is the inverse total equivalence. Source: Ghys p.591. -/
theorem familyJetEquiv_symm_of_inverse (σ : Q ≃ Q)
    (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞)
    (G : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ.symm q)) ∞)
    (hG : ∀ q z,
      (⟨σ (σ.symm q), F (σ.symm q) (G q z)⟩ : (q : Q) × L q) = ⟨q, z⟩) :
    (familyJet1Equiv σ F).symm = familyJet1Equiv σ.symm G ∧
      (familyJet2Equiv σ F).symm = familyJet2Equiv σ.symm G := by
  have hg := familyParamGerm_postcompose_inverse σ F G hG
  constructor
  · apply Equiv.ext
    rintro ⟨q,j⟩
    refine Quotient.inductionOn j ?_
    intro γ
    apply (familyJet1Equiv σ F).injective
    rw [Equiv.apply_symm_apply]
    change _ = familyJet1Equiv σ F
      (familyJet1Equiv σ.symm G ⟨q,curveJet1Class (L q) γ⟩)
    rw [familyJet1Equiv_class, familyJet1Equiv_class]
    exact (congrArg (fun p : (q : Q) × CurveParamGerm (L q) ↦
      (⟨p.1,curveJet1Class (L p.1) p.2⟩ : FamilyJet1 (L := L))) (hg q γ)).symm
  · apply Equiv.ext
    rintro ⟨q,j⟩
    refine Quotient.inductionOn j ?_
    intro γ
    apply (familyJet2Equiv σ F).injective
    rw [Equiv.apply_symm_apply]
    change _ = familyJet2Equiv σ F
      (familyJet2Equiv σ.symm G ⟨q,curveJet2Class (L q) γ⟩)
    rw [familyJet2Equiv_class, familyJet2Equiv_class]
    exact (congrArg (fun p : (q : Q) × CurveParamGerm (L q) ↦
      (⟨p.1,curveJet2Class (L p.1) p.2⟩ : FamilyJet2 (L := L))) (hg q γ)).symm

variable [∀ q, T2Space (L q)] [∀ q, SecondCountableTopology (L q)]
variable [TopologicalSpace (FamilyJet1 (Q := Q) (L := L))]
  [TopologicalSpace (FamilyJet2 (Q := Q) (L := L))]

/-- Assemble total jet homeomorphisms from continuous quotient transports. Source: Ghys, p.591. -/
theorem jet_dynamics_total_maps
    {σ : Q ≃ Q}
    (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞)
    (G : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ.symm q)) ∞)
    (f : M → M) (inclusion : ∀ q, L q → M)
    (hF : ∀ q z, inclusion (σ q) (F q z) = f (inclusion q z))
    (hG : ∀ q z,
      (⟨σ (σ.symm q), F (σ.symm q) (G q z)⟩ : (q : Q) × L q) = ⟨q, z⟩)
    (hc₁ : Continuous (familyJet1Equiv σ F))
    (hci₁ : Continuous (familyJet1Equiv σ F).symm)
    (hc₂ : Continuous (familyJet2Equiv σ F))
    (hci₂ : Continuous (familyJet2Equiv σ F).symm)
    (base₁ : FamilyJet1 (Q := Q) (L := L) → M)
    (base₂ : FamilyJet2 (Q := Q) (L := L) → M)
    (trunc : FamilyJet2 (Q := Q) (L := L) → FamilyJet1 (Q := Q) (L := L))
    (source₁ : ℂˣ → ℂ → FamilyJet1 (Q := Q) (L := L) → FamilyJet1 (Q := Q) (L := L))
    (source₂ : ℂˣ → ℂ → FamilyJet2 (Q := Q) (L := L) → FamilyJet2 (Q := Q) (L := L))
    (hbase₁ : ∀ j, base₁ j = inclusion j.1 (curveJet1Base (L j.1) j.2))
    (_hbase₂ : ∀ j, base₂ j = inclusion j.1 (curveJet2Base (L j.1) j.2))
    (htrunc : ∀ j, trunc j = ⟨j.1, curveJetTruncation (L j.1) j.2⟩)
    (hsource₁ : ∀ (omega : ℂˣ) (mu : ℂ) j,
      source₁ omega mu j = ⟨j.1, curveJet1Scale (L j.1) omega j.2⟩)
    (hsource₂ : ∀ (omega : ℂˣ) (mu : ℂ) j,
      source₂ omega mu j = ⟨j.1, curveJet2Reparametrize (L j.1) ⟨omega, mu⟩ j.2⟩) :
    ∃ (Φ₁ : FamilyJet1 (Q := Q) (L := L) ≃ₜ FamilyJet1 (Q := Q) (L := L))
      (Φ₂ : FamilyJet2 (Q := Q) (L := L) ≃ₜ FamilyJet2 (Q := Q) (L := L)),
    (∀ q (γ : CurveParamGerm (L q)),
      ∃ δ : CurveParamGerm (L (σ q)),
        δ.val = γ.val.map (F q : L q → L (σ q)) ∧
        Φ₁ ⟨q, curveJet1Class (L q) γ⟩ =
          ⟨σ q, curveJet1Class (L (σ q)) δ⟩ ∧
        Φ₂ ⟨q, curveJet2Class (L q) γ⟩ =
          ⟨σ q, curveJet2Class (L (σ q)) δ⟩) ∧
    (∀ q (γ : CurveParamGerm (L q)),
      ∃ δ : CurveParamGerm (L (σ.symm q)),
        δ.val = γ.val.map (G q : L q → L (σ.symm q)) ∧
        Φ₁.symm ⟨q, curveJet1Class (L q) γ⟩ =
          ⟨σ.symm q, curveJet1Class (L (σ.symm q)) δ⟩ ∧
        Φ₂.symm ⟨q, curveJet2Class (L q) γ⟩ =
          ⟨σ.symm q, curveJet2Class (L (σ.symm q)) δ⟩) ∧
    (∀ j, base₁ (Φ₁ j) = f (base₁ j)) ∧
    (∀ j, trunc (Φ₂ j) = Φ₁ (trunc j)) ∧
    (∀ (omega : ℂˣ) (μ : ℂ) j,
      Φ₁ (source₁ omega μ j) = source₁ omega μ (Φ₁ j)) ∧
    (∀ (omega : ℂˣ) (μ : ℂ) j,
      Φ₂ (source₂ omega μ j) = source₂ omega μ (Φ₂ j)) := by
  classical
  let Φ₁ : FamilyJet1 (L := L) ≃ₜ FamilyJet1 (L := L) :=
    ⟨familyJet1Equiv σ F, hc₁, hci₁⟩
  let Φ₂ : FamilyJet2 (L := L) ≃ₜ FamilyJet2 (L := L) :=
    ⟨familyJet2Equiv σ F, hc₂, hci₂⟩
  have hGg := familyParamGerm_postcompose_inverse σ F G hG
  have hf₁ := familyJet1Equiv_class σ F
  have hf₂ := familyJet2Equiv_class σ F
  refine ⟨Φ₁, Φ₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q γ
    exact ⟨curveParamGermPostcompose (F q) γ, rfl, hf₁ q γ, hf₂ q γ⟩
  · intro q γ
    refine ⟨curveParamGermPostcompose (G q) γ, rfl, ?_, ?_⟩
    · apply Φ₁.injective
      rw [Φ₁.apply_symm_apply]
      change _ = familyJet1Equiv σ F _
      rw [hf₁]
      exact (congrArg (fun j : (q : Q) × CurveParamGerm (L q) ↦
        (⟨j.1, curveJet1Class (L j.1) j.2⟩ : FamilyJet1 (L := L))) (hGg q γ)).symm
    · apply Φ₂.injective
      rw [Φ₂.apply_symm_apply]
      change _ = familyJet2Equiv σ F _
      rw [hf₂]
      exact (congrArg (fun j : (q : Q) × CurveParamGerm (L q) ↦
        (⟨j.1, curveJet2Class (L j.1) j.2⟩ : FamilyJet2 (L := L))) (hGg q γ)).symm
  · rintro ⟨q, j⟩
    refine Quotient.inductionOn j ?_
    intro γ
    change base₁ (familyJet1Equiv σ F ⟨q, curveJet1Class (L q) γ⟩) = _
    rw [hf₁, hbase₁, hbase₁]
    change inclusion (σ q)
      (curveJet1Base (L (σ q)) (curveJet1Class (L (σ q))
        (curveParamGermPostcompose (F q) γ))) =
      f (inclusion q (curveJet1Base (L q) (curveJet1Class (L q) γ)))
    rw [((leaf_jet_complex_manifold (L (σ q))).2.1 _).1,
      ((leaf_jet_complex_manifold (L q)).2.1 γ).1]
    have hb : curveGermBase (L (σ q)) (curveParamGermPostcompose (F q) γ).val =
        F q (curveGermBase (L q) γ.val) := by
      change curveGermBase _ (γ.val.map (F q)) = _
      induction γ.val using Filter.Germ.inductionOn with
      | h g => rfl
    rw [hb, hF]
  · rintro ⟨q, j⟩
    refine Quotient.inductionOn j ?_
    intro γ
    change trunc (familyJet2Equiv σ F ⟨q, curveJet2Class (L q) γ⟩) = _
    rw [hf₂, htrunc, htrunc]
    exact (hf₁ q γ).symm
  · intro omega μ
    rintro ⟨q, j⟩
    refine Quotient.inductionOn j ?_
    intro γ
    rw [hsource₁]
    change familyJet1Equiv σ F
      ⟨q, curveJet1Class (L q) (curveParamGermReparametrize (L q) (.scale omega) γ)⟩ = _
    rw [hf₁]
    change _ = source₁ omega μ (familyJet1Equiv σ F ⟨q, curveJet1Class (L q) γ⟩)
    rw [hf₁, hsource₁]
    exact congrArg (fun δ : CurveParamGerm (L (σ q)) ↦
      (⟨σ q, curveJet1Class (L (σ q)) δ⟩ : FamilyJet1 (L := L)))
      (curveParamGermPostcompose_reparametrize (F q) (.scale omega) γ)
  · intro omega μ
    rintro ⟨q, j⟩
    refine Quotient.inductionOn j ?_
    intro γ
    rw [hsource₂]
    change familyJet2Equiv σ F
      ⟨q, curveJet2Class (L q) (curveParamGermReparametrize (L q) ⟨omega, μ⟩ γ)⟩ = _
    rw [hf₂]
    change _ = source₂ omega μ (familyJet2Equiv σ F ⟨q, curveJet2Class (L q) γ⟩)
    rw [hf₂, hsource₂]
    exact congrArg (fun δ : CurveParamGerm (L (σ q)) ↦
      (⟨σ q, curveJet2Class (L (σ q)) δ⟩ : FamilyJet2 (L := L)))
      (curveParamGermPostcompose_reparametrize (F q) ⟨omega, μ⟩ γ)


end HolomorphicAnosov.Ghys
