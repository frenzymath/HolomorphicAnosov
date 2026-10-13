import HolomorphicAnosov.Ghys.CurveJetAffineData
import HolomorphicAnosov.Ghys.JetDynamicsLeafwiseDiffeomorphSmoothness
import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter Function
open scoped _root_.HolomorphicAnosov.Topology Manifold ContDiff
universe u v w x

/-- Under the stated invariance, local holomorphic sections and decay hypotheses, the scalar unit coefficient has holomorphic approximants on a fixed neighborhood with the prescribed geometric error bound. (Ghys, Lemma 3.3) -/
theorem transported_jet_holomorphic_approximation {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]
    [TopologicalSpace (NativeLeafwiseJet1 L)] [TopologicalSpace (NativeLeafwiseJet2 L)]
    (Φ₁ : NativeLeafwiseJet1 L ≃ₜ NativeLeafwiseJet1 L)
    (Φ₂ : NativeLeafwiseJet2 L ≃ₜ NativeLeafwiseJet2 L)
    (htrunc : ∀ j, nativeLeafwiseJetTruncation L (Φ₂ j) = Φ₁ (nativeLeafwiseJetTruncation L j))
    (hshift : ∀ mu j, Φ₂ (nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩ j) =
      nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩ (Φ₂ j))
    (perm : ι → ι) (G : ∀ i, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L (perm i)) ∞)
    (hrep : ∀ i (γ : CurveParamGerm (L i)),
      ∃ δ : CurveParamGerm (L (perm i)), δ.val = γ.val.map (G i) ∧
        Φ₁.symm ⟨i, curveJet1Class (L i) γ⟩ = ⟨perm i, curveJet1Class (L (perm i)) δ⟩ ∧
        Φ₂.symm ⟨i, curveJet2Class (L i) γ⟩ = ⟨perm i, curveJet2Class (L (perm i)) δ⟩)
    (ν : NativeLeafwiseJet1 L → ℝ) (hν : Continuous ν)
    (hinc : ∀ i, Continuous (nativeLeafwiseJet1Inclusion L i))
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
    (hdecay : ∀ n j, ν ((Φ₁.symm : _ → _)^[n] j) ≤ C*q^n*ν j)
    {X : Type u} {b : ℕ} (base : NativeLeafwiseJet1 L → X)
    (O K : Fin b → Set X) (hKO : ∀ k, K k ⊆ O k)
    (s : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (hs : ∀ j, nativeLeafwiseJetTruncation L (s j) = j)
    (heq : ∀ j, s (Φ₁ j) = Φ₂ (s j))
    (sloc : ∀ k, {j : NativeLeafwiseJet1 L | base j ∈ O k} → NativeLeafwiseJet2 L)
    (hsloc : ∀ k j, nativeLeafwiseJetTruncation L (sloc k j) = j.val)
    (hhol : ∀ k ell,
      letI := nativeLeafJet1Charts L ell
      letI := nativeLeafJet2Charts L ell
      ∃ sigma : CurveJet1 (L ell) → CurveJet2 (L ell),
        ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ sigma
          {j | base (nativeLeafwiseJet1Inclusion L ell j) ∈ O k} ∧
        ∀ j (hj : base (nativeLeafwiseJet1Inclusion L ell j) ∈ O k),
          sloc k ⟨nativeLeafwiseJet1Inclusion L ell j, hj⟩ =
            nativeLeafwiseJet2Inclusion L ell (sigma j))
    (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ k j (hj : base j ∈ K k), ∃ mu : ℂ,
      nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩ (s j) = sloc k ⟨j,hKO k hj⟩ ∧
        ‖mu‖ ≤ B * ν j)
    (hdisks : ∀ i (c : LeafChart (L i)) z, z ∈ c.val.target →
      ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ c.val.target ∧
        ∀ᶠ n in atTop, ∃ k, ∀ j, curveJet1Base (L i) j ∈ c.val.source →
          (curveJet1Coeff (L i) c j).1 ∈ V →
          base ((Φ₁.symm : _ → _)^[n] ⟨i,j⟩) ∈ K k) :
    ∀ i (τ : CurveJet1 (L i) → CurveJet2 (L i)),
      (∀ j, s (nativeLeafwiseJet1Inclusion L i j) = nativeLeafwiseJet2Inclusion L i (τ j)) →
      ∀ (c : LeafChart (L i)) (A : ℂ → ℂ),
      (∀ j, curveJet1Base (L i) j ∈ c.val.source →
        (curveJet2Coeff (L i) c (τ j)).2 =
          A (curveJet1Coeff (L i) c j).1 * (curveJet1Coeff (L i) c j).2 ^ 2) →
      ∀ z ∈ c.val.target, ∃ (V : Set ℂ) (F : ℕ → ℂ → ℂ) (ρ : ℂ → ℝ) (C' q' : ℝ),
        IsOpen V ∧ z ∈ V ∧ V ⊆ c.val.target ∧ ContinuousOn ρ V ∧
        0 ≤ C' ∧ 0 ≤ q' ∧ q' < 1 ∧
        (∀ᶠ n in atTop, DifferentiableOn ℂ (F n) V) ∧
        (∀ᶠ n in atTop, ∀ z ∈ V, ‖F n z-A z‖ ≤ C'*q'^n*ρ z) := by
  have holomorphicUnitCoefficient (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
      [IsManifold 𝓘(ℂ) ∞ L] [T2Space L] [SecondCountableTopology L]
      (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
      (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L))
      (hAtlases : CurveJetCoefficientAtlases L A1 A2)
      (s : CurveJet1 L → CurveJet2 L) (c : LeafChart L)
      (V : Set ℂ) (hV : V ⊆ c.1.target)
      (S : Set (CurveJet1 L))
      (hS : ∀ j, curveJet1Base L j ∈ c.1.source → (curveJet1Coeff L c j).1 ∈ V → j ∈ S)
      (htrunc : ∀ j ∈ S, curveJetTruncation L (s j) = j)
      (hhol : letI := A1
        letI := A2
        ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ s S) :
      ∃ A : ℂ → ℂ, DifferentiableOn ℂ A V ∧
        ∀ z ∈ V, ∀ j, curveJet1Base L j ∈ c.val.source →
          curveJet1Coeff L c j = (z, 1) → (curveJet2Coeff L c (s j)).2 = A z := by
    let := A1
    let := A2
    obtain ⟨e1, e2, _, _, hs1, hs2, ht1, ht2, he1, he2,
      _, he1inv, he2smooth, _⟩ := hAtlases.2.2.1 c
    have hunit (z : ℂ) (hz : z ∈ V) : (z, 1) ∈ e1.target := by
      rw [ht1]
      exact ⟨hV hz, one_ne_zero⟩
    have hjbase (z : ℂ) (hz : z ∈ V) : curveJet1Base L (e1.symm (z, 1)) ∈ c.1.source := by
      have hj := e1.map_target (hunit z hz)
      rwa [hs1] at hj
    have hcoords (z : ℂ) (hz : z ∈ V) :
        curveJet1Coeff L c (e1.symm (z, 1)) = (z, 1) :=
      (he1 (e1.map_target (hunit z hz))).symm.trans (e1.right_inv (hunit z hz))
    have hjS (z : ℂ) (hz : z ∈ V) : e1.symm (z, 1) ∈ S :=
      hS _ (hjbase z hz) (by rw [hcoords z hz]; exact hz)
    have hsource (z : ℂ) (hz : z ∈ V) : s (e1.symm (z, 1)) ∈ e2.source := by
      rw [hs2]
      change curveJet2Base L (s (e1.symm (z, 1))) ∈ c.1.source
      rw [← curve_jet_truncation_base L _, htrunc _ (hjS z hz)]
      exact hjbase z hz
    let B : ℂ → ℂ := fun z ↦ (e2 (s (e1.symm (z, 1)))).2
    have h1 : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) ∞ (fun z : ℂ ↦ (z, (1 : ℂ))) V :=
      contMDiffOn_iff_contDiffOn.mpr (contDiff_id.prodMk contDiff_const).contDiffOn
    have hcomp := he2smooth.comp (hhol.comp (he1inv.comp h1 (fun z hz ↦ hunit z hz))
      (fun z hz ↦ hjS z hz)) (fun z hz ↦ hsource z hz)
    have hB : ContDiffOn ℂ ∞ B V :=
      (contMDiffOn_iff_contDiffOn.mp hcomp).snd
    refine ⟨B, hB.differentiableOn (by simp), ?_⟩
    intro z hz j hj hc
    have hj1 : j ∈ e1.source := by rwa [hs1]
    have hjEq : j = e1.symm (z, 1) := by
      rw [← hc, ← he1 hj1, e1.left_inv hj1]
    rw [hjEq]
    exact (congrArg Prod.snd (he2 (hsource z hz))).symm
  have unitCoefficientShift (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
      [IsManifold 𝓘(ℂ) ∞ L] [T2Space L] [SecondCountableTopology L]
      (c : LeafChart L) (j : CurveJet1 L) (s t : CurveJet2 L)
      (hs : curveJetTruncation L s = j)
      (hj : curveJet1Base L j ∈ c.val.source)
      (ha : (curveJet1Coeff L c j).2 = 1)
      (mu : ℂ) (ht : curveJet2Reparametrize L ⟨1, mu⟩ s = t) :
      ‖(curveJet2Coeff L c t).2 - (curveJet2Coeff L c s).2‖ = ‖mu‖ := by
    have hb : curveJet2Base L s ∈ c.val.source := by
      rw [← curve_jet_truncation_base L s, hs]
      exact hj
    have hfirst := ((leaf_jet_complex_manifold L).2.2.2.1 c).2.2 s hb
    have hunit : (curveJet2Coeff L c s).1.2 = 1 := by
      rw [← hfirst.2, hs, ha]
    have hquad := (curve_jet_reparametrization L).2.2.1 ⟨1, mu⟩ s
    have hcoeff := congrArg Prod.snd (hquad.2.2 c hb)
    rw [ht] at hcoeff
    rw [hcoeff, hunit]
    simp only [Units.val_one, one_pow, one_mul, mul_one]
    rw [sub_sub_cancel_left, norm_neg]
  have iteratedJetRestrictions {ι : Type u} (L : ι → Type u)
      [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
      [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
      [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]
      (perm : ι → ι)
      (G : ∀ i, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L (perm i)) ∞)
      (Ψ1 : NativeLeafwiseJet1 L → NativeLeafwiseJet1 L)
      (Ψ2 : NativeLeafwiseJet2 L → NativeLeafwiseJet2 L)
      (hrep : ∀ i (γ : CurveParamGerm (L i)),
        ∃ δ : CurveParamGerm (L (perm i)), δ.val = γ.val.map (G i) ∧
          Ψ1 ⟨i, curveJet1Class (L i) γ⟩ = ⟨perm i, curveJet1Class (L (perm i)) δ⟩ ∧
          Ψ2 ⟨i, curveJet2Class (L i) γ⟩ = ⟨perm i, curveJet2Class (L (perm i)) δ⟩) :
      letI := nativeLeafJet1Charts L
      letI := nativeLeafJet2Charts L
      ∀ n i, ∃ (k : ι)
        (E1 : Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (CurveJet1 (L i)) (CurveJet1 (L k)) ∞)
        (E2 : Diffeomorph 𝓘(ℂ, (ℂ × ℂ) × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) (CurveJet2 (L i)) (CurveJet2 (L k)) ∞),
        (∀ j, Ψ1^[n] ⟨i, j⟩ = ⟨k, E1 j⟩) ∧
        (∀ j, Ψ2^[n] ⟨i, j⟩ = ⟨k, E2 j⟩) := by
    let := nativeLeafJet1Charts L
    let := nativeLeafJet2Charts L
    let := nativeLeafJet1Manifold L
    let := nativeLeafJet2Manifold L
    have hAtlases (i : ι) : CurveJetCoefficientAtlases (L i)
        (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i) := by
      obtain ⟨_, _, _, _, h1,h2,_,_,_,_,_,hc,hs1,hs2⟩ :=
        (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose_spec
      exact ⟨h1,h2,hc,hs1,hs2⟩
    have hstep (i : ι) : ∃
        (E1 : Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (CurveJet1 (L i)) (CurveJet1 (L (perm i))) ∞)
        (E2 : Diffeomorph 𝓘(ℂ, (ℂ × ℂ) × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) (CurveJet2 (L i)) (CurveJet2 (L (perm i))) ∞),
        (∀ j, Ψ1 ⟨i, j⟩ = ⟨perm i, E1 j⟩) ∧
        (∀ j, Ψ2 ⟨i, j⟩ = ⟨perm i, E2 j⟩) := by
      obtain ⟨E1,E2,hE1,hE2⟩ := curve_postcompose_jet_diffeomorph_smooth
        ⟨hAtlases i, hAtlases (perm i)⟩ (G i)
      refine ⟨E1,E2,?_,?_⟩
      · intro j
        obtain ⟨γ, rfl⟩ := Quotient.exists_rep j
        obtain ⟨δ,hδ,h1,h2⟩ := hrep i γ
        have he : δ = curveParamGermPostcompose (G i) γ := Subtype.ext hδ
        change Ψ1 ⟨i, curveJet1Class (L i) γ⟩ = ⟨perm i, E1 (curveJet1Class (L i) γ)⟩
        rw [hE1, ← he]
        exact h1
      · intro j
        obtain ⟨γ, rfl⟩ := Quotient.exists_rep j
        obtain ⟨δ,hδ,h1,h2⟩ := hrep i γ
        have he : δ = curveParamGermPostcompose (G i) γ := Subtype.ext hδ
        change Ψ2 ⟨i, curveJet2Class (L i) γ⟩ = ⟨perm i, E2 (curveJet2Class (L i) γ)⟩
        rw [hE2, ← he]
        exact h2
    intro n
    induction n with
    | zero =>
      intro i
      exact ⟨i, Diffeomorph.refl _ _ _, Diffeomorph.refl _ _ _, fun _ ↦ rfl, fun _ ↦ rfl⟩
    | succ n ih =>
      intro i
      obtain ⟨k,E1,E2,hE1,hE2⟩ := ih i
      obtain ⟨F1,F2,hF1,hF2⟩ := hstep k
      refine ⟨perm k,E1.trans F1,E2.trans F2,?_,?_⟩
      · intro j
        rw [Function.iterate_succ_apply', hE1, hF1]
        rfl
      · intro j
        rw [Function.iterate_succ_apply', hE2, hF2]
        rfl
  classical
  let := nativeLeafJet1Charts L
  let := nativeLeafJet2Charts L
  let := nativeLeafJet1Manifold L
  let := nativeLeafJet2Manifold L
  have hAtlases (i : ι) : CurveJetCoefficientAtlases (L i)
      (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i) := by
    obtain ⟨_, _, _, _, h1,h2,_,_,_,_,_,hc,hs1,hs2⟩ :=
      (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose_spec
    exact ⟨h1,h2,hc,hs1,hs2⟩
  have htruncIter (n : ℕ) (v : NativeLeafwiseJet2 L) :
      nativeLeafwiseJetTruncation L ((Φ₂.symm : _ → _)^[n] v) =
        (Φ₁.symm : _ → _)^[n] (nativeLeafwiseJetTruncation L v) := by
    have hback (v : NativeLeafwiseJet2 L) :
        nativeLeafwiseJetTruncation L (Φ₂.symm v) = Φ₁.symm (nativeLeafwiseJetTruncation L v) := by
      apply Φ₁.injective
      rw [← htrunc, Φ₂.apply_symm_apply, Φ₁.apply_symm_apply]
    induction n generalizing v with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply', hback, ih, iterate_succ_apply']
  have hbackSection (n : ℕ) (j : NativeLeafwiseJet1 L) :
      (Φ₂ : _ → _)^[n] (s ((Φ₁.symm : _ → _)^[n] j)) = s j := by
    induction n generalizing j with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply', iterate_succ_apply (Φ₁.symm : _ → _),
        ih, ← heq, Φ₁.apply_symm_apply]
  have hshiftIter (n : ℕ) (mu : ℂ) (v : NativeLeafwiseJet2 L) :
      (Φ₂ : _ → _)^[n] (nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩ v) =
        nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩ ((Φ₂ : _ → _)^[n] v) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply', ih, hshift, iterate_succ_apply']
  intro i τ hτ c A hA z hz
  obtain ⟨V,hV,hzV,hVc,hreceive⟩ := hdisks i c z hz
  obtain ⟨e1,e2,_,_,hes1,hes2,het1,het2,hec1,hec2,_,_,_,_⟩ := (hAtlases i).2.2.1 c
  let unit : ℂ → CurveJet1 (L i) := fun w ↦ e1.symm (w,1)
  have hunitTarget (w : ℂ) (hw : w ∈ V) : (w, (1 : ℂ)) ∈ e1.target := by
    rw [het1]
    exact ⟨hVc hw,one_ne_zero⟩
  have hunitBase (w : ℂ) (hw : w ∈ V) : curveJet1Base (L i) (unit w) ∈ c.val.source := by
    have hh := e1.map_target (hunitTarget w hw)
    rwa [hes1] at hh
  have hunitCoeff (w : ℂ) (hw : w ∈ V) : curveJet1Coeff (L i) c (unit w) = (w,1) :=
    (hec1 (e1.map_target (hunitTarget w hw))).symm.trans (e1.right_inv (hunitTarget w hw))
  let ρ : ℂ → ℝ := fun w ↦ ν ⟨i,unit w⟩
  have hρ : ContinuousOn ρ V :=
    hν.continuousOn.comp ((hinc i).continuousOn.comp
      (e1.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
        (fun w hw ↦ hunitTarget w hw)) (mapsTo_univ _ _)) (mapsTo_univ _ _)
  have hEach : ∀ᶠ n in atTop, ∃ An : ℂ → ℂ, DifferentiableOn ℂ An V ∧
      ∀ w ∈ V, ‖An w-A w‖ ≤ (B*C)*q^n*ρ w := by
    filter_upwards [hreceive] with n hn
    obtain ⟨k,hk⟩ := hn
    obtain ⟨ell,F1,F2,hF1,hF2⟩ := iteratedJetRestrictions L perm G
      (Φ₁.symm : _ → _) (Φ₂.symm : _ → _) hrep n i
    obtain ⟨sigma,hsigma,hsigmaEq⟩ := hhol k ell
    let S : Set (CurveJet1 (L i)) := {j | curveJet1Base (L i) j ∈ c.val.source ∧
      (curveJet1Coeff (L i) c j).1 ∈ V}
    have hreceive' (j : CurveJet1 (L i)) (hj : j ∈ S) :
        base (nativeLeafwiseJet1Inclusion L ell (F1 j)) ∈ K k := by
      change base ⟨ell,F1 j⟩ ∈ K k
      rw [← hF1]
      exact hk j hj.1 hj.2
    have htruncF (v : CurveJet2 (L i)) :
        curveJetTruncation (L ell) (F2 v) = F1 (curveJetTruncation (L i) v) := by
      have hh := htruncIter n ⟨i,v⟩
      rw [hF2] at hh
      change (⟨ell,curveJetTruncation (L ell) (F2 v)⟩ : NativeLeafwiseJet1 L) =
        (Φ₁.symm : _ → _)^[n] ⟨i,curveJetTruncation (L i) v⟩ at hh
      rw [hF1] at hh
      exact eq_of_heq (Sigma.mk.inj hh).2
    let tn : CurveJet1 (L i) → CurveJet2 (L i) := fun j ↦ F2.symm (sigma (F1 j))
    have htntrunc (j : CurveJet1 (L i)) (hj : j ∈ S) : curveJetTruncation (L i) (tn j) = j := by
      have hh := hsloc k ⟨nativeLeafwiseJet1Inclusion L ell (F1 j), hKO k (hreceive' j hj)⟩
      rw [hsigmaEq _ (hKO k (hreceive' j hj))] at hh
      have hh' : curveJetTruncation (L ell) (sigma (F1 j)) = F1 j :=
        eq_of_heq (Sigma.mk.inj hh).2
      apply F1.injective
      change F1 (curveJetTruncation (L i) (tn j)) = F1 j
      rw [← htruncF]
      change curveJetTruncation (L ell) (F2 (F2.symm (sigma (F1 j)))) = F1 j
      rw [F2.apply_symm_apply,hh']
    have htnhol : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ tn S :=
      F2.symm.contMDiff.comp_contMDiffOn (hsigma.comp F1.contMDiff.contMDiffOn
        (fun j hj ↦ hKO k (hreceive' j hj)))
    obtain ⟨An,hAn,hAnCoeff⟩ := holomorphicUnitCoefficient (L i)
      (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i) (hAtlases i) tn c V hVc S
      (fun j hj hw ↦ ⟨hj,hw⟩) htntrunc htnhol
    refine ⟨An,hAn,?_⟩
    intro w hw
    let j := unit w
    have hjS : j ∈ S := ⟨hunitBase w hw,by rw [hunitCoeff w hw]; exact hw⟩
    have hbK : base ((Φ₁.symm : _ → _)^[n] ⟨i,j⟩) ∈ K k := hk j hjS.1 hjS.2
    obtain ⟨mu,hmu,hbound⟩ := herror k _ hbK
    have htransport := congrArg ((Φ₂ : _ → _)^[n]) hmu
    rw [hshiftIter,hbackSection] at htransport
    have hforward (v : CurveJet2 (L ell)) :
        (Φ₂ : _ → _)^[n] (nativeLeafwiseJet2Inclusion L ell v) =
          nativeLeafwiseJet2Inclusion L i (F2.symm v) := by
      have hh := hF2 (F2.symm v)
      rw [F2.apply_symm_apply] at hh
      change (Φ₂ : _ → _)^[n] ⟨ell,v⟩ = ⟨i,F2.symm v⟩
      rw [← hh]
      exact (show LeftInverse (Φ₂ : _ → _) (Φ₂.symm : _ → _) from Φ₂.apply_symm_apply).iterate n _
    have hlocEq : sloc k ⟨(Φ₁.symm : _ → _)^[n] ⟨i,j⟩,hKO k hbK⟩ =
        nativeLeafwiseJet2Inclusion L ell (sigma (F1 j)) := by
      have hh := hsigmaEq (F1 j) (hKO k (hreceive' j hjS))
      convert hh using 1
      apply congrArg (sloc k)
      apply Subtype.ext
      exact hF1 j
    rw [hlocEq,hforward] at htransport
    change nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩
      (s (nativeLeafwiseJet1Inclusion L i j)) = _ at htransport
    rw [hτ] at htransport
    have htransport' : curveJet2Reparametrize (L i) ⟨1,mu⟩ (τ j) = tn j :=
      eq_of_heq (Sigma.mk.inj htransport).2
    have hτtrunc : curveJetTruncation (L i) (τ j) = j := by
      have hh := hs (nativeLeafwiseJet1Inclusion L i j)
      rw [hτ] at hh
      exact eq_of_heq (Sigma.mk.inj hh).2
    have hAnEq := hAnCoeff w hw j (hunitBase w hw) (hunitCoeff w hw)
    have hAEq := hA j (hunitBase w hw)
    rw [hunitCoeff w hw] at hAEq
    simp only [one_pow,mul_one] at hAEq
    calc
      ‖An w-A w‖ = ‖mu‖ := by
        rw [← hAnEq,← hAEq]
        exact unitCoefficientShift (L i) c j (τ j) (tn j) hτtrunc (hunitBase w hw)
          (congrArg Prod.snd (hunitCoeff w hw)) mu htransport'
      _ ≤ B * ν ((Φ₁.symm : _ → _)^[n] ⟨i,j⟩) := hbound
      _ ≤ B * (C*q^n*ν ⟨i,j⟩) := mul_le_mul_of_nonneg_left (hdecay n _) hB
      _ = (B*C)*q^n*ρ w := by ring
  let Good (n : ℕ) (An : ℂ → ℂ) := DifferentiableOn ℂ An V ∧
    ∀ w ∈ V, ‖An w-A w‖ ≤ (B*C)*q^n*ρ w
  let F (n : ℕ) : ℂ → ℂ := if hn : ∃ An, Good n An then hn.choose else 0
  have hF (n : ℕ) (hn : ∃ An, Good n An) : Good n (F n) := by
    simp only [F,dite_eq_left hn]
    exact hn.choose_spec
  refine ⟨V,F,ρ,B*C,q,hV,hzV,hVc,hρ,mul_nonneg hB hC,hq,hq1,?_,?_⟩
  · filter_upwards [hEach] with n hn
    exact (hF n hn).1
  · filter_upwards [hEach] with n hn
    exact (hF n hn).2

end HolomorphicAnosov.Ghys

