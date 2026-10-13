import HolomorphicAnosov.Ghys.CurveFirstReparam
import HolomorphicAnosov.Ghys.CurveSecondReparam
import HolomorphicAnosov.Ghys.CurveGermBaseReparam
import HolomorphicAnosov.Ghys.CurveReparamSecondCoeff

/-! Rational source actions on first and second curve jets, their coefficient formulas, and their
action laws. (Ghys, §3 p.591) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff

noncomputable section

namespace HolomorphicAnosov.Ghys

universe u

variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]

/-- Rational source reparametrization preserves first and second contact. (Ghys, p.591) -/
theorem curve_reparametrize_contact (p : CurveJetReparametrization)
    {γ δ : CurveParamGerm L} :
    (CurveContact1 L γ δ → CurveContact1 L (curveParamGermReparametrize L p γ)
      (curveParamGermReparametrize L p δ)) ∧
    (CurveContact2 L γ δ → CurveContact2 L (curveParamGermReparametrize L p γ)
      (curveParamGermReparametrize L p δ)) := by
  have hb (γ : CurveParamGerm L) :
      curveGermBase L (curveParamGermReparametrize L p γ).1 = curveGermBase L γ.1 :=
    base_reparam L p γ.1
  constructor
  · rintro ⟨hbase, c, hc, hfirst⟩
    refine ⟨(hb γ).trans (hbase.trans (hb δ).symm), c, (hb γ).symm ▸ hc, ?_⟩
    rw [curve_first_reparam L p γ c hc,
      curve_first_reparam L p δ c (hbase ▸ hc), hfirst]
  · rintro ⟨hbase, c, hc, hfirst, hsecond⟩
    refine ⟨(hb γ).trans (hbase.trans (hb δ).symm), c, (hb γ).symm ▸ hc, ?_, ?_⟩
    · rw [curve_first_reparam L p γ c hc,
        curve_first_reparam L p δ c (hbase ▸ hc), hfirst]
    · rw [curve_second_reparam L p γ c hc,
        curve_second_reparam L p δ c (hbase ▸ hc), hfirst, hsecond]

variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]

/-- The action of nonzero source scaling on first curve jets. (Ghys, p.591) -/
def curveJet1Scale (omega : ℂˣ) : CurveJet1 L → CurveJet1 L :=
  Quotient.map (curveParamGermReparametrize L (.scale omega))
    (fun _ _ h ↦ (curve_reparametrize_contact L (.scale omega)).1 h)

/-- The action of rational source reparametrization on second curve jets. (Ghys, p.591) -/
def curveJet2Reparametrize (p : CurveJetReparametrization) : CurveJet2 L → CurveJet2 L :=
  Quotient.map (curveParamGermReparametrize L p)
    (fun _ _ h ↦ (curve_reparametrize_contact L p).2 h)

/-- Rational reparametrization acts on jet representatives, preserves bases, commutes with
truncation, and transforms coefficients by `(z,a,b) ↦ (z,omega*a,omega²*b-omega*mu*a)`, with
identity, composition, and inverse laws. The parameters with `omega = 1` act freely and transitively
on each truncation fibre. (Ghys, p.591) -/
theorem curve_jet_reparametrization [T2Space L] [SecondCountableTopology L] :
    (∀ (p : CurveJetReparametrization) (γ : CurveParamGerm L),
      curveJet2Reparametrize L p (curveJet2Class L γ) =
        curveJet2Class L (curveParamGermReparametrize L p γ)) ∧
    (∀ (omega : ℂˣ) (γ : CurveParamGerm L),
      curveJet1Scale L omega (curveJet1Class L γ) =
        curveJet1Class L (curveParamGermReparametrize L (.scale omega) γ)) ∧
    (∀ (p : CurveJetReparametrization) (j : CurveJet2 L),
      curveJet2Base L (curveJet2Reparametrize L p j) = curveJet2Base L j ∧
      curveJetTruncation L (curveJet2Reparametrize L p j) =
        curveJet1Scale L p.omega (curveJetTruncation L j) ∧
      ∀ c : LeafChart L, curveJet2Base L j ∈ c.1.source →
        curveJet2Coeff L c (curveJet2Reparametrize L p j) =
          (((curveJet2Coeff L c j).1.1,
            (p.omega : ℂ) * (curveJet2Coeff L c j).1.2),
            (p.omega : ℂ) ^ 2 * (curveJet2Coeff L c j).2 -
              (p.omega : ℂ) * p.mu * (curveJet2Coeff L c j).1.2)) ∧
    (∀ (omega : ℂˣ) (j : CurveJet1 L),
      curveJet1Base L (curveJet1Scale L omega j) = curveJet1Base L j ∧
      ∀ c : LeafChart L, curveJet1Base L j ∈ c.1.source →
        curveJet1Coeff L c (curveJet1Scale L omega j) =
          ((curveJet1Coeff L c j).1, (omega : ℂ) * (curveJet1Coeff L c j).2)) ∧
    (∀ j : CurveJet2 L, curveJet2Reparametrize L (.scale 1) j = j) ∧
    (∀ j : CurveJet1 L, curveJet1Scale L 1 j = j) ∧
    (∀ (p q : CurveJetReparametrization) (j : CurveJet2 L),
      curveJet2Reparametrize L p (curveJet2Reparametrize L q j) =
        curveJet2Reparametrize L (p.compose q) j) ∧
    (∀ (omega η : ℂˣ) (j : CurveJet1 L),
      curveJet1Scale L omega (curveJet1Scale L η j) = curveJet1Scale L (η * omega) j) ∧
    (∀ (p : CurveJetReparametrization) (j : CurveJet2 L),
      curveJet2Reparametrize L p.inverse (curveJet2Reparametrize L p j) = j ∧
      curveJet2Reparametrize L p (curveJet2Reparametrize L p.inverse j) = j) ∧
    (∀ j k : CurveJet2 L, curveJetTruncation L j = curveJetTruncation L k →
      ∃! μ : ℂ, curveJet2Reparametrize L ⟨1, μ⟩ j = k) := by
  have hd (p : CurveJetReparametrization) : deriv p.apply 0 = (p.omega : ℂ) := by
    have h := ((hasDerivAt_id (0 : ℂ)).const_mul (p.omega : ℂ)).div
      ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add
        ((hasDerivAt_id (0 : ℂ)).const_mul p.mu)) (by simp)
    convert h.deriv using 1 <;> simp
    rfl
  have hb (p : CurveJetReparametrization) (γ : CurveParamGerm L) :
      curveGermBase L (curveParamGermReparametrize L p γ).1 = curveGermBase L γ.1 :=
    base_reparam L p γ.1
  have hj := (leaf_jet_complex_manifold L).2.1
  have hc := (leaf_jet_complex_manifold L).2.2.2.1
  have h2 (p : CurveJetReparametrization) (j : CurveJet2 L) :
      curveJet2Base L (curveJet2Reparametrize L p j) = curveJet2Base L j ∧
      curveJetTruncation L (curveJet2Reparametrize L p j) =
        curveJet1Scale L p.omega (curveJetTruncation L j) ∧
      ∀ c : LeafChart L, curveJet2Base L j ∈ c.1.source →
        curveJet2Coeff L c (curveJet2Reparametrize L p j) =
          (((curveJet2Coeff L c j).1.1,
            (p.omega : ℂ) * (curveJet2Coeff L c j).1.2),
            (p.omega : ℂ) ^ 2 * (curveJet2Coeff L c j).2 -
              (p.omega : ℂ) * p.mu * (curveJet2Coeff L c j).1.2) := by
    refine Quotient.inductionOn j ?_
    intro γ
    rw [show (⟦γ⟧ : CurveJet2 L) = curveJet2Class L γ from rfl]
    change curveJet2Base L (curveJet2Class L (curveParamGermReparametrize L p γ)) = _ ∧ _
    refine ⟨by rw [(hj _).2.1, hb, (hj _).2.1], ?_, ?_⟩
    · change curveJet1Class L (curveParamGermReparametrize L p γ) =
        curveJet1Class L (curveParamGermReparametrize L (.scale p.omega) γ)
      apply Quotient.sound
      let c : LeafChart L := ⟨chartAt ℂ (curveGermBase L γ.1), IsManifold.chart_mem_maximalAtlas _⟩
      have hs : curveGermBase L γ.1 ∈ c.1.source := mem_chart_source ℂ _
      refine ⟨(hb p γ).trans (hb (.scale p.omega) γ).symm, c, (hb p γ).symm ▸ hs, ?_⟩
      rw [curve_first_reparam L p γ c hs, curve_first_reparam L (.scale p.omega) γ c hs,
        hd, hd]
      rfl
    · intro c hs
      rw [(hj γ).2.1] at hs
      rw [show curveJet2Reparametrize L p (curveJet2Class L γ) =
        curveJet2Class L (curveParamGermReparametrize L p γ) from rfl]
      rw [(hj (curveParamGermReparametrize L p γ)).2.2.2 c ((hb p γ).symm ▸ hs) |>.2.2,
        (hj γ).2.2.2 c hs |>.2.2]
      rw [hb, curve_first_reparam L p γ c hs, curve_second_reparam L p γ c hs,
        hd, reparam_second_coeff]
      dsimp
      congr 2
      ring
  have h1 (omega : ℂˣ) (j : CurveJet1 L) :
      curveJet1Base L (curveJet1Scale L omega j) = curveJet1Base L j ∧
      ∀ c : LeafChart L, curveJet1Base L j ∈ c.1.source →
        curveJet1Coeff L c (curveJet1Scale L omega j) =
          ((curveJet1Coeff L c j).1, (omega : ℂ) * (curveJet1Coeff L c j).2) := by
    refine Quotient.inductionOn j ?_
    intro γ
    rw [show (⟦γ⟧ : CurveJet1 L) = curveJet1Class L γ from rfl]
    change curveJet1Base L (curveJet1Class L (curveParamGermReparametrize L (.scale omega) γ)) = _ ∧ _
    refine ⟨by rw [(hj _).1, hb, (hj _).1], ?_⟩
    intro c hs
    rw [(hj γ).1] at hs
    rw [show curveJet1Scale L omega (curveJet1Class L γ) =
      curveJet1Class L (curveParamGermReparametrize L (.scale omega) γ) from rfl]
    rw [(hj (curveParamGermReparametrize L (.scale omega) γ)).2.2.2 c
      ((hb (.scale omega) γ).symm ▸ hs) |>.2.1, (hj γ).2.2.2 c hs |>.2.1]
    rw [hb, curve_first_reparam L (.scale omega) γ c hs, hd]
    rfl
  have ext2 (j k : CurveJet2 L) (hbase : curveJet2Base L j = curveJet2Base L k)
      (heq : ∀ c : LeafChart L, curveJet2Base L j ∈ c.1.source →
        curveJet2Coeff L c j = curveJet2Coeff L c k) : j = k := by
    let c : LeafChart L := ⟨chartAt ℂ (curveJet2Base L j), IsManifold.chart_mem_maximalAtlas _⟩
    have hs : curveJet2Base L j ∈ c.1.source := mem_chart_source ℂ _
    exact (hc c).2.1.injOn hs (show curveJet2Base L k ∈ c.1.source from hbase ▸ hs) (heq c hs)
  have ext1 (j k : CurveJet1 L) (hbase : curveJet1Base L j = curveJet1Base L k)
      (heq : ∀ c : LeafChart L, curveJet1Base L j ∈ c.1.source →
        curveJet1Coeff L c j = curveJet1Coeff L c k) : j = k := by
    let c : LeafChart L := ⟨chartAt ℂ (curveJet1Base L j), IsManifold.chart_mem_maximalAtlas _⟩
    have hs : curveJet1Base L j ∈ c.1.source := mem_chart_source ℂ _
    exact (hc c).1.injOn hs (show curveJet1Base L k ∈ c.1.source from hbase ▸ hs) (heq c hs)
  have hi2 (j : CurveJet2 L) : curveJet2Reparametrize L (.scale 1) j = j := by
    apply ext2 _ _ (h2 _ _).1
    intro c hs
    rw [(h2 _ _).1] at hs
    simpa [CurveJetReparametrization.scale] using (h2 (.scale 1) j).2.2 c hs
  have hi1 (j : CurveJet1 L) : curveJet1Scale L 1 j = j := by
    apply ext1 _ _ (h1 _ _).1
    intro c hs
    rw [(h1 _ _).1] at hs
    simpa using (h1 1 j).2 c hs
  have hm2 (p q : CurveJetReparametrization) (j : CurveJet2 L) :
      curveJet2Reparametrize L p (curveJet2Reparametrize L q j) =
        curveJet2Reparametrize L (p.compose q) j := by
    apply ext2 _ _ ((h2 _ _).1.trans ((h2 _ _).1.trans (h2 _ _).1.symm))
    intro c hs
    rw [(h2 _ _).1, (h2 _ _).1] at hs
    rw [(h2 _ _).2.2 c ((h2 _ _).1.symm ▸ hs), (h2 _ _).2.2 c hs,
      (h2 _ _).2.2 c hs]
    simp only [CurveJetReparametrization.compose, Units.val_mul]
    apply Prod.ext
    · apply Prod.ext <;> ring
    · dsimp
      ring
  have hm1 (omega η : ℂˣ) (j : CurveJet1 L) :
      curveJet1Scale L omega (curveJet1Scale L η j) = curveJet1Scale L (η * omega) j := by
    apply ext1 _ _ ((h1 _ _).1.trans ((h1 _ _).1.trans (h1 _ _).1.symm))
    intro c hs
    rw [(h1 _ _).1, (h1 _ _).1] at hs
    rw [(h1 _ _).2 c ((h1 _ _).1.symm ▸ hs), (h1 _ _).2 c hs, (h1 _ _).2 c hs]
    simp only [Units.val_mul]
    congr 1
    ring
  refine ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, h2, h1, hi2, hi1, hm2, hm1, ?_, ?_⟩
  · intro p j
    have hp : p.inverse.compose p = CurveJetReparametrization.scale 1 := by
      cases p with
      | mk omega mu =>
        simp [CurveJetReparametrization.compose, CurveJetReparametrization.inverse,
          CurveJetReparametrization.scale, div_eq_mul_inv]
    have hq : p.compose p.inverse = CurveJetReparametrization.scale 1 := by
      cases p with
      | mk omega mu =>
        simp [CurveJetReparametrization.compose, CurveJetReparametrization.inverse,
          CurveJetReparametrization.scale, div_eq_mul_inv]
    constructor
    · rw [hm2, hp, hi2]
    · rw [hm2, hq, hi2]
  · intro j k htr
    have htbase (a : CurveJet2 L) : curveJet1Base L (curveJetTruncation L a) = curveJet2Base L a := by
      let c : LeafChart L := ⟨chartAt ℂ (curveJet2Base L a), IsManifold.chart_mem_maximalAtlas _⟩
      exact ((hc c).2.2 a (mem_chart_source ℂ _)).1
    have hbases : curveJet2Base L j = curveJet2Base L k :=
      (htbase j).symm.trans ((congrArg (curveJet1Base L) htr).trans (htbase k))
    let c : LeafChart L := ⟨chartAt ℂ (curveJet2Base L j), IsManifold.chart_mem_maximalAtlas _⟩
    have hs : curveJet2Base L j ∈ c.1.source := mem_chart_source ℂ _
    have hks : curveJet2Base L k ∈ c.1.source := hbases ▸ hs
    have ha : (curveJet2Coeff L c j).1.2 ≠ 0 := ((hc c).2.1.mapsTo hs).2
    have hfirst : (curveJet2Coeff L c j).1 = (curveJet2Coeff L c k).1 :=
      ((hc c).2.2 j hs).2.symm.trans
        ((congrArg (curveJet1Coeff L c) htr).trans ((hc c).2.2 k hks).2)
    let μ := ((curveJet2Coeff L c j).2 - (curveJet2Coeff L c k).2) /
      (curveJet2Coeff L c j).1.2
    refine ⟨μ, ?_, ?_⟩
    · apply (hc c).2.1.injOn
        (show curveJet2Base L (curveJet2Reparametrize L ⟨1, μ⟩ j) ∈ c.1.source from
          (h2 _ _).1.symm ▸ hs) hks
      rw [(h2 ⟨1, μ⟩ j).2.2 c hs]
      simp only [Units.val_one, one_mul, one_pow]
      apply Prod.ext
      · exact hfirst
      · dsimp [μ]
        field_simp
        ring
    · intro ν hν
      have he := congrArg (fun a : CurveJet2 L ↦ (curveJet2Coeff L c a).2) hν
      rw [(h2 ⟨1, ν⟩ j).2.2 c hs] at he
      simp only [Units.val_one, one_pow, one_mul] at he
      change ν = ((curveJet2Coeff L c j).2 - (curveJet2Coeff L c k).2) /
        (curveJet2Coeff L c j).1.2
      apply (eq_div_iff ha).mpr
      linear_combination -he




end HolomorphicAnosov.Ghys


