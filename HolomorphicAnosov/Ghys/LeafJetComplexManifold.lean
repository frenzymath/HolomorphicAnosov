import HolomorphicAnosov.Ghys.CurveQuadraticParametrization
import HolomorphicAnosov.Ghys.GeneratedCoefficientAtlas
import HolomorphicAnosov.Ghys.ScalarTwoJetTransitionRegular
import HolomorphicAnosov.Ghys.ProjectedAtlasTopology
import HolomorphicAnosov.Ghys.CurveChartParametrizationRegular
import HolomorphicAnosov.Ghys.CurveChartTwoJetTransport
import HolomorphicAnosov.Ghys.JetGermQuotient
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! One- and two-jets into a complex curve. Source: Ghys §3 p.591. -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff

noncomputable section

namespace HolomorphicAnosov.Ghys

universe u

variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]

/-- Original compatible holomorphic charts, including restrictions and changes of chart. Source: Ghys p.591. -/
abbrev LeafChart := {c : OpenPartialHomeomorph L ℂ //
  c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L}

/-- Germs with values in the original curve, not scalar germs. Source: Ghys p.591. -/
abbrev CurveGerm := Filter.Germ (𝓝 (0 : ℂ)) L

omit [TopologicalSpace L] [ChartedSpace ℂ L] in
/-- Evaluation at zero descends through the neighborhood-germ relation. Source: Ghys p.591. -/
theorem curve_germ_base_respects {f g : ℂ → L} (h : f =ᶠ[𝓝 (0 : ℂ)] g) :
    f 0 = g 0 := by
  exact h.eq_of_nhds

/-- Base of an L-valued germ. Source: Ghys p.591. -/
def curveGermBase (γ : CurveGerm L) : L :=
  γ.liftOn (fun f ↦ f 0) (fun _ _ h ↦ curve_germ_base_respects L h)

/-- A germ represented near zero by an actual local holomorphic biholomorphism. Source: Ghys p.591. -/
def CurveGermAdmissible (γ : CurveGerm L) : Prop :=
  ∃ e : OpenPartialHomeomorph ℂ L,
    0 ∈ e.source ∧
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ e e.source ∧
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ∞ e.symm e.target ∧
    ((e : ℂ → L) : CurveGerm L) = γ

/-- Parametrization germs into the original curve. Source: Ghys p.591. -/
abbrev CurveParamGerm := {γ : CurveGerm L // CurveGermAdmissible L γ}

/-- The actual first coefficient in one compatible chart. Source: Ghys p.591. -/
def curveGermFirst (c : LeafChart L) (γ : CurveParamGerm L) : ℂ :=
  germFirst (γ.1.map (c.1 : L → ℂ))

/-- The actual second derivative divided by two in one chart. Source: Ghys p.591. -/
def curveGermSecond (c : LeafChart L) (γ : CurveParamGerm L) : ℂ :=
  germSecond (γ.1.map (c.1 : L → ℂ))

/-- First contact uses one common chart at the common base. Source: Ghys p.591. -/
def CurveContact1 (γ δ : CurveParamGerm L) : Prop :=
  curveGermBase L γ.1 = curveGermBase L δ.1 ∧
    ∃ c : LeafChart L, curveGermBase L γ.1 ∈ c.1.source ∧
      curveGermFirst L c γ = curveGermFirst L c δ

/-- Second contact adds equality of the normalized quadratic coefficient. Source: Ghys p.591. -/
def CurveContact2 (γ δ : CurveParamGerm L) : Prop :=
  curveGermBase L γ.1 = curveGermBase L δ.1 ∧
    ∃ c : LeafChart L, curveGermBase L γ.1 ∈ c.1.source ∧
      curveGermFirst L c γ = curveGermFirst L c δ ∧
      curveGermSecond L c γ = curveGermSecond L c δ

/-- Contact is chart-independent and is an equivalence relation.591 and Michor pp.2–3. -/
theorem curve_contact_equivalences
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L] :
    Equivalence (CurveContact1 L) ∧ Equivalence (CurveContact2 L) := by
  have hchange (c d : LeafChart L) (γ : CurveParamGerm L)
      (hc : curveGermBase L γ.1 ∈ c.1.source)
      (hd : curveGermBase L γ.1 ∈ d.1.source) :
      curveGermFirst L d γ =
          deriv (d.1 ∘ c.1.symm) (c.1 (curveGermBase L γ.1)) * curveGermFirst L c γ ∧
      curveGermSecond L d γ =
          deriv (d.1 ∘ c.1.symm) (c.1 (curveGermBase L γ.1)) * curveGermSecond L c γ +
          (iteratedDeriv 2 (d.1 ∘ c.1.symm) (c.1 (curveGermBase L γ.1)) / 2) *
            curveGermFirst L c γ ^ 2 := by
    obtain ⟨g, hg0, hg, _, hge⟩ := γ.2
    have hb : curveGermBase L γ.1 = g 0 := by rw [← hge]; rfl
    rw [hb] at hc hd
    have ht := curve_chart_two_jet_transport c.1 d.1 c.2 d.2 g
      (hg.contMDiffAt (g.open_source.mem_nhds hg0)) hc hd
    unfold curveGermFirst curveGermSecond
    rw [← hge]
    exact ht
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro γ
      exact ⟨rfl, ⟨chartAt ℂ (curveGermBase L γ.1),
        IsManifold.chart_mem_maximalAtlas _⟩, mem_chart_source ℂ _, rfl⟩
    · intro γ δ h
      obtain ⟨hbase, c, hc, hfirst⟩ := h
      exact ⟨hbase.symm, c, hbase ▸ hc, hfirst.symm⟩
    · intro γ δ ε hγδ hδε
      obtain ⟨hγδ, c, hc, hfirst⟩ := hγδ
      obtain ⟨hδε, d, hd, hfirst'⟩ := hδε
      have hcδ : curveGermBase L δ.1 ∈ c.1.source := hγδ ▸ hc
      have hcε : curveGermBase L ε.1 ∈ c.1.source := hδε ▸ hcδ
      have hdε : curveGermBase L ε.1 ∈ d.1.source := hδε ▸ hd
      refine ⟨hγδ.trans hδε, c, hc, hfirst.trans ?_⟩
      rw [(hchange d c δ hd hcδ).1, (hchange d c ε hdε hcε).1, hδε, hfirst']
  · refine ⟨?_, ?_, ?_⟩
    · intro γ
      exact ⟨rfl, ⟨chartAt ℂ (curveGermBase L γ.1),
        IsManifold.chart_mem_maximalAtlas _⟩, mem_chart_source ℂ _, rfl, rfl⟩
    · intro γ δ h
      obtain ⟨hbase, c, hc, hfirst, hsecond⟩ := h
      exact ⟨hbase.symm, c, hbase ▸ hc, hfirst.symm, hsecond.symm⟩
    · intro γ δ ε hγδ hδε
      obtain ⟨hγδ, c, hc, hfirst, hsecond⟩ := hγδ
      obtain ⟨hδε, d, hd, hfirst', hsecond'⟩ := hδε
      have hcδ : curveGermBase L δ.1 ∈ c.1.source := hγδ ▸ hc
      have hcε : curveGermBase L ε.1 ∈ c.1.source := hδε ▸ hcδ
      have hdε : curveGermBase L ε.1 ∈ d.1.source := hδε ▸ hd
      refine ⟨hγδ.trans hδε, c, hc, hfirst.trans ?_, hsecond.trans ?_⟩
      · rw [(hchange d c δ hd hcδ).1, (hchange d c ε hdε hcε).1, hδε, hfirst']
      · rw [(hchange d c δ hd hcδ).2, (hchange d c ε hdε hcε).2,
          hδε, hfirst', hsecond']

/-- The first-contact setoid on the original germ carrier. Source: Ghys p.591. -/
def curveContactSetoid1 [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L] :
    Setoid (CurveParamGerm L) :=
  ⟨CurveContact1 L, (curve_contact_equivalences L).1⟩

/-- The second-contact setoid on the original germ carrier. Source: Ghys p.591. -/
def curveContactSetoid2 [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L] :
    Setoid (CurveParamGerm L) :=
  ⟨CurveContact2 L, (curve_contact_equivalences L).2⟩

variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]

/-- One-jets are the actual first-contact quotient. Source: Ghys p.591. -/
abbrev CurveJet1 := Quotient (curveContactSetoid1 L)

/-- Two-jets are the actual second-contact quotient. Source: Ghys p.591. -/
abbrev CurveJet2 := Quotient (curveContactSetoid2 L)

/-- Class of the same original germ at order one. Source: Ghys p.591. -/
def curveJet1Class (γ : CurveParamGerm L) : CurveJet1 L :=
  Quotient.mk (curveContactSetoid1 L) γ

/-- Class of the same original germ at order two. Source: Ghys p.591. -/
def curveJet2Class (γ : CurveParamGerm L) : CurveJet2 L :=
  Quotient.mk (curveContactSetoid2 L) γ

/-- Base projection, computed from a quotient representative. Source: Ghys p.591. -/
def curveJet1Base (j : CurveJet1 L) : L := curveGermBase L j.out.1

/-- Base projection at order two. Source: Ghys p.591. -/
def curveJet2Base (j : CurveJet2 L) : L := curveGermBase L j.out.1

/-- Global extension of a coefficient chart, used only over the chart's base source. Source: Ghys p.591. -/
def curveJet1Coeff (c : LeafChart L) (j : CurveJet1 L) : ℂ × ℂ :=
  (c.1 (curveJet1Base L j), curveGermFirst L c j.out)

/-- Order-two coefficient chart with the normalized quadratic coefficient. Source: Ghys p.591. -/
def curveJet2Coeff (c : LeafChart L) (j : CurveJet2 L) : (ℂ × ℂ) × ℂ :=
  ((c.1 (curveJet2Base L j), curveGermFirst L c j.out), curveGermSecond L c j.out)

/-- The coefficient-generated topology on the actual first-contact quotient. -/
instance curveJet1Topology : TopologicalSpace (CurveJet1 L) :=
  TopologicalSpace.generateFrom {s | ∃ c : LeafChart L, ∃ O : Set (ℂ × ℂ),
    IsOpen O ∧ s = {j | curveJet1Base L j ∈ c.1.source ∧ curveJet1Coeff L c j ∈ O}}

/-- The coefficient-generated topology on the actual second-contact quotient. -/
instance curveJet2Topology : TopologicalSpace (CurveJet2 L) :=
  TopologicalSpace.generateFrom {s | ∃ c : LeafChart L, ∃ O : Set ((ℂ × ℂ) × ℂ),
    IsOpen O ∧ s = {j | curveJet2Base L j ∈ c.1.source ∧ curveJet2Coeff L c j ∈ O}}

omit [IsManifold 𝓘(ℂ, ℂ) ∞ L] in
/-- Second contact forgets to first contact on the identical germ carrier. Source: Ghys p.591. -/
theorem curve_contact_truncates {γ δ : CurveParamGerm L} (h : CurveContact2 L γ δ) :
    CurveContact1 L γ δ := by
  obtain ⟨hbase, c, hc, hfirst, _⟩ := h
  exact ⟨hbase, c, hc, hfirst⟩

/-- Truncation sends the class of a germ to its first-contact class. Source: Ghys p.591. -/
def curveJetTruncation : CurveJet2 L → CurveJet1 L :=
  Quotient.map id (fun _ _ h ↦ curve_contact_truncates L h)

/-- First-order target-chart composition. Source: Michor pp.2–3. -/
def curveJet1Transition (h : ℂ → ℂ) (w : ℂ × ℂ) : ℂ × ℂ :=
  (h w.1, deriv h w.1 * w.2)

/-- Second-order target-chart composition, including its affine highest-coefficient term. Source: Michor pp.2–3. -/
def curveJet2Transition (h : ℂ → ℂ) (w : (ℂ × ℂ) × ℂ) : (ℂ × ℂ) × ℂ :=
  ((h w.1.1, deriv h w.1.1 * w.1.2),
    deriv h w.1.1 * w.2 + iteratedDeriv 2 h w.1.1 * w.1.2 ^ 2 / 2)

/-- First coefficient domain is the chart target times the nonzero complex scalars. Source: Ghys p.591. -/
def curveJet1Target (c : LeafChart L) : Set (ℂ × ℂ) :=
  {w | w.1 ∈ c.1.target ∧ w.2 ≠ 0}

/-- Second coefficient domain also has an unrestricted quadratic coefficient. Source: Ghys p.591. -/
def curveJet2Target (c : LeafChart L) : Set ((ℂ × ℂ) × ℂ) :=
  {w | w.1.1 ∈ c.1.target ∧ w.1.2 ≠ 0}

/-- The coefficient atlases on the two original germ-contact quotients. -/
theorem leaf_jet_complex_manifold [T2Space L] [SecondCountableTopology L] :
    (∀ (γ δ : CurveParamGerm L) (c : LeafChart L),
      curveGermBase L γ.1 ∈ c.1.source → curveGermBase L δ.1 ∈ c.1.source →
      (CurveContact1 L γ δ ↔ curveGermBase L γ.1 = curveGermBase L δ.1 ∧
        curveGermFirst L c γ = curveGermFirst L c δ) ∧
      (CurveContact2 L γ δ ↔ curveGermBase L γ.1 = curveGermBase L δ.1 ∧
        curveGermFirst L c γ = curveGermFirst L c δ ∧
        curveGermSecond L c γ = curveGermSecond L c δ)) ∧
    (∀ γ : CurveParamGerm L,
      curveJet1Base L (curveJet1Class L γ) = curveGermBase L γ.1 ∧
      curveJet2Base L (curveJet2Class L γ) = curveGermBase L γ.1 ∧
      curveJetTruncation L (curveJet2Class L γ) = curveJet1Class L γ ∧
      ∀ c : LeafChart L, curveGermBase L γ.1 ∈ c.1.source →
        GermAdmissible (γ.1.map (c.1 : L → ℂ)) ∧
        curveJet1Coeff L c (curveJet1Class L γ) =
          (c.1 (curveGermBase L γ.1), curveGermFirst L c γ) ∧
        curveJet2Coeff L c (curveJet2Class L γ) =
          ((c.1 (curveGermBase L γ.1), curveGermFirst L c γ),
            curveGermSecond L c γ)) ∧
    (∀ c d : LeafChart L,
      (∀ j : CurveJet1 L,
        curveJet1Base L j ∈ c.1.source ∩ d.1.source →
        curveJet1Coeff L d j =
          curveJet1Transition (d.1 ∘ c.1.symm) (curveJet1Coeff L c j)) ∧
      (∀ j : CurveJet2 L,
        curveJet2Base L j ∈ c.1.source ∩ d.1.source →
        curveJet2Coeff L d j =
          curveJet2Transition (d.1 ∘ c.1.symm) (curveJet2Coeff L c j))) ∧
    (∀ c : LeafChart L,
      BijOn (curveJet1Coeff L c) ((curveJet1Base L) ⁻¹' c.1.source)
        (curveJet1Target L c) ∧
      BijOn (curveJet2Coeff L c) ((curveJet2Base L) ⁻¹' c.1.source)
        (curveJet2Target L c) ∧
      ∀ j : CurveJet2 L, curveJet2Base L j ∈ c.1.source →
        curveJet1Base L (curveJetTruncation L j) = curveJet2Base L j ∧
        curveJet1Coeff L c (curveJetTruncation L j) = (curveJet2Coeff L c j).1) ∧
    ∃ (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
      (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)),
      letI := A1
      letI := A2
      T2Space (CurveJet1 L) ∧ T2Space (CurveJet2 L) ∧
      SecondCountableTopology (CurveJet1 L) ∧ SecondCountableTopology (CurveJet2 L) ∧
      IsManifold (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ (CurveJet1 L) ∧
      IsManifold (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ (CurveJet2 L) ∧
      Module.finrank ℂ (ℂ × ℂ) = 2 ∧ Module.finrank ℂ ((ℂ × ℂ) × ℂ) = 3 ∧
      Continuous (curveJet1Base L) ∧ Continuous (curveJet2Base L) ∧
      ContMDiff (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
        (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ (curveJetTruncation L) ∧
      (∀ c : LeafChart L,
        ∃ (e1 : OpenPartialHomeomorph (CurveJet1 L) (ℂ × ℂ))
          (e2 : OpenPartialHomeomorph (CurveJet2 L) ((ℂ × ℂ) × ℂ)),
          e1 ∈ atlas (ℂ × ℂ) (CurveJet1 L) ∧
          e2 ∈ atlas ((ℂ × ℂ) × ℂ) (CurveJet2 L) ∧
          e1.source = (curveJet1Base L) ⁻¹' c.1.source ∧
          e2.source = (curveJet2Base L) ⁻¹' c.1.source ∧
          e1.target = curveJet1Target L c ∧ e2.target = curveJet2Target L c ∧
          EqOn e1 (curveJet1Coeff L c) e1.source ∧
          EqOn e2 (curveJet2Coeff L c) e2.source ∧
          ContMDiffOn (modelWithCornersSelf ℂ (ℂ × ℂ))
            (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ e1 e1.source ∧
          ContMDiffOn (modelWithCornersSelf ℂ (ℂ × ℂ))
            (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ e1.symm e1.target ∧
          ContMDiffOn (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
            (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ e2 e2.source ∧
          ContMDiffOn (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
            (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ e2.symm e2.target) ∧
      (∀ e ∈ atlas (ℂ × ℂ) (CurveJet1 L), ∃ c : LeafChart L,
        e.source = (curveJet1Base L) ⁻¹' c.1.source ∧
        e.target = curveJet1Target L c ∧ EqOn e (curveJet1Coeff L c) e.source) ∧
      (∀ e ∈ atlas ((ℂ × ℂ) × ℂ) (CurveJet2 L), ∃ c : LeafChart L,
        e.source = (curveJet2Base L) ⁻¹' c.1.source ∧
        e.target = curveJet2Target L c ∧ EqOn e (curveJet2Coeff L c) e.source) := by
  have hchange (c d : LeafChart L) (γ : CurveParamGerm L)
      (hc : curveGermBase L γ.1 ∈ c.1.source)
      (hd : curveGermBase L γ.1 ∈ d.1.source) :
      curveGermFirst L d γ =
          deriv (d.1 ∘ c.1.symm) (c.1 (curveGermBase L γ.1)) * curveGermFirst L c γ ∧
      curveGermSecond L d γ =
          deriv (d.1 ∘ c.1.symm) (c.1 (curveGermBase L γ.1)) * curveGermSecond L c γ +
          (iteratedDeriv 2 (d.1 ∘ c.1.symm) (c.1 (curveGermBase L γ.1)) / 2) *
            curveGermFirst L c γ ^ 2 := by
    obtain ⟨g, hg0, hg, _, hge⟩ := γ.2
    have hb : curveGermBase L γ.1 = g 0 := by rw [← hge]; rfl
    rw [hb] at hc hd
    have ht := curve_chart_two_jet_transport c.1 d.1 c.2 d.2 g
      (hg.contMDiffAt (g.open_source.mem_nhds hg0)) hc hd
    unfold curveGermFirst curveGermSecond
    rw [← hge]
    exact ht
  have hcontact (γ δ : CurveParamGerm L) (c : LeafChart L)
      (hcγ : curveGermBase L γ.1 ∈ c.1.source)
      (hcδ : curveGermBase L δ.1 ∈ c.1.source) :
      (CurveContact1 L γ δ ↔ curveGermBase L γ.1 = curveGermBase L δ.1 ∧
        curveGermFirst L c γ = curveGermFirst L c δ) ∧
      (CurveContact2 L γ δ ↔ curveGermBase L γ.1 = curveGermBase L δ.1 ∧
        curveGermFirst L c γ = curveGermFirst L c δ ∧
        curveGermSecond L c γ = curveGermSecond L c δ) := by
    constructor
    · constructor
      · rintro ⟨hb, e, he, ha⟩
        refine ⟨hb, ?_⟩
        rw [(hchange e c γ he hcγ).1, (hchange e c δ (hb ▸ he) hcδ).1, hb, ha]
      · rintro ⟨hb, ha⟩
        exact ⟨hb, c, hcγ, ha⟩
    · constructor
      · rintro ⟨hb, e, he, ha, hb'⟩
        refine ⟨hb, ?_, ?_⟩
        · rw [(hchange e c γ he hcγ).1, (hchange e c δ (hb ▸ he) hcδ).1, hb, ha]
        · rw [(hchange e c γ he hcγ).2, (hchange e c δ (hb ▸ he) hcδ).2, hb, ha, hb']
      · rintro ⟨hb, ha, hb'⟩
        exact ⟨hb, c, hcγ, ha, hb'⟩
  have hregular (γ : CurveParamGerm L) (c : LeafChart L)
      (hc : curveGermBase L γ.1 ∈ c.1.source) : GermAdmissible (γ.1.map (c.1 : L → ℂ)) := by
    obtain ⟨g, hg0, hg, hgs, hge⟩ := γ.2
    have hc0 : g 0 ∈ c.1.source := by
      rw [← hge] at hc
      exact hc
    have ht := curve_chart_parametrization_regular c.1 c.2 g hg0 hg hgs hc0
    rw [← hge]
    exact ht
  have htrans : ∀ c d : LeafChart L,
      (∀ j : CurveJet1 L,
        curveJet1Base L j ∈ c.1.source ∩ d.1.source →
        curveJet1Coeff L d j =
          curveJet1Transition (d.1 ∘ c.1.symm) (curveJet1Coeff L c j)) ∧
      (∀ j : CurveJet2 L,
        curveJet2Base L j ∈ c.1.source ∩ d.1.source →
        curveJet2Coeff L d j =
          curveJet2Transition (d.1 ∘ c.1.symm) (curveJet2Coeff L c j)) := by
    intro c d
    constructor
    · intro j hj
      change curveGermBase L j.out.1 ∈ c.1.source ∩ d.1.source at hj
      have ht := (hchange c d j.out hj.1 hj.2).1
      change (d.1 (curveGermBase L j.out.1), curveGermFirst L d j.out) =
        (d.1 (c.1.symm (c.1 (curveGermBase L j.out.1))),
          deriv (d.1 ∘ c.1.symm) (c.1 (curveGermBase L j.out.1)) * curveGermFirst L c j.out)
      rw [c.1.left_inv hj.1, ht]
    · intro j hj
      change curveGermBase L j.out.1 ∈ c.1.source ∩ d.1.source at hj
      have ht := hchange c d j.out hj.1 hj.2
      change ((d.1 (curveGermBase L j.out.1), curveGermFirst L d j.out),
        curveGermSecond L d j.out) =
        ((d.1 (c.1.symm (c.1 (curveGermBase L j.out.1))),
          deriv (d.1 ∘ c.1.symm) (c.1 (curveGermBase L j.out.1)) * curveGermFirst L c j.out),
          deriv (d.1 ∘ c.1.symm) (c.1 (curveGermBase L j.out.1)) * curveGermSecond L c j.out +
          iteratedDeriv 2 (d.1 ∘ c.1.symm) (c.1 (curveGermBase L j.out.1)) *
            curveGermFirst L c j.out ^ 2 / 2)
      rw [c.1.left_inv hj.1, ht.1, ht.2]
      congr 1
      ring
  have hcoeff : ∀ c : LeafChart L,
      BijOn (curveJet1Coeff L c) ((curveJet1Base L) ⁻¹' c.1.source)
        (curveJet1Target L c) ∧
      BijOn (curveJet2Coeff L c) ((curveJet2Base L) ⁻¹' c.1.source)
        (curveJet2Target L c) ∧
      ∀ j : CurveJet2 L, curveJet2Base L j ∈ c.1.source →
        curveJet1Base L (curveJetTruncation L j) = curveJet2Base L j ∧
        curveJet1Coeff L c (curveJetTruncation L j) = (curveJet2Coeff L c j).1 := by
    intro c
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro j hj
      refine ⟨c.1.map_source hj, ?_⟩
      exact scalar_jet_germ_quotient.2.2.2.1
        (jet1Class ⟨j.out.1.map (c.1 : L → ℂ), hregular j.out c hj⟩)
    · intro j hj k hk heq
      have hb : curveJet1Base L j = curveJet1Base L k :=
        c.1.injOn hj hk (congrArg Prod.fst heq)
      have hrel : CurveContact1 L j.out k.out := ⟨hb, c, hj, congrArg Prod.snd heq⟩
      have hq := @Quotient.sound (CurveParamGerm L) (curveContactSetoid1 L) j.out k.out hrel
      simpa only [Quotient.out_eq] using hq
    ·
      rintro ⟨z, a⟩ ⟨hz, ha⟩
      obtain ⟨e, he0, he, hes, hb, hd, _⟩ :=
        curve_quadratic_parametrization c.1 c.2 z a 0 hz ha
      let γ : CurveParamGerm L := ⟨((e : ℂ → L) : CurveGerm L), e, he0, he, hes, rfl⟩
      have hγb : curveGermBase L γ.1 = c.1.symm z := hb
      have hγc : curveGermBase L γ.1 ∈ c.1.source := hγb ▸ c.1.map_target hz
      have hr : CurveContact1 L (curveJet1Class L γ).out γ :=
        Quotient.exact (Quotient.out_eq (curveJet1Class L γ))
      have hcj : curveJet1Base L (curveJet1Class L γ) ∈ c.1.source := by
        change curveGermBase L (curveJet1Class L γ).out.1 ∈ c.1.source
        rw [hr.1]
        exact hγc
      refine ⟨curveJet1Class L γ, hcj, ?_⟩
      have hc := ((hcontact _ _ c hcj hγc).1.mp hr).2
      change (c.1 (curveGermBase L (curveJet1Class L γ).out.1),
        curveGermFirst L c (curveJet1Class L γ).out) = (z, a)
      rw [hr.1, hc, hγb, c.1.right_inv hz]
      exact congrArg (fun t ↦ (z, t)) hd
    · intro j hj
      refine ⟨c.1.map_source hj, ?_⟩
      exact scalar_jet_germ_quotient.2.2.2.1
        (jet1Class ⟨j.out.1.map (c.1 : L → ℂ), hregular j.out c hj⟩)
    · intro j hj k hk heq
      have hb : curveJet2Base L j = curveJet2Base L k :=
        c.1.injOn hj hk (congrArg (fun w : (ℂ × ℂ) × ℂ ↦ w.1.1) heq)
      have hrel : CurveContact2 L j.out k.out :=
        ⟨hb, c, hj, congrArg (fun w : (ℂ × ℂ) × ℂ ↦ w.1.2) heq,
          congrArg Prod.snd heq⟩
      have hq := @Quotient.sound (CurveParamGerm L) (curveContactSetoid2 L) j.out k.out hrel
      simpa only [Quotient.out_eq] using hq
    ·
      rintro ⟨⟨z, a⟩, b⟩ ⟨hz, ha⟩
      obtain ⟨e, he0, he, hes, hb, hd, hdd⟩ :=
        curve_quadratic_parametrization c.1 c.2 z a b hz ha
      let γ : CurveParamGerm L := ⟨((e : ℂ → L) : CurveGerm L), e, he0, he, hes, rfl⟩
      have hγb : curveGermBase L γ.1 = c.1.symm z := hb
      have hγc : curveGermBase L γ.1 ∈ c.1.source := hγb ▸ c.1.map_target hz
      have hr : CurveContact2 L (curveJet2Class L γ).out γ :=
        Quotient.exact (Quotient.out_eq (curveJet2Class L γ))
      have hcj : curveJet2Base L (curveJet2Class L γ) ∈ c.1.source := by
        change curveGermBase L (curveJet2Class L γ).out.1 ∈ c.1.source
        rw [hr.1]
        exact hγc
      refine ⟨curveJet2Class L γ, hcj, ?_⟩
      have hc := ((hcontact _ _ c hcj hγc).2.mp hr).2
      change ((c.1 (curveGermBase L (curveJet2Class L γ).out.1),
        curveGermFirst L c (curveJet2Class L γ).out),
        curveGermSecond L c (curveJet2Class L γ).out) = ((z, a), b)
      rw [hr.1, hc.1, hc.2, hγb, c.1.right_inv hz]
      exact congrArg₂ (fun t s ↦ ((z, t), s)) hd hdd
    · intro j hj
      have hq : curveJet1Class L j.out = curveJetTruncation L j :=
        congrArg (curveJetTruncation L) (Quotient.out_eq j)
      have hr : CurveContact1 L (curveJetTruncation L j).out j.out :=
        Quotient.exact ((Quotient.out_eq (curveJetTruncation L j)).trans hq.symm)
      have hc : curveGermBase L (curveJetTruncation L j).out.1 ∈ c.1.source := hr.1.symm ▸ hj
      have ha := ((hcontact _ _ c hc hj).1.mp hr).2
      refine ⟨hr.1, ?_⟩
      change (c.1 (curveGermBase L (curveJetTruncation L j).out.1),
        curveGermFirst L c (curveJetTruncation L j).out) =
        (c.1 (curveGermBase L j.out.1), curveGermFirst L c j.out)
      rw [hr.1, ha]
  refine ⟨hcontact, ?_, ?_, ?_, ?_⟩
  · intro γ
    have h1 : CurveContact1 L (curveJet1Class L γ).out γ :=
      Quotient.exact (Quotient.out_eq (curveJet1Class L γ))
    have h2 : CurveContact2 L (curveJet2Class L γ).out γ :=
      Quotient.exact (Quotient.out_eq (curveJet2Class L γ))
    refine ⟨h1.1, h2.1, rfl, ?_⟩
    intro c hc
    have hc1 : curveGermBase L (curveJet1Class L γ).out.1 ∈ c.1.source := h1.1.symm ▸ hc
    have hc2 : curveGermBase L (curveJet2Class L γ).out.1 ∈ c.1.source := h2.1.symm ▸ hc
    have h1c := ((hcontact _ _ c hc1 hc).1.mp h1).2
    have h2c := ((hcontact _ _ c hc2 hc).2.mp h2).2
    refine ⟨?_, ?_, ?_⟩
    · exact hregular γ c hc
    · change (c.1 (curveGermBase L (curveJet1Class L γ).out.1),
        curveGermFirst L c (curveJet1Class L γ).out) = _
      rw [h1.1, h1c]
    · change ((c.1 (curveGermBase L (curveJet2Class L γ).out.1),
        curveGermFirst L c (curveJet2Class L γ).out),
        curveGermSecond L c (curveJet2Class L γ).out) = _
      rw [h2.1, h2c.1, h2c.2]
  · exact htrans
  · exact hcoeff
  ·
    classical
    rcases isEmpty_or_nonempty L with hL | hL
    · let : IsEmpty (CurveJet1 L) := ⟨fun j ↦ isEmptyElim (curveJet1Base L j)⟩
      let : IsEmpty (CurveJet2 L) := ⟨fun j ↦ isEmptyElim (curveJet2Base L j)⟩
      let A1 := ChartedSpace.empty (ℂ × ℂ) (CurveJet1 L)
      let A2 := ChartedSpace.empty ((ℂ × ℂ) × ℂ) (CurveJet2 L)
      refine ⟨A1, A2, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Module.finrank_prod]
      · simp [Module.finrank_prod]
      · exact continuous_iff_continuousAt.mpr fun j ↦ isEmptyElim j
      · exact continuous_iff_continuousAt.mpr fun j ↦ isEmptyElim j
      · exact fun j ↦ isEmptyElim j
      · intro c
        exact isEmptyElim (c.1.symm 0)
      · intro e he
        exact False.elim he
      · intro e he
        exact False.elim he
    · let x : L := Classical.choice hL
      let c₀ : LeafChart L := ⟨chartAt ℂ x, IsManifold.chart_mem_maximalAtlas x⟩
      have hx : x ∈ c₀.1.source := mem_chart_source ℂ x
      obtain ⟨j₁, _, _⟩ := (hcoeff c₀).1.surjOn
        (show (c₀.1 x, (1 : ℂ)) ∈ curveJet1Target L c₀ from
          ⟨c₀.1.map_source hx, one_ne_zero⟩)
      obtain ⟨j₂, _, _⟩ := (hcoeff c₀).2.1.surjOn
        (show ((c₀.1 x, (1 : ℂ)), (0 : ℂ)) ∈ curveJet2Target L c₀ from
          ⟨c₀.1.map_source hx, one_ne_zero⟩)
      let : Nonempty (CurveJet1 L) := ⟨j₁⟩
      let : Nonempty (CurveJet2 L) := ⟨j₂⟩
      let e1 (c : LeafChart L) : PartialEquiv (CurveJet1 L) (ℂ × ℂ) :=
        (hcoeff c).1.toPartialEquiv _ _ _
      let e2 (c : LeafChart L) : PartialEquiv (CurveJet2 L) ((ℂ × ℂ) × ℂ) :=
        (hcoeff c).2.1.toPartialEquiv _ _ _
      have hb1 (c : LeafChart L) (w : ℂ × ℂ) (hw : w ∈ (e1 c).target) :
          curveJet1Base L ((e1 c).symm w) = c.1.symm w.1 := by
        have heq := congrArg Prod.fst ((e1 c).right_inv hw)
        change c.1 (curveJet1Base L ((e1 c).symm w)) = w.1 at heq
        rw [← heq, c.1.left_inv ((e1 c).map_target hw)]
      have hb2 (c : LeafChart L) (w : (ℂ × ℂ) × ℂ) (hw : w ∈ (e2 c).target) :
          curveJet2Base L ((e2 c).symm w) = c.1.symm w.1.1 := by
        have heq := congrArg (fun v : (ℂ × ℂ) × ℂ ↦ v.1.1) ((e2 c).right_inv hw)
        change c.1 (curveJet2Base L ((e2 c).symm w)) = w.1.1 at heq
        rw [← heq, c.1.left_inv ((e2 c).map_target hw)]
      let D (c d : LeafChart L) := (c.1.symm.trans d.1).source
      have hs1 (c d : LeafChart L) : ((e1 c).symm.trans (e1 d)).source =
          {w : ℂ × ℂ | w.1 ∈ D c d ∧ w.2 ≠ 0} := by
        ext w
        change (w ∈ (e1 c).target ∧ curveJet1Base L ((e1 c).symm w) ∈ d.1.source) ↔
          (w.1 ∈ c.1.target ∧ c.1.symm w.1 ∈ d.1.source) ∧ w.2 ≠ 0
        constructor
        · rintro ⟨hw, hd⟩
          exact ⟨⟨hw.1, by rwa [hb1 c w hw] at hd⟩, hw.2⟩
        · rintro ⟨⟨hc, hd⟩, ha⟩
          have hw : w ∈ (e1 c).target := ⟨hc, ha⟩
          exact ⟨hw, by rwa [hb1 c w hw]⟩
      have hs2 (c d : LeafChart L) : ((e2 c).symm.trans (e2 d)).source =
          {w : (ℂ × ℂ) × ℂ | w.1.1 ∈ D c d ∧ w.1.2 ≠ 0} := by
        ext w
        change (w ∈ (e2 c).target ∧ curveJet2Base L ((e2 c).symm w) ∈ d.1.source) ↔
          (w.1.1 ∈ c.1.target ∧ c.1.symm w.1.1 ∈ d.1.source) ∧ w.1.2 ≠ 0
        constructor
        · rintro ⟨hw, hd⟩
          exact ⟨⟨hw.1, by rwa [hb2 c w hw] at hd⟩, hw.2⟩
        · rintro ⟨⟨hc, hd⟩, ha⟩
          have hw : w ∈ (e2 c).target := ⟨hc, ha⟩
          exact ⟨hw, by rwa [hb2 c w hw]⟩
      have hopen1 (c d : LeafChart L) : IsOpen ((e1 c).symm.trans (e1 d)).source := by
        rw [hs1]
        exact ((c.1.symm.trans d.1).open_source.preimage continuous_fst).inter
          (isOpen_ne.preimage continuous_snd)
      have hopen2 (c d : LeafChart L) : IsOpen ((e2 c).symm.trans (e2 d)).source := by
        rw [hs2]
        exact ((c.1.symm.trans d.1).open_source.preimage continuous_fst.fst).inter
          (isOpen_ne.preimage continuous_fst.snd)
      have hscalar (c d : LeafChart L) : ContDiffOn ℂ ∞ (d.1 ∘ c.1.symm) (D c d) :=
        ((contMDiffOn_of_mem_maximalAtlas d.2).comp'
          (contMDiffOn_symm_of_mem_maximalAtlas c.2)).contDiffOn
      have ht1 (c d : LeafChart L) : ContDiffOn ℂ ∞ ((e1 c).symm.trans (e1 d))
          ((e1 c).symm.trans (e1 d)).source := by
        have h := (scalar_two_jet_transition_regular (c.1.symm.trans d.1).open_source
          (hscalar c d)).1
        apply (h.mono (show ((e1 c).symm.trans (e1 d)).source ⊆
          {w | w.1 ∈ D c d} from fun w hw ↦ (hs1 c d ▸ hw).1)).congr
        intro w hw
        have ht := (htrans c d).1 ((e1 c).symm w) ⟨(e1 c).map_target hw.1, hw.2⟩
        change curveJet1Coeff L d ((e1 c).symm w) = _
        rw [ht]
        change curveJet1Transition _ ((e1 c) ((e1 c).symm w)) = _
        rw [(e1 c).right_inv hw.1]
        rfl
      have ht2 (c d : LeafChart L) : ContDiffOn ℂ ∞ ((e2 c).symm.trans (e2 d))
          ((e2 c).symm.trans (e2 d)).source := by
        have h := (scalar_two_jet_transition_regular (c.1.symm.trans d.1).open_source
          (hscalar c d)).2
        apply (h.mono (show ((e2 c).symm.trans (e2 d)).source ⊆
          {w | w.1.1 ∈ D c d} from fun w hw ↦ (hs2 c d ▸ hw).1)).congr
        intro w hw
        have ht := (htrans c d).2 ((e2 c).symm w) ⟨(e2 c).map_target hw.1, hw.2⟩
        change curveJet2Coeff L d ((e2 c).symm w) = _
        rw [ht]
        change curveJet2Transition _ ((e2 c) ((e2 c).symm w)) = _
        rw [(e2 c).right_inv hw.1]
        rfl
      obtain ⟨A1, ha1, hall1⟩ := generated_coefficient_atlas e1
        (fun j ↦ ⟨⟨chartAt ℂ (curveJet1Base L j), IsManifold.chart_mem_maximalAtlas _⟩,
          mem_chart_source ℂ _⟩) hopen1 (fun c d ↦ (ht1 c d).continuousOn)
      obtain ⟨A2, ha2, hall2⟩ := generated_coefficient_atlas e2
        (fun j ↦ ⟨⟨chartAt ℂ (curveJet2Base L j), IsManifold.chart_mem_maximalAtlas _⟩,
          mem_chart_source ℂ _⟩) hopen2 (fun c d ↦ (ht2 c d).continuousOn)
      let : ChartedSpace (ℂ × ℂ) (CurveJet1 L) := A1
      let : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L) := A2
      have hm1 : IsManifold (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ (CurveJet1 L) := by
        apply isManifold_of_contDiffOn
        intro f g hf hg
        obtain ⟨c, hc⟩ := hall1 f hf
        obtain ⟨d, hd⟩ := hall1 g hg
        simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
          Function.id_comp, Function.comp_id, preimage_id, range_id, inter_univ]
        change ContDiffOn ℂ ∞ (f.toPartialEquiv.symm.trans g.toPartialEquiv)
          (f.toPartialEquiv.symm.trans g.toPartialEquiv).source
        rw [hc, hd]
        exact ht1 c d
      have hm2 : IsManifold (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ (CurveJet2 L) := by
        apply isManifold_of_contDiffOn
        intro f g hf hg
        obtain ⟨c, hc⟩ := hall2 f hf
        obtain ⟨d, hd⟩ := hall2 g hg
        simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
          Function.id_comp, Function.comp_id, preimage_id, range_id, inter_univ]
        change ContDiffOn ℂ ∞ (f.toPartialEquiv.symm.trans g.toPartialEquiv)
          (f.toPartialEquiv.symm.trans g.toPartialEquiv).source
        rw [hc, hd]
        exact ht2 c d
      have hp1 : Continuous (curveJet1Base L) := by
        apply continuous_iff_continuousAt.mpr
        intro j
        let c : LeafChart L := ⟨chartAt ℂ (curveJet1Base L j),
          IsManifold.chart_mem_maximalAtlas _⟩
        have hc : curveJet1Base L j ∈ c.1.source := mem_chart_source ℂ _
        obtain ⟨E, _, hE⟩ := ha1 c
        have hsource : E.source = (curveJet1Base L) ⁻¹' c.1.source :=
          congrArg PartialEquiv.source hE
        have hfun : (E : CurveJet1 L → ℂ × ℂ) = curveJet1Coeff L c :=
          congrArg (fun f : PartialEquiv (CurveJet1 L) (ℂ × ℂ) ↦ (f : CurveJet1 L → ℂ × ℂ)) hE
        have hj : j ∈ E.source := hsource ▸ hc
        have ht : (E j).1 ∈ c.1.target := by
          rw [hfun]
          exact c.1.map_source hc
        have hF : ContinuousAt (fun k : CurveJet1 L ↦ (E k).1) j :=
          (E.continuousAt hj).fst
        have h : ContinuousAt (fun k : CurveJet1 L ↦ c.1.symm (E k).1) j :=
          (c.1.symm.continuousAt ht).comp (f := fun k : CurveJet1 L ↦ (E k).1) hF
        apply h.congr
        filter_upwards [E.open_source.mem_nhds hj] with k hk
        rw [hfun]
        exact c.1.left_inv (by change k ∈ (curveJet1Base L) ⁻¹' c.1.source; rwa [← hsource])
      have hp2 : Continuous (curveJet2Base L) := by
        apply continuous_iff_continuousAt.mpr
        intro j
        let c : LeafChart L := ⟨chartAt ℂ (curveJet2Base L j),
          IsManifold.chart_mem_maximalAtlas _⟩
        have hc : curveJet2Base L j ∈ c.1.source := mem_chart_source ℂ _
        obtain ⟨E, _, hE⟩ := ha2 c
        have hsource : E.source = (curveJet2Base L) ⁻¹' c.1.source :=
          congrArg PartialEquiv.source hE
        have hfun : (E : CurveJet2 L → (ℂ × ℂ) × ℂ) = curveJet2Coeff L c :=
          congrArg (fun f : PartialEquiv (CurveJet2 L) ((ℂ × ℂ) × ℂ) ↦
            (f : CurveJet2 L → (ℂ × ℂ) × ℂ)) hE
        have hj : j ∈ E.source := hsource ▸ hc
        have ht : (E j).1.1 ∈ c.1.target := by
          rw [hfun]
          exact c.1.map_source hc
        have hF : ContinuousAt (fun k : CurveJet2 L ↦ (E k).1.1) j :=
          (E.continuousAt hj).fst.fst
        have h : ContinuousAt (fun k : CurveJet2 L ↦ c.1.symm (E k).1.1) j :=
          (c.1.symm.continuousAt ht).comp (f := fun k : CurveJet2 L ↦ (E k).1.1) hF
        apply h.congr
        filter_upwards [E.open_source.mem_nhds hj] with k hk
        rw [hfun]
        exact c.1.left_inv (by change k ∈ (curveJet2Base L) ⁻¹' c.1.source; rwa [← hsource])
      let E1 (c : LeafChart L) := (ha1 c).choose
      let E2 (c : LeafChart L) := (ha2 c).choose
      have he1 (c : LeafChart L) : (E1 c).toPartialEquiv = e1 c := (ha1 c).choose_spec.2
      have he2 (c : LeafChart L) : (E2 c).toPartialEquiv = e2 c := (ha2 c).choose_spec.2
      have htop1 := projected_atlas_topology (curveJet1Base L) hp1
        (fun c : LeafChart L ↦ c.1.source) (fun c ↦ c.1.open_source)
        (fun x ↦ ⟨⟨chartAt ℂ x, IsManifold.chart_mem_maximalAtlas x⟩, mem_chart_source ℂ x⟩)
        E1 (fun c ↦ congrArg PartialEquiv.source (he1 c))
      have htop2 := projected_atlas_topology (curveJet2Base L) hp2
        (fun c : LeafChart L ↦ c.1.source) (fun c ↦ c.1.open_source)
        (fun x ↦ ⟨⟨chartAt ℂ x, IsManifold.chart_mem_maximalAtlas x⟩, mem_chart_source ℂ x⟩)
        E2 (fun c ↦ congrArg PartialEquiv.source (he2 c))
      have htrunc : ContMDiff (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
          (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ (curveJetTruncation L) := by
        intro j
        let c : LeafChart L := ⟨chartAt ℂ (curveJet2Base L j),
          IsManifold.chart_mem_maximalAtlas _⟩
        have hc : curveJet2Base L j ∈ c.1.source := mem_chart_source ℂ _
        have hs1 : (E1 c).source = (curveJet1Base L) ⁻¹' c.1.source :=
          congrArg PartialEquiv.source (he1 c)
        have hs2 : (E2 c).source = (curveJet2Base L) ⁻¹' c.1.source :=
          congrArg PartialEquiv.source (he2 c)
        have hf1 : (E1 c : CurveJet1 L → ℂ × ℂ) = curveJet1Coeff L c :=
          congrArg (fun f : PartialEquiv (CurveJet1 L) (ℂ × ℂ) ↦ (f : CurveJet1 L → ℂ × ℂ)) (he1 c)
        have hf2 : (E2 c : CurveJet2 L → (ℂ × ℂ) × ℂ) = curveJet2Coeff L c :=
          congrArg (fun f : PartialEquiv (CurveJet2 L) ((ℂ × ℂ) × ℂ) ↦
            (f : CurveJet2 L → (ℂ × ℂ) × ℂ)) (he2 c)
        have hj2 : j ∈ (E2 c).source := hs2 ▸ hc
        have hj1 : curveJetTruncation L j ∈ (E1 c).source := by
          rw [hs1]
          change curveJet1Base L (curveJetTruncation L j) ∈ c.1.source
          rw [((hcoeff c).2.2 j hc).1]
          exact hc
        have ht : (E2 c j).1 ∈ (E1 c).target := by
          rw [hf2, ← ((hcoeff c).2.2 j hc).2, ← hf1]
          exact (E1 c).map_source hj1
        have hE2 : ContMDiffAt (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
            (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ (E2 c) j := contMDiffAt_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
            (n := ∞) ((ha2 c).choose_spec.1)) hj2
        have hpr : ContMDiffAt (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
            (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ Prod.fst (E2 c j) :=
          contDiff_fst.contMDiff.contMDiffAt
        have hmem1 : E1 c ∈ IsManifold.maximalAtlas
            (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ (CurveJet1 L) :=
          IsManifold.subset_maximalAtlas ((ha1 c).choose_spec.1)
        have hinv : ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ℂ))
            (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ (E1 c).symm (E2 c j).1 :=
          (contMDiffOn_symm_of_mem_maximalAtlas hmem1).contMDiffAt
          ((E1 c).open_target.mem_nhds ht)
        have hcomp := hinv.comp j (hpr.comp j hE2)
        apply hcomp.congr_of_eventuallyEq
        filter_upwards [(E2 c).open_source.mem_nhds hj2] with k hk
        have hkc : curveJet2Base L k ∈ c.1.source := by
          change k ∈ (curveJet2Base L) ⁻¹' c.1.source
          rwa [← hs2]
        have hkt : curveJetTruncation L k ∈ (E1 c).source := by
          rw [hs1]
          change curveJet1Base L (curveJetTruncation L k) ∈ c.1.source
          rw [((hcoeff c).2.2 k hkc).1]
          exact hkc
        change curveJetTruncation L k = (E1 c).symm (E2 c k).1
        rw [hf2, ← ((hcoeff c).2.2 k hkc).2, ← hf1, (E1 c).left_inv hkt]
      refine ⟨A1, A2, htop1.1, htop2.1, htop1.2, htop2.2,
        hm1, hm2, ?_, ?_, hp1, hp2, htrunc, ?_, ?_, ?_⟩
      · simp [Module.finrank_prod]
      · simp [Module.finrank_prod]
      · intro c
        refine ⟨E1 c, E2 c, (ha1 c).choose_spec.1, (ha2 c).choose_spec.1,
          congrArg PartialEquiv.source (he1 c), congrArg PartialEquiv.source (he2 c),
          congrArg PartialEquiv.target (he1 c), congrArg PartialEquiv.target (he2 c),
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j _
          exact congrArg (fun f : PartialEquiv (CurveJet1 L) (ℂ × ℂ) ↦ f j) (he1 c)
        · intro j _
          exact congrArg (fun f : PartialEquiv (CurveJet2 L) ((ℂ × ℂ) × ℂ) ↦ f j) (he2 c)
        · exact contMDiffOn_of_mem_maximalAtlas
            (IsManifold.subset_maximalAtlas ((ha1 c).choose_spec.1))
        · exact contMDiffOn_symm_of_mem_maximalAtlas
            (IsManifold.subset_maximalAtlas ((ha1 c).choose_spec.1))
        · exact contMDiffOn_of_mem_maximalAtlas
            (IsManifold.subset_maximalAtlas ((ha2 c).choose_spec.1))
        · exact contMDiffOn_symm_of_mem_maximalAtlas
            (IsManifold.subset_maximalAtlas ((ha2 c).choose_spec.1))
      · intro E hE
        obtain ⟨c, hc⟩ := hall1 E hE
        refine ⟨c, congrArg PartialEquiv.source hc, congrArg PartialEquiv.target hc, ?_⟩
        intro j _
        exact congrArg (fun f : PartialEquiv (CurveJet1 L) (ℂ × ℂ) ↦ f j) hc
      · intro E hE
        obtain ⟨c, hc⟩ := hall2 E hE
        refine ⟨c, congrArg PartialEquiv.source hc, congrArg PartialEquiv.target hc, ?_⟩
        intro j _
        exact congrArg (fun f : PartialEquiv (CurveJet2 L) ((ℂ × ℂ) × ℂ) ↦ f j) hc

end HolomorphicAnosov.Ghys
