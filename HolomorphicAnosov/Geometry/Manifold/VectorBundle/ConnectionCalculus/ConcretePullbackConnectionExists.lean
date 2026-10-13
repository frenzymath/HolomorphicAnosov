import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.QuotientDifferentialContinuousEquivalence
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.QuotientFrameMultiplierSmooth
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicFrameRestrict
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicFrameCover
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferentialChartTransportG12
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FrameTotalCoefficientHolomorphic

import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.BottBracketPushforwardG10

/-! # Pullback of the concrete quotient-line connection Source: Zhang, arXiv:2609.37695v1, §2.1 equation (5), printed p.5; Demailly, Complex Analytic and Differential Geometry, V §14.1, p.273. The local calculations below construct the actual pulled connection, prove its frame independence and smoothness, and verify its covariant derivative and Bott/Dolbeault compatibility. The final theorem preserves the original interface. -/

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

namespace ConcretePullback
open QuotientLineConnection

variable {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
  {r : ℕ} (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
  (f : Biholomorph d d X X)
  (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
    mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))

include hP hline

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The source frame is restricted to its intersection with the target-frame preimage (Zhang, equation (5), p.5). -/
lemma multiplier_holomorphicAt {V W : Opens X} (e : HolomorphicFrame P V)
    (e' : HolomorphicFrame P W) {x : X} (hx : x ∈ V) (hfx : f x ∈ W) :
    ContMDiffAt (complexModel d) 𝓘(ℂ, ℂ) ∞ (imageFrameCoefficient f hf e e') x := by
  let O : Opens X := ⟨(V : Set X) ∩ f ⁻¹' W,
    V.isOpen.inter (W.isOpen.preimage f.continuous)⟩
  let er := holomorphicFrameRestrict e (show O ≤ V from inter_subset_left)
  have h := (quotient_frame_multiplier_smooth P hP hline f hf er e'
    (fun y hy ↦ hy.2)).1.contMDiffAt (O.isOpen.mem_nhds ⟨hx, hfx⟩)
  exact h

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- On the restricted frame domain, the quotient differential equivalence sends the normalized source frame to a nonzero target coefficient (Zhang, equation (5), p.5). -/
lemma multiplier_nonzero {V W : Opens X} (e : HolomorphicFrame P V)
    (e' : HolomorphicFrame P W) {x : X} (hx : x ∈ V) (hfx : f x ∈ W) :
    imageFrameCoefficient f hf e e' x ≠ 0 := by
  let O : Opens X := ⟨(V : Set X) ∩ f ⁻¹' W,
    V.isOpen.inter (W.isOpen.preimage f.continuous)⟩
  exact (quotient_frame_multiplier_smooth P hP hline f hf
    (holomorphicFrameRestrict e (show O ≤ V from inter_subset_left)) e'
    (fun y hy ↦ hy.2)).2 x ⟨hx, hfx⟩

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The multiplier has a real differential obtained by restricting its complex smooth coordinate expression to real scalars (Zhang, equation (5), p.5). -/
lemma multiplier_real_differentiableAt {V W : Opens X} (e : HolomorphicFrame P V)
    (e' : HolomorphicFrame P W) {x : X} (hx : x ∈ V) (hfx : f x ∈ W) :
    MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (imageFrameCoefficient f hf e e') x := by
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp (multiplier_holomorphicAt hP hline f hf e e' hx hfx)
  have hr : ContMDiffAt (realModel d) 𝓘(ℝ, ℂ) ∞ (imageFrameCoefficient f hf e e') x :=
    contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
  exact hr.mdifferentiableAt (by simp)

omit hP hline

omit [IsManifold (complexModel d) ∞ X] [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The real manifold chain rule identifies the differential of the composed scalar function with the composite of the two actual differentials (Zhang, equation (5), p.5). -/
lemma realDifferential_comp (g : X → ℂ) (x : X)
    (hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) g (f x)) :
    realDifferential (g ∘ f) x =
      (realDifferential g (f x)).comp (mfderiv (realModel d) (realModel d) f x) := by
  unfold realDifferential
  rw [mfderiv_comp x hg (f.toReal.contMDiff.mdifferentiable (by simp) x)]
  rfl

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The second source frame is the scalar coefficient times the first (Zhang, equation (5), p.5). -/
lemma multiplier_source_change {V W O : Opens X}
    (e : HolomorphicFrame P V) (e' : HolomorphicFrame P W)
    (a : HolomorphicFrame P O) {x : X} (hx : x ∈ V) (_hx' : x ∈ W)
    (hfx : f x ∈ O) :
    imageFrameCoefficient f hf e' a x =
      imageFrameCoefficient f hf e a x * e.coefficient e'.sectionValue x := by
  have hs : e'.sectionValue x = e.coefficient e'.sectionValue x • e.sectionValue x := by
    apply (e.coordinate x hx).injective
    simp [HolomorphicFrame.coefficient, hx, e.normalized]
  simp only [imageFrameCoefficient, dite_eq_left hfx]
  rw [hs, map_smul, map_smul, smul_eq_mul, mul_comm]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The image quotient vector expressed in the second target frame has coefficient given by the first target coordinate (Zhang, equation (5), p.5). -/
lemma multiplier_target_change {V W O : Opens X}
    (e : HolomorphicFrame P V) (a : HolomorphicFrame P W)
    (b : HolomorphicFrame P O) {x : X} (hfa : f x ∈ W) (hfb : f x ∈ O) :
    imageFrameCoefficient f hf e a x =
      a.coefficient b.sectionValue (f x) * imageFrameCoefficient f hf e b x := by
  have hs : quotientDerivative f hf x (e.sectionValue x) =
      imageFrameCoefficient f hf e b x • b.sectionValue (f x) := by
    apply (b.coordinate (f x) hfb).injective
    simp [imageFrameCoefficient, hfb, b.normalized]
  simp only [imageFrameCoefficient, dite_eq_left hfa]
  rw [hs, map_smul, smul_eq_mul, mul_comm]
  simp [HolomorphicFrame.coefficient, hfa, hfb, b.normalized]


/-- The logarithmic real differential appearing in equation (5) (Zhang, equation (5), p.5). -/
def logDifferential (g : X → ℂ) (x : X) :=
  (g x)⁻¹ • realDifferential (d := d) g x

omit [IsManifold (complexModel d) ∞ X] [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Equal scalar germs have equal values and real differentials at the point, hence equal logarithmic differentials (Zhang, equation (5), p.5). -/
lemma logDifferential_congr {g k : X → ℂ} {x : X} (h : g =ᶠ[nhds x] k) :
    logDifferential (d := d) g x = logDifferential k x := by
  unfold logDifferential realDifferential
  rw [h.eq_of_nhds, h.mfderiv_eq]
  rfl

omit [IsManifold (complexModel d) ∞ X] [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The real product rule yields the logarithmic differential product identity (Zhang, equation (5), p.5). -/
lemma logDifferential_mul (g k : X → ℂ) (x : X)
    (hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) g x)
    (hk : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) k x)
    (hg0 : g x ≠ 0) (hk0 : k x ≠ 0) :
    logDifferential (d := d) (fun y ↦ g y * k y) x = logDifferential g x + logDifferential k x := by
  unfold logDifferential
  rw [realDifferential_mul g k x hg hk]
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp
  ring

omit [IsManifold (complexModel d) ∞ X] [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The real chain rule yields the logarithmic differential chain identity (Zhang, equation (5), p.5). -/
lemma logDifferential_comp (g : X → ℂ) (x : X)
    (hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) g (f x)) :
    logDifferential (g ∘ f) x =
      (logDifferential g (f x)).comp (mfderiv (realModel d) (realModel d) f x) := by
  unfold logDifferential
  rw [realDifferential_comp f g x hg]
  rfl

/-- The equation-(5) form in fixed source and target quotient frames (Zhang, equation (5), p.5). -/
def localForm (D : Connection P) {V W : Opens X} (e : HolomorphicFrame P V)
    (a : HolomorphicFrame P W) (x : X) : TangentSpace (realModel d) x →L[ℝ] ℂ :=
  logDifferential (imageFrameCoefficient f hf e a) x +
    (D.form W a (f x)).comp (mfderiv (realModel d) (realModel d) f x)

include hP hline

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The multiplier changes by the source transition function (Zhang, equation (5), p.5). -/
lemma localForm_source_change (D : Connection P) {V W O : Opens X}
    (e : HolomorphicFrame P V) (e' : HolomorphicFrame P W)
    (a : HolomorphicFrame P O) {x : X} (hx : x ∈ V) (hx' : x ∈ W)
    (hfx : f x ∈ O) :
    localForm f hf D e' a x = localForm f hf D e a x +
      logDifferential (e.coefficient e'.sectionValue) x := by
  have heq : imageFrameCoefficient f hf e' a =ᶠ[nhds x]
      fun y ↦ imageFrameCoefficient f hf e a y * e.coefficient e'.sectionValue y := by
    filter_upwards [V.isOpen.mem_nhds hx, W.isOpen.mem_nhds hx',
      (O.isOpen.preimage f.continuous).mem_nhds hfx] with y hy hy' hfy
    exact multiplier_source_change f hf e e' a hy hy' hfy
  unfold localForm
  rw [logDifferential_congr heq, logDifferential_mul _ _ x
    (multiplier_real_differentiableAt hP hline f hf e a hx hfx)
    (frame_coefficient_real_differentiableAt hP hline V W e e'.sectionValue
      e'.holomorphic x hx hx')
    (multiplier_nonzero hP hline f hf e a hx hfx)
    (frame_transition_nonzero V W e e' x hx hx')]
  abel

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Changing the target frame multiplies its image coefficient by the target transition (Zhang, equation (5), p.5). -/
lemma localForm_target_independent (D : Connection P) {V W O : Opens X}
    (e : HolomorphicFrame P V) (a : HolomorphicFrame P W)
    (b : HolomorphicFrame P O) {x : X} (hx : x ∈ V)
    (hfa : f x ∈ W) (hfb : f x ∈ O) :
    localForm f hf D e a x = localForm f hf D e b x := by
  let g := a.coefficient b.sectionValue
  have hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) g (f x) :=
    frame_coefficient_real_differentiableAt hP hline W O a b.sectionValue
      b.holomorphic (f x) hfa hfb
  have heq : imageFrameCoefficient f hf e a =ᶠ[nhds x]
      fun y ↦ (g ∘ f) y * imageFrameCoefficient f hf e b y := by
    filter_upwards [(W.isOpen.preimage f.continuous).mem_nhds hfa,
      (O.isOpen.preimage f.continuous).mem_nhds hfb] with y hya hyb
    exact multiplier_target_change f hf e a b hya hyb
  have hl := logDifferential_congr (d := d) heq
  rw [logDifferential_mul _ _ x
    (hg.comp x (f.toReal.contMDiff.mdifferentiable (by simp) x))
    (multiplier_real_differentiableAt hP hline f hf e b hx hfb)
    (frame_transition_nonzero W O a b (f x) hfa hfb)
    (multiplier_nonzero hP hline f hf e b hx hfb), logDifferential_comp f g x hg] at hl
  unfold localForm
  rw [hl, D.gauge W O a b (f x) hfa hfb]
  ext v
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, logDifferential, smul_eq_mul]
  ring


/-- Each image point has a selected holomorphic quotient-frame neighborhood (Zhang, equation (5), p.5). -/
def selectedDomain (x : X) : Opens X :=
  (holomorphic_frame_cover P hP hline x).choose

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The selected frame-cover neighborhood contains its base point (Zhang, equation (5), p.5). -/
lemma mem_selectedDomain (x : X) : x ∈ selectedDomain hP hline x :=
  (holomorphic_frame_cover P hP hline x).choose_spec.1

/-- The selected neighborhood carries its normalized holomorphic frame (Zhang, equation (5), p.5). -/
def selectedFrame (x : X) : HolomorphicFrame P (selectedDomain hP hline x) :=
  (holomorphic_frame_cover P hP hline x).choose_spec.2.some

/-- Equation (5) defines the form using a target frame at each image point. -/
def connection (D : Connection P) : Connection P where
  form _V e x := localForm f hf D e (selectedFrame hP hline (f x)) x
  gauge _V _W e e' x hx hx' := localForm_source_change hP hline f hf D e e'
    (selectedFrame hP hline (f x)) hx hx' (mem_selectedDomain hP hline (f x))

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Target-frame independence replaces the selected target frame by any target frame containing the image point (Zhang, equation (5), p.5). -/
lemma connection_form (D : Connection P) {V W : Opens X}
    (e : HolomorphicFrame P V) (a : HolomorphicFrame P W)
    {x : X} (hx : x ∈ V) (hfx : f x ∈ W) :
    (connection hP hline f hf D).form V e x = localForm f hf D e a x := by
  exact localForm_target_independent hP hline f hf D e
    (selectedFrame hP hline (f x)) a hx (mem_selectedDomain hP hline (f x)) hfx

omit hP hline

/-- A source chart transported along the biholomorphism gives the image chart (Zhang, equation (5), p.5). -/
def imageChart (c : OpenPartialHomeomorph X (ComplexModel d)) :=
  (c.symm.transHomeomorph f.toHomeomorph).symm

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The transported chart and inverse are compositions of holomorphic maps, so the maximal-atlas criterion includes it (Zhang, equation (5), p.5). -/
lemma imageChart_mem_atlas (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) :
    imageChart f c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas hc).comp f.symm.contMDiff.contMDiffOn
      (fun y hy ↦ hy)
  · exact f.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hc)

omit [IsManifold (complexModel d) ∞ X] [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- A holomorphic inverse chart is real smooth by scalar restriction; take its first derivative (Zhang, equation (5), p.5). -/
lemma real_chart_inverse_differentiable (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    {z : ComplexModel d} (hz : z ∈ c.target) :
    MDifferentiableAt (realModel d) (realModel d) c.symm z := by
  obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
    (contMDiffAt_symm_of_mem_maximalAtlas hc hz)
  exact (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt (by simp)

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The derivative of the transported inverse chart is the composite of the inverse-chart derivative and the biholomorphism derivative (Zhang, equation (5), p.5). -/
lemma imageChart_coordinateForm (D : Connection P) {W : Opens X}
    (a : HolomorphicFrame P W) (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    {z : ComplexModel d} (hz : z ∈ c.target) :
    coordinateForm D a (imageChart f c) z =
      ((D.form W a (f (c.symm z))).comp
        (mfderiv (realModel d) (realModel d) f (c.symm z))).comp
          ((mfderiv (realModel d) (realModel d) c.symm z).comp
            (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap) := by
  unfold coordinateForm
  change (D.form W a (f (c.symm z))).comp
    ((mfderiv (realModel d) (realModel d) (f ∘ c.symm) z).comp _) = _
  have hfr : MDifferentiableAt (realModel d) (realModel d) f (c.symm z) :=
    f.toReal.contMDiff.mdifferentiable (by simp) _
  rw [mfderiv_comp z hfr (real_chart_inverse_differentiable c hc hz)]
  rfl

include hP hline

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The coordinate formula combines the frame pullback identity, the transported scalar differential, and the transported target form (Zhang, equation (5), p.5). -/
lemma connection_coordinateForm (D : Connection P) {V W : Opens X}
    (e : HolomorphicFrame P V) (a : HolomorphicFrame P W)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    {z : ComplexModel d} (hz : z ∈ c.target) (hx : c.symm z ∈ V)
    (hfx : f (c.symm z) ∈ W) :
    coordinateForm (connection hP hline f hf D) e c z =
      (imageFrameCoefficient f hf e a (c.symm z))⁻¹ •
        fderiv ℝ (fun w ↦ imageFrameCoefficient f hf e a (c.symm w)) z +
      coordinateForm D a (imageChart f c) z := by
  unfold coordinateForm
  rw [connection_form hP hline f hf D e a hx hfx]
  change (localForm f hf D e a (c.symm z)).comp _ = _ +
    coordinateForm D a (imageChart f c) z
  rw [imageChart_coordinateForm f D a c hc hz]
  have ht := scalar_differential_chart_transport (imageFrameCoefficient f hf e a) c hc z hz
    (multiplier_real_differentiableAt hP hline f hf e a hx hfx)
  unfold localForm logDifferential
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ht]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Near each coordinate point, a fixed target frame gives the coordinate expression (Zhang, equation (5), p.5). -/
lemma connection_smooth (D : Connection P)
    (hD : ∀ (V : Opens X) (e : HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (coordinateForm D e c) (c.target ∩ c.symm ⁻¹' (V : Set X))) :
    ∀ (V : Opens X) (e : HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (coordinateForm (connection hP hline f hf D) e c)
        (c.target ∩ c.symm ⁻¹' (V : Set X)) := by
  intro V e c hc z hz
  let W := selectedDomain hP hline (f (c.symm z))
  let a := selectedFrame hP hline (f (c.symm z))
  have hfx : f (c.symm z) ∈ W := mem_selectedDomain hP hline _
  have hq : ContDiffAt ℝ ∞ (fun w ↦ imageFrameCoefficient f hf e a (c.symm w)) z :=
    ((multiplier_holomorphicAt hP hline f hf e a hz.2 hfx).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hc hz.1)).contDiffAt.restrict_scalars ℝ
  have hq0 := multiplier_nonzero hP hline f hf e a hz.2 hfx
  have ha : ContDiffAt ℝ ∞ (coordinateForm D a (imageChart f c)) z :=
    (hD W a (imageChart f c) (imageChart_mem_atlas f c hc)).contDiffAt
      ((imageChart f c).isOpen_inter_preimage_symm W.isOpen |>.mem_nhds ⟨hz.1, hfx⟩)
  have hs := ((hq.inv hq0).smul (hq.fderiv_right (m := ∞) (by simp))).add ha
  apply (hs.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hN : c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ f ⁻¹' W) ∈ nhds z :=
    (c.isOpen_inter_preimage_symm (V.isOpen.inter (W.isOpen.preimage f.continuous))).mem_nhds
      ⟨hz.1, hz.2, hfx⟩
  filter_upwards [hN] with w hw
  exact connection_coordinateForm hP hline f hf D e a c hc hw.1 hw.2.1 hw.2.2

omit hP hline

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The assumed smooth expression in the preferred source chart determines the coefficient differential (Zhang, equation (5), p.5). -/
lemma section_coefficient_differentiable {V : Opens X} (e : HolomorphicFrame P V)
    (s : (x : X) → Fibre P x)
    (hs : ∀ (W : Opens X) (a : HolomorphicFrame P W)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (fun z ↦ a.coefficient s (c.symm z))
        (c.target ∩ c.symm ⁻¹' ((W : Set X) ∩ V)))
    {x : X} (hx : x ∈ V) :
    MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (e.coefficient s) x := by
  let c := chartAt (ComplexModel d) x
  have hc := IsManifold.chart_mem_maximalAtlas (I := complexModel d) (n := ∞) x
  have hcx : c x ∈ c.target := c.map_source (mem_chart_source _ x)
  have hcix : c.symm (c x) = x := c.left_inv (mem_chart_source _ x)
  have hsc : ContDiffAt ℝ ∞ (fun z ↦ e.coefficient s (c.symm z)) (c x) :=
    (hs V e c hc).contDiffAt ((c.isOpen_inter_preimage_symm (V.isOpen.inter V.isOpen)).mem_nhds
      ⟨hcx, by simpa [hcix] using And.intro hx hx⟩)
  obtain ⟨hccont, hcreg⟩ := contMDiffAt_iff.mp
    (contMDiffAt_of_mem_maximalAtlas hc (mem_chart_source _ x))
  have hcr : ContMDiffAt (realModel d) (realModel d) ∞ c x :=
    contMDiffAt_iff.mpr ⟨hccont, hcreg.restrict_scalars ℝ⟩
  have hcomp := hsc.contMDiffAt.comp x hcr
  apply (hcomp.congr_of_eventuallyEq ?_).mdifferentiableAt (by simp)
  filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x)] with y hy
  simp only [Function.comp_apply, c.left_inv hy]

variable (Q : (x : X) → Fibre P x ≃L[ℂ] Fibre P (f x))
  (hQ : ∀ x, (Q x).toLinearMap = quotientDerivative f hf x)

/-- A quotient section is transported by the fibre equivalence over the inverse biholomorphism; the displayed equality supplies the dependent-fibre cast (Zhang, equation (5), p.5). -/
def pushSection (s : (x : X) → Fibre P x) (y : X) : Fibre P y :=
  Eq.mp (congrArg (Fibre P) (f.apply_symm_apply y)) (Q (f.symm y) (s (f.symm y)))

omit [IsManifold (complexModel d) ∞ X] [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The inverse identity reduces the transported section at an image point to the original fibre equivalence applied to the original section (Zhang, equation (5), p.5). -/
lemma pushSection_apply (s : (x : X) → Fibre P x) (x : X) :
    pushSection f Q s (f x) = Q x (s x) := by
  have transport (y : X) (h : y = x) :
      Eq.mp (congrArg (Fibre P) (congrArg f h)) (Q y (s y)) = Q x (s x) := by
    subst y
    rfl
  exact transport _ (f.symm_apply_apply x)

include hQ

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Every quotient vector is its coefficient times the normalized source frame (Zhang, equation (5), p.5). -/
lemma quotient_coordinate {V W : Opens X} (e : HolomorphicFrame P V)
    (a : HolomorphicFrame P W) {x : X} (hx : x ∈ V) (hfx : f x ∈ W)
    (v : Fibre P x) :
    a.coordinate (f x) hfx (Q x v) =
      imageFrameCoefficient f hf e a x * e.coordinate x hx v := by
  have hv : v = (e.coordinate x hx v) • e.sectionValue x := by
    apply (e.coordinate x hx).injective
    simp [e.normalized]
  have he : Q x (e.sectionValue x) = quotientDerivative f hf x (e.sectionValue x) :=
    congrArg (fun L : Fibre P x →ₗ[ℂ] Fibre P (f x) ↦ L (e.sectionValue x)) (hQ x)
  rw [hv, map_smul, map_smul, he]
  simp [imageFrameCoefficient, hfx, e.normalized, mul_comm]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- At an image point, the transported section satisfies the quotient-coordinate multiplication identity (Zhang, equation (5), p.5). -/
lemma pushSection_coefficient {V W : Opens X} (e : HolomorphicFrame P V)
    (a : HolomorphicFrame P W) (s : (x : X) → Fibre P x) {x : X}
    (hx : x ∈ V) (hfx : f x ∈ W) :
    a.coefficient (pushSection f Q s) (f x) =
      imageFrameCoefficient f hf e a x * e.coefficient s x := by
  simp only [HolomorphicFrame.coefficient, dite_eq_left hfx, dite_eq_left hx]
  rw [pushSection_apply]
  exact quotient_coordinate f hf Q hQ e a hx hfx (s x)

include hP hline

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Locally the target coefficient is the product of the image multiplier and source coefficient composed with the inverse biholomorphism (Zhang, equation (5), p.5). -/
lemma pushSection_coefficient_differentiable {V W : Opens X} (e : HolomorphicFrame P V)
    (a : HolomorphicFrame P W) (s : (x : X) → Fibre P x) {x : X}
    (hx : x ∈ V) (hfx : f x ∈ W)
    (hs : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (e.coefficient s) x) :
    MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (a.coefficient (pushSection f Q s)) (f x) := by
  have hprod : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ)
      (fun y ↦ imageFrameCoefficient f hf e a y * e.coefficient s y) x :=
    (multiplier_real_differentiableAt hP hline f hf e a hx hfx).mul hs
  have hp : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ)
      (fun y ↦ imageFrameCoefficient f hf e a (f.symm y) * e.coefficient s (f.symm y))
      (f x) := by
    apply (show MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ)
      (fun y ↦ imageFrameCoefficient f hf e a y * e.coefficient s y) (f.symm (f x)) by
      simpa using hprod).comp (f x)
    exact (Biholomorph.toReal (f.symm : Biholomorph d d X X)).contMDiff.mdifferentiable (by simp) _
  apply hp.congr_of_eventuallyEq
  filter_upwards [(V.isOpen.preimage f.symm.continuous).mem_nhds (by simpa using hx),
    W.isOpen.mem_nhds hfx] with y hy hyW
  have h := pushSection_coefficient f hf Q hQ e a s hy (by simpa using hyW)
  simpa using h

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- In source coordinates the transported coefficient satisfies w∘f=q u (Zhang, equation (5), p.5). -/
lemma covariant_conjugacy (D : Connection P) {V W : Opens X}
    (e : HolomorphicFrame P V) (a : HolomorphicFrame P W)
    (s : (x : X) → Fibre P x) {x : X} (hx : x ∈ V) (hfx : f x ∈ W)
    (hs : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (e.coefficient s) x)
    (v : TangentSpace (realModel d) x) :
    Q x (covariantDerivative (connection hP hline f hf D) e s x hx v) =
      covariantDerivative D a (pushSection f Q s) (f x) hfx
        (mfderiv (realModel d) (realModel d) f x v) := by
  let q := imageFrameCoefficient f hf e a
  let u := e.coefficient s
  let w := a.coefficient (pushSection f Q s)
  have hq := multiplier_real_differentiableAt hP hline f hf e a hx hfx
  have hw := pushSection_coefficient_differentiable hP hline f hf Q hQ e a s hx hfx hs
  have heq : w ∘ f =ᶠ[nhds x] fun y ↦ q y * u y := by
    filter_upwards [V.isOpen.mem_nhds hx, (W.isOpen.preimage f.continuous).mem_nhds hfx]
      with y hy hyf
    exact pushSection_coefficient f hf Q hQ e a s hy hyf
  have hd : (realDifferential w (f x)).comp (mfderiv (realModel d) (realModel d) f x) =
      q x • realDifferential u x + u x • realDifferential q x := by
    rw [← realDifferential_comp f w x hw]
    have he : realDifferential (d := d) (w ∘ f) x =
        realDifferential (fun y ↦ q y * u y) x := by
      unfold realDifferential
      rw [heq.eq_of_nhds, heq.mfderiv_eq]
      rfl
    rw [he, realDifferential_mul q u x hq hs]
  apply (a.coordinate (f x) hfx).injective
  rw [quotient_coordinate f hf Q hQ e a hx hfx]
  simp only [covariantDerivative, LinearEquiv.apply_symm_apply]
  rw [connection_form hP hline f hf D e a hx hfx]
  change q x * (realDifferential u x v + u x * localForm f hf D e a x v) =
    realDifferential w (f x) (mfderiv (realModel d) (realModel d) f x v) +
      w (f x) * D.form W a (f x) (mfderiv (realModel d) (realModel d) f x v)
  have hdv := congrArg (fun L : TangentSpace (realModel d) x →L[ℝ] ℂ ↦ L v) hd
  change realDifferential w (f x) (mfderiv (realModel d) (realModel d) f x v) = _ at hdv
  have hval : w (f x) = q x * u x := heq.eq_of_nhds
  rw [hdv, hval]
  unfold localForm logDifferential
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  have hq0 : q x ≠ 0 := multiplier_nonzero hP hline f hf e a hx hfx
  change q x * (_ + u x * ((q x)⁻¹ * _ + _)) = _
  field_simp
  ring

omit hQ

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The holomorphic multiplier has complex-linear real differential (Zhang, equation (5), p.5). -/
lemma connection_type_one (D : Connection P)
    (hD : ∀ (V : Opens X) (e : HolomorphicFrame P V) (x : X), x ∈ V →
      ∀ v : TangentSpace (complexModel d) x,
        D.form V e x (complexTangentToReal d x (Complex.I • v)) =
          Complex.I * D.form V e x (complexTangentToReal d x v)) :
    ∀ (V : Opens X) (e : HolomorphicFrame P V) (x : X), x ∈ V →
      ∀ v : TangentSpace (complexModel d) x,
        (connection hP hline f hf D).form V e x (complexTangentToReal d x (Complex.I • v)) =
          Complex.I * (connection hP hline f hf D).form V e x
            (complexTangentToReal d x v) := by
  intro V e x hx v
  let W := selectedDomain hP hline (f x)
  let a := selectedFrame hP hline (f x)
  have hfx : f x ∈ W := mem_selectedDomain hP hline _
  rw [connection_form hP hline f hf D e a hx hfx]
  have hq := realDifferential_I_smul_of_holomorphic (imageFrameCoefficient f hf e a) x
    ((multiplier_holomorphicAt hP hline f hf e a hx hfx).mdifferentiableAt (by simp))
    (multiplier_real_differentiableAt hP hline f hf e a hx hfx) v
  have hdf (w : TangentSpace (complexModel d) x) :
      mfderiv (realModel d) (realModel d) f x (complexTangentToReal d x w) =
      complexTangentToReal d (f x) (mfderiv (complexModel d) (complexModel d) f x w) :=
    f.real_mfderiv_realification x w
  simp only [localForm, logDifferential, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, hq, hdf, map_smul]
  rw [hD _ a (f x) hfx]
  ring

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The frame coordinate on the complex tangent total space is holomorphic (Zhang, equation (5), p.5). -/
lemma projected_coefficient_differentiable (V : Opens X) (e : HolomorphicFrame P V)
    (T : (x : X) → TangentSpace (complexModel d) x)
    (hT : IsSmoothTangentField V T) (x : X) (hx : x ∈ V) :
    MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ)
      (e.coefficient (fun y ↦ projection P y (T y))) x := by
  classical
  let p : TangentBundle (complexModel d) X := ⟨x, T x⟩
  let k := chartAt (ComplexModel d) x
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let a : ComplexModel d → ComplexModel d := fun y ↦
    (t (⟨k.symm y, T (k.symm y)⟩ : TangentBundle (complexModel d) X)).2
  let z := k x
  let c := extChartAt (complexModel d).tangent p
  let H : TangentBundle (complexModel d) X → ℂ := fun q ↦
    if hq : q.proj ∈ V then e.coordinate q.proj hq (projection P q.proj q.snd) else 0
  let F : ComplexModel d × ComplexModel d → ℂ := H ∘ c.symm
  have hc : c p = (z, a z) := by
    apply Prod.ext
    · rfl
    · change (t ⟨x, T x⟩).2 = (t ⟨k.symm (k x), T (k.symm (k x))⟩).2
      rw [k.left_inv (mem_chart_source _ x)]
  have hH : ContMDiffAt (complexModel d).tangent 𝓘(ℂ, ℂ) ∞ H p :=
    frame_total_coefficient_holomorphic hP hline V e p hx
  have hF : DifferentiableAt ℂ F (z, a z) := by
    rw [← hc]
    have hh := (hH.mdifferentiableAt (by simp)).differentiableWithinAt_writtenInExtChartAt
    simpa [writtenInExtChartAt, F, c, chartAt_self_eq, differentiableWithinAt_univ] using hh
  have ha : DifferentiableAt ℝ a z := by
    let tr := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x
    have htr := (hT x hx).contMDiffAt (V.isOpen.mem_nhds hx)
    have hcoeff := ((tr.contMDiffAt_section_iff
      (FiberBundle.mem_baseSet_trivializationAt' x)).mp htr).mdifferentiableAt (by simp)
    have hh : MDifferentiableAt (realModel d) (realModel d)
        (fun y ↦ (tr ⟨y, complexTangentToReal d y (T y)⟩).2) (k.symm z) := by
      rw [show k.symm z = x from k.left_inv (mem_chart_source _ x)]
      exact hcoeff
    have hcomp := (hh.comp z (mdifferentiableAt_atlas_symm (I := realModel d)
      (chart_mem_atlas _ x) (mem_chart_target _ x))).differentiableAt
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [k.open_target.mem_nhds (mem_chart_target _ x)] with y hy
    exact (complexTangentToReal_coordinates x ⟨k.symm y, T (k.symm y)⟩
      (k.map_target hy)).symm
  let g := e.coefficient (fun y ↦ projection P y (T y))
  have hpair : (fun y ↦ F (y, a y)) =ᶠ[nhds z] (g ∘ k.symm) := by
    filter_upwards [k.open_target.mem_nhds (mem_chart_target _ x)] with y hy
    have hh : c ⟨k.symm y, T (k.symm y)⟩ = (y, a y) := by
      change (k (k.symm y), a y) = (y, a y)
      rw [k.right_inv hy]
    have hm : (⟨k.symm y, T (k.symm y)⟩ : TangentBundle (complexModel d) X) ∈ c.source := by
      simpa only [c, extChartAt_source, TangentBundle.mem_chart_source_iff] using k.map_target hy
    change H (c.symm (y, a y)) = g (k.symm y)
    rw [← hh, c.left_inv hm]
    rfl
  have hgcoord : DifferentiableAt ℝ (g ∘ k.symm) z :=
    ((hF.restrictScalars ℝ).comp z (differentiableAt_id.prodMk ha)).congr_of_eventuallyEq
      hpair.symm
  have hh := hgcoord.mdifferentiableAt.comp x
    (mdifferentiableAt_atlas (I := realModel d) (chart_mem_atlas _ x) (mem_chart_source _ x))
  apply hh.congr_of_eventuallyEq
  filter_upwards [k.open_source.mem_nhds (mem_chart_source _ x)] with y hy
  exact congrArg g (k.left_inv hy).symm


include hQ

omit hP hline hQ [IsManifold (complexModel d) ∞ X] [T2Space X]
  [SecondCountableTopology X] [CompactSpace X] in
/-- At an image point, the differential pushforward satisfies the inverse-map identity at its base point (Zhang, equation (5), p.5). -/
lemma pushTangentField_at_image (Z : (x : X) → TangentSpace (complexModel d) x) (x : X) :
    pushTangentField f Z (f x) = mfderiv (complexModel d) (complexModel d) f x (Z x) := by
  exact congrArg (fun y : X ↦
    (mfderiv (complexModel d) (complexModel d) f y (Z y) : ComplexModel d))
    (f.symm_apply_apply x)

omit hP hline [IsManifold (complexModel d) ∞ X] [T2Space X]
  [SecondCountableTopology X] [CompactSpace X] in
/-- At an image point the quotient differential commutes with the original tangent projection (Zhang, equation (5), p.5). -/
lemma pushSection_projection (Z : (x : X) → TangentSpace (complexModel d) x) :
    pushSection f Q (fun y ↦ projection P y (Z y)) =
      fun y ↦ projection P y (pushTangentField f Z y) := by
  funext y
  obtain ⟨x, rfl⟩ := f.surjective y
  change pushSection f Q (fun y ↦ projection P y (Z y)) (f x) =
    projection P (f x) (pushTangentField f Z (f x))
  rw [pushSection_apply f Q]
  have h := congrArg (fun L : Fibre P x →ₗ[ℂ] Fibre P (f x) ↦
    L (projection P x (Z x))) (hQ x)
  change Q x (projection P x (Z x)) = _ at h
  rw [h]
  rw [pushTangentField_at_image]
  rfl

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Preservation of type (1,0) gives Dolbeault compatibility (Zhang, equation (5), p.5). -/
lemma connection_compatible (D : Connection P) (hD : IsCompatible D) :
    IsCompatible (connection hP hline f hf D) := by
  refine ⟨connection_type_one hP hline f hf D hD.1, ?_⟩
  intro V e Y Z hY hZ hYP x hx
  let W : Opens X := ⟨(selectedDomain hP hline (f x) : Set X) ∩ f.symm ⁻¹' V,
    (selectedDomain hP hline (f x)).isOpen.inter (V.isOpen.preimage f.symm.continuous)⟩
  let a : HolomorphicFrame P W := holomorphicFrameRestrict
    (selectedFrame hP hline (f x)) inter_subset_left
  have hfx : f x ∈ W := ⟨mem_selectedDomain hP hline _, by simpa using hx⟩
  have hY' : IsSmoothTangentField W (pushTangentField f Y) :=
    (smooth_pushTangentField f hY).mono inter_subset_right
  have hZ' : IsSmoothTangentField W (pushTangentField f Z) :=
    (smooth_pushTangentField f hZ).mono inter_subset_right
  have hYP' : ∀ y ∈ W, pushTangentField f Y y ∈ P y := by
    intro y hy
    obtain ⟨z, rfl⟩ := f.surjective y
    have hz : z ∈ V := by simpa using hy.2
    change pushTangentField f Y (f z) ∈ P (f z)
    rw [pushTangentField_at_image f Y z]
    exact hf z (Y z) (hYP z hz)
  have hb := hD.2 W a (pushTangentField f Y) (pushTangentField f Z) hY' hZ' hYP' (f x) hfx
  have hs := projected_coefficient_differentiable hP hline V e Z hZ x hx
  have hconj (v : TangentSpace (realModel d) x) :=
    covariant_conjugacy hP hline f hf Q hQ D e a
      (fun y ↦ projection P y (Z y)) hx hfx hs v
  simp only [pushSection_projection f hf Q hQ Z] at hconj
  have hdf (v : TangentSpace (complexModel d) x) :
      mfderiv (realModel d) (realModel d) f x (complexTangentToReal d x v) =
      complexTangentToReal d (f x) (mfderiv (complexModel d) (complexModel d) f x v) :=
    f.real_mfderiv_realification x v
  have hpush : pushTangentField f Y (f x) =
      mfderiv (complexModel d) (complexModel d) f x (Y x) := by
    exact pushTangentField_at_image f Y x
  apply (Q x).injective
  rw [map_smul, map_sub, map_smul, hconj, hconj, hdf, hdf, map_smul, ← hpush, hb,
    bottBracket_pushTangentField f V.isOpen hY hZ hx]
  exact (congrArg (fun L : Fibre P x →ₗ[ℂ] Fibre P (f x) ↦
    L (projection P x (bottBracket Y Z x))) (hQ x)).symm

end ConcretePullback

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The pulled-back connection is obtained from the smooth quotient-line connection by the quotient differential (Zhang, equation (5), p.5; Demailly, V §14.1, p.273). -/
theorem concrete_pullback_connection_exists
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P)
    (hline : IsQuotientTangentLine P)
    (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
    :
    let smoothSection := fun (U : Set X)
      (s : (x : X) → QuotientLineConnection.Fibre P x) ↦
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ContDiffOn ℝ ∞ (fun z ↦ e.coefficient s (c.symm z))
          (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ U))
    let smoothConnection := fun (D : QuotientLineConnection.Connection P) ↦
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ContDiffOn ℝ ∞ (QuotientLineConnection.coordinateForm D e c)
          (c.target ∩ c.symm ⁻¹' (V : Set X))
    let pullbackLaw := fun (Dp D : QuotientLineConnection.Connection P)
      (f : Biholomorph d d X X)
      (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
        mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x)) ↦
      ∀ (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (e' : QuotientLineConnection.HolomorphicFrame P W) (x : X),
        x ∈ V → f x ∈ W →
        Dp.form V e x =
          (QuotientLineConnection.imageFrameCoefficient f hf e e' x)⁻¹ •
            QuotientLineConnection.realDifferential
              (QuotientLineConnection.imageFrameCoefficient f hf e e') x +
          (D.form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x)
    ∃ Q : (x : X) → QuotientLineConnection.Fibre P x ≃L[ℂ]
        QuotientLineConnection.Fibre P (f x),
      (∀ x, (Q x).toLinearMap = QuotientLineConnection.quotientDerivative f hf x) ∧
      ∀ D : QuotientLineConnection.Connection P, smoothConnection D →
      ∃ Dp : QuotientLineConnection.Connection P, smoothConnection Dp ∧
        pullbackLaw Dp D f hf ∧
          (QuotientLineConnection.IsCompatible D →
            QuotientLineConnection.IsCompatible Dp) ∧
          ∀ (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
            (e' : QuotientLineConnection.HolomorphicFrame P W)
            (s : (y : X) → QuotientLineConnection.Fibre P y),
            smoothSection V s → ∀ x (hx : x ∈ V) (hfx : f x ∈ W)
              (v : TangentSpace (realModel d) x),
              QuotientLineConnection.covariantDerivative Dp e s x hx v =
                (Q x).symm (QuotientLineConnection.covariantDerivative D e'
                  (fun y ↦ Eq.mp (congrArg (QuotientLineConnection.Fibre P)
                    (f.apply_symm_apply y)) (Q (f.symm y) (s (f.symm y))))
                  (f x) hfx (mfderiv (realModel d) (realModel d) f x v)) := by
  dsimp only
  obtain ⟨Q, hQ⟩ := quotient_differential_continuous_equivalence P hP hline f hf
  refine ⟨Q, hQ, ?_⟩
  intro D hD
  refine ⟨ConcretePullback.connection hP hline f hf D,
    ConcretePullback.connection_smooth hP hline f hf D hD, ?_, ?_, ?_⟩
  · intro V W e a x hx hfx
    exact ConcretePullback.connection_form hP hline f hf D e a hx hfx
  · exact ConcretePullback.connection_compatible hP hline f hf Q hQ D
  · intro V W e a s hs x hx hfx v
    apply (Q x).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact ConcretePullback.covariant_conjugacy hP hline f hf Q hQ D e a s hx hfx
      (ConcretePullback.section_coefficient_differentiable e s hs hx) v

end HolomorphicAnosov.ConnectionCalculus

