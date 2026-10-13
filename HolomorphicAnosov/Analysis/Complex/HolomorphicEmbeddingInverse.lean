import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Holomorphic homeomorphisms of Riemann surfaces

Source: McMullen, *Advanced Complex Analysis*, Math 213a notes, printed pp.8, 13,
15 and 58 (Theorems 1.6, 1.31, Corollary 1.28 and the univalence paragraph).
Application: Ghys, *Holomorphic Anosov systems*, Proposition 2.2, pp.589–590.
DAG node: `analysis.qc_holomorphic_embedding_inverse`.

The surfaces have their original Hausdorff, second-countable complex atlases,
modeled on the complex line with the boundaryless identity model. No global
connectedness, nonemptiness, compactness or uniformization assumption is made.
The open subset of the target has Mathlib's restricted atlas and topology.
Complex manifold differentiability expresses holomorphy: the coordinate
criterion has model range equal to the whole complex line, so it is ordinary
complex differentiability on open coordinate domains. In one complex variable
this is equivalent to analyticity by the Cauchy integral theorem.
-/

open Set
open scoped ContDiff

universe u v

namespace HolomorphicAnosov.Analysis.Complex

attribute [local instance] Classical.propDecidable


open Filter Topology _root_.Topology Metric

/-- A holomorphic coordinate homeomorphism has a differentiable literal inverse.
Source: McMullen's isolated-zero theorem 1.6 and removable-singularity theorem 1.32,
combined with native inverse differentiation. Its analytic derivative is either locally
zero or nonzero on a punctured neighborhood. The former would make the original function
constant on a disk, contradicting injectivity. In the latter case native inverse
differentiation gives differentiability of the continuous supplied inverse away from the
image point; the removable-continuous theorem gives differentiability there too.
Differentiating the actual right-inverse identity then forces the forward derivative
nonzero, and native inversedifferentiation gives the reciprocal formula.
-/
theorem coordinateInverseDeriv (h : OpenPartialHomeomorph ℂ ℂ)
    (hf : DifferentiableOn ℂ h h.source) {w : ℂ} (hw : w ∈ h.target) :
    deriv h (h.symm w) ≠ 0 ∧ HasDerivAt h.symm (deriv h (h.symm w))⁻¹ w := by
  have hz := h.map_target hw
  have ha := hf.analyticOnNhd h.open_source (h.symm w) hz
  have hpunct : ∀ᶠ z in 𝓝[≠] (h.symm w), deriv h z ≠ 0 := by
    rcases ha.deriv.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · have hn := Filter.inter_mem hzero (h.open_source.mem_nhds hz)
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
      have hconst : ∀ z ∈ ball (h.symm w) r, h z = h (h.symm w) := by
        intro z hzb
        exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
          (hf.mono fun t ht ↦ (hball ht).2) (fun t ht ↦ (hball ht).1)
          hzb (mem_ball_self hr)
      have hs : ({h.symm w} : Set ℂ) ∈ 𝓝 (h.symm w) := by
        filter_upwards [Metric.ball_mem_nhds _ hr] with z hzb
        exact h.injOn (hball hzb).2 hz (hconst z hzb)
      exact (not_isOpen_singleton (h.symm w)
        (isOpen_singleton_of_finite_mem_nhds _ hs (Set.finite_singleton _))).elim
    · exact hne
  have hts : Tendsto h.symm (𝓝[≠] w) (𝓝[≠] (h.symm w)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(h.symm.continuousAt hw).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (h.open_target.mem_nhds hw)] with t htw ht
    intro heq
    have ht' := congrArg h heq
    rw [h.right_inv ht, h.right_inv hw] at ht'
    exact htw ht'
  have hdinv : DifferentiableAt ℂ h.symm w := by
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ (h.symm.continuousAt hw)).differentiableAt
    filter_upwards [hts.eventually hpunct,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (h.open_target.mem_nhds hw)] with t hne ht
    exact (h.hasDerivAt_symm ht hne
      (hf.differentiableAt (h.open_source.mem_nhds (h.map_target ht))).hasDerivAt).differentiableAt
  have hforward := (hf.differentiableAt (h.open_source.mem_nhds hz)).hasDerivAt
  have hcomp := hforward.comp w hdinv.hasDerivAt
  have hprod : deriv h (h.symm w) * deriv h.symm w = 1 :=
    (hcomp.congr_of_eventuallyEq
      (Filter.EventuallyEq.symm (h.eventually_right_inverse hw))).unique (hasDerivAt_id w)
  have hne : deriv h (h.symm w) ≠ 0 := by
    intro hzero
    simp [hzero] at hprod
  exact ⟨hne, h.hasDerivAt_symm hw hne hforward⟩

/-- The exact open coordinate domains and the supplied inverse of a surface homeomorphism.
Source: McMullen's local univalent inverse theorem, with the manifold chart transport stated
in this module's main theorem. Native composition constructs the coordinate partial
homeomorphism. Its source is precisely `c '' A` and its target is precisely `d '' e(A)`;
the inverse equals the displayed membership-guarded map on that target. The scalar
`coordinateInverseDeriv` theorem applies on these exact domains. Thus the given inverse,
not a separately selected branch, is analytic there with the reciprocal derivative.
-/
private theorem coordinateEmbeddingInverse
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [SecondCountableTopology X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [T2Space Y] [SecondCountableTopology Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ Y]
    (V : TopologicalSpace.Opens Y) (e : X ≃ₜ V)
    (he : MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) e) :
    ∀ (c : OpenPartialHomeomorph X ℂ) (d : OpenPartialHomeomorph Y ℂ),
      c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ X →
      d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ Y →
      ∀ x : X, x ∈ c.source → (e x : Y) ∈ d.source →
        let A : Set X := c.source ∩ (fun t : X ↦ (e t : Y)) ⁻¹' d.source
        let Ω : Set ℂ := c '' A
        let Λ : Set ℂ := d '' ((fun t : X ↦ (e t : Y)) '' A)
        let f : ℂ → ℂ := fun z ↦ d (e (c.symm z) : Y)
        let g : ℂ → ℂ := fun w ↦
          c (if h : d.symm w ∈ (V : Set Y) then e.symm ⟨d.symm w, h⟩ else x)
        IsOpen Ω ∧ IsOpen Λ ∧ c x ∈ Ω ∧ d (e x : Y) ∈ Λ ∧
        MapsTo f Ω Λ ∧ MapsTo g Λ Ω ∧
        EqOn (g ∘ f) id Ω ∧ EqOn (f ∘ g) id Λ ∧
        (∀ z ∈ Ω, HasDerivAt f (deriv f z) z ∧ deriv f z ≠ 0) ∧
        AnalyticOnNhd ℂ g Λ ∧
        (∀ w ∈ Λ, HasDerivAt g (deriv f (g w))⁻¹ w) := by
  classical
  intro c d hc hd x hxc hxd
  dsimp only
  let q := V.openPartialHomeomorphSubtypeCoe ⟨e x⟩
  let h := c.symm.trans (e.toOpenPartialHomeomorph.trans (q.trans d))
  let E : X → Y := fun t ↦ (e t : Y)
  let A := c.source ∩ E ⁻¹' d.source
  let Ω := c '' A
  let Λ := d '' (E '' A)
  let f : ℂ → ℂ := fun z ↦ d (e (c.symm z) : Y)
  let g : ℂ → ℂ := fun w ↦
    c (if hv : d.symm w ∈ (V : Set Y) then e.symm ⟨d.symm w, hv⟩ else x)
  have hsource : h.source = Ω := by
    ext z
    constructor
    · intro hz
      refine ⟨c.symm z, ⟨c.map_target hz.1, ?_⟩, c.right_inv hz.1⟩
      exact hz.2.2.2
    · rintro ⟨t, ⟨htc, htd⟩, rfl⟩
      refine ⟨c.map_source htc, trivial, trivial, ?_⟩
      change (e (c.symm (c t)) : Y) ∈ d.source
      rw [c.left_inv htc]
      exact htd
  have hfun : (h : ℂ → ℂ) = f := rfl
  have htarget : h.target = Λ := by
    rw [← h.image_source_eq_target, hsource, hfun]
    ext w
    constructor
    · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨E t, ⟨t, ht, rfl⟩, ?_⟩
      change d (e t : Y) = d (e (c.symm (c t)) : Y)
      rw [c.left_inv ht.1]
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨c t, ⟨t, ht, rfl⟩, ?_⟩
      change d (e (c.symm (c t)) : Y) = d (e t : Y)
      rw [c.left_inv ht.1]
  have hinv : EqOn g h.symm Λ := by
    rintro w ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    have hdt : (e t : Y) ∈ d.source := ht.2
    have hv : d.symm (d (e t : Y)) ∈ (V : Set Y) := by
      rw [d.left_inv hdt]
      exact (e t).property
    dsimp only [g]
    rw [dite_eq_left hv]
    change c (e.symm ⟨d.symm (d (e t : Y)), hv⟩) =
      c (e.symm (q.symm (d.symm (d (e t : Y)))))
    congr 2
    apply Subtype.ext
    exact (q.right_inv (by simpa only [q, V.openPartialHomeomorphSubtypeCoe_target] using hv)).symm
  have hf : DifferentiableOn ℂ h h.source := by
    intro z hz
    have hcz := c.map_target hz.1
    have hdz : (e (c.symm z) : Y) ∈ d.source := hz.2.2.2
    have hcsm := (contMDiffAt_symm_of_mem_maximalAtlas hc hz.1).mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hdsm := (contMDiffAt_of_mem_maximalAtlas hd hdz).mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hval : MDifferentiable (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) (Subtype.val : V → Y) :=
      (contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp)
    have hs := hdsm.comp z ((hval (e (c.symm z))).comp z ((he (c.symm z)).comp z hcsm))
    exact hs.differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℂ g Λ := by
    intro w hw
    have hw' : w ∈ h.target := htarget.symm ▸ hw
    have hs := (coordinateInverseDeriv h hf hw').2
    have heq : g =ᶠ[𝓝 w] h.symm :=
      Filter.eventuallyEq_of_mem ((htarget ▸ h.open_target).mem_nhds hw) hinv
    exact (hs.congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
  have hxn : c x ∈ Ω := ⟨x, ⟨hxc, hxd⟩, rfl⟩
  have hyw : d (e x : Y) ∈ Λ := ⟨(e x : Y), ⟨x, ⟨hxc, hxd⟩, rfl⟩, rfl⟩
  change IsOpen Ω ∧ IsOpen Λ ∧ c x ∈ Ω ∧ d (e x : Y) ∈ Λ ∧
    MapsTo f Ω Λ ∧ MapsTo g Λ Ω ∧ EqOn (g ∘ f) id Ω ∧ EqOn (f ∘ g) id Λ ∧
    (∀ z ∈ Ω, HasDerivAt f (deriv f z) z ∧ deriv f z ≠ 0) ∧
    AnalyticOnNhd ℂ g Λ ∧ (∀ w ∈ Λ, HasDerivAt g (deriv f (g w))⁻¹ w)
  refine ⟨hsource ▸ h.open_source, htarget ▸ h.open_target, hxn, hyw, ?_, ?_, ?_, ?_,
    ?_, hg.analyticOnNhd (htarget ▸ h.open_target), ?_⟩
  · intro z hz
    exact htarget ▸ h.map_source (hsource.symm ▸ hz)
  · intro w hw
    rw [hinv hw]
    exact hsource ▸ h.map_target (htarget.symm ▸ hw)
  · intro z hz
    change g (f z) = z
    rw [hinv (htarget ▸ h.map_source (hsource.symm ▸ hz))]
    exact h.left_inv (hsource.symm ▸ hz)
  · intro w hw
    change f (g w) = w
    rw [hinv hw]
    exact h.right_inv (htarget.symm ▸ hw)
  · intro z hz
    have hz' : z ∈ h.source := hsource.symm ▸ hz
    have hw := h.map_source hz'
    have H := coordinateInverseDeriv h hf hw
    rw [h.left_inv hz'] at H
    exact ⟨(hf.differentiableAt (h.open_source.mem_nhds hz')).hasDerivAt, H.1⟩
  · intro w hw
    have hw' : w ∈ h.target := htarget.symm ▸ hw
    have H := (coordinateInverseDeriv h hf hw').2
    have heq : g =ᶠ[𝓝 w] h.symm :=
      Filter.eventuallyEq_of_mem ((htarget ▸ h.open_target).mem_nhds hw) hinv
    rw [← hinv hw] at H
    exact H.congr_of_eventuallyEq heq

/-- A holomorphic homeomorphism onto an open subset of a Riemann surface has
a holomorphic inverse and nonzero derivative in every compatible pair of charts.
The inverse coordinate function is the given inverse, is analytic on its exact
open coordinate domain, and has the reciprocal derivative there.

Source: McMullen, Math 213a notes, Theorem 1.6 p.8 (isolated zeros),
Theorem 1.32 and proof p.15 (removable singularities), and the univalence
paragraph p.58 (analyticity of the inverse). The actual proof uses these local
analytic facts and native Mathlib inverse differentiation; it does not use the
power normal form or analytic-root construction of Theorem 1.31. The derivative
constancy, coordinate transport, and chain-rule deductions below are explicit
formal expansions, rather than a claim that the notes print this exact argument.

Natural-language proof. Fix a source point and arbitrary compatible charts c,d.
Restrict the source chart to A, the intersection of its source with the inverse
image of the target chart source under the given homeomorphism. Compose c.symm,
the given homeomorphism, the native open-subset inclusion chart, and d. The
result is an actual open partial homeomorphism h of the complex line. Its source
is exactly Ω=c(A), and its target is exactly Λ=d(e(A)); both are open and contain
the marked coordinates. Its total forward function is the displayed f. On Λ
its inverse equals the displayed g: the membership test is true there, and the
subtype furnished by the native inclusion inverse is the original target point.
The fallback value in g is used only off Λ. Native left- and right-inverse laws
therefore give the stated domain mappings and both cancellation identities.

Composition of the given manifold derivative with compatible chart derivatives
and the open-subset inclusion derivative makes f complex differentiable on Ω.
Cauchy analyticity makes its derivative analytic near each source coordinate a.
By isolated zeros, f' is either identically zero near a or nonzero throughout a
punctured neighborhood of a. In the first case choose a positive-radius disk
inside that neighborhood and Ω. The native zero-derivative constancy theorem
makes f constant on this convex disk, contradicting injectivity of h: it would
force an open disk to be a singleton. Hence f' is nonzero on a punctured
neighborhood of a, without assuming that it is already nonzero at a.

Let b=h(a). The literal continuous inverse h.symm sends a punctured neighborhood
of b into a punctured neighborhood of a: continuity supplies the neighborhood
condition, and inverse cancellation excludes a as the image of any point other
than b. At these nearby points the forward derivative is nonzero, so
OpenPartialHomeomorph.hasDerivAt_symm proves differentiability of h.symm there.
The inverse is continuous at b by the given coordinate homeomorphism. Thus
Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt makes this
same inverse analytic and differentiable at b. This is the continuous version
of the removable-singularity theorem: continuity supplies local boundedness and
fixes the extension value, so no updated value or independently chosen inverse
is introduced.

Differentiate h∘h.symm=id at b using its actual local cancellation identity.
The chain rule gives f'(a) times the inverse derivative equal to one, so f'(a)
is nonzero. Native inverse differentiation now gives the reciprocal formula
for h.symm at b. Repeating at every b∈Λ proves the formula and differentiability
throughout Λ. The equality g=h.symm on this open set transfers the derivatives
to the stated g, which is analytic on Λ by the native complex regularity theorem.

For a target point y∈V choose preferred charts only for the final manifold
transport. The inverse coordinate function g just proved is analytic at d(y).
Compose its derivative with those of the target chart, open-subset inclusion,
and inverse source chart. On an open neighborhood of y, the membership guard is
true and the chart cancellations identify this composition with the GIVEN
surface inverse e.symm. Manifold differentiability respects that local equality,
so e.symm is holomorphic at y. Since y was arbitrary, it is holomorphic on V.
The coordinate conclusions above were proved independently for every compatible
pair c,d, including restrictions and holomorphic changes of coordinates; they
are not restricted to preferred charts. Empty surfaces give vacuous pointwise
claims and require no chosen point, connectedness, or extra dimension premise.
-/
theorem holomorphicEmbeddingInverse
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [SecondCountableTopology X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [T2Space Y] [SecondCountableTopology Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ Y]
    (V : TopologicalSpace.Opens Y) (e : X ≃ₜ V)
    (he : MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) e) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) e.symm ∧
    ∀ (c : OpenPartialHomeomorph X ℂ) (d : OpenPartialHomeomorph Y ℂ),
      c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ X →
      d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ Y →
      ∀ x : X, x ∈ c.source → (e x : Y) ∈ d.source →
        let A : Set X := c.source ∩ (fun t : X ↦ (e t : Y)) ⁻¹' d.source
        let Ω : Set ℂ := c '' A
        let Λ : Set ℂ := d '' ((fun t : X ↦ (e t : Y)) '' A)
        let f : ℂ → ℂ := fun z ↦ d (e (c.symm z) : Y)
        let g : ℂ → ℂ := fun w ↦
          c (if h : d.symm w ∈ (V : Set Y) then e.symm ⟨d.symm w, h⟩ else x)
        IsOpen Ω ∧ IsOpen Λ ∧ c x ∈ Ω ∧ d (e x : Y) ∈ Λ ∧
        MapsTo f Ω Λ ∧ MapsTo g Λ Ω ∧
        EqOn (g ∘ f) id Ω ∧ EqOn (f ∘ g) id Λ ∧
        (∀ z ∈ Ω, HasDerivAt f (deriv f z) z ∧ deriv f z ≠ 0) ∧
        AnalyticOnNhd ℂ g Λ ∧
        (∀ w ∈ Λ, HasDerivAt g (deriv f (g w))⁻¹ w) := by
  classical
  refine ⟨?_, coordinateEmbeddingInverse V e he⟩
  intro y
  let x := e.symm y
  let c := chartAt ℂ x
  let d := chartAt ℂ (y : Y)
  have hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ X :=
    IsManifold.chart_mem_maximalAtlas x
  have hd : d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ Y :=
    IsManifold.chart_mem_maximalAtlas (y : Y)
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hyd : (y : Y) ∈ d.source := mem_chart_source ℂ (y : Y)
  have hxd : (e x : Y) ∈ d.source := by simpa only [x, e.apply_symm_apply] using hyd
  have H := coordinateEmbeddingInverse V e he c d hc hd x hxc hxd
  dsimp only at H
  obtain ⟨hΩ, hΛ, hcx, hdy, hfm, hgm, hgf, hfg, hder, hga, hgd⟩ := H
  let g : ℂ → ℂ := fun w ↦
    c (if hv : d.symm w ∈ (V : Set Y) then e.symm ⟨d.symm w, hv⟩ else x)
  have hyΛ : d (y : Y) ∈ d '' ((fun t : X ↦ (e t : Y)) ''
      (c.source ∩ (fun t : X ↦ (e t : Y)) ⁻¹' d.source)) := by
    simpa only [x, e.apply_symm_apply] using hdy
  have hgg : g (d (y : Y)) = c x := by
    dsimp only [g]
    have hv : d.symm (d (y : Y)) ∈ (V : Set Y) := by
      rw [d.left_inv hyd]
      exact y.property
    rw [dite_eq_left hv]
    congr 2
    apply Subtype.ext
    exact d.left_inv hyd
  have hgdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) g (d (y : Y)) :=
    (hga _ hyΛ).differentiableAt.mdifferentiableAt
  have hdsm := (contMDiffAt_of_mem_maximalAtlas hd hyd).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hval : MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) (Subtype.val : V → Y) :=
    (contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp)
  have hcdiff := (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hxc)).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  rw [← hgg] at hcdiff
  have hs := hcdiff.comp y (hgdiff.comp y (hdsm.comp y (hval y)))
  apply hs.congr_of_eventuallyEq
  have hn₁ := e.symm.continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hxc)
  have hn₂ := continuous_subtype_val.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hyd)
  filter_upwards [hn₁, hn₂] with t htc htd
  change e.symm t = c.symm (g (d (t : Y)))
  dsimp only [g]
  have hv : d.symm (d (t : Y)) ∈ (V : Set Y) := by
    rw [d.left_inv htd]
    exact t.property
  rw [dite_eq_left hv]
  have ht : (⟨d.symm (d (t : Y)), hv⟩ : V) = t := Subtype.ext (d.left_inv htd)
  rw [ht, c.left_inv htc]


end HolomorphicAnosov.Analysis.Complex
