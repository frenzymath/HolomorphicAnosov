import HolomorphicAnosov.Analysis.Regularity.MontgomeryParameterDerivativeDenseJointContinuity
import HolomorphicAnosov.Geometry.Manifold.VectorActionCoordinateSupport
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Algebra.MulAction
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialJetTransfer

/-! # Joint continuity of the spatial jets of a continuous vector-group action Source: Deane Montgomery, *Topological Groups of Differentiable Transformations*, Annals of Mathematics 46 (1945), Theorem 1, Lemmas 1′–4 and Corollary 1, printed pp.383–387. The locally compact group is the additive group of the finite-dimensional real parameter space. -/

namespace HolomorphicAnosov

open scoped ContDiff

set_option autoImplicit false


end HolomorphicAnosov

namespace HolomorphicAnosov.VectorActionSpatialSupport

open Filter
open scoped Topology _root_.Topology

variable {V E M : Type*} [NormedAddCommGroup V]
  [NormedAddCommGroup E] [TopologicalSpace M]
  [AddAction V M] [ContinuousVAdd V M]


omit [ContinuousVAdd V M] in
/-- The actual inverse-action recovery behind Montgomery's Lemma 3, equation (10), p.386. -/
theorem action_coordinate_recovery
    (e f : OpenPartialHomeomorph M E) (v h : V) (y : E)
    (hdom : (v + h) +ᵥ e.symm y ∈ f.source) :
    e ((-v) +ᵥ f.symm (f ((v + h) +ᵥ e.symm y))) = e (h +ᵥ e.symm y) := by
  rw [f.left_inv hdom, add_vadd, neg_vadd_vadd]

/-- The recovery identity holds on a neighborhood of `(0,y)` (Montgomery, Lemma 3, p.385). -/
theorem action_coordinate_recovery_eventually
    (e f : OpenPartialHomeomorph M E) (v : V) (y : E)
    (hy : y ∈ e.target) (hvy : v +ᵥ e.symm y ∈ f.source) :
    (fun p : V × E ↦ e ((-v) +ᵥ f.symm (f ((v + p.1) +ᵥ e.symm p.2))))
      =ᶠ[𝓝 (0, y)] (fun p : V × E ↦ e (p.1 +ᵥ e.symm p.2)) := by
  have hc : ContinuousAt (fun p : V × E ↦ (v + p.1) +ᵥ e.symm p.2) (0, y) :=
    (continuousAt_const.add continuousAt_fst).vadd
      ((e.symm.continuousAt hy).comp continuousAt_snd)
  have hsource : ∀ᶠ p : V × E in 𝓝 (0, y), (v + p.1) +ᵥ e.symm p.2 ∈ f.source :=
    hc.preimage_mem_nhds (f.open_source.mem_nhds (by simpa using hvy))
  filter_upwards [hsource] with p hp
  exact action_coordinate_recovery e f v p.1 p.2 hp

/-- The derivative of the inverse-action recovery is the solved form of Montgomery (10), p.386. -/
theorem action_coordinate_recovery_hasFDerivAt [NormedSpace ℝ E]
    (e f : OpenPartialHomeomorph M E) (v h : V) (y : E)
    (hy : y ∈ e.target) (hdom : (v + h) +ᵥ e.symm y ∈ f.source)
    (A B : E →L[ℝ] E)
    (hA : HasFDerivAt (fun z : E ↦ e ((-v) +ᵥ f.symm z)) A
      (f ((v + h) +ᵥ e.symm y)))
    (hB : HasFDerivAt (fun z : E ↦ f ((v + h) +ᵥ e.symm z)) B y) :
    HasFDerivAt (fun z : E ↦ e (h +ᵥ e.symm z)) (A.comp B) y := by
  have hc : ContinuousAt (fun z : E ↦ (v + h) +ᵥ e.symm z) y :=
    continuousAt_const.vadd (e.symm.continuousAt hy)
  have hn : ∀ᶠ z : E in 𝓝 y, (v + h) +ᵥ e.symm z ∈ f.source :=
    hc.preimage_mem_nhds (f.open_source.mem_nhds hdom)
  apply (hA.comp y hB).congr_of_eventuallyEq
  filter_upwards [hn] with z hz
  exact (action_coordinate_recovery e f v h z hz).symm

end HolomorphicAnosov.VectorActionSpatialSupport

namespace HolomorphicAnosov.VectorActionSpatialSupport

open Filter
open scoped Topology _root_.Topology ContDiff

/-- Transfer joint Jacobian continuity at the chosen good parameter to the identity (Montgomery, Lemma 3, equations (10)–(11), pp.385–386). -/
theorem action_coordinate_recovery_continuousAt_fderiv
    {V E M : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [AddAction V M] [ContinuousVAdd V M]
    (e f : OpenPartialHomeomorph M E) (v : V) (y : E)
    (hy : y ∈ e.target) (hvy : v +ᵥ e.symm y ∈ f.source)
    (hinv : ContDiffAt ℝ 1 (fun z : E ↦ e ((-v) +ᵥ f.symm z))
      (f (v +ᵥ e.symm y)))
    (hslice : ∀ w : V, ∀ z ∈ e.target, w +ᵥ e.symm z ∈ f.source →
      DifferentiableAt ℝ (fun t : E ↦ f (w +ᵥ e.symm t)) z)
    (hgood : ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ f (p.1 +ᵥ e.symm z)) p.2) (v, y)) :
    ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ e (p.1 +ᵥ e.symm z)) p.2) (0, y) := by
  have hact : ContinuousAt (fun p : V × E ↦ (v + p.1) +ᵥ e.symm p.2) (0, y) :=
    (continuousAt_const.add continuousAt_fst).vadd
      ((e.symm.continuousAt hy).comp continuousAt_snd)
  have hcoord : ContinuousAt (fun p : V × E ↦ f ((v + p.1) +ᵥ e.symm p.2))
      (0, y) :=
    (f.continuousAt (by simpa using hvy)).comp hact
  have hcoord' : Tendsto (fun p : V × E ↦ f ((v + p.1) +ᵥ e.symm p.2))
      (𝓝 (0, y)) (𝓝 (f (v +ᵥ e.symm y))) := by
    simpa [ContinuousAt] using hcoord
  have houter := (hinv.continuousAt_fderiv (by norm_num)).comp_of_eq hcoord
    (by simp)
  have hinner : ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ f ((v + p.1) +ᵥ e.symm z)) p.2)
      (0, y) :=
    hgood.comp_of_eq ((continuousAt_const.add continuousAt_fst).prodMk
      continuousAt_snd) (by simp)
  apply (houter.clm_comp hinner).congr_of_eventuallyEq
  have hsource : ∀ᶠ p : V × E in 𝓝 (0, y), (v + p.1) +ᵥ e.symm p.2 ∈ f.source :=
    hact.preimage_mem_nhds (f.open_source.mem_nhds (by simpa using hvy))
  have htarget : ∀ᶠ p : V × E in 𝓝 (0, y), p.2 ∈ e.target :=
    continuousAt_snd.preimage_mem_nhds (e.open_target.mem_nhds hy)
  have hinv' := hcoord'.eventually (hinv.eventually (by simp))
  filter_upwards [hsource, htarget, hinv'] with p hp hpy hpi
  exact (action_coordinate_recovery_hasFDerivAt e f v p.1 p.2 hpy hp _ _
    hpi.differentiableAt_one.hasFDerivAt
    (hslice (v + p.1) p.2 hpy hp).hasFDerivAt).fderiv

end HolomorphicAnosov.VectorActionSpatialSupport


namespace HolomorphicAnosov.VectorActionSpatialSupport

open scoped Topology _root_.Topology ContDiff

/-- Every fixed-parameter spatial jet is continuous on its genuine chart domain (Montgomery, Lemma 1 and Corollary 1, pp.383–387). -/
theorem action_coordinate_continuousAt_iteratedFDeriv
    {V E M : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [AddAction V M]
    (hsmooth : ∀ v : V, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (v : V) (y : E) (hy : y ∈ e.target) (hvy : v +ᵥ e.symm y ∈ f.source)
    (k : ℕ) :
    ContinuousAt (iteratedFDeriv ℝ k (fun z : E ↦ f (v +ᵥ e.symm z))) y :=
  (action_coordinate_contDiffAt hsmooth e f he hf v y hy hvy).continuousAt_iteratedFDeriv
    (by simp)

/-- A good parameter gives joint Jacobian continuity at the identity under the original smooth-slice assumptions (Montgomery, Lemma 3, pp.385–386). -/
theorem action_coordinate_good_parameter_to_identity
    {V E M : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [AddAction V M] [ContinuousVAdd V M]
    (hsmooth : ∀ v : V, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (v : V) (y : E) (hy : y ∈ e.target) (hvy : v +ᵥ e.symm y ∈ f.source)
    (hgood : ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ f (p.1 +ᵥ e.symm z)) p.2) (v, y)) :
    ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ e (p.1 +ᵥ e.symm z)) p.2) (0, y) := by
  apply action_coordinate_recovery_continuousAt_fderiv e f v y hy hvy
  · apply (action_coordinate_contDiffAt hsmooth f e hf he (-v)
      (f (v +ᵥ e.symm y)) (f.map_source hvy) ?_).of_le (by simp)
    simpa only [f.left_inv hvy, neg_vadd_vadd] using e.map_target hy
  · intro w z hz hwz
    exact (action_coordinate_contDiffAt hsmooth e f he hf w z hz hwz).differentiableAt
      (by simp)
  · exact hgood

/-- Joint Jacobian continuity at the identity transfers to every parameter in any compatible target chart (Montgomery, Theorem 1, p.386). -/
theorem action_coordinate_identity_to_parameter
    {V E M : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [AddAction V M] [ContinuousVAdd V M]
    (hsmooth : ∀ v : V, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (v : V) (y : E) (hy : y ∈ e.target) (hvy : v +ᵥ e.symm y ∈ f.source)
    (hzero : ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ e (p.1 +ᵥ e.symm z)) p.2) (0, y)) :
    ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ f (p.1 +ᵥ e.symm z)) p.2) (v, y) := by
  have hact : ContinuousAt (fun p : V × E ↦ p.1 +ᵥ e.symm p.2) (0, y) :=
    continuousAt_fst.vadd ((e.symm.continuousAt hy).comp continuousAt_snd)
  have hK : ContinuousAt (fun p : V × E ↦ e (p.1 +ᵥ e.symm p.2)) (0, y) :=
    (e.continuousAt (by simpa using e.map_target hy)).comp hact
  have hfixed₀ := action_coordinate_contDiffAt hsmooth e f he hf v y hy hvy
  have houter := (hfixed₀.continuousAt_fderiv (by simp)).comp_of_eq hK
    (by simp [e.right_inv hy])
  have htranslated : ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ f ((v + p.1) +ᵥ e.symm z)) p.2)
      (0, y) := by
    apply (houter.clm_comp hzero).congr_of_eventuallyEq
    have htarget : ∀ᶠ p : V × E in 𝓝 (0, y), p.2 ∈ e.target :=
      continuousAt_snd.preimage_mem_nhds (e.open_target.mem_nhds hy)
    have hsource : ∀ᶠ p : V × E in 𝓝 (0, y),
        p.1 +ᵥ e.symm p.2 ∈ e.source :=
      hact.preimage_mem_nhds (e.open_source.mem_nhds (by simpa using e.map_target hy))
    have hfinal : ∀ᶠ p : V × E in 𝓝 (0, y),
        (v + p.1) +ᵥ e.symm p.2 ∈ f.source :=
      ((continuousAt_const.add continuousAt_fst).vadd
        ((e.symm.continuousAt hy).comp continuousAt_snd)).preimage_mem_nhds
          (f.open_source.mem_nhds (by simpa using hvy))
    filter_upwards [htarget, hsource, hfinal] with p hp hpK hpF
    have hinner :=
      (action_coordinate_contDiffAt hsmooth e e he he p.1 p.2 hp hpK).differentiableAt
        (by simp)
    have hfixed := (action_coordinate_contDiffAt hsmooth e f he hf v
      (e (p.1 +ᵥ e.symm p.2)) (e.map_source hpK) (by
        simpa only [e.left_inv hpK, ← add_vadd] using hpF)).differentiableAt (by simp)
    have hn : ∀ᶠ z : E in 𝓝 p.2, p.1 +ᵥ e.symm z ∈ e.source :=
      (continuousAt_const.vadd (e.symm.continuousAt hp)).preimage_mem_nhds
        (e.open_source.mem_nhds hpK)
    have hderiv := (hfixed.hasFDerivAt.comp p.2 hinner.hasFDerivAt).congr_of_eventuallyEq (show
        (fun z : E ↦ f ((v + p.1) +ᵥ e.symm z)) =ᶠ[𝓝 p.2]
          (fun z : E ↦ f (v +ᵥ e.symm (e (p.1 +ᵥ e.symm z)))) from by
        filter_upwards [hn] with z hz
        simp only [e.left_inv hz, add_vadd])
    exact hderiv.fderiv
  have htranslate : ContinuousAt (fun p : V × E ↦ (p.1 - v, p.2)) (v, y) :=
    (continuousAt_fst.sub continuousAt_const).prodMk continuousAt_snd
  simpa only [Function.comp_def, ← add_sub_assoc, add_sub_cancel_left] using
    htranslated.comp_of_eq htranslate (by simp)

end HolomorphicAnosov.VectorActionSpatialSupport


namespace HolomorphicAnosov.VectorActionSpatialSupport

open scoped Topology _root_.Topology

/-- Simultaneous continuity of the finitely many Jacobian entries is precisely continuity of the derivative in operator norm (Montgomery, Lemma 2, p.385). -/
theorem continuousAt_linearMap_iff_coordinates
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (L : X → E →L[ℝ] E) (x : X) :
    ContinuousAt L x ↔ ∀ i j, ContinuousAt (fun p ↦ b.equivFunL (L p (b j)) i) x := by
  constructor
  · intro h i j
    exact (continuous_apply i).continuousAt.comp
      (b.equivFunL.continuousAt.comp (h.clm_apply continuousAt_const))
  · intro h
    have hb : ∀ j, ContinuousAt (fun p ↦ L p (b j)) x := by
      intro j
      have hc := b.equivFunL.symm.continuousAt.comp (continuousAt_pi.mpr (fun i ↦ h i j))
      simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hc
    apply continuousAt_clm_apply.mpr
    intro y
    have hc : ContinuousAt (fun p ↦ ∑ j, b.repr y j • L p (b j)) x :=
      tendsto_finsetSum Finset.univ (fun j _ ↦ (hb j).const_smul (b.repr y j))
    simpa only [← map_smul, ← map_sum, b.sum_repr] using hc

end HolomorphicAnosov.VectorActionSpatialSupport


namespace HolomorphicAnosov.VectorActionSpatialSupport

open scoped Topology _root_.Topology

/-- The finite-coordinate reconstruction also holds relative to an arbitrary set (Montgomery, Lemma 2, p.385). -/
theorem continuousOn_linearMap_iff_coordinates
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (L : X → E →L[ℝ] E) (s : Set X) :
    ContinuousOn L s ↔ ∀ i j, ContinuousOn
      (fun p ↦ b.equivFunL (L p (b j)) i) s := by
  constructor
  · intro h i j p hp
    have hj : ContinuousWithinAt (fun q ↦ L q (b j)) s p :=
      (continuousOn_clm_apply.mp h (b j)) p hp
    exact (continuous_apply i).continuousAt.comp_continuousWithinAt
      (b.equivFunL.continuousAt.comp_continuousWithinAt hj)
  · intro h
    apply continuousOn_clm_apply.mpr
    intro y p hp
    have hb : ∀ j, ContinuousWithinAt (fun q ↦ L q (b j)) s p := by
      intro j
      have hc : ContinuousWithinAt (fun q ↦ b.equivFunL (L q (b j))) s p :=
        continuousWithinAt_pi.mpr (fun i ↦ h i j p hp)
      have hs := b.equivFunL.symm.continuousAt.comp_continuousWithinAt hc
      simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hs
    have hc : ContinuousWithinAt (fun q ↦ ∑ j, b.repr y j • L q (b j)) s p :=
      tendsto_finsetSum Finset.univ (fun j _ ↦ (hb j).const_smul (b.repr y j))
    simpa only [← map_smul, ← map_sum, b.sum_repr] using hc

end HolomorphicAnosov.VectorActionSpatialSupport


namespace HolomorphicAnosov.VectorActionSpatialSupport

open scoped Topology _root_.Topology ContDiff

/-- The scalar coordinate families and their actual Jacobian entries satisfy the continuity, coordinate-line derivative, and fixed-parameter spatial continuity conditions (Montgomery, Lemma 1′ as used in Lemmas 1–2, pp.383–385). -/
theorem action_coordinate_scalar_family_data
    {V E M : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [AddAction V M] [ContinuousVAdd V M]
    (hsmooth : ∀ v : V, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (W : Set V) (B : Set E)
    (hdom : ∀ v ∈ W, ∀ y ∈ B, y ∈ e.target ∧ v +ᵥ e.symm y ∈ f.source) :
    (∀ i, ContinuousOn (fun p : V × E ↦ b.equivFunL (f (p.1 +ᵥ e.symm p.2)) i)
      (W ×ˢ B)) ∧
    (∀ v ∈ W, ∀ y ∈ B, ∀ i j,
      HasDerivAt (fun t : ℝ ↦ b.equivFunL (f (v +ᵥ e.symm (y + t • b j))) i)
        (b.equivFunL (fderiv ℝ (fun z : E ↦ f (v +ᵥ e.symm z)) y (b j)) i) 0) ∧
    (∀ v ∈ W, ∀ i j, ContinuousOn
      (fun y ↦ b.equivFunL (fderiv ℝ (fun z : E ↦ f (v +ᵥ e.symm z)) y (b j)) i) B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i p hp
    obtain ⟨hy, hfy⟩ := hdom p.1 hp.1 p.2 hp.2
    have hact : ContinuousAt (fun q : V × E ↦ q.1 +ᵥ e.symm q.2) p :=
      continuousAt_fst.vadd ((e.symm.continuousAt hy).comp continuousAt_snd)
    have hcoord : ContinuousAt (fun q : V × E ↦ f (q.1 +ᵥ e.symm q.2)) p :=
      (f.continuousAt hfy).comp_of_eq hact rfl
    exact ((continuous_apply i).continuousAt.comp (b.equivFunL.continuousAt.comp
      hcoord)).continuousWithinAt
  · intro v hv y hy i j
    obtain ⟨hey, hfy⟩ := hdom v hv y hy
    have hF := (action_coordinate_contDiffAt hsmooth e f he hf v y hey hfy).differentiableAt
      (by simp)
    have hline : HasDerivAt (fun t : ℝ ↦ y + t • b j) (b j) 0 := by
      have h := (hasFDerivAt_const y (0 : ℝ)).add
        (ContinuousLinearMap.toSpanSingleton ℝ (b j)).hasFDerivAt
      simpa [Pi.add_def] using h.hasDerivAt
    have hd := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
    let c : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap
    simpa [c, Function.comp_def] using c.hasFDerivAt.comp_hasDerivAt 0 hd
  · intro v hv i j y hy
    obtain ⟨hey, hfy⟩ := hdom v hv y hy
    have hD := (action_coordinate_contDiffAt hsmooth e f he hf v y hey hfy).continuousAt_fderiv
      (by simp)
    exact ((continuous_apply i).continuousAt.comp
      (b.equivFunL.continuousAt.comp (hD.clm_apply continuousAt_const))).continuousWithinAt

end HolomorphicAnosov.VectorActionSpatialSupport


namespace HolomorphicAnosov.VectorActionSpatialSupport

open scoped Topology _root_.Topology ContDiff

/-- The dense Gδ parameter set is obtained by intersecting the sets for the finitely many matrix entries (Montgomery, Lemma 2, p.385). -/
theorem dense_good_parameters_of_coordinate_entries
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E)
    (W : Set V) (hW : IsOpen W) (B : Set E) (hB : IsOpen B) (y : E) (hy : y ∈ B)
    (L : V × E → E →L[ℝ] E)
    (hentry : ∀ i j, Dense {v : W | ContinuousWithinAt
        (fun p : V × E ↦ b.equivFunL (L p (b j)) i) (W ×ˢ B) (v.val, y)} ∧
      IsGδ {v : W | ContinuousWithinAt
        (fun p : V × E ↦ b.equivFunL (L p (b j)) i) (W ×ˢ B) (v.val, y)}) :
    Dense {v : W | ContinuousAt L (v.val, y)} := by
  have : BaireSpace W := hW.baireSpace
  have hd := dense_iInter_of_Gδ
    (fun q : Fin n × Fin n ↦ (hentry q.1 q.2).2)
    (fun q : Fin n × Fin n ↦ (hentry q.1 q.2).1)
  apply hd.mono
  intro v hv
  apply (continuousAt_linearMap_iff_coordinates b L (v.val, y)).mpr
  intro i j
  have hc : ContinuousWithinAt (fun p : V × E ↦ b.equivFunL (L p (b j)) i)
      (W ×ˢ B) (v.val, y) := Set.mem_iInter.mp hv (i, j)
  exact hc.continuousAt ((hW.prod hB).mem_nhds ⟨v.property, hy⟩)

/-- Montgomery (1945), Lemmas 1′ and 2, pp.384–385, for the original action in Euclidean model coordinates. -/
theorem action_coordinate_dense_good_parameters_euclidean
    {r n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [AddAction (EuclideanSpace ℝ (Fin r)) M]
    [ContinuousVAdd (EuclideanSpace ℝ (Fin r)) M]
    (hsmooth : ∀ v : EuclideanSpace ℝ (Fin r),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M)
    (W : Set (EuclideanSpace ℝ (Fin r))) (hW : IsOpen W)
    (a : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (hdom : ∀ v ∈ W, ∀ z ∈ Metric.ball a R,
      z ∈ e.target ∧ v +ᵥ e.symm z ∈ f.source)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Metric.ball a R) :
    Dense {v : W | ContinuousAt
      (fun p : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin n) ↦
        fderiv ℝ (fun z ↦ f (p.1 +ᵥ e.symm z)) p.2) (v.val, y)} := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨hF, hD, hH⟩ :=
    action_coordinate_scalar_family_data hsmooth e f he hf b W (Metric.ball a R) hdom
  apply dense_good_parameters_of_coordinate_entries b W hW (Metric.ball a R) Metric.isOpen_ball y hy
  intro i j
  apply Analysis.Regularity.montgomery_parameter_derivative_dense_joint_continuity
    W hW a R j
    (fun p ↦ b.equivFunL (f (p.1 +ᵥ e.symm p.2)) i)
    (fun p ↦ b.equivFunL (fderiv ℝ (fun z ↦ f (p.1 +ᵥ e.symm z)) p.2 (b j)) i)
    (hF i) ?_ (fun v hv ↦ hH v hv i j) y hy
  intro v hv z hz
  simpa only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using
    hD v hv z hz i j

end HolomorphicAnosov.VectorActionSpatialSupport


namespace HolomorphicAnosov

open VectorActionSpatialSupport
open scoped ContDiff

/-- Montgomery's spatial-derivative continuity theorem, specialized to a finite-dimensional real vector group. -/
theorem vector_action_spatial_derivatives_continuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [AddAction V M] [ContinuousVAdd V M]
    (hsmooth : ∀ v : V, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (k : ℕ) (s : Set (V × E)) (hs : IsOpen s)
    (hdom : ∀ p ∈ s, p.2 ∈ e.target ∧ (p.1 +ᵥ e.symm p.2) ∈ f.source) :
    ContinuousOn
      (fun p : V × E ↦ iteratedFDeriv ℝ k (fun y : E ↦ f (p.1 +ᵥ e.symm y)) p.2) s := by
  cases k with
  | zero =>
    intro p hp
    have hact : ContinuousAt (fun q : V × E ↦ q.1 +ᵥ e.symm q.2) p :=
      continuousAt_fst.vadd ((e.symm.continuousAt (hdom p hp).1).comp continuousAt_snd)
    have hcoord : ContinuousAt (fun q : V × E ↦ f (q.1 +ᵥ e.symm q.2)) p :=
      (f.continuousAt (hdom p hp).2).comp_of_eq hact rfl
    exact ((continuousMultilinearCurryFin0 ℝ E E).symm.continuous.continuousAt.comp
      hcoord).continuousWithinAt
  | succ k =>
    cases k with
    | zero =>
      have hfirst : ContinuousOn
          (fun p : V × E ↦ fderiv ℝ (fun z : E ↦ f (p.1 +ᵥ e.symm z)) p.2) s := by
        intro p hp
        obtain ⟨hy, hpy⟩ := hdom p hp
        obtain ⟨rad, hrad, hproduct⟩ :=
          exists_action_coordinate_product e f p.1 p.2 hy hpy
        let W : Set V := Metric.ball p.1 rad
        let B : Set E := Metric.ball p.2 rad
        let b := Module.finBasis ℝ E
        have hW : IsOpen W := Metric.isOpen_ball
        have hWmem : p.1 ∈ W := Metric.mem_ball_self hrad
        have hBmem : p.2 ∈ B := Metric.mem_ball_self hrad
        obtain ⟨hF, hD, hH⟩ :=
          action_coordinate_scalar_family_data hsmooth e f he hf b W B hproduct
        have hgood : Dense {v : W | ContinuousAt
            (fun q : V × E ↦ fderiv ℝ (fun z : E ↦ f (q.1 +ᵥ e.symm z)) q.2)
              (v.val, p.2)} := by
          apply dense_good_parameters_of_coordinate_entries b W hW B Metric.isOpen_ball
            p.2 hBmem
          intro i j
          exact Analysis.Regularity.montgomery_directional_derivative_dense_joint_continuity
            W hW p.2 rad (b j)
            (fun q ↦ b.equivFunL (f (q.1 +ᵥ e.symm q.2)) i)
            (fun q ↦ b.equivFunL (fderiv ℝ (fun z ↦ f (q.1 +ᵥ e.symm z)) q.2 (b j)) i)
            (hF i) (fun v hv z hz ↦ hD v hv z hz i j)
            (fun v hv ↦ hH v hv i j) p.2 hBmem
        let : Nonempty W := ⟨⟨p.1, hWmem⟩⟩
        obtain ⟨v₀, hv₀⟩ := hgood.nonempty
        obtain ⟨hy₀, hv₀dom⟩ := hproduct v₀.val v₀.property p.2 hBmem
        have hzero := action_coordinate_good_parameter_to_identity
          hsmooth e f he hf v₀.val p.2 hy₀ hv₀dom hv₀
        exact (action_coordinate_identity_to_parameter
          hsmooth e f he hf p.1 p.2 hy hpy hzero).continuousWithinAt
      intro p hp
      have hc := (continuousMultilinearCurryFin1 ℝ E E).symm.continuous.continuousAt
        |>.comp_continuousWithinAt (hfirst p hp)
      convert hc using 1
      ext q m
      simp
    | succ k =>
      exact action_coordinate_spatial_jet_transfer hsmooth e f he hf k s hs hdom


end HolomorphicAnosov

