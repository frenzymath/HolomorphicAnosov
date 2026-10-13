import HolomorphicAnosov.Analysis.Complex.HolomorphicSliceSchwarzianContinuous
import HolomorphicAnosov.Ghys.SchwarzianCoordinateIndependence
import HolomorphicAnosov.Paper.Ghys.SchwarzianLeafCocycleNativeProvider
import HolomorphicAnosov.Paper.Ghys.NativeAffineHolonomyCoordinatesG1
import HolomorphicAnosov.Paper.Ghys.IntrinsicPresentationPlaqueHolomorphic
import HolomorphicAnosov.Paper.Ghys.ArbitraryAffinePresentationJetIdentification

/-!
# Scalar Schwarzians for the supplied affine holonomy family

Source: Ghys, Holomorphic Anosov systems (1995), §4 pp.594–597;
Demailly, Complex Analytic and Differential Geometry, I §3.B pp.22–23.
DAG node: `analysis.affine_holonomy_family_schwarzian_g17`.
-/

noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- The literal scalar evaluation of an ambient-continuous holonomy family in
local affine coordinates has jointly continuous Schwarzian. The domain keeps
all actual source and target guards. At every guarded point, the ambient
coordinate agrees as a germ with an actual receiving affine chart; pulling
that equality back gives slice holomorphicity and nonzero derivative. Joint
holomorphic derivative continuity then supplies the Schwarzian continuity.
Source: Ghys §4 p.594 and Demailly I §3.B pp.22–23. -/
theorem affine_holonomy_family_schwarzian_continuous
    {T M L : Type*} {R : T → Type*}
    [TopologicalSpace T] [TopologicalSpace M] [TopologicalSpace L]
    [ChartedSpace (ComplexModel 1) L] [IsManifold (complexModel 1) ∞ L]
    [∀ t, TopologicalSpace (R t)] [∀ t, ChartedSpace (ComplexModel 1) (R t)]
    [∀ t, IsManifold (complexModel 1) ∞ (R t)]
    (A : ComplexAffineStructure L) (B : ∀ t, ComplexAffineStructure (R t))
    (h : ∀ t, OpenPartialHomeomorph L (R t))
    (hh : ∀ t, IsHolomorphicCurveLocalMap (h t))
    (j : ∀ t, R t → M) (W : Set L) (hW : IsOpen W)
    (hsource : ∀ t, W ⊆ (h t).source)
    (hjoint : ContinuousOn (fun p : T × L ↦ j p.1 (h p.1 p.2)) (univ ×ˢ W))
    (O : Set M) (hO : IsOpen O) (K : M → ℂ) (hK : ContinuousOn K O)
    (hlocal : ∀ t (y : R t), j t y ∈ O →
      ∃ e : OpenPartialHomeomorph (R t) ℂ,
        e ∈ ComplexAffineStructure.maximalAtlas _ (B t) ∧ y ∈ e.source ∧
          (e : R t → ℂ) =ᶠ[𝓝 y] K ∘ j t)
    (c : OpenPartialHomeomorph L ℂ)
    (hc : c ∈ ComplexAffineStructure.maximalAtlas _ A) :
    let D : Set (ℂ × T) := (c.target ∩ c.symm ⁻¹' W) ×ˢ univ
    let E : ℂ × T → M := fun p ↦ j p.2 (h p.2 (c.symm p.1))
    let Ω := D ∩ E ⁻¹' O
    let H : ℂ × T → ℂ := K ∘ E
    IsOpen Ω ∧ ContinuousOn H Ω ∧
      (∀ t, DifferentiableOn ℂ (fun z ↦ H (z,t)) {z | (z,t) ∈ Ω}) ∧
      (∀ p ∈ Ω, deriv (fun z ↦ H (z,p.2)) p.1 ≠ 0) ∧
      ContinuousOn (fun p ↦ schwarzian (fun z ↦ H (z,p.2)) p.1) Ω := by
  intro D E Ω H
  have hD : IsOpen D :=
    (c.symm.continuousOn.isOpen_inter_preimage c.open_target hW).prod isOpen_univ
  have hinv : ContinuousOn (fun p : ℂ × T ↦ c.symm p.1) D :=
    c.symm.continuousOn.comp continuous_fst.continuousOn (fun p hp ↦ hp.1.1)
  have hE : ContinuousOn E D := hjoint.comp
    (continuous_snd.continuousOn.prodMk hinv) (fun p hp ↦ ⟨mem_univ _,hp.1.2⟩)
  have hΩ : IsOpen Ω := hE.isOpen_inter_preimage hD hO
  have hH : ContinuousOn H Ω := hK.comp (hE.mono inter_subset_left)
    (fun p hp ↦ hp.2)
  have hpoint (p : ℂ × T) (hp : p ∈ Ω) :
      DifferentiableAt ℂ (fun z ↦ H (z,p.2)) p.1 ∧
        deriv (fun z ↦ H (z,p.2)) p.1 ≠ 0 := by
    have hct : p.1 ∈ c.target := hp.1.1.1
    have hcw : c.symm p.1 ∈ W := hp.1.1.2
    have hch : c.symm p.1 ∈ (h p.2).source := hsource p.2 hcw
    obtain ⟨e,he,hye,hgerm⟩ := hlocal p.2 (h p.2 (c.symm p.1)) hp.2
    have ht : Tendsto (fun z ↦ h p.2 (c.symm z)) (𝓝 p.1)
        (𝓝 (h p.2 (c.symm p.1))) :=
      ((h p.2).continuousAt hch).tendsto.comp (c.symm.continuousAt hct).tendsto
    have heq : affineLocalMapExpression c (h p.2) e =ᶠ[𝓝 p.1]
        (fun z ↦ H (z,p.2)) := ht.eventually hgerm
    have hcalc := affine_local_map_schwarzian_calculus A (B p.2) A
      (h p.2) (hh p.2) c e hc he (c.symm p.1) (c.map_target hct) hch hye
    have hpdom : p.1 ∈ affineLocalMapDomain c (h p.2) e := ⟨⟨hct,hch⟩,hye⟩
    refine ⟨heq.differentiableAt_iff.mp
      (hcalc.2.1.differentiableAt (hcalc.1.mem_nhds hpdom)),?_⟩
    rw [← heq.deriv_eq]
    exact hcalc.2.2.1 p.1 hpdom
  have hd (t : T) : DifferentiableOn ℂ (fun z ↦ H (z,t)) {z | (z,t) ∈ Ω} :=
    fun z hz ↦ (hpoint (z,t) hz).1.differentiableWithinAt
  have hnz := fun p hp ↦ (hpoint p hp).2
  exact ⟨hΩ,hH,hd,hnz,holomorphic_slice_schwarzian_continuousOn Ω hΩ H hH hd hnz⟩

/-- Fixing the source affine chart makes the scalar Schwarzian independent
of the receiving affine chart. Evaluate the coordinate-independent quadratic
form on the unique tangent vector sent to one by the source chart derivative. -/
theorem affine_scalar_schwarzian_target_independent
    {L R : Type*} [TopologicalSpace L] [TopologicalSpace R]
    [ChartedSpace (ComplexModel 1) L] [ChartedSpace (ComplexModel 1) R]
    (A : ComplexAffineStructure L) (B : ComplexAffineStructure R)
    (h : OpenPartialHomeomorph L R) (hh : IsHolomorphicCurveLocalMap h)
    (c : OpenPartialHomeomorph L ℂ) (e e' : OpenPartialHomeomorph R ℂ)
    (hc : c ∈ A.maximalAtlas _) (he : e ∈ B.maximalAtlas _)
    (he' : e' ∈ B.maximalAtlas _) (z : ℂ) (hzt : z ∈ c.target)
    (hzh : c.symm z ∈ h.source) (hze : h (c.symm z) ∈ e.source)
    (hze' : h (c.symm z) ∈ e'.source) :
    schwarzian (affineLocalMapExpression c h e) z =
      schwarzian (affineLocalMapExpression c h e') z := by
  have hcd : c.MDifferentiable (complexModel 1) 𝓘(ℂ) :=
    ⟨hc.1.1.mdifferentiableOn (by simp), hc.1.2.mdifferentiableOn (by simp)⟩
  obtain ⟨v,hv⟩ := (hcd.mfderiv_surjective (c.map_target hzt)) (1 : ℂ)
  have heq := schwarzian_quadratic_coordinate_independent A B h hh c c e e'
    hc hc he he' (c.symm z) (c.map_target hzt) (c.map_target hzt) hzh hze hze'
  have hev := congrArg (fun Q ↦ Q v) heq
  let vc : ℂ := mfderiv (complexModel 1) 𝓘(ℂ) c (c.symm z) v
  have hvc : vc = 1 := hv
  change schwarzian (affineLocalMapExpression c h e) (c (c.symm z)) * (vc * vc) =
    schwarzian (affineLocalMapExpression c h e') (c (c.symm z)) * (vc * vc) at hev
  simpa [hvc, c.right_inv hzt] using hev

/-- An actual receiving projection factors a transported source map through
the receiving plaque map as a scalar germ. This elementary coordinate identity
keeps the source leaf fixed when the marked root changes. -/
theorem affine_expression_projection_factor_germ
    {L Y R Z : Type*} [TopologicalSpace L] [TopologicalSpace Y]
    [TopologicalSpace R] [TopologicalSpace Z]
    (h : OpenPartialHomeomorph L Y) (E : Y ≃ₜ Z) (k : OpenPartialHomeomorph R Z)
    (c : OpenPartialHomeomorph L ℂ) (d : OpenPartialHomeomorph R ℂ)
    (e : OpenPartialHomeomorph Z ℂ) (hds : d.source = univ)
    (proj : Z → ℂ) (hproj : ∀ z ∈ k.target, proj z = d (k.symm z))
    (G : ℂ → ℂ) (p : L) (hpc : p ∈ c.source) (hph : p ∈ h.source)
    (hpk : E (h p) ∈ k.target)
    (hG : (fun z ↦ proj (E (h z))) =ᶠ[𝓝 p] (fun z ↦ G (c z))) :
    ((affineLocalMapExpression d k e) ∘ G) =ᶠ[𝓝 (c p)]
      affineLocalMapExpression c h (E.toOpenPartialHomeomorph.trans e) := by
  have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa only [c.left_inv hpc] using (c.symm.continuousAt (c.map_source hpc)).tendsto
  have hknear : ∀ᶠ z in 𝓝 p, E (h z) ∈ k.target :=
    (E.continuous.continuousAt.comp (h.continuousAt hph)).eventually
      (k.open_target.mem_nhds hpk)
  filter_upwards [ht.eventually hG,ht.eventually hknear,
    c.open_target.mem_nhds (c.map_source hpc)] with z hz hk hzc
  have hgz : G z = proj (E (h (c.symm z))) := by
    simpa only [c.right_inv hzc] using hz.symm
  change e (k (d.symm (G z))) = e (E (h (c.symm z)))
  rw [hgz,hproj _ hk,d.left_inv (by rw [hds]; trivial),k.right_inv hk]

/-- The scalar chain rule converts a source composite variation bound into
an inverse-squared-derivative bound in the receiving coordinate. Each of the
two receiving holonomies may have a different target curve and affine chart. -/
theorem affine_local_composite_variation_le
    {L R Y Z : Type*}
    [TopologicalSpace L] [TopologicalSpace R] [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel 1) L] [ChartedSpace (ComplexModel 1) R]
    [ChartedSpace (ComplexModel 1) Y] [ChartedSpace (ComplexModel 1) Z]
    (A : ComplexAffineStructure L) (B : ComplexAffineStructure R)
    (A₀ : ComplexAffineStructure Y) (A₁ : ComplexAffineStructure Z)
    (g : OpenPartialHomeomorph L R) (h₀ : OpenPartialHomeomorph R Y)
    (h₁ : OpenPartialHomeomorph R Z)
    (hg : IsHolomorphicCurveLocalMap g) (hh₀ : IsHolomorphicCurveLocalMap h₀)
    (hh₁ : IsHolomorphicCurveLocalMap h₁)
    (c : OpenPartialHomeomorph L ℂ) (d : OpenPartialHomeomorph R ℂ)
    (e₀ : OpenPartialHomeomorph Y ℂ) (e₁ : OpenPartialHomeomorph Z ℂ)
    (hc : c ∈ A.maximalAtlas _) (hd : d ∈ B.maximalAtlas _)
    (he₀ : e₀ ∈ A₀.maximalAtlas _) (he₁ : e₁ ∈ A₁.maximalAtlas _)
    (x : L) (hxc : x ∈ c.source) (hxg : x ∈ g.source) (hxd : g x ∈ d.source)
    (hx₀ : g x ∈ h₀.source) (hx₁ : g x ∈ h₁.source)
    (hxe₀ : h₀ (g x) ∈ e₀.source) (hxe₁ : h₁ (g x) ∈ e₁.source)
    (C : ℝ)
    (hbound : dist (schwarzian (affineLocalMapExpression c (g.trans h₀) e₀) (c x))
      (schwarzian (affineLocalMapExpression c (g.trans h₁) e₁) (c x)) ≤ C) :
    dist (schwarzian (affineLocalMapExpression d h₀ e₀) (d (g x)))
      (schwarzian (affineLocalMapExpression d h₁ e₁) (d (g x))) ≤
        C / ‖deriv (affineLocalMapExpression c g d) (c x)‖ ^ 2 := by
  have hcalc₀ := affine_local_map_schwarzian_calculus A B A₀ g hg c d hc hd x hxc hxg hxd
  have hcalc₁ := affine_local_map_schwarzian_calculus A B A₁ g hg c d hc hd x hxc hxg hxd
  have hchain₀ := (hcalc₀.2.2.2.2 h₀ e₀ hh₀ he₀ hx₀ hxe₀).1
  have hchain₁ := (hcalc₁.2.2.2.2 h₁ e₁ hh₁ he₁ hx₁ hxe₁).1
  have hne : deriv (affineLocalMapExpression c g d) (c x) ≠ 0 :=
    hcalc₀.2.2.1 (c x) (by
      simpa [affineLocalMapDomain,c.left_inv hxc] using
        And.intro (And.intro (c.map_source hxc) hxg) hxd)
  have heq : schwarzian (affineLocalMapExpression c (g.trans h₀) e₀) (c x) -
      schwarzian (affineLocalMapExpression c (g.trans h₁) e₁) (c x) =
      (schwarzian (affineLocalMapExpression d h₀ e₀) (d (g x)) -
        schwarzian (affineLocalMapExpression d h₁ e₁) (d (g x))) *
      deriv (affineLocalMapExpression c g d) (c x) ^ 2 := by
    rw [hchain₀,hchain₁]
    ring
  rw [dist_eq_norm,heq,norm_mul,norm_pow] at hbound
  rw [dist_eq_norm]
  exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hne))).mpr hbound

/-- Local continuous ambient affine coordinates glue to one continuous
scalar Schwarzian on the entire common source domain. Receiving-chart
independence makes the choices agree; no single affine coordinate on all
receiving leaves is assumed. In particular every compact subset has a finite
uniform bound on all scalar Schwarzian differences. -/
theorem affine_holonomy_family_schwarzian_global
    {T M L : Type*} {R : T → Type*}
    [TopologicalSpace T] [TopologicalSpace M] [TopologicalSpace L]
    [ChartedSpace (ComplexModel 1) L] [IsManifold (complexModel 1) ∞ L]
    [∀ t, TopologicalSpace (R t)] [∀ t, ChartedSpace (ComplexModel 1) (R t)]
    [∀ t, IsManifold (complexModel 1) ∞ (R t)]
    (A : ComplexAffineStructure L) (B : ∀ t, ComplexAffineStructure (R t))
    (h : ∀ t, OpenPartialHomeomorph L (R t))
    (hh : ∀ t, IsHolomorphicCurveLocalMap (h t))
    (j : ∀ t, R t → M) (W : Set L) (hW : IsOpen W)
    (hsource : ∀ t, W ⊆ (h t).source)
    (hjoint : ContinuousOn (fun p : T × L ↦ j p.1 (h p.1 p.2)) (univ ×ˢ W))
    (hcoords : ∀ x : M, ∃ (O : Set M) (K : M → ℂ),
      IsOpen O ∧ x ∈ O ∧ ContinuousOn K O ∧
      ∀ t (y : R t), j t y ∈ O →
        ∃ e : OpenPartialHomeomorph (R t) ℂ,
          e ∈ (B t).maximalAtlas _ ∧ y ∈ e.source ∧
            (e : R t → ℂ) =ᶠ[𝓝 y] K ∘ j t)
    (c : OpenPartialHomeomorph L ℂ) (hc : c ∈ A.maximalAtlas _) :
    let D : Set (ℂ × T) := (c.target ∩ c.symm ⁻¹' W) ×ˢ univ
    ∃ S : ℂ × T → ℂ, ContinuousOn S D ∧
      (∀ p ∈ D, ∀ e : OpenPartialHomeomorph (R p.2) ℂ,
        e ∈ (B p.2).maximalAtlas _ → h p.2 (c.symm p.1) ∈ e.source →
        S p = schwarzian (affineLocalMapExpression c (h p.2) e) p.1) ∧
      ∀ C : Set (ℂ × T), IsCompact C → C ⊆ D →
        ∃ b : ℝ, 0 ≤ b ∧ ∀ p ∈ C, ∀ q ∈ C, dist (S p) (S q) ≤ b := by
  classical
  intro D
  choose e he hye using fun p : ℂ × T ↦
    affine_chart_at_g12 (B p.2) (h p.2 (c.symm p.1))
  let S : ℂ × T → ℂ := fun p ↦
    schwarzian (affineLocalMapExpression c (h p.2) (e p)) p.1
  have hrepr (p : ℂ × T) (hp : p ∈ D)
      (e' : OpenPartialHomeomorph (R p.2) ℂ)
      (he' : e' ∈ (B p.2).maximalAtlas _)
      (hy' : h p.2 (c.symm p.1) ∈ e'.source) :
      S p = schwarzian (affineLocalMapExpression c (h p.2) e') p.1 :=
    affine_scalar_schwarzian_target_independent A (B p.2) (h p.2) (hh p.2)
      c (e p) e' hc (he p) he' p.1 hp.1.1 (hsource p.2 hp.1.2) (hye p) hy'
  have hS : ContinuousOn S D := by
    intro p hp
    obtain ⟨O,K,hO,hpO,hK,hlocal⟩ := hcoords (j p.2 (h p.2 (c.symm p.1)))
    let E : ℂ × T → M := fun q ↦ j q.2 (h q.2 (c.symm q.1))
    let Ω : Set (ℂ × T) := D ∩ E ⁻¹' O
    let H : ℂ × T → ℂ := K ∘ E
    obtain ⟨hΩ,_,_,_,hSC⟩ := affine_holonomy_family_schwarzian_continuous
      A B h hh j W hW hsource hjoint O hO K hK hlocal c hc
    have hpΩ : p ∈ Ω := ⟨hp,hpO⟩
    have heq : S =ᶠ[𝓝 p] (fun q ↦ schwarzian (fun z ↦ H (z,q.2)) q.1) := by
      filter_upwards [hΩ.mem_nhds hpΩ] with q hq
      obtain ⟨e',he',hy',hgerm⟩ := hlocal q.2 (h q.2 (c.symm q.1)) hq.2
      rw [hrepr q hq.1 e' he' hy']
      have ht : Tendsto (fun z ↦ h q.2 (c.symm z)) (𝓝 q.1)
          (𝓝 (h q.2 (c.symm q.1))) :=
        ((h q.2).continuousAt (hsource q.2 hq.1.1.2)).tendsto.comp
          (c.symm.continuousAt hq.1.1.1).tendsto
      have hg : affineLocalMapExpression c (h q.2) e' =ᶠ[𝓝 q.1]
          (fun z ↦ H (z,q.2)) := ht.eventually hgerm
      simp only [schwarzian, hg.deriv_eq, hg.deriv.deriv_eq, hg.deriv.deriv.deriv_eq]
    exact ((hSC.continuousAt (hΩ.mem_nhds hpΩ)).congr_of_eventuallyEq heq).continuousWithinAt
  refine ⟨S,hS,hrepr,?_⟩
  intro C hC hCD
  obtain ⟨b,hb⟩ := hC.exists_bound_of_continuousOn (hS.mono hCD)
  refine ⟨2 * max b 0, mul_nonneg (by norm_num) (le_max_right _ _),?_⟩
  intro p hp q hq
  calc
    dist (S p) (S q) ≤ ‖S p‖ + ‖S q‖ := dist_le_norm_add_norm _ _
    _ ≤ b + b := add_le_add (hb p hp) (hb q hq)
    _ ≤ 2 * max b 0 := by linarith [le_max_left b 0]

/-- The actual one-box transports of the supplied intrinsic presentation have
jointly continuous scalar Schwarzians in any ambient continuous affine
coordinate. Both holomorphicity and the jointly continuous ambient family are
proved providers for these exact transports. -/
theorem one_box_affine_holonomy_schwarzian_continuous
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves)
      (b : P.foliations.boxIndex) (s₀ : FoliationCoordinateDisk (2*d-2))
      (w₀ : FoliationCoordinateDisk 2),
      let x := fun s ↦ ((P.foliations.box b).chart (s,w₀)).val
      let W : Set (P.foliations.ULeaf (x s₀)) := {z | ∃ w : FoliationCoordinateDisk 2,
        ((P.foliations.box b).chart (s₀,w)).val = z.val}
      ∀ (c : OpenPartialHomeomorph (P.foliations.ULeaf (x s₀)) ℂ),
      c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves (x s₀)) →
      ∀ (O : Set M) (K : M → ℂ), IsOpen O → ContinuousOn K O →
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ∀ y : IntrinsicFoliationLeaf P.foliations.unstablePartition q, y.val ∈ O →
          ∃ e : OpenPartialHomeomorph (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ,
            e ∈ ComplexAffineStructure.maximalAtlas _ (A.structureAt q) ∧ y ∈ e.source ∧
              (e : _ → ℂ) =ᶠ[𝓝 y] K ∘ Subtype.val) →
      ∃ h : ∀ s, LocalPlaqueTransport P.foliations (x s₀) (x s),
        (∀ s, (h s).box = b ∧ (h s).first = s₀ ∧ (h s).second = s ∧
          (h s).transverse = w₀ ∧ (h s).map.source = W) ∧
        let D : Set (ℂ × FoliationCoordinateDisk (2*d-2)) := (c.target ∩ c.symm ⁻¹' W) ×ˢ univ
        let E : ℂ × FoliationCoordinateDisk (2*d-2) → M := fun p ↦ ((h p.2).map (c.symm p.1)).val
        let Ω := D ∩ E ⁻¹' O
        let H : ℂ × FoliationCoordinateDisk (2*d-2) → ℂ := K ∘ E
        IsOpen Ω ∧ ContinuousOn H Ω ∧
          (∀ s, DifferentiableOn ℂ (fun z ↦ H (z,s)) {z | (z,s) ∈ Ω}) ∧
          (∀ p ∈ Ω, deriv (fun z ↦ H (z,p.2)) p.1 ≠ 0) ∧
          ContinuousOn (fun p ↦ schwarzian (fun z ↦ H (z,p.2)) p.1) Ω := by
  let := P.realCharts
  let : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  let : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
  intro A b s₀ w₀ x W c hc O K hO hK hlocal
  obtain ⟨h,hmeta,hjoint⟩ := one_box_plaque_transport_continuous_family_g1 P.foliations b s₀ w₀
  have hs (s) : (h s).map.source = W := (hmeta s).2.2.2.2
  refine ⟨h,hmeta,?_⟩
  apply affine_holonomy_family_schwarzian_continuous
    (A.atPoint P.foliations P.complexLeaves (x s₀))
    (fun s ↦ A.atPoint P.foliations P.complexLeaves (x s))
    (fun s ↦ (h s).map)
    (fun s ↦ intrinsicPresentation_plaque_holomorphic f a hRank P _ _ (h s))
    (fun _ ↦ Subtype.val) W
    (by rw [← hs s₀]; exact (h s₀).map.open_source)
    (fun s ↦ by rw [hs s]) hjoint O hO K hK
    (fun s y hy ↦ hlocal _ y hy) c hc

/-- For the original supplied affine family, one-box holonomies have a
continuous scalar Schwarzian in a complete source coordinate. Its receiving
chart formula holds for every affine chart, and every compact parameter core
has a finite variation bound. The coordinate bridge identifies the arbitrary
input A before invoking native local affine coordinates. -/
theorem one_box_complete_affine_schwarzian_family
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
      A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves →
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        (A.structureAt q).Complete (IntrinsicFoliationLeaf P.foliations.unstablePartition q)) →
      ∀ (b : P.foliations.boxIndex) (s₀ : FoliationCoordinateDisk (2*d-2))
        (w₀ : FoliationCoordinateDisk 2),
      let x := fun s ↦ ((P.foliations.box b).chart (s,w₀)).val
      let W : Set (P.foliations.ULeaf (x s₀)) := {z | ∃ w : FoliationCoordinateDisk 2,
        ((P.foliations.box b).chart (s₀,w)).val = z.val}
      ∃ (c : OpenPartialHomeomorph (P.foliations.ULeaf (x s₀)) ℂ)
        (h : ∀ s, LocalPlaqueTransport P.foliations (x s₀) (x s))
        (S : ℂ × FoliationCoordinateDisk (2*d-2) → ℂ),
        c ∈ (A.atPoint P.foliations P.complexLeaves (x s₀)).maximalAtlas _ ∧
        c.source = univ ∧ c.target = univ ∧
        (∀ s, (h s).box = b ∧ (h s).first = s₀ ∧ (h s).second = s ∧
          (h s).transverse = w₀ ∧ (h s).map.source = W) ∧
        let D : Set (ℂ × FoliationCoordinateDisk (2*d-2)) := (c.target ∩ c.symm ⁻¹' W) ×ˢ univ
        ContinuousOn S D ∧
        (∀ p ∈ D, ∀ e : OpenPartialHomeomorph (P.foliations.ULeaf (x p.2)) ℂ,
          e ∈ (A.atPoint P.foliations P.complexLeaves (x p.2)).maximalAtlas _ →
          (h p.2).map (c.symm p.1) ∈ e.source →
          S p = schwarzian (affineLocalMapExpression c (h p.2).map e) p.1) ∧
        ∀ C : Set (ℂ × FoliationCoordinateDisk (2*d-2)), IsCompact C → C ⊆ D →
          ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ C, ∀ q ∈ C, dist (S p) (S q) ≤ B := by
  let := P.realCharts
  let : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  let : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
  intro A hAct hCont hComplete b s₀ w₀ x W
  obtain ⟨E,hE⟩ := (hComplete (Quotient.mk P.foliations.unstablePartition (x s₀))).2
  let c := E.toHomeomorph.toOpenPartialHomeomorph
  have hc : c ∈ (A.atPoint P.foliations P.complexLeaves (x s₀)).maximalAtlas _ :=
    ⟨⟨E.contMDiff.contMDiffOn,E.symm.contMDiff.contMDiffOn⟩,
      fun d hd y hy ↦ hE d hd y hy.1⟩
  obtain ⟨h,hmeta,hjoint⟩ := one_box_plaque_transport_continuous_family_g1 P.foliations b s₀ w₀
  have hs (s) : (h s).map.source = W := (hmeta s).2.2.2.2
  obtain ⟨S,hS,hrepr,hbound⟩ := affine_holonomy_family_schwarzian_global
    (A.atPoint P.foliations P.complexLeaves (x s₀))
    (fun s ↦ A.atPoint P.foliations P.complexLeaves (x s))
    (fun s ↦ (h s).map)
    (fun s ↦ intrinsicPresentation_plaque_holomorphic f a hRank P _ _ (h s))
    (fun _ ↦ Subtype.val) W
    (by rw [← hs s₀]; exact (h s₀).map.open_source)
    (fun s ↦ by rw [hs s]) hjoint
    (by
      intro y
      obtain ⟨O,K,hO,hyO,hK,hlocal⟩ :=
        arbitrary_affine_presentation_local_continuous_coordinates f a hRank P A hAct hCont y
      exact ⟨O,K,hO,hyO,hK,fun s z hz ↦ hlocal _ z hz⟩) c hc
  exact ⟨c,h,S,hc,rfl,rfl,hmeta,hS,hrepr,hbound⟩

/-- Project a literal intrinsic holomorphic transport through a receiving
box onto one fixed unstable plaque, then read its affine coordinate. The
result is holomorphic with nonzero derivative wherever the transported point
lies in the box. Locally it is the intrinsic transport followed by the inverse
of the actual receiving plaque holonomy, whose target is an intrinsic open
plaque. This proves the analytic hypothesis for the compact root density. -/
theorem receiving_projection_scalar_calculus
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves)
      (g : M → M), Continuous g →
      ∀ (x x' : M) (E : Biholomorph 1 1 (P.foliations.ULeaf x) (P.foliations.ULeaf x')),
      (∀ z, (E z).val = g z.val) →
      ∀ (c : OpenPartialHomeomorph (P.foliations.ULeaf x) ℂ),
      c ∈ (A.atPoint P.foliations P.complexLeaves x).maximalAtlas _ →
      ∀ (b : P.foliations.boxIndex) (s₀ : FoliationCoordinateDisk (2*d-2))
        (w₀ : FoliationCoordinateDisk 2),
      let y := fun s ↦ ((P.foliations.box b).chart (s,w₀)).val
      let W : Set (P.foliations.ULeaf (y s₀)) := {z | ∃ w : FoliationCoordinateDisk 2,
        ((P.foliations.box b).chart (s₀,w)).val = z.val}
      let j : FoliationCoordinateDisk 2 → P.foliations.ULeaf (y s₀) := fun w ↦
        ⟨((P.foliations.box b).chart (s₀,w)).val,
          (P.foliations.unstable_label b s₀ w).trans (P.foliations.unstable_label b s₀ w₀).symm⟩
      ∀ (h : ∀ s, LocalPlaqueTransport P.foliations (y s₀) (y s)),
      (∀ s, (h s).box = b ∧ (h s).first = s₀ ∧ (h s).second = s ∧
        (h s).transverse = w₀ ∧ (h s).map.source = W) →
      ∀ (d₀ : OpenPartialHomeomorph (P.foliations.ULeaf (y s₀)) ℂ),
      d₀ ∈ (A.atPoint P.foliations P.complexLeaves (y s₀)).maximalAtlas _ →
      d₀.source = univ → ∀ proj : M → ℂ,
      (∀ s w, proj ((P.foliations.box b).chart (s,w)).val = d₀ (j w)) →
      let Ω : Set ℂ := c.target ∩ (fun z ↦ g (c.symm z).val) ⁻¹' (P.foliations.box b).image
      let G : ℂ → ℂ := fun z ↦ proj (g (c.symm z).val)
      IsOpen Ω ∧ DifferentiableOn ℂ G Ω ∧ ∀ z ∈ Ω, deriv G z ≠ 0 := by
  let := P.realCharts
  let : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  let : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
  intro A g hg x x' E hE c hc b s₀ w₀ y W j h hmeta d₀ hd₀ hds proj hproj Ω G
  have heval : ContinuousOn (fun z ↦ g (c.symm z).val) c.target :=
    hg.comp_continuousOn ((P.foliations.unstable_inclusion _).comp_continuousOn c.symm.continuousOn)
  have hΩ : IsOpen Ω := heval.isOpen_inter_preimage c.open_target (P.foliations.box b).isOpen_image
  have hpoint (z : ℂ) (hz : z ∈ Ω) : DifferentiableAt ℂ G z ∧ deriv G z ≠ 0 := by
    let p := c.symm z
    let st := (P.foliations.box b).chart.symm ⟨g p.val,hz.2⟩
    have hst : ((P.foliations.box b).chart (st.1,st.2)).val = g p.val :=
      congrArg Subtype.val ((P.foliations.box b).chart.apply_symm_apply ⟨g p.val,hz.2⟩)
    have hq : Quotient.mk P.foliations.unstablePartition (y st.1) =
        Quotient.mk P.foliations.unstablePartition x' := by
      calc
        _ = P.foliations.unstableLabel b st.1 := P.foliations.unstable_label b st.1 w₀
        _ = Quotient.mk P.foliations.unstablePartition (g p.val) :=
          (P.foliations.unstable_label b st.1 st.2).symm.trans
            (congrArg (Quotient.mk P.foliations.unstablePartition) hst)
        _ = _ := by rw [← hE p]; exact (E p).property
    let E' := E.trans (unstableLeafLabelBiholomorph_g17 f a P _ _ hq.symm)
    have hE' (v) : (E' v).val = g v.val :=
      (unstableLeafLabelBiholomorph_g17_val f a P _ _ hq.symm (E v)).trans (hE v)
    have htarget : (h st.1).map.target = {v | ∃ w : FoliationCoordinateDisk 2,
        ((P.foliations.box b).chart (st.1,w)).val = v.val} := by
      have hsrc : (h st.1).map.source = {v | ∃ w : FoliationCoordinateDisk 2,
          ((P.foliations.box (h st.1).box).chart ((h st.1).first,w)).val = v.val} := by
        rw [(hmeta st.1).1,(hmeta st.1).2.1]
        exact (hmeta st.1).2.2.2.2
      have ht := local_plaque_transport_full_target_g17 P.foliations (h st.1) hsrc
      rw [(hmeta st.1).2.2.1] at ht
      rw [(hmeta st.1).1] at ht
      exact ht
    have hEp : E' p ∈ (h st.1).map.target := by
      rw [htarget]
      exact ⟨st.2,hst.trans (hE' p).symm⟩
    let k := E'.toHomeomorph.toOpenPartialHomeomorph.trans (h st.1).map.symm
    have hh := intrinsicPresentation_plaque_holomorphic f a hRank P _ _ (h st.1)
    have hk : IsHolomorphicCurveLocalMap k := by
      constructor
      · exact hh.2.comp E'.contMDiff.contMDiffOn (fun v hv ↦ hv.2)
      · exact E'.symm.contMDiff.comp_contMDiffOn (hh.1.mono (fun v hv ↦ hv.1))
    have hpk : p ∈ k.source := ⟨mem_univ _,hEp⟩
    have hpd : k p ∈ d₀.source := by rw [hds]; trivial
    have hcalc := affine_local_map_schwarzian_calculus
      (A.atPoint P.foliations P.complexLeaves x)
      (A.atPoint P.foliations P.complexLeaves (y s₀))
      (A.atPoint P.foliations P.complexLeaves x)
      k hk c d₀ hc hd₀ p (c.map_target hz.1) hpk hpd
    have hzdom : z ∈ affineLocalMapDomain c k d₀ := ⟨⟨hz.1,hpk⟩,hpd⟩
    have heq : affineLocalMapExpression c k d₀ =ᶠ[𝓝 z] G := by
      filter_upwards [hcalc.1.mem_nhds hzdom] with w hw
      have hv : E' (c.symm w) ∈ (h st.1).map.target := hw.1.2.2
      have hpj := plaque_projection_eq_inverse_transport_g17 P.foliations (h st.1) d₀ proj
        (by
          intro v t ht
          have hjv : j t = v := Subtype.ext (by
            rw [(hmeta st.1).2.1,(hmeta st.1).1] at ht
            exact ht)
          rw [(hmeta st.1).2.2.1,(hmeta st.1).1]
          exact (hproj st.1 t).trans (congrArg d₀ hjv))
        (E' (c.symm w)) hv
      change d₀ ((h st.1).map.symm (E' (c.symm w))) = proj (g (c.symm w).val)
      rw [← hpj,hE']
    refine ⟨heq.differentiableAt_iff.mp
      (hcalc.2.1.differentiableAt (hcalc.1.mem_nhds hzdom)),?_⟩
    rw [← heq.deriv_eq]
    exact hcalc.2.2.1 z hzdom
  exact ⟨hΩ,fun z hz ↦ (hpoint z hz).1.differentiableWithinAt,fun z hz ↦ (hpoint z hz).2⟩

section FamilyData
variable {s : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
  (F : TransverseContinuousFoliations s 2 M)
  [∀ x : M, ChartedSpace (ComplexModel 1) (F.ULeaf x)]

/-- Packaging of the already constructed whole-box scalar family. Every map
and affine chart retains its exact original leaf and source guards. -/
structure CompletePlaqueScalarFamily
    (A : ∀ x : M, ComplexAffineStructure (F.ULeaf x))
    (b : F.boxIndex) (s₀ : FoliationCoordinateDisk (s))
    (w₀ : FoliationCoordinateDisk 2) where
  coordinate : OpenPartialHomeomorph
    (F.ULeaf (((F.box b).chart (s₀,w₀)).val)) ℂ
  transport : ∀ s : FoliationCoordinateDisk (s),
    LocalPlaqueTransport F (((F.box b).chart (s₀,w₀)).val)
      (((F.box b).chart (s,w₀)).val)
  value : ℂ × FoliationCoordinateDisk (s) → ℂ
  coordinate_mem : coordinate ∈ (A
    (((F.box b).chart (s₀,w₀)).val)).maximalAtlas _
  source_eq : coordinate.source = univ
  target_eq : coordinate.target = univ
  transport_meta : ∀ s, (transport s).box = b ∧ (transport s).first = s₀ ∧
    (transport s).second = s ∧ (transport s).transverse = w₀ ∧
    (transport s).map.source = {z | ∃ w : FoliationCoordinateDisk 2,
      ((F.box b).chart (s₀,w)).val = z.val}
  continuous_value : ContinuousOn value
    ((coordinate.target ∩ coordinate.symm ⁻¹' {z | ∃ w : FoliationCoordinateDisk 2,
      ((F.box b).chart (s₀,w)).val = z.val}) ×ˢ univ)
  represents : ∀ p ∈ ((coordinate.target ∩ coordinate.symm ⁻¹'
      {z | ∃ w : FoliationCoordinateDisk 2, ((F.box b).chart (s₀,w)).val = z.val}) ×ˢ univ),
    ∀ e : OpenPartialHomeomorph
      (F.ULeaf (((F.box b).chart (p.2,w₀)).val)) ℂ,
      e ∈ (A
        (((F.box b).chart (p.2,w₀)).val)).maximalAtlas _ →
      (transport p.2).map (coordinate.symm p.1) ∈ e.source →
      value p = schwarzian (affineLocalMapExpression coordinate (transport p.2).map e) p.1

namespace CompletePlaqueScalarFamily
variable {F} {A : ∀ x : M, ComplexAffineStructure (F.ULeaf x)}
  {b : F.boxIndex} {s₀ : FoliationCoordinateDisk (s)}
  {w₀ : FoliationCoordinateDisk 2} (D : CompletePlaqueScalarFamily F A b s₀ w₀)

def anchor (_D : CompletePlaqueScalarFamily F A b s₀ w₀) (w : FoliationCoordinateDisk 2) :
    F.ULeaf (((F.box b).chart (s₀,w₀)).val) :=
  ⟨((F.box b).chart (s₀,w)).val,
    (F.unstable_label b s₀ w).trans (F.unstable_label b s₀ w₀).symm⟩

def label (w : FoliationCoordinateDisk 2) : ℂ := D.coordinate (D.anchor w)

theorem open_anchor : IsOpenEmbedding D.anchor :=
  unstable_plaque_open_at_class_g10 F b s₀ _
    (F.unstable_label b s₀ w₀).symm

theorem open_label : IsOpenEmbedding D.label :=
  (D.coordinate.isOpenEmbedding D.source_eq).comp D.open_anchor

def projection (z : M) : ℂ := by
  classical
  exact if hz : z ∈ (F.box b).image then
    D.label ((F.box b).chart.symm ⟨z,hz⟩).2 else 0

theorem projection_box (s : FoliationCoordinateDisk (s)) (w : FoliationCoordinateDisk 2) :
    D.projection ((F.box b).chart (s,w)).val = D.label w := by
  simp only [projection,dite_eq_left ((F.box b).chart (s,w)).property,
    Subtype.coe_eta,(F.box b).chart.symm_apply_apply]

theorem projection_coordinate (z : M) (hz : z ∈ (F.box b).image) :
    D.projection z = D.label ((F.box b).chart.symm ⟨z,hz⟩).2 := by
  simp only [projection,dite_eq_left hz]

theorem continuous_projection : ContinuousOn D.projection (F.box b).image := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h := D.open_label.continuous.comp (continuous_snd.comp (F.box b).chart.symm.continuous)
  convert h using 1
  funext z
  exact D.projection_coordinate z.val z.property

theorem projection_inverse (s : FoliationCoordinateDisk (s))
    (z : F.ULeaf (((F.box b).chart (s,w₀)).val))
    (hz : z ∈ (D.transport s).map.target) :
    D.projection z.val = D.coordinate ((D.transport s).map.symm z) := by
  obtain ⟨w,hw⟩ := (D.transport s).source_in_plaque
    ((D.transport s).map.symm z) ((D.transport s).map.map_target hz)
  have hmap := (D.transport s).coordinate_map ((D.transport s).map.symm z) w
    ((D.transport s).map.map_target hz) hw
  rw [(D.transport s).map.right_inv hz] at hmap
  rw [hmap]
  have ha : D.anchor w = (D.transport s).map.symm z := Subtype.ext (by
    rw [(D.transport_meta s).2.1,(D.transport_meta s).1] at hw
    exact hw)
  rw [(D.transport_meta s).2.2.1,(D.transport_meta s).1,D.projection_box]
  exact congrArg D.coordinate ha


/-- The scalar source domain is exactly the open image of the reference
unstable plaque in its complete affine coordinate. -/
theorem domain_eq_range_label :
    D.coordinate.target ∩ D.coordinate.symm ⁻¹' {z | ∃ w : FoliationCoordinateDisk 2,
      ((F.box b).chart (s₀,w)).val = z.val} = range D.label := by
  ext z
  constructor
  · rintro ⟨hz,w,hw⟩
    refine ⟨w,?_⟩
    have he : D.anchor w = D.coordinate.symm z := Subtype.ext hw
    change D.coordinate (D.anchor w) = z
    rw [he,D.coordinate.right_inv hz]
  · rintro ⟨w,rfl⟩
    have hw : D.anchor w ∈ D.coordinate.source := by rw [D.source_eq]; trivial
    refine ⟨D.coordinate.map_source hw,w,?_⟩
    change ((F.box b).chart (s₀,w)).val =
      (D.coordinate.symm (D.coordinate (D.anchor w))).val
    rw [D.coordinate.left_inv hw]
    rfl

/-- Transport along the constant stable plaque has zero scalar Schwarzian.
The actual transport is the identity on its source, by its product-coordinate
formula, and the complete affine coordinate cancels its own inverse. -/
theorem value_self (z : ℂ) (hz : z ∈ range D.label) : D.value (z,s₀) = 0 := by
  have hdom : z ∈ D.coordinate.target ∩ D.coordinate.symm ⁻¹'
      {p | ∃ w : FoliationCoordinateDisk 2, ((F.box b).chart (s₀,w)).val = p.val} :=
    D.domain_eq_range_label ▸ hz
  have hsame (p : F.ULeaf (((F.box b).chart (s₀,w₀)).val))
      (hp : p ∈ (D.transport s₀).map.source) : (D.transport s₀).map p = p := by
    obtain ⟨w,hw⟩ := (D.transport s₀).source_in_plaque p hp
    have he := (D.transport s₀).coordinate_map p w hp hw
    apply Subtype.ext
    rw [(D.transport_meta s₀).1,(D.transport_meta s₀).2.1] at hw
    rw [(D.transport_meta s₀).1,(D.transport_meta s₀).2.2.1] at he
    exact he.trans hw
  rw [D.represents (z,s₀) ⟨hdom,mem_univ _⟩ D.coordinate D.coordinate_mem
    (by rw [D.source_eq]; trivial)]
  have he : affineLocalMapExpression D.coordinate (D.transport s₀).map D.coordinate
      =ᶠ[𝓝 z] id := by
    have hsource : D.coordinate.symm z ∈ (D.transport s₀).map.source := by
      rw [(D.transport_meta s₀).2.2.2.2]
      exact hdom.2
    have hn := (D.coordinate.symm.continuousAt hdom.1).eventually
      ((D.transport s₀).map.open_source.mem_nhds hsource)
    filter_upwards [hn,D.coordinate.open_target.mem_nhds hdom.1] with t ht htc
    change D.coordinate ((D.transport s₀).map (D.coordinate.symm t)) = t
    rw [hsame _ ht,D.coordinate.right_inv htc]
  unfold schwarzian
  rw [he.deriv.eq_of_nhds,he.deriv.deriv.eq_of_nhds,he.deriv.deriv.deriv.eq_of_nhds]
  simp


end CompletePlaqueScalarFamily

end FamilyData


/-- The supplied complete affine family gives the packaged whole-box data. -/
theorem completePlaqueScalarFamily_nonempty
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
      A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves →
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        (A.structureAt q).Complete (IntrinsicFoliationLeaf P.foliations.unstablePartition q)) →
      ∀ (b : P.foliations.boxIndex) (s₀ : FoliationCoordinateDisk (2*d-2))
        (w₀ : FoliationCoordinateDisk 2),
        Nonempty (CompletePlaqueScalarFamily P.foliations
          (A.atPoint P.foliations P.complexLeaves) b s₀ w₀) := by
  let := P.realCharts
  let : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  intro A hAct hCont hComplete b s₀ w₀
  obtain ⟨c,h,S,hc,hcs,hct,hm,hS,hr,_⟩ := one_box_complete_affine_schwarzian_family
    f a hRank P A hAct hCont hComplete b s₀ w₀
  exact ⟨⟨c,h,S,hc,hcs,hct,hm,hS,hr⟩⟩

end HolomorphicAnosov.Ghys
