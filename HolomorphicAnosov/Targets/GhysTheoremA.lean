import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingStageInduction
import HolomorphicAnosov.Paper.Ghys.SurfaceDomainDichotomy
import HolomorphicAnosov.Paper.Ghys.SurfaceGraphDomainExcluded
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveProduct
import HolomorphicAnosov.Paper.Ghys.SurfaceTorusBiholomorphicLift
import HolomorphicAnosov.Paper.Ghys.SurfaceTorusQuotient
import HolomorphicAnosov.Paper.Ghys.TorusAffineLinearization
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.TorusModel

import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover
import HolomorphicAnosov.Topology.ClosedManifoldFiniteSimplicialRetractPi1FG
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Instances.Discrete
import Mathlib.GroupTheory.Finiteness
import Mathlib.SetTheory.Cardinal.Free
import HolomorphicAnosov.Geometry.SmoothMetricPullback
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.GhysTangentTransport
import HolomorphicAnosov.GhysAnosovConjugacy


/-! The classification of holomorphic Anosov diffeomorphisms of compact complex surfaces by complex
torus automorphisms. (Ghys, Thm A, p. 585; Lemma 5.2, pp. 599–600) -/

open scoped ContDiff Manifold
open Set



universe u

namespace HolomorphicAnosov



/-- A holomorphic Anosov diffeomorphism of a compact connected complex surface is biholomorphically
conjugate to a hyperbolic complex-linear torus automorphism. (Ghys, Thm A, p. 585) -/
theorem ghys_theorem_A {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
    [IsCompactComplexManifold 2 X]
    (f : Biholomorph 2 2 X X) (a : AnosovDatum f) :
    HasHyperbolicComplexTorusModel (d := 2) (fun x ↦ f x) := by
  
  
  have affine_finish : ∀ (L : FullComplexLattice 2)
      (hM : IsManifold (complexModel 2) ∞ (ComplexTorus L)),
      letI := hM
      ∀ (h : Biholomorph 2 2 X (ComplexTorus L)),
        IsCoveringMap (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) →
        IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞
          (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) →
        Nonempty (AnosovDatum ((h.symm.trans f).trans h)) →
        HasHyperbolicComplexTorusModel (d := 2) (fun x ↦ f x) := by
    intro L hM h hq hqHol hg
    let g := (h.symm.trans f).trans h
    obtain ⟨F, B, b, hFq, hF, hB, _⟩ :=
      surface_torus_biholomorphic_lift 2 (by norm_num) L hq hqHol g
    let A : LatticeLinearEquiv L := ⟨B, hB⟩
    have hga : ∀ t : ComplexTorus L, g t = quotientAffineEquiv A b t := by
      intro t
      induction t using Quotient.inductionOn with
      | h z =>
        rw [← hFq z, hF z]
        simp [quotientAffineEquiv, quotientLinearEquiv, A,
          QuotientAddGroup.mk_add]
        rfl
    obtain ⟨hhyper, c, τ, _, hτ⟩ := torusAffineLinearization L A b
      ⟨hM, g, hga, hg⟩
    refine ⟨L, A, h.trans τ, hhyper, ?_⟩
    intro x
    change τ (h (f x)) = quotientLinearEquiv A (τ (h x))
    have heq : g (h x) = h (f x) := by
      simp [g, Diffeomorph.coe_trans]
    rw [← heq, hga]
    exact hτ (h x)
  obtain ⟨A, hdevelopment⟩ := Ghys.surface_projective_product f a
  have quotient_stage : ∀ (U : Type u) [TopologicalSpace U]
      [ChartedSpace (ComplexModel 2) U] [IsManifold (complexModel 2) ∞ U]
      (π : U → X), IsCoveringMap π → Function.Surjective π →
      SimplyConnectedSpace U →
      IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ π →
      ∃ (L : FullComplexLattice 2)
        (hM : IsManifold (complexModel 2) ∞ (ComplexTorus L))
        (h : Biholomorph 2 2 X (ComplexTorus L)),
        IsCoveringMap (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) ∧
        IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞
          (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) := by
    intro U _ _ _ π hcover hsurj hsimply hlocal
    obtain ⟨dev, _⟩ := hdevelopment U π hcover hsurj hsimply hlocal
    obtain ⟨ps, pu, ms, mu, D0, τ, L, h, hdata⟩ :=
      surface_torus_quotient f a A π dev
    rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, hM, _, _, hq, _, hqHol, _⟩
    exact ⟨L, hM, h, hq, hqHol⟩
  
  
  
  have holomorphic_cover_stage : ∀ (U : Type u) [TopologicalSpace U]
      [T2Space U] [SecondCountableTopology U] (π : U → X),
      IsCoveringMap π → Function.Surjective π → SimplyConnectedSpace U →
      ∃ (L : FullComplexLattice 2)
        (hM : IsManifold (complexModel 2) ∞ (ComplexTorus L))
        (h : Biholomorph 2 2 X (ComplexTorus L)),
        IsCoveringMap (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) ∧
        IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞
          (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) := by
    intro U _ _ _ π hcover hsurj hsimply
    obtain ⟨c, hc⟩ := complex_cover_pullback_atlas (d := 2) π hcover hsurj
    let : ChartedSpace (ComplexModel 2) U := c
    have hM : IsManifold (complexModel 2) ∞ U := hc.1
    have hlocal : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ π := by
      intro y
      obtain ⟨e, hy, he, heSmooth, heInvSmooth⟩ := hc.2.2.2.1 y
      exact ⟨{
        toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := heSmooth
        contMDiffOn_invFun := heInvSmooth }, hy, he.symm⟩
    exact quotient_stage U π hcover hsurj hsimply hlocal
  
  
  have hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x) := by
    intro x
    let e := chartAt (ComplexModel 2) x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x)
      (mem_chart_target (ComplexModel 2) x)
    let B := Metric.ball (e x) r
    have hB : ContractibleSpace B := (convex_ball (e x) r).contractibleSpace
      ⟨e x, Metric.mem_ball_self hr⟩
    let H : B ≃ₜ (e.symm '' B) :=
      e.symm.homeomorphOfImageSubsetSource hball rfl
    have hU : IsSimplyConnected (e.symm '' B) :=
      H.symm.toHomotopyEquiv.simplyConnectedSpace
    refine ⟨e.symm '' B, e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hball,
      ⟨e x, Metric.mem_ball_self hr, e.left_inv (mem_chart_source _ x)⟩, ?_⟩
    intro p hp
    obtain ⟨F, _⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hU).2 x p hp
    exact ⟨F⟩
  have : LocallyPathConnectedSpace X :=
    ChartedSpace.locallyPathConnectedSpace (ComplexModel 2) X
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  let b : X := Classical.choice inferInstance
  let U := Σ x : X, Path.Homotopic.Quotient b x
  let good : Set X → Prop := fun V ↦ IsOpen V ∧ IsPathConnected V ∧
    ∀ x : X, x ∈ V → ∀ p : Path x x,
      (∀ t, p t ∈ V) → p.Homotopic (Path.refl x)
  let sheet : Set X → U → Set U := fun V z ↦
    {e | ∃ η : Path z.1 e.1, (∀ t, η t ∈ V) ∧
      z.2.trans (Path.Homotopic.Quotient.mk η) = e.2}
  let : TopologicalSpace U := TopologicalSpace.generateFrom
    {S | ∃ (V : Set X) (z : U), good V ∧ z.1 ∈ V ∧ S = sheet V z}
  let π : U → X := fun z ↦ z.1
  obtain ⟨hπsurj, hπcover, hUlpc, hUsimply, hpoint, action, haction, hfree, htrans⟩ :=
    pointed_path_class_universal_cover b hsemi
  have : T2Space U := by
    constructor
    intro z z' hne
    by_cases he : π z = π z'
    · exact hπcover.isSeparatedMap z z' he hne
    · obtain ⟨V, V', hV, hV', hz, hz', hdisj⟩ := t2_separation he
      refine ⟨π ⁻¹' V, π ⁻¹' V', hV.preimage hπcover.continuous,
        hV'.preimage hπcover.continuous, hz, hz', ?_⟩
      exact hdisj.preimage π
  have countable_cover_stage : Countable (FundamentalGroup X b) →
      SecondCountableTopology U := by
    intro hcount
    have : Countable (FundamentalGroup X b)ᵐᵒᵖ :=
      Countable.of_equiv _ MulOpposite.opEquiv
    have hfib : ∀ x : X, Countable (π ⁻¹' {x}) := by
      intro x
      obtain ⟨z, hz⟩ := hπsurj x
      let lift : (FundamentalGroup X b)ᵐᵒᵖ → π ⁻¹' {x} :=
        fun γ ↦ ⟨(action γ : U ≃ₜ U) z, by
          change π ((action γ : U ≃ₜ U) z) = x
          rw [haction]
          exact hz⟩
      apply Function.Surjective.countable (f := lift)
      intro z'
      obtain ⟨γ, hγ⟩ := (htrans z z').mp (hz.trans z'.2.symm)
      refine ⟨γ, Subtype.ext ?_⟩
      change (action γ : U ≃ₜ U) z = z'
      rw [haction, ← hγ]
    choose V hx hV hπV H hH using fun x : X ↦ (hπcover x).2
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
    have : ∀ x : s, SecondCountableTopology (π ⁻¹' V x) := by
      intro x
      have : Countable (π ⁻¹' {x.val}) := hfib x
      have : DiscreteTopology (π ⁻¹' {x.val}) := (hπcover x).1
      exact (H x).secondCountableTopology
    apply TopologicalSpace.secondCountableTopology_of_countable_cover
      (U := fun x : s ↦ π ⁻¹' V x) (fun x ↦ hπV x)
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨x, hxs, hxz⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (π z)))
    exact Set.mem_iUnion.mpr ⟨⟨x, hxs⟩, hxz⟩
  have finitely_generated_cover_stage : Group.FG (FundamentalGroup X b) →
      SecondCountableTopology U := by
    intro hfg
    obtain ⟨S, hS, φ, hφ⟩ :=
      Group.fg_iff_exists_freeGroup_hom_surjective.mp hfg
    have : Finite S := hS
    have : Countable (FundamentalGroup X b) := hφ.countable
    exact countable_cover_stage inferInstance
  have real_finite_generation_stage :
      ∀ c : ChartedSpace (EuclideanSpace ℝ (Fin 4)) X,
        letI := c
        IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ X →
          Group.FG (FundamentalGroup X b) := by
    intro c hM
    obtain ⟨N, P, _, _, cw, hfinite, j, q, hretract, hfg⟩ :=
      closed_manifold_finite_simplicial_retract_pi1_fg 4 X
    exact hfg b
  let B : ComplexModel 2 ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simp [ComplexModel, finrank_real_of_complex, Module.finrank_pi_fintype,
        finrank_euclideanSpace])
  let c : ChartedSpace (EuclideanSpace ℝ (Fin 4)) X :=
    { atlas := (fun e : OpenPartialHomeomorph X (ComplexModel 2) ↦
        e.transHomeomorph B.toHomeomorph) '' atlas (ComplexModel 2) X
      chartAt x := (chartAt (ComplexModel 2) x).transHomeomorph B.toHomeomorph
      mem_chart_source x := ChartedSpace.mem_chart_source x
      chart_mem_atlas x := Set.mem_image_of_mem _ (ChartedSpace.chart_mem_atlas x) }
  have hc : letI := c
      IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞ X := by
    let := c
    apply isManifold_of_contDiffOn
    intro e e' he he'
    rcases he with ⟨c₀, hc₀, rfl⟩
    rcases he' with ⟨c₁, hc₁, rfl⟩
    have : IsManifold (realModel 2) ∞ X := complex_isManifold_real 2 X
    have ht := (mem_groupoid_of_pregroupoid.mp
      ((contDiffGroupoid ∞ (realModel 2)).compatible hc₀ hc₁)).1
    have h0 : ContDiffOn ℝ ∞ (c₀.symm ≫ₕ c₁) (c₀.symm ≫ₕ c₁).source := by
      simpa only [contDiffPregroupoid, mfld_simps] using ht
    have hcomp := B.contDiff.comp_contDiffOn
      (h0.comp B.symm.contDiff.contDiffOn (s := B.symm ⁻¹' (c₀.symm ≫ₕ c₁).source)
        (by intro z hz; exact hz))
    simp only [mfld_simps]
    convert hcomp using 1
    · rfl
    · ext z
      rfl
  have : SecondCountableTopology U :=
    finitely_generated_cover_stage (real_finite_generation_stage c hc)
  obtain ⟨L, hM, h, hq, hqHol⟩ := holomorphic_cover_stage U π hπcover hπsurj hUsimply
  let := hM
  have : IsManifold (realModel 2) ∞ X := complex_isManifold_real 2 X
  have : IsManifold (realModel 2) ∞ (ComplexTorus L) := complex_isManifold_real 2 (ComplexTorus L)
  let s := GhysTangentTransport.transportedSubbundle h.toReal a.splitting.stable
  let t := GhysTangentTransport.transportedSubbundle h.toReal a.splitting.unstable
  have hg : Nonempty (AnosovDatum ((h.symm.trans f).trans h)) :=
    ⟨GhysAnosovConjugacy.transportedAnosovDatum h f a s t (fun y ↦ rfl) (fun y ↦ rfl)⟩
  exact affine_finish L hM h hq hqHol hg


end HolomorphicAnosov
