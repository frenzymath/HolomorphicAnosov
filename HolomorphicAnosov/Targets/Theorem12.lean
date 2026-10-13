import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Targets.Theorem12Support.SmoothSemiconjugacy.conjugatedDiffeomorph
import HolomorphicAnosov.Targets.Theorem12Support.SmoothSemiconjugacy.derivative_iterate_intertwining
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.coordinates
import HolomorphicAnosov.GhysTangentTransport.TransportedSubbundle
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.Recharted
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.identityDiffeomorph
import HolomorphicAnosov.Targets.Theorem12Support.InvariantDistributionTransport.rechart_distribution_invariant
import HolomorphicAnosov.Targets.Theorem12Support.InvariantDistributionTransport.rechart_distribution_isCompl
import HolomorphicAnosov.Targets.Theorem12Support.InvariantDistributionTransport.rechart_iterate_vector_bound
import HolomorphicAnosov.Targets.Theorem12Support.LiftedToralAssembly
import HolomorphicAnosov.Geometry.OriginalNativeLiftedHolomorphicFoliations
import HolomorphicAnosov.Geometry.SmoothMetricPullback
import HolomorphicAnosov.Topology.EuclideanOpenDimensionInvariance
import HolomorphicAnosov.Topology.FranksManning
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacy
import HolomorphicAnosov.Paper.Zhang.TranslationActionHolomorphic
import HolomorphicAnosov.Paper.Zhang.FreeTransitiveVectorOrbitDiffeomorphism
import HolomorphicAnosov.Paper.Zhang.TranslationInvariantComplexTorusDescent

/-!
A holomorphic Anosov diffeomorphism on a compact connected complex manifold homeomorphic to a real torus, with holomorphic stable and unstable distributions, is biholomorphically conjugate to a linear complex torus automorphism. (Zhang, Theorem 1.2, p.3, §3, pp.11–13)
-/

section G10ModelImplementation
universe u v w x liftedUniverse










end G10ModelImplementation

open scoped ContDiff Manifold Topology _root_.Topology
open Set
namespace HolomorphicAnosov.Theorem12SupportW2
noncomputable section
universe u

variable {d n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]
  (B : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin n))

end
end HolomorphicAnosov.Theorem12SupportW2









namespace HolomorphicAnosov

open scoped ContDiff Manifold Bundle _root_.HolomorphicAnosov.Topology _root_.Topology
open Filter Set

universe u

attribute [local instance] complex_isManifold_real

/-- A holomorphic Anosov diffeomorphism on a compact connected complex manifold homeomorphic to a
real torus, whose stable and unstable distributions are holomorphic tangent subbundles, is
biholomorphically conjugate to a lattice-preserving complex-linear torus automorphism. (Zhang,
Theorem 1.2, p.3, pp.11–13) -/
theorem theorem_1_2 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hStable : ∃ (r : ℕ) (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)),
      IsHolomorphicTangentSubbundle r P ∧ ∀ x : X,
        ((P x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap =
            a.splitting.stable.toDistribution x)
    (hUnstable : ∃ (r : ℕ) (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)),
      IsHolomorphicTangentSubbundle r P ∧ ∀ x : X,
        ((P x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap =
            a.splitting.unstable.toDistribution x)
    (hT : ∃ n : ℕ, Nonempty (X ≃ₜ UnitAddTorus (Fin n))) :
    ∃ (L : FullComplexLattice d) (A : LatticeLinearEquiv L)
      (h : Biholomorph d d X (ComplexTorus L)),
      Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
        (fun t ↦ quotientLinearEquiv A t) := by
  classical
  by_cases hd : d = 0
  · subst d
    let : DiscreteTopology X := ChartedSpace.discreteTopology (ComplexModel 0) X
    let : Subsingleton X := subsingleton_of_preconnected_totallyDisconnected
    let L : FullComplexLattice 0 :=
      { lattice := ⊥
        discrete := inferInstance
        full := ⟨Subsingleton.elim _ _⟩ }
    let A : LatticeLinearEquiv L :=
      { linear := LinearEquiv.refl ℂ (ComplexModel 0)
        map_lattice := by
          change AddSubgroup.map (AddMonoidHom.id _) _ = _
          exact AddSubgroup.map_id _ }
    let : Subsingleton (ComplexTorus L) := by
      change Subsingleton (ComplexModel 0 ⧸ L.lattice.toAddSubgroup)
      have ht : L.lattice.toAddSubgroup = ⊤ := Subsingleton.elim _ _
      rw [ht]
      exact QuotientAddGroup.subsingleton_quotient_top
    let := complexTorusChartedSpace L
    let h : Biholomorph 0 0 X (ComplexTorus L) :=
      { toEquiv :=
          { toFun := fun _ ↦ 0
            invFun := fun _ ↦ Classical.choice (inferInstance : Nonempty X)
            left_inv := fun _ ↦ Subsingleton.elim _ _
            right_inv := fun _ ↦ Subsingleton.elim _ _ }
        contMDiff_toFun := contMDiff_of_subsingleton
        contMDiff_invFun := contMDiff_of_subsingleton }
    exact ⟨L, A, h, fun _ ↦ Subsingleton.elim _ _⟩
  · have hTdim : Nonempty (X ≃ₜ UnitAddTorus (Fin (2 * d))) := by
      obtain ⟨n, ⟨q⟩⟩ := hT
      have hn : n = 2 * d := by
        classical
        let circleChart := AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0
        let torusChart : OpenPartialHomeomorph (UnitAddTorus (Fin n)) (Fin n → ℝ) :=
          (OpenPartialHomeomorph.pi (fun _ : Fin n ↦ circleChart)).symm
        let v : Fin n → ℝ := fun _ ↦ 1 / 2
        have hv : v ∈ (OpenPartialHomeomorph.pi (fun _ : Fin n ↦ circleChart)).source := by
          intro i hi
          change (0 : ℝ) < 1 / 2 ∧ 1 / 2 < 0 + 1
          norm_num
        let y := (OpenPartialHomeomorph.pi (fun _ : Fin n ↦ circleChart)) v
        have hy : y ∈ torusChart.source :=
          (OpenPartialHomeomorph.pi (fun _ : Fin n ↦ circleChart)).map_source hv
        let x := q.symm y
        let b := chartAt (ComplexModel d) x
        have hx : x ∈ b.source := mem_chart_source (ComplexModel d) x
        have hrank : Module.finrank ℝ (ComplexModel d) = 2 * d := by
          simp [ComplexModel, Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]
        let realComplex : ComplexModel d ≃ₜ EuclideanSpace ℝ (Fin (2 * d)) :=
          (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (by simpa using hrank)).toHomeomorph
        let realTorus : (Fin n → ℝ) ≃ₜ EuclideanSpace ℝ (Fin n) :=
          (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (by simp)).toHomeomorph
        let e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (2 * d)))
            (EuclideanSpace ℝ (Fin n)) :=
          (realComplex.symm.transOpenPartialHomeomorph
            (b.symm.trans (q.transOpenPartialHomeomorph torusChart))).transHomeomorph realTorus
        have he : realComplex (b x) ∈ e.source := by
          change realComplex.symm (realComplex (b x)) ∈
            (b.symm.trans (q.transOpenPartialHomeomorph torusChart)).source
          rw [realComplex.symm_apply_apply, OpenPartialHomeomorph.trans_source]
          refine ⟨b.map_source hx, ?_⟩
          change q (b.symm (b x)) ∈ torusChart.source
          rw [b.left_inv hx]
          simpa [x] using hy
        exact (euclidean_open_dimension_invariance e.source e.target e.open_source e.open_target
          ⟨_, he⟩ ⟨_, e.map_source he⟩ e.toHomeomorphSourceTarget).symm
      subst n
      exact ⟨q⟩
    obtain ⟨r, S, hS, hSreal⟩ := hStable
    obtain ⟨s, U, hU, hUreal⟩ := hUnstable
    
    let originalReal : Diffeomorph (realModel d) (realModel d) X X ∞ := f.toReal
    have hComplexSplit (x : X) : IsCompl (S x) (U x) := by
      apply (Submodule.isCompl_restrictScalars_iff ℝ).mp
      apply (Submodule.orderIsoMapComap (complexTangentToReal d x).toLinearEquiv).isCompl_iff.mpr
      change IsCompl (((S x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap)
        (((U x).restrictScalars ℝ).map (complexTangentToReal d x).toLinearEquiv.toLinearMap)
      rw [hSreal x, hUreal x]
      exact a.splitting.isCompl x
    
    have hRankS (x : X) : Module.finrank ℂ (S x) = r := by
      obtain ⟨O, frame, hx, hframe, hspan⟩ := hS x
      rw [← hspan x hx]
      simpa using finrank_span_eq_card (hframe.2.2 x hx)
    have hRankU (x : X) : Module.finrank ℂ (U x) = s := by
      obtain ⟨O, frame, hx, hframe, hspan⟩ := hU x
      rw [← hspan x hx]
      simpa using finrank_span_eq_card (hframe.2.2 x hx)
    have hFoliationDimensions : d = r + s := by
      let x0 : X := Classical.choice (inferInstance : Nonempty X)
      have hsum := Submodule.finrank_add_eq_of_isCompl (hComplexSplit x0)
      rw [hRankS x0, hRankU x0] at hsum
      have htangent : Module.finrank ℂ (TangentSpace (complexModel d) x0) = d := by
        change Module.finrank ℂ (ComplexModel d) = d
        simp [ComplexModel]
      exact (hsum.trans htangent).symm
    
    let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    obtain ⟨C, lam, hC, hlam, hlam1, hStableAll, hUnstableAll⟩ :=
      fixed_block_uniform_anosov_estimates f a
    
    let B := Theorem12SupportW2.coordinates d
    let : TopologicalSpace (Theorem12SupportW2.Recharted X) := inferInstanceAs (TopologicalSpace X)
    let : ChartedSpace (EuclideanSpace ℝ (Fin (2 * d))) (Theorem12SupportW2.Recharted X) :=
      Theorem12SupportW2.copiedCharts (X := X) B
    let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) ∞ (Theorem12SupportW2.Recharted X) :=
      Theorem12SupportW2.copied_isManifold (X := X) B
    let e : Diffeomorph (realModel d) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) X (Theorem12SupportW2.Recharted X) ∞ :=
      Theorem12SupportW2.identityDiffeomorph B
    let g := Theorem12SupportW2.conjugatedDiffeomorph e originalReal
    let Sr := GhysTangentTransport.transportedSubbundle e a.splitting.stable
    let Ur := GhysTangentTransport.transportedSubbundle e a.splitting.unstable
    have hRechartForward : Function.Semiconj e originalReal g :=
      e.toEquiv.semiconj_conj originalReal
    have hRechartInverse : Function.Semiconj e originalReal.symm g.symm :=
      hRechartForward.inverses_right originalReal.apply_symm_apply g.symm_apply_apply
    have hRechartStable (y : (Theorem12SupportW2.Recharted X)) :
        (Sr.toDistribution y).map
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d)))
            𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) g y).toLinearMap =
          Sr.toDistribution (g y) :=
      Theorem12SupportW4.rechart_distribution_invariant e originalReal g
        a.splitting.stable.toDistribution a.splitting.stable_map hRechartForward
        (Theorem12SupportW2.derivative_intertwining e originalReal.contMDiff
          g.contMDiff hRechartForward) y
    have hRechartUnstable (y : (Theorem12SupportW2.Recharted X)) :
        (Ur.toDistribution y).map
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d)))
            𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) g y).toLinearMap =
          Ur.toDistribution (g y) :=
      Theorem12SupportW4.rechart_distribution_invariant e originalReal g
        a.splitting.unstable.toDistribution a.splitting.unstable_map hRechartForward
        (Theorem12SupportW2.derivative_intertwining e originalReal.contMDiff
          g.contMDiff hRechartForward) y
    have hRechartComplement (y : (Theorem12SupportW2.Recharted X)) : IsCompl (Sr.toDistribution y) (Ur.toDistribution y) :=
      Theorem12SupportW4.rechart_distribution_isCompl e
        a.splitting.stable.toDistribution a.splitting.unstable.toDistribution
        a.splitting.isCompl y
    let : CompactSpace (Theorem12SupportW2.Recharted X) := inferInstanceAs (CompactSpace X)
    let : ConnectedSpace (Theorem12SupportW2.Recharted X) := inferInstanceAs (ConnectedSpace X)
    let : T2Space (Theorem12SupportW2.Recharted X) := inferInstanceAs (T2Space X)
    let : SecondCountableTopology (Theorem12SupportW2.Recharted X) := inferInstanceAs (SecondCountableTopology X)
    have hTorusRecharted : Nonempty ((Theorem12SupportW2.Recharted X) ≃ₜ UnitAddTorus (Fin (2 * d))) := by
      obtain ⟨q⟩ := hTdim
      exact ⟨e.toHomeomorph.symm.trans q⟩
    
    
    have hFranksApplication
        (metricR : Bundle.ContMDiffRiemannianMetric
          𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) ∞ (EuclideanSpace ℝ (Fin (2 * d)))
          (fun y : (Theorem12SupportW2.Recharted X) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) y)) :
        letI : Bundle.RiemannianBundle
            (fun y : (Theorem12SupportW2.Recharted X) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) y) :=
          ⟨metricR.toRiemannianMetric⟩
        (∀ x (v : TangentSpace (realModel d) x),
          ‖mfderiv (realModel d) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) e x v‖ = ‖v‖) →
        HyperbolicRealToralConjugacy (2 * d) (Theorem12SupportW2.Recharted X) g := by
      let : Bundle.RiemannianBundle
          (fun y : (Theorem12SupportW2.Recharted X) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) y) :=
        ⟨metricR.toRiemannianMetric⟩
      intro hnorm
      apply franks_manning g Sr Ur metricR C lam hTorusRecharted hC hlam hlam1
        hRechartComplement hRechartStable hRechartUnstable
      · intro y n v hv
        obtain ⟨x, rfl⟩ := e.surjective y
        change v ∈ (a.splitting.stable.toDistribution (e.symm (e x))).map
          (GhysTangentTransport.tangentEquiv e (e.symm (e x))).toLinearEquiv.toLinearMap at hv
        rw [e.symm_apply_apply] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        exact Theorem12SupportW4.rechart_iterate_vector_bound e originalReal g
          a.splitting.stable.toDistribution hRechartForward hnorm n (C * lam ^ n)
          (Theorem12SupportW2.derivative_iterate_intertwining e originalReal.contMDiff
            g.contMDiff hRechartForward n) (hStableAll n) x w hw
      · intro y n v hv
        obtain ⟨x, rfl⟩ := e.surjective y
        change v ∈ (a.splitting.unstable.toDistribution (e.symm (e x))).map
          (GhysTangentTransport.tangentEquiv e (e.symm (e x))).toLinearEquiv.toLinearMap at hv
        rw [e.symm_apply_apply] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        exact Theorem12SupportW4.rechart_iterate_vector_bound e originalReal.symm g.symm
          a.splitting.unstable.toDistribution hRechartInverse hnorm n (C * lam ^ n)
          (Theorem12SupportW2.derivative_iterate_intertwining e originalReal.symm.contMDiff
            g.symm.contMDiff hRechartInverse n) (hUnstableAll n) x w hw
    let metricR := smoothMetricPullback e a.metric
    have hRealToralModel : HyperbolicRealToralConjugacy (2 * d) (Theorem12SupportW2.Recharted X) g :=
      hFranksApplication metricR (smoothMetricPullback_norm_forward e a.metric)
    
    
    
    have hOriginalRealToralModel : HyperbolicRealToralConjugacy (2 * d) X f := by
      obtain ⟨A, h, hHyper, hConj⟩ := hRealToralModel
      refine ⟨A, e.toHomeomorph.trans h, hHyper, ?_⟩
      intro x
      change h (e (f x)) = integralToralMap A (h (e x))
      change h (e (originalReal x)) = integralToralMap A (h (e x))
      rw [hRechartForward x]
      exact hConj (e x)
    rcases Theorem12LiftedAssembly.lifted_real_toral_model f hOriginalRealToralModel with
      ⟨hDiscrete, hLattice, hSpan, hDim, hCompactQuotient, A, h, hLatticeInvariant,
        hHyperbolic, hModelConjugacy⟩
    let V := Theorem12LiftedCarrier.Carrier.{u} (2 * d)
    let Γ := (IntegerCoordinateLattice.integerLattice (2 * d)).map
      ((Theorem12LiftedCarrier.liftEquiv.{u} (2 * d)).toLinearMap.restrictScalars ℤ)
    let : FiniteDimensional ℝ V := Theorem12LiftedCarrier.carrier_finiteDimensional (2 * d)
    let : DiscreteTopology Γ := hDiscrete
    let : IsZLattice ℝ Γ := hLattice
    let : CompactSpace (V ⧸ Γ.toAddSubgroup) := hCompactQuotient
    
    rcases covering_conjugacy (X := X) (V := V)
      f a hDim Γ A hHyperbolic hLatticeInvariant h hModelConjugacy with
      ⟨bounds, hBoundsC, m, hm, coverData⟩
    let : MetricSpace X := m.replaceTopology hm
    rcases coverData with
      ⟨native, hQuotientCover, hQuotientSurjective, hSimplyConnected, hDeck,
        hDecaySplitting, hChosen, hEveryCover⟩
    rcases hChosen with ⟨p, hp, hpSurjective, atlasV, liftData⟩
    let : ChartedSpace (ComplexModel d) V := atlasV
    rcases liftData with
      ⟨hManifoldV, hAtlasV, hProjection, hSheets, H, F, delta,
        hProjectionSquare, hLift, hInverseLift, hLinearization, hDeltaCoordinates,
        hDeltaFibres, hAllDeck, hLiftDeck, hLeafImages⟩
    let : IsManifold (complexModel d) ∞ V := hManifoldV
    let : SimplyConnectedSpace V := hSimplyConnected
    rcases hDecaySplitting with ⟨Vs, Vu, hVs, hVu, hComplement⟩
    have hStableDecay (v : V) : v ∈ Vs ↔
        Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0) := by
      change v ∈ (Vs : Set V) ↔ _
      rw [hVs]
      change Tendsto (fun n : ℕ ↦ ((A : V → V)^[n]) v) atTop (𝓝 0) ↔ _
      have heq : (fun n : ℕ ↦ ((A : V → V)^[n]) v) =
          (fun n : ℕ ↦ (A ^ n) v) := by
        funext n
        change ((A.toLinearEquiv : V → V)^[n]) v = (A ^ n).toLinearEquiv v
        rw [ContinuousLinearEquiv.toLinearEquiv_pow, LinearEquiv.pow_apply]
      rw [heq]
    have hUnstableDecay (v : V) : v ∈ Vu ↔
        Tendsto (fun n : ℕ ↦ (A.symm ^ n) v) atTop (𝓝 0) := by
      change v ∈ (Vu : Set V) ↔ _
      rw [hVu]
      change Tendsto (fun n : ℕ ↦ ((A.symm : V → V)^[n]) v) atTop (𝓝 0) ↔ _
      have heq : (fun n : ℕ ↦ ((A.symm : V → V)^[n]) v) =
          (fun n : ℕ ↦ (A.symm ^ n) v) := by
        funext n
        change ((A.symm.toLinearEquiv : V → V)^[n]) v = (A.symm ^ n).toLinearEquiv v
        rw [ContinuousLinearEquiv.toLinearEquiv_pow, LinearEquiv.pow_apply]
      rw [heq]
    have hFibre (y z : V) : p y = p z ↔ H z - H y ∈ Γ := by
      constructor
      · intro heq
        have hq : (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) =
            QuotientAddGroup.mk (H z) :=
          (hProjectionSquare y).trans ((congrArg h heq).trans (hProjectionSquare z).symm)
        simpa only [sub_eq_add_neg, add_comm, Submodule.mem_toAddSubgroup] using
          (QuotientAddGroup.eq.mp hq)
      · intro hmem
        apply h.injective
        rw [← hProjectionSquare y, ← hProjectionSquare z]
        apply QuotientAddGroup.eq.mpr
        simpa only [sub_eq_add_neg, add_comm, Submodule.mem_toAddSubgroup] using hmem
    
    
    have hFinish
        (Ws : RegularHolomorphicFoliation.{u, u} d r s V)
        (Wu : RegularHolomorphicFoliation.{u, u} d s r V)
        (hWsTangent : ∀ y, (Ws.tangent y).map
          (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = S (p y))
        (hWuTangent : ∀ y, (Wu.tangent y).map
          (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = U (p y))
        (hWsRange : ∀ y, H '' (Set.range (fun z : Ws.Leaf y ↦ z.val)) =
          {v : V | ∃ w : Vs, v = H y + (w : V)})
        (hWuRange : ∀ y, H '' (Set.range (fun z : Wu.Leaf y ↦ z.val)) =
          {v : V | ∃ w : Vu, v = H y + (w : V)}) :
        ∃ (L : FullComplexLattice d) (B : LatticeLinearEquiv L)
          (h : Biholomorph d d X (ComplexTorus L)),
          Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
            (fun z ↦ quotientLinearEquiv B z) := by
      have hTranslation := translation_action_holomorphic f a S U hS hU hSreal hUreal hT
        p hp hpSurjective hSheets Γ hSpan A hLatticeInvariant hHyperbolic
        F.toHomeomorph hLift H hLinearization (fun gamma ↦ (delta gamma).toHomeomorph)
        hDeltaFibres (fun gamma y ↦ by
          change H (delta gamma y) = (gamma : V) + H y
          rw [hDeltaCoordinates]; exact add_comm _ _)
        Vs Vu hComplement hStableDecay hUnstableDecay Ws Wu
        hWsTangent hWuTangent hWsRange hWuRange
      
      let T : V → Biholomorph d d V V := fun v ↦ (hTranslation v).choose
      have hT (v y : V) : T v y = H.symm (v + H y) := (hTranslation v).choose_spec y
      have hContinuous : Continuous (fun z : V × V ↦ T z.1 z.2) := by
        have heq : (fun z : V × V ↦ T z.1 z.2) =
            (fun z : V × V ↦ H.symm (z.1 + H z.2)) := by
          funext z
          exact hT z.1 z.2
        rw [heq]
        exact H.symm.continuous.comp (continuous_fst.add (H.continuous.comp continuous_snd))
      have hZero (y : V) : T 0 y = y := by simp [hT]
      have hAdd (v w y : V) : T (v + w) y = T v (T w y) := by simp [hT, add_assoc]
      have hFree (v y : V) (hv : T v y = y) : v = 0 := by
        have hh := congrArg H hv
        simpa [hT] using hh
      have hTransitive (y z : V) : ∃ v : V, T v y = z := by
        refine ⟨H z - H y, ?_⟩
        simp [hT]
      have hDimOrbit : Module.finrank ℝ V = Module.finrank ℝ (ComplexModel d) := by
        rw [hDim]
        simp [ComplexModel, Module.finrank_pi_fintype, Complex.finrank_real_complex,
          Nat.mul_comm]
      obtain ⟨Theta, hTheta⟩ := free_transitive_vector_orbit_diffeomorphism V d V
        hDimOrbit T hContinuous hZero hAdd hFree hTransitive (H.symm 0)
      have hOrbit (v : V) : Theta v = H.symm v := by simpa [hT] using hTheta v
      
      let Hd := Theta.symm
      have hSame (y : V) : Hd y = H y := by
        apply Theta.injective
        change Theta (Theta.symm y) = Theta (H y)
        rw [Theta.apply_symm_apply, hOrbit, H.symm_apply_apply]
      have hLinear' (y : V) : Hd (F y) = A (Hd y) := by
        simpa only [hSame] using hLinearization y
      have hFibre' (y z : V) : p y = p z ↔ Hd z - Hd y ∈ Γ := by
        simpa only [hSame] using hFibre y z
      have hTranslation' : ∀ v : V, ∃ tau : Biholomorph d d V V,
          ∀ y : V, tau y = Hd.symm (Hd y + v) := by
        intro v
        obtain ⟨tau, htau⟩ := hTranslation v
        refine ⟨tau, ?_⟩
        intro y
        rw [htau]
        change H.symm (v + H y) = Theta (Hd y + v)
        rw [hOrbit, hSame, add_comm]
      have hLatticeMap : Γ.toAddSubgroup.map A.toLinearEquiv.toAddEquiv.toAddMonoidHom =
          Γ.toAddSubgroup := by
        apply SetLike.coe_injective
        rw [AddSubgroup.coe_map]
        exact hLatticeInvariant
      obtain ⟨L, B, hFinal, hAtlasFinal, hHyperbolicFinal, hSemiconjugacy⟩ :=
        translation_invariant_complex_torus_descent d hDim p hp hpSurjective hSheets
          f F hLift Γ hSpan A.toLinearEquiv hLatticeMap hHyperbolic
          Hd hLinear' hFibre' hTranslation'
      exact ⟨L, B, hFinal, hSemiconjugacy⟩
    
    
    

    suffices hFoliations :
        ∃ (Ws : RegularHolomorphicFoliation.{u, u} d r s V)
          (Wu : RegularHolomorphicFoliation.{u, u} d s r V),
          (∀ y, (Ws.tangent y).map
            (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = S (p y)) ∧
          (∀ y, (Wu.tangent y).map
            (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = U (p y)) ∧
          (∀ y, H '' (Set.range (fun z : Ws.Leaf y ↦ z.val)) =
            {v : V | ∃ w : Vs, v = H y + (w : V)}) ∧
          (∀ y, H '' (Set.range (fun z : Wu.Leaf y ↦ z.val)) =
            {v : V | ∃ w : Vu, v = H y + (w : V)}) by
      rcases hFoliations with ⟨Ws, Wu, hWsTangent, hWuTangent, hWsRange, hWuRange⟩
      exact hFinish Ws Wu hWsTangent hWuTangent hWsRange hWuRange
    exact Theorem12LiftedFoliationAssembly.bool_native_lifted_foliations
      f a S U hS hU hFoliationDimensions hComplexSplit hSreal hUreal
      native p hp hSheets H _ Vs Vu hVs hVu
      (fun σ y b hb ↦ (hLeafImages σ y b hb).1)


end HolomorphicAnosov
