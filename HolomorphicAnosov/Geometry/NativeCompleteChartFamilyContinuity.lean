import HolomorphicAnosov.Topology.LocalAffineFamilyContinuity
import HolomorphicAnosov.Geometry.DiffeomorphOfExhaustion
import HolomorphicAnosov.Geometry.NativeComplexStableLeafDatum
import HolomorphicAnosov.Geometry.NormalizedLocalCoordinateContinuousG5
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-! This file proves joint continuity of complete normalized complex line charts on native plaque
families. (Zhang, Lemma 2.7, p. 9) -/

open Set Filter Bundle TopologicalSpace
open scoped Topology Manifold ContDiff

noncomputable section
namespace HolomorphicAnosov

universe u

set_option maxHeartbeats 1000000 in
/-- Complete normalized complex line charts vary continuously on every native plaque family. -/
theorem native_complete_chart_family_continuous
    {d : ℕ} {X : Type u} [MetricSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (S : ContinuousComplexTangentSubbundle (complexModel d) X) (f : X ≃ₜ X)
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L) :
    letI : ∀ x : X, NormedAddCommGroup (TangentSpace (complexModel d) x) :=
      fun _ ↦ inferInstanceAs (NormedAddCommGroup (ComplexModel d))
    letI : ∀ x : X, NormedSpace ℂ (TangentSpace (complexModel d) x) :=
      fun _ ↦ inferInstanceAs (NormedSpace ℂ (ComplexModel d))
    letI : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
    letI : ∀ i, IsManifold (complexModel 1) ∞ (L i) :=
      fun i ↦ (F.complexUpgrade i).complex_manifold
    ∀ (φ : ∀ i (z : L i), Diffeomorph (complexModel 1)
        𝓘(ℂ, S.toDistribution ((F.partition.leaf i).inclusion z))
        (L i) (S.toDistribution ((F.partition.leaf i).inclusion z)) ∞)
      (_scalar : ∀ i (z : L i), S.toDistribution ((F.partition.leaf i).inclusion z) ≃L[ℂ] ℂ),
    (∀ x : X, ∃ (V : Opens X) (t : X → ℂ), x ∈ V ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V ∧
      (∀ y ∈ V, (localStableCoordinateDerivative S.toDistribution t y).IsInvertible) ∧
      (∀ i (z : L i), (F.partition.leaf i).inclusion z ∈ V →
        ∀ᶠ p in 𝓝 z, φ i z p = normalizedLocalStableCoordinate S.toDistribution t
          ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p))) →
    letI : ∀ b, TopologicalSpace (F.transversal b) := F.transversalTopology
    ∀ b : F.boxIndex,
      let B := F.boxes.boxes b
      Continuous (fun v : (B.disc × B.disc) × F.transversal b ↦
        let z : L (B.label v.2) := (B.chart v.2 v.1.1).val
        let p : L (B.label v.2) := (B.chart v.2 v.1.2).val
        (⟨(F.partition.leaf (B.label v.2)).inclusion z,
          (φ (B.label v.2) z p).val⟩ : TangentBundle (complexModel d) X)) := by
  let : ∀ x : X, NormedAddCommGroup (TangentSpace (complexModel d) x) :=
    fun _ ↦ inferInstanceAs (NormedAddCommGroup (ComplexModel d))
  let : ∀ x : X, NormedSpace ℂ (TangentSpace (complexModel d) x) :=
    fun _ ↦ inferInstanceAs (NormedSpace ℂ (ComplexModel d))
  let : ∀ i, ChartedSpace (ComplexModel 1) (L i) := fun i ↦ (F.complexUpgrade i).charts
  let : ∀ i, IsManifold (complexModel 1) ∞ (L i) :=
    fun i ↦ (F.complexUpgrade i).complex_manifold
  intro φ scalar hlocal
  let : ∀ b, TopologicalSpace (F.transversal b) := F.transversalTopology
  intro b
  let B := F.boxes.boxes b
  change Continuous (fun v : (B.disc × B.disc) × F.transversal b ↦
    (⟨(F.partition.leaf (B.label v.2)).inclusion (B.chart v.2 v.1.1).val,
      (φ (B.label v.2) (B.chart v.2 v.1.1).val (B.chart v.2 v.1.2).val).val⟩ :
        TangentBundle (complexModel d) X))
  clear_value B
  let base : B.disc × F.transversal b → X := fun p ↦
    (F.partition.leaf (B.label p.2)).inclusion (B.chart p.2 p.1).val
  have hbase : Continuous base := by
    apply (continuous_subtype_val.comp B.box.continuous).congr
    intro p
    exact B.factorization p.2 p.1
  let Φ : (B.disc × F.transversal b) × B.disc → TangentBundle (complexModel d) X :=
    fun r ↦ ⟨base r.1, (φ (B.label r.1.2) (B.chart r.1.2 r.1.1).val
      (B.chart r.1.2 r.2).val).val⟩
  set_option backward.isDefEq.respectTransparency false in
  have hdata (z₀ : B.disc) (τ₀ : F.transversal b) :
      ∃ (Q : Set B.disc) (N : Set (F.transversal b)) (V : Opens X) (t : X → ℂ),
        IsOpen Q ∧ z₀ ∈ Q ∧ IsPreconnected Q ∧ IsOpen N ∧ τ₀ ∈ N ∧
        ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V ∧
        (∀ x ∈ V, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible) ∧
        (∀ z ∈ Q, ∀ τ ∈ N, base (z, τ) ∈ V) ∧
        (∀ τ ∈ N, ∀ z ∈ Q, ∀ p ∈ Q,
          φ (B.label τ) (B.chart τ z).val (B.chart τ p).val =
            normalizedLocalStableCoordinate S.toDistribution t (base (z, τ)) (base (p, τ))) := by
    obtain ⟨V, t, hzV, ht, hdt, hgerm⟩ := hlocal (base (z₀, τ₀))
    have hpre : base ⁻¹' (V : Set X) ∈ 𝓝 (z₀, τ₀) :=
      hbase.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hzV)
    obtain ⟨Q₀, hQ₀, N₀, hN₀, hQN⟩ := mem_nhds_prod_iff.mp hpre
    let : LocallyConnectedSpace B.disc := ChartedSpace.locallyConnectedSpace (Fin 2 → ℝ) B.disc
    obtain ⟨Q, ⟨hQo, hzQ, hQc⟩, hQQ⟩ :=
      (LocallyConnectedSpace.open_connected_basis z₀).mem_iff.mp hQ₀
    obtain ⟨N, hNN, hNo, hτN⟩ := mem_nhds_iff.mp hN₀
    have hinside : ∀ z ∈ Q, ∀ τ ∈ N, base (z, τ) ∈ V :=
      fun z hz τ hτ ↦ hQN ⟨hQQ hz, hNN hτ⟩
    refine ⟨Q, N, V, t, hQo, hzQ, hQc.isPreconnected, hNo, hτN, ht, hdt, hinside, ?_⟩
    intro τ hτ z hz p hp
    let j : B.disc → L (B.label τ) := fun q ↦ (B.chart τ q).val
    have hj : Continuous j := (B.chart τ).continuous.subtype_val
    have hjo : IsOpenMap j :=
      (B.plaque τ).isOpen.isOpenEmbedding_subtypeVal.isOpenMap.comp (B.chart τ).toHomeomorph.isOpenMap
    let W := j '' Q
    have hzW : j z ∈ W := ⟨z, hz, rfl⟩
    have hWV : W ⊆ (F.partition.leaf (B.label τ)).inclusion ⁻¹' (V : Set X) := by
      rintro _ ⟨q, hq, rfl⟩
      exact hinside q hq τ hτ
    have heq : EqOn (φ (B.label τ) (j z))
        (fun q ↦ normalizedLocalStableCoordinate S.toDistribution t (base (z, τ))
          ((F.partition.leaf (B.label τ)).inclusion q)) W := by
      apply line_holomorphic_eqOn_of_germ
        ((scalar (B.label τ) (j z)).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm)
        _ _ (hjo _ hQo) (hQc.isPreconnected.image _ hj.continuousOn) hzW
        (φ (B.label τ) (j z)).contMDiff.contMDiffOn _ (hgerm _ _ (hinside z hz τ hτ))
      apply (localStableCoordinateDerivative S.toDistribution t (base (z, τ))).inverse.contDiff.contMDiff.comp_contMDiffOn
      exact (ht.comp (F.complexUpgrade (B.label τ)).inclusion_holomorphic.contMDiffOn hWV).sub_const _
    exact heq ⟨p, hp, rfl⟩
  have hlocalCont (Q : Set B.disc) (N : Set (F.transversal b)) (V : Opens X) (t : X → ℂ)
      (hQo : IsOpen Q) (hNo : IsOpen N)
      (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
      (hdt : ∀ x ∈ V, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible)
      (hinside : ∀ z ∈ Q, ∀ τ ∈ N, base (z, τ) ∈ V)
      (heq : ∀ τ ∈ N, ∀ z ∈ Q, ∀ p ∈ Q,
          φ (B.label τ) (B.chart τ z).val (B.chart τ p).val =
            normalizedLocalStableCoordinate S.toDistribution t (base (z, τ)) (base (p, τ))) :
      ContinuousOn Φ ((Q ×ˢ N) ×ˢ Q) := by
    have hnorm := normalized_local_coordinate_continuous (S := S) (t := t) (V := V) V.isOpen ht hdt
    have hc : Continuous (fun r : (B.disc × F.transversal b) × B.disc ↦
        (base r.1, base (r.2, r.1.2))) :=
      (hbase.comp continuous_fst).prodMk
        (hbase.comp (continuous_snd.prodMk continuous_fst.snd))
    apply (hnorm.comp hc.continuousOn (fun r hr ↦
      ⟨hinside _ hr.1.1 _ hr.1.2, hinside _ hr.2 _ hr.1.2⟩)).congr
    intro r hr
    exact congrArg (fun v : S.toDistribution (base r.1) ↦
      (⟨base r.1, v.val⟩ : TangentBundle (complexModel d) X))
        (heq _ hr.1.2 _ hr.1.1 _ hr.2)
  have hΦ : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨p₀, y₀⟩
    let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) (base p₀)
    have he₀ : base p₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    let Ψ : (B.disc × F.transversal b) × B.disc → ComplexModel d := fun r ↦ (e (Φ r)).2
    let : PreconnectedSpace B.disc := isPreconnected_iff_preconnectedSpace.mp B.disc_connected.isPreconnected
    have hΨ : ∀ y, ContinuousAt Ψ (p₀, y) := by
      apply continuousAt_of_locally_affine_family Ψ p₀
      · intro y
        obtain ⟨Q, N, V, t, hQo, hyQ, hQc, hNo, hτN, ht, hdt, hinside, heq⟩ := hdata y p₀.2
        let g : (B.disc × F.transversal b) × B.disc → ℂ := fun r ↦ t (base (r.2, r.1.2))
        have hg : ∀ z ∈ Q, ContinuousAt g (p₀, z) := by
          intro z hz
          exact (ht.continuousOn.continuousAt (V.isOpen.mem_nhds (hinside z hz _ hτN))).comp (f := fun r : (B.disc × F.transversal b) × B.disc ↦ base (r.2, r.1.2))
            ((hbase.comp (continuous_snd.prodMk continuous_fst.snd)).continuousAt)
        have hginj : InjOn (fun z : B.disc ↦ g (p₀, z)) Q := by
          intro z hz w hw hzw
          have hφeq : φ (B.label p₀.2) (B.chart p₀.2 y).val (B.chart p₀.2 z).val =
              φ (B.label p₀.2) (B.chart p₀.2 y).val (B.chart p₀.2 w).val := by
            apply (heq _ hτN _ hyQ _ hz).trans
            apply Eq.trans _ (heq _ hτN _ hyQ _ hw).symm
            exact congrArg (fun c : ℂ ↦ (localStableCoordinateDerivative S.toDistribution t
              (base (y, p₀.2))).inverse (c - t (base (y, p₀.2)))) hzw
          exact (B.chart p₀.2).injective (Subtype.ext
            ((φ (B.label p₀.2) (B.chart p₀.2 y).val).injective hφeq))
        refine ⟨Q, hQo, hyQ, g, hg, ?_, ?_⟩
        · intro R hRo hR
          obtain ⟨z, hz⟩ := hR
          have hO := B.disc.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (hRo.inter hQo)
          have hzO : (z : Fin 2 → ℝ) ∈ Subtype.val '' (R ∩ Q) := ⟨z, hz, rfl⟩
          have hn : ∀ᶠ w in 𝓝[≠] (z : Fin 2 → ℝ),
              w ∈ Subtype.val '' (R ∩ Q) ∧ w ≠ z := by
            filter_upwards [nhdsWithin_le_nhds (hO.mem_nhds hzO), self_mem_nhdsWithin] with w hw hwne
            exact ⟨hw, hwne⟩
          obtain ⟨w, ⟨q, hq, hqw⟩, hwne⟩ := hn.exists
          refine ⟨z, hz, q, hq, ?_⟩
          intro hgzq
          have hqz := (hginj hz.2 hq.2 hgzq).symm
          exact hwne (hqw ▸ congrArg Subtype.val hqz)
        · have hevent : ∀ᶠ p in 𝓝 p₀, p.2 ∈ N ∧ base p ∈ e.baseSet :=
            (continuous_snd.continuousAt.eventually (hNo.mem_nhds hτN)).and
              (hbase.continuousAt.eventually (e.open_baseSet.mem_nhds he₀))
          filter_upwards [hevent] with p hp
          obtain ⟨A, C, hAC⟩ := biholomorph_affine_in_scalar_coordinate
            (φ (B.label p.2) (B.chart p.2 p.1).val)
            (φ (B.label p.2) (B.chart p.2 y).val)
            (scalar (B.label p.2) (B.chart p.2 p.1).val)
            (scalar (B.label p.2) (B.chart p.2 y).val)
          let c : ℂ := scalar (B.label p.2) (B.chart p.2 y).val
            ((localStableCoordinateDerivative S.toDistribution t (base (y, p.2))).inverse 1)
          let A' := c • A
          let C' := C - t (base (y, p.2)) • A'
          let lin := e.continuousLinearMapAt ℂ (base p)
          refine ⟨lin A'.val, lin C'.val, ?_⟩
          intro z hz
          have hzformula : φ (B.label p.2) (B.chart p.2 p.1).val (B.chart p.2 z).val =
              t (base (z, p.2)) • A' + C' := by
            apply (hAC (B.chart p.2 z).val).trans
            apply Eq.trans (congrArg (fun v ↦ (scalar (B.label p.2) (B.chart p.2 y).val v) • A + C)
              (heq _ hp.1 _ hyQ _ hz))
            have hcoord : scalar (B.label p.2) (B.chart p.2 y).val
                (normalizedLocalStableCoordinate S.toDistribution t (base (y, p.2)) (base (z, p.2))) =
                (t (base (z, p.2)) - t (base (y, p.2))) * c := by
              simp only [normalizedLocalStableCoordinate, c]
              rw [← smul_eq_mul, ← map_smul, ← map_smul]
              simp only [smul_eq_mul, mul_one]
              rfl
            rw [hcoord]
            dsimp [A', C']
            module
          dsimp only [Ψ, Φ, g]
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hp.2]
          rw [hzformula]
          simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul]
          rfl
      · obtain ⟨Q, N, V, t, hQo, haQ, hQc, hNo, hτN, ht, hdt, hinside, heq⟩ := hdata p₀.1 p₀.2
        refine ⟨Q, hQo, ⟨p₀.1, haQ⟩, fun z hz ↦ ?_⟩
        have hzmem : (p₀, z) ∈ ((Q ×ˢ N) ×ˢ Q) := ⟨⟨haQ, hτN⟩, hz⟩
        have hΦz := (hlocalCont Q N V t hQo hNo ht hdt hinside heq).continuousAt
          ((hQo.prod hNo).prod hQo |>.mem_nhds hzmem)
        exact ((e.continuousAt (e.mem_source.mpr he₀)).comp hΦz).snd
    apply (FiberBundle.continuousAt_totalSpace (ComplexModel d) _).mpr
    exact ⟨(hbase.comp continuous_fst).continuousAt, hΨ y₀⟩
  exact hΦ.comp ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd)

end HolomorphicAnosov

