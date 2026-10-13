import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveFrameSectionG7
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveSectionLocalBiholomorphG7

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

/-- The ordered projective product atlas has a locally biholomorphic development with equivariant
deck holonomy on a simply connected holomorphic cover. (Thurston, §3.5 pp.34–35 and §4.8 p.63;
Ghys, §5 pp.597–598) -/
theorem ordered_projective_product_development_frame_continuation
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hsimply : SimplyConnectedSpace U)
    (hhol : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ p) :
    Nonempty (OrderedProjectiveProductDevelopment A p) ∧ True := by
  obtain ⟨Z, hbase, hindex, hchange, hcover⟩ := ordered_projective_frame_cover A
  obtain ⟨s, hsproj⟩ := ordered_projective_frame_section A Z hcover p hp hsimply
  have hlocal := ordered_projective_section_local_formula A Z hbase hindex hchange
    p hp.continuous s hsproj
  have hlocalB := ordered_projective_section_local_biholomorph A Z hbase hindex hchange
    p hhol s hsproj
  let : SimplyConnectedSpace U := hsimply
  let u₀ : U := Classical.choice (inferInstance : Nonempty U)
  let label : U → OrderedProjectiveFrameGroup := fun u ↦ (s u).2
  let ratio : deck p → U → OrderedProjectiveFrameGroup :=
    fun γ u ↦ label (γ • u) * (label u)⁻¹
  have hbaseγ (γ : deck p) (u : U) : (s (γ • u)).1 = (s u).1 := by
    rw [hsproj, hsproj]
    exact deck.proj_smul γ u
  have hratioform (γ : deck p) (i : A.index) (u : U) :
      ratio γ u = (Z.localTriv i (s (γ • u))).2 *
        ((Z.localTriv i (s u)).2)⁻¹ := by
    rw [Z.localTriv_apply, Z.localTriv_apply, hchange]
    change label (γ • u) * (label u)⁻¹ =
      (label (γ • u) * (A.transition (Z.indexAt (s (γ • u)).1) i (s (γ • u)).1)⁻¹) *
        (label u * (A.transition (Z.indexAt (s u).1) i (s u).1)⁻¹)⁻¹
    rw [hbaseγ γ u]
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
  have hratio (γ : deck p) : IsLocallyConstant (ratio γ) := by
    apply (IsLocallyConstant.iff_continuous _).2
    apply continuous_iff_continuousAt.mpr
    intro u
    let i := Z.indexAt (p u)
    have hsu : s u ∈ (Z.localTriv i).source := by
      rw [(Z.localTriv i).mem_source, ← Z.baseSet_at]
      simpa only [hsproj] using Z.mem_baseSet_at (p u)
    have hsgu : s (γ • u) ∈ (Z.localTriv i).source := by
      rw [(Z.localTriv i).mem_source, ← Z.baseSet_at]
      simpa only [hsproj, deck.proj_smul] using Z.mem_baseSet_at (p u)
    have hc₁ : ContinuousAt (fun y ↦ (Z.localTriv i (s (γ • y))).2) u :=
      (((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hsgu).snd).comp (f := fun y ↦ s (γ • y)) (x := u)
        (s.continuous.comp (continuous_const_smul γ)).continuousAt
    have hc₂ : ContinuousAt (fun y ↦ (Z.localTriv i (s y)).2) u :=
      (((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hsu).snd).comp
        s.continuous.continuousAt
    exact (hc₁.mul hc₂.inv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (hratioform γ i))
  have hconstant (γ : deck p) (u : U) : ratio γ u = ratio γ u₀ :=
    (hratio γ).apply_eq_of_preconnectedSpace u u₀
  let ρ : deck p →* OrderedProjectiveFrameGroup := {
    toFun := fun γ ↦ ratio γ u₀
    map_one' := by simp [ratio]
    map_mul' := by
      intro γ δ
      change ratio (γ * δ) u₀ = ratio γ u₀ * ratio δ u₀
      rw [← hconstant γ (δ • u₀)]
      simp [ratio, mul_smul, mul_assoc]
  }
  let ev : Z.TotalSpace → ComplexProjectiveLine × ComplexProjectiveLine :=
    fun z ↦ (z.2.1 • (A.chart (Z.indexAt z.1) z.1).1,
      z.2.2 • (A.chart (Z.indexAt z.1) z.1).2)
  refine ⟨⟨{
    covering := hp
    surjective := hsurj
    simplyConnected := hsimply
    cover_holomorphic := hhol
    developingMap := fun u ↦ ev (s u)
    localBiholomorph := hlocalB
    holonomy := ρ
    equivariant := ?_
    locally_chart := ?_
  }⟩, trivial⟩
  · intro γ u
    have hlabel : label (γ • u) = ρ γ * label u := by
      change label (γ • u) = ratio γ u₀ * label u
      rw [← hconstant γ u]
      simp [ratio, mul_assoc]
    have hleft := congrArg Prod.fst hlabel
    have hright := congrArg Prod.snd hlabel
    dsimp only [ev]
    rw [hbaseγ γ u]
    apply Prod.ext
    · change (s (γ • u)).2.1 • _ = _
      change (s (γ • u)).2.1 = (ρ γ).1 * (s u).2.1 at hleft
      rw [hleft, mul_smul]
    · change (s (γ • u)).2.2 • _ = _
      change (s (γ • u)).2.2 = (ρ γ).2 * (s u).2.2 at hright
      rw [hright, mul_smul]
  · intro u
    obtain ⟨i, g, N, hN, hu, hpN, hform⟩ := hlocal u
    exact ⟨i, N, g, hN, hu, hpN, hform⟩

end HolomorphicAnosov.Ghys
