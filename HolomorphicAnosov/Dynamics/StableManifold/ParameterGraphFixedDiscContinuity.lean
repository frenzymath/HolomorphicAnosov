import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity

/-!
# Fixed-disc continuity of fibre jets

Munkres, *Topology*, second edition (2000), Theorem 26.7 Step 1 and
Lemma 26.8, pp.167–168, supply the compact tube argument. Applied to the
finite fibre jets in Hirsch–Pugh–Shub, *Invariant Manifolds* (1977),
pp.61–62, it gives uniform parameter continuity on each fixed model disc.
Only the input model disc is compact; the parameter base is arbitrary.
-/

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov

/-- The compact model-disc step in HPS parameter dependence (pp.61–62), as expanded
in the parameter construction using Munkres, *Topology*, Theorem 26.7 and Lemma 26.8,
pp.167–168. On the open overlap of source and receiving charts, each actual fibre jet
is jointly continuous. Subtract its continuous value at the fixed parameter. The norm
of this difference vanishes along the compact model disc at that parameter. The compact
tube lemma gives a parameter neighborhood on which every difference is smaller than the
prescribed positive tolerance. No compactness or separation hypothesis on the base is used. -/
theorem parameter_graph_fixed_disc_continuity
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (r : ℕ) (g : ∀ p, E p → F (b p))
    (hg : JointFiberContDiff e f b r g) : FixedDiscCrContinuous e f b r g := by
  intro i j p hp R hR m hm ε hε
  let U := (e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet
  have hU : IsOpen U := (e.chart i).open_baseSet.inter
    ((f.chart j).open_baseSet.preimage hb)
  let J := fun z : A × FiniteFiberModel (e.rank i) ↦
    FibreJet m (fibreChartExpression e f b g i j z.1) z.2
  have hJ : ContinuousOn J (U ×ˢ univ) := hg.2 i j m hm
  have hJat (x : FiniteFiberModel (e.rank i)) : ContinuousAt J (p, x) :=
    hJ.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ x⟩)
  have hsmall : ∀ᶠ q in 𝓝 p,
      ∀ x ∈ Metric.closedBall (0 : FiniteFiberModel (e.rank i)) R,
        ‖J (q, x) - J (p, x)‖ < ε := by
    apply IsCompact.eventually_forall_of_forall_eventually
      (isCompact_closedBall (0 : FiniteFiberModel (e.rank i)) R)
    intro x hx
    have hmap : Continuous (fun z : A × FiniteFiberModel (e.rank i) ↦ (p, z.2)) :=
      continuous_const.prodMk continuous_snd
    have hreference : ContinuousAt (fun z : A × FiniteFiberModel (e.rank i) ↦
        J (p, z.2)) (p, x) := (hJat x).comp (f := fun z : A × FiniteFiberModel (e.rank i) ↦ (p, z.2))
      (x := (p, x)) hmap.continuousAt
    exact ((hJat x).sub hreference).norm.eventually_lt_const (by simpa using hε)
  filter_upwards [hU.mem_nhds hp, hsmall] with q hq hqsmall
  exact ⟨hq, hqsmall⟩

end HolomorphicAnosov
