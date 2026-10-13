import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity

noncomputable section
open Set Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- Joint fibre regularity on an open part of the original total space. The
spatial derivatives are the actual unrestricted fibre derivatives at interior
points. Their local chart expressions are jointly continuous on precisely the
source/receiving overlap inside that part. This is the local-disc regularity
used in HPS pp.32–36 and the parameter insertion p.62. -/
def JointFiberContDiffOn
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (r : ℕ) (U : Set (Sigma E)) (g : ∀p,E p→F (b p)) : Prop :=
  (∀z∈U,ContDiffAt ℝ (r:ℕ∞ω) (g z.1) z.2) ∧
  ∀i j m,m≤r → ContinuousOn
    (fun z : A × FiniteFiberModel (e.rank i) ↦
      FibreJet m (fibreChartExpression e f b g i j z.1) z.2)
    {z | z.1∈(e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet ∧
      (e.chart i).toOpenPartialHomeomorph.symm z∈U}

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    {e : FiniteRankNormedAtlas (E := E)} {f : FiniteRankNormedAtlas (E := F)}
    {b : A → B} {r n : ℕ} {U V : Set (Sigma E)} {g : ∀p,E p→F (b p)}

/-- Restricting the spatial domain preserves every existing local fibre jet. -/
theorem JointFiberContDiffOn.mono (hg : JointFiberContDiffOn e f b r U g)
    (hVU : V⊆U) : JointFiberContDiffOn e f b r V g := by
  refine ⟨fun z hz ↦ hg.1 z (hVU hz),fun i j m hm ↦ ?_⟩
  exact (hg.2 i j m hm).mono (fun z hz ↦ ⟨hz.1,hVU hz.2⟩)

/-- Forgetting higher derivatives preserves local joint regularity. -/
theorem JointFiberContDiffOn.of_le (hg : JointFiberContDiffOn e f b r U g)
    (hn : n≤r) : JointFiberContDiffOn e f b n U g := by
  refine ⟨fun z hz ↦ (hg.1 z hz).of_le (by exact_mod_cast hn),fun i j m hm ↦ ?_⟩
  exact hg.2 i j m (hm.trans hn)

/-- On the full total space the local definition is exactly the global one. -/
theorem jointFiberContDiffOn_univ_iff :
    JointFiberContDiffOn e f b r Set.univ g ↔ JointFiberContDiff e f b r g := by
  constructor
  · intro hg
    refine ⟨fun p ↦ ?_,fun i j m hm ↦ ?_⟩
    · exact contDiff_iff_contDiffAt.mpr (fun x ↦ hg.1 ⟨p,x⟩ (mem_univ _))
    · exact (hg.2 i j m hm).mono (fun z hz ↦ ⟨hz.1,mem_univ _⟩)
  · intro hg
    refine ⟨fun z _ ↦ (hg.1 z.1).contDiffAt,fun i j m hm ↦ ?_⟩
    exact (hg.2 i j m hm).mono (fun z hz ↦ ⟨hz.1,mem_univ _⟩)

/-- Local regularity patches across original open total-space neighborhoods.
For each chart jet, a tested point lies in one regular neighborhood. The
original inverse chart is continuous there; its preimage and the valid overlap
form a neighborhood on which the local chart jet is continuous. Thus the jet
is continuous at the tested point. Fibre smoothness is already pointwise. -/
theorem JointFiberContDiffOn.of_locally (hb : Continuous b)
    (hg : ∀z∈U,∃V : Set (Sigma E),IsOpen V ∧ z∈V ∧
      JointFiberContDiffOn e f b r V g) : JointFiberContDiffOn e f b r U g := by
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨V,_,hzV,hV⟩ := hg z hz
    exact hV.1 z hzV
  · intro i j m hm z hz
    obtain ⟨V,hVo,hzV,hV⟩ := hg _ hz.2
    have hi : ContinuousAt (e.chart i).toOpenPartialHomeomorph.symm z :=
      (e.chart i).toOpenPartialHomeomorph.continuousAt_symm
        ((e.chart i).mem_target.mpr hz.1.1)
    have hnear : {w : A × FiniteFiberModel (e.rank i) |
        w.1∈(e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet ∧
        (e.chart i).toOpenPartialHomeomorph.symm w∈V} ∈ nhds z := by
      have ho : IsOpen ((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) :=
        (e.chart i).open_baseSet.inter ((f.chart j).open_baseSet.preimage hb)
      exact Filter.inter_mem
        (continuous_fst.continuousAt.preimage_mem_nhds (ho.mem_nhds hz.1))
        (hi.preimage_mem_nhds (hVo.mem_nhds hzV))
    exact ((hV.2 i j m hm).continuousAt hnear).continuousWithinAt

end HolomorphicAnosov
