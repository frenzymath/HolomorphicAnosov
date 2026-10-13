import HolomorphicAnosov.Topology.OpenCoverPathSubdivision
import Mathlib.Topology.Compactness.Compact

open Set Filter _root_.Topology
namespace HolomorphicAnosov

/-- A finite subdivision of one path through open sets persists for every
nearby path in a continuous family, on one common open parameter neighborhood.
First subdivide the distinguished path. The compact tube lemma applied to
each closed subinterval gives a parameter neighborhood on which the entire
segment remains in its assigned open set. Intersect the finitely many such
neighborhoods. Source: Hatcher Lemma 1.15 p.35 and the compact tube lemma;
this is the common-source native-product subdivision in the RankOne proof. -/
theorem parametric_openCover_pathSubdivision_g18
    {P X ι : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (H : unitInterval × P → X) (hH : Continuous H) (p₀ : P)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ r : unitInterval, ∃ i, H (r,p₀) ∈ U i) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → unitInterval,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∃ assigned : Fin n → ι, ∃ N : Set P,
        IsOpen N ∧ p₀ ∈ N ∧ ∀ j : Fin n, ∀ p ∈ N,
          ∀ r ∈ Icc (t j.castSucc) (t j.succ), H (r,p) ∈ U (assigned j) := by
  classical
  let γ : Path (H (0,p₀)) (H (1,p₀)) :=
    ⟨⟨fun r ↦ H (r,p₀), hH.comp (continuous_id.prodMk continuous_const)⟩,rfl,rfl⟩
  obtain ⟨n,hn,t,ht0,ht1,ht,assigned,hassigned⟩ :=
    exists_openCover_pathSubdivision γ U hU hcover
  have hseg (j : Fin n) (r : unitInterval) (hr : r ∈ Icc (t j.castSucc) (t j.succ)) :
      H (r,p₀) ∈ U (assigned j) := by
    apply hassigned j
    rw [γ.range_subpath_of_le _ _ (ht (Fin.castSucc_le_succ j))]
    exact ⟨r,hr,rfl⟩
  have hnear (j : Fin n) : ∃ N : Set P, IsOpen N ∧ p₀ ∈ N ∧
      ∀ p ∈ N, ∀ r ∈ Icc (t j.castSucc) (t j.succ), H (r,p) ∈ U (assigned j) := by
    obtain ⟨V,N,_,hN,hV,hp,hVN⟩ := generalized_tube_lemma
      (isCompact_Icc : IsCompact (Icc (t j.castSucc) (t j.succ))) isCompact_singleton
      ((hU (assigned j)).preimage hH) (by
        rintro ⟨r,p⟩ ⟨hr,hp⟩
        rcases Set.mem_singleton_iff.mp hp with rfl
        exact hseg j r hr)
    exact ⟨N,hN,hp (mem_singleton p₀),fun p hp r hr ↦ hVN ⟨hV hr,hp⟩⟩
  choose N hNo hpN hN using hnear
  refine ⟨n,hn,t,ht0,ht1,ht,assigned,⋂ j, N j,isOpen_iInter_of_finite hNo,?_,?_⟩
  · exact mem_iInter.mpr hpN
  · intro j p hp r hr
    exact hN j p (mem_iInter.mp hp j) r hr

end HolomorphicAnosov
