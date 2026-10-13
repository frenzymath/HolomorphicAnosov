import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Comp

open Set Filter
open scoped Topology _root_.Topology ContDiff
namespace HolomorphicAnosov

/-- On open domains the actual spatial derivatives through the supplied finite order obey the finite
Faà di Bruno formula. Source: Mathlib `HasFTaylorSeriesUpToOn.comp`.
Use the actual within-domain derivative series, compose it, and identify all
coefficients with ordinary derivatives using openness of both domains. -/
theorem iteratedFDeriv_comp_of_contDiffOn_finite
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} {t : Set F} (hs : IsOpen s) (ht : IsOpen t) (n : ℕ)
    {f : E → F} {g : F → G} (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g t)
    (hmap : MapsTo f s t) {x : E} (hx : x ∈ s) :
    iteratedFDeriv ℝ n (g ∘ f) x =
      (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) n := by
  have hc := (hg.ftaylorSeriesWithin ht.uniqueDiffOn).comp
    (hf.ftaylorSeriesWithin hs.uniqueDiffOn) hmap
  have heq := hc.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := n) (by simp)
    hs.uniqueDiffOn hx
  have hsjet : ftaylorSeriesWithin ℝ f s x = ftaylorSeries ℝ f x := by
    funext k
    exact iteratedFDerivWithin_of_isOpen _ hs hx
  have htjet : ftaylorSeriesWithin ℝ g t (f x) = ftaylorSeries ℝ g (f x) := by
    funext k
    exact iteratedFDerivWithin_of_isOpen _ ht (hmap hx)
  rw [iteratedFDerivWithin_of_isOpen _ hs hx, hsjet, htjet] at heq
  exact heq.symm

/-- Finite spatial jets remain jointly continuous after a fixed C^n outer map.
Source: Montgomery (1945), Corollary 1, pp.386–387, the finite composition step;
Mathlib's finite Faà di Bruno formula provides the explicit expansion. On the open
pair domain, every fixed parameter slice is C^n and its image lies in the fixed
outer smooth domain. Expand the nth composition derivative as a finite sum over
ordered partitions. Each summand is a continuous linear/multilinear evaluation of
a fixed outer derivative and inner jets of orders at most n. Their continuity at
the one specified pair suffices. No parameter derivative is used. -/
theorem continuousAt_spatial_jet_comp_finite
    {A E F G : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : A → E → F) (g : F → G) (Ω : Set (A × E)) (hΩ : IsOpen Ω)
    (U : Set F) (hU : IsOpen U) (n : ℕ)
    (hf : ∀ a, ContDiffOn ℝ n (f a) {y | (a, y) ∈ Ω})
    (hg : ContDiffOn ℝ n g U) (hmap : ∀ p ∈ Ω, f p.1 p.2 ∈ U)
    (p : A × E) (hp : p ∈ Ω)
    (hval : ContinuousAt (fun q : A × E ↦ f q.1 q.2) p)
    (hjets : ∀ m ≤ n, ContinuousAt
      (fun q : A × E ↦ iteratedFDeriv ℝ m (f q.1) q.2) p) :
    ContinuousAt (fun q : A × E ↦ iteratedFDeriv ℝ n (g ∘ f q.1) q.2) p := by
  have hformula : (fun q : A × E ↦ iteratedFDeriv ℝ n (g ∘ f q.1) q.2)
      =ᶠ[𝓝 p] (fun q ↦ (ftaylorSeries ℝ g (f q.1 q.2)).taylorComp
        (ftaylorSeries ℝ (f q.1) q.2) n) := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact iteratedFDeriv_comp_of_contDiffOn_finite
      (hΩ.preimage (continuous_const.prodMk continuous_id)) hU n
      (hf q.1) hg (fun y hy ↦ hmap (q.1, y) hy) hq
  apply ContinuousAt.congr_of_eventuallyEq _ hformula
  unfold FormalMultilinearSeries.taylorComp
  apply tendsto_finsetSum
  intro c _
  let B := c.compAlongOrderedFinpartitionL ℝ E F G
  change ContinuousAt
    ((fun q ↦ B q.1 q.2) ∘ (fun q : A × E ↦
      (iteratedFDeriv ℝ c.length g (f q.1 q.2),
        fun i ↦ iteratedFDeriv ℝ (c.partSize i) (f q.1) q.2))) p
  apply B.continuous_uncurry_of_multilinear.continuousAt.comp
  apply ContinuousAt.prodMk
  · have hgg := (hg _ (hmap p hp)).contDiffAt (hU.mem_nhds (hmap p hp))
    have houter : ContinuousAt (iteratedFDeriv ℝ c.length g) (f p.1 p.2) :=
      hgg.continuousAt_iteratedFDeriv (by exact_mod_cast c.length_le)
    exact houter.comp (f := fun q : A × E ↦ f q.1 q.2) hval
  · exact continuousAt_pi.mpr (fun i ↦ hjets _ (c.partSize_le i))
end HolomorphicAnosov

namespace HolomorphicAnosov
/-- On an open parameter/fibre domain, joint finite jets survive pairing.
Source: Mathlib's ordinary iterated derivative product identity and its
continuous multilinear product isometry. No parameter derivative is taken. -/
theorem continuousOn_parametric_jet_prodMk
    {A E F G : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : A → E → F) (g : A → E → G) (Ω : Set (A × E)) (hΩ : IsOpen Ω)
    (n : ℕ)
    (hf : ∀ a, ContDiffOn ℝ n (f a) {u | (a, u) ∈ Ω})
    (hg : ∀ a, ContDiffOn ℝ n (g a) {u | (a, u) ∈ Ω})
    (hfjet : ContinuousOn (fun z : A × E ↦ iteratedFDeriv ℝ n (f z.1) z.2) Ω)
    (hgjet : ContinuousOn (fun z : A × E ↦ iteratedFDeriv ℝ n (g z.1) z.2) Ω) :
    ContinuousOn (fun z : A × E ↦ iteratedFDeriv ℝ n
      (fun u ↦ (f z.1 u, g z.1 u)) z.2) Ω := by
  have hc := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n ↦ E) F G).continuous
    |>.comp_continuousOn (hfjet.prodMk hgjet)
  apply hc.congr
  intro z hz
  have hn : {u : E | (z.1, u) ∈ Ω} ∈ 𝓝 z.2 :=
    (hΩ.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz
  exact iteratedFDeriv_prodMk ((hf z.1).contDiffAt hn) ((hg z.1).contDiffAt hn) le_rfl

/-- Joint finite jets survive a fixed smooth outer composition, on an open
parameter/fibre domain. Source: the finite Faà di Bruno composition above.
The zero jet provides value continuity; openness upgrades each supplied
ContinuousOn certificate to continuity at each point of the domain. -/
theorem continuousOn_parametric_jet_comp_finite
    {A E F G : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : A → E → F) (g : F → G) (Ω : Set (A × E)) (hΩ : IsOpen Ω)
    (n : ℕ) (hf : ∀ a, ContDiffOn ℝ n (f a) {u | (a, u) ∈ Ω})
    (hg : ContDiff ℝ n g)
    (hjets : ∀ m ≤ n,
      ContinuousOn (fun z : A × E ↦ iteratedFDeriv ℝ m (f z.1) z.2) Ω) :
    ContinuousOn (fun z : A × E ↦ iteratedFDeriv ℝ n (g ∘ f z.1) z.2) Ω := by
  have hval : ContinuousOn (fun z : A × E ↦ f z.1 z.2) Ω := by
    have hc := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn
      (hjets 0 (Nat.zero_le n))
    convert hc using 1
    ext z
    simp
  intro p hp
  exact (continuousAt_spatial_jet_comp_finite f g Ω hΩ Set.univ isOpen_univ n hf
    hg.contDiffOn (fun _ _ ↦ mem_univ _) p hp
    (hval.continuousAt (hΩ.mem_nhds hp))
    (fun m hm ↦ (hjets m hm).continuousAt (hΩ.mem_nhds hp))).continuousWithinAt
end HolomorphicAnosov
