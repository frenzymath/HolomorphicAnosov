import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Fin.Basic
/-! The compact spectral part of Franks–Manning periodic density.
Manning (1974), Lemmas 3–4 and 6, pp.427–428; Step 19 of the retained Franks
source proof. All spectral and periodic-fibre inputs remain explicit here. -/
namespace HolomorphicAnosov.FranksOriginalLift
open Set Function
open scoped _root_.Topology
/-- A periodic-point bijection and a finite spectral decomposition force full
periodic density when every target-periodic point lifts periodically inside
any spectral component mapping onto the target. The compact image of the
closure of source periodic points contains the dense target periodic locus.
Choose a source preimage of a dense target orbit in one spectral component;
that entire target orbit lies in its compact image, hence that component maps
onto the target. Periodic-fibre existence and injectivity on all source periodic
points then put every source periodic point in that one component. Closedness
puts their whole closure there. Any second nonempty disjoint component is
impossible, so the supplied spectral properness implication forces the closure
to be the entire source. No source injectivity away from periodic points or
source periodic-density hypothesis is used. -/
theorem spectral_periodic_density {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → X) (g : Y → Y) (h : C(X,Y)) (hsem : Function.Semiconj h f g)
    (hponto : Set.SurjOn h (Function.periodicPts f) (Function.periodicPts g))
    (hpinj : Set.InjOn h (Function.periodicPts f))
    (hpdense : Dense (Function.periodicPts g))
    (y : Y) (hy : DenseRange (fun n : ℕ ↦ g^[n] y))
    {b : ℕ} (L : Fin b → Set X)
    (hL : ∀ i, (L i).Nonempty ∧ IsCompact (L i) ∧ MapsTo f (L i) (L i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (L i) (L j)))
    (hclos : closure (Function.periodicPts f) = ⋃ i, L i)
    (hproper : closure (Function.periodicPts f) ≠ Set.univ → 2 ≤ b)
    (hfibre : ∀ i, h '' L i = Set.univ → ∀ z ∈ Function.periodicPts g,
      ∃ x ∈ L i, x ∈ Function.periodicPts f ∧ h x = z) :
    Dense (Function.periodicPts f) := by
  have hclosed : IsClosed (h '' closure (Function.periodicPts f)) :=
    (isClosed_closure.isCompact.image h.continuous).isClosed
  have honto : h '' closure (Function.periodicPts f) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hpdense.closure_eq]
    apply closure_minimal _ hclosed
    intro z hz
    obtain ⟨x,hx,hxz⟩ := hponto hz
    exact ⟨x,subset_closure hx,hxz⟩
  obtain ⟨x,hx,hxy⟩ := show y ∈ h '' closure (Function.periodicPts f) by rw [honto]; trivial
  rw [hclos] at hx
  obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
  have hionto : h '' L i = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hy.closure_range]
    apply closure_minimal _ ((hL i).2.1.image h.continuous).isClosed
    rintro z ⟨n,rfl⟩
    refine ⟨f^[n] x, (hL i).2.2.iterate n hxi, ?_⟩
    rw [hsem.iterate_right n, hxy]
  have hper : Function.periodicPts f ⊆ L i := by
    intro z hz
    obtain ⟨w,hwi,hw,hwh⟩ := hfibre i hionto (h z) (hsem.mapsTo_periodicPts hz)
    have hwz : w = z := hpinj hw hz hwh
    simpa only [hwz] using hwi
  have hsub : closure (Function.periodicPts f) ⊆ L i :=
    closure_minimal hper (hL i).2.1.isClosed
  apply dense_iff_closure_eq.mpr
  by_contra hn
  have hb := hproper hn
  let : Nontrivial (Fin b) := Fin.nontrivial_iff_two_le.mpr hb
  obtain ⟨j,hji⟩ := exists_ne i
  obtain ⟨z,hz⟩ := (hL j).1
  have hzi : z ∈ L i := hsub (by rw [hclos]; exact mem_iUnion.mpr ⟨j,hz⟩)
  exact Set.disjoint_left.mp (hdisj hji) hz hzi

end HolomorphicAnosov.FranksOriginalLift
