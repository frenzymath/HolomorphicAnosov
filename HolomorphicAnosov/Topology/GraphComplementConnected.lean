import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Complements of finitely many graphs in `OnePoint ℂ × OnePoint ℂ`

Source: Ghys, *Holomorphic Anosov systems* (1995), Lemma 5.2, p. 599.
DAG node: `topo.graph_complement_connected`.
-/

namespace HolomorphicAnosov

open Set

private theorem finite_onePoint_compl_connected (H : Set (OnePoint ℂ)) (hH : H.Finite) :
    IsConnected Hᶜ := by
  let A : Set ℂ := ((↑) : ℂ → OnePoint ℂ) ⁻¹' H
  have hA : A.Finite := hH.preimage OnePoint.coe_injective.injOn
  have hr : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  have hc : IsConnected Aᶜ := hA.countable.isConnected_compl_of_one_lt_rank hr
  have hi := hc.image ((↑) : ℂ → OnePoint ℂ) OnePoint.continuous_coe.continuousOn
  have hd : Dense (((↑) : ℂ → OnePoint ℂ) '' Aᶜ) :=
    OnePoint.denseRange_coe.dense_image OnePoint.continuous_coe (hA.countable.dense_compl ℝ)
  exact hi.subset_closure (by rintro _ ⟨z, hz, rfl⟩; exact hz) (fun _ _ ↦ hd _)

/-- Removing at most two points and finitely many continuous graphs from the one-point
compactification of the complex plane leaves a nonempty path-connected set.

Source: Ghys, *Holomorphic Anosov systems* (1995), Lemma 5.2, p. 599, asserts
intersection connectedness and then chooses a path. This docstring gives the
current DAG's generic Mathlib-composite proof of that omitted topological step;
it does not attribute the full argument to the printed Ghys proof.

Natural-language proof: Write `P = OnePoint ℂ` and `B = P \ F`. First, for any finite
set `H ⊆ P`, the complement `P \ H` is path connected. Pull `H` back along the
open embedding `ℂ → P`; this is a finite set of points in `ℂ`, whose complement is
path connected because the real rank of `ℂ` is two. The same complement is open,
and the one-point compactification adds infinity to its closure: for a neighborhood
of infinity, its compact complement is norm bounded, so a sufficiently large real
point avoids both that compact set and the finite punctures. The continuous image
of this plane complement is therefore connected and dense in `P \ H`, which gives
the claimed connectedness and nonemptiness; the sphere atlas for `P` upgrades the
open connected complements used below to path connectedness. More precisely,
the real finrank of `ℂ` is two, giving a global homeomorphism between `P` and
the unit sphere in `EuclideanSpace ℝ (Fin 3)`. That sphere has its genuine
stereographic charted-space atlas with model `EuclideanSpace ℝ (Fin 2)`. The
model is locally convex, hence locally path connected; the charted-space theorem
transfers this to the sphere, and the global homeomorphism transfers it to `P`.
The product theorem gives local path connectedness of `P × P`.

Now form the subset `X` of `B × P` consisting of pairs `(x,y)` with
`y ≠ u i x` for every `i`. Each equality locus is closed, so `X` is open. The
projection `π : X → B` is open and continuous, and every fibre over `x` is
homeomorphic to `P \ {u i x | i}`; hence every fibre is nonempty and connected.
The open projection with connected fibres is a quotient map, so the whole `X`
is connected because `B` is connected. Finally the inclusion `X → P × P` is an
open continuous map whose image is exactly the displayed graph complement. Thus
that image is open and connected. Since `P × P` is locally path connected, every
open connected subset is path connected. The argument includes `m = 0`, `F = ∅`,
and repeated graph values; when there are one or two removed finite points, the
same fibre argument applies without modification.

No smoothness, holomorphicity, or extension of the maps across `F` is assumed.
-/
theorem graph_complement_nonempty_isPathConnected
    (F : Set (OnePoint ℂ)) (hF : F.Finite) (_hFcard : F.ncard ≤ 2)
    (m : ℕ) (u : Fin m → ({x : OnePoint ℂ // x ∉ F} → OnePoint ℂ))
    (hu : ∀ i : Fin m, Continuous (u i)) :
    IsPathConnected
      {p : OnePoint ℂ × OnePoint ℂ |
        ∃ hx : p.1 ∉ F, ∀ i : Fin m, p.2 ≠ u i ⟨p.1, hx⟩} := by
  classical
  let P := OnePoint ℂ
  let B := {x : P // x ∉ F}
  have hB : IsOpen {x : P | x ∉ F} := hF.isClosed.isOpen_compl
  let C : Set (B × P) := {z | ∀ i, z.2 ≠ u i z.1}
  have hC : IsOpen C := by
    have he : ∀ i : Fin m, IsClosed {z : B × P | z.2 = u i z.1} :=
      fun i ↦ isClosed_eq continuous_snd ((hu i).comp continuous_fst)
    convert (isClosed_iUnion_of_finite he).isOpen_compl using 1
    ext z
    simp [C]
  let X := {z : B × P // z ∈ C}
  let π : X → B := fun z ↦ z.1.1
  have hπc : Continuous π := continuous_fst.comp continuous_subtype_val
  have hπo : IsOpenMap π := isOpenMap_fst.comp hC.isOpenMap_subtype_val
  have hfib : ∀ x : B, IsConnected (π ⁻¹' {x}) := by
    intro x
    let H : Set P := Set.range (fun i : Fin m ↦ u i x)
    have hH : H.Finite := Set.finite_range _
    have hconn := finite_onePoint_compl_connected H hH
    let k : ↥(Hᶜ) → X := fun y ↦ ⟨(x, y.1), by
      intro i hi
      exact y.2 ⟨i, hi.symm⟩⟩
    have hk : Continuous k := by
      exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _
    have hkimage : k '' Set.univ = π ⁻¹' {x} := by
      ext z
      constructor
      · rintro ⟨y, _, rfl⟩
        rfl
      · intro hz
        have hx : z.1.1 = x := hz
        refine ⟨⟨z.1.2, ?_⟩, Set.mem_univ _, ?_⟩
        · rintro ⟨i, hi⟩
          exact z.2 i (by rw [hx]; exact hi.symm)
        · apply Subtype.ext
          exact Prod.ext hx.symm rfl
    let : ConnectedSpace ↥(Hᶜ) := Subtype.connectedSpace hconn
    rw [← hkimage]
    exact isConnected_univ.image k hk.continuousOn
  have hπs : Function.Surjective π := by
    intro x
    obtain ⟨z, hz⟩ := (hfib x).nonempty
    exact ⟨z, hz⟩
  let : ConnectedSpace B := Subtype.connectedSpace (finite_onePoint_compl_connected F hF)
  have hX : IsConnected (Set.univ : Set X) := by
    have hq := hπo.isQuotientMap hπc hπs
    simpa only [preimage_univ] using
      Topology.IsCoinducing.isConnected_preimage_of_isClosed hfib hq.isCoinducing
        isClosed_univ isConnected_univ
  let j : B × P → P × P := Prod.map Subtype.val id
  have hjc : Continuous j := continuous_subtype_val.prodMap continuous_id
  have hjo : IsOpenMap j := hB.isOpenMap_subtype_val.prodMap IsOpenMap.id
  let ψ : X → P × P := fun z ↦ j z.1
  have hψc : Continuous ψ := hjc.comp continuous_subtype_val
  have hψo : IsOpenMap ψ := hjo.comp hC.isOpenMap_subtype_val
  have himage : ψ '' Set.univ =
      {p : P × P | ∃ hx : p.1 ∉ F, ∀ i, p.2 ≠ u i ⟨p.1, hx⟩} := by
    ext p
    constructor
    · rintro ⟨z, _, rfl⟩
      exact ⟨z.1.1.2, z.2⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨(⟨p.1, hx⟩, p.2), h⟩, Set.mem_univ _, rfl⟩
  have hopen := hψo Set.univ isOpen_univ
  have hconn := hX.image ψ hψc.continuousOn
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let : LocallyPathConnectedSpace S :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
  let e : P ≃ₜ S := onePointEquivSphereOfFinrankEq (by
    simp [Complex.finrank_real_complex])
  let : LocallyPathConnectedSpace P := e.symm.locallyPathConnectedSpace
  rw [himage] at hopen hconn
  exact hopen.isConnected_iff_isPathConnected.mp hconn


end HolomorphicAnosov
