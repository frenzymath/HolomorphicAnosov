import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Joint continuity of derivatives of holomorphic slices

Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012,
Chapter I §3.A (3.3), p.21, and §3.B (3.11) and continuity of derivations,
pp.22–23. Ghys, *Holomorphic Anosov systems*, Lemma 3.3, p.592.

The domain is an arbitrary open subset of the product of the complex line and a
metric parameter space. No differentiation in the parameter is asserted.
-/

namespace HolomorphicAnosov

noncomputable section

open Set Filter _root_.Topology
open scoped Uniformity

namespace SliceDerivativePreparation

/-- Joint continuity on a genuine product neighborhood gives compact-uniform convergence
of the original slices as the parameter tends to its marked value. Source: Demailly I §3.B,
pp.22–23. Apply the compact transverse continuity lemma to each compact subset of the open
complex domain; no compactness or differentiation of the parameter space is required. -/
theorem locally_uniform_slices
    {T : Type*} [TopologicalSpace T] (U : Set ℂ) (V : Set T)
    (hU : IsOpen U) (hV : IsOpen V) (H : ℂ × T → ℂ)
    (hH : ContinuousOn H (U ×ˢ V)) (t : T) (ht : t ∈ V) :
    TendstoLocallyUniformlyOn (fun s z ↦ H (z, s)) (fun z ↦ H (z, t)) (𝓝 t) U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK u hu
  have hc : ContinuousOn (fun p : T × ℂ ↦ H (p.2, p.1)) (V ×ˢ K) :=
    hH.comp continuous_swap.continuousOn (fun _ hp ↦ ⟨hKU hp.2, hp.1⟩)
  obtain ⟨W, hW, hw⟩ := hK.mem_uniformity_of_prod (f := fun t z ↦ H (z, t)) hc ht (symm_le_uniformity hu)
  rw [hV.nhdsWithin_eq ht] at hW
  filter_upwards [hW] with s hs z hz
  exact hw s hs z hz

/-- The locally uniform derivative theorem gives actual joint continuity of the first
complex derivative on an open product neighborhood. Source: Demailly I §3.B pp.22–23.
Its limiting derivative is holomorphic, and uniformity controls simultaneous variation of
the parameter and evaluation point. -/
theorem joint_deriv_continuousOn
    {T : Type*} [TopologicalSpace T] (U : Set ℂ) (V : Set T)
    (hU : IsOpen U) (hV : IsOpen V) (H : ℂ × T → ℂ)
    (hH : ContinuousOn H (U ×ˢ V))
    (hd : ∀ t ∈ V, DifferentiableOn ℂ (fun z ↦ H (z, t)) U) :
    ContinuousOn (fun p : ℂ × T ↦ deriv (fun z ↦ H (z, p.2)) p.1) (U ×ˢ V) := by
  intro p hp
  have hloc := locally_uniform_slices U V hU hV H hH p.2 hp.2
  have hder := hloc.deriv (Filter.eventually_of_mem (hV.mem_nhds hp.2) (fun t ht ↦ hd t ht)) hU
  have hnear := (hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hder) p.1 hp.1
  have hswap : Tendsto (fun q : ℂ × T ↦ (q.2, q.1)) (𝓝 p) (𝓝 p.2 ×ˢ 𝓝 p.1) :=
    continuous_snd.continuousAt.tendsto.prodMk continuous_fst.continuousAt.tendsto
  have hlimit : ContinuousAt (fun z ↦ deriv (fun z ↦ H (z, p.2)) z) p.1 :=
    ((hd p.2 hp.2).deriv hU).continuousOn.continuousAt (hU.mem_nhds hp.1)
  have hc : ContinuousAt (fun q : ℂ × T ↦ deriv (fun z ↦ H (z, q.2)) q.1) p :=
    (hlimit.comp continuous_fst.continuousAt).tendsto.congr_uniformity (hnear.comp hswap)
  exact hc.continuousWithinAt

/-- Local open product neighborhoods suffice on an arbitrary varying domain.
Source: Demailly I §3.A (3.3) p.21. At each point choose a product neighborhood inside
Ω and apply the proved local derivative continuity there. -/
theorem joint_deriv_continuousOn_open
    {T : Type*} [TopologicalSpace T] (Ω : Set (ℂ × T)) (hΩ : IsOpen Ω)
    (H : ℂ × T → ℂ) (hH : ContinuousOn H Ω)
    (hd : ∀ t, DifferentiableOn ℂ (fun z ↦ H (z, t)) {z | (z, t) ∈ Ω}) :
    ContinuousOn (fun p : ℂ × T ↦ deriv (fun z ↦ H (z, p.2)) p.1) Ω := by
  intro p hp
  obtain ⟨U, V, hU, hpU, hV, hpV, hUV⟩ := mem_nhds_prod_iff'.mp (hΩ.mem_nhds hp)
  have hc := joint_deriv_continuousOn U V hU hV H (hH.mono hUV)
    (fun t ht ↦ (hd t).mono (fun z hz ↦ hUV ⟨hz, ht⟩))
  exact (hc.continuousAt ((hU.prod hV).mem_nhds ⟨hpU, hpV⟩)).continuousWithinAt

/-- On an open slice, both within derivatives are the ordinary derivatives of the same
original function. Source: Demailly I §3.B pp.22–23. The first equality holds throughout
an open neighborhood, so its germ can be differentiated once more. -/
theorem second_derivWithin_of_isOpen (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (z : ℂ) (hz : z ∈ U) :
    derivWithin (derivWithin f U) U z = deriv (deriv f) z := by
  rw [derivWithin_of_isOpen hU hz]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hz] with w hw
  exact derivWithin_of_isOpen hU hw

end SliceDerivativePreparation

/-- A continuous family of holomorphic slices has jointly continuous first and second
complex derivatives on its original open, possibly varying domain.

DAG node: `analysis.holomorphic_slice_two_derivatives_continuous_g2`.
Source: Demailly, June 21, 2012, Chapter I §3.A (3.3), p.21, and §3.B (3.11)
and continuity of derivations, pp.22–23; Ghys, Lemma 3.3, p.592.

`H` is Mathlib's extension of `h` along the injective subtype inclusion, with value
zero off `Ω`. It agrees with `h` at every point of `Ω`. The hypothesis requires
complex differentiability only on each actual open slice `sliceDomain t`. Both
`derivWithin` operations use that same slice, so values chosen outside `Ω` do not
enter the derivatives. Continuity is on the subtype `Ω`, not on a product-global
extension. The parameter type is an arbitrary metric space.

Proof: Fix `(z₀,t₀)` in `Ω`. Openness supplies `r > 0` and a neighborhood `T₀`
of `t₀` with `closedBall z₀ (2*r) × T₀` contained in `Ω`. For a sequence
`(zₙ,tₙ)` tending to `(z₀,t₀)`, discard finitely many terms so that all `tₙ`
lie in `T₀` and all `zₙ` lie in `ball z₀ r`. The set consisting of `t₀` and
these sequence parameters is compact. Joint continuity on its product with the
closed disk gives uniform continuity. Consequently the functions `H(·,tₙ)`
converge uniformly to `H(·,t₀)` on the closed disk, hence locally uniformly on
the open disk. Every disk and parameter used here lies in the original domain.

Apply `TendstoLocallyUniformlyOn.deriv` on that fixed open disk. Each first
derivative is holomorphic by `DifferentiableOn.deriv`, so applying the same
locally uniform derivative theorem again gives convergence of the second
derivatives. On an open slice these ordinary derivatives agree locally with
`derivWithin` and its iteration. This is Demailly's continuity of derivations
from the Cauchy integral formula on a smaller disk.

For either order, the difference between the derivative at `(zₙ,tₙ)` and that
at `(z₀,t₀)` is bounded by the derivative-family difference at `zₙ` plus the
difference between the limiting holomorphic derivative at `zₙ` and at `z₀`.
Local uniform convergence makes the first term tend to zero; holomorphic
continuity makes the second tend to zero. The subtype of the metric product is
metrizable, so this sequential assertion gives continuity at every point of
`Ω`. Empty domains and slices make no assertion at a nonexistent point. -/
theorem holomorphic_slice_two_derivatives_continuous
    {T : Type*} [MetricSpace T] (Ω : Set (ℂ × T)) (hΩ : IsOpen Ω)
    (h : Ω → ℂ) (hh : Continuous h) :
    let H : ℂ × T → ℂ := Function.extend (Subtype.val : Ω → ℂ × T) h (fun _ ↦ 0)
    let sliceDomain : T → Set ℂ := fun t ↦ {z | (z, t) ∈ Ω}
    (∀ t, DifferentiableOn ℂ (fun z ↦ H (z, t)) (sliceDomain t)) →
      Continuous (fun p : Ω ↦
        derivWithin (fun z ↦ H (z, p.val.2)) (sliceDomain p.val.2) p.val.1) ∧
      Continuous (fun p : Ω ↦
        derivWithin
          (derivWithin (fun z ↦ H (z, p.val.2)) (sliceDomain p.val.2))
          (sliceDomain p.val.2) p.val.1) := by
  dsimp only
  let H : ℂ × T → ℂ := Function.extend (Subtype.val : Ω → ℂ × T) h (fun _ ↦ 0)
  let sliceDomain : T → Set ℂ := fun t ↦ {z | (z, t) ∈ Ω}
  intro hd
  have hagree : (fun p : Ω ↦ H p.val) = h := by
    funext p
    exact Subtype.val_injective.extend_apply h (fun _ ↦ 0) p
  have hH : ContinuousOn H Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun p : Ω ↦ H p.val)
    rw [hagree]
    exact hh
  have hopen : ∀ t, IsOpen (sliceDomain t) := fun t ↦
    hΩ.preimage (continuous_id.prodMk continuous_const)
  have hfirst := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ H hH hd
  have hsecond := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ
    (fun p ↦ deriv (fun z ↦ H (z, p.2)) p.1) hfirst
    (fun t ↦ (hd t).deriv (hopen t))
  constructor
  · have hc := continuousOn_iff_continuous_domRestrict.mp hfirst
    apply hc.congr
    intro p
    exact (derivWithin_of_isOpen (hopen p.val.2) p.property).symm
  · have hc := continuousOn_iff_continuous_domRestrict.mp hsecond
    apply hc.congr
    intro p
    exact (SliceDerivativePreparation.second_derivWithin_of_isOpen
      (fun z ↦ H (z, p.val.2)) (sliceDomain p.val.2) (hopen p.val.2)
      p.val.1 p.property).symm

end
end HolomorphicAnosov


