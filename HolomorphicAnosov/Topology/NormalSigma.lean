import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Constructions.SumProd

/-!
# Normality of topological coproducts

This file proves that a topological coproduct of normal spaces is normal.
-/

open Set
namespace HolomorphicAnosov

/-- A topological coproduct of normal spaces is normal for every index type. (Fritsch–Piccinini, Props. 1.2.1 and 2.3.1) -/
theorem normalSpace_sigma {ι : Type*} {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)] [∀ i, NormalSpace (Y i)] :
    NormalSpace (Σ i, Y i) := by
  classical
  constructor
  intro s t hs ht hst
  have H (i : ι) := normal_separation (hs.preimage (continuous_sigmaMk (i := i)))
    (ht.preimage (continuous_sigmaMk (i := i))) (hst.preimage (Sigma.mk i))
  choose U V hU hV hsU htV hUV using H
  refine ⟨{z | z.2 ∈ U z.1}, {z | z.2 ∈ V z.1}, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_sigma_iff.mpr hU
  · exact isOpen_sigma_iff.mpr hV
  · rintro ⟨i, x⟩ hx
    exact hsU i hx
  · rintro ⟨i, x⟩ hx
    exact htV i hx
  · exact disjoint_left.mpr fun ⟨i, x⟩ hx hy ↦ (hUV i).le_bot ⟨hx, hy⟩

end HolomorphicAnosov

