import HolomorphicAnosov.Paper.Ghys.NativeComplexLineNormalization
import Mathlib.Topology.FiberBundle.Trivialization

/-! This file transports local trivializations across homeomorphisms preserving the base projection. -/

namespace Bundle.Trivialization
open Bundle Set

noncomputable def compHomeomorphOver {B F Z' : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace Z']
    {proj : Z' → B} {Z : Type*} [TopologicalSpace Z]
    {proj' : Z → B} (e : Trivialization F proj) (h : Z ≃ₜ Z')
    (hp : ∀ z, proj (h z) = proj' z) :
    Trivialization F proj' where
  toOpenPartialHomeomorph := h.transOpenPartialHomeomorph e.toOpenPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by
    ext z
    simp [e.source_eq, hp]
  target_eq := by
    simp [e.target_eq]
  proj_toFun := by
    intro p hp'
    have hmem : h p ∈ e.source := by
      rw [e.mem_source]
      simpa [e.mem_source] using hp'
    simpa [hp] using e.proj_toFun (h p) hmem

end Bundle.Trivialization
