/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Locally compact subgroups are closed

A subgroup of a Hausdorff topological group which is locally compact for the subspace topology is
closed.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 4.3][folland2016]
-/

@[expose] public section

/-- A locally compact subgroup of a Hausdorff topological group is closed. -/
@[to_additive
/-- A locally compact additive subgroup of a Hausdorff topological additive group is closed. -/]
instance Subgroup.isClosed_of_locallyCompactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] {H : Subgroup G} [LocallyCompactSpace H] :
    IsClosed (H : Set G) := by
  -- It suffices to show that `H` is locally closed at `1`. Let `K` be a compact neighborhood of
  -- `1` in `H` and `U` an open neighborhood of `1` in `G` with `U ∩ H ⊆ K`. Since `K` is closed
  -- in `G`, we get `U ∩ closure H ⊆ closure (U ∩ H) ⊆ K ⊆ H`.
  refine H.isClosed_of_isLocallyClosedAt H.one_mem ?_
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hK1
  obtain ⟨U, hU, hUK⟩ := hK1
  refine isLocallyClosedAt_iff_exists_inter_closure_subset.mpr
    ⟨interior U, interior_mem_nhds.mpr hU, ?_⟩
  grw [isOpen_interior.inter_closure, closure_minimal _ (hK.image continuous_subtype_val).isClosed]
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · intro x hx
    exact ⟨⟨x, hx.2⟩, hUK (interior_subset (s := U) hx.1), rfl⟩
