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
theorem Subgroup.isClosed_of_locallyCompactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (H : Subgroup G) [LocallyCompactSpace H] :
    IsClosed (H : Set G) := by
  -- A locally compact subspace of a Hausdorff space is locally closed, i.e. open in its closure.
  -- Hence `H` is an open subgroup of the topological group `H.topologicalClosure`, so it is
  -- closed in `H.topologicalClosure` (`Subgroup.isClosed_of_isOpen`), which is closed in `G`.
  sorry
