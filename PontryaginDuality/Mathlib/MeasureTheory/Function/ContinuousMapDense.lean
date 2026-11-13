/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense

import Mathlib.Topology.UrysohnsLemma

/-!
# Density of compactly supported continuous functions in `Lᵖ` without normality

`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` assumes `[NormalSpace α]`. We prove
it for locally compact regular spaces, which covers all locally compact groups.
-/

@[expose] public section

open scoped ENNReal
open Set

namespace MeasureTheory

variable {α E : Type*} [TopologicalSpace α] [WeaklyLocallyCompactSpace α] [R1Space α]
  [MeasurableSpace α] [BorelSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
  {p : ℝ≥0∞}

/-- In a locally compact regular space, any function in `ℒp` can be approximated by compactly
supported continuous functions when `p < ∞`. -/
theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le' [μ.Regular] (hp : p ≠ ∞) {f : α → E}
    (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → E, HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ := by
  suffices H : ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧
      Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g by
    obtain ⟨g, hg, g_cont, g_mem, g_support⟩ := H
    exact ⟨g, g_support, hg, g_cont, g_mem⟩
  refine hf.induction_dense hp _ (fun c t ht htμ ε hε ↦ ?_)
    (fun f g ⟨hf, hf', hf''⟩ ⟨hg, hg', hg''⟩ ↦ ⟨hf.add hg, hf'.add hg', hf''.add hg''⟩) hε
  obtain ⟨δ, δpos, hδ⟩ := exists_Lp_half E μ p hε
  obtain ⟨η, ηpos, hη⟩ := exists_eLpNorm_indicator_le (μ := μ) hp c δpos.ne'
  have hη' : (η : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 ηpos.ne'
  obtain ⟨s, st, s_compact, s_closed, μs⟩ := ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη'
  have hsμ : μ s ≠ ∞ := ((measure_mono st).trans_lt htμ).ne
  obtain ⟨V, sV, V_open, -, hV⟩ := s_closed.measurableSet.exists_isOpen_sdiff_lt hsμ hη'
  -- By Urysohn's lemma, there is a compactly supported `g` with `1_s ≤ g ≤ 1_V`.
  obtain ⟨g, hgs, hgV, g_support, hg_range⟩ := exists_continuous_one_zero_of_isCompact s_compact
    V_open.isClosed_compl (disjoint_compl_right_iff_subset.2 sV)
  have gc_cont : Continuous fun x ↦ g x • c := by fun_prop
  have gc_support : HasCompactSupport fun x ↦ g x • c := g_support.smul_right
  have gc_mem : MemLp (fun x ↦ g x • c) p μ := gc_cont.memLp_of_hasCompactSupport gc_support
  have gc_bd x : ‖g x • c - s.indicator (fun _ ↦ c) x‖ ≤ ‖(V \ s).indicator (fun _ ↦ c) x‖ := by
    by_cases hs : x ∈ s
    · simp [hgs hs, hs]
    by_cases hV : x ∈ V
    · simpa [hs, hV, norm_smul, abs_of_nonneg (hg_range x).1] using
        mul_le_of_le_one_left (norm_nonneg c) (hg_range x).2
    · simp [hgV hV, hs, hV]
  have I1 : eLpNorm ((s.indicator fun _ ↦ c) - t.indicator fun _ ↦ c) p μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ μs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
  have I2 : eLpNorm (fun x ↦ g x • c - s.indicator (fun _ ↦ c) x) p μ ≤ δ :=
    (eLpNorm_mono (gc_mem.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator s_closed.measurableSet)) gc_bd).trans
      (hη _ hV.le (V_open.measurableSet.diff s_closed.measurableSet).nullMeasurableSet)
  refine ⟨fun x ↦ g x • c, ?_, gc_cont, gc_mem, gc_support⟩
  convert (hδ _ _ I2 I1).le using 2
  ext x
  simp

/-- In a locally compact regular space, compactly supported continuous functions are dense in
`Lp` when `p < ∞`. -/
theorem Lp.dense_hasCompactSupport_continuous [μ.Regular] [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {f : Lp E p μ | ∃ g : α → E, f =ᵐ[μ] g ∧ HasCompactSupport g ∧ Continuous g} := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).mpr fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le' hp
    (ε := ENNReal.ofReal ε) (by positivity)
  refine ⟨hg₄.toLp g, ⟨g, hg₄.coeFn_toLp, hg₁, hg₃⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← ENNReal.le_ofReal_iff_toReal_le ((Lp.memLp f).sub (Lp.memLp _)).eLpNorm_ne_top hε.le]
  convert hg₂ using 1
  apply eLpNorm_congr_ae
  gcongr
  exact hg₄.coeFn_toLp

end MeasureTheory
