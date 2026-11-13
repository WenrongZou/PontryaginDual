/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization

/-!
# The Stone–Weierstrass theorem for functions vanishing at infinity

A non-unital star subalgebra of `C₀(X, 𝕜)` which separates points and vanishes nowhere is dense.
This follows from the Stone–Weierstrass theorem on the one-point compactification of `X`.
-/

@[expose] public section

open OnePoint
open scoped ZeroAtInfty

variable {X 𝕜 : Type*} [TopologicalSpace X] [R1Space X] [RCLike 𝕜]

namespace ContinuousMap

@[simp]
theorem toZeroAtInfty_toOnePoint (f : C₀(X, 𝕜)) : f.toOnePoint.toZeroAtInfty = f := by
  ext x
  simp

theorem toZeroAtInfty_mul (g h : C(OnePoint X, 𝕜)) :
    (g * h).toZeroAtInfty =
      g.toZeroAtInfty * h.toZeroAtInfty + g ∞ • h.toZeroAtInfty + h ∞ • g.toZeroAtInfty := by
  ext x
  simp
  ring

theorem continuous_toZeroAtInfty :
    Continuous (toZeroAtInfty : C(OnePoint X, 𝕜) → C₀(X, 𝕜)) := by
  refine AddMonoidHomClass.continuous_of_bound (toZeroAtInftyAddMonoidHom X 𝕜) 2 fun g ↦ ?_
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  calc ‖g x - g ∞‖ ≤ ‖g x‖ + ‖g ∞‖ := norm_sub_le _ _
    _ ≤ 2 * ‖g‖ := by linarith [g.norm_coe_le_norm x, g.norm_coe_le_norm ∞]

end ContinuousMap

namespace ZeroAtInftyContinuousMap

/-- The **Stone–Weierstrass theorem** for functions vanishing at infinity: a non-unital star
subalgebra of `C₀(X, 𝕜)` which separates points and vanishes nowhere is dense. -/
theorem dense_of_separatesPoints (A : NonUnitalStarSubalgebra 𝕜 C₀(X, 𝕜))
    (hA : ∀ ⦃x y : X⦄, x ≠ y → ∃ f ∈ A, f x ≠ f y) (hA' : ∀ x : X, ∃ f ∈ A, f x ≠ 0) :
    Dense (A : Set C₀(X, 𝕜)) := by
  -- The functions `c + f` on `OnePoint X`, with `c` constant and `f ∈ A`, form a star subalgebra.
  let B : StarSubalgebra 𝕜 C(OnePoint X, 𝕜) :=
    { carrier := {g | g.toZeroAtInfty ∈ A}
      mul_mem' := fun {g h} hg hh ↦ by
        change (g * h).toZeroAtInfty ∈ A
        rw [ContinuousMap.toZeroAtInfty_mul]
        exact add_mem (add_mem (mul_mem hg hh) (A.smul_mem _ hh)) (A.smul_mem _ hg)
      one_mem' := by
        change (1 : C(OnePoint X, 𝕜)).toZeroAtInfty ∈ A
        rw [← ContinuousMap.const_one, ContinuousMap.toZeroAtInfty_const]
        exact zero_mem A
      add_mem' := fun {g h} hg hh ↦ by
        change (g + h).toZeroAtInfty ∈ A
        rw [ContinuousMap.toZeroAtInfty_add]
        exact add_mem hg hh
      zero_mem' := by
        change (0 : C(OnePoint X, 𝕜)).toZeroAtInfty ∈ A
        rw [ContinuousMap.toZeroAtInfty_zero]
        exact zero_mem A
      algebraMap_mem' := fun r ↦ by
        change (algebraMap 𝕜 C(OnePoint X, 𝕜) r).toZeroAtInfty ∈ A
        rw [show algebraMap 𝕜 C(OnePoint X, 𝕜) r = .const _ r from rfl,
          ContinuousMap.toZeroAtInfty_const]
        exact zero_mem A
      star_mem' := fun {g} hg ↦ by
        change (star g).toZeroAtInfty ∈ A
        rw [ContinuousMap.toZeroAtInfty_star]
        exact star_mem hg }
  have hB (f : C₀(X, 𝕜)) (hf : f ∈ A) : f.toOnePoint ∈ B := by
    change f.toOnePoint.toZeroAtInfty ∈ A
    rwa [ContinuousMap.toZeroAtInfty_toOnePoint]
  have hsep : B.SeparatesPoints := by
    intro x y hxy
    induction x using OnePoint.rec with
    | infty =>
      induction y using OnePoint.rec with
      | infty => exact absurd rfl hxy
      | coe y =>
        obtain ⟨f, hf, hfy⟩ := hA' y
        exact ⟨_, ⟨_, hB f hf, rfl⟩, by simpa using hfy.symm⟩
    | coe x =>
      induction y using OnePoint.rec with
      | infty =>
        obtain ⟨f, hf, hfx⟩ := hA' x
        exact ⟨_, ⟨_, hB f hf, rfl⟩, by simpa using hfx⟩
      | coe y =>
        obtain ⟨f, hf, hfxy⟩ := hA (OnePoint.coe_injective.ne_iff.1 hxy)
        exact ⟨_, ⟨_, hB f hf, rfl⟩, by simpa using hfxy⟩
  have hBtop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hsep
  intro f
  have hf : f.toOnePoint ∈ closure (B : Set C(OnePoint X, 𝕜)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hBtop]
    trivial
  simpa using map_mem_closure ContinuousMap.continuous_toZeroAtInfty hf fun g hg ↦ hg

end ZeroAtInftyContinuousMap
