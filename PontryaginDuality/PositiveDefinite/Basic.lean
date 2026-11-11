/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Positive definite functions on groups

A function `φ : G → 𝕜` on an additive group is *positive definite* (or *of positive type*) if for
all `x₁, …, xₙ : G` the matrix `(φ (-xᵢ + xⱼ))ᵢⱼ` is positive semidefinite. Note that, despite
the classical name, this is a semidefiniteness condition.

## Main definitions

* `IsPositiveDefinite φ`: the function `φ : G → 𝕜` is positive definite.

## Main statements

* `IsPositiveDefinite.apply_neg`, `IsPositiveDefinite.norm_apply_le`: a positive definite function
  satisfies `φ (-x) = conj (φ x)` and `‖φ x‖ ≤ ‖φ 0‖`.
* `AddChar.isPositiveDefinite`: unitary characters are positive definite.
* `isPositiveDefinite_integral_mul_conj`: the function `x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ` is
  positive definite for `f` in `L²`. This is the convolution of `f` and `x ↦ conj (f (-x))`.
* `IsPositiveDefinite.integral_integral_nonneg`: the integral form of positive definiteness for
  continuous functions.
* `exists_isPositiveDefinite_hasCompactSupport`: on a locally compact group, there are continuous
  positive definite functions supported in arbitrarily small neighborhoods of `0`.

## References

* [G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 3.3][folland2016]
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ComplexOrder ComplexConjugate

variable {G 𝕜 : Type*} [AddGroup G] [RCLike 𝕜]

/-- A function `φ : G → 𝕜` on an additive group is positive definite if for all `x₁, …, xₙ : G`
the matrix `(φ (-xᵢ + xⱼ))ᵢⱼ` is positive semidefinite. -/
def IsPositiveDefinite (φ : G → 𝕜) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G), (Matrix.of fun i j ↦ φ (-x i + x j)).PosSemidef

namespace IsPositiveDefinite

variable {φ ψ : G → 𝕜}

theorem sum_nonneg (hφ : IsPositiveDefinite φ) {n : ℕ} (x : Fin n → G) (c : Fin n → 𝕜) :
    0 ≤ ∑ i, ∑ j, conj (c i) * φ (-x i + x j) * c j := by
  sorry

theorem apply_zero_nonneg (hφ : IsPositiveDefinite φ) : 0 ≤ φ 0 := by
  sorry

theorem apply_neg (hφ : IsPositiveDefinite φ) (x : G) : φ (-x) = conj (φ x) := by
  sorry

theorem norm_apply_le (hφ : IsPositiveDefinite φ) (x : G) : ‖φ x‖ ≤ ‖φ 0‖ := by
  sorry

protected theorem zero : IsPositiveDefinite (0 : G → 𝕜) := by
  sorry

protected theorem add (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (φ + ψ) := by
  sorry

protected theorem smul (hφ : IsPositiveDefinite φ) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveDefinite (c • φ) := by
  sorry

/-- The product of two positive definite functions is positive definite. This follows from the
Schur product theorem. -/
protected theorem mul (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (φ * ψ) := by
  sorry

protected theorem star (hφ : IsPositiveDefinite φ) : IsPositiveDefinite fun x ↦ conj (φ x) := by
  sorry

end IsPositiveDefinite

/-- Unitary characters are positive definite. -/
theorem AddChar.isPositiveDefinite (ψ : AddChar G Circle) :
    IsPositiveDefinite fun x ↦ (ψ x : ℂ) := by
  sorry

section Measure

variable [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
  {μ : Measure G}

/-- If `f` is in `L²`, then `x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ` is positive definite. -/
theorem isPositiveDefinite_integral_mul_conj [μ.IsAddLeftInvariant] {f : G → 𝕜}
    (hf : MemLp f 2 μ) : IsPositiveDefinite fun x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ := by
  -- `∑ i, ∑ j, conj (c i) * φ (-x i + x j) * c j = ∫ z, ‖∑ i, conj (c i) * f (-x i + z)‖ ^ 2 ∂μ`.
  sorry

/-- If `f` is in `L²`, then `x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ` is continuous. -/
theorem continuous_integral_mul_conj [LocallyCompactSpace G] [μ.IsAddHaarMeasure] [μ.Regular]
    {f : G → 𝕜} (hf : MemLp f 2 μ) : Continuous fun x ↦ ∫ y, f y * conj (f (-x + y)) ∂μ := by
  -- Translations act continuously on `L²` (`Lp.instContinuousVAddDomAddAct`).
  sorry

/-- The integral form of positive definiteness, for continuous functions. -/
theorem IsPositiveDefinite.integral_integral_nonneg [IsFiniteMeasureOnCompacts μ] {φ : G → 𝕜}
    (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) {f : G → 𝕜} (hf : Continuous f)
    (hf' : HasCompactSupport f) :
    0 ≤ ∫ x, ∫ y, conj (f x) * φ (-x + y) * f y ∂μ ∂μ := by
  -- Approximate the integral by Riemann sums, which are nonnegative by
  -- `IsPositiveDefinite.sum_nonneg`.
  sorry

end Measure

/-- On a locally compact group, there are continuous positive definite functions with compact
support contained in an arbitrarily small neighborhood of `0`. -/
theorem exists_isPositiveDefinite_hasCompactSupport [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] {U : Set G} (hU : U ∈ 𝓝 (0 : G)) :
    ∃ φ : G → ℂ, Continuous φ ∧ HasCompactSupport φ ∧ IsPositiveDefinite φ ∧ tsupport φ ⊆ U ∧
      φ 0 ≠ 0 := by
  -- Take `φ x = ∫ y, f y * conj (f (-x + y)) ∂μ` where `μ` is a Haar measure and `f` is a nonzero
  -- continuous function supported in a compact neighborhood `V` of `0` with `V - V ⊆ U`.
  sorry
