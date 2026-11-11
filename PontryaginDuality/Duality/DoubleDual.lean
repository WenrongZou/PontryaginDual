/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Fourier.Basic

/-!
# The canonical map from a locally compact group to its double dual

## Main definitions

* `AddPontryaginDual.doubleDualEmb A`: the canonical continuous homomorphism from a locally
  compact additive monoid `A` to its double Pontryagin dual. It sends `a` to the evaluation
  `χ ↦ χ a`.

## Main statements

* `AddPontryaginDual.fourierIntegral_doubleDualEmb`: under the canonical map, the Fourier
  transform on the Pontryagin dual of `G` corresponds to the inverse Fourier transform.
-/

@[expose] public section

open MeasureTheory

namespace AddPontryaginDual

section Monoid

variable (A : Type*) [AddMonoid A] [TopologicalSpace A] [LocallyCompactSpace A]

/-- The canonical continuous homomorphism from a locally compact additive monoid to its double
Pontryagin dual, sending `a` to the evaluation `χ ↦ χ a`. The continuity uses the local
compactness of `A`. -/
def doubleDualEmb : A →ₜ+ AddPontryaginDual (AddPontryaginDual A) where
  toFun a :=
    ⟨{ toFun := fun χ ↦ χ a, map_zero' := rfl, map_add' := fun _ _ ↦ rfl },
      continuous_eval_const a⟩
  map_zero' := AddPontryaginDual.ext fun χ ↦ map_zero χ
  map_add' a b := AddPontryaginDual.ext fun χ ↦ map_add χ a b
  continuous_toFun :=
    ContinuousAddMonoidHom.continuous_of_continuous_uncurry _
      (continuous_eval.comp continuous_swap)

variable {A}

@[simp]
theorem doubleDualEmb_apply (a : A) (χ : AddPontryaginDual A) : doubleDualEmb A a χ = χ a :=
  rfl

@[simp]
theorem toAddChar_doubleDualEmb (a : A) (χ : AddPontryaginDual A) :
    (doubleDualEmb A a).toAddChar χ = χ.toAddChar a :=
  rfl

end Monoid

section Fourier

variable {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace (AddPontryaginDual G)]

/-- Under the canonical map from `G` to its double dual, the Fourier transform on the Pontryagin
dual of `G` corresponds to the inverse Fourier transform. -/
theorem fourierIntegral_doubleDualEmb (ν : Measure (AddPontryaginDual G))
    (F : AddPontryaginDual G → E) (x : G) :
    fourierIntegral ν F (doubleDualEmb G x) = fourierIntegralInv ν F (-x) := by
  simp [fourierIntegral_apply, fourierIntegralInv_apply, AddChar.map_neg_eq_inv]

end Fourier

end AddPontryaginDual
