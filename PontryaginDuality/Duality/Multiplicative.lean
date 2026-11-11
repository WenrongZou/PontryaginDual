/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import PontryaginDuality.Duality.Basic

/-!
# Pontryagin duality for multiplicative groups

We deduce the Pontryagin duality theorem for a multiplicative locally compact Hausdorff abelian
group `G` from the additive version, applied to `Additive G`.

## Main definitions

* `AddPontryaginDual.toMultiplicativeMulEquiv A`: the homeomorphism
  `AddPontryaginDual.toMultiplicative A` as an isomorphism of topological groups
  `Multiplicative (AddPontryaginDual A) ≃ₜ* PontryaginDual (Multiplicative A)`.
* `PontryaginDual.doubleDualEmb A`: the canonical continuous homomorphism from a locally compact
  monoid `A` to its double Pontryagin dual.
* `PontryaginDual.doubleDualEquiv G`: the canonical isomorphism of topological groups
  `G ≃ₜ* PontryaginDual (PontryaginDual G)`.

## TODO

* Once `AddPontryaginDual` is generated from `PontryaginDual` by `to_additive`,
  `AddPontryaginDual.doubleDualEmb` should be generated from `PontryaginDual.doubleDualEmb`.
-/

@[expose] public section

open Topology

/-- `AddPontryaginDual.toMultiplicative` as an isomorphism of topological groups. -/
noncomputable def AddPontryaginDual.toMultiplicativeMulEquiv (A : Type*) [AddMonoid A]
    [TopologicalSpace A] :
    Multiplicative (AddPontryaginDual A) ≃ₜ* PontryaginDual (Multiplicative A) where
  toFun φ := toMultiplicative A φ.toAdd
  invFun ψ := .ofAdd ((toMultiplicative A).symm ψ)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (toMultiplicative A).continuous.comp continuous_toAdd
  continuous_invFun := continuous_ofAdd.comp (toMultiplicative A).symm.continuous

namespace PontryaginDual

section Monoid

variable (A : Type*) [Monoid A] [TopologicalSpace A]

instance : ContinuousEvalConst (PontryaginDual A) A Circle :=
  inferInstanceAs (ContinuousEvalConst (A →ₜ* Circle) A Circle)

instance [LocallyCompactSpace A] : ContinuousEval (PontryaginDual A) A Circle :=
  inferInstanceAs (ContinuousEval (A →ₜ* Circle) A Circle)

variable [LocallyCompactSpace A]

/-- The canonical continuous homomorphism from a locally compact monoid to its double Pontryagin
dual, sending `a` to the evaluation `χ ↦ χ a`. The continuity uses the local compactness of
`A`. -/
noncomputable def doubleDualEmb : A →ₜ* PontryaginDual (PontryaginDual A) where
  toFun a :=
    ⟨{ toFun := fun χ ↦ χ a, map_one' := rfl, map_mul' := fun _ _ ↦ rfl },
      continuous_eval_const a⟩
  map_one' := PontryaginDual.ext fun χ ↦ _root_.map_one χ
  map_mul' a b := PontryaginDual.ext fun χ ↦ _root_.map_mul χ a b
  continuous_toFun :=
    ContinuousMonoidHom.continuous_of_continuous_uncurry _
      (continuous_eval.comp continuous_swap)

variable {A}

@[simp]
theorem doubleDualEmb_apply (a : A) (χ : PontryaginDual A) : doubleDualEmb A a χ = χ a :=
  rfl

end Monoid

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- The canonical map from a locally compact abelian group to its double dual induces the topology
of the group. -/
theorem isInducing_doubleDualEmb : IsInducing (doubleDualEmb G) := by
  -- Apply `AddPontryaginDual.isInducing_doubleDualEmb` to `Additive G`. The isomorphisms of
  -- topological groups `AddPontryaginDual (Additive G) ≃ PontryaginDual G` and
  -- `AddPontryaginDual (AddPontryaginDual (Additive G)) ≃ PontryaginDual (PontryaginDual G)`
  -- obtained from `AddPontryaginDual.toMultiplicativeMulEquiv` intertwine
  -- `AddPontryaginDual.doubleDualEmb (Additive G)` and `PontryaginDual.doubleDualEmb G`.
  sorry

variable [T2Space G]

/-- The canonical map from a locally compact Hausdorff abelian group to its double dual is
bijective. -/
theorem doubleDualEmb_bijective : Function.Bijective (doubleDualEmb G) := by
  -- Same proof as `isInducing_doubleDualEmb`, from `AddPontryaginDual.doubleDualEmb_bijective`.
  sorry

/-- **Pontryagin duality**: a locally compact Hausdorff abelian group is canonically isomorphic,
as a topological group, to its double Pontryagin dual. -/
noncomputable def doubleDualEquiv : G ≃ₜ* PontryaginDual (PontryaginDual G) where
  __ := MulEquiv.ofBijective (doubleDualEmb G) (doubleDualEmb_bijective G)
  continuous_toFun := map_continuous (doubleDualEmb G)
  continuous_invFun :=
    ((Equiv.ofBijective _ (doubleDualEmb_bijective G)).toHomeomorphOfIsInducing
      (isInducing_doubleDualEmb G)).symm.continuous

variable {G}

@[simp]
theorem coe_doubleDualEquiv : ⇑(doubleDualEquiv G) = doubleDualEmb G :=
  rfl

theorem doubleDualEquiv_apply (x : G) (χ : PontryaginDual G) : doubleDualEquiv G x χ = χ x :=
  rfl

end PontryaginDual
