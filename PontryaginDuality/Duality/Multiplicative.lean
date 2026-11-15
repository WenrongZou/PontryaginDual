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

section Additive

/-! ### Reduction to the additive case -/

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A]

/-- The canonical map from the double Pontryagin dual of `Multiplicative A` to the double additive
Pontryagin dual of `A`, obtained from `AddPontryaginDual.toMultiplicativeMulEquiv A` and
`AddPontryaginDual.toMultiplicative (AddPontryaginDual A)`. -/
private noncomputable def toAddDoubleDual
    (ξ : PontryaginDual (PontryaginDual (Multiplicative A))) :
    AddPontryaginDual (AddPontryaginDual A) :=
  (AddPontryaginDual.toMultiplicative (AddPontryaginDual A)).symm
    (map (AddPontryaginDual.toMultiplicativeMulEquiv A :
      Multiplicative (AddPontryaginDual A) →ₜ* PontryaginDual (Multiplicative A)) ξ)

omit [IsTopologicalAddGroup A] [LocallyCompactSpace A] in
private theorem continuous_toAddDoubleDual : Continuous (toAddDoubleDual A) :=
  (AddPontryaginDual.toMultiplicative (AddPontryaginDual A)).symm.continuous.comp
    (map_continuous (map _))

omit [IsTopologicalAddGroup A] [LocallyCompactSpace A] in
private theorem toAddDoubleDual_injective : Function.Injective (toAddDoubleDual A) := by
  intro ξ ξ' h
  have h' := (AddPontryaginDual.toMultiplicative (AddPontryaginDual A)).symm.injective h
  refine PontryaginDual.ext fun χ ↦ ?_
  obtain ⟨φ, rfl⟩ := (AddPontryaginDual.toMultiplicativeMulEquiv A).surjective χ
  exact DFunLike.congr_fun h' φ

omit [IsTopologicalAddGroup A] in
/-- The map `toAddDoubleDual A` intertwines `PontryaginDual.doubleDualEmb (Multiplicative A)` and
`AddPontryaginDual.doubleDualEmb A`. -/
private theorem toAddDoubleDual_comp_doubleDualEmb :
    toAddDoubleDual A ∘ doubleDualEmb (Multiplicative A) =
      AddPontryaginDual.doubleDualEmb A ∘ Multiplicative.toAdd :=
  rfl

private theorem isInducing_doubleDualEmb_multiplicative :
    IsInducing (doubleDualEmb (Multiplicative A)) := by
  have htoAdd : IsInducing (Multiplicative.toAdd : Multiplicative A → A) := ⟨induced_id.symm⟩
  refine .of_comp (map_continuous _) (continuous_toAddDoubleDual A) ?_
  rw [toAddDoubleDual_comp_doubleDualEmb]
  exact (AddPontryaginDual.isInducing_doubleDualEmb A).comp htoAdd

private theorem doubleDualEmb_multiplicative_bijective [T2Space A] :
    Function.Bijective (doubleDualEmb (Multiplicative A)) := by
  have hb : Function.Bijective (toAddDoubleDual A ∘ doubleDualEmb (Multiplicative A)) := by
    rw [toAddDoubleDual_comp_doubleDualEmb]
    exact (AddPontryaginDual.doubleDualEmb_bijective A).comp Multiplicative.toAdd.bijective
  refine ⟨hb.1.of_comp, fun ξ ↦ ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (toAddDoubleDual A ξ)
  exact ⟨x, toAddDoubleDual_injective A hx⟩

end Additive

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
  exact isInducing_doubleDualEmb_multiplicative (Additive G)

variable [T2Space G]

/-- The canonical map from a locally compact Hausdorff abelian group to its double dual is
bijective. -/
theorem doubleDualEmb_bijective : Function.Bijective (doubleDualEmb G) := by
  -- Same proof as `isInducing_doubleDualEmb`, from `AddPontryaginDual.doubleDualEmb_bijective`.
  have : T2Space (Additive G) := ‹T2Space G›
  exact doubleDualEmb_multiplicative_bijective (Additive G)

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
