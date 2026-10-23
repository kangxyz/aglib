/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FundamentalGroupComparison
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.Fintype.EquivFin

/-! # Strict cardinality decrease for original geometric fibre cokernels

The original geometric point functor preserves the actual cokernel and
monomorphism. A nontrivial subobject therefore strictly decreases the cardinality
of a finite fibre. No chosen replacement representation or module structure is
part of this statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

/-- The original point functor identifies the fibre of the literal cokernel
with the cokernel of the original fibre map. -/
def coefficientFiberCokernelIso {L F : AbelianSheaf.{u, u + 1} X} (q : L ⟶ F) :
    coefficientFiber s (cokernel q) ≅
      cokernel (((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map q) := by
  let T := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : T.Additive := Functor.additive_of_preserves_binary_products T
  exact PreservesCokernel.iso T q

/-- Quotienting a finite genuine geometric fibre by a nontrivial actual
subobject strictly decreases its cardinality. -/
theorem card_coefficientFiber_cokernel_lt
    {L F : AbelianSheaf.{u, u + 1} X} (q : L ⟶ F) [Mono q]
    [Nontrivial (coefficientFiber s L)] [Finite (coefficientFiber s F)] :
    Nat.card (coefficientFiber s (cokernel q)) < Nat.card (coefficientFiber s F) := by
  let T := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : T.Additive := Functor.additive_of_preserves_binary_products T
  let π := T.map (cokernel.π q)
  have hsurj : Function.Surjective π :=
    (AddCommGrpCat.epi_iff_surjective π).mp inferInstance
  have hinj : Function.Injective (T.map q) :=
    (AddCommGrpCat.mono_iff_injective (T.map q)).mp inferInstance
  have hcomp : T.map q ≫ π = 0 := by
    dsimp [π]
    rw [← T.map_comp, cokernel.condition, T.map_zero]
  have hninj : ¬Function.Injective π := by
    intro hπ
    obtain ⟨a, ha⟩ := exists_ne (0 : coefficientFiber s L)
    apply ha
    apply hinj
    apply hπ
    have h := congrArg (fun f : T.obj L ⟶ T.obj (cokernel q) => f a) hcomp
    simpa using h
  let : Finite (coefficientFiber s (cokernel q)) := Finite.of_surjective π hsurj
  let := Fintype.ofFinite (coefficientFiber s F)
  let := Fintype.ofFinite (coefficientFiber s (cokernel q))
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective π hsurj hninj

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
