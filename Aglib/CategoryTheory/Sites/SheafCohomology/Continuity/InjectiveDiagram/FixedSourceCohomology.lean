/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Filtered.SystemConstructions
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.CohomologyCocone

/-! # Original fixed-source system and whole Ext transition values

The existing fixedSource constructor and existing represented cohomology
constructor are reused directly. Their original triangle/transition values
and equality transport are exposed before geometric specialization. No new
source, coefficient system, section functor or Ext realization is selected.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem

universe uJ vJ uA vA uI vI e

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)] (D : AdjunctionData A)
  {I : Type uI} [Category.{vI} I] (Y : I ⥤ J) (b : Cone Y) (F : A b.pt)

/-- The existing fixed-source transition has the component of its actual whole triangle. -/
theorem System.fixedSourceTransition_of_triangleIso_eq {i j : I} (a : i ⟶ j)
    (e : D.left (b.π.app j) ≅ D.left (b.π.app i) ⋙ D.left (Y.map a))
    (he : D.triangleIso (b.π.app j) (b.π.app i) (Y.map a) (b.w a) = e) :
    System.fixedSourceTransition D Y b F a = e.inv.app F :=
  NatTrans.congr_app (congrArg Iso.inv he) F

section Transfers

variable (U : System D) [∀ {i j : J} (a : i ⟶ j), IsIso (U.leftMap D a)]
  [∀ j, Abelian (A j)]
  [∀ {i j : J} (a : i ⟶ j), (D.left a).Additive]
  [∀ {i j : J} (a : i ⟶ j), PreservesFiniteLimits (D.left a)]
  [∀ {i j : J} (a : i ⟶ j), PreservesFiniteColimits (D.left a)]

/-- Equality of original arrows and coefficient values transports the same endpoint Ext map. -/
theorem System.extTransfer_of_heq {i j : J} [HasExt.{e} (A i)] [HasExt.{e} (A j)]
    (f g : i ⟶ j) (h : f = g) {M : A i} {N : A j}
    (φ : (D.left f).obj M ⟶ N) (ψ : (D.left g).obj M ⟶ N) (hφ : HEq φ ψ) (n : ℕ) :
    U.extTransfer D f φ n = U.extTransfer D g ψ n := by
  subst g
  cases hφ
  rfl

local instance fixedSourceReindexAdditive :
    ∀ {i j : I} (a : i ⟶ j), ((D.reindex Y).left a).Additive := by
  intro i j a
  change (D.left (Y.map a)).Additive
  infer_instance

local instance fixedSourceReindexLimits :
    ∀ {i j : I} (a : i ⟶ j), PreservesFiniteLimits ((D.reindex Y).left a) := by
  intro i j a
  change PreservesFiniteLimits (D.left (Y.map a))
  infer_instance

local instance fixedSourceReindexColimits :
    ∀ {i j : I} (a : i ⟶ j), PreservesFiniteColimits ((D.reindex Y).left a) := by
  intro i j a
  change PreservesFiniteColimits (D.left (Y.map a))
  infer_instance

local instance fixedSourceReindexCartesian :
    ∀ {i j : I} (a : i ⟶ j), IsIso ((U.reindex D Y).leftMap (D.reindex Y) a) := by
  intro i j a
  change IsIso (U.leftMap D (Y.map a))
  infer_instance

/-- The complete original cohomology transition of the existing fixed-source system. -/
theorem System.representedCohomologyMap_fixedSource
    [∀ i, HasExt.{e} (A (Y.obj i))] (hD : D.Coherent) (n : ℕ)
    {i j : I} (a : i ⟶ j) :
    representedCohomologyMap (D.reindex Y) (U.reindex D Y)
        (System.fixedSource D Y hD b F) n a =
      U.extTransfer D (Y.map a) (System.fixedSourceTransition D Y b F a) n := by
  rw [representedCohomologyMap_reindex_eq_extTransfer, System.fixedSource_leftMap]
  rfl

end Transfers

end CategoryTheory.InjectiveSystem
