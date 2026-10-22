/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-!
# Section algebras of native commutative module-sheaf monoids

All structures use the original section additive groups, scalar actions, and
module morphisms. The internal monoid laws are evaluated once on the original
pure section tensors. Ring and algebra structures are scoped, so ordinary
structure-sheaf rings are not silently replaced by transported structures.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.Algebra

variable {X : Scheme.{u}} (M : X.Modules) [MonObj M] (U : X.Opens)

/-- Evaluation of a native module-sheaf monoid on an open, with its original module. -/
@[instance_reducible]
def sectionMonObj : MonObj (ModuleCat.of Γ(X, U) Γ(M, U)) where
  one := ModuleCat.ofHom ((η[M]).val.app (op U)).hom
  mul := ModuleCat.ofHom (((μ[M]).val.app (op U)).hom.comp
    ((tensorSheafUnit X M M).app (op U)).hom)
  one_mul := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro r m
    change Γ(X, U) at r
    change Γ(M, U) at m
    change (μ[M]).app U (moduleTensorSection X M M U ((η[M]).app U r) m) = r • m
    have h := congrArg (fun f => f.val.app (op U)
      (moduleTensorSection X (𝟙_ X.Modules) M U r m)) (MonObj.one_mul M)
    change (μ[M]).app U (((η[M]) ▷ M).val.app (op U) _) = _ at h
    rw [whiskerRight_moduleTensorSection] at h
    exact h.trans (tensorLeftUnitIso_hom_section X M U r m)
  mul_one := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m r
    change Γ(X, U) at r
    change Γ(M, U) at m
    change (μ[M]).app U (moduleTensorSection X M M U m ((η[M]).app U r)) = r • m
    have h := congrArg (fun f => f.val.app (op U)
      (moduleTensorSection X M (𝟙_ X.Modules) U m r)) (MonObj.mul_one M)
    change (μ[M]).app U ((M ◁ (η[M])).val.app (op U) _) = _ at h
    rw [whiskerLeft_moduleTensorSection] at h
    exact h.trans (tensorRightUnitIso_hom_section X M U m r)
  mul_assoc := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro t p
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => simp only [TensorProduct.add_tmul, map_add, ht, hs]
    | tmul m n =>
      have h := congrArg (fun f => f.val.app (op U)
        (moduleTensorSection X (M ⊗ M) M U (moduleTensorSection X M M U m n) p))
        (MonObj.mul_assoc M)
      change (μ[M]).app U (((μ[M]) ▷ M).val.app (op U) _) =
        (μ[M]).app U ((M ◁ (μ[M])).val.app (op U) ((α_ M M M).hom.val.app (op U) _)) at h
      rw [whiskerRight_moduleTensorSection, associator_hom_moduleTensorSection,
        whiskerLeft_moduleTensorSection] at h
      exact h

/-- The section monoid retains the original unit component. -/
@[simp] theorem sectionMonObj_one (r : Γ(X, U)) :
    @MonObj.one _ _ _ _ (sectionMonObj M U) r = (η[M]).app U r := rfl

/-- The section monoid multiplies the original pure section tensor. -/
@[simp] theorem sectionMonObj_mul (m n : Γ(M, U)) :
    @MonObj.mul _ _ _ _ (sectionMonObj M U) (m ⊗ₜ[Γ(X, U)] n) =
      (μ[M]).app U (moduleTensorSection X M M U m n) := rfl

variable [IsCommMonObj M]

/-- The commutative ring on actual sections of a native commutative algebra object. -/
@[instance_reducible]
def sectionCommRing : CommRing Γ(M, U) := by
  letI hSectionMon : MonObj (ModuleCat.of Γ(X, U) Γ(M, U)) := sectionMonObj M U
  refine { ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing
    (ModuleCat.of Γ(X, U) Γ(M, U)) with mul_comm := ?_ }
  intro m n
  have h := congrArg (fun f => f.val.app (op U) (moduleTensorSection X M M U n m))
    (IsCommMonObj.mul_comm M)
  change (μ[M]).app U ((BraidedCategory.braiding M M).hom.val.app (op U) _) = _ at h
  rw [braiding_hom_moduleTensorSection] at h
  exact h

scoped[AlgebraicGeometry.Scheme.Modules.Algebra] attribute [instance] sectionCommRing
attribute [local instance] sectionCommRing

/-- The section algebra keeps the original scalar multiplication on the module sheaf. -/
@[instance_reducible]
def sectionAlgebra : Algebra Γ(X, U) Γ(M, U) := by
  letI hSectionMon : MonObj (ModuleCat.of Γ(X, U) Γ(M, U)) := sectionMonObj M U
  exact ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_
    (ModuleCat.of Γ(X, U) Γ(M, U))

scoped[AlgebraicGeometry.Scheme.Modules.Algebra] attribute [instance] sectionAlgebra
attribute [local instance] sectionAlgebra

@[simp] theorem section_one : (1 : Γ(M, U)) = (η[M]).app U (1 : Γ(X, U)) := rfl

@[simp] theorem section_mul (m n : Γ(M, U)) :
    m * n = (μ[M]).app U (moduleTensorSection X M M U m n) := rfl

@[simp] theorem section_algebraMap (r : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(M, U) r = (η[M]).app U r := rfl

/-- The original restriction, now as a ring homomorphism. -/
def sectionRestriction {U V : X.Opens} (i : V ⟶ U) : Γ(M, U) →+* Γ(M, V) where
  toFun := M.val.map i.op
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    change M.val.map i.op ((η[M]).val.app (op U) (1 : Γ(X, U))) =
      (η[M]).val.app (op V) (1 : Γ(X, V))
    rw [← PresheafOfModules.naturality_apply]
    congr 1
    exact map_one (X.presheaf.map i.op).hom
  map_mul' m n := by
    change M.val.map i.op ((μ[M]).val.app (op U) (moduleTensorSection X M M U m n)) = _
    rw [← PresheafOfModules.naturality_apply]
    exact congrArg ((μ[M]).val.app (op V)) (moduleTensorSection_restrict M M i m n)

@[simp] theorem sectionRestriction_apply {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    sectionRestriction M i m = M.val.map i.op m := rfl

@[simp] theorem sectionRestriction_id (U : X.Opens) :
    sectionRestriction M (𝟙 U) = RingHom.id _ := by
  ext m
  exact congrArg (fun f => f m) (M.presheaf.map_id (op U))

@[simp] theorem sectionRestriction_comp {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) :
    sectionRestriction M (j ≫ i) = (sectionRestriction M j).comp (sectionRestriction M i) := by
  ext m
  exact congrArg (fun f => f m) (M.presheaf.map_comp i.op j.op)

/-- Restriction preserves the original structure-sheaf action on the unit. -/
theorem sectionRestriction_algebraMap {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, U)) :
    sectionRestriction M i (algebraMap Γ(X, U) Γ(M, U) r) =
      algebraMap Γ(X, V) Γ(M, V) ((X.presheaf.map i.op) r) :=
  (PresheafOfModules.naturality_apply (η[M]).val i.op r).symm

variable {M} {N : X.Modules} [MonObj N] [IsCommMonObj N]

/-- An original algebra-object map acts on sections by its literal module component. -/
def sectionAlgHom (f : M ⟶ N) [IsMonHom f] (U : X.Opens) :
    Γ(M, U) →ₐ[Γ(X, U)] Γ(N, U) where
  __ := ((f.val.app (op U)).hom.toAddMonoidHom)
  toFun := f.app U
  map_one' := congrArg (fun g => g.val.app (op U) (1 : Γ(X, U))) (IsMonHom.one_hom f)
  map_mul' m n := by
    have h := congrArg (fun g => g.val.app (op U) (moduleTensorSection X M M U m n))
      (IsMonHom.mul_hom f)
    change f.app U ((μ[M]).app U _) = (μ[N]).app U ((f ⊗ₘ f).val.app (op U) _) at h
    have ht : (f ⊗ₘ f).val.app (op U) (moduleTensorSection X M M U m n) =
        moduleTensorSection X N N U (f.app U m) (f.app U n) :=
      tensorSheafMap_tmul X f f (op U) m n
    exact h.trans (congrArg ((μ[N]).app U) ht)
  commutes' r := congrArg (fun g => g.val.app (op U) r) (IsMonHom.one_hom f)

@[simp] theorem sectionAlgHom_apply (f : M ⟶ N) [IsMonHom f] (U : X.Opens)
    (m : Γ(M, U)) : sectionAlgHom f U m = f.app U m := rfl

/-- A bijective original algebra-object section map is its canonical algebra equivalence. -/
def sectionAlgEquivOfBijective (f : M ⟶ N) [IsMonHom f] (U : X.Opens)
    (hf : Function.Bijective (f.app U)) : Γ(M, U) ≃ₐ[Γ(X, U)] Γ(N, U) :=
  AlgEquiv.ofBijective (sectionAlgHom f U) hf

@[simp] theorem sectionAlgEquivOfBijective_apply (f : M ⟶ N) [IsMonHom f] (U : X.Opens)
    (hf : Function.Bijective (f.app U)) (m : Γ(M, U)) :
    sectionAlgEquivOfBijective f U hf m = f.app U m := rfl

end AlgebraicGeometry.Scheme.Modules.Algebra
