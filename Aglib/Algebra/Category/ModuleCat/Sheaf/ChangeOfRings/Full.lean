/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Full faithfulness of original scalar restriction along a locally surjective map

The existing presheaf Hom equivalence descends a scalar-linear map by the
original target sheaf's separation. It gives full faithfulness on the actual
module sheaves, an additive Hom equivalence, and the whole represented-Hom
natural isomorphism. Forward and inverse maps keep the original section
functions. No scalar ring, sheafification or module carrier is replaced.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe c h r m

namespace SheafOfModules

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{r}} (α : R ⟶ R') [CategoryTheory.Sheaf.IsLocallySurjective α]

/-- The existing scalar-restriction functor is fully faithful on the original sheaves. -/
def restrictScalarsFullyFaithfulOfLocallySurjective : (restrictScalars.{m} α).FullyFaithful where
  preimage {M N} f := ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    α.hom N.isSheaf).symm f.val⟩
  map_preimage {M N} f := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α.hom N.isSheaf).apply_symm_apply f.val
  preimage_map {M N} f := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α.hom N.isSheaf).symm_apply_apply f.val

/-- The fully faithful original map is an additive equivalence on actual Hom groups. -/
def restrictScalarsHomAddEquiv (M N : SheafOfModules.{m} R') :
    (M ⟶ N) ≃+ ((restrictScalars α).obj M ⟶ (restrictScalars α).obj N) where
  __ := (restrictScalarsFullyFaithfulOfLocallySurjective α).homEquiv
  map_add' _ _ := (restrictScalars α).map_add

/-- The forward map is the original scalar-restriction map. -/
theorem restrictScalarsHomAddEquiv_apply {M N : SheafOfModules.{m} R'} (f : M ⟶ N) :
    restrictScalarsHomAddEquiv α M N f = (restrictScalars α).map f := rfl

/-- The inverse retains every original component function. -/
theorem restrictScalarsHomAddEquiv_symm_apply_val_app {M N : SheafOfModules.{m} R'}
    (f : (restrictScalars α).obj M ⟶ (restrictScalars α).obj N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((restrictScalarsHomAddEquiv α M N).symm f).val.app U x = f.val.app U x := rfl

/-- The original Hom comparison respects composition in both coefficient variables. -/
theorem restrictScalarsHomAddEquiv_comp {M N P : SheafOfModules.{m} R'}
    (f : M ⟶ N) (g : N ⟶ P) :
    restrictScalarsHomAddEquiv α M P (f ≫ g) =
      restrictScalarsHomAddEquiv α M N f ≫ restrictScalarsHomAddEquiv α N P g :=
  (restrictScalars α).map_comp f g

/-- The complete represented-Hom comparison is natural before object evaluation. -/
def restrictScalarsCoyonedaIso (M : SheafOfModules.{m} R') :
    preadditiveCoyoneda.obj (op M) ≅
      restrictScalars α ⋙ preadditiveCoyoneda.obj (op ((restrictScalars α).obj M)) :=
  NatIso.ofComponents (fun N => (restrictScalarsHomAddEquiv α M N).toAddCommGrpIso)
    (fun f => by
      ext g
      exact (restrictScalars α).map_comp g f)

/-- A component of the whole natural isomorphism uses the original functor map. -/
theorem restrictScalarsCoyonedaIso_hom_app_apply (M N : SheafOfModules.{m} R')
    (f : M ⟶ N) :
    (restrictScalarsCoyonedaIso α M).hom.app N f = (restrictScalars α).map f := rfl

end SheafOfModules
