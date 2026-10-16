/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Universal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Exterior powers of actual sheaves of modules

The functor is the native pointwise exterior presheaf followed by the
original module sheafification. Its actual universal property represents
compatible sectionwise alternating maps into every target module sheaf.
The canonical wedge is the original sheafification unit applied to the
original module wedge, with exact restriction and coefficient formulas.
The site and coefficient rings are arbitrary, with all size and
sheafification hypotheses retained.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u v w w'

namespace SheafOfModulesOfCommRing

variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

local notation "Rᵣ" => Functor.obj (sheafCompose J (forget₂ CommRingCat RingCat)) R

local instance exteriorIdentityLocallyInjective :
    Presheaf.IsLocallyInjective J (𝟙 (Rᵣ).obj) :=
  Presheaf.isLocallyInjective_of_injective J _ (fun _ => Function.injective_id)

local instance exteriorIdentityLocallySurjective :
    Presheaf.IsLocallySurjective J (𝟙 (Rᵣ).obj) :=
  Presheaf.isLocallySurjective_of_surjective J _ (fun _ => Function.surjective_id)

/-- The actual exterior presheaf followed by the original module sheafification. -/
def exteriorPowerFunctor (n : ℕ) :
    SheafOfModules.{v} Rᵣ ⥤ SheafOfModules.{max u v} Rᵣ :=
  SheafOfModules.forget.{v} Rᵣ ⋙ PresheafOfModulesOfCommRing.exteriorPowerFunctor R.obj n ⋙
    PresheafOfModules.sheafification.{max u v} (𝟙 (Rᵣ).obj)

/-- The original sheafified exterior power of an actual module sheaf. -/
abbrev exteriorPower (M : SheafOfModules.{v} Rᵣ) (n : ℕ) :
    SheafOfModules.{max u v} Rᵣ := (exteriorPowerFunctor R n).obj M

/-- The original universal property for alternating maps into every actual module sheaf. -/
def exteriorPowerHomEquiv (M : SheafOfModules.{v} Rᵣ)
    (N : SheafOfModules.{max u v} Rᵣ) (n : ℕ) :
    (exteriorPower R M n ⟶ N) ≃
      PresheafOfModulesOfCommRing.AlternatingMap M.val N.val n :=
  (PresheafOfModules.sheafificationHomEquiv.{max u v} (𝟙 (Rᵣ).obj)).trans
    (PresheafOfModulesOfCommRing.exteriorPowerHomEquiv M.val N.val n)

/-- The canonical compatible wedge family in the original sheafified exterior power. -/
def exteriorPowerMk (M : SheafOfModules.{v} Rᵣ) (n : ℕ) :
    PresheafOfModulesOfCommRing.AlternatingMap M.val (exteriorPower R M n).val n :=
  exteriorPowerHomEquiv R M (exteriorPower R M n) n (𝟙 _)

/-- The canonical wedge is exactly the original additive sheafification unit on a wedge. -/
theorem exteriorPowerMk_apply (M : SheafOfModules.{v} Rᵣ) (n : ℕ)
    (X : Cᵒᵖ) (s : Fin n → M.val.obj X) :
    (exteriorPowerMk R M n).app X s =
      (CategoryTheory.toSheafify J
        (PresheafOfModulesOfCommRing.exteriorPower M.val n).presheaf).app X
          (ModuleCat.exteriorPower.mk (R := R.obj.obj X) (M := M.val.obj X) s) := rfl

/-- The universal equivalence evaluates morphisms on the same original wedge family. -/
theorem exteriorPowerHomEquiv_apply (M : SheafOfModules.{v} Rᵣ)
    (N : SheafOfModules.{max u v} Rᵣ) (n : ℕ) (φ : exteriorPower R M n ⟶ N)
    (X : Cᵒᵖ) (s : Fin n → M.val.obj X) :
    (exteriorPowerHomEquiv R M N n φ).app X s =
      φ.val.app X ((exteriorPowerMk R M n).app X s) := rfl

/-- Every original restriction preserves the canonical exterior wedge. -/
theorem exteriorPowerMk_naturality (M : SheafOfModules.{v} Rᵣ) (n : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : Fin n → M.val.obj X) :
    (exteriorPower R M n).val.map f ((exteriorPowerMk R M n).app X s) =
      (exteriorPowerMk R M n).app Y (fun i => M.val.map f (s i)) :=
  (exteriorPowerMk R M n).naturality f s

/-- The original descent map from a compatible sectionwise alternating family. -/
def exteriorPowerDesc (M : SheafOfModules.{v} Rᵣ)
    (N : SheafOfModules.{max u v} Rᵣ) (n : ℕ)
    (d : PresheafOfModulesOfCommRing.AlternatingMap M.val N.val n) :
    exteriorPower R M n ⟶ N := (exteriorPowerHomEquiv R M N n).symm d

/-- Descent sends the canonical wedge to the original given alternating value. -/
@[simp]
theorem exteriorPowerDesc_mk (M : SheafOfModules.{v} Rᵣ)
    (N : SheafOfModules.{max u v} Rᵣ) (n : ℕ)
    (d : PresheafOfModulesOfCommRing.AlternatingMap M.val N.val n)
    (X : Cᵒᵖ) (s : Fin n → M.val.obj X) :
    (exteriorPowerDesc R M N n d).val.app X ((exteriorPowerMk R M n).app X s) = d.app X s := by
  exact congrArg (fun t => t.app X s) ((exteriorPowerHomEquiv R M N n).apply_symm_apply d)

/-- Morphisms out of the actual exterior sheaf are determined by their original wedge values. -/
@[ext]
theorem exteriorPower_hom_ext (M : SheafOfModules.{v} Rᵣ)
    (N : SheafOfModules.{max u v} Rᵣ) (n : ℕ) {φ ψ : exteriorPower R M n ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (s : Fin n → M.val.obj X),
      φ.val.app X ((exteriorPowerMk R M n).app X s) =
        ψ.val.app X ((exteriorPowerMk R M n).app X s)) : φ = ψ := by
  apply (exteriorPowerHomEquiv R M N n).injective
  ext X s
  exact h X s

/-- The coefficient map is exactly sheafification of the original exterior-presheaf map. -/
theorem exteriorPowerFunctor_map {M N : SheafOfModules.{v} Rᵣ} (φ : M ⟶ N) (n : ℕ) :
    (exteriorPowerFunctor R n).map φ =
      (PresheafOfModules.sheafification.{max u v} (𝟙 (Rᵣ).obj)).map
      (PresheafOfModulesOfCommRing.exteriorPowerMap φ.val n) := rfl

/-- Coefficient maps send the original wedge to the wedge of the original images. -/
theorem exteriorPowerFunctor_map_mk {M N : SheafOfModules.{v} Rᵣ} (φ : M ⟶ N)
    (n : ℕ) (X : Cᵒᵖ) (s : Fin n → M.val.obj X) :
    ((exteriorPowerFunctor R n).map φ).val.app X ((exteriorPowerMk R M n).app X s) =
      (exteriorPowerMk R N n).app X (fun i => φ.val.app X (s i)) := by
  let ψ := PresheafOfModulesOfCommRing.exteriorPowerMap φ.val n
  let w := ModuleCat.exteriorPower.mk (R := R.obj.obj X) (M := M.val.obj X) s
  have H := congrArg (fun η => η.app X)
    (CategoryTheory.toSheafify_naturality (J := J)
      ((PresheafOfModules.toPresheaf (Rᵣ).obj).map ψ))
  have H' := ConcreteCategory.congr_hom H w
  change (CategoryTheory.toSheafify J
      (PresheafOfModulesOfCommRing.exteriorPower N.val n).presheaf).app X (ψ.app X w) =
    ((exteriorPowerFunctor R n).map φ).val.app X ((exteriorPowerMk R M n).app X s) at H'
  rw [← H', exteriorPowerMk_apply]
  exact congrArg
    ((CategoryTheory.toSheafify J
      (PresheafOfModulesOfCommRing.exteriorPower N.val n).presheaf).app X)
    (PresheafOfModulesOfCommRing.exteriorPowerMap_app_mk φ.val n X s)

end SheafOfModulesOfCommRing
