/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.Presheaf.Relative
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Relative differential sheaves over arbitrary target sites

Sheafify the sole native relative differential presheaf and compose its
original universal property with the original module-sheafification
adjunction. The resulting object represents native relative derivations
against every target module sheaf. The universal differential is literally
the original sheafification unit applied to the original differential.
No source-site topology, quasicoherence, or geometric base hypothesis is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u v₁ v₂ u₁ u₂

namespace SheafOfModulesOfCommRing.DifferentialsConstruction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⟶ F.op ⋙ R.obj)
  [(PresheafOfModulesOfCommRing.pushforward.{u} φ).IsRightAdjoint]

local notation "Rᵣ" => Functor.obj (sheafCompose J (forget₂ CommRingCat RingCat)) R

local instance differentialIdentityLocallyInjective :
    Presheaf.IsLocallyInjective J (𝟙 (Rᵣ).obj) :=
  Presheaf.isLocallyInjective_of_injective J _ (fun _ => Function.injective_id)

local instance differentialIdentityLocallySurjective :
    Presheaf.IsLocallySurjective J (𝟙 (Rᵣ).obj) :=
  Presheaf.isLocallySurjective_of_surjective J _ (fun _ => Function.surjective_id)

/-- The original module sheafification of the sole relative differential presheaf. -/
def relativeDifferentials : SheafOfModules.{u} Rᵣ :=
  (PresheafOfModules.sheafification (𝟙 (Rᵣ).obj)).obj
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials φ)

/-- The original relative differential sheaf represents derivations into every module sheaf. -/
def relativeDifferentialsHomEquiv (M : SheafOfModules.{u} Rᵣ) :
    (relativeDifferentials R φ ⟶ M) ≃
      PresheafOfModulesOfCommRing.Derivation M.val φ :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (Rᵣ).obj)).trans
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentialsHomEquiv φ M.val)

/-- The original universal derivation into the actual relative differential sheaf. -/
def derivation : PresheafOfModulesOfCommRing.Derivation
    (relativeDifferentials R φ).val φ :=
  relativeDifferentialsHomEquiv R φ (relativeDifferentials R φ) (𝟙 _)

/-- The universal differential is exactly the original sheafification unit on the original `d`. -/
theorem derivation_d (X : Dᵒᵖ) (a : R.obj.obj X) :
    (derivation R φ).d a =
      (CategoryTheory.toSheafify J
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials
          φ).presheaf).app X
        ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation φ).d a) := rfl

/-- The Hom equivalence evaluates the original morphism on the original universal differential. -/
theorem relativeDifferentialsHomEquiv_apply (M : SheafOfModules.{u} Rᵣ)
    (k : relativeDifferentials R φ ⟶ M) (X : Dᵒᵖ) (a : R.obj.obj X) :
    (relativeDifferentialsHomEquiv R φ M k).d a =
      k.val.app X ((derivation R φ).d a) := rfl

/-- The original universal descent to the supplied module sheaf. -/
def desc (M : SheafOfModules.{u} Rᵣ)
    (d : PresheafOfModulesOfCommRing.Derivation M.val φ) :
    relativeDifferentials R φ ⟶ M := (relativeDifferentialsHomEquiv R φ M).symm d

/-- Universal descent retains the exact original derivation values. -/
theorem desc_d (M : SheafOfModules.{u} Rᵣ)
    (d : PresheafOfModulesOfCommRing.Derivation M.val φ)
    (X : Dᵒᵖ) (a : R.obj.obj X) :
    (desc R φ M d).val.app X ((derivation R φ).d a) = d.d a :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    ((relativeDifferentialsHomEquiv R φ M).apply_symm_apply d) a

/-- Canonical coercion form of `desc_d`
for simplification. -/
@[simp]
private theorem desc_d' (M : SheafOfModules.{u} Rᵣ)
    (d : PresheafOfModulesOfCommRing.Derivation M.val φ)
    (X : Dᵒᵖ) (a : R.obj.obj X) :
    let A : ModuleCat (R.obj.obj X) :=
      PresheafOfModulesOfCommRing.obj (R := R.obj) (relativeDifferentials R φ).val X
    let B : ModuleCat (R.obj.obj X) :=
      PresheafOfModulesOfCommRing.obj (R := R.obj) M.val X
    DFunLike.coe (F := A →ₗ[R.obj.obj X] B) (α := A) (β := fun _ => B)
      (PresheafOfModules.Hom.app' (R := R.obj) (desc R φ M d).val X).hom
      ((PresheafOfModulesOfCommRing.Derivation.d (R := R.obj) (X := X)
        (derivation R φ)) a) = d.d a := by
  exact desc_d R φ M d X a

/-- Actual morphisms out of the relative differential sheaf are determined by their `d` values. -/
@[ext]
theorem hom_ext (M : SheafOfModules.{u} Rᵣ) {k l : relativeDifferentials R φ ⟶ M}
    (h : ∀ (X : Dᵒᵖ) (a : R.obj.obj X),
      k.val.app X ((derivation R φ).d a) = l.val.app X ((derivation R φ).d a)) : k = l := by
  apply (relativeDifferentialsHomEquiv R φ M).injective
  ext X a
  exact h X a

/-- The universal equivalence is natural for the original coefficient morphisms. -/
theorem relativeDifferentialsHomEquiv_comp (M N : SheafOfModules.{u} Rᵣ)
    (k : relativeDifferentials R φ ⟶ M) (l : M ⟶ N) :
    relativeDifferentialsHomEquiv R φ N (k ≫ l) =
      (relativeDifferentialsHomEquiv R φ M k).postcomp l.val := by
  ext X a
  rfl

/-- Descent is compatible with the original coefficient postcomposition. -/
theorem desc_postcomp (M N : SheafOfModules.{u} Rᵣ)
    (d : PresheafOfModulesOfCommRing.Derivation M.val φ) (k : M ⟶ N) :
    desc R φ N (d.postcomp k.val) = desc R φ M d ≫ k := by
  apply hom_ext R φ N
  intro X a
  change (desc R φ N (d.postcomp k.val)).val.app X ((derivation R φ).d a) =
    k.val.app X ((desc R φ M d).val.app X ((derivation R φ).d a))
  rw [desc_d, desc_d]
  rfl

section Identity

variable {S' : Dᵒᵖ ⥤ CommRingCat.{u}} (ψ : S' ⟶ R.obj)
  [(PresheafOfModulesOfCommRing.pushforward.{u} (F := 𝟭 D) ψ).IsRightAdjoint]

/-- For the identity functor, this is the sheafification of the original native comparison. -/
def relativeDifferentialsIdIso : relativeDifferentials R (F := 𝟭 D) ψ ≅
    (PresheafOfModules.sheafification (𝟙 (Rᵣ).obj)).obj
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' ψ) :=
  (PresheafOfModules.sheafification (𝟙 (Rᵣ).obj)).mapIso
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentialsIdIso ψ)

/-- The identity comparison preserves the original sheafified differential. -/
theorem relativeDifferentialsIdIso_hom_d (X : Dᵒᵖ) (a : R.obj.obj X) :
    (relativeDifferentialsIdIso R ψ).hom.val.app X ((derivation R (F := 𝟭 D) ψ).d a) =
      (CategoryTheory.toSheafify J
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
          ψ).presheaf).app X
        ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' ψ).d a) := by
  let e := PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentialsIdIso ψ
  have H := congrArg (fun t => t.app X)
    (CategoryTheory.toSheafify_naturality (J := J)
      ((PresheafOfModules.toPresheaf (Rᵣ).obj).map e.hom))
  have H' := ConcreteCategory.congr_hom H
    ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation (F := 𝟭 D) ψ).d a)
  exact H'.symm.trans (congrArg
    ((CategoryTheory.toSheafify J
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        ψ).presheaf).app X)
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentialsIdIso_hom_d ψ X a))

/-- Canonical coercion form of `relativeDifferentialsIdIso_hom_d`
for simplification. -/
@[simp]
private theorem relativeDifferentialsIdIso_hom_d' (X : Dᵒᵖ) (a : R.obj.obj X) :
    let A : ModuleCat (R.obj.obj X) :=
      PresheafOfModulesOfCommRing.obj (R := R.obj)
        (relativeDifferentials R (F := 𝟭 D) ψ).val X
    let B : ModuleCat (R.obj.obj X) :=
      PresheafOfModulesOfCommRing.obj (R := R.obj)
        ((PresheafOfModules.sheafification (𝟙 (Rᵣ).obj)).obj
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' ψ)).val X
    DFunLike.coe (F := A →ₗ[R.obj.obj X] B) (α := A) (β := fun _ => B)
        (PresheafOfModules.Hom.app' (R := R.obj)
          (relativeDifferentialsIdIso R ψ).hom.val X).hom
        ((PresheafOfModulesOfCommRing.Derivation.d (R := R.obj) (X := X)
          (derivation R (F := 𝟭 D) ψ)) a) =
      (CategoryTheory.toSheafify J
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
          ψ).presheaf).app X
        ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' ψ).d a) := by
  exact relativeDifferentialsIdIso_hom_d R ψ X a

/-- The inverse identity comparison preserves the same original differential. -/
theorem relativeDifferentialsIdIso_inv_d (X : Dᵒᵖ) (a : R.obj.obj X) :
    (relativeDifferentialsIdIso R ψ).inv.val.app X
        ((CategoryTheory.toSheafify J
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
            ψ).presheaf).app X
          ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' ψ).d a)) =
      (derivation R (F := 𝟭 D) ψ).d a := by
  let e := PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentialsIdIso ψ
  have H := congrArg (fun t => t.app X)
    (CategoryTheory.toSheafify_naturality (J := J)
      ((PresheafOfModules.toPresheaf (Rᵣ).obj).map e.inv))
  have H' := ConcreteCategory.congr_hom H
    ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' ψ).d a)
  exact H'.symm.trans (congrArg
    ((CategoryTheory.toSheafify J
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials
        (F := 𝟭 D) ψ).presheaf).app X)
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentialsIdIso_inv_d ψ X a))

/-- Canonical coercion form of `relativeDifferentialsIdIso_inv_d`
for simplification. -/
@[simp]
private theorem relativeDifferentialsIdIso_inv_d' (X : Dᵒᵖ) (a : R.obj.obj X) :
    DFunLike.coe (F := _ →ₗ[R.obj.obj X] _)
        (PresheafOfModules.Hom.app' (R := R.obj)
          (relativeDifferentialsIdIso R ψ).inv.val X).hom
        (DFunLike.coe (F :=
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' ψ).obj X →+
            (CategoryTheory.sheafify J
              (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
                ψ).presheaf).obj X)
          ((CategoryTheory.toSheafify J
            (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
              ψ).presheaf).app X).hom
          ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' ψ).d a)) =
      (derivation R (F := 𝟭 D) ψ).d a := by
  exact relativeDifferentialsIdIso_inv_d R ψ X a

end Identity

end SheafOfModulesOfCommRing.DifferentialsConstruction
