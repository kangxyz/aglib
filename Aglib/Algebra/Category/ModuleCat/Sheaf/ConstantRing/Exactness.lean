/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Exactness consequences of the original constant-ring image comparisons

Local surjectivity proves preservation of epimorphisms by the actual
module-valued forgetful functor. The specified underlying comparisons then
transfer the original finite-limit and epi properties to native ringed images.
Injective preservation is obtained only for the genuine right adjoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ r w

section Valued

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ]
  [HasSheafify J (ModuleCat.{w} Λ)] [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{w} Λ))]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [Balanced (Sheaf J (ModuleCat.{w} Λ))] [Balanced (Sheaf J AddCommGrpCat.{w})]

/-- The original module-valued forgetting sends local surjections, and hence
epimorphisms, to epimorphisms of the same additive sheaves. -/
theorem moduleValuedForget_preservesEpimorphisms :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).PreservesEpimorphisms where
  preserves {M N} α hα := by
    have h : Sheaf.IsLocallySurjective α :=
      (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{w} Λ) α).mpr hα
    apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} _).mp
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight α.hom (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    exact (Presheaf.isLocallySurjective_iff_whisker_forget J α.hom).mp h

variable [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]

/-- The original additive sheaf of the native constant-ring module preserves
epimorphisms through its actual coefficient-equivalence comparison. -/
theorem moduleUnderlying_preservesEpimorphisms :
    (SheafOfModules.toSheaf.{w} (constantRing J Λ)).PreservesEpimorphisms := by
  let : (sheafCompose J
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).PreservesEpimorphisms :=
    moduleValuedForget_preservesEpimorphisms.{u₁, v₁, r, w} J Λ
  exact Functor.PreservesEpimorphisms.of_iso (moduleSheafInverseUnderlyingIso J Λ)

/-- The same underlying additive sheaf functor preserves the original
homology, without any assertion about injective objects. -/
theorem moduleUnderlying_preservesHomology :
    (SheafOfModules.toSheaf.{w} (constantRing J Λ)).PreservesHomology := by
  let : (SheafOfModules.toSheaf.{w} (constantRing J Λ)).PreservesEpimorphisms :=
    moduleUnderlying_preservesEpimorphisms.{u₁, v₁, r, w} J Λ
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

end Valued

section Images

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [K.WEqualsLocallyBijective RingCat.{r}]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
  [(forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
  [K.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

section InverseImage

variable [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)]

/-- The original underlying comparison transfers the supplied actual
additive inverse-image finite limits to the same native ringed pullback. -/
theorem moduleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ) := by
  let : PreservesFiniteLimits
      (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ ⋙
        SheafOfModules.toSheaf (constantRing K Λ)) :=
    preservesFiniteLimits_of_natIso
      (moduleInverseImageUnderlyingIso.{u₁, v₁, u₂, v₂, r, w} F J K Λ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ) (SheafOfModules.toSheaf (constantRing K Λ))

/-- Additivity is on the actual native inverse image. -/
theorem moduleInverseImage_additive :
    (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).Additive := by
  let : PreservesFiniteLimits (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ) :=
    moduleInverseImage_preservesFiniteLimits F J K Λ
  exact Functor.additive_of_preserves_binary_products _

local instance inverseImageAdditive :
    (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).Additive :=
  moduleInverseImage_additive F J K Λ

/-- The actual native inverse image preserves homology. -/
theorem moduleInverseImage_preservesHomology :
    (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).PreservesHomology := by
  let : (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).IsLeftAdjoint :=
    (moduleInverseImageAdjunction.{u₁, v₁, u₂, v₂, r, w} F J K Λ).isLeftAdjoint
  let : PreservesFiniteLimits (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ) :=
    moduleInverseImage_preservesFiniteLimits F J K Λ
  let : (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).Additive :=
    moduleInverseImage_additive F J K Λ
  infer_instance

/-- Injectives are preserved by the genuine right adjoint of this exact
left adjoint, never by coefficient forgetting. -/
theorem moduleDirectImage_preservesInjectiveObjects :
    (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).PreservesInjectiveObjects := by
  let : PreservesFiniteLimits (moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ) :=
    moduleInverseImage_preservesFiniteLimits F J K Λ
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleInverseImageAdjunction.{u₁, v₁, u₂, v₂, r, w} F J K Λ)

end InverseImage

end Images

section DirectImage

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]
  [K.WEqualsLocallyBijective RingCat.{r}]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [HasSheafify K (ModuleCat.{w} Λ)] [K.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [K.HasSheafCompose (CategoryTheory.forget (ModuleCat.{w} Λ))]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Balanced (Sheaf K (ModuleCat.{w} Λ))] [Balanced (Sheaf K AddCommGrpCat.{w})]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).PreservesEpimorphisms]

omit [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The original direct-image comparison transfers the supplied actual
additive epi property to native ringed direct image. -/
theorem moduleDirectImage_preservesEpimorphisms :
    (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).PreservesEpimorphisms := by
  let : (SheafOfModules.toSheaf.{w} (constantRing K Λ)).PreservesEpimorphisms :=
    moduleUnderlying_preservesEpimorphisms.{u₂, v₂, r, w} K Λ
  let : (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ ⋙
      SheafOfModules.toSheaf.{w} (constantRing J Λ)).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso
      (moduleDirectImageUnderlyingIso.{u₁, v₁, u₂, v₂, r, w} F J K Λ).symm
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ)
    (SheafOfModules.toSheaf.{w} (constantRing J Λ))

variable [(moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).IsRightAdjoint]

local instance directImageAdditive :
    (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The same genuine right adjoint and supplied epi property preserve
homology on the original native module categories. -/
theorem moduleDirectImage_preservesHomology :
    (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).PreservesHomology := by
  let : (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).PreservesEpimorphisms :=
    moduleDirectImage_preservesEpimorphisms F J K Λ
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

end DirectImage

end ModuleCat.Sheaf.ConstantRing
