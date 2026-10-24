/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure

/-!
# Injectivity of the original first cohomology map

The original first Leray arrow is injective from its single adjacent
vanishing. The existing original-map comparison identifies it with the
geometric coefficient map, for every specified structural ring action.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

/-- The standard derived category of module sheaves for the birational Leray comparison. -/
local instance birationalFirstSource (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- The standard derived category of `R`-modules for the original first cohomology map. -/
local instance birationalFirstTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private theorem mono_moduleBirationalLerayShortComplex_f
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    Mono (moduleBirationalLerayShortComplex X α g hX hff).f := by
  let T := moduleBirationalLerayTriangle X α g hX hff
  let G := Scheme.Modules.pushforward g
  let F := moduleGlobalSectionsFunctorOfHom X α
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let K := G.rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY)
  let P := (DerivedCategory.Plus.TStructure.t.truncGE 1).obj K
  let : P.IsGE 1 := DerivedCategory.Plus.TStructure.t.isGE_truncGE_obj K 1 1 le_rfl
  let : T.obj₃.IsGE 1 := by
    change (F.rightDerivedFunctorPlus.obj P).IsGE 1
    exact F.rightDerivedFunctorPlus_isGE P 1
  have h₀ : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
      T.obj₃) := DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃ 1 0 (by omega)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0
  change Mono ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 1).map T.mor₁)
  exact (H.homologySequence_mono_shift_map_mor₁_iff T
    (moduleBirationalLerayTriangle_distinguished X α g hX hff) 0 1 (by omega)).mpr
      (h₀.eq_of_src _ _)

/-- The original structural coefficient map is injective on degree-one
cohomology for a proper birational morphism to a normal integral scheme,
with the same specified structural ring actions on both cohomology groups. -/
theorem moduleCohomologyMapAlongLinear_unit_injective_of_isProper_birational
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    Function.Injective (moduleCohomologyMapAlongLinear g α
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let := moduleCohomologyModuleOfHom X α OX 1
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) OY 1
  let S := moduleBirationalLerayShortComplex X α g hX hff
  let : Mono S.f := mono_moduleBirationalLerayShortComplex_f X α g hX hff
  have hi : Function.Injective S.f := (ModuleCat.mono_iff_injective S.f).mp inferInstance
  let eX := moduleBirationalLeraySourceEquiv X α g hX hff
  let eY := moduleBirationalLerayMiddleEquiv X α g hX hff
  have hL : Function.Injective (moduleBirationalLerayMap X α g hX hff) := by
    intro x y hxy
    apply eX.symm.injective
    apply hi
    apply eY.injective
    exact (moduleBirationalLerayMap_apply X α g hX hff x).symm.trans
      (hxy.trans (moduleBirationalLerayMap_apply X α g hX hff y))
  exact (moduleBirationalLerayMap_eq_moduleCohomologyMapAlongLinear X α g hX hff) ▸ hL

end AlgebraicGeometry.Scheme.Cohomology
