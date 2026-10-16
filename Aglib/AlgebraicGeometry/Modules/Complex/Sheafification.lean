/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorAdditive
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive

/-!
# The sheafification counit on module-sheaf complexes

The degreewise counit identifies sheafification of the original underlying module
presheaf complex with the original complex. Component and naturality equations
retain the actual adjunction counit. Additivity reuses the existing generic
`SheafOfModulesOfCommRing.associatedSheaf_additive` instance for `X.sheaf`.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/BoundedFlatReplacement.lean`.
SHA-256: `89f8b7540cf9edfc643c2cf03ce76ad70df2b026f31822b17721c6958f85f897`.
Selected source lines: 47–66.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/BoundedFlatModels.lean`.
SHA-256: `e77b85f102e65c7a29202c2987969b58fb7bcc0d24d02e1ac2bba97b0a728ecd`.
Selected source lines: 110–120.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual sheafification counit, on cochain complexes. -/
def sheafificationComplexCounitIso (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app (K.X n)))
    (fun i j _ => ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality (K.d i j)).symm)

/-- The replacement counit has the original sheafification counit in every degree. -/
@[simp]
theorem sheafificationComplexCounitIso_hom_f (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (sheafificationComplexCounitIso X K).hom.f n =
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app (K.X n) :=
  rfl

/-- Naturality of the actual sheafification counit on complexes. -/
theorem sheafificationComplexCounitIso_naturality {X : Scheme.{u}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex (.up ℤ)).map
      (((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
        (.up ℤ)).map f) ≫ (sheafificationComplexCounitIso X L).hom =
      (sheafificationComplexCounitIso X K).hom ≫ f := by
  ext n : 1
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality
    (f.f n)

end AlgebraicGeometry.Scheme.Modules
