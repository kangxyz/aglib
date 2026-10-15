/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorExact
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorExact.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 92]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Exact sheaf tensor with pulled-back finite-free retracts

The original sheafified tensor is viewed in the scheme module category, retaining
its actual coefficient maps. The original pullback of a finite-free retraction,
followed by the actual free-sheaf pullback comparison, supplies exact tensor
coefficients on the source scheme. No flatness assumption on the morphism is needed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModulesOfCommRing

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The original sheafified tensor, with the scheme module category as its domain and codomain. -/
def moduleTensorLeftFunctor (X : Scheme.{u}) (M : X.Modules) : X.Modules ⥤ X.Modules :=
  SheafOfModulesOfCommRing.tensorLeftFunctor X.sheaf M

/-- The original tensor is additive in the scheme module category. -/
instance moduleTensorLeftFunctor_additive (X : Scheme.{u}) (M : X.Modules) :
    (moduleTensorLeftFunctor X M).Additive :=
  tensorLeftFunctor_additive X.sheaf M

/-- The original coefficient tensor map, viewed in the scheme module category. -/
def moduleTensorCoefficientMap (X : Scheme.{u}) {M N : X.Modules} (f : M ⟶ N) :
    moduleTensorLeftFunctor X M ⟶ moduleTensorLeftFunctor X N :=
  (SheafOfModulesOfCommRing.tensorFunctor X.sheaf).map f

/-- The coefficient map retains the original sheafified tensor map in each component. -/
theorem moduleTensorCoefficientMap_app (X : Scheme.{u}) {M N : X.Modules}
    (f : M ⟶ N) (P : X.Modules) :
    (moduleTensorCoefficientMap X f).app P = ((SheafOfModulesOfCommRing.tensorFunctor
        X.sheaf).map f).app P := rfl

/-- The actual coefficient map preserves identity morphisms. -/
theorem moduleTensorCoefficientMap_id (X : Scheme.{u}) (M : X.Modules) :
    moduleTensorCoefficientMap X (𝟙 M) = 𝟙 (moduleTensorLeftFunctor X M) :=
  (SheafOfModulesOfCommRing.tensorFunctor X.sheaf).map_id M

/-- The actual coefficient map preserves composition of original module arrows. -/
theorem moduleTensorCoefficientMap_comp (X : Scheme.{u}) {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    moduleTensorCoefficientMap X (f ≫ g) =
      moduleTensorCoefficientMap X f ≫ moduleTensorCoefficientMap X g :=
  (SheafOfModulesOfCommRing.tensorFunctor X.sheaf).map_comp f g

/-- The original pullback of a finite-free retraction, with the actual free comparison. -/
def pullbackFiniteFreeRetract (f : X ⟶ Y) {M : Y.Modules} {I : Type u}
    (h : Retract M (SheafOfModules.free (R := Y.ringCatSheaf) I)) :
    Retract ((Scheme.Modules.pullback f).obj M)
      (SheafOfModules.free (R := X.ringCatSheaf) I) :=
  (h.map (Scheme.Modules.pullback f)).trans (Retract.ofIso (pullbackFreeIso f I))

/-- The inclusion is the original pulled-back inclusion followed by the actual free isomorphism. -/
theorem pullbackFiniteFreeRetract_i (f : X ⟶ Y) {M : Y.Modules} {I : Type u}
    (h : Retract M (SheafOfModules.free (R := Y.ringCatSheaf) I)) :
    (pullbackFiniteFreeRetract f h).i =
      (Scheme.Modules.pullback f).map h.i ≫ (pullbackFreeIso f I).hom := rfl

/-- The retraction is the actual free isomorphism inverse followed by the pulled-back retraction. -/
theorem pullbackFiniteFreeRetract_r (f : X ⟶ Y) {M : Y.Modules} {I : Type u}
    (h : Retract M (SheafOfModules.free (R := Y.ringCatSheaf) I)) :
    (pullbackFiniteFreeRetract f h).r =
      (pullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map h.r := rfl

/-- The original pullback of a finite-free retract gives an exact tensor coefficient. -/
theorem tensor_shortExact_pullback_finiteFreeRetract (f : X ⟶ Y)
    {M : Y.Modules} {I : Type u} [Finite I]
    (h : Retract M (SheafOfModules.free (R := Y.ringCatSheaf) I))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj M))).ShortExact :=
  tensor_shortExact_of_retract_finiteFree X.sheaf S hS I (pullbackFiniteFreeRetract f h)


/-- Tensoring module sheaves on `Z` on the right by `M`. -/
def moduleTensorRightFunctor (Z : Scheme.{u}) (M : Z.Modules) : Z.Modules ⥤ Z.Modules :=
  SheafOfModulesOfCommRing.tensorFunctor Z.sheaf ⋙ (evaluation _ _).obj M

theorem moduleTensorRightFunctor_map (Z : Scheme.{u}) (M : Z.Modules)
    {E E' : Z.Modules} (g : E ⟶ E') :
    (moduleTensorRightFunctor Z M).map g = (moduleTensorCoefficientMap Z g).app M := rfl

instance moduleTensorRightFunctor_additive (Z : Scheme.{u}) (M : Z.Modules) :
    (moduleTensorRightFunctor Z M).Additive := by
  change (SheafOfModulesOfCommRing.tensorFunctor Z.sheaf ⋙ (evaluation _ _).obj M).Additive
  infer_instance
end AlgebraicGeometry.Scheme.Modules
