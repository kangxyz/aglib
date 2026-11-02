/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorExact
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Objects
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

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})


/-- The existing site tensor object specialized to scheme module sheaves. -/
def tensorSheaf (M N : SheafOfModules.{u} X.ringCatSheaf) :
    SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModulesOfCommRing.tensorProduct X.sheaf M N

/-- The existing sheafified tensor map in both module arguments. -/
def tensorSheafMap {M M' N N' : SheafOfModules.{u} X.ringCatSheaf}
    (f : M ⟶ M') (g : N ⟶ N') : tensorSheaf X M N ⟶ tensorSheaf X M' N' :=
  SheafOfModulesOfCommRing.tensorMap X.sheaf f g

/-- Tensoring two actual module-sheaf isomorphisms. -/
def tensorSheafIso {M M' N N' : SheafOfModules.{u} X.ringCatSheaf}
    (e : M ≅ M') (f : N ≅ N') : tensorSheaf X M N ≅ tensorSheaf X M' N' := by
  letI : MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))
  exact (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (CategoryTheory.MonoidalCategory.tensorIso
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e)
      ((SheafOfModules.forget X.ringCatSheaf).mapIso f))

/-- The sheafification counit on the underlying presheaf of a module sheaf. -/
def sheafifyForgetIso (M : SheafOfModules.{u} X.ringCatSheaf) :
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M :=
  SheafOfModulesOfCommRing.sheafifyForgetIso X.sheaf M

/-- The canonical site left unitor, specialized to the scheme module category. -/
def tensorSheafLeftUnit (M : SheafOfModules.{u} X.ringCatSheaf) :
    tensorSheaf X (SheafOfModules.unit X.ringCatSheaf) M ≅ M :=
  (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app M

/-- The canonical site tensor braiding on scheme modules. -/
def tensorSheafBraiding (M N : SheafOfModules.{u} X.ringCatSheaf) :
    tensorSheaf X M N ≅ tensorSheaf X N M :=
  SheafOfModulesOfCommRing.tensorBraiding X.sheaf M N

/-- The original sheafification unit of the sectionwise tensor. -/
def tensorSheafUnit (M N : SheafOfModules.{u} X.ringCatSheaf) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶
      (tensorSheaf X M N).val :=
  SheafOfModulesOfCommRing.tensorUnitMap X.sheaf M N

/-- The original Scheme tensor is the actual generic sheafified tensor. -/
theorem tensorSheaf_eq_generic (M N : SheafOfModules.{u} X.ringCatSheaf) :
    tensorSheaf X M N = SheafOfModulesOfCommRing.tensorProduct X.sheaf M N := rfl

/-- The original Scheme tensor map is the actual generic two-variable map. -/
theorem tensorSheafMap_eq_generic {M M' N N' : SheafOfModules.{u} X.ringCatSheaf}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorSheafMap X f g = SheafOfModulesOfCommRing.tensorMap X.sheaf f g := rfl

/-- The original Scheme counit comparison is the actual generic counit isomorphism. -/
theorem sheafifyForgetIso_eq_generic (M : SheafOfModules.{u} X.ringCatSheaf) :
    sheafifyForgetIso X M = SheafOfModulesOfCommRing.sheafifyForgetIso X.sheaf M := rfl

/-- The original Scheme tensor unit map is the actual generic unit component. -/
theorem tensorSheafUnit_eq_generic (M N : SheafOfModules.{u} X.ringCatSheaf) :
    tensorSheafUnit X M N = SheafOfModulesOfCommRing.tensorUnitMap X.sheaf M N := rfl

variable {M M' M'' N N' N'' : SheafOfModules.{u} X.ringCatSheaf}

@[reassoc] theorem tensorSheafMap_comp (a : M ⟶ M') (b : N ⟶ N')
    (c : M' ⟶ M'') (d : N' ⟶ N'') :
    tensorSheafMap X a b ≫ tensorSheafMap X c d = tensorSheafMap X (a ≫ c) (b ≫ d) := by
  unfold tensorSheafMap
  rw [← Functor.map_comp]
  congr 1
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

@[reassoc] theorem tensorSheafUnit_naturality (a : M ⟶ M') (b : N ⟶ N') :
    tensorSheafUnit X M N ≫ (tensorSheafMap X a b).val =
      PresheafOfModulesOfCommRing.Monoidal.tensorHom a.val b.val ≫ tensorSheafUnit X M' N' :=
  ((_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality _).symm

theorem tensorSheafMap_tmul (a : M ⟶ M') (b : N ⟶ N')
    (U : X.Opensᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (tensorSheafMap X a b).val.app U ((tensorSheafUnit X M N).app U (m ⊗ₜ n)) =
      (tensorSheafUnit X M' N').app U (a.val.app U m ⊗ₜ b.val.app U n) :=
  congrArg (fun k ↦ k.app U (m ⊗ₜ n)) (tensorSheafUnit_naturality X a b)

end AlgebraicGeometry.Scheme.Modules
