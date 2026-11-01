/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric
public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Naturality
public import Aglib.AlgebraicGeometry.Modules.Pullback.StalkUnit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Aglib.AlgebraicGeometry.Stalk.Product
public import Aglib.Algebra.Module.TensorProduct.External
public import Aglib.AlgebraicGeometry.Modules.Stalk.Exactness
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The original external tensor of scheme module sheaves

The bifunctor is the original sheaf tensor after the two original geometric
pullbacks. Its unit comparisons and stalk comparison retain the same native
maps. No exactness of arbitrary internal sheaf tensor is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The literal external tensor bifunctor on the actual fibre product. -/
def externalTensor : X.Modules ⥤ Y.Modules ⥤ (Limits.pullback f g : Scheme).Modules :=
  Scheme.Modules.pullback (Limits.pullback.fst f g) ⋙
    curriedTensor (Limits.pullback f g : Scheme).Modules ⋙
      (Functor.whiskeringLeft Y.Modules (Limits.pullback f g : Scheme).Modules
        (Limits.pullback f g : Scheme).Modules).obj
          (Scheme.Modules.pullback (Limits.pullback.snd f g))

/-- The external tensor object is the original tensor of the two original pullbacks. -/
theorem externalTensor_obj (M : X.Modules) (N : Y.Modules) :
    ((externalTensor f g).obj M).obj N =
      (Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M ⊗
        (Scheme.Modules.pullback (Limits.pullback.snd f g)).obj N := rfl

/-- Its first-variable map is the original tensor coefficient map. -/
theorem externalTensor_map_app {M M' : X.Modules} (a : M ⟶ M') (N : Y.Modules) :
    ((externalTensor f g).map a).app N =
      (Scheme.Modules.pullback (Limits.pullback.fst f g)).map a ▷
        (Scheme.Modules.pullback (Limits.pullback.snd f g)).obj N := rfl

/-- Its second-variable map is the original tensor functor map. -/
theorem externalTensor_obj_map (M : X.Modules) {N N' : Y.Modules} (b : N ⟶ N') :
    ((externalTensor f g).obj M).map b =
      (Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M ◁
        (Scheme.Modules.pullback (Limits.pullback.snd f g)).map b := rfl

instance externalTensor_additive : (externalTensor f g).Additive := by
  unfold externalTensor
  infer_instance

instance externalTensor_obj_additive (M : X.Modules) :
    ((externalTensor f g).obj M).Additive := by
  change (Scheme.Modules.pullback (Limits.pullback.snd f g) ⋙
    tensorLeft ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M)).Additive
  infer_instance

instance externalTensor_flip_obj_additive (N : Y.Modules) :
    ((externalTensor f g).flip.obj N).Additive where
  map_add {M M'} {a b} :=
    congrArg (fun t : (externalTensor f g).obj M ⟶ (externalTensor f g).obj M' => t.app N)
      ((externalTensor f g).map_add (f := a) (g := b))

/-- The original pullback-unit and tensor left-unit isomorphisms identify
external tensor with the first structure module with the second projection pullback. -/
def externalTensorLeftUnitIso :
    (externalTensor f g).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      Scheme.Modules.pullback (Limits.pullback.snd f g) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback (Limits.pullback.snd f g))
      ((curriedTensor (Limits.pullback f g : Scheme).Modules).mapIso
          (pullbackUnitIso (Limits.pullback.fst f g)) ≪≫
        leftUnitorNatIso (Limits.pullback f g : Scheme).Modules) ≪≫
    Functor.rightUnitor _

/-- The original pullback-unit and tensor right-unit isomorphisms identify
external tensor with the second structure module with the first projection pullback. -/
def externalTensorRightUnitIso :
    (externalTensor f g).flip.obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      Scheme.Modules.pullback (Limits.pullback.fst f g) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback (Limits.pullback.fst f g))
      ((curriedTensor (Limits.pullback f g : Scheme).Modules).flip.mapIso
          (pullbackUnitIso (Limits.pullback.snd f g)) ≪≫
        rightUnitorNatIso (Limits.pullback f g : Scheme).Modules) ≪≫
    Functor.rightUnitor _

/-- The left unit comparison uses exactly the original pullback-unit map and unitor. -/
theorem externalTensorLeftUnitIso_hom_app (N : Y.Modules) :
    (externalTensorLeftUnitIso f g).hom.app N =
      (pullbackUnitIso (Limits.pullback.fst f g)).hom ▷
          (Scheme.Modules.pullback (Limits.pullback.snd f g)).obj N ≫
        (λ_ ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj N)).hom := by
  simp only [externalTensorLeftUnitIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.mapIso_hom,
    curriedTensor_map_app, leftUnitorNatIso_hom_app, Functor.rightUnitor_hom_app]
  exact Category.comp_id _

/-- The right unit comparison uses exactly the original pullback-unit map and unitor. -/
theorem externalTensorRightUnitIso_hom_app (M : X.Modules) :
    (externalTensorRightUnitIso f g).hom.app M =
      (Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M ◁
          (pullbackUnitIso (Limits.pullback.snd f g)).hom ≫
        (ρ_ ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M)).hom := by
  simp only [externalTensorRightUnitIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.mapIso_hom,
    Functor.flip_map_app, curriedTensor_obj_map, rightUnitorNatIso_hom_app,
    Functor.rightUnitor_hom_app]
  exact Category.comp_id _

/-- The original external tensor stalk is the tensor of the original two
scalar-extension stalks, through the existing tensor and pullback comparisons. -/
def externalTensorStalkIso (z : (Limits.pullback f g : Scheme)) (M : X.Modules) (N : Y.Modules) :
    (moduleStalk (Limits.pullback f g) z).obj (((externalTensor f g).obj M).obj N) ≅
      (ModuleCat.extendScalars ((Limits.pullback.fst f g).stalkMap z).hom).obj
          ((moduleStalk X (Limits.pullback.fst f g z)).obj M) ⊗
        (ModuleCat.extendScalars ((Limits.pullback.snd f g).stalkMap z).hom).obj
          ((moduleStalk Y (Limits.pullback.snd f g z)).obj N) :=
  moduleTensorStalkIso (Limits.pullback f g) z
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M)
      ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj N) ≪≫
    tensorIso ((pullbackModuleStalkIso (Limits.pullback.fst f g) z).app M)
      ((pullbackModuleStalkIso (Limits.pullback.snd f g) z).app N)

/-- Whole first-variable naturality of the original external tensor stalk comparison. -/
theorem externalTensorStalkIso_naturality_left (z : (Limits.pullback f g : Scheme))
    {M M' : X.Modules} (a : M ⟶ M') (N : Y.Modules) :
    (moduleStalk (Limits.pullback f g) z).map (((externalTensor f g).map a).app N) ≫
        (externalTensorStalkIso f g z M' N).hom =
      (externalTensorStalkIso f g z M N).hom ≫
        ((ModuleCat.extendScalars ((Limits.pullback.fst f g).stalkMap z).hom).map
            ((moduleStalk X (Limits.pullback.fst f g z)).map a) ⊗ₘ
          𝟙 ((ModuleCat.extendScalars ((Limits.pullback.snd f g).stalkMap z).hom).obj
            ((moduleStalk Y (Limits.pullback.snd f g z)).obj N))) := by
  let p := Limits.pullback.fst f g
  let q := Limits.pullback.snd f g
  let Z : Scheme := Limits.pullback f g
  simp only [externalTensorStalkIso, Iso.trans_hom, tensorIso_hom, Category.assoc]
  change (moduleStalk Z z).map
      ((moduleTensorCoefficientMap Z ((Scheme.Modules.pullback p).map a)).app
        ((Scheme.Modules.pullback q).obj N)) ≫
      (moduleTensorStalkIso Z z ((Scheme.Modules.pullback p).obj M')
        ((Scheme.Modules.pullback q).obj N)).hom ≫
          ((pullbackModuleStalkIso p z).hom.app M' ⊗ₘ
            (pullbackModuleStalkIso q z).hom.app N) =
    (moduleTensorStalkIso Z z ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullback q).obj N)).hom ≫
        ((pullbackModuleStalkIso p z).hom.app M ⊗ₘ
          (pullbackModuleStalkIso q z).hom.app N) ≫ _
  rw [← Category.assoc, moduleTensorStalkIso_naturality_left, Category.assoc]
  apply congrArg (fun h =>
    (moduleTensorStalkIso Z z ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullback q).obj N)).hom ≫ h)
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  erw [Category.comp_id]
  exact congrArg (fun h => h ⊗ₘ (pullbackModuleStalkIso q z).hom.app N)
    ((pullbackModuleStalkIso p z).hom.naturality a)

/-- Whole second-variable naturality of the original external tensor stalk comparison. -/
theorem externalTensorStalkIso_naturality_right (z : (Limits.pullback f g : Scheme))
    (M : X.Modules) {N N' : Y.Modules} (b : N ⟶ N') :
    (moduleStalk (Limits.pullback f g) z).map (((externalTensor f g).obj M).map b) ≫
        (externalTensorStalkIso f g z M N').hom =
      (externalTensorStalkIso f g z M N).hom ≫
        (𝟙 ((ModuleCat.extendScalars ((Limits.pullback.fst f g).stalkMap z).hom).obj
            ((moduleStalk X (Limits.pullback.fst f g z)).obj M)) ⊗ₘ
          (ModuleCat.extendScalars ((Limits.pullback.snd f g).stalkMap z).hom).map
            ((moduleStalk Y (Limits.pullback.snd f g z)).map b)) := by
  let p := Limits.pullback.fst f g
  let q := Limits.pullback.snd f g
  let Z : Scheme := Limits.pullback f g
  simp only [externalTensorStalkIso, Iso.trans_hom, tensorIso_hom, Category.assoc]
  change (moduleStalk Z z).map
      ((moduleTensorLeftFunctor Z ((Scheme.Modules.pullback p).obj M)).map
        ((Scheme.Modules.pullback q).map b)) ≫
      (moduleTensorStalkIso Z z ((Scheme.Modules.pullback p).obj M)
        ((Scheme.Modules.pullback q).obj N')).hom ≫
          ((pullbackModuleStalkIso p z).hom.app M ⊗ₘ
            (pullbackModuleStalkIso q z).hom.app N') =
    (moduleTensorStalkIso Z z ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullback q).obj N)).hom ≫
        ((pullbackModuleStalkIso p z).hom.app M ⊗ₘ
          (pullbackModuleStalkIso q z).hom.app N) ≫ _
  rw [← Category.assoc, moduleTensorStalkIso_naturality_right, Category.assoc]
  apply congrArg (fun h =>
    (moduleTensorStalkIso Z z ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullback q).obj N)).hom ≫ h)
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  erw [Category.comp_id]
  exact congrArg (fun h => (pullbackModuleStalkIso p z).hom.app M ⊗ₘ h)
    ((pullbackModuleStalkIso q z).hom.naturality b)

/-- The whole original second-variable stalk functor comparison. -/
def externalTensorLeftStalkIso (z : (Limits.pullback f g : Scheme)) (M : X.Modules) :
    (externalTensor f g).obj M ⋙ moduleStalk (Limits.pullback f g) z ≅
      moduleStalk Y (Limits.pullback.snd f g z) ⋙
        ModuleCat.extendScalars ((Limits.pullback.snd f g).stalkMap z).hom ⋙
          tensorLeft ((ModuleCat.extendScalars ((Limits.pullback.fst f g).stalkMap z).hom).obj
            ((moduleStalk X (Limits.pullback.fst f g z)).obj M)) :=
  NatIso.ofComponents (fun N => externalTensorStalkIso f g z M N)
    (fun b => by
      simpa only [Functor.comp_map, Functor.comp_obj, tensorLeft,
        curriedTensor_obj_obj, curriedTensor_obj_map, MonoidalCategory.id_tensorHom] using
        externalTensorStalkIso_naturality_right f g z M b)

/-- The whole original first-variable stalk functor comparison. -/
def externalTensorRightStalkIso (z : (Limits.pullback f g : Scheme)) (N : Y.Modules) :
    (externalTensor f g).flip.obj N ⋙ moduleStalk (Limits.pullback f g) z ≅
      moduleStalk X (Limits.pullback.fst f g z) ⋙
        ModuleCat.extendScalars ((Limits.pullback.fst f g).stalkMap z).hom ⋙
          tensorRight ((ModuleCat.extendScalars ((Limits.pullback.snd f g).stalkMap z).hom).obj
            ((moduleStalk Y (Limits.pullback.snd f g z)).obj N)) :=
  NatIso.ofComponents (fun M => externalTensorStalkIso f g z M N)
    (fun a => by
      simpa only [Functor.comp_map, Functor.comp_obj, tensorRight,
        Functor.flip_obj_obj, Functor.flip_obj_map, curriedTensor_obj_obj,
        curriedTensor_map_app, MonoidalCategory.tensorHom_id] using
        externalTensorStalkIso_naturality_left f g z a N)

private theorem unit_comparisons_eq {C : Type*} [Category* C] [MonoidalCategory C]
    {A B : C} (e : A ≅ 𝟙_ C) (d : B ≅ 𝟙_ C) :
    (e.hom ▷ B) ≫ (λ_ B).hom ≫ d.hom =
      (A ◁ d.hom) ≫ (ρ_ A).hom ≫ e.hom := by
  calc
    _ = (e.hom ⊗ₘ d.hom) ≫ (λ_ (𝟙_ C)).hom := by
      rw [← MonoidalCategory.leftUnitor_naturality, ← Category.assoc,
        ← MonoidalCategory.tensorHom_def]
    _ = (e.hom ⊗ₘ d.hom) ≫ (ρ_ (𝟙_ C)).hom := by rw [unitors_equal]
    _ = _ := by
      rw [← MonoidalCategory.rightUnitor_naturality, ← Category.assoc,
        ← MonoidalCategory.tensorHom_def']

/-- The two original external-unit comparisons agree at the two structure
modules, through the actual tensor unitors and pullback-unit maps. -/
theorem externalTensor_unit_comparisons_eq :
    (externalTensorLeftUnitIso f g).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pullbackUnitIso (Limits.pullback.snd f g)).hom =
      (externalTensorRightUnitIso f g).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (pullbackUnitIso (Limits.pullback.fst f g)).hom := by
  simpa only [externalTensorLeftUnitIso_hom_app, externalTensorRightUnitIso_hom_app,
    Category.assoc] using
      unit_comparisons_eq (pullbackUnitIso (Limits.pullback.fst f g))
        (pullbackUnitIso (Limits.pullback.snd f g))

/-- One canonical comparison of the external tensor of the two structure
modules with the original structure module on the actual fibre product. -/
def externalTensorUnitIso :
    ((externalTensor f g).obj (SheafOfModules.unit X.ringCatSheaf)).obj
        (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit (Limits.pullback f g : Scheme).ringCatSheaf :=
  (externalTensorLeftUnitIso f g).app (SheafOfModules.unit Y.ringCatSheaf) ≪≫
    pullbackUnitIso (Limits.pullback.snd f g)

/-- The same canonical unit comparison has the original right-unit formula. -/
theorem externalTensorUnitIso_hom_eq_right :
    (externalTensorUnitIso f g).hom =
      (externalTensorRightUnitIso f g).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (pullbackUnitIso (Limits.pullback.fst f g)).hom :=
  externalTensor_unit_comparisons_eq f g

section Field

variable {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (ρ : Y ⟶ Spec (.of k))

private theorem externalTensor_stalk_exact_right
    (z : (Limits.pullback π ρ : Scheme)) (M : X.Modules)
    (T : ShortComplex Y.Modules) (hT : T.Exact) :
    (T.map (moduleStalk Y (Limits.pullback.snd π ρ z) ⋙
      ModuleCat.extendScalars ((Limits.pullback.snd π ρ).stalkMap z).hom ⋙
        tensorLeft ((ModuleCat.extendScalars ((Limits.pullback.fst π ρ).stalkMap z).hom).obj
          ((moduleStalk X (Limits.pullback.fst π ρ z)).obj M)))).Exact := by
  let x := Limits.pullback.fst π ρ z
  let y := Limits.pullback.snd π ρ z
  let A : CommRingCat := X.presheaf.stalk x
  let B : CommRingCat := Y.presheaf.stalk y
  let C : CommRingCat := (Limits.pullback π ρ : Scheme).presheaf.stalk z
  let α : k →+* A := π.stalkScalar x
  let β : k →+* B := ρ.stalkScalar y
  let γ : k →+* C := (Limits.pullback.fst π ρ ≫ π).stalkScalar z
  let a : A →+* C := ((Limits.pullback.fst π ρ).stalkMap z).hom
  let b : B →+* C := ((Limits.pullback.snd π ρ).stalkMap z).hom
  let := α.toAlgebra
  let := β.toAlgebra
  let := γ.toAlgebra
  let := a.toAlgebra
  let := b.toAlgebra
  have hγα : γ = a.comp α := Scheme.Hom.stalkScalar_comp (Limits.pullback.fst π ρ) π z
  have hγβ : γ = b.comp β := by
    dsimp only [γ, b, β, y]
    rw [Limits.pullback.condition, Scheme.Hom.stalkScalar_comp]
  have : IsScalarTower k A C :=
    IsScalarTower.of_algebraMap_eq (fun r => congrArg (fun h : k →+* C => h r) hγα)
  have : IsScalarTower k B C :=
    IsScalarTower.of_algebraMap_eq (fun r => congrArg (fun h : k →+* C => h r) hγβ)
  let E := (moduleStalk X x).obj M
  let N₁ := (moduleStalk Y y).obj T.X₁
  let N₂ := (moduleStalk Y y).obj T.X₂
  let N₃ := (moduleStalk Y y).obj T.X₃
  let : Module k E := Module.compHom E α
  let : Module k N₁ := Module.compHom N₁ β
  let : Module k N₂ := Module.compHom N₂ β
  let : Module k N₃ := Module.compHom N₃ β
  have : IsScalarTower k A E := ⟨fun r s m => mul_smul (α r) s m⟩
  have : IsScalarTower k B N₁ := ⟨fun r s m => mul_smul (β r) s m⟩
  have : IsScalarTower k B N₂ := ⟨fun r s m => mul_smul (β r) s m⟩
  have : IsScalarTower k B N₃ := ⟨fun r s m => mul_smul (β r) s m⟩
  have hscalar : (TensorProduct.External.scalarMap (R := k) (A := A) (B := B) C).toRingHom =
      Scheme.Pullback.stalkTensorMap π ρ z := rfl
  have hC : (TensorProduct.External.scalarMap (R := k) (A := A) (B := B) C).toRingHom.Flat := by
    rw [hscalar]
    exact Scheme.Pullback.stalkTensorMap_flat π ρ z
  have hN : Function.Exact ((moduleStalk Y y).map T.f).hom ((moduleStalk Y y).map T.g).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hT.map (moduleStalk Y y))
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact
    (TensorProduct.map (LinearMap.id : C ⊗[A] E →ₗ[C] C ⊗[A] E)
      (((moduleStalk Y y).map T.f).hom.baseChange C))
    (TensorProduct.map (LinearMap.id : C ⊗[A] E →ₗ[C] C ⊗[A] E)
      (((moduleStalk Y y).map T.g).hom.baseChange C))
  exact TensorProduct.External.baseChange_exact_right k B E N₁ A C hC
    ((moduleStalk Y y).map T.f).hom ((moduleStalk Y y).map T.g).hom hN

/-- Over a field, the original external tensor preserves exact complexes
in its second variable. Arbitrary module sheaves are allowed. -/
theorem externalTensor_obj_map_exact (M : X.Modules) (T : ShortComplex Y.Modules)
    (hT : T.Exact) : (T.map ((externalTensor π ρ).obj M)).Exact := by
  apply exact_of_moduleStalk
  intro z
  change (T.map (((externalTensor π ρ).obj M) ⋙ moduleStalk (Limits.pullback π ρ) z)).Exact
  exact ShortComplex.exact_of_iso (T.mapNatIso (externalTensorLeftStalkIso π ρ z M)).symm
    (externalTensor_stalk_exact_right π ρ z M T hT)

/-- The same original second-variable functor preserves homology over a field. -/
instance externalTensor_obj_preservesHomology (M : X.Modules) :
    ((externalTensor π ρ).obj M).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (externalTensor_obj_map_exact π ρ M)

instance externalTensor_obj_preservesFiniteLimits (M : X.Modules) :
    PreservesFiniteLimits ((externalTensor π ρ).obj M) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance externalTensor_obj_preservesFiniteColimits (M : X.Modules) :
    PreservesFiniteColimits ((externalTensor π ρ).obj M) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

private theorem externalTensor_stalk_exact_left
    (z : (Limits.pullback π ρ : Scheme)) (N : Y.Modules)
    (T : ShortComplex X.Modules) (hT : T.Exact) :
    (T.map (moduleStalk X (Limits.pullback.fst π ρ z) ⋙
      ModuleCat.extendScalars ((Limits.pullback.fst π ρ).stalkMap z).hom ⋙
        tensorRight ((ModuleCat.extendScalars ((Limits.pullback.snd π ρ).stalkMap z).hom).obj
          ((moduleStalk Y (Limits.pullback.snd π ρ z)).obj N)))).Exact := by
  let x := Limits.pullback.fst π ρ z
  let y := Limits.pullback.snd π ρ z
  let A : CommRingCat := X.presheaf.stalk x
  let B : CommRingCat := Y.presheaf.stalk y
  let C : CommRingCat := (Limits.pullback π ρ : Scheme).presheaf.stalk z
  let α : k →+* A := π.stalkScalar x
  let β : k →+* B := ρ.stalkScalar y
  let γ : k →+* C := (Limits.pullback.fst π ρ ≫ π).stalkScalar z
  let a : A →+* C := ((Limits.pullback.fst π ρ).stalkMap z).hom
  let b : B →+* C := ((Limits.pullback.snd π ρ).stalkMap z).hom
  let := α.toAlgebra
  let := β.toAlgebra
  let := γ.toAlgebra
  let := a.toAlgebra
  let := b.toAlgebra
  have hγα : γ = a.comp α := Scheme.Hom.stalkScalar_comp (Limits.pullback.fst π ρ) π z
  have hγβ : γ = b.comp β := by
    dsimp only [γ, b, β, y]
    rw [Limits.pullback.condition, Scheme.Hom.stalkScalar_comp]
  have : IsScalarTower k A C :=
    IsScalarTower.of_algebraMap_eq (fun r => congrArg (fun h : k →+* C => h r) hγα)
  have : IsScalarTower k B C :=
    IsScalarTower.of_algebraMap_eq (fun r => congrArg (fun h : k →+* C => h r) hγβ)
  let E := (moduleStalk Y y).obj N
  let M₁ := (moduleStalk X x).obj T.X₁
  let M₂ := (moduleStalk X x).obj T.X₂
  let M₃ := (moduleStalk X x).obj T.X₃
  let : Module k E := Module.compHom E β
  let : Module k M₁ := Module.compHom M₁ α
  let : Module k M₂ := Module.compHom M₂ α
  let : Module k M₃ := Module.compHom M₃ α
  have : IsScalarTower k B E := ⟨fun r s m => mul_smul (β r) s m⟩
  have : IsScalarTower k A M₁ := ⟨fun r s m => mul_smul (α r) s m⟩
  have : IsScalarTower k A M₂ := ⟨fun r s m => mul_smul (α r) s m⟩
  have : IsScalarTower k A M₃ := ⟨fun r s m => mul_smul (α r) s m⟩
  have hscalar : (TensorProduct.External.scalarMap (R := k) (A := A) (B := B) C).toRingHom =
      Scheme.Pullback.stalkTensorMap π ρ z := rfl
  have hC : (TensorProduct.External.scalarMap (R := k) (A := A) (B := B) C).toRingHom.Flat := by
    rw [hscalar]
    exact Scheme.Pullback.stalkTensorMap_flat π ρ z
  have hM : Function.Exact ((moduleStalk X x).map T.f).hom ((moduleStalk X x).map T.g).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hT.map (moduleStalk X x))
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact
    (TensorProduct.map (((moduleStalk X x).map T.f).hom.baseChange C)
      (LinearMap.id : C ⊗[B] E →ₗ[C] C ⊗[B] E))
    (TensorProduct.map (((moduleStalk X x).map T.g).hom.baseChange C)
      (LinearMap.id : C ⊗[B] E →ₗ[C] C ⊗[B] E))
  exact TensorProduct.External.baseChange_exact_left k B M₁ E A C hC
    ((moduleStalk X x).map T.f).hom ((moduleStalk X x).map T.g).hom hM

/-- Over a field, the original external tensor also preserves exact
complexes in its first variable, for arbitrary module sheaves. -/
theorem externalTensor_flip_obj_map_exact (N : Y.Modules) (T : ShortComplex X.Modules)
    (hT : T.Exact) : (T.map ((externalTensor π ρ).flip.obj N)).Exact := by
  apply exact_of_moduleStalk
  intro z
  change (T.map (((externalTensor π ρ).flip.obj N) ⋙ moduleStalk (Limits.pullback π ρ) z)).Exact
  exact ShortComplex.exact_of_iso (T.mapNatIso (externalTensorRightStalkIso π ρ z N)).symm
    (externalTensor_stalk_exact_left π ρ z N T hT)

instance externalTensor_flip_obj_preservesHomology (N : Y.Modules) :
    ((externalTensor π ρ).flip.obj N).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (externalTensor_flip_obj_map_exact π ρ N)

instance externalTensor_flip_obj_preservesFiniteLimits (N : Y.Modules) :
    PreservesFiniteLimits ((externalTensor π ρ).flip.obj N) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance externalTensor_flip_obj_preservesFiniteColimits (N : Y.Modules) :
    PreservesFiniteColimits ((externalTensor π ρ).flip.obj N) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Field

end AlgebraicGeometry.Scheme.Modules
