/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.StalkUnit
public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Naturality
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk
public import Aglib.Algebra.Category.ModuleCat.Tensor.ScalarExtension
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Basic

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/ProjectionFormulaStalk.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 125]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The original projection-formula arrow on actual image stalks

The two comparison isomorphisms retain the actual scalar actions. The
original projection arrow is identified with the ordinary scalar-extension
tensor unit map, rather than replaced by an unrelated isomorphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Topology
open scoped TensorProduct ChangeOfRings

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The source of the original projection arrow at an actual image point. -/
def projectionFormulaStalkSourceIso {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f)
    (x : X) (E : Y.Modules) (M : X.Modules) :
    (moduleStalk Y (f x)).obj
        ((moduleTensorLeftFunctor Y E).obj ((Scheme.Modules.pushforward f).obj M)) ≅
      (moduleStalk Y (f x)).obj E ⊗
        (ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj M) :=
  moduleTensorStalkIso Y (f x) E ((Scheme.Modules.pushforward f).obj M) ≪≫
    (tensorLeft ((moduleStalk Y (f x)).obj E)).mapIso
      ((pushforwardModuleStalkIso f hf x).app M)

/-- The target of the original projection arrow at an actual image point. -/
def projectionFormulaStalkTargetIso {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f)
    (x : X) (E : Y.Modules) (M : X.Modules) :
    (moduleStalk Y (f x)).obj ((Scheme.Modules.pushforward f).obj
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M)) ≅
      (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((ModuleCat.extendScalars (f.stalkMap x).hom).obj ((moduleStalk Y (f x)).obj E) ⊗
          (moduleStalk X x).obj M) :=
  (pushforwardModuleStalkIso f hf x).app _ ≪≫
    (ModuleCat.restrictScalars (f.stalkMap x).hom).mapIso
      (moduleTensorStalkIso X x ((Scheme.Modules.pullback f).obj E) M) ≪≫
    (ModuleCat.restrictScalars (f.stalkMap x).hom).mapIso
      ((tensorRight ((moduleStalk X x).obj M)).mapIso ((pullbackModuleStalkIso f x).app E))

/-- The source comparison sends an original pure-section germ to the unchanged germs. -/
theorem projectionFormulaStalkSourceIso_germ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsInducing f) (x : X) (E : Y.Modules) (M : X.Modules)
    (U : Y.Opens) (hx : f x ∈ U) (e : Γ(E, U)) (m : Γ(M, f ⁻¹ᵁ U)) :
    (projectionFormulaStalkSourceIso f hf x E M).hom
        (((moduleTensorLeftFunctor Y E).obj ((Scheme.Modules.pushforward f).obj M)).presheaf.germ
          U (f x) hx (moduleTensorSection Y E ((Scheme.Modules.pushforward f).obj M) U e m)) =
      E.presheaf.germ U (f x) hx e ⊗ₜ[Y.presheaf.stalk (f x)]
        (show (ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj M) from
          M.presheaf.germ (f ⁻¹ᵁ U) x hx m) := by
  change (𝟙 ((moduleStalk Y (f x)).obj E) ⊗ₘ pushforwardModuleStalkMap f x M)
    ((moduleTensorStalkIso Y (f x) E ((Scheme.Modules.pushforward f).obj M)).hom _) = _
  rw [moduleTensorStalkIso_hom_germ, ModuleCat.MonoidalCategory.tensorHom_tmul,
    pushforwardModuleStalkMap_germ]
  rfl

/-- The target comparison preserves the original geometric unit germ and both tensor germs. -/
theorem projectionFormulaStalkTargetIso_unit_germ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsInducing f) (x : X) (E : Y.Modules) (M : X.Modules)
    (U : Y.Opens) (hx : f x ∈ U) (e : Γ(E, U)) (m : Γ(M, f ⁻¹ᵁ U)) :
    (projectionFormulaStalkTargetIso f hf x E M).hom
        (((Scheme.Modules.pushforward f).obj
          ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M)).presheaf.germ
            U (f x) hx (moduleTensorSection X ((Scheme.Modules.pullback f).obj E) M (f ⁻¹ᵁ U)
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app U e) m)) =
      ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x),(f.stalkMap x).hom]
        E.presheaf.germ U (f x) hx e) ⊗ₜ[X.presheaf.stalk x]
          M.presheaf.germ (f ⁻¹ᵁ U) x hx m := by
  change (((pullbackModuleStalkIso f x).hom.app E) ⊗ₘ 𝟙 ((moduleStalk X x).obj M))
    ((moduleTensorStalkIso X x ((Scheme.Modules.pullback f).obj E) M).hom
      (pushforwardModuleStalkMap f x
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M) _)) = _
  rw [pushforwardModuleStalkMap_germ, moduleTensorStalkIso_hom_germ,
    ModuleCat.MonoidalCategory.tensorHom_tmul, pullbackModuleStalkIso_unit_germ]
  rfl

/-- The original projection arrow is the canonical scalar-extension tensor unit on image stalks. -/
theorem projectionFormulaMap_stalk_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsInducing f) (x : X) (E : Y.Modules) (M : X.Modules) :
    (moduleStalk Y (f x)).map (projectionFormulaMap f E M) ≫
        (projectionFormulaStalkTargetIso f hf x E M).hom =
      (projectionFormulaStalkSourceIso f hf x E M).hom ≫
        (ModuleCat.scalarExtensionTensorIso (f.stalkMap x).hom
          ((moduleStalk Y (f x)).obj E) ((moduleStalk X x).obj M)).inv := by
  apply moduleTensorStalk_hom_ext Y (f x) E ((Scheme.Modules.pushforward f).obj M)
  intro U hx e m
  change (projectionFormulaStalkTargetIso f hf x E M).hom
      ((moduleStalk Y (f x)).map (projectionFormulaMap f E M)
        (((moduleTensorLeftFunctor Y E).obj ((Scheme.Modules.pushforward f).obj M)).presheaf.germ
          U (f x) hx (moduleTensorSection Y E ((Scheme.Modules.pushforward f).obj M) U e m))) =
    (ModuleCat.scalarExtensionTensorIso (f.stalkMap x).hom
      ((moduleStalk Y (f x)).obj E) ((moduleStalk X x).obj M)).inv
        ((projectionFormulaStalkSourceIso f hf x E M).hom
          (((moduleTensorLeftFunctor Y E).obj ((Scheme.Modules.pushforward f).obj M)).presheaf.germ
            U (f x) hx (moduleTensorSection Y E ((Scheme.Modules.pushforward f).obj M) U e m)))
  rw [moduleStalk_map_germ, projectionFormulaMap_section,
    projectionFormulaStalkTargetIso_unit_germ, projectionFormulaStalkSourceIso_germ,
    ModuleCat.scalarExtensionTensorIso_inv_tmul]

/-- The unchanged projection arrow is invertible on image stalks of every inducing scheme map. -/
theorem isIso_projectionFormulaMap_moduleStalk_of_isInducing {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : IsInducing f) (x : X) (E : Y.Modules) (M : X.Modules) :
    IsIso ((moduleStalk Y (f x)).map (projectionFormulaMap f E M)) := by
  have : IsIso ((moduleStalk Y (f x)).map (projectionFormulaMap f E M) ≫
      (projectionFormulaStalkTargetIso f hf x E M).hom) := by
    rw [projectionFormulaMap_stalk_comparison f hf x E M]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (projectionFormulaStalkTargetIso f hf x E M).hom

end AlgebraicGeometry.Scheme.Modules
