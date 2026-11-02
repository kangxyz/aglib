/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.LocalSpectrum
public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum.Germs
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.GenericEmbedding
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-!
# Original module stalks in the original function field

One supplied frame at the original generic stalk is transported along the
actual local-spectrum morphism. Original local-spectrum sections and their
native germ comparison then give a map from the original stalk to the same
original function field. No fraction model or second frame is chosen.
Construction and germ values need no quasicoherence or torsion-freeness;
these hypotheses are used only for injectivity.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The native extension/unit formula evaluated before geometric specialization. -/
private theorem extendedFrame_unit_value
    {K L : Type u} [CommRing K] [CommRing L] (φ : K →+* L)
    {V : ModuleCat.{u} K} (g : V ⟶ ModuleCat.of K K) (v : V) :
    (Functor.Monoidal.εIso (ModuleCat.extendScalars φ)).inv
      ((ModuleCat.extendScalars φ).map g
        ((ModuleCat.extendRestrictScalarsAdj φ).unit.app V v)) = φ (g v) := by
  simp only [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
    Functor.Monoidal.εIso_inv,
    ModuleCat.extendScalars_η]
  erw [TensorProduct.AlgebraTensorModule.rid_tmul]
  rw [RingHom.smul_toAlgebra]
  change φ (g v) * (1 : L) = φ (g v)
  exact mul_one _

variable (X : Scheme.{u}) [IsIntegral X] (x : X) (M : X.Modules)
  (eη : ((moduleStalk X (genericPoint X)).obj M) ≃ₗ[X.functionField] X.functionField)

local instance : IsDominant (X.fromSpecStalk x) := Scheme.fromSpecStalk_isDominant X x

/-- Transport the supplied original generic frame through the actual
pullback-stalk comparison and the native extension-of-scalars unit object. -/
def fromSpecStalkGenericFrame :
    ((moduleStalk (Spec (X.presheaf.stalk x))
      (genericPoint (Spec (X.presheaf.stalk x)))).obj
        ((pullback (X.fromSpecStalk x)).obj M)) ≃ₗ[(Spec (X.presheaf.stalk x)).functionField]
      (Spec (X.presheaf.stalk x)).functionField := by
  let j := X.fromSpecStalk x
  let φ := Scheme.functionFieldMap j
  let hη := Scheme.map_genericPoint_of_isDominant (Spec (X.presheaf.stalk x)) j
  exact (((pullbackModuleStalkAtEqIso j (genericPoint (Spec (X.presheaf.stalk x)))
      (genericPoint X) hη).app M) ≪≫
    (ModuleCat.extendScalars φ).mapIso eη.toModuleIso ≪≫
    (Functor.Monoidal.εIso (ModuleCat.extendScalars φ)).symm).toLinearEquiv

/-- The transported frame retains the original pullback-unit germ value. -/
theorem fromSpecStalkGenericFrame_unit_germ
    (U : X.Opens) (hηU : genericPoint X ∈ U) (s : Γ(M, U)) :
    fromSpecStalkGenericFrame X x M eη
      (((pullback (X.fromSpecStalk x)).obj M).presheaf.germ
        ((X.fromSpecStalk x) ⁻¹ᵁ U) (genericPoint (Spec (X.presheaf.stalk x)))
        (by
          change X.fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x))) ∈ U
          simpa only [Scheme.map_genericPoint_of_isDominant] using hηU)
        (((pullbackPushforwardAdjunction (X.fromSpecStalk x)).unit.app M).app U s)) =
      Scheme.functionFieldMap (X.fromSpecStalk x)
        (eη (M.presheaf.germ U (genericPoint X) hηU s)) := by
  let j := X.fromSpecStalk x
  let φ := Scheme.functionFieldMap j
  let hη := Scheme.map_genericPoint_of_isDominant (Spec (X.presheaf.stalk x)) j
  have hu := pullbackModuleStalkAtEqIso_unit_germ j
    (genericPoint (Spec (X.presheaf.stalk x))) (genericPoint X) hη M U hηU s
  have hv := congrArg (fun z =>
    (Functor.Monoidal.εIso (ModuleCat.extendScalars φ)).inv
      ((ModuleCat.extendScalars φ).map eη.toModuleIso.hom z)) hu
  exact hv.trans (extendedFrame_unit_value φ eη.toModuleIso.hom
    (M.presheaf.germ U (genericPoint X) hηU s))

/-- The original stalk maps into the original function field through actual
local-spectrum sections and the transported same generic frame. -/
def stalkToFunctionField :
    ((moduleStalk X x).obj M) →ₗ[X.presheaf.stalk x] X.functionField :=
  (Scheme.fromSpecStalkFunctionFieldAlgEquiv X x).symm.toLinearMap.comp
    ((affineSectionsToFunctionField ((pullback (X.fromSpecStalk x)).obj M)
      (fromSpecStalkGenericFrame X x M eη)).comp
        (stalkFromSpecStalkSectionsIso X x M).hom.hom)

/-- Every original neighbourhood germ has its value in the ONE original
supplied generic frame. No localization model is substituted. -/
theorem stalkToFunctionField_germ (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) :
    stalkToFunctionField X x M eη (M.presheaf.germ U x hx s) =
      eη (M.presheaf.germ U (genericPoint X)
        ((genericPoint_specializes x).mem_open U.isOpen hx) s) := by
  change (Scheme.fromSpecStalkFunctionFieldAlgEquiv X x).symm
    (affineSectionsToFunctionField ((pullback (X.fromSpecStalk x)).obj M)
      (fromSpecStalkGenericFrame X x M eη)
      ((stalkFromSpecStalkSectionsIso X x M).hom (M.presheaf.germ U x hx s))) = _
  rw [stalkFromSpecStalkSectionsIso_germ]
  apply (Scheme.fromSpecStalkFunctionFieldAlgEquiv X x).injective
  rw [AlgEquiv.apply_symm_apply, affineSectionsToFunctionField_apply,
    TopCat.Presheaf.germ_res_apply, Scheme.fromSpecStalkFunctionFieldAlgEquiv_apply]
  exact fromSpecStalkGenericFrame_unit_germ X x M eη U _ s

/-- Genuine quasicoherence and torsion-freeness of the ORIGINAL stalk give
injectivity; no global torsion-free, finite or rank-one premise is added. -/
theorem stalkToFunctionField_injective [M.IsQuasicoherent]
    [Module.IsTorsionFree (X.presheaf.stalk x) ((moduleStalk X x).obj M)] :
    Function.Injective (stalkToFunctionField X x M eη) := by
  let N := (pullback (X.fromSpecStalk x)).obj M
  let α := (stalkFromSpecStalkSectionsIso X x M).toLinearEquiv
  let : Module.IsTorsionFree (X.presheaf.stalk x) (moduleSpecΓFunctor.obj N) :=
    Function.Injective.moduleIsTorsionFree α.symm α.symm.injective α.symm.map_smul
  exact (Scheme.fromSpecStalkFunctionFieldAlgEquiv X x).symm.injective.comp
    ((affineSectionsToFunctionField_injective N (fromSpecStalkGenericFrame X x M eη)).comp
      α.injective)

end AlgebraicGeometry.Scheme.Modules
