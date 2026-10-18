/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Map
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Restriction of actual ideal modules and canonical maps

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Hom

variable {D X Y : Scheme.{u}}

/-- The actual comparison between the restricted pushed unit and the pushed restricted unit. -/
def restrictedStructureIso (i : D ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit D.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (i ∣_ U)).obj
        (SheafOfModules.unit (i ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  Pullback.OpenRestriction.restrictedPushforwardIso i U (SheafOfModules.unit D.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward (i ∣_ U)).mapIso
      (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ U).ι)

@[reassoc]
theorem restrictedStructureMap_comm (i : D ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map (structureModuleMap i) ≫
        (restrictedStructureIso i U).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ structureModuleMap (i ∣_ U) := by
  apply Scheme.Modules.hom_ext
  intro V
  ext r
  simp only [restrictedStructureIso, Iso.trans_hom, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    ConcreteCategory.comp_apply, restrictUnitIso_ι_hom_app_apply]
  erw [restrictUnitIso_ι_hom_app_apply]
  change (Pullback.OpenRestriction.restrictedPushforwardMap i U
    (SheafOfModules.unit D.ringCatSheaf)).app V ((i.app (U.ι ''ᵁ V)) r) = (i ∣_ U).app V r
  rw [Pullback.OpenRestriction.restrictedPushforwardMap_app, morphismRestrict_app]
  rfl

/-- The kernel isomorphism comparing restriction of the actual ideal with the restricted morphism
ideal. -/
def idealRestrictionIso (i : D ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj (idealModule i) ≅ idealModule (i ∣_ U) :=
  PreservesKernel.iso (Scheme.Modules.restrictFunctor U.ι) (structureModuleMap i) ≪≫
    kernel.mapIso _ (structureModuleMap (i ∣_ U))
      (Scheme.Modules.restrictUnitIso U.ι) (restrictedStructureIso i U)
      (restrictedStructureMap_comm i U)

@[reassoc]
theorem idealRestrictionIso_hom_inclusion (i : D ⟶ X) (U : X.Opens) :
    (idealRestrictionIso i U).hom ≫ idealInclusion (i ∣_ U) =
      (Scheme.Modules.restrictFunctor U.ι).map (idealInclusion i) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom := by
  simp only [idealRestrictionIso, idealInclusion, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι]
  rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]

theorem idealPullbackMap_restrict (i : D ⟶ X) (U : X.Opens) :
    idealPullbackMap i (i ∣_ U) U.ι (i ⁻¹ᵁ U).ι (morphismRestrict_ι i U).symm =
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app (idealModule i) ≫
        (idealRestrictionIso i U).hom := by
  apply (cancel_mono (idealInclusion (i ∣_ U))).mp
  rw [idealPullbackMap_inclusion, Category.assoc, idealRestrictionIso_hom_inclusion]
  rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.naturality,
    Category.assoc, restrictFunctorIsoPullback_inv_unit]

/-- The actual ideal pullback map for an open restriction is an isomorphism. -/
instance idealPullbackMap_restrict_isIso (i : D ⟶ X) (U : X.Opens) :
    IsIso (idealPullbackMap i (i ∣_ U) U.ι (i ⁻¹ᵁ U).ι
      (morphismRestrict_ι i U).symm) := by
  rw [idealPullbackMap_restrict]
  infer_instance

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {D X Y : Scheme.{u}}
variable {D' : Scheme.{u}}

/-- The canonical restricted source map of the displayed commutative square. -/
def restrictedSquareSourceMap (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (V : X.Opens) (W : Y.Opens) (hWV : W ≤ b ⁻¹ᵁ V) :
    (i' ⁻¹ᵁ W).toScheme ⟶ (i ⁻¹ᵁ V).toScheme :=
  a.resLE (i ⁻¹ᵁ V) (i' ⁻¹ᵁ W) (by
    rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]
    exact i'.preimage_mono hWV)

theorem restrictedSquareSourceMap_comm (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (V : X.Opens) (W : Y.Opens) (hWV : W ≤ b ⁻¹ᵁ V) :
    restrictedSquareSourceMap i i' b a h V W hWV ≫ (i ∣_ V) =
      (i' ∣_ W) ≫ b.resLE V W hWV := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, morphismRestrict_ι, restrictedSquareSourceMap,
    Scheme.Hom.resLE_comp_ι_assoc]
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  rw [← Category.assoc (i' ∣_ W) W.ι b, morphismRestrict_ι, Category.assoc, h]

theorem idealPullbackMap_restrict_isIso_of_local (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (V : X.Opens) (W : Y.Opens) (hWV : W ≤ b ⁻¹ᵁ V)
    [IsIso (idealPullbackMap (i ∣_ V) (i' ∣_ W) (b.resLE V W hWV)
      (restrictedSquareSourceMap i i' b a h V W hWV)
      (restrictedSquareSourceMap_comm i i' b a h V W hWV))] :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map (idealPullbackMap i i' b a h)) := by
  let b₀ := b.resLE V W hWV
  let a₀ := restrictedSquareSourceMap i i' b a h V W hWV
  have h₀ : a₀ ≫ (i ∣_ V) = (i' ∣_ W) ≫ b₀ :=
    restrictedSquareSourceMap_comm i i' b a h V W hWV
  have hV := (morphismRestrict_ι i V).symm
  have hW := (morphismRestrict_ι i' W).symm
  have hcompV : (a₀ ≫ (i ⁻¹ᵁ V).ι) ≫ i = (i' ∣_ W) ≫ (b₀ ≫ V.ι) := by
    rw [Category.assoc, hV, ← Category.assoc, h₀, Category.assoc]
  have hcompW : ((i' ⁻¹ᵁ W).ι ≫ a) ≫ i = (i' ∣_ W) ≫ (W.ι ≫ b) := by
    rw [Category.assoc, h, ← Category.assoc, hW, Category.assoc]
  have : IsIso (idealPullbackMap i (i' ∣_ W) (b₀ ≫ V.ι)
      (a₀ ≫ (i ⁻¹ᵁ V).ι) hcompV) := by
    rw [← idealPullbackMap_comp i (i ∣_ V) (i' ∣_ W) V.ι b₀
      (i ⁻¹ᵁ V).ι a₀ hV h₀]
    infer_instance
  have : IsIso (idealPullbackMap i (i' ∣_ W) (W.ι ≫ b)
      ((i' ⁻¹ᵁ W).ι ≫ a) hcompW) :=
    idealPullbackMap_isIso_of_eq_base i (i' ∣_ W) (W.ι ≫ b) (b₀ ≫ V.ι)
      ((i' ⁻¹ᵁ W).ι ≫ a) (a₀ ≫ (i ⁻¹ᵁ V).ι) hcompW hcompV
      (b.resLE_comp_ι hWV).symm
  have : IsIso ((Scheme.Modules.pullbackComp W.ι b).inv.app (idealModule i) ≫
      (Scheme.Modules.pullback W.ι).map (idealPullbackMap i i' b a h) ≫
        idealPullbackMap i' (i' ∣_ W) W.ι (i' ⁻¹ᵁ W).ι hW) := by
    rw [idealPullbackMap_comp]
    infer_instance
  have : IsIso ((Scheme.Modules.pullback W.ι).map (idealPullbackMap i i' b a h) ≫
      idealPullbackMap i' (i' ∣_ W) W.ι (i' ⁻¹ᵁ W).ι hW) :=
    (isIso_comp_left_iff ((Scheme.Modules.pullbackComp W.ι b).inv.app
      (idealModule i)) _).mp inferInstance
  have : IsIso ((Scheme.Modules.pullback W.ι).map (idealPullbackMap i i' b a h)) :=
    (isIso_comp_right_iff _ (idealPullbackMap i' (i' ∣_ W) W.ι
      (i' ⁻¹ᵁ W).ι hW)).mp inferInstance
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback W.ι)
    (idealPullbackMap i i' b a h)).mpr inferInstance

theorem idealPullbackMap_isIso_of_local (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (hloc : ∀ y : Y, ∃ (V : X.Opens) (W : Y.Opens) (hWV : W ≤ b ⁻¹ᵁ V),
      y ∈ W ∧ IsIso (idealPullbackMap (i ∣_ V) (i' ∣_ W) (b.resLE V W hWV)
        (restrictedSquareSourceMap i i' b a h V W hWV)
        (restrictedSquareSourceMap_comm i i' b a h V W hWV))) :
    IsIso (idealPullbackMap i i' b a h) := by
  apply Pullback.OpenRestriction.isIso_of_local_restrict
  intro y
  obtain ⟨V, W, hWV, hyW, hIso⟩ := hloc y
  let := hIso
  exact ⟨W, hyW, idealPullbackMap_restrict_isIso_of_local i i' b a h V W hWV⟩

end AlgebraicGeometry.Scheme.Hom
end
