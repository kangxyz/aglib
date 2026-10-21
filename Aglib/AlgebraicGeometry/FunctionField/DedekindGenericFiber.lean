/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericSection

/-!
# Function fields of the actual generic fibre over a Dedekind base

The generic point of an integral scheme dominant over `Spec A` lifts into the
literal pullback along the supplied fraction-field map. Thus its projection is
dominant without an integrality premise on the fibre. When that fibre is integral,
the actual projection induces a canonical function-field equivalence preserving
the structural constants.

Source: `R5Lab/Aglib/AlgebraicGeometry/FunctionField/GenericFiber.lean`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, lines 39–153, SHA-256
`7db91bb84db566ed19365afa1b4198cd302b3ff12ce77cb605626fcd48618ea2`.
The separate finite-dominant morphism theorem in `FunctionField.GenericFiber`
concerns a different pullback and is not used here.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.LocalRing.GenericFiber (baseMap projection scheme)

universe u

namespace AlgebraicGeometry.Scheme.FunctionField.DedekindGenericFiber

variable (A F : Type u) [CommRing A] [IsDedekindDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F] {Y : Scheme.{u}} [IsIntegral Y]
  (p : Y ⟶ Spec (.of A)) [IsDominant p]

/-- The actual generic-point map lifted into the fraction-field pullback of `p`. -/
def genericLift : Spec Y.functionField ⟶ scheme A F p :=
  pullback.lift (Y.fromSpecStalk (genericPoint Y))
    (Spec.map (CommRingCat.ofHom (DedekindBase.constantToFunctionField F p)))
    (GenericSection.generic_base_triangle A F p)

/-- The lift projects to the original map from the generic-point stalk. -/
@[simp, reassoc] theorem genericLift_projection :
    genericLift A F p ≫ projection A F p = Y.fromSpecStalk (genericPoint Y) :=
  pullback.lift_fst _ _ _

/-- The lift has the canonical fraction-field embedding as its structural arrow. -/
@[simp, reassoc] theorem genericLift_structure :
    genericLift A F p ≫ pullback.snd p (baseMap A F) =
      Spec.map (CommRingCat.ofHom (DedekindBase.constantToFunctionField F p)) :=
  pullback.lift_snd _ _ _

/-- The generic-fibre projection is dominant; the fibre need not yet be integral. -/
instance projection_isDominant : IsDominant (projection A F p) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← genericPoint_closure Y]
  apply closure_mono
  rintro x rfl
  refine ⟨genericLift A F p (IsLocalRing.closedPoint Y.functionField), ?_⟩
  change (genericLift A F p ≫ projection A F p) (IsLocalRing.closedPoint Y.functionField) = _
  rw [genericLift_projection]
  exact Scheme.fromSpecStalk_closedPoint

variable [IsIntegral (scheme A F p)]

/-- The actual generic-fibre projection induces an isomorphism on function fields. -/
theorem functionFieldMap_isIso :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (projection A F p))) := by
  let := LocalRing.GenericFiber.projection_stalkMap_isIso A F p
    (genericPoint (scheme A F p))
  change IsIso (Y.presheaf.stalkSpecializes _ ≫
    (projection A F p).stalkMap (genericPoint (scheme A F p)))
  have he : Y.presheaf.stalkSpecializes
      (specializes_of_eq (Scheme.map_genericPoint_of_isDominant
        (scheme A F p) (projection A F p))) =
      (Y.presheaf.stalkCongr (.of_eq
        (Scheme.map_genericPoint_of_isDominant
          (scheme A F p) (projection A F p)).symm)).hom := rfl
  rw [he]
  infer_instance

/-- The canonical equivalence whose forward map is the actual projection's function-field map. -/
def functionFieldRingEquiv : Y.functionField ≃+* (scheme A F p).functionField := by
  let := functionFieldMap_isIso A F p
  exact (asIso (CommRingCat.ofHom
    (Scheme.functionFieldMap (projection A F p)))).commRingCatIsoToRingEquiv

/-- The equivalence acts by the original generic-point stalk ring homomorphism. -/
@[simp] theorem functionFieldRingEquiv_apply (a : Y.functionField) :
    functionFieldRingEquiv A F p a =
      Scheme.functionFieldMap (projection A F p) a := rfl

/-- The structural fraction-field map obtained from the fibre's actual generic-point arrow. -/
def structuralConstants : F →+* (scheme A F p).functionField :=
  (Spec.preimage ((scheme A F p).fromSpecStalk (genericPoint (scheme A F p)) ≫
    pullback.snd p (baseMap A F))).hom

/-- The actual projection commutes with its induced generic-point stalk map. -/
theorem projection_generic_triangle :
    (scheme A F p).fromSpecStalk (genericPoint (scheme A F p)) ≫ projection A F p =
      Spec.map (CommRingCat.ofHom
        (Scheme.functionFieldMap (projection A F p))) ≫
        Y.fromSpecStalk (genericPoint Y) :=
  Scheme.fromSpecStalk_genericPoint_naturality (projection A F p)

/-- The canonical equivalence preserves the literal structural fraction-field maps. -/
theorem functionFieldRingEquiv_constants :
    (functionFieldRingEquiv A F p).toRingHom.comp (DedekindBase.constantToFunctionField F p) =
      structuralConstants A F p := by
  have he : (functionFieldRingEquiv A F p).toRingHom =
      Scheme.functionFieldMap (projection A F p) := by
    ext a
    exact functionFieldRingEquiv_apply A F p a
  rw [he]
  let := LocalRing.GenericFiber.baseMap_preimmersion A F
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  rw [Spec.map_preimage]
  change Spec.map (CommRingCat.ofHom (DedekindBase.constantToFunctionField F p) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap (projection A F p))) =
    (scheme A F p).fromSpecStalk (genericPoint (scheme A F p)) ≫ pullback.snd p (baseMap A F)
  rw [Spec.map_comp]
  apply (cancel_mono (baseMap A F)).mp
  rw [Category.assoc, ← GenericSection.generic_base_triangle A F p, ← Category.assoc,
    ← projection_generic_triangle]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun f => (scheme A F p).fromSpecStalk (genericPoint (scheme A F p)) ≫ f)
    (pullback.condition (f := p) (g := baseMap A F))

/-- Forward transport of a structural constant is its actual structural image on the fibre. -/
theorem functionFieldRingEquiv_constants_apply (a : F) :
    functionFieldRingEquiv A F p (DedekindBase.constantToFunctionField F p a) =
      structuralConstants A F p a :=
  DFunLike.congr_fun (functionFieldRingEquiv_constants A F p) a

/-- Inverse transport recovers the original structural constant in the model's function field. -/
@[simp] theorem functionFieldRingEquiv_symm_constants_apply (a : F) :
    (functionFieldRingEquiv A F p).symm (structuralConstants A F p a) =
      DedekindBase.constantToFunctionField F p a := by
  rw [← functionFieldRingEquiv_constants_apply]
  exact (functionFieldRingEquiv A F p).symm_apply_apply _

end AlgebraicGeometry.Scheme.FunctionField.DedekindGenericFiber
