/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.Properties.Normal.GlobalSections
public import Aglib.AlgebraicGeometry.Morphisms.Proper.AffineStein
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Finite generic normalization from an actual proper birational normal model

On each nonempty affine target open, the original finite section algebra of
the proper source is identified with the integral closure in the original
target function field. The forward map is the original source germ followed
by the inverse of the original function-field map. Normality is used as
integral closedness in that function field; the source function field is not
assumed to be the fraction field of a nonaffine section ring.

The actual generic-normalization chart comparison transfers finiteness to
the literal normalization map. Its factor from the original normal source
is constructed from the existing generic-normalization universal property,
with the original generic arrow and structural triangle retained. There is
no dimension, Nagata or excellence hypothesis. The current consumer is the
necessary-condition direction of absolute surface resolution, beginning
with a supplied proper birational regular model.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

private def finiteNormalIntegralClosureEquiv
    (A C K L : Type u) [CommRing A] [CommRing C] [CommRing K] [CommRing L]
    [Algebra A C] [Algebra A K] [Algebra A L] [Algebra C L]
    [IsScalarTower A C L] [Module.Finite A C] [IsIntegrallyClosedIn C L]
    (e : K ≃ₐ[A] L) : C ≃ₐ[A] integralClosure A K := by
  let ρ : C →ₐ[A] K := e.symm.toAlgHom.comp (IsScalarTower.toAlgHom A C L)
  let t : C →ₐ[A] integralClosure A K :=
    ρ.codRestrict (integralClosure A K)
      (fun c => (Algebra.IsIntegral.isIntegral (R := A) c).map ρ)
  apply AlgEquiv.ofBijective t
  constructor
  · intro c d hcd
    apply (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn C L)).1
    exact e.symm.injective (congrArg Subtype.val hcd)
  · intro b
    have hb : IsIntegral C (e b.val) := (b.property.map e.toAlgHom).tower_top
    obtain ⟨c, hc⟩ :=
      (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn C L)).2 hb
    refine ⟨c, Subtype.ext ?_⟩
    apply e.injective
    change e (e.symm (algebraMap C L c)) = e b.val
    rw [e.apply_symm_apply]
    exact hc

@[expose] public section

namespace AlgebraicGeometry.Scheme

section GenericFactor

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsDominant f] (hX : NormalStalks X)

/-- The original generic map into the literal target normalization. -/
def genericNormalizationLiftGeneric :
    Spec X.functionField ⟶ (Y.fromSpecStalk (genericPoint Y)).normalization :=
  Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫
    (Y.fromSpecStalk (genericPoint Y)).toNormalization

/-- The original generic arrow retains the original structural triangle. -/
@[reassoc]
theorem genericNormalizationLiftGeneric_over :
    genericNormalizationLiftGeneric f ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [genericNormalizationLiftGeneric, Category.assoc,
    Hom.toNormalization_fromNormalization]
  exact (fromSpecStalk_genericPoint_naturality f).symm

/-- A dominant map from a normal integral source factors through the literal
generic normalization. The construction extends its original generic map
through an integral pullback, using the proved trivial source normalization. -/
def genericNormalizationLift : X ⟶ (Y.fromSpecStalk (genericPoint Y)).normalization := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  let γ := X.fromSpecStalk (genericPoint X)
  let ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  let m : Spec X.functionField ⟶ pullback f ν :=
    pullback.lift γ (genericNormalizationLiftGeneric f)
      (genericNormalizationLiftGeneric_over f).symm
  exact inv γ.fromNormalization ≫
    γ.normalizationDesc m (pullback.fst f ν)
      (pullback.lift_fst γ (genericNormalizationLiftGeneric f)
        (genericNormalizationLiftGeneric_over f).symm).symm ≫ pullback.snd f ν

/-- The factorization is a literal equality of the original morphisms. -/
@[reassoc]
theorem genericNormalizationLift_over :
    genericNormalizationLift f hX ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization = f := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  let γ := X.fromSpecStalk (genericPoint X)
  let ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  let m : Spec X.functionField ⟶ pullback f ν :=
    pullback.lift γ (genericNormalizationLiftGeneric f)
      (genericNormalizationLiftGeneric_over f).symm
  change (inv γ.fromNormalization ≫
    γ.normalizationDesc m (pullback.fst f ν)
      (pullback.lift_fst γ (genericNormalizationLiftGeneric f)
        (genericNormalizationLiftGeneric_over f).symm).symm ≫ pullback.snd f ν) ≫ ν = f
  simp only [Category.assoc]
  rw [← pullback.condition, ← Category.assoc _ _ f,
    Hom.normalizationDesc_comp, IsIso.inv_hom_id_assoc]

/-- The factor restricts to the same original generic arrow, rather than a
separately chosen field embedding. -/
@[reassoc]
theorem genericNormalizationLift_generic :
    X.fromSpecStalk (genericPoint X) ≫ genericNormalizationLift f hX =
      genericNormalizationLiftGeneric f := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  let γ := X.fromSpecStalk (genericPoint X)
  let ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  let m : Spec X.functionField ⟶ pullback f ν :=
    pullback.lift γ (genericNormalizationLiftGeneric f)
      (genericNormalizationLiftGeneric_over f).symm
  have hγ : γ ≫ inv γ.fromNormalization = γ.toNormalization := by
    calc
      _ = (γ.toNormalization ≫ γ.fromNormalization) ≫ inv γ.fromNormalization := by
        rw [Hom.toNormalization_fromNormalization]
      _ = _ := by simp
  change γ ≫ inv γ.fromNormalization ≫
    γ.normalizationDesc m (pullback.fst f ν)
      (pullback.lift_fst γ (genericNormalizationLiftGeneric f)
        (genericNormalizationLiftGeneric_over f).symm).symm ≫ pullback.snd f ν = _
  rw [← Category.assoc γ, hγ, Hom.toNormalization_normalizationDesc_assoc,
    pullback.lift_snd]

/-- Dominance of the actual factor follows from its original generic triangle. -/
theorem genericNormalizationLift_isDominant : IsDominant (genericNormalizationLift f hX) := by
  let : Surjective (Spec.map (CommRingCat.ofHom (functionFieldMap f))) :=
    ⟨Function.surjective_to_subsingleton _⟩
  let : IsDominant (genericNormalizationLiftGeneric f) := by
    dsimp only [genericNormalizationLiftGeneric]
    infer_instance
  let : IsDominant (X.fromSpecStalk (genericPoint X) ≫ genericNormalizationLift f hX) := by
    rw [genericNormalizationLift_generic]
    infer_instance
  exact IsDominant.of_comp (X.fromSpecStalk (genericPoint X)) (genericNormalizationLift f hX)

/-- Properness of the original morphism gives properness of its actual
normalization factor; the integral final map is separated. -/
theorem genericNormalizationLift_isProper [IsProper f] :
    IsProper (genericNormalizationLift f hX) := by
  have : IsProper (genericNormalizationLift f hX ≫
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization) := by
    rw [genericNormalizationLift_over]
    infer_instance
  exact IsProper.of_comp (genericNormalizationLift f hX)
    (Y.fromSpecStalk (genericPoint Y)).fromNormalization

/-- The original field-map isomorphism passes to the actual normalization
factor through its original triangle and the original normalization field map. -/
theorem genericNormalizationLift_fieldMap_isIso
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    letI := genericNormalizationLift_isDominant f hX
    IsIso (CommRingCat.ofHom (functionFieldMap (genericNormalizationLift f hX))) := by
  let := genericNormalizationLift_isDominant f hX
  let := genericNormalization_isDominant Y
  let ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  let : IsIso (CommRingCat.ofHom (functionFieldMap ν)) := genericNormalization_fieldMap_isIso Y
  have he : functionFieldMap (genericNormalizationLift f hX ≫ ν) = functionFieldMap f := by
    congr 1
    exact genericNormalizationLift_over f hX
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap ν) ≫
      CommRingCat.ofHom (functionFieldMap (genericNormalizationLift f hX))) := by
    change IsIso (CommRingCat.ofHom
      ((functionFieldMap (genericNormalizationLift f hX)).comp (functionFieldMap ν)))
    rw [← functionFieldMap_comp, he]
    exact hff
  exact IsIso.of_isIso_comp_left (CommRingCat.ofHom (functionFieldMap ν)) _

end GenericFactor

section AffineSections

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsProper f] [IsDominant f]
  (hX : NormalStalks X) (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
  (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]

local instance properBirationalPreimageNonempty : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U
  rw [map_genericPoint_of_isDominant X f]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

/-- The actual field isomorphism used by the section-algebra comparison. -/
def properBirationalFunctionFieldEquiv : Y.functionField ≃+* X.functionField := by
  let := hff
  exact (asIso (CommRingCat.ofHom (functionFieldMap f))).commRingCatIsoToRingEquiv

omit [IsLocallyNoetherian Y] [IsProper f] in
private theorem properBirationalGerm_square :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (functionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.presheaf.germ U _ _ ≫
    (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint X) _

/-- The original proper section algebra is the integral closure in the
original target function field, with its actual structural A-action. -/
def properBirationalSectionsIntegralClosureEquiv :
    letI := (f.app U).hom.toAlgebra
    Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, U)] integralClosure Γ(Y, U) Y.functionField := by
  let A := Γ(Y, U)
  let C := Γ(X, f ⁻¹ᵁ U)
  let := (f.app U).hom.toAlgebra
  let : Algebra A X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  let : IsScalarTower A C X.functionField :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := C) (A := X.functionField) (fun _ => rfl)
  let : Module.Finite A C := AffineStein.finite_coefficient f U hU
  let : IsIntegrallyClosedIn C X.functionField :=
    X.isIntegrallyClosedIn_functionField_sections (f ⁻¹ᵁ U) (fun x => (hX x.val).2)
  let e : Y.functionField ≃ₐ[A] X.functionField :=
    { properBirationalFunctionFieldEquiv f hff with
      commutes' a := by
        change functionFieldMap f (Y.germToFunctionField U a) =
          X.germToFunctionField (f ⁻¹ᵁ U) (f.app U a)
        exact ConcreteCategory.congr_hom (properBirationalGerm_square f U) a }
  exact private_decl% (finiteNormalIntegralClosureEquiv A C Y.functionField X.functionField e)

private theorem properBirationalSectionsIntegralClosureEquiv_val_aux (c : Γ(X, f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    (properBirationalSectionsIntegralClosureEquiv f hX hff U hU c : Y.functionField) =
      (properBirationalFunctionFieldEquiv f hff).symm
        (X.germToFunctionField (f ⁻¹ᵁ U) c) := rfl

/-- The forward value is exactly the original germ followed by the inverse
of the original function-field map. -/
theorem properBirationalSectionsIntegralClosureEquiv_val (c : Γ(X, f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    (properBirationalSectionsIntegralClosureEquiv f hX hff U hU c : Y.functionField) =
      (properBirationalFunctionFieldEquiv f hff).symm
        (X.germToFunctionField (f ⁻¹ᵁ U) c) :=
  properBirationalSectionsIntegralClosureEquiv_val_aux f hX hff U hU c

/-- The native generic-source section ring retains its original affine
coefficient map when identified with the target function field. -/
def properBirationalGenericSectionsEquiv :
    letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    Γ(Spec Y.functionField, (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) ≃ₐ[Γ(Y, U)]
      Y.functionField := by
  let := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  exact
    { (functionFieldSectionsIso Y U).commRingCatIsoToRingEquiv with
      commutes' a := by
        exact ConcreteCategory.congr_hom
          (fromSpecStalk_genericPoint_app_functionFieldSectionsIso Y U) a }

/-- Original source sections identified with the literal closure appearing
in the native normalization chart, not a replacement closure. -/
def properBirationalSectionsNativeClosureEquiv :
    letI := (f.app U).hom.toAlgebra
    letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, U)]
      integralClosure Γ(Y, U)
        Γ(Spec Y.functionField, (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) := by
  let := (f.app U).hom.toAlgebra
  let := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  exact (properBirationalSectionsIntegralClosureEquiv f hX hff U hU).trans
    (properBirationalGenericSectionsEquiv (Y := Y) U).mapIntegralClosure.symm

/-- The actual source section ring is identified with the actual section
ring of the literal generic normalization. -/
def properBirationalNormalizationSectionsIso :
    Γ(X, f ⁻¹ᵁ U) ≅
      Γ((Y.fromSpecStalk (genericPoint Y)).normalization,
        (Y.fromSpecStalk (genericPoint Y)).fromNormalization ⁻¹ᵁ U) := by
  let := (f.app U).hom.toAlgebra
  let := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  exact
    (properBirationalSectionsNativeClosureEquiv f hX hff U hU).toRingEquiv.toCommRingCatIso ≪≫
      ((Y.fromSpecStalk (genericPoint Y)).normalizationObjIso hU).symm

/-- The actual affine normalization comparison fixes the original structural
coefficient map. -/
@[reassoc]
theorem properBirationalNormalizationSectionsIso_coefficients :
    f.app U ≫ (properBirationalNormalizationSectionsIso f hX hff U hU).hom =
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization.app U := by
  let := (f.app U).hom.toAlgebra
  let := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  rw [Hom.fromNormalization_app _ hU]
  apply CommRingCat.hom_ext
  ext a
  change ((Y.fromSpecStalk (genericPoint Y)).normalizationObjIso hU).inv
    (properBirationalSectionsNativeClosureEquiv f hX hff U hU (f.app U a)) = _
  have hcoeff : properBirationalSectionsNativeClosureEquiv f hX hff U hU (f.app U a) =
      algebraMap Γ(Y, U)
        (integralClosure Γ(Y, U)
          Γ(Spec Y.functionField, (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) a :=
    (properBirationalSectionsNativeClosureEquiv f hX hff U hU).commutes a
  exact congrArg ((Y.fromSpecStalk (genericPoint Y)).normalizationObjIso hU).inv hcoeff

include f hX hff hU in
/-- Finiteness of the original proper section algebra gives finiteness of
the actual normalization section map. -/
theorem properBirationalNormalization_finite_app :
    (((Y.fromSpecStalk (genericPoint Y)).fromNormalization).app U).hom.Finite := by
  rw [← properBirationalNormalizationSectionsIso_coefficients f hX hff U hU]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso
      (properBirationalNormalizationSectionsIso f hX hff U hU).hom).2).comp
        (AffineStein.finite_coefficient f U hU)

end AffineSections

/-- A supplied proper birational normal integral model forces finiteness
of the literal generic normalization. Only local Noetherianity of the
integral target is used; no Nagata or dimension premise is introduced. -/
theorem genericNormalization_isFinite_of_proper_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · let := hne
    exact properBirationalNormalization_finite_app f hX hff U hU
  · have hbot : U = ⊥ := by
      apply bot_unique
      intro y hy
      exact (hne ⟨⟨y, hy⟩⟩).elim
    subst U
    let : Subsingleton
        Γ((Y.fromSpecStalk (genericPoint Y)).normalization,
          (Y.fromSpecStalk (genericPoint Y)).fromNormalization ⁻¹ᵁ ⊥) := by
      rw [Hom.preimage_bot]
      infer_instance
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

end AlgebraicGeometry.Scheme
