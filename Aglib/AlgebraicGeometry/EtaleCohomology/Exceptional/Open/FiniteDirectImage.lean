/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.OpenCounitStalk
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange

/-!
# Ordinary finite direct image commutes with open extension

For a Cartesian square with open horizontal arrows and a finite vertical map,
the actual abelian finite base-change map and open-extension unit give the
restriction comparison. Its adjoint under the actual open adjunction is an
isomorphism: outside the open, every coordinate of the finite direct-image
stalk is zero. This is an ordinary direct-image exchange for arbitrary abelian
sheaves, not inverse-image base change or a torsion-derived specialization.
The curve cohomological-dimension argument uses it before finite cohomology
comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open CoefficientStalkBaseChange

attribute [local instance] hasSheafifyLarge

variable {V U Y X : Scheme.{u}} (b : Y ⟶ X) [IsFinite b]
  (v : V ⟶ U) (j : U ⟶ X) (j' : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion j']
  (sq : IsPullback j' v b j)

include sq

omit [IsOpenImmersion j] in
/-- A finite direct image of an open extension has zero stalk outside the base open. -/
theorem isZero_finiteDirectImage_etaleLowerShriek_stalk_of_not_mem
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ X)
    (hη : η (default : Spec (.of Ω)) ∉ Set.range j)
    (G : AbelianSheaf.{u, u + 1} V) :
    IsZero ((pointSmallEtale η).sheafFiber.obj
      ((directImage b).obj ((etaleLowerShriek j').obj G))) := by
  have hz (ζ : {ζ : Spec (.of Ω) ⟶ Y // ζ ≫ b = η}) :
      IsZero (coefficientFiber ζ.val ((etaleLowerShriek j').obj G)) := by
    apply isZero_etaleLowerShriek_stalk_of_no_lift j' ζ.val _ G
    intro ξ hξ
    apply hη
    refine ⟨(ξ ≫ v) (default : Spec (.of Ω)), ?_⟩
    have h : (ξ ≫ v) ≫ j = η := by
      rw [Category.assoc, ← sq.w, ← Category.assoc, hξ, ζ.property]
    exact congrArg (fun f : Spec (.of Ω) ⟶ X => f default) h
  let (ζ : {ζ : Spec (.of Ω) ⟶ Y // ζ ≫ b = η}) :
      Subsingleton (coefficientFiber ζ.val ((etaleLowerShriek j').obj G)) :=
    AddCommGrpCat.subsingleton_of_isZero (hz ζ)
  have ht : IsZero (directImageEvaluationTupleTarget b η
      ((etaleLowerShriek j').obj G)) := by
    unfold directImageEvaluationTupleTarget
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact ht.of_iso (Finite.finiteDirectImageEvaluationIso b η
    ((etaleLowerShriek j').obj G))

/-- The actual open counit is invertible on the finite image of an open extension. -/
theorem etaleLowerShriek_counit_finiteDirectImage_isIso
    (G : AbelianSheaf.{u, u + 1} V) :
    IsIso ((etaleLowerShriekAdjunction j).counit.app
      ((directImage b).obj ((etaleLowerShriek j').obj G))) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 X)
  intro Ω _ _ η _
  by_cases hη : η (default : Spec (.of Ω)) ∈ Set.range j
  · obtain ⟨ζ, hζ⟩ := exists_openImmersion_pointLift j η hη
    exact etaleLowerShriek_counit_stalk_isIso j ζ η hζ _
  · exact (isZero_etaleLowerShriek_stalk_of_not_mem j η hη _).isIso
      (isZero_finiteDirectImage_etaleLowerShriek_stalk_of_not_mem b v j j' sq η hη G) _

/-- Restricting the finite image of the original open extension, using the actual
finite base-change map followed by the inverse of the original open unit. -/
def etaleLowerShriekFiniteRestrictionIso :
    (etaleLowerShriek j' ⋙ directImage b) ⋙ inverseImage j ≅ directImage v := by
  let := Finite.finiteBaseChange_isIso b v j j' sq
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleLowerShriek j')
      (asIso (baseChangeMap b v j j' sq.w.symm)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleLowerShriekInverseImageIso j') (directImage v) ≪≫
    Functor.leftUnitor _

/-- The ordinary finite/open comparison is the original open counit after the
inverse restriction comparison, rather than a choice of objectwise isomorphisms. -/
def etaleLowerShriekFiniteDirectImage :
    directImage v ⋙ etaleLowerShriek j ⟶ etaleLowerShriek j' ⋙ directImage b :=
  Functor.whiskerRight (etaleLowerShriekFiniteRestrictionIso b v j j' sq).inv
      (etaleLowerShriek j) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (etaleLowerShriek j' ⋙ directImage b)
      (etaleLowerShriekAdjunction j).counit ≫
    (Functor.rightUnitor _).hom

/-- Components retain the original adjunction counit and restriction comparison. -/
theorem etaleLowerShriekFiniteDirectImage_app (G : AbelianSheaf.{u, u + 1} V) :
    (etaleLowerShriekFiniteDirectImage b v j j' sq).app G =
      (etaleLowerShriek j).map
          ((etaleLowerShriekFiniteRestrictionIso b v j j' sq).inv.app G) ≫
        (etaleLowerShriekAdjunction j).counit.app
          ((directImage b).obj ((etaleLowerShriek j').obj G)) := by
  simp [etaleLowerShriekFiniteDirectImage]

/-- The actual open adjunction characterizes the ordinary finite/open comparison. -/
theorem etaleLowerShriekFiniteDirectImage_homEquiv
    (G : AbelianSheaf.{u, u + 1} V) :
    (etaleLowerShriekAdjunction j).homEquiv _ _
        ((etaleLowerShriekFiniteDirectImage b v j j' sq).app G) =
      (etaleLowerShriekFiniteRestrictionIso b v j j' sq).inv.app G := by
  apply ((etaleLowerShriekAdjunction j).homEquiv _ _).eq_symm_apply.mp
  rw [etaleLowerShriekFiniteDirectImage_app]
  exact ((etaleLowerShriekAdjunction j).homEquiv_counit _ _ _).symm

/-- Ordinary finite direct image commutes with open extension for every abelian sheaf. -/
instance etaleLowerShriekFiniteDirectImage_isIso :
    IsIso (etaleLowerShriekFiniteDirectImage b v j j' sq) := by
  have h (G : AbelianSheaf.{u, u + 1} V) :
      IsIso ((etaleLowerShriekFiniteDirectImage b v j j' sq).app G) := by
    rw [etaleLowerShriekFiniteDirectImage_app]
    let := etaleLowerShriek_counit_finiteDirectImage_isIso b v j j' sq G
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The natural finite/open exchange on the original abelian sheaf categories. -/
def etaleLowerShriekFiniteDirectImageIso :
    directImage v ⋙ etaleLowerShriek j ≅ etaleLowerShriek j' ⋙ directImage b :=
  asIso (etaleLowerShriekFiniteDirectImage b v j j' sq)

end AlgebraicGeometry.Scheme.EtaleCohomology
