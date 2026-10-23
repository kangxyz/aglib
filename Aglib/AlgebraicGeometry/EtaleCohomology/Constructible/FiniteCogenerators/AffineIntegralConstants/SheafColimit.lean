/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.AffineIntegralConstants.RepresentedSections
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Actual finite-constant direct-image colimits on an affine base

The finite-generated subalgebra diagram gives an actual sheaf colimit of
finite-constant direct images. Integrality is used only to make its stages
finite over the original base. The proof compares original scheme-section
maps on affine étale tests, then reflects the pointwise colimit through the
actual affine restriction and the fully faithful sheaf inclusion.

Only the fixed finite-constant case is exported. No general varying-scheme
coefficient continuity or nonaffine integral approximation is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.AffineIntegralConstants

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory
  IsCofiltered.isConnected

private def fixedTest {X : Scheme.{u}} (U : X.Etale) : Over X ⥤ Over X where
  obj Y := (directImageTests Y).obj U
  map a := (directImageTestsMap a).app U
  map_id Y := congr_app (directImageTestsMap_id Y) U
  map_comp a b := congr_app (directImageTestsMap_comp a b) U

private def fixedTestUnderlyingIso {X : Scheme.{u}} (U : X.Etale) :
    fixedTest U ⋙ Over.forget X ≅
      Over.pullback ((Scheme.Etale.forget X).obj U).hom ⋙
        Over.forget ((Scheme.Etale.forget X).obj U).left :=
  NatIso.ofComponents
    (fun Y => pullbackSymmetry ((Scheme.Etale.forget X).obj U).hom Y.hom) (by
      intro Y Z a
      let U₀ := (Scheme.Etale.forget X).obj U
      change (baseChangedTestMap U₀ a).left ≫ (pullbackSymmetry U₀.hom Z.hom).hom =
        (pullbackSymmetry U₀.hom Y.hom).hom ≫ ((Over.pullback U₀.hom).map a).left
      have hf : ((Over.pullback U₀.hom).map a).left ≫ pullback.fst Z.hom U₀.hom =
          pullback.fst Y.hom U₀.hom ≫ a.left := pullback.lift_fst _ _ _
      have hs : ((Over.pullback U₀.hom).map a).left ≫ pullback.snd Z.hom U₀.hom =
          pullback.snd Y.hom U₀.hom := pullback.lift_snd _ _ _
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [pullbackSymmetry_hom_comp_fst U₀.hom Z.hom, baseChangedTestMap_snd U₀ a, hf,
          ← Category.assoc, pullbackSymmetry_hom_comp_fst U₀.hom Y.hom]
      · simp only [Category.assoc]
        rw [pullbackSymmetry_hom_comp_snd U₀.hom Z.hom, baseChangedTestMap_fst U₀ a, hs,
          pullbackSymmetry_hom_comp_snd U₀.hom Y.hom])

private def directImageEvaluationIso {X : Scheme.{u}}
    (B : Type u) [AddCommGroup B] [Finite B] (U : X.Etale) :
    constantRepresentedDirectImageFunctor (X := X) B ⋙
        (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) ≅
      (fixedTest U).op ⋙ sectionFunctor (ConstantFinite.representation B X).group :=
  NatIso.ofComponents
    (fun Y => (constantDirectImageCoordinatesIso B Y.unop).app (op U)) (by
      intro Y Z a
      exact congr_app (constantRepresentedDirectImageMap_coordinates B a.unop) (op U))

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

private def fixedTestConeIsLimit (U : (Spec (.of R)).Etale) :
    IsLimit ((fixedTest U).mapCone (Scheme.FiniteTypeSubalgebraLimit.baseCone R A)) := by
  have : PreservesLimit (Scheme.FiniteTypeSubalgebraLimit.baseDiagram R A)
      (fixedTest U ⋙ Over.forget (Spec (.of R))) :=
    preservesLimit_of_natIso _ (fixedTestUnderlyingIso U).symm
  exact isLimitOfReflects (Over.forget (Spec (.of R)))
    (isLimitOfPreserves (fixedTest U ⋙ Over.forget (Spec (.of R)))
      (Scheme.FiniteTypeSubalgebraLimit.baseConeIsLimit R A))

private def fixedConstantSectionCoconeIsColimit
    (B : Type u) [AddCommGroup B] [Finite B]
    (U : (Spec (.of R)).Etale) [IsAffine U.left] :
    IsColimit ((sectionFunctor (ConstantFinite.representation B (Spec (.of R))).group).mapCocone
      ((fixedTest U).mapCone (Scheme.FiniteTypeSubalgebraLimit.baseCone R A)).op) := by
  let D := Scheme.FiniteTypeSubalgebraLimit.baseDiagram R A ⋙ fixedTest U
  let H := (ConstantFinite.representation B (Spec (.of R))).group
  have (i : (Finset A)ᵒᵖ) : IsAffine (D.obj i).left := by
    change IsAffine (pullback U.hom
      (Spec.algebraMap R (Algebra.FiniteTypeSubalgebraLimit.stage R A i.unop)))
    exact @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine U.left
      (Spec (.of (Algebra.FiniteTypeSubalgebraLimit.stage R A i.unop))) (Spec (.of R))
      U.hom (Spec.algebraMap R (Algebra.FiniteTypeSubalgebraLimit.stage R A i.unop))
      inferInstance inferInstance inferInstance
  have (i : (Finset A)ᵒᵖ) : CompactSpace (D.obj i).left := inferInstance
  have (i : (Finset A)ᵒᵖ) : QuasiSeparatedSpace (D.obj i).left := inferInstance
  have {i j : (Finset A)ᵒᵖ} (a : i ⟶ j) : IsAffineHom (D.map a).left := inferInstance
  have : PreservesColimit D.op
      (sectionFunctor H ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesColimit_of_natIso D.op (sectionFunctorForgetIso H).symm
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have : ReflectsColimit (D.op ⋙ sectionFunctor H)
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u + 1})
  exact isColimitOfPreserves (sectionFunctor H ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})
    (fixedTestConeIsLimit R A U).op

private def affineDirectImageCoconeIsColimit
    (B : Type u) [AddCommGroup B] [Finite B]
    (U : (Spec (.of R)).Etale) [IsAffine U.left] :
    IsColimit (((sheafSections (Spec (.of R)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (op U)).mapCocone
        ((constantRepresentedDirectImageFunctor (X := Spec (.of R)) B).mapCocone
          (Scheme.FiniteTypeSubalgebraLimit.baseCone R A).op)) := by
  have h := fixedConstantSectionCoconeIsColimit R A B U
  change IsColimit (((fixedTest U).op ⋙
    sectionFunctor (ConstantFinite.representation B (Spec (.of R))).group).mapCocone
      (Scheme.FiniteTypeSubalgebraLimit.baseCone R A).op) at h
  exact IsColimit.mapCoconeEquiv (directImageEvaluationIso B U).symm h

variable (B : Type u) [AddCommGroup B] [Finite B]

/-- Literal finite-constant pushforwards, with the transitions supplied by the
original section coordinates and original represented/constant transports. -/
def constantPushforwardFunctor {X : Scheme.{u}} :
    (Over X)ᵒᵖ ⥤ AbelianSheaf.{u, u + 1} X :=
  (constantRepresentedDirectImageFunctor (X := X) B).copyObj
    (fun Y => (directImage Y.unop.hom).obj (ConstantFinite.coefficient B Y.unop.left))
    (fun Y => constantRepresentedDirectImageIso B Y.unop)

/-- The coordinate comparison keeps its specified original coefficient isomorphisms. -/
def constantPushforwardFunctorIso {X : Scheme.{u}} :
    constantRepresentedDirectImageFunctor (X := X) B ≅ constantPushforwardFunctor B :=
  (constantRepresentedDirectImageFunctor (X := X) B).isoCopyObj _ _

/-- Each morphism is the original geometric section map with the displayed
original coefficient transports. -/
theorem constantPushforwardFunctor_map {X : Scheme.{u}} {Y Z : (Over X)ᵒᵖ}
    (a : Y ⟶ Z) :
    (constantPushforwardFunctor B).map a =
      (constantRepresentedDirectImageIso B Y.unop).inv ≫
        constantRepresentedDirectImageMap B a.unop ≫
          (constantRepresentedDirectImageIso B Z.unop).hom := rfl

/-- The actual finite-generated subalgebra diagram of finite-constant pushforwards. -/
def constantPushforwardDiagram : (Finset A)ᵒᵖᵒᵖ ⥤ AbelianSheaf.{u, u + 1} (Spec (.of R)) :=
  (Scheme.FiniteTypeSubalgebraLimit.baseDiagram R A).op ⋙ constantPushforwardFunctor B

/-- The original spectrum cone gives the actual finite-constant direct-image cocone. -/
def constantPushforwardCocone : Cocone (constantPushforwardDiagram R A B) :=
  (constantPushforwardFunctor B).mapCocone
    (Scheme.FiniteTypeSubalgebraLimit.baseCone R A).op

/-- The cocone point is the literal constant pushforward from the original algebra. -/
theorem constantPushforwardCocone_pt :
    (constantPushforwardCocone R A B).pt =
      (directImage (Spec.algebraMap R A)).obj
        (ConstantFinite.coefficient B (Spec (.of A))) := rfl

/-- The cocone map at a stage is the original scheme-projection section map,
with exactly the displayed represented/constant transports. -/
theorem constantPushforwardCocone_ι (s : Finset A) :
    (constantPushforwardCocone R A B).ι.app (op (op s)) =
      (constantRepresentedDirectImageIso B
        ((Scheme.FiniteTypeSubalgebraLimit.baseDiagram R A).obj (op s))).inv ≫
      constantRepresentedDirectImageMap B
        ((Scheme.FiniteTypeSubalgebraLimit.baseCone R A).π.app (op s)) ≫
      (constantRepresentedDirectImageIso B
        (Scheme.FiniteTypeSubalgebraLimit.baseCone R A).pt).hom := rfl

/-- Finite-constant direct images along the finite-generated subalgebras form
the original sheaf colimit. No integrality or Noetherian hypothesis is needed. -/
theorem nonempty_constantPushforwardCoconeIsColimit :
    Nonempty (IsColimit (constantPushforwardCocone R A B)) := by
  have h : IsColimit
      ((constantRepresentedDirectImageFunctor (X := Spec (.of R)) B).mapCocone
        (Scheme.FiniteTypeSubalgebraLimit.baseCone R A).op) := by
    apply isColimitOfReflects (EtaleAffineBasis.abelianRestriction (Spec (.of R)))
    apply isColimitOfReflects (sheafToPresheaf
      (Scheme.AffineEtale.topology (Spec (.of R))) AddCommGrpCat.{u + 1})
    apply evaluationJointlyReflectsColimits
    intro U
    have : IsAffine ((Scheme.AffineEtale.Spec (Spec (.of R))).obj U.unop).left := by
      change IsAffine (Spec U.unop.left.unop)
      infer_instance
    exact affineDirectImageCoconeIsColimit R A B
      ((Scheme.AffineEtale.Spec (Spec (.of R))).obj U.unop)
  exact ⟨IsColimit.mapCoconeEquiv (constantPushforwardFunctorIso B) h⟩

/-- The universal property of the fixed original finite-constant direct-image cocone. -/
def constantPushforwardCoconeIsColimit :
    IsColimit (constantPushforwardCocone R A B) :=
  Classical.choice (nonempty_constantPushforwardCoconeIsColimit R A B)

/-- Integrality makes every original algebra stage finite over the original base. -/
theorem constantPushforwardStage_isFinite [Algebra.IsIntegral R A] (s : Finset A) :
    IsFinite ((Scheme.FiniteTypeSubalgebraLimit.baseDiagram R A).obj (op s)).hom :=
  stageMap_isFinite R A s

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.AffineIntegralConstants
