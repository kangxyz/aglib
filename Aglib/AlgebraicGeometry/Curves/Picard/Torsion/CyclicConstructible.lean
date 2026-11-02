/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.Torsion.Constructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleCyclicTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Etale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Descent.SurjectiveAffine
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian

/-! # Original cyclic R1 constructibility on a pointed smooth projective curve

The actual finite étale roots-splitting cover is realized through its canonical
`isoSpec`. The same projective embedding and section are base changed. Original
étale exchange, the proved roots R1 endpoint, and surjective affine descent give
constructibility for the original cyclic constant coefficient. No primitive root
on the initial base, separate Picard representer, or constructibility certificate
on the cover is assumed. This uses existing étale exchange, not a new smooth
base-change theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PicardTorsion

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

/-- The literal first higher direct image of the finite cyclic constant
coefficient is constructible. The finite étale roots coordinate is constructed
internally on the original integral affine base. -/
theorem isConstructible_cyclicHigherDirectImage
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsDomain A]
    {ι : Type u} {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι)
    [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1))
    [SmoothOfRelativeDimension 1 (i ≫ ProjectiveSpace.toSpec A ι)]
    [IsProper (i ≫ ProjectiveSpace.toSpec A ι)]
    [Flat (i ≫ ProjectiveSpace.toSpec A ι)]
    [GeometricallyIntegral (i ≫ ProjectiveSpace.toSpec A ι)]
    [GeometricallyConnected (i ≫ ProjectiveSpace.toSpec A ι)]
    (o : Spec (.of A) ⟶ Y) (ho : o ≫ (i ≫ ProjectiveSpace.toSpec A ι) = 𝟙 _)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : A)) :
    IsConstructible ((higherDirectImage (i ≫ ProjectiveSpace.toSpec A ι) 1).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) Y)) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let p := i ≫ ProjectiveSpace.toSpec A ι
  let F := ConstantFinite.coefficient (ULift.{u} (ZMod n)) Y
  let value := ConstantFinite.value (ULift.{u} (ZMod n))
  have hA : IsUnit (n : Γ(Spec (.of A), ⊤)) := by
    simpa only [map_natCast] using hinv.map (Scheme.ΓSpecIso (.of A)).inv.hom
  obtain ⟨T, hsurjT, ⟨eT₀⟩⟩ :=
    GroupCohomology.Kummer.exists_finiteEtale_cyclic_trivialization (Spec (.of A)) n hn hA
  let : Surjective T.obj.hom := hsurjT
  let : IsAffine T.obj.left := isAffine_of_isAffineHom T.obj.hom
  let : IsLocallyNoetherian T.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian T.obj.hom
  let B := Γ(T.obj.left, ⊤)
  let : IsNoetherianRing B :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T.obj.left⟩
  let j : Spec (.of B) ⟶ T.obj.left := T.obj.left.isoSpec.inv
  let b : Spec (.of B) ⟶ Spec (.of A) := j ≫ T.obj.hom
  let : Etale b := inferInstance
  let : Surjective b := inferInstance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective b
  let YB := pullback b p
  let pB : YB ⟶ Spec (.of B) := pullback.fst b p
  let g : YB ⟶ Y := pullback.snd b p
  let a : Over.mk p ⟶ Over.mk (ProjectiveSpace.toSpec A ι) := Over.homMk i rfl
  let aB := ((Over.pullback b).map a).left
  have haB : IsClosedImmersion aB :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) b a
      (inferInstanceAs (IsClosedImmersion i))
  have HP : IsPullback (ProjectiveSpace.map ψ.hom ι) (ProjectiveSpace.toSpec B ι)
      (ProjectiveSpace.toSpec A ι) b := by
    rw [← hψ]
    exact ProjectiveSpace.isPullback_map ψ.hom ι
  let E := HP.isoPullback.symm
  have hE : E.hom ≫ ProjectiveSpace.toSpec B ι =
      pullback.snd (ProjectiveSpace.toSpec A ι) b :=
    (Iso.inv_comp_eq HP.isoPullback).mpr HP.isoPullback_hom_snd.symm
  let iB : YB ⟶ ProjectiveSpace B ι := (pullbackSymmetry b p).hom ≫ aB ≫ E.hom
  have hiB : iB ≫ ProjectiveSpace.toSpec B ι = pB := by
    have hw : aB ≫ pullback.snd (ProjectiveSpace.toSpec A ι) b = pullback.snd p b :=
      Over.w ((Over.pullback b).map a)
    change ((pullbackSymmetry b p).hom ≫ aB ≫ E.hom) ≫ _ = _
    rw [Category.assoc, Category.assoc, hE, hw]
    exact pullbackSymmetry_hom_comp_snd b p
  let : IsClosedImmersion aB := haB
  let : IsClosedImmersion iB := inferInstance
  let oB : Spec (.of B) ⟶ YB := pullback.lift (𝟙 _) (b ≫ o) (by
    rw [Category.id_comp, Category.assoc, ho, Category.comp_id])
  have hoB : oB ≫ (iB ≫ ProjectiveSpace.toSpec B ι) = 𝟙 _ := by
    rw [hiB]
    exact pullback.lift_fst _ _ _
  let : SmoothOfRelativeDimension 1 (iB ≫ ProjectiveSpace.toSpec B ι) := by
    rw [hiB]
    exact MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 1)
      b p (inferInstanceAs (SmoothOfRelativeDimension 1 p))
  let : IsProper (iB ≫ ProjectiveSpace.toSpec B ι) := by
    rw [hiB]
    exact inferInstanceAs (IsProper (pullback.fst b p))
  let : Flat (iB ≫ ProjectiveSpace.toSpec B ι) := by
    rw [hiB]
    exact inferInstanceAs (Flat (pullback.fst b p))
  let : GeometricallyIntegral (iB ≫ ProjectiveSpace.toSpec B ι) := by
    rw [hiB]
    exact inferInstanceAs (GeometricallyIntegral (pullback.fst b p))
  let : GeometricallyConnected (iB ≫ ProjectiveSpace.toSpec B ι) := by
    rw [hiB]
    exact inferInstanceAs (GeometricallyConnected (pullback.fst b p))
  let : ∀ Z : Scheme.{u}, HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z) :=
    fun Z => HasExt.standard _
  let : ∀ U : (Spec (.of B)).Etale, HasExt.{u + 2}
      (Sheaf ((Scheme.smallEtaleTopology YB).over
        ((siteBaseChange (iB ≫ ProjectiveSpace.toSpec B ι)).obj U))
        AddCommGrpCat.{u + 1}) := fun U => HasExt.standard _
  have hBn : IsUnit (n : B) := by simpa only [map_natCast] using hinv.map ψ.hom
  have hroots : IsConstructible ((higherDirectImage pB 1).obj (mu YB n)) := by
    simpa only [hiB] using isConstructible_rootsHigherDirectImage iB e oB hoB n hn hBn
  have hT : IsUnit (n : Γ(T.obj.left, ⊤)) := levelInvertible T.obj.hom n hA
  let eT : mu T.obj.left n ≅ ConstantFinite.coefficient (ULift.{u} (ZMod n)) T.obj.left :=
    (rootsPullbackIso T.obj.hom n hn hA).symm ≪≫ eT₀
  let eS : mu (Spec (.of B)) n ≅
      ConstantFinite.coefficient (ULift.{u} (ZMod n)) (Spec (.of B)) :=
    (rootsPullbackIso j n hn hT).symm ≪≫ (inverseImage j).mapIso eT ≪≫
      (inverseImageConstantIso j).app value
  have hS : IsUnit (n : Γ(Spec (.of B), ⊤)) := levelInvertible j n hT
  let eYB : mu YB n ≅ ConstantFinite.coefficient (ULift.{u} (ZMod n)) YB :=
    (rootsPullbackIso pB n hn hS).symm ≪≫ (inverseImage pB).mapIso eS ≪≫
      (inverseImageConstantIso pB).app value
  let eF : (inverseImage g).obj F ≅ mu YB n :=
    (inverseImageConstantIso g).app value ≪≫ eYB.symm
  let : IsIso (higherBaseChangeMap p pB b g pullback.condition 1) :=
    higherBaseChangeMap_etale_isIso p b 1
  let EBC : (inverseImage b).obj ((higherDirectImage p 1).obj F) ≅
      (higherDirectImage pB 1).obj (mu YB n) :=
    asIso ((higherBaseChangeMap p pB b g pullback.condition 1).app F) ≪≫
      (higherDirectImage pB 1).mapIso eF
  exact isConstructible_of_surjective_pullback_of_isAffine b
    ((higherDirectImage p 1).obj F)
    ((isConstructible_iff_of_iso EBC).mpr hroots)

end AlgebraicGeometry.Scheme.OverField.Curve.PicardTorsion
