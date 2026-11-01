/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.DegreeComponent
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicComparison
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Cartier
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism

/-!
# The intrinsic theta Cartier divisor on the existing degree stratum

The origin-free positive ordered Abel image lies in the existing degree-n
Euler open. Its inclusion there is the canonical open-immersion lift of its
ORIGINAL schematic-image immersion. No rational origin occurs in this
definition. In positive genus, choose an origin only inside the proof:
the already constructed based theta image and the actual translation to
the existing degree-(g-1) stratum identify the original kernel ideals.

This proves Cartierness and constructs its positive line bundle on that
degree stratum. It does not assert equality with an unreduced Hilbert-image
model, and it does not assert a theta line bundle on J without an origin.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open ProjectiveSpace
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard
open Scheme.RelativePicard.Strata Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

variable {k : Type u} [Field k] [IsAlgClosed k] {index : Type u} {Y : Scheme.{u}}
  (i : Y ⟶ ProjectiveSpace k index) [IsClosedImmersion i] {N : ℕ}
  (e : index ≃ Fin (N + 1))
  (hX : Properties (Over.mk (i ≫ toSpec k index) : FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec k index)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original positive schematic image lies in the existing degree-n
Euler stratum. The rational origin is chosen only in this proof. -/
theorem range_positiveAbelImage_subset_degreeStratum (n : ℕ) :
    letI := hX.smooth
    letI := hX.proper
    letI := hX.flat
    Set.range (positiveAbelMorphism (Over.mk (i ≫ toSpec k index)) P R n).hom.left.imageι ⊆
      ((eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
        (T := P.obj) (R.homEquiv (𝟙 P)) : Set P.obj.left) := by
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let := picardCommGrpObj (i ≫ toSpec k index) P R
  let X : FScheme k := Over.mk (i ≫ toSpec k index)
  let U := (eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
    (T := P.obj) (R.homEquiv (𝟙 P))
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  let t := degreeStratumTranslationIso i e hX o ho P R n
  let f := (positiveAbelMorphism X P R n).hom.left
  let j := (jacobianAbelMorphism hX o ho P R n).left
  have ht : t.hom ≫ U.ι = (identityComponentι P.obj).left ≫
      (GrpObj.mulRight (picardPoint (X := X) P R
        (n • classOf Y (PointDivisor.positiveLineBundle X hX o ho)))).hom.left :=
    degreeStratumTranslationIso_hom_ι i e hX o ho P R n
  have hf : f = j ≫ t.hom ≫ U.ι := by
    rw [ht]
    exact (jacobianAbelMorphism_comp_translation hX o ho P R n).symm
  have hr : Set.range f ⊆ (U : Set P.obj.left) := by
    rw [← Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine ⟨(j ≫ t.hom) x, ?_⟩
    exact congrArg (fun g : (locallyNoetherianParameter X n).obj.left ⟶ P.obj.left =>
      g x) hf.symm
  have : IsProper f := isProper_positiveAbelMorphism X P R n
  change Set.range f.imageι ⊆ (U : Set P.obj.left)
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  exact closure_minimal hr
    (isClopen_opens_eulerCondition_degreeStratumPolynomial i e P R hX n).isClosed

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical inclusion of the ORIGINAL origin-free positive image
into the EXISTING degree stratum. It has no rational-origin parameter. -/
def positiveAbelImageInDegree (n : ℕ) :
    letI := hX.smooth
    letI := hX.proper
    letI := hX.flat
    positiveAbelImage (Over.mk (i ≫ toSpec k index)) P R n ⟶
      ((eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
        (T := P.obj) (R.homEquiv (𝟙 P))).toScheme := by
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let U := (eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
    (T := P.obj) (R.homEquiv (𝟙 P))
  let f := (positiveAbelMorphism (Over.mk (i ≫ toSpec k index)) P R n).hom.left
  have hr : Set.range f.imageι ⊆ (U : Set P.obj.left) :=
    range_positiveAbelImage_subset_degreeStratum i e hX P R n
  have hr' : Set.range f.imageι ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hr
  exact IsOpenImmersion.lift U.ι
    f.imageι hr'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The intrinsic inclusion retains the literal original immersion into P. -/
theorem positiveAbelImageInDegree_comp_ι (n : ℕ) :
    letI := hX.smooth
    letI := hX.proper
    letI := hX.flat
    positiveAbelImageInDegree i e hX P R n ≫
      ((eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
        (T := P.obj) (R.homEquiv (𝟙 P))).ι =
      (positiveAbelMorphism (Over.mk (i ≫ toSpec k index)) P R n).hom.left.imageι := by
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let U := (eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
    (T := P.obj) (R.homEquiv (𝟙 P))
  let f := (positiveAbelMorphism (Over.mk (i ≫ toSpec k index)) P R n).hom.left
  have hr : Set.range f.imageι ⊆ (U : Set P.obj.left) :=
    range_positiveAbelImage_subset_degreeStratum i e hX P R n
  have hr' : Set.range f.imageι ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hr
  exact IsOpenImmersion.lift_fac U.ι f.imageι hr'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical intrinsic inclusion is a closed immersion, as the
actual pullback of the original schematic-image immersion to its open. -/
theorem isClosedImmersion_positiveAbelImageInDegree (n : ℕ) :
    IsClosedImmersion (positiveAbelImageInDegree i e hX P R n) := by
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let f := (positiveAbelMorphism (Over.mk (i ≫ toSpec k index)) P R n).hom.left
  let U := (eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
    (T := P.obj) (R.homEquiv (𝟙 P))
  have H : IsPullback (𝟙 f.image) (positiveAbelImageInDegree i e hX P R n) f.imageι U.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by
      simpa only [Category.id_comp] using (positiveAbelImageInDegree_comp_ι i e hX P R n).symm⟩
  exact MorphismProperty.of_isPullback H inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original positive degree-(g-1) image is a genuine intrinsic
effective Cartier divisor on the existing Pic^(g-1) Euler stratum. -/
theorem isEffectiveCartier_intrinsicTheta
    (hg : 0 < coherentGenus k (Over.mk (i ≫ toSpec k index))) :
    Hom.IsEffectiveCartier (positiveAbelImageInDegree i e hX P R
      (coherentGenus k (Over.mk (i ≫ toSpec k index)) - 1)) := by
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let := picardCommGrpObj (i ≫ toSpec k index) P R
  let X : FScheme k := Over.mk (i ≫ toSpec k index)
  let n := coherentGenus k X - 1
  let U := (eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
    (T := P.obj) (R.homEquiv (𝟙 P))
  let a := positiveAbelImageInDegree i e hX P R n
  have : IsClosedImmersion a := isClosedImmersion_positiveAbelImageInDegree i e hX P R n
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  let j := (jacobianAbelMorphism hX o ho P R n).left.imageι
  let eD := basedAbelImageIsoPositive hX o ho P R n
  let eJ := degreeStratumTranslationIso i e hX o ho P R n
  have hJ : Hom.IsEffectiveCartier j := isEffectiveCartier_basedAbelImage_pred hX o ho P R hg
  have hw : eD.hom ≫ a = j ≫ eJ.hom := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, positiveAbelImageInDegree_comp_ι,
      basedAbelImageIsoPositive_hom_comp, Category.assoc, degreeStratumTranslationIso_hom_ι]
    rfl
  have hwinv : eD.inv ≫ j = a ≫ eJ.inv := by
    apply (cancel_mono eJ.hom).mp
    calc
      (eD.inv ≫ j) ≫ eJ.hom = eD.inv ≫ (j ≫ eJ.hom) := Category.assoc _ _ _
      _ = eD.inv ≫ (eD.hom ≫ a) := by rw [hw]
      _ = a := eD.inv_hom_id_assoc a
      _ = (a ≫ eJ.inv) ≫ eJ.hom := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have : IsIso (Hom.idealPullbackMap j a eJ.inv eD.inv hwinv) :=
    Hom.idealPullbackMap_isIso_of_iso_square j a eJ.inv eD.inv hwinv
  exact ⟨inferInstance, isLocallyRankOne_of_iso U.toScheme
    (asIso (Hom.idealPullbackMap j a eJ.inv eD.inv hwinv))
    (pullback_locallyRankOne eJ.inv _ hJ.isLocallyRankOne)⟩

/-- The positive line bundle of the intrinsic theta divisor lives on the
existing degree-(g-1) stratum, with no rational origin in its data. -/
def intrinsicThetaLineBundle
    (hg : 0 < coherentGenus k (Over.mk (i ≫ toSpec k index))) :
    letI := hX.flat
    LineBundle ((eulerCondition i N e (degreeStratumPolynomial i hX
      ((coherentGenus k (Over.mk (i ≫ toSpec k index)) - 1 : ℕ) : ℤ))).opens
        (T := P.obj) (R.homEquiv (𝟙 P))).toScheme := by
  let := hX.flat
  exact dualLineBundle _ (isEffectiveCartier_intrinsicTheta i e hX P R hg).idealLineBundle

end AlgebraicGeometry.Scheme.OverField.Curve
