/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.RepresentedComparison
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Fppf

/-! Values of the original normalized Picard representation on an étale chart. -/

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open RelativePicard Scheme.Modules.Invertible

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S)
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) [IsProper p] [Flat p] [GeometricallyIntegral p]
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (U : S.Etale)

set_option hygiene false in
local notation "T" => (Scheme.Etale.forget S).obj U

/-- The original étale test as a locally Noetherian test. -/
abbrev locallyNoetherianEtaleTest : LocallyNoetherianOver S :=
  ⟨T, by
    change IsLocallyNoetherian U.left
    exact LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := S) U.hom⟩

/-- The original normalized represented sheaf evaluates the original Picard representative. -/
theorem picardRepresenterNormalizedEtaleIso_hom_app
    (t : T ⟶ P.obj) :
    letI := picardCommGrpObj p P R
    (picardRepresenterNormalizedEtaleIso p o ho P R).hom.hom.app (op U)
        (ULift.up (Additive.ofMul t)) =
      ((normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).inv.app (op T)).hom
        (R.homEquiv (ObjectProperty.homMk t : locallyNoetherianEtaleTest U ⟶ P)) := by
  rfl

/-- The original represented chart sends a family class to its original normalization. -/
theorem picardRepresenterNormalizedEtaleIso_hom_app_of_family
    (t : T ⟶ P.obj) (x : PicardGroup (pullback p (T).hom))
    (h : R.homEquiv (ObjectProperty.homMk t : locallyNoetherianEtaleTest U ⟶ P) =
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T)).hom x) :
    letI := picardCommGrpObj p P R
    (picardRepresenterNormalizedEtaleIso p o ho P R).hom.hom.app (op U)
        (ULift.up (Additive.ofMul t)) = normalizedFamilyClass p o ho T x := by
  let N := normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho
  dsimp only
  rw [picardRepresenterNormalizedEtaleIso_hom_app, h]
  let a := normalizedFamilyClass p o ho T x
  have h₀ : (N.hom.app (op T)).hom a =
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T)).hom x :=
    normalizedFamilyClass_fppf p o ho T x
  rw [← h₀]
  exact congrArg (fun g => g.hom a) (N.hom_inv_id_app (op T))

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
