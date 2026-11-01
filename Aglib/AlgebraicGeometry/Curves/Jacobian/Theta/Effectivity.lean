/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Cartier
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.PositiveSection
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# The actual nonzero section of the positive theta line bundle

Transpose the original theta ideal inclusion, then apply the existing
unit-module/global-section equivalence. This constructs a named section of
the same theta line bundle. Its nonvanishing follows from monicity of the
original ideal inclusion on the integral Jacobian. No ampleness, finite
kernel, or polarization assertion is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

/-- The canonical positive theta section as an actual unit-module morphism. -/
def thetaSectionHom (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    (show (identityComponentOver P.obj).left.Modules from
      SheafOfModules.unit (identityComponentOver P.obj).left.ringCatSheaf) ⟶
        (thetaLineBundle hX o ho P R hg).val := by
  let := picardCommGrpObj X.hom P R
  exact Hom.divisorPositiveSection
    (jacobianAbelMorphism hX o ho P R (coherentGenus k X - 1)).left.imageι
    (isEffectiveCartier_basedAbelImage_pred hX o ho P R hg).isLocallyRankOne

-- The transpose is the original ideal-inclusion transpose in the native module category.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem thetaSectionHom_ne_zero (hg : 0 < coherentGenus k X) :
    thetaSectionHom hX o ho P R hg ≠ 0 := by
  let := picardCommGrpObj X.hom P R
  have := geometricallyIntegral_identityComponentOver hX P R
  have : IsIntegral (identityComponentOver P.obj).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (identityComponentOver P.obj).hom
  let i := (jacobianAbelMorphism hX o ho P R (coherentGenus k X - 1)).left.imageι
  let hI := isEffectiveCartier_basedAbelImage_pred hX o ho P R hg
  change InternalHom.transpose (identityComponentOver P.obj).left (Hom.idealInclusion i) ≠ 0
  exact InternalHom.transpose_ne_zero _
    (lineBundleMap_ne_zero_of_mono _ hI.idealLineBundle (Hom.idealInclusion i))

/-- The original global section corresponding to the canonical positive
theta unit-module morphism. -/
def thetaSection (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    Γ((thetaLineBundle hX o ho P R hg).val, ⊤) := by
  let := picardCommGrpObj X.hom P R
  exact unitHomGlobalSectionsAddEquiv (identityComponentOver P.obj).left
    (thetaLineBundle hX o ho P R hg).val (thetaSectionHom hX o ho P R hg)

theorem thetaSection_ne_zero (hg : 0 < coherentGenus k X) :
    thetaSection hX o ho P R hg ≠ 0 := by
  let := picardCommGrpObj X.hom P R
  intro hzero
  apply thetaSectionHom_ne_zero hX o ho P R hg
  exact (unitHomGlobalSectionsAddEquiv (identityComponentOver P.obj).left
    (thetaLineBundle hX o ho P R hg).val).injective
      (hzero.trans (map_zero (unitHomGlobalSectionsAddEquiv
        (identityComponentOver P.obj).left (thetaLineBundle hX o ho P R hg).val)).symm)

/-- Effectivity in the existing ampleness criterion's exact global-section
interface, retaining the same original theta line bundle. -/
theorem exists_nonzero_thetaSection (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    ∃ s : Γ((thetaLineBundle hX o ho P R hg).val, ⊤), s ≠ 0 :=
  ⟨thetaSection hX o ho P R hg, thetaSection_ne_zero hX o ho P R hg⟩

end AlgebraicGeometry.Scheme.OverField.Curve
