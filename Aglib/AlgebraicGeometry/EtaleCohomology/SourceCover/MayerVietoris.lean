/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.MayerVietoris.Relative
public import Aglib.AlgebraicGeometry.Sites.EtaleMayerVietoris.Relative
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Images

/-! # Original relative two-open higher-image gluing

The generic relative sequence is evaluated on the actual source-open product
tests. Native exact precomposition identifies its higher vertices with the
original composite morphisms and original restricted coefficient. Degree one
uses only the original difference epi; higher degrees use the preceding
original overlap. No intermediate open-image acyclicity is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (Q : Square X.Etale)
  [Mono Q.f₂₄] [Mono Q.f₃₄]
  (hQ : Q.IsPullback)
  (hcover : Sieve.ofTwoArrows Q.f₂₄ Q.f₃₄ ∈ X.smallEtaleTopology Q.X₄)

/-- The actual difference of original etale-chart restrictions after direct image. -/
abbrev sourceEtaleSquareCoefficientComplex (F : AbelianSheaf.{u, u + 1} X) :=
  Sheaf.MayerVietoris.coefficientComplex.{_, _, _, _, u + 1}
    X.smallEtaleTopology S.smallEtaleTopology
    (etaleTestSquare f Q) F

include hQ hcover

/-- Original degree-one relative gluing, including literal pulled-back source charts. -/
theorem higherDirectImage_etaleSquare_one_isZero
    (F : AbelianSheaf.{u, u + 1} X)
    [Epi (sourceEtaleSquareCoefficientComplex f Q F).g]
    (hU : IsZero ((higherDirectImage (Q.X₂.hom ≫ f) 1).obj
      ((inverseImage Q.X₂.hom).obj F)))
    (hV : IsZero ((higherDirectImage (Q.X₃.hom ≫ f) 1).obj
      ((inverseImage Q.X₃.hom).obj F))) :
    IsZero ((higherDirectImage (Q.X₄.hom ≫ f) 1).obj
      ((inverseImage Q.X₄.hom).obj F)) := by
  apply IsZero.of_iso ?_ ((sourceEtaleImageRightDerivedIso f Q.X₄ 1).app F).symm
  exact Sheaf.MayerVietoris.rightDerived_isZero_left_one_of_epi.{_, _, _, _, u + 1}
    X.smallEtaleTopology S.smallEtaleTopology (etaleTestSquare f Q)
    (etaleTestSquare_isPullback f Q hQ) (etaleTestSquare_cover f Q hcover)
    (injectiveResolution F)
    (hU.of_iso ((sourceEtaleImageRightDerivedIso f Q.X₂ 1).app F))
    (hV.of_iso ((sourceEtaleImageRightDerivedIso f Q.X₃ 1).app F))

/-- Original higher relative gluing retains the actual composite maps and
coefficient, with the overlap exactly one degree below the other two charts. -/
theorem higherDirectImage_etaleSquare_succ_isZero
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ)
    (hW : IsZero ((higherDirectImage (Q.X₁.hom ≫ f) n).obj
      ((inverseImage Q.X₁.hom).obj F)))
    (hU : IsZero ((higherDirectImage (Q.X₂.hom ≫ f) (n + 1)).obj
      ((inverseImage Q.X₂.hom).obj F)))
    (hV : IsZero ((higherDirectImage (Q.X₃.hom ≫ f) (n + 1)).obj
      ((inverseImage Q.X₃.hom).obj F))) :
    IsZero ((higherDirectImage (Q.X₄.hom ≫ f) (n + 1)).obj
      ((inverseImage Q.X₄.hom).obj F)) := by
  apply IsZero.of_iso ?_ ((sourceEtaleImageRightDerivedIso f Q.X₄ (n + 1)).app F).symm
  exact Sheaf.MayerVietoris.rightDerived_isZero_left_succ_of_vertices.{_, _, _, _, u + 1}
    X.smallEtaleTopology S.smallEtaleTopology (etaleTestSquare f Q)
    (etaleTestSquare_isPullback f Q hQ) (etaleTestSquare_cover f Q hcover)
    (injectiveResolution F) n
    (hW.of_iso ((sourceEtaleImageRightDerivedIso f Q.X₁ n).app F))
    (hU.of_iso ((sourceEtaleImageRightDerivedIso f Q.X₂ (n + 1)).app F))
    (hV.of_iso ((sourceEtaleImageRightDerivedIso f Q.X₃ (n + 1)).app F))

/-- The original source-open difference is the original-square specialization. -/
abbrev sourceOpenCoefficientComplex (U V : X.Opens)
    (F : AbelianSheaf.{u, u + 1} X) :=
  sourceEtaleSquareCoefficientComplex f (etaleOpenSquare U V) F

end AlgebraicGeometry.Scheme.EtaleCohomology
