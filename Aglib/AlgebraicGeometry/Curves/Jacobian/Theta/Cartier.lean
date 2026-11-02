/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AbelFibres
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EffectiveRankOne
public import Aglib.AlgebraicGeometry.Dimension.FiniteFibreImage
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Dimension
public import Aglib.AlgebraicGeometry.Picard.Abel.Basic

/-!
# The genuine based theta Cartier divisor on the original Jacobian

In positive genus over an algebraically closed field, the actual based
degree-(g-1) Abel image has dimension g-1: its rank-one effective class gives
a finite actual fibre, and the general proper-image theorem supplies the
lower dimension bound. The same Jacobian is integral, smooth and g-dimensional.
The general original-stalk-kernel criterion therefore makes the image
immersion effective Cartier. Its positive line bundle is the dual of that
actual kernel ideal.

The rational base point remains an explicit input. Comparison with the
intrinsic Hilbert Abel image on Pic^(g-1), ampleness, principal polarization
and base-point independence are not conclusions of this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Cohomology Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group

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

-- Keep the original product, component inclusion, and scheme image throughout.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual based degree-(g-1) image has dimension g-1, by one finite
actual fibre. This argument makes no separability or birationality inference. -/
theorem topologicalKrullDim_basedAbelImage_pred_eq (hg : 0 < coherentGenus k X) :
    topologicalKrullDim (basedAbelImage hX o ho P R (coherentGenus k X - 1)) =
      (coherentGenus k X - 1 : ℕ) := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  let n := coherentGenus k X - 1
  obtain ⟨L, hdegree, h0⟩ := exists_lineBundle_degree_pred_genus_h0_one hX P R hg
  have : Nontrivial (moduleCohomology k X L.val 0) := Module.nontrivial_of_finrank_eq_succ h0
  obtain ⟨s, hs⟩ := exists_ne (0 : moduleCohomology k X L.val 0)
  have hs' : moduleH0Equiv X L.val s ≠ 0 := fun hz =>
    hs ((moduleH0Equiv X L.val).injective (hz.trans (moduleH0Equiv X L.val).map_zero.symm))
  obtain ⟨a, ha⟩ := exists_comp_abelMorphism_of_nonzero_section hX o ho P R n L hdegree
    (moduleH0Equiv X L.val s) hs'
  let f := jacobianAbelMorphism hX o ho P R n
  let b := picardPoint P R (classOf X.left L -
    n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho))
  let x := a.left (IsLocalRing.closedPoint k)
  have hfinite := finite_preimage_abelMorphism_of_h0_one hX o ho P R n L h0
  have htriangle : f.left ≫ (identityComponentι P.obj).left =
      (abelMorphism o ho P R n).hom.left :=
    congrArg Over.Hom.left (jacobianAbelMorphism_comp_inclusion hX o ho P R n)
  have hpoint : (abelMorphism o ho P R n).hom.left x = b.left (IsLocalRing.closedPoint k) :=
    congrArg (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ P.obj =>
      q.left (IsLocalRing.closedPoint k)) ha
  have hx : (f.left ⁻¹' {f.left x}).Finite := hfinite.subset (by
    intro z hz
    change f.left z = f.left x at hz
    change (abelMorphism o ho P R n).hom.left z = b.left (IsLocalRing.closedPoint k)
    calc
      (abelMorphism o ho P R n).hom.left z = (identityComponentι P.obj).left (f.left z) :=
        (congrArg (fun q => q z) htriangle).symm
      _ = (identityComponentι P.obj).left (f.left x) :=
        congrArg (identityComponentι P.obj).left hz
      _ = (abelMorphism o ho P R n).hom.left x := congrArg (fun q => q x) htriangle
      _ = b.left (IsLocalRing.closedPoint k) := hpoint)
  have : IsProper f.left := isProper_jacobianAbelMorphism hX o ho P R n
  have : SmoothOfRelativeDimension n (parameter X.hom n).hom :=
    smoothOfRelativeDimension_parameter hX n
  exact Scheme.Hom.topologicalKrullDim_image_eq_of_smooth_of_finite_fibre
    (parameter X.hom n).hom n f.left x hx

-- The same local group structure names the original component and its image.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original degree-(g-1) based Abel image is a genuine effective
Cartier divisor on the same Jacobian, with no theta premise as an input. -/
theorem isEffectiveCartier_basedAbelImage_pred (hg : 0 < coherentGenus k X) :
    Hom.IsEffectiveCartier
      (jacobianAbelMorphism hX o ho P R (coherentGenus k X - 1)).left.imageι := by
  let := picardCommGrpObj X.hom P R
  let n := coherentGenus k X - 1
  let f := (jacobianAbelMorphism hX o ho P R n).left
  have := geometricallyIntegral_identityComponentOver hX P R
  have : IsIntegral (identityComponentOver P.obj).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (identityComponentOver P.obj).hom
  have : IsLocallyNoetherian (identityComponentOver P.obj).left :=
    LocallyOfFiniteType.isLocallyNoetherian (identityComponentOver P.obj).hom
  have : IsIntegral f.image := isIntegral_basedAbelImage hX o ho P R n
  have : IsProper f := isProper_jacobianAbelMorphism hX o ho P R n
  have hregular : ∀ y : (identityComponentOver P.obj).left,
      IsRegularLocalRing ((identityComponentOver P.obj).left.presheaf.stalk y) :=
    smoothFieldRegularity k (identityComponentOver P.obj).left
      (identityComponentOver P.obj).hom (smooth_identityComponentOver hX P R)
  have hdim : topologicalKrullDim f.image = n :=
    topologicalKrullDim_basedAbelImage_pred_eq hX o ho P R hg
  have hJdim : topologicalKrullDim (identityComponentOver P.obj).left ≤
      (n : WithBot ℕ∞) + 1 := by
    rw [topologicalKrullDim_identityComponentOver_eq_coherentGenus hX P R]
    have hn : coherentGenus k X ≤ n + 1 := by dsimp [n]; omega
    exact_mod_cast hn
  have hrange : Set.range f.imageι ≠ Set.univ := by
    intro hrange
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
      f.isClosedMap.isClosed_range.closure_eq] at hrange
    exact not_surjective_jacobianAbelMorphism hX o ho P R (by dsimp [n]; omega)
      (Set.range_eq_univ.mp hrange)
  exact Hom.isEffectiveCartier_of_dimension f.imageι hregular n hdim hJdim hrange

/-- The positive theta line bundle is the dual of the actual Cartier ideal
of the original based image. The rational base point is retained. -/
def thetaLineBundle (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    LineBundle (identityComponentOver P.obj).left := by
  let := picardCommGrpObj X.hom P R
  exact dualLineBundle _ (isEffectiveCartier_basedAbelImage_pred hX o ho P R hg).idealLineBundle

/-- The positive-divisor sign is the negative of the class of the actual
kernel ideal. No Weil-pairing sign convention is involved. -/
theorem classOf_thetaLineBundle (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    classOf _ (thetaLineBundle hX o ho P R hg) =
      -classOf _ (isEffectiveCartier_basedAbelImage_pred hX o ho P R hg).idealLineBundle := by
  let := picardCommGrpObj X.hom P R
  exact classOf_dual _ _

end AlgebraicGeometry.Scheme.OverField.Curve
