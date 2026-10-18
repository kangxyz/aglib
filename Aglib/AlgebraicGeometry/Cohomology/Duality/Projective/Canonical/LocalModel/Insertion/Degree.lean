/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Degree
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction.Insertion.ChangeNormal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.NormalFrame

/-!
# The same original insertion in a genuine common normal degree

The actual exterior-degree isomorphism transports both the original normal
frame and the same determinant. The resulting insertion and the original
model class retain their original coefficient value.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w
namespace AlgebraicGeometry.Scheme.Modules

variable {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)

/-- The original normal exterior power in its genuinely equal common degree. -/
def regularListNormalLineInDegree (c : ℕ) (hc : s.length = c) :
    LineBundle (Spec (regularListQuotientRing s)) :=
  lineBundleOfUnitFrame (Spec (regularListQuotientRing s))
    (canonicalAffineNormalFrameInDegree α (regularListQuotientMap s)
      Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm c hc)

/-- Only the genuine original exterior-degree equality changes the normal sheaf. -/
def regularListNormalDegreeIso (c : ℕ) (hc : s.length = c) :
    (closedImmersionRegularListNormalLineBundle α s hs).val ≅
      (regularListNormalLineInDegree α s hs c hc).val :=
  eqToIso (congrArg (moduleExteriorPower (Spec (regularListQuotientRing s))
    ((pullback (Spec.map (regularListQuotientMap s))).obj
      (Hom.idealModule (Spec.map (regularListQuotientMap s))))) hc)

/-- The common normal frame is the same original frame after its inverse degree transport. -/
theorem regularListNormalFrameInDegree_eq (c : ℕ) (hc : s.length = c) :
    canonicalAffineNormalFrameInDegree α (regularListQuotientMap s)
        Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm c hc =
      (regularListNormalDegreeIso α s hs c hc).symm ≪≫
        closedImmersionRegularListNormalFrameIso α s hs := by
  subst c
  simp only [regularListNormalDegreeIso, eqToIso_refl, Iso.refl_symm]
  exact (closedImmersionRegularListNormalFrameIso_eq α s hs).symm

/-- The original determinant in its native degree, using the same common normal factor. -/
def regularListDeterminantFromCommonNormal
    (c : ℕ) (hc : s.length = c)
    {Q P : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf _ (regularListNormalLineInDegree α s hs c hc).val Q ≅ P) :
    tensorSheaf _ (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅ P :=
  ((SheafOfModulesOfCommRing.tensorFunctor (Spec (regularListQuotientRing s)).sheaf).mapIso
    (regularListNormalDegreeIso α s hs c hc)).app Q ≪≫ Δ

/-- Transporting the same normal factor and frame leaves the actual insertion unchanged. -/
theorem regularListInsertionFromCommonNormal
    (c : ℕ) (hc : s.length = c)
    {Q P : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf _ (regularListNormalLineInDegree α s hs c hc).val Q ≅ P) :
    normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
        (closedImmersionRegularListNormalFrameIso α s hs)
        (regularListDeterminantFromCommonNormal α s hs c hc Δ) =
      normalDeterminantInsertionIso (regularListNormalLineInDegree α s hs c hc)
        (canonicalAffineNormalFrameInDegree α (regularListQuotientMap s)
          Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm c hc) Δ := by
  have h := normalDeterminantInsertionIso_transportNormal
    (closedImmersionRegularListNormalLineBundle α s hs)
    (regularListNormalLineInDegree α s hs c hc)
    (closedImmersionRegularListNormalFrameIso α s hs)
    (regularListNormalDegreeIso α s hs c hc) Δ
  rw [← regularListNormalFrameInDegree_eq α s hs c hc] at h
  exact h

variable {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]

/-- The same original model map uses the common normal determinant and genuine homology degree. -/
def regularListCanonicalModelTopHomologyIsoCommonNormal
    (c : ℕ) (hc : s.length = c)
    {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf _ (regularListNormalLineInDegree α s hs c hc).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L) :
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (c : ℤ) ≅ Q :=
  regularListCanonicalModelTopHomologyIsoInDegree s hs J e α
    (regularListDeterminantFromCommonNormal α s hs c hc Δ) c hc

/-- The original common-degree class retains its original coefficient under this same insertion. -/
theorem regularListCanonicalModelTopHomologyIsoCommonNormal_insert_class
    (c : ℕ) (hc : s.length = c)
    {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf _ (regularListNormalLineInDegree α s hs c hc).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    (normalDeterminantInsertionIso (regularListNormalLineInDegree α s hs c hc)
        (canonicalAffineNormalFrameInDegree α (regularListQuotientMap s)
          Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm c hc) Δ).hom.val.app (op U)
      ((regularListCanonicalModelTopHomologyIsoCommonNormal α s hs J e c hc Δ).hom.val.app
        (op U) (regularListModelTopClassInDegree s hs J e c hc (1 : A) U)) =
      closedImmersionRegularListCoefficientSection s e (1 : regularListQuotientRing s) U := by
  have hi := regularListInsertionFromCommonNormal α s hs c hc Δ
  exact (congrArg (fun a => a.hom.val.app (op U)
    ((regularListCanonicalModelTopHomologyIsoCommonNormal α s hs J e c hc Δ).hom.val.app
      (op U) (regularListModelTopClassInDegree s hs J e c hc (1 : A) U))) hi).symm.trans
      (regularListCanonicalModelTopHomologyIsoInDegree_insert_class s hs J e α
        (regularListDeterminantFromCommonNormal α s hs c hc Δ) c hc U)

end AlgebraicGeometry.Scheme.Modules
