/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Insertion.OpenComparison
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Insertion.Degree
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.OpenTop

/-!
# Actual open comparisons of the canonical model arrows

The original class, the same normal insertion and the original coefficient
section identify the actual native homology arrows. Genuine common-degree
transport is retained in the target map and class.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

/-- The original source class and the original common-normal target insertion identify the
actual model arrows once their original insertion and coefficient images agree. -/
theorem regularListCanonicalModelTopHomologyIso_compare_commonNormal
    {R A R' A' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (s : List A) (t : List A') (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A' t) (hc : t.length = s.length)
    {L : (Spec A).Modules} {L' : (Spec A').Modules}
    [L.IsQuasicoherent] [L'.IsQuasicoherent]
    (J : InjectiveResolution L) (J' : InjectiveResolution L')
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
    (e' : moduleSpecΓFunctor.obj L' ≅ ModuleCat.of A' A')
    [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} A')]
    {Q : (Spec (regularListQuotientRing s)).Modules}
    {Q' : (Spec (regularListQuotientRing t)).Modules}
    (Δ : tensorSheaf _ (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (Δ' : tensorSheaf _ (regularListNormalLineInDegree α' t ht s.length hc).val Q' ≅
      (pullback (Spec.map (regularListQuotientMap t))).obj L')
    (j : Spec (regularListQuotientRing t) ⟶ Spec (regularListQuotientRing s))
    [IsOpenImmersion j]
    (T : ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ)).restrict j ⟶
      (closedImmersionRightAdjointRegularListResolutionComplex t J').homology (s.length : ℤ))
    (aQ : Q.restrict j ⟶ Q')
    (bP : ((pullback (Spec.map (regularListQuotientMap s))).obj L).restrict j ⟶
      (pullback (Spec.map (regularListQuotientMap t))).obj L')
    (hI : (restrictFunctor j).map
        (normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
          (closedImmersionRegularListNormalFrameIso α s hs) Δ).hom ≫ bP =
      aQ ≫ (normalDeterminantInsertionIso
        (regularListNormalLineInDegree α' t ht s.length hc)
        (canonicalAffineNormalFrameInDegree α' (regularListQuotientMap t)
          Ideal.Quotient.mk_surjective t ht Ideal.mk_ker.symm s.length hc) Δ').hom)
    (hClass : T.val.app (op ⊤)
        (regularListModelTopClass s hs J e (1 : A) (j ''ᵁ ⊤)) =
      regularListModelTopClassInDegree t ht J' e' s.length hc (1 : A') ⊤)
    (hCoefficient : bP.val.app (op ⊤)
        (closedImmersionRegularListCoefficientSection s e (1 : regularListQuotientRing s)
          (j ''ᵁ ⊤)) =
      closedImmersionRegularListCoefficientSection t e' (1 : regularListQuotientRing t) ⊤) :
    (restrictFunctor j).map (regularListCanonicalModelTopHomologyIso s hs e α J Δ).hom ≫ aQ =
      T ≫ (regularListCanonicalModelTopHomologyIsoCommonNormal
        α' t ht J' e' s.length hc Δ').hom := by
  exact regularListCanonicalModelTopHomologyIso_compare_open_class α s hs J e Δ j T
    (regularListCanonicalModelTopHomologyIsoCommonNormal α' t ht J' e' s.length hc Δ').hom
    (normalDeterminantInsertionIso (regularListNormalLineInDegree α' t ht s.length hc)
      (canonicalAffineNormalFrameInDegree α' (regularListQuotientMap t)
        Ideal.Quotient.mk_surjective t ht Ideal.mk_ker.symm s.length hc) Δ')
    aQ bP (regularListModelTopClassInDegree t ht J' e' s.length hc (1 : A') ⊤)
    (closedImmersionRegularListCoefficientSection t e' (1 : regularListQuotientRing t) ⊤)
    hI hClass
    (regularListCanonicalModelTopHomologyIsoCommonNormal_insert_class α' t ht J' e'
      s.length hc Δ' ⊤) hCoefficient

end AlgebraicGeometry.Scheme.Modules
