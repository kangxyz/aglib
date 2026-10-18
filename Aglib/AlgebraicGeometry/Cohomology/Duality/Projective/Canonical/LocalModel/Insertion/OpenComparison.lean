/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Open
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Insertion

/-!
# Comparing actual local arrows on the original model class

The same-normal insertion formula reduces an actual local canonical-map
comparison to the actual image of the original class-one section and of
its original pulled coefficient section. The target homology degree may
already have been transported through a genuine equality.
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

/-- Actual class and coefficient images, together with the actual insertion square,
identify the original canonical model arrow across the given open. -/
theorem regularListCanonicalModelTopHomologyIso_compare_open_class
    {R A D : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]
    {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf (Spec (regularListQuotientRing s))
      (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L)
    (j : Spec D ⟶ Spec (regularListQuotientRing s)) [IsOpenImmersion j]
    {M' Q' P' : (Spec D).Modules} (T : ((closedImmersionRightAdjointRegularListResolutionComplex
      s J).homology (s.length : ℤ)).restrict j ⟶ M') (f' : M' ⟶ Q') (I' : Q' ≅ P')
    (aQ : Q.restrict j ⟶ Q')
    (bP : (restrictFunctor j).obj ((pullback (Spec.map (regularListQuotientMap s))).obj L) ⟶ P')
    (ξ' : M'.val.obj (op ⊤)) (p' : P'.val.obj (op ⊤))
    (hI : (restrictFunctor j).map
        (normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
          (closedImmersionRegularListNormalFrameIso α s hs) Δ).hom ≫ bP = aQ ≫ I'.hom)
    (hClass : T.val.app (op ⊤)
        (regularListModelTopClass s hs J e (1 : A) (j ''ᵁ (⊤ : (Spec D).Opens))) = ξ')
    (hTarget : I'.hom.val.app (op ⊤) (f'.val.app (op ⊤) ξ') = p')
    (hCoefficient : bP.val.app (op ⊤)
        (closedImmersionRegularListCoefficientSection s e (1 : regularListQuotientRing s)
          (j ''ᵁ (⊤ : (Spec D).Opens))) = p') :
    (restrictFunctor j).map (regularListCanonicalModelTopHomologyIso s hs e α J Δ).hom ≫ aQ =
      T ≫ f' := by
  apply (cancel_mono I'.hom).mp
  apply regularListModelTopClass_hom_ext_open s hs J e j
  let U : (Spec D).Opens := ⊤
  let W := j ''ᵁ U
  let z := regularListModelTopClass s hs J e (1 : A) W
  let q := (regularListCanonicalModelTopHomologyIso s hs e α J Δ).hom.val.app (op W) z
  have hLeft : I'.hom.val.app (op U) (aQ.val.app (op U) q) = p' :=
    (congrArg (fun f => f.val.app (op U) q) hI).symm.trans
      ((congrArg (bP.val.app (op U))
        (regularListCanonicalModelTopHomologyIso_insert_class s hs e α J Δ W)).trans
          hCoefficient)
  have hRight : I'.hom.val.app (op U) (f'.val.app (op U) (T.val.app (op U) z)) = p' :=
    (congrArg (fun x => I'.hom.val.app (op U) (f'.val.app (op U) x)) hClass).trans hTarget
  exact hLeft.trans hRight.symm

end AlgebraicGeometry.Scheme.Modules
