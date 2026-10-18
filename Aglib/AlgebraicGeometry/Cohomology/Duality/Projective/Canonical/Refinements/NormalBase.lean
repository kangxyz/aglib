/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalPurity
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# The same intrinsic normal class in different base descriptions

The inverse original conormal comparison sends a kernel class to the
original pullback of that ideal element. Its tensor representative is
`1 tensor x`, independent of the base algebra. Thus the literal ordered
normal wedge used in the canonical map agrees in two base descriptions.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct

universe u w a b
namespace AlgebraicGeometry.Scheme.Modules

variable {R S A B : CommRingCat.{u}}

/-- The intrinsic original ideal pullback, written by its affine kernel-module comparison. -/
def intrinsicConormalIso (σ : A ⟶ B) :
    (pullback (Spec.map σ)).obj (idealModule (Spec.map σ)) ≅
      tilde ((ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom))) :=
  (pullback (Spec.map σ)).mapIso (affineIdealIso σ).symm ≪≫
    (tildePullbackIso σ).app (ModuleCat.of A (RingHom.ker σ.hom))

/-- The actual original ideal section represented by the pure tensor `1 tensor x`. -/
def intrinsicConormalSection (σ : A ⟶ B) (x : RingHom.ker σ.hom)
    (U : (Spec B).Opens) :
    ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))).val.obj (op U) := by
  letI := σ.hom.toAlgebra
  exact (intrinsicConormalIso σ).inv.val.app (op U)
    (tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom)))
      U ((1 : B) ⊗ₜ[A] x))

/-- The inverse original conormal comparison sends the native kernel class to that
same intrinsic ideal-pullback section. -/
theorem relativeConormalIdealClass_intrinsic (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) (U : (Spec B).Opens) :
    (relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
          (relativeConormalAffineClass α σ hσ x)) =
      intrinsicConormalSection σ x U := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let E := relativeConormalAffineExtension α σ hσ
  have hE : E.cotangentEquiv ((1 : B) ⊗ₜ[A] x) =
      relativeConormalAffineClass α σ hσ x := by
    change E.cotangentEquiv ((1 : B) ⊗ₜ[A] x) = Algebra.Extension.Cotangent.mk (P := E) x
    exact (Algebra.Extension.contangentEquiv_tmul (P := E) (1 : B) x).trans (one_smul B _)
  have hi : E.cotangentEquiv.symm (relativeConormalAffineClass α σ hσ x) =
      ((1 : B) ⊗ₜ[A] x) := by
    apply E.cotangentEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact hE.symm
  have ht := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app E.cotangentEquiv.toModuleIso.inv U)
    (relativeConormalAffineClass α σ hσ x)
  change ((tilde.functor B).map E.cotangentEquiv.toModuleIso.inv).val.app (op U)
      (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
        (relativeConormalAffineClass α σ hσ x)) =
    tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom)))
      U (E.cotangentEquiv.symm (relativeConormalAffineClass α σ hσ x)) at ht
  change (intrinsicConormalIso σ).inv.val.app (op U)
      (((tilde.functor B).map E.cotangentEquiv.toModuleIso.inv).val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
          (relativeConormalAffineClass α σ hσ x))) =
    (intrinsicConormalIso σ).inv.val.app (op U)
      (tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom)))
        U ((1 : B) ⊗ₜ[A] x))
  exact congrArg ((intrinsicConormalIso σ).inv.val.app (op U))
    (ht.trans (congrArg
      (tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom))) U)
      hi))

/-- The actual ideal pullback section of a kernel element is independent of its base algebra. -/
theorem relativeConormalIdealClass_base (α : R ⟶ A) (β : S ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) (U : (Spec B).Opens) :
    (relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
          (relativeConormalAffineClass α σ hσ x)) =
      (relativeConormalAffineIdealPullbackIso β σ hσ).inv.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule β σ hσ) U
          (relativeConormalAffineClass β σ hσ x)) :=
  (relativeConormalIdealClass_intrinsic α σ hσ x U).trans
    (relativeConormalIdealClass_intrinsic β σ hσ x U).symm

/-- The same ordered normal wedge is the identical actual section in two base descriptions. -/
theorem regularListNormalSection_base (α : R ⟶ A) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    closedImmersionRegularListNormalSection α s hs U =
      closedImmersionRegularListNormalSection β s hs U := by
  rw [closedImmersionRegularListNormalSection_eq, closedImmersionRegularListNormalSection_eq]
  congr 1

/-- The same ordered normal frame belongs to the immersion, independently of the base map. -/
theorem regularListNormalFrameIso_base (α : R ⟶ A) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) :
    closedImmersionRegularListNormalFrameIso α s hs =
      closedImmersionRegularListNormalFrameIso β s hs := by
  let Z := Spec (regularListQuotientRing s)
  let F := closedImmersionRegularListNormalFrameIso α s hs
  let G := closedImmersionRegularListNormalFrameIso β s hs
  have hi : F.inv = G.inv := by
    apply (unitHomGlobalSectionsEquiv Z _).injective
    change F.inv.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤)) =
      G.inv.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤))
    have hF := closedImmersionRegularListNormalFrameIso_normalSection α s hs ⊤
    have hG := closedImmersionRegularListNormalFrameIso_normalSection β s hs ⊤
    have hFc := congrArg (fun z => z.val.app (op ⊤)
      (closedImmersionRegularListNormalSection α s hs ⊤)) F.hom_inv_id
    have hGc := congrArg (fun z => z.val.app (op ⊤)
      (closedImmersionRegularListNormalSection β s hs ⊤)) G.hom_inv_id
    exact ((congrArg (F.inv.val.app (op ⊤)) hF.symm).trans hFc).trans
      ((regularListNormalSection_base α β s hs ⊤).trans
        ((congrArg (G.inv.val.app (op ⊤)) hG.symm).trans hGc).symm)
  apply Iso.ext
  apply (cancel_epi F.inv).mp
  rw [Iso.inv_hom_id, hi, Iso.inv_hom_id]

/-- The same original dual frame on its fixed intrinsic source object. This only gives its
source a base-independent type; its map is the original native dual frame. -/
def regularListBaseNormalDualFrame (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) :
    Invertible.dualSheaf (Spec (regularListQuotientRing s))
        (moduleExteriorPower (Spec (regularListQuotientRing s))
          ((pullback (Spec.map (regularListQuotientMap s))).obj
            (idealModule (Spec.map (regularListQuotientMap s)))) s.length) ≅
      SheafOfModules.unit (Spec (regularListQuotientRing s)).ringCatSheaf :=
  closedImmersionRegularListNormalDualFrameIso α s hs

/-- Native dual evaluation gives the same original dual frame in the two base descriptions. -/
theorem regularListNormalDualFrameIso_base (α : R ⟶ A) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) :
    regularListBaseNormalDualFrame α s hs = regularListBaseNormalDualFrame β s hs := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro U
  ext ell
  have hn := congrArg (fun F => F.inv.val.app (op U)
    (1 : Γ(Spec (regularListQuotientRing s), U)))
      (regularListNormalFrameIso_base α β s hs)
  exact (closedImmersionRegularListNormalDualFrameIso_hom_evaluation α s hs U ell).trans
    ((congrArg (fun v => ell.val.app (op (Over.mk (𝟙 U))) v) hn).trans
      (closedImmersionRegularListNormalDualFrameIso_hom_evaluation β s hs U ell).symm)

/-- The same inverse normal section evaluates to one on the same intrinsic ordered wedge. -/
theorem regularListNormalDualSection_base (α : R ⟶ A) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    closedImmersionRegularListNormalDualSection α s hs U =
      closedImmersionRegularListNormalDualSection β s hs U := by
  rw [closedImmersionRegularListNormalDualSection_eq,
    closedImmersionRegularListNormalDualSection_eq]
  have h := congrArg (fun F => F.inv.val.app (op U)
    (1 : Γ(Spec (regularListQuotientRing s), U)))
      (regularListNormalDualFrameIso_base α β s hs)
  exact h

/-- The actual inverse normal/coefficient map retains that identical original dual section. -/
theorem regularListInverseNormalLineIso_base (α : R ⟶ A) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) :
    closedImmersionRegularListInverseNormalLineIso α s hs e =
      closedImmersionRegularListInverseNormalLineIso β s hs e := by
  let Z := Spec (regularListQuotientRing s)
  let D := (Invertible.dualLineBundle Z
    (closedImmersionRegularListNormalLineBundle α s hs)).val
  let P := pullback (Spec.map (regularListQuotientMap s))
  let enα := closedImmersionRegularListInverseNormalLineIso α s hs e
  let enβ := closedImmersionRegularListInverseNormalLineIso β s hs e
  apply Iso.ext
  apply (unitHomGlobalSectionsEquiv Z _).injective
  change enα.hom.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤)) =
    enβ.hom.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤))
  have hα := closedImmersionRegularListInverseNormalLineIso_section α s hs e
    (1 : regularListQuotientRing s) ⊤
  have hβ := closedImmersionRegularListInverseNormalLineIso_section β s hs e
    (1 : regularListQuotientRing s) ⊤
  have hν := regularListNormalDualSection_base α β s hs ⊤
  have ht := congrArg (fun ell => moduleTensorSection Z D (P.obj L) ⊤ ell
    (closedImmersionRegularListCoefficientSection s e (1 : regularListQuotientRing s) ⊤)) hν
  have hc := hα.trans (ht.trans hβ.symm)
  have hOne := tilde_toOpen_self_one (R := regularListQuotientRing s) ⊤
  exact (congrArg (enα.hom.val.app (op ⊤)) hOne).symm.trans
    (hc.trans (congrArg (enβ.hom.val.app (op ⊤)) hOne))

section NativeHomology
variable {L : (Spec A).Modules} [L.IsQuasicoherent]
  [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules]

/-- The installed inverse-normal top-homology arrow is independent of the base description. -/
theorem regularListConormalTopHomologyIso_base (α : R ⟶ A) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    [HasDerivedCategory.{b} (Spec (regularListQuotientRing s)).Modules]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) :
    derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e =
      derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso β s hs e := by
  apply Iso.ext
  rw [derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_hom α s hs e,
    derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_hom β s hs e,
    regularListInverseNormalLineIso_base α β s hs e]

end NativeHomology
end AlgebraicGeometry.Scheme.Modules
