/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Conormal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf.Class

/-!
# The actual local purity map contracted by the normal determinant

This leaf composes the installed regular-list right-adjoint comparison with
the inverse of the same normal-first determinant and native dual evaluation.
The coefficient stays the original pulled-back sheaf. The class formula
retains the original Koszul class, model comparison, affine counit, and tilde
sections; no replacement purity object or comparison family is assumed.

The determinant is an explicit argument of this local construction. The
geometric canonical-bundle theorem must construct that determinant from the
actual conormal sequence and establish its common-refinement equations.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w a b
namespace AlgebraicGeometry.Scheme.Modules

variable {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)

variable {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec (regularListQuotientRing s)).Modules]

/-- The independently installed native right-adjoint object; this is only an abbreviation. -/
abbrev closedImmersionRegularListDerivedValue :
    DerivedCategory.Plus (Spec (regularListQuotientRing s)).Modules :=
  (closedImmersionRightAdjoint (Spec.map (regularListQuotientMap s))).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj L)

local instance canonicalLocalPuritySectionsAdditive :
    (moduleSpecΓFunctor (R := (regularListQuotientRing s))).Additive :=
  moduleSpecΓFunctor_additive _

/-- The original native homology section represented by the ordered top Koszul class. -/
@[no_expose] def closedImmersionRegularListNativeTopClass (r : A)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    ((DerivedCategory.Plus.homologyFunctor (Spec (regularListQuotientRing s)).Modules
      (s.length : ℤ)).obj (closedImmersionRegularListDerivedValue (L := L) s)).val.obj (op U) :=
  (derivedClosedImmersionRightAdjointRegularListModelHomologyIso s (injectiveResolution L)
    (s.length : ℤ)).inv.val.app (op U)
      (regularListModelTopClass s hs (injectiveResolution L) e r U)

/-- The native class retains its literal original model, affine counit and tilde section. -/
theorem closedImmersionRegularListNativeTopClass_eq (r : A)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    let J := injectiveResolution L
    let : QuasiIso (Complex.tildeGlobalSectionsCounit (regularListQuotientRing s) (.up ℤ)
      (closedImmersionRightAdjointRegularListResolutionComplex s J)) :=
        closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J e
    let C := closedImmersionRightAdjointRegularListResolutionComplex s J
    let G := ((moduleSpecΓFunctor (R := regularListQuotientRing s)).mapHomologicalComplex
      (.up ℤ)).obj C
    let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
      s.length).symm
      ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) r).comp
        (Ext.mk₀ e.inv) (Nat.add_zero s.length))
    closedImmersionRegularListNativeTopClass s hs e r U =
      (derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J
        (s.length : ℤ)).inv.val.app (op U)
        ((Complex.tildeGlobalSectionsHomologyIso (regularListQuotientRing s) (.up ℤ) C
          (s.length : ℤ)).hom.val.app (op U)
          (tilde.toOpen (G.homology (s.length : ℤ)) U ξ)) := by
  rfl

private theorem localIsoSections_injective {Z : Scheme.{u}} {M N : Z.Modules}
    (E : M ≅ N) (U : Z.Opens) : Function.Injective (E.hom.val.app (op U)) := by
  intro x y h
  have hx := congrArg (fun f => f.val.app (op U) x) E.hom_inv_id
  have hy := congrArg (fun f => f.val.app (op U) y) E.hom_inv_id
  exact hx.symm.trans ((congrArg (E.inv.val.app (op U)) h).trans hy)

/-- Evaluate the complete original factorization with an explicitly supplied
representative equation, before specializing any native derived coefficient. -/
private theorem localFactorization_value {Z : Scheme.{u}} {M N P : Z.Modules}
    (F : M ⟶ N) (G : N ⟶ P) (K : M ⟶ P) (hK : K = F ≫ G)
    (U : Z.Opens) (x x₀ : M.val.obj (op U)) (y : N.val.obj (op U))
    (hx : x = x₀) (hF : F.val.app (op U) x₀ = y) :
    K.val.app (op U) x = G.val.app (op U) y := by
  subst K
  change G.val.app (op U) (F.val.app (op U) x) = G.val.app (op U) y
  exact congrArg (G.val.app (op U)) ((congrArg (F.val.app (op U)) hx).trans hF)

/-- Evaluate the complete original model-to-native frame, cancelling only
its original model isomorphism before specializing the derived objects. -/
private theorem localModelFrame_value {Z : Scheme.{u}} {M N P : Z.Modules}
    (E : M ≅ N) (F : N ⟶ P) (K : M ⟶ P) (hK : K = E.hom ≫ F)
    (U : Z.Opens) (z : N.val.obj (op U)) (y : P.val.obj (op U))
    (hF : F.val.app (op U) z = y) :
    K.val.app (op U) (E.inv.val.app (op U) z) = y := by
  have h := congrArg (fun f => f.val.app (op U) z) E.inv_hom_id
  exact (localFactorization_value E.hom F K hK U
    (E.inv.val.app (op U) z) (E.inv.val.app (op U) z) z rfl h).trans hF

/-- The original native top class has its original quotient value in the native unit frame. -/
theorem closedImmersionRegularListNativeTopClass_unitFrame (r : A)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs
      (injectiveResolution L) e).hom.val.app (op U)
      (closedImmersionRegularListNativeTopClass s hs e r U) =
        tilde.toOpen (ModuleCat.of (regularListQuotientRing s) (regularListQuotientRing s)) U
          (Ideal.Quotient.mk (Ideal.ofList s) r) := by
  exact localModelFrame_value
    (derivedClosedImmersionRightAdjointRegularListModelHomologyIso s (injectiveResolution L)
      (s.length : ℤ))
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs
      (injectiveResolution L) e).hom
    (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs
      (injectiveResolution L) e).hom
    (derivedClosedImmersionRightAdjointRegularListTopHomologyIso_hom s hs
      (injectiveResolution L) e) U
    (regularListModelTopClass s hs (injectiveResolution L) e r U) _
    (regularListModelTopClass_unitFrame s hs (injectiveResolution L) e r U)

/-- In particular the original class of one is the section-one generator of the native frame. -/
theorem closedImmersionRegularListNativeTopClass_one
    (U : (Spec (regularListQuotientRing s)).Opens) :
    (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs
      (injectiveResolution L) e).hom.val.app (op U)
      (closedImmersionRegularListNativeTopClass s hs e (1 : A) U) =
        (1 : Γ(Spec (regularListQuotientRing s), U)) := by
  have h := closedImmersionRegularListNativeTopClass_unitFrame s hs e (1 : A) U
  rw [map_one] at h
  exact h.trans (tilde_toOpen_self_one (R := regularListQuotientRing s) U)

/-- Equality on the original class-one sections proves equality of the actual homology arrows. -/
theorem closedImmersionRegularListNativeTopClass_hom_ext
    {N : (Spec (regularListQuotientRing s)).Modules}
    {f g : (DerivedCategory.Plus.homologyFunctor (Spec (regularListQuotientRing s)).Modules
      (s.length : ℤ)).obj (closedImmersionRegularListDerivedValue (L := L) s) ⟶ N}
    (hfg : ∀ U : (Spec (regularListQuotientRing s)).Opens,
      f.val.app (op U) (closedImmersionRegularListNativeTopClass s hs e (1 : A) U) =
        g.val.app (op U) (closedImmersionRegularListNativeTopClass s hs e (1 : A) U)) : f = g := by
  let eH := derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs
    (injectiveResolution L) e
  let Z := Spec (regularListQuotientRing s)
  apply (cancel_epi eH.inv).mp
  apply (SheafOfModules.unitHomEquiv N).injective
  apply PresheafOfModules.sections_ext
  intro U
  have hi := congrArg (fun f => f.val.app U (1 : Z.ringCatSheaf.obj.obj U)) eH.inv_hom_id
  have hpoint : eH.inv.val.app U
      (1 : Z.ringCatSheaf.obj.obj U) =
      closedImmersionRegularListNativeTopClass s hs e (1 : A) U.unop :=
    localIsoSections_injective eH U.unop
      (hi.trans (closedImmersionRegularListNativeTopClass_one s hs e U.unop).symm)
  change f.val.app U (eH.inv.val.app U
      (1 : Z.ringCatSheaf.obj.obj U)) =
    g.val.app U (eH.inv.val.app U
      (1 : Z.ringCatSheaf.obj.obj U))
  rw [hpoint]
  exact hfg U.unop

variable {Q : (Spec (regularListQuotientRing s)).Modules}
  (Δ : tensorSheaf (Spec (regularListQuotientRing s))
    (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L)

/-- The actual top homology map, contracted by the inverse normal-first determinant. -/
@[no_expose] def derivedClosedImmersionRegularListCanonicalTopHomologyIso :
    (DerivedCategory.Plus.homologyFunctor (Spec (regularListQuotientRing s)).Modules
      (s.length : ℤ)).obj (closedImmersionRegularListDerivedValue (L := L) s) ≅ Q :=
  derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e ≪≫
    normalDeterminantContractionIso
      (closedImmersionRegularListNormalLineBundle α s hs)
      (closedImmersionRegularListNormalFrameIso α s hs)
      (closedImmersionRegularListNormalDualFrameIso α s hs) Δ

/-- The actual ordinary arrow is the original conormal map followed by native contraction. -/
theorem derivedClosedImmersionRegularListCanonicalTopHomologyIso_hom :
    (derivedClosedImmersionRegularListCanonicalTopHomologyIso α s hs e Δ).hom =
      (derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e).hom ≫
      (normalDeterminantContractionIso
        (closedImmersionRegularListNormalLineBundle α s hs)
        (closedImmersionRegularListNormalFrameIso α s hs)
        (closedImmersionRegularListNormalDualFrameIso α s hs) Δ).hom := by
  rfl

/-- The installed native right adjoint itself, with its original regular-list degree. -/
@[no_expose] def derivedClosedImmersionRegularListCanonicalIso :
    closedImmersionRegularListDerivedValue (L := L) s ≅
      (DerivedCategory.Plus.singleFunctor (Spec (regularListQuotientRing s)).Modules
        (s.length : ℤ)).obj Q :=
  derivedClosedImmersionRightAdjointRegularListConormalIso α s hs e ≪≫
    (DerivedCategory.Plus.singleFunctor (Spec (regularListQuotientRing s)).Modules
      (s.length : ℤ)).mapIso
      (normalDeterminantContractionIso
        (closedImmersionRegularListNormalLineBundle α s hs)
        (closedImmersionRegularListNormalFrameIso α s hs)
        (closedImmersionRegularListNormalDualFrameIso α s hs) Δ)

/-- The actual contracted arrow retains the original ordered Koszul-class representative. -/
theorem derivedClosedImmersionRegularListCanonicalTopHomologyIso_class
    (r : A) (U : (Spec (regularListQuotientRing s)).Opens) :
    (derivedClosedImmersionRegularListCanonicalTopHomologyIso α s hs e Δ).hom.val.app
      (op U) (closedImmersionRegularListNativeTopClass s hs e r U) =
    (normalDeterminantContractionIso
      (closedImmersionRegularListNormalLineBundle α s hs)
      (closedImmersionRegularListNormalFrameIso α s hs)
      (closedImmersionRegularListNormalDualFrameIso α s hs) Δ).hom.val.app (op U)
      (moduleTensorSection _
        (dualLineBundle _ (closedImmersionRegularListNormalLineBundle α s hs)).val
        ((pullback (Spec.map (regularListQuotientMap s))).obj L) U
        (closedImmersionRegularListNormalDualSection α s hs U)
        (closedImmersionRegularListCoefficientSection s e (Ideal.Quotient.mk _ r) U)) := by
  have hconormal := (localFactorization_value
    (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs
      (injectiveResolution L) e).hom
    (closedImmersionRegularListInverseNormalLineIso α s hs e).hom
    (derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e).hom
    (derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_hom α s hs e)
    U (closedImmersionRegularListNativeTopClass s hs e r U)
    (closedImmersionRegularListNativeTopClass s hs e r U) _ rfl
    (closedImmersionRegularListNativeTopClass_unitFrame s hs e r U)).trans
      (closedImmersionRegularListInverseNormalLineIso_section α s hs e
        (Ideal.Quotient.mk (Ideal.ofList s) r) U)
  exact localFactorization_value
    (derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e).hom
    (normalDeterminantContractionIso
      (closedImmersionRegularListNormalLineBundle α s hs)
      (closedImmersionRegularListNormalFrameIso α s hs)
      (closedImmersionRegularListNormalDualFrameIso α s hs) Δ).hom
    (derivedClosedImmersionRegularListCanonicalTopHomologyIso α s hs e Δ).hom
    (derivedClosedImmersionRegularListCanonicalTopHomologyIso_hom α s hs e Δ)
    U (closedImmersionRegularListNativeTopClass s hs e r U)
    (closedImmersionRegularListNativeTopClass s hs e r U) _ rfl hconormal

/-- On the same normal-first determinant section the class formula evaluates to the
original tangent section, with native dual evaluation equal to one. -/
theorem derivedClosedImmersionRegularListCanonicalTopHomologyIso_class_normalFirst
    (r : A) (U : (Spec (regularListQuotientRing s)).Opens) (q : Q.val.obj (op U))
    (hΔ : closedImmersionRegularListCoefficientSection s e (Ideal.Quotient.mk _ r) U =
      Δ.hom.val.app (op U)
        (moduleTensorSection _ (closedImmersionRegularListNormalLineBundle α s hs).val Q U
          (closedImmersionRegularListNormalSection α s hs U) q)) :
    (derivedClosedImmersionRegularListCanonicalTopHomologyIso α s hs e Δ).hom.val.app
      (op U) (closedImmersionRegularListNativeTopClass s hs e r U) = q := by
  rw [derivedClosedImmersionRegularListCanonicalTopHomologyIso_class, hΔ]
  exact normalDeterminantContractionIso_section_one
    (closedImmersionRegularListNormalLineBundle α s hs)
    (closedImmersionRegularListNormalFrameIso α s hs)
    (closedImmersionRegularListNormalDualFrameIso α s hs) Δ U
    (closedImmersionRegularListNormalDualSection α s hs U)
    (closedImmersionRegularListNormalSection α s hs U) q
    (closedImmersionRegularListNormalDualSection_dualEvaluation α s hs U)

end AlgebraicGeometry.Scheme.Modules
