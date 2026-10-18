/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Insertion
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenCounit

/-!
# Genuine degree transport of the original model class

The original Ext class and its original tilde/counit representative carry
the same genuine equality of degrees. The canonical model map uses the
inverse homology transport. Its same-normal insertion formula consequently
retains the original coefficient section.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]

local instance : (moduleSpecΓFunctor (R := regularListQuotientRing s)).Additive :=
  moduleSpecΓFunctor_additive _

/-- The original ordered model class transported only through its actual homology degree. -/
def regularListModelTopClassInDegree (c : ℕ) (hc : s.length = c) (r : A)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
      (c : ℤ)).val.obj (op U) :=
  (eqToIso (congrArg (fun k : ℕ =>
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (k : ℤ))
      hc)).hom.val.app (op U) (regularListModelTopClass s hs J e r U)

/-- The transported original class is exactly the native counit image of its original
degree-transported Ext representative. -/
theorem regularListModelTopClassInDegree_native (c : ℕ) (hc : s.length = c) (r : A)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    let B := regularListQuotientRing s
    let K := closedImmersionRightAdjointRegularListResolutionComplex s J
    let G := ((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).obj K
    let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J c).symm
      ((cast (congrArg (fun k => Ext.{w} (ModuleCat.of A (A ⧸ Ideal.ofList s))
        (ModuleCat.of A A) k) hc) (ChainComplex.Koszul.topExtClass s hs
          (ModuleCat.of A A) r)).comp (Ext.mk₀ e.inv) (add_zero c))
    regularListModelTopClassInDegree s hs J e c hc r U =
      (canonicalTildeHomologyCounitMap K (c : ℤ)).val.app (op U)
        (tilde.toOpen (G.homology (c : ℤ)) U ξ) := by
  subst c
  intro B K G ξ
  let : QuasiIso (Complex.tildeGlobalSectionsCounit B (.up ℤ) K) :=
    closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J e
  exact congrArg (fun f : tilde (G.homology (s.length : ℤ)) ⟶ K.homology (s.length : ℤ) =>
    f.val.app (op U) (tilde.toOpen (G.homology (s.length : ℤ)) U ξ))
      (canonicalTildeHomologyCounitMap_eq K (s.length : ℤ)).symm

variable {R : CommRingCat.{u}} (α : R ⟶ A)
  {Q : (Spec (regularListQuotientRing s)).Modules}
  (Δ : tensorSheaf (Spec (regularListQuotientRing s))
    (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L)

/-- The original canonical model map in a genuinely equal homology degree. -/
def regularListCanonicalModelTopHomologyIsoInDegree (c : ℕ) (hc : s.length = c) :
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (c : ℤ) ≅ Q :=
  (eqToIso (congrArg (fun k : ℕ =>
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (k : ℤ)) hc)).symm ≪≫
    regularListCanonicalModelTopHomologyIso s hs e α J Δ

/-- Genuine degree transport preserves the original class-one insertion formula. -/
theorem regularListCanonicalModelTopHomologyIsoInDegree_insert_class
    (c : ℕ) (hc : s.length = c) (U : (Spec (regularListQuotientRing s)).Opens) :
    (normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
        (closedImmersionRegularListNormalFrameIso α s hs) Δ).hom.val.app (op U)
      ((regularListCanonicalModelTopHomologyIsoInDegree s hs J e α Δ c hc).hom.val.app (op U)
        (regularListModelTopClassInDegree s hs J e c hc (1 : A) U)) =
      closedImmersionRegularListCoefficientSection s e (1 : regularListQuotientRing s) U := by
  subst c
  exact regularListCanonicalModelTopHomologyIso_insert_class s hs e α J Δ U

end AlgebraicGeometry.Scheme.Modules
