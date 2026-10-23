/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.DiscreteDecomposition
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Original global sections on a discrete scheme

The canonical global-section comparison is the product of actual germs.
It follows from the original stalk-spectrum coproduct and preservation of
products by Gamma. Unit coordinates therefore keep all infinitesimal data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [DiscreteTopology X]

/-- The original local-spectrum cofan is a colimit. -/
def stalkSpectraIsColimit :
    IsColimit (Cofan.mk X (fun x : X => X.fromSpecStalk x)) := by
  exact ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (Cofan.mk X (fun x : X => X.fromSpecStalk x))).mpr (by
      change IsIso (Sigma.desc (fun x : X => X.fromSpecStalk x))
      exact stalkCoproductMap_isIso X)).some

/-- Gamma carries the original local-spectrum cofan to a limit fan. -/
def sectionsStalkSpectraIsLimit :
    IsLimit (Fan.mk Γ(X, ⊤) (fun x : X => (X.fromSpecStalk x).appTop)) :=
  isLimitFanMkObjOfIsLimit Scheme.Γ (fun x : X => op (Spec (X.presheaf.stalk x)))
    (fun x : X => (X.fromSpecStalk x).op)
    (Cofan.IsColimit.op (stalkSpectraIsColimit X))

/-- Gamma of the local-spectrum coproduct as an actual ring product. -/
def sectionsStalkSpectraIso :
    Γ(X, ⊤) ≅ CommRingCat.of (∀ x : X, Γ(Spec (X.presheaf.stalk x), ⊤)) :=
  (sectionsStalkSpectraIsLimit X).conePointUniqueUpToIso
    (CommRingCat.piFanIsLimit (fun x : X => Γ(Spec (X.presheaf.stalk x), ⊤)))

private theorem sectionsStalkSpectraIso_eval (x : X) :
    (sectionsStalkSpectraIso X).hom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun x : X => Γ(Spec (X.presheaf.stalk x), ⊤)) x) =
      (X.fromSpecStalk x).appTop :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk x)

/-- Original global functions on a discrete scheme are the product of its actual stalk rings. -/
def globalSectionsStalkProduct : Γ(X, ⊤) ≃+* ∀ x : X, X.presheaf.stalk x :=
  (sectionsStalkSpectraIso X).commRingCatIsoToRingEquiv.trans
    (RingEquiv.piCongrRight fun x => (ΓSpecIso (X.presheaf.stalk x)).commRingCatIsoToRingEquiv)

/-- Every coordinate of the comparison is exactly the original germ. -/
theorem globalSectionsStalkProduct_apply (a : Γ(X, ⊤)) (x : X) :
    globalSectionsStalkProduct X a x = X.presheaf.germ ⊤ x trivial a := by
  have h := congrArg (fun f : Γ(X, ⊤) ⟶ Γ(Spec (X.presheaf.stalk x), ⊤) =>
    (ΓSpecIso (X.presheaf.stalk x)).hom (f.hom a))
    (sectionsStalkSpectraIso_eval X x)
  change (ΓSpecIso (X.presheaf.stalk x)).hom ((sectionsStalkSpectraIso X).hom a x) = _
  have h' : (ΓSpecIso (X.presheaf.stalk x)).hom
      ((sectionsStalkSpectraIso X).hom a x) =
      (ΓSpecIso (X.presheaf.stalk x)).hom ((X.fromSpecStalk x).appTop a) := h
  refine h'.trans ?_
  have hg : (X.fromSpecStalk x).appTop ≫ (ΓSpecIso (X.presheaf.stalk x)).hom =
      X.presheaf.germ ⊤ x trivial := by
    rw [fromSpecStalk_appTop]
    simp
  exact congrArg (fun f : Γ(X, ⊤) ⟶ X.presheaf.stalk x => f.hom a) hg

/-- Actual global units are the product of units in the actual stalk rings. -/
def globalUnitsStalkProduct : Γ(X, ⊤)ˣ ≃* ∀ x : X, (X.presheaf.stalk x)ˣ :=
  (Units.mapEquiv (globalSectionsStalkProduct X).toMulEquiv).trans MulEquiv.piUnits

/-- The unit comparison retains the original unit germ in every coordinate. -/
theorem globalUnitsStalkProduct_apply (a : Γ(X, ⊤)ˣ) (x : X) :
    globalUnitsStalkProduct X a x =
      Units.map (X.presheaf.germ ⊤ x trivial).hom.toMonoidHom a := by
  apply Units.ext
  exact globalSectionsStalkProduct_apply X (a : Γ(X, ⊤)) x

end AlgebraicGeometry.Scheme
