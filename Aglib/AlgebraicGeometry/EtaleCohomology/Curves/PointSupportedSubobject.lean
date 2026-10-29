/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse
public import Aglib.CategoryTheory.Adjunction.KernelSupport
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Original supported subobjects detected by the small geometric-point family

The construction intersects kernels of actual skyscraper units, indexed by
underlying scheme points outside the support set. Outside-stalk vanishing uses
factorization through one individual kernel and the adjunction triangle, never
preservation of an infinite intersection by a stalk functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge

/-- The original large-value sheaf category has the native Grothendieck structure. -/
instance supportSheaves_isGrothendieckAbelian (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (AbelianSheaf.{u, u + 1} X) := by
  let : EssentiallySmall.{u + 1} X.Etale := essentiallySmallSelf.{0, u, u + 1} X.Etale
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall
    X.smallEtaleTopology AddCommGrpCat.{u + 1}

variable {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)

/-- The original subobject whose germs vanish outside the indicated point set. -/
def pointSupportedSubobject (Z : Set X) : Subobject F :=
  Adjunction.kernelSupport.{u + 1}
    (fun x : X => (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction
      (A := Ab.{u + 1})) F Z

/-- The shared constructor is the literal original bounded infimum of unit kernels. -/
theorem pointSupportedSubobject_eq_sInf (Z : Set X) :
    pointSupportedSubobject F Z =
      Subobject.sInf.{u + 1} (Set.range (fun x : {x : X // x ∉ Z} => kernelSubobject
        ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).skyscraperSheafAdjunction.unit.app
          F))) := rfl

/-- Enlarging the support gives the canonical inclusion of original subobjects. -/
theorem pointSupportedSubobject_mono {Z W : Set X} (h : Z ⊆ W) :
    pointSupportedSubobject F Z ≤ pointSupportedSubobject F W := by
  exact Adjunction.kernelSupport_mono.{u + 1}
    (fun x : X => (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction
      (A := Ab.{u + 1})) F h

/-- The actual supported-subobject inclusion is killed by every outside-point unit. -/
theorem pointSupportedSubobject_arrow_unit (Z : Set X) (x : X) (hx : x ∉ Z) :
    (pointSupportedSubobject F Z).arrow ≫
      (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction.unit.app F =
        0 := by
  exact Adjunction.kernelSupport_arrow_unit.{u + 1}
    (fun x : X => (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction
      (A := Ab.{u + 1})) F Z x hx

/-- The original stalk of the supported subobject is zero at each outside point. -/
theorem pointSupportedSubobject_outside_stalk (Z : Set X) (x : X) (hx : x ∉ Z) :
    IsZero ((pointSmallEtale (FibrewiseClosed.geometricPoint x)).sheafFiber.obj
      (pointSupportedSubobject F Z : AbelianSheaf.{u, u + 1} X)) := by
  let Φ := pointSmallEtale (FibrewiseClosed.geometricPoint x)
  let L := Φ.sheafFiber (A := Ab.{u + 1})
  let : LocallySmall.{u} X.Etale := inferInstance
  let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : PreservesFiniteLimits L := inferInstanceAs
    (PreservesFiniteLimits (Φ.sheafFiber (A := Ab.{u + 1})))
  let : L.PreservesMonomorphisms := inferInstance
  exact Adjunction.kernelSupport_outside.{u + 1}
    (fun x : X => (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction
      (A := Ab.{u + 1})) F Z x hx

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
