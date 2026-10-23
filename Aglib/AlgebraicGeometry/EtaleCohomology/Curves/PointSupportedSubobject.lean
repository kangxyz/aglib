/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse
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
  Subobject.sInf.{u + 1} (Set.range (fun x : {x : X // x ∉ Z} => kernelSubobject
    ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).skyscraperSheafAdjunction.unit.app
      F)))

/-- Enlarging the support gives the canonical inclusion of original subobjects. -/
theorem pointSupportedSubobject_mono {Z W : Set X} (h : Z ⊆ W) :
    pointSupportedSubobject F Z ≤ pointSupportedSubobject F W := by
  apply Subobject.le_sInf.{u + 1}
  rintro _ ⟨x, rfl⟩
  exact Subobject.sInf_le.{u + 1} _ _
    ⟨⟨x.val, fun hx => x.property (h hx)⟩, rfl⟩

private theorem subobject_arrow_comp_zero_of_le_kernel
    {C : Type*} [Category* C] [Abelian C] {A B : C}
    (P : Subobject A) (f : A ⟶ B) (h : P ≤ kernelSubobject f) :
    P.arrow ≫ f = 0 := by
  rw [← Subobject.ofLE_arrow h, Category.assoc, kernelSubobject_arrow_comp, comp_zero]

private theorem pointSupportedSubobject_le_kernel (Z : Set X) (x : X) (hx : x ∉ Z) :
    pointSupportedSubobject F Z ≤ kernelSubobject
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction.unit.app F) :=
  Subobject.sInf_le.{u + 1} _ _ ⟨⟨x, hx⟩, rfl⟩

/-- The actual supported-subobject inclusion is killed by every outside-point unit. -/
theorem pointSupportedSubobject_arrow_unit (Z : Set X) (x : X) (hx : x ∉ Z) :
    (pointSupportedSubobject F Z).arrow ≫
      (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction.unit.app F =
        0 := by
  exact subobject_arrow_comp_zero_of_le_kernel (pointSupportedSubobject F Z)
    ((pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction.unit.app F)
    (pointSupportedSubobject_le_kernel F Z x hx)

/-- The original stalk of the supported subobject is zero at each outside point. -/
theorem pointSupportedSubobject_outside_stalk (Z : Set X) (x : X) (hx : x ∉ Z) :
    IsZero ((pointSmallEtale (FibrewiseClosed.geometricPoint x)).sheafFiber.obj
      (pointSupportedSubobject F Z : AbelianSheaf.{u, u + 1} X)) := by
  let Φ := pointSmallEtale (FibrewiseClosed.geometricPoint x)
  let L := Φ.sheafFiber (A := Ab.{u + 1})
  let a := (pointSupportedSubobject F Z).arrow
  have hz := pointSupportedSubobject_arrow_unit F Z x hx
  have h := congrArg (fun q => L.map q ≫ Φ.skyscraperSheafAdjunction.counit.app (L.obj F)) hz
  have ht : L.map (Φ.skyscraperSheafAdjunction.unit.app F) ≫
      Φ.skyscraperSheafAdjunction.counit.app (L.obj F) = 𝟙 (L.obj F) :=
    Φ.skyscraperSheafAdjunction.left_triangle_components F
  have hm : L.map a = 0 := by
    change L.map (a ≫ Φ.skyscraperSheafAdjunction.unit.app F) ≫
      Φ.skyscraperSheafAdjunction.counit.app (L.obj F) = L.map 0 ≫ _ at h
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc, ht,
      Category.comp_id, CategoryTheory.Functor.map_zero, zero_comp] using h
  let : Mono a := inferInstanceAs (Mono (pointSupportedSubobject F Z).arrow)
  let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : PreservesFiniteLimits L := inferInstanceAs
    (PreservesFiniteLimits (Φ.sheafFiber (A := Ab.{u + 1})))
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  refine ⟨fun b c => ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (L.map a)).mp inferInstance
  rw [hm]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
