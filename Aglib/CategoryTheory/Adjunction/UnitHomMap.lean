/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Unit
public import Aglib.CategoryTheory.Adjunction.MateHomEquiv.Composition

/-! # Original section maps from an image unit

The given image unit and right-adjoint comparison define the actual section
map. The existing composite Hom-mate equation retains the supplied original
constant comparison. Its value at the identity proves invertibility using
only the two original constant-unit components.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

universe uA vA uB vB uC vC

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C]
  {K : A ⥤ B} {Γ : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B}
  {K' : A ⥤ C} {Δ : C ⥤ A}

/-- The original section arrow: the image unit followed by the actual right comparison. -/
def unitSectionMap (imageAdj : L ⊣ R) (Γ : B ⥤ A) (e : R ⋙ Γ ≅ Δ) (Y : B) :
    Γ.obj Y ⟶ Δ.obj (L.obj Y) :=
  Γ.map (imageAdj.unit.app Y) ≫ e.hom.app (L.obj Y)

variable (constantAdj : K ⊣ Γ) (imageAdj : L ⊣ R) (constantAdj' : K' ⊣ Δ)
  (e : R ⋙ Γ ≅ Δ) (c : K ⋙ L ≅ K')
  (hc : c = leftAdjointCompIso constantAdj imageAdj constantAdj' e)

include hc in
/-- The full original Hom-mate formula for the actual section map and constant comparison. -/
theorem unitSectionMap_homEquiv {M : A} {Y : B} (a : K.obj M ⟶ Y) :
    constantAdj'.homEquiv M (L.obj Y) (c.inv.app M ≫ L.map a) =
      constantAdj.homEquiv M Y a ≫ imageAdj.unitSectionMap Γ e Y := by
  rw [hc]
  exact homEquiv_leftAdjointCompIso_inv_map constantAdj imageAdj constantAdj' e a

include hc in
/-- At the identity, the original section map compares the two actual constant units. -/
theorem unitSectionMap_unit (M : A) :
    constantAdj.unit.app M ≫ imageAdj.unitSectionMap Γ e (K.obj M) =
      constantAdj'.unit.app M ≫ Δ.map (c.inv.app M) := by
  have h := unitSectionMap_homEquiv constantAdj imageAdj constantAdj' e c hc (𝟙 (K.obj M))
  have hmap : c.inv.app M ≫ L.map (𝟙 (K.obj M)) = c.inv.app M :=
    (congrArg
      (fun k : L.obj (K.obj M) ⟶ L.obj (K.obj M) => c.inv.app M ≫ k)
      (L.map_id (K.obj M))).trans (Category.comp_id (c.inv.app M))
  calc
    _ = constantAdj.homEquiv M (K.obj M) (𝟙 (K.obj M)) ≫
        imageAdj.unitSectionMap Γ e (K.obj M) :=
      (congrArg
        (fun k : M ⟶ Γ.obj (K.obj M) => k ≫ imageAdj.unitSectionMap Γ e (K.obj M))
        (constantAdj.homEquiv_id M)).symm
    _ = constantAdj'.homEquiv M (L.obj (K.obj M))
        (c.inv.app M ≫ L.map (𝟙 (K.obj M))) := h.symm
    _ = constantAdj'.homEquiv M (L.obj (K.obj M)) (c.inv.app M) :=
      congrArg (constantAdj'.homEquiv M (L.obj (K.obj M))) hmap
    _ = _ := rfl

include hc in
/-- Only the source and target constant units are needed to invert the actual section map. -/
theorem isIso_unitSectionMap_of_isIso_units (M : A)
    [IsIso (constantAdj.unit.app M)] [IsIso (constantAdj'.unit.app M)] :
    IsIso (imageAdj.unitSectionMap Γ e (K.obj M)) := by
  have h : IsIso (constantAdj.unit.app M ≫ imageAdj.unitSectionMap Γ e (K.obj M)) := by
    rw [unitSectionMap_unit constantAdj imageAdj constantAdj' e c hc M]
    infer_instance
  exact (isIso_comp_left_iff (constantAdj.unit.app M) _).mp h

end CategoryTheory.Adjunction
