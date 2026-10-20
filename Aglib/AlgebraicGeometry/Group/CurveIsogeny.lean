/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Conditional isogeny geometry for an actual pointed proper-curve map

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.PowerIsogeny`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 220–226,547–571.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
attribute [local instance] Over.cartesianMonoidalCategory

/-- The actual origin equation is the one stored by the native pointed group-law data. -/
theorem pointedGroupLaw_origin_transfer {k : Type u} [Field k]
    {C D : FScheme k} {c : 𝟙_ (FScheme k) ⟶ C} {d : 𝟙_ (FScheme k) ⟶ D}
    (LC : PointedGroupLaw C c) (LD : PointedGroupLaw D d) (m : C ⟶ D)
    (hm : @MonObj.one (FScheme k) _ _ C LC.law.toMonObj ≫ m =
      @MonObj.one (FScheme k) _ _ D LD.law.toMonObj) : c ≫ m = d := by
  rw [LC.origin, LD.origin] at hm
  exact hm

/-- The native dimension-one proper-map criterion applied to these actual field curves. -/
theorem dominant_isFinite {k : Type u} [Field k] {C D : FScheme k}
    (hC : Properties C) (hD : Properties D) (m : C ⟶ D) [IsDominant m.left] :
    IsFinite m.left := by
  let : IsIntegral C.left := hC.isIntegral
  let : IsIntegral D.left := hD.isIntegral
  let : IsNoetherian C.left := curveProperties_isNoetherian hC
  let : IsProper D.hom := hD.proper
  let : IsProper (m.left ≫ D.hom) := by simpa only [m.w] using hC.proper
  let : IsProper m.left := IsProper.of_comp m.left D.hom
  exact Projectivity.proper_dominant_curve_isFinite m.left
    (le_of_eq (curveProperties_dimension Scheme.smoothFieldDimension hC))
    (curveProperties_dimension Scheme.smoothFieldDimension hD)

/-- Pointed proper-curve rigidity and native finiteness package the original morphism.
The exact universal characteristic-zero etaleness family remains an explicit input. -/
theorem pointed_dominant_finite_etale
    (hetale : ∀ (k : Type u) [Field k] [CharZero k] (G H : Grp (FScheme k)),
      Properties G.X → Properties H.X →
      ∀ f : G ⟶ H, IsFinite f.hom.hom.left → Surjective f.hom.hom.left →
        Etale f.hom.hom.left)
    {k : Type u} [Field k] [CharZero k] {C D : FScheme k}
    {c : 𝟙_ (FScheme k) ⟶ C} {d : 𝟙_ (FScheme k) ⟶ D}
    (LC : PointedGroupLaw C c) (LD : PointedGroupLaw D d)
    (hC : Properties C) (hD : Properties D)
    (m : C ⟶ D) [IsDominant m.left] (ho : c ≫ m = d) :
    letI : GrpObj C := LC.law
    letI : GrpObj D := LD.law
    IsMonHom m ∧ IsFinite m.left ∧ Etale m.left ∧ Surjective m.left := by
  let : GrpObj C := LC.law
  let : GrpObj D := LD.law
  let G : Grp (FScheme k) := { X := C, grp := LC.law }
  let H : Grp (FScheme k) := { X := D, grp := LD.law }
  have hpoint : η[C] ≫ m = η[D] := by rw [LC.origin, LD.origin]; exact ho
  let : IsMonHom m := pointedMorphism_of_curveProperties G H hC hD m hpoint
  let : IsIntegral C.left := hC.isIntegral
  let : IsIntegral D.left := hD.isIntegral
  let : IsFinite m.left := dominant_isFinite hC hD m
  let : Surjective m.left := inferInstance
  have hfmap : IsFinite (Grp.ofHom m).hom.hom.left := by
    change IsFinite m.left
    infer_instance
  have hsmap : Surjective (Grp.ofHom m).hom.hom.left := by
    change Surjective m.left
    infer_instance
  exact ⟨inferInstance, inferInstance,
    hetale k G H hC hD (Grp.ofHom m) hfmap hsmap, inferInstance⟩

end AlgebraicGeometry.Scheme.OverField.Curve
