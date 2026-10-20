/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Curves.Isogeny.Etale

/-!
# Characteristic-zero curve-isogeny interfaces

These clients retain arbitrary fields and universes, the native curve predicate,
and the literal underlying scheme morphisms. The pointed client exercises the
existing conditional consumer after discharging its exact etaleness family.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example :
    ∀ (k : Type u) [Field k] [CharZero k] (G H : Grp (FScheme k)),
      Properties G.X → Properties H.X →
      ∀ f : G ⟶ H, IsFinite f.hom.hom.left → Surjective f.hom.hom.left →
        Etale f.hom.hom.left :=
  charZeroFiniteCurveGroupHomEtale

example {k : Type u} [Field k] [CharZero k] (G H : Grp (FScheme k))
    (hG : Properties G.X) (hH : Properties H.X) (f : G ⟶ H)
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left] :
    Etale f.hom.hom.left :=
  finite_hom_etale_of_charZero G H hG hH f

example {k : Type u} [Field k] [CharZero k] {C D : FScheme k}
    {c : 𝟙_ (FScheme k) ⟶ C} {d : 𝟙_ (FScheme k) ⟶ D}
    (LC : PointedGroupLaw C c) (LD : PointedGroupLaw D d)
    (hC : Properties C) (hD : Properties D)
    (m : C ⟶ D) [IsDominant m.left] (ho : c ≫ m = d) :
    letI : GrpObj C := LC.law
    letI : GrpObj D := LD.law
    IsMonHom m ∧ IsFinite m.left ∧ Etale m.left ∧ Surjective m.left :=
  pointed_dominant_finite_etale charZeroFiniteCurveGroupHomEtale LC LD hC hD m ho

example {k : Type u} [Field k] [CharZero k] {C D : FScheme k}
    {c : 𝟙_ (FScheme k) ⟶ C} {d : 𝟙_ (FScheme k) ⟶ D}
    (LC : PointedGroupLaw C c) (LD : PointedGroupLaw D d)
    (hC : Properties C) (hD : Properties D)
    (m : C ⟶ D) [IsDominant m.left] (ho : c ≫ m = d) :
    letI : GrpObj C := LC.law
    letI : GrpObj D := LD.law
    IsMonHom m ∧ IsFinite m.left ∧ Etale m.left ∧ Surjective m.left :=
  pointed_dominant_finite_etale_of_charZero LC LD hC hD m ho
