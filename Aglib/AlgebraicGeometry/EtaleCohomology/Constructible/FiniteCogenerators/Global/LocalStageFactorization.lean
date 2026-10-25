/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.AffineStageFactorization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.FactorTransport

/-! # Complete original local factors before geometric specialization

Relative-object naturality, original chart conjugacy and one original stage
factor give the complete local factor in an abstract categorical argument.
The original affine coefficient consumer specializes that whole conclusion;
it does not pass a repeatedly normalized concrete coefficient square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

/-- The complete original chart square and stage equation give the actual
local factor, before any concrete inverse-image or coefficient is substituted. -/
theorem exists_factor_of_contraFunctorIso_chart_stage
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (P : Aᵒᵖ ⥤ C) (Q : Bᵒᵖ ⥤ D) (R : A ⥤ B) (L : C ⥤ D)
    (e : P ⋙ L ≅ R.op ⋙ Q) {Y Z : A} (h : Y ⟶ Z)
    {Y' Z' : B} (a : Y' ≅ R.obj Y) (c : Z' ≅ R.obj Z) (r : Y' ⟶ Z')
    (hc : a.hom ≫ R.map h = r ≫ c.hom)
    (eA : L.obj (P.obj (op Y)) ≅ Q.obj (op Y'))
    (hEA : eA.hom = e.hom.app (op Y) ≫ Q.map a.hom.op) {F : C}
    (α : F ⟶ P.obj (op Y)) {S : D}
    (b : L.obj F ⟶ S) (t : S ⟶ Q.obj (op Z')) (leg : S ⟶ Q.obj (op Y'))
    (ht : t ≫ Q.map r.op = leg)
    (hb : b ≫ leg = L.map α ≫ eA.hom) :
    ∃ β : L.obj F ⟶ L.obj (P.obj (op Z)),
      β ≫ L.map (P.map h.op) = L.map α := by
  let eC : L.obj (P.obj (op Z)) ≅ Q.obj (op Z') :=
    e.app (op Z) ≪≫ Q.mapIso c.op
  have hτ : L.map (P.map h.op) ≫ eA.hom = eC.hom ≫ Q.map r.op :=
    (congrArg (fun z => L.map (P.map h.op) ≫ z) hEA).trans
      (contraFunctorIso_chart_naturality P Q R L e h a c r hc)
  have hβ : (b ≫ t) ≫ Q.map r.op = L.map α ≫ eA.hom :=
    (Category.assoc b t (Q.map r.op)).trans
      ((congrArg (fun z => b ≫ z) ht).trans hb)
  exact ⟨(b ≫ t) ≫ eC.inv,
    factor_through_original_iso_square eA eC (L.map (P.map h.op))
      (Q.map r.op) hτ (L.map α) (b ≫ t) hβ⟩

universe u

open AffineIntegralConstants

attribute [local instance] hasSheafifyLarge

/-- Normalize the whole original affine restriction iso before its hom
equation enters an actual stage factor. -/
theorem affineConstantPushforwardRestrictionIso_hom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (B : Type u) [AddCommGroup B] [Finite B] (U : X.AffineZariskiSite)
    [Etale U.2.fromSpec] :
    (affineConstantPushforwardRestrictionIso f B U).hom =
      (constantPushforwardRestrictionIso U.2.fromSpec B).hom.app (op (Over.mk f)) ≫
        (constantPushforwardFunctor (X := Spec Γ(X, U.1)) B).map
          (relativeAffineChartObjectIso f U).hom.op := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
