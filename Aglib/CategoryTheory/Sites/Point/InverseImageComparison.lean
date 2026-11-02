/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Topos.Point
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Inverse-image comparison for the actual supplied site points

A natural cross-world family of fibre equivalences reindexes the literal
constant products. The resulting skyscraper comparison has a mate under the
supplied sheaf adjunction. Its whole unit identity gives the original germ
formula. Both points, the adjunction, products and colimits are the given ones.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point.InverseImageComparison

universe wSource wTarget uC vC uD vD uA vA

section Products

variable {A : Type uA} [Category.{vA} A]
  [HasProducts.{wSource} A] [HasProducts.{wTarget} A]
  {I : Type wSource} {T : Type wTarget} (e : I ≃ T)

/-- Reindex the original literal constant families by the supplied equivalence. -/
def constantProductIso (M : A) :
    (∏ᶜ fun _ : T => M) ≅ (∏ᶜ fun _ : I => M) :=
  (Pi.reindex e (fun _ : T => M)).symm

/-- The forward map reads the coordinate prescribed by the same equivalence. -/
@[reassoc]
theorem constantProductIso_hom_π (M : A) (p : I) :
    (constantProductIso e M).hom ≫ Pi.π (fun _ : I => M) p =
      Pi.π (fun _ : T => M) (e p) :=
  Pi.reindex_inv_π e (fun _ : T => M) p

/-- The inverse reads the original inverse-equivalence coordinate. -/
@[reassoc]
theorem constantProductIso_inv_π (M : A) (p : T) :
    (constantProductIso e M).inv ≫ Pi.π (fun _ : T => M) p =
      Pi.π (fun _ : I => M) (e.symm p) := by
  apply (cancel_epi (constantProductIso e M).hom).mp
  rw [Iso.hom_inv_id_assoc, constantProductIso_hom_π, Equiv.apply_symm_apply]

/-- The forward arrow is the exact original product lift. -/
theorem constantProductIso_hom (M : A) :
    (constantProductIso e M).hom =
      Pi.lift (fun p : I => Pi.π (fun _ : T => M) (e p)) := by
  apply Pi.hom_ext
  intro p
  rw [constantProductIso_hom_π, Pi.lift_comp_π]

/-- The inverse arrow is the exact original inverse-coordinate lift. -/
theorem constantProductIso_inv (M : A) :
    (constantProductIso e M).inv =
      Pi.lift (fun p : T => Pi.π (fun _ : I => M) (e.symm p)) := by
  apply Pi.hom_ext
  intro p
  rw [constantProductIso_inv_π, Pi.lift_comp_π]

/-- Coefficient maps commute with reindexing the same constant product families. -/
theorem constantProductIso_naturality {M N : A} (a : M ⟶ N) :
    Limits.Pi.map (fun _ : T => a) ≫ (constantProductIso e N).hom =
      (constantProductIso e M).hom ≫ Limits.Pi.map (fun _ : I => a) := by
  apply Pi.hom_ext
  intro p
  simp only [Category.assoc, constantProductIso_hom_π, Limits.Pi.map_π,
    constantProductIso_hom_π_assoc]

end Products

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (sourcePoint : Point.{wSource} J) (targetPoint : Point.{wTarget} K) (F : C ⥤ D)
  (fiberEquiv : ∀ U, sourcePoint.fiber.obj U ≃ targetPoint.fiber.obj (F.obj U))
  (fiberNaturality : ∀ {U V : C} (a : U ⟶ V) (p : sourcePoint.fiber.obj U),
    fiberEquiv V (sourcePoint.fiber.map a p) =
      targetPoint.fiber.map (F.map a) (fiberEquiv U p))
  {A : Type uA} [Category.{vA} A]
  [HasProducts.{wSource} A] [HasProducts.{wTarget} A]

/-- The whole presheaf comparison uses exactly the supplied actual fibre equivalences. -/
def presheafIso (M : A) :
    F.op ⋙ targetPoint.skyscraperPresheaf M ≅ sourcePoint.skyscraperPresheaf M :=
  NatIso.ofComponents
    (fun U => constantProductIso (fiberEquiv U.unop) M)
    (by
      intro U V a
      apply Pi.hom_ext
      intro p
      change
        (Pi.map' (fun q => targetPoint.fiber.map (F.map a.unop) q) (fun _ => 𝟙 M) ≫
          (constantProductIso (fiberEquiv V.unop) M).hom) ≫ Pi.π _ p =
        ((constantProductIso (fiberEquiv U.unop) M).hom ≫
          Pi.map' (fun q => sourcePoint.fiber.map a.unop q) (fun _ => 𝟙 M)) ≫ Pi.π _ p
      simp only [Category.assoc, constantProductIso_hom_π, Pi.map'_comp_π,
        Category.comp_id]
      rw [fiberNaturality a.unop p])

/-- Each presheaf component retains the original forward coordinate. -/
@[reassoc]
theorem presheafIso_hom_π (M : A) (U : C) (p : sourcePoint.fiber.obj U) :
    (presheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality M).hom.app (op U) ≫
        Pi.π (fun _ : sourcePoint.fiber.obj U => M) p =
      Pi.π (fun _ : targetPoint.fiber.obj (F.obj U) => M) (fiberEquiv U p) :=
  constantProductIso_hom_π (fiberEquiv U) M p

/-- Each inverse component retains the original inverse coordinate. -/
@[reassoc]
theorem presheafIso_inv_π (M : A) (U : C) (p : targetPoint.fiber.obj (F.obj U)) :
    (presheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality M).inv.app (op U) ≫
        Pi.π (fun _ : targetPoint.fiber.obj (F.obj U) => M) p =
      Pi.π (fun _ : sourcePoint.fiber.obj U => M) ((fiberEquiv U).symm p) :=
  constantProductIso_inv_π (fiberEquiv U) M p

/-- The completed presheaf comparisons are natural in the original coefficient map. -/
theorem presheafIso_naturality {M N : A} (a : M ⟶ N) :
    Functor.whiskerLeft F.op (targetPoint.skyscraperPresheafFunctor.map a) ≫
        (presheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality N).hom =
      (presheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality M).hom ≫
        sourcePoint.skyscraperPresheafFunctor.map a := by
  apply NatTrans.ext
  funext U
  exact constantProductIso_naturality (fiberEquiv U.unop) a

variable [Functor.IsContinuous F J K]

/-- The original skyscraper sheaves and actual sheaf pushforward use the same comparison. -/
def sheafIso :
    targetPoint.skyscraperSheafFunctor (A := A) ⋙ F.sheafPushforwardContinuous A J K ≅
      sourcePoint.skyscraperSheafFunctor :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      (presheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality M))
    (by
      intro M N a
      apply Sheaf.hom_ext
      exact presheafIso_naturality sourcePoint targetPoint F fiberEquiv fiberNaturality a)

/-- The sheaf comparison has the same original product-coordinate value. -/
@[reassoc]
theorem sheafIso_hom_π (M : A) (U : C) (p : sourcePoint.fiber.obj U) :
    ((sheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality).hom.app M).hom.app
          (op U) ≫ Pi.π (fun _ : sourcePoint.fiber.obj U => M) p =
      Pi.π (fun _ : targetPoint.fiber.obj (F.obj U) => M) (fiberEquiv U p) :=
  presheafIso_hom_π sourcePoint targetPoint F fiberEquiv fiberNaturality M U p

variable [HasColimitsOfSize.{wSource, wSource} A]
  [HasColimitsOfSize.{wTarget, wTarget} A]
  (left : Sheaf J A ⥤ Sheaf K A) (adj : left ⊣ F.sheafPushforwardContinuous A J K)

/-- One mate Iso under the actual supplied sheaf adjunction and the two original points. -/
def fiberIso :
    sourcePoint.sheafFiber (A := A) ≅ left ⋙ targetPoint.sheafFiber :=
  (conjugateIsoEquiv (adj.comp targetPoint.skyscraperSheafAdjunction)
    sourcePoint.skyscraperSheafAdjunction).symm
      (sheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality)

/-- The entire original mate unit equation is proved before evaluating any coordinate. -/
theorem fiberIso_unit :
    (adj.comp targetPoint.skyscraperSheafAdjunction).unit ≫
        Functor.whiskerLeft (left ⋙ targetPoint.sheafFiber)
          (sheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality).hom =
      sourcePoint.skyscraperSheafAdjunction.unit ≫
        Functor.whiskerRight
          (fiberIso sourcePoint targetPoint F fiberEquiv fiberNaturality left adj).hom
          sourcePoint.skyscraperSheafFunctor := by
  apply NatTrans.ext
  funext M
  exact unit_conjugateEquiv_symm
    (adj.comp targetPoint.skyscraperSheafAdjunction) sourcePoint.skyscraperSheafAdjunction
    (sheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality).hom M

/-- Its Hom-equivalence form is a consequence of that same whole unit identity. -/
theorem fiberIso_homEquiv (M : Sheaf J A) :
    sourcePoint.skyscraperSheafAdjunction.homEquiv _ _
        ((fiberIso sourcePoint targetPoint F fiberEquiv fiberNaturality left adj).hom.app M) =
      (adj.comp targetPoint.skyscraperSheafAdjunction).unit.app M ≫
        (sheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality).hom.app _ := by
  have h := congrArg (fun a => a.app M)
    (fiberIso_unit sourcePoint targetPoint F fiberEquiv fiberNaturality left adj)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  rw [Adjunction.homEquiv_unit]
  exact h.symm

/-- The same mate sends an original germ through the supplied adjunction unit
and the same structural point equivalence. -/
@[reassoc]
theorem germ_fiberIso (M : Sheaf J A) (U : C) (p : sourcePoint.fiber.obj U) :
    sourcePoint.toPresheafFiber U p M.obj ≫
        (fiberIso sourcePoint targetPoint F fiberEquiv fiberNaturality left adj).hom.app M =
      (adj.unit.app M).hom.app (op U) ≫
        targetPoint.toPresheafFiber (F.obj U) (fiberEquiv U p) (left.obj M).obj := by
  have he := fiberIso_homEquiv sourcePoint targetPoint F fiberEquiv fiberNaturality left adj M
  have h := congrArg
    (fun a : M ⟶ sourcePoint.skyscraperSheaf (targetPoint.sheafFiber.obj (left.obj M)) =>
      a.hom.app (op U) ≫ Pi.π
        (fun _ : sourcePoint.fiber.obj U => targetPoint.sheafFiber.obj (left.obj M)) p) he
  erw [GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_apply_hom,
    GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app_π,
    Adjunction.comp_unit_app] at h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc] at h
  have hpush :
      ((F.sheafPushforwardContinuous A J K).map
        (targetPoint.skyscraperSheafAdjunction.unit.app (left.obj M))).hom.app (op U) =
      (targetPoint.skyscraperSheafAdjunction.unit.app (left.obj M)).hom.app (op (F.obj U)) := rfl
  rw [hpush] at h
  change sourcePoint.toPresheafFiber U p M.obj ≫
      (fiberIso sourcePoint targetPoint F fiberEquiv fiberNaturality left adj).hom.app M =
    ((adj.unit.app M).hom.app (op U) ≫
      (targetPoint.skyscraperSheafAdjunction.unit.app (left.obj M)).hom.app (op (F.obj U)) ≫
        ((sheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality).hom.app
          (targetPoint.sheafFiber.obj (left.obj M))).hom.app (op U)) ≫
      Pi.π (fun _ : sourcePoint.fiber.obj U => targetPoint.sheafFiber.obj (left.obj M)) p at h
  calc
    _ = _ := h
    _ = (adj.unit.app M).hom.app (op U) ≫
        (targetPoint.skyscraperSheafAdjunction.unit.app (left.obj M)).hom.app (op (F.obj U)) ≫
          (((sheafIso sourcePoint targetPoint F fiberEquiv fiberNaturality).hom.app
            (targetPoint.sheafFiber.obj (left.obj M))).hom.app (op U) ≫
              Pi.π (fun _ : sourcePoint.fiber.obj U =>
                targetPoint.sheafFiber.obj (left.obj M)) p) := by
      exact (Category.assoc _ _ _).trans
        (congrArg ((adj.unit.app M).hom.app (op U) ≫ ·) (Category.assoc _ _ _))
    _ = (adj.unit.app M).hom.app (op U) ≫
        (targetPoint.skyscraperSheafAdjunction.unit.app (left.obj M)).hom.app (op (F.obj U)) ≫
          Pi.π (fun _ : targetPoint.fiber.obj (F.obj U) =>
            targetPoint.sheafFiber.obj (left.obj M)) (fiberEquiv U p) := by
      exact congrArg
        (fun q => (adj.unit.app M).hom.app (op U) ≫
          (targetPoint.skyscraperSheafAdjunction.unit.app (left.obj M)).hom.app
            (op (F.obj U)) ≫ q)
        (sheafIso_hom_π sourcePoint targetPoint F fiberEquiv fiberNaturality
          (targetPoint.sheafFiber.obj (left.obj M)) U p)
    _ = _ := by
      exact congrArg ((adj.unit.app M).hom.app (op U) ≫ ·)
        (targetPoint.skyscraperSheafAdjunction_unit_π (left.obj M) (F.obj U) (fiberEquiv U p))

end CategoryTheory.GrothendieckTopology.Point.InverseImageComparison
