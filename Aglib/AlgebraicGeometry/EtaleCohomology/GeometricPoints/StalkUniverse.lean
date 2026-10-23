/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FibrewiseClosed.Abelian

/-! # Original geometric stalks and the genuine point-universe lift -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.StalkUniverse

universe u

variable {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (η : Spec (.of Ω) ⟶ T)

open FibrewiseClosed (largePoint)

/-- The native colimit map takes a lifted geometric Hom witness to the original witness. -/
def presheafHom (P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (largePoint η).presheafFiber.obj P ⟶ (pointSmallEtale η).presheafFiber.obj P :=
  (largePoint η).presheafFiberDesc
    (fun U x => (pointSmallEtale η).toPresheafFiber U x.down P)
    (by
      intro U V g x
      exact (pointSmallEtale η).toPresheafFiber_w g x.down P)

/-- The inverse native colimit map lifts the original geometric Hom witness. -/
def presheafInv (P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (pointSmallEtale η).presheafFiber.obj P ⟶ (largePoint η).presheafFiber.obj P :=
  (pointSmallEtale η).presheafFiberDesc
    (fun U x => (largePoint η).toPresheafFiber U (ULift.up x) P)
    (by
      intro U V g x
      exact (largePoint η).toPresheafFiber_w g (ULift.up x) P)

/-- The forward map preserves the original section and removes only the Hom-witness lift. -/
@[reassoc (attr := simp)]
theorem germ_presheafHom (P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (U : T.Etale) (x : (largePoint η).fiber.obj U) :
    (largePoint η).toPresheafFiber U x P ≫ presheafHom η P =
      (pointSmallEtale η).toPresheafFiber U x.down P :=
  (largePoint η).toPresheafFiber_presheafFiberDesc _ _ U x

/-- The inverse map preserves the original section and lifts only the Hom witness. -/
@[reassoc (attr := simp)]
theorem germ_presheafInv (P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (U : T.Etale) (x : (pointSmallEtale η).fiber.obj U) :
    (pointSmallEtale η).toPresheafFiber U x P ≫ presheafInv η P =
      (largePoint η).toPresheafFiber U (ULift.up x) P :=
  (pointSmallEtale η).toPresheafFiber_presheafFiberDesc _ _ U x

/-- The actual presheaf-fibre comparison is induced by the native colimit maps on germs. -/
def presheafFiberIso :
    (largePoint η).presheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (pointSmallEtale η).presheafFiber (A := AddCommGrpCat.{u + 1}) :=
  NatIso.ofComponents
    (fun P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} =>
      { hom := presheafHom η P
        inv := presheafInv η P
        hom_inv_id := by
          apply (largePoint η).presheafFiber_hom_ext
          intro U x
          rw [← Category.assoc, germ_presheafHom, germ_presheafInv, Category.comp_id]
          cases x
          rfl
        inv_hom_id := by
          apply (pointSmallEtale η).presheafFiber_hom_ext
          intro U x
          rw [← Category.assoc, germ_presheafInv, germ_presheafHom, Category.comp_id] })
    (by
      intro P Q q
      apply (largePoint η).presheafFiber_hom_ext
      intro U x
      calc
        (largePoint η).toPresheafFiber U x P ≫
            ((largePoint η).presheafFiber.map q ≫ presheafHom η Q) =
            q.app (op U) ≫
              ((largePoint η).toPresheafFiber U x Q ≫ presheafHom η Q) := by
          rw [← Category.assoc, (largePoint η).toPresheafFiber_naturality, Category.assoc]
        _ = q.app (op U) ≫ (pointSmallEtale η).toPresheafFiber U x.down Q := by
          rw [germ_presheafHom]
        _ = (pointSmallEtale η).toPresheafFiber U x.down P ≫
            (pointSmallEtale η).presheafFiber.map q :=
          ((pointSmallEtale η).toPresheafFiber_naturality q U x.down).symm
        _ = (largePoint η).toPresheafFiber U x P ≫
            (presheafHom η P ≫ (pointSmallEtale η).presheafFiber.map q) := by
          rw [← Category.assoc, germ_presheafHom])

/-- The natural isomorphism between genuine lifted and original geometric stalks,
for every actual standard-universe abelian sheaf. -/
def sheafFiberIso :
    (largePoint η).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf (Scheme.smallEtaleTopology T) AddCommGrpCat.{u + 1})
    (presheafFiberIso η)

/-- The comparison sends the lifted original Hom germ to its unlifted germ,
with the identical test object and section. -/
@[reassoc]
theorem germ_sheafFiberIso (L : AbelianSheaf.{u, u + 1} T) (U : T.Etale)
    (x : (pointSmallEtale η).fiber.obj U) :
    (largePoint η).toPresheafFiber U (ULift.up x) L.obj ≫
        (sheafFiberIso η).hom.app L =
      (pointSmallEtale η).toPresheafFiber U x L.obj := by
  change (largePoint η).toPresheafFiber U (ULift.up x) L.obj ≫ presheafHom η L.obj = _
  exact germ_presheafHom η L.obj U (ULift.up x)

/-- The original germ equation evaluated on an unchanged actual section. -/
theorem germ_sheafFiberIso_apply (L : AbelianSheaf.{u, u + 1} T) (U : T.Etale)
    (x : (pointSmallEtale η).fiber.obj U) (a : L.obj.obj (op U)) :
    (sheafFiberIso η).hom.app L
        ((largePoint η).toPresheafFiber U (ULift.up x) L.obj a) =
      (pointSmallEtale η).toPresheafFiber U x L.obj a :=
  ConcreteCategory.congr_hom (germ_sheafFiberIso η L U x) a

/-- Every actual additive coefficient map commutes with the original stalk comparison. -/
@[reassoc]
theorem sheafFiberIso_naturality {L M : AbelianSheaf.{u, u + 1} T} (q : L ⟶ M) :
    (largePoint η).sheafFiber.map q ≫ (sheafFiberIso η).hom.app M =
      (sheafFiberIso η).hom.app L ≫ (pointSmallEtale η).sheafFiber.map q :=
  (sheafFiberIso η).hom.naturality q

section Conservativity

variable {S : Scheme.{u}} (p : T ⟶ S) [LocallyOfFiniteType p]

/-- Fibrewise-closed point detection applies to the original native geometric stalks. -/
theorem isIso_of_original_geometricStalks
    {F G : AbelianSheaf.{u, u + 1} T} (f : F ⟶ G)
    (h : ∀ x : FibrewiseClosed.Index p,
      IsIso ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1}) |>.map f)) : IsIso f := by
  apply FibrewiseClosed.isIso_of_geometricStalks p f
  intro x
  exact (NatIso.isIso_map_iff (sheafFiberIso (FibrewiseClosed.geometricPoint x.val)) f).mpr (h x)

/-- The original geometric-stalk functors jointly reflect actual abelian-sheaf isomorphisms. -/
theorem originalStalks_jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms (fun x : FibrewiseClosed.Index p =>
      (pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})) where
  isIso f _ := isIso_of_original_geometricStalks p f (fun _ => inferInstance)

/-- Testing all original algebraically closed geometric stalks with literal
fibrewise-closed underlying points detects the original abelian-sheaf isomorphism. -/
theorem isIso_of_all_original_fibrewiseClosed_geometricStalks
    {F G : AbelianSheaf.{u, u + 1} T} (f : F ⟶ G)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (ξ : Spec (.of K) ⟶ T),
      FibrewiseClosed.IsFibrewiseClosed p (ξ default) →
        IsIso ((pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.map f)) :
    IsIso f := by
  apply FibrewiseClosed.isIso_of_all_fibrewiseClosed_geometricStalks p f
  intro K _ _ ξ hξ
  exact (NatIso.isIso_map_iff (sheafFiberIso ξ) f).mpr (h K ξ hξ)

end Conservativity
end AlgebraicGeometry.Scheme.EtaleCohomology.StalkUniverse
