/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-! # Local description of the original continuous-site pullback

The native Kan extension maps to the original sheaf pullback by sheafification
and its original comparison isomorphism. Its actual pointwise colimits supply
representatives and common witnesses, with the indexing sizes retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  (G : C ⥤ D) [∀ P : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension P]

namespace sheafPullbackConstruction

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [HasWeakSheafify K A] [K.WEqualsLocallyBijective A]

/-- The native presentation map to the original sheaf pullback is locally injective. -/
theorem isLocallyInjective_presentationMap (P : Sheaf J A) :
    Presheaf.IsLocallyInjective K
      (toSheafify K (G.op.lan.obj P.obj) ≫
        ((sheafPullbackIso G A J K).inv.app P).hom) := by
  let e := (sheafPullbackIso G A J K).symm.app P
  let : IsIso e.hom.hom := ((sheafToPresheaf K A).mapIso e).isIso_hom
  let h₂ : Presheaf.IsLocallyInjective K e.hom.hom := inferInstance
  let h₁ : Presheaf.IsLocallyInjective K (toSheafify K (G.op.lan.obj P.obj)) :=
    (K.W_toSheafify (G.op.lan.obj P.obj)).isLocallyInjective
  exact @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ K _ _ _
    (toSheafify K (G.op.lan.obj P.obj)) e.hom.hom h₁ h₂

/-- The native presentation map to the original sheaf pullback is locally surjective. -/
theorem isLocallySurjective_presentationMap (P : Sheaf J A) :
    Presheaf.IsLocallySurjective K
      (toSheafify K (G.op.lan.obj P.obj) ≫
        ((sheafPullbackIso G A J K).inv.app P).hom) := by
  let e := (sheafPullbackIso G A J K).symm.app P
  let : IsIso e.hom.hom := ((sheafToPresheaf K A).mapIso e).isIso_hom
  let h₂ : Presheaf.IsLocallySurjective K e.hom.hom :=
    Presheaf.isLocallySurjective_of_iso K e.hom.hom
  let h₁ : Presheaf.IsLocallySurjective K (toSheafify K (G.op.lan.obj P.obj)) :=
    (K.W_toSheafify (G.op.lan.obj P.obj)).isLocallySurjective
  exact @Presheaf.isLocallySurjective_comp _ _ K _ _ _ _ _ _ _ _ _
    (toSheafify K (G.op.lan.obj P.obj)) e.hom.hom h₁ h₂

end sheafPullbackConstruction

variable (P : Cᵒᵖ ⥤ A) [G.op.HasPointwiseLeftKanExtension P] (W : D)
  [IsFiltered (CostructuredArrow G.op (op W))]
  [PreservesFilteredColimitsOfSize.{v₁, max u₁ v₂} (forget A)]

/-- Elements of the original pointwise Kan extension have original-value representatives. -/
theorem exists_lan_representative (s : ToType ((G.op.lan.obj P).obj (op W))) :
    ∃ (U : C) (a : W ⟶ G.obj U) (t : ToType (P.obj (op U))),
      (G.op.lan.obj P).map a.op (((G.op.lanUnit.app P).app (op U)) t) = s := by
  let hc := isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op P (op W)
  obtain ⟨a, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget A) hc) s
  have ht' : ((G.op.lanUnit.app P).app a.left ≫ (G.op.lan.obj P).map a.hom) t = s := ht
  refine ⟨a.left.unop, a.hom.unop, t, ?_⟩
  simpa only [ConcreteCategory.comp_apply, Quiver.Hom.op_unop, op_unop] using ht'

/-- Equality in the original filtered Kan colimit has a common original-value witness. -/
theorem exists_common_lan_representative (U V : C) (a : W ⟶ G.obj U)
    (b : W ⟶ G.obj V) (s : ToType (P.obj (op U))) (t : ToType (P.obj (op V)))
    (h : (G.op.lan.obj P).map a.op (((G.op.lanUnit.app P).app (op U)) s) =
      (G.op.lan.obj P).map b.op (((G.op.lanUnit.app P).app (op V)) t)) :
    ∃ (T : C) (c : W ⟶ G.obj T) (p : T ⟶ U) (q : T ⟶ V),
      c ≫ G.map p = a ∧ c ≫ G.map q = b ∧ P.map p.op s = P.map q.op t := by
  let hc := isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op P (op W)
  have h' : ((G.op.lanUnit.app P).app (op U) ≫ (G.op.lan.obj P).map a.op) s =
      ((G.op.lanUnit.app P).app (op V) ≫ (G.op.lan.obj P).map b.op) t := by
    simpa only [ConcreteCategory.comp_apply] using h
  obtain ⟨T, p, q, hpq⟩ := (Types.FilteredColimit.isColimit_eq_iff _
    (isColimitOfPreserves (forget A) hc)
    (i := CostructuredArrow.mk a.op) (j := CostructuredArrow.mk b.op)
    (xi := s) (xj := t)).mp h'
  refine ⟨T.left.unop, T.hom.unop, p.left.unop, q.left.unop, ?_, ?_, hpq⟩
  · exact congrArg Quiver.Hom.unop (CostructuredArrow.w p)
  · exact congrArg Quiver.Hom.unop (CostructuredArrow.w q)

end CategoryTheory.Functor
