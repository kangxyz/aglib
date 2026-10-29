/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Native constant units under an actual cocontinuous restriction

The map is the original target constant-presheaf unit whiskered by the actual
site functor. Cocontinuity preserves its local bijectivity; native
sheafification and its counit return the same restricted sheaf. Site object,
Hom and concrete coefficient-value universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

universe uC vC uD vD uA vA wA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (H : C ⥤ D)
  {A : Type uA} [Category.{vA} A] [H.IsContinuous J K]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- Restrict the original target constant-presheaf unit to the actual source site. -/
def restrictionConstantMap (M : A) :
    (Functor.const Cᵒᵖ).obj M ⟶
      ((H.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj M)).obj :=
  Functor.whiskerLeft H.op (toSheafify K ((Functor.const Dᵒᵖ).obj M))

variable {FA : A → A → Type*} {CA : A → Type wA}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{wA} A FA]
  [J.WEqualsLocallyBijective A] [K.WEqualsLocallyBijective A]
  [H.IsCocontinuous J K]

instance restrictionConstantMap_locallyInjective (M : A) :
    Presheaf.IsLocallyInjective J (restrictionConstantMap J K H M) :=
  Presheaf.isLocallyInjective_whisker J K H
    (toSheafify K ((Functor.const Dᵒᵖ).obj M))

instance restrictionConstantMap_locallySurjective (M : A) :
    Presheaf.IsLocallySurjective J (restrictionConstantMap J K H M) :=
  Presheaf.isLocallySurjective_whisker J K H
    (toSheafify K ((Functor.const Dᵒᵖ).obj M))

/-- Native local-bijection detection proves that sheafifying the original
restricted unit is an isomorphism. -/
instance restrictionConstantMap_sheafification_isIso (M : A) :
    IsIso ((presheafToSheaf J A).map (restrictionConstantMap J K H M)) :=
  (J.W_iff (restrictionConstantMap J K H M)).mp
    (J.W_of_isLocallyBijective (restrictionConstantMap J K H M))

/-- The original sheafified unit followed by the native counit, with the
actual restricted sheaf as target. -/
def constantRestrictionIso (M : A) :
    (constantSheaf J A).obj M ≅
      (H.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj M) := by
  let L := presheafToSheaf J A
  let P := (Functor.const Cᵒᵖ).obj M
  let Q := (H.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj M)
  let m : P ⟶ Q.obj := restrictionConstantMap J K H M
  let f := L.map m
  letI : IsIso f :=
    restrictionConstantMap_sheafification_isIso (FA := FA) (CA := CA) J K H M
  let e₁ := asIso f
  let e₂ := asIso ((sheafificationAdjunction J A).counit.app Q)
  exact e₁ ≪≫ e₂

/-- The whole comparison retains the literal whiskered original unit. -/
theorem constantRestrictionIso_unit (M : A) :
    toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
        (constantRestrictionIso (FA := FA) (CA := CA) J K H M).hom.hom =
      restrictionConstantMap J K H M := by
  let P := (Functor.const Cᵒᵖ).obj M
  let Q := (H.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj M)
  change ((sheafificationAdjunction J A).homEquiv P Q)
      (((sheafificationAdjunction J A).homEquiv P Q).symm
        (restrictionConstantMap J K H M)) = restrictionConstantMap J K H M
  exact ((sheafificationAdjunction J A).homEquiv P Q).apply_symm_apply _

/-- An original coefficient-label equation on `U` identifies the complete
restricted map. The actual test arrows to `U` are supplied, with no geometric
point, finiteness or connectedness premise. -/
theorem constantRestriction_map_of_unit_eq {U : D} (k : ∀ V : C, H.obj V ⟶ U)
    (M N : A)
    (q : (constantSheaf K A).obj M ⟶ (constantSheaf K A).obj N) (g : M ⟶ N)
    (h : ∀ a : CA M, (toSheafify K ((Functor.const Dᵒᵖ).obj N)).app (op U) (g a) =
      q.hom.app (op U) ((toSheafify K ((Functor.const Dᵒᵖ).obj M)).app (op U) a)) :
    (constantRestrictionIso (FA := FA) (CA := CA) J K H M).hom ≫
        (H.sheafPushforwardContinuous A J K).map q =
      (constantSheaf J A).map g ≫ (constantRestrictionIso (FA := FA) (CA := CA) J K H N).hom := by
  let R := H.sheafPushforwardContinuous A J K
  let S (P : A) := R.obj ((presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj P))
  let q₀ : (presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj M) ⟶
      (presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj N) := q
  let qR : S M ⟶ S N := R.map q₀
  let iM : (presheafToSheaf J A).obj ((Functor.const Cᵒᵖ).obj M) ⟶ S M :=
    (constantRestrictionIso (FA := FA) (CA := CA) J K H M).hom
  let iN : (presheafToSheaf J A).obj ((Functor.const Cᵒᵖ).obj N) ⟶ S N :=
    (constantRestrictionIso (FA := FA) (CA := CA) J K H N).hom
  let mM : (Functor.const Cᵒᵖ).obj M ⟶ (S M).obj := restrictionConstantMap J K H M
  let mN : (Functor.const Cᵒᵖ).obj N ⟶ (S N).obj := restrictionConstantMap J K H N
  have huM : toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ iM.hom = mM :=
    constantRestrictionIso_unit (FA := FA) (CA := CA) J K H M
  have huN : toSheafify J ((Functor.const Cᵒᵖ).obj N) ≫ iN.hom = mN :=
    constantRestrictionIso_unit (FA := FA) (CA := CA) J K H N
  have h₀ : ∀ a : CA M, (toSheafify K ((Functor.const Dᵒᵖ).obj N)).app (op U) (g a) =
      q₀.hom.app (op U) ((toSheafify K ((Functor.const Dᵒᵖ).obj M)).app (op U) a) := h
  change iM ≫ qR = (presheafToSheaf J A).map ((Functor.const Cᵒᵖ).map g) ≫ iN
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (S N).property
  change toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ (iM.hom ≫ qR.hom) =
    toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
      (sheafifyMap J ((Functor.const Cᵒᵖ).map g) ≫ iN.hom)
  rw [← Category.assoc, huM]
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, huN]
  change Functor.whiskerLeft H.op (toSheafify K ((Functor.const Dᵒᵖ).obj M)) ≫
      Functor.whiskerLeft H.op q₀.hom =
    (Functor.const Cᵒᵖ).map g ≫
      Functor.whiskerLeft H.op (toSheafify K ((Functor.const Dᵒᵖ).obj N))
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.ext_apply
  intro a
  have hM : (toSheafify K ((Functor.const Dᵒᵖ).obj M)).app (op (H.obj V.unop)) a =
      ((presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj M)).obj.map (k V.unop).op
        ((toSheafify K ((Functor.const Dᵒᵖ).obj M)).app (op U) a) := by
    simpa using (toSheafify K ((Functor.const Dᵒᵖ).obj M)).naturality_apply (k V.unop).op a
  have hN : (toSheafify K ((Functor.const Dᵒᵖ).obj N)).app (op (H.obj V.unop)) (g a) =
      ((presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj N)).obj.map (k V.unop).op
        ((toSheafify K ((Functor.const Dᵒᵖ).obj N)).app (op U) (g a)) := by
    simpa using (toSheafify K ((Functor.const Dᵒᵖ).obj N)).naturality_apply
      (k V.unop).op (g a)
  have hq := q₀.hom.naturality_apply (k V.unop).op
    ((toSheafify K ((Functor.const Dᵒᵖ).obj M)).app (op U) a)
  have hv : q₀.hom.app (op (H.obj V.unop))
      ((toSheafify K ((Functor.const Dᵒᵖ).obj M)).app (op (H.obj V.unop)) a) =
    (toSheafify K ((Functor.const Dᵒᵖ).obj N)).app (op (H.obj V.unop)) (g a) := by
    calc
      _ = ((presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj N)).obj.map (k V.unop).op
          (q₀.hom.app (op U)
            ((toSheafify K ((Functor.const Dᵒᵖ).obj M)).app (op U) a)) := by
        exact (congrArg (fun z => q₀.hom.app (op (H.obj V.unop)) z) hM).trans hq
      _ = ((presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj N)).obj.map (k V.unop).op
          ((toSheafify K ((Functor.const Dᵒᵖ).obj N)).app (op U) (g a)) :=
        congrArg
          (fun z => ((presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj N)).obj.map
            (k V.unop).op z) (h₀ a).symm
      _ = _ := hN.symm
  simpa using hv

end CategoryTheory.Functor
