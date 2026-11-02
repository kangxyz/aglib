/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Pullback.Restriction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Basic

/-!
# Internal Hom and native module pullback

The comparison map uses the original global adjunction unit. Its sections are
identified with the actual slice adjunction, and this proves invertibility of
that same map for the stated product-preserving site presentation. The ring
world is independent of the common module carrier bounding both sites.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

universe uC vC uD vD r m

namespace SheafOfModules.Pullback

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J CommRingCat.{r}} {R : Sheaf K CommRingCat.{r}}
  (θ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} J K).obj R)

/-- The actual native ring-valued structural map of a commutative ringed-site map. -/
def ringHom : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
    (F.sheafPushforwardContinuous RingCat.{r} J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) :=
  ⟨Functor.whiskerRight θ.hom (forget₂ CommRingCat RingCat)⟩

variable [(pushforward.{max uC vC uD vD m} (ringHom θ)).IsRightAdjoint]
  (N : SheafOfModules.{max uC vC uD vD m}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (P : SheafOfModules.{max uC vC uD vD m}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))

/-- The section map induced by the original global pullback-adjunction unit. -/
def pushforwardHomSection (U : Cᵒᵖ)
    (s : (InternalHom.sheaf R ((pullback (ringHom θ)).obj N) P).val.obj (F.op.obj U)) :
    (InternalHom.sheaf S N ((pushforward (ringHom θ)).obj P)).val.obj U :=
  ⟨{
    app V := AddCommGrpCat.ofHom <|
      ((s.val.app ((Over.post F).op.obj V)).hom).comp
        (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
          (op V.unop.left)).hom.toAddMonoidHom
    naturality {V W} i := by
      ext x
      change s.val.app ((Over.post F).op.obj W)
        (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
          (op W.unop.left) (N.val.map i.unop.left.op x)) =
        P.val.map (F.map i.unop.left).op
          (s.val.app ((Over.post F).op.obj V)
            (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
              (op V.unop.left) x))
      have hu := PresheafOfModules.naturality_apply
        ((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val i.unop.left.op x
      have hs := NatTrans.naturality_apply s.val ((Over.post F).map i.unop).op
        (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
          (op V.unop.left) x)
      exact (congrArg (s.val.app ((Over.post F).op.obj W)) hu).trans hs
  }, by
    intro V a x
    have hu := (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
      (op V.unop.left)).hom.map_smul a x
    have hs := s.property ((Over.post F).op.obj V) (θ.hom.app (op V.unop.left) a)
      (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
        (op V.unop.left) x)
    exact (congrArg (s.val.app ((Over.post F).op.obj V)) hu).trans hs⟩

theorem pushforwardHomSection_apply (U : Cᵒᵖ)
    (s : (InternalHom.sheaf R ((pullback (ringHom θ)).obj N) P).val.obj (F.op.obj U))
    (V : (Over U.unop)ᵒᵖ) (x : N.val.obj (op V.unop.left)) :
    (pushforwardHomSection.{uC, vC, uD, vD, r, m} θ N P U s).val.app V x =
      s.val.app ((Over.post F).op.obj V)
        (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
          (op V.unop.left) x) := rfl

/-- The actual direct-image/internal-Hom comparison, before any invertibility assertion. -/
def pushforwardHomMap :
    (pushforward (ringHom θ)).obj
      (InternalHom.sheaf R ((pullback (ringHom θ)).obj N) P) ⟶
      InternalHom.sheaf S N ((pushforward (ringHom θ)).obj P) where
  val.app U := ModuleCat.ofHom
    (X := ((pushforward (ringHom θ)).obj
      (InternalHom.sheaf R ((pullback (ringHom θ)).obj N) P)).val.obj U)
    (Y := (InternalHom.sheaf S N ((pushforward (ringHom θ)).obj P)).val.obj U) {
    toFun := pushforwardHomSection.{uC, vC, uD, vD, r, m} θ N P U
    map_add' s t := by
      apply Subtype.ext
      change (_ : InternalHom.RawHom S N ((pushforward (ringHom θ)).obj P) U.unop) = _
      ext V x
      rfl
    map_smul' a s := by
      apply Subtype.ext
      change (_ : InternalHom.RawHom S N ((pushforward (ringHom θ)).obj P) U.unop) = _
      ext V x
      change R.obj.map (F.map V.unop.hom).op (θ.hom.app U a) •
          (show P.val.obj (op (F.obj V.unop.left)) from
            s.val.app ((Over.post F).op.obj V)
            (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
              (op V.unop.left) x)) =
        θ.hom.app (op V.unop.left) (S.obj.map V.unop.hom.op a) •
          (show P.val.obj (op (F.obj V.unop.left)) from
            s.val.app ((Over.post F).op.obj V)
            (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
              (op V.unop.left) x))
      congr 1
      exact (ConcreteCategory.congr_hom (θ.hom.naturality V.unop.hom.op) a).symm }
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : InternalHom.RawHom S N ((pushforward (ringHom θ)).obj P) V.unop) = _
    ext W x
    let A : Over (F.obj U.unop) :=
      (Over.post F).obj ((Over.map i.unop).obj W.unop)
    let B : Over (F.obj U.unop) :=
      (Over.map (F.map i.unop)).obj ((Over.post F).obj W.unop)
    let j : A ⟶ B := Over.homMk (𝟙 (F.obj W.unop.left)) (by
      change (𝟙 _) ≫ (F.map W.unop.hom ≫ F.map i.unop) = F.map (W.unop.hom ≫ i.unop)
      exact (Category.id_comp _).trans (F.map_comp _ _).symm)
    let y : ((pullback (ringHom θ)).obj N).val.obj (op (F.obj W.unop.left)) :=
      ((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
        (op W.unop.left) x
    change s.val.app (op B) y = s.val.app (op A) y
    have hs : s.val.app (op A) = s.val.app (op B) := by
      have h := s.val.naturality j.op
      change ((pullback (ringHom θ)).obj N).val.presheaf.map
          (𝟙 (op (F.obj W.unop.left))) ≫ s.val.app (op A) =
        s.val.app (op B) ≫ P.val.presheaf.map (𝟙 (op (F.obj W.unop.left))) at h
      have h₁ := congrArg (fun k : ((pullback (ringHom θ)).obj N).val.presheaf.obj
        (op (F.obj W.unop.left)) ⟶ ((pullback (ringHom θ)).obj N).val.presheaf.obj
          (op (F.obj W.unop.left)) ↦ k ≫ s.val.app (op A))
        (((pullback (ringHom θ)).obj N).val.presheaf.map_id (op (F.obj W.unop.left)))
      have h₂ := congrArg (fun k : P.val.presheaf.obj (op (F.obj W.unop.left)) ⟶
        P.val.presheaf.obj (op (F.obj W.unop.left)) ↦ s.val.app (op B) ≫ k)
        (P.val.presheaf.map_id (op (F.obj W.unop.left)))
      exact (Category.id_comp _).symm.trans
        (h₁.symm.trans (h.trans (h₂.trans (Category.comp_id _))))
    exact congrArg (fun k : ((pullback (ringHom θ)).obj N).val.presheaf.obj
      (op (F.obj W.unop.left)) ⟶ P.val.presheaf.obj (op (F.obj W.unop.left)) ↦ k y) hs.symm

theorem pushforwardHomMap_apply (U : Cᵒᵖ)
    (s : (InternalHom.sheaf R ((pullback (ringHom θ)).obj N) P).val.obj (F.op.obj U)) :
    (pushforwardHomMap.{uC, vC, uD, vD, r, m} θ N P).val.app U s =
      pushforwardHomSection.{uC, vC, uD, vD, r, m} θ N P U s := rfl

section Slice

variable [HasBinaryProducts C] [HasBinaryProducts D]
  [PreservesLimitsOfShape (Discrete WalkingPair) F]
  (U : C) [(Over.post F).IsContinuous (J.over U) (K.over (F.obj U))]
  [(pushforward.{max uC vC uD vD m} (restrictedRingHom (ringHom θ) U)).IsRightAdjoint]

/-- The original native slice adjunction as a bijection of internal-Hom sections. -/
def pullbackHomSectionsEquiv :
    (InternalHom.sheaf R ((pullback (ringHom θ)).obj N) P).val.obj (op (F.obj U)) ≃
      (InternalHom.sheaf S N ((pushforward (ringHom θ)).obj P)).val.obj (op U) :=
  (InternalHom.sectionHomEquiv R ((pullback (ringHom θ)).obj N) P (F.obj U)).trans
    ((restrictionHomEquiv (ringHom θ) U N P).trans
      (InternalHom.sectionHomEquiv S N ((pushforward (ringHom θ)).obj P) U).symm)

/-- The slice equivalence is the previously defined original-unit section map. -/
theorem pullbackHomSectionsEquiv_apply
    (s : (InternalHom.sheaf R ((pullback (ringHom θ)).obj N) P).val.obj (op (F.obj U))) :
    pullbackHomSectionsEquiv.{uC, vC, uD, vD, r, m} θ N P U s =
      pushforwardHomSection.{uC, vC, uD, vD, r, m} θ N P (op U) s := by
  apply Subtype.ext
  change (_ : InternalHom.RawHom S N ((pushforward (ringHom θ)).obj P) U) = _
  ext V x
  change (restrictionHomEquiv (ringHom θ) U N P
    (InternalHom.sectionHomEquiv R ((pullback (ringHom θ)).obj N) P (F.obj U) s)).val.app V x =
      s.val.app ((Over.post F).op.obj V)
        (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
          (op V.unop.left) x)
  rw [restrictionHomEquiv_apply]
  rfl

end Slice

section IsIso

variable [HasBinaryProducts C] [HasBinaryProducts D]
  [PreservesLimitsOfShape (Discrete WalkingPair) F]
  [∀ U : C, (Over.post F).IsContinuous (J.over U) (K.over (F.obj U))]
  [∀ U : C,
    (pushforward.{max uC vC uD vD m} (restrictedRingHom (ringHom θ) U)).IsRightAdjoint]

/-- The actual unit-induced map is invertible under the proved slice-comparison conditions. -/
theorem pushforwardHomMap_isIso : IsIso (pushforwardHomMap.{uC, vC, uD, vD, r, m} θ N P) := by
  let T := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
  let G := forget T ⋙ PresheafOfModules.toPresheaf T.obj
  rw [← isIso_iff_of_reflects_iso (pushforwardHomMap.{uC, vC, uD, vD, r, m} θ N P) G]
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (pushforwardHomSection.{uC, vC, uD, vD, r, m} θ N P U)
  convert (pullbackHomSectionsEquiv.{uC, vC, uD, vD, r, m} θ N P U.unop).bijective using 1
  funext s
  exact (pullbackHomSectionsEquiv_apply.{uC, vC, uD, vD, r, m} θ N P U.unop s).symm

/-- The isomorphism whose forward map is the actual original-unit Hom comparison. -/
def pushforwardHomIso :
    (pushforward (ringHom θ)).obj
      (InternalHom.sheaf R ((pullback (ringHom θ)).obj N) P) ≅
      InternalHom.sheaf S N ((pushforward (ringHom θ)).obj P) :=
  let := pushforwardHomMap_isIso.{uC, vC, uD, vD, r, m} θ N P
  asIso (pushforwardHomMap.{uC, vC, uD, vD, r, m} θ N P)

end IsIso

end SheafOfModules.Pullback
