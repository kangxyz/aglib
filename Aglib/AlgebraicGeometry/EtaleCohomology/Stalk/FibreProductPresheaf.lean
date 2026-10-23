/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestriction

/-! # The actual fibre-product scheme cohomology presheaf -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w s t

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{t} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The original scheme cohomology groups are small in the coefficient universe.
Only these groups will be resized; the coefficient sheaf is unchanged. -/
instance fibreProductCohomology_small (U : S.Etale) :
    Small.{u + 1} (Sheaf.H.{t} ((inverseImage (pullback.snd U.hom f)).obj F) q) := by
  let : Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :=
    originalCohomologyPresheaf_small f F q (op U)
  exact small_of_injective (fibreProductCohomologyEquiv f U F q).symm.injective

/-- The inverse value comparison preserves the actual scheme restriction. -/
theorem fibreProductCohomologyRestriction_original {U V : S.Etale} (g : V ⟶ U)
    (x : Sheaf.H.{t} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (fibreProductCohomologyEquiv f V F q).symm
        (fibreProductCohomologyRestriction f g F q x) =
      (originalCohomologyPresheaf f F q).map g.op
        ((fibreProductCohomologyEquiv f U F q).symm x) := by
  obtain ⟨y, rfl⟩ := (fibreProductCohomologyEquiv f U F q).surjective x
  rw [← fibreProductCohomologyEquiv_restriction, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-- Identity for the actual original cohomology restriction. -/
theorem fibreProductCohomologyRestriction_id (U : S.Etale)
    (x : Sheaf.H.{t} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    fibreProductCohomologyRestriction f (𝟙 U) F q x = x := by
  obtain ⟨y, rfl⟩ := (fibreProductCohomologyEquiv f U F q).surjective x
  rw [← fibreProductCohomologyEquiv_restriction]
  exact congrArg (fibreProductCohomologyEquiv f U F q)
    (ConcreteCategory.congr_hom ((originalCohomologyPresheaf f F q).map_id (op U)) y)

/-- Composition for the actual original cohomology restriction. -/
theorem fibreProductCohomologyRestriction_comp {U V W : S.Etale}
    (g : V ⟶ U) (h : W ⟶ V)
    (x : Sheaf.H.{t} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    fibreProductCohomologyRestriction f (h ≫ g) F q x =
      fibreProductCohomologyRestriction f h F q
        (fibreProductCohomologyRestriction f g F q x) := by
  obtain ⟨y, rfl⟩ := (fibreProductCohomologyEquiv f U F q).surjective x
  rw [← fibreProductCohomologyEquiv_restriction,
    ← fibreProductCohomologyEquiv_restriction, ← fibreProductCohomologyEquiv_restriction]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Original cohomology on the actual fibre products, with original scheme pullbacks. -/
def smallFibreProductCohomologyPresheaf : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := AddCommGrpCat.of
    (Shrink.{u + 1} (Sheaf.H.{t} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q))
  map g := AddCommGrpCat.ofHom (Shrink.addEquiv.symm.toAddMonoidHom.comp
    ((fibreProductCohomologyRestriction f g.unop F q).comp
      Shrink.addEquiv.toAddMonoidHom))
  map_id U := by
    apply ConcreteCategory.ext_apply
    intro x
    change Shrink.addEquiv.symm
      (fibreProductCohomologyRestriction f (𝟙 U.unop) F q (Shrink.addEquiv x)) = x
    rw [fibreProductCohomologyRestriction_id, AddEquiv.symm_apply_apply]
  map_comp g h := by
    apply ConcreteCategory.ext_apply
    intro x
    change Shrink.addEquiv.symm
      (fibreProductCohomologyRestriction f (h.unop ≫ g.unop) F q (Shrink.addEquiv x)) =
      Shrink.addEquiv.symm (fibreProductCohomologyRestriction f h.unop F q
        (Shrink.addEquiv (Shrink.addEquiv.symm
          (fibreProductCohomologyRestriction f g.unop F q (Shrink.addEquiv x)))))
    rw [AddEquiv.apply_symm_apply, fibreProductCohomologyRestriction_comp]

/-- The actual scheme-cohomology diagram is naturally the original represented diagram. -/
def smallFibreProductOriginalIso :
    smallFibreProductCohomologyPresheaf f F q ≅ smallOriginalCohomologyPresheaf f F q :=
  NatIso.ofComponents
    (fun U => (((Shrink.addEquiv :
      Shrink.{u + 1} (Sheaf.H.{t}
        ((inverseImage (pullback.snd U.unop.hom f)).obj F) q) ≃+
      Sheaf.H.{t} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q).trans
      (fibreProductCohomologyEquiv f U.unop F q).symm).trans
        (Shrink.addEquiv : Shrink.{u + 1} ((originalCohomologyPresheaf f F q).obj U) ≃+
          (originalCohomologyPresheaf f F q).obj U).symm).toAddCommGrpIso)
    (by
      intro U V g
      apply ConcreteCategory.ext_apply
      intro x
      let aU : Shrink.{u + 1} (Sheaf.H.{t}
          ((inverseImage (pullback.snd U.unop.hom f)).obj F) q) ≃+
          Sheaf.H.{t} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q :=
        Shrink.addEquiv
      let aV : Shrink.{u + 1} (Sheaf.H.{t}
          ((inverseImage (pullback.snd V.unop.hom f)).obj F) q) ≃+
          Sheaf.H.{t} ((inverseImage (pullback.snd V.unop.hom f)).obj F) q :=
        Shrink.addEquiv
      let bU : Shrink.{u + 1} ((originalCohomologyPresheaf f F q).obj U) ≃+
          (originalCohomologyPresheaf f F q).obj U := Shrink.addEquiv
      let bV : Shrink.{u + 1} ((originalCohomologyPresheaf f F q).obj V) ≃+
          (originalCohomologyPresheaf f F q).obj V := Shrink.addEquiv
      change bV.symm ((fibreProductCohomologyEquiv f V.unop F q).symm
          (aV (aV.symm (fibreProductCohomologyRestriction f g.unop F q (aU x))))) =
        bV.symm ((originalCohomologyPresheaf f F q).map g
          (bU (bU.symm ((fibreProductCohomologyEquiv f U.unop F q).symm (aU x)))))
      simp only [AddEquiv.apply_symm_apply]
      exact congrArg bV.symm
        (fibreProductCohomologyRestriction_original f F q g.unop (aU x)))

end AlgebraicGeometry.Scheme.EtaleCohomology
