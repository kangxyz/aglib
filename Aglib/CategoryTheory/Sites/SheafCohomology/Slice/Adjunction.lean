/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Coproduct
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Exact lower shriek for restriction to a slice site

The left adjoint is constructed from the hom-indexed coproduct extension and
ordinary sheafification. Its exactness follows from exact coproducts, not from
full faithfulness of the forgetful functor from the slice.
-/

@[expose] public noncomputable section

universe v u v' u' t

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [HasCoproducts.{v} A]

/-- Exact coproducts are available at the site-hom size for larger abelian coefficients. -/
instance (priority := 100) abelianGroupsAB4OfSize :
    AB4OfSize.{v} AddCommGrpCat.{max v t} :=
  AB4OfSize_shrink.{v, t} _

/-- The discrete family of actual slice objects over a fixed source. -/
abbrev summandIndex (U V : C) : Discrete (V ⟶ U) ⥤ (Over U)ᵒᵖ :=
  Discrete.functor fun f ↦ op (Over.mk f)

/-- Evaluation of the extension is the ordinary colimit of its discrete summands. -/
def coproductExtensionEvaluationIso (U V : C) :
    coproductExtension (A := A) U ⋙ (evaluation Cᵒᵖ A).obj (op V) ≅
      (Functor.whiskeringLeft _ _ A).obj (summandIndex U V) ⋙ colim :=
  NatIso.ofComponents (fun G ↦ colim.mapIso
    (Discrete.compNatIsoDiscrete (fun f : V ⟶ U ↦ op (Over.mk f)) G).symm) (by
      intro G H α
      change colim.map (Discrete.natTrans (fun f : Discrete (V ⟶ U) ↦
        α.app (op (Over.mk f.as)))) ≫
          colim.map (Discrete.compNatIsoDiscrete (fun f : V ⟶ U ↦ op (Over.mk f)) H).inv =
        colim.map (Discrete.compNatIsoDiscrete (fun f : V ⟶ U ↦ op (Over.mk f)) G).inv ≫
          colim.map ((summandIndex U V).whiskerLeft α)
      rw [← colim.map_comp, ← colim.map_comp]
      congr 1
      ext f
      simp)

instance coproductExtension_preservesFiniteLimits [HasFiniteLimits A] [AB4OfSize.{v} A]
    (U : C) : PreservesFiniteLimits (coproductExtension (A := A) U) := by
  apply preservesFiniteLimits_of_evaluation
  intro V
  exact preservesFiniteLimits_of_natIso (coproductExtensionEvaluationIso A U V.unop).symm

/-- Actual lower shriek, using the explicit hom-indexed coproduct construction. -/
def lowerShriek (U : C) [HasWeakSheafify J A] :
    Sheaf (J.over U) A ⥤ Sheaf J A :=
  sheafToPresheaf (J.over U) A ⋙ coproductExtension U ⋙ presheafToSheaf J A

/-- The lower-shriek adjunction has the original slice-restriction right adjoint. -/
def lowerShriekAdjunction (U : C) [HasWeakSheafify J A] :
    lowerShriek J A U ⊣ J.overPullback A U :=
  ((coproductAdjunction (A := A) U).comp (sheafificationAdjunction J A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (J.over U) A) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

instance lowerShriek_isLeftAdjoint (U : C) [HasWeakSheafify J A] :
    (lowerShriek J A U).IsLeftAdjoint := (lowerShriekAdjunction J A U).isLeftAdjoint

instance lowerShriek_preservesFiniteLimits [HasFiniteLimits A] [AB4OfSize.{v} A]
    (U : C) [HasSheafify J A] : PreservesFiniteLimits (lowerShriek J A U) := by
  unfold lowerShriek
  infer_instance

instance lowerShriek_preservesFiniteColimits (U : C) [HasWeakSheafify J A] :
    PreservesFiniteColimits (lowerShriek J A U) := by infer_instance

instance lowerShriek_additive [Preadditive A] (U : C) [HasSheafify J A] :
    (lowerShriek J A U).Additive := by
  let : (J.overPullback A U).Additive := ⟨by intros; rfl⟩
  exact (lowerShriekAdjunction J A U).left_adjoint_additive

/-- The hom equivalence is evaluated on the designated slice summand. -/
theorem lowerShriekAdjunction_homEquiv_app (U : C) [HasWeakSheafify J A]
    (G : Sheaf (J.over U) A) (F : Sheaf J A) (α : (lowerShriek J A U).obj G ⟶ F)
    (V : (Over U)ᵒᵖ) :
    ((lowerShriekAdjunction J A U).homEquiv G F α).hom.app V =
      Limits.Sigma.ι (summands U G.obj V.unop.left) V.unop.hom ≫
        ((sheafificationAdjunction J A).homEquiv _ F α).app (op V.unop.left) := by
  simp only [lowerShriekAdjunction, Adjunction.restrictFullyFaithful,
    Adjunction.mkOfHomEquiv_homEquiv, Adjunction.comp_homEquiv, coproductAdjunction,
    coproductHomEquiv, Trans.trans, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  change (restrictHom U (((sheafificationAdjunction J A).homEquiv _ F) (𝟙 _ ≫ α)) ≫
    𝟙 _).app V = _
  simp only [Category.comp_id]
  simpa only [] using! congrArg
    (fun b : (lowerShriek J A U).obj G ⟶ F ↦
      (restrictHom U ((sheafificationAdjunction J A).homEquiv _ F b)).app V)
    (Category.id_comp α)

/-- On each summand the counit is the original presheaf sheafification unit. -/
theorem lowerShriekAdjunction_counit_summand (U : C) [HasWeakSheafify J A]
    (F : Sheaf J A) (V : C) (f : V ⟶ U) :
    Limits.Sigma.ι (summands U ((J.overPullback A U).obj F).obj V) f ≫
      ((sheafificationAdjunction J A).homEquiv _ F
        ((lowerShriekAdjunction J A U).counit.app F)).app (op V) = 𝟙 (F.obj.obj (op V)) := by
  have h : (lowerShriekAdjunction J A U).homEquiv _ F
      ((lowerShriekAdjunction J A U).counit.app F) = 𝟙 _ := by
    rw [← (lowerShriekAdjunction J A U).homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  simpa only [lowerShriekAdjunction_homEquiv_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
    using! congrArg (fun β ↦ β.hom.app (op (Over.mk f))) h

end CategoryTheory.Sheaf.SliceCohomology
