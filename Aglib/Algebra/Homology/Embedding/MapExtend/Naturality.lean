/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Embedding.MapExtend

/-!
# Functor naturality of the original extension comparison

The same native extension comparison commutes with natural transformations
between zero-preserving functors and with their composition. Retained terms
give the original components; all maps to an omitted target term are the
unique maps to the original zero object. No additivity or homology
preservation is required. These equations transport actual unit squares
through the unchanged extension by zero.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u₁ u₂ u₃ v₁ v₂ v₃ w w'

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The original optional-term comparison is natural in the actual
coefficient functor, retaining the original transformation component. -/
theorem extend.mapXIso_hom_natTrans (G : C ⥤ D) [G.PreservesZeroMorphisms]
    (α : F ⟶ G) (a : Option ι) :
    α.app (extend.X K a) ≫ (extend.mapXIso K G a).hom =
      (extend.mapXIso K F a).hom ≫
        extend.mapX ((NatTrans.mapHomologicalComplex α c).app K) a := by
  cases a with
  | none => exact (CategoryTheory.Limits.isZero_zero D).eq_of_tgt _ _
  | some i => simp [extend.mapXIso, extend.mapX, extend.X]

/-- Two-naturality retains the same actual chain comparison and actual
extended natural-transformation map on both sides. -/
@[reassoc]
theorem mapExtendIso_hom_natTrans (G : C ⥤ D) [G.PreservesZeroMorphisms]
    (α : F ⟶ G) (e : c.Embedding c') :
    (NatTrans.mapHomologicalComplex α c').app (K.extend e) ≫
        (K.mapExtendIso G e).hom =
      (K.mapExtendIso F e).hom ≫
        HomologicalComplex.extendMap ((NatTrans.mapHomologicalComplex α c).app K) e := by
  ext j
  exact extend.mapXIso_hom_natTrans K F G α (e.r j)

variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [HasZeroMorphisms E]

/-- Successive original optional-term comparisons agree with the
comparison for the original composite functor. -/
theorem extend.mapXIso_hom_comp (G : D ⥤ E) [G.PreservesZeroMorphisms] (a : Option ι) :
    (extend.mapXIso K (F ⋙ G) a).hom =
      G.map (extend.mapXIso K F a).hom ≫
        (extend.mapXIso ((F.mapHomologicalComplex c).obj K) G a).hom := by
  cases a with
  | none => exact (CategoryTheory.Limits.isZero_zero E).eq_of_tgt _ _
  | some i => simp [extend.mapXIso]

/-- Composition coherence for the same actual extension-by-zero chain
comparison, using the original mapped comparison in the middle. -/
theorem mapExtendIso_hom_comp (G : D ⥤ E) [G.PreservesZeroMorphisms]
    (e : c.Embedding c') :
    (K.mapExtendIso (F ⋙ G) e).hom =
      (G.mapHomologicalComplex c').map (K.mapExtendIso F e).hom ≫
        (((F.mapHomologicalComplex c).obj K).mapExtendIso G e).hom := by
  ext j
  exact extend.mapXIso_hom_comp K F G (e.r j)

/-- An actual natural-transformation square remains the same square
after native extension by zero, with all original comparison factors.
The hypothesis is the original chain square, rather than a homology or
base-change comparison premise. -/
theorem mapExtendIso_hom_natTrans_square
    (U : C ⥤ E) (V : D ⥤ E) [U.PreservesZeroMorphisms] [V.PreservesZeroMorphisms]
    (α : U ⟶ F ⋙ V) (e : c.Embedding c')
    (L : HomologicalComplex D c) (A B : HomologicalComplex E c)
    (δ : (F.mapHomologicalComplex c).obj K ⟶ L)
    (i : (U.mapHomologicalComplex c).obj K ⟶ A)
    (j : (V.mapHomologicalComplex c).obj L ⟶ B) (g : A ⟶ B)
    (h : (NatTrans.mapHomologicalComplex α c).app K ≫
      (V.mapHomologicalComplex c).map δ ≫ j = i ≫ g) :
    (NatTrans.mapHomologicalComplex α c').app (K.extend e) ≫
        (V.mapHomologicalComplex c').map
          ((K.mapExtendIso F e).hom ≫ HomologicalComplex.extendMap δ e) ≫
        (L.mapExtendIso V e).hom ≫ HomologicalComplex.extendMap j e =
      (K.mapExtendIso U e).hom ≫ HomologicalComplex.extendMap i e ≫
        HomologicalComplex.extendMap g e := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (((F.mapHomologicalComplex c).obj K).mapExtendIso_hom_naturality V e δ)]
  rw [← reassoc_of% (K.mapExtendIso_hom_comp F V e)]
  rw [reassoc_of% (K.mapExtendIso_hom_natTrans U (F ⋙ V) α e)]
  have he := congrArg (fun φ => (K.mapExtendIso U e).hom ≫ (e.extendFunctor E).map φ) h
  simpa only [Functor.map_comp, ComplexShape.Embedding.extendFunctor_obj,
    ComplexShape.Embedding.extendFunctor_map, HomologicalComplex.extendMap_comp,
    Category.assoc] using he

end HomologicalComplex
