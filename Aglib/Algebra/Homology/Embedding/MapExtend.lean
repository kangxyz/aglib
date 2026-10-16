/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Mapping the original extension of a homological complex

A zero-preserving functor commutes with the original extension by zero along
an embedding of complex shapes. On the image, the comparison retains the
native `extendXIso`; outside the image it is the unique isomorphism of the
actual zero objects. No kernel or exactness preservation is required.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u₁ u₂ v₁ v₂ w w'

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Mapping the original optional extension term retains its original support. -/
def extend.mapXIso (a : Option ι) :
    F.obj (extend.X K a) ≅ extend.X ((F.mapHomologicalComplex c).obj K) a :=
  match a with
  | some _ => Iso.refl _
  | none => (F.map_isZero (CategoryTheory.Limits.isZero_zero C)).iso
      (CategoryTheory.Limits.isZero_zero D)

/-- The optional term comparison retains the original extension differentials. -/
theorem extend.mapXIso_hom_d (a b : Option ι) :
    (extend.mapXIso K F a).hom ≫ extend.d ((F.mapHomologicalComplex c).obj K) a b =
      F.map (extend.d K a b) ≫ (extend.mapXIso K F b).hom := by
  cases a <;> cases b <;> simp [extend.mapXIso, extend.d]

/-- A retained optional term uses the native original extension term transport. -/
theorem extend.mapXIso_hom_XIso {a : Option ι} {i : ι} (h : a = some i) :
    (extend.mapXIso K F a).hom ≫
        (extend.XIso ((F.mapHomologicalComplex c).obj K) h).hom =
      F.map (extend.XIso K h).hom := by
  subst a
  simp [extend.mapXIso, extend.XIso, extend.X]

/-- Original coefficient components commute with the optional term comparison. -/
theorem extend.mapXIso_hom_naturality
    {L : HomologicalComplex C c} (φ : K ⟶ L) (a : Option ι) :
    F.map (extend.mapX φ a) ≫ (extend.mapXIso L F a).hom =
      (extend.mapXIso K F a).hom ≫
        extend.mapX ((F.mapHomologicalComplex c).map φ) a := by
  cases a <;> simp [extend.mapXIso, extend.mapX]

variable (e : c.Embedding c')

/-- The original extension terms commute with a zero-preserving functor. -/
def mapExtendXIso (j : ι') :
    F.obj ((K.extend e).X j) ≅ (((F.mapHomologicalComplex c).obj K).extend e).X j :=
  extend.mapXIso K F (e.r j)

/-- The component comparison retains the native extension term isomorphisms. -/
@[reassoc]
theorem mapExtendXIso_hom_extendXIso {i : ι} {j : ι'} (h : e.f i = j) :
    (K.mapExtendXIso F e j).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom =
      F.map (K.extendXIso e h).hom :=
  extend.mapXIso_hom_XIso K F (e.r_eq_some h)

/-- A zero-preserving functor commutes with the original native extension
along an embedding of complex shapes. -/
def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e := by
  refine HomologicalComplex.Hom.isoOfComponents (K.mapExtendXIso F e) ?_
  intro i j _
  exact extend.mapXIso_hom_d K F (e.r i) (e.r j)

/-- The actual chain comparison has the original term comparison components. -/
@[simp]
theorem mapExtendIso_hom_f (j : ι') :
    (K.mapExtendIso F e).hom.f j = (K.mapExtendXIso F e j).hom := rfl

/-- In every retained degree the original extension term equation is unchanged. -/
@[reassoc]
theorem mapExtendIso_hom_f_extendXIso {i : ι} {j : ι'} (h : e.f i = j) :
    (K.mapExtendIso F e).hom.f j ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom =
      F.map (K.extendXIso e h).hom :=
  K.mapExtendXIso_hom_extendXIso F e h

/-- The retained-degree component is the original mapped term transport
followed by the inverse native transport on the extended target. -/
theorem mapExtendIso_hom_f_eq {i : ι} {j : ι'} (h : e.f i = j) :
    (K.mapExtendIso F e).hom.f j = F.map (K.extendXIso e h).hom ≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  apply (cancel_mono (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact K.mapExtendIso_hom_f_extendXIso F e h

/-- Outside the original support the comparison is the unique zero morphism. -/
theorem mapExtendIso_hom_f_eq_zero (j : ι') (h : ∀ i, e.f i ≠ j) :
    (K.mapExtendIso F e).hom.f j = 0 :=
  (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j h).eq_of_tgt _ _

/-- The same extension comparison retains every original coefficient chain map. -/
@[reassoc]
theorem mapExtendIso_hom_naturality {L : HomologicalComplex C c} (φ : K ⟶ L) :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
        (L.mapExtendIso F e).hom =
      (K.mapExtendIso F e).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext j
  exact extend.mapXIso_hom_naturality K F φ (e.r j)

end HomologicalComplex

namespace ComplexShape.Embedding

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- Native extension by zero commutes naturally with a zero-preserving functor. -/
def mapExtendNatIso (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (fun K => K.mapExtendIso F e)
    (fun {K _L} φ => K.mapExtendIso_hom_naturality F e φ)

end ComplexShape.Embedding
