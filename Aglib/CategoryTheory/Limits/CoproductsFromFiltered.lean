/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Coproduct preservation from finite sums and filtered colimits

The native diagram of finite subcoproducts computes an arbitrary coproduct.
Consequently a functor preserving finite coproducts and this filtered colimit
preserves the original coproduct. The indexing universe is unrestricted.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

open CoproductsFromFiniteFiltered

universe u v u' v' i

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) [HasFiniteCoproducts C] [PreservesFiniteCoproducts F]
  {ι : Type i} [HasColimitsOfShape (Finset (Discrete ι)) C]
  [PreservesColimitsOfShape (Finset (Discrete ι)) F]
  (f : ι → C) [HasCoproduct f]

/-- An inclusion into the literal native finite-subcoproduct stage. -/
def finiteSubcoproductInclusion (S : Finset (Discrete ι)) (j : S) :
    f j.val.as ⟶ (liftToFinsetObj (Discrete.functor f)).obj S :=
  Sigma.ι (fun j : S => (Discrete.functor f).obj j.val) j

omit [HasColimitsOfShape (Finset (Discrete ι)) C] [HasCoproduct f] in
@[reassoc]
theorem finiteSubcoproductInclusion_map {S T : Finset (Discrete ι)} (h : S ⟶ T) (j : S) :
    finiteSubcoproductInclusion f S j ≫ (liftToFinsetObj (Discrete.functor f)).map h =
      finiteSubcoproductInclusion f T ⟨j.val, h.down.down j.property⟩ := by
  simp [finiteSubcoproductInclusion, liftToFinsetObj]

/-- The native assembly leg, with its total coproduct target fixed explicitly. -/
def finiteSubcoproductLeg (S : Finset (Discrete ι)) :
    (liftToFinsetObj (Discrete.functor f)).obj S ⟶ ∐ f :=
  (finiteSubcoproductsCocone f).ι.app S

omit [HasColimitsOfShape (Finset (Discrete ι)) C] in
@[reassoc]
theorem finiteSubcoproductInclusion_leg (S : Finset (Discrete ι)) (j : S) :
    finiteSubcoproductInclusion f S j ≫ finiteSubcoproductLeg f S =
      Sigma.ι f j.val.as := by
  exact Sigma.ι_comp_desc (fun j : S => Sigma.ι f j.val.as) j

/-- The literal native finite stage, with its original inclusions, is colimiting. -/
def finiteSubcoproductIsColimit (S : Finset (Discrete ι)) :
    IsColimit (Cofan.mk ((liftToFinsetObj (Discrete.functor f)).obj S)
      (finiteSubcoproductInclusion f S)) :=
  coproductIsCoproduct (fun j : S => (Discrete.functor f).obj j.val)

/-- Images of arbitrary coproduct cocones are colimiting whenever finite
coproducts and their native filtered assembly are preserved. -/
def isColimitCofanOfFiniteSubcoproducts :
    IsColimit (Cofan.mk (F.obj (∐ f)) (fun i => F.map (Sigma.ι f i))) := by
  classical
  let G := liftToFinsetObj (Discrete.functor f)
  let hc := isColimitOfPreserves F (isColimitFiniteSubproductsCocone f)
  let hS (S : Finset (Discrete ι)) :=
    isColimitCofanMkObjOfIsColimit F (fun j : S => f j.val.as)
      (finiteSubcoproductInclusion f S) (finiteSubcoproductIsColimit f S)
  let d (s : Cofan (fun i => F.obj (f i))) : Cocone (G ⋙ F) :=
    { pt := s.pt
      ι :=
        { app := fun S => (hS S).desc (Cofan.mk s.pt (fun j : S => s.ι.app j.val))
          naturality := by
            intro S T h
            change F.map (G.map h) ≫ _ = _ ≫ 𝟙 s.pt
            rw [Category.comp_id]
            apply (hS S).hom_ext
            rintro ⟨j⟩
            change F.map (finiteSubcoproductInclusion f S j) ≫ F.map (G.map h) ≫ _ = _
            rw [← F.map_comp_assoc, finiteSubcoproductInclusion_map]
            exact ((hS T).fac (Cofan.mk s.pt (fun j : T => s.ι.app j.val))
              ⟨⟨j.val, h.down.down j.property⟩⟩).trans
                ((hS S).fac (Cofan.mk s.pt (fun j : S => s.ι.app j.val)) ⟨j⟩).symm } }
  refine
    { desc := fun s => hc.desc (d s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    let S : Finset (Discrete ι) := {i}
    let j : S := ⟨i, Finset.mem_singleton_self i⟩
    let t : F.obj (∐ f) ⟶ s.pt := hc.desc (d s)
    have hj : F.map (finiteSubcoproductInclusion f S j) ≫
        F.map (finiteSubcoproductLeg f S) = F.map (Sigma.ι f i.as) := by
      rw [← F.map_comp]
      exact congrArg F.map (finiteSubcoproductInclusion_leg f S j)
    have ht : F.map (finiteSubcoproductLeg f S) ≫ t = (d s).ι.app S :=
      hc.fac (d s) S
    change F.map (Sigma.ι f i.as) ≫ t = s.ι.app i
    rw [← hj, Category.assoc, ht]
    exact (hS S).fac _ ⟨j⟩
  · intro s m hm
    apply hc.hom_ext
    intro S
    change F.map (finiteSubcoproductLeg f S) ≫ m =
      F.map (finiteSubcoproductLeg f S) ≫ hc.desc (d s)
    have ht : F.map (finiteSubcoproductLeg f S) ≫ hc.desc (d s) =
        (d s).ι.app S := hc.fac (d s) S
    rw [ht]
    apply (hS S).hom_ext
    rintro ⟨j⟩
    change F.map (finiteSubcoproductInclusion f S j) ≫
      F.map (finiteSubcoproductLeg f S) ≫ m = _
    rw [← F.map_comp_assoc, finiteSubcoproductInclusion_leg]
    exact (hm j.val).trans
      ((hS S).fac (Cofan.mk s.pt (fun j : S => s.ι.app j.val)) ⟨j⟩).symm

/-- Preservation of finite coproducts and the filtered diagram of finite subsets
implies preservation of the actual arbitrary coproduct. -/
theorem preservesCoproduct_of_finiteSubcoproducts :
    PreservesColimit (Discrete.functor f) F :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f)
    ((isColimitMapCoconeCofanMkEquiv F f (Sigma.ι f)).symm
      (isColimitCofanOfFiniteSubcoproducts F f))

end CategoryTheory.Limits
