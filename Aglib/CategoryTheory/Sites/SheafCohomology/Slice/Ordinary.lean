/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Naturality

/-!
# The ordinary slice comparison and its original evaluation

The ordinary source is Mathlib's literal `Sheaf.H'`. Both naturality equations
use its original cohomology presheaf maps. Degree zero evaluates the original
sheafification adjunction at the identity generator, without redefining that
evaluation by transport through the comparison.
-/

@[expose] public noncomputable section

universe w₀ w₁ w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- The free presheaf map underlying the ordinary source comparison sends the
lifted identity to the original identity generator. -/
theorem ordinarySource_generator (U : C) :
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
      (uliftYonedaIsoYoneda.{v, v}.hom.app U)).app (op U)
        (FreeAbelianGroup.of (ULift.up.{v} (𝟙 U))) =
      FreeAbelianGroup.of (𝟙 U) := by
  change FreeAbelianGroup.map ULift.down (FreeAbelianGroup.of (ULift.up.{v} (𝟙 U))) = _
  exact FreeAbelianGroup.map_of_apply _

/-- The actual ordinary source isomorphism preserves the native evaluation
formula, by naturality of sheafification and the free identity generator. -/
theorem ordinarySource_evaluation (U : C) (F : Sheaf J AddCommGrpCat.{v})
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    Hypercohomology.sectionsAddEquiv J U F
      ((LargeCohomology.ordinarySourceIso J).hom.app U ≫ a) =
      (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F a).app (op U))
        (FreeAbelianGroup.of (𝟙 U)) := by
  let p := ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
    (uliftYonedaIsoYoneda.{v, v}.hom.app U)
  have h := (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv_naturality_left p a
  have he := congrArg (fun b => b.app (op U)
    (FreeAbelianGroup.of (ULift.up.{v} (𝟙 U)))) h
  change Hypercohomology.sectionsEquiv J U F
    ((presheafToSheaf J AddCommGrpCat.{v}).map p ≫ a) = _
  rw [Hypercohomology.sectionsEquiv_apply]
  exact he.trans (congrArg
    (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F a).app (op U))
    (ordinarySource_generator U))

variable [HasExt.{w₀} (Sheaf J AddCommGrpCat.{v})]

/-- The inverse ordinary comparison is precomposition by the actual source
isomorphism, including in degree zero. -/
theorem ordinaryComparison_inv_mk₀ (U : C) (F : Sheaf J AddCommGrpCat.{v})
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    (((LargeCohomology.ordinaryComparison.{w₀} J 0).inv.app F).app (op U)) (Ext.mk₀ a) =
      Ext.mk₀ ((LargeCohomology.ordinarySourceIso J).hom.app U ≫ a) := by
  change (Ext.mk₀ ((LargeCohomology.ordinarySourceIso J).hom.app U)).comp
    (Ext.mk₀ a) (Nat.zero_add 0) = _
  exact Ext.mk₀_comp_mk₀ _ _

variable (U : C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})]
  [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{v})]
  [HasExt.{w₁} (Sheaf (J.over U) AddCommGrpCat.{v})]

/-- Naturality in coefficients for Mathlib's original cohomology presheaf. -/
theorem ordinarySliceComparison_naturality {F G : Sheaf J AddCommGrpCat.{v}}
    (g : F ⟶ G) (n : ℕ) (x : F.H'.{w₀} n U) :
    ordinarySliceComparison.{w₀, w₁, v, u} J U G n
      (((Sheaf.cohomologyPresheafFunctor J n).map g).app (op U) x) =
    Sheaf.H.map ((J.overPullback AddCommGrpCat.{v} U).map g) n
      (ordinarySliceComparison.{w₀, w₁, v, u} J U F n x) := by
  have h := congrArg (fun a => a.app (op U) x)
    ((LargeCohomology.ordinaryComparison.{w₀} J n).inv.naturality g)
  change (((LargeCohomology.ordinaryComparison.{w₀} J n).inv.app G).app (op U))
      (((Sheaf.cohomologyPresheafFunctor J n).map g).app (op U) x) =
    (((LargeCohomology.presheafFunctor J n).map g).app (op U))
      ((((LargeCohomology.ordinaryComparison.{w₀} J n).inv.app F).app (op U)) x) at h
  exact (congrArg (sliceComparison.{w₀, w₁, v, v, u} J U G n) h).trans
    (sliceComparison_naturality.{w₀, w₁, v, v, u} J U g n _)

/-- Degree zero is evaluation of the literal original `H'` source at its
identity generator under the native sheafification adjunction. -/
theorem ordinarySliceComparison_equiv₀ (F : Sheaf J AddCommGrpCat.{v})
    (x : F.H'.{w₀} 0 U) :
    Sheaf.H.equiv₀ (F.over U) Over.mkIdTerminal (ordinarySliceComparison.{w₀, w₁, v, u} J U F 0 x) =
      (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F
        (Ext.addEquiv₀ x)).app (op U)) (FreeAbelianGroup.of (𝟙 U)) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  change Sheaf.H.equiv₀ (F.over U) Over.mkIdTerminal
    (sliceComparison.{w₀, w₁, v, v, u} J U F 0
      ((((LargeCohomology.ordinaryComparison.{w₀} J 0).inv.app F).app (op U)) (Ext.mk₀ a))) = _
  rw [ordinaryComparison_inv_mk₀]
  refine (sliceComparison_equiv₀.{w₀, w₁, v, v, u} J U F
    (Ext.mk₀ ((LargeCohomology.ordinarySourceIso J).hom.app U ≫ a))).trans ?_
  have h₀ {A B : Sheaf J AddCommGrpCat.{v}} (a : A ⟶ B) :
      Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  simp only [h₀]
  exact ordinarySource_evaluation J U F a

variable {U} {V : C} (f : V ⟶ U)
  [HasSheafify (J.over V) AddCommGrpCat.{v}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(J.over V).HasSheafCompose (forget AddCommGrpCat.{v})]
  [HasExt.{w₂} (Sheaf (J.over V) AddCommGrpCat.{v})]

/-- The ordinary comparison intertwines the original presheaf restriction and
the independently constructed exact-functor slice restriction. -/
theorem ordinarySliceComparison_restriction (F : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) (x : F.H'.{w₀} n U) :
    sliceRestriction.{w₁, w₂, v, v, u} J f F n (ordinarySliceComparison.{w₀, w₁, v, u} J U F n x) =
      ordinarySliceComparison.{w₀, w₂, v, u} J V F n ((F.cohomologyPresheaf n).map f.op x) := by
  have h := congrArg (fun a => a x)
    (((LargeCohomology.ordinaryComparison.{w₀} J n).inv.app F).naturality f.op)
  change (((LargeCohomology.ordinaryComparison.{w₀} J n).inv.app F).app (op V))
      ((F.cohomologyPresheaf n).map f.op x) =
    (LargeCohomology.presheaf J F n).map f.op
      ((((LargeCohomology.ordinaryComparison.{w₀} J n).inv.app F).app (op U)) x) at h
  exact (sliceComparison_restriction.{w₀, w₁, w₂, v, v, u} J f F n
    ((((LargeCohomology.ordinaryComparison.{w₀} J n).inv.app F).app (op U)) x)).trans
    (congrArg (sliceComparison.{w₀, w₂, v, v, u} J V F n) h.symm)

end CategoryTheory.Sheaf.SliceCohomology
