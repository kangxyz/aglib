/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.NormalConstants
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition

/-! # Extend original generic maps through a normal integral model

For a normal integral scheme N over any X, maps from the original generic
inverse image of a coefficient to a finite constant extend to the direct image
of that same constant on N. The extension equation retains the original generic
adjunction, the original direct-image composition and the original constant
generic unit. The model need not be finite or Noetherian.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge

variable {X N : Scheme.{u}} [IsIntegral N]
  [∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)]
  (f : N ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
  (A : AddCommGrpCat.{u + 1}) [Finite A]

/-- Extend the supplied original generic map by the proved finite-constant
generic isomorphism on the actual normal integral model. -/
def extendGenericMap
    (b : (inverseImage (N.fromSpecStalk (genericPoint N) ≫ f)).obj F ⟶
      (constantSheaf (Scheme.smallEtaleTopology (Spec N.functionField))
        AddCommGrpCat.{u + 1}).obj A) :
    F ⟶ (directImage f).obj
      ((constantSheaf (Scheme.smallEtaleTopology N) AddCommGrpCat.{u + 1}).obj A) :=
  (inverseImageAdjunction (N.fromSpecStalk (genericPoint N) ≫ f)).homEquiv F _ b ≫
    (directImageCompIso f (N.fromSpecStalk (genericPoint N))).inv.app _ ≫
      (directImage f).map (NormalConstants.constantGenericIso N A).inv

/-- After the original finite-constant generic comparison and direct-image
composition, the extended map is exactly the supplied original generic adjoint. -/
@[reassoc]
theorem extendGenericMap_comp
    (b : (inverseImage (N.fromSpecStalk (genericPoint N) ≫ f)).obj F ⟶
      (constantSheaf (Scheme.smallEtaleTopology (Spec N.functionField))
        AddCommGrpCat.{u + 1}).obj A) :
    extendGenericMap f F A b ≫
        (directImage f).map (NormalConstants.constantGenericIso N A).hom ≫
        (directImageCompIso f (N.fromSpecStalk (genericPoint N))).hom.app _ =
      (inverseImageAdjunction (N.fromSpecStalk (genericPoint N) ≫ f)).homEquiv F _ b := by
  let e := NormalConstants.constantGenericIso N A
  let c := (directImageCompIso f (N.fromSpecStalk (genericPoint N))).app
    ((constantSheaf (Scheme.smallEtaleTopology (Spec N.functionField))
      AddCommGrpCat.{u + 1}).obj A)
  let a := (inverseImageAdjunction (N.fromSpecStalk (genericPoint N) ≫ f)).homEquiv F _ b
  change (a ≫ c.inv ≫ (directImage f).map e.inv) ≫
    (directImage f).map e.hom ≫ c.hom = a
  calc
    (a ≫ c.inv ≫ (directImage f).map e.inv) ≫
        (directImage f).map e.hom ≫ c.hom =
        a ≫ c.inv ≫ ((directImage f).map e.inv ≫ (directImage f).map e.hom) ≫ c.hom := by
      simp only [Category.assoc]
    _ = a ≫ c.inv ≫ (directImage f).map (e.inv ≫ e.hom) ≫ c.hom := by
      rw [Functor.map_comp]
    _ = a ≫ c.inv ≫ c.hom := by
      have hmap : (directImage f).map (e.inv ≫ e.hom) = 𝟙 _ :=
        (congrArg (fun k => (directImage f).map k) e.inv_hom_id).trans
          ((directImage f).map_id _)
      exact (congrArg (fun k => a ≫ c.inv ≫ k ≫ c.hom) hmap).trans
        (congrArg (fun k => a ≫ c.inv ≫ k) (Category.id_comp c.hom))
    _ = a := by rw [c.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
