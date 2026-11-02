/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageAssociativity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionCoherence

/-! # Associativity on the original native torsion inverse images -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wT wV
variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original torsion inverse-image compositors associate, by the faithful native
full-subcategory inclusion. The source and all three target models remain independent. -/
theorem moduleDerivedInverseImageTorsionCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)] :
    Functor.CompositionAssociates
      (eqToIso (congrArg (fun k : V ⟶ X => moduleDerivedInverseImageTorsion k Λ)
        (Category.assoc h g f)))
      (moduleDerivedInverseImageTorsionCompIso Λ f (h ≫ g))
      (moduleDerivedInverseImageTorsionCompIso Λ g h)
      (moduleDerivedInverseImageTorsionCompIso Λ (g ≫ f) h)
      (moduleDerivedInverseImageTorsionCompIso Λ f g) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  have hc := congrArg (fun i => i.hom.app K.obj)
    (moduleDerivedInverseImageCompIso_assoc Λ f g h)
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, moduleDerivedInverseImageTorsionCompIso_hom_app,
    moduleDerivedInverseImageTorsion_map, eqToIso.hom, eqToHom_app,
    ObjectProperty.eqToHom_hom] at hc ⊢
  exact hc

end AlgebraicGeometry.Scheme.EtaleCohomology
