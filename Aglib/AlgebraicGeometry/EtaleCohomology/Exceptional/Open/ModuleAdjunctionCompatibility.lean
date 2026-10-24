/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange

/-! # Original native-to-valued adjunction compatibility -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

/-- The direct-image transport cancels by the original inverse-equivalence unit. -/
@[reassoc]
theorem moduleDirectImageTransportIso_inv_comparison (M : ModuleSheaf S Λ) :
    (moduleSheafEquivalence X Λ).inverse.map
        ((moduleDirectImageTransportIso f Λ).inv.app M) ≫
      (moduleDirectImageComparison f Λ).hom.app M =
    (moduleSheafEquivalence X Λ).unitIso.inv.app
      ((moduleValuedDirectImage f Λ).obj ((moduleSheafEquivalence S Λ).inverse.obj M)) := by
  let E := moduleSheafEquivalence X Λ
  have hk : (moduleDirectImageTransportIso f Λ).inv.app M =
      E.functor.map ((moduleDirectImageComparison f Λ).inv.app M) ≫
        E.counitIso.hom.app ((moduleDirectImage f Λ).obj M) := by
    simp [moduleDirectImageTransportIso, E]
  rw [hk, Functor.map_comp]
  change (E.inverse.map (E.functor.map _) ≫ E.inverse.map (E.counit.app _)) ≫ _ = _
  rw [← E.unitInv_app_inverse]
  have hn := E.unitIso.inv.naturality ((moduleDirectImageComparison f Λ).inv.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  change (E.inverse.map (E.functor.map _) ≫ E.unitIso.inv.app _) ≫ _ = _
  rw [hn]
  simp only [Functor.id_map, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
    ]
  exact Category.comp_id _

/-- The transported adjunction unit recovers the actual valued unit and the source unit. -/
@[reassoc]
theorem moduleTransportAdjunction_unit_comparison (M : ModuleSheaf X Λ) :
    (moduleSheafEquivalence X Λ).inverse.map ((moduleTransportAdjunction f Λ).unit.app M) ≫
      (moduleDirectImageComparison f Λ).hom.app
        ((((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ) ⋙
          (moduleSheafEquivalence S Λ).functor).obj M) =
    (moduleValuedInverseImageAdjunction f Λ).unit.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) ≫
      (moduleValuedDirectImage f Λ).map ((moduleSheafEquivalence S Λ).unitIso.hom.app
        ((moduleValuedInverseImage f Λ).obj ((moduleSheafEquivalence X Λ).inverse.obj M))) := by
  let EX := moduleSheafEquivalence X Λ
  let ES := moduleSheafEquivalence S Λ
  let L := moduleValuedInverseImage f Λ
  let R := moduleValuedDirectImage f Λ
  let η := (moduleValuedInverseImageAdjunction f Λ).unit
  change EX.inverse.map
      ((((EX.symm.toAdjunction.comp (moduleValuedInverseImageAdjunction f Λ)).comp
        ES.toAdjunction).unit.app M) ≫
        (moduleDirectImageTransportIso f Λ).inv.app
          (ES.functor.obj (L.obj (EX.inverse.obj M)))) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  have hk := moduleDirectImageTransportIso_inv_comparison f Λ
    (ES.functor.obj (L.obj (EX.inverse.obj M)))
  change EX.inverse.map _ ≫
      (EX.inverse.map ((moduleDirectImageTransportIso f Λ).inv.app
        (ES.functor.obj (L.obj (EX.inverse.obj M)))) ≫
      (moduleDirectImageComparison f Λ).hom.app
        (ES.functor.obj (L.obj (EX.inverse.obj M)))) = _
  rw [hk]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  change EX.inverse.map ((EX.counitIso.inv.app M ≫
      EX.functor.map (η.app (EX.inverse.obj M))) ≫
      EX.functor.map (R.map (ES.unitIso.hom.app (L.obj (EX.inverse.obj M))))) ≫
    EX.unitIso.inv.app (R.obj (ES.inverse.obj (ES.functor.obj
      (L.obj (EX.inverse.obj M))))) =
    η.app (EX.inverse.obj M) ≫ R.map (ES.unitIso.hom.app (L.obj (EX.inverse.obj M)))
  rw [Functor.map_comp, Functor.map_comp, ← EX.unit_app_inverse]
  change ((EX.unit.app (EX.inverse.obj M) ≫
      EX.inverse.map (EX.functor.map (η.app (EX.inverse.obj M)))) ≫
      EX.inverse.map (EX.functor.map (R.map
        (ES.unitIso.hom.app (L.obj (EX.inverse.obj M)))))) ≫
    EX.unitIso.inv.app (R.obj (ES.inverse.obj (ES.functor.obj
      (L.obj (EX.inverse.obj M))))) = _
  have hη := EX.unit_naturality (η.app (EX.inverse.obj M))
  have hu := EX.unit_naturality (R.map (ES.unitIso.hom.app (L.obj (EX.inverse.obj M))))
  simp only [Functor.comp_obj, Functor.id_obj] at hη hu
  change EX.unit.app (EX.inverse.obj M) ≫
      EX.inverse.map (EX.functor.map (η.app (EX.inverse.obj M))) =
    η.app (EX.inverse.obj M) ≫ EX.unit.app (R.obj (L.obj (EX.inverse.obj M))) at hη
  have hc := congrArg (fun a => a ≫ EX.unitIso.inv.app
    (R.obj (ES.inverse.obj (ES.functor.obj (L.obj (EX.inverse.obj M)))))) hu
  simp only [Category.assoc, Iso.hom_inv_id_app] at hc
  rw [hη]
  simp only [Category.assoc]
  rw [hc]
  exact congrArg (fun a => η.app (EX.inverse.obj M) ≫ a) (Category.comp_id _)

/-- The actual native and valued pullback units form the original adjunction square. -/
@[reassoc]
theorem moduleInverseImageValuedIso_unit (M : ModuleSheaf X Λ) :
    (moduleSheafEquivalence X Λ).inverse.map
        ((moduleInverseImageAdjunction f Λ).unit.app M) ≫
      (moduleDirectImageComparison f Λ).hom.app ((moduleInverseImage f Λ).obj M) ≫
      (moduleValuedDirectImage f Λ).map ((moduleInverseImageValuedIso Λ f).hom.app M) =
    (moduleValuedInverseImageAdjunction f Λ).unit.app
      ((moduleSheafEquivalence X Λ).inverse.obj M) := by
  have h := congrArg ((moduleSheafEquivalence X Λ).inverse.map)
    (moduleInverseImageTransportIso_unit f Λ M)
  have hn := (moduleDirectImageComparison f Λ).hom.naturality
    ((moduleInverseImageTransportIso f Λ).hom.app M)
  simp only [Functor.comp_map] at hn
  have ht := moduleTransportAdjunction_unit_comparison f Λ M
  have hh := congrArg (fun a => a ≫ (moduleDirectImageComparison f Λ).hom.app
    ((((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ) ⋙
      (moduleSheafEquivalence S Λ).functor).obj M)) h
  rw [Functor.map_comp, Category.assoc, hn, ht] at hh
  have hc := congrArg (fun a => a ≫ (moduleValuedDirectImage f Λ).map
    ((moduleSheafEquivalence S Λ).unitIso.inv.app
      ((moduleValuedInverseImage f Λ).obj ((moduleSheafEquivalence X Λ).inverse.obj M)))) hh
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    ] at hc
  erw [(moduleValuedDirectImage f Λ).map_id] at hc
  have hc' := hc.trans (Category.comp_id _)
  simpa only [moduleInverseImageValuedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Iso.symm_hom, Functor.map_comp, Functor.map_id,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
    Category.assoc] using hc'

end AlgebraicGeometry.Scheme.EtaleCohomology
