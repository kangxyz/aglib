/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramRelativeTail
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeComparison

/-! # Identification of the actual coefficient tail with original relative sections -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (i : I)

lemma relativeTailSectionsMap_eq {a b : Under i} (m : a ⟶ b) :
    (SchemeSystemColimits.tailToArrow i ⋙ arrowSectionsFunctor X F).map m =
      (relativeSchemeTail X i ⋙ pullbackSectionsFunctor (F.obj i)).map m := by
  change squareSectionsMap (X.map a.hom).unop (X.map b.hom).unop
    (X.map (𝟙 i)).unop (X.map m.right).unop _
    (diagramInverseTransition X F (𝟙 i)) =
      pullbackSectionsMap (F.obj i) ((relativeSchemeTail X i).map m).unop
  rw [diagramInverseTransition_id]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  let q := ((relativeSchemeTail X i).map m).unop
  have ht := squareSectionsMap_transport (X.map a.hom).unop (X.map b.hom).unop
    (𝟙 _) (X.map (𝟙 i)).unop (X.map m.right).unop (X.map m.right).unop
    (congrArg (fun k : X.obj i ⟶ X.obj i => k.unop) (X.map_id i)) rfl
    ((Category.comp_id (X.map b.hom).unop).trans q.w.symm)
    (arrowSectionsSquare X ((SchemeSystemColimits.tailToArrow i).map m))
    ((inverseImageId (X.obj i).unop).hom.app (F.obj i))
  exact ht.trans (squareSectionsMap_base_id (F.obj i) q)

/-- Identity on objects, with the original relative pullback maps on morphisms. -/
def relativeTailSectionsIso :
    SchemeSystemColimits.tailToArrow i ⋙ arrowSectionsFunctor X F ≅
      relativeSchemeTail X i ⋙ pullbackSectionsFunctor (F.obj i) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {a b} m => by
    let d : arrowSectionsObj X F (Arrow.mk a.hom) ⟶ arrowSectionsObj X F (Arrow.mk b.hom) :=
      (SchemeSystemColimits.tailToArrow i ⋙ arrowSectionsFunctor X F).map m
    let s : arrowSectionsObj X F (Arrow.mk a.hom) ⟶ arrowSectionsObj X F (Arrow.mk b.hom) :=
      (relativeSchemeTail X i ⋙ pullbackSectionsFunctor (F.obj i)).map m
    have h : d = s := relativeTailSectionsMap_eq X F i m
    exact (Category.comp_id d).trans (h.trans (Category.id_comp s).symm))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
