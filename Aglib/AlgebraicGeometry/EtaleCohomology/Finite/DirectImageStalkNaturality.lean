/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageStalkStages

/-! # Coefficient naturality of the original direct-image stage comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  {F G : AbelianSheaf.{u, u + 1} X} (α : F ⟶ G)

/-- The actual original direct-image coefficient map agrees with the actual
coefficient map on the base-changed stage colimit. -/
@[reassoc]
theorem directImageStalkStagesIso_naturality :
    (pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber.map ((directImage f).map α).hom ≫
      (directImageStalkStagesIso R Ω f G).hom =
        (directImageStalkStagesIso R Ω f F).hom ≫
          colim.map (Functor.whiskerLeft (baseChangedEtaleDiagram R Ω f).op α.hom) := by
  apply (cancel_epi (stalkIso R Ω ((directImage f).obj F).obj).hom).mp
  apply colimit.hom_ext
  intro i
  simp only [ι_stalkIso_hom_assoc]
  let pF := (pointSmallEtale (Spec.algebraMap R Ω)).toPresheafFiber
    (etaleObject R Ω i) (stagePoint R Ω i) ((directImage f).obj F).obj
  let pG := (pointSmallEtale (Spec.algebraMap R Ω)).toPresheafFiber
    (etaleObject R Ω i) (stagePoint R Ω i) ((directImage f).obj G).obj
  let a := ((directImage f).map α).hom.app (op (etaleObject R Ω i))
  let b := (pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber.map
    ((directImage f).map α).hom
  let E := directImageStalkStagesIso R Ω f F
  let K := directImageStalkStagesIso R Ω f G
  let d := colim.map (Functor.whiskerLeft (baseChangedEtaleDiagram R Ω f).op α.hom)
  have hN : pF ≫ b = a ≫ pG :=
    (pointSmallEtale (Spec.algebraMap R Ω)).toPresheafFiber_naturality
      ((directImage f).map α).hom (etaleObject R Ω i) (stagePoint R Ω i)
  have hF := germ_directImageStalkStagesIso_hom R Ω f F i
  have hG := germ_directImageStalkStagesIso_hom R Ω f G i
  have hC : colimit.ι (directImageStageSections R Ω f F) (op (op i)) ≫ d =
      a ≫ colimit.ι (directImageStageSections R Ω f G) (op (op i)) :=
    colimit.ι_map (Functor.whiskerLeft (baseChangedEtaleDiagram R Ω f).op α.hom)
      (op (op i))
  exact (Category.assoc pF b K.hom).symm.trans
    ((congrArg (fun q => q ≫ K.hom) hN).trans
      ((Category.assoc a pG K.hom).trans
        ((congrArg (fun q => a ≫ q) hG).trans
          (hC.symm.trans ((congrArg (fun q => q ≫ d) hF.symm).trans
            (Category.assoc pF E.hom d))))))

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
