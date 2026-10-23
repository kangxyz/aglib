/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks

/-! # Original all-degree cohomology of a compatible coefficient system -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  (F : DiagramCoefficientSystem X) (n : ℕ)

/-- The native stage cohomology group in the independent Ext universe. -/
abbrev diagramCohomologyObj (i : I) : AddCommGrpCat.{e} :=
  AddCommGrpCat.of (Sheaf.H.{e} (F.obj i) n)

/-- The original stage pullback followed by its compatible coefficient morphism. -/
def diagramCohomologyMap {i j : I} (a : i ⟶ j) :
    diagramCohomologyObj X F n i ⟶ diagramCohomologyObj X F n j :=
  cohomologyTransfer (X.map a).unop (diagramInverseTransition X F a) n

lemma diagramCohomologyMap_id (i : I) : diagramCohomologyMap X F n (𝟙 i) = 𝟙 _ := by
  dsimp only [diagramCohomologyMap]
  rw [diagramInverseTransition_id]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  exact (cohomologyTransfer_transport (𝟙 _) (X.map (𝟙 i)).unop
    (congrArg (fun f : X.obj i ⟶ X.obj i => f.unop) (X.map_id i))
    ((inverseImageId (X.obj i).unop).hom.app (F.obj i)) n).trans
      (cohomologyTransfer_id (F.obj i) n)

lemma diagramCohomologyMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramCohomologyMap X F n (a ≫ b) =
      diagramCohomologyMap X F n a ≫ diagramCohomologyMap X F n b := by
  dsimp only [diagramCohomologyMap]
  rw [diagramInverseTransition_comp]
  simp only [diagramInverseImageComp, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  let φ : (inverseImage ((X.map b).unop ≫ (X.map a).unop)).obj (F.obj i) ⟶ F.obj k :=
    (inverseImageComp (X.map a).unop (X.map b).unop).hom.app (F.obj i) ≫
      (inverseImage (X.map b).unop).map (diagramInverseTransition X F a) ≫
        diagramInverseTransition X F b
  have ht := cohomologyTransfer_transport ((X.map b).unop ≫ (X.map a).unop)
    (X.map (a ≫ b)).unop
    (congrArg (fun f : X.obj i ⟶ X.obj k => f.unop) (X.map_comp a b)) φ n
  exact ht.trans (cohomologyTransfer_comp (X.map a).unop (X.map b).unop
    (diagramInverseTransition X F a) (diagramInverseTransition X F b) n).symm

/-- The actual all-degree source diagram, without assuming continuity. -/
def diagramCohomologyFunctor : I ⥤ AddCommGrpCat.{e} where
  obj := diagramCohomologyObj X F n
  map := diagramCohomologyMap X F n
  map_id := diagramCohomologyMap_id X F n
  map_comp := diagramCohomologyMap_comp X F n

variable {F} {G : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F G)

/-- A morphism of actual systems induces the original cohomological coefficient maps. -/
def diagramCohomologyNatTrans : diagramCohomologyFunctor X F n ⟶
    diagramCohomologyFunctor X G n where
  app i := AddCommGrpCat.ofHom (Sheaf.H.map (η.app i) n)
  naturality _ _ a := cohomologyTransfer_naturality (X.map a).unop
    (diagramInverseTransition X F a) (diagramInverseTransition X G a)
    (η.app _) (η.app _) (diagramInverseTransition_naturality X η a) n

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
