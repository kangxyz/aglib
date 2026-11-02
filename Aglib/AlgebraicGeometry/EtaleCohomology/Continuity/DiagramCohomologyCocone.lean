/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitFunctor

/-! # The original all-degree scheme-limit comparison map

Only the comparison map and its exact cocone equations are constructed here.
No invertibility or scheme-limit continuity theorem is assumed or asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e uI vI
attribute [local instance] hasSheafifyLarge
attribute [local instance] schemeTransferLeftAdditive schemeTransferLeftLimits
  schemeTransferLeftColimits schemeTransferSourceCartesian
attribute [local instance] diagramLeftAdditive diagramLeftPreservesFiniteLimits
  diagramLeftPreservesFiniteColimits diagramIntegerCartesian

lemma cohomologyTransfer_triangle {X Y Z : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]
    (f : Y ⟶ X) (p : Z ⟶ X) (q : Z ⟶ Y) (h : q ≫ f = p)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    {H : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage q).obj G ⟶ H) (n : ℕ) :
    cohomologyTransfer f φ n ≫ cohomologyTransfer q ψ n =
      cohomologyTransfer p (triangleCoefficientMap f p q h φ ≫ ψ) n := by
  have ht := schemeIntegerSystem.extTransfer_triangle schemeAdjunctionData
    f.op p.op q.op (congrArg Quiver.Hom.op h) φ ψ n
  simp only [schemeIntegerSystem_obj, schemeIntegerSystem_extTransfer_eq_cohomologyTransfer,
    InjectiveSystem.AdjunctionData.triangleCoefficientMap,
    schemeTriangleIso_eq_pullbackTriangleIso, schemeLeft_eq_inverseImage,
    triangleCoefficientMap, Quiver.Hom.unop_op] at ht ⊢
  exact ht

section CoefficientCorrespondence

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- The actual coefficient functor has the original whole triangle-map value. -/
lemma diagramCohomologyCoefficientMap_eq {i j : I} (a : i ⟶ j) :
    (coneCoefficientFunctor X c F).map a =
      schemeAdjunctionData.triangleCoefficientMap (X.map a) (c.ι.app i) (c.ι.app j)
        (c.w a) (F.leftMap (diagramAdjunctionData X) a) := by
  change triangleCoefficientMap (X.map a).unop (c.ι.app i).unop (c.ι.app j).unop
      (congrArg Quiver.Hom.unop (c.w a)) (diagramInverseTransition X F a) = _
  dsimp only [InjectiveSystem.AdjunctionData.triangleCoefficientMap]
  rw [schemeTriangleIso_eq_pullbackTriangleIso]
  rfl

/-- The actual coefficient transition also has the literal generic transport type. -/
lemma diagramCohomologyCoefficientMap_eq_generic {i j : I} (a : i ⟶ j) :
    (coneCoefficientFunctor X c F).map a =
      eqToHom (rfl : (coneCoefficientFunctor X c F).obj i =
        (schemeAdjunctionData.left (c.ι.app i)).obj (F.obj i)) ≫
      schemeAdjunctionData.triangleCoefficientMap (X.map a) (c.ι.app i) (c.ι.app j)
        (c.w a) (F.leftMap (schemeAdjunctionData.reindex X) a) ≫
      eqToHom (rfl : (coneCoefficientFunctor X c F).obj j =
        (schemeAdjunctionData.left (c.ι.app j)).obj (F.obj j)).symm := by
  let φ : (schemeAdjunctionData.left (X.map a)).obj (F.obj i) ⟶ F.obj j :=
    F.leftMap (diagramAdjunctionData X) a
  let t : (coneCoefficientFunctor X c F).obj i ⟶ (coneCoefficientFunctor X c F).obj j :=
    schemeAdjunctionData.triangleCoefficientMap (X.map a) (c.ι.app i) (c.ι.app j)
      (c.w a) φ
  have ht : (coneCoefficientFunctor X c F).map a = t :=
    diagramCohomologyCoefficientMap_eq X c F a
  change (coneCoefficientFunctor X c F).map a =
    𝟙 ((coneCoefficientFunctor X c F).obj i) ≫ t ≫
      𝟙 ((coneCoefficientFunctor X c F).obj j)
  rw [Category.id_comp, Category.comp_id]
  exact ht

end CoefficientCorrespondence

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  (c : Cocone X) [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  (F : DiagramCoefficientSystem X) (n : ℕ)
  [HasColimit (coneCoefficientFunctor X c F)]

/-- The original stage pullback followed by its coefficient colimit injection. -/
def diagramCohomologyLeg (i : I) : diagramCohomologyObj X F n i ⟶
    AddCommGrpCat.of (Sheaf.H.{e} (colimit (coneCoefficientFunctor X c F)) n) :=
  cohomologyTransfer (X := (X.obj i).unop) (Y := c.pt.unop)
    (c.ι.app i).unop (colimit.ι (coneCoefficientFunctor X c F) i) n

/-- The original native leg is the complete generic transfer to the same coefficient colimit. -/
lemma diagramCohomologyLeg_eq_generic (i : I) :
    diagramCohomologyLeg X c F n i =
      schemeIntegerSystem.cohomologyLeg schemeAdjunctionData X c F
        (coneCoefficientFunctor X c F) (fun _ => rfl) n i := by
  symm
  change schemeIntegerSystem.extTransfer schemeAdjunctionData
    (show X.obj i ⟶ c.pt from c.ι.app i)
    (colimit.ι (coneCoefficientFunctor X c F) i) n = _
  exact schemeIntegerSystem_extTransfer_eq_cohomologyTransfer (S := X.obj i) (T := c.pt)
    (show X.obj i ⟶ c.pt from c.ι.app i) (colimit.ι (coneCoefficientFunctor X c F) i) n

lemma diagramCohomologyLeg_naturality {i j : I} (a : i ⟶ j) :
    diagramCohomologyMap X F n a ≫ diagramCohomologyLeg X c F n j =
      diagramCohomologyLeg X c F n i := by
  have hn := schemeIntegerSystem.cohomologyLeg_naturality schemeAdjunctionData X c F
    (coneCoefficientFunctor X c F) (fun _ => rfl)
    (diagramCohomologyCoefficientMap_eq_generic X c F) n a
  simp only [schemeIntegerSystem_obj, ← diagramCohomologyLeg_eq_generic] at hn ⊢
  exact hn

/-- The canonical cocone on original stage cohomology. -/
def diagramCohomologyCocone : Cocone (diagramCohomologyFunctor X F n) :=
  schemeIntegerSystem.cohomologyCocone schemeAdjunctionData X c F
    (coneCoefficientFunctor X c F) (fun _ => rfl)
    (diagramCohomologyCoefficientMap_eq_generic X c F) n
    (diagramCohomologyLeg X c F n) (diagramCohomologyLeg_eq_generic X c F n)

/-- The generic constructor stores the actual original native leg. -/
lemma diagramCohomologyCocone_ι (i : I) :
    (diagramCohomologyCocone X c F n).ι.app i = diagramCohomologyLeg X c F n i := rfl

variable [HasColimit (diagramCohomologyFunctor X F n)]

local instance genericCohomologyHasColimit :
    HasColimit (InjectiveSystem.representedCohomologyFunctor (schemeAdjunctionData.reindex X)
      (schemeIntegerSystem.reindex schemeAdjunctionData X) F n) :=
  (inferInstance : HasColimit (diagramCohomologyFunctor X F n))

/-- The literal map induced by the original pullback and coefficient injections. -/
def schemeLimitCohomologyComparison : colimit (diagramCohomologyFunctor X F n) ⟶
    AddCommGrpCat.of (Sheaf.H.{e} (colimit (coneCoefficientFunctor X c F)) n) :=
  schemeIntegerSystem.cohomologyComparison schemeAdjunctionData X c F
    (coneCoefficientFunctor X c F) (fun _ => rfl)
    (diagramCohomologyCoefficientMap_eq_generic X c F) n
    (diagramCohomologyLeg X c F n) (diagramCohomologyLeg_eq_generic X c F n)

/-- The shared construction is the literal desc of the original native cocone. -/
lemma schemeLimitCohomologyComparison_eq_desc :
    schemeLimitCohomologyComparison X c F n =
      colimit.desc _ (diagramCohomologyCocone X c F n) := rfl

@[reassoc]
lemma ι_schemeLimitCohomologyComparison (i : I) :
    colimit.ι (diagramCohomologyFunctor X F n) i ≫
        schemeLimitCohomologyComparison X c F n = diagramCohomologyLeg X c F n i :=
  schemeIntegerSystem.ι_cohomologyComparison schemeAdjunctionData X c F
    (coneCoefficientFunctor X c F) (fun _ => rfl)
    (diagramCohomologyCoefficientMap_eq_generic X c F) n
    (diagramCohomologyLeg X c F n) (diagramCohomologyLeg_eq_generic X c F n) i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
