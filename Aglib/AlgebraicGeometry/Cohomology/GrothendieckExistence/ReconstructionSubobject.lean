/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionPullback
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompatiblePresentation

/-! # Original maps of coherent reconstruction subobjects

This leaf constructs the original algebraic projection and completion comparison
of a coherent subobject. It makes no effectivity assertion: invertibility of
the comparison must be proved for the actual glued subobject.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H G : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (s : G.obj ⟶ reconstructionPullback α)

/-- The original target map restricted to the coherent subobject. -/
def reconstructionSubobjectTarget : G ⟶ H :=
  ObjectProperty.homMk (s ≫ reconstructionToTarget α)

/-- All original stage maps restricted to the same coherent subobject. -/
def reconstructionSubobjectStages : (Functor.const ℕᵒᵖ).obj G.obj ⟶ F.obj where
  app n := s ≫ reconstructionToStage α n
  naturality m n f := by
    change 𝟙 G.obj ≫ s ≫ reconstructionToStage α n =
      (s ≫ reconstructionToStage α m) ≫ F.obj.map f
    simp only [Category.id_comp, Category.assoc, reconstructionToStage_naturality]

/-- The unique original quotient factor of those stage maps. -/
def reconstructionSubobjectCompletionMap : (completionFunctor X K).obj G ⟶ F :=
  completionDesc K G F (reconstructionSubobjectStages α s)

/-- Every original unit followed by the completion comparison is the original
projection of the subobject, not an independently chosen formal map. -/
@[reassoc (attr := simp)]
theorem reconstructionSubobjectCompletionMap_unit (n : ℕᵒᵖ) :
    (idealSheafQuotientUnit X (K ^ n.unop)).app G.obj ≫
      (reconstructionSubobjectCompletionMap α s).hom.app n =
        s ≫ reconstructionToStage α n :=
  idealSheafQuotientUnit_desc X (K ^ n.unop) _ (F.property.annihilated n.unop)

/-- The global comparison retains the original algebraic target square. -/
theorem reconstructionSubobjectCompletionMap_comp :
    reconstructionSubobjectCompletionMap α s ≫ α =
      (completionFunctor X K).map (reconstructionSubobjectTarget α s) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  apply (cancel_epi ((idealSheafQuotientUnit X (K ^ n.unop)).app G.obj)).mp
  change _ ≫ (reconstructionSubobjectCompletionMap α s).hom.app n ≫ α.hom.app n =
    _ ≫ (idealSheafQuotientFunctor X (K ^ n.unop)).map (s ≫ reconstructionToTarget α)
  rw [← Category.assoc, reconstructionSubobjectCompletionMap_unit,
    ← (idealSheafQuotientUnit X (K ^ n.unop)).naturality]
  simp only [Functor.id_map, Category.assoc, reconstructionToStage_comp]

/-- Target and every original finite-stage projection determine a map into a
coherent reconstruction subobject. The source is an arbitrary module sheaf. -/
theorem reconstructionSubobject_hom_ext [Mono s] {M : X.Modules}
    (f g : M ⟶ G.obj)
    (ha : f ≫ (reconstructionSubobjectTarget α s).hom =
      g ≫ (reconstructionSubobjectTarget α s).hom)
    (hs : ∀ n : ℕᵒᵖ,
      f ≫ (reconstructionSubobjectStages α s).app n =
        g ≫ (reconstructionSubobjectStages α s).app n) : f = g := by
  apply (cancel_mono s).mp
  apply reconstructionPullback_hom_ext α
  · exact (Category.assoc _ _ _).trans (ha.trans (Category.assoc _ _ _).symm)
  · intro n
    exact (Category.assoc _ _ _).trans ((hs n).trans (Category.assoc _ _ _).symm)

end AlgebraicGeometry.Scheme.Modules.Coherent
