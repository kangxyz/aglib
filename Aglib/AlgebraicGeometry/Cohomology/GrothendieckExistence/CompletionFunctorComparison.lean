/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompletionNaturality

/-! # Functorial comparison of original quotient diagrams and native completion -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (α : A →+* Γ(X, ⊤)) (I : Ideal A)

/-- Every original coefficient morphism induces its original quotient-tower morphism. -/
def idealPowerQuotientTowerHom {F G : X.Modules} (g : F ⟶ G) :
    idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I where
  app n := idealQuotientHom X α (I ^ n.unop) g
  naturality _ _ h :=
    (idealQuotientHom_map X α (Ideal.pow_le_pow_right (leOfHom h.unop)) g).symm

/-- The original coefficient quotient diagrams, functorial in the actual coefficient. -/
def idealPowerQuotientDiagramFunctor : X.Modules ⥤ (ℕᵒᵖ ⥤ X.Modules) where
  obj F := idealPowerQuotientFunctor X α F I
  map g := idealPowerQuotientTowerHom X α I g
  map_id F := by
    apply NatTrans.ext
    funext n
    exact idealQuotientHom_id X α (I ^ n.unop) F
  map_comp g h := by
    apply NatTrans.ext
    funext n
    exact idealQuotientHom_comp X α (I ^ n.unop) g h

variable {X} (f : X ⟶ Spec (CommRingCat.of A))

/-- Coefficient naturality on the full original inverse diagrams. -/
@[reassoc]
theorem idealPowerQuotientTowerHom_comparison {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (g : F ⟶ G) :
    idealPowerQuotientTowerHom X (idealThickeningBaseScalar f) I g ≫
      (idealPowerQuotientIdealSheafTowerIso f I G).hom =
    (idealPowerQuotientIdealSheafTowerIso f I F).hom ≫
      idealSheafQuotientTowerHom X (idealThickeningIdealSheaf f I) g := by
  apply NatTrans.ext
  funext n
  exact idealPowerQuotientIdealSheafIso_naturality f I g n.unop

variable [IsLocallyNoetherian X]

local instance completionComparisonCoefficient_isQuasicoherent (F : X.CoherentSheaf) :
    F.obj.IsQuasicoherent :=
  quasicoherent_of_affineCharts _ (fun R j _ => (F.property R j).1)

/-- The original ideal-power completion of coherent coefficients into native diagrams. -/
def idealPowerCompletionToDiagram : X.CoherentSheaf ⥤ (ℕᵒᵖ ⥤ X.Modules) :=
  ObjectProperty.ι (affineLocallyFiniteType X) ⋙
    idealPowerQuotientDiagramFunctor X (idealThickeningBaseScalar f) I

/-- The original quotient-tower functor and the native coherent completion agree
naturally in every original coefficient morphism. -/
def idealPowerCompletionComparison :
    idealPowerCompletionToDiagram I f ≅
      completionFunctor X (idealThickeningIdealSheaf f I) ⋙
        adicSystemToDiagram X (idealThickeningIdealSheaf f I) :=
  NatIso.ofComponents (fun F => idealPowerQuotientIdealSheafTowerIso f I F.obj) (by
    intro F G g
    exact idealPowerQuotientTowerHom_comparison I f g.hom)

end AlgebraicGeometry.Scheme.Cohomology
