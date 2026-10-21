/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackNaturality

/-! # Shared compatibility of original affine-chart coordinates

This regular compatibility predicate records the original coefficient square
once, so abstract naturality suppliers and concrete chart consumers use the
same proposition head. It contains precisely the original map equality and
adds no geometric hypothesis or replacement comparison.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Z : Scheme.{u}} (p : Z ⟶ X)
  (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
  (c : Spec (CommRingCat.of S) ⟶ Z) [IsOpenImmersion c]
  (H : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ j)
  {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  {L L' : ModuleCat.{u} R}

/-- Compatibility of specified coordinates with an actual coefficient map on
both of the supplied original affine charts. -/
def chartPullbackCoordinatesCompatible (q : M ⟶ N)
    (eM : moduleSpecΓFunctor.obj (M.restrict j) ≅ L)
    (eN : moduleSpecΓFunctor.obj (N.restrict j) ≅ L') (b : L ⟶ L') : Prop :=
  moduleSpecΓFunctor.map ((restrictFunctor c).map ((pullback p).map q)) ≫
      (chartPullbackCoordinatesIso p j c H N eN).hom =
    (chartPullbackCoordinatesIso p j c H M eM).hom ≫
      (ModuleCat.extendScalarsAlgebraIso R S L).inv ≫
      (ModuleCat.extendScalars (algebraMap R S)).map b ≫
      (ModuleCat.extendScalarsAlgebraIso R S L').hom

/-- Naturality of the original source-chart coordinates gives the shared
compatibility proposition for the actual pullback coefficient map. -/
theorem chartPullbackCoordinatesCompatible_of_source_naturality (q : M ⟶ N)
    (eM : moduleSpecΓFunctor.obj (M.restrict j) ≅ L)
    (eN : moduleSpecΓFunctor.obj (N.restrict j) ≅ L') (b : L ⟶ L')
    (he : moduleSpecΓFunctor.map ((restrictFunctor j).map q) ≫ eN.hom = eM.hom ≫ b) :
    chartPullbackCoordinatesCompatible p j c H q eM eN b := by
  exact chartPullbackCoordinatesIso_naturality p j c H q eM eN b he

end AlgebraicGeometry.Scheme.Modules
