/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model
public import Aglib.AlgebraicGeometry.Modules.Restriction.Square

/-!
# The common ambient resolution under actual open refinement

The native comparison between two iterated restrictions of the same
ambient resolution preserves its original augmentation. It is therefore
an actual morphism of the supplied injective resolutions, over the same
native coefficient restriction isomorphism.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {U V W P : Scheme.{u}} {L : P.Modules} (J : InjectiveResolution L)
  (a : W ⟶ U) (j : U ⟶ P) (c : W ⟶ V) (b : V ⟶ P)
  [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion c] [IsOpenImmersion b]
  (h : a ≫ j = c ≫ b)

/-- The original square restriction comparison on the literal common cocomplex. -/
def canonicalAmbientResolutionSquareIso :
    (canonicalAmbientChartResolution (canonicalAmbientChartResolution J j) a).cocomplex ≅
      (canonicalAmbientChartResolution (canonicalAmbientChartResolution J b) c).cocomplex :=
  (Functor.mapHomologicalComplexCompIso (restrictionSquareIso a j c b h) (.up ℕ)).app
      J.cocomplex ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictFunctor b ⋙ restrictFunctor c)) (.up ℕ)).symm.app J.cocomplex

/-- Each component is the same original coefficient restriction comparison. -/
theorem canonicalAmbientResolutionSquareIso_hom_f (k : ℕ) :
    (canonicalAmbientResolutionSquareIso J a j c b h).hom.f k =
      (restrictionSquareIso a j c b h).hom.app (J.cocomplex.X k) := by
  simp [canonicalAmbientResolutionSquareIso]

/-- The native square comparison is an actual lift of the same coefficient isomorphism. -/
def canonicalAmbientResolutionSquareLift :
    InjectiveResolution.Hom
      (canonicalAmbientChartResolution (canonicalAmbientChartResolution J j) a)
      (canonicalAmbientChartResolution (canonicalAmbientChartResolution J b) c)
      ((restrictionSquareIso a j c b h).hom.app L) where
  hom := (canonicalAmbientResolutionSquareIso J a j c b h).hom
  ι_f_zero_comp_hom_f_zero := by
    rw [canonicalAmbientResolutionSquareIso_hom_f]
    change (restrictFunctor a).map ((restrictFunctor j).map (J.ι.f 0)) ≫
      (restrictionSquareIso a j c b h).hom.app (J.cocomplex.X 0) =
      (restrictionSquareIso a j c b h).hom.app L ≫
        (restrictFunctor c).map ((restrictFunctor b).map (J.ι.f 0))
    exact (restrictionSquareIso a j c b h).hom.naturality (J.ι.f 0)

end AlgebraicGeometry.Scheme.Modules
