/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.BaseChangeRestrictionEpi
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.MayerVietoris
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Restriction
public import Aglib.CategoryTheory.Adjunction.Mates.FaceEpimorphism

/-! # Original degree-zero difference epimorphism after smooth base change

The actual face equation transports an original restriction epi using only
ordinary smooth exchange. No derived open-image acyclicity or compatibility
of biproduct comparison models is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g) [Smooth g]

include H

/-- An actual overlap restriction epi gives the original Mayer–Vietoris
sum-and-difference epi, without any biproduct base-change comparison. -/
theorem sourceEtaleSquare_difference_epi (Q : Square X.Etale)
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0)
    [Epi ((sourceEtaleImageMap f Q.f₁₃).app F)] :
    Epi (sourceEtaleSquareCoefficientComplex f' (Q.map (siteBaseChange g'))
      ((inverseImage g').obj F)).g := by
  let r := (sourceEtaleImageMap f' ((siteBaseChange g').map Q.f₁₃)).app
    ((inverseImage g').obj F)
  have : Epi r := sourceEtaleImageMap_baseChange_epi f f' g g' H Q.f₁₃ F n hn hF
  have : Epi (-r) := ⟨fun u v h => (cancel_epi r).mp
    (neg_injective (by simpa only [Preadditive.neg_comp] using h))⟩
  exact epi_of_epi_fac (biprod.inr_desc
    ((sourceEtaleImageMap f' ((siteBaseChange g').map Q.f₁₂)).app
      ((inverseImage g').obj F)) (-r))

end AlgebraicGeometry.Scheme.EtaleCohomology
