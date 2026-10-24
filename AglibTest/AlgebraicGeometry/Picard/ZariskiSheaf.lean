/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.ZariskiSheaf

/-!
# Consumer checks for the Zariski sheaf property of `Pic_{X/S,(fppf)}`

The restriction of `Pic_{X/S,(fppf)}` to locally Noetherian test schemes satisfies the sheaf
condition for every jointly surjective family of open immersions, the form consumed by
`Scheme.LocalRepresentability.SubfunctorCover.representableByGlued`; on all of `Over S` it is a
Zariski sheaf.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open Scheme.RelativePicard Scheme.LocalRepresentability

universe u

namespace AglibTest.PicardZariskiSheaf

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- The sheaf condition for a jointly surjective family of open immersions between locally
Noetherian test schemes. -/
example {T : Scheme.LocallyNoetherianOver S} {ι : Type u} (W : ι → Scheme.LocallyNoetherianOver S)
    (g : ∀ i, W i ⟶ T) (hg : ∀ i, IsOpenImmersion (g i).hom.left)
    (hcov : ∀ x : T.obj.left, ∃ i, x ∈ Set.range (g i).hom.left) :
    (Presieve.ofArrows W g).IsSheafFor ((Scheme.locallyNoetherianOverInclusion S).op ⋙
      (fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  isZariskiSheaf_fppfPicardSheaf_forget p W g hg hcov

/-- The Zariski sheaf property on all of `Over S`. -/
example : Presieve.IsSheaf (Scheme.zariskiTopology.over S)
    ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  isSheaf_zariskiTopology_fppfPicardSheaf_forget p

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isZariskiSheaf_fppfPicardSheaf_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isZariskiSheaf_fppfPicardSheaf_forget

end AglibTest.PicardZariskiSheaf
