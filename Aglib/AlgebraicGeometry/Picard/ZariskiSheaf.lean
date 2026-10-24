/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FppfSections
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Fppf
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.LocallyNoetherian

/-!
# The Zariski sheaf property of the fppf Picard sheaf

For a morphism of schemes `p : X ⟶ S`, the underlying presheaf of sets
`(fppfPicardSheaf p).obj ⋙ forget AddCommGrpCat` of `Pic_{X/S,(fppf)}` is a sheaf for the
Zariski topology on `Over S` (`isSheaf_zariskiTopology_fppfPicardSheaf_forget`), since it is an
fppf sheaf (`isSheaf_fppfPicardSheaf_forget`) and the Zariski topology is coarser. Its restriction
to locally Noetherian test schemes satisfies the Zariski sheaf hypothesis
`Scheme.LocalRepresentability.IsZariskiSheaf` of the Zariski-local representability criterion
(`isZariskiSheaf_fppfPicardSheaf_forget`), the input that `SubfunctorCover.representableByGlued`
needs to glue representing schemes of open subfunctors. This is the sheaf condition behind
Kleiman's appeal to [EGA G, (0, 4.5.4), p. 103] in the proof of Thm 4.8
(arXiv:math/0504020v1, p. 29), for the fppf form of the Picard functor on locally Noetherian
test schemes. No hypothesis on `p` is used.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- The underlying presheaf of sets of `Pic_{X/S,(fppf)}` is a sheaf for the Zariski topology on
`Over S`. -/
theorem isSheaf_zariskiTopology_fppfPicardSheaf_forget :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  isSheaf_zariskiTopology_over_of_isSheaf_fppfTopology_over (isSheaf_fppfPicardSheaf_forget p)

/-- **The Zariski sheaf hypothesis for `Pic_{X/S,(fppf)}` on locally Noetherian test schemes**:
the restriction of its underlying presheaf of sets to `Scheme.LocallyNoetherianOver S` satisfies
`Scheme.LocalRepresentability.IsZariskiSheaf`. -/
theorem isZariskiSheaf_fppfPicardSheaf_forget :
    LocalRepresentability.IsZariskiSheaf ((Scheme.locallyNoetherianOverInclusion S).op ⋙
      (fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  LocalRepresentability.isZariskiSheaf_comp_ι_of_isSheaf_fppfTopology_over
    (isSheaf_fppfPicardSheaf_forget p)

end AlgebraicGeometry.Scheme.RelativePicard
