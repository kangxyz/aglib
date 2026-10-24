/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Basic
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fppf sheaves on schemes over a base are Zariski sheaves

The Zariski topology on schemes is coarser than the fppf topology
(`Scheme.zariskiTopology_le_fppfTopology`, from Mathlib's
`Scheme.zariskiPrecoverage_le_fppfPrecoverage`: open immersions are flat and locally of finite
presentation), and so are the induced topologies on `Over S`
(`Scheme.zariskiTopology_over_le_fppfTopology_over`). Hence a presheaf on `Over S`, with values in
any universe, that is a sheaf for `Scheme.fppfTopology.over S` is a sheaf for
`Scheme.zariskiTopology.over S`
(`Scheme.isSheaf_zariskiTopology_over_of_isSheaf_fppfTopology_over`), and its restriction to the
full subcategory of an open-local property `P` (`LocalRepresentability.IsOpenLocal`, for example
locally Noetherian test schemes) satisfies the sheaf hypothesis
`LocalRepresentability.IsZariskiSheaf` of the Zariski-local representability criterion
(`LocalRepresentability.isZariskiSheaf_comp_ι_of_isSheaf_fppfTopology_over`; Stacks, Tag 01JJ,
relative to `S`). No hypothesis on `S` is used.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Scheme

/-- The Zariski topology on schemes is coarser than the fppf topology. -/
theorem zariskiTopology_le_fppfTopology : zariskiTopology.{u} ≤ fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage

/-- The Zariski topology on `Over S` is coarser than the fppf topology on `Over S`. -/
theorem zariskiTopology_over_le_fppfTopology_over (S : Scheme.{u}) :
    zariskiTopology.over S ≤ fppfTopology.over S :=
  fun T _ hR => zariskiTopology_le_fppfTopology T.left hR

/-- A sheaf for the fppf topology on `Over S` is a sheaf for the Zariski topology on `Over S`. -/
theorem isSheaf_zariskiTopology_over_of_isSheaf_fppfTopology_over {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type v} (hF : Presieve.IsSheaf (fppfTopology.over S) F) :
    Presieve.IsSheaf (zariskiTopology.over S) F :=
  Presieve.isSheaf_of_le _ (zariskiTopology_over_le_fppfTopology_over S) hF

namespace LocalRepresentability

/-- The restriction of an fppf sheaf on `Over S` to the full subcategory of an open-local property
`P` satisfies the Zariski sheaf hypothesis `IsZariskiSheaf` of the local representability
criterion. -/
theorem isZariskiSheaf_comp_ι_of_isSheaf_fppfTopology_over {S : Scheme.{u}}
    {P : ObjectProperty (Over S)} [IsOpenLocal P] {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presieve.IsSheaf (fppfTopology.over S) F) : IsZariskiSheaf (P.ι.op ⋙ F) :=
  isZariskiSheaf_comp_ι (isSheaf_zariskiTopology_over_of_isSheaf_fppfTopology_over hF)

end LocalRepresentability

end AlgebraicGeometry.Scheme
