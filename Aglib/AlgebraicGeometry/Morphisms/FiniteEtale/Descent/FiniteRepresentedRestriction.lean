/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTorsorRepresentation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! The actual represented set sheaf commutes with restriction to etale charts. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u
variable {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] (Y : Scheme.FiniteEtale X)

/-- The pullback universal property identifies the represented sections on
every etale test scheme, with the existing explicit universe lift. -/
def finiteRepresentedRestrictionIso :
    (Scheme.EtaleCohomology.setEtaleRestriction f).obj
      (Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y) ≅
      Scheme.EtaleCohomology.finiteRepresentedSetSheaf ((baseChange f).obj Y) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => ((Equiv.ulift.trans ((Over.mapPullbackAdj f).homEquiv
      ((Scheme.Etale.forget S).obj U.unop) Y.obj)).trans Equiv.ulift.symm).toIso)
    (fun {U V} g => by
      ext s
      apply ULift.ext
      exact (Over.mapPullbackAdj f).homEquiv_naturality_left
        ((Scheme.Etale.forget S).map g.unop) s.down))

/-- Genuine inverse image, not just a change in the section-set notation. -/
def finiteRepresentedInverseImageIso :
    (Scheme.EtaleCohomology.setInverseImage f).obj
      (Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y) ≅
      Scheme.EtaleCohomology.finiteRepresentedSetSheaf ((baseChange f).obj Y) :=
  (Scheme.EtaleCohomology.setInverseImageEtaleIso f).app
    (Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y) ≪≫
    finiteRepresentedRestrictionIso f Y

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 40f0163532877614227b67108af4558ec20e6657ad87faa56d3abd7f5b1f5754.
Definitions, hypotheses and universes are retained modulo native names. -/
