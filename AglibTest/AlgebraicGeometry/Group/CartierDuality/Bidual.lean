/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Bidual

/-! The native bidual comparison stays on the original group and its actual dual objects. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.Group.CartierDuality
open scoped Module.Dual.FiniteDual

universe u

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]

example : G ≅ dualGroup (dualGroup G) := bidualIso G

example : (bidualIso G).hom ≫ (bidualIso G).inv = 𝟙 G := (bidualIso G).hom_inv_id

example {H : Grp (FScheme k)} [IsFinite H.X.hom] [IsCommMonObj H.X] (f : G ⟶ H) :
    (dualCoordinateIso G).hom ≫ coordinateMap (dualMap f) =
      CommHopfAlgCat.ofHom (coordinateMap f).hom.dual ≫ (dualCoordinateIso H).hom :=
  dualCoordinateIso_naturality f

example {H : Grp (FScheme k)} [IsFinite H.X.hom] [IsCommMonObj H.X] (f : G ⟶ H) :
    f ≫ (bidualIso H).hom = (bidualIso G).hom ≫ dualMap (dualMap f) :=
  bidualIso_naturality f

example : dualMap (bidualIso G).hom = (bidualIso (dualGroup G)).inv :=
  dualMap_bidualIso_hom G
