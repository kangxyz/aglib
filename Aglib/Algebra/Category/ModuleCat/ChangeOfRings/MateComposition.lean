/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Whole scalar adjoints of original composites

The existing scalar comparison is transposed by the existing adjunctions.
No tensor element or alternative scalar action is introduced.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory

namespace ModuleCat

/-- The scalar adjoint of the original two-step composite is the composite of
its original scalar adjoints and restriction comparison. -/
theorem homEquiv_extendScalarsComp_map_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    {P : ModuleCat.{u} R} {Q : ModuleCat.{u} S} {N : ModuleCat.{u} T}
    (t : (extendScalars f).obj P ⟶ Q) (s : (extendScalars g).obj Q ⟶ N) :
    (extendRestrictScalarsAdj (g.comp f)).homEquiv P N
      ((extendScalarsComp f g).hom.app P ≫
        CategoryTheory.Functor.map (extendScalars g) t ≫ s) =
      (extendRestrictScalarsAdj f).homEquiv P Q t ≫
        (restrictScalars f).map ((extendRestrictScalarsAdj g).homEquiv Q N s) ≫
        (restrictScalarsComp f g).inv.app N := by
  let k := CategoryTheory.Functor.map (extendScalars g) t ≫ s
  have hn := (restrictScalarsComp f g).inv.naturality k
  change (restrictScalars f).map ((restrictScalars g).map k) ≫
      (restrictScalarsComp f g).inv.app N =
    (restrictScalarsComp f g).inv.app ((extendScalars g).obj ((extendScalars f).obj P)) ≫
      (restrictScalars (g.comp f)).map k at hn
  let ηf : P ⟶ (restrictScalars f).obj ((extendScalars f).obj P) :=
    (extendRestrictScalarsAdj f).unit.app P
  let ηgP : (extendScalars f).obj P ⟶
      (restrictScalars g).obj ((extendScalars g).obj ((extendScalars f).obj P)) :=
    (extendRestrictScalarsAdj g).unit.app ((extendScalars f).obj P)
  let ηgQ : Q ⟶ (restrictScalars g).obj ((extendScalars g).obj Q) :=
    (extendRestrictScalarsAdj g).unit.app Q
  have hg : t ≫ ηgQ = ηgP ≫ (restrictScalars g).map ((extendScalars g).map t) :=
    (extendRestrictScalarsAdj g).unit.naturality t
  have hu := congrArg (CategoryTheory.Functor.map (restrictScalars f)) hg
  simp only [Functor.map_comp] at hu
  have ht : (extendRestrictScalarsAdj f).homEquiv P Q t =
      ηf ≫ (restrictScalars f).map t :=
    (extendRestrictScalarsAdj f).homEquiv_unit P Q t
  have hs' : (extendRestrictScalarsAdj g).homEquiv Q N s =
      ηgQ ≫ (restrictScalars g).map s :=
    (extendRestrictScalarsAdj g).homEquiv_unit Q N s
  have hc : (extendRestrictScalarsAdj (g.comp f)).homEquiv P _
      ((extendScalarsComp f g).hom.app P) =
      ηf ≫ (restrictScalars f).map ηgP ≫
        (restrictScalarsComp f g).inv.app ((extendScalars g).obj ((extendScalars f).obj P)) :=
    homEquiv_extendScalarsComp f g P
  have hs : ηf ≫ (restrictScalars f).map ηgP ≫
        (restrictScalars f).map ((restrictScalars g).map k) =
      (extendRestrictScalarsAdj f).homEquiv P Q t ≫
        (restrictScalars f).map ((extendRestrictScalarsAdj g).homEquiv Q N s) := by
    rw [ht, hs']
    simpa only [k, Functor.map_comp, Category.assoc] using
      congrArg (fun z => ηf ≫ z ≫
        (restrictScalars f).map ((restrictScalars g).map s)) hu.symm
  calc
    _ = (extendRestrictScalarsAdj (g.comp f)).homEquiv P _
        ((extendScalarsComp f g).hom.app P) ≫ (restrictScalars (g.comp f)).map k :=
      (extendRestrictScalarsAdj (g.comp f)).homEquiv_naturality_right _ _
    _ = ηf ≫ (restrictScalars f).map ηgP ≫
        (restrictScalarsComp f g).inv.app ((extendScalars g).obj ((extendScalars f).obj P)) ≫
        (restrictScalars (g.comp f)).map k := by
      rw [hc, Category.assoc, Category.assoc]
    _ = ηf ≫ (restrictScalars f).map ηgP ≫
        (restrictScalars f).map ((restrictScalars g).map k) ≫
        (restrictScalarsComp f g).inv.app N := by
      simpa only [Category.assoc] using
        congrArg (fun z => ηf ≫ (restrictScalars f).map ηgP ≫ z) hn.symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ (restrictScalarsComp f g).inv.app N) hs

end ModuleCat
