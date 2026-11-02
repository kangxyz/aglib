/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Map

/-!
# Identity laws of the original double-dual map

The two original internal-Hom identity equations imply bidual identity for
arbitrary module sheaves. Mapped reflexivity uses the given functor's identity
law. No dual-functor correspondence or second bidual construction is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u})

/-- The original double-dual map preserves the identity of every actual module
sheaf, with no regularity, coherence, rank or line-bundle premise. -/
theorem doubleDualMap_id (M : X.Modules) :
    doubleDualMap X (𝟙 M) = 𝟙 (dualSheaf X (dualSheaf X M)) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hinner : InternalHom.map X (𝟙 M) (𝟙 O) = 𝟙 (dualSheaf X M) :=
    InternalHom.map_id X
  have houter : InternalHom.map X (𝟙 (dualSheaf X M)) (𝟙 O) =
      𝟙 (dualSheaf X (dualSheaf X M)) :=
    InternalHom.map_id X
  change InternalHom.map X (InternalHom.map X (𝟙 M) (𝟙 O)) (𝟙 O) = _
  exact (congrArg
    (fun f : dualSheaf X M ⟶ dualSheaf X M => InternalHom.map X f (𝟙 O))
    hinner).trans houter

/-- Reflexive comparisons mapped by ANY actual functor into module sheaves
have their original double-dual identity; the whole equation is proved before
specialization to differential or exterior sheaves. -/
theorem doubleDualMap_map_refl {C : Type*} [Category* C]
    (F : C ⥤ X.Modules) (M : C) :
    doubleDualMap X (F.map (Iso.refl M).hom) =
      𝟙 (dualSheaf X (dualSheaf X (F.obj M))) := by
  have hmap : F.map (Iso.refl M).hom = 𝟙 (F.obj M) := F.map_id M
  exact (congrArg
    (fun f : F.obj M ⟶ F.obj M => doubleDualMap X f) hmap).trans
    (doubleDualMap_id X (F.obj M))

end AlgebraicGeometry.Scheme.Modules.Invertible
