/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Map


/-!
# Naturality of the original extension to a line

Original double-dual composition and line evaluation naturality identify
extensions under source precomposition and actual maps between target lines.
No new extension or inverse-Hom map is selected.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem inverse_square {C : Type*} [Category C] {A B D E : C}
    (u : A ≅ B) (v : D ≅ E) (g : A ⟶ D) (h : B ⟶ E)
    (he : u.hom ≫ h = g ≫ v.hom) : u.inv ≫ g = h ≫ v.inv := by
  apply (cancel_epi u.hom).mp
  calc
    _ = g := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = (g ≫ v.hom) ≫ v.inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (u.hom ≫ h) ≫ v.inv := congrArg (fun q => q ≫ v.inv) he.symm
    _ = _ := Category.assoc _ _ _

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- Original double-dual maps compose using the actual internal-Hom bifunctor. -/
theorem doubleDualMap_comp (h : M ⟶ N) (k : N ⟶ P) :
    doubleDualMap X (h ≫ k) = doubleDualMap X h ≫ doubleDualMap X k := by
  let u : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hu : (𝟙 u) ≫ 𝟙 u = 𝟙 u := Category.id_comp (𝟙 u)
  have hi := (InternalHom.map_comp X k (𝟙 u) h (𝟙 u)).trans
    (congrArg (InternalHom.map X (h ≫ k)) hu)
  have ho := InternalHom.map_comp X (InternalHom.map X h (𝟙 u)) (𝟙 u)
    (InternalHom.map X k (𝟙 u)) (𝟙 u)
  exact (ho.trans ((congrArg (fun t => InternalHom.map X t ((𝟙 u) ≫ 𝟙 u)) hi).trans
    (congrArg (InternalHom.map X (InternalHom.map X (h ≫ k) (𝟙 u))) hu))).symm

/-- The same extension commutes with original source precomposition. -/
theorem extendToBidualLine_precomp (L : LineBundle X) (h : M ⟶ N) (k : N ⟶ L.val) :
    doubleDualMap X h ≫ extendToBidualLine X L k =
      extendToBidualLine X L (h ≫ k) := by
  exact (Category.assoc (doubleDualMap X h) (doubleDualMap X k) (bidualIso X L).inv).symm.trans
    (congrArg (fun q => q ≫ (bidualIso X L).inv) (doubleDualMap_comp h k).symm)

/-- The same extension commutes with an actual map between the original target lines. -/
theorem extendToBidualLine_postcomp (L L' : LineBundle X) (h : M ⟶ L.val)
    (g : L.val ⟶ L'.val) :
    extendToBidualLine X L h ≫ g = extendToBidualLine X L' (h ≫ g) := by
  have hi := inverse_square (bidualIso X L) (bidualIso X L') g
    (doubleDualMap X g) (bidualMap_naturality X g)
  exact (Category.assoc (doubleDualMap X h) (bidualIso X L).inv g).trans
    ((congrArg (fun q => doubleDualMap X h ≫ q) hi).trans
      ((Category.assoc (doubleDualMap X h) (doubleDualMap X g) (bidualIso X L').inv).symm.trans
        (congrArg (fun q => q ≫ (bidualIso X L').inv) (doubleDualMap_comp h g).symm)))

end AlgebraicGeometry.Scheme.Modules.Invertible
