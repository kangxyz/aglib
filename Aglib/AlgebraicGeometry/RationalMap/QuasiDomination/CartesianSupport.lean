/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GraphBaseChange

/-!
# Transporting graph support to a specified cartesian open model

The canonical supported graph lift can be expressed over any actual pullback
square for the ambient open. The transport uses the square's canonical
pullback isomorphism and preserves the literal global graph-target map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {B X Y S G M : Scheme.{u}}
    (W : X.Opens) (pX : X ⟶ S) (pY : Y ⟶ S)
    (c : G ⟶ pullback pX pY) (r : G ⟶ W.toScheme)
    (hr : r ≫ W.ι = c ≫ pullback.fst pX pY) (α : B ⟶ X)
    (m : M ⟶ B) (z : M ⟶ W.toScheme) (hm : IsPullback m z α W.ι)

/-- The original support lift expressed on a specified cartesian open model. -/
def supportedGraphBaseChangeLiftOfIsPullback :
    pullback c (productBaseChangeMap α pX pY) ⟶ pullback (m ≫ α ≫ pX) pY :=
  supportedGraphBaseChangeLift W pX pY c r hr α ≫
    pullback.map (pullback.fst α W.ι ≫ α ≫ pX) pY (m ≫ α ≫ pX) pY
      hm.isoPullback.inv (𝟙 Y) (𝟙 S)
      (by simp only [Category.comp_id, ← Category.assoc, hm.isoPullback_inv_fst])
      (by simp)

@[reassoc (attr := simp)]
lemma supportedGraphBaseChangeLiftOfIsPullback_fst :
    supportedGraphBaseChangeLiftOfIsPullback W pX pY c r hr α m z hm ≫
      pullback.fst (m ≫ α ≫ pX) pY =
        supportedGraphBaseChangeToOpen W pX pY c r hr α ≫ hm.isoPullback.inv := by
  simp [supportedGraphBaseChangeLiftOfIsPullback, Category.assoc]

@[reassoc (attr := simp)]
lemma supportedGraphBaseChangeLiftOfIsPullback_snd :
    supportedGraphBaseChangeLiftOfIsPullback W pX pY c r hr α m z hm ≫
      pullback.snd (m ≫ α ≫ pX) pY =
        pullback.snd c (productBaseChangeMap α pX pY) ≫ pullback.snd (α ≫ pX) pY := by
  simp [supportedGraphBaseChangeLiftOfIsPullback, Category.assoc]

/-- The transported support factor has the same actual global target map. -/
@[reassoc (attr := simp)]
lemma supportedGraphBaseChangeLiftOfIsPullback_comp :
    supportedGraphBaseChangeLiftOfIsPullback W pX pY c r hr α m z hm ≫
      productBaseChangeMap m (α ≫ pX) pY =
        pullback.snd c (productBaseChangeMap α pX pY) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productBaseChangeMap_fst,
      supportedGraphBaseChangeLiftOfIsPullback_fst_assoc,
      hm.isoPullback_inv_fst, supportedGraphBaseChangeToOpen_fst]
  · simp only [Category.assoc, productBaseChangeMap_snd,
      supportedGraphBaseChangeLiftOfIsPullback_snd]

end AlgebraicGeometry.Scheme.QuasiDomination
