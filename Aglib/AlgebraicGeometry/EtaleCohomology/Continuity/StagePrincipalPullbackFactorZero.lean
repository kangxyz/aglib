/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StagePrincipalPullbackZero

/-! # Principal-open zero through the original factorization equations

The structural and target factorizations are used before specializing the
family. The literal principal pullback and original class are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalization.PrincipalDiagram

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u eT

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- An original stage-open zero descends through the supplied structural and
 target factorization equations on the same principal pullback. -/
theorem principalPullback_factor_zero_of_stageOpen_zero
    {S : Type u} [CommRing S] (D : Submonoid S) (t : Finset D)
    {Y Z W T : Scheme.{u}} [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
    (b : Y ⟶ Spec (.of S)) (h : Y ⟶ T)
    (M : AbelianSheaf.{u, u + 1} T) (q : ℕ) (c : Sheaf.H.{eT} M q)
    (v : Z ⟶ Y) (b' : Z ⟶ Spec (.of S)) (w : Z ⟶ W) (a : W ⟶ T)
    (hb : v ≫ b = b') (hh : v ≫ h = w ≫ a)
    (hc : cohomologyPullback.{u, eT, u + 2}
      ((PrincipalNeighborhoodLimit.stageSourceOpen D b t).ι ≫ h) M q c = 0) :
    cohomologyPullback.{u, eT, u + 2}
      ((pullback.snd (principalSupportOpen S (denominator D t)).ι b' ≫ w) ≫ a)
      M q c = 0 := by
  subst b'
  have hz := principalPullback_precomp_zero_of_stageOpen_zero D t b h M q c v hc
  have hm :
      (pullback.snd (principalSupportOpen S (denominator D t)).ι (v ≫ b) ≫ v) ≫ h =
        (pullback.snd (principalSupportOpen S (denominator D t)).ι (v ≫ b) ≫ w) ≫ a := by
    simp only [Category.assoc, hh]
  rw [hm] at hz
  exact hz

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
