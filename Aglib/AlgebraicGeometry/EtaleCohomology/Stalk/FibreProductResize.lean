/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductPresheaf

/-! # The original fibre-product resize with fixed cohomology universe

These are the existing `Shrink.addEquiv` and original resize restriction law,
instantiated on the native fibre-product cohomology diagram. No new diagram,
coefficient, cohomology model or smallness assumption is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
      ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
    [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The actual canonical equivalence from the native resized group to original cohomology. -/
def fibreProductResizeEquiv (U : S.Etale) :
    (smallFibreProductCohomologyPresheaf.{u, w, s, e} p F q).obj (op U) ≃+
      Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj F) q := by
  let : Small.{u + 1}
      (Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj F) q) :=
    fibreProductCohomology_small.{u, w, s, e} p F q U
  exact (Shrink.addEquiv.{u + 1}
    (α := Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj F) q))

/-- The same canonical equivalences commute with the original restriction maps. -/
theorem fibreProductResizeEquiv_restriction {U V : S.Etale} (a : V ⟶ U)
    (c : (smallFibreProductCohomologyPresheaf.{u, w, s, e} p F q).obj (op U)) :
    fibreProductResizeEquiv.{u, w, s, e} p F q V
      ((smallFibreProductCohomologyPresheaf.{u, w, s, e} p F q).map a.op c) =
      fibreProductCohomologyRestriction.{u, e, e} p a F q
        (fibreProductResizeEquiv.{u, w, s, e} p F q U c) := by
  change fibreProductResizeEquiv.{u, w, s, e} p F q V
      ((fibreProductResizeEquiv.{u, w, s, e} p F q V).symm
        (fibreProductCohomologyRestriction.{u, e, e} p a F q
          (fibreProductResizeEquiv.{u, w, s, e} p F q U c))) = _
  exact (fibreProductResizeEquiv.{u, w, s, e} p F q V).apply_symm_apply _

end AlgebraicGeometry.Scheme.EtaleCohomology
