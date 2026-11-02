/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsComposition
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.SquareComparison

/-!
# Roots on an original commutative inverse-image square

The original roots comparison respects the original composition and equality
transport of inverse image. Only commutativity of the scheme square is needed;
this statement is not a right-direct-image base-change assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

namespace GroupCohomology.Kummer.CoefficientBaseChange

universe u

variable {Y X V U : Scheme.{u}}
  (p : Y ⟶ X) (f : V ⟶ U) (jU : U ⟶ X) (jV : V ⟶ Y)
  (h : f ≫ jU = jV ≫ p) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The whole roots coefficient map respects the original inverse-image square,
without a Cartesian, flatness or étaleness hypothesis on its scheme arrows. -/
theorem rootsPullbackIso_square :
    (inverseImageSquareIso p f jU jV h).hom.app (mu X n) ≫
        (inverseImage jV).map (rootsPullbackIso p n hn hinv).hom ≫
        (rootsPullbackIso jV n hn (levelInvertible p n hinv)).hom =
      (inverseImage f).map (rootsPullbackIso jU n hn hinv).hom ≫
        (rootsPullbackIso f n hn (levelInvertible jU n hinv)).hom := by
  apply (cancel_epi ((inverseImageComp jU f).hom.app (mu X n))).mp
  have hs := NatTrans.congr_app (inverseImageSquareIso_comp_hom p f jU jV h) (mu X n)
  simp only [NatTrans.comp_app, eqToHom_app] at hs
  rw [← Category.assoc ((inverseImageComp jU f).hom.app (mu X n))
      ((inverseImageSquareIso p f jU jV h).hom.app (mu X n)), hs]
  simp only [Category.assoc]
  rw [rootsPullbackIso_comp, rootsPullbackIso_eqToHom h, rootsPullbackIso_comp]

/-- The same whole square with inverse open-coefficient transports, in the
orientation used by the original lower-shriek counits. -/
theorem rootsPullbackIso_square_inv :
    (inverseImage f).map (rootsPullbackIso jU n hn hinv).inv ≫
        (inverseImageSquareIso p f jU jV h).hom.app (mu X n) ≫
        (inverseImage jV).map (rootsPullbackIso p n hn hinv).hom =
      (rootsPullbackIso f n hn (levelInvertible jU n hinv)).hom ≫
        (rootsPullbackIso jV n hn (levelInvertible p n hinv)).inv := by
  apply (cancel_epi ((inverseImage f).map (rootsPullbackIso jU n hn hinv).hom)).mp
  simp only [← (inverseImage f).map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_mono (rootsPullbackIso jV n hn (levelInvertible p n hinv)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact rootsPullbackIso_square p f jU jV h n hn hinv

end GroupCohomology.Kummer.CoefficientBaseChange
