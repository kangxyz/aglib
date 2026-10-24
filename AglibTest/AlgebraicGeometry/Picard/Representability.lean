/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Representability

/-!
# Consumer checks for the representability of the fppf Picard functor

The collected statement of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8,
pp. 27–31 (fppf form on locally Noetherian test schemes over a Noetherian affine base), under the
representability of the fine strata and the finiteness of their ranks, with an axiom guard.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata

universe u

namespace AglibTest.PicardRepresentability

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}

/-- The fppf Picard functor on locally Noetherian test schemes is representable by a separated
scheme locally of finite type, with H-quasi-projective levels. -/
example (h : FineStrataRepresentableByHQuasiProjective i N e)
    (hrank : FiniteFineStrataRanks i N e) :
    ∃ (P : Scheme.LocallyNoetherianOver (Spec (.of A)))
      (_ : ((Scheme.locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (level : Polynomial ℚ → ℤ → P.obj.left.Opens),
      IsSeparated P.obj.hom ∧ LocallyOfFiniteType P.obj.hom ∧
        ∀ φ m, IsHQuasiProjective ((level φ m).ι ≫ P.obj.hom) := by
  obtain ⟨P, R, -, level, hsep, hlft, -, -, -, -, -, hqp, -⟩ :=
    exists_representableBy_fppfPicardSheaf_of_fineStrata h hrank
  exact ⟨P, R, level, hsep, hlft, hqp⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_of_fineStrata' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_representableBy_fppfPicardSheaf_of_fineStrata

end AglibTest.PicardRepresentability
