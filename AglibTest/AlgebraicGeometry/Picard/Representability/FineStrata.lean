/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Representability.FineStrata

/-!
# Consumer checks for the representability of the fppf Picard functor, unconditionally

The two premises on the fine strata hold, so the Picard scheme `picardScheme h` exists with no
further hypothesis, and Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8, pp. 27–31
(fppf form on locally Noetherian test schemes over a Noetherian affine base) holds as stated, with
axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata

universe u

namespace AglibTest.PicardRepresentabilityFineStrata

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} (e : ι ≃ Fin (N + 1))

/-- The Picard scheme with its premises discharged: separated, locally of finite type, and with
H-quasi-projective levels `Pic^φ_m`. -/
example (φ : Polynomial ℚ) (m : ℤ) :
    IsSeparated (picardScheme (fineStrataRepresentableByHQuasiProjective i e)).obj.hom ∧
      LocallyOfFiniteType (picardScheme (fineStrataRepresentableByHQuasiProjective i e)).obj.hom ∧
      IsHQuasiProjective ((picardLevelOpens (fineStrataRepresentableByHQuasiProjective i e) φ m).ι ≫
        (picardScheme (fineStrataRepresentableByHQuasiProjective i e)).obj.hom) :=
  ⟨inferInstance, inferInstance,
    isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks _ (finiteFineStrataRanks i e) φ m⟩

/-- The unconditional statement implies representability by a separated scheme. -/
example : ∃ (P : Scheme.LocallyNoetherianOver (Spec (.of A)))
      (_ : ((Scheme.locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P),
      IsSeparated P.obj.hom := by
  obtain ⟨P, R, -, -, hsep, -⟩ := exists_representableBy_fppfPicardSheaf i e
  exact ⟨P, R, hsep⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_representableBy_fppfPicardSheaf

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fineStrataRepresentableByHQuasiProjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fineStrataRepresentableByHQuasiProjective

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.finiteFineStrataRanks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finiteFineStrataRanks

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.nonempty_of_holds_of_representableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.nonempty_of_holds_of_representableBy

end AglibTest.PicardRepresentabilityFineStrata
