/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootCover
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# The original Picard Kummer boundary

The map is the connecting homomorphism of the existing Kummer sequence,
precomposed with the original frame-class equivalence. No Brauer vanishing
or surjectivity of this boundary is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology.Picard
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w

/-- The actual Kummer short exact sequence, with its root-cover supplier closed. -/
theorem shortExact (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) : (sequence X n).ShortExact :=
  sequence_shortExact GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The actual connecting map in arbitrary degree, without any vanishing hypothesis. -/
def boundary (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) :
    Sheaf.H.{w} (gm X) q →+ Sheaf.H.{w} (mu X n) (q + 1) :=
  Sheaf.H.δ (shortExact X n hn hinv) q (q + 1) rfl

/-- The Kummer boundary on the existing ordinary Picard group. -/
def picardBoundary (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    PicardGroup X →+ Sheaf.H.{w} (mu X n) 2 :=
  (boundary X n hn hinv 1).comp (picardCohomologyEquiv X).toAddMonoidHom

/-- The boundary retains the original frame class and connecting homomorphism. -/
theorem picardBoundary_apply (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (c : PicardGroup X) :
    picardBoundary X n hn hinv c =
      Sheaf.H.δ (shortExact X n hn hinv) 1 2 rfl (picardCohomologyEquiv X c) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
