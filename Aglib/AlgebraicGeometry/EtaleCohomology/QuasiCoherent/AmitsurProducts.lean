/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Conerve
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Spectra of the original Amitsur conerve are the actual Čech powers

The native wide algebraic pushout is a coproduct because the base algebra is
initial. Applying the original `algSpec` functor gives the categorical products
in `Over (Spec R)`, with the original indexed projections and all simplicial maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The original algebraic Amitsur inclusions, viewed as an opposite product cone. -/
def amitsurTermFan (n : ℕ) :
    Fan (fun _ : Fin (n + 1) => op (CommAlgCat.of R S)) :=
  Algebra.Amitsur.termFan R S n

/-- The original wide pushout over the initial base algebra is a coproduct. -/
def amitsurTermFanIsLimit (n : ℕ) : IsLimit (amitsurTermFan R S n) :=
  Algebra.Amitsur.termFanIsLimit R S n

/-- The original spectrum factors form an actual limiting product cone over `Spec R`. -/
def amitsurSpecFanIsLimit (n : ℕ) :
    IsLimit (Fan.mk
      ((algSpec (CommRingCat.of R)).obj (op (Algebra.Amitsur.term R S n)))
      (fun i : Fin (n + 1) =>
        (algSpec (CommRingCat.of R)).map (Algebra.Amitsur.ι R S n i).op)) := by
  letI : PreservesLimitsOfSize.{0, 0} (algSpec (CommRingCat.of R)) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  exact Algebra.Amitsur.mapFanIsLimit R S (algSpec (CommRingCat.of R)) n

/-- The actual spectrum of each original conerve term is its categorical Čech power. -/
def amitsurSpecProductIso (n : ℕ) :
    (algSpec (CommRingCat.of R)).obj (op (Algebra.Amitsur.term R S n)) ≅
      ∏ᶜ fun _ : Fin (n + 1) =>
        (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) := by
  letI : PreservesLimitsOfSize.{0, 0} (algSpec (CommRingCat.of R)) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  exact Algebra.Amitsur.mapProductIso R S (algSpec (CommRingCat.of R)) n

/-- The product comparison retains every original indexed algebra factor. -/
@[reassoc (attr := simp)]
theorem amitsurSpecProductIso_hom_π (n : ℕ) (i : Fin (n + 1)) :
    (amitsurSpecProductIso R S n).hom ≫ Pi.π _ i =
      (algSpec (CommRingCat.of R)).map (Algebra.Amitsur.ι R S n i).op := by
  let : PreservesLimitsOfSize.{0, 0} (algSpec (CommRingCat.of R)) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  exact Algebra.Amitsur.mapProductIso_hom_π R S (algSpec (CommRingCat.of R)) n i

/-- The original spectrum conerve is the native product Čech nerve, including all faces. -/
def amitsurSpecCechIso :
    (Algebra.Amitsur.conerve R S).op ⋙ algSpec (CommRingCat.of R) ≅
      cechNerveTerminalFrom
        ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S))) := by
  letI : PreservesLimitsOfSize.{0, 0} (algSpec (CommRingCat.of R)) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  letI : ∀ n : ℕ, PreservesLimit (Discrete.functor
      (fun _ : Fin (n + 1) => op (CommAlgCat.of R S))) (algSpec (CommRingCat.of R)) :=
    fun _ => inferInstance
  exact Algebra.Amitsur.mapCechIso R S (algSpec (CommRingCat.of R))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
