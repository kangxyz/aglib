/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Rank

/-! Original cohomology, coefficient maps, level one and genus zero. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Curves
open GroupCohomology.Kummer.Coefficients

universe u w

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

example : Nat.card (Sheaf.H.{w} (mu X.left 1) 1) = 1 := by
  exact (card_rootsOne hX 1 (by decide)
    (by simpa only [Nat.cast_one] using (isUnit_one : IsUnit (1 : k)))).trans (one_pow _)

example (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := rootsOneZModModule (X := X) n
    Nonempty (Module.Basis (Fin (2 * coherentGenus k X)) (ZMod n)
      (Sheaf.H.{w} (mu X.left n) 1)) :=
  ⟨rootsOneBasis hX n hn hunit⟩

example (hg : coherentGenus k X = 0) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := constantOneZModModule (X := X) n
    Nonempty (Module.Basis (Fin 0) (ZMod n)
      (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 1)) := by
  let := constantOneZModModule (X := X) n
  have b := constantOneBasis hX n hn hunit
  rw [hg, Nat.mul_zero] at b
  exact ⟨b⟩

example (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    (constantOneRankAddEquiv hX n hn hunit).toAddMonoidHom =
      (rootsOneRankAddEquiv hX n hn hunit).toAddMonoidHom.comp
        (Sheaf.H.map (constantRootIso (X := X) n hn hunit).hom 1) :=
  constantOneRankAddEquiv_coefficientMap hX n hn hunit

end
