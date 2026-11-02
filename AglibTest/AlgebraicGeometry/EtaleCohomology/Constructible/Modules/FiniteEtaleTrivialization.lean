/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleTrivialization

/-! Actual global finite covers and original module isomorphisms at positive levels. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- The lifted coefficient retains its actual finite étale cover, original
ring, module value and module-valued inverse-image isomorphism. -/
example (n : ℕ) (hn : 0 < n)
    (F : ModuleSheaf (ULift.{u + 1} (ZMod n)) X) (hF : IsFiniteTypeLocallyConstant F) :
    ∃ Y : Scheme.FiniteEtale X,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∃ M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)),
        Module.Finite (ULift.{u + 1} (ZMod n)) M ∧
        Nonempty ((moduleInverseImage (ULift.{u + 1} (ZMod n)) Y.obj.hom).obj F ≅
          (constantSheaf Y.obj.left.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))).obj M) := by
  let T := uLiftZModGaloisCoverConstantTrivialization n hn F hF
  exact ⟨T.cover, T.galois_cover, T.connected_cover, T.surjective_cover,
    T.value, T.finite_value, ⟨T.iso⟩⟩

/-- Composite and zero-ring levels use the same intrinsic existence construction. -/
example (F : ModuleSheaf (ZMod 6) X) (hF : IsFiniteTypeLocallyConstant F) :
    GaloisCoverConstantTrivialization F :=
  zmodGaloisCoverConstantTrivialization 6 (by decide) F hF

example (F : ModuleSheaf (ULift.{u + 1} (ZMod 1)) X)
    (hF : IsFiniteTypeLocallyConstant F) : GaloisCoverConstantTrivialization F :=
  uLiftZModGaloisCoverConstantTrivialization 1 (by decide) F hF

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.nonempty_galoisCoverConstantTrivialization' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.nonempty_galoisCoverConstantTrivialization

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.uLiftZModGaloisCoverConstantTrivialization' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.uLiftZModGaloisCoverConstantTrivialization
