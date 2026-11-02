/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.IsomorphismSheaf.Inverse

/-! Native consumers of whole isomorphism-sheaf inversion and scalar inversion. -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped MonoidalCategory
open AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent

universe u
variable {X : Scheme.{u}} (L M N : lineBundles.obj (.mk (op X)))
  (h : EtaleLineBundleDescent.{u})

example : isoSheafInverse L M h ≪≫ isoSheafInverse M L h = Iso.refl _ :=
  isoSheafInverse_twice L M h

example : isoSheafComposition L M N h ≫ (isoSheafInverse L N h).hom =
    ((isoSheafInverse L M h).hom ⊗ₘ (isoSheafInverse M N h).hom) ≫
      (β_ (isoSheaf M L h) (isoSheaf N M h)).hom ≫ isoSheafComposition N M L h :=
  isoSheafComposition_inverse L M N h

example {P Q : X.Modules} (φ : P ≅ Q) (a : Γ(X, ⊤)ˣ) :
    (φ ≪≫ Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X Q a).symm =
      φ.symm ≪≫ Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X P a⁻¹ :=
  Scheme.Modules.Invertible.ScalarAutomorphisms.inverse_scalarIso X φ a

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.isoSheafComposition_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isoSheafComposition_inverse
