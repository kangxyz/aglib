/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Grassmannian.QuasiProjective
public import Aglib.AlgebraicGeometry.HilbertScheme.QuasiProjective

/-!
# The Grassmannian is projective and the Hilbert scheme quasi-projective

The declarations below restate that the Grassmannian `Gr(R^n, k)` is H-projective over `Spec R`
by the Plücker embedding, hence proper and separated, that its closed subschemes are H-projective,
and that the Hilbert scheme of `P^n_A` over a Noetherian ring is H-quasi-projective, hence
separated and of finite type, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial

universe u

namespace AglibTest.GrassmannianQuasiProjective

/-- The Grassmannian is H-projective over its base, and so are its closed subschemes. -/
theorem isHProjective (R : CommRingCat.{u}) (k n : ℕ)
    (I : (Grassmannian.schemeOver R k n).left.IdealSheafData) :
    IsHProjective (Grassmannian.toBase R k n) ∧
      IsHProjective (I.subschemeι ≫ (Grassmannian.schemeOver R k n).hom) :=
  ⟨inferInstance, inferInstance⟩

/-- The Hilbert scheme of `P^n_A` is H-quasi-projective over `Spec A`, hence separated and locally
of finite type. -/
theorem hilbertScheme (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (Φ : ℚ[X]) (r : ℕ) :
    IsHQuasiProjective (ProjectiveSpace.hilbertSchemeOver ι n e A Φ r).obj.hom ∧
      IsSeparated (ProjectiveSpace.hilbertSchemeOver ι n e A Φ r).obj.hom ∧
      LocallyOfFiniteType (ProjectiveSpace.hilbertSchemeOver ι n e A Φ r).obj.hom :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- info: 'AglibTest.GrassmannianQuasiProjective.isHProjective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuasiProjective.isHProjective

/-- info: 'AglibTest.GrassmannianQuasiProjective.hilbertScheme' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuasiProjective.hilbertScheme

end AglibTest.GrassmannianQuasiProjective
