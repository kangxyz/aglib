/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Algebra equivalences from spectrum isomorphisms

Relocated declarations with native names from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; explicit
source and hypothesis boundaries are retained.
-/

@[expose] public section




universe u

section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Spec
variable {A B : Type u} [CommRing A] [CommRing B]

/-- The contravariant coordinate-ring equivalence of an actual spectrum
isomorphism, obtained from the fully faithful Spec functor. -/
def ringEquivOfIso (e : Spec (.of A) ≅ Spec (.of B)) : A ≃+* B :=
  ((Scheme.Spec.preimageIso e).unop.symm).commRingCatIsoToRingEquiv

theorem map_ringEquivOfIso (e : Spec (.of A) ≅ Spec (.of B)) :
    Spec.map (CommRingCat.ofHom (ringEquivOfIso e).toRingHom) = e.inv := by
  change Spec.map (Spec.preimage e.inv) = e.inv
  exact Spec.map_preimage _

/-- An actual spectrum isomorphism over Spec R gives the corresponding
R-algebra equivalence, preserving the original scalar maps. -/
def algEquivOfIso (R : Type u) [CommRing R] [Algebra R A] [Algebra R B]
    (e : Spec (.of A) ≅ Spec (.of B))
    (h : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) : A ≃ₐ[R] B :=
  { ringEquivOfIso e with
    commutes' := fun r => by
      have hinv : e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
          Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
        rw [← h, Iso.inv_hom_id_assoc]
      have hr : CommRingCat.ofHom (algebraMap R A) ≫
          CommRingCat.ofHom (ringEquivOfIso e).toRingHom =
            CommRingCat.ofHom (algebraMap R B) := by
        apply Spec.map_injective
        rw [Spec.map_comp, map_ringEquivOfIso, hinv]
      exact congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of B => q.hom r) hr }

theorem map_algEquivOfIso (R : Type u) [CommRing R] [Algebra R A] [Algebra R B]
    (e : Spec (.of A) ≅ Spec (.of B))
    (h : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec.map (CommRingCat.ofHom (algEquivOfIso R e h).toRingHom) = e.inv :=
  map_ringEquivOfIso e

end AlgebraicGeometry.Spec

end -- original noncomputable section
end

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AffineScheme/IsomorphismCoordinates.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 c5bbd5e24dcca1ef79d1419ea83f4ec7666e102627ad3fa73283ec0999583f79.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
