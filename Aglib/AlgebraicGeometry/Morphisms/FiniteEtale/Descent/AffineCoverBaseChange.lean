/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineCoverAlgebra
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Actual affine finite-etale cover comparisons

Algebra equivalences and tensor scalar extension give the corresponding
isomorphisms of native finite-etale covers, over arbitrary commutative rings.
The field-descent interfaces delegate to these same comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Spec of an algebra equivalence, preserving the actual structural map. -/
def specCoverIso {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Finite A B] [Algebra.Etale A B]
    [Module.Finite A C] [Algebra.Etale A C] (e : B ≃ₐ[A] C) :
    specCover A B ≅ specCover A C :=
  ObjectProperty.isoMk _ (Over.isoMk
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).symm (by
      change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A C)) =
          Spec.map (CommRingCat.ofHom (algebraMap A B))
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext e.symm.toAlgHom.comp_algebraMap)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor-spectrum comparison as an isomorphism of finite-etale covers. -/
def specBaseChangeIso (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] :
    (baseChange (Spec.algebraMap R S)).obj (specCover R A) ≅ specCover S (S ⊗[R] A) :=
  ObjectProperty.isoMk _ (Over.isoMk
    (pullbackSymmetry (Spec.algebraMap R A) (Spec.algebraMap R S) ≪≫ pullbackSpecIso R S A)
    (by
      change (_ ≫ _) ≫ Spec.algebraMap S (S ⊗[R] A) = _
      rw [Category.assoc, pullbackSpecIso_hom_fst']
      exact pullbackSymmetry_hom_comp_fst _ _))

end AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent
