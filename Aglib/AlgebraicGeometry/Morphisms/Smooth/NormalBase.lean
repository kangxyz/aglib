/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.RingTheory.Smooth.Normal

/-! # Smooth domain algebras over normal domains

The original smooth-field stalk theorem gives normality of the actual generic
fibre. Smooth integral-closure base change then descends normality to the
original domain algebra. Neither excellence nor regularity of the base is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

/-- Smoothness of an actual affine scheme over a field implies that its
domain coordinate ring is integrally closed. -/
theorem isIntegrallyClosed_of_smoothSpec
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A)))) : IsIntegrallyClosed A := by
  let X := Spec (.of A)
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (smoothFieldNormality k X _ h x).2
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : IsIntegrallyClosed Γ(X, ⊤) :=
    isIntegrallyClosed_sections_of_isAffineOpen X ⊤ (isAffineOpen_top _)
  exact IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv

end AlgebraicGeometry.Scheme

namespace Algebra.Smooth

/-- An arbitrary smooth domain algebra over a normal domain is normal.
The base need not be regular, Noetherian, excellent, or a field. -/
theorem isIntegrallyClosed_of_normalBase
    (R S : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Smooth R S] :
    IsIntegrallyClosed S := by
  let K := FractionRing R
  let : IsDomain (S ⊗[R] K) := generic_isDomain R K S
  let : IsDomain (K ⊗[R] S) :=
    MulEquiv.isDomain _ (Algebra.TensorProduct.comm R K S).toRingEquiv.toMulEquiv
  let : IsIntegrallyClosed (K ⊗[R] S) :=
    Scheme.isIntegrallyClosed_of_smoothSpec K (K ⊗[R] S)
      (HasRingHomProperty.Spec_iff.mpr (by
        change (algebraMap K (K ⊗[R] S)).Smooth
        exact RingHom.smooth_algebraMap.mpr inferInstance))
  let : IsIntegrallyClosed (S ⊗[R] K) :=
    IsIntegrallyClosed.of_equiv (Algebra.TensorProduct.comm R K S).toRingEquiv
  exact isIntegrallyClosed_of_generic R K S

end Algebra.Smooth
