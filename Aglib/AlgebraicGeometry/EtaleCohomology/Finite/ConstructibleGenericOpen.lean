/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ConstructibleSplitBase
public import Aglib.RingTheory.Artinian.NoetherianGenericSplitThickening

/-! # Actual generic principal opens for finite-image constructibility

The same original split quotient is transported by the native
cancel-base-change equivalence. Its surjectivity and kernel power descend
through the actual map square. The finite integral base map is surjective
only over the second principal open. The Noetherian specialization consumes
the existing generic splitting producer without assuming a basis, quotient
or constructibility conclusion. Global stratification is a separate step.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

/-- Transport the same quotient along the original base-change cancellation,
then use the actual spectrum base change over `S`. -/
theorem isConstructible_directImage_of_splitBaseChangeTower
    {R S C A : Type u} [CommRing R] [CommRing S] [CommRing C] [CommRing A]
    [Algebra R S] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
    [Algebra R A] [Module.Finite R A]
    (hC : Function.Surjective (PrimeSpectrum.comap (algebraMap S C)))
    {J : Type u} [Finite J] (q : C ⊗[R] A →ₐ[C] (J → C))
    (hq : Function.Surjective q) (n : ℕ) (hn : (RingHom.ker q.toRingHom) ^ n = ⊥)
    {F : AbelianSheaf.{u, u + 1} (Spec (.of (S ⊗[R] A)))}
    (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((directImage (Spec.algebraMap S (S ⊗[R] A))).obj F) := by
  let e := Algebra.TensorProduct.cancelBaseChange R S C C A
  let q' := q.comp e.toAlgHom
  have hq' : Function.Surjective q' := hq.comp e.surjective
  have hn' : (RingHom.ker q'.toRingHom) ^ n = ⊥ :=
    RingHom.ker_pow_eq_bot_of_injective_square e.toAlgHom q'.toRingHom q.toRingHom
      (RingHom.id _) e.injective (fun _ => rfl) n hn
  exact isConstructible_directImage_of_splitBase hC q' hq' n hn' hF

/-- The actual principal-open conclusion, uniformly for all original
constructible abelian coefficients on the restricted finite algebra. -/
def constructibleFiniteImageOnPrincipalOpen
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Prop :=
  ∃ b : R, b ≠ 0 ∧
    ∀ (F : AbelianSheaf.{u, u + 1} (Spec (.of ((Localization.Away b) ⊗[R] A)))),
      Constructible.IsConstructible F → Constructible.IsConstructible
        ((directImage (Spec.algebraMap (Localization.Away b)
          ((Localization.Away b) ⊗[R] A))).obj F)

/-- Extract the original finite integral base map and original quotient from
the already constructed splitting, and use their actual structure maps. -/
theorem constructibleFiniteImageOnPrincipalOpen_of_splitThickening
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ω : Type u) [Field Ω] [Algebra K Ω]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A]
    (hsplit : Algebra.FiniteAlgebra.finiteSplitThickeningOnPrincipalOpen R K Ω A) :
    constructibleFiniteImageOnPrincipalOpen R A := by
  have : IsArtinianRing (Ω ⊗[K] (K ⊗[R] A)) := IsArtinianRing.of_finite Ω _
  obtain ⟨n, _hn, L, hL⟩ := hsplit
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  obtain ⟨b, hb, B, _hB, _hfinite, hsurj, q, hq, hnil⟩ := hL
  let S := Localization.Away b
  let C := Localization.Away (algebraMap R B b)
  let β := IsFractionRing.finiteSubalgebraAwayBaseMap B b
  let : Algebra S C := β.toRingHom.toAlgebra
  have : IsScalarTower R S C :=
    IsScalarTower.of_algebraMap_eq fun x => (β.commutes x).symm
  refine ⟨b, hb, ?_⟩
  intro F hF
  exact isConstructible_directImage_of_splitBaseChangeTower
    (R := R) (S := S) (C := C) (A := A) hsurj q hq n hnil hF

/-- A finite algebra over a Noetherian domain has two genuine nonzero
principal restrictions on which every original constructible abelian
coefficient has constructible finite direct image. Neither a basis nor a
splitting certificate is an input. -/
theorem exists_noetherianGeneric_constructibleFiniteImage
    (R A : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ a : R, a ≠ 0 ∧ constructibleFiniteImageOnPrincipalOpen
      (Localization.Away a) ((Localization.Away a) ⊗[R] A) := by
  obtain ⟨a, ha, hsplit⟩ :=
    Algebra.FiniteAlgebra.exists_noetherianGeneric_splitThickening R A
  refine ⟨a, ha, ?_⟩
  let : IsDomain (Localization.Away a) := Localization.Away.isDomain ha
  exact constructibleFiniteImageOnPrincipalOpen_of_splitThickening
    (Localization.Away a) (FractionRing (Localization.Away a))
    (AlgebraicClosure (FractionRing (Localization.Away a)))
    ((Localization.Away a) ⊗[R] A) hsplit

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
