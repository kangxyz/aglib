/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.RationalPointEtaleLocal
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk

/-! # The actual base-change section through a rational residue point

The ring-level producer supplies one local tensor slice. Its original algebra
map gives a section of the native scheme pullback. The first projection,
structural section equation, and original residue-point triangle are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

variable {R B S : Type u} [CommRing R] [CommRing B] [CommRing S]
  [Algebra R B] [Algebra R S]

/-- The original algebra map defines a section of the native affine base
change, not a separately selected fibre-product model. -/
def rationalPointBaseChangeSection (ε : B →ₐ[R] S) :
    Spec (.of S) ⟶ pullback (Spec.algebraMap R B) (Spec.algebraMap R S) :=
  pullback.lift (Spec.map (CommRingCat.ofHom ε.toRingHom)) (𝟙 _) (by
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact ε.commutes r)

/-- The structural projection is the identity on the same local base. -/
@[reassoc]
theorem rationalPointBaseChangeSection_snd (ε : B →ₐ[R] S) :
    rationalPointBaseChangeSection ε ≫ pullback.snd (Spec.algebraMap R B)
      (Spec.algebraMap R S) = 𝟙 _ := pullback.lift_snd _ _ _

/-- The first projection is exactly the originally supplied chart map. -/
@[reassoc]
theorem rationalPointBaseChangeSection_fst (ε : B →ₐ[R] S) :
    rationalPointBaseChangeSection ε ≫ pullback.fst (Spec.algebraMap R B)
      (Spec.algebraMap R S) = Spec.map (CommRingCat.ofHom ε.toRingHom) :=
  pullback.lift_fst _ _ _

/-- The original residue rational point is recovered under the same first
projection of the base-change section. -/
@[reassoc]
theorem rationalPointBaseChangeSection_residue [IsLocalRing R]
    (ε : B →ₐ[R] S) (l : S →ₐ[R] ResidueField R) (ψ : B →ₐ[R] ResidueField R)
    (h : l.comp ε = ψ) :
    Spec.map (CommRingCat.ofHom l.toRingHom) ≫ rationalPointBaseChangeSection ε ≫
      pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R S) =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
  rw [rationalPointBaseChangeSection_fst, ← Spec.map_comp]
  congr 1
  ext b
  exact DFunLike.congr_fun h b

/-- The residue point of the selected local slice is its original closed
point, as follows from the actual local residue homomorphism. -/
theorem localResiduePoint_eq_closedPoint [IsLocalRing R] [IsLocalRing S]
    (l : S →ₐ[R] ResidueField R) [IsLocalHom l.toRingHom] :
    Spec.map (CommRingCat.ofHom l.toRingHom) (closedPoint (ResidueField R)) =
      closedPoint S := by
  apply PrimeSpectrum.ext
  exact maximalIdeal_comap l.toRingHom

/-- A smooth algebra's original rational residue point admits the actual
base-change section over the constructed essentially etale local ring. The
same algebra and residue maps remain in the conclusion. -/
theorem exists_essEtale_local_baseChangeSection
    (R B : Type u) [CommRing R] [CommRing B] [IsLocalRing R]
    [Algebra R B] [Algebra.Smooth R B] (ψ : B →ₐ[R] ResidueField R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : IsLocalRing S),
      Algebra.FormallyEtale R S ∧ Algebra.EssFiniteType R S ∧ Module.Flat R S ∧
        IsLocalHom (algebraMap R S) ∧
          ∃ (ε : B →ₐ[R] S) (l : S →ₐ[R] ResidueField R),
            Function.Surjective l ∧ IsLocalHom l.toRingHom ∧ l.comp ε = ψ ∧
              rationalPointBaseChangeSection ε ≫
                pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R S) = 𝟙 _ ∧
              Spec.map (CommRingCat.ofHom l.toRingHom) ≫ rationalPointBaseChangeSection ε ≫
                pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R S) =
                  Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
  obtain ⟨S, hS, hRS, hlocal, he, hft, hflat, hl, ε, l, hsurj, hll, hcomp⟩ :=
    Algebra.Smooth.RationalPointEtaleLocal.exists_local_lift R B ψ
  let : CommRing S := hS
  let : Algebra R S := hRS
  let : IsLocalRing S := hlocal
  exact ⟨S, hS, hRS, hlocal, he, hft, hflat, hl, ε, l, hsurj, hll, hcomp,
    rationalPointBaseChangeSection_snd ε,
    rationalPointBaseChangeSection_residue ε l ψ hcomp⟩

end AlgebraicGeometry.Scheme
