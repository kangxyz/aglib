/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Decomposition
public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Family

/-! Focused consumer of the clopen decomposition of a flat family of closed subschemes of
`P^n_A ×_{Spec A} T` by fibre Hilbert polynomial and of its restrictions to the pieces, with axiom
guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology
open scoped Polynomial

universe u

/-- The restriction of a flat family to an open subscheme on which its fibre polynomial is `Φ` is
a point of `Hilb^Φ`. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {T : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} (V : (pullback (toSpec A ι) g).IdealSheafData)
    (hflat : Flat (V.subschemeι ≫ pullback.snd (toSpec A ι) g)) (Φ : ℚ[X]) (U : T.Opens)
    (hU : ∀ t ∈ U, fiberHilbertPolynomialAt ι g V.quotientModule t = Φ) :
    IsHilbertFamily ι Φ (U.ι ≫ g) (V.comap (pullbackBaseChange ι g U.ι)) :=
  isHilbertFamily_comap_pullbackBaseChange_of_flat ι V hflat _ fun t' =>
    hU _ ((Scheme.Opens.range_ι U).subset ⟨t', rfl⟩)

/-- For a flat family over a locally Noetherian base, the locus where the fibre polynomial is `Φ`
is an open subscheme over which the family is a point of `Hilb^Φ`. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {T : Scheme.{u}}
    [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)} (n : ℕ) (e : ι ≃ Fin (n + 1))
    (V : (pullback (toSpec A ι) g).IdealSheafData)
    (hflat : Flat (V.subschemeι ≫ pullback.snd (toSpec A ι) g)) (Φ : ℚ[X]) :
    ∃ U : T.Opens, (U : Set T) = {t | fiberHilbertPolynomialAt ι g V.quotientModule t = Φ} ∧
      IsHilbertFamily ι Φ (U.ι ≫ g) (V.comap (pullbackBaseChange ι g U.ι)) :=
  ⟨⟨_, (isClopen_setOf_fiberHilbertPolynomialAt_quotientModule_eq_of_flat ι n e
      V.affineLocallyFiniteType_quotientModule hflat Φ).isOpen⟩, rfl,
    isHilbertFamily_comap_pullbackBaseChange_of_flat ι V hflat _ fun t' =>
      (Scheme.Opens.range_ι _).subset ⟨t', rfl⟩⟩

/-- The restriction of any family to a flattening stratum is a point of `Hilb^Φ`. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {T : Scheme.{u}}
    [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)} (n : ℕ) (e : ι ≃ Fin (n + 1))
    (V : (pullback (toSpec A ι) g).IdealSheafData) (Φ : ℚ[X]) :
    IsHilbertFamily ι Φ
      (flatteningStratumι ι g n e V.affineLocallyFiniteType_quotientModule Φ ≫ g)
      (V.comap (pullbackBaseChange ι g
        (flatteningStratumι ι g n e V.affineLocallyFiniteType_quotientModule Φ))) :=
  isHilbertFamily_comap_flatteningStratumι ι V n e _ Φ

/-- A flat family over a locally Noetherian base whose fibre polynomials lie in a finite set `F`
decomposes the base as `∐_{Φ ∈ F} T_Φ`. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {T : Scheme.{u}}
    [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)} (n : ℕ) (e : ι ≃ Fin (n + 1))
    (V : (pullback (toSpec A ι) g).IdealSheafData)
    (hflat : Flat (V.subschemeι ≫ pullback.snd (toSpec A ι) g)) (F : Finset ℚ[X])
    (hP : ∀ t, fiberHilbertPolynomialAt ι g V.quotientModule t ∈ F) :
    IsIso (Sigma.desc fun Φ : F =>
      flatteningStratumι ι g n e V.affineLocallyFiniteType_quotientModule Φ) :=
  isIso_sigmaDesc_flatteningStratumι_of_flat ι n e _ hflat (fun Φ : F => (Φ : ℚ[X]))
    Subtype.val_injective fun t => ⟨⟨_, hP t⟩, rfl⟩

/-- Fibre polynomials of a pulled-back family are those at the image points. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {T T' : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} (V : (pullback (toSpec A ι) g).IdealSheafData)
    (f : T' ⟶ T) (t' : T') :
    fiberHilbertPolynomialAt ι (f ≫ g)
        (V.comap (baseChangeMap ι g (f ≫ g) f rfl)).quotientModule t' =
      fiberHilbertPolynomialAt ι g V.quotientModule (f t') :=
  fiberHilbertPolynomialAt_quotientModule_comap_baseChangeMap ι V _ f rfl t'

/-- Hilbert families `D j ∈ Hilb^{Φ j}(H j)` glue to a flat family over `∐ H` with fibre
polynomial `Φ j` on the `j`-th component. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {J : Type} [Finite J]
    {H : J → Scheme.{u}} (πH : ∀ j, H j ⟶ Spec (CommRingCat.of A)) (Φ : J → ℚ[X])
    (D : ∀ j, (pullback (toSpec A ι) (πH j)).IdealSheafData)
    (hD : ∀ j, IsHilbertFamily ι (Φ j) (πH j) (D j)) (j : J) (y : H j) :
    fiberHilbertPolynomialAt ι (Sigma.desc πH)
        (Scheme.IdealSheafData.sigmaGlue (toSpec A ι) πH D).quotientModule (Sigma.ι H j y) =
          Φ j ∧
      Flat ((Scheme.IdealSheafData.sigmaGlue (toSpec A ι) πH D).subschemeι ≫
        pullback.snd (toSpec A ι) (Sigma.desc πH)) :=
  ⟨fiberHilbertPolynomialAt_sigmaGlue_sigmaι_of_isHilbertFamily ι πH D Φ hD j y,
    Scheme.IdealSheafData.flat_sigmaGlue _ πH D fun j => (hD j).flat⟩

/-- For distinct polynomials, the preimage of the `j`-th component under `a : T ⟶ ∐ H` is the
locus where the pulled-back glued family has fibre polynomial `Φ j`. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {J : Type} [Finite J]
    {H : J → Scheme.{u}} (πH : ∀ j, H j ⟶ Spec (CommRingCat.of A)) (Φ : J → ℚ[X])
    (hΦ : Function.Injective Φ) (D : ∀ j, (pullback (toSpec A ι) (πH j)).IdealSheafData)
    (hD : ∀ j, IsHilbertFamily ι (Φ j) (πH j) (D j)) {T : Scheme.{u}} (a : T ⟶ ∐ H) (j : J) :
    {t | fiberHilbertPolynomialAt ι (a ≫ Sigma.desc πH)
        ((Scheme.IdealSheafData.sigmaGlue (toSpec A ι) πH D).comap
          (baseChangeMap ι (Sigma.desc πH) _ a rfl)).quotientModule t = Φ j} =
      a ⁻¹' Set.range (Sigma.ι H j) :=
  Set.ext fun t => fiberHilbertPolynomialAt_sigmaGlue_comap_eq_iff ι πH D Φ hΦ hD _ a rfl t j

/--
info: 'AlgebraicGeometry.ProjectiveSpace.fiberHilbertPolynomialAt_sigmaGlue_sigmaι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.fiberHilbertPolynomialAt_sigmaGlue_sigmaι

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isIso_sigmaDesc_flatteningStratumι_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isIso_sigmaDesc_flatteningStratumι_of_flat

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_comap_pullbackBaseChange_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_comap_pullbackBaseChange_of_flat
