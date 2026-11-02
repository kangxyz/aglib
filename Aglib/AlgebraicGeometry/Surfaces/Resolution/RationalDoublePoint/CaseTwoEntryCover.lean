/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoEntry

/-!
# First entry on the original two-chart cover

Both branches use the same true cubic, with its original coefficients swapped
on the second chart. No preferred-chart hypothesis or new cubic is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open Localization.Away Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoEntryCover

variable {A : Type u} [CommRing A] [IsLocalRing A]

private theorem swapped_cubic_ne_zero (C : CubicCoefficients A) (hn : C.residueCubic ≠ 0) :
    C.swap.residueCubic ≠ 0 := by
  intro hz
  have h0 : IsLocalRing.residue A C.a0 = 0 := by
    simpa only [CubicCoefficients.residueCubic_coeff_three, CubicCoefficients.swap,
      Polynomial.coeff_zero] using congrArg (fun p : Polynomial (ResidueField A) => p.coeff 3) hz
  have h1 : IsLocalRing.residue A C.a1 = 0 := by
    simpa only [CubicCoefficients.residueCubic_coeff_two, CubicCoefficients.swap,
      Polynomial.coeff_zero] using congrArg (fun p : Polynomial (ResidueField A) => p.coeff 2) hz
  have h2 : IsLocalRing.residue A C.a2 = 0 := by
    simpa only [CubicCoefficients.residueCubic_coeff_one, CubicCoefficients.swap,
      Polynomial.coeff_zero] using congrArg (fun p : Polynomial (ResidueField A) => p.coeff 1) hz
  have h3 : IsLocalRing.residue A C.a3 = 0 := by
    simpa only [CubicCoefficients.residueCubic_coeff_zero, CubicCoefficients.swap,
      Polynomial.coeff_zero] using congrArg (fun p : Polynomial (ResidueField A) => p.coeff 0) hz
  apply hn
  dsimp only [CubicCoefficients.residueCubic, IsLocalRing.residueBinaryCubic]
  simp only [h0, h1, h2, h3, Polynomial.C_0, zero_mul, add_zero]

variable [IsDomain A] [IsNoetherianRing A]
    (B : BlowupDatum (affineCenter A (maximalIdeal A)))

/-- Every actual first Case-II child produces a full parent marker or a full
original-stalk entry identity. The original parameter/coefficient alternatives
record exactly which chart of the same true cubic contains the child. -/
theorem marker_or_tripleEntry_at_closed_point
    (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2})
    (F : CubicRelation t s z) (hn : F.coefficients.residueCubic ≠ 0)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x))
    (tC sC zC : maximalIdeal (B.Y.presheaf.stalk x))
    (hgenC : maximalIdeal (B.Y.presheaf.stalk x) = Ideal.span
      ({(tC : B.Y.presheaf.stalk x), (sC : B.Y.presheaf.stalk x),
        (zC : B.Y.presheaf.stalk x)} : Set (B.Y.presheaf.stalk x)))
    (hrankC : Module.finrank
      ((B.Y.presheaf.stalk x) ⧸ maximalIdeal (B.Y.presheaf.stalk x))
      (maximalIdeal (B.Y.presheaf.stalk x)).Cotangent = 3)
    (hkerC : doubleLineChildCotangentKernel (B.Y.presheaf.stalk x) ![sC, zC, tC] =
      Ideal.span {(MvPolynomial.X 1 :
        MvPolynomial (Fin 3) (ResidueField (B.Y.presheaf.stalk x))) ^ 2}) :
    letI := B.map.stalkScalar_isLocalHom_of_closedPoint x hbase
    (∃ r : maximalIdeal A, ∃ M : MarkedCubic r, M.square = z) ∨
      (∃ p u w : maximalIdeal (B.Y.presheaf.stalk x), ∃ T : TripleEntryData p u w,
        (((p : B.Y.presheaf.stalk x) = B.map.stalkScalar x (t : A) ∧
            T.coefficient = B.map.stalkScalar x F.coefficients.a3) ∨
          ((p : B.Y.presheaf.stalk x) = B.map.stalkScalar x (s : A) ∧
            T.coefficient = B.map.stalkScalar x F.coefficients.a0)) ∧
          (p : B.Y.presheaf.stalk x) ∉ maximalIdeal (B.Y.presheaf.stalk x) ^ 2 ∧
          (maximalIdeal A).map (B.map.stalkScalar x) =
            Ideal.span {(p : B.Y.presheaf.stalk x)} ∧
          Function.Bijective (ResidueField.map (B.map.stalkScalar x))) := by
  let : IsLocalHom (B.map.stalkScalar x) := B.map.stalkScalar_isLocalHom_of_closedPoint x hbase
  obtain ht | hs := CaseTwoPoint.mem_planeChart_or_opposite_of_closed_exceptional_point
    B t s z hgen hker x hx hbase
  · rcases CaseTwoEntry.marker_or_tripleEntry_at_closed_point
      B t s z hgen hker F hn x hx hbase hsing ht tC sC zC hgenC hrankC hkerC with
      hM | ⟨p, u, w, hp, T, hT, hmin, hcenter, hres⟩
    · exact Or.inl hM
    · exact Or.inr ⟨p, u, w, T, Or.inl ⟨hp, hT⟩, hmin, hcenter, hres⟩
  · have hg : maximalIdeal A = Ideal.span ({(s : A), (t : A), (z : A)} : Set A) := by
      simpa only [Set.insert_comm] using hgen
    have hk : doubleLineChildCotangentKernel A ![t, z, s] =
        Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
      have h := cotangentKernel_planeChange ![s, z, t] 0 1 1 0 (by simp) hker
      simpa only [planeChangeTriple_triple, zero_smul, one_smul, zero_add, add_zero] using h
    have hn' : F.swap.coefficients.residueCubic ≠ 0 := swapped_cubic_ne_zero F.coefficients hn
    rcases CaseTwoEntry.marker_or_tripleEntry_at_closed_point
      B s t z hg hk F.swap hn' x hx hbase hsing hs tC sC zC hgenC hrankC hkerC with
      hM | ⟨p, u, w, hp, T, hT, hmin, hcenter, hres⟩
    · exact Or.inl hM
    · exact Or.inr ⟨p, u, w, T, Or.inr ⟨hp, hT⟩, hmin, hcenter, hres⟩

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoEntryCover
