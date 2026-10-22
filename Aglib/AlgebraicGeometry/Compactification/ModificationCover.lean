/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.DenseAffine
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.CompactifiableSequence

/-!
# A finite cover with actual compactifiable modifications

Each dense affine chart is first compactified over the original base. The
compactifiable-sequence theorem then modifies the entire source while fixing
that chart. All source lifts and structural maps are retained literally.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A separated finite-type morphism over a Noetherian base admits a finite
cover by dense affine opens, each protected by an actual compactifiable
admissible sequence. The common intersection is dense, including when the
index is empty. Schematic density is asserted for each original chart lift,
not for the common intersection in every model. -/
theorem exists_finite_dense_compactifiable_modification_cover
    {X S : Scheme.{u}} [IsNoetherian S]
    (p : X ⟶ S) [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ a, IsAffineOpen (U a) ∧ Dense (U a : Set X) ∧
        ∃ (T Y : Scheme.{u}) (β : T ⟶ X) (pY : Y ⟶ S)
          (i : T ⟶ Y) (t : (U a).toScheme ⟶ T),
          IsNoetherian T ∧ IsNoetherian Y ∧
          Blowup.AdmissibleSequence (U a) β ∧ IsProper β ∧
          IsIso (β ∣_ U a) ∧ IsProper pY ∧
          IsOpenImmersion i ∧ IsOpenImmersion t ∧
          IsSchemeTheoreticallyDominant t ∧
          IsSchemeTheoreticallyDominant (t ≫ i) ∧ DenseRange i ∧
          i ≫ pY = β ≫ p ∧ t ≫ β = (U a).ι) ∧
      (⨆ a, U a) = ⊤ ∧ Dense ((⨅ a, U a : X.Opens) : Set X) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨ι, hι, U, hU, hcover, hinter⟩ :=
    exists_finite_dense_affine_compactifiable_cover p
  let : Fintype ι := hι
  refine ⟨ι, hι, U, ?_, hcover, hinter⟩
  intro a
  obtain ⟨haff, hdense, _, C, hC⟩ := hU a
  let : IsSchemeTheoreticallyDominant C.j := hC
  let : IsLocallyNoetherian C.Xbar := LocallyOfFiniteType.isLocallyNoetherian C.p
  let : CompactSpace C.Xbar := QuasiCompact.compactSpace_of_compactSpace C.p
  let : IsNoetherian C.Xbar := ⟨⟩
  obtain ⟨T, Y, β, γ, i, t, hβ, _, hβp, _, hpY, hi, ht, hti, hd,
    hibase, htbase, _⟩ :=
    QuasiDomination.exists_compactifiable_sequence_of_openImmersion
      p C.p (U a) hdense C.j C.fac
  let : IsProper β := hβp
  let : IsProper (γ ≫ C.p) := hpY
  let : IsIso (β ∣_ U a) := hβ.restrict_isIso
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian β
  let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace β
  let : IsNoetherian T := ⟨⟩
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (γ ≫ C.p)
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (γ ≫ C.p)
  let : IsNoetherian Y := ⟨⟩
  refine ⟨haff, hdense, T, Y, β, γ ≫ C.p, i, t, inferInstance, inferInstance,
    hβ, hβp, inferInstance, hpY, hi, ?_, ht, hti, hd, hibase, htbase⟩
  exact β.isOpenImmersion_of_isIso_restriction (U a) t htbase

end AlgebraicGeometry.Scheme
