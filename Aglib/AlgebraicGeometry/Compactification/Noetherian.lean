/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.PatchFamily
public import Aglib.AlgebraicGeometry.Compactification.ProperSource.Patches

/-!
# Nagata compactification over a Noetherian base

The finite patch family is constructed from actual compactifiable modifications
and boundary control. A proper covering model and actual sequence lifts prove
the separated common enlargement proper. The empty source is included. No
projectivity or replacement of a sequence by one blowup is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A separated finite-type morphism to a Noetherian scheme admits a
compactification, with the original structural morphism unchanged. -/
theorem exists_compactification_of_isNoetherian {X S : Scheme.{u}}
    [IsNoetherian S] (p : X ⟶ S)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] :
    Nonempty p.Compactification := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
    let : IsEmpty X := hX
    exact ⟨{
      Xbar := X
      j := 𝟙 X
      p := p
      isOpenImmersion_j := inferInstance
      isProper_p := inferInstance
      fac := Category.id_comp p }⟩
  | inr hX =>
    let : Nonempty X := hX
    obtain ⟨U, P, pP, c, n, O, M, pM, x, k, a, hU, hP, hpP, hc, hdc,
      _hbasec, hO, hfamily⟩ := Scheme.Compactification.exists_finite_patch_family p
    let : IsNoetherian P := hP
    let : IsProper pP := hpP
    let : IsOpenImmersion c := hc
    let : IsSchemeTheoreticallyDominant c := hdc
    have hN := fun i ↦ (hfamily i).1
    have hs := fun i ↦ (hfamily i).2.1
    have hqc := fun i ↦ (hfamily i).2.2.1
    have hlft := fun i ↦ (hfamily i).2.2.2.1
    have ho := fun i ↦ (hfamily i).2.2.2.2.1
    have hd := fun i ↦ (hfamily i).2.2.2.2.2.1
    let : ∀ i, IsNoetherian (M i) := hN
    let : ∀ i, IsSeparated (pM i) := hs
    let : ∀ i, QuasiCompact (pM i) := hqc
    let : ∀ i, LocallyOfFiniteType (pM i) := hlft
    let : ∀ i, IsOpenImmersion (x i) := ho
    let : ∀ i, IsSchemeTheoreticallyDominant (x i) := hd
    exact Scheme.Compactification.exists_compactification_of_patch_family p U hU pP c
      n O hO M pM x (fun i ↦ (hfamily i).2.2.2.2.2.2.1)
      k (fun i ↦ (hfamily i).2.2.2.2.2.2.2.1)
      a (fun i ↦ (hfamily i).2.2.2.2.2.2.2.2.1)
      (fun i ↦ (hfamily i).2.2.2.2.2.2.2.2.2)

/-- The compactification can be chosen with schematically dense original
source, by taking the actual scheme-theoretic image of the open embedding. -/
theorem exists_schematicallyDense_compactification_of_isNoetherian
    {X S : Scheme.{u}} [IsNoetherian S] (p : X ⟶ S)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] :
    ∃ C : p.Compactification, IsSchemeTheoreticallyDominant C.j := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨C⟩ := exists_compactification_of_isNoetherian p
  exact ⟨Compactification.ofImmersion p C.j C.p C.fac, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom
