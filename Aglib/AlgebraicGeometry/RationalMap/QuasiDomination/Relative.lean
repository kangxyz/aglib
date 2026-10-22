/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.FiniteCover
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.RelativeAffine
public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.SchematicDensity

/-!
# Relative quasi-affine partial maps on arbitrary Noetherian sources

A concrete immersion into an affine scheme over the base supplies the relative
quasi-affine target. An initial complement blowup makes the protected open
schematically dense. Actual affine-source extensions, open extension of their
admissible sequences, finite common refinement, and the original graph's
schematic image produce the global partial map. Neither the base nor the
modified source is assumed affine or reduced.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

private lemma lift_congrHom {A B C Z : Scheme.{u}} {a a' : A ⟶ Z} {b b' : B ⟶ Z}
    (ha : a = a') (hb : b = b') (i : C ⟶ A) (k : C ⟶ B)
    (v : i ≫ a = k ≫ b) (v' : i ≫ a' = k ≫ b') :
    pullback.lift i k v' = pullback.lift i k v ≫ (pullback.congrHom ha hb).hom := by
  subst a'
  subst b'
  simp

private theorem exists_relative_extension_of_schematicallyDense
    {X Y P S : Scheme.{u}} [IsNoetherian X]
    (U : X.Opens) [IsSchemeTheoreticallyDominant U.ι]
    (p : X ⟶ S) (e : Y ⟶ P) (a : P ⟶ S)
    [IsImmersion e] [IsAffineHom a]
    [QuasiCompact (e ≫ a)] [LocallyOfFiniteType (e ≫ a)]
    (g : U.toScheme ⟶ Y) (hg : g ≫ (e ≫ a) = U.ι ≫ p) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (E : Scheme.{u}) (d : E ⟶ X')
      (F : E ⟶ Y) (k : U.toScheme ⟶ E) (w : d ≫ β ≫ p = F ≫ (e ≫ a)),
      Blowup.AdmissibleSequence U β ∧ IsOpenImmersion d ∧
      IsSchemeTheoreticallyDominant d ∧ IsSchemeTheoreticallyDominant k ∧
      k ≫ d ≫ β = U.ι ∧ k ≫ F = g ∧ IsClosedImmersion (pullback.lift d F w) := by
  classical
  let C := X.affineCover.finiteSubcover
  let : Finite C.I₀ := inferInstanceAs (Finite X.affineCover.finiteSubcover.I₀)
  let : ∀ i, IsAffine (C.X i) := fun i ↦ inferInstance
  let : ∀ i, IsNoetherian (C.X i) := fun i ↦
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (C.f i) }
  let : ∀ i, QuasiCompact (C.f i) := fun i ↦ inferInstance
  have local_data (i : C.I₀) := exists_relative_quasiDomination_of_isAffine
    (C.f i ⁻¹ᵁ U) (C.f i ≫ p) e a ((C.f i ∣_ U) ≫ g) (by
      simp only [Category.assoc, hg, morphismRestrict_ι_assoc])
  choose B β D h j hw hseq _ _ _ _ hj hjh hc using local_data
  exact exists_quasiDomination_of_finite_cover U p (e ≫ a) g hg C
    B β hseq D h j hw hj hjh hc

/-- A partial map to a concretely relative quasi-affine finite-type target
extends after a finite admissible blowup sequence. The extension domain is
open and schematically dense in the modified source, its relative graph is
closed, and the original map is preserved literally on the entire given open.
The initial open need not be dense; no surjectivity of the modification is
asserted, and a finite sequence is not asserted to be a single blowup. -/
theorem exists_relative_quasiDomination
    {X Y P S : Scheme.{u}} [IsNoetherian X]
    (U : X.Opens) (p : X ⟶ S) (e : Y ⟶ P) (a : P ⟶ S)
    [IsImmersion e] [IsAffineHom a]
    [QuasiCompact (e ≫ a)] [LocallyOfFiniteType (e ≫ a)]
    (g : U.toScheme ⟶ Y) (hg : g ≫ (e ≫ a) = U.ι ≫ p) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (E : Scheme.{u}) (d : E ⟶ X')
      (F : E ⟶ Y) (k : U.toScheme ⟶ E) (w : d ≫ β ≫ p = F ≫ (e ≫ a)),
      Blowup.AdmissibleSequence U β ∧ IsProper β ∧ IsIso (β ∣_ U) ∧
      IsOpenImmersion d ∧ IsSchemeTheoreticallyDominant d ∧ DenseRange d ∧
      IsSchemeTheoreticallyDominant k ∧ k ≫ d ≫ β = U.ι ∧ k ≫ F = g ∧
      IsClosedImmersion (pullback.lift d F w) := by
  let K := IdealSheafData.vanishingIdeal U.compl
  let B := Blowup.blowupDatum K
  have hsupp : K.support.compl = U := TopologicalSpace.Opens.compl_compl U
  have hKU : K.comap U.ι = ⊤ := Blowup.BlowupDatum.comap_eq_top_of_disjoint U (by
    change Disjoint (U : Set X) (U.compl : Set X)
    exact Set.disjoint_left.mpr (fun _ hx hn ↦ hn hx))
  have hB := Blowup.AdmissibleSequence.single B U hKU
  let : IsProper B.map := hB.isProper
  let : IsIso (B.map ∣_ U) := hB.restrict_isIso
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  let : CompactSpace B.Y := QuasiCompact.compactSpace_of_compactSpace B.map
  let : IsNoetherian B.Y := ⟨⟩
  let V := B.map ⁻¹ᵁ U
  have hV : B.exceptionalComplement = V := congrArg (fun W ↦ B.map ⁻¹ᵁ W) hsupp
  let : IsSchemeTheoreticallyDominant V.ι := by
    rw [← hV]
    exact B.exceptionalComplement_isSchemeTheoreticallyDominant
  let gV := (B.map ∣_ U) ≫ g
  have hgV : gV ≫ (e ≫ a) = V.ι ≫ (B.map ≫ p) := by
    simp only [gV, Category.assoc, hg, morphismRestrict_ι_assoc]
    rfl
  obtain ⟨X', β, E, d, F, kV, hw, hβ, hd, hdom, hkV, hkVd, hkVF, hclosed⟩ :=
    exists_relative_extension_of_schematicallyDense V (B.map ≫ p) e a gV hgV
  let α := β ≫ B.map
  have hα : Blowup.AdmissibleSequence U α := hB.comp hβ
  let : IsProper α := hα.isProper
  let : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian α
  let : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace α
  let : IsNoetherian X' := ⟨⟩
  let : IsOpenImmersion d := hd
  let : IsSchemeTheoreticallyDominant d := hdom
  let : IsSchemeTheoreticallyDominant kV := hkV
  let k := inv (B.map ∣_ U) ≫ kV
  have hw' : d ≫ α ≫ p = F ≫ (e ≫ a) := by
    simpa only [α, Category.assoc] using hw
  refine ⟨X', α, E, d, F, k, hw', hα, hα.isProper, hα.restrict_isIso,
    hd, hdom, d.denseRange, inferInstance, ?_, ?_, ?_⟩
  · calc
      k ≫ d ≫ α = inv (B.map ∣_ U) ≫ (kV ≫ d ≫ β) ≫ B.map := by
        simp only [k, α, Category.assoc]
      _ = inv (B.map ∣_ U) ≫ V.ι ≫ B.map := by rw [hkVd]
      _ = U.ι := by
        change inv (B.map ∣_ U) ≫ (B.map ⁻¹ᵁ U).ι ≫ B.map = U.ι
        rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  · simp only [k, Category.assoc, hkVF, gV, IsIso.inv_hom_id_assoc]
  · let L := pullback.congrHom (Category.assoc β B.map p).symm (rfl : e ≫ a = e ≫ a)
    have heq : pullback.lift d F hw' = pullback.lift d F hw ≫ L.hom :=
      lift_congrHom (Category.assoc β B.map p).symm rfl d F hw hw'
    rw [heq]
    let : IsClosedImmersion (pullback.lift d F hw) := hclosed
    infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
