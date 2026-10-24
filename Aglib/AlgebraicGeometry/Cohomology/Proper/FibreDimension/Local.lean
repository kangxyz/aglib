/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Thickening
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Noetherian
public import Aglib.Algebra.Category.ModuleCat.NatTower
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Proper coherent vanishing above the closed-fibre dimension over a local base

All positive actual maximal-ideal thickenings have the same underlying
space. Noetherian sheaf-cohomology vanishing therefore kills their original
cohomology above the dimension of the first thickening. Compatibility also
kills coordinate zero of the original tower.

General formal functions identifies the completion of the original finite
cohomology module with this zero tower-section module. Krull intersection
makes the original map into that completion injective over a Noetherian
local ring. The base ring need not be complete, and no source regularity,
integrality or coefficient flatness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u v

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem range_actualThickening {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (I : Ideal A) :
    Set.range (idealThickeningι f I) = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
  change Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) = _
  rw [Scheme.Pullback.range_fst]
  have hspec : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  rw [hspec]

private theorem compatibleSections_subsingleton_of_positive
    {A : Type u} [CommRing A] (Q : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (hQ : ∀ n : ℕ, Subsingleton (Q.obj (op (n + 1)))) :
    Subsingleton (ModuleCat.sectionsSubmodule Q) := by
  constructor
  intro s t
  apply Subtype.ext
  funext j
  obtain ⟨n⟩ := j
  cases n with
  | zero =>
      let : Subsingleton (Q.obj (op 1)) := hQ 0
      have hs := ModuleCat.map_sectionsEval Q (show 0 ≤ 1 by decide) s
      have ht := ModuleCat.map_sectionsEval Q (show 0 ≤ 1 by decide) t
      exact hs.symm.trans
        ((congrArg (Q.map (homOfLE (show 0 ≤ 1 by decide)).op)
          (Subsingleton.elim (ModuleCat.sectionsEval Q 1 s)
            (ModuleCat.sectionsEval Q 1 t))).trans ht)
  | succ n =>
      let : Subsingleton (Q.obj (op (n + 1))) := hQ n
      exact Subsingleton.elim _ _

/-- Original proper coherent cohomology above the dimension of the actual
closed fibre vanishes over every Noetherian local base, without completeness. -/
theorem subsingleton_moduleCohomology_of_local_of_dim_firstThickening
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (d q : ℕ)
    (hdim : topologicalKrullDim
      (idealThickeningSpace f (IsLocalRing.maximalIdeal A)) ≤ d) (hq : d < q) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let I := IsLocalRing.maximalIdeal A
  have hstage (n : ℕ) :
      Subsingleton (idealThickeningCohomology f M (I ^ (n + 1)) q) := by
    let Yn := idealThickeningSpace f (I ^ (n + 1))
    let jn := idealThickeningι f (I ^ (n + 1))
    let : CompactSpace Yn := QuasiCompact.compactSpace_of_compactSpace (jn ≫ f)
    let : IsNoetherian Yn := { __ := LocallyOfFiniteType.isLocallyNoetherian (jn ≫ f) }
    let e : Yn ≃ₜ idealThickeningSpace f I :=
      jn.isClosedEmbedding.isEmbedding.toHomeomorph.trans
        ((Homeomorph.setCongr (by
          rw [range_actualThickening, range_actualThickening,
            PrimeSpectrum.zeroLocus_pow I (Nat.succ_ne_zero n)])).trans
          (idealThickeningι f I).isClosedEmbedding.isEmbedding.toHomeomorph.symm)
    have hn : topologicalKrullDim Yn ≤ d :=
      (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).le.trans hdim
    exact noetherianSheafCohomology_vanishing Yn
      (moduleAddSheaf Yn (idealThickeningCoefficient f M (I ^ (n + 1)))) d q hn hq
  let Q := properIdealThickeningCohomologyTower f M hM I q
  have hQ (n : ℕ) : Subsingleton (Q.obj (op (n + 1))) := by
    change Subsingleton (idealThickeningCohomology f M (I ^ (n + 1)) q)
    exact hstage n
  let : Subsingleton (ModuleCat.sectionsSubmodule Q) :=
    compatibleSections_subsingleton_of_positive Q hQ
  let H : ModuleCat.{u + 1} A :=
    (moduleCohomologyFunctorOfHom X (idealThickeningBaseScalar f) q).obj M
  let : Module.Finite A H := moduleCohomology_finite_of_proper A f M hM q
  let e := moduleCohomologyFormalFunctionsThickeningEquiv f M hM I q
  change Subsingleton H
  exact (e.injective.comp (AdicCompletion.of_injective I H)).subsingleton

/-- The same result in the original module category, using the unchanged
structural base-ring action on native cohomology. -/
theorem isZero_moduleCohomology_of_local_of_dim_firstThickening
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (d q : ℕ)
    (hdim : topologicalKrullDim
      (idealThickeningSpace f (IsLocalRing.maximalIdeal A)) ≤ d) (hq : d < q) :
    IsZero ((moduleCohomologyFunctorOfHom X (idealThickeningBaseScalar f) q).obj M) := by
  let : Subsingleton
      ((moduleCohomologyFunctorOfHom X (idealThickeningBaseScalar f) q).obj M) := by
    change Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)
    exact subsingleton_moduleCohomology_of_local_of_dim_firstThickening f M hM d q hdim hq
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry.Scheme.Cohomology
