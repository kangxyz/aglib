/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.CompleteBase
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Noetherian
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.Topology.KrullDimension.ClosedSubspace
public import Aglib.Algebra.Category.ModuleCat.NatTower
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Original proper cohomology above the closed-fibre dimension

The positive actual ideal thickenings have the same underlying space as the
first one. Noetherian dimension vanishing kills their original cohomology,
and the actual complete-base formal-functions equivalence kills the original
cohomology with its original structural scalar action. No coefficient
flatness or supplied cohomology comparison is assumed.

For an integral source of dimension at most two dominating a local domain
of dimension two, the actual closed fibre avoids the original generic point
and has dimension at most one. The resulting complete-base surface statement
retains both the original map and its actual source dimension bound.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u v

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original ideal-thickening immersion has the actual inverse-image
zero locus as its range. -/
private theorem range_idealThickeningι {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (I : Ideal A) :
    Set.range (idealThickeningι f I) = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
  change Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) = _
  rw [Scheme.Pullback.range_fst]
  have hspec : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  rw [hspec]

/-- Every positive thickening has the same underlying space as the actual
first thickening. This is a homeomorphism of spaces, not a scheme isomorphism. -/
private def positiveThickeningHomeomorph {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (I : Ideal A) (n : ℕ) :
    idealThickeningSpace f (I ^ (n + 1)) ≃ₜ idealThickeningSpace f I :=
  (idealThickeningι f (I ^ (n + 1))).isClosedEmbedding.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr (by
      rw [range_idealThickeningι, range_idealThickeningι,
        PrimeSpectrum.zeroLocus_pow I (Nat.succ_ne_zero n)])).trans
      (idealThickeningι f I).isClosedEmbedding.isEmbedding.toHomeomorph.symm)

/-- Positive coordinates force the whole original compatible-family module
to vanish: coordinate zero is its actual transition from coordinate one. -/
private theorem sectionsSubmodule_subsingleton_of_positive
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

/-- Original coherent cohomology above the dimension of the actual first
ideal thickening vanishes over a complete Noetherian base. No coefficient
flatness or supplied cohomology comparison is assumed. -/
theorem subsingleton_moduleCohomology_of_complete_of_dim_firstThickening
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (d q : ℕ)
    (hdim : topologicalKrullDim (idealThickeningSpace f I) ≤ d) (hq : d < q) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  have hstage (n : ℕ) :
      Subsingleton (idealThickeningCohomology f M (I ^ (n + 1)) q) := by
    let Yn := idealThickeningSpace f (I ^ (n + 1))
    let jn := idealThickeningι f (I ^ (n + 1))
    let : CompactSpace Yn := QuasiCompact.compactSpace_of_compactSpace (jn ≫ f)
    let : IsNoetherian Yn := { __ := LocallyOfFiniteType.isLocallyNoetherian (jn ≫ f) }
    have hn : topologicalKrullDim Yn ≤ d :=
      (IsHomeomorph.topologicalKrullDim_eq
        (positiveThickeningHomeomorph f I n)
        (positiveThickeningHomeomorph f I n).isHomeomorph).le.trans hdim
    exact noetherianSheafCohomology_vanishing Yn
      (moduleAddSheaf Yn (idealThickeningCoefficient f M (I ^ (n + 1)))) d q hn hq
  let Q := properIdealThickeningCohomologyTower f M hM I q
  have hQ (n : ℕ) : Subsingleton (Q.obj (op (n + 1))) := by
    change Subsingleton (idealThickeningCohomology f M (I ^ (n + 1)) q)
    exact hstage n
  let : Subsingleton (ModuleCat.sectionsSubmodule Q) :=
    sectionsSubmodule_subsingleton_of_positive Q hQ
  let e := moduleCohomologyFormalFunctionsCompleteThickeningEquiv I f M hM q
  constructor
  intro x y
  exact e.injective (Subsingleton.elim _ _)

/-- The same vanishing is zero in the module category for the original
structural ring action, as needed by the actual derived-image consumer. -/
theorem isZero_moduleCohomology_of_complete_of_dim_firstThickening
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (d q : ℕ)
    (hdim : topologicalKrullDim (idealThickeningSpace f I) ≤ d) (hq : d < q) :
    IsZero ((moduleCohomologyFunctorOfHom X (idealThickeningBaseScalar f) q).obj M) := by
  let : Subsingleton
      ((moduleCohomologyFunctorOfHom X (idealThickeningBaseScalar f) q).obj M) := by
    change Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)
    exact subsingleton_moduleCohomology_of_complete_of_dim_firstThickening I f M hM d q hdim hq
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual closed fibre misses the original source generic point, so
its underlying closed subset has dimension at most one. -/
theorem closedFibre_dim_le_one_of_integral_source
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsDominant f]
    (hdX : topologicalKrullDim X ≤ 2)
    (hne : (IsLocalRing.closedPoint A : Spec (.of A)) ≠ genericPoint (Spec (.of A))) :
    topologicalKrullDim (idealThickeningSpace f (IsLocalRing.maximalIdeal A)) ≤ 1 := by
  let Z : Set X := f ⁻¹' {IsLocalRing.closedPoint A}
  have hclosed : IsClosed Z :=
    (IsLocalRing.isClosed_singleton_closedPoint A).preimage f.continuous
  have havoid : Disjoint Z (genericPoints X) := by
    rw [genericPoints_eq_singleton, Set.disjoint_singleton_right]
    change f (genericPoint X) ≠ IsLocalRing.closedPoint A
    rw [map_genericPoint_of_isDominant X f]
    exact hne.symm
  have hdZ : topologicalKrullDim Z ≤ 1 :=
    topologicalKrullDim_closed_le_of_avoids_genericPoints Z hclosed havoid 1 hdX
  have hrange : Set.range (idealThickeningι f (IsLocalRing.maximalIdeal A)) = Z := by
    rw [range_idealThickeningι, PrimeSpectrum.zeroLocus_eq_singleton]
    rfl
  let embedding :=
    (idealThickeningι f (IsLocalRing.maximalIdeal A)).isClosedEmbedding.isEmbedding
  let e : idealThickeningSpace f (IsLocalRing.maximalIdeal A) ≃ₜ Z :=
    (embedding.toHomeomorph).trans (Homeomorph.setCongr hrange)
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).le.trans hdZ

/-- In dimension two the closed point of the original local domain is not
its generic point. This retains the original closed stalk comparison. -/
private theorem closedPoint_ne_generic_of_ringKrullDim_two
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] (hdA : ringKrullDim A = 2) :
    (IsLocalRing.closedPoint A : Spec (.of A)) ≠ genericPoint (Spec (.of A)) := by
  intro he
  have hf : IsField ((Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) :=
    he.symm ▸ Field.toIsField (Spec (.of A)).functionField
  have hA : IsField A := (stalkClosedPointIso (.of A)).symm.commRingCatIsoToRingEquiv.isField hf
  have hh := ringKrullDim_eq_zero_of_isField hA
  rw [hdA] at hh
  norm_num at hh

/-- Above degree one, original coherent cohomology on the actual integral
surface modification vanishes over the complete local two-dimensional base.
The proof needs the actual source dimension bound, not only target dimension. -/
theorem subsingleton_moduleCohomology_of_complete_surface_modification
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hdA : ringKrullDim A = 2) (hdX : topologicalKrullDim X ≤ 2)
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) :=
  subsingleton_moduleCohomology_of_complete_of_dim_firstThickening
    (IsLocalRing.maximalIdeal A) f M hM 1 q
    (closedFibre_dim_le_one_of_integral_source f hdX
      (closedPoint_ne_generic_of_ringKrullDim_two A hdA)) hq

end AlgebraicGeometry.Scheme.Cohomology
