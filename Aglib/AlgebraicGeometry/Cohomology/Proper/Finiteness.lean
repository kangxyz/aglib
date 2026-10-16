/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Chow
public import Aglib.AlgebraicGeometry.Cohomology.Proper.SupportInduction
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Mathlib.Topology.NoetherianSpace

/-!
# Coherent actual proper direct images over a Noetherian affine base

Well-founded induction on closed subsets of a fixed ambient proper source
quantifies every actual closed subscheme with range in that subset. The
proved coefficient-independent Chow modification and original ordinary
modification triangle reduce the claim to a strictly smaller closed
boundary. Supported coherent homology descends directly to positive ideal
powers through the original closed derived comparison and shared finite
Postnikov argument. Every induction hypothesis is discharged internally.
No proper-finiteness, Chow or cohomology theorem family is a premise.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The installed standard ambient derived category of actual module sheaves. -/
local instance properFinitenessStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- Every coherent coefficient on an actual closed subscheme of a proper
Noetherian-affine source has coherent original derived direct image in every
integer single placement. The closed-support induction is internal. -/
theorem proper_closed_derivedSingle_coherent
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {W : Scheme.{u}} (j : W ⟶ X) [IsClosedImmersion j]
    (M : W.Modules) (hM : affineLocallyFiniteType W M) (k : ℤ) :
    coherentHomologyObjects (Spec (.of R)) ((derivedPushforwardPlus (j ≫ f)).obj
      ((DerivedCategory.Plus.singleFunctor W.Modules k).obj M)) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  have hP : ∀ Z : Closeds X, ∀ (W : Scheme.{u}) (j : W ⟶ X) [IsClosedImmersion j],
      Set.range j ⊆ Z → ∀ (M : W.Modules), affineLocallyFiniteType W M → ∀ k : ℤ,
        coherentHomologyObjects (Spec (.of R)) ((derivedPushforwardPlus (j ≫ f)).obj
          ((DerivedCategory.Plus.singleFunctor W.Modules k).obj M)) := by
    intro Z
    apply wellFounded_lt.induction Z
    intro Z ih W j _ hj M hM k
    by_cases hW : Nonempty W
    · let : Nonempty W := hW
      let : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (j ≫ f)
      let : IsNoetherian W := { __ := LocallyOfFiniteType.isLocallyNoetherian (j ≫ f) }
      obtain ⟨m, σ, hσ, Y, π, q, U, comm, hproper, hsurj, hq, hdense, hiso, hpair, hcoh⟩ :=
        exists_chowModification_cohomology R (j ≫ f)
      let : ∀ i, Fintype (σ i) := hσ
      let : IsIso (π ∣_ U) := hiso
      let B : Closeds X :=
        ⟨j '' (U : Set W)ᶜ, j.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hB : B < Z := by
        apply lt_of_le_of_ne
        · rintro x ⟨w, hw, rfl⟩
          exact hj ⟨w, rfl⟩
        · intro heq
          obtain ⟨w, hw⟩ := hdense.nonempty
          have hx : j w ∈ B := by
            rw [heq]
            exact hj ⟨w, rfl⟩
          obtain ⟨w', hw', he⟩ := hx
          have he' : w' = w := j.isClosedEmbedding.injective he
          subst w'
          exact hw' hw
      have hsmall : ∀ (Z' : Scheme.{u}) (i : Z' ⟶ W) [IsClosedImmersion i],
          Set.range i ⊆ (U : Set W)ᶜ → ∀ (N : Z'.Modules), affineLocallyFiniteType Z' N →
            ∀ l : ℤ, coherentHomologyObjects (Spec (.of R))
              ((derivedPushforwardPlus (i ≫ (j ≫ f))).obj
                ((DerivedCategory.Plus.singleFunctor Z'.Modules l).obj N)) := by
        intro Z' i _ hi N hN l
        have hirange : Set.range (i ≫ j) ⊆ B := by
          rintro x ⟨z, rfl⟩
          exact ⟨i z, hi ⟨z, rfl⟩, rfl⟩
        simpa only [Category.assoc] using ih B hB Z' (i ≫ j) hirange N hN l
      have hM' := affineLocallyFiniteType_pullback π hM
      obtain ⟨hπ, hfπ, hfinite⟩ := hcoh ((Scheme.Modules.pullback π).obj M) hM'
      let N : ℕ := ∑ i, Fintype.card (σ i)
      let : ((derivedPushforwardPlus π).obj
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
            ((Scheme.Modules.pullback π).obj M))).IsLE (N : ℤ) := by
        simpa only [N, Nat.cast_sum, zero_add] using (hπ 0).2.2
      have hzero : coherentHomologyObjects (Spec (.of R))
          ((derivedPushforwardPlus (j ≫ f)).obj
            ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj M)) :=
        coherent_derivedSingle_of_modification (j ≫ f) π U hsmall M hM (hπ 0).1 N (hfπ 0).1
      let F := (pushforward (j ≫ f)).rightDerivedFunctorPlus
      let A := (DerivedCategory.Plus.singleFunctor W.Modules 0).obj M
      let E : (F.obj A)⟦-k⟧ ≅
          F.obj ((DerivedCategory.Plus.singleFunctor W.Modules k).obj M) :=
        (((DerivedCategory.Plus.singleFunctors W.Modules).postcomp F).shiftIso
          (-k) k 0 (by omega)).app M
      exact (coherentHomologyObjects (Spec (.of R))).prop_of_iso E
        (coherentHomologyObjects_shift (Spec (.of R)) (F.obj A) hzero (-k))
    · have : IsEmpty W := not_nonempty_iff.mp hW
      have hzero : IsZero M := (isZero_iff_stalks M).mpr (fun x => isEmptyElim x)
      exact (coherentHomologyObjects (Spec (.of R))).prop_of_isZero
        ((pushforward (j ≫ f)).rightDerivedFunctorPlus.map_isZero
          ((DerivedCategory.Plus.singleFunctor W.Modules k).map_isZero hzero))
  exact hP ⊤ W j (by simp) M hM k

/-- An actual proper direct image over a Noetherian affine base has coherent
native homology on every coherent coefficient in any integer single degree. -/
theorem proper_derivedSingle_coherent
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (k : ℤ) :
    coherentHomologyObjects (Spec (.of R)) ((derivedPushforwardPlus f).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules k).obj M)) := by
  simpa only [Category.id_comp] using proper_closed_derivedSingle_coherent R f (𝟙 X) M hM k

/-- Every original native higher direct image of a coherent coefficient
under a proper morphism to a Noetherian affine base is coherent. -/
theorem proper_higherDirectImage_coherent
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (q : ℕ) :
    affineLocallyFiniteType (Spec (.of R)) (((pushforward f).rightDerived q).obj M) :=
  (affineLocallyFiniteType (Spec (.of R))).prop_of_iso
    (((pushforward f).rightDerivedSingleHomologyIso q).app M).symm
    (proper_derivedSingle_coherent R f M hM 0 q)

/-- Original cohomology of a coherent coefficient on a proper scheme over
a Noetherian ring is finite, with its unchanged structural ring action. -/
theorem moduleCohomology_finite_of_proper
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (q : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α M q
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  have hN := proper_higherDirectImage_coherent R f M hM q
  let : Module.Finite R
      (moduleSpecΓFunctor.obj (((pushforward f).rightDerived q).obj M)) :=
    ((affineLocallyFiniteType_spec_iff (.of R) _).mp hN).2
  exact Module.Finite.equiv (moduleHigherDirectImageAffineSectionsLinearEquiv f M
    (injectiveResolution M) q)

end AlgebraicGeometry.Scheme.Cohomology
