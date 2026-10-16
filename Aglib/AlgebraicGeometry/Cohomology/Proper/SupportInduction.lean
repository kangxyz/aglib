/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.CoherentSupport
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ClosedImmersion.Descent
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Modification.Support
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov

/-!
# The closed-support step for proper coherent-image induction

An explicit smaller-support induction hypothesis applies to actual closed
immersions and coherent coefficients on their sources. Each coherent
module supported in the prescribed closed set descends directly to one
positive power of its native vanishing ideal. Original closed derived
descent transfers the conclusion, and the sole finite Postnikov theorem
then handles bounded coherent objects with that homology support. This
is an induction step, not an unconditional proper-finiteness theorem.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The installed standard ambient derived category of actual module sheaves. -/
local instance supportInductionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {X S : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian S]
  (f : X ⟶ S) (T : Closeds X)

/-- Direct positive ideal-power descent applies a smaller-support closed-image
induction hypothesis to the original supported coherent single. -/
theorem coherent_derivedSingle_of_closed_support
    (hsmall : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i],
      Set.range i ⊆ T → ∀ (N : Z.Modules), affineLocallyFiniteType Z N → ∀ k : ℤ,
        coherentHomologyObjects S ((derivedPushforwardPlus (i ≫ f)).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj N)))
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (hs : support M ⊆ T) (k : ℤ) :
    coherentHomologyObjects S ((derivedPushforwardPlus f).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules k).obj M)) := by
  let J : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T
  have hsJ : support M ⊆ J.support := hs
  obtain ⟨n, hn, hkill⟩ :=
    exists_pos_pow_killedByIdealSheaf_of_coherent_support J M hM hsJ
  let i := (J ^ n).subschemeι
  have hker : killedByIdealSheaf i.ker M := by
    change killedByIdealSheaf (J ^ n).subschemeι.ker M
    rwa [(J ^ n).ker_subschemeι]
  have hi : Set.range i ⊆ T := by
    rw [Scheme.IdealSheafData.range_subschemeι, J.support_pow n (Nat.ne_zero_of_lt hn)]
    exact Set.Subset.rfl
  have hN := affineLocallyFiniteType_pullback i hM
  have hIH := hsmall (J ^ n).subscheme i hi ((Scheme.Modules.pullback i).obj M) hN k
  exact (coherentHomologyObjects S).prop_of_iso
    (closedImmersionDerivedDescentIso i f M hker k).symm hIH

/-- The same explicit smaller-support induction hypothesis handles every bounded
coherent object supported there, using its actual homology layers alone. -/
theorem coherent_derived_of_closed_support
    (hsmall : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i],
      Set.range i ⊆ T → ∀ (N : Z.Modules), affineLocallyFiniteType Z N → ∀ k : ℤ,
        coherentHomologyObjects S ((derivedPushforwardPlus (i ≫ f)).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj N)))
    (K : DerivedCategory.Plus X.Modules) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : coherentHomologyObjects X K)
    (hs : ∀ k : ℤ, support ((DerivedCategory.Plus.homologyFunctor X.Modules k).obj K) ⊆ T) :
    coherentHomologyObjects S ((derivedPushforwardPlus f).obj K) := by
  let F := (pushforward f).rightDerivedFunctorPlus
  let P := (coherentHomologyObjects S).inverseImage F
  apply DerivedCategory.Plus.property_of_homology_bounds P K a b
  intro k _ _
  exact coherent_derivedSingle_of_closed_support f T hsmall
    ((DerivedCategory.Plus.homologyFunctor X.Modules k).obj K) (hK k) (hs k) k

omit T in
/-- The actual original modification triangle reduces coherent direct image
of a coefficient to the two proved modification images and a smaller closed
boundary. This is the explicit induction step used by proper finiteness. -/
theorem coherent_derivedSingle_of_modification
    {Y : Scheme.{u}} (π : Y ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)]
    (hsmall : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i],
      Set.range i ⊆ (U : Set X)ᶜ → ∀ (N : Z.Modules), affineLocallyFiniteType Z N → ∀ k : ℤ,
        coherentHomologyObjects S ((derivedPushforwardPlus (i ≫ f)).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj N)))
    (M : X.Modules) (hM : affineLocallyFiniteType X M)
    (hπ : coherentHomologyObjects X ((derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((Scheme.Modules.pullback π).obj M))))
    (N : ℕ) [((derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pullback π).obj M))).IsLE (N : ℤ)]
    (hfπ : coherentHomologyObjects S ((derivedPushforwardPlus (π ≫ f)).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pullback π).obj M)))) :
    coherentHomologyObjects S ((derivedPushforwardPlus f).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
  obtain ⟨C, v, w, hT, hC, hGE, hLE, hs⟩ :=
    exists_ordinaryModificationCone_bounded_coherent π M hM hπ N U
  let : C.IsGE (-1) := hGE
  let : C.IsLE (N : ℤ) := hLE
  have hCf : coherentHomologyObjects S ((derivedPushforwardPlus f).obj C) :=
    coherent_derived_of_closed_support f U.compl hsmall C (-1) N hC hs
  let F := (pushforward f).rightDerivedFunctorPlus
  let T := Triangle.mk (ordinaryModificationUnit π M) v w
  have hB : coherentHomologyObjects S (F.obj ((derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pullback π).obj M)))) :=
    (coherentHomologyObjects S).prop_of_iso
      ((derivedPushforwardPlusCompIso π f).app
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
          ((Scheme.Modules.pullback π).obj M))) hfπ
  exact (coherentHomologyObjects S).ext_of_isTriangulatedClosed₁
    (F.mapTriangle.obj T) (F.map_distinguished T hT) hB hCf

end AlgebraicGeometry.Scheme.Cohomology
