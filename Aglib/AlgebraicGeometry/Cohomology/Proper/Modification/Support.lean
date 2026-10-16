/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Modification.Restriction
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Coherent.Single
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Coherent.Shift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure

/-!
# Homology support and bounds of the actual modification triangle

Any actual distinguished triangle on the original ordinary modification
map becomes zero in its third object after restriction to the isomorphism
locus. Exact native restriction and the original homology comparison
therefore place every native homology sheaf of that third object on the
closed boundary. Its lower bound is minus one, without assuming the
ordinary adjunction unit is monic. Coherence and an upper bound are
transported from the actual derived image by the native triangle.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The installed standard ambient derived category of actual module sheaves. -/
local instance modificationSupportStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {Y X : Scheme.{u}} (π : Y ⟶ X) (M : X.Modules)

section Triangle

variable
  (C : DerivedCategory.Plus X.Modules)
  (v : (derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M)) ⟶ C)
  (w : C ⟶ ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)⟦(1 : ℤ)⟧)
  (hT : Triangle.mk (ordinaryModificationUnit π M) v w ∈ distTriang _)

include hT

/-- The actual third object of a modification triangle vanishes after
native restriction to an open on which the morphism is an isomorphism. -/
theorem ordinaryModificationCone_restrict_isZero (U : X.Opens) [IsIso (π ∣_ U)] :
    IsZero ((restrictFunctor U.ι).rightDerivedFunctorPlus.obj C) := by
  let F := (restrictFunctor U.ι).rightDerivedFunctorPlus
  let T := Triangle.mk (ordinaryModificationUnit π M) v w
  have hF : F.mapTriangle.obj T ∈ distTriang _ := F.map_distinguished T hT
  exact (F.mapTriangle.obj T).isZero₃_of_isIso₁ hF
    (ordinaryModificationUnit_restrict_isIso π U M)

/-- Every original homology sheaf of the actual modification cone is
supported in the closed complement of the native isomorphism locus. -/
theorem ordinaryModificationCone_homology_support_subset
    (U : X.Opens) [IsIso (π ∣_ U)] (i : ℤ) :
    support ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj C) ⊆ (U : Set X)ᶜ := by
  let J := restrictFunctor U.ι
  have hC := ordinaryModificationCone_restrict_isZero π M C v w hT U
  have hH := (DerivedCategory.Plus.homologyFunctor U.toScheme.Modules i).map_isZero hC
  have hres : IsZero (J.obj ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj C)) :=
    hH.of_iso (((J.rightDerivedFunctorPlusHomologyIso i).app C).symm)
  have hs := (supportedAway_iff_support_disjoint U.ι
    ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj C)).mp hres
  intro x hx hxU
  exact Set.disjoint_left.mp hs hx ⟨⟨x, hxU⟩, rfl⟩

/-- The actual modification cone has the precise possible lower bound minus one. -/
theorem ordinaryModificationCone_isGE : C.IsGE (-1) := by
  let T := Triangle.mk (ordinaryModificationUnit π M) v w
  let t := DerivedCategory.Plus.TStructure.t (C := X.Modules)
  let B := (derivedPushforwardPlus π).obj
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M))
  let A := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M
  let : B.IsGE 0 := (pushforward π).rightDerivedFunctorPlus_isGE
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M)) 0
  let : (A⟦(1 : ℤ)⟧).IsGE (-1) := t.isGE_shift A 0 1 (-1) (by omega)
  apply t.isGE₂ T.rotate (rot_of_distTriang T hT) (-1)
  · change B.IsGE (-1)
    exact t.isGE_of_ge B (-1) 0 (by omega)
  · change (A⟦(1 : ℤ)⟧).IsGE (-1)
    infer_instance

/-- An actual upper bound on the derived pulled coefficient is retained by
the modification cone. No monomorphism of the ordinary unit is assumed. -/
theorem ordinaryModificationCone_isLE (N : ℕ)
    [((derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M))).IsLE
        (N : ℤ)] : C.IsLE (N : ℤ) := by
  let T := Triangle.mk (ordinaryModificationUnit π M) v w
  let t := DerivedCategory.Plus.TStructure.t (C := X.Modules)
  let A := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M
  let : (A⟦(1 : ℤ)⟧).IsLE (-1) := t.isLE_shift A 0 1 (-1) (by omega)
  apply t.isLE₂ T.rotate (rot_of_distTriang T hT) N
  · change ((derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M))).IsLE (N : ℤ)
    infer_instance
  · change (A⟦(1 : ℤ)⟧).IsLE (N : ℤ)
    exact t.isLE_of_le (A⟦(1 : ℤ)⟧) (-1) N (by omega)

/-- Coherent native homology of the original coefficient and of its actual
derived image gives coherent native homology of the same modification cone. -/
theorem ordinaryModificationCone_coherent [IsLocallyNoetherian X]
    (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (hB : coherentHomologyObjects X ((derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M)))) :
    coherentHomologyObjects X C :=
  (coherentHomologyObjects X).ext_of_isTriangulatedClosed₃
    (Triangle.mk (ordinaryModificationUnit π M) v w) hT
    (coherentHomologyObjects_single X M hM 0) hB

end Triangle

/-- The native distinguished cocone of the original map supplies an actual
bounded coherent third object supported on the closed isomorphism boundary. -/
theorem exists_ordinaryModificationCone_bounded_coherent [IsLocallyNoetherian X]
    (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (hB : coherentHomologyObjects X ((derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M))))
    (N : ℕ) [((derivedPushforwardPlus π).obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M))).IsLE (N : ℤ)]
    (U : X.Opens) [IsIso (π ∣_ U)] :
    ∃ (C : DerivedCategory.Plus X.Modules)
      (v : (derivedPushforwardPlus π).obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M)) ⟶ C)
      (w : C ⟶ ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)⟦(1 : ℤ)⟧),
      Triangle.mk (ordinaryModificationUnit π M) v w ∈ distTriang _ ∧
        coherentHomologyObjects X C ∧ C.IsGE (-1) ∧ C.IsLE (N : ℤ) ∧
          ∀ i : ℤ, support ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj C) ⊆
            (U : Set X)ᶜ := by
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle (ordinaryModificationUnit π M)
  exact ⟨C, v, w, hT, ordinaryModificationCone_coherent π M C v w hT hM hB,
    ordinaryModificationCone_isGE π M C v w hT,
    ordinaryModificationCone_isLE π M C v w hT N,
    ordinaryModificationCone_homology_support_subset π M C v w hT U⟩

end AlgebraicGeometry.Scheme.Modules
