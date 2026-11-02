/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification.SurfaceChain
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.ProjectiveEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GenericStalk.StructureTriangle
public import Aglib.AlgebraicGeometry.Descent.LocalModification.Dimension

/-!
# The same supplied local surface chain on a global projective model

The existing supported globalization retains the original local terminal
and Cartesian square. The existing chain embedding embeds that SAME global
terminal over the original ring. Dimension is transported through the actual
central-fibre and away-open stalk isomorphisms. Original function-field
composition derives finiteness for the new embedding's generic base map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.LocalModification

open Blowup

/-- A supplied proper local normalized chain with its genuine surface
bound globalizes to the SAME projectively embedded global modification.
The original Cartesian, structural and generic-field triangles and length
are retained. No regularity of either terminal or new generic-finiteness
hypothesis is introduced. -/
theorem exists_projective_surface_supported_normalizedChain
    (R : Type u) [CommRing R] [IsDomain R]
    (ι : Type u) [Finite ι]
    {X T : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ toSpec R ι)]
    (hfin : (genericImageBaseMap R ι i).Finite)
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p]
    (upper : NormalizedPointBlowupChain p) (hdT : topologicalKrullDim T ≤ 2) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (lower : NormalizedPointBlowupChain f)
      (a : T ⟶ Z) (hZ : IsIntegral Z),
      letI := hZ
      ∃ (hfD : IsDominant f),
        letI := hfD
        IsProper f ∧ NormalStalks Z ∧ IsNoetherian Z ∧
          topologicalKrullDim Z ≤ 2 ∧ lower.length = upper.length ∧
          IsPullback a p f (X.fromSpecStalk x) ∧
          a ≫ f = p ≫ X.fromSpecStalk x ∧
          IsIso (f ∣_ pointComplement x hx) ∧
          IsIso (CommRingCat.ofHom (functionFieldMap f)) ∧
          ∃ (m : ℕ) (k : Z ⟶ ProjectiveSpace R (ULift.{u} (Fin (m + 1)))),
            IsClosedImmersion k ∧
              ∃ (hkD : IsDominant (k ≫ toSpec R (ULift.{u} (Fin (m + 1))))),
                letI := hkD
                k ≫ toSpec R (ULift.{u} (Fin (m + 1))) = f ≫ i ≫ toSpec R ι ∧
                  genericImageBaseMap R (ULift.{u} (Fin (m + 1))) k =
                    (functionFieldMap f).comp (genericImageBaseMap R ι i) ∧
                  (genericImageBaseMap R (ULift.{u} (Fin (m + 1))) k).Finite := by
  obtain ⟨Z, f, lower, a, hfP, hlen, H, hfU⟩ :=
    exists_surface_supported_normalizedChain hX hdX x hx hxη p upper
  let hZ : IsIntegral Z := lower.isIntegral inferInstance
  let : IsIntegral Z := hZ
  let hfD : IsDominant f := lower.isDominant inferInstance
  let : IsDominant f := hfD
  let : IsProper f := hfP
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  have hZNoeth : IsNoetherian Z := ⟨⟩
  have hff : IsIso (CommRingCat.ofHom (functionFieldMap f)) :=
    lower.functionFieldMap_isIso inferInstance
  have hdZ : topologicalKrullDim Z ≤ 2 :=
    topologicalKrullDim_le_of_local_replacement x hx a p f H hfU 2 hdX hdT
  obtain ⟨m, k, hk, hbase⟩ := lower.exists_projective_embedding i
  have hkD : IsDominant (k ≫ toSpec R (ULift.{u} (Fin (m + 1)))) := by
    rw [hbase]
    infer_instance
  let : IsDominant (k ≫ toSpec R (ULift.{u} (Fin (m + 1)))) := hkD
  have hmap : genericImageBaseMap R (ULift.{u} (Fin (m + 1))) k =
      (functionFieldMap f).comp (genericImageBaseMap R ι i) :=
    genericImageBaseMap_eq_comp_of_structureTriangle
      R ι (ULift.{u} (Fin (m + 1))) f i k hbase
  have hkfinite : (genericImageBaseMap R (ULift.{u} (Fin (m + 1))) k).Finite :=
    genericImageBaseMap_finite_of_structureTriangle
      R ι (ULift.{u} (Fin (m + 1))) f i k hbase hff hfin
  exact ⟨Z, f, lower, a, hZ, hfD, hfP, lower.normalStalks hX, hZNoeth,
    hdZ, hlen, H, H.w, hfU, hff, m, k, hk, hkD, hbase, hmap, hkfinite⟩

end AlgebraicGeometry.Scheme.LocalModification
