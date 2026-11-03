/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.SupportedStages
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.ProjectiveEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GenericStalk.StructureTriangle

/-!
# Projective embeddings of the actual strict interior stages

The original proper prefix chain embeds each SAME interior scheme over the
original ring. Native structural and function-field triangles derive its
finite generic-image extension. The two endpoint embeddings remain outside
this choice family, so a length-zero chain never identifies them.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain

/-- A zero-length native chain has an invertible ORIGINAL structural map.
This does not identify any two projective embeddings of its endpoints. -/
theorem isIso_of_length_eq_zero
    {Z X : Scheme.{u}} {f : Z ⟶ X} (c : NormalizedPointBlowupChain f)
    (h : c.length = 0) : IsIso f := by
  cases c with
  | refl X => infer_instance
  | cons x hx hne g tail =>
    change tail.length + 1 = 0 at h
    omega

/-- Choose one finite-coordinate embedding of each STRICT interior stage.
The schemes, prefix maps and field maps are exactly the native accessors.
Original endpoint embeddings are not replaced, even when the chain is empty.
No regularity, normality, dimension or Nagata hypothesis is needed. -/
theorem exists_interior_projective_embeddings
    (R : Type u) [CommRing R] [IsDomain R]
    {Z X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : Z ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    {ι : Type u} [Finite ι]
    (j : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion j]
    [IsDominant (j ≫ toSpec R ι)]
    (hfin : (genericImageBaseMap R ι j).Finite) :
    let I := {i : Fin (c.length + 1) // 0 < i.val ∧ i.val < c.length}
    letI (i : Fin (c.length + 1)) : IsIntegral (c.stage i) :=
      (c.«prefix» i).isIntegral inferInstance
    letI (i : Fin (c.length + 1)) : IsDominant (c.toBase i) :=
      (c.«prefix» i).isDominant inferInstance
    ∃ (n : I → ℕ)
      (k : ∀ i : I, c.stage i.val ⟶ ProjectiveSpace R (ULift.{u} (Fin (n i + 1)))),
      ∀ i : I, IsClosedImmersion (k i) ∧
        ∃ hkD : IsDominant (k i ≫ toSpec R (ULift.{u} (Fin (n i + 1)))),
          letI := hkD
          k i ≫ toSpec R (ULift.{u} (Fin (n i + 1))) =
              c.toBase i.val ≫ j ≫ toSpec R ι ∧
            genericImageBaseMap R (ULift.{u} (Fin (n i + 1))) (k i) =
              (functionFieldMap (c.toBase i.val)).comp (genericImageBaseMap R ι j) ∧
            (genericImageBaseMap R (ULift.{u} (Fin (n i + 1))) (k i)).Finite := by
  classical
  let I := {i : Fin (c.length + 1) // 0 < i.val ∧ i.val < c.length}
  let (i : Fin (c.length + 1)) : IsIntegral (c.stage i) :=
    (c.«prefix» i).isIntegral inferInstance
  let (i : Fin (c.length + 1)) : IsDominant (c.toBase i) :=
    (c.«prefix» i).isDominant inferInstance
  have h (i : I) :
      ∃ (n : ℕ) (k : c.stage i.val ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))),
        IsClosedImmersion k ∧
          ∃ hkD : IsDominant (k ≫ toSpec R (ULift.{u} (Fin (n + 1)))),
            letI := hkD
            k ≫ toSpec R (ULift.{u} (Fin (n + 1))) =
                c.toBase i.val ≫ j ≫ toSpec R ι ∧
              genericImageBaseMap R (ULift.{u} (Fin (n + 1))) k =
                (functionFieldMap (c.toBase i.val)).comp (genericImageBaseMap R ι j) ∧
              (genericImageBaseMap R (ULift.{u} (Fin (n + 1))) k).Finite := by
    let : IsProper (c.toBase i.val) := (c.isProper_toBase_and_fromTop i.val).1
    obtain ⟨n, k, hk, hbase⟩ := (c.«prefix» i.val).exists_projective_embedding j
    have hkD : IsDominant (k ≫ toSpec R (ULift.{u} (Fin (n + 1)))) := by
      rw [hbase]
      infer_instance
    let : IsDominant (k ≫ toSpec R (ULift.{u} (Fin (n + 1)))) := hkD
    have hmap := genericImageBaseMap_eq_comp_of_structureTriangle
      R ι (ULift.{u} (Fin (n + 1))) (c.toBase i.val) j k hbase
    have hkfinite := genericImageBaseMap_finite_of_structureTriangle
      R ι (ULift.{u} (Fin (n + 1))) (c.toBase i.val) j k hbase
        ((c.«prefix» i.val).functionFieldMap_isIso inferInstance) hfin
    exact ⟨n, k, hk, hkD, hbase, hmap, hkfinite⟩
  choose n k hk using h
  exact ⟨n, k, hk⟩

end AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain
