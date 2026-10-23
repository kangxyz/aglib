/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.ChowDomination
public import Aglib.AlgebraicGeometry.Surfaces.Birational.ProjectiveDomination.Chain
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.ProperProjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ClosedComposition

/-!
# Projectivity of regular proper surfaces over an affine base

The original proper morphism has a projective Chow modification dominated by
actual point blowups. The literal base change of that chain is projective by
the full tensor-Rees construction. Its closed comparison graph embeds the top
stage, and reverse contraction transfers its presentation to the original
regular scheme. Every embedding retains the original affine-base map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Surfaces

/-- A regular integral Noetherian scheme of dimension at most two, proper over
a Noetherian affine scheme, has an actual finite projective embedding over its
original proper map. No ample bundle or projective presentation is an input. -/
theorem exists_projective_embedding_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (hX : RegularStalks X) (hd : topologicalKrullDim X ≤ 2)
    (q : X ⟶ Spec (.of A)) [IsProper q] :
    ∃ (J : Type u) (p : X ⟶ ProjectiveSpace A J),
      Finite J ∧ IsClosedImmersion p ∧ p ≫ toSpec A J = q := by
  obtain ⟨W, π, n, j, V, hV, hiso, hπ, hπsurj, hj, hjbase, Y, β, c, hout⟩ :=
    Birational.exists_pointBlowupChain_chowDomination hX hd q
  let : IsIntegral Y := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  let : IsProper π := hπ
  let : IsClosedImmersion j := hj
  obtain ⟨a, h, hβ, hbir, hYN, hYR, hYD, haπ, haj, hhbase, habase, haη, hhη⟩ := hout
  obtain ⟨J, hJ, k, hk, hkbase⟩ := c.exists_projective_embedding_pullback π j
  let : Finite J := hJ
  let : IsClosedImmersion k := hk
  apply Contraction.exists_projective_embedding_of_projective_pullback c hX q π a haπ k
  calc
    k ≫ toSpec A J = pullback.snd β π ≫ j ≫ toSpec A (ULift.{u} (Fin (n + 1))) := hkbase
    _ = pullback.snd β π ≫ π ≫ q := by rw [hjbase]

/-- The original nonempty scheme has an embedding into finite positive standard
coordinates; the nonempty coordinate set is derived from its actual map. -/
theorem exists_standard_projective_embedding_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (hX : RegularStalks X) (hd : topologicalKrullDim X ≤ 2)
    (q : X ⟶ Spec (.of A)) [IsProper q] :
    ∃ (n : ℕ) (p : X ⟶ ProjectiveSpace A (ULift.{u} (Fin (n + 1)))),
      IsClosedImmersion p ∧ p ≫ toSpec A (ULift.{u} (Fin (n + 1))) = q := by
  classical
  obtain ⟨J, p, hJ, hp, hbase⟩ := exists_projective_embedding_of_isProper hX hd q
  let : Finite J := hJ
  let : IsClosedImmersion p := hp
  let : Nonempty J := Segre.nonempty_coordinates_of_nonempty_source A p
  let : Fintype J := Fintype.ofFinite J
  let n := Fintype.card J - 1
  have hc : Fintype.card J = n + 1 := (Nat.sub_add_cancel Fintype.card_pos).symm
  let e : J ≃ ULift.{u} (Fin (n + 1)) :=
    (Fintype.equivFinOfCardEq hc).trans Equiv.ulift.symm
  refine ⟨n, p ≫ (reindexIso A e).hom, inferInstance, ?_⟩
  have he := reindexIso_hom_toSpec A e
  change (reindexIso A e).hom ≫ toSpec A (ULift.{u} (Fin (n + 1))) = toSpec A J at he
  rw [Category.assoc, he, hbase]

end AlgebraicGeometry.Scheme.Surfaces
