/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.PointBlowupComparison
public import Aglib.AlgebraicGeometry.Surfaces.Birational.ProjectiveDomination
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.Principalization

/-!
# Descending projective embeddings through the original point-blowup chain

The projective presentation at the top of an actual finite point-blowup chain
descends to its original regular target over the same affine base. The induction
uses the actual reverse-one-blowup comparison, keeping every structural triangle.
The separate forward construction must still supply the top presentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

open Blowup Blowup.RegularPoint

private theorem pointBlowup_noetherian {X : Scheme.{u}} [IsNoetherian X] (x : X) :
    IsNoetherian (pointBlowup X x) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsLocallyNoetherian B.Y := B.isLocallyNoetherian
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : CompactSpace B.Y := QuasiCompact.compactSpace_of_compactSpace B.map
  change IsNoetherian B.Y
  exact ⟨⟩

private theorem point_ne_generic {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) : x ≠ genericPoint X := by
  intro h
  subst x
  change ringKrullDim X.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

private theorem embedding_descends {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} {β : Y ⟶ X} (c : PointBlowupChain β) :
    ∀ [IsIntegral X] [IsNoetherian X], RegularStalks X →
      ∀ (q : X ⟶ Spec (.of A)) {I : Type u} [Finite I]
        (j : Y ⟶ ProjectiveSpace A I) [IsClosedImmersion j],
        j ≫ toSpec A I = β ≫ q →
        ∃ (J : Type u) (p : X ⟶ ProjectiveSpace A J),
          Finite J ∧ IsClosedImmersion p ∧ p ≫ toSpec A J = q := by
  induction c with
  | refl X =>
      intro _ _ hX q I hI j hj hbase
      exact ⟨I, j, hI, hj, by simpa only [Category.id_comp] using hbase⟩
  | @cons X Y x hx hd g tail ih =>
      intro hInt hNoeth hX q I hI j hj hbase
      let : IsIntegral (pointBlowup X x) :=
        pointBlowup_isIntegral X x hx (point_ne_generic x hd)
      let : IsNoetherian (pointBlowup X x) := pointBlowup_noetherian x
      have hregular := regularStalks_pointBlowup X hX x hx hd
      obtain ⟨J, p, hJ, hp, hpbase⟩ :=
        ih hregular (pointBlowdown X x ≫ q) j
          (by simpa only [Category.assoc] using hbase)
      let : Finite J := hJ
      let : IsClosedImmersion p := hp
      exact exists_projective_embedding_of_pointBlowup hX x hx hd q p hpbase

/-- A projective presentation of the top of the specified regular point-blowup
chain descends to the original target, retaining the original affine-base map. -/
theorem exists_projective_embedding_of_pointBlowupChain
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    {β : Y ⟶ X} (c : PointBlowupChain β) (hX : RegularStalks X)
    (q : X ⟶ Spec (.of A)) {I : Type u} [Finite I]
    (j : Y ⟶ ProjectiveSpace A I) [IsClosedImmersion j]
    (hbase : j ≫ toSpec A I = β ≫ q) :
    ∃ (J : Type u) (p : X ⟶ ProjectiveSpace A J),
      Finite J ∧ IsClosedImmersion p ∧ p ≫ toSpec A J = q :=
  embedding_descends c hX q j hbase

/-- An actual projective presentation of the literal pullback along a separated
modification supplies the top presentation through its closed comparison graph.
Descending the original chain then retains the original target and base map. -/
theorem exists_projective_embedding_of_projective_pullback
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X Y W : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    {β : Y ⟶ X} (c : PointBlowupChain β) (hX : RegularStalks X)
    (q : X ⟶ Spec (.of A)) (π : W ⟶ X) [IsSeparated π]
    (a : Y ⟶ W) (ha : a ≫ π = β) {I : Type u} [Finite I]
    (j : pullback β π ⟶ ProjectiveSpace A I) [IsClosedImmersion j]
    (hbase : j ≫ toSpec A I = pullback.snd β π ≫ π ≫ q) :
    ∃ (J : Type u) (p : X ⟶ ProjectiveSpace A J),
      Finite J ∧ IsClosedImmersion p ∧ p ≫ toSpec A J = q := by
  let g := Birational.comparisonGraph β π a ha
  let : IsClosedImmersion g := Birational.comparisonGraph_isClosedImmersion β π a ha
  apply exists_projective_embedding_of_pointBlowupChain c hX q (g ≫ j)
  calc
    (g ≫ j) ≫ toSpec A I = (g ≫ pullback.snd β π) ≫ π ≫ q := by
      rw [Category.assoc, hbase, Category.assoc]
    _ = a ≫ π ≫ q := by rw [Birational.comparisonGraph_snd]
    _ = β ≫ q := by rw [← Category.assoc, ha]

/-- A finite projective embedding supplies its own positive exceptional twist.
The contraction retains the prescribed affine-base map, the original full field
point, its pulled ideal and the canonical blowup and complement comparisons. -/
theorem exists_cartier_contraction_of_projective_embedding
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (hX : RegularStalks X)
    (q : X ⟶ Spec (.of A)) {I : Type u} [Finite I]
    (p : X ⟶ ProjectiveSpace A I) [IsClosedImmersion p]
    (hp : p ≫ toSpec A I = q)
    {k : Type u} [Field k]
    (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (Hom.idealModule i))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1) :
    ∃ (Y : Scheme.{u}) (b : X ⟶ Y) (c : Spec (.of k) ⟶ Y)
      (s : Y ⟶ Spec (.of A)) (hf : cartierPullback c.ker b),
      Surjective b ∧ IsProper b ∧ IsClosedImmersion c ∧ IsProper s ∧ IsNoetherian Y ∧
      RegularStalks Y ∧ IsIntegral Y ∧
      ringKrullDim (Y.presheaf.stalk (c (IsLocalRing.closedPoint k))) = 2 ∧
      IsIso ((blowupDatum c.ker).lift b hf) ∧
      c.ker.comap b = i.ker ∧
      i ≫ b = toSpec k (ULift.{u} (Fin 2)) ≫ c ∧
      b ≫ s = q ∧
      (∃ (J : Type u) (j : Y ⟶ ProjectiveSpace A J),
        Finite J ∧ IsClosedImmersion j ∧ j ≫ toSpec A J = s) ∧
      ∃ (V : Y.Opens) (ε : (exceptionalComplement i).toScheme ≅ V.toScheme),
        (V : Set Y) = (Set.range c)ᶜ ∧
        b ⁻¹ᵁ V = exceptionalComplement i ∧
        IsIso (b ∣_ V) ∧
        ε.hom ≫ V.ι = (exceptionalComplement i).ι ≫ b := by
  classical
  let H := Scheme.Modules.Invertible.pullbackLineBundle p (twistingLineBundle A I 1)
  obtain ⟨d, hd, ⟨eH₀⟩⟩ :=
    Line.exists_positiveTwist_of_isClosedImmersion_over_ring (i ≫ p)
  let eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ) :=
    (Scheme.Modules.pullbackComp i p).app (twistingSheaf A I 1) ≪≫ eH₀
  let : Nonempty I := ⟨(coordinateAffineOpenCover A I).idx (p (genericPoint X))⟩
  let : Fintype I := Fintype.ofFinite I
  let r := Fintype.card I - 1
  have hcard : Fintype.card I = r + 1 := (Nat.sub_add_cancel Fintype.card_pos).symm
  let ecoord : I ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcard
  obtain ⟨Y, b, c, s, hf, hb, hbp, hc, hs, hYN, hYR, hYI, hdim,
    hbl, hfull, hexc, hbase, hj, hcompl⟩ :=
    exists_cartier_projective_contraction (p := p) i hI H (eP := Iso.refl _) d
      hX r ecoord eI eH hd
  exact ⟨Y, b, c, s, hf, hb, hbp, hc, hs, hYN, hYR, hYI, hdim,
    hbl, hfull, hexc, hbase.trans hp, hj, hcompl⟩

end AlgebraicGeometry.Scheme.Surfaces.Contraction
