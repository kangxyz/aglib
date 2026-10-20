/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineConstruction
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of the actual affine Rees construction

The examples use the original base map, literal saturated charts and the actual
pulled-back centre ideal. Properness is tested under precisely Noetherianity.
The zero ideal and a nonzero nilpotent denominator test empty scheme cases.
These interfaces do not assume or supply a `BlowupDatum` universal property.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Blowup
universe u

example (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    IsProper (affineProjMap I) := inferInstance

example (A : Type u) [CommRing A] (I : Ideal A) (a : I) :
    affineProjChart I a ≫ affineProjMap I =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away.saturatedChart A I a))) :=
  affineProjChart_map I a

example (A : Type u) [CommRing A] (I : Ideal A) :
    Scheme.Hom.IsEffectiveCartier ((affineCenter A I).comap (affineProjMap I)).subschemeι :=
  (cartierPullback_iff_isEffectiveCartier _ _).mp (affineProjMap_cartier I)

example (A : Type u) [CommRing A] (I : Ideal A) (a b : I) :
    Set.range (affineOverlapMap A I a b ≫ affineProjChart I a) =
      Set.range (affineProjChart I a) ∩ Set.range (affineProjChart I b) :=
  affineProjChart_overlap I a b

example (A : Type u) [CommRing A] : IsEmpty (affineProj (⊥ : Ideal A)) := inferInstance

example :
    IsEmpty (Spec (.of (affineBlowupAlgebra (ZMod 4) (Ideal.span {(2 : ZMod 4)}) 2))) := by
  exact affineChart_isEmpty_of_isNilpotent (Ideal.span {(2 : ZMod 4)})
    ⟨2, Ideal.subset_span (Set.mem_singleton _)⟩ ⟨2, by decide⟩

example (A : Type u) [CommRing A] :
    cartierPullback (affineCenter A ⊤) (affineProjMap (⊤ : Ideal A)) :=
  affineProjMap_cartier ⊤
