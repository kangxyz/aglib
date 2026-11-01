/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.At
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Locus

/-! # Pointwise etaleness under flat preimmersion base change

Only an etale neighborhood of the specified pullback point is needed. The
original commuting stalk square and its two native isomorphisms transfer
formal etaleness back to the original stalk map. Local finite presentation
of the original morphism then produces its actual etale neighborhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- An actual etale source neighborhood makes the original stalk map formally
etale, through the original open immersion's stalk isomorphism. -/
theorem etaleAt.stalkMap_formallyEtale {Z X : Scheme.{u}} {f : Z ⟶ X} {z : Z}
    (h : f.etaleAt z) : (f.stalkMap z).hom.FormallyEtale := by
  obtain ⟨U, hz, hU⟩ := h
  let : Etale (U.ι ≫ f) := hU
  let w : U := ⟨z, hz⟩
  let e : Arrow.mk (f.stalkMap z) ≅ Arrow.mk ((U.ι ≫ f).stalkMap w) :=
    Arrow.isoMk' _ _ (Iso.refl _) (U.stalkIso w).symm (by
      simp only [Iso.refl_hom, Iso.symm_hom, Scheme.Opens.stalkIso_inv]
      exact (Category.id_comp _).trans (stalkMap_comp U.ι f w))
  exact (RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff e).mpr
    (LocalRing.Etale.etale_stalkMap_formallyEtale (U.ι ≫ f) w)

/-- A chosen point of a flat-preimmersion base change detects etaleness at
its original image. No etaleness of the whole pullback is assumed. -/
theorem etaleAt_of_isPullback_of_flat_of_preimmersion
    {P Z Y X : Scheme.{u}} {fst : P ⟶ Z} {snd : P ⟶ Y}
    {f : Z ⟶ X} {g : Y ⟶ X}
    (H : IsPullback fst snd f g) [Flat g] [IsPreimmersion g]
    [LocallyOfFinitePresentation f] (p : P) (z : Z) (hz : fst p = z)
    (h : snd.etaleAt p) : f.etaleAt z := by
  have he := stalkMapIsoOfIsPullbackOfFlatOfPreimmersion H p z hz
  exact LocalRing.Etale.exists_etale_neighborhood_of_stalkMap_formallyEtale f z
    ((RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff he).mpr
      h.stalkMap_formallyEtale)

end AlgebraicGeometry.Scheme.Hom
