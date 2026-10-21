/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FormalProperties
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.RingHom.EssFiniteType

/-!
# Unramified local maps from their actual cotangent and residue maps

Surjectivity of the original cotangent map makes the source maximal ideal
generate the target maximal ideal, by the native local Nakayama criterion.
Together with a surjective residue map this proves formal unramifiedness for
an essentially finite type local map. An actual fraction-field square then
passes formal unramifiedness to the field map; finiteness of that field map
gives formal etaleness. No finite-presentation claim about a stalk is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

namespace AlgHom

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [IsLocalRing R] [IsLocalRing S]

/-- A surjective actual cotangent pullback makes the original source maximal
ideal generate the target maximal ideal. Only the target is assumed Noetherian. -/
theorem map_maximalIdeal_of_surjective_mapCotangent [IsNoetherianRing S]
    (f : R →ₐ[k] S) [IsLocalHom f.toRingHom]
    (hf : Function.Surjective (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f
      (fun a ha => _root_.map_nonunit f.toRingHom a ha))) :
    (maximalIdeal R).map f.toRingHom = maximalIdeal S := by
  let I := (maximalIdeal R).map f.toRingHom
  let M : Submodule S (maximalIdeal S) :=
    Submodule.comap (Submodule.subtype (maximalIdeal S)) (I : Submodule S S)
  have hM : M = ⊤ := by
    apply (IsLocalRing.CotangentSpace.map_eq_top_iff).mp
    apply top_unique
    intro v _
    obtain ⟨a, rfl⟩ := hf v
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal R) a
    refine ⟨⟨f a, _root_.map_nonunit f.toRingHom a a.property⟩, ?_, rfl⟩
    exact Ideal.mem_map_of_mem f.toRingHom a.property
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le f.toRingHom)
  intro a ha
  have hm : (⟨a, ha⟩ : maximalIdeal S) ∈ M := by rw [hM]; trivial
  exact hm

/-- Surjectivity of the actual cotangent and residue maps proves formal
unramifiedness of an essentially finite type local homomorphism. -/
theorem formallyUnramified_of_surjective_mapCotangent [IsNoetherianRing S]
    (f : R →ₐ[k] S) [IsLocalHom f.toRingHom] (hft : f.toRingHom.EssFiniteType)
    (hr : Function.Surjective (IsLocalRing.ResidueField.map f.toRingHom))
    (hc : Function.Surjective (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) f
      (fun a ha => _root_.map_nonunit f.toRingHom a ha))) :
    f.toRingHom.FormallyUnramified := by
  have hm := f.map_maximalIdeal_of_surjective_mapCotangent hc
  let := f.toRingHom.toAlgebra
  let : Algebra.EssFiniteType R S := hft
  have hr' : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)) := hr
  let e : ResidueField R ≃ₐ[ResidueField R] ResidueField S :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨(Algebra.ofId (ResidueField R) (ResidueField S)).injective, hr'⟩
  let : Algebra.IsSeparable (ResidueField R) (ResidueField S) := AlgEquiv.Algebra.isSeparable e
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hm

end AlgHom

namespace RingHom.FormallyEtale

/-- In an actual commutative fraction-field square, formal unramifiedness of
the local map passes to the field map. A finite field map is then formally etale. -/
theorem of_formallyUnramified_fraction_square
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra S L] [IsFractionRing S L]
    (f : R →+* S) (i : R →+* K) (g : K →+* L)
    (hsq : (algebraMap S L).comp f = g.comp i)
    (hf : f.FormallyUnramified) (hg : g.Finite) : g.FormallyEtale := by
  have hj : (algebraMap S L).FormallyUnramified := by
    rw [RingHom.formallyUnramified_algebraMap]
    exact Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors S)
  have hcomp := hf.comp hj
  rw [hsq] at hcomp
  have hgu : g.FormallyUnramified := RingHom.FormallyUnramified.of_comp hcomp
  let := g.toAlgebra
  let : Module.Finite K L := hg
  let : Algebra.FormallyUnramified K L := hgu
  exact Algebra.FormallyEtale.of_formallyUnramified_of_field K L

end RingHom.FormallyEtale
