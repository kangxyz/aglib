/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.GaloisCech
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.ArtinianOverlap
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.Covers

/-! # The actual field cover and its Artinian overlap

The covering family is certified in the original small-etale topology. Its
literal overlap is identified with the spectrum of the original Amitsur term,
which is finite-dimensional over the field and hence Artinian.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.Amitsur

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

open QuasiCoherent Scheme.FiniteEtale Scheme.FiniteEtale.FieldGalois.Arbitrary

variable (E L : Type u) [Field E] [Field L] [Algebra E L]
  [FiniteDimensional E L] [Algebra.IsSeparable E L]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite field cover is covering in the original small-etale topology. -/
theorem galoisCoverFamily_covering :
    Sieve.ofArrows (fun i => (galoisCoverFamily E L i).left)
      (fun i => (galoisCoverFamily E L i).hom) ∈
        Scheme.smallEtaleTopology (Spec (.of E)) (StrictlyLocal.terminalObject E) := by
  change _ ∈ Scheme.smallGrothendieckTopology
    (@Etale : MorphismProperty Scheme.{u}) (Spec (.of E)) _
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  let y : Spec (.of L) := default
  refine ⟨(galoisCoverOver E L).left, (galoisCoverOver E L).hom, y, ?_, ?_, ?_⟩
  · exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨default, 𝟙 _, by simp [galoisCoverFamily]⟩
  · exact ((toEtale _).obj (finiteFieldCover E L)).prop
  · change (_ : Spec (.of E)) = (x : Spec (.of E))
    exact Subsingleton.elim _ _

/-- The original coproduct-of-representables map is genuinely locally surjective. -/
instance galoisCoverFamily_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology (Spec (.of E)))
      (Presheaf.Cech.familyMap (galoisCoverFamily E L)) :=
  Sheaf.BasisAcyclicity.familyMap_locallySurjective _ (galoisCoverFamily_covering E L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original small-etale product has the original Amitsur spectrum as its scheme. -/
def galoisCechSchemeIso (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => galoisCoverOver E L).left.left ≅
      Spec (.of (term E L n)) :=
  (Over.forget (Spec (.of E))).mapIso
    ((PreservesProduct.iso (etaleSliceToScheme (StrictlyLocal.terminalObject E))
      (fun _ : Fin (n + 1) => galoisCoverOver E L)) ≪≫
      (Pi.mapIso fun _ : Fin (n + 1) => galoisCoverSchemeIso E L) ≪≫
        (amitsurSpecProductIso E L n).symm)

/-- The actual degree-one overlap is Artinian; no reducedness or locality is assumed. -/
instance galoisCechOverlap_isArtinianScheme :
    IsArtinianScheme (∏ᶜ fun _ : Fin 2 => galoisCoverOver E L).left.left := by
  let : Module.Finite E (term E L 1) :=
    Module.Finite.equiv (oneTensorEquiv E L).symm.toLinearEquiv
  let : IsArtinianRing (term E L 1) := IsArtinianRing.of_finite E _
  let : IsLocallyArtinian (Spec (.of (term E L 1))) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  let e := galoisCechSchemeIso E L 1
  let : IsLocallyArtinian (∏ᶜ fun _ : Fin 2 => galoisCoverOver E L).left.left :=
    IsLocallyArtinian.of_isImmersion e.hom
  let : Finite (∏ᶜ fun _ : Fin 2 => galoisCoverOver E L).left.left :=
    Finite.of_injective e.hom e.hom.homeomorph.injective
  exact { toIsLocallyArtinian := inferInstance, toCompactSpace := inferInstance }

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
