/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.EtaleDimensionOne
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinResidue
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericHigherImageOne
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ResidueRootsVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ArtinPoints
public import Aglib.AlgebraicGeometry.ResidueField.StalkIsomorphism

/-! # Original higher images of the actual generic Artin locus

The generic source and all its affine etale base changes retain their original
nilpotent stalk rings. Original represented cohomology on those tests computes
the actual higher images. The degree-one calculation uses the native Artinian
Picard theorem; higher scalar invertibility uses actual curve residue fields
and the original Kummer sequence. No strict-local limit is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [IsNoetherian X]

variable {k : Type u} [Field k] [IsSepClosed k]
  (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (hdim : topologicalKrullDim X ≤ 1)

include p hdim

/-- Actual generic pullbacks on quasi-compact etale tests have vanishing original
root cohomology in degrees at least two. -/
theorem genericArtinBaseChange_roots_subsingleton
    (U : X.Etale) [QuasiCompact U.hom]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (pullback U.hom (genericArtinMap X)))]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (mu (pullback U.hom (genericArtinMap X)) n) q) := by
  let B := pullback U.hom (genericArtinMap X)
  let π : B ⟶ U.left := pullback.fst U.hom (genericArtinMap X)
  let : IsArtinianScheme B :=
    genericArtinBaseChange_isArtinian (X := X) (U := U.left) U.hom
  have hΓ : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hU : IsUnit (n : Γ(U.left, ⊤)) := levelInvertible (U.hom ≫ p) n hΓ
  let : ∀ x : B, HasExt.{u + 2}
      (AbelianSheaf.{u, u + 1} (Spec (B.residueField x))) := fun x => HasExt.standard _
  let : ∀ x : B, Subsingleton
      (Sheaf.H.{u + 2} (mu (Spec (B.residueField x)) n) q) := fun x => by
    let : HasExt.{u + 2}
        (AbelianSheaf.{u, u + 1} (Spec (U.left.residueField (π x)))) := HasExt.standard _
    let : Subsingleton (Sheaf.H.{u + 2}
        (mu (Spec (U.left.residueField (π x))) n) q) :=
      residueRoots_subsingleton U.left (U.hom ≫ p)
        (topologicalKrullDim_le_one_of_etale (X := X) (U := U.left) U.hom hdim) (π x) n hn hΓ q hq
    let : IsIso (π.stalkMap x) :=
      genericArtinBaseChange_stalkMap_isIso (X := X) (U := U.left) U.hom x
    let : IsIso (π.residueFieldMap x) := π.residueFieldMap_isIso_of_stalkMap x
    exact (Kummer.rootsCohomologyPullback_bijective_of_isEquivalence.{u, u + 2, u + 2}
      (Spec.map (π.residueFieldMap x)) n hn
      (levelInvertible (U.left.fromSpecResidueField (π x)) n hU) q).surjective.subsingleton
  exact Kummer.roots_subsingleton_of_artinian_residues.{u, w, u + 2}
    B n hn (levelInvertible π n hU) q

/-- The literal power map is bijective on original higher multiplicative
cohomology of every actual quasi-compact etale generic pullback. -/
theorem genericArtinBaseChange_power_bijective
    (U : X.Etale) [QuasiCompact U.hom]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (pullback U.hom (genericArtinMap X)))]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    Function.Bijective
      (Sheaf.H.map (power (pullback U.hom (genericArtinMap X)) n) q) := by
  let := genericArtinBaseChange_roots_subsingleton X p hdim U n hn hunit q hq
  let := genericArtinBaseChange_roots_subsingleton X p hdim U n hn hunit (q + 1) (by omega)
  have hΓ : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  exact Kummer.power_bijective_of_roots_subsingleton _ n hn
    (levelInvertible (pullback.fst U.hom (genericArtinMap X) ≫ U.hom ≫ p) n hΓ) q

/-- Positive invertible integers act isomorphically on the original higher
multiplicative images in degrees at least two. -/
theorem genericHigherImage_nsmul_isIso
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    IsIso (n • 𝟙 ((higherDirectImage (genericArtinMap X) q).obj
      (gm (genericArtinLocus X)))) := by
  apply higherDirectImage_nsmul_isIso_of_affine (genericArtinMap X)
    (gm (genericArtinLocus X)) q n
  intro U hU
  let : IsAffine U.left := hU
  let : IsLocallyNoetherian U.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
  let : IsNoetherian U.left := { }
  let : QuasiCompact U.hom :=
    quasiCompact_of_noetherianSpace_source (X := U.left) (Y := X) U.hom
  let T := (siteBaseChange (genericArtinMap X)).obj U
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} T.left) := HasExt.standard _
  let : HasExt.{u + 2} (Sheaf ((genericArtinLocus X).smallEtaleTopology.over T)
      AddCommGrpCat.{u + 1}) := HasExt.standard _
  let e := Kummer.gmRepresentedCohomologyEquiv.{u, w, u + 2, u + 2} T q
  let : HasExt.{u + 2}
      (AbelianSheaf.{u, u + 1} (pullback U.hom (genericArtinMap X))) :=
    inferInstanceAs (HasExt.{u + 2} (AbelianSheaf.{u, u + 1} T.left))
  have hb := genericArtinBaseChange_power_bijective.{u, u + 2}
    X p hdim U n hn hunit q hq
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} T.left)
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  have he : (Sheaf.H.map (power T.left n) q : _ → _) = (fun x => n • x) :=
    funext (cohomology_map_nsmul_id (gm T.left) q n)
  have hb' : Function.Bijective (fun x : Sheaf.H.{u + 2} (gm T.left) q => n • x) :=
    he ▸ hb
  have he' : (fun x => n • x) = e.symm ∘ (fun x => n • x) ∘ e := by
    funext x
    simp
  rw [he']
  exact e.symm.bijective.comp (hb'.comp e.bijective)

/-- The degree-one vanishing discharges the remaining positive-degree scalar case. -/
theorem genericHigherImage_positive_nsmul_isIso
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 1 ≤ q) :
    IsIso (n • 𝟙 ((higherDirectImage (genericArtinMap X) q).obj
      (gm (genericArtinLocus X)))) := by
  by_cases h : q = 1
  · subst q
    exact (genericHigherImage_one_isZero X).isIso (genericHigherImage_one_isZero X) _
  · exact genericHigherImage_nsmul_isIso X p hdim n hn hunit q (by omega)

/-- Higher original multiplicative cohomology of the whole generic Artin locus
has bijective literal power maps, with all residue-field inputs discharged. -/
theorem genericArtin_power_bijective
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    Function.Bijective (Sheaf.H.map (power (genericArtinLocus X) n) q) := by
  have hΓ : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  let : ∀ η : genericPoints X,
      HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (Spec (X.residueField η.val))) :=
    fun η => HasExt.standard _
  let : ∀ η : genericPoints X,
      Subsingleton (Sheaf.H.{u + 2} (mu (Spec (X.residueField η.val)) n) q) :=
    fun η => residueRoots_subsingleton X p hdim η.val n hn hΓ q hq
  let : ∀ η : genericPoints X,
      Subsingleton (Sheaf.H.{u + 2} (mu (Spec (X.residueField η.val)) n) (q + 1)) :=
    fun η => residueRoots_subsingleton X p hdim η.val n hn hΓ (q + 1) (by omega)
  exact genericArtin_power_bijective_of_residue_roots_subsingleton.{u, w, u + 2}
    X n hn (levelInvertible p n hΓ) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
