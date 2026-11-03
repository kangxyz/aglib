/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.ScaledSections
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineRawCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.SectionsMap


/-!
# The actual regular-pair scaled raw sheaf map

The sole native affine equivalence realizes the constructed exact section
map as an ordinary sheaf morphism into the original pulled-back line. Its
sections and original exceptional-coordinate normalization remain exact.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u vK


open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.RegularPair

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (x y : R)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "S" =>
  Localization.Away.saturatedChart R (Ideal.span (Set.insert x (Set.singleton y))) x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "σ" => CommRingCat.ofHom (algebraMap R S)

/-- The actual raw sheaf map into the original pulled-back line, constructed
without an image-bound or generic-injectivity premise. -/
def saturatedPairScaledRawMap :
    moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n ⟶
    (pullback (Spec.map σ)).obj L.val := by
  letI : (moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec (.of S)).ringCatSheaf).prop_of_iso
      (targetRawFormsAffineIso α σ n).symm inferInstance
  letI : ((pullback (Spec.map σ)).obj L.val).IsQuasicoherent :=
    Invertible.lineBundle_isQuasicoherent (Invertible.pullbackLineBundle (Spec.map σ) L)
  exact affineSectionsMap
    (ModuleCat.ofHom
      (X := moduleSpecΓFunctor.obj (moduleExteriorPower (Spec (.of S))
        (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n))
      (Y := moduleSpecΓFunctor.obj ((pullback (Spec.map σ)).obj L.val))
      (saturatedPairScaledSections Λ R K x y hx hy n L φ))

/-- The actual sheaf map has exactly the original constructed section map. -/
theorem saturatedPairScaledRawMap_sections :
    moduleSpecΓFunctor.map (saturatedPairScaledRawMap Λ R K x y hx hy n L φ) =
      ModuleCat.ofHom
        (X := moduleSpecΓFunctor.obj (moduleExteriorPower (Spec (.of S))
          (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n))
        (Y := moduleSpecΓFunctor.obj ((pullback (Spec.map σ)).obj L.val))
        (saturatedPairScaledSections Λ R K x y hx hy n L φ) := by
  let : (moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec (.of S)).ringCatSheaf).prop_of_iso
      (targetRawFormsAffineIso α σ n).symm inferInstance
  let : ((pullback (Spec.map σ)).obj L.val).IsQuasicoherent :=
    Invertible.lineBundle_isQuasicoherent (Invertible.pullbackLineBundle (Spec.map σ) L)
  unfold saturatedPairScaledRawMap
  exact affineSectionsMap_sections _

/-- Original raw coefficient sections have their exact exceptional-coordinate
normalization under the constructed ordinary sheaf morphism. -/
theorem saturatedPairScaledRawMap_comp_apply
    (p : moduleSpecΓFunctor.obj ((pullback (Spec.map σ)).obj
      (moduleExteriorPower (Spec (.of R)) (relativeDifferentialSheaf (Spec.map α)) n))) :
    moduleSpecΓFunctor.map (saturatedPairScaledRawMap Λ R K x y hx hy n L φ)
      (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n) p) =
    algebraMap R S x • (moduleSpecΓFunctor.map ((pullback (Spec.map σ)).map φ) p) :=
  (ConcreteCategory.congr_hom
    (saturatedPairScaledRawMap_sections Λ R K x y hx hy n L φ) _).trans
      (saturatedPairScaledSections_comp Λ R K x y hx hy n L φ p)

end AlgebraicGeometry.Scheme.Blowup.RegularPair
