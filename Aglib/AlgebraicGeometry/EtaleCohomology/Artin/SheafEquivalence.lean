/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ArtinBaseChangeSite
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# Original small-etale sheaves from the actual Artin finite-etale basis

A surjective map inducing an equivalence on finite etale objects induces an
equivalence on the original abelian small-etale sheaves of locally Artinian
quasi-separated schemes. The original direct and inverse image functors are
retained. No assertion identifies the multiplicative coefficient across this map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Artin

universe u

variable {X S : Scheme.{u}}
  [IsLocallyArtinian X] [QuasiSeparatedSpace X]
  [IsLocallyArtinian S] [QuasiSeparatedSpace S]

/-- Restriction to the actual finite-etale basis, at the original coefficient size. -/
abbrev finiteEtaleRestriction (X : Scheme.{u}) [IsLocallyArtinian X]
    [QuasiSeparatedSpace X] :
    AbelianSheaf.{u, u + 1} X ⥤ Sheaf (artinTopology X) AddCommGrpCat.{u + 1} :=
  (toEtale X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (artinTopology X) X.smallEtaleTopology

instance finiteEtaleRestriction_isEquivalence :
    (finiteEtaleRestriction X).IsEquivalence := by
  unfold finiteEtaleRestriction
  infer_instance

/-- Original direct image is an equivalence under the actual finite-etale site comparison. -/
theorem directImage_isEquivalence (f : S ⟶ X) [Surjective f]
    [(baseChange f).IsEquivalence] : (directImage f).IsEquivalence := by
  let F := (baseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (artinTopology X) (artinTopology S)
  let : F.IsEquivalence :=
    (artinBaseChangeSheafEquivalence f AddCommGrpCat.{u + 1}).isEquivalence_inverse
  let e : directImage f ⋙ finiteEtaleRestriction X ≅ finiteEtaleRestriction S ⋙ F :=
    Iso.refl _
  let : (directImage f ⋙ finiteEtaleRestriction X).IsEquivalence :=
    CategoryTheory.Functor.isEquivalence_of_iso e.symm
  exact CategoryTheory.Functor.isEquivalence_of_comp_right
    (directImage f) (finiteEtaleRestriction X)

/-- The original inverse image, rather than a replacement transport, is an equivalence. -/
theorem inverseImage_isEquivalence (f : S ⟶ X) [Surjective f]
    [(baseChange f).IsEquivalence] : (inverseImage f).IsEquivalence := by
  let := directImage_isEquivalence f
  exact (inverseImageAdjunction f).isEquivalence_left_of_isEquivalence_right

end AlgebraicGeometry.Scheme.EtaleCohomology.Artin
