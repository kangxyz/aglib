/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Open

/-! # Original coefficient formulas for open restriction cohomology

The original additive open-restriction equivalence retains the actual module
restriction unit. Postcomposing that unit with an arbitrary actual local
coefficient map gives the original coefficient map on unchanged `Sheaf.H`.
The proof uses only the existing geometric normalization and coefficient
naturality; no Ext adjunction is reconstructed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original additive open equivalence uses the actual module restriction unit. -/
theorem moduleHPrimeOpenRestrictionAddEquiv_geometric (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) (n : ℕ) (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :
    sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n x =
      sheafHPrimeTopAddEquiv U.toScheme (moduleAddSheaf U.toScheme (M.restrict U.ι)) n
        ((Sheaf.cohomologyPresheaf.{u + 1}
            (moduleAddSheaf U.toScheme (M.restrict U.ι)) n).map
          (eqToHom U.ι_preimage_self.symm).op
            ((zariskiCohomologyOpenMap U.ι (moduleAddSheaf X M)
              (moduleAddSheaf U.toScheme (M.restrict U.ι))
              (moduleCoefficientPullback U.ι (M := M) (N := M.restrict U.ι)
                ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)) n).app (op U) x)) := by
  have H := sheafHPrimeOpenRestrictionAddEquiv_geometric X U (moduleAddSheaf X M) n x
  erw [← moduleCoefficientPullback_restrictUnit X U M] at H
  exact H

/-- An actual coefficient arrow out of the local restriction acts on the original
open comparison by the original geometric map of the postcomposed restriction unit. -/
theorem moduleHPrimeOpenRestrictionAddEquiv_postcomp (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) {N : U.toScheme.Modules} (ε : M.restrict U.ι ⟶ N)
    (n : ℕ) (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :
    Sheaf.H.map ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map ε) n
        (sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n x) =
      sheafHPrimeTopAddEquiv U.toScheme (moduleAddSheaf U.toScheme N) n
        ((Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf U.toScheme N) n).map
          (eqToHom U.ι_preimage_self.symm).op
            ((zariskiCohomologyOpenMap U.ι (moduleAddSheaf X M)
              (moduleAddSheaf U.toScheme N)
              (moduleCoefficientPullback U.ι (M := M) (N := N)
                ((Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
                  (Scheme.Modules.pushforward U.ι).map ε)) n).app (op U) x)) := by
  let a := U.ι
  let K : U.toScheme.Modules := M.restrict a
  let A : U.toScheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf U.toScheme K) n
  let B : U.toScheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf U.toScheme N) n
  let F : moduleAddSheaf U.toScheme K ⟶ moduleAddSheaf U.toScheme N :=
    (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map ε
  let θ : A ⟶ B :=
    (Sheaf.cohomologyPresheafFunctor.{u + 1} (Opens.grothendieckTopology U.toScheme) n).map F
  let η : M ⟶ (Scheme.Modules.pushforward a).obj K :=
    (Scheme.Modules.restrictAdjunction a).unit.app M
  let φ : M ⟶ (Scheme.Modules.pushforward a).obj N :=
    η ≫ (Scheme.Modules.pushforward a).map ε
  let P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) n
  let g₀ : P ⟶ (Opens.map a.base).op ⋙ A :=
    zariskiCohomologyOpenMap a (moduleAddSheaf X M) (moduleAddSheaf U.toScheme K)
      (moduleCoefficientPullback a (M := M) (N := K) η) n
  let g₁ : P ⟶ (Opens.map a.base).op ⋙ B :=
    zariskiCohomologyOpenMap a (moduleAddSheaf X M) (moduleAddSheaf U.toScheme N)
      (moduleCoefficientPullback a (M := M) (N := N) φ) n
  let k : (⊤ : U.toScheme.Opens) ⟶ a ⁻¹ᵁ U := eqToHom U.ι_preimage_self.symm
  let topA := sheafHPrimeTopAddEquiv U.toScheme (moduleAddSheaf U.toScheme K) n
  let topB := sheafHPrimeTopAddEquiv U.toScheme (moduleAddSheaf U.toScheme N) n
  have hx : sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n x =
      topA (A.map k.op (g₀.app (op U) x)) :=
    moduleHPrimeOpenRestrictionAddEquiv_geometric X U M n x
  have hg : g₁.app (op U) x = θ.app (op (a ⁻¹ᵁ U)) (g₀.app (op U) x) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (zariskiCohomologyOpenMap_module_postcomp a η ε n) (op U)) x
  have hn : θ.app (op ⊤) (A.map k.op (g₀.app (op U) x)) =
      B.map k.op (θ.app (op (a ⁻¹ᵁ U)) (g₀.app (op U) x)) :=
    ConcreteCategory.congr_hom (θ.naturality k.op) (g₀.app (op U) x)
  calc
    _ = Sheaf.H.map F n (topA (A.map k.op (g₀.app (op U) x))) :=
      congrArg (Sheaf.H.map F n) hx
    _ = topB (θ.app (op ⊤) (A.map k.op (g₀.app (op U) x))) :=
      (sheafHPrimeTopAddEquiv_naturality U.toScheme F n _).symm
    _ = topB (B.map k.op (θ.app (op (a ⁻¹ᵁ U)) (g₀.app (op U) x))) :=
      congrArg topB hn
    _ = _ := congrArg (fun z => topB (B.map k.op z)) hg.symm

end AlgebraicGeometry.Scheme.Cohomology
