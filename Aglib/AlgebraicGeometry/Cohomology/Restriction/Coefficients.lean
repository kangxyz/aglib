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

universe u v

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

private theorem postcomp_restriction_values
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {P : C ⥤ AddCommGrpCat.{v}} {A B : D ⥤ AddCommGrpCat.{v}}
    {θ : A ⟶ B} {g₀ : P ⟶ F ⋙ A} {g₁ : P ⟶ F ⋙ B}
    (hg : g₁ = g₀ ≫ Functor.whiskerLeft F θ)
    {U : C} {V : D} (k : F.obj U ⟶ V)
    {H₀ H₁ : Type*} (topA : A.obj V → H₀) (topB : B.obj V → H₁)
    (f : H₀ → H₁) (htop : ∀ z, topB (θ.app V z) = f (topA z))
    (e : P.obj U → H₀) (x : P.obj U)
    (hx : e x = topA (A.map k (g₀.app U x))) :
    f (e x) = topB (B.map k (g₁.app U x)) := by
  have hgx : g₁.app U x = θ.app (F.obj U) (g₀.app U x) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hg U) x
  have hn := ConcreteCategory.congr_hom (θ.naturality k) (g₀.app U x)
  calc
    _ = f (topA (A.map k (g₀.app U x))) := congrArg f hx
    _ = topB (θ.app V (A.map k (g₀.app U x))) := (htop _).symm
    _ = topB (B.map k (θ.app (F.obj U) (g₀.app U x))) := congrArg topB hn
    _ = _ := congrArg (fun z => topB (B.map k z)) hgx.symm

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
  let F : moduleAddSheaf U.toScheme K ⟶ moduleAddSheaf U.toScheme N :=
    (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map ε
  let η : M ⟶ (Scheme.Modules.pushforward a).obj K :=
    (Scheme.Modules.restrictAdjunction a).unit.app M
  let k : (⊤ : U.toScheme.Opens) ⟶ a ⁻¹ᵁ U := eqToHom U.ι_preimage_self.symm
  let topA := sheafHPrimeTopAddEquiv U.toScheme (moduleAddSheaf U.toScheme K) n
  let topB := sheafHPrimeTopAddEquiv U.toScheme (moduleAddSheaf U.toScheme N) n
  have hpost := zariskiCohomologyOpenMap_module_postcomp a η ε n
  have hfinal := postcomp_restriction_values (Opens.map a.base).op hpost k.op topA topB
    (Sheaf.H.map F n) (sheafHPrimeTopAddEquiv_naturality U.toScheme F n)
    (sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n) x
    (moduleHPrimeOpenRestrictionAddEquiv_geometric X U M n x)
  exact hfinal

end AlgebraicGeometry.Scheme.Cohomology
