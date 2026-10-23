/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineAcyclicity
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineBasis
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.EtaleSliceProducts
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.SmallCovers
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.TupleProducts
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Injectives

/-! # Original étale cohomology vanishing for affine quasi-coherent coefficients

The selected basis consists of genuine finite affine families in the original
covering sieves. Raising its index universe only reindexes those same families.
Amitsur exactness proves their original tuple-cochain acyclicity; the independent
basis criterion then gives the original represented Ext and original `Sheaf.H`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sheaf.BasisAcyclicity
open AlgebraicGeometry.Scheme.Modules

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- The same finite affine cover basis at the actual additive coefficient size. -/
abbrev largeAffineCoverBasis (X : Scheme.{u}) :=
  CoverBasis.raise.{u + 1, u, 0, u + 1} (affineCoverBasis X)

/-- Transport actual slice exactness through the original tuple and coefficient maps. -/
theorem tuple_exactAt_of_slice {X : Scheme.{u}} (W : X.Etale)
    {ι : Type (u + 1)} (U : ι → Over W)
    (P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (Q : (Over W.left)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (e : (Over.map W.hom).op ⋙ P ≅ Q) (n : ℕ)
    (h : ((cechComplexFunctor (fun i => (etaleSliceToScheme W).obj (U i))).obj Q).ExactAt
      (n + 1)) :
    (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U)
      ((Etale.forget X).op ⋙ P)).ExactAt (n + 1) := by
  exact ((h.of_iso ((cechComplexFunctor
    (fun i => (etaleSliceToScheme W).obj (U i))).mapIso e).symm).of_iso
      (etaleSliceCechIso W U P).symm).of_iso
        (Presheaf.Cech.tupleHomCechIso.{u + 1, u, 0} U
          ((Etale.forget X).op ⋙ P)).symm

/-- Genuine finite-family Amitsur descent gives the exact original tuple Čech criterion. -/
theorem additiveCoefficient_cechAcyclic (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] : CechAcyclic (largeAffineCoverBasis X) (additiveCoefficient X F) := by
  intro W ι U hU n
  have hcover := (largeAffineCoverBasis X).covering hU
  obtain ⟨κ, V, e, hV, rfl⟩ := hU
  let : IsAffine W.left := hV.1
  let : Finite κ := hV.2.1
  let : Finite ι := Finite.of_equiv κ e.symm
  let : ∀ i, IsAffine (V (e i)).left.left := fun i => hV.2.2.1 (e i)
  let U' : ι → Over W.left := fun i => (etaleSliceToScheme W).obj (V (e i))
  let : ∀ i, IsAffine (U' i).left := fun i =>
    inferInstanceAs (IsAffine (V (e i)).left.left)
  let : ∀ i, Etale (U' i).hom := fun i =>
    inferInstanceAs (Etale (V (e i)).hom.left)
  have hs : ∀ x : W.left, ∃ i y, (U' i).hom y = x :=
    etaleFamily_jointlySurjective (V ∘ e) hcover
  exact tuple_exactAt_of_slice W (V ∘ e) (additiveSectionsPresheaf X F)
    (additiveSectionsPresheaf W.left ((Modules.pullback W.hom).obj F))
    (additiveBaseRestrictionIso W.hom F) n
    (finiteAffineFamily_exactAt_succ W.left ((Modules.pullback W.hom).obj F) U' hs n)

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]

/-- Original positive Ext from every affine representable vanishes. -/
theorem affineObject_ext_eq_zero (W : X.Etale) [IsAffine W.left] (n : ℕ)
    (x : Ext.{e}
      (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1} (smallEtaleTopology X) W)
      (additiveCoefficient X F) (n + 1)) : x = 0 := by
  let : EnoughInjectives (AbelianSheaf.{u, u + 1} X) :=
    Sheaf.LargeCohomology.enoughInjectivesLarge (smallEtaleTopology X)
  exact (additiveCoefficient_cechAcyclic X F).ext_eq_zero W
    (show IsAffine W.left from inferInstance) n x

/-- Positive original small-étale `Sheaf.H` of an affine quasi-coherent module
vanishes, without coefficient flatness or finite-generation hypotheses. -/
theorem affine_cohomology_eq_zero [IsAffine X] (n : ℕ)
    (x : Sheaf.H.{e} (additiveCoefficient X F) (n + 1)) : x = 0 := by
  let : EnoughInjectives (AbelianSheaf.{u, u + 1} X) :=
    Sheaf.LargeCohomology.enoughInjectivesLarge (smallEtaleTopology X)
  exact (additiveCoefficient_cechAcyclic X F).cohomology_eq_zero
    (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) X)
    (show IsAffine X from inferInstance) n x

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
