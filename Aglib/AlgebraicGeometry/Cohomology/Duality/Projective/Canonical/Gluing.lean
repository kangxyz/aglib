/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers

/-!
# Gluing the ordinary homology map in the canonical-bundle comparison

Compatible actual local homology isomorphisms glue in the category of module
sheaves. Their inverses are the restrictions of the inverse of the glued
map. Native single-homology reconstruction is applied only after the
homology bounds have been proved for the installed derived object.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.InternalHom

universe u v w
namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type v}
  (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
  (M N : X.Modules) (e : ∀ i, M.restrict (a i) ≅ N.restrict (a i))
  (hcomp : RestrictionHomCompatible a M N (fun i => (e i).hom))

/-- Glue actual ordinary homology arrows; local invertibility proves global invertibility. -/
def canonicalHomologyGlueIso : M ≅ N := by
  let f := glueRestrictionHom Y a hcover M N (fun i => (e i).hom) hcomp
  have hf : IsIso f := by
    apply isIso_of_restrict_openCover Y a hcover
    intro i
    rw [show (restrictFunctor (a i)).map f = (e i).hom from
      glueRestrictionHom_restrict Y a hcover M N (fun i => (e i).hom) hcomp i]
    infer_instance
  exact asIso f

/-- The glued map restricts to the prescribed local homology isomorphism. -/
theorem canonicalHomologyGlueIso_restrict (i : ι) :
    (restrictFunctor (a i)).mapIso (canonicalHomologyGlueIso Y a hcover M N e hcomp) =
      e i := by
  apply Iso.ext
  exact glueRestrictionHom_restrict Y a hcover M N (fun i => (e i).hom) hcomp i

/-- The inverse restricts to the actual local inverse, with no independently chosen inverse. -/
theorem canonicalHomologyGlueIso_inv_restrict (i : ι) :
    (restrictFunctor (a i)).map (canonicalHomologyGlueIso Y a hcover M N e hcomp).inv =
      (e i).inv :=
  congrArg Iso.inv (canonicalHomologyGlueIso_restrict Y a hcover M N e hcomp i)

section Reconstruction
variable [HasDerivedCategory.{w} X.Modules]
  (K : DerivedCategory.Plus X.Modules) (c : ℤ) [K.IsGE c] [K.IsLE c]
  (N : X.Modules)

/-- Reconstruct the installed derived object from its actual glued ordinary homology map. -/
def canonicalIsoOfHomology
    (e : (DerivedCategory.Plus.homologyFunctor X.Modules c).obj K ≅ N) :
    K ≅ (DerivedCategory.Plus.singleFunctor X.Modules c).obj N :=
  DerivedCategory.Plus.isoSingleHomology K c ≪≫
    (DerivedCategory.Plus.singleFunctor X.Modules c).mapIso e

end Reconstruction
end AlgebraicGeometry.Scheme.Modules
