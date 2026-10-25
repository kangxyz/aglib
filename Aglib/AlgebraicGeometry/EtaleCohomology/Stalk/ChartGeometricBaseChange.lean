/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodBaseChange

/-! # Geometric neighborhood limits over an original, possibly non-affine base

The affine chart is postcomposed into the original base before taking fibre
products. The construction therefore has literal original-base fibre products
at every stage and at the limit, rather than iterated fibre products.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u
open Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) (f : X ⟶ S)

/-- The original affine neighborhood structural maps, postcomposed into the base. -/
def chartGeometricStructureMap :
    diagram R Ω ⟶ (Functor.const _).obj S :=
  structureMap R Ω ≫ (Functor.const _).map j

/-- The actual geometric system over the original source, without iterated pullbacks. -/
def chartGeometricBaseChangedDiagram :
    (GeometricEtaleNeighborhood R Ω)ᵒᵖ ⥤ Over X :=
  Over.lift (diagram R Ω) (chartGeometricStructureMap R Ω j) ⋙ Over.pullback f

/-- The original limit projections commute with the postcomposed structural maps. -/
theorem chartGeometricStructure_fac (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
    (specCone R Ω).π.app i ≫ (chartGeometricStructureMap R Ω j).app i =
      Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j := by
  change (specCone R Ω).π.app i ≫ (Spec.algebraMap R i.unop.algebra ≫ j) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫ j) (π_structure R Ω i.unop))

/-- The actual limit over the original base, with point the literal single fibre product. -/
def chartGeometricBaseChangedCone : Cone (chartGeometricBaseChangedDiagram R Ω j f) :=
  (Over.pullback f).mapCone
    (Over.liftCone (diagram R Ω) (chartGeometricStructureMap R Ω j) (specCone R Ω)
      (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j)
      (chartGeometricStructure_fac R Ω j))

/-- The literal original-base fibre-product cone is a limit. -/
def chartGeometricBaseChangedConeIsLimit :
    IsLimit ((Over.forget X).mapCone (chartGeometricBaseChangedCone R Ω j f)) :=
  Scheme.FixedBaseChange.isLimitCone (diagram R Ω) (chartGeometricStructureMap R Ω j) f
    (specCone R Ω) (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j)
    (chartGeometricStructure_fac R Ω j) (specConeIsLimit R Ω)

instance chartGeometricBaseChangedDiagram_compactSpace [QuasiCompact f]
    (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
    CompactSpace ((chartGeometricBaseChangedDiagram R Ω j f).obj i).left := by
  have hcompact (k : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      CompactSpace ((diagram R Ω).obj k) :=
    inferInstanceAs (CompactSpace (Spec (.of k.unop.algebra)))
  exact Scheme.FixedBaseChange.obj_compactSpace
    (diagram R Ω) (chartGeometricStructureMap R Ω j) f i

instance chartGeometricBaseChangedDiagram_quasiSeparatedSpace [QuasiSeparated f]
    (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
    QuasiSeparatedSpace ((chartGeometricBaseChangedDiagram R Ω j f).obj i).left := by
  have hqs (k : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      QuasiSeparatedSpace ((diagram R Ω).obj k) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of k.unop.algebra)))
  exact Scheme.FixedBaseChange.obj_quasiSeparatedSpace
    (diagram R Ω) (chartGeometricStructureMap R Ω j) f i

instance chartGeometricBaseChangedDiagram_map_isAffineHom
    {i k : (GeometricEtaleNeighborhood R Ω)ᵒᵖ} (a : i ⟶ k) :
    IsAffineHom ((chartGeometricBaseChangedDiagram R Ω j f).map a).left := by
  have haffine {i k : (GeometricEtaleNeighborhood R Ω)ᵒᵖ} (a : i ⟶ k) :
      IsAffineHom ((diagram R Ω).map a) :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom a.unop.val.toRingHom)))
  exact Scheme.FixedBaseChange.map_isAffineHom
    (diagram R Ω) (chartGeometricStructureMap R Ω j) f a

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
