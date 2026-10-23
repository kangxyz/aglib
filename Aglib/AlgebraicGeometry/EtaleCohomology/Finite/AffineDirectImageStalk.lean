/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageStalkStages
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.TupleStalkColimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FiniteAffineModel
public import Aglib.RingTheory.Henselian.StrictHenselization.SeparablyClosedResidue

/-! # Original finite direct-image stalks over affine bases -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

/-- The original finite scheme after the actual strict-local base change. -/
abbrev finiteAffineSource : Scheme.{u} := (baseChangedEtaleCone R Ω f).pt.left

/-- The native finite structural projection, without a presentation hypothesis. -/
abbrev finiteAffineProjection : finiteAffineSource R Ω f ⟶
    Spec (.of (GeometricEtaleColimit R Ω)) :=
  pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f

/-- The product uses the actual finite algebra of global functions on the
original strict-local base change and its individual residue-field points. -/
def finiteAffineStalkTuple (F : AbelianSheaf.{u, u + 1} X) : AddCommGrpCat.{u + 1} := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  exact finiteSourceStalkTuple Γ(Y, ⊤) B (baseChangedEtaleDiagram R Ω f)
    (baseChangedEtaleCone R Ω f) Y.isoSpec.symm F

/-- The original direct-image stalk is the product of actual component stalks.
Neither the finite morphism nor its source is required to be finitely presented. -/
def finiteAffineDirectImageStalkIso (F : AbelianSheaf.{u, u + 1} X) :
    (pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber.obj ((directImage f).obj F).obj ≅
      finiteAffineStalkTuple R Ω f F := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  have hcompact (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      CompactSpace ((diagram R Ω).obj i) :=
    inferInstanceAs (CompactSpace (Spec (.of i.unop.algebra)))
  have hqs (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      QuasiSeparatedSpace ((diagram R Ω).obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of i.unop.algebra)))
  have haffine {i j : (GeometricEtaleNeighborhood R Ω)ᵒᵖ} (a : i ⟶ j) :
      IsAffineHom ((diagram R Ω).map a) :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom a.unop.val.toRingHom)))
  have hsourcecompact (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      CompactSpace ((baseChangedEtaleDiagram R Ω f).obj i).left :=
    Scheme.FixedBaseChange.obj_compactSpace (diagram R Ω) (structureMap R Ω) f i
  have hsourceqs (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
      QuasiSeparatedSpace ((baseChangedEtaleDiagram R Ω f).obj i).left :=
    Scheme.FixedBaseChange.obj_quasiSeparatedSpace (diagram R Ω) (structureMap R Ω) f i
  have hsourceaffine {i j : (GeometricEtaleNeighborhood R Ω)ᵒᵖ} (a : i ⟶ j) :
      IsAffineHom ((baseChangedEtaleDiagram R Ω f).map a).left :=
    Scheme.FixedBaseChange.map_isAffineHom (diagram R Ω) (structureMap R Ω) f a
  exact directImageStalkStagesIso R Ω f F ≪≫
    finiteSourceStalkTupleIso Γ(Y, ⊤) B (baseChangedEtaleDiagram R Ω f)
      (baseChangedEtaleCone R Ω f) Y.isoSpec.symm F (baseChangedEtaleConeIsLimit R Ω f)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
