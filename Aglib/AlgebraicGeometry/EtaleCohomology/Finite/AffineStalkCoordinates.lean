/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineDirectImageStalk

/-! # Literal original germ coordinates of the finite direct-image stalk product -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
  (F : AbelianSheaf.{u, u + 1} X)

/-- Every coordinate of the actual finite stalk isomorphism is its original
component germ, with the actual stage section unchanged. -/
theorem germ_finiteAffineDirectImageStalkIso (i : GeometricEtaleNeighborhood R Ω)
    (a : ((directImage f).obj F).obj.obj (op (etaleObject R Ω i))) :
    let B := GeometricEtaleColimit R Ω
    let Y := finiteAffineSource R Ω f
    let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
    let : IsFinite p := inferInstanceAs (IsFinite
      (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
    let : IsAffine Y := isAffine_of_isAffineHom p
    let := finiteSourceAlgebra B p
    let := finiteSource_moduleFinite B p
    ∀ m : MaximalSpectrum Γ(Y, ⊤),
      (finiteAffineDirectImageStalkIso R Ω f F).hom
        ((pointSmallEtale (Spec.algebraMap R Ω)).toPresheafFiber
          (etaleObject R Ω i) (stagePoint R Ω i) ((directImage f).obj F).obj a) m =
        (finiteSourceComponentPoint Γ(Y, ⊤) B
          (Y.isoSpec.inv ≫ (baseChangedEtaleCone R Ω f).pt.hom) m).toPresheafFiber
          ((baseChangedEtaleDiagram R Ω f).obj (op i))
          (finiteLimitStagePoint Γ(Y, ⊤) B (baseChangedEtaleDiagram R Ω f)
            (baseChangedEtaleCone R Ω f) Y.isoSpec.symm (op i) m) F.obj a := by
  dsimp only
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  intro m
  let D := baseChangedEtaleDiagram R Ω f
  let c := baseChangedEtaleCone R Ω f
  let e := Y.isoSpec.symm
  let t := finiteSourceColimitToStalkTuple Γ(Y, ⊤) B D c e F
  have h₁ := ConcreteCategory.congr_hom
    (germ_directImageStalkStagesIso_hom R Ω f F i) a
  have h₂ := ConcreteCategory.congr_hom
    (ι_finiteSourceColimitToStalkTuple Γ(Y, ⊤) B D c e F (op (op i))) a
  exact congrFun ((congrArg t h₁).trans h₂) m

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
