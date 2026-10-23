/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineDirectImageStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageStalkNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.TupleStalkNaturality

/-! # Original finite direct-image stalks preserve epimorphisms over affine bases -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
  {F G : AbelianSheaf.{u, u + 1} X} (α : F ⟶ G) [Epi α]

/-- Every prescribed original direct-image stalk element lifts under the image
of an epimorphism of original sheaves. -/
theorem finiteAffineDirectImage_stalkMap_surjective :
    Function.Surjective ((pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber.map
      ((directImage f).map α).hom) := by
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
  have hsurj := finiteSourceSectionsColimitMap_surjective Γ(Y, ⊤) B
    (baseChangedEtaleDiagram R Ω f) (baseChangedEtaleCone R Ω f) Y.isoSpec.symm α
      (baseChangedEtaleConeIsLimit R Ω f)
  intro z
  let E := directImageStalkStagesIso R Ω f F
  let K := directImageStalkStagesIso R Ω f G
  obtain ⟨y, hy⟩ := hsurj (K.hom z)
  refine ⟨E.inv y, (ConcreteCategory.bijective_of_isIso K.hom).1 ?_⟩
  exact (ConcreteCategory.congr_hom
    (directImageStalkStagesIso_naturality R Ω f α) (E.inv y)).trans
    ((congrArg (colim.map (Functor.whiskerLeft (baseChangedEtaleDiagram R Ω f).op α.hom))
      (ConcreteCategory.congr_hom E.inv_hom_id y)).trans hy)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
