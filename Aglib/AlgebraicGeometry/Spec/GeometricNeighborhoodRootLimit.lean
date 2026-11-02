/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodBaseChange
public import Aglib.AlgebraicGeometry.Spec.RootBaseChange

/-! # The original root algebra over the geometric neighborhood limit

Keep the original root algebra fixed. Its native base-change diagram has the
literal root algebra over the original neighborhood colimit as limit, via the
canonical root/tensor comparison. No second ring colimit is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

open EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] (N : ℕ) (f : R)

local notation "T" => RootAlgebra N f
local notation "C" => GeometricEtaleColimit R Ω

/-- The existing base-change diagram with the original root spectrum held fixed. -/
abbrev rootDiagram : (GeometricEtaleNeighborhood R Ω)ᵒᵖ ⥤ Scheme.{u} :=
  baseChangedDiagram R Ω (Spec.algebraMap R T) ⋙ Over.forget (Spec (.of T))

/-- The original second projections give the structure over the fixed root spectrum. -/
abbrev rootStructure : rootDiagram R Ω N f ⟶
    (Functor.const _).obj (Spec (.of T)) :=
  FixedBaseChange.baseStructure (diagram R Ω) (structureMap R Ω) (Spec.algebraMap R T)

/-- The existing pullback cone, with apex identified with the actual root algebra
of the original geometric neighborhood colimit. -/
def rootCone : Cone (rootDiagram R Ω N f) :=
  ((Over.forget (Spec (.of T))).mapCone
    (baseChangedCone R Ω (Spec.algebraMap R T))).extend
      (rootBaseChangeSpecIso R C N f).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual root-spectrum cone is limiting. -/
def rootConeIsLimit : IsLimit (rootCone R Ω N f) :=
  IsLimit.extendIso
    (s := (Over.forget (Spec (.of T))).mapCone
      (baseChangedCone R Ω (Spec.algebraMap R T)))
    (rootBaseChangeSpecIso R C N f).hom
    (baseChangedConeIsLimit R Ω (Spec.algebraMap R T))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The coefficient projection retains the original stage projection from the
original ring colimit, not a replacement root or coefficient model. -/
@[reassoc]
theorem rootCone_π_fst (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
    (rootCone R Ω N f).π.app i ≫
        pullback.fst (Spec.algebraMap R i.unop.algebra) (Spec.algebraMap R T) =
      Spec.algebraMap C (RootAlgebra N (algebraMap R C f)) ≫ (specCone R Ω).π.app i := by
  change ((rootBaseChangeSpecIso R C N f).hom ≫
    pullback.lift
      (pullback.fst (Spec.algebraMap R C) (Spec.algebraMap R T) ≫
        (specCone R Ω).π.app i)
      (pullback.snd (Spec.algebraMap R C) (Spec.algebraMap R T)) _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (rootBaseChangeSpecIso R C N f).hom ≫ q)
      (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ (specCone R Ω).π.app i)
          (rootBaseChangeSpecIso_hom_fst R C N f))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole fixed-root structural equation uses the original root-change map. -/
@[reassoc]
theorem rootCone_π_structure (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
    (rootCone R Ω N f).π.app i ≫ (rootStructure R Ω N f).app i =
      Spec.map (CommRingCat.ofHom (rootBaseChangeHom C N f).toRingHom) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (rootBaseChangeSpecIso R C N f).hom ≫ q)
      (FixedBaseChange.cone_fac (diagram R Ω) (structureMap R Ω) (Spec.algebraMap R T)
        (specCone R Ω) (Spec.algebraMap R C) (fun j => π_structure R Ω j.unop) i)).trans
      (rootBaseChangeSpecIso_hom_snd R C N f))

/-- The entire cone is over the original fixed root algebra. -/
theorem rootCone_structure :
    (rootCone R Ω N f).π ≫ rootStructure R Ω N f =
      (Functor.const _).map
        (Spec.map (CommRingCat.ofHom (rootBaseChangeHom C N f).toRingHom)) := by
  ext i
  exact rootCone_π_structure R Ω N f i

instance rootDiagram_isAffine (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
    IsAffine ((rootDiagram R Ω N f).obj i) := by
  change IsAffine (pullback (Spec.algebraMap R i.unop.algebra) (Spec.algebraMap R T))
  exact isAffine_of_isAffineHom (pullback.snd _ _)

instance rootDiagram_map_isAffineHom
    {i j : (GeometricEtaleNeighborhood R Ω)ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom ((rootDiagram R Ω N f).map g) := inferInstance

end AlgebraicGeometry.Scheme.Kummer
