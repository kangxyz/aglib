/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Smooth.RelativeRepresentative
public import Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy
public import Aglib.AlgebraicGeometry.Curves.Projectivity.AffineMap
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Smoothness of the same curve Picard representative

An actual residue-field point supplies a section after faithfully flat base
change. The existing affine map to the projective line and two-affine lifting
prove smoothness of that same base-changed representative. Smoothness descends
to the original representative; no fine-stratum existence construction is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

set_option backward.isDefEq.respectTransparency.types false in
/-- A supplied locally finite type Picard representative of a proper integral
curve is smooth, by actual two-affine lifting and faithfully flat descent. -/
theorem smooth_representative_of_proper_integral_curve
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsProper p] [Flat p] [GeometricallyIntegral p] [IsIntegral X]
    (hdim : topologicalKrullDim X = 1)
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf p).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    Smooth P.obj.hom := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  let : Algebra k (X.residueField x) :=
    ((X.residue x).hom.comp (p.stalkScalar x)).toAlgebra
  have hy : X.fromSpecResidueField x ≫ p =
      (specOver k (X.residueField x)).hom := by
    rw [Scheme.fromSpecResidueField, Category.assoc, fromSpecStalk_comp_eq_spec_map_stalkScalar,
      ← Spec.map_comp]
    rfl
  let o := pullback.lift (X.fromSpecResidueField x) (𝟙 _) (by rw [hy, Category.id_comp])
  have ho : o ≫ pullback.snd p (specOver k (X.residueField x)).hom = 𝟙 _ :=
    pullback.lift_snd _ _ _
  let : IsProper (pullback.snd p (specOver k (X.residueField x)).hom) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  let : IsLocallyNoetherian (specOver k (X.residueField x)).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of (X.residueField x))))
  obtain ⟨ρ, hρ⟩ :=
    OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1 p hdim
  let := isAffineHom_pullback_fst_specOver p (X.residueField x)
  let PK := LocallyNoetherianOver.baseChange (specOver k (X.residueField x)).hom P
  let RK := baseChangeRepresentableBy p (specOver k (X.residueField x)).hom P R
  let : LocallyOfFiniteType PK.obj.hom :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd P.obj.hom (specOver k (X.residueField x)).hom))
  have hsK : Smooth (pullback.snd P.obj.hom (specOver k (X.residueField x)).hom) :=
    smooth_representative_of_isAffineHom_projectiveP1
      (pullback.snd p (specOver k (X.residueField x)).hom) o ho PK RK
      (pullback.fst p (specOver k (X.residueField x)).hom ≫ ρ)
  let : Nonempty (specOver k (X.residueField x)).left :=
    inferInstanceAs (Nonempty (Spec (.of (X.residueField x))))
  let : Surjective (specOver k (X.residueField x)).hom :=
    ⟨Function.surjective_to_subsingleton _⟩
  let : Flat (specOver k (X.residueField x)).hom :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : QuasiCompact (specOver k (X.residueField x)).hom :=
    (inferInstance : QuasiCompact (Spec.algebraMap k (X.residueField x)))
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := P.obj.hom)
    (g := (specOver k (X.residueField x)).hom) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsK

end AlgebraicGeometry.Scheme.RelativePicard

namespace AlgebraicGeometry.Scheme.OverField.Curve

/-- Smoothness for the original representative of a smooth proper connected curve. -/
theorem smooth_picardRepresentative_of_locallyFiniteType
    {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (RelativePicard.fppfPicardSheaf X.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    Smooth P.obj.hom := by
  let := hX.proper
  let := hX.smooth
  let := hX.isGeometricallyIntegral
  let := hX.isIntegral
  exact RelativePicard.smooth_representative_of_proper_integral_curve X.hom
    (curveProperties_dimension smoothFieldDimension hX) P R

end AlgebraicGeometry.Scheme.OverField.Curve
