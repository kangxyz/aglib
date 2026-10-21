/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.DVRRecognition
public import Aglib.AlgebraicGeometry.Stalk.EtaleCurveDVR
public import Aglib.AlgebraicGeometry.Stalk.OpenSmoothCurveDVR
public import Aglib.AlgebraicGeometry.FunctionField.MorphismExt
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.SingularNormalization
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.SmoothLoci
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.WeierstrassStrictTransformCover
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.WeierstrassSections

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.StrictTransformRecognition`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`00634eaeb53cba8a79080a092e417669bd32d9ee12b63836afb36adc5f15b8db`.
Actual strict-original function-field comparison, normalization lift, pointwise DVR applicability,
  positive-thickness recognition and the original P1 maps. The source1012+ SplitRationalComponents
  record adapter is excluded. Actual etale charts use the proved regularity descent and
  smooth-stalk suppliers. The parametric H and DVR-locus inputs remain explicit; no
  purity or global regularity theorem is inferred. The infinity point reuses the native
  infinityPoint; its short chart proof also follows the source-present
  PresentationComponents471–506 argument.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode WeierstrassCurve
open AlgebraicGeometry.Scheme.FunctionField AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

section StrictTransformBirational

/-! The actual unchanged-open triangle identifies the strict transform's
function field with the SAME original cubic, preserving residue constants. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
attribute [local instance] specialFibre_isIntegral
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "f" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))


local notation "C" => strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "q" => finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

local instance punctured_integral : IsIntegral (q ⁻¹ᵁ originalPuncturedOpen he).toScheme :=
  strictPunctured_integral M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

/-- The canonical morphism from the strict punctured open to its scheme-theoretic image, the
strict transform. -/
abbrev strictOpenMap : (V).toScheme ⟶ C := AlgebraicGeometry.Scheme.Hom.toImage (V).ι

/-- The strict transform mapped to the original special fibre through its inclusion in the final
special fibre. -/
def strictOriginalMap : C ⟶ specialFibre W := i ≫ q

@[reassoc] lemma strictOpen_original :
    strictOpenMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
      strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc =
      (q ∣_ originalPuncturedOpen he) ≫ (originalPuncturedOpen he).ι := by
  rw [strictOriginalMap, ← Category.assoc, AlgebraicGeometry.Scheme.Hom.Image.openMap_inclusion]
  exact (morphismRestrict_ι _ _).symm

instance strictOriginalMap_dominant : IsDominant
    (strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) := by
  have : IsDominant ((q ∣_ originalPuncturedOpen he) ≫ (originalPuncturedOpen he).ι) :=
    AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _
  have : IsDominant (strictOpenMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
      strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) := by
    rw [strictOpen_original]
    infer_instance
  exact IsDominant.of_comp (strictOpenMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) _

@[reassoc] lemma strictOriginalMap_over :
    strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ pullback.snd (structureMap W) r =
      i ≫ pullback.snd (f ≫ structureMap W) r := by
  simp [strictOriginalMap]

instance strictOriginalMap_functionField_isIso : IsIso (CommRingCat.ofHom (functionFieldMap
    (strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc))) := by
  let j := strictOpenMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
  let t := strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
  let : IsDominant j := AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _
  let := AlgebraicGeometry.Scheme.FunctionField.fieldMap_isIso j
  have : IsOpenImmersion (j ≫ t) := by
    dsimp [j, t]
    rw [strictOpen_original]
    infer_instance
  let := AlgebraicGeometry.Scheme.FunctionField.fieldMap_isIso (j ≫ t)
  have : IsIso (CommRingCat.ofHom (functionFieldMap t) ≫ CommRingCat.ofHom (functionFieldMap j))
    := by
    change IsIso (CommRingCat.ofHom ((functionFieldMap j).comp (functionFieldMap t)))
    rw [← functionFieldMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (CommRingCat.ofHom (functionFieldMap j))

/-- A genuine field identification induced by the actual closed-fibre map. -/
def strictOriginalFieldEquiv : (specialFibre W).functionField ≃+* (C).functionField :=
  (asIso (CommRingCat.ofHom (functionFieldMap
    (strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)))).commRingCatIsoToRingEquiv

lemma strictOriginalFieldEquiv_constants :
    (strictOriginalFieldEquiv M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).toRingHom.comp
      (AlgebraicGeometry.Scheme.functionFieldConstants _ (pullback.snd (structureMap W) r)) =
      AlgebraicGeometry.Scheme.functionFieldConstants _ (i ≫ pullback.snd (f ≫ structureMap W) r)
        := by
  exact (AlgebraicGeometry.Scheme.FunctionField.map_constants
    (strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) _).trans
    (congrArg (AlgebraicGeometry.Scheme.functionFieldConstants _)
      (strictOriginalMap_over M π hπ n hn a ha he ρ hρ hex hp hatlas hbc))

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end StrictTransformBirational


section AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift

/-! A proved helper lifting an actual P1 map through a proper integral
birational target. The only extension input is the EXISTING general
NormalProperCurveGenericExtension family. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift
variable (k : Type u) [Field k] {Z C : Scheme.{u}} [IsIntegral Z] [IsIntegral C]
  (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
  (sC : C ⟶ Spec (.of k)) [IsSeparated sC]
  (f : Z ⟶ C) [IsDominant f]
  [IsIso (CommRingCat.ofHom (functionFieldMap f))]
  (hf : f ≫ sC = sZ)
local notation "P" => AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k
local notation "sP" => AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k
variable (g : AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k ⟶ C) [IsDominant g]
  (hg : g ≫ sC = AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k)

/-- The function-field homomorphism from `Z` to `P` obtained by inverting the field map of `f` and
composing with that of `g`. -/
def fieldMap (f : Z ⟶ C) [IsDominant f]
    [IsIso (CommRingCat.ofHom (functionFieldMap f))]
    (g : P ⟶ C) [IsDominant g] : Z.functionField →+* (P).functionField :=
  (functionFieldMap g).comp
    (asIso (CommRingCat.ofHom (functionFieldMap f))).commRingCatIsoToRingEquiv.symm.toRingHom

include hf hg in
omit [IsProper sZ] [IsSeparated sC] in
lemma fieldMap_constants :
    (fieldMap k f g).comp (AlgebraicGeometry.Scheme.functionFieldConstants _ sZ) =
      AlgebraicGeometry.Scheme.functionFieldConstants _ sP := by
  let e := (asIso (CommRingCat.ofHom (functionFieldMap f))).commRingCatIsoToRingEquiv
  have hfc : e.toRingHom.comp (AlgebraicGeometry.Scheme.functionFieldConstants _ sC) =
      AlgebraicGeometry.Scheme.functionFieldConstants _ sZ :=
    (AlgebraicGeometry.Scheme.FunctionField.map_constants f sC).trans
      (congrArg (AlgebraicGeometry.Scheme.functionFieldConstants _) hf)
  have hgc : (functionFieldMap g).comp (AlgebraicGeometry.Scheme.functionFieldConstants _ sC) =
      AlgebraicGeometry.Scheme.functionFieldConstants _ sP :=
    (AlgebraicGeometry.Scheme.FunctionField.map_constants g sC).trans
      (congrArg (AlgebraicGeometry.Scheme.functionFieldConstants _) hg)
  ext c
  change functionFieldMap g (e.symm (AlgebraicGeometry.Scheme.functionFieldConstants _ sZ c)) = _
  have hc : AlgebraicGeometry.Scheme.functionFieldConstants _ sZ c = e
    (AlgebraicGeometry.Scheme.functionFieldConstants _ sC c) :=
    (DFunLike.congr_fun hfc c).symm
  rw [hc, e.symm_apply_apply]
  exact DFunLike.congr_fun hgc c

variable (H : NormalProperCurveGenericExtension.{u})

/-- Constructed from the actual inverse birational field map. -/
def lift : P ⟶ Z :=
  extend sP sZ (fieldMap k f g) H inferInstance
    (WeierstrassCurve.CriticalCubic.parameterProjectiveLine_smooth k)
    (WeierstrassCurve.CriticalCubic.parameterProjectiveLine_normal k) inferInstance
    (fieldMap_constants k sZ sC f hf g hg)

omit [IsSeparated sC] in
@[reassoc] lemma lift_over : lift k sZ sC f hf g hg H ≫ sZ = sP :=
  extend_over _ _ _ _ _ _ _ _ _

omit [IsSeparated sC] in
lemma lift_generic : (P).fromSpecStalk (genericPoint P) ≫ lift k sZ sC f hf g hg H =
    genericMap (fieldMap k f g) := extend_generic _ _ _ _ _ _ _ _ _

instance lift_dominant : IsDominant (lift k sZ sC f hf g hg H) :=
  extend_dominant _ _ _ _ _ _ _ _ _

omit [IsSeparated sC] in
lemma lift_fieldMap : functionFieldMap (lift k sZ sC f hf g hg H) = fieldMap k f g :=
  extend_fieldMap _ _ _ _ _ _ _ _ _

/-- Separated uniqueness recovers the SAME original map globally. -/
@[reassoc] lemma lift_comp : lift k sZ sC f hf g hg H ≫ f = g := by
  apply AlgebraicGeometry.Scheme.FunctionField.hom_ext sC
  · rw [Category.assoc, hf, lift_over, hg]
  · rw [functionFieldMap_comp, lift_fieldMap]
    ext z
    change functionFieldMap g
      ((asIso (CommRingCat.ofHom (functionFieldMap f))).commRingCatIsoToRingEquiv.symm
        ((asIso (CommRingCat.ofHom (functionFieldMap f))).commRingCatIsoToRingEquiv z)) = _
    rw [RingEquiv.symm_apply_apply]

end AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift

end -- noncomputable section
end AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift


section WeierstrassStrictNormalization

/-! The actual normalization of the original special cubic lifted into its
constructed integral strict transform, then into the SAME final special fibre.
No extension theorem is applied to the possibly reducible whole fibre. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
attribute [local instance] specialFibre_isIntegral
  WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "f" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))


local notation "C" => strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "q" => finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ n hn a ha he ρ hρ hex hp hatlas hbc


variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
local notation "k" => ResidueField R
local notation "P1" => AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k
local notation "sP1" => AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k
local notation "sC" => pullback.snd (structureMap W) r
local notation "sZ" => i ≫ pullback.snd (f ≫ structureMap W) r
local notation "t" => strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

/-- The existing explicit original normalization, transported by the actual
coefficient/special-fibre isomorphism. -/
def originalSpecialNormalization : P1 ⟶ specialFibre W :=
  WeierstrassCurve.CriticalCubic.SingularNormalization.originalNormalization
    (W.map (IsLocalRing.residue R)) x y he hx hy H ≫
    (specialCoefficientIso W).hom

instance originalSpecialNormalization_dominant : IsDominant (originalSpecialNormalization he hx hy
  H) := by
  dsimp [originalSpecialNormalization]
  infer_instance

@[reassoc] lemma originalSpecialNormalization_over :
    originalSpecialNormalization he hx hy H ≫ sC = sP1 := by
  simp only [originalSpecialNormalization, Category.assoc, specialCoefficientIso_hom_snd]
  exact WeierstrassCurve.CriticalCubic.SingularNormalization.originalNormalization_over (W.map
    (IsLocalRing.residue R)) x y he hx hy H

/-- The global P1 map to the genuinely constructed proper integral closure. -/
def strictNormalization : P1 ⟶ C :=
  AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift.lift k sZ sC t
    (strictOriginalMap_over M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
    (originalSpecialNormalization he hx hy H) (originalSpecialNormalization_over he hx hy H) H

@[reassoc] lemma strictNormalization_over :
    strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H ≫ sZ = sP1 :=
  AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift.lift_over _ _ _ _ _ _ _ _

lemma strictNormalization_generic : (P1).fromSpecStalk (genericPoint P1) ≫
    strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H =
    AlgebraicGeometry.Scheme.FunctionField.GenericExtension.genericMap
      (AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift.fieldMap k t
        (originalSpecialNormalization he hx hy H)) :=
  AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift.lift_generic _ _ _ _ _ _ _ _

@[reassoc] lemma strictNormalization_original :
    strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H ≫ t =
      originalSpecialNormalization he hx hy H :=
  AlgebraicGeometry.Scheme.ProjectiveLine.BirationalLift.lift_comp _ _ _ _ _ _ _ _

/-- The actual global P1 component candidate in the same final special fibre.
This declaration alone makes no finiteness, immersion, or coverage claim. -/
def strictP1ToFinal : P1 ⟶ finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc :=
  strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H ≫ i

@[reassoc] lemma strictP1ToFinal_over :
    strictP1ToFinal M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H ≫
      pullback.snd (f ≫ structureMap W) r = sP1 := by
  simpa only [strictP1ToFinal, Category.assoc] using
    strictNormalization_over M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H

@[reassoc] lemma strictP1ToFinal_original :
    strictP1ToFinal M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H ≫ q =
      originalSpecialNormalization he hx hy H := by
  simpa only [strictP1ToFinal, strictOriginalMap, Category.assoc] using
    strictNormalization_original M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H


/-- On the actual inverse image of the punctured cubic the global map is
exactly the canonical inverse of the unchanged-open isomorphism. Its map
to the original cubic is the original normalization by the preceding triangle. -/
lemma strictP1ToFinal_punctured :
    let h := strictP1ToFinal M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H
    (h ⁻¹ᵁ V).ι ≫ h =
      ((h ≫ q) ∣_ originalPuncturedOpen he) ≫
        inv (q ∣_ originalPuncturedOpen he) ≫ (V).ι := by
  dsimp only
  let h := strictP1ToFinal M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H
  change (h ⁻¹ᵁ V).ι ≫ h = _
  rw [morphismRestrict_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact (morphismRestrict_ι h V).symm

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictNormalization


section WeierstrassStrictNormalizationApplicability
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
attribute [local instance] specialFibre_isIntegral
  WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "f" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))


local notation "C" => strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "q" => finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ n hn a ha he ρ hρ hex hp hatlas hbc


variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
local notation "k" => ResidueField R
local notation "P1" => AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k
local notation "sP1" => AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k
local notation "sC" => pullback.snd (structureMap W) r
local notation "sZ" => i ≫ pullback.snd (f ≫ structureMap W) r
local notation "t" => strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

instance strictTransform_noetherian : IsLocallyNoetherian C :=
  LocallyOfFiniteType.isLocallyNoetherian i

/-- Applicability of the already constructed original normalization lift. -/
instance strictNormalization_dominant : IsDominant
    (strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H) := by
  unfold strictNormalization
  infer_instance

instance strictNormalization_proper : IsProper
    (strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H) := by
  have : IsProper
      (strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H ≫ sZ) := by
    rw [strictNormalization_over]
    infer_instance
  exact IsProper.of_comp _ sZ

instance strictNormalization_surjective : Surjective
    (strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H) := by
  infer_instance

instance originalSpecialNormalization_functionField_isIso : IsIso (CommRingCat.ofHom
    (functionFieldMap (originalSpecialNormalization he hx hy H))) := by
  let normalizationMap : P1 ⟶ scheme (W.map (IsLocalRing.residue R)) :=
    WeierstrassCurve.CriticalCubic.SingularNormalization.originalNormalization
      (W.map (IsLocalRing.residue R)) x y he hx hy H
  let coefficientMap : scheme (W.map (IsLocalRing.residue R)) ⟶ specialFibre W :=
    (specialCoefficientIso W).hom
  let : IsIso coefficientMap := by
    dsimp [coefficientMap]
    infer_instance
  let : IsIso (CommRingCat.ofHom (functionFieldMap normalizationMap)) :=
    WeierstrassCurve.CriticalCubic.SingularNormalization.originalNormalization_functionField_isIso
      (W.map (IsLocalRing.residue R)) x y he hx hy H
  let : IsIso (CommRingCat.ofHom (functionFieldMap coefficientMap)) :=
    AlgebraicGeometry.Scheme.FunctionField.fieldMap_isIso coefficientMap
  change IsIso (CommRingCat.ofHom (functionFieldMap (normalizationMap ≫ coefficientMap)))
  rw [functionFieldMap_comp normalizationMap coefficientMap]
  change IsIso (CommRingCat.ofHom (functionFieldMap coefficientMap) ≫
    CommRingCat.ofHom (functionFieldMap normalizationMap))
  infer_instance

/-- The actual function-field map, rather than an independently chosen equivalence,
is an isomorphism by the original normalization triangle. -/
instance strictNormalization_functionField_isIso : IsIso (CommRingCat.ofHom
    (functionFieldMap (strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H)))
      := by
  have : IsIso (CommRingCat.ofHom (functionFieldMap t) ≫ CommRingCat.ofHom
      (functionFieldMap (strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H)))
        := by
    change IsIso (CommRingCat.ofHom
      ((functionFieldMap (strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy
        H)).comp
        (functionFieldMap t)))
    rw [← functionFieldMap_comp]
    simpa only [strictNormalization_original] using
      (inferInstance : IsIso (CommRingCat.ofHom
        (functionFieldMap (originalSpecialNormalization he hx hy H))))
  exact IsIso.of_isIso_comp_left (CommRingCat.ofHom (functionFieldMap t)) _

/-- Every genuine DVR target stalk supplies an actual open isomorphism of the
SAME strict normalization, via the existing general codimension-one family. -/
lemma strictNormalization_iso_near_dvr
    (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u})
    (z : strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
    [IsDiscreteValuationRing ((strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas
      hbc).presheaf.stalk z)] :
    ∃ U : (strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).Opens,
      z ∈ U ∧ IsIso ((strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H) ∣_
        U) :=
  hdvr _ _ (strictNormalization M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H) inferInstance z

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictNormalizationApplicability


section WeierstrassStrictInfinity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
attribute [local instance] specialFibre_isIntegral
  WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "f" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))


local notation "C" => strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "q" => finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ n hn a ha he ρ hρ hex hp hatlas hbc


variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
local notation "k" => ResidueField R
local notation "P1" => AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k
local notation "sP1" => AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k
local notation "sC" => pullback.snd (structureMap W) r
local notation "sZ" => i ≫ pullback.snd (f ≫ structureMap W) r
local notation "t" => strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc


/-- Lift the entire SAME original punctured cubic into its actual strict closure. -/
def strictPunctureOriginalLift : (originalPuncturedOpen he).toScheme ⟶ C :=
  inv (q ∣_ originalPuncturedOpen he) ≫
    strictOpenMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

instance strictPunctureOriginalLift_open : IsOpenImmersion
    (strictPunctureOriginalLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) := by
  unfold strictPunctureOriginalLift
  infer_instance

@[reassoc] lemma strictPunctureOriginalLift_original :
    strictPunctureOriginalLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ t =
      (originalPuncturedOpen he).ι := by
  rw [strictPunctureOriginalLift, Category.assoc, strictOpen_original]
  simp

/-- The point of the original special fibre determined by the base-changed infinity section. -/
def strictInfinityOriginalPoint : specialFibre W :=
  baseChangedInfinitySection (S := k) W (genericPoint (Spec (.of k)))

lemma strictInfinityOriginalPoint_coefficient :
    (specialCoefficientIso W).hom (WeierstrassCurve.Projective.infinityPoint (W.baseChange k)) =
      strictInfinityOriginalPoint (W := W) := by
  have hp : IsLocalRing.closedPoint k = genericPoint (Spec (.of k)) := Subsingleton.elim _ _
  have hpointed : infinitySection (W.baseChange k) ≫ (specialCoefficientIso W).hom =
      baseChangedInfinitySection (S := k) W := coefficientBaseChangeIso_pointed (S := k) W
  change (specialCoefficientIso W).hom
      (infinitySection (W.baseChange k) (IsLocalRing.closedPoint k)) =
    baseChangedInfinitySection (S := k) W (genericPoint (Spec (.of k)))
  calc
    _ = (specialCoefficientIso W).hom
        (infinitySection (W.baseChange k) (genericPoint (Spec (.of k)))) :=
      congrArg (specialCoefficientIso W).hom (congrArg (infinitySection (W.baseChange k)) hp)
    _ = _ :=
      (Scheme.Hom.comp_apply (infinitySection (W.baseChange k))
        (specialCoefficientIso W).hom (genericPoint (Spec (.of k)))).symm.trans
          (congrArg (fun sectionMap : Spec (.of k) ⟶ specialFibre W =>
            sectionMap (genericPoint (Spec (.of k)))) hpointed)

lemma strictInfinityOriginalPoint_mem : strictInfinityOriginalPoint (W := W) ∈
    originalPuncturedOpen he := by
  change pullback.fst (structureMap W) r
    (baseChangedInfinitySection (S := k) W (genericPoint (Spec (.of k)))) ∈
      residueNodeComplement W x y he
  change (baseChangedInfinitySection (S := k) W ≫ pullback.fst (structureMap W) r)
    (genericPoint (Spec (.of k))) ∈ _
  have ht : baseChangedInfinitySection (S := k) W ≫ pullback.fst (structureMap W) r =
      r ≫ infinitySection W := pullback.lift_fst _ _ _
  rw [ht]
  exact infinitySection_range_subset_nodeComplement W x y he
    ⟨r (genericPoint (Spec (.of k))), rfl⟩

/-- The original infinity point regarded as a point of the punctured special fibre. -/
def strictInfinityPuncturedPoint : (originalPuncturedOpen he).toScheme :=
  ⟨strictInfinityOriginalPoint (W := W), strictInfinityOriginalPoint_mem he⟩

/-- The lift of the original punctured infinity point to the strict transform. -/
def strictInfinityPoint : C :=
  strictPunctureOriginalLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
    (strictInfinityPuncturedPoint he)

/-- The actual unchanged original infinity point supplies a genuine DVR stalk
of the same strict scheme, even before global strict-curve recognition. -/
lemma strictInfinityPoint_dvr :
    IsDiscreteValuationRing ((C).presheaf.stalk
      (strictInfinityPoint M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)) := by
  have : IsDiscreteValuationRing ((specialFibre W).presheaf.stalk
      (strictInfinityOriginalPoint (W := W))) := by
    rw [← strictInfinityOriginalPoint_coefficient]
    let coefficientCurve := W.baseChange k
    let infinityChartPoint : Spec (.of (infinitySmoothRing coefficientCurve)) :=
      infinitySmoothSection coefficientCurve (IsLocalRing.closedPoint k)
    have hq : infinitySmoothChart coefficientCurve infinityChartPoint =
        WeierstrassCurve.Projective.infinityPoint coefficientCurve := by
      change infinitySmoothChart coefficientCurve
          (infinitySmoothSection coefficientCurve (IsLocalRing.closedPoint k)) =
        infinitySection coefficientCurve (IsLocalRing.closedPoint k)
      exact (Scheme.Hom.comp_apply (infinitySmoothSection coefficientCurve)
        (infinitySmoothChart coefficientCurve) (IsLocalRing.closedPoint k)).symm.trans
          (congrArg (fun sectionMap : Spec (.of k) ⟶ scheme coefficientCurve =>
            sectionMap (IsLocalRing.closedPoint k)) (infinitySmoothSection_chart coefficientCurve))
    have : IsIntegral (scheme coefficientCurve) :=
      WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain coefficientCurve
    have : IsClosedImmersion (infinitySection coefficientCurve) :=
      isClosedImmersion_of_comp_eq_id (structureMap coefficientCurve)
        (infinitySection coefficientCurve) (infinitySection_structure coefficientCurve)
    have hc : IsClosed ({infinitySmoothChart coefficientCurve infinityChartPoint} :
        Set (scheme coefficientCurve)) := by
      rw [hq]
      simpa only [WeierstrassCurve.Projective.infinityPoint, Set.image_singleton] using
        (infinitySection coefficientCurve).isClosedMap {IsLocalRing.closedPoint k}
          isClosed_singleton
    let : IsDiscreteValuationRing ((scheme coefficientCurve).presheaf.stalk
        (WeierstrassCurve.Projective.infinityPoint coefficientCurve)) := by
      exact hq ▸ Scheme.smoothChart_closedPoint_dvr
        (infinitySmoothChart coefficientCurve) (structureMap coefficientCurve) infinityChartPoint hc
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (asIso ((specialCoefficientIso W).hom.stalkMap
        (WeierstrassCurve.Projective.infinityPoint (W.baseChange
          k)))).commRingCatIsoToRingEquiv.symm
  have : IsDiscreteValuationRing ((specialFibre W).presheaf.stalk
      ((originalPuncturedOpen he).ι (strictInfinityPuncturedPoint he))) := by
    change IsDiscreteValuationRing ((specialFibre W).presheaf.stalk
      (strictInfinityOriginalPoint (W := W)))
    infer_instance
  have : IsDiscreteValuationRing ((originalPuncturedOpen he).toScheme.presheaf.stalk
      (strictInfinityPuncturedPoint he)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (asIso ((originalPuncturedOpen he).ι.stalkMap
        (strictInfinityPuncturedPoint he))).commRingCatIsoToRingEquiv
  change IsDiscreteValuationRing ((C).presheaf.stalk
    (strictPunctureOriginalLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
      (strictInfinityPuncturedPoint he)))
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso ((strictPunctureOriginalLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).stalkMap
      (strictInfinityPuncturedPoint he))).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictInfinity


section WeierstrassPuncturedDVRCharts

/-! Actual Jacobian/infinity charts give DVR stalks on every displayed open
mapping into the original cubic away from its unique singular node. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open WeierstrassCurve.Projective
universe u
namespace WeierstrassCurve.Projective
variable {k : Type u} [Field k] (W : WeierstrassCurve k) (r s : k)
  (he : W.toAffine.Equation r s)
  (hx : W.toAffine.polynomialX.evalEval r s = 0)
  (hy : W.toAffine.polynomialY.evalEval r s = 0)

include hx hy

lemma exists_smooth_curve_chart_away_node (p : scheme W)
    (hp : p ≠ affineChart W (affineSingularPoint W r s he)) :
    ∃ (A : Scheme.{u}) (j : A ⟶ scheme W), IsOpenImmersion j ∧
      SmoothOfRelativeDimension 1 (j ≫ structureMap W) ∧ p ∈ Set.range j := by
  rcases affine_or_smoothInfinity W p with ha | hi
  · obtain ⟨q, rfl⟩ := ha
    have hq : q ≠ affineSingularPoint W r s he := fun h => hp (congrArg (affineChart W) h)
    have hg : affineGradientX W ∉ q.asIdeal ∨ affineGradientY W ∉ q.asIdeal := by
      simpa only [not_and_or] using
        mt (affine_singular_point_iff W r s he hx hy q).mpr hq
    rcases hg with hg | hg
    · refine ⟨_, affineSmoothChart W 0, inferInstance, inferInstance, ?_⟩
      apply (affineChart_mem_smoothChart_iff W 0 q).mpr
      simpa only [affineJacobian_zero, affineGradientX] using hg
    · refine ⟨_, affineSmoothChart W 1, inferInstance, inferInstance, ?_⟩
      apply (affineChart_mem_smoothChart_iff W 1 q).mpr
      simpa only [affineJacobian_one, affineGradientY] using hg
  · exact ⟨_, infinitySmoothChart W, inferInstance, inferInstance, hi⟩

/-- This pointwise consumer pulls back the actual smooth chart. Neither the
pulled chart nor the displayed open source is assumed integral. -/
lemma dvr_at_open_over_punctured_weierstrass
    {U Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (g : U ⟶ scheme W) [IsOpenImmersion g] (j : U ⟶ Y) [Etale j]
    (u : U) (hu : g u ≠ affineChart W (affineSingularPoint W r s he))
    (himage : j u ≠ genericPoint Y) :
    IsDiscreteValuationRing (Y.presheaf.stalk (j u)) := by
  obtain ⟨A, a, ha, hs, hga⟩ := exists_smooth_curve_chart_away_node W r s he hx hy (g u) hu
  let : IsOpenImmersion a := ha
  let : SmoothOfRelativeDimension 1 (a ≫ structureMap W) := hs
  have hpre : u ∈ Set.range (pullback.fst g a) := by
    rw [Scheme.Pullback.range_fst]
    exact hga
  obtain ⟨v, rfl⟩ := hpre
  have : SmoothOfRelativeDimension 1
      (pullback.snd g a ≫ a ≫ structureMap W) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  have hne : (pullback.fst g a ≫ j) v ≠ genericPoint Y := by
    simpa only [Scheme.Hom.comp_apply] using himage
  have hdvr := Scheme.dvr_at_image_of_etale_smooth_curve_chart_any_point k
    (pullback.fst g a ≫ j) (pullback.snd g a ≫ a ≫ structureMap W) inferInstance v hne
  exact hdvr

end WeierstrassCurve.Projective

end -- noncomputable section
end WeierstrassPuncturedDVRCharts


section WeierstrassStrictPunctureDVR
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
attribute [local instance] specialFibre_isIntegral
  WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "f" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))


local notation "C" => strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "q" => finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ n hn a ha he ρ hρ hex hp hatlas hbc


variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
local notation "k" => ResidueField R
local notation "P1" => AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k
local notation "sP1" => AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k
local notation "sC" => pullback.snd (structureMap W) r
local notation "sZ" => i ≫ pullback.snd (f ≫ structureMap W) r
local notation "t" => strictOriginalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc


lemma affinePointEval_comp_residueCoefficient :
    (affinePointEval (W.map (IsLocalRing.residue R)) x y he).comp
      (affineCoefficientMap W (IsLocalRing.residue R)) = affineResidueEval W x y he := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      change affinePointEval (W.map (IsLocalRing.residue R)) x y he
        (affineCoefficientMap W (IsLocalRing.residue R) (algebraMap R (affineRing W) c)) =
          affineResidueEval W x y he (algebraMap R (affineRing W) c)
      simp
    · change affinePointEval (W.map (IsLocalRing.residue R)) x y he
        (affineCoefficientMap W (IsLocalRing.residue R) (affineX W)) =
          affineResidueEval W x y he (affineX W)
      simp
  · change affinePointEval (W.map (IsLocalRing.residue R)) x y he
      (affineCoefficientMap W (IsLocalRing.residue R) (affineY W)) =
        affineResidueEval W x y he (affineY W)
    simp

lemma residueCoefficient_node_point :
    coefficientSchemeMap W (IsLocalRing.residue R)
      (affineChart (W.map (IsLocalRing.residue R))
        (affineSingularPoint (W.map (IsLocalRing.residue R)) x y he)) = residueNode W x y he := by
  change (Spec.map (CommRingCat.ofHom (affinePointEval (W.map (IsLocalRing.residue R)) x y he)) ≫
    affineChart (W.map (IsLocalRing.residue R)) ≫ coefficientSchemeMap W (IsLocalRing.residue R))
      (closedPoint k) = _
  rw [affineChart_coefficient, ← Category.assoc, ← Spec.map_comp]
  change (Spec.map (CommRingCat.ofHom
    ((affinePointEval (W.map (IsLocalRing.residue R)) x y he).comp
      (affineCoefficientMap W (IsLocalRing.residue R)))) ≫ affineChart W) (closedPoint k) = _
  rw [affinePointEval_comp_residueCoefficient]
  rfl

/-- The original punctured special fibre mapped to the projective curve of the residue-field
Weierstrass coefficients. -/
def originalPunctureToCoefficient : (originalPuncturedOpen he).toScheme ⟶
    scheme (W.map (IsLocalRing.residue R)) :=
  (originalPuncturedOpen he).ι ≫ (specialCoefficientIso W).inv

instance originalPunctureToCoefficient_open : IsOpenImmersion
    (originalPunctureToCoefficient he) := by
  unfold originalPunctureToCoefficient
  infer_instance

lemma originalPunctureToCoefficient_avoids
    (u : (originalPuncturedOpen he).toScheme) :
    originalPunctureToCoefficient he u ≠
      affineChart (W.map (IsLocalRing.residue R))
        (affineSingularPoint (W.map (IsLocalRing.residue R)) x y he) := by
  intro h
  have hc := congrArg (coefficientSchemeMap W (IsLocalRing.residue R)) h
  rw [residueCoefficient_node_point] at hc
  have ht : originalPunctureToCoefficient he ≫ coefficientSchemeMap W (IsLocalRing.residue R) =
      (originalPuncturedOpen he).ι ≫ pullback.fst (structureMap W) r := by
    rw [originalPunctureToCoefficient, Category.assoc,
      ← specialCoefficientIso_hom_fst, Iso.inv_hom_id_assoc]
  change (originalPunctureToCoefficient he ≫ coefficientSchemeMap W
    (IsLocalRing.residue R)) u = _ at hc
  rw [ht] at hc
  exact u.property hc

include hx hy in
lemma strictPunctureOriginalLift_dvr
    (u : (originalPuncturedOpen he).toScheme)
    (hu : strictPunctureOriginalLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc u ≠ genericPoint
      C) :
    IsDiscreteValuationRing ((C).presheaf.stalk
      (strictPunctureOriginalLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc u)) :=
  WeierstrassCurve.Projective.dvr_at_open_over_punctured_weierstrass
    (W.map (IsLocalRing.residue R)) x y he hx hy
    (originalPunctureToCoefficient he)
    (strictPunctureOriginalLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
    u (originalPunctureToCoefficient_avoids he u) hu

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictPunctureDVR





section WeierstrassStrictRecognition

/-! Recognition of the SAME actual strict transform by its original
normalization, from genuine punctured/outer/middle charts and the already
proved actual-etale regularity and smooth-stalk suppliers, with the retained
DVR-locus family.
No component isomorphism, resolved cycle, or chart coverage is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "S₀" => initialState M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
local notation "C₀" => initialChart M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
local notation "g" => modification M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
  hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
  hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ
  hρ hex hp hatlas hbc

local notation "CC" => strictTransform M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
  hp hatlas hbc



lemma firstStrictOuter_dvr (side : Bool)
    (z : pullback (C := Scheme.{u}) (strictTransformInclusion M π hπ (m + 2) (Nat.zero_lt_succ (m
      + 1)) a ha he ρ hρ hex hp hatlas hbc)
      (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side))
    (hz : pullback.fst i (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
      z ≠
      genericPoint CC) :
    IsDiscreteValuationRing ((CC).presheaf.stalk
      (pullback.fst i (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
        z)) := by
  let := firstStrictOuterSpecialMap_etale M π hπ m a ha he ρ hρ hex hp hatlas hbc side
  let := firstStrictOuterToNode_etale M π hπ m a ha he ρ hρ hex hp hatlas hbc side
  let e := firstStrictOuterPullbackIso M π hπ m a ha he ρ hρ hex hp hatlas hbc side
  exact AlgebraicGeometry.Scheme.dvr_at_image_of_etale_affine_line_chart
    (ResidueField R)
    (pullback.fst i (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side))
    (e.hom ≫ pullback.snd (firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
      (Resolution.outerEndBranch hπ)) z hz

variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)

include hx hy

/-- Every nongeneric stalk of the SAME actual strict closure is a DVR.
Coverage is the proved original-puncture/first-outer/full-middle cover, and the
full strict pullback to the middle is actually empty. -/
lemma strictTransform_dvr_off_generic (z : CC) (hz : z ≠ genericPoint CC) :
    IsDiscreteValuationRing ((CC).presheaf.stalk z) := by
  rcases strictPunctured_firstSpecialCharts_cover M π hπ m a ha he ρ hρ hex hp hatlas hbc (i z)
      with hu | hl | hr | hm
  · obtain ⟨v, hv⟩ := hu
    let qres := finalSpecialMap M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
      hatlas hbc ∣_
      originalPuncturedOpen he
    have hv' : strictOpenMap M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas
      hbc v = z := by
      apply (i).isClosedEmbedding.injective
      change (strictOpenMap M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas
        hbc ≫ i) v = i z
      rw [AlgebraicGeometry.Scheme.Hom.Image.openMap_inclusion]
      exact hv
    have hj : strictPunctureOriginalLift M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
      hex hp hatlas hbc
        (qres v) = z := by
      change (qres ≫ inv qres ≫ strictOpenMap M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ
        hρ hex hp hatlas hbc) v = z
      rw [IsIso.hom_inv_id_assoc]
      exact hv'
    have hd := strictPunctureOriginalLift_dvr M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ
      hρ hex hp hatlas hbc
      hx hy (qres v) (by simpa only [hj] using hz)
    exact hj ▸ hd
  · have hpull : z ∈ Set.range (pullback.fst i
        (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc false)) := by
      rw [Scheme.Pullback.range_fst]
      exact hl
    obtain ⟨v, hv⟩ := hpull
    have hd := firstStrictOuter_dvr M π hπ m a ha he ρ hρ hex hp hatlas hbc false v
      (by simpa only [hv] using hz)
    exact hv ▸ hd
  · have hpull : z ∈ Set.range (pullback.fst i
        (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc true)) := by
      rw [Scheme.Pullback.range_fst]
      exact hr
    obtain ⟨v, hv⟩ := hpull
    have hd := firstStrictOuter_dvr M π hπ m a ha he ρ hρ hex hp hatlas hbc true v
      (by simpa only [hv] using hz)
    exact hv ▸ hd
  · have hpull : z ∈ Set.range (pullback.fst i
        (firstMiddleSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc)) := by
      rw [Scheme.Pullback.range_fst]
      exact hm
    obtain ⟨v, hv⟩ := hpull
    let := firstMiddleStrictPullback_empty M π hπ m a ha he ρ hρ hex hp hatlas hbc
    exact isEmptyElim v

/-- The already-defined normalization of the original residue cubic is an
isomorphism onto its actual strict transform for every thickness m + 2. -/
lemma strictNormalization_isIso_positive
    (H :
      AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
    (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u}) :
    IsIso (strictNormalization M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
      hatlas hbc hx hy H) := by
  let := strictInfinityPoint_dvr M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
    hatlas hbc
  exact AlgebraicGeometry.Scheme.Hom.isIso_of_dvr_off_generic hdvr
    (strictNormalization M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas hbc
      hx hy H)
    inferInstance (strictInfinityPoint M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
      hp hatlas hbc)
    (strictTransform_dvr_off_generic M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy)

/-- The isomorphism has the original strict normalization as its actual hom. -/
def strictNormalizationIsoPositive
    (H :
      AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
    (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u}) :
    AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 (ResidueField R) ≅ CC := by
  let := strictNormalization_isIso_positive M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy H hdvr
  exact asIso (strictNormalization M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
    hatlas hbc hx hy H)

lemma strictNormalizationIsoPositive_hom
    (H :
      AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
    (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u}) :
    (strictNormalizationIsoPositive M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr).hom =
      strictNormalization M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas hbc
        hx hy H := rfl

@[reassoc] lemma strictNormalizationIsoPositive_original
    (H :
      AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
    (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u}) :
    (strictNormalizationIsoPositive M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr).hom ≫
        strictOriginalMap M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas hbc =
      originalSpecialNormalization he hx hy H :=
  strictNormalization_original M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
    hatlas hbc hx hy H

@[reassoc] lemma strictNormalizationIsoPositive_over
    (H :
      AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
    (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u}) :
    (strictNormalizationIsoPositive M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr).hom ≫ i ≫ pullback.snd (g ≫ structureMap W) r =
        AlgebraicGeometry.Scheme.ProjectiveLine.structureMap (ResidueField R) :=
  strictNormalization_over M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas
    hbc hx hy H

/-- This is an isomorphism over the original residue field, with the literal
original P1 structure map and actual strict-transform structure map. -/
def strictNormalizationOverIsoPositive
    (H :
      AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
    (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u}) :
    Over.mk (AlgebraicGeometry.Scheme.ProjectiveLine.structureMap (ResidueField R)) ≅
      Over.mk (i ≫ pullback.snd (g ≫ structureMap W) r) :=
  Over.isoMk (strictNormalizationIsoPositive M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy H hdvr)
    (strictNormalizationIsoPositive_over M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr)

/-- The same original-residue P1 map is now a genuine closed immersion into
the same resolved special fibre; all its existing original/base triangles remain. -/
lemma strictP1ToFinal_closedImmersion_positive
    (H :
      AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
    (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u}) :
    IsClosedImmersion (strictP1ToFinal M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
      hp hatlas hbc hx hy H) := by
  let := strictNormalization_isIso_positive M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy H hdvr
  unfold strictP1ToFinal
  infer_instance

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictRecognition


section WeierstrassP1ComponentMaps

/-! Native rational components indexed by ALL actual irreducible components.
Every source is the same literal original-residue-field P1. The actual strict
normalization and exceptional maps are retained exactly, and no component
inventory, count, or P1 isomorphism is supplied as a premise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.ProjectiveLine (projectiveP1)
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H :
    AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
local notation "k" => ResidueField R
local notation "T" => originalRun M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp hatlas
  hbc
local notation "g" => modification M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "i" => strictTransformInclusion M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ
  hex hp hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "e" => resolvedComponentEquiv M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
  (Nat.succ_pos m)

/-- The maps already constructed geometrically, with unchanged P1 source. -/
def resolvedP1Map : Option (Fin (m + 1)) → (projectiveP1 k ⟶ F)
  | none => strictP1ToFinal M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp hatlas hbc
    hx hy H
  | some j => originalExceptionalP1 M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc j

@[reassoc] lemma resolvedP1Map_base (j : Option (Fin (m + 1))) :
    resolvedP1Map M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j ≫
      pullback.snd (g ≫ structureMap W) r = AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k
        := by
  cases j with
  | none =>
    exact strictP1ToFinal_over M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp
      hatlas hbc hx hy H
  | some j => exact originalExceptionalP1_base M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc j

variable (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u})

include hdvr

lemma resolvedP1Map_closed (j : Option (Fin (m + 1))) :
    IsClosedImmersion (resolvedP1Map M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j) := by
  cases j with
  | none =>
    exact strictP1ToFinal_closedImmersion_positive M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr
  | some j => exact originalExceptionalP1_closed M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc j

lemma resolvedP1Map_range (j : Option (Fin (m + 1))) :
    Set.range (resolvedP1Map M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j) =
      resolvedComponentRange M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc j := by
  cases j with
  | none =>
    let n := strictNormalization M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp hatlas
      hbc hx hy H
    let : IsIso n := strictNormalization_isIso_positive M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr
    change Set.range (i ∘ n) = Set.range i
    rw [Set.range_comp, n.surjective.range_eq, Set.image_univ]
  | some j => rfl

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassP1ComponentMaps
