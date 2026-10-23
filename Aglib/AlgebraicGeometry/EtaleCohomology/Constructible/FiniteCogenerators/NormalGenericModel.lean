/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.GenericExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.GenericTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.DominantDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.ConstructibleTorsion
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Actual normal integral models of generic finite constant trivializations

For an integral locally closed stratum of an affine base, the finite locally
constant restriction becomes constant after a produced finite Galois extension
of the residue field of its generic image. The integral closure of the actual
prime quotient in that field is a normal integral algebra over the original
base. It can be infinite. Its actual function field carries the original
trivialization through the canonical localization equivalence.

The generic point lifts through the original immersion, so no identification
between stratum residue fields is assumed. No Noetherian, Japanese, Nagata or
finite-normalization premise is used in this construction.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge

/-- The original localization equivalence maps the actual affine function
field spectrum to any given fraction field of the same domain. -/
def givenFractionFieldPoint (C L : Type u) [CommRing C] [IsDomain C]
    [Field L] [Algebra C L] [IsFractionRing C L] :
    Spec (Spec (.of C)).functionField ⟶ Spec (.of L) := by
  let : Algebra C (Spec (.of C)).functionField :=
    StructureSheaf.stalkAlgebra C (genericPoint (Spec (.of C)))
  have : IsFractionRing C (Spec (.of C)).functionField :=
    @functionField_isFractionRing_of_affine (CommRingCat.of C) ‹IsDomain C›
  exact Spec.map (CommRingCat.ofHom
    (IsLocalization.algEquiv (nonZeroDivisors C) L (Spec (.of C)).functionField).toRingHom)

/-- The original localization comparison retains the structural map from an
arbitrary base ring. The argument stays at abstract ring parameters. -/
theorem givenFractionFieldPoint_comp (R C L : Type u) [CommRing R] [CommRing C]
    [IsDomain C] [Field L] [Algebra R C] [Algebra C L] [Algebra R L]
    [IsScalarTower R C L] [IsFractionRing C L] :
    givenFractionFieldPoint C L ≫ Spec.algebraMap R L =
      (Spec (.of C)).fromSpecStalk (genericPoint (Spec (.of C))) ≫
        Spec.algebraMap R C := by
  let : Algebra C (Spec (.of C)).functionField :=
    StructureSheaf.stalkAlgebra C (genericPoint (Spec (.of C)))
  have : IsFractionRing C (Spec (.of C)).functionField :=
    @functionField_isFractionRing_of_affine (CommRingCat.of C) ‹IsDomain C›
  let e : L ≃ₐ[C] (Spec (.of C)).functionField :=
    IsLocalization.algEquiv (nonZeroDivisors C) L (Spec (.of C)).functionField
  rw [Spec.fromSpecStalk_eq']
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R L)) =
    Spec.map (StructureSheaf.toStalk C _) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R C))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change e (algebraMap R L r) =
    algebraMap C (Spec (.of C)).functionField (algebraMap R C r)
  rw [IsScalarTower.algebraMap_apply R C L]
  exact e.commutes _

/-- A normal integral affine model, an actual dominant generic point of the
given stratum, and the original finite constant generic trivialization. -/
structure NormalGenericModel (R : Type u) [CommRing R] {S : Scheme.{u}}
    (j : S ⟶ Spec (.of R)) (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) where
  /-- The actual normal integral-closure algebra. -/
  ringType : Type u
  /-- Its inherited commutative ring structure. -/
  [commRing : CommRing ringType]
  /-- The original algebra map from the affine base. -/
  [algebra : Algebra R ringType]
  /-- The actual model ring is a domain. -/
  [domain : IsDomain ringType]
  /-- Its elements integral in its fraction field already lie in the ring. -/
  [normal : IsIntegrallyClosed ringType]
  /-- The original algebra map is integral; finiteness is not asserted. -/
  [integral : Algebra.IsIntegral R ringType]
  /-- The finite coefficient lies in the original scheme universe. -/
  value : AddCommGrpCat.{u}
  /-- Its actual underlying group is finite. -/
  [finite_value : Finite value]
  /-- The actual model function-field point of the original stratum. -/
  point : Spec (Spec (.of ringType)).functionField ⟶ S
  /-- Its image contains the stratum generic point. -/
  [dominant : IsDominant point]
  /-- The original generic point commutes with the original model map. -/
  over : point ≫ j = (Spec (.of ringType)).fromSpecStalk (genericPoint (Spec (.of ringType))) ≫
    Spec.algebraMap R ringType
  /-- The original generic coefficient is the actual finite constant sheaf. -/
  trivialization :
    (inverseImage ((Spec (.of ringType)).fromSpecStalk (genericPoint (Spec (.of ringType))) ≫
      Spec.algebraMap R ringType)).obj F ≅
        ConstantFinite.coefficient value (Spec (Spec (.of ringType)).functionField)

attribute [instance] NormalGenericModel.commRing NormalGenericModel.algebra
  NormalGenericModel.domain NormalGenericModel.normal NormalGenericModel.integral
  NormalGenericModel.finite_value NormalGenericModel.dominant

/-- Assemble the whole original generic triangle and constant trivialization
at abstract field and normal-ring parameters, before specializing the model. -/
def normalGenericModelOfFields (R C K L : Type u) [CommRing R] [CommRing C]
    [IsDomain C] [IsIntegrallyClosed C] [Algebra R C] [Algebra.IsIntegral R C]
    [Field K] [Field L] [Algebra R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Algebra C L] [IsScalarTower R C L] [IsFractionRing C L]
    {S : Scheme.{u}} [IsIntegral S] (j : S ⟶ Spec (.of R))
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) (ζ : Spec (.of K) ⟶ S)
    (hζ : ζ ≫ j = Spec.algebraMap R K) (hζpoint : ζ default = genericPoint S)
    (B : AddCommGrpCat.{u}) [Finite B]
    (b : (inverseImage (Spec.algebraMap R L)).obj F ≅
      ConstantFinite.coefficient B (Spec (.of L))) : NormalGenericModel R j F := by
  let N := Spec (.of C)
  have : IsIntegral N := inferInstanceAs (IsIntegral (Spec (.of C)))
  let Q := N.functionField
  let q : Spec Q ⟶ Spec (.of L) := givenFractionFieldPoint C L
  let f : N ⟶ Spec (.of R) := Spec.algebraMap R C
  have hqf : q ≫ Spec.algebraMap R L = N.fromSpecStalk (genericPoint N) ≫ f :=
    givenFractionFieldPoint_comp R C L
  have hbase : Spec.algebraMap K L ≫ Spec.algebraMap R K = Spec.algebraMap R L := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    change (algebraMap K L).comp (algebraMap R K) = algebraMap R L
    exact (IsScalarTower.algebraMap_eq R K L).symm
  let ζQ : Spec Q ⟶ S := q ≫ Spec.algebraMap K L ≫ ζ
  let q₀ : Spec Q := IsLocalRing.closedPoint Q
  have hζQpoint : ζQ q₀ = genericPoint S := by
    change ζ ((q ≫ Spec.algebraMap K L) q₀) = genericPoint S
    rw [Subsingleton.elim ((q ≫ Spec.algebraMap K L) q₀) (default : Spec (.of K))]
    exact hζpoint
  have : IsDominant ζQ :=
    isDominant_of_genericPoint_mem_range ζQ ⟨q₀, hζQpoint⟩
  have htriangle : ζQ ≫ j = N.fromSpecStalk (genericPoint N) ≫ f := by
    calc
      ζQ ≫ j = q ≫ Spec.algebraMap K L ≫ Spec.algebraMap R K := by
        simp only [ζQ, Category.assoc, hζ]
      _ = q ≫ Spec.algebraMap R L := congrArg (fun a => q ≫ a) hbase
      _ = _ := hqf
  let eQ : (inverseImage (N.fromSpecStalk (genericPoint N) ≫ f)).obj F ≅
      ConstantFinite.coefficient B (Spec Q) :=
    eqToIso (congrArg (fun a => (inverseImage a).obj F) hqf.symm) ≪≫
      (inverseImageComp (Spec.algebraMap R L) q).app F ≪≫
        (inverseImage q).mapIso b ≪≫
          (inverseImageConstantIso q).app (ConstantFinite.value B)
  exact {
    ringType := C
    value := B
    point := ζQ
    over := htriangle
    trivialization := eQ }

/-- Produce the actual integral closure of the original prime quotient in a
finite generic Galois extension; its size over the original base is unrestricted. -/
def normalGenericModel (R : Type u) [CommRing R] {S : Scheme.{u}} [IsIntegral S]
    (j : S ⟶ Spec (.of R)) [IsImmersion j]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R)))
    (hF : IsFiniteLocallyConstant ((inverseImage j).obj F)) : NormalGenericModel R j F := by
  apply Classical.choice
  let x : PrimeSpectrum R := j (genericPoint S)
  let p : Ideal R := x.asIdeal
  have : p.IsPrime := x.isPrime
  let D := R ⧸ p
  let K := p.ResidueField
  let η : Spec (.of K) ⟶ Spec (.of R) := Spec.algebraMap R K
  have hηrange : Set.range η = {x} := by
    change Set.range (PrimeSpectrum.comap (algebraMap R p.ResidueField)) = {x}
    exact PrimeSpectrum.residueField_comap x
  have hηpoint : η default = j (genericPoint S) := by
    have h : η default ∈ Set.range η := ⟨default, rfl⟩
    rw [hηrange] at h
    exact h
  obtain ⟨ζ, hζ⟩ := exists_fieldPoint_lift_of_mem_range j η
    ⟨genericPoint S, hηpoint.symm⟩
  have hζpoint : ζ default = genericPoint S := by
    apply j.isEmbedding.injective
    exact (congrArg (fun a : Spec (.of K) ⟶ Spec (.of R) => a default) hζ).trans hηpoint
  have hK : IsFiniteLocallyConstant ((inverseImage η).obj F) := by
    let e : (inverseImage η).obj F ≅ (inverseImage ζ).obj ((inverseImage j).obj F) :=
      eqToIso (congrArg (fun a => (inverseImage a).obj F) hζ.symm) ≪≫
        (inverseImageComp j ζ).app F
    exact (isFiniteLocallyConstant_iff_of_iso e).mpr
      (isFiniteLocallyConstant_pullback ζ hF)
  let t := finiteGaloisConstantTrivialization K ((inverseImage η).obj F) hK
  let L := t.extension
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra D L := ((algebraMap K L).comp (algebraMap D K)).toAlgebra
  have : IsScalarTower D K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R D L := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap K L (algebraMap R K r) =
      algebraMap K L (algebraMap D K (Ideal.Quotient.mk p r))
    rw [Ideal.algebraMap_quotient_residueField_mk])
  let C := integralClosure D L
  let : Algebra R C := ((algebraMap D C).comp (Ideal.Quotient.mk p)).toAlgebra
  have : IsScalarTower R D C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R C L := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap K L (algebraMap R K r) =
      algebraMap K L (algebraMap D K (Ideal.Quotient.mk p r))
    rw [Ideal.algebraMap_quotient_residueField_mk])
  have : Algebra.IsIntegral R D := Algebra.isIntegral_of_surjective Ideal.Quotient.mk_surjective
  have : Algebra.IsIntegral R C := Algebra.IsIntegral.trans D
  have : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  have : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hLbase : Spec.algebraMap K L ≫ η = Spec.algebraMap R L := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
  let eL : (inverseImage (Spec.algebraMap R L)).obj F ≅
      ConstantFinite.coefficient t.value (Spec (.of L)) :=
    eqToIso (congrArg (fun a => (inverseImage a).obj F) hLbase.symm) ≪≫
      (inverseImageComp η (Spec.algebraMap K L)).app F ≪≫ t.iso
  have : Finite t.value := t.finite_value
  exact ⟨normalGenericModelOfFields R C K L j F ζ hζ hζpoint t.value eL⟩

namespace NormalGenericModel

variable {R : Type u} [CommRing R] {S : Scheme.{u}}
  {j : S ⟶ Spec (.of R)} {F : AbelianSheaf.{u, u + 1} (Spec (.of R))}

instance integrallyClosed_stalk (m : NormalGenericModel R j F)
    (x : Spec (.of m.ringType)) :
    IsIntegrallyClosed ((Spec (.of m.ringType)).presheaf.stalk x) :=
  (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec m.ringType x).1

/-- The original generic adjoint extended through this actual normal model. -/
def extensionMap (m : NormalGenericModel R j F) :
    F ⟶ (directImage (Spec.algebraMap R m.ringType)).obj
      (ConstantFinite.coefficient m.value (Spec (.of m.ringType))) :=
  extendGenericMap (Spec.algebraMap R m.ringType) F (ConstantFinite.value m.value)
    m.trivialization.hom

/-- The extension retains exactly the original generic adjoint after the
specified original constant and direct-image comparisons. -/
@[reassoc]
theorem extensionMap_comp (m : NormalGenericModel R j F) :
    m.extensionMap ≫
        (directImage (Spec.algebraMap R m.ringType)).map
          (NormalConstants.constantGenericIso (Spec (.of m.ringType))
            (ConstantFinite.value m.value)).hom ≫
        (directImageCompIso (Spec.algebraMap R m.ringType)
          ((Spec (.of m.ringType)).fromSpecStalk
            (genericPoint (Spec (.of m.ringType))))).hom.app _ =
      (inverseImageAdjunction
        ((Spec (.of m.ringType)).fromSpecStalk (genericPoint (Spec (.of m.ringType))) ≫
          Spec.algebraMap R m.ringType)).homEquiv F _ m.trivialization.hom :=
  extendGenericMap_comp (Spec.algebraMap R m.ringType) F (ConstantFinite.value m.value)
    m.trivialization.hom

end NormalGenericModel
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
