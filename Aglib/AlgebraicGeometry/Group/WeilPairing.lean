/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IsogenyPairing.Galois
public import Aglib.AlgebraicGeometry.Group.MultiplicationTorsion
public import Aglib.AlgebraicGeometry.Picard.TranslationLift
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# Actual Weil pairing on literal multiplication torsion

The Cartier pairing for multiplication by `n` has geometric degree `n * n`.
Its values lie in `μ_n` because its arguments are killed by `n`. Actual lifts
of the pulled-back identity ideal supply alternation of the original positive
frame transport. The construction retains the original geometric points and
Galois actions, with native curve properties and coherent genus one explicit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.FiniteEtale
open Field.absoluteGaloisGroup.RootsOfUnity

namespace AlgebraicGeometry.Scheme.Group.WeilPairing

universe u v
attribute [local instance] Over.cartesianMonoidalCategory

variable {F : Type u} [Field F]

/-- The original root group has the scalar structure dictated by its level. -/
instance cyclotomicModule (n : ℕ) : Module (ZMod n) (Mu F n) :=
  AddCommGroup.zmodModule (mu_nsmul F n)

/-- Inclusion of actual roots from the torsion level to the isogeny degree. -/
def squareRootInclusion (n : ℕ) : Mu F n →+ Mu F (n * n) where
  toFun z := Additive.ofMul ⟨z.toMul.val, (mem_rootsOfUnity _ _).mpr (by
    rw [pow_mul, (mem_rootsOfUnity _ _).mp z.toMul.property, one_pow])⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem squareRootInclusion_injective (n : ℕ) :
    Function.Injective (squareRootInclusion (F := F) n) := by
  intro x y h
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z : Mu F (n * n) => z.toMul.val) h

/-- A character of a group killed by `n` already has values in the actual
`n`th roots, even when it was originally presented at degree `n * n`. -/
def restrictRootCharacter {M : Type v} [AddCommGroup M] (n : ℕ)
    (hM : ∀ x : M, n • x = 0) (χ : M →+ Mu F (n * n)) : M →+ Mu F n where
  toFun x := Additive.ofMul ⟨(χ x).toMul.val, (mem_rootsOfUnity _ _).mpr (by
    have h : n • χ x = 0 := by rw [← map_nsmul, hM x, map_zero]
    exact congrArg (fun z : Mu F (n * n) => z.toMul.val) h)⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : Mu F (n * n) => z.toMul.val) χ.map_zero
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : Mu F (n * n) => z.toMul.val) (χ.map_add x y)

/-- Restriction of roots is an equivalence on characters of the actual
annihilated group. In particular it preserves perfectness. -/
def rootCharacterEquiv {M : Type v} [AddCommGroup M] (n : ℕ)
    (hM : ∀ x : M, n • x = 0) :
    (M →+ Mu F (n * n)) ≃+ (M →+ Mu F n) where
  toFun := restrictRootCharacter n hM
  invFun χ := (squareRootInclusion n).comp χ
  left_inv χ := by
    apply AddMonoidHom.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  right_inv χ := by
    apply AddMonoidHom.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  map_add' χ ψ := by
    apply AddMonoidHom.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl

/-- Precomposition by an actual additive equivalence on a character group. -/
def precompCharacterEquiv {A B C : Type*} [AddZeroClass A]
    [AddZeroClass B] [AddCommMonoid C] (e : A ≃+ B) : (B →+ C) ≃+ (A →+ C) where
  toFun χ := χ.comp e.toAddMonoidHom
  invFun χ := χ.comp e.symm.toAddMonoidHom
  left_inv χ := by ext x; exact congrArg χ (e.apply_symm_apply x)
  right_inv χ := by ext x; exact congrArg χ (e.symm_apply_apply x)
  map_add' _ _ := rfl

open MultiplicationKernel IsogenyPairing.Galois

variable (E : Grp (FScheme F)) [IsCommMonObj E.X]

/-- The native kernel comparison preserves the literal additive point law. -/
def torsionKernelEquiv (n : ℕ) : finiteTorsionPoints E n ≃+
    Additive (GeometricKernelPoints (multiplicationHom E n)) where
  toFun x := Additive.ofMul (nativeKernelPointEquiv E n x)
  invFun x := (nativeKernelPointEquiv E n).symm x.toMul
  left_inv x := (nativeKernelPointEquiv E n).left_inv x
  right_inv x := (nativeKernelPointEquiv E n).right_inv x.toMul
  map_add' x y := by
    change nativeKernelPointEquiv E n (x + y) =
      nativeKernelPointEquiv E n x * nativeKernelPointEquiv E n y
    apply Kernel.DeckTranslation.inclusion_points_injective
      (multiplicationHom E n) (Over.mk (FieldGalois.geometricPoint F))
    change nativeKernelPointEquiv E n (x + y) ≫
      (Kernel.inclusion (multiplicationHom E n)).hom.hom =
        (nativeKernelPointEquiv E n x * nativeKernelPointEquiv E n y) ≫
          (Kernel.inclusion (multiplicationHom E n)).hom.hom
    rw [MonObj.mul_comp, nativeKernelPointEquiv_inclusion,
      nativeKernelPointEquiv_inclusion, nativeKernelPointEquiv_inclusion]
    rfl

/-- The comparison uses the original absolute-Galois precomposition. -/
theorem torsionKernelEquiv_galois (n : ℕ) (σ : Field.absoluteGaloisGroup F)
    (x : finiteTorsionPoints E n) :
    torsionKernelEquiv E n (torsionGalois E n σ x) =
      Additive.ofMul (FieldGalois.pointEnd F σ ≫ (torsionKernelEquiv E n x).toMul) := by
  change nativeKernelPointEquiv E n (torsionGalois E n σ x) =
    FieldGalois.pointEnd F σ ≫ nativeKernelPointEquiv E n x
  apply Kernel.DeckTranslation.inclusion_points_injective
    (multiplicationHom E n) (Over.mk (FieldGalois.geometricPoint F))
  change nativeKernelPointEquiv E n (torsionGalois E n σ x) ≫
      (Kernel.inclusion (multiplicationHom E n)).hom.hom =
    (FieldGalois.pointEnd F σ ≫ nativeKernelPointEquiv E n x) ≫
      (Kernel.inclusion (multiplicationHom E n)).hom.hom
  rw [Category.assoc, nativeKernelPointEquiv_inclusion, nativeKernelPointEquiv_inclusion]
  rfl

/-- The self-dual multiplication triangle has degree `n * n`. -/
theorem multiplicationTriangle (n : ℕ) :
    (multiplicationHom E n).hom.hom ≫ (multiplicationHom E n).hom.hom =
      (𝟙 E.X) ^ (n * n) := by
  rw [multiplicationHom_hom]
  change ((𝟙 E.X) ^ n) ≫ ((𝟙 E.X) ^ n) = (𝟙 E.X) ^ (n * n)
  rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]

variable (hE : Curve.Properties E.X) (hg : Curve.coherentGenus F E.X = 1)
variable (n : ℕ) (hn : IsUnit (n : F))

/-- The canonical torsion carrier is killed by its defining level. -/
theorem torsion_nsmul (x : finiteTorsionPoints E n) : n • x = 0 :=
  Subtype.ext (torsion_killed E n x)

/-- Positive Cartier evaluation for actual multiplication, before restricting
its roots from the geometric degree to the torsion level. -/
def degreePairing : finiteTorsionPoints E n →+
    (finiteTorsionPoints E n →+ Mu F (n * n)) := by
  let hfinite := Multiplication.multiplication_finite_etale_of_invertible E hE n hn
  have hf := hfinite.1
  have he := hfinite.2.1
  have hs := hfinite.2.2
  let : IsFinite (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using hf
  let : Etale (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using he
  let : Surjective (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using hs
  exact ((precompCharacterEquiv (torsionKernelEquiv E n)).toAddMonoidHom.comp
    (geometricPairing (multiplicationHom E n) hE hE (n * n)
      (by simpa only [multiplicationHom_hom, multiplication] using
        Multiplication.multiplication_hasGeometricDegree E hE hg n hn) hg hg
      (multiplicationHom E n) (multiplicationTriangle E n))).comp
        (torsionKernelEquiv E n).toAddMonoidHom

/-- Perfectness of the degree-valued pairing uses the genuine multiplication
degree and the accepted frame-descent pairing. -/
theorem degreePairing_bijective : Function.Bijective (degreePairing E hE hg n hn) := by
  obtain ⟨hf, he, hs⟩ := Multiplication.multiplication_finite_etale_of_invertible E hE n hn
  let : IsFinite (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using hf
  let : Etale (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using he
  let : Surjective (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using hs
  exact (precompCharacterEquiv (torsionKernelEquiv E n)).bijective.comp
    ((geometricPairing_bijective (multiplicationHom E n) hE hE (n * n)
      (by simpa only [multiplicationHom_hom, multiplication] using
        Multiplication.multiplication_hasGeometricDegree E hE hg n hn) hg hg
      (multiplicationHom E n) (multiplicationTriangle E n)
      (by simpa only [Nat.cast_mul] using hn.mul hn)).comp
        (torsionKernelEquiv E n).bijective)

/-- The original Galois and coefficient actions on the degree-valued map. -/
theorem degreePairing_galois (σ : Field.absoluteGaloisGroup F)
    (x y : finiteTorsionPoints E n) :
    degreePairing E hE hg n hn (torsionGalois E n σ x) (torsionGalois E n σ y) =
      σ • degreePairing E hE hg n hn x y := by
  obtain ⟨hf, he, hs⟩ := Multiplication.multiplication_finite_etale_of_invertible E hE n hn
  let : IsFinite (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using hf
  let : Etale (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using he
  let : Surjective (multiplicationHom E n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using hs
  change geometricPairing (multiplicationHom E n) hE hE (n * n)
      (by simpa only [multiplicationHom_hom, multiplication] using
        Multiplication.multiplication_hasGeometricDegree E hE hg n hn) hg hg
      (multiplicationHom E n) (multiplicationTriangle E n)
      (torsionKernelEquiv E n (torsionGalois E n σ x))
      (torsionKernelEquiv E n (torsionGalois E n σ y)) = _
  rw [torsionKernelEquiv_galois, torsionKernelEquiv_galois]
  exact geometricPairing_galois (multiplicationHom E n) hE hE (n * n)
    (by simpa only [multiplicationHom_hom, multiplication] using
        Multiplication.multiplication_hasGeometricDegree E hE hg n hn) hg hg
    (multiplicationHom E n) (multiplicationTriangle E n) σ
    (torsionKernelEquiv E n x).toMul (torsionKernelEquiv E n y).toMul

/-- The actual pairing with its correct cyclotomic coefficient group. -/
def additivePairing : finiteTorsionPoints E n →+
    (finiteTorsionPoints E n →+ Mu F n) :=
  (rootCharacterEquiv n (torsion_nsmul E n)).toAddMonoidHom.comp
    (degreePairing E hE hg n hn)

/-- The original positive scalar is unchanged by restriction of its level. -/
theorem additivePairing_scalar (x y : finiteTorsionPoints E n) :
    (additivePairing E hE hg n hn x y).toMul.val =
      (degreePairing E hE hg n hn x y).toMul.val := rfl

/-- Bilinearity for the canonical `ZMod n` structures on literal torsion and roots. -/
def pairing : finiteTorsionPoints E n →ₗ[ZMod n]
    finiteTorsionPoints E n →ₗ[ZMod n] Mu F n :=
  (((AddMonoidHom.toZModLinearMapEquiv n).toAddMonoidHom).comp
    (additivePairing E hE hg n hn)).toZModLinearMap n

/-- Perfectness survives both the root restriction and the canonical change
from additive homomorphisms to `ZMod n`-linear maps. -/
theorem pairing_bijective : Function.Bijective (pairing E hE hg n hn) :=
  (AddMonoidHom.toZModLinearMapEquiv n).bijective.comp
    ((rootCharacterEquiv n (torsion_nsmul E n)).bijective.comp
      (degreePairing_bijective E hE hg n hn))

/-- The pairing is equivariant for the original torsion action and the actual
field-automorphism action on the original cyclotomic roots. -/
theorem pairing_galois (σ : Field.absoluteGaloisGroup F)
    (x y : finiteTorsionPoints E n) :
    pairing E hE hg n hn (torsionGalois E n σ x) (torsionGalois E n σ y) =
      rootAction F n σ (pairing E hE hg n hn x y) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z : Mu F (n * n) => z.toMul.val)
    (degreePairing_galois E hE hg n hn σ x y)

/-- Level one has the required diagonal identity on its literal zero torsion. -/
theorem pairing_one_alternating (hn : IsUnit ((1 : ℕ) : F))
    (x : finiteTorsionPoints E 1) : pairing E hE hg 1 hn x x = 0 := by
  have hx : x = 0 := by simpa only [one_nsmul] using torsion_nsmul E 1 x
  subst x
  exact map_zero (pairing E hE hg 1 hn 0)

section TranslationGeometry

open Scheme.Modules.Invertible
open CategoryTheory.Limits
open IsogenyPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (G : Grp (FScheme k)) [IsCommMonObj G.X]
variable [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom]
variable (hG : Curve.Properties G.X) (hgG : Curve.coherentGenus k G.X = 1)

include hG hgG in
/-- The identity ideal has the positive point-class translation difference. -/
theorem translation_identityIdealClass (P : 𝟙_ (FScheme k) ⟶ G.X) :
    pullbackClass (Translation.translation P).left (Multiplication.identityIdealClass G) -
      Multiplication.identityIdealClass G = pointDivisorClass G P := by
  have hd : lift (𝟙 G.X) (toUnit G.X ≫ P⁻¹) ≫ Multiplication.difference G =
      Translation.translation P := by
    calc
      _ = (lift (𝟙 G.X) (toUnit G.X ≫ P⁻¹) ≫ fst G.X G.X) /
          (lift (𝟙 G.X) (toUnit G.X ≫ P⁻¹) ≫ snd G.X G.X) :=
        GrpObj.comp_div _ _ _
      _ = (𝟙 G.X) / (toUnit G.X ≫ P⁻¹) := by rw [lift_fst, lift_snd]
      _ = (𝟙 G.X) * (toUnit G.X ≫ P) := by rw [GrpObj.comp_inv, div_inv_eq_mul]
      _ = Translation.translation P := mul_comm _ _
  have hc : pullbackClass (toUnit G.X ≫ P⁻¹).left
      (Multiplication.identityIdealClass G) = 0 := by
    rw [Over.comp_left, pullbackClass_comp,
      Scheme.Hom.fieldPicard_eq_zero k
        (pullbackClass P⁻¹.left (Multiplication.identityIdealClass G)),
      pullbackClass_zero]
  have hP : pointDivisorClass G P⁻¹ =
      -pullbackClass (Translation.translation P).left (Multiplication.identityIdealClass G) +
        Multiplication.identityIdealClass G := by
    change pullbackClass (lift (𝟙 G.X) (toUnit G.X ≫ P⁻¹)).left
      (Multiplication.normalizedDiagonalClass G) = _
    simp only [Multiplication.normalizedDiagonalClass, pullbackClass_add moduleTensorPullback,
      pullbackClass_neg moduleTensorPullback, ← pullbackClass_comp, ← Over.comp_left,
      hd, lift_fst, lift_snd, hc, Over.id_left, pullbackClass_id, add_zero]
  have hi : pointDivisorClass G P⁻¹ = -pointDivisorClass G P := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [add_comm, ← pointDivisorClass_mul G hG hgG, mul_inv_cancel,
      pointDivisorClass_one]
  calc
    _ = -(-pullbackClass (Translation.translation P).left
        (Multiplication.identityIdealClass G) + Multiplication.identityIdealClass G) := by abel
    _ = -pointDivisorClass G P⁻¹ := congrArg Neg.neg hP.symm
    _ = pointDivisorClass G P := by rw [hi, neg_neg]

include hG hgG in
omit [IsCommMonObj G.X] [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom] in
/-- A point has an actual division point under invertible multiplication. -/
theorem exists_divisionPoint (n : ℕ) (hn : IsUnit (n : k))
    (P : 𝟙_ (FScheme k) ⟶ G.X) : ∃ Q : 𝟙_ (FScheme k) ⟶ G.X, Q ^ n = P := by
  have hn0 : n ≠ 0 := by
    intro hz
    exact hn.ne_zero (by simp only [hz, Nat.cast_zero])
  have hc := Multiplication.multiplication_hasGeometricDegree G hG hgG n hn
    k (𝟙 (Base k)) P
  have hnon : Nat.card {Q : 𝟙_ (FScheme k) ⟶ G.X //
      Q ≫ multiplication G n = P} ≠ 0 := by
    dsimp only [multiplication]
    erw [hc]
    exact mul_ne_zero hn0 hn0
  obtain ⟨⟨Q, hQ⟩⟩ := (Nat.card_ne_zero.mp hnon).1
  exact ⟨Q, (point_multiplication G n Q).symm.trans hQ⟩

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom] in
/-- Literal multiplication intertwines the actual translations. -/
theorem translation_multiplication (n : ℕ) (Q : 𝟙_ (FScheme k) ⟶ G.X) :
    Translation.translation Q ≫ multiplication G n =
      multiplication G n ≫ Translation.translation (Q ^ n) := by
  rw [point_multiplication]
  change ((toUnit G.X ≫ Q) * 𝟙 G.X) ^ n =
    multiplication G n ≫ ((toUnit G.X ≫ Q ^ n) * 𝟙 G.X)
  rw [mul_pow, MonObj.comp_mul, Category.comp_id]
  congr 1
  rw [← Category.assoc, comp_toUnit, MonObj.comp_pow]

include hG hgG in
/-- A division point preserves the actual pullback of the identity ideal.
The proof uses its translation difference and the actual reverse-kernel
Picard pullback; no choice of a torsion basis enters. -/
theorem divisionPoint_preserves_pullback (n : ℕ) (hn : IsUnit (n : k))
    (P : KernelPoints (multiplicationHom G n))
    (Q : 𝟙_ (FScheme k) ⟶ G.X) (hQ : Q ^ n = kernelPoint (multiplicationHom G n) P) :
    pullbackClass (Translation.translation Q).left
        (pullbackClass (multiplication G n).left (Multiplication.identityIdealClass G)) =
      pullbackClass (multiplication G n).left (Multiplication.identityIdealClass G) := by
  obtain ⟨hf, he, hs⟩ := Multiplication.multiplication_finite_etale_of_invertible G hG n hn
  let : IsFinite (multiplicationHom G n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using hf
  let : Etale (multiplicationHom G n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using he
  let : Surjective (multiplicationHom G n).hom.hom.left := by
    simpa only [multiplicationHom_hom, multiplication] using hs
  have hp := pullback_kernelPointClass_zero (multiplicationHom G n) hG hG (n * n)
    (by simpa only [multiplicationHom_hom, multiplication] using
      Multiplication.multiplication_hasGeometricDegree G hG hgG n hn) hgG
    (multiplicationHom G n) (multiplicationTriangle G n) P
  rw [multiplicationHom_hom] at hp
  rw [← translation_identityIdealClass G hG hgG] at hp
  rw [sub_eq_add_neg, pullbackClass_add moduleTensorPullback,
    pullbackClass_neg moduleTensorPullback] at hp
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg]
  convert hp using 1
  rw [← pullbackClass_comp, ← Over.comp_left, translation_multiplication, hQ,
    Over.comp_left, pullbackClass_comp]

end TranslationGeometry


section TranslationMaps

variable {k : Type u} [Field k] (G : Grp (FScheme k))

/-- Literal point translation as an actual automorphism. -/
def translationAutHom : (𝟙_ (FScheme k) ⟶ G.X) →* Aut G.X :=
  (Aut.unitsEndEquivAut G.X).toMonoidHom.comp
    (Translation.translationHom (G := G)).toHomUnits

@[simp] theorem translationAutHom_hom (P : 𝟙_ (FScheme k) ⟶ G.X) :
    (translationAutHom G P).hom = Translation.translation P := rfl

/-- The actual scheme automorphism underlying point translation. -/
def schemeTranslationHom : (𝟙_ (FScheme k) ⟶ G.X) →* Aut G.X.left :=
  (Functor.mapAut G.X (Over.forget (Base k))).comp (translationAutHom G)

@[simp] theorem schemeTranslationHom_hom (P : 𝟙_ (FScheme k) ⟶ G.X) :
    (schemeTranslationHom G P).hom = (Translation.translation P).left := rfl

/-- Proper-curve endomorphisms over the original field fix every global function. -/
theorem curveFunctions_fixed (hG : Curve.Properties G.X)
    (g : G.X ⟶ G.X) (r : Γ(G.X.left, ⊤)) : g.left.appTop r = r := by
  obtain ⟨c, hc⟩ :=
    (Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen G.X hG).surjective r
  rw [← hc, Curve.curveConstantsEquiv_apply, Cohomology.map_constants]

end TranslationMaps

/-- Closure base change retains the literal multiplication morphism, without
replacing its geometric kernel by a chosen abstract group. -/
theorem fieldMap_multiplication_underlying (n : ℕ) :
    (fieldMap (multiplicationHom E n)).hom.hom = (𝟙 (fieldGroup E).X) ^ n := by
  let P := Over.pullback (FieldGalois.geometricPoint F)
  let : GrpObj (P.obj E.X) := (fieldGroup E).grp
  change P.map (multiplicationHom E n).hom.hom = _
  rw [multiplicationHom_hom]
  change P.map ((𝟙 E.X) ^ n) = _
  calc
    _ = (P.map (𝟙 E.X)) ^ n := (P.homMonoidHom (X := E.X) (M := E.X)).map_pow _ _
    _ = _ := by rw [P.map_id]; rfl

section ClosedDiagonal

open Scheme.Modules.Invertible
open Scheme.Modules.Invertible.EtaleDescent Scheme.Modules.Invertible.FrameTorsor
open Scheme.Modules.Invertible.AssociatedBundle Scheme.Modules.Invertible.UnitDescent
open IsogenyPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (G : Grp (FScheme k)) [IsCommMonObj G.X]
variable [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom]
variable (hG : Curve.Properties G.X) (hgG : Curve.coherentGenus k G.X = 1)
variable (m : ℕ) (hm : IsUnit (m : k)) (f : G ⟶ G)
variable [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left]
variable (hf : f.hom.hom = multiplication G m)
variable (hdeg : HasGeometricDegree f.hom.hom (m * m))
variable (htriangle : f.hom.hom ≫ f.hom.hom = (𝟙 G.X) ^ (m * m))

include hm hf in
/-- Positive frame transport on the actual multiplication kernel has trivial
diagonal, by actual division-point lifts and their powers. -/
theorem evaluationCharacter_self (P : KernelPoints f) :
    evaluationCharacter f hG hG (m * m) hdeg hgG f htriangle P P = 1 := by
  obtain ⟨Q, hQ⟩ := exists_divisionPoint G hG hgG m hm (kernelPoint f P)
  let M := Multiplication.identityIdealLineBundle G
  let R := kernelPointLineBundle f P
  let a := schemeTranslationHom G Q
  let b := schemeTranslationHom G (kernelPoint f P)
  have w : a.hom ≫ f.hom.hom.left = f.hom.hom.left ≫ b.hom := by
    have ht := translation_multiplication G m Q
    rw [hQ, ← hf] at ht
    simpa only [a, b, schemeTranslationHom_hom, Over.comp_left] using
      congrArg Over.Hom.left ht
  have hb : b.hom = (kernelDeckAut f P).hom.left := by
    rw [schemeTranslationHom_hom]
    rfl
  have hd : b.hom ≫ f.hom.hom.left = f.hom.hom.left := by
    rw [hb]
    exact (kernelDeckAut f P).hom.w
  have hpow : b = a ^ m := by
    change schemeTranslationHom G (kernelPoint f P) = (schemeTranslationHom G Q) ^ m
    rw [← hQ, map_pow]
  have hclass : classOf G.X.left (tensorLineBundle G.X.left R M) =
      classOf G.X.left (pullbackLineBundle b.hom M) := by
    change classOf G.X.left (tensorLineBundle G.X.left (kernelPointLineBundle f P)
        (Multiplication.identityIdealLineBundle G)) = _
    rw [classOf_tensor, kernelPointLineBundle_class]
    change pointDivisorClass G (kernelPoint f P) + Multiplication.identityIdealClass G =
      pullbackClass b.hom (Multiplication.identityIdealClass G)
    rw [schemeTranslationHom_hom]
    exact eq_sub_iff_add_eq.mp (translation_identityIdealClass G hG hgG (kernelPoint f P)).symm
  obtain ⟨e⟩ := Quotient.exact hclass
  have hR := kernelPointLineBundle_pullback_zero f hG hG (m * m) hdeg hgG f htriangle P
  let s := frameOfPullbackClassZero f R hR
  let φ := frameSectionsEquiv etaleLineBundleDescent G.X.left R (op (cover f)) s
  have hs : FrameTensor.pullFrame R f.hom.hom.left f.hom.hom.left b.hom hd φ = φ :=
    TranslationLift.frame_fixed_of_deck_power f.hom.hom.left R M a b w e φ b hd m hpow
      (by
        intro r
        rw [schemeTranslationHom_hom]
        exact curveFunctions_fixed G hG (Translation.translation Q) r)
  have hs' : (frameSheaf etaleLineBundleDescent G.X.left R).obj.map
      (kernelDeckAut f P).hom.op s = s := by
    apply (frameSectionsEquiv etaleLineBundleDescent G.X.left R (op (cover f))).injective
    rw [FrameTensor.frameSections_restriction]
    change FrameTensor.pullFrame R f.hom.hom.left f.hom.hom.left
      (kernelDeckAut f P).hom.left (kernelDeckAut f P).hom.w φ = φ
    simpa only [hb] using hs
  apply Subtype.ext
  change (Units.map
    (Curve.curveConstantsEquiv smoothFieldNormality normalComponentsOpen G.X hG).symm.toMonoidHom)
      (Transport.scalar (frameTorsor etaleLineBundleDescent G.X.left R)
        (cover f) (kernelDeckRepresentation f) s P) = 1
  rw [Transport.scalar]
  erw [hs', transportUnit_self, map_one]

end ClosedDiagonal

section ClosedDiagonalAdditive

open IsogenyPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (G : Grp (FScheme k)) [IsCommMonObj G.X]
variable [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom]
variable (hG : Curve.Properties G.X) (hgG : Curve.coherentGenus k G.X = 1)
variable (m : ℕ) (hm : IsUnit (m : k)) (f : G ⟶ G)
variable [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left]
variable (hf : f.hom.hom = multiplication G m)
variable (hdeg : HasGeometricDegree f.hom.hom (m * m))
variable (htriangle : f.hom.hom ≫ f.hom.hom = (𝟙 G.X) ^ (m * m))

include hm hf in
/-- Additive form of the actual diagonal evaluation. -/
theorem kernelPairing_self (x : Additive (KernelPoints f)) :
    kernelPairing f hG hG (m * m) hdeg hgG f htriangle hgG x x = 0 := by
  apply Additive.toMul.injective
  exact evaluationCharacter_self G hG hgG m hm f hf hdeg htriangle x.toMul

end ClosedDiagonalAdditive

open scoped CategoryTheory.Obj in
/-- The same diagonal statement after the original closure-base and kernel
point comparisons used by the degree pairing. -/
theorem degreePairing_self (x : finiteTorsionPoints E n) :
    degreePairing E hE hg n hn x x = 0 := by
  obtain ⟨hf, he, hs⟩ := Multiplication.multiplication_finite_etale_of_invertible E hE n hn
  let f := multiplicationHom E n
  let : IsFinite f.hom.hom.left := by
    simpa only [f, multiplicationHom_hom, multiplication] using hf
  let : Etale f.hom.hom.left := by
    simpa only [f, multiplicationHom_hom, multiplication] using he
  let : Surjective f.hom.hom.left := by
    simpa only [f, multiplicationHom_hom, multiplication] using hs
  let G := fieldGroup E
  let hG := fieldProperties E hE
  let hgG := fieldGenus E hE hg
  let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
  let : IsProper G.X.hom := hG.proper
  let : IsCommMonObj G.X :=
    inferInstanceAs (IsCommMonObj ((Over.pullback (FieldGalois.geometricPoint F)).obj E.X))
  let : IsFinite (fieldMap f).hom.hom.left :=
    BaseChange.map_finite (FieldGalois.geometricPoint F) f inferInstance
  let : Etale (fieldMap f).hom.hom.left :=
    BaseChange.map_etale (FieldGalois.geometricPoint F) f inferInstance
  let : Surjective (fieldMap f).hom.hom.left :=
    BaseChange.map_surjective (FieldGalois.geometricPoint F) f inferInstance
  let hd : HasGeometricDegree f.hom.hom (n * n) := by
    simpa only [f, multiplicationHom_hom, multiplication] using
      Multiplication.multiplication_hasGeometricDegree E hE hg n hn
  have hnK : IsUnit (n : AlgebraicClosure F) := by
    simpa only [map_natCast] using hn.map (algebraMap F (AlgebraicClosure F))
  let y := (kernelEquiv f).toAdditive (torsionKernelEquiv E n x)
  change IsogenyPairing.kernelPairing (fieldMap f) hG hG (n * n)
    (fieldDegree f (n * n) hd) hgG (fieldMap f)
    (fieldTriangle f f (n * n) (multiplicationTriangle E n)) hgG y y = 0
  exact kernelPairing_self G hG hgG n hnK (fieldMap f)
    (fieldMap_multiplication_underlying E n) (fieldDegree f (n * n) hd)
    (fieldTriangle f f (n * n) (multiplicationTriangle E n)) y

/-- Alternation of the actual positive evaluation pairing at every invertible
level, including even and composite levels and level one. -/
theorem pairing_alternating (x : finiteTorsionPoints E n) :
    pairing E hE hg n hn x x = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z : Mu F (n * n) => z.toMul.val)
    (degreePairing_self E hE hg n hn x)

/-- The complete intrinsic pairing data on the original literal torsion and
original roots of unity. The coefficient action remains the actual field action. -/
structure PerfectWeilPairing (E : Grp (FScheme F)) [IsCommMonObj E.X] (n : ℕ) where
  /-- The level `n` is invertible in the base field. -/
  primeTo : IsUnit (n : F)
  /-- A basis of the literal multiplication torsion over `ZMod n`, indexed by `Fin 2`. -/
  basis : Module.Basis (Fin 2) (ZMod n) (finiteTorsionPoints E n)
  /-- The `ZMod n`-bilinear map from two literal torsion points to the additive group
  of `n`th roots of unity in the algebraic closure of `F`. -/
  pairing : finiteTorsionPoints E n →ₗ[ZMod n]
    finiteTorsionPoints E n →ₗ[ZMod n] Mu F n
  /-- The pairing of any torsion point with itself is zero in the additive root group. -/
  alternating : ∀ x, pairing x x = 0
  /-- The pairing identifies torsion points bijectively with their `ZMod n`-linear
  characters valued in `Mu F n`. -/
  perfect : Function.Bijective pairing
  /-- Simultaneous Galois action on both torsion arguments agrees with the field action
  on the resulting root of unity. -/
  equivariant : ∀ (σ : Field.absoluteGaloisGroup F) x y,
    pairing (torsionGalois E n σ x) (torsionGalois E n σ y) =
      rootAction F n σ (pairing x y)

/-- The actual Weil pairing record, retaining native curve properties and
native coherent genus one until the independent genus bridge is supplied. -/
def perfectWeilPairing (hpos : 0 < n) : PerfectWeilPairing E n where
  primeTo := hn
  basis := torsionBasis E hE hg n hpos hn
  pairing := pairing E hE hg n hn
  alternating := pairing_alternating E hE hg n hn
  perfect := pairing_bijective E hE hg n hn
  equivariant := pairing_galois E hE hg n hn

end AlgebraicGeometry.Scheme.Group.WeilPairing
