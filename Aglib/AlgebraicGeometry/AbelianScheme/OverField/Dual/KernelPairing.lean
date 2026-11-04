/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Kernel.Characters
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare
public import Aglib.AlgebraicGeometry.Group.Kernel.ClosedImmersion
public import Aglib.AlgebraicGeometry.Group.CartierDuality.UniversalProperty.Group

/-!
# The original Poincare pair on a dual-map kernel

The existing Picard pullback kernel carries the actual Poincare pair from
the same supplied Picard representative. Its source pullback has a unique
origin-normalized trivialization. The construction and its parameter laws
hold on all test schemes; representability is used only at its original
locally Noetherian representing objects. Along an original subgroup of the
zero fibre, the transported character gives a group map into the original
Cartier dual. Its original scheme kernel is trivial by full faithfulness
of line-bundle descent and classification on that one locally Noetherian
test. The given group may be the original multiplication kernel itself.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.OverField Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A B : Grp (FScheme k))
  [IsProper A.X.hom] [GeometricallyIntegral A.X.hom]
  [IsProper B.X.hom] [GeometricallyIntegral B.X.hom]
  (PA : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PA.obj.hom]
  (RA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PA)
  (PB : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PB.obj.hom]
  (RB : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf B.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PB)
  (q : A ⟶ B)

/-- A point in the original dual-map kernel gives the unique normalized
trivialization of the original Poincare pullback, with no finite, etale or
Noetherian hypothesis on the test scheme. -/
def poincareKernelTrivialization {T : FScheme k}
    (t : T ⟶ picardIdentityComponent B.X.hom PB RB)
    (ht : t ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1) :
    RigidifiedPair.Iso
      (RigidifiedPair.sourcePullback η[A.X] η[B.X] q.hom.hom (IsMonHom.one_hom _)
        (poincarePullback B.X PB RB t))
      (trivialRigidifiedPair A.X.hom η[A.X].left (Over.w η[A.X]) T) := by
  letI := picardCommGrpObj A.X.hom PA RA
  letI := isMonHom_picardIdentityComponentι A.X.hom PA RA
  have h : (t ≫ picardIdentityComponentι B.X.hom PB RB) ≫
      picardPullback PA RA PB RB q.hom.hom = 1 := by
    rw [Category.assoc, ← picardIdentityComponentPullback_ι,
      ← Category.assoc, ht, MonObj.one_comp]
  exact (RigidifiedPair.Iso.sourcePullback η[A.X] η[B.X] q.hom.hom
      (IsMonHom.one_hom _) (poincareUniversalPullbackIso B.X PB RB t)).symm.trans
    (picardKernelTrivialization PA RA PB RB η[A.X] η[B.X] q.hom.hom
      (IsMonHom.one_hom _) (t ≫ picardIdentityComponentι B.X.hom PB RB) h)

/-- The same whole normalized trivialization is unique on every test
scheme, by the original source geometry. -/
theorem poincareKernelTrivialization_unique {T : FScheme k}
    (t : T ⟶ picardIdentityComponent B.X.hom PB RB)
    (ht : t ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1)
    (e : RigidifiedPair.Iso
      (RigidifiedPair.sourcePullback η[A.X] η[B.X] q.hom.hom (IsMonHom.one_hom _)
        (poincarePullback B.X PB RB t))
      (trivialRigidifiedPair A.X.hom η[A.X].left (Over.w η[A.X]) T)) :
    e = poincareKernelTrivialization A B PA RA PB RB q t ht :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    A.X.hom η[A.X].left (Over.w η[A.X]) _ _

/-- The original Poincare trivialization commutes with arbitrary parameter
pullback through the existing Poincare and source/parameter comparisons. -/
theorem poincareKernelTrivialization_naturality {T T' : FScheme k}
    (a : T' ⟶ T) (t : T ⟶ picardIdentityComponent B.X.hom PB RB)
    (ht : t ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1) :
    poincareKernelTrivialization A B PA RA PB RB q (a ≫ t)
        (by rw [Category.assoc, ht, MonObj.comp_one]) =
      (RigidifiedPair.Iso.sourcePullback η[A.X] η[B.X] q.hom.hom
        (IsMonHom.one_hom _) (poincarePullbackCompIso B.X PB RB a t)).trans
        ((RigidifiedPair.sourcePullbackParameterIso η[A.X] η[B.X] q.hom.hom
          (IsMonHom.one_hom _) a (poincarePullback B.X PB RB t)).symm.trans
          ((RigidifiedPair.Iso.map a
            (poincareKernelTrivialization A B PA RA PB RB q t ht)).trans
              (trivialRigidifiedPairMapIso A.X.hom η[A.X].left (Over.w η[A.X]) a))) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    A.X.hom η[A.X].left (Over.w η[A.X]) _ _

/-- On the original universal scheme kernel of the actual dual map, this
is the normalized trivialization of the SAME original Poincare pair. -/
def dualKernelPoincareTrivialization :
    let qDual := picardIdentityComponentPullbackGroupHom PA RA PB RB q.hom.hom
    RigidifiedPair.Iso
      (RigidifiedPair.sourcePullback η[A.X] η[B.X] q.hom.hom (IsMonHom.one_hom _)
        (poincarePullback B.X PB RB (Kernel.inclusion qDual).hom.hom))
      (trivialRigidifiedPair A.X.hom η[A.X].left (Over.w η[A.X])
        (Kernel.group qDual).X) := by
  let qDual := picardIdentityComponentPullbackGroupHom PA RA PB RB q.hom.hom
  exact poincareKernelTrivialization A B PA RA PB RB q (Kernel.inclusion qDual).hom.hom
    (Kernel.square qDual).w

section Characters

open Scheme.Modules Scheme.Modules.Invertible Scheme.Group.CartierDuality

/-- The actual frame of the source pullback is the same normalized
trivialization followed by the canonical comparison of the trivial line
bundle with the structure module. -/
def poincareKernelFrame {T : FScheme k}
    (t : T ⟶ picardIdentityComponent B.X.hom PB RB)
    (ht : t ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1) :
    (Modules.pullback (familyMapOfHom q.hom.hom T)).obj
      (poincarePullback B.X PB RB t).bundle.val ≅
      (SheafOfModules.unit (pullback A.X.hom T.hom).ringCatSheaf :
        (pullback A.X.hom T.hom).Modules) :=
  (poincareKernelTrivialization A B PA RA PB RB q t ht).iso ≪≫
    coproductUniqueIso (fun _ : PUnit.{u + 1} =>
      SheafOfModules.unit (pullback A.X.hom T.hom).ringCatSheaf)

/-- The original Poincare frame induces its genuine character of the
original kernel, on every parameter scheme. -/
def poincareKernelCharacter {T : FScheme k}
    (t : T ⟶ picardIdentityComponent B.X.hom PB RB)
    (ht : t ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1) :
    (Over.pullback T.hom).mapGrp.obj (Kernel.group q) ⟶
      MultiplicativeGroup.groupScheme T.left :=
  kernelTrivializationCharacter q (Kernel.marking q) T (poincarePullback B.X PB RB t).bundle
    (poincareKernelFrame A B PA RA PB RB q t ht)

/-- The original Picard representation supplies the tensor comparison
on its actual locally Noetherian tests. It uses the original two Poincare
pullbacks and their original rigidifications. -/
def poincarePullbackTensorIso {T : LocallyNoetherianOver (Spec (.of k))}
    (t s : T.obj ⟶ picardIdentityComponent B.X.hom PB RB) :
    (poincarePullback B.X PB RB (t * s)).bundle.val ≅
      (tensorLineBundle _ (poincarePullback B.X PB RB t).bundle
        (poincarePullback B.X PB RB s).bundle).val := by
  letI := picardCommGrpObj B.X.hom PB RB
  letI := isMonHom_picardIdentityComponentι B.X.hom PB RB
  let U := poincarePullback B.X PB RB t
  let V := poincarePullback B.X PB RB s
  let W : RigidifiedPair B.X.hom η[B.X].left (Over.w η[B.X]) T.obj :=
    ⟨tensorLineBundle _ U.bundle V.bundle,
      FrameTensor.tensorFrame (originSection B.X.hom η[B.X].left (Over.w η[B.X]) T.obj)
        U.bundle V.bundle U.rigidification V.rigidification⟩
  refine (poincarePullbackIsoOfFppfClass B.X PB RB (t * s) W ?_).iso
  rw [MonObj.mul_comp, picard_homEquiv_mul]
  let c : PicardGroup (pullback B.X.hom T.obj.hom) →+
      (fppfPicardSheaf B.X.hom).obj.obj (op T.obj) :=
    ((quotientProjection B.X.hom ≫ toFppfPicardSheaf B.X.hom).app (op T.obj)).hom
  have hU : c (classOf _ U.bundle) = RB.homEquiv
      (ObjectProperty.homMk (t ≫ picardIdentityComponentι B.X.hom PB RB) : T ⟶ PB) :=
    poincarePullback_fppfClass B.X PB RB t
  have hV : c (classOf _ V.bundle) = RB.homEquiv
      (ObjectProperty.homMk (s ≫ picardIdentityComponentι B.X.hom PB RB) : T ⟶ PB) :=
    poincarePullback_fppfClass B.X PB RB s
  have hsum := congrArg₂
    (fun x y : (fppfPicardSheaf B.X.hom).obj.obj (op T.obj) => x + y) hU.symm hV.symm
  exact hsum.trans (map_add c (classOf _ U.bundle) (classOf _ V.bundle)).symm

/-- The original character is multiplicative in the Picard point on each
represented test. The original normalized trivialization is used on the
left; the existing actual tensor frame computes the same character. -/
theorem poincareKernelCharacter_mul {T : LocallyNoetherianOver (Spec (.of k))}
    (t s : T.obj ⟶ picardIdentityComponent B.X.hom PB RB)
    (ht : t ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1)
    (hs : s ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1) :
    poincareKernelCharacter A B PA RA PB RB q (t * s)
        (by
          let := isMonHom_picardIdentityComponentPullback PA RA PB RB q.hom.hom
          rw [MonObj.mul_comp, ht, hs, _root_.one_mul]) =
      poincareKernelCharacter A B PA RA PB RB q t ht *
        poincareKernelCharacter A B PA RA PB RB q s hs := by
  let G := Kernel.group q
  let := MultiplicativeGroup.commGroup T.obj.left
  apply Grp.hom_ext
  apply (MultiplicativeGroup.sectionsUnitsEquiv T.obj.left
    ((Over.pullback T.obj.hom).mapGrp.obj G).X).injective
  let L := (poincarePullback B.X PB RB t).bundle
  let M := (poincarePullback B.X PB RB s).bundle
  let a := poincareKernelFrame A B PA RA PB RB q t ht
  let b := poincareKernelFrame A B PA RA PB RB q s hs
  let p := familyMapOfHom q.hom.hom T.obj
  have htm : (t * s) ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1 := by
    let := isMonHom_picardIdentityComponentPullback PA RA PB RB q.hom.hom
    rw [MonObj.mul_comp, ht, hs, _root_.one_mul]
  change MultiplicativeGroup.sectionsUnitsEquiv T.obj.left _
      (poincareKernelCharacter A B PA RA PB RB q (t * s) htm).hom.hom =
    MultiplicativeGroup.sectionsUnitsEquiv T.obj.left _
      ((poincareKernelCharacter A B PA RA PB RB q t ht).hom.hom *
        (poincareKernelCharacter A B PA RA PB RB q s hs).hom.hom)
  rw [MultiplicativeGroup.sectionsUnitsEquiv_mul]
  simp only [poincareKernelCharacter, sectionsUnitsEquiv_kernelTrivializationCharacter]
  exact (kernelMultiplier_eq_of_iso q (Kernel.marking q) T.obj _ _
      (tensorLineBundle _ L M) (poincarePullbackTensorIso B PB RB t s)
      (FrameTensor.tensorFrame p L M a b)).trans
    (kernelMultiplier_tensor q (Kernel.marking q) T.obj L a M b)

variable [IsFinite q.hom.hom.left] [IsCommMonObj (Kernel.group q).X]

private theorem sectionsUnitsEquiv_restrictCharacter (G : Grp (FScheme k))
    {T U : FScheme k} (r : U ⟶ T)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left) :
    MultiplicativeGroup.sectionsUnitsEquiv U.left ((Over.pullback U.hom).mapGrp.obj G).X
        (restrictCharacter G r c).hom.hom =
      Units.map ((familyScheme G.X.hom).map r).appTop.hom.toMonoidHom
        (MultiplicativeGroup.sectionsUnitsEquiv T.left
          ((Over.pullback T.hom).mapGrp.obj G).X c.hom.hom) := by
  have hbase : groupPullbackBaseMap G r = (familyScheme G.X.hom).map r := by
    apply pullback.hom_ext <;> simp
  change MultiplicativeGroup.affineHomUnits (pullback G.X.hom U.hom)
      ((restrictCharacter G r c).hom.hom.left ≫ Limits.prod.snd) =
    Units.map ((familyScheme G.X.hom).map r).appTop.hom.toMonoidHom
      (MultiplicativeGroup.affineHomUnits (pullback G.X.hom T.hom)
        (c.hom.hom.left ≫ Limits.prod.snd))
  rw [restrictCharacter_coordinates, MultiplicativeGroup.affineHomUnits_comp, hbase]
  rfl

omit [IsFinite q.hom.hom.left] [IsCommMonObj (Kernel.group q).X] in
/-- The original character of the same Poincare pair commutes with every
parameter pullback, including arbitrary nonreduced or non-Noetherian tests. -/
theorem poincareKernelCharacter_naturality {T U : FScheme k} (r : U ⟶ T)
    (t : T ⟶ picardIdentityComponent B.X.hom PB RB)
    (ht : t ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1) :
    restrictCharacter (Kernel.group q) r (poincareKernelCharacter A B PA RA PB RB q t ht) =
      poincareKernelCharacter A B PA RA PB RB q (r ≫ t)
        (by rw [Category.assoc, ht, MonObj.comp_one]) := by
  apply Grp.hom_ext
  apply (MultiplicativeGroup.sectionsUnitsEquiv U.left
    ((Over.pullback U.hom).mapGrp.obj (Kernel.group q)).X).injective
  rw [sectionsUnitsEquiv_restrictCharacter (Kernel.group q)]
  simp only [poincareKernelCharacter, sectionsUnitsEquiv_kernelTrivializationCharacter]
  let L := (poincarePullback B.X PB RB t).bundle
  let L' := pullbackLineBundle ((familyScheme B.X.hom).map r) L
  let a := poincareKernelFrame A B PA RA PB RB q t ht
  let a' := familyFramePullback q T L a r
  have e : (poincarePullback B.X PB RB (r ≫ t)).bundle.val ≅ L'.val :=
    (poincarePullbackCompIso B.X PB RB r t).iso
  exact ((kernelMultiplier_eq_of_iso q (Kernel.marking q) U _ _ L' e a').trans
    (kernelMultiplier_parameter q (Kernel.marking q) T L a r)).symm

variable (E : Grp (FScheme k))
  (j : E ⟶ Grp.mk (picardIdentityComponent B.X.hom PB RB))
  (hj : j.hom.hom ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1)

local notation "Gq" => Kernel.group q
local notation "ιE" => j.hom.hom

/-- The Cartier point represented by the character of the same original
Poincare frame along the given original zero-fibre inclusion. This permits
the actual multiplication kernel to be used directly. -/
def poincareKernelCartierMap : E.X ⟶ (dualGroup Gq).X :=
  (characterEquiv Gq E.X).symm (poincareKernelCharacter A B PA RA PB RB q ιE hj)

/-- The represented character formula on every actual test scheme. -/
theorem characterEquiv_comp_poincareKernelCartierMap {T : FScheme k} (t : T ⟶ E.X) :
    characterEquiv Gq T (t ≫ poincareKernelCartierMap A B PA RA PB RB q E j hj) =
      poincareKernelCharacter A B PA RA PB RB q (t ≫ ιE)
        (by rw [Category.assoc, hj, MonObj.comp_one]) := by
  rw [characterEquiv_naturality, poincareKernelCartierMap, Equiv.apply_symm_apply]
  exact poincareKernelCharacter_naturality A B PA RA PB RB q t ιE hj

private theorem characterEquiv_one (G : Grp (FScheme k))
    [IsFinite G.X.hom] [IsCommMonObj G.X] (T : FScheme k) :
    characterEquiv G T (1 : T ⟶ (dualGroup G).X) = 1 := by
  have h := characterEquiv_mul G T (1 : T ⟶ (dualGroup G).X) 1
  rw [_root_.one_mul] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

private theorem poincareKernelCartierMap_mul_at {T : LocallyNoetherianOver (Spec (.of k))}
    (x y : T.obj ⟶ E.X) :
    (x * y) ≫ poincareKernelCartierMap A B PA RA PB RB q E j hj =
      (x ≫ poincareKernelCartierMap A B PA RA PB RB q E j hj) *
        (y ≫ poincareKernelCartierMap A B PA RA PB RB q E j hj) := by
  apply (characterEquiv Gq T.obj).injective
  rw [characterEquiv_mul, characterEquiv_comp_poincareKernelCartierMap,
    characterEquiv_comp_poincareKernelCartierMap, characterEquiv_comp_poincareKernelCartierMap]
  have hx : (x ≫ ιE) ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1 := by
    rw [Category.assoc, hj, MonObj.comp_one]
  have hy : (y ≫ ιE) ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1 := by
    rw [Category.assoc, hj, MonObj.comp_one]
  simpa only [MonObj.mul_comp] using
    poincareKernelCharacter_mul A B PA RA PB RB q (T := T) (x ≫ ιE) (y ≫ ιE) hx hy

variable [LocallyOfFiniteType E.X.hom]

/-- The actual Cartier morphism is a group homomorphism. Picard
classification is used only on the original locally Noetherian group
square; the resulting morphism laws hold on every test. -/
theorem isMonHom_poincareKernelCartierMap :
    IsMonHom (poincareKernelCartierMap A B PA RA PB RB q E j hj) where
  one_hom := by
    let U : LocallyNoetherianOver (Spec (.of k)) :=
      ⟨𝟙_ (FScheme k), by change IsLocallyNoetherian (Spec (.of k)); infer_instance⟩
    have h := poincareKernelCartierMap_mul_at A B PA RA PB RB q E j hj (T := U) 1 1
    rw [_root_.one_mul] at h
    have h' : (1 : U.obj ⟶ E.X) ≫ poincareKernelCartierMap A B PA RA PB RB q E j hj = 1 :=
      mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
    simpa only [U, Hom.one_def, toUnit_unit, Category.id_comp] using h'
  mul_hom := by
    have : LocallyOfFiniteType (E.X ⊗ E.X).hom := by dsimp; infer_instance
    let U : LocallyNoetherianOver (Spec (.of k)) :=
      ⟨E.X ⊗ E.X, LocallyOfFiniteType.isLocallyNoetherian (E.X ⊗ E.X).hom⟩
    have hm := poincareKernelCartierMap_mul_at A B PA RA PB RB q E j hj (T := U)
      (fst E.X E.X) (snd E.X E.X)
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
    exact hm.trans (congrArg (fun f => f ≫ μ[(dualGroup Gq).X])
      (lift_fst_comp_snd_comp (poincareKernelCartierMap A B PA RA PB RB q E j hj)
        (poincareKernelCartierMap A B PA RA PB RB q E j hj)))

/-- The original Picard-kernel character map in the actual category of
original group schemes. -/
def poincareKernelCartierHom : E ⟶ dualGroup Gq :=
  letI := isMonHom_poincareKernelCartierMap A B PA RA PB RB q E j hj
  Grp.homMk (poincareKernelCartierMap A B PA RA PB RB q E j hj)

private theorem familyMapOfHom_isPullback {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (T : Over S) :
    IsPullback (familyMapOfHom f T) (pullback.fst X.hom T.hom)
      (pullback.fst Y.hom T.hom) f.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd Y.hom T.hom) (h₂₂ := Y.hom) (v₁₃ := T.hom)
    _ (familyMapOfHom_fst f T) (IsPullback.of_hasPullback Y.hom T.hom).flip
  simpa only [familyMapOfHom_snd, Over.w] using (IsPullback.of_hasPullback X.hom T.hom).flip

private theorem mono_of_originalKernel_eq_one {S : Scheme.{u}} {P Q : Grp (Over S)}
    (f : P ⟶ Q) (h : (Kernel.inclusion f).hom.hom = 1) : Mono f.hom.hom := by
  refine ⟨?_⟩
  intro U x y hxy
  have hx : (x * y⁻¹) ≫ f.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
  obtain ⟨z, hz, _⟩ := (Kernel.marking f).unique_lift (x * y⁻¹) hx
  change z ≫ (Kernel.inclusion f).hom.hom = x * y⁻¹ at hz
  have hd : x * y⁻¹ = 1 := by rw [← hz, h, MonObj.comp_one]
  exact mul_inv_eq_one.mp hd

variable [Mono j.hom.hom] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

/-- The original Picard-kernel character map is monic on all tests. The
locally Noetherian classification is used only on the actual scheme kernel
of this map, after descending its own original trivialization. -/
theorem mono_poincareKernelCartierHom :
    Mono (poincareKernelCartierHom A B PA RA PB RB q E j hj).hom.hom := by
  let δ := poincareKernelCartierHom A B PA RA PB RB q E j hj
  let Z := Kernel.group δ
  let i : Z.X ⟶ E.X := (Kernel.inclusion δ).hom.hom
  let t : Z.X ⟶ picardIdentityComponent B.X.hom PB RB := i ≫ ιE
  have ht : t ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1 := by
    change (i ≫ ιE) ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1
    rw [Category.assoc, hj, MonObj.comp_one]
  have hδ : i ≫ poincareKernelCartierMap A B PA RA PB RB q E j hj = 1 := (Kernel.square δ).w
  have hc := characterEquiv_comp_poincareKernelCartierMap A B PA RA PB RB q E j hj i
  rw [hδ, characterEquiv_one] at hc
  let L := (poincarePullback B.X PB RB t).bundle
  let a := poincareKernelFrame A B PA RA PB RB q t ht
  have hc' : kernelTrivializationCharacterMap q (Kernel.marking q) Z.X L a = 1 := by
    exact congrArg (fun f => f.hom.hom) hc.symm
  have : IsSeparated (dualGroup Gq).X.hom := inferInstance
  have : IsClosedImmersion i.left := Kernel.inclusion_isClosedImmersion δ
  have : LocallyOfFiniteType Z.X.hom := by
    rw [← Over.w i]
    infer_instance
  have : IsLocallyNoetherian Z.X.left := LocallyOfFiniteType.isLocallyNoetherian Z.X.hom
  let Zₙ : LocallyNoetherianOver (Spec (.of k)) := ⟨Z.X, inferInstance⟩
  let p := familyMapOfHom q.hom.hom Z.X
  have hp := familyMapOfHom_isPullback q.hom.hom Z.X
  have : IsFinite p := MorphismProperty.of_isPullback hp.flip inferInstance
  have : Flat p := MorphismProperty.of_isPullback hp.flip inferInstance
  have : Surjective p := MorphismProperty.of_isPullback hp.flip inferInstance
  have : IsLocallyNoetherian (pullback B.X.hom Z.X.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd B.X.hom Z.X.hom)
  let e := descendKernelTrivialization q (Kernel.marking q) Z.X L a
    (FppfSingle.singleton_cover_of_finite p) hc'
  have hz : classOf _ L = 0 := by
    rw [← classOf_trivial]
    exact Quotient.sound ⟨e ≪≫ (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
      SheafOfModules.unit (pullback B.X.hom Z.X.hom).ringCatSheaf)).symm⟩
  let := picardCommGrpObj B.X.hom PB RB
  let := isMonHom_picardIdentityComponentι B.X.hom PB RB
  let c : PicardGroup (pullback B.X.hom Z.X.hom) →+
      (fppfPicardSheaf B.X.hom).obj.obj (op Z.X) :=
    ((quotientProjection B.X.hom ≫ toFppfPicardSheaf B.X.hom).app (op Z.X)).hom
  have hclass : c (classOf _ L) = RB.homEquiv
      (ObjectProperty.homMk (t ≫ picardIdentityComponentι B.X.hom PB RB) : Zₙ ⟶ PB) :=
    poincarePullback_fppfClass B.X PB RB (T := Zₙ) t
  have hzero : c (classOf _ L) = 0 := (congrArg c hz).trans (map_zero c)
  have hP : t ≫ picardIdentityComponentι B.X.hom PB RB = 1 :=
    congrArg (fun f : Zₙ ⟶ PB => f.hom) (RB.homEquiv.injective
      ((hclass.symm.trans hzero).trans (picard_homEquiv_one B.X.hom PB RB Zₙ).symm))
  have : Mono (picardIdentityComponentι B.X.hom PB RB) := Over.mono_of_mono_left _
  have ht' : t = 1 := by
    apply (cancel_mono (picardIdentityComponentι B.X.hom PB RB)).mp
    rwa [MonObj.one_comp]
  have hi : i = 1 := by
    apply (cancel_mono ιE).mp
    rw [MonObj.one_comp]
    exact ht'
  exact mono_of_originalKernel_eq_one δ hi

/-- The same monomorphism after forgetting to the actual schemes. -/
theorem mono_poincareKernelCartierHom_left :
    Mono (poincareKernelCartierHom A B PA RA PB RB q E j hj).hom.hom.left := by
  have := mono_poincareKernelCartierHom A B PA RA PB RB q E j hj
  infer_instance

end Characters

end AlgebraicGeometry.Scheme.RelativePicard
