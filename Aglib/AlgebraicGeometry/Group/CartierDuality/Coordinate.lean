/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.CategoryTheory.Monoidal.CommMonObjOfMono
public import Aglib.CategoryTheory.Monoidal.Grp.Transport
public import Aglib.RingTheory.HopfAlgebra.FiniteDual
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The original finite group scheme and its coordinate Hopf dual

The selected coordinate Hopf algebra is exactly the native global sections of
the original group scheme. Its group comparison uses the original `isoSpec`.
The dual group is the native Spec of the already constructed linear-dual Hopf
algebra. Finiteness is derived from the actual structure morphism; no point
count, alternate finite-group carrier, or etaleness assumption is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj Module.Dual.FiniteDual

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

open AlgebraicGeometry.Scheme.OverField (FScheme Base)

variable {k : Type u} [Field k]

/-- The native Spec functor retains its braided structure for coordinate comparisons. -/
local instance instBraidedAlgSpecCoordinate :
    (AlgebraicGeometry.algSpec (CommRingCat.of k)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

/-- The existing affine global-sections algebra with its original base and scheme explicit. -/
abbrev affineCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) :=
  instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfOverSpecOfIsAffine
    (R := R) (X := Y)

/-- Native Spec of a Hopf algebra, with the scheme category fixed before evaluating coordinates. -/
def specGroup (A : CommHopfAlgCat.{u} k) : Grp (FScheme k) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).obj (op A)

@[simp]
theorem specGroup_hom (A : CommHopfAlgCat.{u} k) :
    (specGroup A).X.hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native Hopf/cogroup roundtrip comparison, before choosing coordinates. -/
def specGroupCogroupIso (H : Grp (CommAlgCat.{u} k)ᵒᵖ) :
    specGroup ((commHopfAlgCatEquivCogrpCommAlgCat k).inverse.obj (op H)) ≅
      (AlgebraicGeometry.algSpec (CommRingCat.of k)).mapGrp.obj H :=
  (AlgebraicGeometry.algSpec (CommRingCat.of k)).mapGrp.mapIso
    (((commHopfAlgCatEquivCogrpCommAlgCat k).counitIso.app (op H)).unop.symm)

@[simp]
theorem specGroupCogroupIso_inv_hom (H : Grp (CommAlgCat.{u} k)ᵒᵖ) :
    (specGroupCogroupIso H).inv.hom.hom =
      𝟙 ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj H.X) := by
  change (AlgebraicGeometry.algSpec (CommRingCat.of k)).map (𝟙 H.X) = _
  exact (AlgebraicGeometry.algSpec (CommRingCat.of k)).map_id H.X

/-- Composing the native roundtrip keeps the original inverse arrow. -/
theorem specGroupCogroupIso_trans_inv_hom (H : Grp (CommAlgCat.{u} k)ᵒᵖ)
    (G : Grp (FScheme k))
    (e : (AlgebraicGeometry.algSpec (CommRingCat.of k)).mapGrp.obj H ≅ G) :
    (specGroupCogroupIso H ≪≫ e).inv.hom.hom = e.inv.hom.hom := by
  rw [Iso.trans_inv, Grp.comp_hom_hom, specGroupCogroupIso_inv_hom]
  exact Category.comp_id e.inv.hom.hom


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The one selected coordinate Hopf algebra: native global sections of the same finite group. -/
def coordinateHopf (G : Grp (FScheme k)) [IsFinite G.X.hom] : CommHopfAlgCat.{u} k := by
  let R : CommRingCat.{u} := CommRingCat.of k
  let Y : Scheme.{u} := G.X.left
  letI : Y.Over (Spec R) := OverClass.fromOver G.X
  letI : IsAffine Y := isAffine_of_isAffineHom G.X.hom
  letI : GrpObj (Y.asOver (Spec R)) := by
    change GrpObj G.X
    infer_instance
  letI : Algebra R Γ(Y, ⊤) := affineCoordinateAlgebra R Y
  letI : (AlgebraicGeometry.algSpec R).Braided := AlgebraicGeometry.braidedAlgSpec
  let X : (CommAlgCat R)ᵒᵖ := op (CommAlgCat.of R Γ(Y, ⊤))
  let e : G.X ≅ (AlgebraicGeometry.algSpec R).obj X := Y.isoSpec.asOver (Spec R)
  letI : GrpObj ((AlgebraicGeometry.algSpec R).obj X) := GrpObj.ofIso e
  letI : GrpObj X := (AlgebraicGeometry.algSpec.fullyFaithful (R := R)).grpObj X
  exact (commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj (op (Grp.mk X))

/-- The selected coordinate Hopf algebra has literally the original global-section carrier. -/
theorem coordinateHopf_carrier (G : Grp (FScheme k)) [IsFinite G.X.hom] :
    (coordinateHopf G : Type u) = Γ(G.X.left, ⊤) := rfl

-- This follows the same faithful transport used by Mathlib's native Gamma Hopf instance.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The native affine comparison preserves the original group structure. -/
def coordinateSpecIso (G : Grp (FScheme k)) [IsFinite G.X.hom] :
    specGroup (coordinateHopf G) ≅ G := by
  let R : CommRingCat.{u} := CommRingCat.of k
  let Y : Scheme.{u} := G.X.left
  letI : Y.Over (Spec R) := OverClass.fromOver G.X
  letI : IsAffine Y := isAffine_of_isAffineHom G.X.hom
  letI : GrpObj (Y.asOver (Spec R)) := by
    change GrpObj G.X
    infer_instance
  letI : Algebra R Γ(Y, ⊤) := affineCoordinateAlgebra R Y
  letI : (AlgebraicGeometry.algSpec R).Braided := AlgebraicGeometry.braidedAlgSpec
  let X : (CommAlgCat R)ᵒᵖ := op (CommAlgCat.of R Γ(Y, ⊤))
  let e : (AlgebraicGeometry.algSpec R).obj X ≅ G.X :=
    (Y.isoSpec.asOver (Spec R)).symm
  letI : GrpObj ((AlgebraicGeometry.algSpec R).obj X) := GrpObj.ofIso e.symm
  letI : GrpObj X := (AlgebraicGeometry.algSpec.fullyFaithful (R := R)).grpObj X
  exact specGroupCogroupIso (Grp.mk X) ≪≫
    AlgebraicGeometry.algSpec.fullyFaithful.grpObjIso X G e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem coordinateSpecIso_inv_left (G : Grp (FScheme k)) [IsFinite G.X.hom] :
    (coordinateSpecIso G).inv.hom.hom.left = G.X.left.toSpecΓ := by
  dsimp only [coordinateSpecIso]
  rw [specGroupCogroupIso_trans_inv_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Commutativity of the actual Spec group reflects cocommutativity of its Hopf algebra. -/
theorem isCocomm_of_isCommSpec (A : CommHopfAlgCat.{u} k)
    [IsCommMonObj (specGroup A).X] :
    Coalgebra.IsCocomm k A := by
  let R : CommRingCat.{u} := CommRingCat.of k
  let X : (CommAlgCat R)ᵒᵖ := op (CommAlgCat.of R A)
  let F := AlgebraicGeometry.algSpec R
  let : F.Braided := AlgebraicGeometry.braidedAlgSpec
  let : MonObj (F.obj X) := Functor.monObjObj (F := F) X
  have : IsCommMonObj (F.obj X) :=
    inferInstanceAs (IsCommMonObj (specGroup A).X)
  have : IsCommMonObj X := by
    constructor
    apply (AlgebraicGeometry.algSpec.fullyFaithful (R := R)).map_injective
    rw [F.map_comp]
    apply (cancel_epi (Functor.LaxMonoidal.μ F X X)).mp
    simpa only [Functor.obj.μ_def, Category.assoc, Functor.LaxBraided.braided_assoc] using
      (IsCommMonObj.mul_comm (F.obj X))
  constructor
  ext a
  exact congr($(IsCommMonObj.mul_comm X).unop.hom a)

/-- Cocommutativity comes from the original commutative group object. -/
instance coordinate_isCocomm (G : Grp (FScheme k)) [IsFinite G.X.hom]
    [IsCommMonObj G.X] : Coalgebra.IsCocomm k (coordinateHopf G) := by
  let e := coordinateSpecIso G
  have : IsIso e.hom.hom.hom := by
    change IsIso ((Grp.forget (FScheme k)).map e.hom)
    infer_instance
  have : IsCommMonObj (specGroup (coordinateHopf G)).X :=
    IsCommMonObj.of_mono e.hom.hom.hom
  exact isCocomm_of_isCommSpec (coordinateHopf G)

/-- Finiteness of the actual group morphism gives finite-dimensional coordinates. -/
instance coordinate_finiteDimensional (G : Grp (FScheme k)) [IsFinite G.X.hom] :
    FiniteDimensional k (coordinateHopf G) := by
  let e := coordinateSpecIso G
  have : IsIso e.hom.hom.hom.left := by
    change IsIso ((Over.forget (Base k)).map ((Grp.forget (FScheme k)).map e.hom))
    infer_instance
  have h : IsFinite (specGroup (coordinateHopf G)).X.hom := by
    rw [← e.hom.hom.hom.w]
    infer_instance
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (coordinateHopf G)))) at h
  rw [IsFinite.SpecMap_iff] at h
  simpa only [CommRingCat.hom_ofHom, RingHom.finite_algebraMap] using h

/-- The actual finite Cartier-dual group, using native Spec of the native linear dual. -/
def dualGroup (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X] :
    Grp (FScheme k) :=
  specGroup (CommHopfAlgCat.of k (Module.Dual k (coordinateHopf G)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native Spec sends a cocommutative Hopf algebra to a commutative group. -/
instance specGroup_isComm (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    IsCommMonObj (specGroup A).X := by
  change IsCommMonObj ((Spec (CommRingCat.of A)).asOver (Base k))
  infer_instance

/-- The native dual group is commutative because the original coordinate ring is commutative. -/
instance dualGroup_isComm (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X] :
    IsCommMonObj (dualGroup G).X := by
  unfold dualGroup
  infer_instance

/-- The native dual structure morphism is finite in every characteristic. -/
instance dualGroup_finite (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X] :
    IsFinite (dualGroup G).X.hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap k (Module.Dual k (coordinateHopf G)))))
  rw [IsFinite.SpecMap_iff]
  simpa only [CommRingCat.hom_ofHom, RingHom.finite_algebraMap] using
    (inferInstance : Module.Finite k (Module.Dual k (coordinateHopf G)))

/-- The actual dual is flat over the ground field; no invertibility of its rank is required. -/
instance dualGroup_flat (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X] :
    Flat (dualGroup G).X.hom := by
  infer_instance

end AlgebraicGeometry.Scheme.Group.CartierDuality
