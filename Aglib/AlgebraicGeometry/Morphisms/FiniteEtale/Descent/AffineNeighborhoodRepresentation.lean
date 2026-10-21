/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineSingleChartSheafDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineCoverAlgebra
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineTrivializingNeighborhood
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.OpenRepresentatives
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverConstant

/-! Produce actual finite-etale representatives on affine open neighborhoods. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u

/-- The natural isomorphism from inverse image along `𝟙 X` to the identity functor
on set-valued sheaves on the small étale site of `X`. -/
def setInverseImageId (X : Scheme.{u}) : Scheme.EtaleCohomology.setInverseImage (𝟙 X) ≅ 𝟭
  (Scheme.EtaleCohomology.SetSheaf X) := by
  let adj := (Scheme.EtaleCohomology.siteBaseChange (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology X)
  let e := Functor.sheafPushforwardContinuousId' (Scheme.EtaleCohomology.siteBaseChangeId X)
    (Type (u + 1)) (Scheme.smallEtaleTopology X)
  exact (adj.ofNatIsoRight e).leftAdjointUniq Adjunction.id

/-- A single actual surjective affine etale trivializing chart produces a
representative of the sheaf on the affine base. -/
theorem exists_of_affine_trivializing_chart {X : Scheme.{u}} [IsAffine X]
    (F : Scheme.EtaleCohomology.SetSheaf X) (S : CommRingCat.{u}) (f : Spec S ⟶ X) [Etale f]
      [Surjective f]
    (A : Type u) [Finite A]
    (hlocal : (Scheme.EtaleCohomology.setInverseImage f).obj F ≅
      (constantSheaf (Scheme.smallEtaleTopology (Spec S)) (Type (u + 1))).obj (ULift.{u + 1} A)) :
    ∃ Y : Scheme.FiniteEtale X, Nonempty (Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y ≅ F)
      := by
  let R := Γ(X, ⊤)
  let r : R ⟶ S := Spec.preimage (f ≫ X.isoSpec.hom)
  let : Algebra R S := r.hom.toAlgebra
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) = f ≫ X.isoSpec.hom :=
    Spec.map_preimage _
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by rw [hq]; infer_instance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by rw [hq]; infer_instance
  have : Algebra.Etale R S := RingHom.etale_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @Etale)).1 inferInstance)
  have : Module.FaithfullyFlat R S := RingHom.faithfullyFlat_algebraMap_iff.1
    ((flat_and_surjective_SpecMap_iff _).1 ⟨inferInstance, inferInstance⟩)
  let FR : Scheme.EtaleCohomology.SetSheaf (Spec R) := (Scheme.EtaleCohomology.setInverseImage
    X.isoSpec.inv).obj F
  have hc : (Scheme.EtaleCohomology.setInverseImage (AffineSheafAlgebraDatum.chart R S)).obj FR ≅
      (constantSheaf (Scheme.smallEtaleTopology (Spec S)) (Type (u + 1))).obj (ULift.{u + 1} A) :=
    ((setInverseImageComp X.isoSpec.inv (AffineSheafAlgebraDatum.chart R S)).app F).symm ≪≫
    eqToIso (congrArg (fun q => (Scheme.EtaleCohomology.setInverseImage q).obj F) (by
      change Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ X.isoSpec.inv = f
      rw [hq, Category.assoc, Iso.hom_inv_id, Category.comp_id])) ≪≫ hlocal
  let YS := trivialCover (Spec S) A
  let eYS : Scheme.EtaleCohomology.finiteRepresentedSetSheaf YS ≅
      (Scheme.EtaleCohomology.setEtaleRestriction (AffineSheafAlgebraDatum.chart R S)).obj FR :=
    trivialCoverConstantIso (Spec S) A ≪≫ hc.symm ≪≫
      (Scheme.EtaleCohomology.setInverseImageEtaleIso (AffineSheafAlgebraDatum.chart R S)).app FR
  let M := AffineDescent.algebraModel YS
  let : Algebra R M.algebra := ((algebraMap S M.algebra).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S M.algebra := IsScalarTower.of_algebraMap_eq' rfl
  let eB : Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.specCover S M.algebra) ≅
      (Scheme.EtaleCohomology.setEtaleRestriction (AffineSheafAlgebraDatum.chart R S)).obj FR :=
    Scheme.EtaleCohomology.finiteRepresentedSetSheafMapIso M.iso ≪≫ eYS
  obtain ⟨Z, ⟨eZ⟩⟩ := AffineSheafAlgebraDatum.exists_affine_representative FR M.algebra eB
  refine ⟨(baseChange X.isoSpec.hom).obj Z, ⟨?_⟩⟩
  exact (finiteRepresentedInverseImageIso X.isoSpec.hom Z).symm ≪≫
    (Scheme.EtaleCohomology.setInverseImage X.isoSpec.hom).mapIso eZ ≪≫
    ((setInverseImageComp X.isoSpec.inv X.isoSpec.hom).app F).symm ≪≫
    eqToIso (congrArg (fun q => (Scheme.EtaleCohomology.setInverseImage q).obj F)
      X.isoSpec.hom_inv_id) ≪≫
    (setInverseImageId X).app F

variable {X : Scheme.{u}} {F : Scheme.EtaleCohomology.SetSheaf X} {x : X}

/-- Turn the constructed affine trivializing neighborhood into an actual
representative on its open range in the original scheme. -/
def AffineTrivializingNeighborhood.representation (N : AffineTrivializingNeighborhood F x) :
    FiniteSetOpenRepresentation F N.baseMap.opensRange := by
  apply Classical.choice
  let FU := (Scheme.EtaleCohomology.setInverseImage N.baseMap).obj F
  have hc : (Scheme.EtaleCohomology.setInverseImage N.chart).obj FU ≅
      (constantSheaf (Scheme.smallEtaleTopology (Spec N.ring)) (Type (u + 1))).obj
        (ULift.{u + 1} N.value) :=
    ((setInverseImageComp N.baseMap N.chart).app F).symm ≪≫ N.trivialization
  obtain ⟨Y, ⟨eY⟩⟩ := exists_of_affine_trivializing_chart FU N.ring N.chart N.value hc
  exact ⟨FiniteSetOpenRepresentation.ofOpenImmersion N.baseMap Y
    (eY ≪≫ (Scheme.EtaleCohomology.setInverseImageEtaleIso N.baseMap).app F)⟩

theorem AffineTrivializingNeighborhood.goodOpen (N : AffineTrivializingNeighborhood F x) :
    IsGoodAffineOpen F N.baseMap.opensRange :=
  ⟨isAffineOpen_opensRange N.baseMap, ⟨N.representation⟩⟩

theorem
  _root_.AlgebraicGeometry.Scheme.EtaleCohomology.FiniteSetLocalTrivialization.exists_goodAffineOpen
    (t : Scheme.EtaleCohomology.FiniteSetLocalTrivialization F) (x : X) :
    ∃ U : X.Opens, IsGoodAffineOpen F U ∧ x ∈ U := by
  let N := t.affineTrivializingNeighborhood x
  exact ⟨N.baseMap.opensRange, N.goodOpen, ⟨N.point, N.point_eq⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 4f74c3eff4d7b9bbaa7ae8660b0dad8dbb07554b5c1f438ad765e9d66e6e8246.
Definitions, hypotheses and universes are retained modulo native names. -/
