/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism

/-!
# The original global Cartier coefficient row

The original tensor--Hom equivalence proves right exactness of the actual
module-sheaf tensor. The original closed projection formula identifies the
tensor quotient with the original pullback/pushforward unit. The actual ideal
algebra and dual evaluation then identify the first map with the canonical
Cartier section, with positive sign.

The resulting row is short exact for any coefficient on which this original
section is monic. No coefficient freeness, coherence or Noetherian hypothesis
is needed for this lower family. Installed global right-adjoint concentration
and its counit-compatible purity isomorphism are not yet asserted here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

private theorem tensorCancellation_action
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    (L M I : C) (i : I ⟶ 𝟙_ C) :
    (α_ L M I).hom ≫ L ◁ (β_ M I).hom ≫ (α_ L I M).inv ≫
        (L ◁ i) ▷ M ≫ (ρ_ L).hom ▷ M =
      (L ⊗ M) ◁ i ≫ (ρ_ (L ⊗ M)).hom := by
  have hunit : (α_ L (𝟙_ C) M).inv ≫ (ρ_ L).hom ▷ M = L ◁ (λ_ M).hom := by
    rw [← triangle L M, Iso.inv_hom_id_assoc]
  rw [← associator_inv_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    ← braiding_naturality_right, whiskerLeft_comp_assoc,
    ← associator_naturality_right_assoc, hunit, ← whiskerLeft_comp,
    braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← rightUnitor_tensor_hom]

private def tensorCancellationIso
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    (L M I : C) (e : L ⊗ I ≅ 𝟙_ C) : (L ⊗ M) ⊗ I ≅ M :=
  (α_ L M I) ≪≫ (tensorLeft L).mapIso (β_ M I) ≪≫ (α_ L I M).symm ≪≫
    (tensorRight M).mapIso e ≪≫ λ_ M

private theorem tensorCancellationIso_section
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    (L M I : C) (e : L ⊗ I ≅ 𝟙_ C) (s : 𝟙_ C ⟶ L) (i : I ⟶ 𝟙_ C)
    (he : e.hom ≫ s = L ◁ i ≫ (ρ_ L).hom) :
    (tensorCancellationIso L M I e).hom ≫ ((λ_ M).inv ≫ s ▷ M) =
      (L ⊗ M) ◁ i ≫ (ρ_ (L ⊗ M)).hom := by
  change ((α_ L M I).hom ≫ L ◁ (β_ M I).hom ≫ (α_ L I M).inv ≫
    e.hom ▷ M ≫ (λ_ M).hom) ≫ ((λ_ M).inv ≫ s ▷ M) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight, he, comp_whiskerRight]
  exact tensorCancellation_action L M I i

private theorem tensorQuotientZero
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {I O P : C}
    (φ : I ⟶ O) (s : O ⟶ P) (hzero : φ ≫ s = 0)
    {N Q : D} (r : F.obj O ≅ N) (e : F.obj P ≅ Q) (q : N ⟶ Q)
    (he : F.map s ≫ e.hom = r.hom ≫ q) : (F.map φ ≫ r.hom) ≫ q = 0 := by
  rw [Category.assoc, ← he, ← Category.assoc, ← Functor.map_comp,
    hzero, Functor.map_zero, zero_comp]

private theorem tensorCancellationZero
    {C : Type*} [Category* C] [HasZeroMorphisms C] {A M N Q : C}
    (c : A ≅ M) (τ : M ⟶ N) (μ : A ⟶ N) (q : N ⟶ Q)
    (hc : c.hom ≫ τ = μ) (hzero : μ ≫ q = 0) : τ ≫ q = 0 := by
  apply (cancel_epi c.hom).mp
  rw [comp_zero, ← Category.assoc, hc, hzero]

namespace AlgebraicGeometry.Scheme.Modules

universe u

private theorem tensorHomEquiv_coefficient_naturality (X : Scheme.{u}) (N : X.Modules)
    {M M' P : X.Modules} (f : M' ⟶ M) (h : tensorSheaf X M N ⟶ P) :
    Pullback.Tensor.tensorHomEquiv X M' N P ((moduleTensorRightFunctor X N).map f ≫ h) =
      f ≫ Pullback.Tensor.tensorHomEquiv X M N P h := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (_ : InternalHom.RawHom X N P U.unop) = _
  ext V n
  change h.val.app (op V.unop.left)
      ((tensorSheafMap X f (𝟙 N)).val.app (op V.unop.left)
        ((tensorSheafUnit X M' N).app (op V.unop.left)
          (M'.val.map V.unop.hom.op m ⊗ₜ n))) =
    h.val.app (op V.unop.left)
      ((tensorSheafUnit X M N).app (op V.unop.left)
        (M.val.map V.unop.hom.op (f.val.app U m) ⊗ₜ n))
  have ht := tensorSheafMap_tmul X f (𝟙 N) (op V.unop.left)
    (M'.val.map V.unop.hom.op m) n
  have hn := PresheafOfModules.naturality_apply f.val V.unop.hom.op m
  exact (congrArg (h.val.app (op V.unop.left)) ht).trans
    (congrArg (fun z => h.val.app (op V.unop.left)
      ((tensorSheafUnit X M N).app (op V.unop.left) (z ⊗ₜ n))) hn)

private theorem moduleTensorRight_isLeftAdjoint (X : Scheme.{u}) (N : X.Modules) :
    (moduleTensorRightFunctor X N).IsLeftAdjoint := by
  let E (M P : X.Modules) := Pullback.Tensor.tensorHomEquiv X M N P
  let adj := Adjunction.adjunctionOfEquivRight (F := moduleTensorRightFunctor X N) E
    (fun _ _ _ f h => tensorHomEquiv_coefficient_naturality X N f h)
  exact adj.isLeftAdjoint

private theorem moduleTensorLeft_rightExact (X : Scheme.{u}) (N : X.Modules)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTensorLeftFunctor X N)).Exact ∧
      Epi ((moduleTensorLeftFunctor X N).map S.g) := by
  let : (moduleTensorRightFunctor X N).IsLeftAdjoint := moduleTensorRight_isLeftAdjoint X N
  let : PreservesFiniteColimits (moduleTensorRightFunctor X N) := inferInstance
  let : PreservesFiniteColimits (moduleTensorLeftFunctor X N) :=
    preservesFiniteColimits_of_natIso (moduleTensorRightLeftIso X N)
  let : (moduleTensorLeftFunctor X N).Additive := moduleTensorLeftFunctor_additive X N
  let : Epi S.g := hS.epi_g
  exact ⟨hS.exact.map_of_epi_of_preservesCokernel
    (moduleTensorLeftFunctor X N) hS.epi_g inferInstance, inferInstance⟩

/-- Two actual ideal sections commute after applying the original ideal inclusion. -/
public theorem idealInclusion_smul_comm {D X : Scheme.{u}} (i : D ⟶ X) (U : X.Opens)
    (a b : Γ(idealModule i, U)) :
    (show Γ(X, U) from (idealInclusion i).val.app (op U) a) • b =
      (show Γ(X, U) from (idealInclusion i).val.app (op U) b) • a := by
  apply (idealSectionsEquiv i U).injective
  apply Subtype.ext
  let r : Γ(X, U) := (idealInclusion i).val.app (op U) a
  let s : Γ(X, U) := (idealInclusion i).val.app (op U) b
  have ha : (show Γ(X, U) from (idealInclusion i).val.app (op U) (r • b)) = r * s :=
    ((idealInclusion i).val.app (op U)).hom.map_smul r b
  have hb : (show Γ(X, U) from (idealInclusion i).val.app (op U) (s • a)) = s * r :=
    ((idealInclusion i).val.app (op U)).hom.map_smul s a
  exact (idealSectionsEquiv_val i U (r • b)).trans
    (ha.trans ((mul_comm r s).trans
      (hb.symm.trans (idealSectionsEquiv_val i U (s • a)).symm)))

private theorem idealEvaluation_transpose_presheaf {D X : Scheme.{u}} (i : D ⟶ X) :
    evaluationPresheaf X (idealModule i) (SheafOfModules.unit X.ringCatSheaf) ≫
      (cartierDualIdealSection i).val =
    PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        (𝟙 (dualSheaf X (idealModule i)).val) (idealInclusion i).val ≫
      (MonoidalCategory.rightUnitor (C := PresheafOfModulesOfCommRing.{u} X.presheaf)
        (show PresheafOfModulesOfCommRing.{u} X.presheaf from
          (dualSheaf X (idealModule i)).val)).hom := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro ell a
  apply Subtype.ext
  change (_ : InternalHom.RawHom X (idealModule i)
    (SheafOfModules.unit X.ringCatSheaf) U.unop) = _
  ext V b
  change Γ(idealModule i, V.unop.left) at b
  let aV : Γ(idealModule i, V.unop.left) := (idealModule i).val.map V.unop.hom.op a
  have hi := PresheafOfModules.naturality_apply (idealInclusion i).val V.unop.hom.op a
  change (idealInclusion i).val.app (op V.unop.left) aV =
    X.presheaf.map V.unop.hom.op ((idealInclusion i).val.app U a) at hi
  have he := NatTrans.naturality_apply ell.val
    (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U.unop)).op a
  change ell.val.app V aV =
    X.presheaf.map V.unop.hom.op (ell.val.app (op (Over.mk (𝟙 U.unop))) a) at he
  change X.presheaf.map V.unop.hom.op
      (ell.val.app (op (Over.mk (𝟙 U.unop))) a) *
        (show Γ(X, V.unop.left) from (idealInclusion i).val.app (op V.unop.left) b) =
    X.presheaf.map V.unop.hom.op ((idealInclusion i).val.app U a) *
      (show Γ(X, V.unop.left) from ell.val.app V b)
  rw [← he, ← hi, mul_comm (show Γ(X, V.unop.left) from ell.val.app V aV)]
  let r : Γ(X, V.unop.left) := (idealInclusion i).val.app (op V.unop.left) aV
  let s : Γ(X, V.unop.left) := (idealInclusion i).val.app (op V.unop.left) b
  have h := congrArg (ell.val.app V) (idealInclusion_smul_comm i V.unop.left aV b)
  have hleft : (show Γ(X, V.unop.left) from ell.val.app V (r • b)) =
      r * (show Γ(X, V.unop.left) from ell.val.app V b) := ell.property V r b
  have hright : (show Γ(X, V.unop.left) from ell.val.app V (s • aV)) =
      s * (show Γ(X, V.unop.left) from ell.val.app V aV) := ell.property V s aV
  exact hright.symm.trans (h.symm.trans hleft)

private theorem evaluationSheaf_tmul (X : Scheme.{u}) (M N : X.Modules) (U : X.Opens)
    (ell : (InternalHom.sheaf X M N).val.obj (op U)) (a : Γ(M, U)) :
    (evaluationSheaf X M N).val.app (op U)
      ((tensorSheafUnit X (InternalHom.sheaf X M N) M).app (op U) (ell ⊗ₜ a)) =
        ell.val.app (op (Over.mk (𝟙 U))) a := by
  have h := (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).apply_symm_apply
    (evaluationPresheaf X M N)
  exact congrArg (fun f => f.app (op U) (ell ⊗ₜ a)) h

/-- Actual ideal evaluation followed by its transpose is the original tensor ideal action. -/
public theorem idealEvaluation_transpose {D X : Scheme.{u}} (i : D ⟶ X) :
    evaluationSheaf X (idealModule i) (SheafOfModules.unit X.ringCatSheaf) ≫
        cartierDualIdealSection i =
      tensorSheafMap X (𝟙 (dualSheaf X (idealModule i))) (idealInclusion i) ≫
        ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app
          (dualSheaf X (idealModule i))).hom := by
  apply moduleTensor_hom_ext
  intro U ell a
  let L : X.Modules := dualSheaf X (idealModule i)
  let s := (cartierDualIdealSection i).val.app (op U)
  let r := ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app L).hom.val.app (op U)
  have hev := evaluationSheaf_tmul X (idealModule i)
    (SheafOfModules.unit X.ringCatSheaf) U ell a
  have hm := tensorSheafMap_tmul X (𝟙 L) (idealInclusion i) (op U) ell a
  have hu := tensorRightUnitIso_hom_section X L U ell
    (show Γ(X, U) from (idealInclusion i).val.app (op U) a)
  have hp := congrArg (fun f => f.app (op U) (ell ⊗ₜ a))
    (idealEvaluation_transpose_presheaf i)
  change s (ell.val.app (op (Over.mk (𝟙 U))) a) =
    (show Γ(X, U) from (idealInclusion i).val.app (op U) a) •
      (show Γ(L, U) from ell) at hp
  exact (congrArg (fun z => s z) hev).trans
    (hp.trans (hu.symm.trans (congrArg (fun z => r z) hm.symm)))

/-- The positive evaluation identity uses the actual invertible ideal evaluation. -/
public theorem cartierDualEvaluation_transpose {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) :
    (dualEvaluationIso X ⟨idealModule i, hI⟩).hom ≫ cartierDualIdealSection i =
      tensorSheafMap X (𝟙 (dualSheaf X (idealModule i))) (idealInclusion i) ≫
        ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app
          (dualSheaf X (idealModule i))).hom := by
  exact (congrArg (fun f => f ≫ cartierDualIdealSection i)
    (dualEvaluationIso_hom X ⟨idealModule i, hI⟩)).trans (idealEvaluation_transpose i)

/-- The specified cancellation isomorphism uses only the original tensor maps and evaluation. -/
public def cartierCoefficientCancellationIso {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) :
    tensorSheaf X (tensorSheaf X (dualSheaf X (idealModule i)) M) (idealModule i) ≅ M :=
  tensorSheafAssociator X (dualSheaf X (idealModule i)) M (idealModule i) ≪≫
    (moduleTensorLeftFunctor X (dualSheaf X (idealModule i))).mapIso
      (tensorSheafBraiding X M (idealModule i)) ≪≫
    (tensorSheafAssociator X (dualSheaf X (idealModule i)) (idealModule i) M).symm ≪≫
    (moduleTensorRightFunctor X M).mapIso (dualEvaluationIso X ⟨idealModule i, hI⟩) ≪≫
    tensorSheafLeftUnit X M

/-- The original coefficient-row first map is the canonical section, with positive sign. -/
public theorem cartierCoefficientCancellationIso_section {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) :
    (cartierCoefficientCancellationIso i hI M).hom ≫ (cartierTensorSection i).app M =
      (moduleTensorLeftFunctor X (tensorSheaf X (dualSheaf X (idealModule i)) M)).map
          (idealInclusion i) ≫
        ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app
          (tensorSheaf X (dualSheaf X (idealModule i)) M)).hom := by
  let I : X.Modules := idealModule i
  let L : X.Modules := dualSheaf X I
  let e₀ := dualEvaluationIso X ⟨idealModule i, hI⟩
  let e : (L ⊗ I : X.Modules) ≅ 𝟙_ X.Modules :=
    ⟨e₀.hom, e₀.inv, e₀.hom_inv_id, e₀.inv_hom_id⟩
  exact tensorCancellationIso_section (C := X.Modules) L M I e
    (cartierDualIdealSection i) (idealInclusion i) (cartierDualEvaluation_transpose i hI)

/-- Original closed projection formula, followed by the original right tensor unitor. -/
public def closedImmersionTensorQuotientIso {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : X.Modules) :
    (moduleTensorLeftFunctor X N).obj
        ((pushforward i).obj (SheafOfModules.unit D.ringCatSheaf)) ≅
      (pushforward i).obj ((pullback i).obj N) :=
  closedImmersionProjectionFormulaIso i N (SheafOfModules.unit D.ringCatSheaf) ≪≫
    (pushforward i).mapIso
      ((SheafOfModulesOfCommRing.tensorRightUnitIso D.sheaf).app ((pullback i).obj N))

/-- The quotient tensor map is exactly the original geometric quotient unit. -/
private theorem closedImmersionTensorQuotientIso_section {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : X.Modules) (U : X.Opens)
    (n : Γ(N, U)) (a : Γ(D, i ⁻¹ᵁ U)) :
    (closedImmersionTensorQuotientIso i N).hom.val.app (op U)
      (moduleTensorSection X N ((pushforward i).obj (SheafOfModules.unit D.ringCatSheaf))
        U n a) =
      a • (show Γ((pullback i).obj N, i ⁻¹ᵁ U) from
        ((pullbackPushforwardAdjunction i).unit.app N).val.app (op U) n) := by
  let r := ((SheafOfModulesOfCommRing.tensorRightUnitIso D.sheaf).app
    ((pullback i).obj N)).hom.val.app (op (i ⁻¹ᵁ U))
  have hp := projectionFormulaMap_section i N (SheafOfModules.unit D.ringCatSheaf) U n a
  have hu := tensorRightUnitIso_hom_section D ((pullback i).obj N) (i ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction i).unit.app N).val.app (op U) n) a
  exact (congrArg (fun z => r z) hp).trans hu

/-- The quotient tensor map is exactly the original geometric quotient unit. -/
public theorem closedImmersionTensorQuotientIso_unit {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : X.Modules) :
    (moduleTensorLeftFunctor X N).map (structureModuleMap i) ≫
        (closedImmersionTensorQuotientIso i N).hom =
      ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app N).hom ≫
        (pullbackPushforwardAdjunction i).unit.app N := by
  apply moduleTensor_hom_ext
  intro U n a
  let e := (closedImmersionTensorQuotientIso i N).hom.val.app (op U)
  let q := ((pullbackPushforwardAdjunction i).unit.app N).val.app (op U)
  have hm := moduleTensorLeftFunctor_map_section N (structureModuleMap i) U n a
  have he := closedImmersionTensorQuotientIso_section i N U n ((i.app U) a)
  have hs := q.hom.map_smul a n
  have hu := tensorRightUnitIso_hom_section X N U n a
  exact (congrArg (fun z => e z) hm).trans
    (he.trans (hs.symm.trans (congrArg (fun z => q z) hu.symm)))

/-- The original ideal multiplication followed by the original quotient unit is zero. -/
public theorem idealTensorQuotient_zero {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : X.Modules) :
    ((moduleTensorLeftFunctor X N).map (idealInclusion i) ≫
      ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app N).hom) ≫
        (pullbackPushforwardAdjunction i).unit.app N = 0 :=
  tensorQuotientZero (moduleTensorLeftFunctor X N) (idealInclusion i) (structureModuleMap i)
    (idealInclusion_structureMap i)
    ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app N)
    (closedImmersionTensorQuotientIso i N) ((pullbackPushforwardAdjunction i).unit.app N)
    (closedImmersionTensorQuotientIso_unit i N)

/-- Original coefficient ideal multiplication and the original quotient unit. -/
public def idealTensorQuotientSequence {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk
    ((moduleTensorLeftFunctor X N).map (idealInclusion i) ≫
      ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app N).hom)
    ((pullbackPushforwardAdjunction i).unit.app N)
    (idealTensorQuotient_zero i N)

/-- The original coefficient quotient row is the tensor of the actual ideal row. -/
public def idealTensorQuotientSequenceIso {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : X.Modules) :
    (idealSequence i).map (moduleTensorLeftFunctor X N) ≅
      idealTensorQuotientSequence i N :=
  ShortComplex.isoMk (Iso.refl _)
    ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app N)
    (closedImmersionTensorQuotientIso i N)
    (by
      exact Category.id_comp
        ((moduleTensorLeftFunctor X N).map (idealInclusion i) ≫
          ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app N).hom))
    (closedImmersionTensorQuotientIso_unit i N).symm

/-- The actual coefficient quotient is right exact for every module-sheaf coefficient. -/
public theorem idealTensorQuotientSequence_exact {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (N : X.Modules) :
    (idealTensorQuotientSequence i N).Exact :=
  ShortComplex.exact_of_iso (idealTensorQuotientSequenceIso i N)
    (moduleTensorLeft_rightExact X N (idealSequence i) (idealSequence_shortExact i)).1

/-- The actual Cartier section is killed by the original quotient of the twisted coefficient. -/
public theorem cartierCoefficientSequence_zero {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) :
    (cartierTensorSection i).app M ≫
      (pullbackPushforwardAdjunction i).unit.app
        (tensorSheaf X (dualSheaf X (idealModule i)) M) = 0 := by
  let S := idealTensorQuotientSequence i (tensorSheaf X (dualSheaf X (idealModule i)) M)
  let c₀ := cartierCoefficientCancellationIso i hI M
  let c : S.X₁ ≅ M := ⟨c₀.hom, c₀.inv, c₀.hom_inv_id, c₀.inv_hom_id⟩
  let τ : M ⟶ S.X₂ := (cartierTensorSection i).app M
  exact tensorCancellationZero c τ S.f S.g
    (cartierCoefficientCancellationIso_section i hI M)
    (idealTensorQuotient_zero i (tensorSheaf X (dualSheaf X (idealModule i)) M))

/-- The canonical Cartier section and the original twisted pullback/pushforward quotient unit. -/
public def cartierCoefficientSequence {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) :
    ShortComplex X.Modules :=
  ShortComplex.mk ((cartierTensorSection i).app M)
    ((pullbackPushforwardAdjunction i).unit.app
      (tensorSheaf X (dualSheaf X (idealModule i)) M))
    (cartierCoefficientSequence_zero i hI M)

/-- The actual Cartier row is transported only by the specified dual-evaluation cancellation. -/
public def cartierCoefficientSequenceIso {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) :
    idealTensorQuotientSequence i (tensorSheaf X (dualSheaf X (idealModule i)) M) ≅
      cartierCoefficientSequence i hI M :=
  ShortComplex.isoMk (cartierCoefficientCancellationIso i hI M) (Iso.refl _) (Iso.refl _)
    (by
      exact (cartierCoefficientCancellationIso_section i hI M).trans
        (Category.comp_id
          (idealTensorQuotientSequence i (tensorSheaf X (dualSheaf X (idealModule i)) M)).f).symm)
    (by
      exact (Category.id_comp
        ((pullbackPushforwardAdjunction i).unit.app
          (tensorSheaf X (dualSheaf X (idealModule i)) M))).trans (Category.comp_id _).symm)

/-- Exactness of the original global Cartier row is derived from the original ideal quotient. -/
public theorem cartierCoefficientSequence_exact {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) :
    (cartierCoefficientSequence i hI M).Exact :=
  ShortComplex.exact_of_iso (cartierCoefficientSequenceIso i hI M)
    (idealTensorQuotientSequence_exact i (tensorSheaf X (dualSheaf X (idealModule i)) M))

/-- Genuine coefficient regularity makes the original global Cartier row short exact. -/
public theorem cartierCoefficientSequence_shortExact {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules)
    [Mono ((cartierTensorSection i).app M)] :
    (cartierCoefficientSequence i hI M).ShortExact where
  exact := cartierCoefficientSequence_exact i hI M
  mono_f := inferInstanceAs (Mono ((cartierTensorSection i).app M))
  epi_g := pullbackPushforwardUnit_epi i (tensorSheaf X (dualSheaf X (idealModule i)) M)

end AlgebraicGeometry.Scheme.Modules
