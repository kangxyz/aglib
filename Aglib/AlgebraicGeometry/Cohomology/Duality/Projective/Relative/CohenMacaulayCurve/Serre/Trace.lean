/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Transport

/-!
# Original structural-one and trace normalization
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent RelativeCanonicalReindex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveAnchorModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k]

/-- The actual affine section endomorphism, normalized by the original
structural section isomorphism. -/
def cmCurveSerreAffineUnitEnd
    (h : (cmCurveSerreUnit (Spec (.of k)) : (Spec (.of k)).Modules) ⟶
      cmCurveSerreUnit (Spec (.of k))) :
    ModuleCat.of k k ⟶ ModuleCat.of k k :=
  (moduleAffineStructureSectionsIso (.of k)).inv ≫
    (moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom).map h ≫
      (moduleAffineStructureSectionsIso (.of k)).hom

/-- Its value at `1` is original unit-module evaluation followed by ΓSpec. -/
theorem cmCurveSerreAffineUnitEnd_apply_one
    (h : (cmCurveSerreUnit (Spec (.of k)) : (Spec (.of k)).Modules) ⟶
      cmCurveSerreUnit (Spec (.of k))) :
    cmCurveSerreAffineUnitEnd k h 1 =
      (Scheme.ΓSpecIso (.of k)).hom
        (unitHomGlobalSectionsEquiv (Spec (.of k))
          (cmCurveSerreUnit (Spec (.of k))) h) := by
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let G := moduleGlobalSectionsFunctorOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom
  let E := moduleAffineStructureSectionsIso (.of k)
  let R := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have hE (x : G.obj O) : E.hom x = R (show Γ(Y, ⊤) from x) := by
    have hx := ConcreteCategory.congr_hom E.hom_inv_id x
    change R.symm (E.hom x) = (show Γ(Y, ⊤) from x) at hx
    exact (R.apply_symm_apply (E.hom x)).symm.trans (congrArg R hx)
  change E.hom (G.map h (E.inv (1 : k))) = _
  exact (hE _).trans (by
    change (Scheme.ΓSpecIso (.of k)).hom
      (Scheme.Modules.Hom.app h ⊤ ((Scheme.ΓSpecIso (.of k)).inv (1 : k))) =
      (Scheme.ΓSpecIso (.of k)).hom (Scheme.Modules.Hom.app h ⊤ (1 : Γ(Y, ⊤)))
    exact congrArg
      (fun z : Γ(Y, ⊤) => (Scheme.ΓSpecIso (.of k)).hom (Scheme.Modules.Hom.app h ⊤ z))
      ((Scheme.ΓSpecIso (.of k)).inv.hom.map_one))

/-- The actual affine target isomorphism intertwines the original single
endomorphism with its actual section map, by the native single-unit law. -/
theorem cmCurveSerreAffineTarget_end
    (h : (cmCurveSerreUnit (Spec (.of k)) : (Spec (.of k)).Modules) ⟶
      cmCurveSerreUnit (Spec (.of k))) :
    (affineDerivedStructureTargetIso (.of k)).inv ≫
        (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
          (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).map h) ≫
        (affineDerivedStructureTargetIso (.of k)).hom =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveSerreAffineUnitEnd k h) := by
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let G := moduleGlobalSectionsFunctorOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0
  let E := moduleAffineStructureSectionsIso (.of k)
  let η := G.rightDerivedSingleUnit O
  let : IsIso η := affineStructureUnit_isIso (.of k)
  let b := G.rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map h)
  have hn : S.map (G.map h) ≫ η = η ≫ b := G.rightDerivedSingleUnit_naturality h
  change (S.map E.inv ≫ η) ≫ b ≫ (inv η ≫ S.map E.hom) =
    S.map (E.inv ≫ G.map h ≫ E.hom)
  calc
    _ = S.map E.inv ≫ (η ≫ b) ≫ inv η ≫ S.map E.hom := by
      simp only [Category.assoc]
    _ = S.map E.inv ≫ (S.map (G.map h) ≫ η) ≫ inv η ≫ S.map E.hom :=
      congrArg (fun z => S.map E.inv ≫ z ≫ inv η ≫ S.map E.hom) hn.symm
    _ = S.map E.inv ≫ S.map (G.map h) ≫ S.map E.hom := by
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = _ := by simp only [Functor.map_comp]

variable (ι : Type u) {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

omit [IsClosedImmersion j] in
/-- The inverse native single equivalence in unit evaluation is exactly
the original fully faithful preimage. -/
theorem cmCurveSerreUnitEvaluationLinearMap_apply
    (φ : cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (cmCurveSerreUnit (Spec (.of k))))⟦(0 : ℤ)⟧) :
    cmCurveSerreUnitEvaluationLinearMap k ι j φ =
      (Scheme.ΓSpecIso (.of k)).hom
        (unitHomGlobalSectionsEquiv (Spec (.of k))
          (cmCurveSerreUnit (Spec (.of k)))
          ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).preimage
            (DerivedCategory.Plus.ι.map
                (moduleDerivedPushforwardUnit (Spec (.of k)) (j ≫ toSpec k ι)) ≫
              φ ≫ (shiftFunctorZero (DerivedCategory (Spec (.of k)).Modules) ℤ).hom.app
                ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
                  (cmCurveSerreUnit (Spec (.of k))))))) := by
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let := moduleCategoryLinearOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom
  let S := DerivedCategory.singleFunctor Y.Modules 0
  let X := cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C)
  let η : S.obj O ⟶ X := DerivedCategory.Plus.ι.map
    (moduleDerivedPushforwardUnit Y (j ≫ toSpec k ι))
  let U : (O ⟶ O) ≃ₗ[k] (moduleSpecΓFunctor (R := .of k)).obj O :=
    unitHomGlobalSectionsLinearEquivOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom O
  have h := (cmCurveUnitEvaluationPacket S O X η U
    (cmCurveSerreSpecUnitSectionsIso k).hom.hom).apply φ
  exact h.trans (cmCurveSerreSpecUnitSectionsIso_apply k _)

variable (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- The geometric unit evaluation and the installed UnitTrace base trace
are the same scalar for the same literal degree-`n` Serre input. -/
theorem cmCurveSerreUnitEvaluation_eq_base
    (s : chosenEmbeddingUnitTraceSource k j (toSpec k ι) n) :
    cmCurveSerreUnitEvaluationLinearMap k ι j
        (relativeClosedEmbeddingDegreeZeroSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
          (IsPullback.id_horiz (toSpec k ι)) n e
          (cmCurveSerreUnit (Spec (.of k)))
          (cmCurveSerreUnit C) s ≫
          (shiftFunctorZero (DerivedCategory (Spec (.of k)).Modules) ℤ).inv.app
            ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
              (cmCurveSerreUnit (Spec (.of k))))) =
      chosenEmbeddingTraceBase k ι j (toSpec k ι) (𝟙 _)
        (IsPullback.id_horiz (toSpec k ι)) n e s := by
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let SY := DerivedCategory.singleFunctor Y.Modules 0
  let SYp := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let SM := DerivedCategory.singleFunctor (ModuleCat.{u} k) 0
  let Mp := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let Yp := DerivedCategory.Plus.ι (C := Y.Modules)
  let p := j ≫ toSpec k ι
  let η := moduleDerivedPushforwardUnit Y p
  let Φ := chosenEmbeddingSerreMapPlus k ι j (toSpec k ι) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) n e s
  let f := η ≫ Φ
  let h : O ⟶ O := SY.preimage (Yp.map f)
  have hh : SY.map h = Yp.map f := SY.map_preimage _
  have hp : SYp.map h = f := by
    apply Yp.map_injective
    exact hh
  let hk := cmCurveSerreAffineUnitEnd k h
  have hg := chosenEmbeddingTraceBase_geometric_unit k ι j (toSpec k ι) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) n e s
  have hmod : moduleDerivedStructureUnit C (chosenEmbeddingBaseScalar k j (toSpec k ι)) ≫
      chosenEmbeddingModuleSerreMap k ι j (toSpec k ι) (𝟙 _)
        (IsPullback.id_horiz (toSpec k ι)) n e s =
        (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).map hk := by
    exact hg.trans ((congrArg (fun g =>
      (affineDerivedStructureTargetIso (.of k)).inv ≫
        (moduleGlobalSectionsFunctorOfHom Y (Scheme.ΓSpecIso (.of
          k)).inv.hom).rightDerivedFunctorPlus.map g ≫
        (affineDerivedStructureTargetIso (.of k)).hom) hp.symm).trans
      (cmCurveSerreAffineTarget_end k h))
  have hb : chosenEmbeddingTraceBase k ι j (toSpec k ι) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) n e s = hk 1 := by
    change (SM.preimage (Mp.map
      (moduleDerivedStructureUnit C (chosenEmbeddingBaseScalar k j (toSpec k ι)) ≫
        chosenEmbeddingModuleSerreMap k ι j (toSpec k ι) (𝟙 _)
          (IsPullback.id_horiz (toSpec k ι)) n e s))) 1 = hk 1
    exact congrArg (fun g : ModuleCat.of k k ⟶ ModuleCat.of k k => g 1)
      ((congrArg SM.preimage (congrArg Mp.map hmod)).trans (SM.preimage_map hk))
  let Ψ := relativeClosedEmbeddingDegreeZeroSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) n e O (cmCurveSerreUnit C) s
  let Z := (shiftFunctorZero (DerivedCategory Y.Modules) ℤ).app (SY.obj O)
  have hΦ : Yp.map Φ = Ψ := Yp.map_preimage _
  have hcancel : (Ψ ≫ Z.inv) ≫ Z.hom = Ψ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => Ψ ≫ z) Z.inv_hom_id).trans (Category.comp_id _))
  have hz : Yp.map η ≫ (Ψ ≫ Z.inv) ≫ Z.hom = Yp.map f :=
    (congrArg (fun z => Yp.map η ≫ z) hcancel).trans
      ((congrArg (fun z => Yp.map η ≫ z) hΦ.symm).trans (Yp.map_comp η Φ).symm)
  exact (cmCurveSerreUnitEvaluationLinearMap_apply k ι j (Ψ ≫ Z.inv)).trans
    ((congrArg (fun z => (Scheme.ΓSpecIso (.of k)).hom
      (unitHomGlobalSectionsEquiv Y O (SY.preimage z))) hz).trans
      ((cmCurveSerreAffineUnitEnd_apply_one k h).symm.trans hb.symm))

variable (hCM : ∀ x : C, IsClosed ({x} : Set C) →
    ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
      IsSMulRegular (C.presheaf.stalk x) b ∧
        (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))

/-- The degree-one Ext input is reindexed into the literal original
degree-`n` UnitTrace source by the same canonical reconstruction. -/
def cmCurveSerreDegreeOneInput
    (β : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules)
      (cmCurveCanonicalModule k ι j n) 1) :
    chosenEmbeddingUnitTraceSource k j (toSpec k ι) n := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  exact RelativeCanonicalReindex.purityInputLinearEquiv (S := k)
    (cmCurveSerreUnit C) (cmCurveCanonicalModule k ι j n)
    (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n)) ((n : ℤ) - 1)
    (cmCurveSerreCanonicalIso k ι j n e hCM) n 1 (by omega) β

/-- Degree-one purity transport retains the original natural degree
and native zero-shift output normalization. -/
theorem cmCurvePurityOneNormalization
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt.{w} A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    {S : Type*} [CommRing S] [Linear S A] [Linear S B]
    (M W : A) (K : DerivedCategory A) (D : DerivedCategory B) (N : B)
    (n q : ℕ) (hq : q = n) (hd : (q : ℤ) - 1 = (n : ℤ) - 1)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - 1)).obj W)
    (Φ : ∀ q : ℕ, ((DerivedCategory.singleFunctor A 0).obj M ⟶ K⟦(q : ℤ)⟧) →ₗ[S]
      (D ⟶ ((DerivedCategory.singleFunctor B n).obj N)⟦(q : ℤ)⟧))
    (β : Ext.{w} M W 1) :
    serreLinearMapOfPurity M W K D N n 1 q 1 hd E (Φ q) β ≫
        (shiftFunctorZero (DerivedCategory B) ℤ).hom.app
          ((DerivedCategory.singleFunctor B 0).obj N) =
      Φ n (purityInputLinearEquiv (S := S) M W K ((n : ℤ) - 1) E n 1 (by omega) β) ≫
        ((DerivedCategory.singleFunctors B).shiftIso (n : ℤ) 0 n (by omega)).hom.app N := by
  subst q
  have h := serreLinearMapOfPurity_apply M W K D N n 1 n 1 hd E (Φ n) β
  exact (congrArg (fun f => f ≫ (shiftFunctorZero (DerivedCategory B) ℤ).hom.app
    ((DerivedCategory.singleFunctor B 0).obj N)) h).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f => Φ n (purityInputLinearEquiv (S := S)
          M W K ((n : ℤ) - 1) E n 1 (by omega) β) ≫ f)
            (cmCurveSingleReindexTrace N (n : ℤ))))

/-- Degree one has exactly the installed original UnitTrace target after
the native zero-shift isomorphism. -/
theorem cmCurveSerreDerivedLinearMap_one_normalization (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules)
      (cmCurveCanonicalModule k ι j n) 1) :
    cmCurveSerreDerivedLinearMap k ι j n e hCM (cmCurveSerreUnit C) 1 hn β ≫
        (shiftFunctorZero (DerivedCategory (Spec (.of k)).Modules) ℤ).hom.app
          ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
            (cmCurveSerreUnit (Spec (.of k)))) =
      relativeClosedEmbeddingDegreeZeroSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
        (IsPullback.id_horiz (toSpec k ι)) n e
        (cmCurveSerreUnit (Spec (.of k)))
        (cmCurveSerreUnit C) (cmCurveSerreDegreeOneInput k ι j n e hCM β) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  exact cmCurvePurityOneNormalization (S := k)
    (cmCurveSerreUnit C) (cmCurveCanonicalModule k ι j n)
    (DerivedCategory.Plus.ι.obj (cmCurveDualizingObject k ι j n))
    (cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C))
    (cmCurveSerreUnit (Spec (.of k))) n (1 + (n - 1)) (by omega) (by omega)
    (cmCurveSerreCanonicalIso k ι j n e hCM)
    (fun q => relativeClosedEmbeddingSerreLinearMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) (Scheme.ΓSpecIso (.of k)).inv.hom
      n e (cmCurveSerreUnit (Spec (.of k))) (cmCurveSerreUnit C) q) β

/-- The already constructed linear trace is the original UnitTrace base
trace on the same degree-one canonical input. -/
theorem cmCurveSerreTrace_ext_eq_base (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules)
      (cmCurveCanonicalModule k ι j n) 1) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCanonicalModule k ι j n) 1
    cmCurveSerreTrace k ι j n e hCM hn
        (moduleExtCohomologyMap C (cmCurveCanonicalModule k ι j n) 1 β) =
      chosenEmbeddingTraceBase k ι j (toSpec k ι) (𝟙 _)
        (IsPullback.id_horiz (toSpec k ι)) n e
        (cmCurveSerreDegreeOneInput k ι j n e hCM β) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCanonicalModule k ι j n) 1
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let Z := (shiftFunctorZero (DerivedCategory (Spec (.of k)).Modules) ℤ).app
    ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj O)
  let Φ := relativeClosedEmbeddingDegreeZeroSerreMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) n e O (cmCurveSerreUnit C)
    (cmCurveSerreDegreeOneInput k ι j n e hCM β)
  have hΦ := Functor.cmCurveOutputIsoInverse Z
    (cmCurveSerreDerivedLinearMap k ι j n e hCM (cmCurveSerreUnit C) 1 hn β) Φ
    (cmCurveSerreDerivedLinearMap_one_normalization k ι j n e hCM hn β)
  exact (cmCurveSerreTrace_apply_ext k ι j n e hCM hn β).trans
    ((congrArg (cmCurveSerreUnitEvaluationLinearMap k ι j) hΦ).trans
      (cmCurveSerreUnitEvaluation_eq_base k ι j n e
        (cmCurveSerreDegreeOneInput k ι j n e hCM β)))

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveOriginalClassDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

omit [IsClosedImmersion j] in
/-- The original structural section map at one is the section of the
original identity morphism of the structure module. -/
theorem cmCurveSerreStructuralSection_id :
    let O : C.Modules := cmCurveSerreUnit C
    (moduleStructuralSectionsMap C (cmCurveSerreScalar k ι j)) (1 : k) =
      unitHomGlobalSectionsEquiv C O (𝟙 O) := by
  let O : C.Modules := cmCurveSerreUnit C
  change (cmCurveSerreScalar k ι j) 1 =
    Scheme.Modules.Hom.app (𝟙 O) ⊤ (1 : Γ(C, ⊤))
  have h := congrArg (fun f => f (1 : Γ(C, ⊤)))
    (Scheme.Modules.Hom.id_app O (U := ⊤))
  exact (cmCurveSerreScalar k ι j).map_one.trans
    ((h.trans (by rfl)).symm)

omit [IsClosedImmersion j] in
/-- The actual native unit homology equation, on its original section carrier. -/
theorem cmCurveSerreDerivedUnit_native :
    let α := cmCurveSerreScalar k ι j
    let O : C.Modules := cmCurveSerreUnit C
    let G := moduleGlobalSectionsFunctorOfHom C α
    let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) 0
    H.map (moduleDerivedStructureUnit C α)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).inv.app
          (ModuleCat.of k k) (1 : k)) =
      G.rightDerivedSingleHomologyZeroIso.inv.app O
        (moduleStructuralSectionsMap C α (1 : k)) := by
  dsimp only
  let α := cmCurveSerreScalar k ι j
  let O : C.Modules := cmCurveSerreUnit C
  let G := moduleGlobalSectionsFunctorOfHom C α
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) 0
  let E₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} k) 0).app (ModuleCat.of k k)
  have h := cmCurveUnitHomologyInverse E₀ (G.rightDerivedSingleHomologyZeroIso.app O)
    (H.map (moduleDerivedStructureUnit C α)) (moduleStructuralSectionsMap C α)
    (moduleDerivedStructureUnit_homology C α)
  exact congrArg (fun f : ModuleCat.of k k ⟶ _ => f (1 : k)) h

omit [IsClosedImmersion j] in
/-- The literal structural module unit represents the original section
one under the native degree-zero homology comparison. -/
theorem cmCurveSerreDerivedUnit_one :
    let α := cmCurveSerreScalar k ι j
    let O : C.Modules := cmCurveSerreUnit C
    let G := moduleGlobalSectionsFunctorOfHom C α
    let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) 0
    H.map (moduleDerivedStructureUnit C α)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).inv.app
          (ModuleCat.of k k) (1 : k)) =
      G.rightDerivedSingleHomologyZeroIso.inv.app O (1 : Γ(C, ⊤)) := by
  dsimp only
  let α := cmCurveSerreScalar k ι j
  let O : C.Modules := cmCurveSerreUnit C
  let G := moduleGlobalSectionsFunctorOfHom C α
  have hs : moduleStructuralSectionsMap C α (1 : k) =
      (show G.obj O from (1 : Γ(C, ⊤))) := α.map_one
  exact (cmCurveSerreDerivedUnit_native k ι j).trans
    (congrArg (G.rightDerivedSingleHomologyZeroIso.inv.app O) hs)

omit [IsClosedImmersion j] in
/-- Acting on the original structural section one by an Ext class in
curve degree zero or one gives its original Ext/cohomology class. -/
theorem cmCurveSerreDerivedClass (F : C.Modules) (i : ℕ) (hi : i ≤ 1)
    (a : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules) F i) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
    let G := moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)
    let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) 0
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) i
    E (H.shiftMap (a.homPlus.map G.rightDerivedFunctorPlus) 0 (i : ℤ) (by omega)
      (H.map (moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).inv.app
          (ModuleCat.of k k) (1 : k)))) = moduleExtCohomologyMap C F i a := by
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  dsimp only
  let O : C.Modules := cmCurveSerreUnit C
  let α := cmCurveSerreScalar k ι j
  let G := moduleGlobalSectionsFunctorOfHom C α
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) 0
  let s₀ : G.obj O := moduleStructuralSectionsMap C α (1 : k)
  let z₀ := G.rightDerivedSingleHomologyZeroIso.inv.app O s₀
  have hU := cmCurveSerreDerivedUnit_native k ι j
  have hsource := congrArg (fun z =>
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C α (injectiveResolution F) i
      (H.shiftMap (a.homPlus.map G.rightDerivedFunctorPlus) 0 (i : ℤ) (by omega) z)) hU
  refine hsource.trans ?_
  interval_cases i
  · obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective O F).surjective a
    let m := G.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor C.Modules 0).map f)
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C α
      (injectiveResolution F) 0
    let Z := G.rightDerivedSingleHomologyZeroIso
    have hm : (Ext.mk₀ f).homPlus.map G.rightDerivedFunctorPlus =
        ShiftedHom.mk₀ (0 : ℤ) rfl m :=
      (congrArg (fun z => ShiftedHom.map z G.rightDerivedFunctorPlus)
        (Ext.homPlus_mk₀ f)).trans
          (ShiftedHom.map_mk₀ (0 : ℤ) rfl _ G.rightDerivedFunctorPlus)
    have hf : H.shiftMap ((Ext.mk₀ f).homPlus.map G.rightDerivedFunctorPlus) 0 0 (by omega) =
        H.map m := (congrArg (fun z => H.shiftMap z 0 0 (by omega)) hm).trans
      (DerivedCategory.Plus.cmCurve_homology_shiftMap_mk₀ m)
    have hnat : Z.hom.app F (H.map m z₀) = G.map f (Z.hom.app O z₀) :=
      congrArg (fun q => q z₀) (Z.hom.naturality f)
    have hzero : Z.hom.app O z₀ = s₀ :=
      congrArg (fun q => q s₀) (Z.inv_hom_id_app O)
    have hs : G.map f s₀ = unitHomGlobalSectionsEquiv C F f := by
      change Scheme.Modules.Hom.app f ⊤ (α 1) =
        Scheme.Modules.Hom.app f ⊤ (1 : Γ(C, ⊤))
      exact congrArg (Scheme.Modules.Hom.app f ⊤) α.map_one
    apply (moduleH0EquivOfHom C α F).injective
    have h₁ := moduleDerivedGlobalSections_homology_zero_sections C α F (injectiveResolution F)
      (H.shiftMap ((Ext.mk₀ f).homPlus.map G.rightDerivedFunctorPlus) 0 0 (by omega) z₀)
    have h₂ := congrArg (Z.hom.app F) (congrArg (fun q => q z₀) hf)
    have h₃ := hnat.trans (congrArg (G.map f) hzero)
    have hsections : moduleH0EquivOfHom C α F
        (moduleExtCohomologyMap C F 0 (Ext.mk₀ f)) =
        unitHomGlobalSectionsEquiv C F f :=
      moduleExtCohomologyMap_mk₀_sections C F f
    exact h₁.trans (h₂.trans (h₃.trans (hs.trans hsections.symm)))
  · have h := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_extAction C α
      (injectiveResolution F) a s₀
    dsimp only at h
    have hg : (unitHomGlobalSectionsEquiv C O).symm s₀ = 𝟙 O :=
      (unitHomGlobalSectionsEquiv C O).symm_apply_eq.mpr
        (cmCurveSerreStructuralSection_id k ι j)
    have hcomp := congrArg (fun f : O ⟶ O => moduleExtCohomologyMap C F 1
      ((Ext.mk₀ f).comp a (Nat.zero_add 1))) hg
    exact h.trans (hcomp.trans
      (congrArg (moduleExtCohomologyMap C F 1) (Ext.mk₀_id_comp a)))

omit [IsClosedImmersion j] in
/-- Original Ext classes act on the original derived structural section
one to give their original cohomology classes, also in the full model. -/
theorem cmCurveSerreDerivedClass_full (F : C.Modules) (i : ℕ) (hi : i ≤ 1)
    (a : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules) F i) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
    let G := moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) i
    E.symm (moduleExtCohomologyMap C F i a) =
      H.shiftMap (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι))
        0 (i : ℤ) (by omega)
        (H.map (DerivedCategory.Plus.ι.map
          (moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j)))
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).inv.app
            (ModuleCat.of k k) (1 : k))) := by
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  dsimp only
  let G := moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)
  let HP := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
    (cmCurveSerreScalar k ι j) (injectiveResolution F) i
  let u := moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j)
  let z := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).inv.app
    (ModuleCat.of k k) (1 : k)
  have h := cmCurveSerreDerivedClass k ι j F i hi a
  dsimp only at h
  have hshift := DerivedCategory.Plus.cmCurveHomology_shiftMap_full
    (a.homPlus.map G.rightDerivedFunctorPlus) (show (i : ℤ) + 0 = (i : ℤ) by omega)
  have hmap := congrArg (fun f => H.shiftMap f 0 (i : ℤ) (by omega))
    (ShiftedHom.comp_map a.homPlus G.rightDerivedFunctorPlus DerivedCategory.Plus.ι).symm
  have hunit := congrArg (fun f => f z)
    (DerivedCategory.Plus.cmCurve_homology_map_full u 0)
  have hvalue := congrArg (fun f => f (HP.map u z)) (hshift.trans hmap)
  have hpoint := hvalue.trans
    (congrArg (H.shiftMap
      (a.homPlus.map (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι))
      0 (i : ℤ) (by omega)) hunit)
  apply E.injective
  exact (E.apply_symm_apply _).trans (h.symm.trans (congrArg E hpoint))

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveModuleTraceDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))

/-- In curve degree one the module model is the literal original
UnitTrace module arrow, padded only by the native zero shift. -/
theorem cmCurveSerreModuleHom_one (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules)
      (cmCurveCanonicalModule k ι j n) 1) :
    cmCurveSerreModuleHom k ι j (cmCurveSerreUnit C) 0
        (cmCurveSerreDerivedLinearMap k ι j n e hCM
          (cmCurveSerreUnit C) 1 hn β) =
      ShiftedHom.mk₀ (0 : ℤ) rfl
        (DerivedCategory.Plus.ι.map
          (chosenEmbeddingModuleSerreMap k ι j (toSpec k ι) (𝟙 _)
            (IsPullback.id_horiz (toSpec k ι)) n e
            (cmCurveSerreDegreeOneInput k ι j n e hCM β))) := by
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let O : (Spec (.of k)).Modules := cmCurveSerreUnit (Spec (.of k))
  let OC : C.Modules := cmCurveSerreUnit C
  let f : (derivedPushforwardPlus (j ≫ toSpec k ι)).obj
        ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj OC) ⟶
      (DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O :=
    chosenEmbeddingSerreMapPlus k ι j (toSpec k ι) (𝟙 _)
      (IsPullback.id_horiz (toSpec k ι)) n e (cmCurveSerreDegreeOneInput k ι j n e hCM β)
  have hf : IY.map f = relativeClosedEmbeddingDegreeZeroSerreMap j (toSpec k ι) k ι
      (𝟙 _) (𝟙 _) (IsPullback.id_horiz (toSpec k ι)) n e O OC
      (cmCurveSerreDegreeOneInput k ι j n e hCM β) := IY.map_preimage _
  have hβ : cmCurveSerreDerivedLinearMap k ι j n e hCM OC 1 hn β =
      ShiftedHom.mk₀ (0 : ℤ) rfl (IY.map f) :=
    Functor.cmCurveEqMk₀_of_postZero
      (cmCurveSerreDerivedLinearMap k ι j n e hCM OC 1 hn β) (IY.map f)
      ((cmCurveSerreDerivedLinearMap_one_normalization k ι j n e hCM hn β).trans hf.symm)
  have hmodel := cmCurveSerreModuleHom_mk₀ k ι j OC f
  exact (congrArg (cmCurveSerreModuleHom k ι j OC 0) hβ).trans hmodel

/-- Evaluation of the module-valued native degree-one arrow on the
original structural section one is the same already installed curve
trace. -/
theorem cmCurveSerreModuleHom_one_trace (hn : 1 ≤ n)
    (β : Ext.{u + 1} (C := C.Modules) (cmCurveSerreUnit C : C.Modules)
      (cmCurveCanonicalModule k ι j n) 1) :
    let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
      (cmCurveCanonicalModule k ι j n) 1
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
    let E := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
      (ModuleCat.of k k)
    let u := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j))
    (H.shiftMap (cmCurveSerreModuleHom k ι j (cmCurveSerreUnit C) 0
        (cmCurveSerreDerivedLinearMap k ι j n e hCM
          (cmCurveSerreUnit C) 1 hn β)) 0 0 (by omega) ≫ E.hom)
      (H.map u (E.inv (1 : k))) =
      cmCurveSerreTrace k ι j n e hCM hn
        (moduleExtCohomologyMap C (cmCurveCanonicalModule k ι j n) 1 β) := by
  let := moduleCategoryLinearOfHom C (cmCurveSerreScalar k ι j)
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j)
    (cmCurveCanonicalModule k ι j n) 1
  dsimp only
  let E := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
    (ModuleCat.of k k)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let I := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let O : C.Modules := cmCurveSerreUnit C
  let u := moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j)
  let s := cmCurveSerreDegreeOneInput k ι j n e hCM β
  let Φ := chosenEmbeddingModuleSerreMap k ι j (toSpec k ι) (𝟙 _)
    (IsPullback.id_horiz (toSpec k ι)) n e s
  let χ := cmCurveSerreModuleHom k ι j O 0
    (cmCurveSerreDerivedLinearMap k ι j n e hCM O 1 hn β)
  let v := H.map (I.map u)
  let w := H.map (I.map Φ)
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} k) 0
  let σ := (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} k) 0).app
    (ModuleCat.of k k)
  let f : S.obj (ModuleCat.of k k) ⟶ S.obj (ModuleCat.of k k) :=
    σ.inv ≫ I.map (u ≫ Φ) ≫ σ.hom
  have hf : f = I.map (u ≫ Φ) :=
    (Category.id_comp (I.map (u ≫ Φ) ≫ 𝟙 _)).trans
      (Category.comp_id (I.map (u ≫ Φ)))
  have hχ : χ = ShiftedHom.mk₀ (0 : ℤ) rfl (I.map Φ) :=
    cmCurveSerreModuleHom_one k ι j n e hCM hn β
  have hH : H.shiftMap χ 0 0 (by omega) = w :=
    (congrArg (fun q => H.shiftMap q 0 0 (by omega)) hχ).trans
      (DerivedCategory.cmCurve_homology_shiftMap_mk₀ (I.map Φ))
  have hfunctor : H.map f = v ≫ w :=
    (congrArg H.map hf).trans
      ((congrArg H.map (I.map_comp u Φ)).trans (H.map_comp (I.map u) (I.map Φ)))
  have hpre := DerivedCategory.cmCurveSinglePreimage_homology
    (A := ModuleCat.{u} k) (M := ModuleCat.of k k) (N := ModuleCat.of k k) 0 f
  have hchain : E.inv ≫ v ≫ w ≫ E.hom =
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).preimage f :=
    (congrArg (fun q => E.inv ≫ q) (Category.assoc v w E.hom).symm).trans
      ((congrArg (fun q => E.inv ≫ q ≫ E.hom) hfunctor.symm).trans hpre)
  have hvalue := congrArg (fun q : ModuleCat.of k k ⟶ ModuleCat.of k k => q (1 : k)) hchain
  have hraw := congrArg (fun q => (S.preimage q) (1 : k)) hf
  have htrace := cmCurveSerreTrace_ext_eq_base k ι j n e hCM hn β
  have hleft := congrArg
    (fun q => (q ≫ E.hom) (v (E.inv (1 : k)))) hH
  exact hleft.trans (hvalue.trans (hraw.trans htrace.symm))

end AlgebraicGeometry.Scheme.Cohomology
