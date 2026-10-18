/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Conormal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenCoefficient
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.Class
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.AmbientIsomorphism.Classes
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction.Counit

/-!
# The original fixed coefficient class on an ambient open

The original inverse coefficient frame is the pullback of its unit section.
The native affine restriction comparison and its original adjunction unit
identify the transported frame. The actual mixed pullback/open square thus
preserves coefficient class one on every open, without regularity assumptions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem scalarSelfIso_hom_one_tmul {A B : CommRingCat.{u}} [Algebra A B] (x : A) :
    (ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A A) ≪≫
      (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso).hom
        ((1 : B) ⊗ₜ[A,algebraMap A B] x) = algebraMap A B x := by
  change (TensorProduct.AlgebraTensorModule.rid A B B)
    ((ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A A)).hom
      ((1 : B) ⊗ₜ[A,algebraMap A B] x)) = algebraMap A B x
  rw [ModuleCat.extendScalarsAlgebraObjIso_hom_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]

/-- The original native scalar-extension self-unit, formed before specializing rings. -/
def regularListOpenScalarUnitIso {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of A A) ≅ ModuleCat.of B B := by
  letI := φ.hom.toAlgebra
  exact ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso

/-- The same native self-unit keeps every original unit tensor. -/
theorem regularListOpenScalarUnitIso_hom_one_tmul {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (x : A) :
    (regularListOpenScalarUnitIso φ).hom ((1 : B) ⊗ₜ[A,φ.hom] x) = φ.hom x := by
  let := φ.hom.toAlgebra
  exact scalarSelfIso_hom_one_tmul (A := A) (B := B) x

/-- The same original scalar-extension coefficient frame for an arbitrary ambient map. -/
def regularListOpenCoefficientFrame {A A' : CommRingCat.{u}} (φ : A ⟶ A')
    {E : ModuleCat.{u} A} {E' : ModuleCat.{u} A'}
    (e : E ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars φ.hom).obj E ≅ E') :
    E' ≅ ModuleCat.of A' A' :=
  θ.symm ≪≫ (ModuleCat.extendScalars φ.hom).mapIso e ≪≫ regularListOpenScalarUnitIso φ

private theorem regularListOpenCoefficientFrame_original {A A' : CommRingCat.{u}}
    (φ : A ⟶ A') {E : ModuleCat.{u} A} {E' : ModuleCat.{u} A'}
    (e : E ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars φ.hom).obj E ≅ E') :
    regularListOpenCoefficientFrame φ e θ =
      (by
        letI := φ.hom.toAlgebra
        exact θ.symm ≪≫ (ModuleCat.extendScalars φ.hom).mapIso e ≪≫
          ModuleCat.extendScalarsAlgebraObjIso A A' (ModuleCat.of A A) ≪≫
            (TensorProduct.AlgebraTensorModule.rid A A' A').toModuleIso) := by
  rfl

/-- The transported frame retains the original unit tensor of the chosen generator. -/
theorem regularListOpenCoefficientFrame_inv_one {A A' : CommRingCat.{u}} (φ : A ⟶ A')
    {E : ModuleCat.{u} A} {E' : ModuleCat.{u} A'}
    (e : E ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars φ.hom).obj E ≅ E') :
    (regularListOpenCoefficientFrame φ e θ).inv (1 : A') =
      θ.hom ((1 : A') ⊗ₜ[A,φ.hom] e.inv (1 : A)) := by
  let := φ.hom.toAlgebra
  let F := ModuleCat.extendScalars φ.hom
  let ε := ModuleCat.extendScalarsAlgebraObjIso A A' (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A A' A').toModuleIso
  let e' := regularListOpenCoefficientFrame φ e θ
  have hε : ε.hom ≫ e'.inv = F.map e.inv ≫ θ.hom := by
    change ε.hom ≫ (ε.inv ≫ F.map e.inv ≫ θ.hom) = _
    rw [Iso.hom_inv_id_assoc]
  have hεone : ε.hom ((1 : A') ⊗ₜ[A,φ.hom] (1 : A)) = (1 : A') := by
    change (TensorProduct.AlgebraTensorModule.rid A A' A')
      ((ModuleCat.extendScalarsAlgebraObjIso A A' (ModuleCat.of A A)).hom
        ((1 : A') ⊗ₜ[A,φ.hom] (1 : A))) = (1 : A')
    erw [ModuleCat.extendScalarsAlgebraObjIso_hom_tmul]
    exact one_smul A (1 : A')
  have h := ConcreteCategory.congr_hom hε ((1 : A') ⊗ₜ[A,φ.hom] (1 : A))
  change e'.inv (ε.hom ((1 : A') ⊗ₜ[A,φ.hom] (1 : A))) =
    θ.hom (F.map e.inv ((1 : A') ⊗ₜ[A,φ.hom] (1 : A))) at h
  rw [hεone] at h
  exact h

/-- The generic frame is the same original principal-open frame. The native
self-unit maps are compared on their original unit tensors. -/
theorem regularListOpenCoefficientFrame_principal {A : CommRingCat.{u}} (r : A)
    {E : ModuleCat.{u} A} {E' : ModuleCat.{u} (Localization.Away r)}
    (e : E ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars (algebraMap A (Localization.Away r))).obj E ≅ E') :
    regularListOpenCoefficientFrame
        (CommRingCat.ofHom (algebraMap A (Localization.Away r))) e θ =
      regularListPrincipalCoefficientFrame r e θ := by
  let S : CommRingCat.{u} := .of (Localization.Away r)
  let φ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
  let F := ModuleCat.extendScalars φ.hom
  let ε₀ : F.obj (ModuleCat.of A A) ≅ ModuleCat.of S S := regularListOpenScalarUnitIso φ
  let ε₁ : F.obj (ModuleCat.of A A) ≅ ModuleCat.of S S :=
    ModuleCat.extendScalarsAlgebraObjIso A S (ModuleCat.of A A) ≪≫
      (TensorProduct.AlgebraTensorModule.rid A S S).toModuleIso
  have hε : ε₀ = ε₁ := by
    apply Iso.ext
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    have h₀ : ε₀.hom ((1 : S) ⊗ₜ[A,φ.hom] x) = φ.hom x :=
      regularListOpenScalarUnitIso_hom_one_tmul φ x
    have h₁ : ε₁.hom ((1 : S) ⊗ₜ[A,φ.hom] x) = φ.hom x :=
      scalarSelfIso_hom_one_tmul (A := A) (B := S) x
    exact h₀.trans h₁.symm
  change θ.symm ≪≫ F.mapIso e ≪≫ ε₀ = θ.symm ≪≫ F.mapIso e ≪≫ ε₁
  rw [hε]

/-- The generic frame is literally the original ambient-isomorphism frame. -/
theorem regularListOpenCoefficientFrame_ambient {A A' : CommRingCat.{u}} (a : A ≃+* A')
    {E : ModuleCat.{u} A} {E' : ModuleCat.{u} A'}
    (e : E ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars a.toRingHom).obj E ≅ E') :
    regularListOpenCoefficientFrame a.toCommRingCatIso.hom e θ =
      regularListAmbientCoefficientFrame a e θ := by
  rfl

private theorem affineUnitSection_map {A : CommRingCat.{u}}
    {E F : ModuleCat.{u} A} (f : E ⟶ F) (x : E) :
    canonicalAffineUnitSection E x ≫ (tilde.functor A).map f =
      canonicalAffineUnitSection F (f x) := by
  apply (unitHomGlobalSectionsEquiv (Spec A) (tilde F)).injective
  change ((tilde.functor A).map f).val.app (op ⊤)
    ((canonicalAffineUnitSection E x).val.app (op ⊤) (1 : Γ(Spec A, ⊤))) =
      (canonicalAffineUnitSection F (f x)).val.app (op ⊤) (1 : Γ(Spec A, ⊤))
  rw [canonicalAffineUnitSection_app, canonicalAffineUnitSection_app]
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) x

private theorem affineUnitSection_one (A : CommRingCat.{u}) :
    canonicalAffineUnitSection (ModuleCat.of A A) (1 : A) =
      (tildeSelf (R := A)).inv := by
  apply (unitHomGlobalSectionsEquiv (Spec A) (tilde (ModuleCat.of A A))).injective
  change (canonicalAffineUnitSection (ModuleCat.of A A) (1 : A)).val.app (op ⊤)
    (1 : Γ(Spec A, ⊤)) = (1 : Γ(Spec A, ⊤))
  rw [canonicalAffineUnitSection_app, tilde_toOpen_self_one]

private def coefficientUnitSection {A : CommRingCat.{u}} (L : (Spec A).Modules)
    (x : moduleSpecΓFunctor.obj L) : SheafOfModules.unit (Spec A).ringCatSheaf ⟶ L :=
  canonicalAffineUnitSection (moduleSpecΓFunctor.obj L) x ≫ L.fromTildeΓ

private theorem coefficientUnitSection_pullback {A : CommRingCat.{u}} (s : List A)
    {L : (Spec A).Modules} [L.IsQuasicoherent]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) :
    (pullbackUnitIso (Spec.map (regularListQuotientMap s))).inv ≫
        (pullback (Spec.map (regularListQuotientMap s))).map
          (coefficientUnitSection L (e.inv (1 : A))) =
      (closedImmersionRegularListCoefficientFrameIso s e).inv := by
  let B := regularListQuotientRing s
  let q := regularListQuotientMap s
  let E := moduleSpecΓFunctor.obj L
  let P := pullback (Spec.map q)
  let T := tilde.functor B
  let F := ModuleCat.extendScalars q.hom
  let c := asIso L.fromTildeΓ
  let ε := ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
  let D := F.mapIso e ≪≫ ε
  let v := canonicalAffineUnitSection E (e.inv (1 : A))
  let x : F.obj E := (1 : B) ⊗ₜ[A,q.hom] e.inv (1 : A)
  have hx : D.hom x = (1 : B) := by
    change (TensorProduct.AlgebraTensorModule.rid A B B)
      ((ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A A)).hom
        (F.map e.hom ((1 : B) ⊗ₜ[A,q.hom] e.inv (1 : A)))) = (1 : B)
    rw [ModuleCat.ExtendScalars.map_tmul, Iso.inv_hom_id_apply,
      ModuleCat.extendScalarsAlgebraObjIso_hom_tmul,
      TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]
  have hD := affineUnitSection_map D.hom x
  rw [hx, affineUnitSection_one] at hD
  have hp := canonicalAffineUnitSection_pullback q E (e.inv (1 : A))
  have hc : P.map c.hom ≫ P.map c.inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  apply (cancel_mono (closedImmersionRegularListCoefficientFrameIso s e).hom).mp
  rw [Iso.inv_hom_id]
  change (pullbackUnitIso (Spec.map q)).inv ≫ P.map (v ≫ c.hom) ≫
      P.map c.inv ≫ (tildePullbackIso q).hom.app E ≫ T.map D.hom ≫
        (tildeSelf (R := B)).hom = 𝟙 _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (P.map c.hom) (P.map c.inv), hc, Category.id_comp]
  have hp' := congrArg (fun k => k ≫ T.map D.hom ≫ (tildeSelf (R := B)).hom) hp
  have hD' := congrArg (fun k => k ≫ (tildeSelf (R := B)).hom) hD
  simp only [Category.assoc] at hp' hD'
  simpa only [Iso.inv_hom_id] using hp'.trans hD'

private theorem restrictionUnitSection_pullback {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {L : Y.Modules}
    (v : SheafOfModules.unit Y.ringCatSheaf ⟶ L) :
    (restrictUnitIso j).inv ≫ (restrictFunctor j).map v =
      (pullbackUnitIso j).inv ≫ (pullback j).map v ≫
        (restrictFunctorIsoPullback j).inv.app L := by
  let C := restrictFunctorIsoPullback j
  have hu₀ := restrictFunctorIsoPullback_inv_unit j
  change C.inv.app (SheafOfModules.unit Y.ringCatSheaf) ≫
    (restrictUnitIso j).hom = (pullbackUnitIso j).hom at hu₀
  have hu : (pullbackUnitIso j).inv ≫
      C.inv.app (SheafOfModules.unit Y.ringCatSheaf) = (restrictUnitIso j).inv := by
    apply (cancel_mono (restrictUnitIso j).hom).mp
    rw [Category.assoc, hu₀, Iso.inv_hom_id, Iso.inv_hom_id]
  have hn := C.inv.naturality v
  change (pullback j).map v ≫ C.inv.app L =
    C.inv.app (SheafOfModules.unit Y.ringCatSheaf) ≫ (restrictFunctor j).map v at hn
  rw [hn, ← Category.assoc, hu]

private theorem coefficientRestrictionCounit {A A' : CommRingCat.{u}} (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (L : (Spec A).Modules) [L.IsQuasicoherent] :
    (tilde.functor A').map (affineRestrictGlobalSectionsIso φ L).hom ≫
        (L.restrict (Spec.map φ)).fromTildeΓ =
      (tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj L) ≫
        (pullback (Spec.map φ)).map L.fromTildeΓ ≫
          (restrictFunctorIsoPullback (Spec.map φ)).inv.app L := by
  let j := Spec.map φ
  let C := restrictFunctorIsoPullback j
  let adj := ModuleCat.extendRestrictScalarsAdj φ.hom
  let θ := affineRestrictGlobalSectionsIso φ L
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (restrictAdjunction j) (pullbackPushforwardAdjunction j) L
  change (restrictAdjunction j).unit.app L ≫ (pushforward j).map (C.hom.app L) =
    (pullbackPushforwardAdjunction j).unit.app L at hu
  have hu' := congrArg (fun k => k ≫ (pushforward j).map (C.inv.app L)) hu
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id] at hu'
  have hD : (adj.homEquiv (moduleSpecΓFunctor.obj L)
      (moduleSpecΓFunctor.obj (L.restrict j))).symm
        (moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction j).unit.app L ≫
          (pushforward j).map (C.inv.app L)) ≫
            (pushforwardGlobalSectionsIso φ).hom.app (L.restrict j)) = θ.hom := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    rw [← hu']
    exact (affineRestrictGlobalSectionsIso_unit φ L).symm
  have hc := tildePullbackIso_counit φ L (L.restrict j) (C.inv.app L)
  dsimp only at hc
  rw [hD] at hc
  exact hc

private theorem coefficientUnitSection_restrict {A A' : CommRingCat.{u}} (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (L : (Spec A).Modules) [L.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj L) :
    (restrictUnitIso (Spec.map φ)).inv ≫ (restrictFunctor (Spec.map φ)).map
        (coefficientUnitSection L x) =
      coefficientUnitSection (L.restrict (Spec.map φ))
        ((affineRestrictGlobalSectionsIso φ L).hom ((1 : A') ⊗ₜ[A,φ.hom] x)) := by
  let j := Spec.map φ
  let E := moduleSpecΓFunctor.obj L
  let θ := affineRestrictGlobalSectionsIso φ L
  let T := tilde.functor A'
  let v := canonicalAffineUnitSection E x
  let b := (tildePullbackIso φ).app E
  have hc := coefficientRestrictionCounit φ L
  change T.map θ.hom ≫ (L.restrict j).fromTildeΓ =
    b.inv ≫ (pullback j).map L.fromTildeΓ ≫
      (restrictFunctorIsoPullback j).inv.app L at hc
  have hc' : b.hom ≫ T.map θ.hom ≫ (L.restrict j).fromTildeΓ =
      (pullback j).map L.fromTildeΓ ≫ (restrictFunctorIsoPullback j).inv.app L := by
    rw [hc, Iso.hom_inv_id_assoc]
  have h₀ := congrArg (fun k : (pullback j).obj (tilde E) ⟶ L.restrict j =>
    (pullbackUnitIso j).inv ≫ (pullback j).map v ≫ k) hc'
  have h₁ := congrArg (fun k => k ≫ T.map θ.hom ≫
    (L.restrict j).fromTildeΓ) (canonicalAffineUnitSection_pullback φ E x)
  have h₂ := congrArg (fun k => k ≫ (L.restrict j).fromTildeΓ)
    (affineUnitSection_map θ.hom ((1 : A') ⊗ₜ[A,φ.hom] x))
  simp only [Category.assoc] at h₁ h₂
  rw [restrictionUnitSection_pullback]
  change (pullbackUnitIso j).inv ≫ (pullback j).map (v ≫ L.fromTildeΓ) ≫
    (restrictFunctorIsoPullback j).inv.app L = _
  simpa only [coefficientUnitSection, Functor.map_comp, Category.assoc] using
    h₀.symm.trans (h₁.trans h₂)

private theorem restrictedUnitSection_comp_apply {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M : Y.Modules} {N : X.Modules}
    (v : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (k : M.restrict j ⟶ N)
    (w : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    (h : (restrictUnitIso j).inv ≫ (restrictFunctor j).map v ≫ k = w) (U : X.Opens) :
    k.val.app (op U) (v.val.app (op (j ''ᵁ U)) (1 : Γ(Y, j ''ᵁ U))) =
      w.val.app (op U) (1 : Γ(X, U)) := by
  have hU := congrArg (fun z : SheafOfModules.unit X.ringCatSheaf ⟶ N =>
    z.val.app (op U) (1 : Γ(X, U))) h
  change k.val.app (op U)
      (v.val.app (op (j ''ᵁ U)) ((j.appIso U).inv (1 : Γ(X, U)))) =
    w.val.app (op U) (1 : Γ(X, U)) at hU
  rw [map_one] at hU
  exact hU

private theorem coefficientSection_one_eq {A : CommRingCat.{u}} (s : List A)
    {L : (Spec A).Modules} [L.IsQuasicoherent]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    @Eq (((pullback (Spec.map (regularListQuotientMap s))).obj L).val.obj (op U))
      (closedImmersionRegularListCoefficientSection s e (1 : regularListQuotientRing s) U)
      ((PresheafOfModules.Hom.app
        (M₁ := (SheafOfModules.unit (Spec (regularListQuotientRing s)).ringCatSheaf).val)
        (M₂ := ((pullback (Spec.map (regularListQuotientMap s))).obj L).val)
        (SheafOfModules.Hom.val
          (X := SheafOfModules.unit (Spec (regularListQuotientRing s)).ringCatSheaf)
          (Y := (pullback (Spec.map (regularListQuotientMap s))).obj L)
          (closedImmersionRegularListCoefficientFrameIso s e).inv) (op U))
        (1 : Γ(Spec (regularListQuotientRing s), U))) := by
  dsimp +instances only [regularListQuotientRing, regularListQuotientMap]
  rw [closedImmersionRegularListCoefficientSection_eq, tilde_toOpen_self_one]

private theorem unitSection_compFunctor_eq
    {C D : Type*} [Category* C] [Category* D] {Z : Scheme.{u}}
    (F : C ⥤ D) (G : D ⥤ Z.Modules) (c : C)
    (v : SheafOfModules.unit Z.ringCatSheaf ⟶ G.obj (F.obj c)) (U : Z.Opens)
    (z : (G.obj (F.obj c)).val.obj (op U))
    (hv : @Eq ((G.obj (F.obj c)).val.obj (op U))
      (v.val.app (op U) (1 : Γ(Z, U))) z) :
    let w : SheafOfModules.unit Z.ringCatSheaf ⟶ (F ⋙ G).obj c := v
    @Eq (((F ⋙ G).obj c).val.obj (op U))
      (w.val.app (op U) (1 : Γ(Z, U))) z := by
  exact hv

private theorem restrictedMap_compFunctor_eq
    {C : Type*} [Category* C] {X Y : Scheme.{u}} (F : C ⥤ Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (c : C) {N : X.Modules}
    (v : SheafOfModules.unit Y.ringCatSheaf ⟶ F.obj c)
    (k : (F.obj c).restrict j ⟶ N) (U : X.Opens) (z : N.val.obj (op U))
    (h : @Eq (N.val.obj (op U))
      (k.val.app (op U) (v.val.app (op (j ''ᵁ U)) (1 : Γ(Y, j ''ᵁ U)))) z) :
    @Eq (N.val.obj (op U))
      ((PresheafOfModules.Hom.app (M₁ := ((F ⋙ restrictFunctor j).obj c).val)
        (M₂ := N.val) (SheafOfModules.Hom.val (X := (F ⋙ restrictFunctor j).obj c)
          (Y := N) k) (op U))
        (v.val.app (op (j ''ᵁ U)) (1 : Γ(Y, j ''ᵁ U)))) z := by
  exact h

private theorem mixedOpenSquare_section_eq
    {W X V Y : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion j] (H : p ≫ f = q ≫ j) (L : Y.Modules)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ (pullback f).obj L)
    (b : SheafOfModules.unit W.ringCatSheaf ⟶ (pullback q).obj (L.restrict j))
    (U : W.Opens) (x : ((pullback f).obj L).val.obj (op (p ''ᵁ U)))
    (y : ((pullback q).obj (L.restrict j)).val.obj (op U))
    (h : (restrictUnitIso p).inv ≫ (restrictFunctor p).map a ≫
      (pullbackOpenSquare p q f j H).hom.app L = b)
    (hx : x = a.val.app (op (p ''ᵁ U)) (1 : Γ(X, p ''ᵁ U)))
    (hy : b.val.app (op U) (1 : Γ(W, U)) = y) :
    ((pullbackOpenSquare p q f j H).hom.app L).val.app (op U) x = y := by
  have hU := restrictedUnitSection_comp_apply p a
    ((pullbackOpenSquare p q f j H).hom.app L) b h U
  have hleft := congrArg (((pullbackOpenSquare p q f j H).hom.app L).val.app (op U)) hx
  have hrightComp := unitSection_compFunctor_eq (restrictFunctor j) (pullback q) L b U y hy
  have htail := hU.trans hrightComp
  have htailComp := restrictedMap_compFunctor_eq (pullback f) p L a
    ((pullbackOpenSquare p q f j H).hom.app L) U y htail
  exact hleft.trans htailComp

/-- The original inverse coefficient frames commute with the actual mixed square. -/
theorem regularListCoefficientFrame_open
    {A A' : CommRingCat.{u}} (s : List A) (t : List A') (φ : A ⟶ A')
    (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map (regularListQuotientMap s) =
      Spec.map (regularListQuotientMap t) ≫ Spec.map φ)
    {L : (Spec A).Modules} [L.IsQuasicoherent]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) :
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' : moduleSpecΓFunctor.obj (L.restrict (Spec.map φ)) ≅ ModuleCat.of A' A' :=
      regularListOpenCoefficientFrame φ e θ
    (restrictUnitIso (Spec.map ψ)).inv ≫
      (restrictFunctor (Spec.map ψ)).map
        (closedImmersionRegularListCoefficientFrameIso s (L := L) e).inv ≫
      (pullbackOpenSquare (Spec.map ψ) (Spec.map (regularListQuotientMap t))
        (Spec.map (regularListQuotientMap s)) (Spec.map φ) H).hom.app L =
      (closedImmersionRegularListCoefficientFrameIso t
        (L := L.restrict (Spec.map φ)) e').inv := by
  intro θ e'
  let v := coefficientUnitSection L (e.inv (1 : A))
  have hv := coefficientUnitSection_restrict φ L (e.inv (1 : A))
  rw [← regularListOpenCoefficientFrame_inv_one φ e θ] at hv
  have hs := coefficientUnitSection_pullback s (L := L) e
  have ht := coefficientUnitSection_pullback t (L := L.restrict (Spec.map φ)) e'
  have h := canonicalOpenPullbackSquare_section (Spec.map ψ)
    (Spec.map (regularListQuotientMap t)) (Spec.map (regularListQuotientMap s))
    (Spec.map φ) H v
  change (restrictUnitIso (Spec.map ψ)).inv ≫
      (restrictFunctor (Spec.map ψ)).map ((pullbackUnitIso
        (Spec.map (regularListQuotientMap s))).inv ≫
          (pullback (Spec.map (regularListQuotientMap s))).map
            (coefficientUnitSection L (e.inv (1 : A)))) ≫
      (pullbackOpenSquare (Spec.map ψ) (Spec.map (regularListQuotientMap t))
        (Spec.map (regularListQuotientMap s)) (Spec.map φ) H).hom.app L = _ at h
  rw [hs, hv, ht] at h
  exact h

/-- The actual mixed ambient-open square preserves original coefficient class one
on every open of the literal target regular-list quotient. -/
theorem regularListCoefficientSection_open
    {A A' : CommRingCat.{u}} (s : List A) (t : List A') (φ : A ⟶ A')
    (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map (regularListQuotientMap s) =
      Spec.map (regularListQuotientMap t) ≫ Spec.map φ)
    {L : (Spec A).Modules} [L.IsQuasicoherent]
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
    (U : (Spec (regularListQuotientRing t)).Opens) :
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' : moduleSpecΓFunctor.obj (L.restrict (Spec.map φ)) ≅ ModuleCat.of A' A' :=
      regularListOpenCoefficientFrame φ e θ
    ((pullbackOpenSquare (Spec.map ψ) (Spec.map (regularListQuotientMap t))
        (Spec.map (regularListQuotientMap s)) (Spec.map φ) H).hom.app L).val.app (op U)
      (closedImmersionRegularListCoefficientSection s (L := L) e (1 : regularListQuotientRing s)
        ((Spec.map ψ) ''ᵁ U)) =
      closedImmersionRegularListCoefficientSection t (L := L.restrict (Spec.map φ)) e'
        (1 : regularListQuotientRing t) U := by
  intro θ e'
  exact mixedOpenSquare_section_eq (Spec.map ψ) (Spec.map (regularListQuotientMap t))
    (Spec.map (regularListQuotientMap s)) (Spec.map φ) H L
    (closedImmersionRegularListCoefficientFrameIso s (L := L) e).inv
    (closedImmersionRegularListCoefficientFrameIso t (L := L.restrict (Spec.map φ)) e').inv U
    (closedImmersionRegularListCoefficientSection s (L := L) e
      (1 : regularListQuotientRing s) ((Spec.map ψ) ''ᵁ U))
    (closedImmersionRegularListCoefficientSection t (L := L.restrict (Spec.map φ)) e'
      (1 : regularListQuotientRing t) U)
    (regularListCoefficientFrame_open s t φ ψ H (L := L) e)
    (coefficientSection_one_eq s (L := L) e ((Spec.map ψ) ''ᵁ U))
    (coefficientSection_one_eq t (L := L.restrict (Spec.map φ)) e' U).symm

end AlgebraicGeometry.Scheme.Modules
