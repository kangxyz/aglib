/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientNormal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.DeterminantSquare.Definition

/-!
# The original ordered normal frame on an open square

The original normal map preserves actual kernel classes on every open.
Its exterior power therefore preserves the ordered normal wedge. The
original top-free frame sends this wedge to one, including after the
genuine equality of the two normal degrees is transported.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

private abbrev nativeFreeModule (X : Scheme.{u}) (U : X.Opens) (d : ℕ) :
    Module (X.sheaf.obj.obj (op U))
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d))).val.obj (op U)) := by
  change Module (X.ringCatSheaf.obj.obj (op U)) _
  infer_instance

/-- The original ordered normal frame, transported through its actual exterior degree. -/
def canonicalAffineNormalFrameInDegree
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B) (hσ : Function.Surjective σ)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hker : Ideal.ofList s = RingHom.ker σ.hom) (c : ℕ) (hc : s.length = c) :
    moduleExteriorPower (Spec B)
      ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))) c ≅
        SheafOfModules.unit (Spec B).ringCatSheaf :=
  (eqToIso (congrArg (moduleExteriorPower (Spec B)
      ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ)))) hc)).symm ≪≫
    (moduleExteriorPowerFunctor (Spec B) s.length).mapIso
      (relativeConormalAffineGeometricFreeIso α σ hσ s hs hker) ≪≫
    SheafOfModulesOfCommRing.exteriorTopFreeIso (Spec B).sheaf s.length

/-- The original inverse affine kernel classes, with their genuine common index cast. -/
def canonicalAffineOrderedNormalVectors
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B) (hσ : Function.Surjective σ)
    (s : List A) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (c : ℕ) (hc : s.length = c) (U : (Spec B).Opens) :
    Fin c → ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))).val.obj (op U) :=
  fun i => (relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app (op U)
    (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
      (relativeConormalAffineClass α σ hσ
        ⟨s.get (Fin.cast hc.symm i), hker.le (Ideal.subset_span
          (s.get_mem (Fin.cast hc.symm i)))⟩))

private theorem orderedNormalVectors_apply
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B) (hσ : Function.Surjective σ)
    (s : List A) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (c : ℕ) (hc : s.length = c) (U : (Spec B).Opens) (i : Fin c) :
    canonicalAffineOrderedNormalVectors α σ hσ s hker c hc U i =
      (relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
          (relativeConormalAffineClass α σ hσ
            ⟨s.get (Fin.cast hc.symm i), hker.le (Ideal.subset_span
              (s.get_mem (Fin.cast hc.symm i)))⟩)) := rfl

/-- The same ordered inverse affine kernel classes, with only their genuine index cast. -/
def canonicalAffineOrderedNormalSection
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B) (hσ : Function.Surjective σ)
    (s : List A) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (c : ℕ) (hc : s.length = c) (U : (Spec B).Opens) :
    (moduleExteriorPower (Spec B)
      ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))) c).val.obj (op U) :=
  (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
    ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))) c).app (op U)
      (canonicalAffineOrderedNormalVectors α σ hσ s hker c hc U)

/-- The original normal top frame sends the same original ordered normal wedge to one. -/
theorem canonicalAffineNormalFrameInDegree_orderedSection
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B) (hσ : Function.Surjective σ)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hker : Ideal.ofList s = RingHom.ker σ.hom) (c : ℕ) (hc : s.length = c)
    (U : (Spec B).Opens) :
    (canonicalAffineNormalFrameInDegree α σ hσ s hs hker c hc).hom.val.app (op U)
      (canonicalAffineOrderedNormalSection α σ hσ s hker c hc U) =
        (1 : Γ(Spec B, U)) := by
  subst c
  let := nativeFreeModule (Spec B) U s.length
  let e := relativeConormalAffineGeometricFreeIso α σ hσ s hs hker
  let v := canonicalAffineOrderedNormalVectors α σ hσ s hker s.length rfl U
  let b := SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf s.length (op U)
  have h₁ := congrArg
    ((SheafOfModulesOfCommRing.exteriorTopFreeHom (Spec B).sheaf s.length).val.app (op U))
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk (Spec B).sheaf e.hom
      s.length (op U) v)
  have h₂ := SheafOfModulesOfCommRing.exteriorTopFreeHom_mk (Spec B).sheaf s.length (op U)
    (fun i => e.hom.val.app (op U) (v i))
  have hv : (fun i => e.hom.val.app (op U) (v i)) = b := by
    funext i
    exact (relativeConormalAffineGeometricFreeIso_class α σ hσ s hs hker i U).trans
      (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec B).sheaf s.length (op U) i).symm
  change (SheafOfModulesOfCommRing.exteriorTopFreeHom (Spec B).sheaf s.length).val.app
    (op U) (((moduleExteriorPowerFunctor (Spec B) s.length).map e.hom).val.app (op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
        ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))) s.length).app (op U) v)) = _
  exact h₁.trans (h₂.trans ((congrArg b.det.toFun hv).trans (Module.Basis.det_self b)))

private theorem unitFrame_hom_ext {X : Scheme.{u}} {L N : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (z : L.val.obj (op ⊤))
    (hz : e.hom.val.app (op ⊤) z = (1 : Γ(X, ⊤))) {f g : L ⟶ N}
    (h : f.val.app (op ⊤) z = g.val.app (op ⊤) z) : f = g := by
  have hi : e.inv.val.app (op ⊤) (1 : Γ(X, ⊤)) = z :=
    (congrArg (e.inv.val.app (op ⊤)) hz.symm).trans
      (congrArg (fun k => k.val.app (op ⊤) z) e.hom_inv_id)
  apply (cancel_epi e.inv).mp
  apply (unitHomGlobalSectionsEquiv X N).injective
  change f.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(X, ⊤))) =
    g.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(X, ⊤)))
  exact (congrArg (f.val.app (op ⊤)) hi).trans
    (h.trans (congrArg (g.val.app (op ⊤)) hi).symm)

private theorem unitFrame_openSquare
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    {L : X.Modules} {L' : X'.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf)
    (e' : L' ≅ SheafOfModules.unit X'.ringCatSheaf) (f : L.restrict j ⟶ L')
    (v : ∀ U : X.Opens, L.val.obj (op U))
    (v' : ∀ U : X'.Opens, L'.val.obj (op U))
    (hv : ∀ U, e.hom.val.app (op U) (v U) = (1 : Γ(X, U)))
    (hv' : ∀ U, e'.hom.val.app (op U) (v' U) = (1 : Γ(X', U)))
    (hf : ∀ U, f.val.app (op U) (v (j ''ᵁ U)) = v' U) :
    (restrictFunctor j).map e.hom ≫ (restrictUnitIso j).hom = f ≫ e'.hom := by
  let U : X'.Opens := ⊤
  let W := j ''ᵁ U
  let eR := (restrictFunctor j).mapIso e ≪≫ restrictUnitIso j
  have hz : eR.hom.val.app (op U) (v W) = (1 : Γ(X', U)) :=
    (congrArg (j.appIso U).hom.hom (hv W)).trans (map_one (j.appIso U).hom.hom)
  apply unitFrame_hom_ext eR (v W) hz
  exact hz.trans ((congrArg (e'.hom.val.app (op U)) (hf U)).trans (hv' U)).symm

/-- The actual exterior normal map on the original mixed open square. -/
def canonicalNormalTopOpenMap
    {A B A' B' : CommRingCat.{u}} (σ : A ⟶ B) (τ : A' ⟶ B')
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map σ = Spec.map τ ≫ Spec.map φ) (c : ℕ) :
    (restrictFunctor (Spec.map ψ)).obj
      (moduleExteriorPower (Spec B)
        ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))) c) ⟶
      moduleExteriorPower (Spec B')
        ((pullback (Spec.map τ)).obj (Hom.idealModule (Spec.map τ))) c :=
  canonicalExteriorOpenMap (X := Spec B) (X' := Spec B') (Spec.map ψ)
    ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ)))
    ((pullback (Spec.map τ)).obj (Hom.idealModule (Spec.map τ))) c
    (canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map τ) (Spec.map φ) (Spec.map ψ) H)

private theorem normalTopOpenMap_wedge_congr
    {A B A' B' : CommRingCat.{u}} (σ : A ⟶ B) (τ : A' ⟶ B')
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map σ = Spec.map τ ≫ Spec.map φ) (c : ℕ)
    (U : (Spec B').Opens)
    (v : Fin c → ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))).val.obj
      (op (Spec.map ψ ''ᵁ U)))
    (v' : Fin c → ((pullback (Spec.map τ)).obj (Hom.idealModule (Spec.map τ))).val.obj
      (op U))
    (hv : ∀ i, (canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map τ)
      (Spec.map φ) (Spec.map ψ) H).val.app (op U) (v i) = v' i) :
    (canonicalNormalTopOpenMap σ τ φ ψ H c).val.app (op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
        ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ))) c).app
          (op (Spec.map ψ ''ᵁ U)) v) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B').sheaf
        ((pullback (Spec.map τ)).obj (Hom.idealModule (Spec.map τ))) c).app (op U) v' :=
  canonicalExteriorOpenMap_wedge_congr (Spec.map ψ)
    ((pullback (Spec.map σ)).obj (Hom.idealModule (Spec.map σ)))
    ((pullback (Spec.map τ)).obj (Hom.idealModule (Spec.map τ))) c
    (canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map τ)
      (Spec.map φ) (Spec.map ψ) H) U v v' hv

/-- The literal equality between the original ordered wedges under the original top map. -/
def CanonicalAffineOrderedNormalSectionOpenSquare
    {R A B R' A' B' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (σ : A ⟶ B) (τ : A' ⟶ B') (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (s : List A) (t : List A')
    (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (hker' : Ideal.ofList t = RingHom.ker τ.hom) (c : ℕ)
    (hc : s.length = c) (hc' : t.length = c)
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map σ = Spec.map τ ≫ Spec.map φ)
    (U : (Spec B').Opens) : Prop :=
    (canonicalNormalTopOpenMap σ τ φ ψ H c).val.app (op U)
      (canonicalAffineOrderedNormalSection α σ hσ s hker c hc (Spec.map ψ ''ᵁ U)) =
    canonicalAffineOrderedNormalSection α' τ hτ t hker' c hc' U

private theorem orderedNormalClass_openSquare
    {R A B R' A' B' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (σ : A ⟶ B) (τ : A' ⟶ B') (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (s : List A) (t : List A')
    (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (hker' : Ideal.ofList t = RingHom.ker τ.hom) (c : ℕ)
    (hc : s.length = c) (hc' : t.length = c)
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map σ = Spec.map τ ≫ Spec.map φ)
    (hst : ∀ i : Fin c, φ (s.get (Fin.cast hc.symm i)) = t.get (Fin.cast hc'.symm i))
    (i : Fin c) (U : (Spec B').Opens) :
    (canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map τ)
      (Spec.map φ) (Spec.map ψ) H).val.app (op U)
      ((relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app
        (op (Spec.map ψ ''ᵁ U))
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) (Spec.map ψ ''ᵁ U)
          (relativeConormalAffineClass α σ hσ
            ⟨s.get (Fin.cast hc.symm i), hker.le
              (Ideal.subset_span (s.get_mem (Fin.cast hc.symm i)))⟩))) =
      (relativeConormalAffineIdealPullbackIso α' τ hτ).inv.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α' τ hτ) U
          (relativeConormalAffineClass α' τ hτ
            ⟨t.get (Fin.cast hc'.symm i), hker'.le
              (Ideal.subset_span (t.get_mem (Fin.cast hc'.symm i)))⟩)) :=
  relativeConormalIdealClass_openSquare α α' σ τ hσ hτ φ ψ H _ _ (hst i) U

private theorem orderedNormalVectors_openSquare
    {R A B R' A' B' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (σ : A ⟶ B) (τ : A' ⟶ B') (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (s : List A) (t : List A')
    (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (hker' : Ideal.ofList t = RingHom.ker τ.hom) (c : ℕ)
    (hc : s.length = c) (hc' : t.length = c)
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map σ = Spec.map τ ≫ Spec.map φ)
    (hst : ∀ i : Fin c, φ (s.get (Fin.cast hc.symm i)) = t.get (Fin.cast hc'.symm i))
    (U : (Spec B').Opens) (i : Fin c) :
    (canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map τ)
      (Spec.map φ) (Spec.map ψ) H).val.app (op U)
      (canonicalAffineOrderedNormalVectors α σ hσ s hker c hc (Spec.map ψ ''ᵁ U) i) =
      canonicalAffineOrderedNormalVectors α' τ hτ t hker' c hc' U i := by
  have hSource := orderedNormalVectors_apply α σ hσ s hker c hc (Spec.map ψ ''ᵁ U) i
  have hTarget := orderedNormalVectors_apply α' τ hτ t hker' c hc' U i
  exact (congrArg
    ((canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map τ)
      (Spec.map φ) (Spec.map ψ) H).val.app (op U)) hSource).trans
    ((orderedNormalClass_openSquare α α' σ τ hσ hτ s t hker hker'
      c hc hc' φ ψ H hst i U).trans hTarget.symm)

/-- The original normal top map preserves the same ordered inverse affine kernel classes. -/
theorem canonicalAffineOrderedNormalSection_openSquare
    {R A B R' A' B' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (σ : A ⟶ B) (τ : A' ⟶ B') (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (s : List A) (t : List A')
    (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (hker' : Ideal.ofList t = RingHom.ker τ.hom) (c : ℕ)
    (hc : s.length = c) (hc' : t.length = c)
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map σ = Spec.map τ ≫ Spec.map φ)
    (hst : ∀ i : Fin c, φ (s.get (Fin.cast hc.symm i)) = t.get (Fin.cast hc'.symm i))
    (U : (Spec B').Opens) :
    CanonicalAffineOrderedNormalSectionOpenSquare α α' σ τ hσ hτ s t hker hker'
      c hc hc' φ ψ H U := by
  exact normalTopOpenMap_wedge_congr σ τ φ ψ H c U
    (canonicalAffineOrderedNormalVectors α σ hσ s hker c hc (Spec.map ψ ''ᵁ U))
    (canonicalAffineOrderedNormalVectors α' τ hτ t hker' c hc' U)
    (orderedNormalVectors_openSquare α α' σ τ hσ hτ s t hker hker'
      c hc hc' φ ψ H hst U)

/-- An actual ordered generator image law gives the original ordered normal-frame square. -/
theorem canonicalAffineNormalFrameInDegree_openSquare
    {R A B R' A' B' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (σ : A ⟶ B) (τ : A' ⟶ B') (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (s : List A) (t : List A') (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
    (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (hker' : Ideal.ofList t = RingHom.ker τ.hom) (c : ℕ)
    (hc : s.length = c) (hc' : t.length = c)
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map σ = Spec.map τ ≫ Spec.map φ)
    (hst : ∀ i : Fin c, φ (s.get (Fin.cast hc.symm i)) = t.get (Fin.cast hc'.symm i)) :
    (restrictFunctor (Spec.map ψ)).map
        (canonicalAffineNormalFrameInDegree α σ hσ s hs hker c hc).hom ≫
        (restrictUnitIso (Spec.map ψ)).hom =
      canonicalNormalTopOpenMap σ τ φ ψ H c ≫
        (canonicalAffineNormalFrameInDegree α' τ hτ t ht hker' c hc').hom := by
  apply unitFrame_openSquare (Spec.map ψ)
    (canonicalAffineNormalFrameInDegree α σ hσ s hs hker c hc)
    (canonicalAffineNormalFrameInDegree α' τ hτ t ht hker' c hc')
    (canonicalNormalTopOpenMap σ τ φ ψ H c)
    (canonicalAffineOrderedNormalSection α σ hσ s hker c hc)
    (canonicalAffineOrderedNormalSection α' τ hτ t hker' c hc')
    (canonicalAffineNormalFrameInDegree_orderedSection α σ hσ s hs hker c hc)
    (canonicalAffineNormalFrameInDegree_orderedSection α' τ hτ t ht hker' c hc')
  exact canonicalAffineOrderedNormalSection_openSquare α α' σ τ hσ hτ s t hker hker'
    c hc hc' φ ψ H hst

end AlgebraicGeometry.Scheme.Modules
