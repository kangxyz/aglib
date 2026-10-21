/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Frames
public import Aglib.AlgebraicGeometry.Modules.Differentials.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Affine diagonal conormal comparison

`Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal.Affine` owns the
canonical coordinate-difference map and its actual affine comparison.

The affine diagonal is the spectrum map of tensor multiplication. Its original
kernel modulo its square is the native Kähler differential module. The geometric
conormal uses the actual module-sheaf pullback of the diagonal ideal.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The literal first tensor inclusion of the affine diagonal presentation. -/
def diagonalTensorInclusion : CommRingCat.of A ⟶ CommRingCat.of (A ⊗[R] A) :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := A))

/-- The literal multiplication map whose spectrum is the affine diagonal. -/
def diagonalTensorMultiplication : CommRingCat.of (A ⊗[R] A) ⟶ CommRingCat.of A :=
  CommRingCat.ofHom (Algebra.TensorProduct.lmul' R).toRingHom

theorem diagonalTensorMultiplication_surjective :
    Function.Surjective (diagonalTensorMultiplication R A) := by
  intro a
  exact ⟨a ⊗ₜ[R] 1, by simp [diagonalTensorMultiplication]⟩

/-- The positive coordinate difference in the actual tensor-multiplication kernel. -/
def diagonalDifferenceElement (a : A) : RingHom.ker (diagonalTensorMultiplication R A).hom :=
  ⟨(1 : A) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : A),
    KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R a⟩

private theorem diagonalTensor_smul (a : A) (x : KaehlerDifferential R A) :
    (a ⊗ₜ[R] (1 : A)) • x = a • x :=
  IsScalarTower.algebraMap_smul (A ⊗[R] A) a x

/-- The affine diagonal conormal quotient has the original Kähler carrier and
the original scalar action of the first tensor factor. -/
def diagonalCotangentIso :
    relativeConormalAffineModule (𝟙 (CommRingCat.of (A ⊗[R] A)))
      (diagonalTensorMultiplication R A) (diagonalTensorMultiplication_surjective R A) ≅
      ModuleCat.of A (KaehlerDifferential R A) := by
  let α := 𝟙 (CommRingCat.of (A ⊗[R] A))
  let σ := diagonalTensorMultiplication R A
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let E := relativeConormalAffineExtension α σ (diagonalTensorMultiplication_surjective R A)
  let e : relativeConormalAffineModule α σ (diagonalTensorMultiplication_surjective R A) ≃ₗ[A]
      KaehlerDifferential R A :=
    { toFun := fun x => Algebra.Extension.Cotangent.val (P := E) x
      invFun := fun x => Algebra.Extension.Cotangent.of (P := E) x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' a x := by
        change E.Cotangent at x
        rw [Algebra.Extension.Cotangent.val_smul]
        let t : A ⊗[R] A := E.σ a
        have hker : t - a ⊗ₜ[R] (1 : A) ∈
            KaehlerDifferential.ideal R A := by
          change diagonalTensorMultiplication R A (t - a ⊗ₜ[R] (1 : A)) = 0
          rw [map_sub]
          have hσ : diagonalTensorMultiplication R A t = a := E.algebraMap_σ a
          rw [hσ]
          simp [diagonalTensorMultiplication]
        have hz := Ideal.Cotangent.smul_eq_zero_of_mem hker x.val
        rw [sub_smul, sub_eq_zero] at hz
        exact hz.trans (diagonalTensor_smul R A a x.val) }
  exact e.toModuleIso

/-- Actual pullback of the affine diagonal ideal is the tilde of the native
Kähler module, through the original ideal and tensor-pullback comparisons. -/
def affineDiagonalConormalIso :
    (Scheme.Modules.pullback (Spec.map (diagonalTensorMultiplication R A))).obj
      (idealModule (Spec.map (diagonalTensorMultiplication R A))) ≅
        tilde (ModuleCat.of A (KaehlerDifferential R A)) :=
  relativeConormalAffineIdealPullbackIso (𝟙 (CommRingCat.of (A ⊗[R] A)))
      (diagonalTensorMultiplication R A) (diagonalTensorMultiplication_surjective R A) ≪≫
    (tilde.functor (.of A)).mapIso (diagonalCotangentIso R A)

end AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Modules.Differentials.Diagonal

variable {X Y S : Scheme.{u}}

theorem module_comp_apply {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (U : X.Opens) (m : Γ(M, U)) :
    (f ≫ g).val.app (op U) m = g.val.app (op U) (f.val.app (op U) m) := rfl

theorem module_id_apply (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    (𝟙 M : M ⟶ M).val.app (op U) m = m := rfl

theorem pullbackComp_inv_unit (f : X ⟶ Y) (g : Y ⟶ S) (M : S.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
      (Scheme.Modules.pushforward (f ≫ g)).map
        ((Scheme.Modules.pullbackComp f g).inv.app M) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  simpa only [Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj] using h.symm

theorem pullbackComp_inv_unit_apply (f : X ⟶ Y) (g : Y ⟶ S) (M : S.Modules)
    (U : S.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app (op U) m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((Scheme.Modules.pullback g).obj M)).val.app (op (g ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op U) m) :=
  congrArg (fun q => q.val.app (op U) m) (pullbackComp_inv_unit f g M)

theorem pullbackComp_inv_unit_top (f : X ⟶ Y) (g : Y ⟶ S) (M : S.Modules)
    (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app (op ⊤) m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((Scheme.Modules.pullback g).obj M)).val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤) m) :=
  pullbackComp_inv_unit_apply f g M ⊤ m

/-- Pullback of an actual module section, restricted to the chosen source open. -/
def pullbackSection (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) : Γ(M, U) →+ Γ((Scheme.Modules.pullback f).obj M, V) :=
  (((Scheme.Modules.pullback f).obj M).val.map (homOfLE h).op).hom.toAddMonoidHom.comp
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
      (op U)).hom.toAddMonoidHom

theorem pullbackSection_smul (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (r : Γ(Y, U)) (m : Γ(M, U)) :
    pullbackSection f M U V h (r • m) =
      f.appLE U V h r • pullbackSection f M U V h m := by
  let N := (Scheme.Modules.pullback f).obj M
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U)
  change N.val.map (homOfLE h).op (η (r • m)) =
    f.appLE U V h r • N.val.map (homOfLE h).op (η m)
  let t : N.val.obj (op (f ⁻¹ᵁ U)) := η m
  have hs : (show N.val.obj (op (f ⁻¹ᵁ U)) from η (r • m)) = f.app U r • t :=
    η.hom.map_smul r m
  calc
    _ = N.val.map (homOfLE h).op (f.app U r • t) :=
      congrArg (fun z => N.val.map (homOfLE h).op z) hs
    _ = _ := N.val.map_smul (homOfLE h).op (f.app U r) _

/-- The neighborhood where both diagonal coordinates belong to the same open. -/
def squareOpen (p : X ⟶ S) (U : X.Opens) : (Limits.pullback p p).Opens :=
  (pullback.fst p p) ⁻¹ᵁ U ⊓ (pullback.snd p p) ⁻¹ᵁ U

theorem diagonal_preimage_squareOpen (p : X ⟶ S) (U : X.Opens) :
    (pullback.diagonal p) ⁻¹ᵁ squareOpen p U = U := by
  simp only [squareOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem]

theorem squareOpenAlongDiagonal (p : X ⟶ S) (U : X.Opens) :
    U ≤ (pullback.diagonal p) ⁻¹ᵁ squareOpen p U :=
  (diagonal_preimage_squareOpen p U).ge

private theorem appLE_self_of_eq_id (f : X ⟶ X) (hf : f = 𝟙 X) (U : X.Opens)
    (h : U ≤ f ⁻¹ᵁ U) : f.appLE U U h = 𝟙 Γ(X, U) := by
  subst f
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  exact X.presheaf.map_id (op U)

theorem first_diagonal_app (p : X ⟶ S) (U : X.Opens) :
    (pullback.fst p p).appLE U (squareOpen p U) inf_le_left ≫
      (pullback.diagonal p).appLE (squareOpen p U) U (squareOpenAlongDiagonal p U) =
        𝟙 Γ(X, U) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  exact appLE_self_of_eq_id _ (pullback.diagonal_fst p) U _

theorem second_diagonal_app (p : X ⟶ S) (U : X.Opens) :
    (pullback.snd p p).appLE U (squareOpen p U) inf_le_right ≫
      (pullback.diagonal p).appLE (squareOpen p U) U (squareOpenAlongDiagonal p U) =
        𝟙 Γ(X, U) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  exact appLE_self_of_eq_id _ (pullback.diagonal_snd p) U _

/-- The difference of the two coordinate pullbacks is an actual diagonal-ideal section. -/
def idealDifference (p : X ⟶ S) (U : X.Opens) :
    Γ(X, U) →+ RingHom.ker ((pullback.diagonal p).app (squareOpen p U)).hom where
  toFun a := ⟨(pullback.snd p p).appLE U (squareOpen p U) inf_le_right a -
    (pullback.fst p p).appLE U (squareOpen p U) inf_le_left a, by
    let h := squareOpenAlongDiagonal p U
    have : IsIso (homOfLE h) := homOfLE_isIso_of_eq _ (diagonal_preimage_squareOpen p U).symm
    have hinj := (ConcreteCategory.bijective_of_isIso (X.presheaf.map (homOfLE h).op)).1
    apply hinj
    change (pullback.diagonal p).appLE (squareOpen p U) U h (_ - _) =
      X.presheaf.map (homOfLE h).op 0
    rw [map_sub, map_zero]
    have h₁ := congrArg (fun f : Γ(X, U) ⟶ Γ(X, U) => f a) (first_diagonal_app p U)
    have h₂ := congrArg (fun f : Γ(X, U) ⟶ Γ(X, U) => f a) (second_diagonal_app p U)
    exact sub_eq_zero.mpr (h₂.trans h₁.symm)⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by
    apply Subtype.ext
    change _ - _ = (_ - _) + (_ - _)
    simp only [map_add]
    abel

/-- The same coordinate difference in the original kernel module sheaf. -/
def idealDifferenceSection (p : X ⟶ S) (U : X.Opens) :
    Γ(X, U) →+ Γ(idealModule (pullback.diagonal p), squareOpen p U) :=
  (idealSectionsEquiv (pullback.diagonal p) (squareOpen p U)).symm.toAddMonoidHom.comp
    (idealDifference p U)

theorem idealDifferenceSection_inclusion (p : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) :
    (idealInclusion (pullback.diagonal p)).val.app (op (squareOpen p U))
        (idealDifferenceSection p U a) =
      (pullback.snd p p).appLE U (squareOpen p U) inf_le_right a -
        (pullback.fst p p).appLE U (squareOpen p U) inf_le_left a := by
  exact (idealSectionsEquiv_val (pullback.diagonal p) (squareOpen p U) _).symm.trans
    (congrArg Subtype.val ((idealSectionsEquiv (pullback.diagonal p)
      (squareOpen p U)).apply_symm_apply (idealDifference p U a)))

theorem idealDifferenceSection_mul (p : X ⟶ S) (U : X.Opens) (a b : Γ(X, U)) :
    idealDifferenceSection p U (a * b) =
      (pullback.fst p p).appLE U (squareOpen p U) inf_le_left a •
        idealDifferenceSection p U b +
      (pullback.snd p p).appLE U (squareOpen p U) inf_le_right b •
        idealDifferenceSection p U a := by
  apply (idealSectionsEquiv (pullback.diagonal p) (squareOpen p U)).injective
  apply Subtype.ext
  simp only [map_add, _root_.map_smul, Submodule.coe_add, Submodule.coe_smul,
    idealSectionsEquiv_val,
    idealDifferenceSection_inclusion]
  let f := (pullback.fst p p).appLE U (squareOpen p U) inf_le_left
  let g := (pullback.snd p p).appLE U (squareOpen p U) inf_le_right
  change g (a * b) - f (a * b) = f a * (g b - f b) + g b * (g a - f a)
  simp only [map_mul]
  ring

/-- The actual conormal module on the source of the diagonal. -/
abbrev conormal (p : X ⟶ S) : X.Modules :=
  (Scheme.Modules.pullback (pullback.diagonal p)).obj (idealModule (pullback.diagonal p))

/-- The universal coordinate-difference candidate in the actual diagonal conormal. -/
def difference (p : X ⟶ S) (U : X.Opens) : Γ(X, U) →+ Γ(conormal p, U) :=
  (pullbackSection (pullback.diagonal p) (idealModule (pullback.diagonal p))
    (squareOpen p U) U (squareOpenAlongDiagonal p U)).comp (idealDifferenceSection p U)

theorem difference_mul (p : X ⟶ S) (U : X.Opens) (a b : Γ(X, U)) :
    difference p U (a * b) = a • difference p U b + b • difference p U a := by
  change pullbackSection _ _ _ _ _ (idealDifferenceSection p U (a * b)) = _
  rw [idealDifferenceSection_mul, map_add, pullbackSection_smul, pullbackSection_smul]
  have h₁ := congrArg (fun f : Γ(X, U) ⟶ Γ(X, U) => f a) (first_diagonal_app p U)
  have h₂ := congrArg (fun f : Γ(X, U) ⟶ Γ(X, U) => f b) (second_diagonal_app p U)
  change (pullback.diagonal p).appLE _ _ _ ((pullback.fst p p).appLE _ _ _ a) = a at h₁
  change (pullback.diagonal p).appLE _ _ _ ((pullback.snd p p).appLE _ _ _ b) = b at h₂
  rw [h₁, h₂]
  rfl

theorem pullbackSection_naturality (f : X ⟶ Y) (M : Y.Modules)
    {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U') (m : Γ(M, U)) :
    ((Scheme.Modules.pullback f).obj M).val.map (homOfLE hV).op
        (pullbackSection f M U V h m) =
      pullbackSection f M U' V' h' (M.val.map (homOfLE hU).op m) := by
  let N := (Scheme.Modules.pullback f).obj M
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val
  change N.val.map (homOfLE hV).op (N.val.map (homOfLE h).op (η.app (op U) m)) =
    N.val.map (homOfLE h').op (η.app (op U') (M.val.map (homOfLE hU).op m))
  have hn := PresheafOfModules.naturality_apply η (homOfLE hU).op m
  change η.app (op U') (M.val.map (homOfLE hU).op m) =
    N.val.map ((TopologicalSpace.Opens.map f.base).map (homOfLE hU)).op (η.app (op U) m) at hn
  rw [hn]
  change N.val.map (homOfLE hV).op (N.val.map (homOfLE h).op (η.app (op U) m)) =
    N.val.map (homOfLE h').op
      (N.val.map ((TopologicalSpace.Opens.map f.base).map (homOfLE hU)).op (η.app (op U) m))
  rw [← N.val.map_comp_apply, ← N.val.map_comp_apply]
  rfl

theorem squareOpen_mono (p : X ⟶ S) {U V : X.Opens} (h : V ≤ U) :
    squareOpen p V ≤ squareOpen p U :=
  inf_le_inf ((pullback.fst p p).preimage_mono h) ((pullback.snd p p).preimage_mono h)

theorem idealDifferenceSection_naturality (p : X ⟶ S) {U V : X.Opens}
    (h : V ≤ U) (a : Γ(X, U)) :
    (idealModule (pullback.diagonal p)).val.map (homOfLE (squareOpen_mono p h)).op
        (idealDifferenceSection p U a) =
      idealDifferenceSection p V (X.presheaf.map (homOfLE h).op a) := by
  apply (idealSectionsEquiv (pullback.diagonal p) (squareOpen p V)).injective
  apply Subtype.ext
  simp only [idealSectionsEquiv_val, PresheafOfModules.naturality_apply,
    idealDifferenceSection_inclusion]
  change (Limits.pullback p p).presheaf.map (homOfLE (squareOpen_mono p h)).op
      ((pullback.snd p p).appLE _ _ _ a - (pullback.fst p p).appLE _ _ _ a) =
    (pullback.snd p p).appLE _ _ _ (X.presheaf.map (homOfLE h).op a) -
      (pullback.fst p p).appLE _ _ _ (X.presheaf.map (homOfLE h).op a)
  rw [map_sub]
  congr 1
  · exact congrArg (fun q : Γ(X, U) ⟶ Γ(Limits.pullback p p, squareOpen p V) => q a)
      (((pullback.snd p p).appLE_map inf_le_right
        (homOfLE (squareOpen_mono p h)).op).trans
        ((pullback.snd p p).map_appLE inf_le_right (homOfLE h).op).symm)
  · exact congrArg (fun q : Γ(X, U) ⟶ Γ(Limits.pullback p p, squareOpen p V) => q a)
      (((pullback.fst p p).appLE_map inf_le_left
        (homOfLE (squareOpen_mono p h)).op).trans
        ((pullback.fst p p).map_appLE inf_le_left (homOfLE h).op).symm)

theorem difference_naturality (p : X ⟶ S) {U V : X.Opens} (h : V ≤ U)
    (a : Γ(X, U)) :
    difference p V (X.presheaf.map (homOfLE h).op a) =
      (conormal p).val.map (homOfLE h).op (difference p U a) := by
  change pullbackSection _ _ _ _ _
    (idealDifferenceSection p V (X.presheaf.map (homOfLE h).op a)) = _
  rw [← idealDifferenceSection_naturality]
  exact (pullbackSection_naturality (pullback.diagonal p)
    (idealModule (pullback.diagonal p)) (squareOpen_mono p h) h
    (squareOpenAlongDiagonal p U) (squareOpenAlongDiagonal p V)
    (idealDifferenceSection p U a)).symm

/-- Equal scheme morphisms give the same restricted map on structure sections. -/
theorem appLE_congr {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

theorem difference_base (p : X ⟶ S) (U : S.Opens) (a : Γ(S, U)) :
    difference p (p ⁻¹ᵁ U) (p.app U a) = 0 := by
  have he : idealDifferenceSection p (p ⁻¹ᵁ U) (p.app U a) = 0 := by
    apply (idealSectionsEquiv (pullback.diagonal p) (squareOpen p (p ⁻¹ᵁ U))).injective
    apply Subtype.ext
    simp only [idealSectionsEquiv_val, map_zero, idealDifferenceSection_inclusion]
    apply sub_eq_zero.mpr
    have hfst : squareOpen p (p ⁻¹ᵁ U) ≤ (pullback.fst p p ≫ p) ⁻¹ᵁ U := inf_le_left
    have hsnd : squareOpen p (p ⁻¹ᵁ U) ≤ (pullback.snd p p ≫ p) ⁻¹ᵁ U := inf_le_right
    have hm := appLE_congr (pullback.condition (f := p) (g := p)) U
      (squareOpen p (p ⁻¹ᵁ U)) hfst hsnd
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.comp_appLE] at hm
    exact (congrArg (fun q : Γ(S, U) ⟶ Γ(Limits.pullback p p, squareOpen p (p ⁻¹ᵁ U)) =>
      q a) hm).symm
  change pullbackSection _ _ _ _ _ (idealDifferenceSection p (p ⁻¹ᵁ U) (p.app U a)) = 0
  rw [he, map_zero]

/-- Coordinate differences define a derivation into the actual conormal module. -/
def derivation (p : X ⟶ S) : PresheafOfModulesOfCommRing.Derivation (conormal p).val p.c where
  d {U} := difference p U.unop
  d_mul {U} := difference_mul p U.unop
  d_map i a := difference_naturality p (leOfHom i.unop) a
  d_app {U} := difference_base p U.unop

/-- The canonical comparison from actual relative differentials to the diagonal conormal. -/
def differentialToConormal (p : X ⟶ S) : relativeDifferentialSheaf p ⟶ conormal p :=
  relativeDifferentialDesc p (conormal p) (derivation p)

theorem differentialToConormal_d (p : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) :
    (differentialToConormal p).val.app (op U) ((relativeDifferentialDerivation p).d a) =
      difference p U a :=
  relativeDifferentialDesc_d p (conormal p) (derivation p) (op U) a

theorem pullbackCongr_unit_top {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤) m := by
  subst g
  rfl

theorem pullback_map_unit_top (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N)
    (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).map φ).val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op ⊤)
      (φ.val.app (op ⊤) m) :=
  (congrArg (fun q => q.val.app (op ⊤) m)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)).symm

theorem idealPullbackMap_unit_top {D D' : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b) (m : Γ(idealModule i, ⊤)) :
    (idealPullbackMap i i' b a h).val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (idealModule i)).val.app
        (op ⊤) m) = (idealPushforwardMap i i' b a h).val.app (op ⊤) m := by
  have he := idealPullbackMap_adjoint i i' b a h
  rw [Adjunction.homEquiv_unit] at he
  exact congrArg (fun q => q.val.app (op ⊤) m) he

/-- An ambient scheme isomorphism preserves the actual conormal of a fixed source. -/
def conormalAmbientIso {D : Scheme.{u}} (i : D ⟶ X) (i' : D ⟶ Y)
    (b : Y ⟶ X) [IsIso b] (h : i = i' ≫ b) :
    (Scheme.Modules.pullback i).obj (idealModule i) ≅
      (Scheme.Modules.pullback i').obj (idealModule i') := by
  have hh : (𝟙 D) ≫ i = i' ≫ b := by simpa only [Category.id_comp] using h
  let : IsIso (idealPullbackMap i i' b (𝟙 D) hh) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ hh
  exact (Scheme.Modules.pullbackCongr h).app (idealModule i) ≪≫
    ((Scheme.Modules.pullbackComp i' b).app (idealModule i)).symm ≪≫
    (Scheme.Modules.pullback i').mapIso (asIso (idealPullbackMap i i' b (𝟙 D) hh))

theorem conormalAmbientIso_unit_top {D : Scheme.{u}} (i : D ⟶ X) (i' : D ⟶ Y)
    (b : Y ⟶ X) [IsIso b] (h : i = i' ≫ b) (m : Γ(idealModule i, ⊤)) :
    (conormalAmbientIso i i' b h).hom.val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (idealModule i)).val.app
        (op ⊤) m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app (idealModule i')).val.app
      (op ⊤) ((idealPushforwardMap i i' b (𝟙 D)
        (by simpa only [Category.id_comp] using h)).val.app (op ⊤) m) := by
  have hh : (𝟙 D) ≫ i = i' ≫ b := by simpa only [Category.id_comp] using h
  change ((Scheme.Modules.pullback i').map (idealPullbackMap i i' b (𝟙 D) hh)).val.app (op ⊤)
    (((Scheme.Modules.pullbackComp i' b).inv.app (idealModule i)).val.app (op ⊤)
      (((Scheme.Modules.pullbackCongr h).hom.app (idealModule i)).val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (idealModule i)).val.app
          (op ⊤) m))) = _
  rw [pullbackCongr_unit_top, pullbackComp_inv_unit_top, pullback_map_unit_top,
    idealPullbackMap_unit_top]

/-- The map of the actual diagonal ambient products induced by a source map. -/
def squareMap (p : X ⟶ S) (j : Y ⟶ X) :
    Limits.pullback (j ≫ p) (j ≫ p) ⟶ Limits.pullback p p :=
  pullback.map (j ≫ p) (j ≫ p) p p j j (𝟙 S) (by simp) (by simp)

theorem diagonal_squareMap (p : X ⟶ S) (j : Y ⟶ X) :
    j ≫ pullback.diagonal p = pullback.diagonal (j ≫ p) ≫ squareMap p j := by
  apply pullback.hom_ext <;> simp [squareMap]

theorem diagonal_isPullback (p : X ⟶ S) (j : Y ⟶ X) [Mono j] :
    IsPullback j (pullback.diagonal (j ≫ p)) (pullback.diagonal p) (squareMap p j) := by
  apply IsPullback.mk' (diagonal_squareMap p j)
  · intro T a b hab _
    exact (cancel_mono j).mp hab
  · intro T a b hab
    have hfst : b ≫ pullback.fst (j ≫ p) (j ≫ p) ≫ j = a := by
      have h := congrArg (fun q => q ≫ pullback.fst p p) hab
      simpa [squareMap, Category.assoc] using h.symm
    have hsnd : b ≫ pullback.snd (j ≫ p) (j ≫ p) ≫ j = a := by
      have h := congrArg (fun q => q ≫ pullback.snd p p) hab
      simpa [squareMap, Category.assoc] using h.symm
    refine ⟨b ≫ pullback.fst (j ≫ p) (j ≫ p), hfst, ?_⟩
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      apply (cancel_mono j).mp
      simpa only [Category.assoc] using hfst.trans hsnd.symm

/-- Restriction of the actual diagonal conormal along a source open immersion. -/
def conormalPullbackIso (p : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.pullback j).obj (conormal p) ≅ conormal (j ≫ p) := by
  let b := squareMap p j
  let : IsOpenImmersion b := by dsimp [b, squareMap]; infer_instance
  let : IsIso (idealPullbackMap (pullback.diagonal p) (pullback.diagonal (j ≫ p))
      b j (diagonal_squareMap p j)) :=
    idealPullbackMap_isIso_of_isOpenImmersion _ _ _ _ (diagonal_squareMap p j)
      (diagonal_isPullback p j)
  exact (Scheme.Modules.pullbackComp j (pullback.diagonal p)).app
      (idealModule (pullback.diagonal p)) ≪≫
    (Scheme.Modules.pullbackCongr (diagonal_squareMap p j)).app
      (idealModule (pullback.diagonal p)) ≪≫
    ((Scheme.Modules.pullbackComp (pullback.diagonal (j ≫ p)) b).app
      (idealModule (pullback.diagonal p))).symm ≪≫
    (Scheme.Modules.pullback (pullback.diagonal (j ≫ p))).mapIso
      (asIso (idealPullbackMap (pullback.diagonal p) (pullback.diagonal (j ≫ p))
        b j (diagonal_squareMap p j)))

/-- The original tensor quotient and the native affine conormal module. -/
def affineCotangentTensorIso {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (hσ : Function.Surjective σ) :
    (ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom)) ≅
      relativeConormalAffineModule (𝟙 A) σ hσ := by
  let := (𝟙 A : A ⟶ A).hom.toAlgebra
  let := ((𝟙 A) ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let E := relativeConormalAffineExtension (𝟙 A) σ hσ
  exact E.cotangentEquiv.toModuleIso

/-- The original kernel-class map into the scalar-restricted native affine conormal. -/
def affineClassMap {A B : CommRingCat.{u}} (σ : A ⟶ B) (hσ : Function.Surjective σ) :
    ModuleCat.of A (RingHom.ker σ.hom) ⟶ (ModuleCat.restrictScalars σ.hom).obj
      (relativeConormalAffineModule (𝟙 A) σ hσ) :=
  (ModuleCat.extendRestrictScalarsAdj σ.hom).unit.app
    (ModuleCat.of A (RingHom.ker σ.hom)) ≫
      (ModuleCat.restrictScalars σ.hom).map (affineCotangentTensorIso σ hσ).hom

private theorem adjunction_unit_iso {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) {M N : C} (e : M ≅ N) {P : D}
    (q : F.obj M ⟶ P) :
    e.hom ≫ adj.unit.app N ≫ U.map (F.map e.inv ≫ q) = adj.unit.app M ≫ U.map q := by
  have h : e.hom ≫ adj.unit.app N = adj.unit.app M ≫ U.map (F.map e.hom) :=
    adj.unit.naturality e.hom
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [F.map_id, Category.id_comp]

/-- The affine conormal comparison preserves the actual geometric pullback unit
and sends an original ideal section to its original quotient class. -/
theorem affineConormalIso_unit {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (hσ : Function.Surjective σ) :
    (affineIdealIso σ).hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map σ)).unit.app
        (idealModule (Spec.map σ)) ≫
      (Scheme.Modules.pushforward (Spec.map σ)).map
        (relativeConormalAffineIdealPullbackIso (𝟙 A) σ hσ).hom ≫
      (tildePushforwardIso σ).hom.app (relativeConormalAffineModule (𝟙 A) σ hσ) =
    (tilde.functor A).map (affineClassMap σ hσ) := by
  let I := ModuleCat.of A (RingHom.ker σ.hom)
  let C := relativeConormalAffineModule (𝟙 A) σ hσ
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map σ)
  let q := (affineCotangentTensorIso σ hσ).hom
  have hl : (affineIdealIso σ).hom ≫ adj.unit.app (idealModule (Spec.map σ)) ≫
      (Scheme.Modules.pushforward (Spec.map σ)).map
        (relativeConormalAffineIdealPullbackIso (𝟙 A) σ hσ).hom =
      adj.unit.app (tilde I) ≫ (Scheme.Modules.pushforward (Spec.map σ)).map
        ((tildePullbackIso σ).hom.app I ≫ (tilde.functor B).map q) := by
    exact adjunction_unit_iso adj (affineIdealIso σ)
      ((tildePullbackIso σ).hom.app I ≫ (tilde.functor B).map q)
  have ht := congrArg (fun z => z ≫ (tildePushforwardIso σ).hom.app C) hl
  simp only [Category.assoc] at ht
  apply ht.trans
  simp only [Functor.map_comp, Category.assoc]
  have hn := (tildePushforwardIso σ).hom.naturality q
  change (Scheme.Modules.pushforward (Spec.map σ)).map ((tilde.functor B).map q) ≫
      (tildePushforwardIso σ).hom.app C =
    (tildePushforwardIso σ).hom.app ((ModuleCat.extendScalars σ.hom).obj I) ≫
      (tilde.functor A).map ((ModuleCat.restrictScalars σ.hom).map q) at hn
  rw [hn]
  calc
    _ = (tilde.functor A).map ((ModuleCat.extendRestrictScalarsAdj σ.hom).unit.app I) ≫
        (tilde.functor A).map ((ModuleCat.restrictScalars σ.hom).map q) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (tilde.functor A).map ((ModuleCat.restrictScalars σ.hom).map q))
        (tildePullbackIso_unit σ I)
    _ = _ := by rw [← Functor.map_comp]; rfl

theorem tildePushforwardIso_inv_top {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (M : ModuleCat B) (m : M) :
    ((tildePushforwardIso σ).inv.app M).val.app (op ⊤)
      (tilde.toOpen ((ModuleCat.restrictScalars σ.hom).obj M) ⊤ m) =
        tilde.toOpen M ⊤ m := by
  exact congrArg (fun q => q m) (tildePushforwardIso_inv_homEquiv σ M)

theorem tildePushforwardIso_hom_top {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (M : ModuleCat B) (m : M) :
    ((tildePushforwardIso σ).hom.app M).val.app (op ⊤) (tilde.toOpen M ⊤ m) =
      tilde.toOpen ((ModuleCat.restrictScalars σ.hom).obj M) ⊤ m := by
  have h := congrArg (fun q => q.val.app (op ⊤)
    (tilde.toOpen ((ModuleCat.restrictScalars σ.hom).obj M) ⊤ m))
      ((tildePushforwardIso σ).app M).inv_hom_id
  change ((tildePushforwardIso σ).hom.app M).val.app (op ⊤)
      (((tildePushforwardIso σ).inv.app M).val.app (op ⊤)
        (tilde.toOpen ((ModuleCat.restrictScalars σ.hom).obj M) ⊤ m)) = _ at h
  rw [tildePushforwardIso_inv_top] at h
  exact h

/- The section formula is kept abstract to avoid expanding a concrete cotangent
quotient while elaborating its consumer. -/
private theorem tilde_map_section {A : CommRingCat.{u}} {M N : ModuleCat A}
    (f : M ⟶ N) (U : (Spec A).Opens) (m : M) :
    ((tilde.functor A).map f).val.app (op U) (tilde.toOpen M U m) =
      tilde.toOpen N U (f m) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app f U) m

/-- On original top sections the affine geometric comparison is precisely
the native kernel-to-cotangent map. -/
theorem affineConormalIso_unit_top {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) :
    (relativeConormalAffineIdealPullbackIso (𝟙 A) σ hσ).hom.val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map σ)).unit.app
        (idealModule (Spec.map σ))).val.app (op ⊤)
          ((affineIdealIso σ).hom.val.app (op ⊤)
            (tilde.toOpen (ModuleCat.of A (RingHom.ker σ.hom)) ⊤ x))) =
      tilde.toOpen (relativeConormalAffineModule (𝟙 A) σ hσ) ⊤ (affineClassMap σ hσ x) := by
  let C := relativeConormalAffineModule (𝟙 A) σ hσ
  let : IsIso (((tildePushforwardIso σ).hom.app C).val.app (op ⊤)) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation (Spec A).ringCatSheaf (op ⊤)).map
      ((tildePushforwardIso σ).hom.app C)))
  apply (ConcreteCategory.bijective_of_isIso
    (((tildePushforwardIso σ).hom.app C).val.app (op ⊤))).1
  rw [tildePushforwardIso_hom_top]
  have h := congrArg (fun q => q.val.app (op ⊤)
      (tilde.toOpen (ModuleCat.of A (RingHom.ker σ.hom)) ⊤ x))
    (affineConormalIso_unit σ hσ)
  exact h.trans (tilde_map_section (affineClassMap σ hσ) ⊤ x)

theorem affineClassMap_apply {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) :
    affineClassMap σ hσ x = relativeConormalAffineClass (𝟙 A) σ hσ x := by
  let := (𝟙 A : A ⟶ A).hom.toAlgebra
  let := ((𝟙 A) ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let E := relativeConormalAffineExtension (𝟙 A) σ hσ
  change E.cotangentEquiv ((1 : B) ⊗ₜ[E.Ring] (show E.ker from x)) =
    Algebra.Extension.Cotangent.mk (show E.ker from x)
  exact (E.contangentEquiv_tmul 1 (show E.ker from x)).trans (one_smul B _)

/-- The positive coordinate difference is the original native Kähler differential. -/
theorem diagonalCotangentIso_difference (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (a : A) :
    (diagonalCotangentIso R A).hom
      (affineClassMap (diagonalTensorMultiplication R A)
        (diagonalTensorMultiplication_surjective R A)
        (diagonalDifferenceElement R A a)) =
      KaehlerDifferential.D R A a := by
  rw [affineClassMap_apply]
  rfl

theorem squareOpen_top (p : X ⟶ S) : squareOpen p ⊤ = ⊤ := by
  simp [squareOpen]

theorem pullbackSection_full (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    pullbackSection f M U (f ⁻¹ᵁ U) le_rfl m =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) m := by
  let N := (Scheme.Modules.pullback f).obj M
  change N.presheaf.map (𝟙 (op (f ⁻¹ᵁ U)))
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) m) = _
  rw [N.presheaf.map_id]
  rfl

/-- The same coordinate difference, placed on the top open of the diagonal ambient scheme. -/
def topIdealDifference (p : X ⟶ S) (a : Γ(X, ⊤)) : Γ(idealModule (pullback.diagonal p), ⊤) :=
  (idealModule (pullback.diagonal p)).val.map (homOfLE (squareOpen_top p).ge).op
    (idealDifferenceSection p ⊤ a)

theorem difference_top (p : X ⟶ S) (a : Γ(X, ⊤)) :
    difference p ⊤ a =
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.diagonal p)).unit.app
        (idealModule (pullback.diagonal p))).val.app (op ⊤) (topIdealDifference p a) := by
  have h := pullbackSection_naturality (pullback.diagonal p)
    (idealModule (pullback.diagonal p)) (V := ⊤) (V' := ⊤)
    (squareOpen_top p).ge le_rfl (squareOpenAlongDiagonal p ⊤) le_rfl
    (idealDifferenceSection p ⊤ a)
  change (conormal p).presheaf.map (𝟙 (op ⊤)) (difference p ⊤ a) =
    pullbackSection (pullback.diagonal p) (idealModule (pullback.diagonal p))
      ⊤ ⊤ le_rfl (topIdealDifference p a) at h
  rw [(conormal p).presheaf.map_id] at h
  exact h.trans (pullbackSection_full (pullback.diagonal p)
    (idealModule (pullback.diagonal p)) ⊤ (topIdealDifference p a))

private theorem appLE_top (f : X ⟶ Y) : f.appLE ⊤ ⊤ le_rfl = f.appTop := by
  change f.appTop ≫ X.presheaf.map (𝟙 (op ⊤)) = f.appTop
  rw [X.presheaf.map_id, Category.comp_id]

theorem topIdealDifference_inclusion (p : X ⟶ S) (a : Γ(X, ⊤)) :
    (idealInclusion (pullback.diagonal p)).val.app (op ⊤) (topIdealDifference p a) =
      (pullback.snd p p).appTop a - (pullback.fst p p).appTop a := by
  have h := PresheafOfModules.naturality_apply (idealInclusion (pullback.diagonal p)).val
    (homOfLE (squareOpen_top p).ge).op (idealDifferenceSection p ⊤ a)
  change (idealInclusion (pullback.diagonal p)).val.app (op ⊤) (topIdealDifference p a) =
    (Limits.pullback p p).presheaf.map (homOfLE (squareOpen_top p).ge).op
      ((idealInclusion (pullback.diagonal p)).val.app (op (squareOpen p ⊤))
        (idealDifferenceSection p ⊤ a)) at h
  rw [h, idealDifferenceSection_inclusion, map_sub]
  congr 1
  · have he := ((pullback.snd p p).appLE_map (U := ⊤) inf_le_right
      (homOfLE (squareOpen_top p).ge).op).trans (appLE_top (pullback.snd p p))
    exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Limits.pullback p p, ⊤) => q a) he
  · have he := ((pullback.fst p p).appLE_map (U := ⊤) inf_le_left
      (homOfLE (squareOpen_top p).ge).op).trans (appLE_top (pullback.fst p p))
    exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Limits.pullback p p, ⊤) => q a) he

private theorem spec_map_top {A B : CommRingCat.{u}} (σ : A ⟶ B) (a : A) :
    (Spec.map σ).appTop ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso B).inv (σ a) :=
  congrArg (fun q : A ⟶ Γ(Spec B, ⊤) => q a) (Scheme.ΓSpecIso_inv_naturality σ).symm

theorem affineIdealIso_top_inclusion {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (x : RingHom.ker σ.hom) :
    (idealInclusion (Spec.map σ)).val.app (op ⊤)
      ((affineIdealIso σ).hom.val.app (op ⊤)
        (tilde.toOpen (ModuleCat.of A (RingHom.ker σ.hom)) ⊤ x)) =
      (Scheme.ΓSpecIso A).inv x := by
  have h := congrArg (fun q => q.val.app (op ⊤)
    (tilde.toOpen (ModuleCat.of A (RingHom.ker σ.hom)) ⊤ x))
      (affineIdealIso_hom_inclusion σ)
  exact h.trans (tilde_map_section (ModuleCat.ofHom (RingHom.ker σ.hom).subtype) ⊤ x)

theorem idealPushforwardMap_inclusion_top {D D' : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (m : Γ(idealModule i, ⊤)) :
    (idealInclusion i').val.app (op ⊤)
      ((idealPushforwardMap i i' b a h).val.app (op ⊤) m) =
      b.appTop ((idealInclusion i).val.app (op ⊤) m) :=
  congrArg (fun q => q.val.app (op ⊤) m) (idealPushforwardMap_inclusion i i' b a h)

theorem specProduct_first_top (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (a : A) :
    (pullbackSpecIso R A A).inv.appTop
      ((pullback.fst (Spec.algebraMap R A) (Spec.algebraMap R A)).appTop
        ((Scheme.ΓSpecIso (.of A)).inv a)) =
      (Scheme.ΓSpecIso (.of (A ⊗[R] A))).inv (a ⊗ₜ[R] (1 : A)) := by
  have h := congrArg (fun q : Spec (.of (A ⊗[R] A)) ⟶ Spec (.of A) => q.appTop)
    (pullbackSpecIso_inv_fst R A A)
  exact (congrArg (fun q => q ((Scheme.ΓSpecIso (.of A)).inv a)) h).trans
    (spec_map_top (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := A))) a)

theorem specProduct_second_top (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (a : A) :
    (pullbackSpecIso R A A).inv.appTop
      ((pullback.snd (Spec.algebraMap R A) (Spec.algebraMap R A)).appTop
        ((Scheme.ΓSpecIso (.of A)).inv a)) =
      (Scheme.ΓSpecIso (.of (A ⊗[R] A))).inv ((1 : A) ⊗ₜ[R] a) := by
  have h := congrArg (fun q : Spec (.of (A ⊗[R] A)) ⟶ Spec (.of A) => q.appTop)
    (pullbackSpecIso_inv_snd R A A)
  exact (congrArg (fun q => q ((Scheme.ΓSpecIso (.of A)).inv a)) h).trans
    (spec_map_top (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A)).toRingHom) a)

theorem diagonalSpecSquare (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (𝟙 (Spec (.of A))) ≫ pullback.diagonal (Spec.algebraMap R A) =
      Spec.map (diagonalTensorMultiplication R A) ≫ (pullbackSpecIso R A A).inv := by
  rw [Category.id_comp]
  exact diagonal_SpecMap R A

/-- The actual coordinate-difference section becomes exactly the original
tensor-kernel element in the native affine presentation. -/
theorem specIdealDifference (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (a : A) :
    (idealPushforwardMap (pullback.diagonal (Spec.algebraMap R A))
      (Spec.map (diagonalTensorMultiplication R A)) (pullbackSpecIso R A A).inv
      (𝟙 (Spec (.of A))) (diagonalSpecSquare R A)).val.app (op ⊤)
        (topIdealDifference (Spec.algebraMap R A) ((Scheme.ΓSpecIso (.of A)).inv a)) =
      (affineIdealIso (diagonalTensorMultiplication R A)).hom.val.app (op ⊤)
        (tilde.toOpen (R := CommRingCat.of (A ⊗[R] A))
          (ModuleCat.of (A ⊗[R] A) (RingHom.ker (diagonalTensorMultiplication R A).hom)) ⊤
          (diagonalDifferenceElement R A a)) := by
  apply (idealSectionsEquiv (Spec.map (diagonalTensorMultiplication R A)) ⊤).injective
  apply Subtype.ext
  simp only [idealSectionsEquiv_val]
  rw [idealPushforwardMap_inclusion_top, affineIdealIso_top_inclusion,
    topIdealDifference_inclusion, map_sub, specProduct_second_top, specProduct_first_top]
  exact ((Scheme.ΓSpecIso (.of (A ⊗[R] A))).inv.hom.map_sub _ _).symm

theorem diagonalSpecFactorization (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    pullback.diagonal (Spec.algebraMap R A) =
      Spec.map (diagonalTensorMultiplication R A) ≫ (pullbackSpecIso R A A).inv := by
  simpa only [Category.id_comp] using diagonalSpecSquare R A

/-- The native product-scheme presentation of the actual affine diagonal conormal. -/
def conormalAlgebraAmbientIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    conormal (Spec.algebraMap R A) ≅
      (Scheme.Modules.pullback (Spec.map (diagonalTensorMultiplication R A))).obj
        (idealModule (Spec.map (diagonalTensorMultiplication R A))) :=
  conormalAmbientIso (pullback.diagonal (Spec.algebraMap R A))
    (Spec.map (diagonalTensorMultiplication R A)) (pullbackSpecIso R A A).inv
    (diagonalSpecFactorization R A)

theorem conormalAlgebraAmbientIso_hom (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : (conormalAlgebraAmbientIso R A).hom =
      (conormalAmbientIso (pullback.diagonal (Spec.algebraMap R A))
        (Spec.map (diagonalTensorMultiplication R A)) (pullbackSpecIso R A A).inv
        (diagonalSpecFactorization R A)).hom := rfl

theorem conormalAlgebraAmbientIso_unit_top (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (m : Γ(idealModule (pullback.diagonal (Spec.algebraMap R A)), ⊤)) :
    (conormalAlgebraAmbientIso R A).hom.val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.diagonal (Spec.algebraMap R A))).unit.app
        (idealModule (pullback.diagonal (Spec.algebraMap R A)))).val.app (op ⊤) m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (diagonalTensorMultiplication R A))).unit.app
      (idealModule (Spec.map (diagonalTensorMultiplication R A)))).val.app (op ⊤)
      ((idealPushforwardMap (pullback.diagonal (Spec.algebraMap R A))
        (Spec.map (diagonalTensorMultiplication R A)) (pullbackSpecIso R A A).inv
        (𝟙 (Spec (.of A))) (diagonalSpecSquare R A)).val.app (op ⊤) m) :=
by
  rw [conormalAlgebraAmbientIso_hom]
  exact conormalAmbientIso_unit_top (pullback.diagonal (Spec.algebraMap R A))
    (Spec.map (diagonalTensorMultiplication R A)) (pullbackSpecIso R A A).inv
    (diagonalSpecFactorization R A) m

/-- The actual affine diagonal conormal in its native Kähler-module presentation. -/
def conormalAlgebraIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    conormal (Spec.algebraMap R A) ≅ tilde (ModuleCat.of A (KaehlerDifferential R A)) :=
  conormalAlgebraAmbientIso R A ≪≫ affineDiagonalConormalIso R A

theorem conormalAlgebraIso_hom_apply (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (m : Γ(conormal (Spec.algebraMap R A), ⊤)) :
    (conormalAlgebraIso R A).hom.val.app (op ⊤) m =
      (affineDiagonalConormalIso R A).hom.val.app (op ⊤)
        ((conormalAlgebraAmbientIso R A).hom.val.app (op ⊤) m) := rfl

theorem conormalAlgebraAmbientIso_difference_top (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (a : A) :
    (conormalAlgebraAmbientIso R A).hom.val.app (op ⊤)
      (difference (Spec.algebraMap R A) ⊤ ((Scheme.ΓSpecIso (.of A)).inv a)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (diagonalTensorMultiplication R A))).unit.app
      (idealModule (Spec.map (diagonalTensorMultiplication R A)))).val.app (op ⊤)
      ((affineIdealIso (diagonalTensorMultiplication R A)).hom.val.app (op ⊤)
        (tilde.toOpen (R := CommRingCat.of (A ⊗[R] A))
          (ModuleCat.of (A ⊗[R] A) (RingHom.ker (diagonalTensorMultiplication R A).hom)) ⊤
          (diagonalDifferenceElement R A a))) := by
  have h₀ := congrArg ((conormalAlgebraAmbientIso R A).hom.val.app (op ⊤))
    (difference_top (Spec.algebraMap R A) ((Scheme.ΓSpecIso (.of A)).inv a))
  have h₁ := conormalAlgebraAmbientIso_unit_top R A
    (topIdealDifference (Spec.algebraMap R A) ((Scheme.ΓSpecIso (.of A)).inv a))
  have h₂ := congrArg
    (((Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (diagonalTensorMultiplication R A))).unit.app
      (idealModule (Spec.map (diagonalTensorMultiplication R A)))).val.app (op ⊤))
    (specIdealDifference R A a)
  exact h₀.trans (h₁.trans h₂)

/-- The actual affine comparison sends the canonical geometric coordinate
difference to the same original Kähler differential. -/
theorem affineDiagonalConormalIso_difference_top (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (a : A) :
    (affineDiagonalConormalIso R A).hom.val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (diagonalTensorMultiplication R A))).unit.app
          (idealModule (Spec.map (diagonalTensorMultiplication R A)))).val.app (op ⊤)
        ((affineIdealIso (diagonalTensorMultiplication R A)).hom.val.app (op ⊤)
          (tilde.toOpen (R := CommRingCat.of (A ⊗[R] A))
            (ModuleCat.of (A ⊗[R] A) (RingHom.ker (diagonalTensorMultiplication R A).hom)) ⊤
            (diagonalDifferenceElement R A a)))) =
      tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A (KaehlerDifferential R A)) ⊤
        (KaehlerDifferential.D R A a) := by
  let σ := diagonalTensorMultiplication R A
  let hs := diagonalTensorMultiplication_surjective R A
  let x := diagonalDifferenceElement R A a
  have h := affineConormalIso_unit_top σ hs x
  exact (congrArg
    (((tilde.functor (.of A)).map (diagonalCotangentIso R A).hom).val.app (op ⊤)) h).trans
      ((tilde_map_section (diagonalCotangentIso R A).hom ⊤ (affineClassMap σ hs x)).trans
        (congrArg (tilde.toOpen (R := CommRingCat.of A)
          (ModuleCat.of A (KaehlerDifferential R A)) ⊤) (diagonalCotangentIso_difference R A a)))

/-- The actual affine comparison sends the canonical geometric coordinate
difference to the same original Kähler differential. -/
theorem conormalAlgebraIso_difference_top (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (a : A) :
    (conormalAlgebraIso R A).hom.val.app (op ⊤)
      (difference (Spec.algebraMap R A) ⊤ ((Scheme.ΓSpecIso (.of A)).inv a)) =
      tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A (KaehlerDifferential R A)) ⊤
        (KaehlerDifferential.D R A a) := by
  exact (conormalAlgebraIso_hom_apply R A _).trans
    ((congrArg ((affineDiagonalConormalIso R A).hom.val.app (op ⊤))
      (conormalAlgebraAmbientIso_difference_top R A a)).trans
        (affineDiagonalConormalIso_difference_top R A a))


/-- Tilde morphisms are determined by their values on original global sections. -/
theorem tilde_hom_ext_top {A : CommRingCat.{u}} (M : ModuleCat A) (N : (Spec A).Modules)
    {f g : tilde M ⟶ N}
    (h : ∀ m : M, f.val.app (op ⊤) (tilde.toOpen M ⊤ m) =
      g.val.app (op ⊤) (tilde.toOpen M ⊤ m)) : f = g := by
  apply ((tilde.adjunction (R := A)).homEquiv M N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h

/-- The native affine differential comparison on original global generators. -/
theorem relativeDifferentialAffineIso_inv_top {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (a : A) :
    (relativeDifferentialAffineIso φ).inv.val.app (op ⊤)
      (tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤
        (CommRingCat.KaehlerDifferential.d a)) =
    (relativeDifferentialDerivation (Spec.map φ)).d ((Scheme.ΓSpecIso A).inv a) := by
  have h := relativeDifferentialAffineIso_inv_d φ 1 a
  have htop : PrimeSpectrum.basicOpen (1 : A) = ⊤ := PrimeSpectrum.basicOpen_one
  rw [htop] at h
  exact h

/-- Maps from affine relative differentials are determined by the original ring generators. -/
theorem relativeDifferentialAffine_hom_ext {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (M : (Spec A).Modules) {f g : relativeDifferentialSheaf (Spec.map φ) ⟶ M}
    (h : ∀ a : A,
      f.val.app (op ⊤) ((relativeDifferentialDerivation (Spec.map φ)).d
        ((Scheme.ΓSpecIso A).inv a)) =
      g.val.app (op ⊤) ((relativeDifferentialDerivation (Spec.map φ)).d
        ((Scheme.ΓSpecIso A).inv a))) : f = g := by
  apply (cancel_epi (relativeDifferentialAffineIso φ).inv).mp
  apply ((tilde.adjunction (R := A)).homEquiv _ M).injective
  apply ModuleCat.hom_ext
  let := φ.hom.toAlgebra
  let : Module R ((moduleSpecΓFunctor (R := A)).obj M) := Module.compHom _ φ.hom
  let : IsScalarTower R A ((moduleSpecΓFunctor (R := A)).obj M) :=
    IsScalarTower.of_compHom _ _ _
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change f.val.app (op ⊤) ((relativeDifferentialAffineIso φ).inv.val.app (op ⊤)
    (tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤
      (CommRingCat.KaehlerDifferential.d a))) =
    g.val.app (op ⊤) ((relativeDifferentialAffineIso φ).inv.val.app (op ⊤)
      (tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤
        (CommRingCat.KaehlerDifferential.d a)))
  rw [relativeDifferentialAffineIso_inv_top]
  exact h a



/-- The original Kähler module with its algebra structure made an explicit argument. -/
def kaehlerModuleWith (R A : Type u) [CommRing R] [CommRing A]
    (alg : Algebra R A) : ModuleCat A := by
  let := alg
  exact ModuleCat.of A (KaehlerDifferential R A)

/-- The original universal differential in the explicitly parameterized Kähler module. -/
def kaehlerDWith (R A : Type u) [CommRing R] [CommRing A]
    (alg : Algebra R A) (a : A) : kaehlerModuleWith R A alg := by
  let := alg
  exact KaehlerDifferential.D R A a

/-- Transport along equality of algebra structures preserves the original differential. -/
theorem kaehlerModuleWith_transport_d (R A : Type u) [CommRing R] [CommRing A]
    (alg alg' : Algebra R A) (h : alg = alg') (a : A) :
    (eqToIso (congrArg (kaehlerModuleWith R A) h)).hom (kaehlerDWith R A alg a) =
      kaehlerDWith R A alg' a := by
  subst alg'
  rfl

/-- The native ring-map Kähler object and the original algebra Kähler module,
using the actual equality of algebra structures. -/
def algebraKaehlerIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap R A)) ≅
      ModuleCat.of A (KaehlerDifferential R A) :=
  eqToIso (congrArg (kaehlerModuleWith R A) (toAlgebra_algebraMap (R := R) (S := A)))

/-- The module comparison carries the same original universal differential. -/
theorem algebraKaehlerIso_d (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (a : A) :
    (algebraKaehlerIso R A).hom
      (CommRingCat.KaehlerDifferential.d (f := CommRingCat.ofHom (algebraMap R A)) a) =
        KaehlerDifferential.D R A a :=
  kaehlerModuleWith_transport_d R A (algebraMap R A).toAlgebra
    (inferInstanceAs (Algebra R A)) (toAlgebra_algebraMap (R := R) (S := A)) a

/-- The native affine differential comparison on original global generators. -/
theorem relativeDifferentialAffineIso_hom_top {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (a : A) :
    (relativeDifferentialAffineIso φ).hom.val.app (op ⊤)
      ((relativeDifferentialDerivation (Spec.map φ)).d ((Scheme.ΓSpecIso A).inv a)) =
    tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤
      (CommRingCat.KaehlerDifferential.d a) := by
  have h := relativeDifferentialAffineIso_hom_d φ 1 a
  have htop : PrimeSpectrum.basicOpen (1 : A) = ⊤ := PrimeSpectrum.basicOpen_one
  rw [htop] at h
  exact h

/-- Native relative differentials in the original algebra presentation. The scalar
comparison is an actual module isomorphism, rather than a bundled definitional conversion. -/
def relativeDifferentialAlgebraIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    relativeDifferentialSheaf (Spec.algebraMap R A) ≅
      tilde (R := CommRingCat.of A) (ModuleCat.of A (KaehlerDifferential R A)) :=
  relativeDifferentialAffineIso (CommRingCat.ofHom (algebraMap R A)) ≪≫
    (tilde.functor (.of A)).mapIso (algebraKaehlerIso R A)

theorem relativeDifferentialAlgebraIso_hom (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    (relativeDifferentialAlgebraIso R A).hom =
      (relativeDifferentialAffineIso (CommRingCat.ofHom (algebraMap R A))).hom ≫
        (tilde.functor (.of A)).map (algebraKaehlerIso R A).hom := rfl

/-- The original affine differential is carried to the original raw Kähler generator. -/
theorem relativeDifferentialAlgebraIso_hom_top (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (a : A) :
    (relativeDifferentialAlgebraIso R A).hom.val.app (op ⊤)
      ((relativeDifferentialDerivation (Spec.algebraMap R A)).d
        ((Scheme.ΓSpecIso (.of A)).inv a)) =
      tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A (KaehlerDifferential R A)) ⊤
        (KaehlerDifferential.D R A a) := by
  rw [relativeDifferentialAlgebraIso_hom, module_comp_apply]
  have h := relativeDifferentialAffineIso_hom_top (R := .of R) (A := .of A)
    (CommRingCat.ofHom (algebraMap R A)) a
  exact (congrArg (((tilde.functor (.of A)).map (algebraKaehlerIso R A).hom).val.app
    (op ⊤)) h).trans
    ((tilde_map_section (algebraKaehlerIso R A).hom ⊤
      (CommRingCat.KaehlerDifferential.d
        (f := CommRingCat.ofHom (algebraMap R A)) a)).trans
      (congrArg (tilde.toOpen (R := CommRingCat.of A)
        (ModuleCat.of A (KaehlerDifferential R A)) ⊤) (algebraKaehlerIso_d R A a)))

/-- An affine map out of the conormal is compared with a differential map by its
values on the original coordinate differences. -/
theorem differentialToConormal_specMap_comp_eq {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (M : (Spec A).Modules) (f : conormal (Spec.map φ) ⟶ M)
    (g : relativeDifferentialSheaf (Spec.map φ) ⟶ M)
    (h : ∀ a : A,
      f.val.app (op ⊤) (difference (Spec.map φ) ⊤ ((Scheme.ΓSpecIso A).inv a)) =
      g.val.app (op ⊤) ((relativeDifferentialDerivation (Spec.map φ)).d
        ((Scheme.ΓSpecIso A).inv a))) :
    differentialToConormal (Spec.map φ) ≫ f = g := by
  apply relativeDifferentialAffine_hom_ext φ
  intro a
  rw [module_comp_apply, differentialToConormal_d]
  exact h a

/-- Two actual affine presentations preserving the original generators make the
canonical differential-to-conormal map invertible. -/
theorem differentialToConormal_specMap_isIso_of_generators {R A : CommRingCat.{u}}
    (φ : R ⟶ A) (M : (Spec A).Modules) (eC : conormal (Spec.map φ) ≅ M)
    (eD : relativeDifferentialSheaf (Spec.map φ) ≅ M) (d : A → Γ(M, ⊤))
    (hC : ∀ a : A,
      eC.hom.val.app (op ⊤) (difference (Spec.map φ) ⊤ ((Scheme.ΓSpecIso A).inv a)) = d a)
    (hD : ∀ a : A,
      eD.hom.val.app (op ⊤) ((relativeDifferentialDerivation (Spec.map φ)).d
        ((Scheme.ΓSpecIso A).inv a)) = d a) :
    IsIso (differentialToConormal (Spec.map φ)) := by
  have he : differentialToConormal (Spec.map φ) ≫ eC.hom = eD.hom :=
    differentialToConormal_specMap_comp_eq φ M eC.hom eD.hom
      (fun a => (hC a).trans (hD a).symm)
  have : IsIso (differentialToConormal (Spec.map φ) ≫ eC.hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ eC.hom

/-- Transport the affine generator criterion to the original algebra-map presentation
while its module and comparison maps are still abstract. -/
theorem differentialToConormal_algebra_isIso_of_generators (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] (M : (Spec (.of A)).Modules)
    (eC : conormal (Spec.algebraMap R A) ≅ M)
    (eD : relativeDifferentialSheaf (Spec.algebraMap R A) ≅ M)
    (d : A → Γ(M, ⊤))
    (hC : ∀ a : A,
      eC.hom.val.app (op ⊤) (difference (Spec.algebraMap R A) ⊤
        ((Scheme.ΓSpecIso (.of A)).inv a)) = d a)
    (hD : ∀ a : A,
      eD.hom.val.app (op ⊤) ((relativeDifferentialDerivation (Spec.algebraMap R A)).d
        ((Scheme.ΓSpecIso (.of A)).inv a)) = d a) :
    IsIso (differentialToConormal (Spec.algebraMap R A)) :=
  differentialToConormal_specMap_isIso_of_generators (CommRingCat.ofHom (algebraMap R A))
    M eC eD d hC hD

/-- The canonical conormal map is invertible for the original spectrum algebra map. -/
theorem differentialToConormal_algebra_isIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : IsIso (differentialToConormal (Spec.algebraMap R A)) :=
  differentialToConormal_algebra_isIso_of_generators R A
    (tilde (R := CommRingCat.of A) (ModuleCat.of A (KaehlerDifferential R A)))
    (conormalAlgebraIso R A) (relativeDifferentialAlgebraIso R A)
    (fun a => tilde.toOpen (R := CommRingCat.of A)
      (ModuleCat.of A (KaehlerDifferential R A)) ⊤ (KaehlerDifferential.D R A a))
    (conormalAlgebraIso_difference_top R A) (relativeDifferentialAlgebraIso_hom_top R A)

theorem specAlgebraMap_eq {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    letI := φ.hom.toAlgebra
    Spec.algebraMap R A = Spec.map φ := rfl

theorem differentialToConormal_isIso_of_eq {p q : X ⟶ S} (h : p = q)
    (hp : IsIso (differentialToConormal p)) : IsIso (differentialToConormal q) := by
  subst q
  exact hp

/-- The affine result concerns the original spectrum morphism of every ring map. -/
instance differentialToConormal_specMap_isIso {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    IsIso (differentialToConormal (Spec.map φ)) := by
  rcases R with ⟨R⟩
  rcases A with ⟨A⟩
  let := φ.hom.toAlgebra
  exact differentialToConormal_isIso_of_eq (specAlgebraMap_eq φ)
    (differentialToConormal_algebra_isIso R A)

/-- The actual affine diagonal conormal and native relative differential sheaf agree. -/
def conormalSpecIso {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    conormal (Spec.map φ) ≅ relativeDifferentialSheaf (Spec.map φ) :=
  (asIso (differentialToConormal (Spec.map φ))).symm

/-- The native ring-map Kähler presentation uses the same canonical comparison. -/
def conormalSpecAlgebraIso {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    conormal (Spec.map φ) ≅ tilde (CommRingCat.KaehlerDifferential φ) :=
  conormalSpecIso φ ≪≫ relativeDifferentialAffineIso φ

end AlgebraicGeometry.Scheme.Modules.Differentials.Diagonal
