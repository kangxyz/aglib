/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethAffine
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent

/-!
# Flat base change identifies the original affine Kunneth map

The normalized tensor map is the original module-cohomology scalar-extension
mate followed by the original pullback-unit coefficient isomorphism. Its whole
comparison with the original external product is proved before bijectivity.

For X qcqs over a field and Y affine, every degree of the original finite
antidiagonal Kunneth map is bijective. Gamma(Y) is an arbitrary commutative
algebra, including the zero ring; no Noetherian, finite-type or proper
hypothesis is used. The product and cohomology remain the original objects.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original module pullback, normalized by its original unit coefficient
isomorphism, is the original structure-sheaf cohomology pullback. -/
theorem moduleCohomologyMapAlong_pullbackUnitIso {U V : Scheme.{u}} (p : V ⟶ U)
    (n : ℕ) (x : Sheaf.H.{u + 1} (structureAddSheaf U) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf.{u} V.ringCatSheaf).map (pullbackUnitIso p).hom) n
      (moduleCohomologyMapAlong p ((pullbackPushforwardAdjunction p).unit.app
        (SheafOfModules.unit U.ringCatSheaf)) n x) =
      structureCohomologyPullback p n x := by
  change Sheaf.H.map _ n (zariskiCohomologyMap p (structureAddSheaf U)
    (moduleAddSheaf V ((Scheme.Modules.pullback p).obj
      (SheafOfModules.unit U.ringCatSheaf)))
    ((modulePullbackAdditiveComparison p).app (SheafOfModules.unit U.ringCatSheaf)) n x) = _
  rw [← zariskiCohomologyMap_postcomp, modulePullbackAdditiveComparison_unit]
  rfl

/-- The canonical affine isomorphism normalizes the actual structural scalar
map after an arbitrary preceding scheme morphism. -/
theorem isoSpec_comp_scalar {U V : Scheme.{u}} [IsAffine V] (p : U ⟶ V) :
    (p ≫ V.isoSpec.hom).appTop.hom.comp (Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom =
      p.appTop.hom := by
  apply RingHom.ext
  intro s
  change p.appTop (V.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(V, ⊤)).inv s)) = p.appTop s
  simp only [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]

section UnitTensor

variable {R S : Type u} [CommRing R] [CommRing S] {U V : Scheme.{u}}

/-- The actual scalar-extension mate with its original pullback-unit
coefficient normalization, for arbitrary compatible structural ring maps. -/
def unitCohomologyTensorMap (p : V ⟶ U) (σ : R →+* S)
    (α : R →+* Γ(U, ⊤)) (β : S →+* Γ(V, ⊤))
    (hs : p.appTop.hom.comp α = β.comp σ) (n : ℕ) :
    letI : Module R (Sheaf.H.{u + 1} (structureAddSheaf U) n) :=
      moduleCohomologyModuleOfHom U α (SheafOfModules.unit U.ringCatSheaf) n
    letI : Module S (Sheaf.H.{u + 1} (structureAddSheaf V) n) :=
      moduleCohomologyModuleOfHom V β (SheafOfModules.unit V.ringCatSheaf) n
    (ModuleCat.extendScalars σ).obj
        (ModuleCat.of R (Sheaf.H.{u + 1} (structureAddSheaf U) n)) ⟶
      ModuleCat.of S (Sheaf.H.{u + 1} (structureAddSheaf V) n) := by
  letI : Module R (Sheaf.H.{u + 1} (structureAddSheaf U) n) :=
    moduleCohomologyModuleOfHom U α (SheafOfModules.unit U.ringCatSheaf) n
  letI : Module S (Sheaf.H.{u + 1} (structureAddSheaf V) n) :=
    moduleCohomologyModuleOfHom V β (SheafOfModules.unit V.ringCatSheaf) n
  exact moduleCohomologyTensorMap p σ α β hs
      ((pullbackPushforwardAdjunction p).unit.app
        (SheafOfModules.unit U.ringCatSheaf)) n ≫
    (moduleCohomologyIsoOfHom V β (pullbackUnitIso p) n).hom

/-- The normalized original map retains the original unit pure tensor. -/
theorem unitCohomologyTensorMap_one_tmul (p : V ⟶ U) (σ : R →+* S)
    (α : R →+* Γ(U, ⊤)) (β : S →+* Γ(V, ⊤))
    (hs : p.appTop.hom.comp α = β.comp σ) (n : ℕ)
    (x : Sheaf.H.{u + 1} (structureAddSheaf U) n) :
    letI : Module R (Sheaf.H.{u + 1} (structureAddSheaf U) n) :=
      moduleCohomologyModuleOfHom U α (SheafOfModules.unit U.ringCatSheaf) n
    letI : Module S (Sheaf.H.{u + 1} (structureAddSheaf V) n) :=
      moduleCohomologyModuleOfHom V β (SheafOfModules.unit V.ringCatSheaf) n
    unitCohomologyTensorMap p σ α β hs n ((1 : S) ⊗ₜ[R,σ] x) =
      structureCohomologyPullback p n x := by
  let : Module R (Sheaf.H.{u + 1} (structureAddSheaf U) n) :=
    moduleCohomologyModuleOfHom U α (SheafOfModules.unit U.ringCatSheaf) n
  let : Module S (Sheaf.H.{u + 1} (structureAddSheaf V) n) :=
    moduleCohomologyModuleOfHom V β (SheafOfModules.unit V.ringCatSheaf) n
  let a : (ModuleCat.extendScalars σ).obj
      (ModuleCat.of R (Sheaf.H.{u + 1} (structureAddSheaf U) n)) := (1 : S) ⊗ₜ[R,σ] x
  have hu := moduleCohomologyTensorMap_one_tmul p σ α β hs
    ((pullbackPushforwardAdjunction p).unit.app
      (SheafOfModules.unit U.ringCatSheaf)) n x
  have hc := moduleCohomologyIsoOfHom_hom_apply V β (pullbackUnitIso p) n
    (moduleCohomologyTensorMap p σ α β hs
      ((pullbackPushforwardAdjunction p).unit.app
        (SheafOfModules.unit U.ringCatSheaf)) n a)
  have hm := congrArg
    (fun y : Sheaf.H.{u + 1} (moduleAddSheaf V
        ((Scheme.Modules.pullback p).obj (SheafOfModules.unit U.ringCatSheaf))) n =>
      Sheaf.H.map ((SheafOfModules.toSheaf.{u} V.ringCatSheaf).map
        (pullbackUnitIso p).hom) n y) hu
  have hn := moduleCohomologyMapAlong_pullbackUnitIso p n x
  have hfinal := hc.trans (hm.trans hn)
  exact hfinal

/-- S-linearity gives the original global-section coefficient action on
every pure tensor of the same normalized map. -/
theorem unitCohomologyTensorMap_tmul (p : V ⟶ U) (σ : R →+* S)
    (α : R →+* Γ(U, ⊤)) (β : S →+* Γ(V, ⊤))
    (hs : p.appTop.hom.comp α = β.comp σ) (n : ℕ) (s : S)
    (x : Sheaf.H.{u + 1} (structureAddSheaf U) n) :
    letI : Module R (Sheaf.H.{u + 1} (structureAddSheaf U) n) :=
      moduleCohomologyModuleOfHom U α (SheafOfModules.unit U.ringCatSheaf) n
    letI : Module S (Sheaf.H.{u + 1} (structureAddSheaf V) n) :=
      moduleCohomologyModuleOfHom V β (SheafOfModules.unit V.ringCatSheaf) n
    unitCohomologyTensorMap p σ α β hs n (s ⊗ₜ[R,σ] x) =
      Sheaf.H.map (moduleScalarOfGlobal V (SheafOfModules.unit V.ringCatSheaf) (β s)) n
        (structureCohomologyPullback p n x) := by
  let : Module R (Sheaf.H.{u + 1} (structureAddSheaf U) n) :=
    moduleCohomologyModuleOfHom U α (SheafOfModules.unit U.ringCatSheaf) n
  let : Module S (Sheaf.H.{u + 1} (structureAddSheaf V) n) :=
    moduleCohomologyModuleOfHom V β (SheafOfModules.unit V.ringCatSheaf) n
  have htensor := ModuleCat.ExtendScalars.smul_tmul σ
    (M := ModuleCat.of R (Sheaf.H.{u + 1} (structureAddSheaf U) n)) s (1 : S) x
  have hone := congrArg
    (fun t : S => (t ⊗ₜ[R,σ] x : (ModuleCat.extendScalars σ).obj
      (ModuleCat.of R (Sheaf.H.{u + 1} (structureAddSheaf U) n)))) (mul_one s)
  have ht := hone.symm.trans htensor.symm
  have hmap := congrArg (unitCohomologyTensorMap p σ α β hs n) ht
  have hlinear := (unitCohomologyTensorMap p σ α β hs n).hom.map_smul
    s ((1 : S) ⊗ₜ[R,σ] x)
  have hunit := unitCohomologyTensorMap_one_tmul p σ α β hs n x
  have hfinal := (hmap.trans hlinear).trans
    (congrArg (fun y : Sheaf.H.{u + 1} (structureAddSheaf V) n => s • y) hunit)
  exact hfinal

/-- Native qcqs flat base change makes that same unit-normalized map
invertible, on the actual supplied cartesian square. -/
theorem unitCohomologyTensorMap_isIso_of_isPullback
    (p : V ⟶ U) (q : V ⟶ Spec (CommRingCat.of S))
    (f : U ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    (hflat : σ.Flat) (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    IsIso (unitCohomologyTensorMap p σ α β
      (moduleSectionsBaseChangeScalars p q f σ h.w) n) := by
  let := Scheme.Modules.isQuasicoherent_unit U
  let := moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback p q f σ h hflat
    (SheafOfModules.unit U.ringCatSheaf) n
  dsimp only [unitCohomologyTensorMap]
  infer_instance

end UnitTensor

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

/-- The original structural morphism factors through the canonical global
section morphism by the original constants homomorphism. -/
theorem structureMorphism_toSpec_constants :
    Y.hom = Y.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (constants Y)) := by
  change Y.hom = Y.left.toSpecΓ ≫
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Y.hom.appTop)
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The original constants homomorphism is flat over a field, also when
the global-section ring is the zero ring. -/
theorem constants_flat : (constants Y).Flat := by
  let := (constants Y).toAlgebra
  change Module.Flat k Γ(Y.left, ⊤)
  infer_instance

/-- The canonical source equivalence uses the original H0 comparison and
tensor commutativity, with the actual constants action on Gamma(Y). -/
def structureAffineSourceEquiv (n : ℕ) :
    letI : Module k Γ(Y.left, ⊤) := (constants Y).toModule
    structureCohomology k X n ⊗[k] structureCohomology k Y 0 ≃ₗ[k]
      Γ(Y.left, ⊤) ⊗[k] structureCohomology k X n := by
  letI : Module k Γ(Y.left, ⊤) := (constants Y).toModule
  exact (TensorProduct.congr (LinearEquiv.refl k (structureCohomology k X n))
      (Scheme.structureH0Equiv Y)).trans
    (TensorProduct.comm k (structureCohomology k X n) Γ(Y.left, ⊤))

/-- Its whole pure-tensor formula keeps the original global section. -/
theorem structureAffineSourceEquiv_tmul (n : ℕ)
    (x : structureCohomology k X n) (y : structureCohomology k Y 0) :
    letI : Module k Γ(Y.left, ⊤) := (constants Y).toModule
    structureAffineSourceEquiv X Y n (x ⊗ₜ[k] y) =
      Scheme.structureH0Equiv Y y ⊗ₜ[k] x := by
  let : Module k Γ(Y.left, ⊤) := (constants Y).toModule
  simp only [structureAffineSourceEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, TensorProduct.comm_tmul]

variable [IsAffine Y.left]

/-- The original product square, using only the canonical affine
isomorphism at the actual scalar-comparison boundary. -/
theorem structureProduct_isoSpec_isPullback :
    IsPullback (fst X Y).left ((snd X Y).left ≫ Y.left.isoSpec.hom)
      X.hom (Spec.map (CommRingCat.ofHom (constants Y))) := by
  apply (IsPullback.of_hasPullback X.hom Y.hom).of_iso
    (Iso.refl _) (Iso.refl _) Y.left.isoSpec (Iso.refl _)
  · simp
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id, Scheme.isoSpec_hom] using
      structureMorphism_toSpec_constants Y

/-- Native scalar extension on the original product, followed by the
original pullback-unit coefficient isomorphism. -/
def structureAffineTensorMap (n : ℕ) :
    let S : Type u := Γ(Y.left, ⊤)
    let β := ((snd X Y).left ≫ Y.left.isoSpec.hom).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    letI : Module S (structureCohomology k (X ⊗ Y) n) :=
      moduleCohomologyModuleOfHom (X ⊗ Y).left β
        (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
    (ModuleCat.extendScalars (constants Y)).obj
        (ModuleCat.of k (structureCohomology k X n)) ⟶
      ModuleCat.of S (structureCohomology k (X ⊗ Y) n) := by
  let S : Type u := Γ(Y.left, ⊤)
  let p := (fst X Y).left
  let q := (snd X Y).left ≫ Y.left.isoSpec.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  exact unitCohomologyTensorMap p (constants Y) (constants X) β
    (moduleSectionsBaseChangeScalars p q X.hom (constants Y)
      (structureProduct_isoSpec_isPullback X Y).w) n

/-- The original affine tensor map on every pure tensor, before any
bijectivity assertion. Its section acts on the original p1 pullback. -/
theorem structureAffineTensorMap_tmul (n : ℕ) (s : Γ(Y.left, ⊤))
    (x : structureCohomology k X n) :
    structureAffineTensorMap X Y n (s ⊗ₜ[k,constants Y] x) =
      Sheaf.H.map
        (moduleScalarOfGlobal (X ⊗ Y).left (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf)
          ((snd X Y).left.appTop s)) n
        (structureCohomologyPullbackLinear (fst X Y) n x) := by
  let S : Type u := Γ(Y.left, ⊤)
  let p := (fst X Y).left
  let q := (snd X Y).left ≫ Y.left.isoSpec.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  have h := unitCohomologyTensorMap_tmul p (constants Y) (constants X) β
    (moduleSectionsBaseChangeScalars p q X.hom (constants Y)
      (structureProduct_isoSpec_isPullback X Y).w) n s x
  have hs : β s = (snd X Y).left.appTop s :=
    congrArg (fun t : Γ(Y.left, ⊤) →+* Γ((X ⊗ Y).left, ⊤) => t s)
      (isoSpec_comp_scalar (snd X Y).left)
  have hfinal := h.trans (congrArg
    (fun t : Γ((X ⊗ Y).left, ⊤) => Sheaf.H.map
      (moduleScalarOfGlobal (X ⊗ Y).left (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) t)
      n (structureCohomologyPullback p n x)) hs)
  exact hfinal

/-- The WHOLE original external tensor map equals the normalized original
scalar-extension mate after the canonical source equivalence. -/
theorem structureAffineTensorMap_sourceEquiv (n : ℕ) :
    (fun z : structureCohomology k X n ⊗[k] structureCohomology k Y 0 =>
      structureAffineTensorMap X Y n (structureAffineSourceEquiv X Y n z)) =
      fun z => structureExternalTensor X Y (Nat.add_zero n) z := by
  let : Module k Γ(Y.left, ⊤) := (constants Y).toModule
  let S : Type u := Γ(Y.left, ⊤)
  let β := ((snd X Y).left ≫ Y.left.isoSpec.hom).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let : Module S (structureCohomology k (X ⊗ Y) n) :=
    moduleCohomologyModuleOfHom (X ⊗ Y).left β
      (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
  let E : (ModuleCat.extendScalars (constants Y)).obj
      (ModuleCat.of k (structureCohomology k X n)) ⟶
      ModuleCat.of S (structureCohomology k (X ⊗ Y) n) := structureAffineTensorMap X Y n
  funext z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    have hφ := structureAffineSourceEquiv_tmul X Y n x y
    have he := structureAffineTensorMap_tmul X Y n (Scheme.structureH0Equiv Y y) x
    have hκ := structureExternalTensor_tmul X Y (Nat.add_zero n) x y
    have hcup := structureExternalCup_zero_right X Y x y
    have hleft := congrArg (structureAffineTensorMap X Y n) hφ
    have hfinal := (hleft.trans he).trans (hκ.trans hcup).symm
    exact hfinal
  | add a b ha hb =>
    have hφ := (structureAffineSourceEquiv X Y n).map_add a b
    have he := E.hom.map_add
      (structureAffineSourceEquiv X Y n a) (structureAffineSourceEquiv X Y n b)
    have hκ := (structureExternalTensor X Y (Nat.add_zero n)).map_add a b
    have hleft := congrArg (structureAffineTensorMap X Y n) hφ
    have hsum := congrArg₂ (fun x y : structureCohomology k (X ⊗ Y) n => x + y) ha hb
    have hfinal := ((hleft.trans he).trans hsum).trans hκ.symm
    exact hfinal

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]

/-- Genuine qcqs flat base change proves invertibility of the same
normalized tensor map, with Gamma(Y) only a commutative algebra. -/
theorem structureAffineTensorMap_isIso (n : ℕ) :
    IsIso (structureAffineTensorMap X Y n) := by
  exact unitCohomologyTensorMap_isIso_of_isPullback
    (fst X Y).left ((snd X Y).left ≫ Y.left.isoSpec.hom) X.hom (constants Y)
    (structureProduct_isoSpec_isPullback X Y) (constants_flat Y) n

/-- The original degree-(n,0) external tensor map is bijective when
X is qcqs over the field and Y is affine. -/
theorem structureExternalTensor_bijective_of_isAffine (n : ℕ) :
    Function.Bijective (structureExternalTensor X Y (Nat.add_zero n)) := by
  let := structureAffineTensorMap_isIso X Y n
  have he := ConcreteCategory.bijective_of_isIso (structureAffineTensorMap X Y n)
  have hφ := (structureAffineSourceEquiv X Y n).bijective
  have h := structureAffineTensorMap_sourceEquiv X Y n
  exact Eq.mp (congrArg Function.Bijective h) (he.comp hφ)

/-- The full original finite-antidiagonal Kunneth map is bijective for
a qcqs first factor and an affine second factor over any field. -/
theorem structureKunnethMap_bijective_of_isAffine (n : ℕ) :
    Function.Bijective (structureKunnethMap X Y n) :=
  (structureKunnethMap_bijective_iff_of_isAffine X Y n).mpr
    (structureExternalTensor_bijective_of_isAffine X Y n)

end AlgebraicGeometry.Scheme.Cohomology
