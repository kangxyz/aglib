/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FiniteEtale.InertiaTorsor
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic
public import Aglib.CategoryTheory.TorsorAction.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Literal affine normalization torsors

The finite etale cover uses the existing `Scheme.FiniteEtale` type and the
literal spectrum of the integral closure. Its pullback transporter is the
actual pair of first projection and coaction. An ordinary supplied Hopf algebra
with cocommutative comultiplication constructs the coefficient group through
Mathlib `hopfSpec` and the existing `CategoryTheory.TorsorAction` on every
scheme-valued test object. No coefficient Hopf realization is inferred.

Source slices: `Normalization.SpecTorsor`, the generic pullback portion of
`Normalization.SpecPullbackTorsor`, and `Normalization.H1SchemeTorsor:53–350`,
at R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Pure action-evaluation algebra is in the new lower `FiniteEtale.InertiaTorsor`
leaf. Existing generic relative normalization remains owned by
`Scheme.FiniteEtale.GenericNormalization`; its implementation is unchanged.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.MonObj
open Algebra.FiniteEtale.GenericMaps Algebra.FiniteEtale.TorsorExtension

namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor

universe u

section SpecConsequences

/-- The original structural ring map, as an actual affine scheme morphism.

Supporting helper for the module's explicit C3 source mapping. -/
abbrev structureMap (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :=
  Spec.map (CommRingCat.ofHom (algebraMap R B))

variable (R B H : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [CommRing H] [Algebra R H] {ε : H →ₐ[R] R} {Δ : H →ₐ[R] H ⊗[R] H}

/-- Faithful flatness is consumed from the DERIVED algebraic torsor output,
not passed as an extra final model hypothesis.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: supplied AlgebraicTorsorData and etale B/R give a flat, surjective
etale affine cover. -/
theorem spec_cover (T : AlgebraicTorsorData R B H ε Δ) [Algebra.Etale R B] :
    Etale (structureMap R B) ∧ Flat (structureMap R B) ∧
      Surjective (structureMap R B) := by
  have hf : (algebraMap R B).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr T.faithfullyFlat
  have hfs := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R B))).mpr hf
  have he : Etale (structureMap R B) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  exact ⟨he, hfs⟩

/-- The same actual Spec(B) is a finite etale surjective cover.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: the affine cover with supplied AlgebraicTorsorData and finite etale
B/R. -/
theorem spec_finite_cover (T : AlgebraicTorsorData R B H ε Δ)
    [Module.Finite R B] [Algebra.Etale R B] :
    IsFinite (structureMap R B) ∧ Etale (structureMap R B) ∧
      Flat (structureMap R B) ∧ Surjective (structureMap R B) := by
  have hfin : IsFinite (structureMap R B) :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R B))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  exact ⟨hfin, spec_cover R B H T⟩

/-- The actual affine transporter is a scheme isomorphism. Its product
objects are literally Spec(B tensor B) and Spec(B tensor H).

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: the actual Spec(tensor) transporter isomorphism from supplied
AlgebraicTorsorData. -/
theorem spec_transporter_isIso (T : AlgebraicTorsorData R B H ε Δ) :
    IsIso (Spec.map (CommRingCat.ofHom
      (Algebra.FiniteEtale.GenericMaps.transporter R B H T.coaction.coact).toRingHom)) := by
  let e := AlgEquiv.ofBijective
    (Algebra.FiniteEtale.GenericMaps.transporter R B H T.coaction.coact) T.transporter_bijective
  let i : CommRingCat.of (B ⊗[R] B) ≅ CommRingCat.of (B ⊗[R] H) :=
    { hom := CommRingCat.ofHom e.toRingEquiv.toRingHom
      inv := CommRingCat.ofHom e.symm.toRingEquiv.toRingHom
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        exact e.left_inv x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro x
        exact e.right_inv x }
  change IsIso (Scheme.Spec.mapIso i.op).hom
  infer_instance


end SpecConsequences

section Pullback

variable (R B H : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [CommRing H] [Algebra R H]

/-- The actual affine coaction morphism on the actual product Spec(B) x Spec(H).

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: the action-shaped affine morphism defined by a supplied algebra map,
without assuming its coaction laws here. -/
def specCoaction (δ : B →ₐ[R] B ⊗[R] H) :
    pullback (structureMap R B) (structureMap R H) ⟶ Spec (.of B) :=
  (pullbackSpecIso R B H).hom ≫ Spec.map (CommRingCat.ofHom δ.toRingHom)

/-- The coordinate transporter on the actual fibre products.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: the coordinate transporter on the actual categorical fibre products. -/
def specTransporter (δ : B →ₐ[R] B ⊗[R] H) :
    pullback (structureMap R B) (structureMap R H) ⟶
      pullback (structureMap R B) (structureMap R B) :=
  (pullbackSpecIso R B H).hom ≫
    Spec.map (CommRingCat.ofHom (transporter R B H δ).toRingHom) ≫
      (pullbackSpecIso R B B).inv

/-- The first transporter component is the actual first projection.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: identification of the transporter's first categorical component. -/
theorem specTransporter_fst (δ : B →ₐ[R] B ⊗[R] H) :
    specTransporter R B H δ ≫ pullback.fst _ _ =
      pullback.fst (structureMap R B) (structureMap R H) := by
  have h : (transporter R B H δ).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B) =
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] H) := by
    ext b
    simp [transporter]
  simp only [specTransporter, Category.assoc, pullbackSpecIso_inv_fst]
  rw [← Spec.map_comp]
  change (pullbackSpecIso R B H).hom ≫ Spec.map (CommRingCat.ofHom
    ((transporter R B H δ).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom)) = _
  rw [h]
  exact pullbackSpecIso_hom_fst R B H

/-- The second transporter component is the actual coaction morphism.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: identification of the transporter's second categorical component. -/
theorem specTransporter_snd (δ : B →ₐ[R] B ⊗[R] H) :
    specTransporter R B H δ ≫ pullback.snd _ _ = specCoaction R B H δ := by
  have h : (transporter R B H δ).toRingHom.comp
      (Algebra.TensorProduct.includeRight.toRingHom : B →+* B ⊗[R] B) =
        δ.toRingHom := by
    ext b
    simp [transporter, ← Algebra.TensorProduct.one_def]
  simp only [specTransporter, Category.assoc, pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp]
  change (pullbackSpecIso R B H).hom ≫ Spec.map (CommRingCat.ofHom
    ((transporter R B H δ).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)) = specCoaction R B H δ
  rw [h]
  rfl

/-- The affine coaction morphism lies over the original base Spec(R).

Supporting helper for the module's explicit C3 source mapping. -/
theorem specCoaction_over (δ : B →ₐ[R] B ⊗[R] H) :
    specCoaction R B H δ ≫ structureMap R B =
      pullback.fst (structureMap R B) (structureMap R H) ≫
        structureMap R B := by
  have h : δ.toRingHom.comp (algebraMap R B) = algebraMap R (B ⊗[R] H) := by
    ext r
    exact δ.commutes r
  simp only [specCoaction, structureMap, Category.assoc]
  rw [← Spec.map_comp]
  change (pullbackSpecIso R B H).hom ≫ Spec.map (CommRingCat.ofHom
    (δ.toRingHom.comp (algebraMap R B))) = _
  rw [h]
  exact pullbackSpecIso_hom_base R B H

/-- The usual actual torsor comparison `(x,g) |-> (x,x.g)` as a pullback lift.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: the actual categorical pair of first projection and action. -/
def specTransporterPair (δ : B →ₐ[R] B ⊗[R] H) :
    pullback (structureMap R B) (structureMap R H) ⟶
      pullback (structureMap R B) (structureMap R B) :=
  pullback.lift (pullback.fst _ _) (specCoaction R B H δ)
    (specCoaction_over R B H δ).symm

/-- The coordinate transporter is exactly the ordinary scheme torsor comparison.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: equality of the coordinate transporter and that actual pair. -/
theorem specTransporter_eq_pair (δ : B →ₐ[R] B ⊗[R] H) :
    specTransporter R B H δ = specTransporterPair R B H δ := by
  apply pullback.hom_ext
  · rw [specTransporterPair, pullback.lift_fst]
    exact specTransporter_fst R B H δ
  · rw [specTransporterPair, pullback.lift_snd]
    exact specTransporter_snd R B H δ

/-- Derived algebraic torsor data makes the actual scheme comparison an isomorphism.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C3: the actual pair isomorphism from supplied AlgebraicTorsorData, without
finiteness or field hypotheses. -/
theorem specTransporterPair_isIso {ε : H →ₐ[R] R} {Δ : H →ₐ[R] H ⊗[R] H}
    (T : AlgebraicTorsorData R B H ε Δ) :
    IsIso (specTransporterPair R B H T.coaction.coact) := by
  rw [← specTransporter_eq_pair]
  letI := spec_transporter_isIso R B H T
  unfold specTransporter
  infer_instance


end Pullback

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory
abbrev affine (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    Over (Spec (.of R)) := Over.mk (structureMap R B)

def ringPoint {X : Scheme.{u}} {B : Type u} [CommRing B]
    (f : X ⟶ Spec (.of B)) : B →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop).hom

theorem ringPoint_injective {X : Scheme.{u}} {B : Type u} [CommRing B] :
    Function.Injective (ringPoint (X := X) (B := B)) := by
  intro f g h
  apply ext_to_Spec
  exact CommRingCat.hom_ext h

@[simp] theorem ringPoint_precomp {X Y : Scheme.{u}} {B : Type u} [CommRing B]
    (q : X ⟶ Y) (f : Y ⟶ Spec (.of B)) :
    ringPoint (q ≫ f) = q.appTop.hom.comp (ringPoint f) := by
  simp only [ringPoint, Scheme.Hom.comp_appTop]
  rfl

@[simp] theorem ringPoint_spec {X : Scheme.{u}} {B C : Type u} [CommRing B] [CommRing C]
    (f : X ⟶ Spec (.of B)) (q : C →+* B) :
    ringPoint (f ≫ Spec.map (CommRingCat.ofHom q)) = (ringPoint f).comp q := by
  unfold ringPoint
  simp only [Scheme.Hom.comp_appTop]
  have h := (Scheme.SpecΓIdentity.inv.naturality (CommRingCat.ofHom q)).symm
  change (Scheme.ΓSpecIso (.of C)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
    CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (.of B)).inv at h
  rw [← Category.assoc, h, Category.assoc]
  rfl

@[instance_reducible] def sectionAlgebra (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) : Algebra R Γ(X.left, ⊤) := (ringPoint X.hom).toAlgebra

section Basic
variable (R : Type u) [CommRing R]
variable (B H : Type u) [CommRing B] [Algebra R B] [CommRing H] [Algebra R H]

local instance (X : Over (Spec (.of R))) : Algebra R Γ(X.left, ⊤) := sectionAlgebra R X

def pointAlg {X : Over (Spec (.of R))} (p : X ⟶ affine R B) : B →ₐ[R] Γ(X.left, ⊤) where
  __ := ringPoint p.left
  commutes' r := by
    have h := congrArg ringPoint (Over.w p)
    change ringPoint (p.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) = ringPoint X.hom at h
    rw [ringPoint_spec] at h
    exact DFunLike.congr_fun h r

theorem pointAlg_injective {X : Over (Spec (.of R))} :
    Function.Injective (pointAlg R B (X := X)) := by
  intro f g h
  apply Over.OverMorphism.ext
  apply ringPoint_injective
  exact congrArg AlgHom.toRingHom h

def action (alpha : B →ₐ[R] B ⊗[R] H) {X : Over (Spec (.of R))}
    (a : X ⟶ affine R H) (x : X ⟶ affine R B) : X ⟶ affine R B :=
  Over.homMk (pullback.lift (f := structureMap R B) (g := structureMap R H) x.left a.left
      ((Over.w x).trans (Over.w a).symm) ≫
    specCoaction R B H alpha) (by
      change (_ ≫ specCoaction R B H alpha) ≫ structureMap R B = _
      rw [Category.assoc, specCoaction_over, ← Category.assoc]
      erw [pullback.lift_fst]
      exact Over.w x)

@[simp] theorem action_natural (alpha : B →ₐ[R] B ⊗[R] H)
    {X Y : Over (Spec (.of R))} (q : X ⟶ Y)
    (a : Y ⟶ affine R H) (x : Y ⟶ affine R B) :
    q ≫ action R B H alpha a x = action R B H alpha (q ≫ a) (q ≫ x) := by
  apply Over.OverMorphism.ext
  simp only [action, Over.comp_left, Over.homMk_left, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

theorem pointAlg_action (alpha : B →ₐ[R] B ⊗[R] H) {X : Over (Spec (.of R))}
    (a : X ⟶ affine R H) (x : X ⟶ affine R B) :
    pointAlg R B (action R B H alpha a x) =
      (Algebra.TensorProduct.lift (pointAlg R B x) (pointAlg R H a)
        (fun _ _ => .all _ _)).comp alpha := by
  let p : X.left ⟶ Spec (.of (B ⊗[R] H)) :=
    pullback.lift (f := structureMap R B) (g := structureMap R H) x.left a.left
      ((Over.w x).trans (Over.w a).symm) ≫ (pullbackSpecIso R B H).hom
  have hleft : p ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] H)) = x.left := by
    simp [p, Category.assoc, pullbackSpecIso_hom_fst]
  have hright : p ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom : H →+* B ⊗[R] H)) = a.left := by
    simp [p, Category.assoc, pullbackSpecIso_hom_snd]
  have hbase : p ≫ structureMap R (B ⊗[R] H) = X.hom := by
    dsimp [p]
    rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc]
    erw [pullback.lift_fst]
    exact Over.w x
  let z : X ⟶ affine R (B ⊗[R] H) := Over.homMk p hbase
  have hz : pointAlg R (B ⊗[R] H) z =
      Algebra.TensorProduct.lift (pointAlg R B x) (pointAlg R H a) (fun _ _ => .all _ _) := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro b
      have hh := congrArg ringPoint hleft
      rw [ringPoint_spec] at hh
      have hv := DFunLike.congr_fun hh b
      change ringPoint p (b ⊗ₜ[R] 1) = ringPoint x.left b at hv
      dsimp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]
      simp only [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      exact hv
    · apply AlgHom.ext
      intro h
      have hh := congrArg ringPoint hright
      rw [ringPoint_spec] at hh
      have hv := DFunLike.congr_fun hh h
      change ringPoint p (1 ⊗ₜ[R] h) = ringPoint a.left h at hv
      dsimp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply]
      simp only [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
      exact hv
  apply AlgHom.ext
  intro b
  change ringPoint (p ≫ Spec.map (CommRingCat.ofHom alpha.toRingHom)) b = _
  rw [ringPoint_spec]
  exact DFunLike.congr_fun hz (alpha b)


/-- Unique transport holds on every scheme-valued point, by the actual pullback comparison. -/
theorem action_transport {epsilon : H →ₐ[R] R} {delta : H →ₐ[R] H ⊗[R] H}
    (T : AlgebraicTorsorData R B H epsilon delta)
    {X : Over (Spec (.of R))} (x y : X ⟶ affine R B) :
    ∃! a : X ⟶ affine R H, action R B H T.coaction.coact a x = y := by
  let m := specTransporterPair R B H T.coaction.coact
  letI : IsIso m := specTransporterPair_isIso R B H T
  let xy := pullback.lift (f := structureMap R B) (g := structureMap R B) x.left y.left
    ((Over.w x).trans (Over.w y).symm)
  let z := xy ≫ inv m
  have hz : z ≫ m = xy := by simp only [z, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hx : z ≫ pullback.fst (structureMap R B) (structureMap R H) = x.left := by
    have h := congrArg (fun f => f ≫ pullback.fst (structureMap R B) (structureMap R B)) hz
    simpa only [m, specTransporterPair, Category.assoc, pullback.lift_fst, xy] using h
  have hy : z ≫ specCoaction R B H T.coaction.coact = y.left := by
    have h := congrArg (fun f => f ≫ pullback.snd (structureMap R B) (structureMap R B)) hz
    simpa only [m, specTransporterPair, Category.assoc, pullback.lift_snd, xy] using h
  let a : X ⟶ affine R H := Over.homMk (z ≫ pullback.snd _ _) (by
    change (z ≫ pullback.snd _ _) ≫ structureMap R H = X.hom
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hx]
    exact Over.w x)
  have hpair : pullback.lift (f := structureMap R B) (g := structureMap R H) x.left a.left
      ((Over.w x).trans (Over.w a).symm) = z := by
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using hx.symm
    · simp [a]
  refine ⟨a, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change pullback.lift (f := structureMap R B) (g := structureMap R H) x.left a.left _ ≫
      specCoaction R B H T.coaction.coact = y.left
    rw [hpair]
    exact hy
  · intro b hb
    have hbm : pullback.lift (f := structureMap R B) (g := structureMap R H) x.left b.left
        ((Over.w x).trans (Over.w b).symm) ≫ m = xy := by
      apply pullback.hom_ext
      · simp only [m, specTransporterPair, Category.assoc, pullback.lift_fst, xy]
      · simpa only [m, specTransporterPair, Category.assoc, pullback.lift_snd, xy, action,
          Over.homMk_left] using congrArg (fun q => q.left) hb
    have hzb := (cancel_mono m).mp (hbm.trans hz.symm)
    apply Over.OverMorphism.ext
    have h := congrArg (fun q => q ≫ pullback.snd (structureMap R B) (structureMap R H)) hzb
    simpa only [pullback.lift_snd, a, Over.homMk_left] using h

variable {epsilon : H →ₐ[R] R} {delta : H →ₐ[R] H ⊗[R] H}

end Basic
section Hopf
variable (R B H : Type u) [CommRing R] [CommRing B] [Algebra R B] [CommRing H]
variable [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
local instance (X : Over (Spec (.of R))) : Algebra R Γ(X.left, ⊤) := sectionAlgebra R X
abbrev coefficientGroup : Grp (Over (Spec (.of R))) :=
  (hopfSpec (.of R)).obj (op (CommHopfAlgCat.of R H))

omit [Coalgebra.IsCocomm R H] in
/-- The constructed coefficient group retains the original affine carrier and structural map. -/
@[simp] theorem coefficientGroup_X : (coefficientGroup R H).X = affine R H := rfl
omit [Coalgebra.IsCocomm R H] in
@[simp] theorem coefficient_one {X : Over (Spec (.of R))} :
    pointAlg R H (1 : X ⟶ (coefficientGroup R H).X) =
      (Algebra.ofId R Γ(X.left, ⊤)).comp (Bialgebra.counitAlgHom R H) := by
  apply AlgHom.ext
  intro h
  change ringPoint (X.hom ≫ Spec.map
    (CommRingCat.ofHom (Bialgebra.counitAlgHom R H).toRingHom)) h = _
  rw [ringPoint_spec]
  rfl

omit [Coalgebra.IsCocomm R H] in
@[simp] theorem coefficient_mul {X : Over (Spec (.of R))}
    (a b : X ⟶ (coefficientGroup R H).X) :
    pointAlg R H (a * b) =
      (Algebra.TensorProduct.lift (pointAlg R H a) (pointAlg R H b) (fun _ _ => .all _ _)).comp
        (Bialgebra.comulAlgHom R H) := by
  change pointAlg R H (action R H H (Bialgebra.comulAlgHom R H) b a) = _
  exact pointAlg_action R H H _ b a

theorem coefficient_points_comm {X : Over (Spec (.of R))}
    (a b : X ⟶ (coefficientGroup R H).X) : a * b = b * a := by
  apply pointAlg_injective R H
  rw [coefficient_mul, coefficient_mul]
  have hs : Algebra.TensorProduct.lift (pointAlg R H a) (pointAlg R H b) (fun _ _ => .all _ _) =
      (Algebra.TensorProduct.lift (pointAlg R H b) (pointAlg R H a) (fun _ _ => .all _ _)).comp
        (Algebra.TensorProduct.comm R H H).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro h k
    simp [_root_.mul_comm]
  rw [hs, AlgHom.comp_assoc]
  congr 1
  ext h
  exact Coalgebra.comm_comul R h

/-- Cocommutativity gives commutativity of the actual coefficient group object. -/
instance coefficientGroup_comm : IsCommMonObj (coefficientGroup R H).X where
  mul_comm := by
    have h := coefficient_points_comm R H
      (snd (coefficientGroup R H).X (coefficientGroup R H).X)
      (fst (coefficientGroup R H).X (coefficientGroup R H).X)
    simpa only [Hom.mul_def, lift_snd_fst, lift_fst_snd, Category.id_comp] using h

instance coefficientGroup_finite [Module.Finite R H] : IsFinite (coefficientGroup R H).X.hom :=
  (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R H))).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)

instance coefficientGroup_etale [Algebra.Etale R H] : Etale (coefficientGroup R H).X.hom := by
  change Etale (structureMap R H)
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale R H))

variable (T : AlgebraicTorsorData R B H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))

theorem action_one {X : Over (Spec (.of R))} (x : X ⟶ affine R B) :
    action R B H T.coaction.coact (1 : X ⟶ (coefficientGroup R H).X) x = x := by
  apply pointAlg_injective R B
  rw [pointAlg_action, coefficient_one]
  have ht : Algebra.TensorProduct.lift (pointAlg R B x)
      ((Algebra.ofId R Γ(X.left, ⊤)).comp (Bialgebra.counitAlgHom R H))
      (fun _ _ => .all _ _) =
        (pointAlg R B x).comp (coactionCounit R B H (Bialgebra.counitAlgHom R H)) := by
    apply Algebra.TensorProduct.ext'
    intro b h
    simp [coactionCounit, Algebra.smul_def, mul_comm]
  rw [ht, AlgHom.comp_assoc, T.coaction.counit]
  rfl


theorem action_mul {X : Over (Spec (.of R))}
    (a b : X ⟶ (coefficientGroup R H).X) (x : X ⟶ affine R B) :
    action R B H T.coaction.coact (a * b) x =
      action R B H T.coaction.coact a (action R B H T.coaction.coact b x) := by
  rw [coefficient_points_comm R H a b]
  apply pointAlg_injective R B
  simpa only [pointAlg_action, coefficient_mul, evaluateCoaction] using
    evaluateCoaction_mul R B H T.coaction (pointAlg R H b) (pointAlg R H a) (pointAlg R B x)

/-- The actual scheme torsor action, derived from the given algebraic coaction and transporter. -/
def schemeTorsorAction : _root_.CategoryTheory.TorsorAction
    (coefficientGroup R H) (toUnit (affine R B)) where
  act := action R B H T.coaction.coact
  naturality := action_natural R B H T.coaction.coact
  one_act := action_one R B H T
  mul_act := action_mul R B H T
  over _ _ := toUnit_unique _ _
  transport x y _ := action_transport R B H T x y
end Hopf


/-- The finite etale cover is the existing native object with its literal
structural map; its total scheme is exactly `Spec B`. -/
def cover (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.Etale R B] : Scheme.FiniteEtale (Spec (.of R)) := by
  letI : IsFinite (structureMap R B) :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R B))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  letI : Etale (structureMap R B) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  exact Scheme.FiniteEtale.mk (structureMap R B)

@[simp] theorem cover_obj (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.Etale R B] : (cover R B).obj = affine R B := rfl

section ActionMap

variable (R B H : Type u) [CommRing R] [CommRing B] [Algebra R B] [CommRing H]
  [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  (T : AlgebraicTorsorData R B H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))

/-- Evaluation of the constructed native action is the displayed Spec coaction. -/
@[simp] theorem schemeTorsorAction_act {X : Over (Spec (.of R))}
    (a : X ⟶ (coefficientGroup R H).X) (x : X ⟶ affine R B) :
    (schemeTorsorAction R B H T).act a x = action R B H T.coaction.coact a x := rfl

/-- The actual action morphism has this formula on every scheme-valued point. -/
theorem schemeTorsorAction_comp_actionMap {X : Over (Spec (.of R))}
    (a : X ⟶ (coefficientGroup R H).X) (x : X ⟶ affine R B) :
    lift a x ≫ (schemeTorsorAction R B H T).actionMap = action R B H T.coaction.coact a x :=
  (schemeTorsorAction R B H T).comp_actionMap a x

end ActionMap

section Normalization

universe v
variable (R K Ω A H : Type u) (Lambda : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]
  [CommRing H] [Algebra R H] [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [IsTopologicalAddGroup Lambda]
  [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda] [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A

variable {epsilon : H →ₐ[R] R} {delta : H →ₐ[R] H ⊗[R] H}
  (tau : OriginalTorsorData R K A H epsilon delta)
  (coords : Algebra.FiniteEtale.TorsorCoordinates.CoefficientPointCoordinates
    R K Ω H Lambda epsilon delta)
  (f : A →ₐ[K] Ω) (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : Algebra.FiniteEtale.TorsorCoordinates.inertiaClass
    R K Ω A H Lambda tau coords f Q = 0)

/-- The same literal integral closure is a native finite etale cover.
Its etaleness is derived from the actual class's inertia restriction. -/
def normalizationCover : Scheme.FiniteEtale (Spec (.of R)) := by
  haveI := integralClosure.finite_of_etale R K A
  haveI := Algebra.FiniteEtale.InertiaTorsor.model_etale_of_H1
    R K Ω A H Lambda tau coords f Q hvan
  exact cover R (integralClosure R A)

@[simp] theorem normalizationCover_obj :
    (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj =
      affine R (integralClosure R A) := rfl

/-- Surjectivity is obtained from the derived faithful-flat torsor model. -/
theorem normalizationCover_surjective :
    Surjective (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj.hom := by
  haveI := Algebra.FiniteEtale.InertiaTorsor.model_etale_of_H1
    R K Ω A H Lambda tau coords f Q hvan
  exact (spec_cover R (integralClosure R A) H
    (Algebra.FiniteEtale.InertiaTorsor.ofH1 R K Ω A H Lambda tau coords f Q hvan)).2.2

/-- The canonical generic square is the contravariant image of the original
algebra square, with every ring map and orientation retained. -/
theorem normalization_generic_square :
    Spec.map (CommRingCat.ofHom (actualTensorEquiv R K A H).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.BaseChange.map R K
        (Algebra.FiniteEtale.InertiaTorsor.ofH1
          R K Ω A H Lambda tau coords f Q hvan).coaction.coact).toRingHom) =
    Spec.map (CommRingCat.ofHom tau.coaction.coact.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (integralClosure.genericFiberEquiv R K A).toAlgHom.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom
    (Algebra.FiniteEtale.InertiaTorsor.ofH1_square R K Ω A H Lambda tau coords f Q hvan)

/-- The literal normalization's transporter is the actual pullback pair isomorphism. -/
theorem normalization_transporter_isIso :
    IsIso (specTransporterPair R (integralClosure R A) H
      (Algebra.FiniteEtale.InertiaTorsor.ofH1
        R K Ω A H Lambda tau coords f Q hvan).coaction.coact) :=
  specTransporterPair_isIso R (integralClosure R A) H
    (Algebra.FiniteEtale.InertiaTorsor.ofH1 R K Ω A H Lambda tau coords f Q hvan)

/-- Restrict the original generic point to the same integral closure and take Spec. -/
def normalizationGenericPoint :
    Over.mk (structureMap R Ω) ⟶
      (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    ((f.restrictScalars R).comp (integralClosure R A).val).toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact ((f.restrictScalars R).comp (integralClosure R A).val).commutes r)

end Normalization

section NormalizationAction

universe v
variable (R K Ω A H : Type u) (Lambda : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A] [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [IsTopologicalAddGroup Lambda]
  [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda] [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
  (tau : OriginalTorsorData R K A H
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (coords : Algebra.FiniteEtale.TorsorCoordinates.CoefficientPointCoordinates R K Ω H Lambda
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (f : A →ₐ[K] Ω) (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : Algebra.FiniteEtale.TorsorCoordinates.inertiaClass
    R K Ω A H Lambda tau coords f Q = 0)

/-- The supplied cocommutative Hopf coefficient structure and the derived
algebraic torsor construct the native action on the actual normalization cover. -/
def normalizationSchemeAction : CategoryTheory.TorsorAction
    (coefficientGroup R H)
    (toUnit (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj) :=
  schemeTorsorAction R (integralClosure R A) H
    (Algebra.FiniteEtale.InertiaTorsor.ofH1 R K Ω A H Lambda tau coords f Q hvan)

end NormalizationAction

end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor
