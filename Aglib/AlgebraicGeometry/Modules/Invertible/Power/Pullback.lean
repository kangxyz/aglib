/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.TrivializedPower
public import Aglib.CategoryTheory.Adjunction.MateHomEquiv
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.PowerPullback` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`586ea539bf790a0b4266cf82a863198ec4fdab0fd09075de09b316a37385fb2c`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle pullbackLineBundle tensorPowerLineBundle trivialLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_adjoint pushforwardTensorMap
      pushforwardTensorMap_naturality pushforwardTensorMap_tmul
    tensorSheaf tensorSheafIso tensorSheafMap tensorSheafMap_comp tensorSheafMap_tmul
    tensorSheafUnit)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Canonical tensor and power pullback maps

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For arbitrary schemes and actual module sheaves, the canonical tensor
pullback comparison obeys the native identity and composition coherences.
The proof uses actual sectionwise pushforward tensor maps, their pure-tensor
formulas, and the native adjunction mates. The structure-module comparison
has the same identity/composition compatibility. For actual line bundles,
the already proved locally rank-one comparison gives a recursively defined
actual tensor-power pullback isomorphism, including the free-unit level zero,
and hence the literal pullback of a bundle with specified power trivialization.
No tensor-pullback or cohomological comparison premise is retained. This file
constructs the power and pair maps; the further power/pair naturality laws
are separate applications, not assumptions hidden in these definitions.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback
universe u

@[simp] theorem tensorSheafMap_id (X : Scheme.{u}) (M N : X.Modules) :
    tensorSheafMap X (𝟙 M) (𝟙 N) = 𝟙 (tensorSheaf X M N) := by
  unfold tensorSheafMap
  have h : PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 M.val) (𝟙 N.val) = 𝟙 _ := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 M.val) (𝟙 N.val)) = 𝟙 _
  rw [h, CategoryTheory.Functor.map_id]

theorem pushforwardTensorMap_id (X : Scheme.{u}) (M N : X.Modules) :
    pushforwardTensorMap (𝟙 X) M N ≫
      (Scheme.Modules.pushforwardId X).hom.app (show X.Modules from tensorSheaf X M N) =
    tensorSheafMap X ((Scheme.Modules.pushforwardId X).hom.app M)
      ((Scheme.Modules.pushforwardId X).hom.app N) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change ((Scheme.Modules.pushforwardId X).hom.app (show X.Modules from tensorSheaf X M
      N)).val.app U
    ((pushforwardTensorMap (𝟙 X) M N).val.app U
      ((tensorSheafUnit X ((Scheme.Modules.pushforward (𝟙 X)).obj M)
        ((Scheme.Modules.pushforward (𝟙 X)).obj N)).app U (m ⊗ₜ n))) =
    (tensorSheafMap X ((Scheme.Modules.pushforwardId X).hom.app M)
      ((Scheme.Modules.pushforwardId X).hom.app N)).val.app U
        ((tensorSheafUnit X ((Scheme.Modules.pushforward (𝟙 X)).obj M)
          ((Scheme.Modules.pushforward (𝟙 X)).obj N)).app U (m ⊗ₜ n))
  rw [pushforwardTensorMap_tmul, tensorSheafMap_tmul]
  rfl

theorem pullbackId_adjoint (X : Scheme.{u}) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv M M
      ((Scheme.Modules.pullbackId X).hom.app M) = (Scheme.Modules.pushforwardId X).inv.app M := by
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)) (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  simpa [Adjunction.homEquiv_unit] using h.symm

theorem pullbackTensorMap_id (X : Scheme.{u}) (M N : X.Modules) :
    pullbackTensorMap (𝟙 X) M N ≫
      tensorSheafMap X ((Scheme.Modules.pullbackId X).hom.app M)
        ((Scheme.Modules.pullbackId X).hom.app N) =
      (Scheme.Modules.pullbackId X).hom.app (show X.Modules from tensorSheaf X M N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint]
  refine Eq.trans ?_ (pullbackId_adjoint X (show X.Modules from tensorSheaf X M N)).symm
  rw [Category.assoc, ← pushforwardTensorMap_naturality, ← Category.assoc, tensorSheafMap_comp]
  have hM := pullbackId_adjoint X M
  have hN := pullbackId_adjoint X N
  rw [Adjunction.homEquiv_unit] at hM hN
  rw [hM, hN]
  apply (cancel_mono ((Scheme.Modules.pushforwardId X).hom.app
    (show X.Modules from tensorSheaf X M N))).mp
  rw [Category.assoc]
  erw [pushforwardTensorMap_id X M N]
  rw [tensorSheafMap_comp,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app, Iso.inv_hom_id_app, tensorSheafMap_id]
  rfl


section Mate
variable {C D : Type*} [Category C] [Category D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

end Mate

section CompositeMate
variable {C D E : Type*} [Category C] [Category D] [Category E]
variable {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}

theorem homEquiv_comp_apply (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {M : C} {P : D} {N : E} (α : L₁.obj M ⟶ P) (β : L₂.obj P ⟶ N) :
    (a₁.comp a₂).homEquiv M N (L₂.map α ≫ β) =
      a₁.homEquiv M P α ≫ R₁.map (a₂.homEquiv P N β) := by
  rw [Adjunction.comp_homEquiv]
  change a₁.homEquiv M (R₂.obj N) (a₂.homEquiv (L₁.obj M) N (L₂.map α ≫ β)) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
end CompositeMate

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem pullbackComp_adjoint (M : Z.Modules) (N : X.Modules)
    (φ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
      ((Scheme.Modules.pullbackComp f g).inv.app M ≫ φ) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv M N φ ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N := by
  rw [homEquiv_conjugate
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]

theorem unit_pullbackComp (M : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
      (Scheme.Modules.pushforward (f ≫ g)).map ((Scheme.Modules.pullbackComp f g).inv.app M) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  exact h.symm.trans (Category.assoc _ _ _)

theorem pushforwardTensorMap_comp (M N : X.Modules) :
    tensorSheafMap Z ((Scheme.Modules.pushforwardComp f g).hom.app M)
      ((Scheme.Modules.pushforwardComp f g).hom.app N) ≫ pushforwardTensorMap (f ≫ g) M N =
    pushforwardTensorMap g ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward
        f).obj N) ≫
      (Scheme.Modules.pushforward g).map (pushforwardTensorMap f M N) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (show X.Modules from tensorSheaf X M N) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 Z.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change (pushforwardTensorMap (f ≫ g) M N).val.app U
    ((tensorSheafMap Z ((Scheme.Modules.pushforwardComp f g).hom.app M)
      ((Scheme.Modules.pushforwardComp f g).hom.app N)).val.app U
        ((tensorSheafUnit Z
          ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj M))
          ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj N))).app U (m
              ⊗ₜ n))) =
    ((Scheme.Modules.pushforward g).map (pushforwardTensorMap f M N)).val.app U
      ((pushforwardTensorMap g ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N)).val.app U
          ((tensorSheafUnit Z
            ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj M))
            ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj N))).app U
                (m ⊗ₜ n)))
  have ht := tensorSheafMap_tmul Z
    (M := (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj M))
    (N := (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj N))
    (M' := (Scheme.Modules.pushforward (f ≫ g)).obj M)
    (N' := (Scheme.Modules.pushforward (f ≫ g)).obj N)
    ((Scheme.Modules.pushforwardComp f g).hom.app M)
    ((Scheme.Modules.pushforwardComp f g).hom.app N) U m n
  have hfg := pushforwardTensorMap_tmul (f ≫ g) M N U m n
  have hg := pushforwardTensorMap_tmul g ((Scheme.Modules.pushforward f).obj M)
    ((Scheme.Modules.pushforward f).obj N) U m n
  have hf := pushforwardTensorMap_tmul f M N (Opposite.op (g ⁻¹ᵁ U.unop)) m n
  exact (congrArg (fun z => (pushforwardTensorMap (f ≫ g) M N).val.app U z) ht).trans
    (hfg.trans (hf.symm.trans
      (congrArg (fun z => ((Scheme.Modules.pushforward g).map (pushforwardTensorMap f M
          N)).val.app U z) hg).symm))


/-- Composition coherence for the actual canonical tensor pullback map. -/
theorem pullbackTensorMap_comp (M N : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app (show Z.Modules from tensorSheaf Z M N) ≫
      (Scheme.Modules.pullback f).map (pullbackTensorMap g M N) ≫
      pullbackTensorMap f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N) =
    pullbackTensorMap (f ≫ g) M N ≫
      tensorSheafMap X ((Scheme.Modules.pullbackComp f g).inv.app M)
        ((Scheme.Modules.pullbackComp f g).inv.app N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [pullbackComp_adjoint]
  conv_lhs =>
    rw [homEquiv_comp_apply
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (pullbackTensorMap g M N)
      (pullbackTensorMap f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)),
      pullbackTensorMap_adjoint g M N,
      pullbackTensorMap_adjoint f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback
          g).obj N)]
  conv_rhs =>
    rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint (f ≫ g) M N]
  conv_rhs =>
    rw [Category.assoc, ← pushforwardTensorMap_naturality, ← Category.assoc, tensorSheafMap_comp,
      unit_pullbackComp, unit_pullbackComp]
    rw [← tensorSheafMap_comp Z
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N)]
    rw [← tensorSheafMap_comp Z
      ((Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback
            g).obj M)))
      ((Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback
            g).obj N)))]
    simp only [Category.assoc]
    erw [pushforwardTensorMap_comp f g
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N))]
    simp only [Category.assoc]
    erw [AlgebraicGeometry.Scheme.Modules.pushforwardTensorMap_naturality_assoc g
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback
          g).obj M))
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback
          g).obj N))]
  simp only [Functor.map_comp, Category.assoc]
  rfl


/-- Unit comparison is the actual structural map under adjunction. -/
theorem unitIso_adjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- Composition coherence for the actual structure-module pullback map. -/
def freeUnitIso (X : Scheme.{u}) :
    (trivialLineBundle X).val ≅ SheafOfModules.unit X.ringCatSheaf :=
  Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)

/-- The actual tensor-power pullback map is recursively the canonical tensor comparison. -/
def pullbackPowerIso {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    (n : ℕ) → (Scheme.Modules.pullback f).obj (tensorPowerLineBundle Y L n).val ≅
      (tensorPowerLineBundle X (pullbackLineBundle f L) n).val
  | 0 => (Scheme.Modules.pullback f).mapIso (freeUnitIso Y) ≪≫ pullbackUnitIso f ≪≫
      (freeUnitIso X).symm
  | n + 1 =>
      Scheme.Modules.Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso f L
          (tensorPowerLineBundle Y L n) ≪≫
      tensorSheafIso X (Iso.refl (pullbackLineBundle f L).val) (pullbackPowerIso f L n)

/-- Actual pullback of a line bundle with specified power trivialization. -/
def pullbackPair {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ}
    (P : AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.Pair Y n) :
        AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.Pair X n where
  lineBundle := pullbackLineBundle f P.lineBundle
  trivialization := (pullbackPowerIso f P.lineBundle n).symm ≪≫
    (Scheme.Modules.pullback f).mapIso P.trivialization ≪≫ pullbackUnitIso f

end AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback
