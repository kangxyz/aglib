/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitInverse
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.PowerPullbackNaturality` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`dd49140673401c12dc1c371832f9d5cf47e57f78c62ceedcaec0dfbc0e06d8d4`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle pullbackLineBundle tensorPowerLineBundle trivialLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap tensorSheaf tensorSheafMap tensorSheafMap_comp)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Naturality of actual tensor-power and power-pair pullbacks

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For arbitrary schemes and actual line bundles, the recursively constructed
power pullback isomorphism is natural in actual bundle isomorphisms and
compatible with the native identity/composition pullback maps. The proofs
are inductions using the proved canonical tensor and structure-unit squares;
the free-unit level zero is handled explicitly. Consequently genuine pairs
(L, tau:L^n≅O) pull back along actual scheme morphisms, preserve actual
power-compatible pair isomorphisms, and obey identity/composition through
those same native isomorphisms. No standard-theorem or target-comparison
premise is retained, and no H1 classification is asserted here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullbackNaturality
open PowerPullback TrivializedPower
universe u
variable {X Y Z : Scheme.{u}}

/-- Naturality of the actual recursively constructed power comparison. -/
theorem pullbackPowerIso_naturality (f : X ⟶ Y) {L M : LineBundle Y}
    (e : L.val ≅ M.val) (n : ℕ) :
    (Scheme.Modules.pullback f).mapIso (powerIso Y e n) ≪≫ pullbackPowerIso f M n =
      pullbackPowerIso f L n ≪≫ powerIso X ((Scheme.Modules.pullback f).mapIso e) n := by
  apply Iso.ext
  induction n with
  | zero =>
    change (Scheme.Modules.pullback f).map (𝟙 (trivialLineBundle Y).val) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    rfl
  | succ n ih =>
    change (Scheme.Modules.pullback f).map
      (tensorSheafMap Y e.hom (powerIso Y e n).hom) ≫
        pullbackTensorMap f M.val (tensorPowerLineBundle Y M n).val ≫
          tensorSheafMap X (𝟙 _) (pullbackPowerIso f M n).hom =
      (pullbackTensorMap f L.val (tensorPowerLineBundle Y L n).val ≫
        tensorSheafMap X (𝟙 _) (pullbackPowerIso f L n).hom) ≫
          tensorSheafMap X ((Scheme.Modules.pullback f).map e.hom)
            (powerIso X ((Scheme.Modules.pullback f).mapIso e) n).hom
    rw [Scheme.Modules.pullbackTensorMap_naturality_assoc f e.hom
        (powerIso Y e n).hom,
      tensorSheafMap_comp, Category.assoc, tensorSheafMap_comp,
      Category.comp_id, Category.id_comp]
    change (Scheme.Modules.pullback f).map (powerIso Y e n).hom ≫
      (pullbackPowerIso f M n).hom =
      (pullbackPowerIso f L n).hom ≫ (powerIso X ((Scheme.Modules.pullback f).mapIso e) n).hom at ih
    rw [ih]

/-- Native identity coherence for actual tensor-power pullback. -/
theorem pullbackPowerIso_id (L : LineBundle X) (n : ℕ) :
    (pullbackPowerIso (𝟙 X) L n).hom ≫
      (powerIso X ((Scheme.Modules.pullbackId X).app L.val) n).hom =
    (Scheme.Modules.pullbackId X).hom.app (tensorPowerLineBundle X L n).val := by
  induction n with
  | zero =>
    change ((Scheme.Modules.pullback (𝟙 X)).map (freeUnitIso X).hom ≫
      (pullbackUnitIso (𝟙 X)).hom ≫ (freeUnitIso X).inv) ≫ 𝟙 _ = _
    rw [Category.comp_id, ← Scheme.Modules.pullbackUnitIso_id X]
    rw [← Category.assoc, (Scheme.Modules.pullbackId X).hom.naturality (freeUnitIso X).hom]
    simp
    rfl
  | succ n ih =>
    change (pullbackTensorMap (𝟙 X) L.val (tensorPowerLineBundle X L n).val ≫
      tensorSheafMap X (𝟙 _) (pullbackPowerIso (𝟙 X) L n).hom) ≫
        tensorSheafMap X ((Scheme.Modules.pullbackId X).hom.app L.val)
          (powerIso X ((Scheme.Modules.pullbackId X).app L.val) n).hom = _
    rw [Category.assoc, tensorSheafMap_comp, Category.id_comp, ih]
    exact pullbackTensorMap_id X L.val (tensorPowerLineBundle X L n).val

/-- Composition coherence for actual tensor-power pullback. -/
theorem pullbackPowerIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L : LineBundle Z) (n : ℕ) :
    (Scheme.Modules.pullbackComp f g).inv.app (tensorPowerLineBundle Z L n).val ≫
      (Scheme.Modules.pullback f).map (pullbackPowerIso g L n).hom ≫
      (pullbackPowerIso f (pullbackLineBundle g L) n).hom =
    (pullbackPowerIso (f ≫ g) L n).hom ≫
      (powerIso X (L := pullbackLineBundle (f ≫ g) L) (M := pullbackLineBundle f
          (pullbackLineBundle g L)) ((Scheme.Modules.pullbackComp f g).app L.val).symm n).hom := by
  induction n with
  | zero =>
    change (Scheme.Modules.pullbackComp f g).inv.app (trivialLineBundle Z).val ≫
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback g).map (freeUnitIso Z).hom ≫
          (pullbackUnitIso g).hom ≫ (freeUnitIso Y).inv) ≫
      (Scheme.Modules.pullback f).map (freeUnitIso Y).hom ≫
        (pullbackUnitIso f).hom ≫ (freeUnitIso X).inv =
      ((Scheme.Modules.pullback (f ≫ g)).map (freeUnitIso Z).hom ≫
        (pullbackUnitIso (f ≫ g)).hom ≫ (freeUnitIso X).inv) ≫ 𝟙 _
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Category.comp_id]
    have hcancel := Iso.inv_hom_id_assoc ((Scheme.Modules.pullback f).mapIso (freeUnitIso Y))
      ((pullbackUnitIso f).hom ≫ (freeUnitIso X).inv)
    erw [hcancel]
    erw [← (Scheme.Modules.pullbackComp f g).inv.naturality_assoc (freeUnitIso Z).hom]
    have hu := congrArg (fun v => v ≫ (freeUnitIso X).inv)
        (Scheme.Modules.pullbackUnitIso_comp_inv f g)
    simp only [Category.assoc] at hu
    rw [hu]
  | succ n ih =>
    change (Scheme.Modules.pullbackComp f g).inv.app
        (show Z.Modules from tensorSheaf Z L.val (tensorPowerLineBundle Z L n).val) ≫
      (Scheme.Modules.pullback f).map
        (pullbackTensorMap g L.val (tensorPowerLineBundle Z L n).val ≫
          tensorSheafMap Y (𝟙 _) (pullbackPowerIso g L n).hom) ≫
      pullbackTensorMap f ((Scheme.Modules.pullback g).obj L.val)
        (tensorPowerLineBundle Y (pullbackLineBundle g L) n).val ≫
      tensorSheafMap X (𝟙 _) (pullbackPowerIso f (pullbackLineBundle g L) n).hom =
      (pullbackTensorMap (f ≫ g) L.val (tensorPowerLineBundle Z L n).val ≫
        tensorSheafMap X (𝟙 _) (pullbackPowerIso (f ≫ g) L n).hom) ≫
      tensorSheafMap X ((Scheme.Modules.pullbackComp f g).inv.app L.val)
        (powerIso X (L := pullbackLineBundle (f ≫ g) L) (M := pullbackLineBundle f
            (pullbackLineBundle g L)) ((Scheme.Modules.pullbackComp f g).app L.val).symm n).hom
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    erw [Scheme.Modules.pullbackTensorMap_naturality_assoc f (𝟙
        ((Scheme.Modules.pullback g).obj L.val))
      (pullbackPowerIso g L n).hom]
    rw [CategoryTheory.Functor.map_id, tensorSheafMap_comp, Category.id_comp]
    have hc := congrArg (fun v => v ≫ tensorSheafMap X
      (𝟙 ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L.val)))
      ((Scheme.Modules.pullback f).map (pullbackPowerIso g L n).hom ≫
        (pullbackPowerIso f (pullbackLineBundle g L) n).hom))
      (pullbackTensorMap_comp f g L.val (tensorPowerLineBundle Z L n).val)
    simp only [Category.assoc] at hc
    erw [hc]
    rw [tensorSheafMap_comp]
    erw [tensorSheafMap_comp X
      (𝟙 ((Scheme.Modules.pullback (f ≫ g)).obj L.val))
      (pullbackPowerIso (f ≫ g) L n).hom
      ((Scheme.Modules.pullbackComp f g).inv.app L.val)
      (powerIso X (L := pullbackLineBundle (f ≫ g) L) (M := pullbackLineBundle f
          (pullbackLineBundle g L)) ((Scheme.Modules.pullbackComp f g).app L.val).symm n).hom]
    exact congrArg₂ (fun a b => pullbackTensorMap (f ≫ g) L.val
      (tensorPowerLineBundle Z L n).val ≫ tensorSheafMap X a b)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ih


/-- Inverse form of the canonical power-comparison naturality square. -/
theorem pullbackPowerIso_inv_naturality (f : X ⟶ Y) {L M : LineBundle Y}
    (e : L.val ≅ M.val) (n : ℕ) :
    (powerIso X ((Scheme.Modules.pullback f).mapIso e) n).hom ≫
      (pullbackPowerIso f M n).inv =
    (pullbackPowerIso f L n).inv ≫ (Scheme.Modules.pullback f).map (powerIso Y e n).hom := by
  apply (pullbackPowerIso f L n).eq_inv_comp.mpr
  have hn := congrArg Iso.hom (pullbackPowerIso_naturality f e n)
  change (Scheme.Modules.pullback f).map (powerIso Y e n).hom ≫ (pullbackPowerIso f M n).hom =
    (pullbackPowerIso f L n).hom ≫ (powerIso X ((Scheme.Modules.pullback f).mapIso e) n).hom at hn
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Actual pair isomorphisms remain actual pair isomorphisms under pullback. -/
theorem pullbackPair_isomorphic (f : X ⟶ Y) {n : ℕ} {P Q : Pair Y n}
    (h : Isomorphic Y P Q) : Isomorphic X (pullbackPair f P) (pullbackPair f Q) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(Scheme.Modules.pullback f).mapIso e, ?_⟩
  change (powerIso X ((Scheme.Modules.pullback f).mapIso e) n).hom ≫
    ((pullbackPowerIso f Q.lineBundle n).inv ≫
      (Scheme.Modules.pullback f).map Q.trivialization.hom ≫ (pullbackUnitIso f).hom) =
    (pullbackPowerIso f P.lineBundle n).inv ≫
      (Scheme.Modules.pullback f).map P.trivialization.hom ≫ (pullbackUnitIso f).hom
  rw [← Category.assoc, pullbackPowerIso_inv_naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc, he]

/-- The native identity isomorphism preserves the actual power trivialization. -/
theorem pullbackPair_id {n : ℕ} (P : Pair X n) :
    Isomorphic X (pullbackPair (𝟙 X) P) P := by
  refine ⟨(Scheme.Modules.pullbackId X).app P.lineBundle.val, ?_⟩
  change (powerIso X ((Scheme.Modules.pullbackId X).app P.lineBundle.val) n).hom ≫
    P.trivialization.hom = (pullbackPowerIso (𝟙 X) P.lineBundle n).inv ≫
      ((Scheme.Modules.pullback (𝟙 X)).map P.trivialization.hom ≫ (pullbackUnitIso (𝟙 X)).hom)
  apply (pullbackPowerIso (𝟙 X) P.lineBundle n).eq_inv_comp.mpr
  rw [← Category.assoc, pullbackPowerIso_id, ← Scheme.Modules.pullbackUnitIso_id X]
  exact ((Scheme.Modules.pullbackId X).hom.naturality P.trivialization.hom).symm

/-- The native composite pullback isomorphism preserves the actual power trivialization. -/
theorem pullbackPair_comp (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (P : Pair Z n) :
    Isomorphic X (pullbackPair (f ≫ g) P) (pullbackPair f (pullbackPair g P)) := by
  refine ⟨((Scheme.Modules.pullbackComp f g).app P.lineBundle.val).symm, ?_⟩
  change (powerIso X ((Scheme.Modules.pullbackComp f g).app P.lineBundle.val).symm n).hom ≫
      ((pullbackPowerIso f (pullbackLineBundle g P.lineBundle) n).inv ≫
        (Scheme.Modules.pullback f).map
          ((pullbackPowerIso g P.lineBundle n).inv ≫
            (Scheme.Modules.pullback g).map P.trivialization.hom ≫ (pullbackUnitIso g).hom) ≫
        (pullbackUnitIso f).hom) =
    (pullbackPowerIso (f ≫ g) P.lineBundle n).inv ≫
      ((Scheme.Modules.pullback (f ≫ g)).map P.trivialization.hom ≫ (pullbackUnitIso (f ≫ g)).hom)
  apply (pullbackPowerIso (f ≫ g) P.lineBundle n).eq_inv_comp.mpr
  rw [← Category.assoc, ← pullbackPowerIso_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_comp]
  have hcancel := Iso.hom_inv_id_assoc ((Scheme.Modules.pullback f).mapIso
    (pullbackPowerIso g P.lineBundle n))
    ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map P.trivialization.hom) ≫
      (Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom)
  erw [hcancel]
  erw [← (Scheme.Modules.pullbackComp f g).inv.naturality_assoc P.trivialization.hom]
  rw [Scheme.Modules.pullbackUnitIso_comp_inv]

end AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullbackNaturality
