/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericH1ClassEffacement.Affine
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericCoefficientPresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericCoefficientPresentationConsumer
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CoefficientCompositeZero

/-! # Original generic pointed H1 effacement

The actual generic square identifies the produced finite coefficient stage.
Affine separable effacement and the original coefficient transport then kill
the original class, retaining its independent Ext world.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

section Generic
variable (B k K : Type u) [CommRing B] [Field k] [Field K]
  [Algebra B K] [Algebra k K]
  {Y U : Scheme.{u}} (e : Y ⟶ Spec (.of B)) [QuasiCompact e] [QuasiSeparated e]
  (p : U ⟶ Spec (.of k))

/-- The unique canonical comparison for the actual generic square and the
actual finite coefficient stage. No second coefficient sheaf is selected. -/
def genericCoefficientStageIso
    (aη : pullback e (Spec.algebraMap B K) ⟶ U)
    (Hη : IsPullback aη (pullback.snd e (Spec.algebraMap B K))
      p (Spec.algebraMap k K))
    (L : Type u) [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L] :
    pullback (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≅
      pullback p (Spec.algebraMap k L) := by
  have ht : Spec.algebraMap K L ≫ Spec.algebraMap k K = Spec.algebraMap k L := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      (IsScalarTower.algebraMap_eq k K L).symm)
  have H := (IsPullback.of_hasPullback
    (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L)).paste_horiz Hη
  rw [ht] at H
  exact H.isoPullback

/-- The complete original pointed-cover conclusion over one specified coefficient
field, before specializing that field to the produced finite Galois carrier.
The coefficient, maps and scalar actions are the original selected ones. -/
def GenericPointedH1StageEffacement
    [GeometricallyConnected p]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (aη : pullback e (Spec.algebraMap B K) ⟶ U)
    (Hη : IsPullback aη (pullback.snd e (Spec.algebraMap B K)) p (Spec.algebraMap k K))
    (M : AbelianSheaf.{u, u + 1} (Spec (.of B))) (n : ℕ)
    (c : Sheaf.H.{eX} ((inverseImage e).obj M) 1)
    (L : Type u) [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (C : Type u) [AddCommGroup C] [Finite C] : Prop :=
    ∃ (F : IntermediateField k (AlgebraicClosure k))
      (E : Type u) (_ : Field E) (_ : Algebra L E),
      letI : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
      letI : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq' rfl
      letI : ConnectedSpace
          (pullback p (Spec.algebraMap k (separableClosure k F)) : Scheme.{u}) :=
        GeometricallyConnected.connectedSpace_of_subsingleton
          (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
      Module.Finite k F ∧ Module.Finite L E ∧
      ∃ (jE : E →ₐ[L] AlgebraicClosure L) (a : F →ₐ[k] E),
        jE.toRingHom.comp a.toRingHom =
          ((Geometrically.commonClosureEmbedding k L).comp F.val).toRingHom ∧
        ∃ Z : FiniteEtale (pullback p (Spec.algebraMap k (separableClosure k F))),
          IsGalois Z ∧ Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative C) ∧
          ∃ z : Spec (.of (separableClosure k F)) ⟶ Z.obj.left,
            z ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
            cohomologyPullback.{u, eX, u + 2}
              ((((FiniteEtale.baseChange (pullback.fst
                (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
                (Spec.map (CommRingCat.ofHom
                  (separableSourceMap k F L E a).toRingHom)))).obj Z).obj.hom ≫
                  separableFieldClassMap k L p F E a ≫
                    (genericCoefficientStageIso B k K e p aη Hη L).inv) ≫
                      (pullback.fst (pullback.snd e (Spec.algebraMap B K))
                        (Spec.algebraMap K L) ≫ pullback.fst e (Spec.algebraMap B K)))
              ((inverseImage e).obj M) 1 c = 0

/-- The single original generic H1 conclusion, shared by the actual family instance.
It asserts the produced cover and literal original class zero; it is not an input certificate. -/
def GenericPointedH1Effacement
    [GeometricallyConnected p]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (aη : pullback e (Spec.algebraMap B K) ⟶ U)
    (Hη : IsPullback aη (pullback.snd e (Spec.algebraMap B K)) p (Spec.algebraMap k K))
    (M : AbelianSheaf.{u, u + 1} (Spec (.of B))) (n : ℕ)
    (c : Sheaf.H.{eX} ((inverseImage e).obj M) 1) : Prop :=
    ∃ (L : FiniteGaloisIntermediateField K (SeparableClosure K))
      (C : Type u) (_ : AddCommGroup C) (_ : Finite C),
      letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
      letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
      (∀ z : C, n • z = 0) ∧
      GenericPointedH1StageEffacement B k K e p x hx aη Hη M n c L C

end Generic

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
