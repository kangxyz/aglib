/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineFiniteH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericH1ClassEffacement.Separable

/-! # Affine separable pointed H1 effacement

The affine finite-source producer and its actual common-field stage supply the
original pointed Galois cover. Its separable refinement retains the original
point, order bound and literal class-zero map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

section Constant
variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {U : Scheme.{u}} [IsAffine U] (p : U ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]

run_cmd do
  let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
  IO.FS.withFile markerPath .append fun out => do
    out.putStr "H1_AFFINE_STATEMENT BEFORE_HEADER\n"
    out.flush

theorem affine_effacement_statement_probe
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ z : A, n • z = 0) (hunit : IsUnit (n : k))
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A
      (pullback p (Spec.algebraMap k K))) 1)
    (_statement :
    ∃ (F : IntermediateField k (AlgebraicClosure k))
      (E : Type u) (_ : Field E) (_ : Algebra K E),
      letI : Algebra k E := ((algebraMap K E).comp (algebraMap k K)).toAlgebra
      letI : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq' rfl
      letI : ConnectedSpace
          (pullback p (Spec.algebraMap k (separableClosure k F)) : Scheme.{u}) :=
        GeometricallyConnected.connectedSpace_of_subsingleton
          (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
      Module.Finite k F ∧ Module.Finite K E ∧
      ∃ (jE : E →ₐ[K] AlgebraicClosure K) (a : F →ₐ[k] E),
        jE.toRingHom.comp a.toRingHom =
          ((Geometrically.commonClosureEmbedding k K).comp F.val).toRingHom ∧
        ∃ (Z : FiniteEtale (pullback p (Spec.algebraMap k (separableClosure k F)))),
          IsGalois Z ∧ Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative A) ∧
          ∃ z : Spec (.of (separableClosure k F)) ⟶ Z.obj.left,
            z ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
            Curves.constantRestriction A
              (((FiniteEtale.baseChange (pullback.fst
                (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
                (Spec.map (CommRingCat.ofHom
                  (separableSourceMap k F K E a).toRingHom)))).obj Z).obj.hom ≫
                  separableFieldClassMap k K p F E a) 1 c = 0) : True := by
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE_STATEMENT BODY_ENTER\n"
      out.flush
  exact True.intro

run_cmd do
  let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
  IO.FS.withFile markerPath .append fun out => do
    out.putStr "H1_AFFINE_STATEMENT AFTER_DECLARATION_COMMAND\n"
    out.flush

end Constant

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
