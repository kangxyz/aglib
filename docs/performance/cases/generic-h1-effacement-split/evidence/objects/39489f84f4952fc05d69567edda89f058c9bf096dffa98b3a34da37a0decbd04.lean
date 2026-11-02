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
    out.putStr "H1_AFFINE HEADER_BEFORE_PRODUCER\n"
    out.flush

/-- The affine producer supplies the cover and its original zero; both finite
extensions are then refined to their actual separable subfields. -/
theorem exists_affine_separable_pointed_H1_effacement
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ z : A, n • z = 0) (hunit : IsUnit (n : k))
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A
      (pullback p (Spec.algebraMap k K))) 1) :
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
                  separableFieldClassMap k K p F E a) 1 c = 0 := by
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 0 BODY_ENTER\n"
      out.flush
  have hsource :=
    exists_affine_finite_pointed_H1_effacement k K U p x hx A n hn hkill hunit c
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 1 SOURCE_PRODUCED\n"
      out.flush
  obtain ⟨F, V, qV, aV, H, hsource⟩ := hsource
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 2 SOURCE_FIELD_AND_CARTESIAN_DATA\n"
      out.flush
  let : QuasiSeparatedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (Spec.algebraMap k F))
  let : ConnectedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap k F))
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 3A CANONICAL_SOURCE_INSTANCES\n"
      out.flush
  let : CompactSpace V := H.isoPullback.inv.homeomorph.compactSpace
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 3B ORIGINAL_SOURCE_COMPACT\n"
      out.flush
  let : QuasiSeparatedSpace V :=
    (quasiSeparatedSpace_congr H.isoPullback.hom.homeomorph).mpr inferInstance
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 3C ORIGINAL_SOURCE_QUASISEPARATED\n"
      out.flush
  let : ConnectedSpace V := H.isoPullback.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 3D ORIGINAL_SOURCE_CONNECTED\n"
      out.flush
  obtain ⟨Y, xF, zF, hF, hxFq, hxFa, hzF, hY, hcard, hfinite⟩ := hsource
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 4 COVER_AND_FINITE_PACKAGE\n"
      out.flush
  let : Module.Finite k F := hF
  let : IsGalois Y := hY
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 5 COVER_INSTANCES\n"
      out.flush
  let emb := Geometrically.commonClosureEmbedding k K
  let C := commonField k K (AlgebraicClosure k) (AlgebraicClosure K) F emb
  let aC := sourceCommonMap k K (AlgebraicClosure k) (AlgebraicClosure K) F emb
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 6 COMMON_FIELD_SELECTED\n"
      out.flush
  have hambient : (algebraMap C (AlgebraicClosure K)).comp aC.toRingHom =
      (emb.comp F.val).toRingHom :=
    congrArg (fun m : F →ₐ[k] AlgebraicClosure K => m.toRingHom)
      (IntermediateField.val_comp_mappedFiniteCompositumInclusion K F emb)
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 7 AMBIENT_EQUATION\n"
      out.flush
  have hz₁ : zF ≫ Y.obj.hom ≫ aV = Spec.algebraMap k F ≫ x :=
    (Category.assoc zF Y.obj.hom aV).symm.trans
      ((congrArg (fun z => z ≫ aV) hzF).trans hxFa)
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 8A FIRST_POINT_TRIANGLE\n"
      out.flush
  have hz₂ : zF ≫ Y.obj.hom ≫ qV = 𝟙 _ :=
    (Category.assoc zF Y.obj.hom qV).symm.trans
      ((congrArg (fun z => z ≫ qV) hzF).trans hxFq)
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 8B SECOND_POINT_TRIANGLE\n"
      out.flush
  have refineFields := exists_finiteStage_separable_pointed_effacement
    k K p F C (AlgebraicClosure K) aC (emb.comp F.val).toRingHom hambient
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 9 FIELDS_APPLIED\n"
      out.flush
  have refinePointed := refineFields x hx aV qV H Y zF hz₁ hz₂
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 10 COVER_APPLIED\n"
      out.flush
  have refineClass := refinePointed A 1 (n ^ Group.rank (Multiplicative A)) hcard c
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 11 CLASS_APPLIED\n"
      out.flush
  have refined := refineClass hfinite
  run_tac do
    let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
    IO.FS.withFile markerPath .append fun out => do
      out.putStr "H1_AFFINE 12 FINITE_PACKAGE_APPLIED\n"
      out.flush
  exact ⟨F, refined⟩

run_cmd do
  let markerPath := (← IO.getEnv "R5_H1_MARKER_FILE").getD ""
  IO.FS.withFile markerPath .append fun out => do
    out.putStr "H1_AFFINE 13 AFTER_PRODUCER_COMMAND\n"
    out.flush

end Constant

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
