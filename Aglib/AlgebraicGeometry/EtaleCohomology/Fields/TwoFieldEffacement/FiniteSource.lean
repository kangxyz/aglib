/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldPointedGalois
public import Mathlib.GroupTheory.Rank

/-! # Finite source-field descent of an original pointed class-killing cover

The algebraic source extension, original qcqs base, prescribed point, two-stage
finite field construction and literal class-zero equation are retained. This
construction neither requires nor constructs a compactification of the source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

open FiniteEtale FiniteEtale.FieldCoverDescent

/-- An actual reconstruction of the original finite cover preserves the
literal composite class-zero equation after any further base change. -/
theorem constantRestriction_zero_of_cover_reconstruction
    {V U W T : Scheme.{u}} (v : U ⟶ V) (g : W ⟶ U) (h : W ⟶ T)
    (Z : FiniteEtale V) (Y : FiniteEtale U)
    (e : (baseChange v).obj Z ≅ Y)
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (hc : Curves.constantRestriction A (((baseChange g).obj Y).obj.hom ≫ h) q c = 0) :
    Curves.constantRestriction A (((baseChange (g ≫ v)).obj Z).obj.hom ≫ h) q c = 0 := by
  let E : (baseChange (g ≫ v)).obj Z ≅ (baseChange g).obj Y :=
    (baseChangeComp v g).app Z ≪≫ (baseChange g).mapIso e
  let a := E.hom.hom.left
  have ha : a ≫ ((baseChange g).obj Y).obj.hom =
      ((baseChange (g ≫ v)).obj Z).obj.hom := Over.w E.hom.hom
  calc
    Curves.constantRestriction A (((baseChange (g ≫ v)).obj Z).obj.hom ≫ h) q c =
        Curves.constantRestriction A (a ≫ (((baseChange g).obj Y).obj.hom ≫ h)) q c := by
      rw [← Category.assoc, ha]
    _ = Curves.constantRestriction A a q
        (Curves.constantRestriction A (((baseChange g).obj Y).obj.hom ≫ h) q c) :=
      Curves.constantRestriction_comp A _ _ q c
    _ = 0 := by rw [hc, map_zero]

/-- Descend the original pointed Galois cover through two finite source-field
stages, preserving its given order bound and its literal class-killing equation.
The source extension is genuinely algebraic; the further class base is arbitrary. -/
theorem exists_finite_source_pointed_effacement_of_cover
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    (p : U ⟶ Spec (.of k)) [GeometricallyConnected p]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (Y : FiniteEtale (pullback p (Spec.algebraMap k Ω))) [IsGalois Y]
    (z : FiniteEtale.Fiber
      (pullback.lift (Spec.algebraMap k Ω ≫ x) (𝟙 _)
        (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])) Y)
    (A : Type u) [AddCommGroup A] [Finite A] (n : ℕ)
    (hcard : Nat.card (Aut Y) ∣ n ^ Group.rank (Multiplicative A))
    {W T : Scheme.{u}} (g : W ⟶ pullback p (Spec.algebraMap k Ω)) (h : W ⟶ T)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) 1)
    (hzero : Curves.constantRestriction A (((baseChange g).obj Y).obj.hom ≫ h) 1 c = 0) :
    ∃ (s : Finset Ω)
      (Z : FiniteEtale (((FieldLimit.schemeDiagram k Ω p).obj (op s)).left))
      (t : Finset Ω),
      let k₀ := FieldLimit.finiteField k Ω s
      let q₀ := pullback.fst (Spec.algebraMap k k₀) p
      let F := pointField k₀ Ω t
      let a := pullback.fst q₀ (Spec.algebraMap k₀ F)
      let ZF := (baseChange a).obj Z
      let v := pointProjection k₀ Ω q₀
        (FieldLimit.fieldProjection k Ω p (op s)) (pullback.snd p (Spec.algebraMap k Ω))
        (fieldProjection_isPullback k Ω p s) t
      ∃ (xF : Spec (.of F) ⟶ pointBase k₀ Ω q₀ t)
        (zF : Spec (.of F) ⟶ ZF.obj.left),
        Module.Finite k F ∧
        IsPullback (a ≫ pullback.snd (Spec.algebraMap k k₀) p)
          (pullback.snd q₀ (Spec.algebraMap k₀ F)) p (Spec.algebraMap k F) ∧
        xF ≫ pullback.snd q₀ (Spec.algebraMap k₀ F) = 𝟙 _ ∧
        xF ≫ a ≫ pullback.snd (Spec.algebraMap k k₀) p = Spec.algebraMap k F ≫ x ∧
        zF ≫ ZF.obj.hom = xF ∧ IsGalois ZF ∧
        Nat.card (Aut ZF) ∣ n ^ Group.rank (Multiplicative A) ∧
        Curves.constantRestriction A
          (((baseChange (g ≫ v)).obj ZF).obj.hom ≫ h) 1 c = 0 := by
  have hz₁ : z.left ≫ Y.obj.hom ≫ pullback.fst p (Spec.algebraMap k Ω) =
      Spec.algebraMap k Ω ≫ x := by
    rw [← Category.assoc, Over.w z]
    exact pullback.lift_fst _ _ _
  have hz₂ : z.left ≫ Y.obj.hom ≫ pullback.snd p (Spec.algebraMap k Ω) = 𝟙 _ := by
    rw [← Category.assoc, Over.w z]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, Z, E, hGZ, hcardZ, t, xF, zF, hfinite, H, hxF, hxFa, hzF,
    hzambient, hGF, hcardF, ⟨EF⟩⟩ :=
    exists_qcqs_pointed_galois_cover k Ω p x hx Y z.left hz₁ hz₂
  refine ⟨s, Z, t, xF, zF, hfinite, H, hxF, hxFa, hzF, hGF, ?_, ?_⟩
  · rw [hcardF]
    exact hcard
  · exact constantRestriction_zero_of_cover_reconstruction _ _ _ _ Y EF A 1 c hzero

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
