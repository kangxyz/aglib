/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent.Boundary
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent.Devissage
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent.TargetRow

/-!
# The actual finite-cover coefficient induction

The literal comparison is bijective on every coefficient if it is bijective
on the finite affine-cover coefficients. The quotient stays quasicoherent,
and the induction proves injectivity uniformly before surjectivity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The actual finite biproduct of open direct images used by the cover sequence. -/
abbrev relativeSerreCoverCoefficients {Y : Scheme.{u}} {J : Type u} [Finite J]
    (U : J → Y.Opens) (N : Y.Modules) : Y.Modules :=
  biproduct (fun j => (Scheme.Modules.pushforward (U j).ι).obj (N.restrict (U j).ι))

instance relativeSerreCoverCoefficients_isQuasicoherent
    {Y : Scheme.{u}} {J : Type u} [Finite J] (U : J → Y.Opens)
    [∀ j, QuasiCompact (U j).ι] (N : Y.Modules) [N.IsQuasicoherent] :
    (relativeSerreCoverCoefficients U N).IsQuasicoherent := by
  classical
  let : ∀ j, ((Scheme.Modules.pushforward (U j).ι).obj
      (N.restrict (U j).ι)).IsQuasicoherent := fun j =>
    Scheme.Modules.QuasiCoherent.quasicoherent_pushforward_open (U j).ι
      (N.restrict (U j).ι)
  apply (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_isLimit
    (biproduct.isLimit _)
  intro j
  change ((Scheme.Modules.pushforward (U j.as).ι).obj
    (N.restrict (U j.as).ι)).IsQuasicoherent
  infer_instance

private instance quasicoherentSubtype {Y : Scheme.{u}}
    (N : {N : Y.Modules // N.IsQuasicoherent}) : N.val.IsQuasicoherent := N.property

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
  [Y.IsSeparated]

/-- The original map in every degree follows from its values on the actual cover terms.
This is the coefficient dévissage step, prior to supplying affine-open duality. -/
theorem relativeProjectiveSerreMap_bijective_of_finiteOpenCover
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {J : Type u} [Finite J]
    (U : J → Y.Opens) [∀ j, QuasiCompact (U j).ι] (hU : iSup U = ⊤)
    (M : X.Modules) [M.IsQuasicoherent]
    (hCover : ∀ (N : Y.Modules) [N.IsQuasicoherent] (q : ℕ),
      Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e
        (relativeSerreCoverCoefficients U N) M q))
    (N : Y.Modules) [N.IsQuasicoherent] (q : ℕ) :
    Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e N M q) := by
  classical
  let I := {N : Y.Modules // N.IsQuasicoherent}
  let F := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  let K := F.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let H := preadditiveCoyoneda.obj (Opposite.op K)
  let W := relativeTopDifferentialCoefficientsFunctor p n
  let A (N : I) (q : ℕ) := Ext.{u + 1} M (W.obj N.val) q
  let B (N : I) (q : ℕ) :=
    K ⟶ (((DerivedCategory.singleFunctor Y.Modules 0).obj N.val)⟦-(n : ℤ)⟧)⟦(q : ℤ)⟧
  let φ (N : I) (q : ℕ) : A N q →+ B N q :=
    relativeProjectiveSerreShiftMap R ι a p f h n e N.val M q
  let : K.IsLE (n : ℤ) := by
    exact (DerivedCategory.Plus.isLE_ι_obj_iff
      ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) (n : ℤ)).mpr
      (projectiveProjection_derivedSingle_zero_isLE R ι a p f h n e M)
  have hs : ∀ N₀ : I, ∃ C Q : I,
      Nonempty (AddMonoidHom.CoefficientDevissageSequence φ N₀ C Q) := by
    intro N₀
    obtain ⟨Q₀, s, t, hst, hC, hQ, hS, hW, -⟩ :=
      exists_shortExact_finiteOpenCover_differentialCoefficients U p n hU N₀.val
    let C : I := ⟨relativeSerreCoverCoefficients U N₀.val, hC⟩
    let Q : I := ⟨Q₀, hQ⟩
    let S := ShortComplex.mk s t hst
    let T := (Triangle.shiftFunctor (DerivedCategory Y.Modules) (-(n : ℤ))).obj
      hS.singleTriangle
    have hT : T ∈ distTriang (DerivedCategory Y.Modules) :=
      Triangle.shift_distinguished _ hS.singleTriangle_distinguished _
    let ε := (-(n : ℤ)).negOnePow
    refine ⟨C, Q, ⟨{
      a₁ := fun r => (Ext.mk₀ (W.map s)).postcomp M (Nat.add_zero r)
      a₂ := fun r => (Ext.mk₀ (W.map t)).postcomp M (Nat.add_zero r)
      aδ := fun r => hW.extClass.postcomp M rfl
      b₁ := fun r => ((H.shift (r : ℤ)).map T.mor₁).hom
      b₂ := fun r => ((H.shift (r : ℤ)).map T.mor₂).hom
      bδ := fun r => (H.homologySequenceδ T (r : ℤ) ((r + 1 : ℕ) : ℤ) (by omega)).hom
      coverMap := fun r => ε • φ C r
      cover_bijective := ?_
      comm₁ := ?_
      comm₂ := ?_
      commδ := ?_
      exact_a₂ := ?_
      exact_a₃ := ?_
      exact_a₁ := ?_
      exact_b₂ := ?_
      exact_b₃ := ?_
      exact_b₁ := ?_
      injective_a₁_zero := ?_
      injective_b₁_zero := ?_ }⟩⟩
    · intro r
      change Function.Bijective (fun x => ε • φ C r x)
      apply (MulAction.bijective ε).comp
      exact (relativeProjectiveSerreShiftMap_bijective_iff R ι a p f h n e C.val M r).mpr
        (hCover N₀.val r)
    · intro r
      ext x
      change φ N₀ r x ≫ (shiftFunctor (DerivedCategory Y.Modules) (r : ℤ)).map
          (ε • ((DerivedCategory.singleFunctor Y.Modules 0).map s)⟦-(n : ℤ)⟧') =
        ε • φ C r (x.comp (Ext.mk₀ (W.map s)) (Nat.add_zero r))
      have hm (v : T.obj₁ ⟶ T.obj₂) :
          (shiftFunctor (DerivedCategory Y.Modules) (r : ℤ)).map (ε • v) =
            ε • (shiftFunctor (DerivedCategory Y.Modules) (r : ℤ)).map v :=
        Functor.map_zsmul _
      rw [hm, Linear.comp_units_smul]
      exact congrArg (fun z => ε • z)
        (relativeProjectiveSerreShiftMap_naturality_coefficients R ι a p f h n e s M r x).symm
    · intro r
      ext x
      change (ε • φ C r x) ≫ (shiftFunctor (DerivedCategory Y.Modules) (r : ℤ)).map
          (ε • ((DerivedCategory.singleFunctor Y.Modules 0).map t)⟦-(n : ℤ)⟧') =
        φ Q r (x.comp (Ext.mk₀ (W.map t)) (Nat.add_zero r))
      have hm (v : T.obj₂ ⟶ T.obj₃) :
          (shiftFunctor (DerivedCategory Y.Modules) (r : ℤ)).map (ε • v) =
            ε • (shiftFunctor (DerivedCategory Y.Modules) (r : ℤ)).map v :=
        Functor.map_zsmul _
      rw [hm, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
        Int.units_mul_self, one_smul]
      exact (relativeProjectiveSerreShiftMap_naturality_coefficients
        R ι a p f h n e t M r x).symm
    · intro r
      ext x
      exact (relativeProjectiveSerreShiftMap_extClass R ι a p f h n e hS hW M r x).symm
    · intro r
      exact (ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₂' M hW r)
    · intro r
      exact (ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' M hW r (r + 1) rfl)
    · intro r
      exact (ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₁' M hW r (r + 1) rfl)
    · intro r
      exact (ShortComplex.ab_exact_iff_function_exact _).mp
        (H.homologySequence_exact₂ T hT (r : ℤ))
    · intro r
      exact (ShortComplex.ab_exact_iff_function_exact _).mp
        (H.homologySequence_exact₃ T hT (r : ℤ) ((r + 1 : ℕ) : ℤ) (by omega))
    · intro r
      exact (ShortComplex.ab_exact_iff_function_exact _).mp
        (H.homologySequence_exact₁ T hT (r : ℤ) ((r + 1 : ℕ) : ℤ) (by omega))
    · let : Mono (W.map s) := hW.mono_f
      exact Ext.postcomp_mk₀_injective_of_mono M (W.map s)
    · exact DerivedCategory.coyoneda_shifted_singleTriangle_zero_injective (n : ℤ) K hS
  exact (relativeProjectiveSerreShiftMap_bijective_iff R ι a p f h n e N M q).mp
    (AddMonoidHom.bijective_of_coefficient_devissage φ hs q ⟨N, inferInstance⟩)

end AlgebraicGeometry.Scheme.Cohomology
