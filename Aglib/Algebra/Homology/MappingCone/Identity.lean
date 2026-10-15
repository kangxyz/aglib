/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.BiproductPushout
public import Aglib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # The identity-cone functor on abelian cochain complexes

Source:
`Quillen/Waldhausen/SplitComplexes/FactorizationFunctor.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`bb3576f24fe649de3950079b904d286221a10cdc9fc8832a80cd4bf2bfa1a977`.
Selected declarations: identityConeFunctor.
Source:
`Quillen/Waldhausen/Cylinder/Pushout.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`b760358f4aa9027f932f99e0995fa531b339463b1f583f7e1ae8891b0e893514`.
Selected declarations: isPushout_of_degreewise, identityConeTermIso,
  identityConeTermIso_naturality, identityConeFunctor_map_isPushout.
Source:
`Quillen/Waldhausen/Cylinder/ZeroEndpoint.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`854e6ef243c7560d5891a3684ac31ad97ee34a8810606e993a7da90e5a9e61ab`.
Selected declarations: identityCone_isZero.
Source:
`Quillen/Algebra/Homology/MappingConeBiprod.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`4b95511976c458eb12ca317b8f4ac2190ccdcdd40f065cdc57c796359d8b291c`.
Selected declarations: mappingCone_map_add.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/FlasqueShift.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`78944f4baecd627e51378eba3c20d6c215bd1e010a46566c0bfc2cf673a8fd62`.
Selected declarations: identityConeFunctor_additive, coneSequence_shortExact,
  identityConeFunctor_map_mono, identityConeFunctor_shortExact.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The functor sending an integer-indexed cochain complex `K` to the cone of `𝟙 K`. -/
def identityConeFunctor : CochainComplex A ℤ ⥤ CochainComplex A ℤ where
  obj K := mappingCone (𝟙 K)
  map f := mappingCone.map _ _ f f (by simp)
  map_id K := mappingCone.map_id _
  map_comp f g := by
    ext n
    simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map]

private lemma mappingCone_map_add {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) (a a' : K₁ ⟶ K₂) (b b' : L₁ ⟶ L₂)
    (h : f ≫ b = a ≫ g) (h' : f ≫ b' = a' ≫ g) :
    mappingCone.map f g (a + a') (b + b') (by simp [Preadditive.comp_add, Preadditive.add_comp, h,
      h']) =
      mappingCone.map f g a b h + mappingCone.map f g a' b' h' := by
  ext n
  simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map,
    Preadditive.comp_add, Preadditive.add_comp]

theorem isPushout_of_degreewise
    {K L M N : CochainComplex A ℤ} {f : K ⟶ L} {g : K ⟶ M} {i : L ⟶ N} {j : M ⟶ N}
    (h : ∀ n, IsPushout (f.f n) (g.f n) (i.f n) (j.f n)) : IsPushout f g i j := by
  have w : f ≫ i = g ≫ j := by ext n; exact (h n).w
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i j w)
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact (isColimitMapCoconePushoutCoconeEquiv (eval A (ComplexShape.up ℤ) n) w).symm
    (h n).isColimit

/-- The degree-`n` term of the identity cone, identified with `K.X (n + 1) ⊞ K.X n`. -/
def identityConeTermIso (K : CochainComplex A ℤ) (n : ℤ) :
    (identityConeFunctor.obj K).X n ≅ K.X (n + 1) ⊞ K.X n where
  hom := biprod.lift ((mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl)
    ((mappingCone.snd (𝟙 K)).v n n (add_zero n))
  inv := biprod.desc ((mappingCone.inl (𝟙 K)).v (n + 1) n (by omega))
    ((mappingCone.inr (𝟙 K)).f n)
  hom_inv_id := by
    dsimp only [identityConeFunctor]
    simp [mappingCone.ext_from_iff _ (n + 1) n rfl]
  inv_hom_id := by ext <;> simp

theorem identityConeTermIso_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (identityConeTermIso K n).hom ≫ biprod.map (f.f (n + 1)) (f.f n) =
      (identityConeFunctor.map f).f n ≫ (identityConeTermIso L n).hom := by
  apply biprod.hom_ext <;>
    simp [identityConeTermIso, identityConeFunctor, mappingCone.map,
      mappingCone.ext_from_iff _ (n + 1) n rfl]

theorem identityConeFunctor_map_isPushout
    {K L M N : CochainComplex A ℤ} {f : K ⟶ L} {g : K ⟶ M} {i : L ⟶ N} {j : M ⟶ N}
    (h : IsPushout f g i j) :
    IsPushout (identityConeFunctor.map f) (identityConeFunctor.map g)
      (identityConeFunctor.map i) (identityConeFunctor.map j) := by
  apply isPushout_of_degreewise
  intro n
  have H := IsPushout.biprod_map (h.map (eval A (ComplexShape.up ℤ) (n + 1)))
    (h.map (eval A (ComplexShape.up ℤ) n))
  apply H.of_iso (identityConeTermIso K n).symm (identityConeTermIso L n).symm
    (identityConeTermIso M n).symm (identityConeTermIso N n).symm
  all_goals simp only [Iso.symm_hom]; apply (cancel_epi (identityConeTermIso _ n).hom).1
  all_goals simp only [Iso.hom_inv_id_assoc]
  all_goals simp only [eval_map]
  all_goals rw [← Category.assoc, identityConeTermIso_naturality]
  all_goals simp

theorem identityCone_isZero {K : CochainComplex A ℤ} (hK : IsZero K) :
    IsZero (mappingCone (𝟙 K)) := by
  rw [IsZero.iff_id_eq_zero]
  ext n
  have h := (mappingCone.isZero_X_iff (𝟙 K) n).2
    ⟨(eval A (ComplexShape.up ℤ) (n + 1)).map_isZero hK,
      (eval A (ComplexShape.up ℤ) n).map_isZero hK⟩
  exact h.eq_of_src _ _

instance identityConeFunctor_additive : (identityConeFunctor (A := A)).Additive where
  map_add := by
    intro K L f g
    exact mappingCone_map_add (𝟙 K) (𝟙 L)
      f g f g (by simp) (by simp)

lemma coneSequence_shortExact (K : CochainComplex A ℤ) :
    (mappingCone.triangleRotateShortComplex (𝟙 K)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (mappingCone.triangleRotateShortComplexSplitting (𝟙 K) n).shortExact)

lemma identityConeFunctor_map_mono {K L : CochainComplex A ℤ} (f : K ⟶ L) [Mono f] :
    Mono (identityConeFunctor.map f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let : Mono (f.f (n + 1)) := (HomologicalComplex.eval A (.up ℤ) (n + 1)).map_mono f
  let : Mono (f.f n) := (HomologicalComplex.eval A (.up ℤ) n).map_mono f
  have h : Mono ((identityConeFunctor.map f).f n ≫ (identityConeTermIso L n).hom) := by
    rw [← identityConeTermIso_naturality]
    infer_instance
  exact mono_of_mono _ (identityConeTermIso L n).hom

lemma identityConeFunctor_shortExact {S : ShortComplex (CochainComplex A ℤ)} (hS : S.ShortExact) :
    (S.map identityConeFunctor).ShortExact := by
  let F : CochainComplex A ℤ ⥤ CochainComplex A ℤ := identityConeFunctor
  let : F.Additive := ⟨by
    intro K L f g
    exact mappingCone_map_add (𝟙 K) (𝟙 L)
      f g f g (by simp) (by simp)⟩
  have hp : IsPushout S.f (0 : S.X₁ ⟶ 0) S.g (0 : 0 ⟶ S.X₃) :=
    isPushout_of_isColimit_cokernel S.zero hS.gIsCokernel
      (isZero_zero _) _ _
  have hFp := identityConeFunctor_map_isPushout hp
  have hFzero : IsZero (F.obj (0 : CochainComplex A ℤ)) := identityCone_isZero (isZero_zero _)
  have hc : IsColimit (CokernelCofork.ofπ (F.map S.g)
      (show F.map S.f ≫ F.map S.g = 0 by rw [← F.map_comp, S.zero, F.map_zero])) := by
    refine Cofork.IsColimit.mk _ (fun s => hFp.desc s.π 0 (by
      rw [CokernelCofork.condition s, comp_zero])) ?_ ?_
    · intro s
      exact hFp.inl_desc _ _ _
    · intro s m hm
      apply hFp.hom_ext
      · rw [hFp.inl_desc]
        exact hm
      · exact hFzero.eq_of_src _ _
  have : Mono S.f := hS.mono_f
  have : Mono (F.map S.f) := identityConeFunctor_map_mono S.f
  have : Epi (F.map S.g) := epi_of_isColimit_cofork hc
  change (S.map F).ShortExact
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _ hc
    mono_f := by change Mono (F.map S.f); infer_instance
    epi_g := by change Epi (F.map S.g); infer_instance }

end CochainComplex
