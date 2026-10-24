/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.PairingEquiv
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The linear-system functor `LinSys_{L/X/S}`

Let `p : X ⟶ S` be a morphism of schemes and `L` a line bundle on `X`. For a scheme `T` over `S`
write `X_T = X ×_S T`, with projections `g_T : X_T ⟶ X` and `p_T : X_T ⟶ T`. Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, Def. 3.12, p. 25, defines

`LinSys_{L/X/S}(T) = {D ∈ Div(X_T/T) : O_{X_T}(D) ≅ L_T ⊗ p_T^* N for some invertible N on T}`.

Here a relative effective Cartier divisor is a closed subscheme `D ⊆ X_T`, recorded by its ideal
sheaf data, whose ideal is invertible and which is flat over `T` (Kleiman, Def. 3.3, p. 22;
`Scheme.Hom.IsRelativeEffectiveCartier`). The condition on `O(D) = I_D^∨` is stated for the ideal
itself: `IsLinearSystemDivisor p L T D` asks for an invertible `N` on `T` with

`I_D ≅ p_T^* N ⊗ g_T^* L^∨`,

which is Kleiman's condition with `N` replaced by `N^∨` (dualize both sides). Using the ideal and
the pulled-back dual `g_T^* L^∨` avoids double duals and duals of pulled-back bundles.

* `familyMap p t : X_{T'} ⟶ X_T`, the base-change map of the family, and
  `isPullback_familyMap`: its square over `t : T' ⟶ T` is cartesian.
* `IsLinearSystemDivisor.comap`: the condition is stable under base change, through the flat
  ideal comparison `flatQuotient_idealPullbackMap_isIso` (the remark after Def. 3.6, p. 23) and
  `IsRelativeEffectiveCartier.of_isPullback`.
* `linearSystemFunctor p L : (Over S)ᵒᵖ ⥤ Type u`, with pullback of closed subschemes
  (`IdealSheafData.comap`) along the base-change maps `familyMap p`, as for the Hilbert functor.
* `evaluationPairing L : L ⊗ L^∨ ⟶ 𝒪_X`, an isomorphism; its pullback to `X_T` pairs maps
  `M ⟶ g_T^* L` with maps `M ⊗ g_T^* L^∨ ⟶ 𝒪` (`pullbackPairingOfEquiv`).

No hypothesis on `p` or `S` is needed here; the representability statement is in
`Picard/LinearSystem/Representability`. Consumer: Picard plan row F15 and the proof of Kleiman's
Thm 4.8 (p. 30), where `Z ×_P Z` is identified with a linear system.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.LinearSystem

open Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **The base-change map of the family** `X_{T'} ⟶ X_T` along `t : T' ⟶ T`: the map
`(familyScheme p).map t`, typed with source and target the fibre products `X ×_S T'` and
`X ×_S T`. Statements use this map, so that all module sheaves on `X_T` are typed over the same
expression `Limits.pullback p T.hom`. It is `(familyScheme p).map t` by definition, and equals the
`pullback.lift` form `Scheme.Hom.familyMap p T.hom T'.hom t.left (Over.w t)`
(`RelativePicard.Classes.familyMap_eq_familyScheme_map`). -/
def familyMap {T T' : Over S} (t : T' ⟶ T) : Limits.pullback p T'.hom ⟶ Limits.pullback p T.hom :=
  (familyScheme p).map t

theorem familyMap_fst {T T' : Over S} (t : T' ⟶ T) :
    familyMap p t ≫ Limits.pullback.fst p T.hom = Limits.pullback.fst p T'.hom :=
  familyScheme_map_fst p t

theorem familyMap_snd {T T' : Over S} (t : T' ⟶ T) :
    familyMap p t ≫ Limits.pullback.snd p T.hom = Limits.pullback.snd p T'.hom ≫ t.left :=
  familyScheme_map_snd p t

theorem familyMap_id (T : Over S) : familyMap p (𝟙 T) = 𝟙 (Limits.pullback p T.hom) :=
  (familyScheme p).map_id T

theorem familyMap_comp {T T' T'' : Over S} (s : T'' ⟶ T') (t : T' ⟶ T) :
    familyMap p (s ≫ t) = familyMap p s ≫ familyMap p t :=
  (familyScheme p).map_comp s t

/-- The base-change square of the family `X ×_S T ⟶ T` along `t : T' ⟶ T` is cartesian. -/
theorem isPullback_familyMap {T T' : Over S} (t : T' ⟶ T) :
    IsPullback (familyMap p t) (Limits.pullback.snd p T'.hom)
      (Limits.pullback.snd p T.hom) t.left := by
  refine IsPullback.of_right ?_ (familyMap_snd p t) (IsPullback.of_hasPullback p T.hom)
  rw [familyMap_fst, Over.w t]
  exact IsPullback.of_hasPullback p T'.hom

/-- The pullback of a closed subscheme `D` along `b` is the fibre product with `D`: the square
`(D.comap b).subscheme ⟶ D.subscheme`, `D.comap b ↪ Y`, `D ↪ X`, `b : Y ⟶ X` is cartesian. -/
theorem isPullback_comap {Y Z : Scheme.{u}} (b : Y ⟶ Z) (D : Z.IdealSheafData) :
    IsPullback ((D.comapIso b).hom ≫ Limits.pullback.snd b D.subschemeι)
      (D.comap b).subschemeι D.subschemeι b :=
  (IsPullback.of_hasPullback b D.subschemeι).flip.of_iso (D.comapIso b).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc])
    (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      Scheme.IdealSheafData.comapIso_inv_subschemeι])
    (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])

variable (L : LineBundle X)

/-- **Divisors of the linear system** (Kleiman, Def. 3.12, ideal form): `D` is a relative
effective Cartier divisor of `X_T ⟶ T` whose ideal is isomorphic to `p_T^* N ⊗ g_T^* L^∨` for some
line bundle `N` on `T`. -/
def IsLinearSystemDivisor (T : Over S) (D : (Limits.pullback p T.hom).IdealSheafData) : Prop :=
  Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (Limits.pullback.snd p T.hom) ∧
    ∃ N : LineBundle T.left, Nonempty (Scheme.Hom.idealModule D.subschemeι ≅
      (show (Limits.pullback p T.hom).Modules from tensorSheaf (Limits.pullback p T.hom)
        ((Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).obj N.val)
        ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj (dualLineBundle X L).val)))

/-- **Linear-system divisors are stable under base change**: for `t : T' ⟶ T`, the pullback of a
divisor of the linear system along `X_{T'} ⟶ X_T` is one, with `N` replaced by `t^* N`. -/
theorem IsLinearSystemDivisor.comap {T T' : Over S} (t : T' ⟶ T)
    {D : (Limits.pullback p T.hom).IdealSheafData} (hD : IsLinearSystemDivisor p L T D) :
    IsLinearSystemDivisor p L T' (D.comap (familyMap p t)) := by
  obtain ⟨hR, N, ⟨e⟩⟩ := hD
  let b := familyMap p t
  have H := isPullback_familyMap p t
  have H' := isPullback_comap b D
  have := hR.isClosedImmersion
  have := hR.flat
  have := Scheme.Hom.flatQuotient_idealPullbackMap_isIso (Limits.pullback.snd p T.hom) t.left
    (Limits.pullback.snd p T'.hom) b D.subschemeι (D.comap b).subschemeι _ H'.w H H'
  refine ⟨hR.of_isPullback H H', pullbackLineBundle t.left N, ⟨?_⟩⟩
  let eN : (Scheme.Modules.pullback b).obj
      ((Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).obj N.val) ≅
        (Scheme.Modules.pullback (Limits.pullback.snd p T'.hom)).obj
          ((Scheme.Modules.pullback t.left).obj N.val) :=
    (pullbackComp b (Limits.pullback.snd p T.hom)).app N.val ≪≫
      (pullbackCongr (familyMap_snd p t)).app N.val ≪≫
      ((pullbackComp (Limits.pullback.snd p T'.hom) t.left).app N.val).symm
  let eL : (Scheme.Modules.pullback b).obj
      ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj (dualLineBundle X L).val) ≅
        (Scheme.Modules.pullback (Limits.pullback.fst p T'.hom)).obj (dualLineBundle X L).val :=
    (pullbackComp b (Limits.pullback.fst p T.hom)).app _ ≪≫
      (pullbackCongr (familyMap_fst p t)).app _
  exact (asIso (Scheme.Hom.idealPullbackMap D.subschemeι (D.comap b).subschemeι b _ H'.w)).symm ≪≫
    (Scheme.Modules.pullback b).mapIso e ≪≫ pullbackTensorMapIso b _ _ ≪≫
    tensorSheafIso _ eN eL

/-- **The linear-system functor** `LinSys_{L/X/S}` (Kleiman, Def. 3.12, p. 25) on all schemes over
`S`: `T` goes to the divisors of the linear system on `X_T`, and `t : T' ⟶ T` acts by pullback of
closed subschemes along `familyMap p t : X_{T'} ⟶ X_T`. -/
def linearSystemFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := {D : (Limits.pullback p T.unop.hom).IdealSheafData //
    IsLinearSystemDivisor p L T.unop D}
  map {T T'} t := TypeCat.ofHom fun D =>
    ⟨D.1.comap (familyMap p t.unop), D.2.comap p L t.unop⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun D => Subtype.ext ?_
    change D.1.comap (familyMap p (𝟙 T.unop)) = D.1
    rw [familyMap_id, Scheme.IdealSheafData.comap_id]
  map_comp {T T' T''} t t' := by
    refine ConcreteCategory.hom_ext _ _ fun D => Subtype.ext ?_
    change D.1.comap (familyMap p (t'.unop ≫ t.unop)) =
      (D.1.comap (familyMap p t.unop)).comap (familyMap p t'.unop)
    rw [familyMap_comp, Scheme.IdealSheafData.comap_comp]

theorem linearSystemFunctor_map_coe {T T' : (Over S)ᵒᵖ} (t : T ⟶ T')
    (D : (linearSystemFunctor p L).obj T) :
    ((linearSystemFunctor p L).map t D).1 = D.1.comap (familyMap p t.unop) :=
  rfl

/-- The evaluation pairing `L ⊗ L^∨ ⟶ 𝒪_X` (braiding, then dual evaluation). -/
def evaluationPairing :
    (show X.Modules from tensorSheaf X L.val (dualLineBundle X L).val) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
  (tensorSheafBraiding X L.val (dualLineBundle X L).val).hom ≫ (dualEvaluationIso X L).hom

instance isIso_evaluationPairing : IsIso (evaluationPairing L) := by
  unfold evaluationPairing
  infer_instance

end AlgebraicGeometry.Scheme.LinearSystem
