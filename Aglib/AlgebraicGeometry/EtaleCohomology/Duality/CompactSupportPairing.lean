/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.YonedaPairing

/-!
# The Yoneda pairing on compactly supported cohomology of abelian sheaves

Let `j : U ⟶ X` be an open immersion and `Λ` a ring. For sheaves `F`, `G` of modules over the
constant ring sheaf `Λ_U` with underlying abelian sheaves `F₀`, `G₀`, the Yoneda pairing
`moduleLowerShriekPairing` of `Duality/YonedaPairing`, transported through the comparison
`moduleLowerShriekCohomologyAddEquiv : Ext^r(Λ_X, j_! F) ≃+ CompactSupport.H j F₀ r`, is the
pairing

`compactSupportPairing : H^r_c(U, F₀) × Ext^s(F, G) → H^{r+s}_c(U, G₀)`

on the compactly supported cohomology `CompactSupport.H` of `CompactSupport/Cohomology`
(`H^r_c(U, F) = H^r(X, j_! F)`, Milne, *Lectures on Étale Cohomology* v2.21, p. 92; the pairing of
p. 103). It is biadditive (`compactSupportPairingHom`), natural in `F` and `G` with
`CompactSupport.H.map` of the underlying maps (`compactSupportPairing_naturality`,
`compactSupportPairing_comp_mk₀`), and sends the original connecting map `CompactSupport.δ` of
the underlying short exact sequence to precomposition with the extension class, sign `+1`
(`compactSupportPairing_δ`).

For `Λ = ULift (ZMod n)` and `G = moduleRootsOfUnity U n`, `compactSupportRootsPairing` lands in
`CompactSupport.H j (Kummer.Coefficients.mu U n) (r + s)` through `CompactSupport.H.map` of the
original isomorphism `moduleRootsOfUnityUnderlyingIso`. No trace or perfectness is asserted;
`HasExt` is a size hypothesis and the three Ext universes are independent.
-/

@[expose] public noncomputable section

universe w w' w'' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type (u + 1)) [Ring Λ]
  [HasExt.{w} (ModuleSheaf U Λ)] [HasExt.{w'} (ModuleSheaf X Λ)]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X)]

/-- The pairing `H^r_c(U, F₀) × Ext^s(F, G) → H^t_c(U, G₀)`, `r + s = t`, on compactly supported
cohomology of the underlying abelian sheaves: the Yoneda pairing transported through
`moduleLowerShriekCohomologyAddEquiv`. -/
def compactSupportPairing {F G : ModuleSheaf U Λ} {r s t : ℕ}
    (x : CompactSupport.H.{w''} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r)
    (e : Ext.{w} F G s) (h : r + s = t) :
    CompactSupport.H.{w''} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj G) t :=
  moduleLowerShriekCohomologyAddEquiv.{w', w''} j Λ G t
    (moduleLowerShriekPairing j Λ ((moduleLowerShriekCohomologyAddEquiv.{w', w''} j Λ F r).symm x)
      e h)

/-- The transported pairing as a biadditive map. -/
def compactSupportPairingHom (F G : ModuleSheaf U Λ) (r s t : ℕ) (h : r + s = t) :
    CompactSupport.H.{w''} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r →+
      Ext.{w} F G s →+
        CompactSupport.H.{w''} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj G) t :=
  ((moduleLowerShriekPairingHom j Λ F G r s t h).comp
      (moduleLowerShriekCohomologyAddEquiv.{w', w''} j Λ F r).symm.toAddMonoidHom).compr₂
    (moduleLowerShriekCohomologyAddEquiv.{w', w''} j Λ G t).toAddMonoidHom

theorem compactSupportPairingHom_apply_apply (F G : ModuleSheaf U Λ) (r s t : ℕ)
    (h : r + s = t)
    (x : CompactSupport.H.{w''} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r)
    (e : Ext.{w} F G s) :
    compactSupportPairingHom.{w, w'} j Λ F G r s t h x e =
      compactSupportPairing.{w, w'} j Λ x e h :=
  rfl

variable {j Λ}

/-- The transported pairing on an element in the image of the comparison is the Yoneda pairing. -/
theorem compactSupportPairing_moduleLowerShriekCohomologyAddEquiv {F G : ModuleSheaf U Λ}
    {r s t : ℕ} (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r)
    (e : Ext.{w} F G s) (h : r + s = t) :
    compactSupportPairing.{w, w'} j Λ (moduleLowerShriekCohomologyAddEquiv.{w', w''} j Λ F r c) e
        h =
      moduleLowerShriekCohomologyAddEquiv.{w', w''} j Λ G t
        (moduleLowerShriekPairing j Λ c e h) := by
  rw [compactSupportPairing, AddEquiv.symm_apply_apply]

/-- Naturality in the first variable: for `u : F ⟶ F'`, `φ(u_* x, e') = φ(x, u^* e')`, where
`u_*` is `CompactSupport.H.map` of the underlying map and `u^*` is precomposition with `u`. -/
theorem compactSupportPairing_naturality {F F' G : ModuleSheaf U Λ} (u : F ⟶ F') {r s t : ℕ}
    (x : CompactSupport.H.{w''} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r)
    (e' : Ext.{w} F' G s) (h : r + s = t) :
    compactSupportPairing.{w, w'} j Λ
        (CompactSupport.H.map j ((SheafOfModules.toSheaf (constantRing U Λ)).map u) r x) e' h =
      compactSupportPairing.{w, w'} j Λ x ((Ext.mk₀ u).comp e' (zero_add s)) h := by
  obtain ⟨c, rfl⟩ := (moduleLowerShriekCohomologyAddEquiv.{w', w''} j Λ F r).surjective x
  rw [compactSupportPairing_moduleLowerShriekCohomologyAddEquiv, CompactSupport.H.map_apply,
    ← moduleLowerShriekCohomologyAddEquiv_naturality,
    compactSupportPairing_moduleLowerShriekCohomologyAddEquiv,
    moduleLowerShriekPairing_naturality]

/-- Naturality in the second variable: for `v : G ⟶ G'`, `φ(x, v_* e) = v_* φ(x, e)`, with `v_*`
on compactly supported cohomology `CompactSupport.H.map` of the underlying map. -/
theorem compactSupportPairing_comp_mk₀ {F G G' : ModuleSheaf U Λ} (v : G ⟶ G') {r s t : ℕ}
    (x : CompactSupport.H.{w''} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r)
    (e : Ext.{w} F G s) (h : r + s = t) :
    compactSupportPairing.{w, w'} j Λ x (e.comp (Ext.mk₀ v) (add_zero s)) h =
      CompactSupport.H.map j ((SheafOfModules.toSheaf (constantRing U Λ)).map v) t
        (compactSupportPairing.{w, w'} j Λ x e h) := by
  rw [compactSupportPairing, compactSupportPairing, moduleLowerShriekPairing_comp_mk₀,
    moduleLowerShriekCohomologyAddEquiv_naturality, CompactSupport.H.map_apply]

/-- Connecting maps, sign `+1`: for a short exact sequence `S` of `Λ_U`-modules, the original
connecting map `CompactSupport.δ` of compactly supported cohomology for the underlying short
exact sequence corresponds to precomposition with the extension class of `S`:
`φ(δ x, e) = φ(x, δ e)`. -/
theorem compactSupportPairing_δ {S : ShortComplex (ModuleSheaf U Λ)} (hS : S.ShortExact)
    {G : ModuleSheaf U Λ} {r s s' t : ℕ}
    (x : CompactSupport.H.{w''} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj S.X₃) r)
    (e : Ext.{w} S.X₁ G s) (hs : 1 + s = s') (h : r + 1 + s = t) (h' : r + s' = t) :
    compactSupportPairing.{w, w'} j Λ
        (CompactSupport.δ j (hS.map_of_exact (SheafOfModules.toSheaf (constantRing U Λ))) r
          (r + 1) rfl x) e h =
      compactSupportPairing.{w, w'} j Λ x (hS.extClass.comp e hs) h' := by
  obtain ⟨c, rfl⟩ := (moduleLowerShriekCohomologyAddEquiv.{w', w''} j Λ S.X₃ r).surjective x
  have hc := moduleLowerShriekCohomologyAddEquiv_connecting.{w', w''} j Λ S hS r c
  rw [compactSupportPairing_moduleLowerShriekCohomologyAddEquiv]
  refine (congrArg (fun y => compactSupportPairing.{w, w'} j Λ y e h) hc.symm).trans ?_
  rw [compactSupportPairing_moduleLowerShriekCohomologyAddEquiv,
    moduleLowerShriekPairing_extClass hS c e rfl hs h h']

section RootsOfUnity

variable (j) (n : ℕ) [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- The pairing with values in `H_c(U, μ_n)` for sheaves of `ℤ/n`-modules:
`H^r_c(U, F₀) × Ext^s(F, μ_n) → H^{r+s}_c(U, μ_n)`, `compactSupportPairing` followed by
`CompactSupport.H.map` of the original isomorphism `toSheaf μ_n ≅ Kummer.Coefficients.mu U n`. -/
def compactSupportRootsPairing {F : ModuleSheaf U (ULift.{u + 1} (ZMod n))} {r s t : ℕ}
    (x : CompactSupport.H.{w''} j
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F) r)
    (e : Ext.{w} F (moduleRootsOfUnity U n) s) (h : r + s = t) :
    CompactSupport.H.{w''} j (GroupCohomology.Kummer.Coefficients.mu U n) t :=
  CompactSupport.H.map j (moduleRootsOfUnityUnderlyingIso U n).hom t
    (compactSupportPairing.{w, w'} j _ x e h)

theorem compactSupportRootsPairing_def {F : ModuleSheaf U (ULift.{u + 1} (ZMod n))}
    {r s t : ℕ}
    (x : CompactSupport.H.{w''} j
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F) r)
    (e : Ext.{w} F (moduleRootsOfUnity U n) s) (h : r + s = t) :
    compactSupportRootsPairing.{w, w'} j n x e h =
      CompactSupport.H.map j (moduleRootsOfUnityUnderlyingIso U n).hom t
        (compactSupportPairing.{w, w'} j _ x e h) :=
  rfl

end RootsOfUnity

end AlgebraicGeometry.Scheme.EtaleCohomology
