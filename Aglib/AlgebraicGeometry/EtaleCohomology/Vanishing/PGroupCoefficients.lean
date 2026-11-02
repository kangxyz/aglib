/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PGroupModuleSheaves
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Vanishing after an exact coefficient functor and a p-group trivialization

This is an honest reduction lemma: the constant-coefficient vanishing is an
explicit input. In the curve application, L is original scalar forgetting
followed by actual extension by zero, and that input is proved geometrically
on the proper compactification. It is not an assumed cohomological-dimension
bound. No finite underlying additive group or Noetherian coefficient ring is
inserted into the reusable statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

open Constructible.Modules

universe u r e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]
  {X Z : Scheme.{u}} [ConnectedSpace X]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]
  (Y : Scheme.FiniteEtale X) [PreGaloisCategory.IsGalois Y]
  [Surjective Y.obj.hom] [ConnectedSpace Y.obj.left]
  [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]

/-- Original cohomology vanishing is transported through the already-proved
actual p-group coefficient induction, after any displayed exact functor.
The scheme, scalar and original Ext universes are retained independently. -/
theorem subsingleton_H_obj_of_pGroup_trivialization
    (p : ℕ) [Fact p.Prime] (hY : IsPGroup p (Aut Y))
    (L : ModuleSheaf R X ⥤ AbelianSheaf.{u, u + 1} Z)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (q : ℕ)
    (hconstant : ∀ (N : ModuleCat.{u + 1} R), ∀ [Module.Finite R N],
      (∀ n : N, p • n = 0) →
        Subsingleton (Sheaf.H.{e}
          (L.obj ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} R)).obj N)) q))
    (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton (Sheaf.H.{e} (L.obj F) q) := by
  apply property_of_pGroup_trivialization Y p hY
    (fun E => Subsingleton (Sheaf.H.{e} (L.obj E) q))
    hconstant ?_ ?_ F M hM t
  · intro E E' i hE
    let : Subsingleton (Sheaf.H.{e} (L.obj E) q) := hE
    exact (cohomologyMapIso_bijective ((L.mapIso i).symm) q).injective.subsingleton
  · intro S hS h₁ h₃
    let : Subsingleton (Sheaf.H.{e} (S.map L).X₁ q) := h₁
    let : Subsingleton (Sheaf.H.{e} (S.map L).X₃ q) := h₃
    exact Sheaf.H.subsingleton_middle_of_shortExact (hS.map_of_exact L) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
