# AS coefficient HomEquiv-zero repair 4

The closed run `remote-8e5b2c8d38cd47ebb7f3db16ab7b7725` accepted the prior AS statement/proof code except for the raw `comp_zero` term at line 135. Its expected type was `E 0 = 0`, while the supplied term stated the raw composition equation. The separate Proper missing import belongs to another author.

Only that local proof changes: unfold the exact original HomEquiv E, apply native `Adjunction.homEquiv_apply`, type the actual original unit composite with the right-functor zero at literal `presheafToSheaf.obj` endpoints, and apply `comp_zero`. The zero normalization stays entirely at that canonical head; no constantSheaf/sheafify carrier cast, transparency flag, new realization or desired-law premise occurs.

The actual presheaf hz calculation, map_pow/ZMod.pow_card step, native naturality transport, all other source and both fixed wrappers are byte-identical. Exact input, repaired output, delta and closed-run provenance are preserved here. Other owned native paths and prior fixed packets are held.

READY/HOLD, uncompiled by this author. Root retries only the same AS3 changed modules plus necessary dependencies. No compiler/probe, Git/index, registry, README, network or extra test/lint chain was used here; untouched AS consumers remain untargeted.
