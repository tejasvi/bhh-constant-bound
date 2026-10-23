# Lean 4 proof of beta >= 0.6496497227 (native evaluation by native_decide)

Theorems (`BHH/BetaN3W20.lean`):

    theorem BHH.betaBoundV3At_N_w20    : BetaBoundV3At (6496497227 / 10 ^ 10)     -- beta >= 0.6496497227 for every beta with DongCaoK30 beta
    theorem BHH.bhhBetaBoundV3At_N_w20 : BHHBetaBoundV3At (6496497227 / 10 ^ 10)  -- the same for the BHH constant

They combine two parts:
- the three C_k bounds `BHH.mainBoundsV3_N : MainBoundsV3` (`BHH/MainN3.lean`): C_3 >= 0.0117130195, C_4 >= 0.0063707166,
  C_5 >= 0.0035280362;
- the window-3 bound `W3Prod20.w3_bound_lit : W3BoundAt (30379504113 / 10000000000000)` (`W3Prod20/Final.lean`):
  sum_{k=6}^{22} C_k >= 0.0030379504113, certified on the grid (20,10,48);

so beta >= 5/8 + C_3 + C_4 + C_5 + 0.0030379504113 >= 0.6496497227. The paper's bound beta >= 0.6508522354 uses the window-3
constant 0.0042404631563 of the grid (60,30,144); that constant is not proved in Lean here.

The statements are in `BHH/StatementW3.lean`. They are implications from two named hypotheses. `GreenFormula`, in
`BHH/Defs.lean`, is Green's formula (3.1). `VertexLemmaSeg`, in `BHH/DefsV2.lean`, is Lemma 3.1 with Remark 3.2 and the
gradient formula (3.2), along a segment. The beta bounds also assume `DongCaoK30 beta`, Theorem 3 of Dong and Cao with
K = 30, and the theorem for the BHH constant assumes it for every beta with `IsBHHConstant beta`.

Axioms: the two theorems depend on `propext`, `Classical.choice`, `Quot.sound` and 5,671 auxiliary axioms of
`native_decide`, and on nothing else; `lean BHH/AxN3W20.lean` prints them into `axioms_N3W20.txt`. Of the auxiliary
axioms, 5,661 are for box shards (62 for C_3, 1,142 for C_4 and 4,457 for C_5), 6 for the g tables and 4 for the
window-3 bound (`W3Prod20.shard00`, `tint`, `nondeg`, `chpos`).

The claims of the window-3 check, in `W3Prod20/Claims.lean`, are untrusted input. They are enclosures computed by the C
evaluator of the window-3 certificate, run with the triple-entry classes of this Lean code, and the shard `W3Prod20.S00`
checks every one of them. Checking the proof does not need their source. To regenerate them, run
`bash provenance/w3/regen_claims.sh` from this directory. It writes `Claims.lean`, `Grid.lean`, `TInt.lean` and
`Nondeg.lean` into a work directory, `./_w3regen` or `$W3_REGEN_DIR` for a read-only copy, checks their sha256 and
compares them with the files here (`provenance/w3/RECIPE.md`).

Build: Lean v4.35.0-rc3 and Mathlib c55e6e786f49 (`lean-toolchain`, `lake-manifest.json`). `lake build` covers the
libraries `BHH`, `BHHCert`, `W2`, `W2Cert`, `W3`, `W3Cert` and `W3Prod20`; the shard, chain and assembly modules of the C_k
part and the final assembly are compiled with plain `lean -o` in the order that `BUILD.md` gives ("Build route").
`BUILD.md` also describes the files and a full kernel replay. `SHA256SUMS` lists every file of this directory except itself
and this README.

Lemma, proposition and remark numbers in the comments of the Lean files are those of the paper, except "Lemma 4" in the
window-2 files, which names the polar-box bound (G6) of `W2/GeoProps.lean`. Green's formula and the gradient formula are
cited there as (2.1) and (2.2); they are (3.1) and (3.2) in the paper. Section numbers in the comments may differ from those
of the paper.
