# IsomClAbVarFqCommEndAlg

Description
--

A Magma package to compute (unpolarized) Fq-isomorphism classes of abelian varieties over Fq belonging to an isogeny class with commutative Fq-endomorphism ring, for any finite field Fq.

For the theory on which this code is based, see the `References` section at the bottom.

This package requires the packages [`AlgEt`](https://github.com/stmar89/AlgEt) (all spec files) and [`AbVarFq`](https://github.com/stmar89/AbVarFq).

Please send comments and bug reports to `stefano.marseglia89@gmail.com`.

Details
--

For complete descriptions and more details we refer to the [`List of commands`](https://github.com/stmar89/IsomClAbVarFqCommEndAlg/blob/main/doc/ListOfCommands.md).
Use the magma command `AttachSpec("spec")`, after opening magma in the folder where you have downloaded the repo.

In the folder [`examples`](https://github.com/stmar89/IsomClAbVarFqCommEndAlg/tree/main/examples) you will find files containing the code to reproduce the examples from the papers in the reference below, which should be of help to get a quick start on the functionalities.

As in [`AbVarFq`](https://github.com/stmar89/AbVarFq), the abelian varieties have type `AbelianVarietyFq`.
In this package the information about the isomorphism class of each abelian variety is stored in the attribute `IsomDataCommEndAlg=<I,M,L,S>`, where `I` is a `Z[pi,q/pi]`-ideal which encodes the local information of all l-Tate modules (for all l neq p) together with the étale-local and local-étale part of the Dieudonné module, `M` represents the local-local part of the Dieudonné module, and `L` determines the position of variety in the orbit of the class group of the endomorphism ring `S`, which acts on the local information just described.
This representation is slightly different what what we do in the paper: in `Algorithm 7`, we represent each isomorphism class by a 5-tuple `(I0,II,I1,(I^l)_l,J)` where `I0` is the étale local part of the Dieudonné module, `II` its local-local part, `I1` its local-étale, `I^l` represents the l-Tate modules (l \neq p), and `J` is an invertible ideal of the endomorphism ring. So, `I` in the code is equivalent to the combined information of `I0`,`I1` and all the `I^l`, `M` is the same as `II` and `L` is the same as `J`. See `Remark 7.6` in the paper for further discussion.


References
--
Check my webpage for more up-to-date bibliography info.

Jonas Bergström, Valentijn Karemaker, and Stefano Marseglia,<br>
*Abelian varieties over finite fields with commutative endomorphism algebra: theory and algorithms*,<br>
TODO ADD ARXIV LINK
