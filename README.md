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
Use the magma command `AttachSpec("spec")` after opening magma in the folder where you have downloaded the repo.

In the folder [`examples`](https://github.com/stmar89/IsomClAbVarFqCommEndAlg/tree/main/examples) you will find files containing the code to reproduce the examples from the paper in the reference below. This should help to get a quick start on the functionalities.

As in [`AbVarFq`](https://github.com/stmar89/AbVarFq), the abelian varieties have type `AbelianVarietyFq`.
In this package the information about the isomorphism class of each abelian variety is stored in the attribute `IsomDataCommEndAlg=<I,M,J,S>`, where `I` is a `Z[pi,q/pi]`-ideal which encodes the local information of all l-Tate modules (for all l neq p) together with the étale-local and local-étale part of the Dieudonné module, `M` represents the local-local part of the Dieudonné module, and `J` determines the position of the abelian variety in the orbit of the class group of the endomorphism ring `S`, which acts on the local information just described.

One can compute the action of the semilinear Frobenius and Verschiebung on each `M` (in an appropriate finite quotient) using `SemilinearOperators`. We refer to the documentation of that intrinsic for details.

The representation `IsomDataCommEndAlg=<I,M,J,S>` is slightly different from what we have in `Algorithm 7` in the paper. There we represent each isomorphism class by a 5-tuple `(I0,M,I1,(I^l)_l,J)` where `I0` is the étale-local part of the Dieudonné module, `M` its local-local part, `I1` its local-étale, `I^l` represents the l-Tate modules (l \neq p), and `J` is an invertible ideal of the endomorphism ring. So, `I` in the code is equivalent to the combined information of `I0`,`I1` and all the `I^l`, while `M` and `J` are the same. See `Remark 7.6` in the paper for further discussion.

We provide a second way to represnet abelian varieties over Fq with commutative endomorphism algebra, which we call `Generalized Deligne Module`.
A `Generalized Deligne Module` is a pair `<II,MM>` such that `<II,M ⊗ ℤ>`.
For each abelian variety over Fq with the attribute IsomDataCommEndAlg assigned, one can recover a representation 
of the form `<II,MM>` with `II` a `Z[pi,q/pi]`-ideal and  


References
--
Check my webpage for more up-to-date bibliography info.

Jonas Bergström, Valentijn Karemaker, and Stefano Marseglia,<br>
*Abelian varieties over finite fields with commutative endomorphism algebra: theory and algorithms*,<br>
TODO ADD ARXIV LINK
