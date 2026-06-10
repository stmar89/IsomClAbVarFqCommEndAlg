# IsomClAbVarFqCommEndAlg

Description
--

A Magma package to compute (unpolarized) Fq-isomorphism classes of abelian varieties over Fq belonging to an isogeny class with commutative Fq-endomorphism ring, for any finite field Fq.

For the theory on which this code is based, see the `References` section at the bottom.
The package contains the implementation of the algorithms in the paper, together with the ones contained in the accompanying [`appendix`](Computational_Appendix.pdf).
The appendix contains also several technical intermediate lemmas and algorithms, also discussed below.

Please send comments and bug reports to `stefano.marseglia89@gmail.com`.

Installation
--
- Clone the repository [`AlgEt`](https://github.com/stmar89/AlgEt). If you are on a version of Magma prior to 2.29 then attach all `spec`  files. If you are using Magma 2.29 or more recent, then attach only `specMtrx` and `specMod`.
- Clone the repository [`AbVarFq`](https://github.com/stmar89/AbVarFq) and make sure to attach the corresponding `spec` file.

Quick start
---
The main intrinsic provided by the package is `IsomorphismClassesCommEndAlg`. Here is a first example:
```
AttachSpec("~/AbVarFq/spec"); AttachSpec("~/AlgEt/specMod"); AttachSpec("~/AlgEt/specMtrx"); //AttachSpec("~/AlgEt/spec"); // this spec file is part of Magma since 2.29
AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");    
PP<x>:=PolynomialRing(Integers());
isog:=IsogenyClass(x^6-3*x^4+2*x^3-12*x^2+64);
E:=DeligneAlgebra(isog);
iso:=IsomorphismClassesCommEndAlg(isog);
A:=iso[1];
ends:=[EndomorphismRing(A):A in iso];
[ Index(MaximalOrder(E),S) : S in ends ];
```
In the folder [`examples`](https://github.com/stmar89/IsomClAbVarFqCommEndAlg/tree/main/examples), you'll find the code to reproduce the examples from the paper in the reference below.

Details
--

For complete descriptions and more details we refer to the [`List of commands`](https://github.com/stmar89/IsomClAbVarFqCommEndAlg/blob/main/doc/ListOfCommands.md).
Use the magma command `AttachSpec("spec")` after opening magma in the folder where you have downloaded the repo.

As in [`AbVarFq`](https://github.com/stmar89/AbVarFq), the abelian varieties have type `AbelianVarietyFq`.
In this package the information about the isomorphism class of each abelian variety is stored in the attribute `IsomDataCommEndAlg=<I,M,J,S>`, where `I` is a `Z[pi,q/pi]`-ideal encoding the local information of all l-Tate modules (for all l neq p) together with the étale-local and local-étale part of the Dieudonné module, `M` represents the local-local part of the Dieudonné module, and `J` determines the position of the abelian variety in the orbit of the class group of the endomorphism ring `S`, which acts on the local information just described.

The representation as tuple `<I,M,J,S>` is slightly different from the isomorphism classes of objects in the category C_&pi; from Definition 5.1 and Theorem 5.2 of the main paper.
The intrinsic `GeneralizedDeligneModule` takes as input an abelian variety whose attribute `IsomDataCommEndAlg` is assigned and computes a pair `<II,MM>` which belongs to C_&pi; (after tensoring `MM` with the p-adic integers).
The ideal `II` encodes the local information away from the characteristic of `Fq`, `MM` is the Dieudonné module (not just its local-local part), and the p-parts of `II` and `MM` are compatible. See Remark IX in the [`appendix`](Computational_Appendix.pdf) for details.

In order to recover all isomorphism classes, as tuples `<I,M,J,S>`, we do the following:
  - The isomorphism classes of the `I`s are computed using the intrinsic `IsomorphismClassesAwayFromLocalLocalCommEndAlg`; see Algorithm B in the [`appendix`](Computational_Appendix.pdf).
  - The isomorphism classes of the `M`s are computed using the intrinsic `IsomorphismClassesDieudonneModulesCommEndAlg`, which is a combination of Algorithm A from the [`appendix`](Computational_Appendix.pdf) together with Algorithms 1 and 2 from the main paper.
  - The action of the semilinear Frobenius and Verschiebung on each `M` (in an appropriate finite quotient) is recovered by the intrinsic `SemilinearOperators`.
  - The endomorphism ring `S` of each isomorphism class can be recovered using the intrinsic `EndomorphismRing` from [`AbVarFq`](https://github.com/stmar89/AbVarFq); see Algorithm C in the [`appendix`](Computational_Appendix.pdf).
  - All tuples `<I,M,J,S>` are computed by the intrinsic `IsomorphismClassesCommEndAlg`, which is based on the wrapper Algorithm D from the [`appendix`](Computational_Appendix.pdf).

Changelog
--
- <code>v1.0.0</code> Version accompanying the submission of the paper.
- <code>v1.0.1</code> Bugfixes:
  - A bug affecting the correct loading of the examples has been fixed.
  - The primes of the `Dieudonne Algebra` above a given place of the `Deligne Algebra` are now sorted according to the action of `sigma`.
  - A bug affecting in some cases the computation of the precision required to verify when a `WR`-ideal is a `WR{F,V}`-ideal leading to incorrect outputs, is now fixed.
         
  This version has been tested with Magma 2.29-6.
- <code>v1.0.2</code> Bugfix:
  * The representative function returned with `units_quotient_fixed_sigma` now gives representatives which are units at all places of `OA'` and not just modulo `ff_prod`. See Remark IV in the [`appendix`](Computational_Appendix.pdf).
  
  This version has been tested with Magma 2.29-7.
  
  The bug above does not affect the content of the referenced paper below.

References
--
Check my webpage for more up-to-date bibliography info.

Jonas Bergström, Valentijn Karemaker, and Stefano Marseglia,<br>
*Abelian varieties over finite fields with commutative endomorphism algebra: theory and algorithms*,<br>
[https://arxiv.org/abs/2409.08865](https://arxiv.org/abs/2409.08865)
