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

As of `v1.1.0-alpha`, the program allows the user to chose two slightly different methods to compute and represent the isomorphism classes. They are regulated by the parameters `slopes` and `slopesDieudonneModules` which can take the values `"(0,1)"` and `"all"`. We stress that the method `"(0,1)"` is mathematically identical to the one implemented in `v1.0.2` described in the referenced paper together with the [`accompanying appendix`](Computational_Appendix.pdf) , while the method `"all"` is an undocumented but easy generalization. The differences between the two methods are detailed in the next paragraph. The method `"(0,1)"` is the default. In the example above, if one wants to use the method `"all"` use `iso:=IsomorphismClassesCommEndAlg(isog:slopesDieudonneModules:="all");` instead.

As in [`AbVarFq`](https://github.com/stmar89/AbVarFq), the abelian varieties have type `AbelianVarietyFq`.
In this package the information about the isomorphism class of each abelian variety is stored in the attribute `IsomDataCommEndAlg=<I,M,J,S,slopes>`, where:
- `I` is a `Z[pi,q/pi]`-ideal that when, using the method `"(0,1)"`, encodes the local information of all l-Tate modules (for all l neq p) together with the étale-local and local-étale part of the Dieudonné module, while, with the method `"all"`, it encodes only the l-Tate modules.
- `M` represents the local-local part of the Dieudonné module with the method `"(0,1)"`, while it represents the Dieudonné module at all places above p when the method used is `"all"`.
- `J` determines the position of the abelian variety in the orbit of the class group of the endomorphism ring `S`, which acts on the local information just described.
- the flag `slopes` simply records which method was used.

The representation as tuple `<I,M,J,S,slopes>` is slightly different from the isomorphism classes of objects in the category C_&pi; from Definition 5.1 and Theorem 5.2 of the main paper.
The intrinsic `GeneralizedDeligneModule` takes as input an abelian variety whose attribute `IsomDataCommEndAlg` is assigned and computes a pair `<II,MM>` which belongs to C_&pi; (after tensoring `MM` with the p-adic integers).
The ideal `II` encodes the local information away from the characteristic of `Fq`, `MM` is the Dieudonné module (not just its local-local part), and the p-parts of `II` and `MM` are compatible. See Remark IX in the [`appendix`](Computational_Appendix.pdf) for details.

In order to recover all isomorphism classes, as tuples `<I,M,J,S,slopes>`, we do the following:
  - If the method used is `"(0,1)"`, the isomorphism classes of the `I`s are computed using the intrinsic `IsomorphismClassesAwayFromLocalLocalCommEndAlg`; see Algorithm B in the [`appendix`](Computational_Appendix.pdf). If instead one uses `"all"` the intrinsic `IsomorphismClassesAwayFrom_pCommEndAlg` is used.
  - The isomorphism classes of the `M`s are computed using the intrinsic `IsomorphismClassesDieudonneModulesCommEndAlg` which is an implementation of Algorithm 2 of the main paper.
 This intrinsic calls internally `WRIdealsWithFVStableExtensionToOA` which is a combination of Algorithm A from the [`appendix`](Computational_Appendix.pdf) together with Algorithms 1 from the main paper.  The method is passed as the VarArg `slopes`.
  - The action of the semilinear Frobenius and Verschiebung on each `M` (in an appropriate finite quotient) is recovered by the intrinsic `SemilinearOperators`.
  - The endomorphism ring `S` of each isomorphism class can be recovered using the intrinsic `EndomorphismRing` from [`AbVarFq`](https://github.com/stmar89/AbVarFq); see Algorithm C in the [`appendix`](Computational_Appendix.pdf).
  - All tuples `<I,M,J,S,slopes>` are computed by the intrinsic `IsomorphismClassesCommEndAlg`, which is based on the wrapper Algorithm D from the [`appendix`](Computational_Appendix.pdf).
  The VarArg `slopesDieudonneModules` determines which method is used.

Changelog
--
- <code>v1.0.0</code> Version accompanying the submission of the paper.</li>
- <code>v1.0.1</code> Bugfixes:
  - A bug affecting the correct loading of the examples has been fixed.</li>
  - The primes of the `Dieudonne Algebra` above a given place of the `Deligne Algebra` are now sorted according to the action of `sigma`.</li>
  - A bug affecting in some cases the computation of the precision required to verify when a `WR`-ideal is a `WR{F,V}`-ideal leading to incorrect outputs, is now fixed.</li>
         
  This version has been tested with Magma 2.29-6.
- <code>v1.0.2</code> Bugfix:
  * The representative function returned with `units_quotient_fixed_sigma` now gives representatives which are units at all places of `OA'` and not just modulo `ff_prod`. See Remark IV in the [`accompanying appendix`](Computational_Appendix.pdf).</li>
  
  This version has been tested with Magma 2.29-7.
  
  The bug above did not affect the content of the paper referenced below.
  
- <code>v1.1.0-alpha</code>
  * New functionality: The computation of the isomorphism classes now can be performed in two different ways using methods `"(0,1)"` or `"all"`.
  * Code refactoring: The large monolithic intrinsics `DieudonneAlgebraCommEndAlg` and `IsomorphismClassesDieudonneModulesCommEndAlg` have been divided into several intermediate intrinsics. Several functions returned as output by `DieudonneAlgebraCommEndAlg` are now their own intrinsics. We refer to the documentation for a description of the new intriniscs.
 
  This version has been tested with Magma 2.29-7.

References
--
Check my webpage for more up-to-date bibliography info.

Jonas Bergström, Valentijn Karemaker, and Stefano Marseglia,<br>
*Abelian varieties over finite fields with commutative endomorphism algebra: theory and algorithms*,<br>
[https://arxiv.org/abs/2409.08865](https://arxiv.org/abs/2409.08865)
