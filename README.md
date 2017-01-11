This branch (no-rescale-cyc) is a fork of master that attempts to remove the
accursed 'RescaleCyc' class. I got pretty close; the only part I'm unable to fix
is due to the interaction between overlapping instances and the 'Sub' constructor
for 'Cyc'. The problem is this: I moved the overlapping instances of
'RescaleCyc (Cyc t)' to overlapping 'Rescale (UCyc P/D)' instances. This is pretty
natural. The problem is that with overlapping instances, you are *required*
to write the constraint 'Rescale (UCyc t m P zq) (UCyc t m P zq')' on 'Cyc.rescalePow'.
However, we need a constraint w.r.t some hidden index 'l' when we recurse in the
'Sub' case. One solution is to force an embed, but this is a pretty hefty price.
On the other hand, it lets us get rid of RescaleCyc!

The constraints get annoying since they involve UCyc; it would probably be best
to export constraint synonyms for rescalePow/rescaleDec from Cyc.

**UPDATE**
After a meeting, we discussed some of the challenges. We could get rid of overlapping instances
by changing the generic instance to ZqBasic, but this solves nothing: the Cyc funcs still need
a constraint 'Rescale (UCyc ...)' in order to be polymorphic over the base ring.

We could get rid of the Sub optimization for Cyc.rescalePow, but we still need the
constraint, and the beauty of RescaleCyc is that it does not involve the index.
Currently, this would be the only constraint that involves both the index and the base ring,
which are otherwise orthogonal. Also, there's no way to write rescaleCyc with just
the Rescale dictionary on the base rings (indeed, the optimized algorithm doesn't even use
Rescale on the base rings.)

We don't have a concrete reason yet, but we expect that having the constraint that involves the index and base ring might mean death in the compiler.

We're stuck with RescaleCyc for now.

--------------------------------------------------------------------------------

This repository contains several Haskell libraries:

  * The `lol` directory contains the Haskell library Λ ○ λ (Lol),
    described in the paper
    [Λ ○ λ: Functional Lattice Cryptography](https://eprint.iacr.org/2015/1134). More
    documentation can be found on
    [Hackage](https://hackage.haskell.org/package/lol). This is the
    core of the project, and you'll need to install it to use anything
    else.

  * The `apps` directory contains example cryptographic applications
    built using Lol. If you are interested in using our example
    applications, you will need this library. It is on Hackage
    [here](https://hackage.haskell.org/package/lol-apps). If you are
    just writing your own applications, you don't need to install this
    library.

  * The `challenges` directory contains code to generate and verify
    RLWE and RLWR challenges, which are described [here](https://web.eecs.umich.edu/~cpeikert/rlwe-challenges).

  * The `compiler` directory contains an unmaintained, primitive FHE
    compiler for Lol. Eventually, this will work in conjuction with
    lol-apps to transform plaintext descriptions of algorithms into
    their homomorphic counterparts.

Installing lol:

The easiest way to install Lol is to use stack, which is included in
the [Haskell Platform](https://www.haskell.org/platform/).
```
> stack setup
> stack install lol
```
You can run unit tests with `stack test lol`. You can run
microbenchmarks with `stack bench lol`. You can configure the
benchmarks by editing `lol/benchmarks/BenchConfig.hs`.

Installing lol-apps:
```
> stack install lol-apps
```
You can run unit tests with `stack test lol-apps`. You can run
benchmarks with `stack bench lol-apps`. An example of how to use each
application is included and is built automatically when you install
lol-apps.

Developing in the lol ecosystem:

./ghci path/to/file

This command builds the C++ library for lol-cpp and the loads
all imported files from lol* packages from source. You may
need to run 'stack bench lol-cpp' or similar first to install
the necessary dependencies.

You can load all top-level executables with ./ghci AllMain.hs