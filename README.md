This branch (offline-suppress) was created expressly for generating (real)
RLWE/RLWR challenges. Previously, the 'suppress' phase of generation required
an internet connection to download the necessary NIST beacons and certificate.
However, we generate the challenges on an air-gapped machine, so we have to
supply the beacons and certificates separately and load them from disk during
the 'suppress' phase. This branch modifies the 'suppress' stage to do exactly
that.

This branch was forked a long time ago, but very few changes have been made
to the challenge code in the interim. Thus we will keep this branch (or merge it)
just in case we want to release more challenges later.

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
