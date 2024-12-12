This repository contains the code for the paper "Maps between isolated points on modular curves".

The code is divided into two directories:

- `level_7` contains code for computing the isolation graph of closed points on modular curves of level 7 with j-invariant 2268945/128, see Section 6 of the paper.

- `x0` contains code for computing which exceptional j-invariants can give rise to isolated points on the modular curves X_0(n), see Section 7 of the paper.

This code relies on code by Jeremy Rouse, Andrew V. Sutherland and David Zureick-Brown for computing genera of modular curves (see file `groups/gl2.m` in the following [repository](https://github.com/AndrewVSutherland/ell-adic-galois-images)), as well as data files computed by David Zywina containing the adelic Galois image of all known exceptional j-invariants (see file `data-files/exceptional_images.dat` in the following [repository](https://github.com/davidzywina/OpenImage)).