# Coq à la Carte - A Practical Approach to Modular Syntax with Binders

This repository contains the accompanying Coq code for the above mentioned paper by Yannick Forster and Kathrin Stark, accepted for publication at CPP '20.

## Compilation

Our development is tested under Coq 8.9.1 with the Equations package 1.2+8.9 (see below on how to install).

You need a development version of MetaCoq, which is contained in this zip file as well. Everything is handled by the `Makefile` and you can just type `make`.

## Coq installtion

If you need to install Coq first, make sure you have `opam 2` installed and set up. You can then type

``` shell
# opam switch create coq.8.9.1 4.07.1
# eval $(opam env)
# opam pin add coq 8.9.1
# opam pin add coq-equations 1.2+8.9
```

to install Coq and the Equations package.
