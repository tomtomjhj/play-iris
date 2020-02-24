# build

```
git submodule update --init
opam switch create ./ <ocaml version>
opam pin coq <coq version>
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
make build-dep
opam pin add iris-examples
make -j
```
