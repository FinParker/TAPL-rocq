## Requirements

[Make Sure you have rocq-prover at least 9.0.0](https://rocq-prover.org/docs/using-opam)

## Coq Makefile生成与编译

(1) Run this command to generate Makefile.

```sh
coq_makefile -f _CoqProject -o Makefile
```

(2) Make
```sh
make
```

(3) Make clean

```sh
make clean
make cleanall  # clean *.aux and *.timing
```

(4) Compile single file

```sh
make <rocq_file>.vo
```
Or,

```sh
coqc -Q . LF <rocq_file>.v
```