## Requirements

[Make Sure you have rocq-prover at least 9.0.0](https://rocq-prover.org/docs/using-opam)

## How to build this project

(A) Just run the `./run_make.sh`

```sh
./run_make.sh
```

Or

(B-1) Run this command to generate Makefile.

```sh
coq_makefile -f _CoqProject -o Makefile
```

(B-2) Make
```sh
make
```

(B-3) Make clean

```sh
make clean
make cleanall  # clean *.aux and *.timing
```

(B-4) Compile single file

```sh
make <rocq_file>.vo  
# or
coqc -Q . LF <rocq_file>.v
```