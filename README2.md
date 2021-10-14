

## generating Clight ast
(for linux) to generate .v files for lite.c, run

    ./gen lite.c

## dependency
works on:
compcert version=3.9, linux 64
coqtop 8.13.2
opam switch 4.12.0

## issues
It's not gonna compile because lot's definitions are changed / missing

one should be able to use the .v files (Clight ast in Coq) as long as the VST version is compatible with compcert3.9.