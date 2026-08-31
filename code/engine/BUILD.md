# Building the engines

Every `cengine_*` binary in `private/bin/` is built from a source in this directory. The binary
name does **not** always match the source name: five of them are successive revisions of
`cengine_iso.cpp`, which is why a search for `*rx2*.cpp` finds nothing.

    R=$(git rev-parse --show-toplevel)
    P=$(brew --prefix gmp)
    cd code/engine
    g++ -O2 -std=c++17 -I$P/include -L$P/lib -o $R/private/bin/<name> <source>.cpp -lgmpxx -lgmp

| Binary | Source |
|---|---|
| `cengine_rx2` | `cengine_iso.cpp` |
| `cengine_gen` | `cengine_iso.cpp` |
| `cengine_fan` | `cengine_iso.cpp` |
| `cengine_learn` | `cengine_iso.cpp` |
| `cengine_p7` | `cengine_iso.cpp` |
| `cengine_c2` | `cengine_c2.cpp` |
| `cengine_dump` | `cengine_dump.cpp` |
| `cengine_eq` | `cengine_eq.cpp` |
| `cengine_iso` | `cengine_iso.cpp` |
| `cengine_tiles` | `cengine_tiles.cpp` |

## Verification (2026-08-31)

Rebuilding `cengine_rx2` from the committed `cengine_iso.cpp` reproduces the shipped binary at
293800 bytes exactly, and on `uni_f12_b4c2.txt` returns `RESULT EXHAUSTED_NO_TILING nodes=565` --
the verdict and node count logged in `runrx.log`. The member certifications are reproducible from
committed source.
