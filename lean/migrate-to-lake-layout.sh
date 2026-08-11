#!/bin/bash
# migrate-to-lake-layout.sh — NOT RUN. Kept ready in case the project ever acquires its own Mathlib.
#
# WHAT IT WOULD DO. Move every module from lean/X.lean to lean/Erdos634/X.lean so that Lake's module
# naming matches the imports the corpus already uses (`import Erdos634.X`). Today Lake, whose srcDir
# is lean/, names those modules X, so `lake build` cannot resolve a single import.
#
# WHY IT IS NOT RUN. The layout is not the binding constraint. This project holds no Mathlib of its
# own and no lake-manifest.json; it borrows LEAN_PATH from a sibling project carrying a 7.4 GB
# Mathlib build. `lake build` here would therefore have to fetch and build Mathlib from scratch
# before it could compile anything, whatever the directory layout. Fixing the layout alone changes
# nothing that works today, while costing:
#
#   * 68 file moves;
#   * a name collision to resolve — lean/Erdos634.lean is a substantive module (the arithmetic layer
#     of the prime case), but Lake wants that path for the library root, so it must be renamed and
#     All.lean promoted in its place;
#   * 41 `\texttt{lean/X.lean}` citations to rewrite across both papers, plus lean/PAPER_MAP.md,
#     README.md and lean/check-all.sh.
#
# Verification does not depend on any of this: `bash lean/check-all.sh` compiles all 68 modules
# against the borrowed Mathlib and is the check that actually runs.
#
# IF THE PROJECT EVER GAINS ITS OWN MATHLIB, the migration is:
#
#   set -e
#   cd "$(dirname "$0")/.."
#   mkdir -p lean/Erdos634
#   git mv lean/Erdos634.lean lean/Erdos634/PrimeArithmetic.lean      # free the root path
#   for f in lean/*.lean; do
#     [ "$(basename "$f")" = All.lean ] && continue
#     git mv "$f" "lean/Erdos634/$(basename "$f")"
#   done
#   git mv lean/All.lean lean/Erdos634.lean                            # aggregator becomes the root
#   sed -i '' 's/^import Erdos634\.Erdos634$/import Erdos634.PrimeArithmetic/' lean/Erdos634.lean
#   sed -i '' 's|lean/\([A-Za-z0-9]*\)\.lean|lean/Erdos634/\1.lean|g' paper/*.tex README.md lean/PAPER_MAP.md
#   # then re-point lean/check-all.sh at lean/Erdos634/*.lean and re-run it.
#
# Do this as its own piece of work, with the full check-all.sh pass afterwards — not tacked onto
# other changes.
echo "This script is documentation, not an action. Read it before running anything." >&2
exit 1
