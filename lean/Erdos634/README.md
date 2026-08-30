
## Docstring convention (2026-08-30)

A docstring explains what a declaration is *for*; it must not assert what the declaration does not
prove.  Where a statement is arithmetic and its geometric reading needs further input, the
docstring says so — `AngleArithmetic.no_perpendicular_cut` is the worked example, and
`SideNoB.side_no_b_e_one` and `BlockNeverCompletes.every_corner_breaks` were corrected the same way.

A scan for docstrings that assert a geometric consequence over an arithmetic statement flags 18
declarations; three are corrected, the rest read as explanation rather than assertion.  Anyone
adding to the corpus should keep that distinction, because it is the same confusion that put ten
wrong VERIFIED labels in the papers.
