# Minting a Zenodo DOI

This repo is **private**. Zenodo's automatic GitHub integration only archives **public** repos, so:

**Option A — when ready to go public:**
1. In Zenodo (logged in via GitHub), open *Account → GitHub* and flip the toggle ON for
   `ElVec1o/erdos_634_proof_vico`.
2. Make the GitHub repo public.
3. Create a GitHub **Release** (e.g. tag `v1.0.0`) — Zenodo archives it and mints a DOI
   automatically. `.zenodo.json` (in this repo) pre-fills the metadata.

**Option B — keep private, upload manually:**
1. Go to <https://zenodo.org/uploads/new>, upload a zip of this repo (or the paper PDF + code).
2. Paste the metadata from `.zenodo.json`; choose "Preprint"; reserve a DOI before publishing.

Either way, after the DOI exists, add it to `README.md` and `CITATION.cff`, and cite it when
contacting reviewers (see `proof/reviewers-and-journals.md`) and on the erdosproblems.com/634 page.
