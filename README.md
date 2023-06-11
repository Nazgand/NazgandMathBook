# This is a collection of math notes.

I first tried using knowls in PreTeXt HTML. Unfortunately, the HTML book is not properly viewable offline.

Later, I used Zim to create a wiki. I disliked that it made a new image file for each equation.

Thus, multiple LaTeX files reference each other. They may also reference kig files or images for geometry.

# I implemented some proofs in Lean.

[Click here for Lean installation instructions](https://leanprover-community.github.io/get_started.html#regular-install)

To initialize the Lean code and download mathlib, try:

```
cd NazgandLean3
leanproject get-mathlib-cache
./_target/deps/mathlib/scripts/mk_all.sh
```
I needed to increase the memory limit from the default in the settings of the Lean3 VSCode extention.
