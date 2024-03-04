# This is a collection of math notes.

I first tried using knowls in PreTeXt HTML. Unfortunately, the HTML book is not properly viewable offline.

Later, I used Zim to create a wiki. I disliked that it made a new image file for each equation.

Thus, multiple LaTeX files reference each other. They may also reference kig files or images for geometry.

# I implemented some proofs in Lean 3; they are still good to look at and verify

To initialize the Lean 3 code and download mathlib, try:

```
sudo apt install mathlibtools
cd NazgandLean3
leanproject get-mathlib-cache
./_target/deps/mathlib/scripts/mk_all.sh
```
I needed to increase the memory limit from the default in the settings of the Lean 3 VSCode extention.
```
Lean: Memory Limit
Set a memory limit (in megabytes) for the Lean server.

54000
```
I needed to increase the memory limit from the default in the settings of the Lean 3 VSCode extention.
```
Lean: Time Limit
Set a deterministic timeout (it is approximately the maximum number of memory allocations in thousands) for the Lean server.

10000000
```
I also needed to disable the Lean 4 VSCode extention for VSCode to realize it should use Lean 3.

[Click here for my Lean 4 code](https://github.com/Nazgand/NazgandLean4)
