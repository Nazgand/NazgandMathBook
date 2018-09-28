# This is a collection of math notes.

I first tried using knowls in PreTeXt HTML. Unfortunately, the HTML book is not properly viewable offline.

Later, I used Zim to create a wiki. I disliked that it made a new image file for each equation.

Thus, multiple LaTeX files reference each other. They may also reference `.kig` files or images for geometry.

# [Click here for Nazgand's Lean 4 Code](https://github.com/Nazgand/NazgandLean4)

# Compiling `.tex` documents

All documents reference `NazgandStyle.tex`, which includes Lua code to allow all documents to reference all other documents without specifying each document with `\externaldocument`. Thus, use `LuaLaTeX`.

## Run `./Maintain.sh Compile` to compile all `.tex` files under the `LaTeX` directory.

## TeXstudio:
- `Options > Configure TeXstudio > Commands > LuaLaTeX` should be set to `lualatex --shell-escape -synctex=1 -interaction=nonstopmode %.tex`, or something else that works.
- `Options > Configure TeXstudio > Build > Default Compiler` should be set to `LuaLaTeX`.

## VS Code with the `james-yu.latex-workshop` extension can work with modifications to `settings.json`:
```
    "latex-workshop.latex.rootFile.indicator": "\\begin{document}",
    "latex-workshop.latex.tools": [
        {
            "name": "lualatex-shell",
            "command": "lualatex",
            "args": [
                "--shell-escape",
                "-synctex=1",
                "-interaction=nonstopmode",
                "-file-line-error",
                "%DOC%"
            ],
            "env": {
                "TERM": "xterm-256color"
            }
        }
    ],
    "latex-workshop.latex.recipes": [
        {
            "name": "luaLaTeX --shell-escape",
            "tools": [
                "lualatex-shell"
            ]
        },
```