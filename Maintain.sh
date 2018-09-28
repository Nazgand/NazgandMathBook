#!/usr/bin/env bash

# --- Configuration ---
GitRoot="$(git rev-parse --show-toplevel)"
LatexRoot="${GitRoot}/LaTeX"
PDFRoot="${GitRoot}/PDFs"

# File extensions to remove during Clean
TrashExts=(aux bbl fdb_latexmk fls log out synctex.gz)

# Globbing options
shopt -s nullglob
shopt -s globstar

# --- Commands ---

Clean () {
	echo "--- Cleaning Trash Files ---"
	for TrashExt in "${TrashExts[@]}"
	do
		for FilePath in "${LatexRoot}"/**/*."${TrashExt}"
		do
			rm -v "${FilePath}"
		done
	done
}

Compile () {
	# Compiling twice is typically required for resolving cross-references (xr/zref)
	for i in {1..2}
	do
		echo "--- Compilation Pass ${i} ---"
		for FilePath in "${LatexRoot}"/**/*.tex
		do
			# Skip the style file itself
			if [[ "${FilePath}" -ef "${LatexRoot}/NazgandStyle.tex" ]]
			then continue
			fi

			ParentDirectory="$(dirname "${FilePath}")"
			BaseName="$(basename -- "${FilePath}")"
			
			# Calculate relative path for pretty printing
			RelPath="$(realpath --relative-to="${LatexRoot}" "${FilePath}")"
			echo "Compiling: ${RelPath}"
			
			# Run lualatex inside the directory to keep artifacts local
			(cd "${ParentDirectory}" && lualatex --shell-escape "${BaseName}")
		done
	done
}

PascalCase () {
	echo "--- Normalizing Filenames to PascalCase ---"
	for FilePath in "${LatexRoot}"/**/*.tex
	do
		Dir="$(dirname "${FilePath}")"
		Base="$(basename -- "${FilePath}" .tex)"
		
		# 1. Capitalize the first letter of every word
		# 2. Remove spaces, underscores, and hyphens
		NewBase=$(echo "${Base}" | sed -E 's/(\b[a-z])/\U\1/g; s/[[:space:]_-]//g')
		
		if [[ "${Base}" != "${NewBase}" ]]
    then
			# Rename the .tex file
			echo "Renaming Tex: ${Base}.tex -> ${NewBase}.tex"
			git mv "${FilePath}" "${Dir}/${NewBase}.tex"

			# Rename the corresponding .pdf in PDFRoot if it exists
			# Calculate relative directory to maintain structure
			RelDir="$(realpath --relative-to="${LatexRoot}" "${Dir}")"
			# Handle root case
			if [[ "${RelDir}" == "." ]]
      then RelDir=""
      else RelDir="/${RelDir}"
      fi
			
			OldPdf="${PDFRoot}${RelDir}/${Base}.pdf"
			NewPdf="${PDFRoot}${RelDir}/${NewBase}.pdf"

			if [[ -f "${OldPdf}" ]]
      then
				echo "Renaming PDF: ${Base}.pdf -> ${NewBase}.pdf"
				git mv "${OldPdf}" "${NewPdf}"
			fi
		fi
	done
}

UpdatePDFs () {
	echo "--- Syncing PDFs to ${PDFRoot} ---"
	# Iterate over generated PDFs in the Source Directory
	for SourcePdf in "${LatexRoot}"/**/*.pdf
  do
		# Identify the source Tex file to check timestamps
		SourceTex="${SourcePdf%.pdf}.tex"

		# If the .tex file doesn't exist, this might be a stray PDF; skip it
		if [[ ! -f "${SourceTex}" ]]
    then continue
    fi

		# Determine destination path
		RelDir="$(realpath --relative-to="${LatexRoot}" "$(dirname "${SourcePdf}")")"
		BaseName="$(basename -- "${SourcePdf}")"
		TargetPdf="${PDFRoot}/${RelDir}/${BaseName}"
		
		# Ensure destination directory exists
		mkdir -p "$(dirname "${TargetPdf}")"

		# LOGIC:
		# 1. If Target doesn't exist: Move it.
		# 2. If Target exists but SourceTex or NazgandStyle is NEWER than Target: Overwrite it.
		if [[ ! -f "${TargetPdf}" ]] ||
			 [[ "${SourceTex}" -nt "${TargetPdf}" ]] ||
			 [[ "${LatexRoot}/NazgandStyle.tex" -nt "${TargetPdf}" ]]
		then
			echo "Updating: ${RelDir}/${BaseName}"
			cp "${SourcePdf}" "${TargetPdf}"
		fi
	done
}

Rename () {
	Target="${1}"
	NewName="${2}" # Expecting Base Name only (no extension)

	if [[ -z "${Target}" || -z "${NewName}" ]]
  then
		echo "Error: Usage \`Rename <file> <NewBaseName>\`"
		exit 1
	fi

	if [[ ! -f "${Target}" ]]
  then
		echo "Error: File '${Target}' not found."
		exit 1
	fi

	# Determine which is the Source (Tex/Pdf) based on extension
	if [[ "${Target}" == *.tex ]]
  then
		SourceTex="${Target}"
		
		# Resolve PDF path
		RelDir="$(realpath --relative-to="${LatexRoot}" "$(dirname "${SourceTex}")")"
		Base="$(basename -- "${SourceTex}" .tex)"
		SourcePdf="${PDFRoot}/${RelDir}/${Base}.pdf"
	elif [[ "${Target}" == *.pdf ]]
  then
		SourcePdf="${Target}"
		
		# Resolve Tex path
		RelDir="$(realpath --relative-to="${PDFRoot}" "$(dirname "${SourcePdf}")")"
		Base="$(basename -- "${SourcePdf}" .pdf)"
		SourceTex="${LatexRoot}/${RelDir}/${Base}.tex"
	else
		echo "Error: Target must be a .tex or .pdf file."
		exit 1
	fi

	# Perform Git Moves
	if [[ -f "${SourceTex}" ]]
  then
		DestDir="$(dirname "${SourceTex}")"
		echo "Git Moving Tex: ${SourceTex} -> ${NewName}.tex"
		git mv "${SourceTex}" "${DestDir}/${NewName}.tex"
	else
		echo "Warning: Corresponding .tex file not found."
	fi

	if [[ -f "${SourcePdf}" ]]
  then
		DestDir="$(dirname "${SourcePdf}")"
		echo "Git Moving PDF: ${SourcePdf} -> ${NewName}.pdf"
		git mv "${SourcePdf}" "${DestDir}/${NewName}.pdf"
	else
		echo "Warning: Corresponding .pdf file not found in PDFRoot."
	fi
}

GitAdd () {
	echo "--- Staging Files ---"
	git add "${LatexRoot}"/**/*.tex
	git add "${PDFRoot}"/**/*.pdf
}

ListTex () {
	for FilePath in "${LatexRoot}"/**/*.tex
  do
		realpath --relative-to="${LatexRoot}" "${FilePath}"
	done
}

ListTrash () {
	for TrashExt in "${TrashExts[@]}"
  do
		for FilePath in "${LatexRoot}"/**/*."${TrashExt}"
  do
			realpath --relative-to="${LatexRoot}" "${FilePath}"
		done
	done
}

# --- Main Execution ---

case "${1}" in
	"Clean")
		Clean
		;;
	"Compile")
		Compile
		;;
	"PascalCase")
		PascalCase
		;;
	"UpdatePDFs")
		UpdatePDFs
		;;
	"Rename")
		Rename "${2}" "${3}"
		;;
	"GitAdd")
		GitAdd
		;;
	"ListTex")
		ListTex
		;;
	"ListTrash")
		ListTrash
		;;
	*)
		echo "Usage: ./Maintain.sh [COMMAND] [ARGS]"
		echo ""
		echo "Commands:"
		echo "  Clean        - Removes temporary LaTeX build files (aux, log, etc.) recursively."
		echo "  Compile      - Compiles all .tex files using lualatex (runs twice for references)."
		echo "  PascalCase   - Renames all .tex files (and linked PDFs) to PascalCase format"
		echo "                 using 'git mv'. Removes spaces/hyphens."
		echo "  UpdatePDFs   - Moves generated PDFs from LaTeX/ to PDFs/."
		echo "                 Only updates the destination if the source .tex file is newer"
		echo "                 than the existing PDF."
		echo "  Rename       - Renames a .tex OR .pdf file and its counterpart in the other tree."
		echo "                 Usage: Rename <path/to/file> <NewBaseName>"
		echo "  GitAdd       - Stages all .tex and .pdf files in the project."
		echo "  ListTex      - Lists all .tex files targeted for compilation."
		echo "  ListTrash    - Lists all temporary files targeted for Clean."
		;;
esac