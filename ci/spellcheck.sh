#!/bin/bash

set -eu

export LANG=en_US.UTF-8
aspell --version
echo "LANG=$LANG"
# Checks project Markdown files for spelling mistakes.

# Notes:

# This script needs dictionary file ($dict_filename) with project-specific
# valid words. If this file is missing, first invocation of a script generates
# a file of words considered typos at the moment. User should remove real typos
# from this file and leave only valid words. When script generates false
# positive after source modification, new valid word should be added
# to dictionary file.

# When running in CI, this script should be run in "list" mode (pass "list"
# as first argument). In this mode script scans all files and reports found
# errors. Exit code in this case depends on scan result:
# 1 if any errors found,
# 0 if all is clear.

# Script skips words with length less than or equal to 3. This helps to avoid
# some false positives.

# We can consider skipping source code in markdown files (```code```) to reduce
# rate of false positives, but then we lose ability to detect typos in code
# comments/strings etc.

shopt -s nullglob

dict_filename=./ci/dictionary.txt
markdown_sources=(./src/*.md)
mode=${1:-"check"}

# aspell repeatedly modifies the personal dictionary for some reason,
# so we should use a copy of our dictionary.
dict_path="/tmp/dictionary.txt"

# Error if running in list (CI) mode and there isn't a dictionary file;
# creating one in CI won't do any good :(
if [[ "$mode" == "list" && ! -f "$dict_filename" ]]; then
    echo "No dictionary file found! A dictionary file is required in CI!"
    exit 1
fi

# ignore math for spellchecking
remove_math() {
    sed 's/\\\\\[[^]]*\\\\\]//g; s/\\\\([^)]*\\\\)//g' "$1"
}

# ignore markdown code blocks for spellchecking
remove_code() {
    # shellcheck disable=SC2016
    sed '/^```/,/```/d; s/`[^`]*`//g' "$1"
}

# ignore comments (HTML format) for spellchecking
remove_comments() {
    sed -E ':a; /<!--/!b; s/<!--(.*?)-->//g; /-->/!{N; ba}' "$1"
}

if [[ ! -f "$dict_filename" ]]; then
    # Pre-check mode: generates dictionary of words aspell consider typos.
    # After user validates that this file contains only valid words, we can
    # look for typos using this dictionary and some default aspell dictionary.
    echo "Scanning files to generate dictionary file '$dict_filename'."
    echo "Please check that it doesn't contain any misspellings."

    echo "personal_ws-1.1 en 0 utf-8" >"$dict_filename"
    cat "${markdown_sources[@]}" | aspell --ignore 3 list | sort -u >>"$dict_filename"
elif [[ "$mode" == "list" ]]; then
    # List (default) mode: scan all files, report errors.
    declare -i retval=0

    cp "$dict_filename" "$dict_path"

    if [ ! -f $dict_path ]; then
        retval=1
        exit "$retval"
    fi

    for fname in "${markdown_sources[@]}"; do
        command=$(remove_code "$fname" | remove_math - | remove_comments - | aspell --ignore 3 --personal="$dict_path" "$mode")
        if [[ -n "$command" ]]; then
            for error in $command; do
                echo "$error"
                # FIXME: find more correct way to get line number
                # (ideally from aspell). Now it can make some false positives,
                # because it is just a grep.
                grep --with-filename --line-number --color=always "$error" "$fname"
            done
            retval=1
        fi
    done
    exit "$retval"
elif [[ "$mode" == "check" ]]; then
    # Interactive mode: fix typos.

    if [ ! -f $dict_filename ]; then
        retval=1
        exit "$retval"
    fi

    for fname in "${markdown_sources[@]}"; do
        aspell --ignore 3 --dont-backup --personal="$dict_filename" "$mode" "$fname"
    done
fi
