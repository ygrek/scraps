#! /bin/bash

# OASIS query helper
# https://github.com/ygrek/scraps/blob/master/oasis-query.sh

set -eu

code_sections() {
  oasis query ListSections | egrep '^(Library|Executable|Object)'
}

# query oasis for all BuildDepends and exclude internal Library names
show_deps() {
  join -v 2 <(oasis query ListSections | grep Library | sed 's/Library(\(.*\))/\1/' | sort -u) <(oasis query $(code_sections | sed s/$/.BuildDepends/ ) | tr ',' '\n' | awk '($1!=""){print $1}' | sort -u)
}

show_source_dirs() {
  oasis query $(code_sections | sed s/$/.Path/ ) | sort -u
}

show_build_dirs() {
  show_source_dirs | sed 's@^@_build/@'
}

show_include_dirs() {
  ocamlfind query -r -i-format $(show_deps)
  show_build_dirs | sed 's/^/-I /'
}

generate_merlin() {
  show_source_dirs | sed 's/^/S /'
  show_build_dirs | sed 's/^/B /'
  show_deps | sed 's/^/PKG /'
}

case "${1:-}" in
"deps") show_deps ;;
"build-dirs") show_build_dirs ;;
"source-dirs") show_source_dirs ;;
"include-dirs") show_include_dirs ;;
"merlin") generate_merlin ;;
*)
  echo "whoa?" >&2
  echo "Supported commands : deps build-dirs source-dirs include-dirs merlin" >&2
  exit 1
esac