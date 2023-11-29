#!/usr/bin/env bash

if [ $# -ne 1 ]; then
  echo Usage: update.sh \$tag_name
  echo
  echo Downloads the mathport release with tag \$tag_name
  echo and creates a bump commit.
  exit 1
fi

set -ex

tag=$1

curl -qsSL {https://raw.githubusercontent.com/leanprover-community/mathport/$tag/,-o}lean-toolchain

mathlib4_rev=$(
  curl -qsSL https://raw.githubusercontent.com/leanprover-community/mathport/$tag/lake-manifest.json |
  jq -r '.packages[] | select(.name=="mathlib") | .rev'
)

# We specify a suffix for `-i` for macos compatibility.
sed -i.bak '
  /^def tag / s/"\(.*\)"$/"'$tag'"/;
  /^require mathlib / s/@"\([^"]*\)"$/@"'$mathlib4_rev'"/
' lakefile.lean
rm lakefile.lean.bak
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update

rm -rf Leanbin
curl -qsSL https://github.com/leanprover-community/mathport/releases/download/$tag/lean3-synport.tar.gz \
  | tar xz

git add Leanbin
git commit -am "bump to $tag" || true that
