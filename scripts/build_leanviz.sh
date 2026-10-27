#!/usr/bin/env bash
# Reuse the compiled project; all external sources and intermediates live outside its tree.
set -euo pipefail

PROJECT_ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
LEANVIZ_REF=1f80be49d0a8ee2210d62a86989f15035abcd083
TENET_REF=0ea5f0680505858c05484b605bb902961c9c33c4
cd "$PROJECT_ROOT"

for tool in dotnet lake git python3; do
  command -v "$tool" >/dev/null || { echo "Missing required tool: $tool" >&2; exit 1; }
done
test -f .lake/build/lib/lean/LeanMachineLearning.olean || {
  echo 'Build the project first: lake build LeanMachineLearning LMLTutorial' >&2
  exit 1
}

if [[ -n ${GITHUB_REPOSITORY:-} ]]; then
  PROJECT_REPO="https://github.com/$GITHUB_REPOSITORY"
else
  PROJECT_REPO=$(git remote get-url origin)
  PROJECT_REPO=${PROJECT_REPO/#git@github.com:/https:\/\/github.com/}
  PROJECT_REPO=${PROJECT_REPO/#ssh:\/\/git@github.com\//https:\/\/github.com/}
  PROJECT_REPO=${PROJECT_REPO%.git}
fi
[[ $PROJECT_REPO == https://github.com/*/* ]] || {
  echo "Expected a GitHub origin, got: $PROJECT_REPO" >&2
  exit 1
}

TOOLS_DIR=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/lml-leanviz.XXXXXX")
trap 'rm -rf -- "$TOOLS_DIR"' EXIT
checkout_tool() {
  local repo=$1 ref=$2 dest=$3
  git init -q "$dest"
  git -C "$dest" remote add origin "https://github.com/$repo.git"
  git -C "$dest" fetch --depth 1 origin "$ref"
  git -C "$dest" checkout -q --detach FETCH_HEAD
  test "$(git -C "$dest" rev-parse HEAD)" = "$ref"
}
checkout_tool keithadler/leanviz "$LEANVIZ_REF" "$TOOLS_DIR/leanviz"
checkout_tool keithadler/tenet "$TENET_REF" "$TOOLS_DIR/tenet"
echo "leanviz $LEANVIZ_REF; Tenet reader $TENET_REF"

dotnet build "$TOOLS_DIR/tenet/src/Tenet.Olean" -c Release -f net10.0 -p:TargetFrameworks=net10.0
mkdir -p "$TOOLS_DIR/leanviz/lib"
cp "$TOOLS_DIR/tenet/src/Tenet.Olean/bin/Release/net10.0/"Tenet.{Kernel,Olean}.dll \
  "$TOOLS_DIR/leanviz/lib/"
dotnet build "$TOOLS_DIR/leanviz/generator" -c Release

SITE_DIR="$PROJECT_ROOT/home_page/leanviz"
# Replace this generated subtree so deleted modules cannot survive a local rebuild.
rm -rf -- "$SITE_DIR"
mkdir -p "$SITE_DIR"
cp -R "$TOOLS_DIR/leanviz/site/." "$SITE_DIR/"
cp "$TOOLS_DIR/leanviz/LICENSE" "$SITE_DIR/LICENSE"
LEANVIZ_DLL="$TOOLS_DIR/leanviz/generator/bin/Release/net10.0/leanviz.dll"
# The reader asks Git for origin to construct source links. Override it for this process only,
# including when a local checkout uses an SSH remote; leave the checkout's config untouched.
GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=remote.origin.url GIT_CONFIG_VALUE_0="$PROJECT_REPO" \
  lake env dotnet "$LEANVIZ_DLL" "$PROJECT_ROOT" \
    --out "$SITE_DIR/data" --slug lml --title "Lean Machine Learning" --repo "$PROJECT_REPO"

python3 "$TOOLS_DIR/leanviz/tests/check_bundle.py" "$SITE_DIR/data"
python3 scripts/check_leanviz.py "$TOOLS_DIR/leanviz" "$PROJECT_REPO"
