#!/usr/bin/env bash
# Publish the Lean version supported by this checkout, without backfilling merged history.
set -euo pipefail

revision=$(git rev-parse --verify --end-of-options "${AFTER:-HEAD}^{commit}")
toolchain=$(git show "$revision:lean-toolchain")
if [[ $toolchain != leanprover/lean4:* ]]; then
  echo "Custom Lean toolchain; no release tag to create."
  exit 0
fi
version=${toolchain#leanprover/lean4:}
git check-ref-format "refs/tags/$version"

if git ls-remote --exit-code --tags origin "refs/tags/$version" >/dev/null; then
  echo "Release tag $version already exists; leaving it unchanged."
  exit 0
else
  status=$?
  # Exit 2 means no matching ref; authentication/network errors must remain failures.
  if [[ $status != 2 ]]; then
    exit "$status"
  fi
fi

if git show-ref --verify --quiet "refs/tags/$version"; then
  if [[ $(git rev-parse "refs/tags/$version^{commit}") != "$revision" ]]; then
    echo "Local tag $version points elsewhere; refusing to move it." >&2
    exit 1
  fi
else
  git -c user.name='github-actions[bot]' \
    -c user.email='41898282+github-actions[bot]@users.noreply.github.com' \
    tag -a "$version" -m "Release $version" "$revision"
fi

git push origin "refs/tags/$version"
if [[ ${DO_RELEASE:-false} == true ]]; then
  gh release create "$version" --verify-tag --target "$revision" --title "$version" \
    --notes "Automated release for Lean version $version"
fi
