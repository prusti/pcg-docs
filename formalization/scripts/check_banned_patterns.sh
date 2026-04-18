#!/usr/bin/env bash
# Check for banned source patterns in Lean files.
# Each entry: file glob to search, grep pattern, allowed file:line, description.
set -euo pipefail

cd "$(dirname "$0")/.."

status=0

# .cmd "href" should only appear inside Latex.externalLink
matches=$(grep -rn '\.cmd "href"' --include='*.lean' . || true)
while IFS= read -r line; do
  [ -z "$line" ] && continue
  case "$line" in
    ./Core/Export/Latex.lean:*) ;; # allowed: externalLink definition
    *) echo "ERROR: raw .cmd \"href\" usage (use Latex.externalLink instead): $line"
       status=1 ;;
  esac
done <<< "$matches"

if [ "$status" -eq 0 ]; then
  echo "-- Banned-pattern check passed."
fi
exit "$status"
