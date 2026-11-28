#!/usr/bin/env bash
# The steps of the workflow bridge-full: the build of the bridge package bridge/ with the theorem modules of AxiomMath/MMP (spec 09.4, the bridges O-R2-2 and O-R2-3 of spec 04.3).
#
#   bridge-full.sh room            free disk space on the runner and add swap
#   bridge-full.sh pins            check that the pins of bridge/lake-manifest.json agree with lake-manifest.json
#   bridge-full.sh build MINUTES   run lake build in bridge/ on the modules of bridge/full.txt for at most MINUTES minutes
#   bridge-full.sh record          after a full build: the manifest, the sizes and the axioms of the declarations of bridge/full.txt
#
# The theorem modules of AxiomMath/MMP import about 25,000 modules of AxiomMath/Stacks and AxiomMath/MMP, so the build is longer than one job of 6 hours on a standard runner. Each run builds for at most MINUTES minutes, the workflow saves the partial build in the cache, and the next run goes on from it. Lake rebuilds a module only when its trace changes, so a module that one run built is not built again.
#
# This is the model of scripts/audit-build.sh in tamnd/mmp, which builds AxiomMath/MMP at the same commit.
#
# The step build writes done=true, done=false or failed=true to $GITHUB_OUTPUT, and the time and memory of the segment to out/segment.txt.
set -euo pipefail

OUT=${OUT:-out}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
ROOT=$(pwd)
FULL="$ROOT/bridge/full.txt"
HEAVY="$ROOT/bridge/heavy.txt"
AXIOM_COMMIT=1f9ade367087ec711a2ce1382bad279a5a0284c3

# The modules of bridge/full.txt, each once, in the order of the file.
modules() {
  grep -v '^#' "$FULL" | awk 'NF { print $1 }' | awk '!seen[$0]++'
}

case "${1:-}" in
room)
  df -h / | tail -1
  sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc /opt/hostedtoolcache/CodeQL /usr/local/share/boost /usr/share/swift
  sudo docker image prune --all --force >/dev/null 2>&1 || true
  sudo swapoff -a || true
  sudo fallocate -l 16G /swapfile2
  sudo chmod 600 /swapfile2
  sudo mkswap /swapfile2 >/dev/null
  sudo swapon /swapfile2
  df -h / | tail -1
  free -g
  ;;
pins)
  cd bridge
  python3 - "$AXIOM_COMMIT" <<'EOF'
import json, sys
bridge = {p["name"]: p for p in json.load(open("lake-manifest.json"))["packages"]}
root = {p["name"]: p for p in json.load(open("../lake-manifest.json"))["packages"]}
assert bridge["MMP"]["rev"] == sys.argv[1], bridge["MMP"]["rev"]
for name, p in root.items():
    assert bridge[name]["rev"] == p["rev"], (name, bridge[name]["rev"], p["rev"])
for name in sorted(bridge):
    print(name, bridge[name].get("rev", bridge[name].get("dir")))
EOF
  ;;
build)
  minutes=${2:?minutes}
  command -v /usr/bin/time >/dev/null || sudo apt-get install -y time >/dev/null
  mapfile -t targets < <(modules)
  cd bridge
  start=$(date +%s)
  # A lean process that runs out of memory should be killed before the runner agent is, so that the partial build is still saved.
  # As in the audit build of tamnd/mmp, the build runs in a systemd scope with a hard memory limit: the kernel kills a lean process inside the scope, and the runner agent outside it keeps its memory.
  # The default OOMPolicy=stop of a scope stops the whole scope after the first kill, so the scope keeps running after a kill.
  echo 1000 > /proc/self/oom_score_adj || true
  mem_kb=$(awk '/MemTotal/ {print $2}' /proc/meminfo)
  limit_mb=$(( mem_kb / 1024 - 2048 ))
  scope=()
  if command -v systemd-run >/dev/null && sudo -n true 2>/dev/null; then
    scope=(sudo systemd-run --quiet --scope -p "MemoryMax=${limit_mb}M" -p MemorySwapMax=4G -p OOMPolicy=continue
      --uid="$(id -u)" --gid="$(id -g)" env PATH="$PATH" HOME="$HOME")
    echo "the build runs in a scope with MemoryMax=${limit_mb}M and MemorySwapMax=4G"
  fi
  set +e
  # Some modules of AxiomMath/Stacks need more memory than the runner has when lake builds them next to others (bridge/heavy.txt).
  # Each one is built first, alone in the scope, so that it has all the memory. A module already built costs only the check of its trace.
  : > "$OUT/build.log"
  if [ -f "$HEAVY" ]; then
    grep -v '^#' "$HEAVY" | while read -r m; do
      [ -n "$m" ] || continue
      left=$(( minutes * 60 - ($(date +%s) - start) - 600 ))
      [ "$left" -gt 0 ] || break
      echo "heavy module $m, alone, at most ${left}s" >> "$OUT/build.log"
      "${scope[@]}" timeout -k 1m "${left}s" lake build "$m" >> "$OUT/build.log" 2>&1
      echo "heavy module $m: status $?" >> "$OUT/build.log"
    done
  fi
  left=$(( minutes * 60 - ($(date +%s) - start) ))
  [ "$left" -gt 60 ] || left=60
  echo "targets: ${targets[*]}" >> "$OUT/build.log"
  "${scope[@]}" timeout -k 2m "${left}s" /usr/bin/time -v -o "$OUT/time.txt" lake build "${targets[@]}" >> "$OUT/build.log" 2>&1
  status=$?
  set -e
  end=$(date +%s)
  cd ..
  sudo -n dmesg 2>/dev/null | grep -iE "out of memory|oom-kill|killed process" | tail -n 20 > "$OUT/oom.txt" || true
  built=$(grep -c "^✔ \[" "$OUT/build.log" || true)
  rss=$(grep "Maximum resident set size" "$OUT/time.txt" 2>/dev/null | awk '{print $NF}' || true)
  {
    echo "segment=${SEGMENT:-1}"
    echo "status=$status"
    echo "seconds=$((end - start))"
    echo "max_rss_kb=${rss:-unknown}"
    echo "lines_built=$built"
    echo "oom_kills=$(grep -ciE "killed process" "$OUT/oom.txt" || true)"
  } > "$OUT/segment.txt"
  cat "$OUT/segment.txt"
  tail -n 30 "$OUT/build.log"
  if [ "$status" -eq 0 ]; then
    echo "done=true" >> "$GITHUB_OUTPUT"
  elif [ "$status" -eq 124 ] || [ "$status" -eq 137 ]; then
    echo "done=false" >> "$GITHUB_OUTPUT"
  elif grep -qE "code 137|signal 9" "$OUT/build.log"; then
    echo "a lean process was killed, most likely for memory; the next segment goes on from the saved build"
    echo "oom=true" >> "$OUT/segment.txt"
    echo "done=false" >> "$GITHUB_OUTPUT"
  else
    grep -n "error" "$OUT/build.log" | head -n 40 || true
    echo "failed=true" >> "$GITHUB_OUTPUT"
  fi
  ;;
record)
  mapfile -t targets < <(modules)
  cp bridge/lake-manifest.json "$OUT/lake-manifest.json"
  cp "$FULL" "$OUT/full.txt"
  cd bridge
  du -sh .lake/build .lake/packages/*/.lake/build ../.lake/build 2>/dev/null | tee "$OUT/sizes.txt"
  {
    for m in "${targets[@]}"; do echo "import $m"; done
    grep -v '^#' "$FULL" | awk 'NF { print "#print axioms " $2 }'
  } > axioms-full.lean
  cp axioms-full.lean "$OUT/axioms-full.lean"
  set +e
  lake env lean axioms-full.lean > "$OUT/axioms.txt" 2>&1
  status=$?
  set -e
  cat "$OUT/axioms.txt"
  echo "lean exit $status"
  [ "$status" -eq 0 ] || exit 1
  expected=$(grep -v '^#' "$FULL" | awk 'NF' | wc -l)
  found=$(grep -c "depends on axioms" "$OUT/axioms.txt" || true)
  if [ "$found" -ne "$expected" ]; then
    echo "$found of $expected declarations have an axiom line; a declaration without axioms or with sorryAx needs a look"
  fi
  if grep "depends on axioms" "$OUT/axioms.txt" | grep -vE "depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$"; then
    echo "a declaration uses an axiom outside propext, Classical.choice and Quot.sound"
    exit 1
  fi
  ;;
*)
  sed -n '2,7p' "$0"
  exit 2
  ;;
esac
