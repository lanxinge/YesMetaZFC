#!/usr/bin/env bash
# 全源构建的 Shell 入口；模块枚举和缓存验证共用同一 Python 实现。
set -euo pipefail
if command -v python >/dev/null 2>&1; then
  exec python "$(dirname -- "${BASH_SOURCE[0]}")/lean_cache.py" build "$@"
else
  exec python3 "$(dirname -- "${BASH_SOURCE[0]}")/lean_cache.py" build "$@"
fi
