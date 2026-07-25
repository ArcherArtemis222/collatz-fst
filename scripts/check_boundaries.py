#!/usr/bin/env python3
"""匯入邊界檢查（不需要 Lean 工具鏈，秒級完成）。

在 Lean 裡，「資料夾所有權」不等於「隔離」——真正的爆炸半徑是 import DAG。
本腳本把分區規則變成機器可檢的東西：

    Core     只能匯入 mathlib / Core
    ProjectA 只能匯入 mathlib / Core / ProjectA
    ProjectB 只能匯入 mathlib / Core / ProjectB
    Recon    可匯入任何東西，但不得被任何人匯入
    Audit    可匯入 Core / ProjectA / ProjectB

用法：  python3 scripts/check_boundaries.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = "Lean4RealConstruction"
LIBDIR = ROOT / LIB

# zone -> 允許匯入的 zone 集合（mathlib 等外部依賴一律放行）
ALLOWED: dict[str, set[str]] = {
    "Core": {"Core"},
    "ProjectA": {"Core", "ProjectA"},
    "ProjectB": {"Core", "ProjectB"},
    "Recon": {"Core", "ProjectA", "ProjectB", "Recon"},
    "Audit": {"Core", "ProjectA", "ProjectB"},
    "_root_": {"Core", "ProjectA", "ProjectB", "Recon", "Audit"},
}

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.\u00c0-\uffff«»]+)")


def zone_of(module: str) -> str | None:
    """把模組名映射到分區；非本 library 的模組回傳 None。"""
    if module == LIB:
        return "_root_"
    if not module.startswith(LIB + "."):
        return None
    rest = module[len(LIB) + 1 :]
    return rest.split(".", 1)[0]


def zone_of_path(path: Path) -> str:
    rel = path.relative_to(LIBDIR)
    return rel.parts[0].removesuffix(".lean") if rel.parts else "_root_"


def main() -> int:
    errors: list[str] = []
    files = sorted(LIBDIR.rglob("*.lean")) + [ROOT / f"{LIB}.lean"]

    for f in files:
        if not f.exists():
            continue
        here = "_root_" if f.parent == ROOT else zone_of_path(f)
        allowed = ALLOWED.get(here)
        if allowed is None:
            errors.append(f"{f.relative_to(ROOT)}: 未知分區 {here!r}（新分區要先寫進本腳本與 CODEOWNERS）")
            continue
        for lineno, line in enumerate(f.read_text(encoding="utf-8").splitlines(), 1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            target = zone_of(m.group(1))
            if target is None:          # mathlib / Lean 內建：放行
                continue
            if target not in allowed:
                errors.append(
                    f"{f.relative_to(ROOT)}:{lineno}: {here} 不得匯入 {target}"
                    f"  ({m.group(1)})"
                )

    # 殘留的舊路徑（restructure 前的扁平配置）
    for f in files:
        if f.exists() and f".{LIB}.Collatz." in "." + f.read_text(encoding="utf-8"):
            errors.append(f"{f.relative_to(ROOT)}: 還有舊的 .Collatz. 模組路徑")

    if errors:
        print("匯入邊界檢查失敗：\n", file=sys.stderr)
        for e in errors:
            print("  " + e, file=sys.stderr)
        print(
            "\n規則見 AGENTS.md。若這是刻意的架構調整，請改 scripts/check_boundaries.py "
            "並在 PR 說明理由。",
            file=sys.stderr,
        )
        return 1

    print(f"匯入邊界檢查通過（{len(files)} 個模組）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
