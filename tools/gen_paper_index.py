"""從 paper/registry.yaml 生成 PaperIndex.lean（論文定理重述層）與
paper/theorem-index.tex（附錄對應表）。

用法：python3 tools/gen_paper_index.py   （路徑相對 __file__，任何 checkout 可跑；
輸出應與 repo 中兩檔逐位一致——CI 以 regeneration + git diff --exit-code 強制）

## 設計原則（改本檔前先讀）

1. **型別快照是人工輸入，本檔絕不從 Lean 原始檔抽取敘述。**
   自動抽取會讓重新生成靜默刷新快照，「敘述未變」的 kernel 強制就死了。
   本檔只做搬運：把 registry 的 `lean_type` 逐字排進
   `theorem Paper.<id> : <lean_type> := @<lean>`，相容性由 kernel 在
   lake build 時檢查。
2. **決定性**：entries 依 id 排序；import 由各條 `file` 欄推導、去重排序；
   不嵌時間戳。同一 registry 必然生出逐位相同的兩個檔。
3. **PaperIndex 只 import 個別模組，絕不 import ProjectA 根模組**
   （ProjectA.lean 會 import PaperIndex，反向就成環）。本檔對 root
   module 檔名有硬防呆。
4. RHS 一律 `@<lean 全名>`：`@` 關掉 implicit 插入，讓含 implicit binder
   的重述（如 flow-kirchhoff-l2 的 {s} {w}）也能直接以常數項驗型別。
5. lean_type 在 registry 內以 block scalar 保存相對縮排；本檔統一加 4 格
   基底縮排排進 Lean 檔。除此之外一個字元都不動。

## Schema 檢查

id kebab-case 且唯一；lean 全名唯一且（文字層）能在 file 內 grep 到宣告；
file 限 Core/ 或 ProjectA/ 的非 root 模組；reviewed 恰為七欄。
kernel 才是敘述相容性的真裁判，這裡的檢查只是提早失敗。
"""
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("需要 PyYAML：python3 -m pip install pyyaml")

_HERE = Path(__file__).resolve().parent          # tools/
ROOT = _HERE.parent
REGISTRY = ROOT / "paper" / "registry.yaml"
OUT_LEAN = ROOT / "Lean4RealConstruction" / "ProjectA" / "PaperIndex.lean"
OUT_TEX = ROOT / "paper" / "theorem-index.tex"

REVIEWED_KEYS = [
    "strictness", "coefficients", "scope", "feature_level",
    "mode_definition", "witness_vs_universal", "model_class",
]
ID_RE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")
# 個別模組白名單：Core/ 與 ProjectA/ 之下的檔案。root 模組（Core.lean、
# ProjectA.lean、Lean4RealConstruction.lean）不在其下，天然被擋。
FILE_RE = re.compile(r"^Lean4RealConstruction/(Core|ProjectA)/[A-Za-z0-9_]+\.lean$")


def die(msg):
    sys.exit(f"gen_paper_index: {msg}")


def load_registry():
    entries = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    if not isinstance(entries, list) or not entries:
        die("registry.yaml 必須是非空 list")
    ids, leans = set(), set()
    for e in entries:
        for k in ("id", "lean", "file", "lean_type", "latex", "unreferenced_ok", "reviewed"):
            if k not in e:
                die(f"{e.get('id', '<no id>')} 缺欄位 {k}")
        if not ID_RE.match(e["id"]):
            die(f"id 不是 kebab-case：{e['id']}")
        if e["id"] in ids:
            die(f"id 重複：{e['id']}")
        ids.add(e["id"])
        if e["lean"] in leans:
            die(f"lean 全名重複：{e['lean']}")
        leans.add(e["lean"])
        if not FILE_RE.match(e["file"]):
            die(f"{e['id']}: file 必須是 Core/ 或 ProjectA/ 下的個別模組（不得是 root 模組）：{e['file']}")
        src = ROOT / e["file"]
        if not src.is_file():
            die(f"{e['id']}: 找不到原始檔 {e['file']}")
        decl = e["lean"].rsplit(".", 1)[-1]
        if not re.search(rf"^theorem {re.escape(decl)}\b", src.read_text(encoding="utf-8"), re.M):
            die(f"{e['id']}: 在 {e['file']} 內 grep 不到 `theorem {decl}`（全名或檔案欄有誤？）")
        if not isinstance(e["lean_type"], str) or not e["lean_type"].strip():
            die(f"{e['id']}: lean_type 空白")
        if not isinstance(e["unreferenced_ok"], bool):
            die(f"{e['id']}: unreferenced_ok 必須是 bool")
        if not isinstance(e["reviewed"], dict) or sorted(e["reviewed"]) != sorted(REVIEWED_KEYS):
            die(f"{e['id']}: reviewed 必須恰為七欄 {REVIEWED_KEYS}")
    return sorted(entries, key=lambda e: e["id"])


def file_to_module(f):
    return f[: -len(".lean")].replace("/", ".")


def gen_lean(entries):
    imports = sorted({file_to_module(e["file"]) for e in entries})
    forbidden = {"Lean4RealConstruction.Core", "Lean4RealConstruction.ProjectA",
                 "Lean4RealConstruction"}
    assert not (set(imports) & forbidden), "import 出現 root 模組（會成環）"
    lines = [
        "/-",
        "# PaperIndex：論文定理重述層（A-4）",
        "",
        "本檔由 tools/gen_paper_index.py 從 paper/registry.yaml 生成——**不要手改**。",
        "CI 以 regeneration + `git diff --exit-code` 強制逐位一致（guard.yml certs job）。",
        "",
        "每條 `Paper.<id>` 的型別是 registry 的人工快照，`:= @<原定理>` 由 kernel",
        "檢查快照與原定理相容。原定理被改到不相容 ⇒ 本檔編譯失敗 ⇒ 修 registry，",
        "該 PR 標【敘述變更】（AGENTS §2.6 [statement change]）。",
        "-/",
    ]
    lines += [f"import {m}" for m in imports]
    lines += [
        "",
        "-- 本檔只有型別重述（無證明項），binder 名逐字承自原敘述、純屬文件；",
        "-- unusedVariables 對重述層無意義，全檔關閉。",
        "set_option linter.unusedVariables false",
        "",
        "namespace Paper", "", "open CollatzFST", "",
    ]
    for e in entries:
        name = e["id"].replace("-", "_")
        lines.append(f"/-- Paper ref: {e['id']}（`{e['lean']}`） -/")
        lines.append(f"theorem {name} :")
        for tl in e["lean_type"].rstrip("\n").split("\n"):
            lines.append(f"    {tl}".rstrip())
        lines[-1] += " :="
        lines.append(f"  @{e['lean']}")
        lines.append("")
    lines += ["end Paper", ""]
    return "\n".join(lines)


def tex_escape(s):
    return s.replace("_", r"\_")


def gen_tex(entries):
    # 在 PREAMBLE \input 本檔。它定義兩樣東西：
    #   1. 每條 id 的 Lean 全名巨集 \leanname@<id>（main.tex 的 \leanref 用
    #      \csname 取用——映射由 registry 生成，不得在 main.tex 手工維護，
    #      否則重新引入 PR-0 要殺掉的漂移）；
    #   2. \TheoremIndexTable：附錄對應表（id / Lean 全名 / 檔案）。
    lines = [
        "% AUTO-GENERATED by tools/gen_paper_index.py — do not edit by hand.",
        "% Regenerate: python3 tools/gen_paper_index.py",
        "% Input this file in the PREAMBLE (after \\usepackage{etoolbox}). It",
        "% defines (1) one macro \\csname leanname@<id>\\endcsname per registry",
        "% entry via \\csdef (consumed by the \\leanref macro in main.tex) and",
        "% (2) \\TheoremIndexTable, which typesets the appendix table:",
        "% paper id / Lean full name / source file.",
    ]
    for e in entries:
        lines.append(rf"\csdef{{leanname@{e['id']}}}{{{tex_escape(e['lean'])}}}")
    lines += [
        r"\newcommand{\TheoremIndexTable}{%",
        r"\begin{longtable}{@{}p{0.32\textwidth}p{0.63\textwidth}@{}}",
        r"\toprule",
        r"Paper id & Lean theorem / source file \\",
        r"\midrule",
        r"\endhead",
    ]
    for e in entries:
        lines.append(
            rf"\texttt{{{tex_escape(e['id'])}}} & \texttt{{{tex_escape(e['lean'])}}}"
            rf" \newline {{\small \texttt{{{tex_escape(e['file'])}}}}} \\"
        )
    lines += [r"\bottomrule", r"\end{longtable}}", ""]
    return "\n".join(lines)


entries = load_registry()
OUT_LEAN.write_text(gen_lean(entries), encoding="utf-8")
OUT_TEX.write_text(gen_tex(entries), encoding="utf-8")
print(f"gen_paper_index: {len(entries)} 條 → {OUT_LEAN.relative_to(ROOT)}, {OUT_TEX.relative_to(ROOT)}")
