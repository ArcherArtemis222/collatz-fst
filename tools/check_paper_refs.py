"""論文引用一致性檢查：paper/*.tex 的 \\leanref{ID} 與 \\begin{paperthm}{ID}
↔ paper/registry.yaml 雙向。

用法：python3 tools/check_paper_refs.py   （路徑相對 __file__；CI guard.yml 每次 push 跑）

「引用」有兩種形式：`\\leanref{ID}`（點名引用）與 `\\begin{paperthm}{ID}`
（以 registry latex 欄陳述該定理——最強形式的引用）。兩種都算。
\\paperthm 對未知／未填 id 的 TeX 硬報錯只在本機編譯時起作用（CI 不編譯
TeX），所以方向一必須在這裡把 \\paperthm 一併掃進來，防線才到 CI 層。

方向一（引用必有出處）：每個被引用的 ID 都必須在 registry 內，
否則 exit 1——論文不得引用未註冊的定理宣稱。

方向二（出處必被引用）：每條 registry entry 都必須被引用（兩種形式擇一），
或在 YAML 標 `unreferenced_ok: true`。**只掃非生成的 .tex 原始檔**
（生成檔以檔頭 AUTO-GENERATED 標記辨識）；當 paper/ 尚無任何非生成
.tex 原始檔時（PR-0 的空窗期），本方向整個跳過並印明原因——
不要用臨時 unreferenced_ok 硬撐空窗。

方向三（陳述必已填）：每個 `\\begin{paperthm}{ID}` 的 registry `latex` 欄
必須已填（整欄恰為【…】狀態標記者視為未填）。「合法 id 但未填」在本機
由 \\paperthm 的 TeX 硬報錯攔截，但 CI 不編譯 TeX——沒有本方向，這種
狀態在 CI 全盲（實測 exit 0）。W3 起補上。
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
PAPER_DIR = ROOT / "paper"
GENERATED_MARK = "AUTO-GENERATED"
LEANREF_RE = re.compile(r"\\leanref\{([^}]*)\}")
PAPERTHM_RE = re.compile(r"\\begin\{paperthm\}\{([^}]*)\}")
# TeX 註解（未跳脫的 % 起）不算引用——註解裡提到 id 不能滿足方向二，
# 也不該觸發方向一。巨集「定義站點」同理：擷取值含 #（TeX 參數記號，
# 如 \newenvironment 內的 \leanref{#1}）者跳過，只算真正的使用站點。
COMMENT_RE = re.compile(r"(?<!\\)%.*$")
# latex 欄狀態標記（與 tools/gen_paper_index.py 的 STATUS_RE 同步；
# 生成器據此不排 leanstmt@，本檢查據此判「未填」——兩處判準必須一致）。
STATUS_RE = re.compile(r"^【.*】$")

entries = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
ids = [e["id"] for e in entries]
if len(ids) != len(set(ids)):
    sys.exit("check_paper_refs: registry id 重複")
known = set(ids)

# 非生成的 .tex 原始檔（生成檔＝前 5 行含 AUTO-GENERATED 標記）
sources = []
for tex in sorted(PAPER_DIR.glob("*.tex")):
    head = "\n".join(tex.read_text(encoding="utf-8").splitlines()[:5])
    if GENERATED_MARK not in head:
        sources.append(tex)

# 方向一：每個 \leanref 與 \begin{paperthm} 的 ID 都在 registry
# （\paperthm 使用站點另記，供方向三檢查）
bad = []
referenced = set()
paperthm_uses = []
for tex in sources:
    for lineno, line in enumerate(tex.read_text(encoding="utf-8").splitlines(), 1):
        code = COMMENT_RE.sub("", line)
        for regex, form in ((LEANREF_RE, "\\leanref"), (PAPERTHM_RE, "\\begin{paperthm}")):
            for m in regex.finditer(code):
                rid = m.group(1)
                if "#" in rid:
                    continue
                referenced.add(rid)
                if regex is PAPERTHM_RE:
                    paperthm_uses.append((tex, lineno, rid))
                if rid not in known:
                    bad.append(f"  {tex.relative_to(ROOT)}:{lineno}: {form}{{{rid}}} 不在 registry")
if bad:
    print("check_paper_refs: 引用了未註冊的 ID（方向一失敗）：")
    print("\n".join(bad))
    sys.exit(1)

# 方向三：每個 \begin{paperthm}{ID} 的 latex 欄必須已填（非狀態標記）
latex_by_id = {e["id"]: e.get("latex") for e in entries}
bad3 = []
for tex, lineno, rid in paperthm_uses:
    latex = str(latex_by_id.get(rid) or "").strip()
    if not latex or STATUS_RE.match(latex):
        bad3.append(f"  {tex.relative_to(ROOT)}:{lineno}: \\begin{{paperthm}}{{{rid}}} "
                    f"的 latex 欄未填（{latex or '空白'}）")
if bad3:
    print("check_paper_refs: \\paperthm 陳述了 latex 欄未填的條目（方向三失敗）：")
    print("\n".join(bad3))
    sys.exit(1)

# 方向二：registry 全被引用（或標 unreferenced_ok）
if not sources:
    print("check_paper_refs: paper/ 下尚無非生成的 .tex 原始檔（PR-0 空窗期），"
          "「registry 全被引用」方向跳過；方向一空集合上恆真。")
    print(f"check_paper_refs: OK（registry {len(ids)} 條；tex 原始檔 0 個）")
    sys.exit(0)

unreferenced = [e["id"] for e in entries
                if e["id"] not in referenced and not e.get("unreferenced_ok", False)]
if unreferenced:
    print("check_paper_refs: 下列 registry 條目未被任何 \\leanref／\\paperthm 引用，"
          "也未標 unreferenced_ok（方向二失敗）：")
    for rid in unreferenced:
        print(f"  {rid}")
    sys.exit(1)

print(f"check_paper_refs: OK（registry {len(ids)} 條；tex 原始檔 {len(sources)} 個；"
      f"引用 {len(referenced & known)} 條；\\paperthm 陳述 "
      f"{len({r for _, _, r in paperthm_uses})} 條）")
