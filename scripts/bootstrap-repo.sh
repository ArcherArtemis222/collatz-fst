#!/usr/bin/env bash
# 一次把 repo 建起來：git init → 首次 commit → 在 GitHub 開 repo → 推上去 → 上分支保護。
#
#   ./scripts/bootstrap-repo.sh collatz-fst public
#   ./scripts/bootstrap-repo.sh collatz-fst private
#
# 需要 gh CLI 並已登入：  gh auth login
# 跑完之後這個腳本就沒用了，可以刪掉。
set -euo pipefail

repo="${1:?用法: bootstrap-repo.sh <repo 名稱> <public|private>}"
vis="${2:-private}"
case "$vis" in public|private) ;; *) echo "第二個參數只能是 public 或 private" >&2; exit 1;; esac

command -v gh >/dev/null || { echo "找不到 gh CLI：https://cli.github.com" >&2; exit 1; }
gh auth status >/dev/null 2>&1 || { echo "先跑 gh auth login" >&2; exit 1; }

owner="$(gh api user --jq .login)"
echo "GitHub 帳號：$owner"

# ── CODEOWNERS 填入真實帳號 ────────────────────────────────────────────
if grep -q "@YOUR-GITHUB-ID" .github/CODEOWNERS; then
  sed -i.bak "s/@YOUR-GITHUB-ID/@$owner/g" .github/CODEOWNERS && rm -f .github/CODEOWNERS.bak
  echo "已把 CODEOWNERS 的 @YOUR-GITHUB-ID 換成 @$owner"
fi

# ── git ───────────────────────────────────────────────────────────────
if [ ! -d .git ]; then
  git init -b main
fi
git add -A
git commit -m "初始化：Collatz FST 形式化，分區為 Core / ProjectA / ProjectB / Recon

- 13 個既有 .lean 依所有權分區搬遷，import 路徑同步改寫
- mathlib 硬釘 c66c0c58，toolchain 釘 v4.28.0-rc1
- CI：匯入邊界 + 依賴釘選守衛 + lake build + leanchecker + nanoda(禁 sorry)
- AGENTS.md 定下多方協作規約" || echo "（沒有東西要 commit）"

# ── GitHub ────────────────────────────────────────────────────────────
if gh repo view "$owner/$repo" >/dev/null 2>&1; then
  echo "$owner/$repo 已存在，直接推。"
  git remote get-url origin >/dev/null 2>&1 || git remote add origin "https://github.com/$owner/$repo.git"
  git push -u origin main
else
  gh repo create "$repo" "--$vis" --source=. --remote=origin --push \
    --description "Collatz 有限狀態平攤勢能：模板極限定理"
fi

# ── 分支保護 ──────────────────────────────────────────────────────────
# 注意：免費方案的「私有」repo 可能不支援分支保護。公開 repo 一定支援。
echo
echo "設定 main 的分支保護…"
if gh api -X PUT "repos/$owner/$repo/branches/main/protection" --input - <<'JSON' >/dev/null 2>&1
{
  "required_status_checks": {
    "strict": true,
    "contexts": ["boundaries", "build"]
  },
  "enforce_admins": false,
  "required_pull_request_reviews": {
    "require_code_owner_reviews": true,
    "required_approving_review_count": 1
  },
  "restrictions": null,
  "allow_force_pushes": false,
  "allow_deletions": false,
  "required_linear_history": true
}
JSON
then
  echo "分支保護已啟用：main 不能直接 push、不能 force push，PR 必須 CI 綠燈 + code owner 核可。"
else
  echo "!! 分支保護設定失敗。"
  echo "   最常見原因：免費方案的私有 repo 不支援分支保護。"
  echo "   解法：把 repo 改成 public，或到 Settings → Rules → Rulesets 手動設。"
  echo "   在設好之前，'main 受保護' 這件事只是口頭約定，不是機制。"
fi

echo
echo "完成。 https://github.com/$owner/$repo"
echo "接著在本機跑：  lake update && lake exe cache get && lake build"
echo "build 綠了之後：git add lake-manifest.json && git commit -m 'pin manifest' && git push"
