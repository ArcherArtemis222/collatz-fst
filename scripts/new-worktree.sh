#!/usr/bin/env bash
# 幫某個代理開一個獨立工作區（git worktree）+ 分支。
#
#   ./scripts/new-worktree.sh a fix-trivial-quantifier
#     -> 分支 a/fix-trivial-quantifier
#     -> 目錄 ../collatz-a-fix-trivial-quantifier
#
# 為什麼用 worktree 而不是 clone：共用同一份 .git，磁碟省一半，
# 而且下面會把 .lake/packages 符號連結過去，避免每個工作區各存一份 mathlib（每份約數 GB）。
set -euo pipefail

zone="${1:?用法: new-worktree.sh <core|a|b|recon> <議題名>}"
topic="${2:?用法: new-worktree.sh <core|a|b|recon> <議題名>}"

case "$zone" in
  core|a|b|recon) ;;
  *) echo "分區只能是 core / a / b / recon" >&2; exit 1 ;;
esac

root="$(git rev-parse --show-toplevel)"
branch="$zone/$topic"
dir="$root/../$(basename "$root")-$zone-$topic"

git -C "$root" fetch origin
git -C "$root" worktree add -b "$branch" "$dir" origin/main

# 共用 mathlib 依賴，省去重抓
if [ -d "$root/.lake/packages" ]; then
  mkdir -p "$dir/.lake"
  ln -sfn "$root/.lake/packages" "$dir/.lake/packages"
  echo "已連結 .lake/packages（共用 mathlib 原始碼）"
fi

cat <<MSG

工作區已建立：
  目錄  $dir
  分支  $branch

接著：
  cd "$dir"
  lake exe cache get
  lake build

完成後：
  git push -u origin $branch && gh pr create --fill

清掉：
  git worktree remove "$dir"
MSG
