#!/usr/bin/env python3
"""由可信主分支 CI 发布完整缓存集合；已发布的提交快照不覆盖。"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


TARGETS = {
    "x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu",
    "x86_64-w64-windows-gnu", "x86_64-apple-darwin", "aarch64-apple-darwin",
}


def publish(directory: Path) -> None:
    repository = "lanxinge/YesMetaZFC"
    if os.environ.get("GITHUB_REPOSITORY") != repository or os.environ.get("GITHUB_REF") != "refs/heads/main":
        raise ValueError("只允许在原仓库主分支发布缓存")
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    expected = {(target, kind) for target in TARGETS for kind in ("lean", "full")}
    found, fingerprints, sums, assets = set(), set(), [], []
    for path in sorted(directory.glob("*.tar.gz.json")):
        metadata = json.loads(path.read_text(encoding="utf-8"))
        pair = (metadata["target"], metadata["kind"])
        if pair in found or pair not in expected:
            raise ValueError(f"缓存平台重复或未知：{pair}")
        suffix = "-lean" if metadata["kind"] == "lean" else ""
        name = f"YesMetaZFC-{metadata['target']}{suffix}.tar.gz"
        if (metadata["revision"] != revision or metadata["dirty"]
                or metadata["format"] != 1 or metadata["archive"] != name
                or path.name != name + ".json"):
            raise ValueError(f"缓存清单不符合发布条件：{path.name}")
        archive = directory / name
        with archive.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if digest != metadata["sha256"] or archive.stat().st_size != metadata["bytes"]:
            raise ValueError(f"归档校验失败：{name}")
        found.add(pair)
        fingerprints.add((metadata["source_sha256"], metadata["toolchain"]))
        sums.append(f"{digest}  {name}\n")
        assets.extend([str(archive), str(path)])
    if found != expected or len(fingerprints) != 1:
        raise ValueError(f"缓存集合不完整或源码版本不统一；缺少：{expected - found}")
    checksums = directory / "SHA256SUMS"
    checksums.write_text("".join(sums), encoding="utf-8")
    assets.append(str(checksums))
    tag = f"cache-{revision}"
    gh = ["gh", "release"]
    existing = subprocess.run([*gh, "view", tag, "--repo", repository, "--json", "isDraft,assets"],
                              text=True, capture_output=True)
    if existing.returncode == 0:
        release = json.loads(existing.stdout)
        if not release["isDraft"]:
            names = {asset["name"] for asset in release["assets"]}
            if not {Path(asset).name for asset in assets} <= names:
                raise ValueError("已发布快照缺少资产；保留原快照，请人工检查")
            print(f"快照已发布，保持原资产：{tag}")
            return
    else:
        notes = directory / "release-notes.md"
        notes.write_text(
            f"Prebuilt Lean caches for commit `{revision}`.\n\n"
            "Five platforms, each with Lean/editor and full/native archives. "
            "Each archive has a matching JSON manifest and SHA-256 checksum.\n\n"
            "From a checkout of this commit, run:\n\n"
            "```sh\npython scripts/lean_cache.py get\n"
            "python scripts/lean_cache.py get --kind full\n```\n\n"
            f"[Cache documentation](https://github.com/{repository}/blob/{revision}/markdown/CACHE.md)\n",
            encoding="utf-8",
        )
        subprocess.run([*gh, "create", tag, "--repo", repository, "--target", revision, "--draft", "--prerelease",
                        "--latest=false", "--title", f"Lean cache {revision[:12]}",
                        "--notes-file", str(notes)], check=True)
    # 未完成的草稿允许重新上传；公开后不再覆盖。
    subprocess.run([*gh, "upload", tag, "--repo", repository, *assets, "--clobber"], check=True)
    subprocess.run([*gh, "edit", tag, "--repo", repository, "--draft=false"], check=True)
    print(f"已发布：https://github.com/{repository}/releases/tag/{tag}")


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    publish(Path(sys.argv[1]).resolve())
