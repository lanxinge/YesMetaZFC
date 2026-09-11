#!/usr/bin/env python3
"""构建、打包和恢复与当前源码及工具链精确匹配的 Lean 缓存。仅使用 Python 标准库。"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.error
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "lanxinge/YesMetaZFC"
FORMAT = 1
NATIVE_TARGETS = ["YesMetaZFC:static", "YesMetaZFC:shared", "prove_auto_sweep"]
SOURCE_CONFIG = ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]


def run(root: Path, *args: str, capture: bool = False) -> str:
    result = subprocess.run(
        args, cwd=root, check=True, text=True, encoding="utf-8",
        stdout=subprocess.PIPE if capture else None,
        env={**os.environ, "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS", "4")},
    )
    return result.stdout.strip() if capture else ""


def sources(root: Path) -> list[Path]:
    modules = sorted((root / "YesMetaZFC").rglob("*.lean"),
                     key=lambda p: p.relative_to(root).as_posix())
    return [root / "YesMetaZFC.lean", *modules]


def build_all(root: Path, kind: str, *, no_build: bool = False) -> None:
    modules = [p.relative_to(root).with_suffix("").as_posix().replace("/", ".")
               for p in sources(root)]
    options = ["--wfail", *(["--no-build"] if no_build else []), "build"]
    print(f"{'验证缓存' if no_build else '构建'}：{len(modules)} 个 Lean 模块", flush=True)
    # 所有独立模块都进入检查；分批避免 Windows 命令行长度限制。
    for start in range(0, len(modules), 128):
        batch = modules[start:start + 128]
        run(root, "lake", *options, *batch)
        if kind == "full":
            run(root, "lake", *options, *(f"+{module}:o" for module in batch))
    if kind != "lean":
        run(root, "lake", *options, *(NATIVE_TARGETS if kind == "full" else ["prove_auto_sweep"]))


def identity(root: Path) -> dict:
    version = run(root, "lean", "--version", capture=True)
    match = re.search(r"\(version [^,]+, ([\w-]+), commit ", version)
    if not match:
        raise ValueError(f"无法识别 Lean 平台：{version}")
    revision = run(root, "git", "rev-parse", "HEAD", capture=True)
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("无法识别当前 Git 提交")
    fingerprint = hashlib.sha256()
    for path in [*(root / name for name in SOURCE_CONFIG), *sources(root)]:
        # 同一文本在 Git 的 LF/CRLF 转换后具有相同源码指纹。
        fingerprint.update(path.relative_to(root).as_posix().encode() + b"\0")
        fingerprint.update(hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).digest())
    return {
        "format": FORMAT, "revision": revision, "target": match[1],
        "toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_version": version, "source_sha256": fingerprint.hexdigest(),
    }


def archive_name(info: dict, kind: str) -> str:
    # 完整包遵循 Lake 的默认 buildArchive 命名，可直接由 Lake 下载和 unpack。
    suffix = "-lean" if kind == "lean" else ""
    return f"YesMetaZFC-{info['target']}{suffix}.tar.gz"


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def confined(path: Path, root: Path) -> Path:
    resolved = path.resolve()
    if not resolved.is_relative_to(root.resolve()) or resolved == root.resolve():
        raise ValueError(f"路径超出工作区：{path}")
    return resolved


def selected(path: PurePosixPath, kind: str) -> bool:
    if kind == "full":
        return path.parts[0] in {"lib", "ir", "bin", "share"}
    if path.parts[:2] in {("lib", "lean"), ("share", "YesMetaZFC")}:
        return True
    # Lake 的默认 leanArts 还需要生成的 C/LLVM 文件及其记录，不能只分发 olean。
    return path.parts[0] == "ir" and path.name.endswith(
        (".c", ".c.hash", ".bc", ".bc.hash", ".setup.json")
    )


def pack_cache(root: Path, output: Path, kind: str, *, allow_dirty: bool = False) -> Path:
    info = identity(root)
    changed = run(root, "git", "-c", "core.safecrlf=false", "status", "--porcelain", "--untracked-files=all", "--",
                  *SOURCE_CONFIG, "YesMetaZFC.lean", "YesMetaZFC", capture=True)
    if changed and not allow_dirty:
        raise ValueError("构建源码尚未提交；本地试验可使用 --allow-dirty，CI 发布必须使用干净源码")
    build_all(root, kind, no_build=True)
    build = confined(root / ".lake/build", root)
    notices = confined(build / "share/YesMetaZFC", root)
    notices.mkdir(parents=True, exist_ok=True)
    for name in ("LICENSE", "NOTICE"):
        shutil.copyfile(root / name, notices / name)
    # 原生工具链接 Lean 的运行库，随包保留发行工具链附带的第三方许可。
    toolchain = Path(run(root, "lean", "--print-prefix", capture=True))
    third_party = notices / "third-party/lean4"
    third_party.mkdir(parents=True, exist_ok=True)
    for name in ("LICENSE", "LICENSES"):
        if not (toolchain / name).is_file():
            raise ValueError(f"工具链缺少随附许可文件：{toolchain / name}")
        shutil.copyfile(toolchain / name, third_party / name)
    output = output.resolve()
    if output.is_relative_to(build):
        raise ValueError("压缩包不能输出到被打包的构建目录内")
    output.mkdir(parents=True, exist_ok=True)
    archive = output / archive_name(info, kind)
    active = {p.relative_to(root).with_suffix("").as_posix() for p in sources(root)}
    paths = []
    for path in sorted(build.rglob("*")):
        relative = PurePosixPath(path.relative_to(build).as_posix())
        if not path.is_file() or not selected(relative, kind):
            continue
        # 增量目录可能残留已删除或迁移的模块，公开包只保留当前模块的产物。
        parts = relative.parts
        module = PurePosixPath(*parts[2:]) if parts[:2] == ("lib", "lean") else (
            PurePosixPath(*parts[1:]) if parts[0] == "ir" else None)
        if module and module.with_name(module.name.split(".", 1)[0]).as_posix() not in active:
            continue
        paths.append(path)
    print(f"打包 {kind}：{len(paths)} 个文件 → {archive}", flush=True)
    # 先在新目录完成归档与清单，失败不覆盖之前成功生成的缓存。
    with tempfile.TemporaryDirectory(prefix=".cache-pack-", dir=output) as temporary:
        stage = confined(Path(temporary), output)
        pending = stage / archive.name
        # 将 Lake 链接到全局缓存的产物物化成普通文件，不分发链接。
        with tarfile.open(pending, "w:gz", compresslevel=6, dereference=True) as bundle:
            for path in paths:
                bundle.add(path, arcname=path.relative_to(build).as_posix(), recursive=False)
            unpacked_bytes = sum(member.size for member in bundle.getmembers())
        if identity(root) != info:
            raise ValueError("打包期间源码或工具链发生变化，不能发布此压缩包")
        if pending.stat().st_size >= 2 * 1024**3:
            raise ValueError("压缩包超过 GitHub 单个 Release 资产的 2 GiB 限制")
        metadata = {
            **info, "kind": kind, "dirty": bool(changed), "archive": archive.name,
            "sha256": sha256(pending), "bytes": pending.stat().st_size,
            "files": len(paths), "unpacked_bytes": unpacked_bytes,
        }
        manifest = stage / (archive.name + ".json")
        manifest.write_text(json.dumps(metadata, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        os.replace(pending, archive)
        os.replace(manifest, Path(str(archive) + ".json"))
    print(f"SHA-256：{metadata['sha256']}", flush=True)
    return archive


def validate_metadata(info: dict, metadata: dict, kind: str) -> None:
    if not isinstance(metadata, dict):
        raise ValueError("缓存清单必须是 JSON 对象")
    for key, expected in {**info, "kind": kind, "archive": archive_name(info, kind)}.items():
        if metadata.get(key) != expected:
            raise ValueError(f"缓存不匹配：{key}，需要 {expected!r}，收到 {metadata.get(key)!r}")
    for key in ("bytes", "files", "unpacked_bytes"):
        if type(metadata.get(key)) is not int or metadata[key] <= 0:
            raise ValueError(f"缓存清单字段无效：{key}")
    if not re.fullmatch(r"[0-9a-f]{64}", str(metadata.get("sha256", ""))):
        raise ValueError("缓存清单缺少有效 SHA-256")
    if type(metadata.get("dirty")) is not bool:
        raise ValueError("缓存清单缺少源码状态")


def safe_members(bundle: tarfile.TarFile, kind: str) -> list[tarfile.TarInfo]:
    members = bundle.getmembers()
    names: set[str] = set()
    for member in members:
        path = PurePosixPath(member.name)
        if (path.is_absolute() or ".." in path.parts or ":" in member.name
                or "\\" in member.name or not path.parts
                or not selected(path, kind) or not member.isfile()):
            raise ValueError(f"缓存包含不允许的路径或文件类型：{member.name}")
        name = path.as_posix().casefold() if os.name == "nt" else path.as_posix()
        if name in names:
            raise ValueError(f"缓存包含重复路径：{member.name}")
        names.add(name)
    return members


def restore_cache(root: Path, archive: Path, metadata: dict, kind: str) -> None:
    validate_metadata(identity(root), metadata, kind)
    if archive.stat().st_size != metadata["bytes"] or sha256(archive) != metadata["sha256"]:
        raise ValueError("缓存文件大小或 SHA-256 校验失败")
    lake = confined(root / ".lake", root)
    lake.mkdir(exist_ok=True)
    build = confined(lake / "build", root)
    if (lake / "build").is_symlink():
        raise ValueError("构建目录是符号链接，不能替换")
    # 先检查整个归档，再在工作区内的独立目录解包；失败时保留原有缓存。
    with tempfile.TemporaryDirectory(prefix="cache-restore-", dir=lake) as temporary:
        stage = confined(Path(temporary), root)
        incoming, backup = stage / "incoming", stage / "previous"
        incoming.mkdir()
        with tarfile.open(archive, "r:gz") as bundle:
            members = safe_members(bundle, kind)
            if (len(members) != metadata["files"]
                    or sum(m.size for m in members) != metadata["unpacked_bytes"]):
                raise ValueError("缓存文件清单与归档内容不一致")
            for member in members:
                path = confined(incoming / member.name, incoming)
                path.parent.mkdir(parents=True, exist_ok=True)
                with bundle.extractfile(member) as source, path.open("wb") as destination:
                    shutil.copyfileobj(source, destination)
                path.chmod(member.mode & 0o777)
                os.utime(path, (member.mtime, member.mtime))
        existed = build.exists()
        if existed:
            os.replace(confined(build, root), confined(backup, root))
        try:
            os.replace(confined(incoming, root), confined(build, root))
            build_all(root, kind, no_build=True)
        except BaseException:
            if build.exists():
                os.replace(confined(build, root), confined(stage / "rejected", root))
            if existed:
                os.replace(confined(backup, root), confined(build, root))
            raise
    print(f"已恢复 {kind} 缓存；全部对应目标均通过 --no-build 验证", flush=True)


def download(url: str, destination: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "YesMetaZFC-cache/1"})
    with urllib.request.urlopen(request, timeout=60) as response, destination.open("wb") as out:
        shutil.copyfileobj(response, out)


def get_cache(root: Path, kind: str, repository: str) -> None:
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repository):
        raise ValueError("仓库名必须是 owner/name")
    info = identity(root)
    name = archive_name(info, kind)
    url = f"https://github.com/{repository}/releases/download/cache-{info['revision']}/{name}"
    lake = confined(root / ".lake", root)
    lake.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cache-download-", dir=lake) as temporary:
        stage = confined(Path(temporary), root)
        manifest = stage / (name + ".json")
        try:
            download(url + ".json", manifest)
        except urllib.error.HTTPError as error:
            if error.code == 404:
                raise ValueError(f"此提交/平台的 {kind} 缓存尚未发布：{url}") from error
            raise
        metadata = json.loads(manifest.read_text(encoding="utf-8"))
        validate_metadata(info, metadata, kind)
        if metadata["dirty"]:
            raise ValueError("公开缓存不能来自未提交的源码")
        print(f"下载 {name}（{metadata['bytes'] / 1024**2:.1f} MiB）", flush=True)
        archive = stage / name
        download(url, archive)
        restore_cache(root, archive, metadata, kind)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="项目根目录")
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("info", help="显示当前缓存标识")
    build = commands.add_parser("build", help="检查全部独立模块，默认包含扫描工具")
    profiles = build.add_mutually_exclusive_group()
    profiles.add_argument("--library-only", action="store_true")
    profiles.add_argument("--native", action="store_true", help="另构建静态库、共享库及扫描工具")
    build.add_argument("--no-build", action="store_true", help="只验证目标已存在，不允许重编译")
    for command in ("pack", "get", "restore"):
        subparser = commands.add_parser(command)
        subparser.add_argument("--kind", choices=("lean", "full"), default="lean")
        if command == "pack":
            subparser.add_argument("--output", type=Path, help="默认输出到项目的 tmp/lean-cache")
            subparser.add_argument("--allow-dirty", action="store_true", help="仅供本地缓存试验")
        elif command == "get":
            subparser.add_argument("--repo", default=REPOSITORY)
        else:
            subparser.add_argument("archive", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    if args.command == "info":
        print(json.dumps(identity(root), ensure_ascii=False, indent=2))
    elif args.command == "build":
        kind = "lean" if args.library_only else "full" if args.native else "tools"
        build_all(root, kind, no_build=args.no_build)
    elif args.command == "pack":
        pack_cache(root, args.output or root / "tmp/lean-cache", args.kind, allow_dirty=args.allow_dirty)
    elif args.command == "get":
        get_cache(root, args.kind, args.repo)
    else:
        manifest = Path(str(args.archive) + ".json")
        metadata = json.loads(manifest.read_text(encoding="utf-8"))
        restore_cache(root, args.archive.resolve(), metadata, args.kind)


if __name__ == "__main__":
    if sys.version_info < (3, 11):
        sys.exit("需要 Python 3.11 或以上")
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError, tarfile.TarError) as error:
        print(f"错误：{error}", file=sys.stderr)
        sys.exit(1)
