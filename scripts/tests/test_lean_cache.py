"""缓存的错配拒绝、解包边界、恢复回滚及发布完整性测试。"""

import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_cache as cache
import publish_cache


class CacheTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.build = self.root / ".lake/build"
        self.build.mkdir(parents=True)
        (self.build / "existing").write_text("keep me", encoding="utf-8")
        self.info = {
            "format": 1, "revision": "a" * 40, "target": "x86_64-unknown-linux-gnu",
            "toolchain": "leanprover/lean4:v4.33.1", "lean_version": "test compiler",
            "source_sha256": "b" * 64,
        }

    def archive(self, entries=None):
        entries = entries or [("lib/lean/YesMetaZFC.olean", b"test payload", tarfile.REGTYPE)]
        archive = self.root / cache.archive_name(self.info, "lean")
        with tarfile.open(archive, "w:gz") as bundle:
            for name, data, kind in entries:
                member = tarfile.TarInfo(name)
                member.type, member.mode = kind, 0o644
                if kind == tarfile.REGTYPE:
                    member.size = len(data)
                    bundle.addfile(member, io.BytesIO(data))
                else:
                    member.linkname = "../../outside"
                    bundle.addfile(member)
        metadata = {
            **self.info, "kind": "lean", "dirty": False, "archive": archive.name,
            "sha256": cache.sha256(archive), "bytes": archive.stat().st_size,
            "files": len(entries), "unpacked_bytes": sum(len(data) for _, data, _ in entries),
        }
        return archive, metadata

    def test_rejects_identity_mismatch_before_touching_build(self):
        archive, metadata = self.archive()
        for key in ("revision", "target", "toolchain", "lean_version", "source_sha256", "format"):
            with self.subTest(key=key), patch.object(cache, "identity", return_value=self.info):
                with self.assertRaisesRegex(ValueError, "缓存不匹配"):
                    cache.restore_cache(self.root, archive, {**metadata, key: "wrong"}, "lean")
                self.assertTrue((self.build / "existing").exists())

    def test_rejects_corruption_before_touching_build(self):
        archive, metadata = self.archive()
        with archive.open("ab") as stream:
            stream.write(b"corruption")
        with patch.object(cache, "identity", return_value=self.info):
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                cache.restore_cache(self.root, archive, metadata, "lean")
        self.assertTrue((self.build / "existing").exists())

    def test_rejects_paths_and_links(self):
        entries = [
            ("../outside", tarfile.REGTYPE), ("/outside", tarfile.REGTYPE),
            ("lib/lean/../../outside", tarfile.REGTYPE),
            ("lib/lean/C:stream", tarfile.REGTYPE),
            ("lib\\lean\\outside", tarfile.REGTYPE),
            ("lib/lean/link", tarfile.SYMTYPE), ("lib/lean/link", tarfile.LNKTYPE),
            ("lib/lean/device", tarfile.CHRTYPE),
        ]
        for name, kind in entries:
            with self.subTest(name=name, kind=kind):
                archive, metadata = self.archive([(name, b"x", kind)])
                with patch.object(cache, "identity", return_value=self.info):
                    with self.assertRaisesRegex(ValueError, "不允许"):
                        cache.restore_cache(self.root, archive, metadata, "lean")
                self.assertTrue((self.build / "existing").exists())
                self.assertFalse((self.root / "outside").exists())

    def test_rejects_duplicate_members(self):
        entry = ("lib/lean/A.olean", b"x", tarfile.REGTYPE)
        archive, _ = self.archive([entry, entry])
        with tarfile.open(archive) as bundle:
            with self.assertRaisesRegex(ValueError, "重复"):
                cache.safe_members(bundle, "lean")

    def test_rejects_wrong_inventory(self):
        archive, metadata = self.archive()
        metadata["files"] += 1
        with patch.object(cache, "identity", return_value=self.info):
            with self.assertRaisesRegex(ValueError, "清单"):
                cache.restore_cache(self.root, archive, metadata, "lean")
        self.assertTrue((self.build / "existing").exists())

    def test_success_replaces_old_cache_and_verifies_without_build(self):
        archive, metadata = self.archive()
        with patch.object(cache, "identity", return_value=self.info), patch.object(cache, "build_all") as verify:
            cache.restore_cache(self.root, archive, metadata, "lean")
            verify.assert_called_once_with(self.root, "lean", no_build=True)
        self.assertFalse((self.build / "existing").exists())
        self.assertEqual((self.build / "lib/lean/YesMetaZFC.olean").read_bytes(), b"test payload")
        self.assertEqual(list((self.root / ".lake").iterdir()), [self.build])

    def test_failed_lake_verification_restores_previous_cache(self):
        archive, metadata = self.archive()
        failure = subprocess.CalledProcessError(1, ["lake", "--no-build", "build"])
        with patch.object(cache, "identity", return_value=self.info), patch.object(cache, "build_all", side_effect=failure):
            with self.assertRaises(subprocess.CalledProcessError):
                cache.restore_cache(self.root, archive, metadata, "lean")
        self.assertEqual((self.build / "existing").read_text(), "keep me")
        self.assertFalse((self.build / "lib").exists())

    def test_lean_profile_keeps_c_and_metadata_but_not_native_outputs(self):
        for name in ("lib/lean/A.olean.private", "lib/lean/A.ilean", "lib/lean/A.trace",
                     "ir/A.c", "ir/A.c.hash", "ir/A.setup.json", "share/YesMetaZFC/LICENSE"):
            self.assertTrue(cache.selected(PurePosixPath(name), "lean"), name)
        for name in ("ir/A.c.o", "ir/A.c.o.export", "lib/libYesMetaZFC.a", "bin/prove_auto_sweep"):
            self.assertFalse(cache.selected(PurePosixPath(name), "lean"), name)
            self.assertTrue(cache.selected(PurePosixPath(name), "full"), name)

    def test_download_rejects_dirty_manifest_before_fetching_archive(self):
        _, metadata = self.archive()
        metadata["dirty"] = True
        def manifest_only(_url, destination):
            destination.write_text(json.dumps(metadata), encoding="utf-8")
        with patch.object(cache, "identity", return_value=self.info), patch.object(cache, "download", side_effect=manifest_only) as fetch:
            with self.assertRaisesRegex(ValueError, "未提交"):
                cache.get_cache(self.root, "lean", cache.REPOSITORY)
            self.assertEqual(fetch.call_count, 1)

    def test_source_fingerprint_normalizes_line_endings_and_detects_edits(self):
        for name in cache.SOURCE_CONFIG:
            (self.root / name).write_bytes(b"configuration\n")
        source = self.root / "YesMetaZFC.lean"
        source.write_bytes(b"import Init\n")
        def command(_root, *args, **_kwargs):
            return "Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit test, Release)" if args[0] == "lean" else "a" * 40
        with patch.object(cache, "run", side_effect=command):
            first = cache.identity(self.root)
            source.write_bytes(b"import Init\r\n")
            self.assertEqual(first, cache.identity(self.root))
            source.write_bytes(b"import Lean\n")
            self.assertNotEqual(first["source_sha256"], cache.identity(self.root)["source_sha256"])

    def test_identity_preserves_versioned_darwin_targets_and_archive_names(self):
        for name in cache.SOURCE_CONFIG:
            (self.root / name).write_bytes(b"configuration\n")
        (self.root / "YesMetaZFC.lean").write_bytes(b"import Init\n")
        targets = (
            "arm64-apple-darwin24.6.0", "aarch64-apple-darwin25.0.0",
            "x86_64-apple-darwin24.6.0", "x86_64-apple-darwin", "aarch64-apple-darwin",
            "x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu", "x86_64-w64-windows-gnu",
        )
        for target in targets:
            version = (f"Lean (version 4.33.1, {target}, "
                       "commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)")
            with self.subTest(target=target), patch.object(cache, "run", side_effect=[version, "a" * 40]):
                info = cache.identity(self.root)
                self.assertEqual(info["target"], target)
                self.assertEqual(info["lean_version"], version)
                self.assertEqual(cache.archive_name(info, "full"), f"YesMetaZFC-{target}.tar.gz")

    def prepare_pack(self):
        (self.root / "YesMetaZFC.lean").write_text("import Init\n")
        for name in ("LICENSE", "NOTICE"):
            (self.root / name).write_text("test notice\n")
        toolchain = self.root / "toolchain"
        toolchain.mkdir()
        for name in ("LICENSE", "LICENSES"):
            (toolchain / name).write_text("upstream notice\n")
        artifacts = self.build / "lib/lean"
        artifacts.mkdir(parents=True)
        (artifacts / "YesMetaZFC.olean").write_bytes(b"current")
        (artifacts / "DeletedModule.olean").write_bytes(b"stale")
        return self.root / "output"

    def pack_command(self, _root, *args, **_kwargs):
        return str(self.root / "toolchain") if args[:2] == ("lean", "--print-prefix") else ""

    def test_pack_omits_deleted_modules(self):
        output = self.prepare_pack()
        with patch.object(cache, "identity", return_value=self.info), patch.object(cache, "run", side_effect=self.pack_command), patch.object(cache, "build_all"):
            archive = cache.pack_cache(self.root, output, "lean")
        with tarfile.open(archive) as bundle:
            names = bundle.getnames()
        self.assertIn("lib/lean/YesMetaZFC.olean", names)
        self.assertNotIn("lib/lean/DeletedModule.olean", names)
        self.assertIn("share/YesMetaZFC/LICENSE", names)
        self.assertIn("share/YesMetaZFC/third-party/lean4/LICENSES", names)

    def test_source_change_during_pack_preserves_previous_archive(self):
        output = self.prepare_pack()
        output.mkdir()
        archive = output / cache.archive_name(self.info, "lean")
        archive.write_bytes(b"previous archive")
        changed = {**self.info, "source_sha256": "c" * 64}
        with patch.object(cache, "identity", side_effect=[self.info, changed]), patch.object(cache, "run", side_effect=self.pack_command), patch.object(cache, "build_all"):
            with self.assertRaisesRegex(ValueError, "发生变化"):
                cache.pack_cache(self.root, output, "lean")
        self.assertEqual(archive.read_bytes(), b"previous archive")
        self.assertEqual(list(output.iterdir()), [archive])


class PublishTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.environment = {"GITHUB_REPOSITORY": "lanxinge/YesMetaZFC", "GITHUB_REF": "refs/heads/main"}

    def collection(self, targets=None):
        for target in publish_cache.PLATFORMS if targets is None else targets:
            for kind in ("lean", "full"):
                info = {"target": target}
                name = cache.archive_name(info, kind)
                payload = name.encode()
                (self.directory / name).write_bytes(payload)
                metadata = {
                    "format": 1, "revision": "a" * 40, "dirty": False,
                    "source_sha256": "b" * 64, "toolchain": "test", "target": target,
                    "kind": kind, "archive": name, "bytes": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                }
                (self.directory / (name + ".json")).write_text(json.dumps(metadata))

    def test_incomplete_collection_is_not_published(self):
        with patch.dict(os.environ, self.environment), patch.object(subprocess, "check_output", return_value="a" * 40), patch.object(subprocess, "run") as gh:
            with self.assertRaisesRegex(ValueError, "不完整"):
                publish_cache.publish(self.directory)
            gh.assert_not_called()

    def test_complete_published_snapshot_is_not_overwritten(self):
        self.collection()
        names = [p.name for p in self.directory.iterdir()] + ["SHA256SUMS"]
        response = subprocess.CompletedProcess([], 0, json.dumps({"isDraft": False, "assets": [{"name": n} for n in names]}))
        with patch.dict(os.environ, self.environment), patch.object(subprocess, "check_output", return_value="a" * 40), patch.object(subprocess, "run", return_value=response) as gh:
            publish_cache.publish(self.directory)
            self.assertEqual(gh.call_count, 1)
            self.assertEqual(gh.call_args.args[0][2], "view")

    def test_other_branch_cannot_publish(self):
        with patch.dict(os.environ, {**self.environment, "GITHUB_REF": "refs/heads/feature"}):
            with self.assertRaisesRegex(ValueError, "主分支"):
                publish_cache.publish(self.directory)

    def test_versioned_darwin_targets_are_published_without_renaming(self):
        targets = publish_cache.PLATFORMS - {"x86_64-apple-darwin", "aarch64-apple-darwin"}
        targets |= {"x86_64-apple-darwin24.6.0", "arm64-apple-darwin24.6.0"}
        self.collection(targets)
        responses = [subprocess.CompletedProcess([], code, "") for code in (1, 0, 0, 0)]
        with patch.dict(os.environ, self.environment), patch.object(subprocess, "check_output", return_value="a" * 40), patch.object(subprocess, "run", side_effect=responses) as gh:
            publish_cache.publish(self.directory)
            upload = gh.call_args_list[2].args[0]
            self.assertEqual(upload[2], "upload")
            self.assertIn(str(self.directory / "YesMetaZFC-arm64-apple-darwin24.6.0.tar.gz"), upload)
            self.assertIn(str(self.directory / "YesMetaZFC-x86_64-apple-darwin24.6.0-lean.tar.gz"), upload)

    def test_aliases_cannot_supply_duplicate_platform_caches(self):
        self.collection(publish_cache.PLATFORMS | {"arm64-apple-darwin24.6.0"})
        with patch.dict(os.environ, self.environment), patch.object(subprocess, "check_output", return_value="a" * 40), patch.object(subprocess, "run") as gh:
            with self.assertRaisesRegex(ValueError, "重复或未知"):
                publish_cache.publish(self.directory)
            gh.assert_not_called()

    def test_two_profiles_must_use_the_same_exact_darwin_target(self):
        self.collection()
        old = self.directory / "YesMetaZFC-aarch64-apple-darwin.tar.gz.json"
        metadata = json.loads(old.read_text())
        metadata["target"] = "arm64-apple-darwin24.6.0"
        metadata["archive"] = cache.archive_name(metadata, "full")
        (self.directory / "YesMetaZFC-aarch64-apple-darwin.tar.gz").rename(self.directory / metadata["archive"])
        old.unlink()
        (self.directory / (metadata["archive"] + ".json")).write_text(json.dumps(metadata))
        with patch.dict(os.environ, self.environment), patch.object(subprocess, "check_output", return_value="a" * 40), patch.object(subprocess, "run") as gh:
            with self.assertRaisesRegex(ValueError, "目标不一致"):
                publish_cache.publish(self.directory)
            gh.assert_not_called()


if __name__ == "__main__":
    unittest.main()
