#!/usr/bin/env python3
"""Exercise compiled checks in a downstream Lake package using cached dependencies."""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def run(cwd, *args, success=True):
    proc = subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        output, _ = proc.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        output, _ = proc.communicate()
        raise AssertionError(f"Timed out: {args}\n{output}")
    if (proc.returncode == 0) != success:
        raise AssertionError(f"Unexpected exit {proc.returncode}: {args}\n{output}")
    return output


MODEL = """set_option veil.modelChecker.maxStoredBuilds 0
veil module NativeBuild
individual active : Bool
#gen_state
after_init { active := false }
action toggle { active := !active }
invariant true
#gen_spec
#model_check compiled {} {} (sequential := true)
#simulate compiled {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)
end NativeBuild
"""


def check_native_inputs(project):
    (project / "App.lean").write_text("import Veil.Core\ndef appValue : Nat := 1\n")
    (project / "Main.lean").write_text("import App\ndef main : IO Unit := IO.println appValue\n")
    (project / "Tests.lean").write_text("import App\n" + MODEL)
    run(project, "lake", "build", "normal")
    # Lean artifacts remain current while a missing native object needs compiling.
    for artifact in (project / ".lake/build/ir").glob("App.c.o*"):
        artifact.unlink()
    output = run(project, "lake", "env", "lean", "Tests.lean")
    assert output.count("No violation") == 2, output
    binaries = list((project / ".lake/model_checker_builds").glob("*/ModelCheckerMain"))
    assert len(binaries) == 2
    mtimes = {p: p.stat().st_mtime_ns for p in binaries}
    # Deduplication must retain dependency traces: changing a package object relinks.
    (project / "extra.c").write_text("int review_extra = 2;\n")
    run(project, "lake", "env", "leanc", "-c", "extra.c", "-o", "extra.o")
    run(project, "lake", "env", "lean", "Tests.lean")
    assert all(p.stat().st_mtime_ns != t for p, t in mtimes.items())


def check_stale_import(project):
    source = project / "App.lean"
    source.write_text("import Veil.Core\n" + MODEL.replace("NativeBuild", "ImportedBuild"))
    run(project, "lake", "build", "App")
    artifact = project / ".lake/build/lib/lean/App.olean"
    before = artifact.stat().st_mtime_ns
    source.write_text(source.read_text() + "\n-- Invalidate the imported Lean artifacts.\n")
    output = run(project, "lake", "env", "lean", "Tests.lean", success=False)
    assert "Imported Lean artifacts for 'App' need rebuilding" in output, output
    assert artifact.stat().st_mtime_ns == before
    run(project, "lake", "build", "+App")
    output = run(project, "lake", "env", "lean", "Tests.lean")
    assert output.count("No violation") == 2, output


def main():
    with tempfile.TemporaryDirectory(prefix="native-build-test-", dir=ROOT / ".lake") as tmp:
        project = Path(tmp)
        (project / "lakefile.lean").write_text(f"""import Lake
open Lake DSL System
package nativeBuildTest where
  moreLinkObjs := #[⟨.packageTarget .anonymous `extraObj⟩]
input_file extraObj where
  path := "extra.o"
require veil from {json.dumps(str(ROOT))}
lean_lib App
lean_lib Tests
lean_exe normal where
  root := `Main
""")
        shutil.copyfile(ROOT / "lean-toolchain", project / "lean-toolchain")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        manifest["name"] = "nativeBuildTest"
        for package in manifest["packages"]:
            package["inherited"] = True
        manifest["packages"].append({"type": "path", "name": "veil", "dir": str(ROOT),
            "inherited": False, "configFile": "lakefile.lean", "manifestFile": "lake-manifest.json"})
        (project / "lake-manifest.json").write_text(json.dumps(manifest))
        (project / ".lake").mkdir()
        (project / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)
        (project / "extra.c").write_text("int review_extra = 1;\n")
        run(project, "lake", "env", "leanc", "-c", "extra.c", "-o", "extra.o")
        check_native_inputs(project)
        check_stale_import(project)
    print("Native build regressions passed")


if __name__ == "__main__":
    main()
