from __future__ import annotations
import argparse
import json
import re
import tomllib
import hashlib
import urllib.request
import configparser
from urllib.parse import unquote, quote
import xml.etree.ElementTree as ET
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

MAVEN_CENTRAL = "https://repo1.maven.org/maven2"
GOOGLE_MAVEN = "https://dl.google.com/dl/android/maven2"
JITPACK = "https://jitpack.io"
DEFAULT_MAVEN_REPOSITORIES = [
    MAVEN_CENTRAL,
    GOOGLE_MAVEN,
    JITPACK,
]
POM_CACHE: dict[str, str] = {}
MAVEN_MODEL_CACHE: dict[str, "MavenSurfaceModel"] = {}
NPM_= "https://registry.npmjs.org"
NPM_PACKAGE_CACHE: dict[str, dict[str, Any] | None] = {}
PYPI_= "https://pypi.org/pypi"
PYPI_PACKAGE_CACHE: dict[str, dict[str, Any] | None] = {}
SURFACE_COMMENT_PREFIX = "surface_scanner:"

@dataclass(frozen=True)
class Dependency:
    ecosystem: str
    package_manager: str
    name: str
    version: str | None
    scope: str
    source_file: str
    source_type: str
    confidence: str
    purl: str | None = None
    notes: str | None = None

@dataclass(frozen=True)
class UnresolvedDependency:
    ecosystem: str
    package_manager: str
    raw: str
    source_file: str
    reason: str

@dataclass(frozen=True)
class DuplicateIssue:
    issue_type: str
    key: str
    count: int
    spdx_ids: list[str]
    notes: str | None = None

@dataclass(frozen=True)
class SkippedDependency:
    dependency: Dependency
    reason: str
    matched_spdx_id: str | None = None

@dataclass(frozen=True)
class SurfaceWriteStats:
    packages_added: int = 0
    packages_enriched: int = 0
    packages_repaired: int = 0
    packages_removed: int = 0

@dataclass(frozen=True)
class GradleRepoReport:
    source_file: str
    repository_type: str
    value: str | None
    notes: str | None = None

@dataclass(frozen=True)
class MavenArtifact:
    group: str
    artifact: str
    version: str

@dataclass(frozen=True)
class MavenSurfaceModel:
    properties: dict[str, str]
    dependency_management: dict[tuple[str, str], str]
    repositories: list[str]
    repository_reports: list[GradleRepoReport]
    issues: list[str]
    project_coordinates: set[tuple[str, str]]

# Skips known locations where dependency files aren't located
IGNORED_DIRS = {".git", ".github", "node_modules", "vendor", "target", "build", "dist", ".gradle", ".idea", ".venv", "venv", "__pycache__", ".mypy_cache"}
def should_skip(path: Path) -> bool:
    return any(part in IGNORED_DIRS for part in path.parts)


def repo_files(repo: Path, names: set[str]) -> list[Path]:
    return [p for p in repo.rglob("*") if p.is_file() and p.name in names and not should_skip(p.relative_to(repo))]

def rel(repo: Path, path: Path) -> str:
    return str(path.relative_to(repo))

def make_purl(ecosystem: str, name: str, version: str | None) -> str | None:
    if not version:
        return None

    if ecosystem == "maven":
        if ":" not in name:
            return None
        group, artifact = name.split(":", 1)
        return f"pkg:maven/{group}/{artifact}@{version}"

    if ecosystem == "npm":
        return f"pkg:npm/{name}@{version}"
    if ecosystem == "pypi":
        return f"pkg:pypi/{name}@{version}"
    if ecosystem == "golang":
        return f"pkg:golang/{name}@{version}"
    if ecosystem == "cargo":
        return f"pkg:cargo/{name}@{version}"
    if ecosystem == "composer":
        return f"pkg:composer/{name}@{version}"

    return None


def normalize_name(name: str) -> str:
    return name.strip().lower()


def normalize_pypi_name(name: str) -> str:
    return re.sub(r"[-_.]+", "-", name.strip().lower())

def purl_id(purl: str) -> str | None:
    if not purl.startswith("pkg:"):
        return None

    body = purl[4:].split("?", 1)[0]
    if "/" not in body:
        return None

    ecosystem, rest = body.split("/", 1)
    ecosystem = ecosystem.lower()

    if "@" in rest:
        name_part, version = rest.rsplit("@", 1)
    else:
        name_part, version = rest, None

    name_part = unquote(name_part)
    if ecosystem == "pypi":
        name_part = normalize_pypi_name(name_part)
    else:
        name_part = normalize_name(name_part)

    if version:
        return f"pkg:{ecosystem}/{name_part}@{version}"

    return f"pkg:{ecosystem}/{name_part}"

def dep_scope(scope: str) -> str:
    scope = scope.lower()
    if "test" in scope:
        return "test"
    if scope in {"development", "dev"} or "dev" in scope:
        return "development"
    if scope in {"build", "annotation-processor"} or "processor" in scope:
        return "build"
    if "optional" in scope:
        return "optional"
    if "runtime" in scope:
        return "runtime"
    if "compile" in scope:
        return "compile"

    return "other"

def get_composer_name(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if not isinstance(loc, str):
            continue

        parsed = get_purl_key(loc)
        if parsed and parsed[0] == "composer":
            return parsed[1]

    name = pkg.get("name")
    if isinstance(name, str):
        return normalize_name(name)

    return None

def repair_comp_pkg(sbom_data: dict[str, Any], exact_composer_versions: dict[str, str]) -> int:
    sbom = sbom_data.get("sbom", sbom_data)
    repaired = 0

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        name = get_composer_name(pkg)
        if not name:
            continue

        exact_version = exact_composer_versions.get(name)
        if not exact_version:
            continue

        current_version = pkg.get("versionInfo")
        current_purl = None

        for ref in pkg.get("externalRefs", []) or []:
            if ref.get("referenceType") == "purl":
                current_purl = ref.get("referenceLocator")
                break

        desired_purl = make_purl("composer", name, exact_version)

        if current_version == exact_version and current_purl == desired_purl:
            continue

        pkg["versionInfo"] = exact_version

        refs = pkg.setdefault("externalRefs", [])
        updated = False

        for ref in refs:
            if ref.get("referenceType") == "purl":
                ref["referenceCategory"] = "PACKAGE-MANAGER"
                ref["referenceLocator"] = desired_purl
                updated = True
                break

        if not updated:
            refs.append({
                "referenceCategory": "PACKAGE-MANAGER",
                "referenceType": "purl",
                "referenceLocator": desired_purl,
            })

        repaired += 1

    return repaired

def load_sbom_pkgs(sbom_path: Path) -> set[str]:
    data = json.loads(sbom_path.read_text(encoding="utf-8"))
    sbom = data.get("sbom", data)

    identities: set[str] = set()

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        identity = get_pkg_id(pkg)
        if identity:
            identities.add(identity)

    return identities


def get_pkg_eco(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator", "")
        parsed = get_purl_key(loc)
        if parsed:
            return parsed[0]
    return None


def get_purl_key(purl: str) -> tuple[str, str] | None:
    if not purl.startswith("pkg:"):
        return None

    body = purl[4:].split("?", 1)[0]
    if "/" not in body:
        return None

    ecosystem, rest = body.split("/", 1)

    if "@" in rest and not (ecosystem == "npm" and rest.startswith("@") and rest.count("@") == 1):
        versionless = rest.rsplit("@", 1)[0]
    else:
        versionless = rest

    if ecosystem == "maven":
        parts = versionless.split("/")
        if len(parts) >= 2:
            group = "/".join(parts[:-1]).replace("/", ".")
            artifact = parts[-1]
            return ("maven", normalize_name(f"{group}:{artifact}"))

    ecosystem_map = {
        "npm": "npm",
        "pypi": "pypi",
        "golang": "golang",
        "cargo": "cargo",
        "composer": "composer",
        "gem": "ruby",
        "nuget": "nuget",
    }

    mapped = ecosystem_map.get(ecosystem)
    if mapped:
        if mapped == "pypi":
            return (mapped, normalize_pypi_name(unquote(versionless)))
        return (mapped, normalize_name(unquote(versionless)))

    return None

def get_pkg_id(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if isinstance(loc, str) and loc.startswith("pkg:"):
            return purl_id(loc)

    name = pkg.get("name")
    version = pkg.get("versionInfo")

    if not isinstance(name, str):
        return None

    if not isinstance(version, str) or version in {"", "NOASSERTION"}:
        return None

    inferred = get_pkg_eco(pkg)
    if not inferred:
        return None

    return f"{inferred}:{name.lower()}@{version.lower()}"

def find_dupe_pkgs(sbom_data: dict[str, Any]) -> list[DuplicateIssue]:
    sbom = sbom_data.get("sbom", sbom_data)
    seen: dict[str, list[str]] = {}

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        identity = get_pkg_id(pkg)
        spdx_id = pkg.get("SPDXID", "NO_SPDX_ID")

        if identity:
            seen.setdefault(identity, []).append(spdx_id)

    duplicates: list[DuplicateIssue] = []

    for identity, spdx_ids in seen.items():
        if len(spdx_ids) > 1:
            duplicates.append(DuplicateIssue(
                issue_type="duplicate_package",
                key=identity,
                count=len(spdx_ids),
                spdx_ids=spdx_ids,
                notes="Multiple SBOM packages appear to describe the same dependency identity.",
            ))

    return duplicates

def get_dep_id(dep: Dependency) -> str | None:
    if dep.purl:
        identity = purl_id(dep.purl)
        if identity:
            return identity

    if dep.ecosystem == "pypi":
        name = normalize_pypi_name(dep.name)
        if not dep.version:
            return f"pypi:{name}"
        return f"pypi:{name}@{dep.version.lower()}"

    if not dep.version:
        return None

    return f"{dep.ecosystem}:{normalize_name(dep.name)}@{dep.version.lower()}"

def get_pypi_id(identity: str) -> tuple[str, str | None] | None:
    if identity.startswith("pkg:pypi/"):
        body = identity[len("pkg:pypi/"):]
        if "@" in body:
            name, version = body.rsplit("@", 1)
            return normalize_pypi_name(unquote(name)), unquote(version).lower()
        return normalize_pypi_name(unquote(body)), None

    if identity.startswith("pypi:"):
        body = identity[len("pypi:"):]
        if "@" in body:
            name, version = body.rsplit("@", 1)
            return normalize_pypi_name(name), version.lower()
        return normalize_pypi_name(body), None

    return None

def get_pypi_spdxid(dep: Dependency, identity_to_spdxid: dict[str, str]) -> str | None:
    if dep.ecosystem != "pypi" or not dep.version:
        return None

    dep_name = normalize_pypi_name(dep.name)
    dep_version = dep.version.strip().lower()

    for identity, spdxid in identity_to_spdxid.items():
        parsed = get_pypi_id(identity)
        if not parsed:
            continue
        sbom_name, sbom_version = parsed
        if sbom_name != dep_name or not sbom_version:
            continue
        if not is_pypi_ver(sbom_version):
            continue
        if dep_version == sbom_version:
            return spdxid
        if dep_version.startswith("==") and dep_version[2:] == sbom_version:
            return spdxid
        if dep_version.startswith((">=", "<=", "~=", ">", "<")):
            if pypi_match_req(dep_version, sbom_version):
                return spdxid

    return None

def get_comp_id(identity: str) -> tuple[str, str | None] | None:
    if identity.startswith("pkg:composer/"):
        body = identity[len("pkg:composer/"):]
        if "@" in body:
            name, version = body.rsplit("@", 1)
            return normalize_name(unquote(name)), unquote(version).lower()
        return normalize_name(unquote(body)), None

    if identity.startswith("composer:"):
        body = identity[len("composer:"):]
        if "@" in body:
            name, version = body.rsplit("@", 1)
            return normalize_name(name), version.lower()
        return normalize_name(body), None

    return None

def get_comp_spdxid(dep: Dependency, identity_to_spdxid: dict[str, str]) -> str | None:
    if dep.ecosystem != "composer":
        return None

    dep_name = normalize_name(dep.name)

    for identity, spdxid in identity_to_spdxid.items():
        parsed = get_comp_id(identity)
        if not parsed:
            continue

        sbom_name, _sbom_version = parsed
        if sbom_name == dep_name:
            return spdxid

    return None

def get_npm_id(identity: str) -> tuple[str, str] | None:
    if not identity.startswith("pkg:npm/") or "@" not in identity:
        return None

    body = identity[len("pkg:npm/"):]
    name, version = body.rsplit("@", 1)
    return unquote(name).lower(), unquote(version).lower()


def get_npm_semvers(version: str) -> tuple[int, int, int] | None:
    m = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)(?:[-+][A-Za-z0-9.-]+)?", version.strip())
    if not m:
        return None
    return int(m.group(1)), int(m.group(2)), int(m.group(3))

def matches_npm_range(declared: str, exact: str) -> bool:
    declared = declared.strip().lower()
    exact = exact.strip().lower()

    if declared.startswith("v"):
        declared = declared[1:]
    if exact.startswith("v"):
        exact = exact[1:]

    exact_parsed = get_npm_semvers(exact)
    if not exact_parsed:
        return False

    if declared == exact:
        return True

    if declared in {"*", "x", "latest"}:
        return True

    # Version #'s: 
    # 1.x or 1.2.x
    x_match = re.fullmatch(r"(\d+)(?:\.(\d+))?\.x", declared)
    if x_match:
        e_major, e_minor, _e_patch = exact_parsed
        major = int(x_match.group(1))
        minor = int(x_match.group(2)) if x_match.group(2) is not None else None

        if minor is None:
            return e_major == major
        return e_major == major and e_minor == minor

    # >=1.2.3
    if declared.startswith(">="):
        base = get_npm_semvers(declared[2:])
        return bool(base and exact_parsed >= base)

    # >1.2.3
    if declared.startswith(">"):
        base = get_npm_semvers(declared[1:])
        return bool(base and exact_parsed > base)

    # <=1.2.3
    if declared.startswith("<="):
        base = get_npm_semvers(declared[2:])
        return bool(base and exact_parsed <= base)

    # <1.2.3
    if declared.startswith("<"):
        base = get_npm_semvers(declared[1:])
        return bool(base and exact_parsed < base)

    if declared.startswith("^"):
        base = get_npm_semvers(declared[1:])
        if not base:
            return False

        e_major, e_minor, e_patch = exact_parsed
        b_major, b_minor, b_patch = base

        if exact_parsed < base:
            return False

        if b_major > 0:
            return e_major == b_major
        if b_minor > 0:
            return e_major == 0 and e_minor == b_minor
        return e_major == 0 and e_minor == 0 and e_patch == b_patch

    if declared.startswith("~"):
        base = get_npm_semvers(declared[1:])
        if not base:
            return False

        e_major, e_minor, e_patch = exact_parsed
        b_major, b_minor, b_patch = base

        return exact_parsed >= base and e_major == b_major and e_minor == b_minor

    return False

def is_local_ver(version: str) -> bool:
    v = version.strip().lower()
    return (
        v.startswith("workspace:")
        or v.startswith("file:")
        or v.startswith("link:")
        or v.startswith("path:")
        or v.startswith("../")
        or v.startswith("./")
    )

def is_git_ver(version: str) -> bool:
    v = version.strip().lower()
    return (
        v.startswith("git+")
        or v.startswith("github:")
        or v.startswith("http://")
        or v.startswith("https://")
        or ".git#" in v
    )

def is_npm_alias(version: str) -> bool:
    return version.strip().lower().startswith("npm:")

def is_npm_ver(version: str | None) -> bool:
    if not version:
        return False

    return bool(re.fullmatch(
        r"\d+\.\d+\.\d+(?:[-+][A-Za-z0-9.-]+)?",
        version.strip(),
    ))

def npm_lfname(selector: str) -> str | None:
    selector = selector.strip().strip('"').strip("'")

    if selector.startswith("@"):
        index = selector.rfind("@")
        if index > 0:
            return selector[:index]
        return selector

    if "@" in selector:
        return selector.split("@", 1)[0]

    return selector or None

def yarn_lfver(lock_path: Path, versions: dict[str, str]) -> None:
    text = lock_path.read_text(encoding="utf-8", errors="ignore")

    current_names: list[str] = []

    for line in text.splitlines():
        if not line.strip():
            continue

        if not line.startswith((" ", "\t")) and line.rstrip().endswith(":"):
            raw_key = line.rstrip()[:-1]
            current_names = []

            for selector in raw_key.split(","):
                name = npm_lfname(selector)
                if name:
                    current_names.append(normalize_name(name))

            continue

        m = re.match(r'^\s+version\s+["\']([^"\']+)["\']', line)
        if m and current_names:
            version = m.group(1)
            if is_npm_ver(version):
                for name in current_names:
                    versions[name] = version


def pnpm_lfvers(lock_path: Path, versions: dict[str, str]) -> None:
    text = lock_path.read_text(encoding="utf-8", errors="ignore")

    patterns = [
        # pnpm v5/v6 style: /react/18.2.0:
        r"^\s*/((?:@[^/\s]+/)?[^/\s@]+)[/@]([^:\s()]+)(?:\([^)]*\))?:\s*$",

        # pnpm newer style: react@18.2.0:
        r"^\s*['\"]?((?:@[^/\s]+/)?[^/\s@]+)@([^:'\"\s()]+)(?:\([^)]*\))?['\"]?:\s*$",
    ]

    for line in text.splitlines():
        for p in patterns:
            m = re.match(p, line)
            if not m:
                continue

            name, version = m.groups()
            if is_npm_ver(version):
                versions[normalize_name(name)] = version
            break

def npm_load_lfver(repo: Path) -> dict[str, str]:
    versions: dict[str, str] = {}

    for lock_path in repo_files(repo, {"package-lock.json", "npm-shrinkwrap.json"}):
        try:
            data = json.loads(lock_path.read_text(encoding="utf-8"))
        except Exception:
            continue

        packages = data.get("packages")
        if isinstance(packages, dict):
            for package_path, package_data in packages.items():
                if not isinstance(package_data, dict):
                    continue
                if not package_path.startswith("node_modules/"):
                    continue

                name = package_path[len("node_modules/"):]
                version = package_data.get("version")

                if isinstance(version, str) and is_npm_ver(version):
                    versions[normalize_name(name)] = version

        dependencies = data.get("dependencies")
        if isinstance(dependencies, dict):
            npm_lfdeps(dependencies, versions)

    for lock_path in repo_files(repo, {"yarn.lock"}):
        try:
            yarn_lfver(lock_path, versions)
        except Exception:
            continue

    for lock_path in repo_files(repo, {"pnpm-lock.yaml"}):
        try:
            pnpm_lfvers(lock_path, versions)
        except Exception:
            continue

    return versions

def npm_lfdeps(dependencies: dict[str, Any], versions: dict[str, str]) -> None:
    for name, dep_data in dependencies.items():
        if not isinstance(dep_data, dict):
            continue

        version = dep_data.get("version")
        if isinstance(version, str) and is_npm_ver(version):
            versions[normalize_name(name)] = version

        nested = dep_data.get("dependencies")
        if isinstance(nested, dict):
            npm_lfdeps(nested, versions)

def npm_get_metadata(name: str) -> dict[str, Any] | None:
    normalized = normalize_name(name)

    if normalized in NPM_PACKAGE_CACHE:
        return NPM_PACKAGE_CACHE[normalized]

    encoded_name = quote(name, safe="@")
    url = f"{NPM_REGISTRY}/{encoded_name}"

    try:
        req = urllib.request.Request(
            url,
            headers={"Accept": "application/vnd.npm.install-v1+json"},
        )
        with urllib.request.urlopen(req, timeout=20) as response:
            data = json.loads(response.read().decode("utf-8", errors="replace"))
            NPM_PACKAGE_CACHE[normalized] = data
            return data
    except Exception:
        NPM_PACKAGE_CACHE[normalized] = None
        return None


def npm_sort_key(version: str) -> tuple[int, int, int, int, str]:
    parsed = get_npm_semvers(version)
    if not parsed:
        return (-1, -1, -1, -1, version)

    major, minor, patch = parsed
    prerelease_penalty = 0 if "-" not in version else -1
    return (major, minor, patch, prerelease_penalty, version)


def npm_solver(name: str, declared_version: str) -> tuple[str | None, str | None]:
    metadata = npm_get_metadata(name)
    if not metadata:
        return None, "npm lookup failed."

    declared = declared_version.strip().lower()

    dist_tags = metadata.get("dist-tags") or {}
    versions_obj = metadata.get("versions") or {}

    if not isinstance(versions_obj, dict):
        return None, "npm metadata did not contain versions."

    if declared in {"latest", "*", "x"}:
        latest = dist_tags.get("latest")
        if isinstance(latest, str) and is_npm_ver(latest):
            return latest, f"Resolved npm declaration {declared_version!r} from dist-tag to {latest}."

    published_versions = [
        version for version in versions_obj.keys()
        if isinstance(version, str) and is_npm_ver(version)
    ]

    allow_prerelease = "-" in declared
    candidates = [
        version for version in published_versions
        if matches_npm_range(declared, version)
        and (allow_prerelease or "-" not in version)
    ]

    if not candidates:
        return None, f"npm lookup found no exact published version satisfying {declared_version!r}."

    best = sorted(candidates, key=npm_sort_key)[-1]
    return best, f"Resolved npm declaration {declared_version!r} from metadata to {best}."

def resolve_npm_declared_version(name: str, declared_version: str | None, lock_versions: dict[str, str]) -> tuple[str | None, str | None]:
    if not declared_version:
        return None, "No npm version declared."

    declared = declared_version.strip()
    locked = lock_versions.get(normalize_name(name))
    if locked:
        return locked, f"Declared npm requirement {declared!r} resolved from lockfile to exact version {locked}."
    if is_npm_ver(declared):
        return declared, None
    if is_local_ver(declared):
        return declared, "Local/workspace/path npm dependency, not resolved through registry."
    if is_git_ver(declared):
        return declared, "Git/URL npm dependency not resolved through registry."
    if is_npm_alias(declared):
        return declared, "npm alias dependency not resolved through registry."
    if is_github_dep_ver(declared):
        return declared, "GitHub-hosted npm dependency detected as real direct dependency but not resolved through npm registry."

    registry_version, registry_note = npm_solver(name, declared)
    if registry_version:
        return registry_version, registry_note

    return declared, registry_note or "No exact npm version available from lockfile or registry, declaration kept for report only."

def is_pypi_ver(version: str | None) -> bool:
    if not version:
        return False

    v = version.strip()
    if v.lower() in {"", "noassertion"}:
        return False

    # Practical PEP 440:
    return bool(re.fullmatch(
        r"\d+(?:\.\d+)*(?:a\d+|b\d+|rc\d+)?(?:\.post\d+)?(?:\.dev\d+)?(?:\+[A-Za-z0-9_.-]+)?",
        v,
        re.IGNORECASE,
    ))

def get_pypi_metadata(name: str) -> dict[str, Any] | None:
    normalized = normalize_pypi_name(name)

    if normalized in PYPI_PACKAGE_CACHE:
        return PYPI_PACKAGE_CACHE[normalized]

    url = f"{PYPI_REGISTRY}/{quote(normalized)}/json"

    try:
        with urllib.request.urlopen(url, timeout=20) as response:
            data = json.loads(response.read().decode("utf-8", errors="replace"))
            PYPI_PACKAGE_CACHE[normalized] = data
            return data
    except Exception:
        PYPI_PACKAGE_CACHE[normalized] = None
        return None

def get_pypi_ver(version: str) -> tuple[int, ...]:
    parts = re.findall(r"\d+", version)
    return tuple(int(p) for p in parts) if parts else (-1,)

def pypi_match_req(requirement: str, exact: str) -> bool:
    req = requirement.strip()
    exact_tuple = get_pypi_ver(exact)

    if req.startswith("=="):
        return exact == req[2:]

    for part in req.split(","):
        part = part.strip()
        if not part:
            continue

        if part.startswith(">="):
            if exact_tuple < get_pypi_ver(part[2:]):
                return False
        elif part.startswith(">"):
            if exact_tuple <= get_pypi_ver(part[1:]):
                return False
        elif part.startswith("<="):
            if exact_tuple > get_pypi_ver(part[2:]):
                return False
        elif part.startswith("<"):
            if exact_tuple >= get_pypi_ver(part[1:]):
                return False
        elif part.startswith("~="):
            base = part[2:]
            if exact_tuple < get_pypi_ver(base):
                return False
        elif is_pypi_ver(part):
            if exact != part:
                return False
    return True

def get_pypi_bestver(name: str, declared_version: str) -> tuple[str | None, str | None]:
    metadata = get_pypi_metadata(name)
    if not metadata:
        return None, "PyPI lookup failed."

    releases = metadata.get("releases") or {}
    if not isinstance(releases, dict):
        return None, "PyPI metadata did not contain releases."

    candidates = [
        version for version in releases.keys()
        if isinstance(version, str)
        and is_pypi_ver(version)
        and pypi_match_req(declared_version, version)
    ]

    if not candidates:
        return None, f"PyPI lookup found no exact published version for {declared_version!r}."

    best = sorted(candidates, key=get_pypi_ver)[-1]
    return best, f"Resolved PyPI declaration {declared_version!r} from metadata to {best}."

def get_pypi_latest_ver(name: str) -> tuple[str | None, str | None]:
    metadata = get_pypi_metadata(name)
    if not metadata:
        return None, "PyPI lookup failed."

    info = metadata.get("info") or {}
    latest = info.get("version")

    if isinstance(latest, str) and is_pypi_ver(latest):
        return latest, f"No PyPI version declared, resolved from PyPI latest release to {latest}."

    releases = metadata.get("releases") or {}
    if not isinstance(releases, dict):
        return None, "PyPI metadata did not contain releases."

    candidates = [
        version for version in releases.keys()
        if isinstance(version, str)
        and is_pypi_ver(version)
    ]

    if not candidates:
        return None, "No PyPI version declared and no stable published version found."

    best = sorted(candidates, key=get_pypi_ver)[-1]
    return best, f"No PyPI version declared, resolved from PyPI release list to {best}."

def resolve_pypi_ver(name: str, declared_version: str | None, lock_versions: dict[str, str] | None = None) -> tuple[str | None, str | None]:
    lock_versions = lock_versions or {}
    locked = lock_versions.get(normalize_pypi_name(name))

    if locked:
        return locked, f"Resolved PyPI declaration from lockfile to exact version {locked}."

    if not declared_version:
        registry_version, registry_note = get_pypi_latest_ver(name)
        if registry_version:
            return registry_version, registry_note
        return None, registry_note or "No PyPI version declared."

    declared = declared_version.strip()

    if declared.startswith("==") and is_pypi_ver(declared[2:]):
        return declared[2:], f"Resolved exact PyPI declaration {declared!r} to {declared[2:]}."

    if is_pypi_ver(declared):
        return declared, None

    registry_version, registry_note = get_pypi_bestver(name, declared)
    if registry_version:
        return registry_version, registry_note

    return declared, registry_note or "No exact PyPI version available from lockfile or registry, declaration kept for report only."

def get_pypi_vers(deps: list[Dependency]) -> dict[str, str]:
    versions: dict[str, str] = {}

    for dep in deps:
        if dep.ecosystem != "pypi":
            continue
        if dep.version and is_pypi_ver(dep.version):
            versions[normalize_pypi_name(dep.name)] = dep.version

    return versions

def get_pypi_depname(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if not isinstance(loc, str):
            continue

        parsed = get_purl_key(loc)
        if parsed and parsed[0] == "pypi":
            return parsed[1]

    name = pkg.get("name")
    if isinstance(name, str):
        return normalize_pypi_name(name)

    return None

def is_valid_pypi_dep(pkg: dict[str, Any]) -> bool:
    is_pypi = False

    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if isinstance(loc, str) and loc.startswith("pkg:pypi/"):
            is_pypi = True
            break

    if not is_pypi:
        return False

    version = pkg.get("versionInfo")
    return not is_pypi_ver(version if isinstance(version, str) else None)

def repair_pypi_pkg(sbom_data: dict[str, Any], exact_pypi_versions: dict[str, str]) -> tuple[int, int]:
    sbom = sbom_data.get("sbom", sbom_data)
    packages = sbom.get("packages", []) or []

    repaired = 0
    removed = 0
    removed_spdxids: set[str] = set()
    kept_packages: list[dict[str, Any]] = []

    for pkg in packages:
        if not isinstance(pkg, dict):
            kept_packages.append(pkg)
            continue

        if not is_valid_pypi_dep(pkg):
            kept_packages.append(pkg)
            continue

        name = get_pypi_depname(pkg)
        spdxid = pkg.get("SPDXID")
        exact_version = exact_pypi_versions.get(name) if name else None

        if name and exact_version:
            pkg["versionInfo"] = exact_version

            refs = pkg.setdefault("externalRefs", [])
            updated = False

            for ref in refs:
                if ref.get("referenceType") == "purl":
                    ref["referenceCategory"] = "PACKAGE-MANAGER"
                    ref["referenceLocator"] = make_purl("pypi", name, exact_version)
                    updated = True
                    break

            if not updated:
                refs.append({
                    "referenceCategory": "PACKAGE-MANAGER",
                    "referenceType": "purl",
                    "referenceLocator": make_purl("pypi", name, exact_version),
                })

            kept_packages.append(pkg)
            repaired += 1
        else:
            if isinstance(spdxid, str):
                removed_spdxids.add(spdxid)
            removed += 1

    sbom["packages"] = kept_packages

    if removed_spdxids:
        sbom["relationships"] = [
            rel_obj for rel_obj in sbom.get("relationships", []) or []
            if not (
                isinstance(rel_obj, dict)
                and (
                    rel_obj.get("spdxElementId") in removed_spdxids
                    or rel_obj.get("relatedSpdxElement") in removed_spdxids
                )
            )
        ]

    return repaired, removed

def should_add_dependency(dep: Dependency, sbom_package_identities: set[str], identity_to_spdxid: dict[str, str]) -> tuple[bool, str, str | None]:
    identity = get_dep_id(dep)

    if identity is None:
        return False, "No strict dependency identity could be created.", None

    pypi_match = get_pypi_spdxid(dep, identity_to_spdxid)
    if pypi_match:
        return False, "PyPI package already exists in SBOM by normalized package name.", pypi_match
    
    composer_match = get_comp_spdxid(dep, identity_to_spdxid)
    if composer_match:
        return False, "Composer package already exists in SBOM by package name.", composer_match

    if not dep.version:
        return False, "Dependency has no version, skipped to avoid adding ambiguous package.", None

    version = dep.version.strip()

    if is_local_ver(version):
        return False, "Local/workspace/path dependency, not added as external package.", None

    if is_github_dep_ver(version):
        return False, "GitHub-hosted dependency detected, real direct dependency but not auto-added as npm package.", None

    if is_git_ver(version):
        return False, "Git/URL dependency requires special purl handling, skipped for now.", None

    if dep.ecosystem == "npm" and is_npm_alias(version):
        return False, "npm alias dependency requires resolution, skipped for now.", None

    if identity in sbom_package_identities:
        return False, "Exact dependency identity already exists in SBOM.", identity_to_spdxid.get(identity)

    npm_match = get_npm_spdxid(dep, identity_to_spdxid)
    if npm_match:
        return False, "npm declared range is already satisfied by exact package in SBOM.", npm_match
    
    if dep.ecosystem == "npm" and not is_npm_ver(version):
        return False, "npm declaration has no exact resolved version, kept in report but not added as SBOM package.", None

    if dep.ecosystem == "pypi" and not is_pypi_ver(version):
        return False, "PyPI declaration has no exact resolved version, kept in report but not added as SBOM package.", None

    return True, "Dependency is missing and safe to auto-add.", None

def get_unique_ids(deps: list[Dependency]) -> set[str]:
    ids: set[str] = set()

    for dep in deps:
        dep_id = get_dep_id(dep)
        if dep_id:
            ids.add(dep_id)

    return ids

def get_dupe_relationships(sbom_data: dict[str, Any]) -> list[DuplicateIssue]:
    sbom = sbom_data.get("sbom", sbom_data)
    seen: dict[str, list[str]] = {}

    for rel_obj in sbom.get("relationships", []) or []:
        if not isinstance(rel_obj, dict):
            continue

        src = rel_obj.get("spdxElementId")
        dst = rel_obj.get("relatedSpdxElement")
        typ = rel_obj.get("relationshipType")

        if not src or not dst or not typ:
            continue

        key = f"{src}|{typ}|{dst}"
        seen.setdefault(key, []).append(key)

    duplicates: list[DuplicateIssue] = []

    for key, entries in seen.items():
        if len(entries) > 1:
            duplicates.append(DuplicateIssue(
                issue_type="duplicate_relationship",
                key=key,
                count=len(entries),
                spdx_ids=[],
                notes="The same SPDX relationship appears more than once.",
            ))

    return duplicates

def get_npm_vers(deps: list[Dependency]) -> dict[str, str]:
    versions: dict[str, str] = {}

    for dep in deps:
        if dep.ecosystem != "npm":
            continue
        if dep.version and is_npm_ver(dep.version):
            versions[normalize_name(dep.name)] = dep.version

    return versions

def get_npm_name(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if not isinstance(loc, str):
            continue

        parsed = get_purl_key(loc)
        if parsed and parsed[0] == "npm":
            return parsed[1]

    name = pkg.get("name")
    if isinstance(name, str):
        return normalize_name(name)

    return None


def is_valid_npm_dep(pkg: dict[str, Any]) -> bool:
    is_npm = False

    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if isinstance(loc, str) and loc.startswith("pkg:npm/"):
            is_npm = True
            break

    if not is_npm:
        return False

    version = pkg.get("versionInfo")
    return not isinstance(version, str) or not is_npm_ver(version)


def repair_npm_pkg(sbom_data: dict[str, Any], exact_npm_versions: dict[str, str]) -> tuple[int, int]:
    sbom = sbom_data.get("sbom", sbom_data)
    packages = sbom.get("packages", []) or []
    repaired = 0
    removed = 0
    removed_spdxids: set[str] = set()
    kept_packages: list[dict[str, Any]] = []

    for pkg in packages:
        if not isinstance(pkg, dict):
            kept_packages.append(pkg)
            continue

        if not is_valid_npm_dep(pkg):
            kept_packages.append(pkg)
            continue

        name = get_npm_name(pkg)
        spdxid = pkg.get("SPDXID")

        exact_version = exact_npm_versions.get(name) if name else None

        if name and exact_version:
            pkg["versionInfo"] = exact_version

            refs = pkg.setdefault("externalRefs", [])
            updated = False

            for ref in refs:
                if ref.get("referenceType") == "purl":
                    ref["referenceCategory"] = "PACKAGE-MANAGER"
                    ref["referenceLocator"] = make_purl("npm", name, exact_version)
                    updated = True
                    break

            if not updated:
                refs.append({
                    "referenceCategory": "PACKAGE-MANAGER",
                    "referenceType": "purl",
                    "referenceLocator": make_purl("npm", name, exact_version),
                })

            kept_packages.append(pkg)
            repaired += 1
        else:
            if isinstance(spdxid, str):
                removed_spdxids.add(spdxid)
            removed += 1

    sbom["packages"] = kept_packages

    if removed_spdxids:
        kept_relationships = []
        for rel_obj in sbom.get("relationships", []) or []:
            if not isinstance(rel_obj, dict):
                kept_relationships.append(rel_obj)
                continue

            src = rel_obj.get("spdxElementId")
            dst = rel_obj.get("relatedSpdxElement")

            if src in removed_spdxids or dst in removed_spdxids:
                continue

            kept_relationships.append(rel_obj)

        sbom["relationships"] = kept_relationships

    return repaired, removed

def dedupe_pkgs(sbom_data: dict[str, Any]) -> int:
    sbom = sbom_data.get("sbom", sbom_data)

    packages = sbom.get("packages", []) or []
    relationships = sbom.get("relationships", []) or []

    identity_to_kept_spdxid: dict[str, str] = {}
    removed_to_kept_spdxid: dict[str, str] = {}
    deduped_packages: list[dict[str, Any]] = []

    for pkg in packages:
        if not isinstance(pkg, dict):
            deduped_packages.append(pkg)
            continue

        identity = get_pkg_id(pkg)
        spdxid = pkg.get("SPDXID")

        if not identity or not isinstance(spdxid, str):
            deduped_packages.append(pkg)
            continue

        kept_spdxid = identity_to_kept_spdxid.get(identity)

        if kept_spdxid is None:
            identity_to_kept_spdxid[identity] = spdxid
            deduped_packages.append(pkg)
        else:
            removed_to_kept_spdxid[spdxid] = kept_spdxid

    sbom["packages"] = deduped_packages

    deduped_relationships: list[dict[str, Any]] = []
    seen_relationships: set[tuple[str, str, str]] = set()

    for rel_obj in relationships:
        if not isinstance(rel_obj, dict):
            deduped_relationships.append(rel_obj)
            continue

        new_rel = dict(rel_obj)

        src = new_rel.get("spdxElementId")
        dst = new_rel.get("relatedSpdxElement")
        typ = new_rel.get("relationshipType")

        if isinstance(src, str):
            new_rel["spdxElementId"] = removed_to_kept_spdxid.get(src, src)

        if isinstance(dst, str):
            new_rel["relatedSpdxElement"] = removed_to_kept_spdxid.get(dst, dst)

        src = new_rel.get("spdxElementId")
        dst = new_rel.get("relatedSpdxElement")
        typ = new_rel.get("relationshipType")

        if isinstance(src, str) and isinstance(dst, str) and isinstance(typ, str):
            key = (src, typ, dst)
            if key in seen_relationships:
                continue
            seen_relationships.add(key)

        deduped_relationships.append(new_rel)

    sbom["relationships"] = deduped_relationships

    return len(removed_to_kept_spdxid)

# -------------------------
# Java: Maven
# -------------------------

def strip_xml(root: ET.Element) -> None:
    for elem in root.iter():
        if "}" in elem.tag:
            elem.tag = elem.tag.split("}", 1)[1]

def pom_matches_artifact(pom_path: Path, group: str, artifact: str, version: str) -> bool:
    try:
        tree = ET.parse(pom_path)
        root = tree.getroot()
        strip_xml(root)
    except Exception:
        return False

    pom_group = text_at(root, "groupId")
    pom_artifact = text_at(root, "artifactId")
    pom_version = normalize_maven_version(text_at(root, "version"))

    return pom_group == group and pom_artifact == artifact and pom_version == version


def get_parent_pom(current_pom: Path, parent_node: ET.Element, parent_group: str, parent_artifact: str, parent_version: str) -> Path | None:
    relative_path = text_at(parent_node, "relativePath")

    candidates: list[Path] = []

    if relative_path is not None and relative_path.strip() != "":
        candidates.append((current_pom.parent / relative_path).resolve())
    else:
        candidates.append((current_pom.parent / "../pom.xml").resolve())

    for parent_dir in current_pom.parents:
        candidates.append((parent_dir / "pom.xml").resolve())

    seen: set[Path] = set()
    for candidate in candidates:
        if candidate in seen:
            continue
        seen.add(candidate)

        if candidate == current_pom:
            continue
        if not candidate.exists() or candidate.name != "pom.xml":
            continue

        if pom_matches_artifact(candidate, parent_group, parent_artifact, parent_version):
            return candidate

    return None

def get_maven_coordinates(repo: Path) -> set[tuple[str, str]]:
    coords: set[tuple[str, str]] = set()

    for pom in repo_files(repo, {"pom.xml"}):
        try:
            tree = ET.parse(pom)
            root = tree.getroot()
            strip_xml(root)
        except Exception:
            continue

        group = text_at(root, "groupId")
        artifact = text_at(root, "artifactId")

        parent = root.find("parent")
        parent_group = text_at(parent, "groupId") if parent is not None else None

        resolved_group = group or parent_group

        if resolved_group and artifact:
            coords.add((resolved_group, artifact))

    return coords

def parse_pom(repo: Path, pom: Path, local_maven_projects: set[tuple[str, str]], extra_repositories: list[str] | None = None) -> tuple[list[Dependency], list[UnresolvedDependency], list[GradleRepoReport]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []
    repository_reports: list[GradleRepoReport] = []

    try:
        tree = ET.parse(pom)
        root = tree.getroot()
        strip_xml(root)
    except Exception as e:
        unresolved.append(UnresolvedDependency("maven", "maven", pom.name, rel(repo, pom), f"XML parse failed: {e}"))
        return deps, unresolved, repository_reports

    raw_group = text_at(root, "groupId")
    raw_artifact = text_at(root, "artifactId")
    raw_version = normalize_maven_version(text_at(root, "version"))

    parent = root.find("parent")
    parent_group = text_at(parent, "groupId") if parent is not None else None
    parent_version = normalize_maven_version(text_at(parent, "version")) if parent is not None else None

    project_group = raw_group or parent_group
    project_artifact = raw_artifact
    project_version = raw_version or parent_version

    initial_properties = {}
    if project_group:
        initial_properties["project.groupId"] = project_group
        initial_properties["pom.groupId"] = project_group
    if project_artifact:
        initial_properties["project.artifactId"] = project_artifact
        initial_properties["pom.artifactId"] = project_artifact
    if project_version:
        initial_properties["project.version"] = project_version
        initial_properties["pom.version"] = project_version

    props = root.find("properties")
    if props is not None:
        for child in list(props):
            if child.text:
                initial_properties[child.tag] = child.text.strip()

    initial_pom_repos, initial_pom_repo_reports = detect_pom_repos(repo, pom, root, initial_properties)

    model = build_maven_model(
        root,
        project_group,
        project_artifact,
        project_version,
        list(dict.fromkeys([*(extra_repositories or []), *initial_pom_repos])),
        pom,
    )

    resolved_pom_repos, resolved_pom_repo_reports = detect_pom_repos(repo, pom, root, model.properties)

    repository_reports.extend(initial_pom_repo_reports)
    repository_reports.extend(model.repository_reports)
    repository_reports.extend(resolved_pom_repo_reports)

    properties = model.properties
    dependency_management = model.dependency_management

    for issue in model.issues:
        unresolved.append(UnresolvedDependency("maven", "maven", issue, rel(repo, pom), "Maven model resolution issue"))

    dependencies = root.find("dependencies")
    if dependencies is None:
        return deps, unresolved, repository_reports

    for dep_node in dependencies.findall("dependency"):
        group = resolve_maven_property(text_at(dep_node, "groupId"), properties)
        artifact = resolve_maven_property(text_at(dep_node, "artifactId"), properties)
        version = normalize_maven_version(resolve_maven_property(text_at(dep_node, "version"), properties))
        scope = resolve_maven_property(text_at(dep_node, "scope"), properties) or "compile"
        optional = resolve_maven_property(text_at(dep_node, "optional"), properties)

        if (group, artifact) in local_maven_projects:
            deps.append(Dependency(
                ecosystem="internal",
                package_manager="maven",
                name=f"{group}:{artifact}",
                version=version,
                scope=scope.strip(),
                source_file=rel(repo, pom),
                source_type="pom.xml",
                confidence="high",
                purl=None,
                notes="Maven reactor/module dependency, not added as external package.",
            ))
            continue

        notes = None if version else "No version resolved from direct declaration, parent, dependencyManagement, or imported BOM."
        if optional == "true":
            scope = f"{scope.strip()}:optional"
            notes = f"{notes} Maven optional dependency." if notes else "Maven optional dependency."

        if not group or not artifact:
            unresolved.append(UnresolvedDependency("maven","maven",  ET.tostring(dep_node, encoding="unicode"), rel(repo, pom), "Missing or unresolved groupId/artifactId",))
            continue

        if not version:
            version = dependency_management.get((group, artifact))

        version = normalize_maven_version(version)

        name = f"{group}:{artifact}"
        confidence = "high" if version else "medium"

        deps.append(Dependency(
            ecosystem="maven",
            package_manager="maven",
            name=name,
            version=version,
            scope=scope.strip(),
            source_file=rel(repo, pom),
            source_type="pom.xml",
            confidence=confidence,
            purl=make_purl("maven", name, version),
            notes=notes,
        ))

    return deps, unresolved, repository_reports

def normalize_maven_version(version: str | None) -> str | None:
    if not version:
        return None

    version = version.strip()
    exact_range = re.fullmatch(r"\[([^,\[\]]+)\]", version)
    if exact_range:
        return exact_range.group(1).strip()

    if re.search(r"\$\{[^}]+}", version):
        return None

    return version

def normalize_repo_url(url: str) -> str:
    return url.strip().rstrip("/")

def get_pom_text(a: MavenArtifact, repositories: list[str] | None = None) -> tuple[str | None, str | None]:
    repos = repositories or DEFAULT_MAVEN_REPOSITORIES

    for repo_url in repos:
        base = normalize_repo_url(repo_url)
        group_path = a.group.replace(".", "/")
        url = f"{base}/{group_path}/{a.artifact}/{a.version}/{a.artifact}-{a.version}.pom"
        if url in POM_CACHE:
            return POM_CACHE[url], repo_url

        try:
            with urllib.request.urlopen(url, timeout=20) as response:
                text = response.read().decode("utf-8", errors="replace")
                POM_CACHE[url] = text
                return text, repo_url
        except Exception:
            continue

    return None, None

def detect_pom_repos(repo: Path, pom: Path, root: ET.Element, properties: dict[str, str] | None = None) -> tuple[list[str], list[GradleRepoReport]]:
    properties = properties or {}
    repository_urls: list[str] = []
    reports: list[GradleRepoReport] = []

    for container_name, child_name in (("repositories", "repository"), ("pluginRepositories", "pluginRepository")):
        container = root.find(container_name)
        if container is None:
            continue

        for repo_node in container.findall(child_name):
            url = resolve_maven_property(text_at(repo_node, "url"), properties)
            repo_id = resolve_maven_property(text_at(repo_node, "id"), properties)

            if not url:
                continue

            url = normalize_repo_url(url)
            repository_urls.append(url)

            reports.append(GradleRepoReport(
                source_file=rel(repo, pom),
                repository_type=f"maven_{container_name}",
                value=url,
                notes=f"Maven repository detected from pom.xml, id={repo_id or 'NOASSERTION'}",
            ))

    return repository_urls, reports

def text_at(node: ET.Element, name: str) -> str | None:
    value = node.findtext(name)
    return value.strip() if value else None


def resolve_maven_property(value: str | None, properties: dict[str, str]) -> str | None:
    if not value:
        return None

    value = value.strip()

    def replace(match: re.Match[str]) -> str:
        key = match.group(1)
        return properties.get(key, match.group(0))

    previous = None
    for _ in range(10):
        if value == previous:
            break
        previous = value
        value = re.sub(r"\$\{([^}]+)}", replace, value)

    return value


def load_maven_model(a: MavenArtifact, repositories: list[str] | None = None) -> MavenSurfaceModel:
    repos = repositories or DEFAULT_MAVEN_REPOSITORIES
    artifact_key = f"{a.group}:{a.artifact}:{a.version}"
    key = f"{artifact_key}|" + "|".join(normalize_repo_url(r) for r in repos)
    if key in MAVEN_MODEL_CACHE:
        return MAVEN_MODEL_CACHE[key]
    text, resolved_repo = get_pom_text(a, repos)

    if text is None:
        model = MavenSurfaceModel({}, {}, [], [], [f"Could not fetch external Maven POM: {artifact_key}"], set())
        MAVEN_MODEL_CACHE[key] = model
        return model
    try:
        root = ET.fromstring(text)
        strip_xml(root)
    except Exception as e:
        model = MavenSurfaceModel({}, {}, [], [], [f"Could not parse external Maven POM {artifact_key}: {e}"], set())
        MAVEN_MODEL_CACHE[key] = model
        return model
    
    child_repos = list(dict.fromkeys([resolved_repo, *repos] if resolved_repo else repos))
    model = build_maven_model(root, a.group, a.artifact, a.version, child_repos, None)
    MAVEN_MODEL_CACHE[key] = model
    return model


def build_maven_model(root: ET.Element, project_group: str | None, project_artifact: str | None, project_version: str | None, repositories: list[str] | None = None, current_pom: Path | None = None) -> MavenSurfaceModel:
    issues: list[str] = []
    properties: dict[str, str] = {}
    dependency_management: dict[tuple[str, str], str] = {}
    repository_reports: list[GradleRepoReport] = []
    active_repositories = list(dict.fromkeys([
    *(repositories or []),
    *DEFAULT_MAVEN_REPOSITORIES,
    ]))
    project_coordinates: set[tuple[str, str]] = set()

    if project_group and project_artifact:
        project_coordinates.add((project_group, project_artifact))
    
    parent = root.find("parent")
    if parent is not None:
        parent_group = text_at(parent, "groupId")
        parent_artifact = text_at(parent, "artifactId")
        parent_version = normalize_maven_version(text_at(parent, "version"))

        if parent_group and parent_artifact and parent_version:
            local_parent = None
            if current_pom is not None:
                local_parent = get_parent_pom(
                    current_pom,
                    parent,
                    parent_group,
                    parent_artifact,
                    parent_version,
                )

            if local_parent is not None:
                try:
                    parent_tree = ET.parse(local_parent)
                    parent_root = parent_tree.getroot()
                    strip_xml(parent_root)

                    parent_model = build_maven_model(
                        parent_root,
                        parent_group,
                        parent_artifact,
                        parent_version,
                        active_repositories,
                        local_parent,
                    )
                except Exception as e:
                    parent_model = MavenSurfaceModel(
                        {}, {}, [], [], [f"Could not parse local parent POM {local_parent}: {e}"], set()
                    )
            else:
                parent_model = load_maven_model(
                    MavenArtifact(parent_group, parent_artifact, parent_version),
                    active_repositories,
                )

            properties.update(parent_model.properties)
            dependency_management.update(parent_model.dependency_management)
            issues.extend(parent_model.issues)
            project_coordinates.update(parent_model.project_coordinates)

            active_repositories.extend(parent_model.repositories)
            repository_reports.extend(parent_model.repository_reports)
            active_repositories = list(dict.fromkeys(active_repositories))

            if not project_group:
                project_group = parent_group
            if not project_version:
                project_version = parent_version

    if project_group:
        properties["project.groupId"] = project_group
        properties["pom.groupId"] = project_group
    if project_artifact:
        properties["project.artifactId"] = project_artifact
        properties["pom.artifactId"] = project_artifact
    if project_version:
        properties["project.version"] = project_version
        properties["pom.version"] = project_version

    props = root.find("properties")
    if props is not None:
        for child in list(props):
            if child.text:
                properties[child.tag] = child.text.strip()

    dm = root.find("dependencyManagement")
    if dm is not None:
        deps_node = dm.find("dependencies")
        if deps_node is not None:
            for dep in deps_node.findall("dependency"):
                group = resolve_maven_property(text_at(dep, "groupId"), properties)
                artifact = resolve_maven_property(text_at(dep, "artifactId"), properties)
                version = normalize_maven_version(resolve_maven_property(text_at(dep, "version"), properties))
                dep_type = resolve_maven_property(text_at(dep, "type"), properties)
                scope = resolve_maven_property(text_at(dep, "scope"), properties)

                if dep_type == "pom" and scope == "import":
                    if group and artifact and version:
                        bom_model = load_maven_model(
                            MavenArtifact(group, artifact, version),
                            active_repositories,
                        )

                        dependency_management.update(bom_model.dependency_management)
                        issues.extend(bom_model.issues)

                        active_repositories.extend(bom_model.repositories)
                        repository_reports.extend(bom_model.repository_reports)
                        active_repositories = list(dict.fromkeys(active_repositories))
                    else:
                        issues.append(f"Unresolved BOM import: {group}:{artifact}:{version}")
                    continue

                if group and artifact and version:
                    dependency_management[(group, artifact)] = version
                elif group and artifact:
                    issues.append(f"Unresolved dependencyManagement version for {group}:{artifact}")

    return MavenSurfaceModel(properties, dependency_management, active_repositories, repository_reports, issues, project_coordinates)


# -------------------------
# Java: Gradle / Gradle KTS
# -------------------------

GRADLE_CONFIG_SCOPE = {
    "implementation": "runtime",
    "api": "runtime",
    "compile": "runtime",
    "compileOnly": "compile-only",
    "runtimeOnly": "runtime",
    "testImplementation": "test",
    "testRuntimeOnly": "test-runtime",
    "testCompileOnly": "test-compile-only",
    "testCompile": "test",
    "annotationProcessor": "annotation-processor",
    "testAnnotationProcessor": "test-annotation-processor",
    "kapt": "annotation-processor",
    "kaptTest": "test-annotation-processor",
    "classpath": "build",
    "modImplementation": "runtime",
    "modApi": "runtime",
    "include": "runtime",
    "provided": "provided",
    "providedCompile": "provided",
    "providedRuntime": "provided-runtime",
}

def parse_gradle_toml(repo: Path, extra_catalog_files: list[Path] | None = None) -> tuple[dict[str, str], dict[str, str], dict[str, list[str]], list[UnresolvedDependency]]:
    library_aliases: dict[str, str] = {}
    plugin_aliases: dict[str, str] = {}
    bundles: dict[str, list[str]] = {}
    unresolved: list[UnresolvedDependency] = []

    paths = repo_files(repo, {"libs.versions.toml"})
    paths += extra_catalog_files or []

    seen_paths: set[Path] = set()

    for path in paths:
        path = path.resolve()
        if path in seen_paths or not path.exists():
            continue
        seen_paths.add(path)

        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception as e:
            unresolved.append(UnresolvedDependency("maven", "gradle", str(path), str(path), f"Version catalog parse failed: {e}"))
            continue

        versions = data.get("versions", {}) or {}
        libraries = data.get("libraries", {}) or {}
        plugins = data.get("plugins", {}) or {}
        raw_bundles = data.get("bundles", {}) or {}

        def resolve_version(value: Any) -> str | None:
            if isinstance(value, str):
                return value
            if isinstance(value, dict):
                if isinstance(value.get("ref"), str):
                    return versions.get(value["ref"])
                if isinstance(value.get("require"), str):
                    return value.get("require")
                if isinstance(value.get("strictly"), str):
                    return value.get("strictly")
                if isinstance(value.get("prefer"), str):
                    return value.get("prefer")
            return None

        for alias, value in libraries.items():
            if not isinstance(value, dict):
                continue

            module = value.get("module")
            group = value.get("group")
            name = value.get("name")
            version = resolve_version(value.get("version"))

            gav_name = None
            if isinstance(module, str) and ":" in module:
                parts = module.split(":")
                if len(parts) >= 2:
                    gav_name = f"{parts[0]}:{parts[1]}"
            elif isinstance(group, str) and isinstance(name, str):
                gav_name = f"{group}:{name}"

            if gav_name:
                library_aliases[alias.replace("-", ".")] = f"{gav_name}:{version or ''}"

        for alias, value in plugins.items():
            if not isinstance(value, dict):
                continue

            plugin_id = value.get("id")
            version = resolve_version(value.get("version"))

            if isinstance(plugin_id, str) and version:
                marker = f"{plugin_id}:{plugin_id}.gradle.plugin"
                plugin_aliases[alias.replace("-", ".")] = f"{marker}:{version}"

        for bundle_name, items in raw_bundles.items():
            if isinstance(items, list):
                bundles[bundle_name.replace("-", ".")] = [
                    str(i).replace("-", ".") for i in items
                ]

    return library_aliases, plugin_aliases, bundles, dedupe_unresolved(unresolved)

def get_gradle_vars(text: str) -> dict[str, str]:
    vars_found: dict[str, str] = {}

    patterns = [
        r"^\s*(?:def|val|var)\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*['\"]([^'\"]+)['\"]",
        r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*['\"]([^'\"]+)['\"]",
        r"^\s*ext\.([A-Za-z_][A-Za-z0-9_]*)\s*=\s*['\"]([^'\"]+)['\"]",
        r"^\s*set\(\s*['\"]([A-Za-z_][A-Za-z0-9_]*)['\"]\s*,\s*['\"]([^'\"]+)['\"]\s*\)",
    ]

    for pattern in patterns:
        for m in re.finditer(pattern, text, re.MULTILINE):
            vars_found[m.group(1)] = m.group(2)

    ext_block = re.search(r"ext\s*\{(?P<body>.*?)\}", text, re.DOTALL)
    if ext_block:
        body = ext_block.group("body")
        for m in re.finditer(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*['\"]([^'\"]+)['\"]", body, re.MULTILINE):
            vars_found[m.group(1)] = m.group(2)

    return vars_found

def get_gradle_properties(repo: Path) -> dict[str, str]:
    props: dict[str, str] = {}

    for path in repo_files(repo, {"gradle.properties"}):
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            raw = line.strip()
            if not raw or raw.startswith("#") or raw.startswith("!"):
                continue
            if "=" in raw:
                key, value = raw.split("=", 1)
            elif ":" in raw:
                key, value = raw.split(":", 1)
            else:
                continue
            props[key.strip()] = value.strip()

    return props


def parse_gradle_settings(repo: Path) -> tuple[list[Path], list[Path], list[UnresolvedDependency]]:
    include_builds: list[Path] = []
    catalog_files: list[Path] = []
    unresolved: list[UnresolvedDependency] = []

    for path in repo_files(repo, {"settings.gradle", "settings.gradle.kts"}):
        text = path.read_text(encoding="utf-8", errors="ignore")

        for m in re.finditer(r"includeBuild\s*\(\s*['\"]([^'\"]+)['\"]\s*\)", text):
            include_builds.append((path.parent / m.group(1)).resolve())

        for m in re.finditer(r"from\s*\(\s*files\s*\(\s*['\"]([^'\"]+\.toml)['\"]\s*\)\s*\)", text):
            catalog_files.append((path.parent / m.group(1)).resolve())

        for m in re.finditer(r"from\s*\(\s*['\"]([^'\"]+\.toml)['\"]\s*\)", text):
            catalog_files.append((path.parent / m.group(1)).resolve())

    return include_builds, catalog_files, unresolved

def resolve_gradle_vars(value: str, variables: dict[str, str]) -> tuple[str, bool]:
    unresolved = False

    def replace_braced(match: re.Match[str]) -> str:
        nonlocal unresolved
        key = match.group(1)
        if key in variables:
            return variables[key]
        unresolved = True
        return match.group(0)

    value = re.sub(r"\$\{([A-Za-z_][A-Za-z0-9_]*)}", replace_braced, value)

    def replace_plain(match: re.Match[str]) -> str:
        nonlocal unresolved
        key = match.group(1)
        if key in variables:
            return variables[key]
        unresolved = True
        return match.group(0)

    value = re.sub(r"\$([A-Za-z_][A-Za-z0-9_]*)", replace_plain, value)

    return value, not unresolved

def is_gradle_rich(version: str | None) -> bool:
    if not version:
        return False

    v = version.strip()
    return any(x in v for x in ["strictly", "prefer", "require"])

def is_gradle_dynamic(version: str | None) -> bool:
    if not version:
        return False

    v = version.strip().lower()
    return (
        v == "+"
        or v.endswith(".+")
        or v in {"latest.release", "latest.integration"}
    )

def split_gradle_coord_ver(version: str) -> tuple[str, str | None]:
    parts = version.split(":", 1)

    if len(parts) == 2:
        return parts[0], parts[1]

    return version, None


def make_maven_purl(name: str, version: str | None, classifier: str | None) -> str | None:
    if not version or ":" not in name:
        return None

    group, artifact = name.split(":", 1)
    purl = f"pkg:maven/{group}/{artifact}@{version}"

    if classifier:
        purl += f"?classifier={classifier}"

    return purl

def gradle_report_repos(reports: list[GradleRepoReport]) -> list[str]:
    urls: list[str] = []

    for report in reports:
        if report.repository_type == "mavenCentral":
            urls.append(MAVEN_CENTRAL)
        elif report.repository_type == "google":
            urls.append(GOOGLE_MAVEN)
        elif report.repository_type == "custom_maven_repository" and report.value:
            urls.append(report.value)

    return list(dict.fromkeys(normalize_repo_url(u) for u in urls))

def gradle_repos(repo: Path, path: Path, text: str) -> list[GradleRepoReport]:
    reports: list[GradleRepoReport] = []

    simple_patterns = [
        ("mavenCentral", r"\bmavenCentral\s*\("),
        ("google", r"\bgoogle\s*\("),
        ("jcenter", r"\bjcenter\s*\("),
        ("gradlePluginPortal", r"\bgradlePluginPortal\s*\("),
        ("flatDir", r"\bflatDir\s*\{"),
    ]

    for repo_type, pattern in simple_patterns:
        for _ in re.finditer(pattern, text, re.DOTALL):
            reports.append(GradleRepoReport(
                source_file=rel(repo, path),
                repository_type=repo_type,
                value=repo_type,
                notes="Gradle repository detected.",
            ))

    custom_maven_patterns = [
        r"\bmaven\s*\{[^}]*url\s*[= ]\s*['\"]([^'\"]+)['\"]",
        r"\bmaven\s*\{[^}]*url\s*[= ]\s*uri\(\s*['\"]([^'\"]+)['\"]\s*\)",
        r"\bmaven\s*\{[^}]*setUrl\(\s*['\"]([^'\"]+)['\"]\s*\)",
        r"\bmaven\s*\{[^}]*setUrl\(\s*uri\(\s*['\"]([^'\"]+)['\"]\s*\)\s*\)",
    ]

    for pattern in custom_maven_patterns:
        for m in re.finditer(pattern, text, re.DOTALL):
            url = normalize_repo_url(m.group(1))
            reports.append(GradleRepoReport(
                source_file=rel(repo, path),
                repository_type="custom_maven_repository",
                value=url,
                notes="Custom Gradle Maven repository detected.",
            ))

    return reports

def get_gradle_plugins(repo: Path, path: Path, text: str) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    plugin_pattern = re.compile(r"id\s*\(?\s*['\"]([^'\"]+)['\"]\s*\)?\s*version\s*['\"]([^'\"]+)['\"]", re.MULTILINE)

    for m in plugin_pattern.finditer(text):
        plugin_id, version = m.groups()

        if is_gradle_dynamic(version):
            unresolved.append(UnresolvedDependency(
                "maven",
                "gradle-plugin",
                f"id '{plugin_id}' version '{version}'",
                rel(repo, path),
                "Dynamic Gradle plugin version cannot be converted into a stable SBOM package version.",
            ))
            continue

        marker_name = f"{plugin_id}:{plugin_id}.gradle.plugin"

        deps.append(Dependency(
            ecosystem="maven",
            package_manager="gradle-plugin",
            name=marker_name,
            version=version,
            scope="build",
            source_file=rel(repo, path),
            source_type=path.name,
            confidence="medium",
            purl=make_purl("maven", marker_name, version),
            notes=f"Gradle plugin declaration for plugin id: {plugin_id}",
        ))

    return deps, unresolved

def get_gradle_platforms(repo: Path, path: Path, text: str, gradle_vars: dict[str, str]) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    pattern = re.compile(
        r"^\s*(\w+)\s*\(?\s*(enforcedPlatform|platform)\(\s*['\"]([^:'\"]+):([^:'\"]+):([^'\"]+)['\"]\s*\)\s*\)?",
        re.MULTILINE,
    )

    for m in pattern.finditer(text):
        config, platform_kind, group, artifact, version = m.groups()

        if config not in GRADLE_CONFIG_SCOPE:
            continue

        version, resolved_ok = resolve_gradle_vars(version, gradle_vars)
        name = f"{group}:{artifact}"

        if is_gradle_rich(version):
            unresolved.append(UnresolvedDependency(
                "maven", "gradle", f"{group}:{artifact}:{version}", rel(repo, path),
                "Gradle rich version declaration requires evaluation.",
            ))
            continue

        if is_gradle_dynamic(version):
            unresolved.append(UnresolvedDependency(
                "maven", "gradle", f"{group}:{artifact}:{version}", rel(repo, path),
                "Dynamic Gradle version cannot be converted into a stable SBOM package version.",
            ))
            continue

        deps.append(Dependency(
            ecosystem="maven",
            package_manager="gradle",
            name=name,
            version=version,
            scope=f"{GRADLE_CONFIG_SCOPE.get(config, config)}:platform",
            source_file=rel(repo, path),
            source_type=path.name,
            confidence="high" if resolved_ok else "medium",
            purl=make_purl("maven", name, version),
            notes=f"Gradle {platform_kind} dependency declared in configuration: {config}",
        ))

    return deps, unresolved

def get_gradle_constraints(repo: Path, path: Path, text: str, gradle_vars: dict[str, str]) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    constraints_block = re.search(r"constraints\s*\{(?P<body>.*?)\n\s*\}", text, re.DOTALL)
    if not constraints_block:
        return deps, unresolved

    body = constraints_block.group("body")

    pattern = re.compile(
        r"^\s*(\w+)\s*\(?\s*['\"]([^:'\"]+):([^:'\"]+):([^'\"]+)['\"]\s*\)?",
        re.MULTILINE,
    )

    for m in pattern.finditer(body):
        config, group, artifact, version = m.groups()

        if config not in GRADLE_CONFIG_SCOPE:
            continue

        version, resolved_ok = resolve_gradle_vars(version, gradle_vars)
        name = f"{group}:{artifact}"

        if is_gradle_rich(version):
            unresolved.append(UnresolvedDependency(
                "maven", "gradle", f"{group}:{artifact}:{version}", rel(repo, path),
                "Gradle rich version declaration requires evaluation.",
            ))
            continue

        if is_gradle_dynamic(version):
            unresolved.append(UnresolvedDependency(
                "maven", "gradle", f"{group}:{artifact}:{version}", rel(repo, path),
                "Dynamic Gradle version cannot be converted into a stable SBOM package version.",
            ))
            continue

        deps.append(Dependency(
            ecosystem="maven",
            package_manager="gradle",
            name=name,
            version=version,
            scope=f"{GRADLE_CONFIG_SCOPE.get(config, config)}:constraint",
            source_file=rel(repo, path),
            source_type=path.name,
            confidence="high" if resolved_ok else "medium",
            purl=make_purl("maven", name, version),
            notes=f"Gradle dependency constraint declared in configuration: {config}",
        ))

    return deps, unresolved

def parse_gradle_file(repo: Path, path: Path, aliases: dict[str, str], plugin_aliases: dict[str, str],bundles: dict[str, list[str]]) -> tuple[list[Dependency], list[UnresolvedDependency], list[GradleRepoReport]]:
    text = path.read_text(encoding="utf-8", errors="ignore")
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []
    repository_reports: list[GradleRepoReport] = []
    gradle_vars = get_gradle_properties(repo)
    gradle_vars.update(get_gradle_vars(text))
    repository_reports.extend(gradle_repos(repo, path, text))
    for m in re.finditer(r"""files\s*\(\s*["']([^"']+\.jar)["']\s*\)""", text):
        jar_path = m.group(1)
        deps.append(Dependency(
            ecosystem="local",
            package_manager="gradle",
            name=Path(jar_path).stem,
            version=None,
            scope="runtime",
            source_file=rel(repo, path),
            source_type=path.name,
            confidence="medium",
            purl=None,
            notes=f"Gradle local file dependency detected: {jar_path}",
        ))

    for m in re.finditer(r"""fileTree\s*\(\s*dir\s*:\s*["']([^"']+)["']""", text):
        deps.append(Dependency(
            ecosystem="local",
            package_manager="gradle",
            name=f"fileTree:{m.group(1)}",
            version=None,
            scope="runtime",
            source_file=rel(repo, path),
            source_type=path.name,
            confidence="medium",
            purl=None,
            notes="Gradle fileTree dependency detected, individual JARs may be found by local JAR scan.",
        ))
    plugin_deps, plugin_unresolved = get_gradle_plugins(repo, path, text)
    deps.extend(plugin_deps)
    unresolved.extend(plugin_unresolved)
    platform_deps, platform_unresolved = get_gradle_platforms(repo, path, text, gradle_vars)
    deps.extend(platform_deps)
    unresolved.extend(platform_unresolved)
    constraint_deps, constraint_unresolved = get_gradle_constraints(repo, path, text, gradle_vars)
    deps.extend(constraint_deps)
    unresolved.extend(constraint_unresolved)
    plugin_alias_pattern = re.compile(
        r"alias\s*\(\s*libs\.plugins\.([A-Za-z0-9_.-]+)\s*\)"
    )

    for m in plugin_alias_pattern.finditer(text):
        alias = m.group(1).replace("-", ".")
        gav = plugin_aliases.get(alias)

        if not gav:
            unresolved.append(UnresolvedDependency(
                "maven",
                "gradle-plugin",
                f"libs.plugins.{alias}",
                rel(repo, path),
                "Unresolved Gradle plugin alias.",
            ))
            continue

        parts = gav.split(":")
        if len(parts) >= 3 and parts[2]:
            name = f"{parts[0]}:{parts[1]}"
            version = parts[2]

            deps.append(Dependency(
                ecosystem="maven",
                package_manager="gradle-plugin",
                name=name,
                version=version,
                scope="build",
                source_file=rel(repo, path),
                source_type=path.name,
                confidence="high",
                purl=make_purl("maven", name, version),
                notes=f"Resolved from Gradle plugin alias libs.plugins.{alias}",
            ))

    # implementation "g:a:v" or implementation("g:a:v")
    patterns = [
        re.compile(r"^\s*(\w+)\s+['\"]([^:'\"]+):([^:'\"]+):([^'\"]+)['\"]", re.MULTILINE),
        re.compile(r"^\s*(\w+)\s*\(\s*['\"]([^:'\"]+):([^:'\"]+):([^'\"]+)['\"]\s*\)", re.MULTILINE),
        re.compile(r"^\s*(\w+)\s+group:\s*['\"]([^'\"]+)['\"]\s*,\s*name:\s*['\"]([^'\"]+)['\"]\s*,\s*version:\s*['\"]([^'\"]+)['\"]", re.MULTILINE),
        re.compile(
            r"^\s*(\w+)\s*\(\s*group\s*=\s*['\"]([^'\"]+)['\"]\s*,\s*name\s*=\s*['\"]([^'\"]+)['\"]\s*,\s*version\s*=\s*['\"]([^'\"]+)['\"]",
            re.MULTILINE,
        ),
    ]

    for pattern in patterns:
        for m in pattern.finditer(text):
            config, group, artifact, version = m.groups()
            if config not in GRADLE_CONFIG_SCOPE:
                continue

            version, resolved_ok = resolve_gradle_vars(version, gradle_vars)
            version, classifier = split_gradle_coord_ver(version)

            name = f"{group}:{artifact}"
            notes = f"Declared in Gradle configuration: {config}"
            if classifier:
                notes += f", classifier={classifier}"

            if is_gradle_rich(version):
                unresolved.append(UnresolvedDependency(
                    "maven",
                    "gradle",
                    f"{config} {group}:{artifact}:{version}",
                    rel(repo, path),
                    "Gradle rich version declaration requires evaluation.",
                ))
                continue

            if is_gradle_dynamic(version):
                unresolved.append(UnresolvedDependency(
                    "maven",
                    "gradle",
                    f"{config} {group}:{artifact}:{version}",
                    rel(repo, path),
                    "Dynamic Gradle version cannot be converted into a stable SBOM package version.",
                ))
                continue

            deps.append(Dependency(
                ecosystem="maven",
                package_manager="gradle",
                name=name,
                version=version,
                scope=GRADLE_CONFIG_SCOPE.get(config, config),
                source_file=rel(repo, path),
                source_type=path.name,
                confidence="high" if resolved_ok else "medium",
                purl=make_maven_purl(name, version, classifier),
                notes=notes,
            ))

    project_dep_pattern = re.compile(
        r"^\s*(\w+)\s*\(?\s*project\(\s*['\"]:([^'\"]+)['\"]\s*\)\s*\)?",
        re.MULTILINE,
    )

    for m in project_dep_pattern.finditer(text):
        config, module_name = m.groups()

        if config not in GRADLE_CONFIG_SCOPE:
            continue

        deps.append(Dependency(
            ecosystem="internal",
            package_manager="gradle",
            name=f":{module_name}",
            version=None,
            scope=GRADLE_CONFIG_SCOPE.get(config, config),
            source_file=rel(repo, path),
            source_type=path.name,
            confidence="high",
            purl=None,
            notes=f"Internal Gradle project/module dependency declared in configuration: {config}",
        ))

    alias_pattern = re.compile(r"^\s*(\w+)\s*\(?\s*libs\.([A-Za-z0-9_.-]+)\s*\)?", re.MULTILINE)
    for m in alias_pattern.finditer(text):
        config, alias = m.groups()
        if config not in GRADLE_CONFIG_SCOPE:
            continue

        normalized_alias = alias.replace("-", ".")
        gav = aliases.get(normalized_alias)

        if gav:
            parts = gav.split(":")
            if len(parts) >= 3 and parts[2]:
                name = f"{parts[0]}:{parts[1]}"
                version = parts[2]
                deps.append(Dependency(
                    ecosystem="maven",
                    package_manager="gradle",
                    name=name,
                    version=version,
                    scope=GRADLE_CONFIG_SCOPE.get(config, config),
                    source_file=rel(repo, path),
                    source_type=path.name,
                    confidence="high",
                    purl=make_purl("maven", name, version),
                    notes=f"Resolved from libs.versions.toml alias {alias}",
                ))
            else:
                unresolved.append(UnresolvedDependency(
                    "maven", "gradle", f"libs.{alias}", rel(repo, path),
                    "Version catalog alias resolved to module but missing version"
                ))
        else:
            unresolved.append(UnresolvedDependency(
                "maven", "gradle", f"libs.{alias}", rel(repo, path),
                "Unresolved Gradle version catalog alias"
            ))

    bundle_pattern = re.compile(
        r"^\s*(\w+)\s*\(?\s*libs\.bundles\.([A-Za-z0-9_.-]+)\s*\)?",
        re.MULTILINE,
    )

    for m in bundle_pattern.finditer(text):
        config, bundle_name = m.groups()

        if config not in GRADLE_CONFIG_SCOPE:
            continue

        normalized_bundle = bundle_name.replace("-", ".")
        bundle_aliases = bundles.get(normalized_bundle)

        if not bundle_aliases:
            unresolved.append(UnresolvedDependency(
                "maven",
                "gradle",
                f"libs.bundles.{bundle_name}",
                rel(repo, path),
                "Unresolved Gradle version catalog bundle.",
            ))
            continue

        for alias in bundle_aliases:
            gav = aliases.get(alias)

            if not gav:
                unresolved.append(UnresolvedDependency(
                    "maven",
                    "gradle",
                    f"libs.{alias}",
                    rel(repo, path),
                    f"Bundle libs.bundles.{bundle_name} references unresolved alias.",
                ))
                continue

            parts = gav.split(":")
            if len(parts) >= 3 and parts[2]:
                name = f"{parts[0]}:{parts[1]}"
                version = parts[2]

                deps.append(Dependency(
                    ecosystem="maven",
                    package_manager="gradle",
                    name=name,
                    version=version,
                    scope=GRADLE_CONFIG_SCOPE.get(config, config),
                    source_file=rel(repo, path),
                    source_type=path.name,
                    confidence="high",
                    purl=make_purl("maven", name, version),
                    notes=f"Resolved from Gradle bundle libs.bundles.{bundle_name}",
                ))

    sus_lines = []
    dependency_line_pattern = re.compile(
        r"^\s*(" + "|".join(re.escape(cfg) for cfg in GRADLE_CONFIG_SCOPE) + r")\s*(?:\(|\s)"
    )

    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("//"):
            continue
        if not dependency_line_pattern.match(stripped):
            continue
        if "project(" in stripped:
            continue
        if ("$" in stripped or "libs." in stripped) and not re.search(
            r"['\"][^:'\"]+:[^:'\"]+:[^'\"]+['\"]",
            stripped,
        ):
            sus_lines.append(stripped)

    for line in sus_lines:
        unresolved.append(UnresolvedDependency(
            "maven", "gradle", line, rel(repo, path),
            "Dependency declaration requires Gradle evaluation or unsupported expression handling"
        ))

    return deps, unresolved, repository_reports

def scan_jars(repo: Path) -> list[Dependency]:
    deps: list[Dependency] = []

    for path in repo.rglob("*.jar"):
        if not path.is_file() or should_skip(path.relative_to(repo)):
            continue

        deps.append(Dependency(
            ecosystem="local",
            package_manager="java-jar",
            name=path.stem,
            version=None,
            scope="runtime",
            source_file=rel(repo, path),
            source_type="jar",
            confidence="medium",
            purl=None,
            notes="Local JAR artifact detected but version/transitives cannot be safely resolved without more metadata.",
        ))

    return deps


def parse_ant_xml(repo: Path, path: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except Exception as e:
        unresolved.append(UnresolvedDependency("java", "ant", path.name, rel(repo, path), f"Read failed: {e}"))
        return deps, unresolved

    for m in re.finditer(r"""(?:location|file|name)\s*=\s*["']([^"']+\.jar)["']""", text):
        jar_path = m.group(1)
        deps.append(Dependency(
            ecosystem="local",
            package_manager="ant",
            name=Path(jar_path).stem,
            version=None,
            scope="runtime",
            source_file=rel(repo, path),
            source_type="build.xml",
            confidence="medium",
            purl=None,
            notes=f"Ant build file local JAR reference detected: {jar_path}. Ant dependency resolution is not currently supported."
        ))

    return deps, unresolved


def parse_ivy_xml(repo: Path, path: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    try:
        tree = ET.parse(path)
        root = tree.getroot()
        strip_xml(root)
    except Exception as e:
        unresolved.append(UnresolvedDependency("maven", "ivy", path.name, rel(repo, path), f"XML parse failed: {e}"))
        return deps, unresolved

    for dep_node in root.findall(".//dependency"):
        org = dep_node.get("org")
        name = dep_node.get("name")
        rev = dep_node.get("rev")
        conf = dep_node.get("conf") or "runtime"

        if rev and ("+" in rev or "[" in rev):
            unresolved.append(
                UnresolvedDependency(
                    "maven",
                    "ivy",
                    f"{org}:{name}:{rev}",
                    rel(repo, path),
                    "Ivy dynamic version detected.",
                )
            )

        if not org or not name:
            unresolved.append(UnresolvedDependency("maven", "ivy", ET.tostring(dep_node, encoding="unicode"), rel(repo, path), "Missing Ivy org/name"))
            continue

        dep_name = f"{org}:{name}"
        deps.append(Dependency(
            ecosystem="maven",
            package_manager="ivy",
            name=dep_name,
            version=normalize_maven_version(rev),
            scope=conf,
            source_file=rel(repo, path),
            source_type="ivy.xml",
            confidence="high" if rev else "medium",
            purl=make_purl("maven", dep_name, normalize_maven_version(rev)),
            notes=None if rev else "Ivy dependency has no resolved revision.",
        ))

    return deps, unresolved

def scan_java(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency], list[GradleRepoReport]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []
    repository_reports: list[GradleRepoReport] = []

    deps.extend(scan_jars(repo))
    pre_gradle_repository_reports: list[GradleRepoReport] = []
    for gradle in repo_files(repo, {"build.gradle", "build.gradle.kts"}):
        text = gradle.read_text(encoding="utf-8", errors="ignore")
        pre_gradle_repository_reports.extend(gradle_repos(repo, gradle, text))

    extra_maven_repositories = gradle_report_repos(
        pre_gradle_repository_reports
    )

    repository_reports.extend(pre_gradle_repository_reports)
    local_maven_projects = get_maven_coordinates(repo)
    for pom in repo_files(repo, {"pom.xml"}):
        d, u, r = parse_pom(repo, pom, local_maven_projects, extra_maven_repositories)
        deps.extend(d)
        unresolved.extend(u)
        repository_reports.extend(r)

    for ant in repo_files(repo, {"build.xml"}):
        d, u = parse_ant_xml(repo, ant)
        deps.extend(d)
        unresolved.extend(u)

    for ivy in repo_files(repo, {"ivy.xml"}):
        d, u = parse_ivy_xml(repo, ivy)
        deps.extend(d)
        unresolved.extend(u)

    include_builds, catalog_files, settings_unresolved = parse_gradle_settings(repo)
    aliases, plugin_aliases, bundles, toml_unresolved = parse_gradle_toml(
        repo,
        catalog_files,
    )

    unresolved.extend(settings_unresolved)
    unresolved.extend(toml_unresolved)

    for gradle in repo_files(repo, {"build.gradle", "build.gradle.kts"}):
        d, u, r = parse_gradle_file(repo, gradle, aliases, plugin_aliases, bundles)
        deps.extend(d)
        unresolved.extend(u)
        repository_reports.extend(r)

    return deps, unresolved, repository_reports


# -------------------------
# JavaScript / npm
# -------------------------

def is_github_ver(version: str | None) -> bool:
    if not version:
        return False

    v = version.strip()
    return bool(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:#[A-Za-z0-9_.\-\/]+)?", v))


def is_github_dep_ver(version: str | None) -> bool:
    if not version:
        return False

    v = version.strip().lower()
    return (
        is_github_ver(version)
        or v.startswith("github:")
        or v.startswith("git+https://github.com/")
        or v.startswith("https://github.com/")
    )

def scan_javascript(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    lock_versions = npm_load_lfver(repo)

    scope_map = {
        "dependencies": "runtime",
        "devDependencies": "development",
        "peerDependencies": "peer",
        "optionalDependencies": "optional",
        "bundledDependencies": "bundled",
        "bundleDependencies": "bundled",
    }

    for path in repo_files(repo, {"package.json"}):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception as e:
            unresolved.append(UnresolvedDependency("npm", "npm", "package.json", rel(repo, path), f"JSON parse failed: {e}"))
            continue

        for section, scope in scope_map.items():
            entries = data.get(section)

            if isinstance(entries, dict):
                for name, raw_version in entries.items():
                    declared_version = str(raw_version) if raw_version is not None else None
                    resolved_version, resolution_note = resolve_npm_declared_version(
                        name,
                        declared_version,
                        lock_versions,
                    )

                    purl = (
                        make_purl("npm", name, resolved_version)
                        if is_npm_ver(resolved_version)
                        else None
                    )

                    notes = None
                    if resolution_note:
                        notes = resolution_note
                    if declared_version and resolved_version != declared_version:
                        notes = f"{notes or ''} Original declaration: {declared_version}".strip()

                    deps.append(Dependency(
                        ecosystem="npm",
                        package_manager="npm",
                        name=name,
                        version=resolved_version,
                        scope=scope,
                        source_file=rel(repo, path),
                        source_type="package.json",
                        confidence="high" if purl else "medium",
                        purl=purl,
                        notes=notes,
                    ))

            elif isinstance(entries, list):
                for name in entries:
                    deps.append(Dependency(
                        ecosystem="npm",
                        package_manager="npm",
                        name=str(name),
                        version=None,
                        scope=scope,
                        source_file=rel(repo, path),
                        source_type="package.json",
                        confidence="medium",
                        purl=None,
                        notes=f"{section} listed as array without versions",
                    ))

    return deps, unresolved


# -------------------------
# Python
# -------------------------

PYTHON_DEP_RE = re.compile(
    r"^\s*"
    r"(?P<name>[A-Za-z0-9_.-]+)"
    r"(?:\[(?P<extras>[A-Za-z0-9_,.\-\s]+)\])?"
    r"\s*"
    r"(?P<op>==|>=|<=|~=|>|<)?"
    r"\s*"
    r"(?P<version>[^;\s#]+)?"
)
PYTHON_SETUP_LIST_RE = re.compile(r"(?:install_requires|setup_requires|tests_require)\s*=\s*\[(?P<body>.*?)\]", re.DOTALL)
PYTHON_SETUP_EXTRAS_RE = re.compile(r"extras_require\s*=\s*\{(?P<body>.*?)\}", re.DOTALL)
PYTHON_STRING_RE = re.compile(r"""['"]([^'"]+)['"]""")

def get_python_requirement(raw: str) -> tuple[str, str | None, str | None, str | None]:
    raw = raw.strip()

    if not raw or raw.startswith("#"):
        raise ValueError("Empty/comment Python dependency string")

    raw = raw.split("#", 1)[0].strip()

    raw = raw.split(";", 1)[0].strip()

    if " @ " in raw or raw.endswith(" @") or raw == "@":
        raise ValueError("Python direct-reference dependency requires special handling")

    m = PYTHON_DEP_RE.match(raw)
    if not m:
        raise ValueError("Unsupported Python dependency string")

    name = m.group("name")
    extras = m.group("extras")
    op = m.group("op")
    version = m.group("version")

    if not name:
        raise ValueError("Missing Python package name")

    if version == "@":
        raise ValueError("Malformed Python direct-reference dependency")

    normalized_extras = ",".join(
        e.strip() for e in extras.split(",") if e.strip()
    ) if extras else None

    normalized_version = f"{op}{version}" if op and version else None

    return name, normalized_version, normalized_extras, raw

def get_root_python(repo: Path) -> set[str]:
    names: set[str] = set()

    root_pyproject = repo / "pyproject.toml"
    if root_pyproject.exists():
        try:
            data = tomllib.loads(root_pyproject.read_text(encoding="utf-8"))
            project = data.get("project") or {}
            name = project.get("name")
            if isinstance(name, str):
                names.add(normalize_pypi_name(name))
        except Exception:
            pass

    return names


def is_self_python_dep(repo: Path, name: str) -> bool:
    return normalize_pypi_name(name) in get_root_python(repo)

def parse_pip_editable(raw: str) -> tuple[str, str | None] | None:
    if raw.startswith("-e "):
        target = raw[3:].strip()
    elif raw.startswith("--editable "):
        target = raw[len("--editable "):].strip()
    else:
        return None

    extras_match = re.search(r"\[([^\]]+)\]", target)
    extras = extras_match.group(1) if extras_match else None
    return target, extras

def poetry_dep_str(name: str, value: Any) -> str:
    if isinstance(value, str):
        return f"{name}{value}"

    if isinstance(value, dict):
        version = value.get("version")
        if isinstance(version, str):
            return f"{name}{version}"

    return name


def get_pypi_lockvers(repo: Path) -> dict[str, str]:
    versions: dict[str, str] = {}

    lock_paths = repo_files(repo, {"poetry.lock", "uv.lock", "PDM.lock", "pdm.lock"})
    lock_paths += [
        p for p in repo.rglob("pylock*.toml")
        if p.is_file() and not should_skip(p.relative_to(repo))
    ]

    for path in lock_paths:
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue

        packages = data.get("package") or data.get("packages") or []
        if isinstance(packages, list):
            for pkg in packages:
                if not isinstance(pkg, dict):
                    continue
                name = pkg.get("name")
                version = pkg.get("version")
                if isinstance(name, str) and isinstance(version, str):
                    versions[normalize_pypi_name(name)] = version

    for path in repo_files(repo, {"Pipfile.lock"}):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue

        for section in ("default", "develop"):
            entries = data.get(section, {}) or {}
            if isinstance(entries, dict):
                for name, pkg in entries.items():
                    if not isinstance(pkg, dict):
                        continue
                    version = pkg.get("version")
                    if isinstance(version, str) and version.startswith("=="):
                        versions[normalize_pypi_name(name)] = version[2:]

    return versions


def parse_pydep(repo: Path, path: Path, item: str, scope: str, deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_versions: dict[str, str] | None = None, package_manager: str = "python") -> None:
    try:
        name, version, extras, original = get_python_requirement(item)
    except ValueError as e:
        unresolved.append(UnresolvedDependency("pypi", package_manager, item, rel(repo, path), str(e)))
        return

    if is_self_python_dep(repo, name):
        deps.append(Dependency(
            ecosystem="internal",
            package_manager=package_manager,
            name=name,
            version=None,
            scope=scope,
            source_file=rel(repo, path),
            source_type=path.name,
            confidence="high",
            purl=None,
            notes="Self-dependency on the root Python project, not added as external PyPI package.",
        ))
        return

    resolved_version, resolution_note = resolve_pypi_ver(name, version, lock_versions)
    if resolved_version and not is_pypi_ver(resolved_version):
        unresolved.append(UnresolvedDependency(
            "pypi",
            package_manager,
            item,
            rel(repo, path),
            resolution_note or "PyPI dependency could not be resolved to an exact stable version.",
        ))

    notes = f"extras={extras}" if extras else None
    if resolution_note:
        notes = f"{notes}, {resolution_note}" if notes else resolution_note
    if version and resolved_version != version:
        notes = f"{notes or ''} Original declaration: {version}".strip()

    deps.append(Dependency(
        ecosystem="pypi",
        package_manager=package_manager,
        name=name,
        version=resolved_version,
        scope=scope,
        source_file=rel(repo, path),
        source_type=path.name,
        confidence="high" if is_pypi_ver(resolved_version) else "medium",
        purl=make_purl("pypi", name, resolved_version) if is_pypi_ver(resolved_version) else None,
        notes=notes,
    ))


def scan_requirements_file(repo: Path, path: Path, deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_versions: dict[str, str], seen_files: set[Path] | None = None, scope: str = "runtime") -> None:
    seen_files = seen_files or set()
    path = path.resolve()

    if path in seen_files:
        return
    seen_files.add(path)

    if not path.exists():
        unresolved.append(UnresolvedDependency("pypi", "pip", str(path), str(path), "Referenced requirements file does not exist."))
        return

    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        raw = line.strip()

        editable = parse_pip_editable(raw)
        if editable:
            target, extras = editable
            deps.append(Dependency(
                ecosystem="internal",
                package_manager="pip",
                name=target,
                version=None,
                scope=scope,
                source_file=rel(repo, path),
                source_type=path.name,
                confidence="high",
                purl=None,
                notes=(
                    "Editable/local project install detected. "
                    "This is not added as an external PyPI package."
                    + (f" Extras requested: {extras}." if extras else "")
                ),
            ))
            continue

        if not raw or raw.startswith("#"):
            continue

        if raw.startswith("-r ") or raw.startswith("--requirement "):
            included = raw.split(maxsplit=1)[1].strip()
            scan_requirements_file(repo, (path.parent / included), deps, unresolved, lock_versions, seen_files, scope)
            continue
        if raw.startswith("-c ") or raw.startswith("--constraint "):
            included = raw.split(maxsplit=1)[1].strip()
            scan_requirements_file(repo, (path.parent / included), deps, unresolved, lock_versions, seen_files, "constraint")
            continue
        if raw.startswith("-"):
            unresolved.append(UnresolvedDependency("pypi", "pip", raw, rel(repo, path), "Unsupported pip option line."))
            continue

        parse_pydep(repo, path, raw, scope, deps, unresolved, lock_versions, "pip")


def scan_setup_cfg(repo: Path, path: Path, deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_versions: dict[str, str]) -> None:
    parser = configparser.ConfigParser()
    try:
        parser.read(path, encoding="utf-8")
    except Exception as e:
        unresolved.append(UnresolvedDependency("pypi", "setuptools", "setup.cfg", rel(repo, path), f"INI parse failed: {e}"))
        return

    if parser.has_option("options", "install_requires"):
        for item in parser.get("options", "install_requires").splitlines():
            item = item.strip()
            if item:
                parse_pydep(repo, path, item, "runtime", deps, unresolved, lock_versions, "setuptools")

    if parser.has_section("options.extras_require"):
        for extra, value in parser.items("options.extras_require"):
            for item in value.splitlines():
                item = item.strip()
                if item:
                    parse_pydep(repo, path, item, f"optional:{extra}", deps, unresolved, lock_versions, "setuptools")


def scan_setup_py(repo: Path, path: Path, deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_versions: dict[str, str]) -> None:
    text = path.read_text(encoding="utf-8", errors="ignore")

    for m in PYTHON_SETUP_LIST_RE.finditer(text):
        body = m.group("body")
        scope = "runtime"
        raw_header = m.group(0).split("=", 1)[0].strip()
        if raw_header == "tests_require":
            scope = "test"
        elif raw_header == "setup_requires":
            scope = "build"

        for item in PYTHON_STRING_RE.findall(body):
            parse_pydep(repo, path, item, scope, deps, unresolved, lock_versions, "setuptools")

    extras_match = PYTHON_SETUP_EXTRAS_RE.search(text)
    if extras_match:
        for item in PYTHON_STRING_RE.findall(extras_match.group("body")):
            parse_pydep(repo, path, item, "optional", deps, unresolved, lock_versions, "setuptools")


def scan_pipfile(repo: Path, path: Path, deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_versions: dict[str, str]) -> None:
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        unresolved.append(UnresolvedDependency("pypi", "pipenv", "Pipfile", rel(repo, path), f"TOML parse failed: {e}"))
        return

    for section, scope in (("packages", "runtime"), ("dev-packages", "development")):
        entries = data.get(section, {}) or {}
        if isinstance(entries, dict):
            for name, value in entries.items():
                if isinstance(value, str):
                    req = name if value == "*" else f"{name}{value}"
                elif isinstance(value, dict):
                    version = value.get("version")
                    req = name if not isinstance(version, str) or version == "*" else f"{name}{version}"
                else:
                    req = name

                parse_pydep(repo, path, req, scope, deps, unresolved, lock_versions, "pipenv")


def scan_tox_ini(repo: Path, path: Path, deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_versions: dict[str, str]) -> None:
    parser = configparser.ConfigParser()
    try:
        parser.read(path, encoding="utf-8")
    except Exception as e:
        unresolved.append(UnresolvedDependency("pypi", "tox", "tox.ini", rel(repo, path), f"INI parse failed: {e}"))
        return

    for section in parser.sections():
        if not section.startswith("testenv"):
            continue
        if not parser.has_option(section, "deps"):
            continue

        for item in parser.get(section, "deps").splitlines():
            item = item.strip()
            if not item or item.startswith("-"):
                continue
            parse_pydep(repo, path, item, f"test:{section}", deps, unresolved, lock_versions, "tox")


def scan_conda(repo: Path, path: Path, deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_versions: dict[str, str]) -> None:
    text = path.read_text(encoding="utf-8", errors="ignore")
    in_pip = False

    for line in text.splitlines():
        stripped = line.strip()

        if not stripped or stripped.startswith("#"):
            continue
        if stripped == "- pip:":
            in_pip = True
            continue
        if in_pip:
            if stripped.startswith("- "):
                item = stripped[2:].strip()
                parse_pydep(repo, path, item, "runtime:conda-pip", deps, unresolved, lock_versions, "conda")
            elif not line.startswith((" ", "\t")):
                in_pip = False

def scan_pyproject_groups(repo: Path, path: Path, data: dict[str, Any], deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_versions: dict[str, str]) -> None:
    groups = data.get("dependency-groups") or {}
    if not isinstance(groups, dict):
        return

    visited: set[str] = set()

    def scan_group(group_name: str, items: Any) -> None:
        if group_name in visited:
            return
        visited.add(group_name)

        if not isinstance(items, list):
            unresolved.append(UnresolvedDependency(
                "pypi", "python", group_name, rel(repo, path),
                "dependency-groups entry is not a list."
            ))
            return

        for item in items:
            if isinstance(item, str):
                parse_pydep(
                    repo, path, item, f"group:{group_name}",
                    deps, unresolved, lock_versions, "python"
                )
            elif isinstance(item, dict) and isinstance(item.get("include-group"), str):
                included = item["include-group"]
                scan_group(included, groups.get(included))
            else:
                unresolved.append(UnresolvedDependency(
                    "pypi", "python", str(item), rel(repo, path),
                    "Unsupported dependency-groups entry."
                ))

    for group_name, items in groups.items():
        scan_group(group_name, items)

def scan_python(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []
    pypi_lock_versions = get_pypi_lockvers(repo)

    req_files = [
        p for p in repo.rglob("requirements*.txt")
        if p.is_file() and not should_skip(p.relative_to(repo))
    ]

    req_files += [
        p for p in repo.rglob("constraints*.txt")
        if p.is_file() and not should_skip(p.relative_to(repo))
    ]

    req_files += [
        p for p in repo.rglob("requirements*.in")
        if p.is_file() and not should_skip(p.relative_to(repo))
    ]

    req_files += [
        p for p in repo.rglob("constraints*.in")
        if p.is_file() and not should_skip(p.relative_to(repo))
    ]

    for path in req_files:
        scope = "constraint" if "constraint" in path.name.lower() else "runtime"
        scan_requirements_file(repo, path, deps, unresolved, pypi_lock_versions, scope=scope)

    for path in repo_files(repo, {"setup.cfg"}):
        scan_setup_cfg(repo, path, deps, unresolved, pypi_lock_versions)

    for path in repo_files(repo, {"setup.py"}):
        scan_setup_py(repo, path, deps, unresolved, pypi_lock_versions)

    for path in repo_files(repo, {"Pipfile"}):
        scan_pipfile(repo, path, deps, unresolved, pypi_lock_versions)

    for path in repo_files(repo, {"tox.ini"}):
        scan_tox_ini(repo, path, deps, unresolved, pypi_lock_versions)

    for path in repo_files(repo, {"environment.yml", "environment.yaml", "conda-lock.yml", "conda-lock.yaml"}):
        scan_conda(repo, path, deps, unresolved, pypi_lock_versions)

    for path in repo_files(repo, {"pyproject.toml"}):
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception as e:
            unresolved.append(UnresolvedDependency("pypi", "python", "pyproject.toml", rel(repo, path), f"TOML parse failed: {e}"))
            continue

        build_system = data.get("build-system") or {}
        if isinstance(build_system, dict):
            for item in build_system.get("requires", []) or []:
                if isinstance(item, str):
                    parse_pydep(
                        repo, path, item, "build-system",
                        deps, unresolved, pypi_lock_versions, "python-build-system"
                    )

        scan_pyproject_groups(
            repo, path, data, deps, unresolved, pypi_lock_versions
        )

        project = data.get("project", {}) or {}
        for item in project.get("dependencies", []) or []:
            parse_pydep(repo, path, item, "runtime", deps, unresolved, pypi_lock_versions)

        optional = project.get("optional-dependencies", {}) or {}
        if isinstance(optional, dict):
            for group, items in optional.items():
                for item in items or []:
                    parse_pydep(repo, path, item, f"optional:{group}", deps, unresolved, pypi_lock_versions)

        poetry_deps = (((data.get("tool") or {}).get("poetry") or {}).get("dependencies") or {})
        for name, version in poetry_deps.items():
            if name.lower() == "python":
                continue
            parse_pydep(
                repo, path, poetry_dep_str(name, version),
                "runtime", deps, unresolved, pypi_lock_versions, "poetry"
            )

        poetry_groups = (((data.get("tool") or {}).get("poetry") or {}).get("group") or {})
        for group, group_data in poetry_groups.items():
            group_deps = ((group_data or {}).get("dependencies") or {})
            for name, version in group_deps.items():
                parse_pydep(
                    repo, path, poetry_dep_str(name, version),
                    f"group:{group}", deps, unresolved, pypi_lock_versions, "poetry"
                )

        poetry_dev_deps = (((data.get("tool") or {}).get("poetry") or {}).get("dev-dependencies") or {})
        if isinstance(poetry_dev_deps, dict):
            for name, version in poetry_dev_deps.items():
                if name.lower() == "python":
                    continue
                parse_pydep(
                    repo, path, poetry_dep_str(name, version),
                    "development", deps, unresolved, pypi_lock_versions, "poetry"
                )

        pdm_deps = (((data.get("tool") or {}).get("pdm") or {}).get("dev-dependencies") or {})
        if isinstance(pdm_deps, dict):
            for group, items in pdm_deps.items():
                for item in items or []:
                    parse_pydep(
                        repo, path, item,
                        f"development:{group}", deps, unresolved, pypi_lock_versions, "pdm"
                    )

    return deps, unresolved

# -------------------------
# Go
# -------------------------

def get_go_deps(repo: Path, path: Path, text: str, scope_prefix: str = "runtime") -> list[Dependency]:
    deps: list[Dependency] = []
    in_block = False

    for line in text.splitlines():
        raw = line.strip()
        if not raw or raw.startswith("//"):
            continue

        if raw.startswith("require ("):
            in_block = True
            continue
        if in_block and raw == ")":
            in_block = False
            continue

        if raw.startswith("require "):
            raw = raw[len("require "):].strip()

        if in_block or re.match(r"^[A-Za-z0-9_.~/.-]+\s+v", raw):
            parts = raw.split()
            if len(parts) >= 2:
                name, version = parts[0], parts[1]
                scope = "indirect" if "// indirect" in line else scope_prefix
                deps.append(Dependency(
                    ecosystem="golang",
                    package_manager="go",
                    name=name,
                    version=version,
                    scope=scope,
                    source_file=rel(repo, path),
                    source_type=path.name,
                    confidence="high",
                    purl=make_purl("golang", name, version),
                ))

    return deps

def scan_go_work(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    for path in repo_files(repo, {"go.work"}):
        text = path.read_text(encoding="utf-8", errors="ignore")

        for m in re.finditer(
            r"replace\s+([A-Za-z0-9_.~/.-]+)(?:\s+v[^\s]+)?\s+=>\s+([A-Za-z0-9_.~/.-]+)(?:\s+(v[^\s]+))?",
            text,
        ):
            old_name, new_name, new_version = m.groups()

            if new_version:
                deps.append(Dependency(
                    ecosystem="golang",
                    package_manager="go-work",
                    name=new_name,
                    version=new_version,
                    scope="workspace-replacement",
                    source_file=rel(repo, path),
                    source_type="go.work",
                    confidence="high",
                    purl=make_purl("golang", new_name, new_version),
                    notes=f"go.work replaces {old_name}",
                ))
            else:
                deps.append(Dependency(
                    ecosystem="internal",
                    package_manager="go-work",
                    name=new_name,
                    version=None,
                    scope="workspace-replacement",
                    source_file=rel(repo, path),
                    source_type="go.work",
                    confidence="medium",
                    purl=None,
                    notes=f"go.work local replacement for {old_name}",
                ))

    return deps, unresolved

def scan_gopkg_files(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    for path in repo_files(repo, {"Gopkg.lock"}):
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception as e:
            unresolved.append(UnresolvedDependency("golang", "dep", path.name, rel(repo, path), f"TOML parse failed: {e}"))
            continue

        for project in data.get("projects", []) or []:
            if not isinstance(project, dict):
                continue
            name = project.get("name")
            version = project.get("version") or project.get("revision")
            if isinstance(name, str) and isinstance(version, str):
                deps.append(Dependency(
                    ecosystem="golang",
                    package_manager="dep",
                    name=name,
                    version=version,
                    scope="legacy-lock",
                    source_file=rel(repo, path),
                    source_type="Gopkg.lock",
                    confidence="high",
                    purl=make_purl("golang", name, version),
                ))

    for path in repo_files(repo, {"Gopkg.toml"}):
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception as e:
            unresolved.append(UnresolvedDependency("golang", "dep", path.name, rel(repo, path), f"TOML parse failed: {e}"))
            continue

        for constraint in data.get("constraint", []) or []:
            if not isinstance(constraint, dict):
                continue
            name = constraint.get("name")
            version = constraint.get("version") or constraint.get("branch") or constraint.get("revision")
            if isinstance(name, str):
                deps.append(Dependency(
                    ecosystem="golang",
                    package_manager="dep",
                    name=name,
                    version=str(version) if version else None,
                    scope="legacy-declared",
                    source_file=rel(repo, path),
                    source_type="Gopkg.toml",
                    confidence="medium" if version else "low",
                    purl=make_purl("golang", name, str(version)) if version else None,
                ))

    return deps, unresolved

def scan_glide_files(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    for path in repo_files(repo, {"glide.lock", "glide.yaml"}):
        text = path.read_text(encoding="utf-8", errors="ignore")

        current_name: str | None = None
        current_version: str | None = None

        for line in text.splitlines():
            stripped = line.strip()

            if stripped.startswith("- name:"):
                if current_name:
                    deps.append(Dependency(
                        ecosystem="golang",
                        package_manager="glide",
                        name=current_name,
                        version=current_version,
                        scope="legacy-lock" if path.name == "glide.lock" else "legacy-declared",
                        source_file=rel(repo, path),
                        source_type=path.name,
                        confidence="medium" if current_version else "low",
                        purl=make_purl("golang", current_name, current_version),
                    ))

                current_name = stripped.split(":", 1)[1].strip().strip('"').strip("'")
                current_version = None

            elif stripped.startswith("version:") and current_name:
                current_version = stripped.split(":", 1)[1].strip().strip('"').strip("'")

        if current_name:
            deps.append(Dependency(
                ecosystem="golang",
                package_manager="glide",
                name=current_name,
                version=current_version,
                scope="legacy-lock" if path.name == "glide.lock" else "legacy-declared",
                source_file=rel(repo, path),
                source_type=path.name,
                confidence="medium" if current_version else "low",
                purl=make_purl("golang", current_name, current_version),
            ))

    return deps, unresolved

def parse_go_replacements(text: str) -> dict[str, tuple[str, str | None, bool]]:
    replacements: dict[str, tuple[str, str | None, bool]] = {}

    in_replace_block = False

    for line in text.splitlines():
        raw = line.strip()
        if not raw or raw.startswith("//"):
            continue

        if raw.startswith("replace ("):
            in_replace_block = True
            continue

        if in_replace_block and raw == ")":
            in_replace_block = False
            continue

        if raw.startswith("replace "):
            raw = raw[len("replace "):].strip()

        if not in_replace_block and "=>" not in raw:
            continue

        raw_no_comment = raw.split("//", 1)[0].strip()
        if "=>" not in raw_no_comment:
            continue

        left, right = [part.strip() for part in raw_no_comment.split("=>", 1)]
        left_parts = left.split()
        right_parts = right.split()

        if not left_parts or not right_parts:
            continue

        old_module = left_parts[0]
        new_module = right_parts[0]

        is_local = (
            new_module.startswith("./")
            or new_module.startswith("../")
            or new_module.startswith("/")
        )

        new_version = right_parts[1] if len(right_parts) >= 2 else None
        replacements[old_module] = (new_module, new_version, is_local)

    return replacements


def parse_go_requirements(repo: Path, path: Path, text: str) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []
    replacements = parse_go_replacements(text)

    in_require_block = False

    for line in text.splitlines():
        raw = line.strip()

        if not raw or raw.startswith("//"):
            continue

        is_indirect = "// indirect" in line

        if raw.startswith("require ("):
            in_require_block = True
            continue

        if in_require_block and raw == ")":
            in_require_block = False
            continue

        if raw.startswith("require "):
            raw = raw[len("require "):].strip()
        elif not in_require_block:
            continue

        raw_no_comment = raw.split("//", 1)[0].strip()
        parts = raw_no_comment.split()

        if len(parts) < 2:
            unresolved.append(UnresolvedDependency(
                "golang",
                "go",
                raw,
                rel(repo, path),
                "Go require declaration could not be parsed.",
            ))
            continue

        name, version = parts[0], parts[1]
        scope = "indirect" if is_indirect else "runtime"
        notes = None
        purl_name = name
        purl_version = version
        confidence = "high"

        replacement = replacements.get(name)
        if replacement:
            replacement_name, replacement_version, is_local = replacement

            if is_local:
                deps.append(Dependency(
                    ecosystem="internal",
                    package_manager="go",
                    name=name,
                    version=version,
                    scope=scope,
                    source_file=rel(repo, path),
                    source_type="go.mod",
                    confidence="high",
                    purl=None,
                    notes=f"Go module is replaced by local path: {replacement_name}",
                ))
                continue

            purl_name = replacement_name
            if replacement_version:
                purl_version = replacement_version

            notes = (
                f"Original Go module {name}@{version} replaced by "
                f"{purl_name}@{purl_version}."
            )

        deps.append(Dependency(
            ecosystem="golang",
            package_manager="go",
            name=purl_name,
            version=purl_version,
            scope=scope,
            source_file=rel(repo, path),
            source_type="go.mod",
            confidence=confidence,
            purl=make_purl("golang", purl_name, purl_version),
            notes=notes,
        ))

    return deps, unresolved


def scan_go(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    # go.mod
    for path in repo_files(repo, {"go.mod"}):
        text = path.read_text(encoding="utf-8", errors="ignore")

        d, u = parse_go_requirements(repo, path, text)
        deps.extend(d)
        unresolved.extend(u)

    # go.work workspace replacements
    d, u = scan_go_work(repo)
    deps.extend(d)
    unresolved.extend(u)

    # vendor/modules.txt
    for path in repo_files(repo, {"modules.txt"}):
        if "vendor" not in path.parts:
            continue

        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            m = re.match(r"^#\s+([A-Za-z0-9_.~/.-]+)\s+(v[^\s]+)", line.strip())
            if not m:
                continue

            name, version = m.groups()
            deps.append(Dependency(
                ecosystem="golang",
                package_manager="go-vendor",
                name=name,
                version=version,
                scope="vendored",
                source_file=rel(repo, path),
                source_type="vendor/modules.txt",
                confidence="high",
                purl=make_purl("golang", name, version),
            ))

    # legacy Dep
    d, u = scan_gopkg_files(repo)
    deps.extend(d)
    unresolved.extend(u)

    # legacy Glide
    d, u = scan_glide_files(repo)
    deps.extend(d)
    unresolved.extend(u)

    return deps, unresolved


# -------------------------
# Rust
# -------------------------

def load_cargo_pkgs(repo: Path) -> dict[str, dict[str, str | None]]:
    packages: dict[str, dict[str, str | None]] = {}

    for path in repo_files(repo, {"Cargo.lock"}):
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue

        for pkg in data.get("package") or []:
            if not isinstance(pkg, dict):
                continue

            name = pkg.get("name")
            version = pkg.get("version")
            source = pkg.get("source")

            if isinstance(name, str) and isinstance(version, str):
                packages[normalize_name(name)] = {
                    "version": version,
                    "source": source if isinstance(source, str) else None,
                }

    return packages


def load_cargo_vers(repo: Path) -> dict[str, str]:
    return {
        name: meta["version"]
        for name, meta in load_cargo_pkgs(repo).items()
        if isinstance(meta.get("version"), str)
    }


def cargo_lock_note(package_name: str, lock_packages: dict[str, dict[str, str | None]]) -> str | None:
    meta = lock_packages.get(normalize_name(package_name))
    if not meta:
        return None

    source = meta.get("source")
    if not source:
        return "Resolved from Cargo.lock."

    if source.startswith("registry+"):
        return f"Resolved from Cargo.lock registry+ source: {source}"
    if source.startswith("git+"):
        return f"Resolved from Cargo.lock git source: {source}"

    return f"Resolved from Cargo.lock source: {source}"


def scan_cargo_configs(repo: Path) -> list[UnresolvedDependency]:
    reports: list[UnresolvedDependency] = []

    for config_path in repo_files(repo, {"config.toml", "config"}):
        if ".cargo" not in config_path.parts:
            continue

        rel_path = rel(repo, config_path)

        try:
            data = tomllib.loads(config_path.read_text(encoding="utf-8"))
        except Exception as e:
            reports.append(UnresolvedDependency(
                "cargo",
                "cargo",
                config_path.name,
                rel_path,
                f"Cargo config parse failed: {e}",
            ))
            continue

        registries = data.get("registries") or {}
        if isinstance(registries, dict):
            for registry_name, registry_data in registries.items():
                if isinstance(registry_data, dict):
                    index = registry_data.get("index")
                    reports.append(UnresolvedDependency(
                        "cargo",
                        "cargo",
                        f"registry.{registry_name}",
                        rel_path,
                        f"Cargo alternate detected, index={index or 'NOASSERTION'}",
                    ))

        sources = data.get("source") or {}
        if isinstance(sources, dict):
            for source_name, source_data in sources.items():
                if not isinstance(source_data, dict):
                    continue

                details = []
                for key in ("replace-with", "registry", "directory", "local-registry"):
                    value = source_data.get(key)
                    if isinstance(value, str):
                        details.append(f"{key}={value}")

                reports.append(UnresolvedDependency(
                    "cargo",
                    "cargo",
                    f"source.{source_name}",
                    rel_path,
                    "Cargo source configuration detected: " + (", ".join(details) if details else "NOASSERTION"),
                ))

    return reports


def rust_dep_info(declared_name: str, value: Any, workspace_dependencies: dict[str, tuple[str, str | None, bool, str | None]]) -> tuple[str, str | None, bool, str | None]:
    if isinstance(value, str):
        return declared_name, value, False, None

    if isinstance(value, dict):
        if value.get("workspace") is True:
            inherited = workspace_dependencies.get(normalize_name(declared_name))
            if inherited:
                package_name, version, is_internal, inherited_notes = inherited
                notes = f"Inherited from [workspace.dependencies]."
                if inherited_notes:
                    notes += f" {inherited_notes}"
                return package_name, version, is_internal, notes

            return declared_name, None, False, "workspace = true dependency could not be resolved from [workspace.dependencies]."

        package_name = value.get("package")
        if not isinstance(package_name, str):
            package_name = declared_name

        if "path" in value:
            return package_name, None, True, f"Rust path dependency detected: {value.get('path')}"

        version = value.get("version")
        if isinstance(version, str):
            note = None
            if package_name != declared_name:
                note = f"Cargo dependency alias detected: {declared_name} -> package {package_name}"
            return package_name, version, False, note

        if "git" in value:
            return package_name, None, False, f"Rust git dependency detected: {value.get('git')}"

    return declared_name, None, False, None


def get_cargo_workspace_deps(repo: Path) -> dict[str, tuple[str, str | None, bool, str | None]]:
    workspace_deps: dict[str, tuple[str, str | None, bool, str | None]] = {}

    for path in repo_files(repo, {"Cargo.toml"}):
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue

        workspace = data.get("workspace") or {}
        if not isinstance(workspace, dict):
            continue

        entries = workspace.get("dependencies") or {}
        if not isinstance(entries, dict):
            continue

        for declared_name, value in entries.items():
            package_name, version, is_internal, notes = rust_dep_info(
                declared_name,
                value,
                {},
            )
            workspace_deps[normalize_name(declared_name)] = (
                package_name,
                version,
                is_internal,
                notes,
            )

    return workspace_deps


def scan_cargo_patches(repo: Path, path: Path, data: dict[str, Any]) -> list[UnresolvedDependency]:
    reports: list[UnresolvedDependency] = []

    patch = data.get("patch") or {}
    if isinstance(patch, dict):
        for patch_source, entries in patch.items():
            if not isinstance(entries, dict):
                continue

            for dep_name, dep_data in entries.items():
                reports.append(UnresolvedDependency(
                    "cargo",
                    "cargo",
                    f"[patch.{patch_source}] {dep_name}",
                    rel(repo, path),
                    "Cargo patch override detected, scanner records it but does not rewrite dependency identity from patch metadata.",
                ))

    replace = data.get("replace") or {}
    if isinstance(replace, dict):
        for replaced, replacement in replace.items():
            reports.append(UnresolvedDependency(
                "cargo",
                "cargo",
                f"[replace] {replaced}",
                rel(repo, path),
                "Cargo replace override detected, scanner records it but does not rewrite dependency identity from replacement metadata.",
            ))

    return reports


def scan_rust_deps(repo: Path, path: Path, entries: dict[str, Any], scope: str, deps: list[Dependency], unresolved: list[UnresolvedDependency], lock_packages: dict[str, dict[str, str | None]], workspace_dependencies: dict[str, tuple[str, str | None, bool, str | None]]) -> None:
    for declared_name, value in entries.items():
        package_name, declared_version, is_internal, notes = rust_dep_info(
            declared_name,
            value,
            workspace_dependencies,
        )

        if is_internal:
            deps.append(Dependency(
                ecosystem="internal",
                package_manager="cargo",
                name=package_name,
                version=None,
                scope=scope,
                source_file=rel(repo, path),
                source_type="Cargo.toml",
                confidence="high",
                purl=None,
                notes=notes or "Rust internal/path dependency, not added as external Cargo package.",
            ))
            continue

        lock_meta = lock_packages.get(normalize_name(package_name))
        locked_version = lock_meta.get("version") if lock_meta else None
        resolved_version = locked_version or declared_version

        lock_note = cargo_lock_note(package_name, lock_packages)
        final_notes = notes

        if lock_note:
            final_notes = f"{final_notes}, {lock_note}" if final_notes else lock_note

        if locked_version and declared_version and locked_version != declared_version:
            final_notes = f"{final_notes or ''} Original declaration: {declared_version}".strip()

        if not resolved_version:
            unresolved.append(UnresolvedDependency(
                "cargo",
                "cargo",
                declared_name,
                rel(repo, path),
                notes or "Rust dependency has no exact version and was not found in Cargo.lock.",
            ))

        deps.append(Dependency(
            ecosystem="cargo",
            package_manager="cargo",
            name=package_name,
            version=resolved_version,
            scope=scope,
            source_file=rel(repo, path),
            source_type="Cargo.toml",
            confidence="high" if locked_version else ("medium" if resolved_version else "low"),
            purl=make_purl("cargo", package_name, resolved_version),
            notes=final_notes,
        ))


def scan_rust(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    lock_packages = load_cargo_pkgs(repo)
    workspace_dependencies = get_cargo_workspace_deps(repo)

    unresolved.extend(scan_cargo_configs(repo))

    for vendor_dir in repo.rglob("vendor"):
        if vendor_dir.is_dir() and not should_skip(vendor_dir.relative_to(repo)):
            unresolved.append(UnresolvedDependency(
                "cargo",
                "cargo",
                "vendor/",
                rel(repo, vendor_dir),
                "Rust vendored source directory detected, scanner records this but doesn't infer packages from source metadata.",
            ))

    normal_sections = {
        "dependencies": "runtime",
        "dev-dependencies": "development",
        "build-dependencies": "build",
    }

    for path in repo_files(repo, {"Cargo.toml"}):
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception as e:
            unresolved.append(UnresolvedDependency("cargo", "cargo", "Cargo.toml", rel(repo, path), f"TOML parse failed: {e}"))
            continue

        unresolved.extend(scan_cargo_patches(repo, path, data))

        for section, scope in normal_sections.items():
            entries = data.get(section, {}) or {}
            if isinstance(entries, dict):
                scan_rust_deps(
                    repo,
                    path,
                    entries,
                    scope,
                    deps,
                    unresolved,
                    lock_packages,
                    workspace_dependencies,
                )

        target = data.get("target", {}) or {}
        if isinstance(target, dict):
            for target_name, target_data in target.items():
                if not isinstance(target_data, dict):
                    continue

                for section, base_scope in normal_sections.items():
                    entries = target_data.get(section, {}) or {}
                    if isinstance(entries, dict):
                        scan_rust_deps(
                            repo,
                            path,
                            entries,
                            f"{base_scope}:{target_name}",
                            deps,
                            unresolved,
                            lock_packages,
                            workspace_dependencies,
                        )

    return deps, unresolved

# -------------------------
# PHP / Composer
# -------------------------

def is_composer_exact_version(version: str | None) -> bool:
    if not version:
        return False

    v = version.strip().lower()
    if v in {"", "noassertion"}:
        return False
    if v.startswith(("^", "~", ">", "<", "=", "*")):
        return False
    if "|" in v or "," in v or " " in v:
        return False
    if v.startswith(("dev-", "self.version")):
        return False

    return bool(re.fullmatch(
        r"v?\d+(?:\.\d+)*(?:[-+][A-Za-z0-9_.-]+)?",
        v,
        re.IGNORECASE,
    ))


def get_composer_vers(repo: Path) -> dict[str, str]:
    versions: dict[str, str] = {}

    for path in repo_files(repo, {"composer.lock"}):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue

        for section in ("packages", "packages-dev"):
            packages = data.get(section) or []
            if not isinstance(packages, list):
                continue

            for pkg in packages:
                if not isinstance(pkg, dict):
                    continue

                name = pkg.get("name")
                version = pkg.get("version")

                if isinstance(name, str) and isinstance(version, str):
                    versions[normalize_name(name)] = version

    return versions


def get_composer_ivers(repo: Path) -> dict[str, str]:
    versions: dict[str, str] = {}
    for path in repo.rglob("vendor/composer/installed.json"):
        if not path.is_file():
            continue

        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue

        packages_obj = data.get("packages") if isinstance(data, dict) else data
        if not isinstance(packages_obj, list):
            continue

        for pkg in packages_obj:
            if not isinstance(pkg, dict):
                continue

            name = pkg.get("name")
            version = pkg.get("version")

            if isinstance(name, str) and isinstance(version, str):
                versions[normalize_name(name)] = version

    return versions


def resolve_composer_ver(name: str, declared_version: str | None, lock_versions: dict[str, str], installed_versions: dict[str, str]) -> tuple[str | None, str | None]:
    normalized = normalize_name(name)

    locked = lock_versions.get(normalized)
    if locked:
        return locked, f"Resolved Composer declaration from composer.lock to exact version {locked}."

    installed = installed_versions.get(normalized)
    if installed:
        return installed, f"Resolved Composer declaration from vendor/composer/installed.json to exact version {installed}."

    if declared_version and is_composer_exact_version(declared_version):
        return declared_version, None

    return declared_version, "Composer dependency kept as declared constraint, no composer.lock or installed.json exact version found."


def get_composer_exact_vers(deps: list[Dependency]) -> dict[str, str]:
    versions: dict[str, str] = {}

    for dep in deps:
        if dep.ecosystem != "composer":
            continue

        if dep.version and is_composer_exact_version(dep.version):
            versions[normalize_name(dep.name)] = dep.version

    return versions

def scan_php(repo: Path) -> tuple[list[Dependency], list[UnresolvedDependency]]:
    deps: list[Dependency] = []
    unresolved: list[UnresolvedDependency] = []

    lock_versions = get_composer_vers(repo)
    installed_versions = get_composer_ivers(repo)

    for path in repo_files(repo, {"composer.json", "composer.local.json"}):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception as e:
            unresolved.append(UnresolvedDependency("composer", "composer", path.name, rel(repo, path), f"JSON parse failed: {e}"))
            continue

        for section, scope in {"require": "runtime", "require-dev": "development"}.items():
            entries = data.get(section, {}) or {}

            if isinstance(entries, dict):
                for name, raw_version in entries.items():
                    if name.lower() == "php" or name.startswith("ext-"):
                        continue

                    declared_version = str(raw_version) if raw_version is not None else None
                    resolved_version, resolution_note = resolve_composer_ver(
                        name,
                        declared_version,
                        lock_versions,
                        installed_versions,
                    )

                    purl = (
                        make_purl("composer", name, resolved_version)
                        if is_composer_exact_version(resolved_version)
                        else None
                    )

                    notes = resolution_note
                    if declared_version and resolved_version != declared_version:
                        notes = f"{notes or ''} Original declaration: {declared_version}".strip()

                    deps.append(Dependency(
                        ecosystem="composer",
                        package_manager="composer",
                        name=name,
                        version=resolved_version,
                        scope=scope,
                        source_file=rel(repo, path),
                        source_type=path.name,
                        confidence="high" if purl else "medium",
                        purl=purl,
                        notes=notes,
                    ))

    return deps, unresolved


# -------------------------
# Main scan/compare
# -------------------------

def dedupe_deps(deps: list[Dependency]) -> list[Dependency]:
    seen: set[tuple[str, str, str | None, str, str]] = set()
    out: list[Dependency] = []

    for d in deps:
        key = (d.ecosystem, normalize_name(d.name), d.version, d.scope, d.source_file)
        if key not in seen:
            seen.add(key)
            out.append(d)

    return out

def dedupe_unresolved(unresolved: list[UnresolvedDependency]) -> list[UnresolvedDependency]:
    seen: set[tuple[str, str, str, str, str]] = set()
    out: list[UnresolvedDependency] = []

    for u in unresolved:
        key = (u.ecosystem, u.package_manager, u.raw, u.source_file, u.reason)

        if key not in seen:
            seen.add(key)
            out.append(u)

    return out

def dedupe_gradle_repos(reports: list[GradleRepoReport]) -> list[GradleRepoReport]:
    seen: set[tuple[str, str, str | None]] = set()
    out: list[GradleRepoReport] = []

    for r in reports:
        key = (r.source_file, r.repository_type, r.value)

        if key not in seen:
            seen.add(key)
            out.append(r)

    return out

# -------------------------
# Languages List (TODO: convert to imported file/scan so this isn't hardcoded)
# -------------------------
SCANNERS = {
    "java": scan_java,
    "javascript": scan_javascript,
    "python": scan_python,
    "go": scan_go,
    "rust": scan_rust,
    "php": scan_php,
}

def scan_deps(repo: Path, ecosystems: list[str] | None = None) -> tuple[list[Dependency], list[UnresolvedDependency], list[GradleRepoReport]]:
    all_deps: list[Dependency] = []
    all_unresolved: list[UnresolvedDependency] = []
    all_repository_reports: list[GradleRepoReport] = []

    selected = ecosystems or list(SCANNERS.keys())

    for ecosystem in selected:
        scanner = SCANNERS.get(ecosystem)

        if scanner is None:
            all_unresolved.append(UnresolvedDependency(
                ecosystem=ecosystem,
                package_manager="unknown",
                raw=ecosystem,
                source_file=str(repo),
                reason=f"No scanner registered for ecosystem: {ecosystem}",
            ))
            continue

        if ecosystem == "java":
            deps, unresolved, repository_reports = scanner(repo)
            all_repository_reports.extend(repository_reports)
        else:
            deps, unresolved = scanner(repo)

        all_deps.extend(deps)
        all_unresolved.extend(unresolved)

    return (
        dedupe_deps(all_deps),
        dedupe_unresolved(all_unresolved),
        dedupe_gradle_repos(all_repository_reports),
    )

def compare_to_sbom(deps: list[Dependency],  sbom_package_identities: set[str], identity_to_spdxid: dict[str, str]) -> tuple[list[Dependency], list[SkippedDependency]]:
    missing: list[Dependency] = []
    skipped: list[SkippedDependency] = []

    for dep in deps:
        should_add, reason, matched_spdx_id = should_add_dependency(dep, sbom_package_identities, identity_to_spdxid)
        if should_add:
            missing.append(dep)
        else:
            skipped.append(SkippedDependency(dep, reason, matched_spdx_id))

    return missing, skipped

def clean_comments(sbom_data: dict[str, Any]) -> None:
    sbom = sbom_data.get("sbom", sbom_data)

    for rel_obj in sbom.get("relationships", []) or []:
        if not isinstance(rel_obj, dict):
            continue

        comment = rel_obj.get("comment")
        if isinstance(comment, str) and comment.startswith(SURFACE_COMMENT_PREFIX):
            rel_obj.pop("comment", None)


def upsert_relationship(sbom_data: dict[str, Any], root_spdxid: str, dep_spdxid: str) -> None:
    sbom = sbom_data.get("sbom", sbom_data)
    sbom.setdefault("relationships", [])

    for rel_obj in sbom["relationships"]:
        if (
            rel_obj.get("spdxElementId") == root_spdxid
            and rel_obj.get("relatedSpdxElement") == dep_spdxid
            and rel_obj.get("relationshipType") == "DEPENDS_ON"
        ):
            comment = rel_obj.get("comment")
            if isinstance(comment, str) and comment.startswith(SURFACE_COMMENT_PREFIX):
                rel_obj.pop("comment", None)
            return

    sbom["relationships"].append({
        "spdxElementId": root_spdxid,
        "relatedSpdxElement": dep_spdxid,
        "relationshipType": "DEPENDS_ON",
    })

def find_root_spdxid(sbom_data: dict[str, Any]) -> str | None:
    sbom = sbom_data.get("sbom", sbom_data)

    # Prefer the package described by the document.
    for rel_obj in sbom.get("relationships", []) or []:
        if (
            rel_obj.get("spdxElementId") == "SPDXRef-DOCUMENT"
            and rel_obj.get("relationshipType") == "DESCRIBES"
        ):
            return rel_obj.get("relatedSpdxElement")

    # Fallback: GitHub package/root repo package.
    for pkg in sbom.get("packages", []) or []:
        for ref in pkg.get("externalRefs", []) or []:
            loc = ref.get("referenceLocator", "")
            if isinstance(loc, str) and loc.startswith("pkg:github/"):
                return pkg.get("SPDXID")

    return None


def safe_spdxid(dep: Dependency) -> str:
    identity = get_dep_id(dep) or f"{dep.ecosystem}:{dep.name}:{dep.version or 'unknown'}"
    digest = hashlib.sha1(identity.encode("utf-8")).hexdigest()[:8]

    base = f"{dep.ecosystem}-{dep.name}-{dep.version or 'unknown'}"
    safe = re.sub(r"[^A-Za-z0-9.-]+", "-", base).strip("-")

    return f"SPDXRef-surface-{safe}-{digest}"


def dep_to_spdx_pkg(dep: Dependency) -> dict[str, Any]:
    package = {
        "name": dep.name,
        "SPDXID": safe_spdxid(dep),
        "versionInfo": dep.version or "NOASSERTION",
        "downloadLocation": "NOASSERTION",
        "filesAnalyzed": False,
        "licenseConcluded": "NOASSERTION",
        "licenseDeclared": "NOASSERTION",
        "copyrightText": "NOASSERTION",
    }

    if dep.purl:
        package["externalRefs"] = [
            {
                "referenceCategory": "PACKAGE-MANAGER",
                "referenceType": "purl",
                "referenceLocator": dep.purl,
            }
        ]

    return package

def maven_name_from_dep(dep: Dependency) -> tuple[str, str] | None:
    if dep.ecosystem != "maven" or ":" not in dep.name:
        return None
    group, artifact = dep.name.split(":", 1)
    return group, artifact


def get_maven_pkg(sbom_data: dict[str, Any], dep: Dependency) -> dict[str, Any] | None:
    parts = maven_name_from_dep(dep)
    if not parts or not dep.version:
        return None

    group, artifact = parts
    unversioned_purl = f"pkg:maven/{group}/{artifact}".lower()

    sbom = sbom_data.get("sbom", sbom_data)

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        for ref in pkg.get("externalRefs", []) or []:
            loc = ref.get("referenceLocator")
            if isinstance(loc, str) and loc.split("?", 1)[0].lower() == unversioned_purl:
                return pkg

    return None


def upgrade_maven_pkg(pkg: dict[str, Any], dep: Dependency) -> None:
    if not dep.version:
        return

    pkg["versionInfo"] = dep.version

    if dep.purl:
        refs = pkg.setdefault("externalRefs", [])

        for ref in refs:
            if ref.get("referenceType") == "purl":
                ref["referenceLocator"] = dep.purl
                return

        refs.append({
            "referenceCategory": "PACKAGE-MANAGER",
            "referenceType": "purl",
            "referenceLocator": dep.purl,
        })

def add_missing_deps(sbom_path: Path, deps: list[Dependency], missing: list[Dependency], skipped: list[SkippedDependency]) -> tuple[dict[str, Any], SurfaceWriteStats]:
    sbom_data = json.loads(sbom_path.read_text(encoding="utf-8"))
    sbom = sbom_data.get("sbom", sbom_data)

    sbom.setdefault("packages", [])
    sbom.setdefault("relationships", [])
    packages_added = 0
    packages_enriched = 0

    clean_comments(sbom_data)

    existing_spdx_ids = set()
    existing_package_keys = set()

    for pkg in sbom.get("packages", []):
        if not isinstance(pkg, dict):
            continue

        spdx_id = pkg.get("SPDXID")
        if spdx_id:
            existing_spdx_ids.add(spdx_id)

        identity = get_pkg_id(pkg)
        if identity:
            existing_package_keys.add(identity)

    root_spdxid = find_root_spdxid(sbom_data)

    for dep in missing:
        existing_unversioned = get_maven_pkg(sbom_data, dep)
        if existing_unversioned:
            upgrade_maven_pkg(existing_unversioned, dep)
            packages_enriched += 1
            upgraded_identity = get_pkg_id(existing_unversioned)
            if upgraded_identity:
                existing_package_keys.add(upgraded_identity)

            if root_spdxid and existing_unversioned.get("SPDXID"):
                upsert_relationship(sbom_data, root_spdxid, existing_unversioned["SPDXID"])

            continue

        package = dep_to_spdx_pkg(dep)
        package_identity = get_pkg_id(package)

        if package["SPDXID"] in existing_spdx_ids:
            continue
        if package_identity and package_identity in existing_package_keys:
            continue

        sbom["packages"].append(package)
        packages_added += 1
        existing_spdx_ids.add(package["SPDXID"])
        if package_identity:
            existing_package_keys.add(package_identity)

        if root_spdxid:
            upsert_relationship(sbom_data, root_spdxid, package["SPDXID"])

    if root_spdxid:
        for skipped_dep in skipped:
            if skipped_dep.matched_spdx_id:
                upsert_relationship(sbom_data, root_spdxid, skipped_dep.matched_spdx_id)
    
    npm_repaired, npm_removed = repair_npm_pkg(sbom_data, get_npm_vers(deps))

    pypi_repaired, pypi_removed = repair_pypi_pkg(sbom_data, get_pypi_vers(deps))

    composer_repaired = repair_comp_pkg(sbom_data, get_composer_exact_vers(deps))

    dedupe_pkgs(sbom_data)

    return sbom_data, SurfaceWriteStats(packages_added=packages_added, packages_enriched=packages_enriched, packages_repaired=npm_repaired + pypi_repaired + composer_repaired, packages_removed=npm_removed + pypi_removed)


def repo_out_dir(sbom_path: Path) -> Path:
    # If baseline_generator saves as generated_sboms/owner_repo/github.spdx.json, this returns generated_sboms/owner_repo.
    return sbom_path.resolve().parent


def write_surface_sbom(sbom_path: Path, sbom_data: dict[str, Any]) -> Path:
    output_dir = repo_out_dir(sbom_path)

    original_name = sbom_path.name
    surface_name = f"surface_{original_name}"

    output_path = output_dir / surface_name
    output_path.write_text(json.dumps(sbom_data, indent=2), encoding="utf-8")

    return output_path


def write_log(
    sbom_path: Path,
    repo: Path,
    deps: list[Dependency],
    missing: list[Dependency],
    skipped: list[SkippedDependency],
    unresolved: list[UnresolvedDependency],
    original_duplicate_packages: list[DuplicateIssue],
    original_duplicate_relationships: list[DuplicateIssue],
    surface_duplicate_packages: list[DuplicateIssue],
    surface_duplicate_relationships: list[DuplicateIssue],
    write_stats: SurfaceWriteStats,
    gradle_repositories: list[GradleRepoReport],
) -> Path:
    output_dir = repo_out_dir(sbom_path)
    logs_dir = output_dir / "logs"
    logs_dir.mkdir(parents=True, exist_ok=True)
    log_path = logs_dir / "surface_report.json"
    scope_summary: dict[str, int] = {}
    for dep in deps:
        category = dep_scope(dep.scope)
        scope_summary[category] = scope_summary.get(category, 0) + 1
    unique_deps = get_unique_ids(deps)
    unique_missing = get_unique_ids(missing)
    repeated_declarations_collapsed = len(deps) - len(unique_deps)
    report = {
        "repo": str(repo),
        "sbom": str(sbom_path),
        "direct_dependency_declarations_found": len(deps),
        "unique_direct_dependency_packages_found": len(unique_deps),
        "dependency_declarations_needing_sbom_changes": len(missing),
        "gradle_repositories_detected": len(gradle_repositories),
        "gradle_repositories": [asdict(r) for r in gradle_repositories],
        "existing_packages_enriched_in_sbom": write_stats.packages_enriched,
        "new_packages_added_to_sbom": write_stats.packages_added,
        "baseline_packages_repaired_in_sbom": write_stats.packages_repaired,
        "baseline_packages_removed_from_sbom": write_stats.packages_removed,
        "repeated_declarations_collapsed_during_sbom_writing": repeated_declarations_collapsed,
        "unresolved_declarations": len(unresolved),
        "dependencies": [asdict(d) for d in deps],
        "dependencies_enriched": [asdict(d) for d in missing],
        "unresolved": [asdict(u) for u in unresolved],
        "original_duplicate_packages": [asdict(d) for d in original_duplicate_packages],
        "original_duplicate_relationships": [asdict(d) for d in original_duplicate_relationships],
        "surface_duplicate_packages": [asdict(d) for d in surface_duplicate_packages],
        "surface_duplicate_relationships": [asdict(d) for d in surface_duplicate_relationships],
        "scope_summary": scope_summary,
        "skipped_dependencies": [
        {
            "dependency": asdict(s.dependency),
            "reason": s.reason,
            "matched_spdx_id": s.matched_spdx_id,
        }
        for s in skipped
        ],
    }

    log_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    return log_path

def pkgid_to_spdxid(sbom_data: dict[str, Any]) -> dict[str, str]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, str] = {}

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_pkg_id(pkg)
        spdxid = pkg.get("SPDXID")
        if identity and isinstance(spdxid, str):
            out[identity] = spdxid

    return out


def get_npm_spdxid(dep: Dependency, identity_to_spdxid: dict[str, str]) -> str | None:
    if dep.ecosystem != "npm" or not dep.version:
        return None

    declared_name = normalize_name(dep.name)
    declared_version = dep.version.lower()

    for identity, spdxid in identity_to_spdxid.items():
        parsed = get_npm_id(identity)
        if not parsed:
            continue

        sbom_name, sbom_version = parsed
        if sbom_name == declared_name and matches_npm_range(declared_version, sbom_version):
            return spdxid

    return None


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Scan a repository for direct/surface-level dependencies and add missing ones to a GitHub SPDX SBOM."
    )
    parser.add_argument("repo", help="Path to cloned repository")
    parser.add_argument("sbom", help="Path to GitHub-generated SPDX SBOM JSON")
    parser.add_argument(
        "--ecosystems",
        nargs="+",
        choices=list(SCANNERS.keys()),
        help="Optional list of ecosystems to scan. Default: all supported ecosystems.",
    )
    parser.add_argument(
        "--log",
        action="store_true",
        help="Write a surface dependency report to the repo's logs folder.",
    )

    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    sbom = Path(args.sbom).resolve()

    if not repo.exists():
        raise FileNotFoundError(f"Repo not found: {repo}")
    if not sbom.exists():
        raise FileNotFoundError(f"SBOM not found: {sbom}")

    deps, unresolved, gradle_repositories = scan_deps(repo, args.ecosystems)
    original_sbom_data = json.loads(sbom.read_text(encoding="utf-8"))
    identity_to_spdxid = pkgid_to_spdxid(original_sbom_data)
    sbom_keys = set(identity_to_spdxid.keys())
    missing, skipped = compare_to_sbom(deps, sbom_keys, identity_to_spdxid)

    unique_deps = get_unique_ids(deps)
    unique_missing = get_unique_ids(missing)
    repeated_declarations_collapsed = len(deps) - len(unique_deps)

    original_sbom_data = json.loads(sbom.read_text(encoding="utf-8"))
    original_duplicate_packages = find_dupe_pkgs(original_sbom_data)
    original_duplicate_relationships = get_dupe_relationships(original_sbom_data)

    surface_sbom_data, write_stats = add_missing_deps(sbom, deps, missing, skipped)
    surface_sbom_path = write_surface_sbom(sbom, surface_sbom_data)
    surface_duplicate_packages = find_dupe_pkgs(surface_sbom_data)
    surface_duplicate_relationships = get_dupe_relationships(surface_sbom_data)

    print(f"- Direct dependency declarations found: {len(deps)}")
    print(f"- Unique direct dependency packages found: {len(unique_deps)}")
    print(f"- Missing dependency declarations found: {len(missing)}")
    print(f"- Gradle repositories detected: {len(gradle_repositories)}")
    print(f"- Baseline packages repaired in SBOM: {write_stats.packages_repaired}")
    print(f"- Baseline packages removed from SBOM: {write_stats.packages_removed}")
    print(f"- Dependency declarations needing SBOM changes: {len(missing)}")
    print(f"- Existing packages enriched in SBOM: {write_stats.packages_enriched}")
    print(f"- New packages added to SBOM: {write_stats.packages_added}")
    print(f"- Repeated declarations collapsed during SBOM writing: {repeated_declarations_collapsed}")
    print(f"- Unresolved declarations: {len(unresolved)}")
    print(f"- Skipped declarations: {len(skipped)}")
    print(f"- Surface-level SBOM written to: {surface_sbom_path}")
    scope_summary: dict[str, int] = {}
    for dep in deps:
        category = dep_scope(dep.scope)
        scope_summary[category] = scope_summary.get(category, 0) + 1
    print(f"- Scope summary: {scope_summary}")

    if args.log:
        log_path = write_log(sbom, repo, deps, missing, skipped, unresolved, original_duplicate_packages, original_duplicate_relationships, surface_duplicate_packages, surface_duplicate_relationships, write_stats, gradle_repositories)       
        print(f"- Surface scan log written to: {log_path}")


if __name__ == "__main__":
    main()