from __future__ import annotations

import argparse
import json
import re
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any
from urllib.parse import quote, unquote


MAVEN_CENTRAL = "https://repo1.maven.org/maven2"
GOOGLE_MAVEN = "https://dl.google.com/dl/android/maven2"
JITPACK = "https://jitpack.io"
GRADLE_PLUGIN_PORTAL_MAVEN = "https://plugins.gradle.org/m2"
SPRING_RELEASE = "https://repo.spring.io/release"
SPRING_MILESTONE = "https://repo.spring.io/milestone"
ALIYUN_MAVEN_PUBLIC = "https://maven.aliyun.com/repository/public"
ALIYUN_MAVEN_CENTRAL = "https://maven.aliyun.com/repository/central"
HUAWEI_MAVEN = "https://repo.huaweicloud.com/repository/maven"

DEFAULT_MAVEN_REPOSITORIES = [
    MAVEN_CENTRAL,
    GOOGLE_MAVEN,
    JITPACK,
    GRADLE_PLUGIN_PORTAL_MAVEN,
    SPRING_RELEASE,
    SPRING_MILESTONE,
    ALIYUN_MAVEN_PUBLIC,
    ALIYUN_MAVEN_CENTRAL,
    HUAWEI_MAVEN,
]


@dataclass(frozen=True)
class Artifact:
    group: str
    artifact: str
    version: str
    scope: str = "runtime"
    source: str | None = None
    exclusions: frozenset[tuple[str, str]] = field(default_factory=frozenset)


@dataclass(frozen=True)
class ResolutionIssue:
    artifact: str
    reason: str


@dataclass(frozen=True)
class SkippedArtifact:
    artifact: str
    source: str | None
    scope: str
    reason: str


@dataclass(frozen=True)
class DependencyEdge:
    parent: str
    child: str


@dataclass(frozen=True)
class MavenModel:
    properties: dict[str, str]
    dependency_management: dict[tuple[str, str], str]
    repositories: list[str]
    issues: list[ResolutionIssue]


@dataclass(frozen=True)
class MavenPackageMetadata:
    artifact: str
    source_repository: str | None = None
    pom_url: str | None = None
    jar_url: str | None = None
    package_file_name: str | None = None
    homepage: str | None = None
    supplier: str | None = None
    license_declared: str | None = None
    copyright_text: str | None = None
    checksum_sha1: str | None = None


@dataclass(frozen=True)
class PackageValidationFinding:
    artifact: str
    spdx_id: str
    field: str
    action: str
    old_value: str | None
    new_value: str | None
    notes: str | None = None


EXCLUDED_MAVEN_TRANSITIVE_SCOPES = {"test", "provided", "optional", "system"}
POM_CACHE: dict[str, str] = {}
MODEL_CACHE: dict[str, MavenModel] = {}
METADATA_CACHE: dict[str, MavenPackageMetadata] = {}
ARTIFACT_REDIRECT_CACHE: dict[str, Artifact] = {}


# -------------------------
# Maven helpers
# -------------------------

def normalize_repo_url(url: str) -> str:
    return url.strip().rstrip("/")


def unique_repos(repositories: list[str] | None = None) -> list[str]:
    return list(dict.fromkeys(normalize_repo_url(r) for r in [*(repositories or []), *DEFAULT_MAVEN_REPOSITORIES] if isinstance(r, str) and r.strip()))


def maven_recurse(a: Artifact) -> tuple[bool, str | None]:
    scope_parts = {part.strip().lower() for part in a.scope.split(":") if part.strip()}

    blocked = scope_parts & EXCLUDED_MAVEN_TRANSITIVE_SCOPES
    if blocked:
        return False, f"Excluded Maven transitive scope: {', '.join(sorted(blocked))}"

    return True, None


def maven_url(repository: str, a: Artifact, extension: str = "pom") -> str:
    group_path = a.group.replace(".", "/")
    return f"{normalize_repo_url(repository)}/{group_path}/{a.artifact}/{a.version}/{a.artifact}-{a.version}.{extension}"


def get_text(url: str) -> str:
    if url in POM_CACHE:
        return POM_CACHE[url]

    with urllib.request.urlopen(url, timeout=20) as response:
        text = response.read().decode("utf-8", errors="replace")

    POM_CACHE[url] = text
    return text


def get_sha1_or_none(url: str) -> str | None:
    try:
        text = get_text(url)
    except Exception:
        return None
    if not text:
        return None
    m = re.search(r"\b[0-9a-fA-F]{40}\b", text)
    return m.group(0).lower() if m else None


_XML_ENTITY_RE = re.compile(r"&([A-Za-z][A-Za-z0-9_.:-]*);")
_BUILTIN_XML_ENTITIES = {"amp", "lt", "gt", "quot", "apos"}


def escape_xml(xml_text: str) -> str:
    return _XML_ENTITY_RE.sub(lambda m: m.group(0) if m.group(1) in _BUILTIN_XML_ENTITIES else f"&amp;{m.group(1)};", xml_text)


def parse_xml_lenient(xml_text: str) -> ET.Element:
    try:
        root = ET.fromstring(xml_text)
    except ET.ParseError:
        root = ET.fromstring(escape_xml(xml_text))
    strip_xml_ns(root)
    return root


def maven_coord_fallbacks(artifact: Artifact) -> list[Artifact]:
    candidates = [artifact]
    if (artifact.group.startswith("org.springframework.boot") and re.fullmatch(r"\d+\.\d+\.\d+", artifact.version or "")):
        candidates.append(Artifact(artifact.group, artifact.artifact, artifact.version + ".RELEASE", artifact.scope, artifact.source, artifact.exclusions))

    return candidates

def get_first_pom_dep(xml_text: str, source: Artifact) -> tuple[Artifact | None, list[ResolutionIssue]]:
    issues: list[ResolutionIssue] = []
    try:
        root = parse_xml_lenient(xml_text)
    except Exception as e:
        return None, [ResolutionIssue(coord_key(source), f"Could not parse plugin marker POM: {e}")]

    props: dict[str, str] = {
        "project.groupId": source.group,
        "project.artifactId": source.artifact,
        "project.version": source.version,
        "pom.groupId": source.group,
        "pom.artifactId": source.artifact,
        "pom.version": source.version,
    }
    props_node = root.find("properties")
    if props_node is not None:
        for child in list(props_node):
            if child.text:
                props[child.tag] = child.text.strip()

    dep = root.find("dependencies/dependency")
    if dep is None:
        return None, [ResolutionIssue(coord_key(source), "Gradle plugin marker POM had no implementation dependency")]

    group = resolve_maven_property(xml_text(dep, "groupId"), props)
    artifact_id = resolve_maven_property(xml_text(dep, "artifactId"), props)
    version = normalize_maven_ver(resolve_maven_property(xml_text(dep, "version"), props))
    scope = resolve_maven_property(xml_text(dep, "scope"), props) or source.scope

    if not group or not artifact_id or not version:
        return None, [ResolutionIssue(coord_key(source), f"Gradle plugin marker dependency unresolved: {group}:{artifact_id}:{version}")]

    return Artifact(group, artifact_id, version, scope=scope, source=coord_key(source)), issues


def resolve_gradle_plugin_marker(artifact: Artifact, repositories: list[str] | None = None) -> tuple[Artifact | None, list[ResolutionIssue], list[str]]:
    if not artifact.artifact.endswith(".gradle.plugin"):
        return None, [], unique_repos(repositories)

    searched: list[str] = []
    active_repos = unique_repos([GRADLE_PLUGIN_PORTAL_MAVEN, *(repositories or [])])
    for candidate in maven_coord_fallbacks(artifact):
        for repo in active_repos:
            url = maven_url(repo, candidate, "pom")
            searched.append(url)
            try:
                xml_text = get_text(url)
            except Exception:
                continue
            impl, issues = get_first_pom_dep(xml_text, candidate)
            if impl:
                ARTIFACT_REDIRECT_CACHE[coord_key(artifact)] = impl
                return impl, issues, active_repos
            return None, issues, active_repos

    return None, [ResolutionIssue(coord_key(artifact), "Could not resolve Gradle plugin marker from configured repositories. Searched: " + "; ".join(searched))], active_repos


def strip_xml_ns(root: ET.Element) -> None:
    for elem in root.iter():
        if "}" in elem.tag:
            elem.tag = elem.tag.split("}", 1)[1]


def xml_text(node: ET.Element | None, name: str) -> str | None:
    if node is None:
        return None
    value = node.findtext(name)
    return value.strip() if value else None


def coord_purl(a: Artifact) -> str:
    return f"pkg:maven/{a.group}/{a.artifact}@{a.version}"


def coord_key(a: Artifact) -> str:
    return f"pkg:maven/{a.group.lower()}/{a.artifact.lower()}@{a.version}"


def exclusion_matches(artifact: Artifact, exclusions: frozenset[tuple[str, str]] | set[tuple[str, str]]) -> bool:
    group = artifact.group.lower()
    artifact_id = artifact.artifact.lower()

    for ex_group, ex_artifact in exclusions:
        ex_group = (ex_group or "").lower()
        ex_artifact = (ex_artifact or "").lower()

        group_matches = ex_group in {"*", group}
        artifact_matches = ex_artifact in {"*", artifact_id}

        if group_matches and artifact_matches:
            return True

    return False


def coord_spdxid(a: Artifact) -> str:
    safe = re.sub(r"[^A-Za-z0-9.-]+", "-", f"maven-{a.group}-{a.artifact}-{a.version}")
    return f"SPDXRef-transitive-{safe}"


def normalize_maven_ver(version: str | None) -> str | None:
    if not version:
        return None

    version = version.strip()

    exact_range = re.fullmatch(r"\[([^,\[\]]+)\]", version)
    if exact_range:
        return exact_range.group(1).strip()

    if re.search(r"\$\{[^}]+}", version):
        return None

    return version


def find_missing_maven_ver(group: str, artifact_id: str, source_artifact: Artifact) -> str | None:
    if group == source_artifact.group:
        return source_artifact.version

    source_base = source_artifact.artifact
    for suffix in ("-spring-boot-starter", "-spring-boot3-starter", "-boot-starter", "-starter"):
        if source_base.endswith(suffix) and artifact_id == source_base[: -len(suffix)]:
            return source_artifact.version

    return None


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


def get_pom_repos(root: ET.Element, properties: dict[str, str]) -> list[str]:
    repositories: list[str] = []

    for container_name, child_name in (("repositories", "repository"), ("pluginRepositories", "pluginRepository")):
        container = root.find(container_name)
        if container is None:
            continue

        for repo_node in container.findall(child_name):
            url = resolve_maven_property(xml_text(repo_node, "url"), properties)
            if url:
                repositories.append(normalize_repo_url(url))

    return list(dict.fromkeys(repositories))


def get_maven_pom(artifact: Artifact, repositories: list[str] | None = None) -> tuple[str | None, str | None, str | None, list[ResolutionIssue]]:
    searched: list[str] = []
    errors: list[str] = []

    for candidate in maven_coord_fallbacks(artifact):
        for repository in unique_repos(repositories):
            url = maven_url(repository, candidate, "pom")
            searched.append(url)

            try:
                return get_text(url), repository, url, []
            except urllib.error.HTTPError as e:
                errors.append(f"{url} -> HTTP {e.code}")
            except Exception as e:
                errors.append(f"{url} -> {type(e).__name__}: {e}")

    note = "Could not fetch POM from configured Maven repositories. Searched: " + "; ".join(searched)
    if errors:
        note += ". Errors: " + "; ".join(errors[:8])
    return None, None, None, [ResolutionIssue(coord_key(artifact), note)]


# -------------------------
# Metadata enrichment / validation
# -------------------------

def license_name_to_spdx(raw: str | None) -> str | None:
    if not raw:
        return None

    value = raw.strip()
    lowered = value.lower()

    known = {
        "apache license, version 2.0": "Apache-2.0",
        "apache 2": "Apache-2.0",
        "apache-2.0": "Apache-2.0",
        "mit license": "MIT",
        "mit": "MIT",
        "bsd license": "BSD-3-Clause",
        "bsd 3-clause": "BSD-3-Clause",
        "bsd-3-clause": "BSD-3-Clause",
        "bsd-like": "NOASSERTION",
        "bsd": "NOASSERTION",
        "eclipse public license - v 1.0": "EPL-1.0",
        "eclipse public license 1.0": "EPL-1.0",
        "epl-1.0": "EPL-1.0",
        "common public license version 1.0": "CPL-1.0",
        "cpl-1.0": "CPL-1.0",
        "gnu lesser general public license": "LGPL-2.1-or-later",
    }

    for key, spdx in known.items():
        if key in lowered:
            return spdx

    return value


def get_maven_metadata(artifact: Artifact, repositories: list[str] | None = None) -> tuple[MavenPackageMetadata, list[ResolutionIssue]]:
    key = coord_key(artifact)
    if key in METADATA_CACHE:
        return METADATA_CACHE[key], []

    xml_text, repo_url, pom_url, issues = get_maven_pom(artifact, repositories)

    base_metadata = MavenPackageMetadata(
        artifact=key,
        source_repository=repo_url,
        pom_url=pom_url,
        jar_url=maven_url(repo_url, artifact, "jar") if repo_url else None,
        package_file_name=f"{artifact.artifact}-{artifact.version}.jar",
        checksum_sha1=get_sha1_or_none(maven_url(repo_url, artifact, "jar.sha1")) if repo_url else None,
    )

    if xml_text is None:
        METADATA_CACHE[key] = base_metadata
        return base_metadata, issues

    try:
        root = parse_xml_lenient(xml_text)
    except Exception as e:
        issue = ResolutionIssue(key, f"Could not parse POM while extracting metadata: {e}")
        METADATA_CACHE[key] = base_metadata
        return base_metadata, [*issues, issue]

    organization_name = xml_text(root.find("organization"), "name")
    developer_name = xml_text(root.find("developers/developer"), "name")
    developer_email = xml_text(root.find("developers/developer"), "email")
    supplier = None
    if organization_name:
        supplier = f"Organization: {organization_name}"
    elif developer_name and developer_email:
        supplier = f"Person: {developer_name} ({developer_email})"
    elif developer_name:
        supplier = f"Person: {developer_name}"

    license_name = xml_text(root.find("licenses/license"), "name")
    metadata = MavenPackageMetadata(
        artifact=key,
        source_repository=repo_url,
        pom_url=pom_url,
        jar_url=maven_url(repo_url, artifact, "jar") if repo_url else None,
        package_file_name=f"{artifact.artifact}-{artifact.version}.jar",
        homepage=xml_text(root, "url") or xml_text(root.find("scm"), "url"),
        supplier=supplier,
        license_declared=license_name_to_spdx(license_name),
        copyright_text="NOASSERTION",
        checksum_sha1=get_sha1_or_none(maven_url(repo_url, artifact, "jar.sha1")) if repo_url else None,
    )

    METADATA_CACHE[key] = metadata
    return metadata, issues


def missing_or_noassert(value: Any) -> bool:
    return value is None or value == "" or value == "NOASSERTION"


def set_pkg_field_from_metadata(pkg: dict[str, Any], spdx_id: str, artifact: Artifact, field_name: str, new_value: str | None, findings: list[PackageValidationFinding]) -> None:
    if not new_value:
        return

    old_value = pkg.get(field_name)
    artifact_id = coord_key(artifact)

    if missing_or_noassert(old_value):
        pkg[field_name] = new_value
        findings.append(PackageValidationFinding(
            artifact=artifact_id,
            spdx_id=spdx_id,
            field=field_name,
            action="filled",
            old_value=old_value if isinstance(old_value, str) else None,
            new_value=new_value,
        ))
    elif str(old_value) == new_value:
        findings.append(PackageValidationFinding(artifact=artifact_id, spdx_id=spdx_id, field=field_name, action="verified", old_value=str(old_value), new_value=new_value))
    else:
        findings.append(PackageValidationFinding(
            artifact=artifact_id,
            spdx_id=spdx_id,
            field=field_name,
            action="differs",
            old_value=str(old_value),
            new_value=new_value,
            notes="Existing SBOM value was preserved; registry/POM value is recorded for manual review.",
        ))


def enrich_pkg_with_maven_metadata(pkg: dict[str, Any], artifact: Artifact, metadata: MavenPackageMetadata, findings: list[PackageValidationFinding]) -> None:
    spdx_id = pkg.get("SPDXID")
    if not isinstance(spdx_id, str):
        spdx_id = coord_spdxid(artifact)
        pkg["SPDXID"] = spdx_id

    set_pkg_field_from_metadata(pkg, spdx_id, artifact, "packageFileName", metadata.package_file_name, findings)
    set_pkg_field_from_metadata(pkg, spdx_id, artifact, "downloadLocation", metadata.jar_url, findings)
    set_pkg_field_from_metadata(pkg, spdx_id, artifact, "homepage", metadata.homepage, findings)
    set_pkg_field_from_metadata(pkg, spdx_id, artifact, "supplier", metadata.supplier, findings)
    set_pkg_field_from_metadata(pkg, spdx_id, artifact, "licenseDeclared", metadata.license_declared, findings)
    set_pkg_field_from_metadata(pkg, spdx_id, artifact, "licenseConcluded", metadata.license_declared, findings)

    checksums = pkg.setdefault("checksums", [])
    if metadata.checksum_sha1 and not any(isinstance(c, dict) and c.get("algorithm") == "SHA1" and c.get("checksumValue") == metadata.checksum_sha1 for c in checksums):
        checksums.append({"algorithm": "SHA1", "checksumValue": metadata.checksum_sha1})
        findings.append(PackageValidationFinding(
            artifact=coord_key(artifact),
            spdx_id=spdx_id,
            field="checksums.SHA1",
            action="filled",
            old_value=None,
            new_value=metadata.checksum_sha1,
            notes="Fetched from Maven repository .jar.sha1 sidecar file.",
        ))
    elif not metadata.checksum_sha1 and not checksums:
        findings.append(PackageValidationFinding(
            artifact=coord_key(artifact),
            spdx_id=spdx_id,
            field="checksums",
            action="unresolved",
            old_value=None,
            new_value=None,
            notes="Checksum sidecar was not available or could not be fetched.",
        ))

    if metadata.copyright_text:
        set_pkg_field_from_metadata(pkg, spdx_id, artifact, "copyrightText", metadata.copyright_text, findings)

    refs = pkg.setdefault("externalRefs", [])
    wanted_purl = coord_purl(artifact)
    has_purl = False
    for ref in refs:
        if isinstance(ref, dict) and ref.get("referenceType") == "purl":
            if ref.get("referenceLocator") == wanted_purl:
                has_purl = True
            elif isinstance(ref.get("referenceLocator"), str) and ref.get("referenceLocator", "").startswith("pkg:maven/"):
                findings.append(PackageValidationFinding(
                    artifact=coord_key(artifact),
                    spdx_id=spdx_id,
                    field="externalRefs.purl",
                    action="differs",
                    old_value=ref.get("referenceLocator"),
                    new_value=wanted_purl,
                    notes="Existing Maven purl differs from resolved artifact identity.",
                ))

    if not has_purl:
        refs.append({"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": wanted_purl})
        findings.append(PackageValidationFinding(artifact=coord_key(artifact), spdx_id=spdx_id, field="externalRefs.purl", action="filled", old_value=None, new_value=wanted_purl))


# -------------------------
# Maven POM parsing / resolution
# -------------------------

def load_maven_model(artifact: Artifact, repositories: list[str] | None = None) -> MavenModel:
    active_repositories = unique_repos(repositories)
    cache_key = coord_key(artifact) + "|" + "|".join(active_repositories)
    if cache_key in MODEL_CACHE:
        return MODEL_CACHE[cache_key]

    xml_text, resolved_repo, _pom_url, issues = get_maven_pom(artifact, active_repositories)
    if xml_text is None:
        model = MavenModel({}, {}, active_repositories, issues)
        MODEL_CACHE[cache_key] = model
        return model

    try:
        root = parse_xml_lenient(xml_text)
    except Exception as e:
        model = MavenModel({}, {}, active_repositories, [ResolutionIssue(coord_key(artifact), f"POM XML parse failed: {e}")])
        MODEL_CACHE[cache_key] = model
        return model

    properties: dict[str, str] = {
        "project.groupId": artifact.group,
        "project.artifactId": artifact.artifact,
        "project.version": artifact.version,
        "pom.groupId": artifact.group,
        "pom.artifactId": artifact.artifact,
        "pom.version": artifact.version,
    }
    dependency_management: dict[tuple[str, str], str] = {}
    model_repositories = list(active_repositories)

    parent = root.find("parent")
    if parent is not None:
        parent_group = xml_text(parent, "groupId")
        parent_artifact = xml_text(parent, "artifactId")
        parent_version = normalize_maven_ver(xml_text(parent, "version"))

        if parent_group and parent_artifact and parent_version:
            parent_art = Artifact(parent_group, parent_artifact, parent_version)
            parent_model = load_maven_model(parent_art, model_repositories)
            properties.update(parent_model.properties)
            dependency_management.update(parent_model.dependency_management)
            issues.extend(parent_model.issues)
            model_repositories = unique_repos([*model_repositories, *parent_model.repositories])

    properties.update({
        "project.groupId": artifact.group,
        "project.artifactId": artifact.artifact,
        "project.version": artifact.version,
        "pom.groupId": artifact.group,
        "pom.artifactId": artifact.artifact,
        "pom.version": artifact.version,
    })

    props = root.find("properties")
    if props is not None:
        for child in list(props):
            if child.text:
                properties[child.tag] = child.text.strip()

    model_repositories = unique_repos([*model_repositories, *get_pom_repos(root, properties)])

    dm = root.find("dependencyManagement")
    if dm is not None:
        for dep in dm.findall(".//dependency"):
            group = resolve_maven_property(xml_text(dep, "groupId"), properties)
            artifact_id = resolve_maven_property(xml_text(dep, "artifactId"), properties)
            raw_version = resolve_maven_property(xml_text(dep, "version"), properties)
            version = normalize_maven_ver(raw_version)
            dep_type = resolve_maven_property(xml_text(dep, "type"), properties)
            scope = resolve_maven_property(xml_text(dep, "scope"), properties)
            if group and artifact_id and not version:
                version = find_missing_maven_ver(group, artifact_id, artifact)

            if dep_type == "pom" and scope == "import":
                if group and artifact_id and version:
                    bom_artifact = Artifact(group, artifact_id, version)
                    bom_model = load_maven_model(bom_artifact, model_repositories)
                    dependency_management.update(bom_model.dependency_management)
                    issues.extend(bom_model.issues)
                    model_repositories = unique_repos([*model_repositories, *bom_model.repositories])
                else:
                    issues.append(ResolutionIssue(coord_key(artifact), f"Unresolved BOM import: {group}:{artifact_id}:{version}"))
                continue

            if group and artifact_id and version:
                dependency_management[(group, artifact_id)] = version

    model = MavenModel(properties, dependency_management, model_repositories, issues)
    MODEL_CACHE[cache_key] = model
    return model


def parse_pom_xml(
    xml_text: str,
    source_artifact: Artifact,
    inherited_properties: dict[str, str],
    inherited_dependency_management: dict[tuple[str, str], str],
) -> tuple[list[Artifact], list[ResolutionIssue]]:
    issues: list[ResolutionIssue] = []
    deps: list[Artifact] = []

    try:
        root = parse_xml_lenient(xml_text)
    except Exception as e:
        return [], [ResolutionIssue(coord_key(source_artifact), f"POM XML parse failed: {e}")]

    properties: dict[str, str] = dict(inherited_properties)
    properties.update({
        "project.groupId": source_artifact.group,
        "project.artifactId": source_artifact.artifact,
        "project.version": source_artifact.version,
        "pom.groupId": source_artifact.group,
        "pom.artifactId": source_artifact.artifact,
        "pom.version": source_artifact.version,
    })

    props = root.find("properties")
    if props is not None:
        for child in list(props):
            if child.text:
                properties[child.tag] = child.text.strip()

    dependency_management: dict[tuple[str, str], str] = dict(inherited_dependency_management)

    dependencies = root.find("dependencies")
    if dependencies is None:
        return deps, issues

    for dep in dependencies.findall("dependency"):
        group = resolve_maven_property(xml_text(dep, "groupId"), properties)
        artifact_id = resolve_maven_property(xml_text(dep, "artifactId"), properties)
        version = resolve_maven_property(xml_text(dep, "version"), properties)
        scope = resolve_maven_property(xml_text(dep, "scope"), properties) or "runtime"
        optional = resolve_maven_property(xml_text(dep, "optional"), properties)

        if not group or not artifact_id:
            issues.append(ResolutionIssue(coord_key(source_artifact), f"Dependency missing group/artifact in {coord_key(source_artifact)}"))
            continue

        if not version:
            version = dependency_management.get((group, artifact_id))
        if not version:
            version = find_missing_maven_ver(group, artifact_id, source_artifact)

        version = normalize_maven_ver(version)
        if not version:
            issues.append(ResolutionIssue(coord_key(source_artifact), f"Missing or unresolved version for dependency {group}:{artifact_id}"))
            continue

        exclusions: set[tuple[str, str]] = set()
        exclusions_node = dep.find("exclusions")
        if exclusions_node is not None:
            for exclusion in exclusions_node.findall("exclusion"):
                ex_group = resolve_maven_property(xml_text(exclusion, "groupId"), properties)
                ex_artifact = resolve_maven_property(xml_text(exclusion, "artifactId"), properties)
                if ex_group and ex_artifact:
                    exclusions.add((ex_group.lower(), ex_artifact.lower()))

        deps.append(Artifact(
            group=group,
            artifact=artifact_id,
            version=version,
            scope=f"{scope}{':optional' if optional == 'true' else ''}",
            source=coord_key(source_artifact),
            exclusions=frozenset(exclusions),
        ))

    return deps, issues


def resolve_maven_coord(artifact: Artifact, repositories: list[str] | None = None) -> tuple[list[Artifact], list[ResolutionIssue], list[str]]:
    marker_impl, marker_issues, marker_repos = resolve_gradle_plugin_marker(artifact, repositories)
    if marker_impl is not None:
        return [marker_impl], marker_issues, marker_repos

    model = load_maven_model(artifact, repositories)
    xml_text, _resolved_repo, _pom_url, fetch_issues = get_maven_pom(artifact, model.repositories)
    if xml_text is None:
        return [], fetch_issues + model.issues + marker_issues, model.repositories

    deps, parse_issues = parse_pom_xml(xml_text, artifact, model.properties, model.dependency_management)

    return deps, marker_issues + fetch_issues + model.issues + parse_issues, model.repositories


# -------------------------
# SBOM parsing / writing
# -------------------------

def get_maven_coords(sbom_data: dict[str, Any]) -> list[Artifact]:
    sbom = sbom_data.get("sbom", sbom_data)
    artifacts: list[Artifact] = []

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        for ref in pkg.get("externalRefs", []) or []:
            loc = ref.get("referenceLocator")
            if not isinstance(loc, str):
                continue

            if not loc.startswith("pkg:maven/") or "@" not in loc:
                continue

            body = loc[len("pkg:maven/"):].split("?", 1)[0]
            gav, version = body.rsplit("@", 1)

            parts = gav.split("/")
            if len(parts) < 2:
                continue

            group = ".".join(parts[:-1])
            artifact = parts[-1]

            artifacts.append(Artifact(group, artifact, version, source="surface_sbom"))

    return artifacts


def coord_to_spdx_pkg(a: Artifact, metadata: MavenPackageMetadata | None = None) -> dict[str, Any]:
    package = {
        "name": f"{a.group}:{a.artifact}",
        "SPDXID": coord_spdxid(a),
        "versionInfo": a.version,
        "downloadLocation": metadata.jar_url if metadata and metadata.jar_url else "NOASSERTION",
        "filesAnalyzed": False,
        "checksums": ([{"algorithm": "SHA1", "checksumValue": metadata.checksum_sha1}] if metadata and metadata.checksum_sha1 else []),
        "licenseConcluded": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "licenseDeclared": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "copyrightText": metadata.copyright_text if metadata and metadata.copyright_text else "NOASSERTION",
        "externalRefs": [{"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": coord_purl(a)}],
    }

    if metadata:
        if metadata.package_file_name:
            package["packageFileName"] = metadata.package_file_name
        if metadata.homepage:
            package["homepage"] = metadata.homepage
        if metadata.supplier:
            package["supplier"] = metadata.supplier

    return package


def get_maven_id(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if isinstance(loc, str) and loc.startswith("pkg:maven/") and "@" in loc:
            body = loc[len("pkg:maven/"):].split("?", 1)[0]
            gav, version = body.rsplit("@", 1)
            return f"pkg:maven/{gav.lower()}@{version}"

    name = pkg.get("name")
    version = pkg.get("versionInfo")

    if not isinstance(name, str) or ":" not in name:
        return None
    if not isinstance(version, str) or not version or version == "NOASSERTION":
        return None

    group, artifact = name.split(":", 1)
    return f"pkg:maven/{group.lower()}/{artifact.lower()}@{version}"


def build_id_to_spdxid(sbom_data: dict[str, Any]) -> dict[str, str]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, str] = {}

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        identity = get_maven_id(pkg)
        spdx_id = pkg.get("SPDXID")

        if identity and isinstance(spdx_id, str):
            out[identity] = spdx_id

    return out


def build_id_to_pkg(sbom_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, dict[str, Any]] = {}

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_maven_id(pkg)
        if identity:
            out[identity] = pkg

    return out


def parse_maven_purl(locator: str) -> tuple[str, str, str | None] | None:
    if not isinstance(locator, str) or not locator.startswith("pkg:maven/"):
        return None

    body = locator[len("pkg:maven/"):].split("?", 1)[0]
    version = None
    if "@" in body:
        gav, version = body.rsplit("@", 1)
    else:
        gav = body

    parts = gav.split("/")
    if len(parts) < 2:
        return None

    group = ".".join(parts[:-1])
    artifact = parts[-1]
    return group, artifact, version


def infer_unversioned_pkgs(sbom_data: dict[str, Any], discovered: dict[str, Artifact]) -> list[PackageValidationFinding]:
    sbom = sbom_data.get("sbom", sbom_data)
    findings: list[PackageValidationFinding] = []

    exact_versions: dict[tuple[str, str], str] = {}
    group_versions: dict[str, dict[str, int]] = {}

    for artifact in discovered.values():
        ga = (artifact.group.lower(), artifact.artifact.lower())
        exact_versions.setdefault(ga, artifact.version)
        versions = group_versions.setdefault(artifact.group.lower(), {})
        versions[artifact.version] = versions.get(artifact.version, 0) + 1

    dominant_group_version: dict[str, str] = {}
    for group, counts in group_versions.items():
        dominant_group_version[group] = max(counts.items(), key=lambda item: item[1])[0]

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        refs = pkg.get("externalRefs", []) or []
        for ref in refs:
            if not isinstance(ref, dict):
                continue

            loc = ref.get("referenceLocator")
            parsed = parse_maven_purl(loc) if isinstance(loc, str) else None
            if not parsed:
                continue

            group, artifact_id, version = parsed
            if version:
                continue

            current_version = pkg.get("versionInfo")
            if isinstance(current_version, str) and current_version and current_version != "NOASSERTION":
                inferred = current_version
            else:
                inferred = exact_versions.get((group.lower(), artifact_id.lower()))

            if not inferred and group.lower() == "org.springframework.boot":
                inferred = dominant_group_version.get("org.springframework.boot")

            if not inferred:
                continue

            new_locator = f"pkg:maven/{group}/{artifact_id}@{inferred}"
            old_locator = loc
            ref["referenceLocator"] = new_locator
            old_version = pkg.get("versionInfo")
            pkg["versionInfo"] = inferred

            spdx_id = pkg.get("SPDXID") if isinstance(pkg.get("SPDXID"), str) else "NOASSERTION"
            findings.append(PackageValidationFinding(
                artifact=new_locator,
                spdx_id=spdx_id,
                field="versionInfo/externalRefs.referenceLocator",
                action="filled",
                old_value=f"versionInfo={old_version}; purl={old_locator}",
                new_value=f"versionInfo={inferred}; purl={new_locator}",
                notes="Inferred missing Maven package version from resolved SBOM context before metadata enrichment.",
            ))

    return findings


def has_relationship(sbom_data: dict[str, Any], src: str, dst: str, rel_type: str) -> bool:
    sbom = sbom_data.get("sbom", sbom_data)

    for rel_obj in sbom.get("relationships", []) or []:
        if (rel_obj.get("spdxElementId") == src and rel_obj.get("relatedSpdxElement") == dst and rel_obj.get("relationshipType") == rel_type):
            return True

    return False


def add_maven_transitives(
    sbom_data: dict[str, Any],
    discovered: dict[str, Artifact],
    edges: list[DependencyEdge],
    repositories_by_artifact: dict[str, list[str]],
) -> tuple[dict[str, Any], list[PackageValidationFinding], list[ResolutionIssue]]:
    sbom = sbom_data.get("sbom", sbom_data)
    sbom.setdefault("packages", [])
    sbom.setdefault("relationships", [])

    findings: list[PackageValidationFinding] = []
    metadata_issues: list[ResolutionIssue] = []

    findings.extend(infer_unversioned_pkgs(sbom_data, discovered))

    identity_to_spdxid = build_id_to_spdxid(sbom_data)
    identity_to_package = build_id_to_pkg(sbom_data)

    for key, artifact in discovered.items():
        metadata, issues = get_maven_metadata(artifact, repositories_by_artifact.get(key))
        metadata_issues.extend(issues)

        if key in identity_to_spdxid:
            existing_pkg = identity_to_package.get(key)
            existing_spdx = identity_to_spdxid[key]
            findings.append(PackageValidationFinding(
                artifact=key,
                spdx_id=existing_spdx,
                field="package",
                action="existed",
                old_value=coord_purl(artifact),
                new_value=coord_purl(artifact),
                notes="Package was already present in the input SBOM; enrichment/validation was attempted.",
            ))
            if existing_pkg is not None:
                enrich_pkg_with_maven_metadata(existing_pkg, artifact, metadata, findings)
            continue

        package = coord_to_spdx_pkg(artifact, metadata)
        sbom["packages"].append(package)
        identity_to_spdxid[key] = package["SPDXID"]
        identity_to_package[key] = package
        findings.append(PackageValidationFinding(
            artifact=key,
            spdx_id=package["SPDXID"],
            field="package",
            action="added",
            old_value=None,
            new_value=coord_purl(artifact),
            notes="Package added from Maven transitive resolution.",
        ))

    for edge in edges:
        parent_spdxid = identity_to_spdxid.get(edge.parent)
        child_spdxid = identity_to_spdxid.get(edge.child)

        if not parent_spdxid or not child_spdxid:
            continue

        if has_relationship(sbom_data, parent_spdxid, child_spdxid, "DEPENDS_ON"):
            continue

        sbom["relationships"].append({"spdxElementId": parent_spdxid, "relatedSpdxElement": child_spdxid, "relationshipType": "DEPENDS_ON"})

    return sbom_data, findings, metadata_issues


# -------------------------
# npm / JavaScript helpers
# -------------------------

NPM_REGISTRY = "https://registry.npmjs.org"
NPM_PACKUMENT_CACHE: dict[str, dict[str, Any]] = {}


@dataclass(frozen=True)
class NpmArtifact:
    name: str
    version: str
    scope: str = "runtime"
    source: str | None = None
    requested: str | None = None


@dataclass(frozen=True)
class NpmPackageMetadata:
    artifact: str
    registry_url: str | None = None
    tarball_url: str | None = None
    package_file_name: str | None = None
    homepage: str | None = None
    supplier: str | None = None
    license_declared: str | None = None
    checksum_sha1: str | None = None


NPM_DEPENDENCY_FIELDS: tuple[tuple[str, str], ...] = (("dependencies", "runtime"), ("optionalDependencies", "optional"))

def canonical_npm_name(name: str) -> str:
    name = unquote((name or "").strip())
    if name.startswith("pkg:npm/"):
        name = name[len("pkg:npm/"):]
    if "?" in name:
        name = name.split("?", 1)[0]
    if "@" in name:
        if name.startswith("@"):
            second_at = name.find("@", 1)
            if second_at > 0:
                name = name[:second_at]
        else:
            name = name.rsplit("@", 1)[0]
    return name


def npm_purl(name: str, version: str) -> str:
    return f"pkg:npm/{quote(canonical_npm_name(name), safe='/')}@{version}"


def npm_identity(name: str, version: str) -> str:
    return npm_purl(canonical_npm_name(name).lower(), version)

def npm_pkg_key(a: NpmArtifact) -> str:
    return npm_identity(a.name, a.version)


def npm_pkg_purl(a: NpmArtifact) -> str:
    return npm_purl(a.name, a.version)


def npm_pkg_spdxid(a: NpmArtifact) -> str:
    safe_name = canonical_npm_name(a.name)
    safe = re.sub(r"[^A-Za-z0-9.-]+", "-", f"npm-{safe_name}-{a.version}").strip("-")
    return f"SPDXRef-transitive-{safe}"


def npm_registry_pkg_url(package_name: str) -> str:
    package_name = canonical_npm_name(package_name)
    return f"{NPM_REGISTRY}/{urllib.parse.quote(package_name, safe='')}"


def npm_registry_ver_url(package_name: str, version: str) -> str:
    return f"{npm_registry_pkg_url(package_name)}/{urllib.parse.quote(version, safe='')}"


JSON_TIMEOUT_SECONDS = 8

def get_json(url: str) -> dict[str, Any]:
    req = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": "RestoreSBOM-transitive-finder/1.0"})
    with urllib.request.urlopen(req, timeout=JSON_TIMEOUT_SECONDS) as response:
        return json.loads(response.read().decode("utf-8", errors="replace"))


def get_npm_packument(package_name: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    package_name = canonical_npm_name(package_name)
    key = package_name.lower()
    if key in NPM_PACKUMENT_CACHE:
        return NPM_PACKUMENT_CACHE[key], []

    candidates = list(dict.fromkeys([package_name, package_name.lower()]))
    errors: list[str] = []
    for candidate in candidates:
        url = npm_registry_pkg_url(candidate)
        try:
            data = get_json(url)
            NPM_PACKUMENT_CACHE[key] = data
            return data, []
        except urllib.error.HTTPError as e:
            errors.append(f"{url} -> HTTP {e.code}")
        except Exception as e:
            errors.append(f"{url} -> {type(e).__name__}: {e}")

    return None, [ResolutionIssue(npm_purl(package_name, "UNKNOWN"), "npm registry fetch failed. Tried: " + "; ".join(errors))]

def normalize_npm_license(value: str | None) -> str:
    normalized = license_name_to_spdx(value)
    if not normalized:
        return "NOASSERTION"
    if normalized.strip().lower() in {"bsd-like", "bsd"}:
        return "NOASSERTION"
    return normalized

def parse_semver_core(version: str) -> tuple[int, int, int, str] | None:
    m = re.match(r"^v?(\d+)\.(\d+)\.(\d+)([-+].*)?$", version.strip())
    if not m:
        return None
    return int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4) or ""


def is_npm_prerelease(version: str) -> bool:
    parsed = parse_semver_core(version)
    if not parsed:
        return False
    return parsed[3].startswith("-")


def range_has_prerelease(range_spec: str | None) -> bool:
    if not range_spec:
        return False
    return bool(re.search(r"\d+\.\d+\.\d+-[0-9A-Za-z]", range_spec))


def semver_sort_key(version: str) -> tuple[int, int, int, int, list[Any]]:
    parsed = parse_semver_core(version)
    if not parsed:
        return (-1, -1, -1, -1, [version])

    major, minor, patch, suffix = parsed
    stable = 1 if not suffix.startswith("-") else 0

    prerelease_key: list[Any] = []
    if suffix.startswith("-"):
        prerelease = suffix[1:].split("+", 1)[0]
        for part in re.split(r"[.-]", prerelease):
            if part.isdigit():
                prerelease_key.append((0, int(part)))
            else:
                prerelease_key.append((1, part))

    return major, minor, patch, stable, prerelease_key


def compare_semver(a: str, b: str) -> int:
    ka = semver_sort_key(a)
    kb = semver_sort_key(b)
    return (ka > kb) - (ka < kb)


def normalize_partial_ver(version: str) -> str:
    version = version.strip()
    if version.startswith("v"):
        version = version[1:]

    if re.match(r"^\d+$", version):
        return f"{version}.0.0"
    if re.match(r"^\d+\.\d+$", version):
        return f"{version}.0"
    return version


def is_non_npm_range(range_spec: str | None) -> bool:
    if not range_spec:
        return False
    return range_spec.strip().startswith(("file:", "link:", "workspace:", "git+", "git://", "github:", "http://", "https://"))


def npm_ver_matches_comparator(version: str, comparator: str) -> bool:
    comparator = comparator.strip()
    if not comparator or comparator in {"*", "x", "X"}:
        return True

    if comparator.lower() in {"latest"}:
        return True

    m = re.match(r"^(>=|<=|>|<|=)?\s*v?([^\s]+)$", comparator)
    if not m:
        return False

    op = m.group(1) or "="
    target = m.group(2).strip()

    if not target:
        return False

    if re.search(r"(^|\.)(x|X|\*)($|\.)", target):
        parts = re.split(r"\.", target)
        try:
            major = int(parts[0]) if parts[0] not in {"x", "X", "*"} else None
            minor = int(parts[1]) if len(parts) > 1 and parts[1] not in {"x", "X", "*"} else None
        except ValueError:
            return False

        parsed = parse_semver_core(version)
        if not parsed:
            return False

        vmaj, vmin, _vpatch, _suffix = parsed
        if major is None:
            return True
        if vmaj != major:
            return False
        if minor is None:
            return True
        return vmin == minor

    target = normalize_partial_ver(target)
    if not parse_semver_core(target):
        return False

    cmp = compare_semver(version, target)

    if op == "=":
        raw_target = m.group(2).strip().lstrip("v")
        if rust_ver_parts(raw_target) < 3:
            return rust_ver_matches_range(version, raw_target)
        return cmp == 0
    if op == ">=":
        return cmp >= 0
    if op == "<=":
        return cmp <= 0
    if op == ">":
        return cmp > 0
    if op == "<":
        return cmp < 0

    return False


def expand_caret(version: str) -> list[str]:
    original = normalize_partial_ver(version)
    parsed = parse_semver_core(original)
    if not parsed:
        return [version]

    major, minor, patch, _suffix = parsed
    lower = f">={original}"

    if major > 0:
        upper = f"<{major + 1}.0.0"
    elif minor > 0:
        upper = f"<0.{minor + 1}.0"
    else:
        upper = f"<0.0.{patch + 1}"

    return [lower, upper]


def expand_tilde(version: str) -> list[str]:
    original = normalize_partial_ver(version)
    parsed = parse_semver_core(original)
    if not parsed:
        return [version]

    major, minor, patch, _suffix = parsed
    return [f">={original}", f"<{major}.{minor + 1}.0"]


def normalize_npm_range(range_spec: str) -> list[list[str]]:
    if not range_spec or range_spec.strip() in {"*", "latest"}:
        return [["*"]]

    range_spec = re.sub(r"(?<![<>=])\b(v)(?=\d)", "", range_spec.strip())
    range_spec = re.sub(r"(>=|<=|>|<|=)\s+(?=\d|v)", r"\1", range_spec)

    groups: list[list[str]] = []

    for raw_group in range_spec.split("||"):
        group = raw_group.strip()
        if not group:
            continue

        hyphen = re.match(r"^v?([0-9][^\s]*)\s+-\s+v?([0-9][^\s]*)$", group)
        if hyphen:
            groups.append([f">={normalize_partial_ver(hyphen.group(1))}", f"<={normalize_partial_ver(hyphen.group(2))}"])
            continue

        comparators: list[str] = []

        for token in re.split(r"\s+", group):
            token = token.strip().strip(",")
            if not token:
                continue

            if token.startswith("^"):
                comparators.extend(expand_caret(token[1:]))
            elif token.startswith("~"):
                comparators.extend(expand_tilde(token[1:]))
            elif re.match(r"^\d+$", token):
                major = int(token)
                comparators.extend([f">={major}.0.0", f"<{major + 1}.0.0"])
            elif re.match(r"^\d+\.\d+$", token):
                major, minor = token.split(".")
                comparators.extend([f">={major}.{minor}.0", f"<{major}.{int(minor) + 1}.0"])
            elif re.match(r"^\d+\.\d+\.\d+(?:[-+].*)?$", token):
                comparators.append(f"={token}")
            else:
                comparators.append(token)

        groups.append(comparators or ["*"])

    return groups or [["*"]]


def npm_ver_matches_range(version: str, range_spec: str) -> bool:
    if range_spec in {None, "", "*", "latest"}:  # type: ignore[comparison-overlap]
        return True

    if range_spec.startswith("npm:"):
        return False

    if is_non_npm_range(range_spec):
        return False

    for group in normalize_npm_range(range_spec):
        if all(npm_ver_matches_comparator(version, comp) for comp in group):
            return True

    return False


def resolve_npm_ver(package_name: str, range_spec: str | None) -> tuple[str | None, list[ResolutionIssue]]:
    packument, issues = get_npm_packument(package_name)
    if not packument:
        return None, issues

    versions = packument.get("versions")
    if not isinstance(versions, dict) or not versions:
        return None, [*issues, ResolutionIssue(npm_purl(package_name, "UNKNOWN"), "npm packument contained no versions")]

    dist_tags = packument.get("dist-tags") if isinstance(packument.get("dist-tags"), dict) else {}
    requested = (range_spec or "latest").strip()

    if is_non_npm_range(requested):
        return None, [*issues, ResolutionIssue(npm_purl(package_name, "UNKNOWN"), f"Skipped non-registry npm dependency range: {requested}")]

    if requested in dist_tags:
        candidate = dist_tags.get(requested)
        if isinstance(candidate, str) and candidate in versions:
            return candidate, issues

    if requested in versions:
        return requested, issues

    valid_versions = [v for v in versions.keys() if isinstance(v, str) and parse_semver_core(v)]

    if not valid_versions:
        return None, [*issues, ResolutionIssue(npm_purl(package_name, "UNKNOWN"), f"No semver versions available to satisfy range {requested}")]

    allow_prerelease = range_has_prerelease(requested)

    satisfying = [v for v in valid_versions if npm_ver_matches_range(v, requested) and (allow_prerelease or not is_npm_prerelease(v))]

    if satisfying:
        return sorted(satisfying, key=semver_sort_key)[-1], issues

    return None, [*issues, ResolutionIssue(npm_purl(package_name, "UNKNOWN"), f"Could not resolve npm version range: {requested}")]


def get_npm_version_metadata(package_name: str, version: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    packument, issues = get_npm_packument(package_name)
    if not packument:
        return None, issues

    versions = packument.get("versions")
    if isinstance(versions, dict) and isinstance(versions.get(version), dict):
        return versions[version], issues

    url = npm_registry_ver_url(package_name, version)
    try:
        return get_json(url), issues
    except Exception as e:
        return None, [*issues, ResolutionIssue(npm_purl(package_name, version), f"npm version metadata fetch failed: {type(e).__name__}: {e}")]


def parse_npm_dep(raw_name: str, raw_range: Any) -> tuple[str, str | None, list[ResolutionIssue]]:
    issues: list[ResolutionIssue] = []
    dep_name = canonical_npm_name(raw_name)
    dep_range = str(raw_range).strip() if raw_range is not None else "latest"

    if dep_range.startswith("npm:"):
        alias_body = dep_range[len("npm:"):]
        if alias_body.startswith("@"):
            second_at = alias_body.find("@", 1)
            if second_at > 0:
                dep_name = alias_body[:second_at]
                dep_range = alias_body[second_at + 1:] or "latest"
            else:
                dep_name = alias_body
                dep_range = "latest"
        elif "@" in alias_body:
            dep_name, dep_range = alias_body.rsplit("@", 1)
            dep_range = dep_range or "latest"
        else:
            dep_name = alias_body
            dep_range = "latest"

    dep_name = canonical_npm_name(dep_name)
    if dep_range.startswith(("file:", "link:", "workspace:")):
        issues.append(ResolutionIssue(npm_purl(dep_name, "UNKNOWN"), f"Skipped local/workspace npm dependency range: {dep_range}"))
        return dep_name, None, issues

    if is_non_npm_range(dep_range):
        issues.append(ResolutionIssue(npm_purl(dep_name, "UNKNOWN"), f"Skipped non-registry npm dependency range: {dep_range}"))
        return dep_name, None, issues

    return dep_name, dep_range, issues


def resolve_npm_pkg(artifact: NpmArtifact) -> tuple[list[NpmArtifact], list[ResolutionIssue]]:
    metadata, issues = get_npm_version_metadata(artifact.name, artifact.version)
    if metadata is None:
        return [], issues

    children: list[NpmArtifact] = []
    peer_metadata = metadata.get("peerDependenciesMeta") if isinstance(metadata.get("peerDependenciesMeta"), dict) else {}
    for field_name, scope in NPM_DEPENDENCY_FIELDS:
        deps = metadata.get(field_name)
        if not isinstance(deps, dict):
            continue
        for raw_name, raw_range in deps.items():
            if not isinstance(raw_name, str):
                continue
            if field_name == "peerDependencies":
                metadata_for_dep = peer_metadata.get(raw_name) if isinstance(peer_metadata, dict) else None
                if isinstance(metadata_for_dep, dict) and metadata_for_dep.get("optional") is True:
                    issues.append(ResolutionIssue(npm_pkg_key(artifact), f"Skipped optional npm peer dependency {raw_name}@{raw_range}"))
                    continue
            dep_name, dep_range, parse_issues = parse_npm_dep(raw_name, raw_range)
            issues.extend(parse_issues)
            if not dep_range:
                continue
            dep_version, version_issues = resolve_npm_ver(dep_name, dep_range)
            issues.extend(version_issues)
            if dep_version:
                children.append(NpmArtifact(name=dep_name, version=dep_version, scope=scope, source=npm_pkg_key(artifact), requested=str(raw_range) if raw_range is not None else None))

    return children, issues

def get_npm_metadata_from_registry(artifact: NpmArtifact) -> tuple[NpmPackageMetadata, list[ResolutionIssue]]:
    key = npm_pkg_key(artifact)
    artifact = NpmArtifact(canonical_npm_name(artifact.name), artifact.version, artifact.scope, artifact.source, artifact.requested)
    metadata, issues = get_npm_version_metadata(artifact.name, artifact.version)
    if metadata is None:
        return NpmPackageMetadata(artifact=key, registry_url=npm_registry_ver_url(artifact.name, artifact.version)), issues

    dist = metadata.get("dist") if isinstance(metadata.get("dist"), dict) else {}
    author = metadata.get("author")
    supplier = None
    if isinstance(author, dict):
        name = author.get("name")
        email = author.get("email")
        if isinstance(name, str) and isinstance(email, str):
            supplier = f"Person: {name} ({email})"
        elif isinstance(name, str):
            supplier = f"Person: {name}"
    elif isinstance(author, str) and author.strip():
        supplier = f"Person: {author.strip()}"

    homepage = metadata.get("homepage")
    if not isinstance(homepage, str) or not homepage:
        repo = metadata.get("repository")
        if isinstance(repo, dict) and isinstance(repo.get("url"), str):
            homepage = repo.get("url")
        else:
            homepage = None

    license_declared = metadata.get("license")
    if isinstance(license_declared, dict):
        license_declared = license_declared.get("type")
    if not isinstance(license_declared, str):
        license_declared = None

    tarball = dist.get("tarball") if isinstance(dist.get("tarball"), str) else None
    shasum = dist.get("shasum") if isinstance(dist.get("shasum"), str) and re.fullmatch(r"[0-9a-fA-F]{40}", dist.get("shasum")) else None
    safe_filename_name = artifact.name.replace("/", "-").replace("@", "")

    return NpmPackageMetadata(
        artifact=key,
        registry_url=npm_registry_ver_url(artifact.name, artifact.version),
        tarball_url=tarball,
        package_file_name=f"{safe_filename_name}-{artifact.version}.tgz",
        homepage=homepage,
        supplier=supplier,
        license_declared=normalize_npm_license(license_declared),
        checksum_sha1=shasum.lower() if isinstance(shasum, str) else None,
    ), issues


def get_npm_pkgs(sbom_data: dict[str, Any]) -> list[NpmArtifact]:
    sbom = sbom_data.get("sbom", sbom_data)
    artifacts: list[NpmArtifact] = []

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        for ref in pkg.get("externalRefs", []) or []:
            loc = ref.get("referenceLocator")
            if not isinstance(loc, str) or not loc.startswith("pkg:npm/") or "@" not in loc:
                continue
            body = loc[len("pkg:npm/"):].split("?", 1)[0]
            name_part, version = body.rsplit("@", 1)
            package_name = canonical_npm_name(name_part)
            if package_name and version:
                artifacts.append(NpmArtifact(package_name, version, source="surface_sbom"))

    return artifacts


def get_npm_id(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if isinstance(loc, str) and loc.startswith("pkg:npm/") and "@" in loc:
            body = loc[len("pkg:npm/"):].split("?", 1)[0]
            name, version = body.rsplit("@", 1)
            return npm_identity(name, version)
    return None


def build_npm_id_to_spdxid(sbom_data: dict[str, Any]) -> dict[str, str]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, str] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_npm_id(pkg)
        spdx_id = pkg.get("SPDXID")
        if identity and isinstance(spdx_id, str):
            out[identity] = spdx_id
    return out


def build_npm_id_to_pkg(sbom_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, dict[str, Any]] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_npm_id(pkg)
        if identity:
            out[identity] = pkg
    return out


def npm_pkg_to_spdx_pkg(a: NpmArtifact, metadata: NpmPackageMetadata | None = None) -> dict[str, Any]:
    a = NpmArtifact(canonical_npm_name(a.name), a.version, a.scope, a.source, a.requested)
    package = {
        "name": a.name,
        "SPDXID": npm_pkg_spdxid(a),
        "versionInfo": a.version,
        "downloadLocation": metadata.tarball_url if metadata and metadata.tarball_url else "NOASSERTION",
        "filesAnalyzed": False,
        "checksums": ([{"algorithm": "SHA1", "checksumValue": metadata.checksum_sha1}] if metadata and metadata.checksum_sha1 else []),
        "licenseConcluded": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "licenseDeclared": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "copyrightText": "NOASSERTION",
        "externalRefs": [{"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": npm_pkg_purl(a)}],
    }
    if metadata:
        if metadata.package_file_name:
            package["packageFileName"] = metadata.package_file_name
        if metadata.homepage:
            package["homepage"] = metadata.homepage
        if metadata.supplier:
            package["supplier"] = metadata.supplier
    return package


def set_pkg_field_from_registry(pkg: dict[str, Any], spdx_id: str, artifact_id: str, field_name: str, new_value: str | None, findings: list[PackageValidationFinding]) -> None:
    if not new_value:
        return
    old_value = pkg.get(field_name)
    if missing_or_noassert(old_value):
        pkg[field_name] = new_value
        findings.append(PackageValidationFinding(
            artifact=artifact_id,
            spdx_id=spdx_id,
            field=field_name,
            action="filled",
            old_value=old_value if isinstance(old_value, str) else None,
            new_value=new_value,
        ))
    elif str(old_value) == new_value:
        findings.append(PackageValidationFinding(artifact=artifact_id, spdx_id=spdx_id, field=field_name, action="verified", old_value=str(old_value), new_value=new_value))
    else:
        findings.append(PackageValidationFinding(
            artifact=artifact_id,
            spdx_id=spdx_id,
            field=field_name,
            action="differs",
            old_value=str(old_value),
            new_value=new_value,
            notes="Existing SBOM value was preserved; registry value is recorded for manual review.",
        ))

def enrich_pkg_with_npm_metadata(pkg: dict[str, Any], artifact: NpmArtifact, metadata: NpmPackageMetadata, findings: list[PackageValidationFinding]) -> None:
    spdx_id = pkg.get("SPDXID")
    if not isinstance(spdx_id, str):
        spdx_id = npm_pkg_spdxid(artifact)
        pkg["SPDXID"] = spdx_id
    artifact = NpmArtifact(canonical_npm_name(artifact.name), artifact.version, artifact.scope, artifact.source, artifact.requested)
    artifact_id = npm_pkg_key(artifact)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "packageFileName", metadata.package_file_name, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "downloadLocation", metadata.tarball_url, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "homepage", metadata.homepage, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "supplier", metadata.supplier, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseDeclared", metadata.license_declared, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseConcluded", metadata.license_declared, findings)

    checksums = pkg.setdefault("checksums", [])
    if metadata.checksum_sha1 and not any(isinstance(c, dict) and c.get("algorithm") == "SHA1" and c.get("checksumValue") == metadata.checksum_sha1 for c in checksums):
        checksums.append({"algorithm": "SHA1", "checksumValue": metadata.checksum_sha1})
        findings.append(PackageValidationFinding(
            artifact=npm_pkg_key(artifact),
            spdx_id=spdx_id,
            field="checksums.SHA1",
            action="filled",
            old_value=None,
            new_value=metadata.checksum_sha1,
            notes="Fetched from npm registry dist.shasum.",
        ))

    refs = pkg.setdefault("externalRefs", [])
    wanted_purl = npm_pkg_purl(artifact)
    has_purl = any(isinstance(ref, dict) and ref.get("referenceType") == "purl" and ref.get("referenceLocator") == wanted_purl for ref in refs)
    if not has_purl:
        refs.append({"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": wanted_purl})
        findings.append(PackageValidationFinding(artifact=npm_pkg_key(artifact), spdx_id=spdx_id, field="externalRefs.purl", action="filled", old_value=None, new_value=wanted_purl))


def resolve_npm_transitives(roots: list[NpmArtifact], max_depth: int) -> tuple[dict[str, NpmArtifact], list[DependencyEdge], list[ResolutionIssue], list[SkippedArtifact]]:
    discovered: dict[str, NpmArtifact] = {}
    edges: list[DependencyEdge] = []
    issues: list[ResolutionIssue] = []
    skipped: list[SkippedArtifact] = []
    queue: list[tuple[NpmArtifact, int]] = [(NpmArtifact(canonical_npm_name(a.name), a.version, a.scope, a.source, a.requested), 0) for a in roots]
    processed: set[str] = set()

    while queue:
        current, depth = queue.pop(0)
        current = NpmArtifact(canonical_npm_name(current.name), current.version, current.scope, current.source, current.requested)
        key = npm_pkg_key(current)

        if key not in discovered:
            discovered[key] = current

        if key in processed:
            continue

        processed.add(key)

        if depth >= max_depth:
            continue

        children, child_issues = resolve_npm_pkg(current)
        issues.extend(child_issues)

        for child in children:
            child = NpmArtifact(canonical_npm_name(child.name), child.version, child.scope, child.source, child.requested)
            child_key = npm_pkg_key(child)
            edges.append(DependencyEdge(parent=key, child=child_key))

            if child_key not in discovered:
                discovered[child_key] = child
                queue.append((child, depth + 1))

    return discovered, edges, issues, skipped

def add_npm_transitives(
    sbom_data: dict[str, Any],
    discovered: dict[str, NpmArtifact],
    edges: list[DependencyEdge],
) -> tuple[dict[str, Any], list[PackageValidationFinding], list[ResolutionIssue]]:
    sbom = sbom_data.get("sbom", sbom_data)
    sbom.setdefault("packages", [])
    sbom.setdefault("relationships", [])

    findings: list[PackageValidationFinding] = []
    metadata_issues: list[ResolutionIssue] = []
    identity_to_spdxid = build_npm_id_to_spdxid(sbom_data)
    identity_to_package = build_npm_id_to_pkg(sbom_data)

    for key, artifact in discovered.items():
        metadata, issues = get_npm_metadata_from_registry(artifact)
        metadata_issues.extend(issues)
        if key in identity_to_spdxid:
            existing_spdx = identity_to_spdxid[key]
            existing_pkg = identity_to_package.get(key)
            findings.append(PackageValidationFinding(
                artifact=key,
                spdx_id=existing_spdx,
                field="package",
                action="existed",
                old_value=npm_pkg_purl(artifact),
                new_value=npm_pkg_purl(artifact),
                notes="npm package was already present in the input SBOM; enrichment/validation was attempted.",
            ))
            if existing_pkg is not None:
                enrich_pkg_with_npm_metadata(existing_pkg, artifact, metadata, findings)
            continue

        package = npm_pkg_to_spdx_pkg(artifact, metadata)
        sbom["packages"].append(package)
        identity_to_spdxid[key] = package["SPDXID"]
        identity_to_package[key] = package
        findings.append(PackageValidationFinding(
            artifact=key,
            spdx_id=package["SPDXID"],
            field="package",
            action="added",
            old_value=None,
            new_value=npm_pkg_purl(artifact),
            notes="Package added from npm registry transitive resolution.",
        ))

    for edge in edges:
        parent_key = edge.parent
        child_key = edge.child
        if parent_key.startswith("pkg:golang/") and "@" in parent_key:
            body = parent_key[len("pkg:golang/"):].split("?", 1)[0]
            mod, ver = body.rsplit("@", 1)
            parent_key = go_id_key(mod, ver)
        if child_key.startswith("pkg:golang/") and "@" in child_key:
            body = child_key[len("pkg:golang/"):].split("?", 1)[0]
            mod, ver = body.rsplit("@", 1)
            child_key = go_id_key(mod, ver)

        parent_spdxid = identity_to_spdxid.get(parent_key)
        child_spdxid = identity_to_spdxid.get(child_key)
        if not parent_spdxid or not child_spdxid:
            continue
        if has_relationship(sbom_data, parent_spdxid, child_spdxid, "DEPENDS_ON"):
            continue
        sbom["relationships"].append({"spdxElementId": parent_spdxid, "relatedSpdxElement": child_spdxid, "relationshipType": "DEPENDS_ON"})

    return sbom_data, findings, metadata_issues


# -------------------------
# PyPI / Python helpers
# -------------------------

PYPI_REGISTRY = "https://pypi.org/pypi"
PYPI_CACHE: dict[str, dict[str, Any]] = {}
PYPI_VERSION_CACHE: dict[tuple[str, str], dict[str, Any]] = {}

try:
    from packaging.requirements import Requirement as PackagingRequirement  # type: ignore
    from packaging.specifiers import SpecifierSet  # type: ignore
    from packaging.version import Version, InvalidVersion  # type: ignore
    PACKAGING_AVAILABLE = True
except Exception:  # pragma: no cover - fallback for minimal Python installs
    PackagingRequirement = None  # type: ignore
    SpecifierSet = None  # type: ignore
    Version = None  # type: ignore
    InvalidVersion = Exception  # type: ignore
    PACKAGING_AVAILABLE = False


@dataclass(frozen=True)
class PyPIArtifact:
    name: str
    version: str
    scope: str = "runtime"
    source: str | None = None
    requested: str | None = None


@dataclass(frozen=True)
class PyPIPackageMetadata:
    artifact: str
    registry_url: str | None = None
    download_url: str | None = None
    package_file_name: str | None = None
    homepage: str | None = None
    supplier: str | None = None
    license_declared: str | None = None
    checksum_sha256: str | None = None


def canonical_pypi_name(name: str) -> str:
    name = unquote((name or "").strip())
    if name.startswith("pkg:pypi/"):
        name = name[len("pkg:pypi/"):]
    if "?" in name:
        name = name.split("?", 1)[0]
    if "@" in name:
        name = name.rsplit("@", 1)[0]
    return re.sub(r"[-_.]+", "-", name).lower()


def pypi_purl(name: str, version: str) -> str:
    return f"pkg:pypi/{quote(canonical_pypi_name(name), safe='')}@{version}"


def pypi_identity(name: str, version: str) -> str:
    return pypi_purl(name, version)


def pypi_pkg_key(a: PyPIArtifact) -> str:
    return pypi_identity(a.name, a.version)


def pypi_pkg_purl(a: PyPIArtifact) -> str:
    return pypi_purl(a.name, a.version)


def pypi_pkg_spdxid(a: PyPIArtifact) -> str:
    safe = re.sub(r"[^A-Za-z0-9.-]+", "-", f"pypi-{canonical_pypi_name(a.name)}-{a.version}").strip("-")
    return f"SPDXRef-transitive-{safe}"


def pypi_ver_url(package_name: str, version: str) -> str:
    return f"{PYPI_REGISTRY}/{urllib.parse.quote(canonical_pypi_name(package_name), safe='')}/{urllib.parse.quote(version, safe='')}/json"


def get_pypi_project(package_name: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    name = canonical_pypi_name(package_name)
    if name in PYPI_CACHE:
        return PYPI_CACHE[name], []
    url = f"{PYPI_REGISTRY}/{urllib.parse.quote(canonical_pypi_name(name), safe='')}/json"
    try:
        data = get_json(url)
        PYPI_CACHE[name] = data
        return data, []
    except urllib.error.HTTPError as e:
        return None, [ResolutionIssue(pypi_purl(name, "UNKNOWN"), f"PyPI registry fetch failed: HTTP {e.code} at {url}")]
    except Exception as e:
        return None, [ResolutionIssue(pypi_purl(name, "UNKNOWN"), f"PyPI registry fetch failed: {type(e).__name__}: {e}")]


def get_pypi_version(package_name: str, version: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    canonical_name = canonical_pypi_name(package_name)
    cache_key = (canonical_name, version)
    if cache_key in PYPI_VERSION_CACHE:
        return PYPI_VERSION_CACHE[cache_key], []

    project, issues = get_pypi_project(canonical_name)
    if project:
        releases = project.get("releases")
        if isinstance(releases, dict) and version in releases:
            info = dict(project.get("info") or {})
            if info.get("version") == version:
                PYPI_VERSION_CACHE[cache_key] = project
                return project, issues

            url = pypi_ver_url(canonical_name, version)
            try:
                data = get_json(url)
                PYPI_VERSION_CACHE[cache_key] = data
                return data, issues
            except Exception:
                data = {"info": info, "releases": releases, "urls": releases.get(version) or []}
                PYPI_VERSION_CACHE[cache_key] = data
                return data, [*issues, ResolutionIssue(
                    pypi_purl(canonical_name, version),
                    "Used project-level PyPI metadata fallback because version-specific metadata could not be fetched",
                )]

    url = pypi_ver_url(canonical_name, version)
    try:
        data = get_json(url)
        PYPI_VERSION_CACHE[cache_key] = data
        return data, issues
    except Exception as e:
        return None, [*issues, ResolutionIssue(pypi_purl(canonical_name, version), f"PyPI version metadata fetch failed: {type(e).__name__}: {e}")]


def is_py_prerelease_ver(version: str) -> bool:
    return bool(re.search(r"(?i)(a|b|rc|dev|alpha|beta|pre|preview)", version))


def py_ver_key(version: str) -> tuple[Any, ...]:
    if PACKAGING_AVAILABLE:
        try:
            return (1, Version(version))  # type: ignore[misc]
        except Exception:
            pass
    nums = [int(x) for x in re.findall(r"\d+", version)[:6]]
    while len(nums) < 6:
        nums.append(0)
    return (0, *nums, version)


def py_spec_allows(version: str, spec: str | None) -> bool:
    spec = (spec or "").strip()
    if not spec or spec == "*":
        return True
    if PACKAGING_AVAILABLE:
        try:
            return Version(version) in SpecifierSet(spec)  # type: ignore[operator,misc]
        except Exception:
            return False

    for part in [p.strip() for p in spec.split(",") if p.strip()]:
        m = re.match(r"^(==|!=|>=|<=|>|<|~=)\s*([^,\s]+)$", part)
        if not m:
            continue
        op, target = m.groups()
        if op == "!=" and version == target:
            return False
        if op == "==":
            if target.endswith(".*"):
                if not version.startswith(target[:-2]):
                    return False
            elif version != target:
                return False
            continue
        cmp = (py_ver_key(version) > py_ver_key(target)) - (py_ver_key(version) < py_ver_key(target))
        if op == ">=" and cmp < 0: return False
        if op == "<=" and cmp > 0: return False
        if op == ">" and cmp <= 0: return False
        if op == "<" and cmp >= 0: return False
        if op == "~=":
            if cmp < 0: return False
    return True


def resolve_pypi_ver(package_name: str, specifier: str | None) -> tuple[str | None, list[ResolutionIssue]]:
    project, issues = get_pypi_project(package_name)
    if not project:
        return None, issues
    releases = project.get("releases")
    if not isinstance(releases, dict) or not releases:
        return None, [*issues, ResolutionIssue(pypi_purl(package_name, "UNKNOWN"), "PyPI project contained no releases")]

    requested = (specifier or "").strip()
    if requested in releases:
        return requested, issues

    allow_prerelease = bool(requested and re.search(r"(?i)(a|b|rc|dev)", requested))
    candidates: list[str] = []
    for v, files in releases.items():
        if not isinstance(v, str):
            continue
        if not allow_prerelease and is_py_prerelease_ver(v):
            continue
        if isinstance(files, list) and len(files) == 0:
            continue
        if py_spec_allows(v, requested):
            candidates.append(v)

    if candidates:
        return sorted(candidates, key=py_ver_key)[-1], issues

    return None, [*issues, ResolutionIssue(pypi_purl(package_name, "UNKNOWN"), f"Could not resolve PyPI version specifier: {requested or '<any>'}")]


def pypi_marker_extra(marker: str) -> bool:
    return bool(re.search(r"(?i)\bextra\b\s*(==|!=|in|not\s+in)\s*", marker or ""))


def pypi_marker_env() -> dict[str, str]:
    import os
    import platform
    import sys

    impl = platform.python_implementation()
    impl_name = {"CPython": "cpython", "PyPy": "pypy", "Jython": "jython", "IronPython": "ironpython"}.get(impl, impl.lower())

    return {
        "python_version": f"{sys.version_info.major}.{sys.version_info.minor}",
        "python_full_version": platform.python_version(),
        "sys_platform": sys.platform,
        "platform_system": platform.system(),
        "platform_machine": platform.machine(),
        "platform_python_implementation": impl,
        "implementation_name": impl_name,
        "os_name": os.name,
        "extra": "",
    }


def version_tuple(value: str) -> tuple[int, ...]:
    parts = re.findall(r"\d+", value or "")
    return tuple(int(p) for p in parts[:4]) if parts else (0,)


def compare_marker_values(left: str, op: str, right: str, variable: str | None = None) -> bool:
    if variable in {"python_version", "python_full_version"}:
        l_val: Any = version_tuple(left)
        r_val: Any = version_tuple(right)
    else:
        l_val = left
        r_val = right

    if op == "==":
        return l_val == r_val
    if op == "!=":
        return l_val != r_val
    if op == "<":
        return l_val < r_val
    if op == "<=":
        return l_val <= r_val
    if op == ">":
        return l_val > r_val
    if op == ">=":
        return l_val >= r_val
    if op == "in":
        return str(left) in str(right)
    if op == "not in":
        return str(left) not in str(right)
    return False


def split_marker_bool(marker: str, operator: str) -> list[str] | None:
    depth = 0
    parts: list[str] = []
    current: list[str] = []
    tokens = re.split(r"(\(|\)|\s+and\s+|\s+or\s+)", marker, flags=re.I)

    wanted = operator.lower()
    saw_operator = False
    for token in tokens:
        low = token.lower()
        if token == "(":
            depth += 1
            current.append(token)
        elif token == ")":
            depth = max(0, depth - 1)
            current.append(token)
        elif depth == 0 and low.strip() == wanted:
            parts.append("".join(current).strip())
            current = []
            saw_operator = True
        else:
            current.append(token)

    if not saw_operator:
        return None

    parts.append("".join(current).strip())
    return [p for p in parts if p]


def eval_pypi_marker(marker: str) -> bool | None:
    marker = (marker or "").strip()
    if not marker:
        return True

    if pypi_marker_extra(marker):
        return False

    while marker.startswith("(") and marker.endswith(")"):
        inner = marker[1:-1].strip()
        if inner.count("(") == inner.count(")"):
            marker = inner
        else:
            break

    or_parts = split_marker_bool(marker, "or")
    if or_parts is not None:
        vals = [eval_pypi_marker(p) for p in or_parts]
        return True if any(v is True for v in vals) else (False if all(v is False for v in vals) else None)

    and_parts = split_marker_bool(marker, "and")
    if and_parts is not None:
        vals = [eval_pypi_marker(p) for p in and_parts]
        return False if any(v is False for v in vals) else (True if all(v is True for v in vals) else None)

    env = pypi_marker_env()

    m = re.fullmatch(r"\s*([A-Za-z_][A-Za-z0-9_]*)\s*(==|!=|<=|>=|<|>|not\s+in|in)\s*['\"]([^'\"]*)['\"]\s*", marker, flags=re.I)
    if m:
        var, op, value = m.group(1), re.sub(r"\s+", " ", m.group(2).lower()), m.group(3)
        if var not in env:
            return None
        return compare_marker_values(env[var], op, value, var)

    m = re.fullmatch(r"\s*['\"]([^'\"]*)['\"]\s*(==|!=|<=|>=|<|>|not\s+in|in)\s*([A-Za-z_][A-Za-z0-9_]*)\s*", marker, flags=re.I)
    if m:
        value, op, var = m.group(1), re.sub(r"\s+", " ", m.group(2).lower()), m.group(3)
        if var not in env:
            return None
        return compare_marker_values(value, op, env[var], var)

    return None

def parse_requires_dist(requirement_text: str, parent: PyPIArtifact) -> tuple[str | None, str | None, str, list[ResolutionIssue], bool]:
    issues: list[ResolutionIssue] = []
    raw = requirement_text.strip()
    if not raw:
        return None, None, "runtime", issues, True

    marker_part = raw.split(";", 1)[1].strip() if ";" in raw else ""
    if marker_part and pypi_marker_extra(marker_part):
        return None, None, "optional-extra", [ResolutionIssue(pypi_pkg_key(parent), f"Skipped PyPI optional-extra dependency: {raw}")], True

    if PACKAGING_AVAILABLE:
        try:
            req = PackagingRequirement(raw)  # type: ignore[misc]
            if req.marker is not None:
                try:
                    if not req.marker.evaluate({"extra": ""}):
                        return None, None, "marker", [ResolutionIssue(pypi_pkg_key(parent), f"Skipped PyPI dependency due to marker: {raw}")], True
                except Exception:
                    return None, None, "marker", [ResolutionIssue(pypi_pkg_key(parent), f"Could not evaluate PyPI marker, skipped: {raw}")], True
            name = canonical_pypi_name(req.name)
            spec = str(req.specifier) if req.specifier else ""
            return name, spec, "runtime", issues, False
        except Exception as e:
            issues.append(ResolutionIssue(pypi_pkg_key(parent), f"Could not parse Requires-Dist with packaging: {raw} ({e})"))

    result = eval_pypi_marker(marker_part)
    marker_extra = bool(result) if result is not None else False

    if marker_part and not marker_extra:
        return None, None, "marker", [*issues, ResolutionIssue(pypi_pkg_key(parent), f"Skipped PyPI dependency due to unevaluated marker: {raw}")], True

    req_part = raw.split(";", 1)[0].strip()
    m = re.match(r"^([A-Za-z0-9_.-]+)(?:\[[^\]]+\])?\s*(.*)$", req_part)
    if not m:
        return None, None, "runtime", [*issues, ResolutionIssue(pypi_pkg_key(parent), f"Could not parse Requires-Dist: {raw}")], True

    spec = m.group(2).strip()
    if spec.startswith("(") and spec.endswith(")"):
        spec = spec[1:-1].strip()

    return canonical_pypi_name(m.group(1)), spec, "runtime", issues, False


def resolve_pypi_pkg(artifact: PyPIArtifact) -> tuple[list[PyPIArtifact], list[ResolutionIssue], list[SkippedArtifact]]:
    data, issues = get_pypi_version(artifact.name, artifact.version)
    skipped: list[SkippedArtifact] = []
    if data is None:
        return [], issues, skipped
    info = data.get("info") if isinstance(data.get("info"), dict) else {}
    requires_dist = info.get("requires_dist") if isinstance(info, dict) else None
    if not isinstance(requires_dist, list):
        return [], issues, skipped

    children: list[PyPIArtifact] = []
    for req_text in requires_dist:
        if not isinstance(req_text, str):
            continue
        dep_name, dep_spec, scope, parse_issues, was_skipped = parse_requires_dist(req_text, artifact)
        if was_skipped:
            skip_reason = parse_issues[0].reason if parse_issues else "Skipped PyPI dependency marker or optional extra"
            if not skip_reason.startswith("Skipped PyPI"):
                issues.extend(parse_issues)
            skipped.append(SkippedArtifact(artifact=req_text, source=pypi_pkg_key(artifact), scope=scope, reason=skip_reason))
            continue
        issues.extend(parse_issues)
        if not dep_name:
            continue
        dep_version, version_issues = resolve_pypi_ver(dep_name, dep_spec)
        issues.extend(version_issues)
        if dep_version:
            children.append(PyPIArtifact(name=dep_name, version=dep_version, scope=scope, source=pypi_pkg_key(artifact), requested=dep_spec or None))
    return children, issues, skipped


def get_pypi_metadata_from_registry(artifact: PyPIArtifact) -> tuple[PyPIPackageMetadata, list[ResolutionIssue]]:
    key = pypi_pkg_key(artifact)
    data, issues = get_pypi_version(artifact.name, artifact.version)
    if data is None:
        return PyPIPackageMetadata(artifact=key, registry_url=pypi_ver_url(artifact.name, artifact.version)), issues
    info = data.get("info") if isinstance(data.get("info"), dict) else {}
    urls = data.get("urls") if isinstance(data.get("urls"), list) else []
    if not urls and isinstance(data.get("releases"), dict):
        release_files = data["releases"].get(artifact.version)
        if isinstance(release_files, list):
            urls = release_files

    chosen_file = None
    for f in urls:
        if isinstance(f, dict) and f.get("packagetype") == "sdist":
            chosen_file = f
            break
    if chosen_file is None:
        for f in urls:
            if isinstance(f, dict):
                chosen_file = f
                break

    project_urls = info.get("project_urls") if isinstance(info.get("project_urls"), dict) else {}
    homepage = None
    for k in ("Homepage", "Home", "Source", "Source Code", "Repository", "Bug Tracker"):
        if isinstance(project_urls.get(k), str):
            homepage = project_urls[k]
            break
    if not homepage and isinstance(info.get("home_page"), str) and info.get("home_page"):
        homepage = info.get("home_page")
    if not homepage and isinstance(info.get("package_url"), str):
        homepage = info.get("package_url")

    author = info.get("author") if isinstance(info.get("author"), str) else None
    author_email = info.get("author_email") if isinstance(info.get("author_email"), str) else None
    maintainer = info.get("maintainer") if isinstance(info.get("maintainer"), str) else None
    maintainer_email = info.get("maintainer_email") if isinstance(info.get("maintainer_email"), str) else None
    supplier = None
    person = author or maintainer
    email = author_email or maintainer_email
    if person and email:
        supplier = f"Person: {person} ({email})"
    elif person:
        supplier = f"Person: {person}"

    license_value = info.get("license") if isinstance(info.get("license"), str) else None
    if not license_value:
        classifiers = info.get("classifiers") if isinstance(info.get("classifiers"), list) else []
        for c in classifiers:
            if isinstance(c, str) and c.startswith("License ::"):
                license_value = c.rsplit("::", 1)[-1].strip()
                break

    sha256 = None
    download_url = None
    filename = None
    if isinstance(chosen_file, dict):
        download_url = chosen_file.get("url") if isinstance(chosen_file.get("url"), str) else None
        filename = chosen_file.get("filename") if isinstance(chosen_file.get("filename"), str) else None
        digests = chosen_file.get("digests") if isinstance(chosen_file.get("digests"), dict) else {}
        if isinstance(digests.get("sha256"), str):
            sha256 = digests.get("sha256")

    return PyPIPackageMetadata(
        artifact=key,
        registry_url=pypi_ver_url(artifact.name, artifact.version),
        download_url=download_url,
        package_file_name=filename,
        homepage=homepage,
        supplier=supplier,
        license_declared=license_name_to_spdx(license_value) or "NOASSERTION",
        checksum_sha256=sha256.lower() if isinstance(sha256, str) else None,
    ), issues


def pypi_pkg_from_spdx_pkg(pkg: dict[str, Any]) -> PyPIArtifact | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if not isinstance(loc, str) or not loc.startswith("pkg:pypi/") or "@" not in loc:
            continue
        body = loc[len("pkg:pypi/"):].split("?", 1)[0]
        name_part, version = body.rsplit("@", 1)
        name = canonical_pypi_name(name_part)
        if name and version:
            return PyPIArtifact(name, version, source="surface_sbom")
    return None


def get_all_pypi_pkgs(sbom_data: dict[str, Any]) -> list[PyPIArtifact]:
    sbom = sbom_data.get("sbom", sbom_data)
    artifacts: list[PyPIArtifact] = []
    seen: set[str] = set()
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        artifact = pypi_pkg_from_spdx_pkg(pkg)
        if artifact is None:
            continue
        key = pypi_pkg_key(artifact)
        if key not in seen:
            seen.add(key)
            artifacts.append(artifact)
    return artifacts


def get_project_spdxids(sbom_data: dict[str, Any]) -> set[str]:
    sbom = sbom_data.get("sbom", sbom_data)
    project_ids: set[str] = set()

    for rel in sbom.get("relationships", []) or []:
        if not isinstance(rel, dict):
            continue
        if rel.get("spdxElementId") == "SPDXRef-DOCUMENT" and rel.get("relationshipType") == "DESCRIBES":
            related = rel.get("relatedSpdxElement")
            if isinstance(related, str):
                project_ids.add(related)

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        spdx_id = pkg.get("SPDXID")
        if not isinstance(spdx_id, str):
            continue
        for ref in pkg.get("externalRefs", []) or []:
            loc = ref.get("referenceLocator") if isinstance(ref, dict) else None
            if isinstance(loc, str) and loc.startswith("pkg:github/"):
                project_ids.add(spdx_id)

    return project_ids


def get_direct_pypi_pkgs(sbom_data: dict[str, Any]) -> list[PyPIArtifact]:
    sbom = sbom_data.get("sbom", sbom_data)
    packages_by_id: dict[str, dict[str, Any]] = {}
    for pkg in sbom.get("packages", []) or []:
        if isinstance(pkg, dict) and isinstance(pkg.get("SPDXID"), str):
            packages_by_id[pkg["SPDXID"]] = pkg

    project_ids = get_project_spdxids(sbom_data)
    direct_ids: set[str] = set()
    for rel in sbom.get("relationships", []) or []:
        if not isinstance(rel, dict):
            continue
        if rel.get("relationshipType") not in {"DEPENDS_ON", "CONTAINS"}:
            continue
        if rel.get("spdxElementId") not in project_ids:
            continue
        related = rel.get("relatedSpdxElement")
        if isinstance(related, str):
            direct_ids.add(related)

    artifacts: list[PyPIArtifact] = []
    seen: set[str] = set()
    for spdx_id in direct_ids:
        pkg = packages_by_id.get(spdx_id)
        if not pkg:
            continue
        artifact = pypi_pkg_from_spdx_pkg(pkg)
        if artifact is None:
            continue
        key = pypi_pkg_key(artifact)
        if key not in seen:
            seen.add(key)
            artifacts.append(artifact)
    return sorted(artifacts, key=lambda a: pypi_pkg_key(a))


def get_pypi_pkgs(sbom_data: dict[str, Any], root_mode: str = "direct") -> list[PyPIArtifact]:
    if root_mode == "all":
        return get_all_pypi_pkgs(sbom_data)

    direct = get_direct_pypi_pkgs(sbom_data)
    if direct:
        return direct

    return get_all_pypi_pkgs(sbom_data)

def get_pypi_id(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator")
        if isinstance(loc, str) and loc.startswith("pkg:pypi/") and "@" in loc:
            body = loc[len("pkg:pypi/"):].split("?", 1)[0]
            name, version = body.rsplit("@", 1)
            return pypi_identity(name, version)
    return None


def build_pypi_id_to_spdxid(sbom_data: dict[str, Any]) -> dict[str, str]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, str] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_pypi_id(pkg)
        spdx_id = pkg.get("SPDXID")
        if identity and isinstance(spdx_id, str):
            out[identity] = spdx_id
    return out


def build_pypi_id_to_pkg(sbom_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, dict[str, Any]] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_pypi_id(pkg)
        if identity:
            out[identity] = pkg
    return out


def pypi_pkg_to_spdx_pkg(a: PyPIArtifact, metadata: PyPIPackageMetadata | None = None) -> dict[str, Any]:
    package = {
        "name": canonical_pypi_name(a.name),
        "SPDXID": pypi_pkg_spdxid(a),
        "versionInfo": a.version,
        "downloadLocation": metadata.download_url if metadata and metadata.download_url else "NOASSERTION",
        "filesAnalyzed": False,
        "checksums": ([{"algorithm": "SHA256", "checksumValue": metadata.checksum_sha256}] if metadata and metadata.checksum_sha256 else []),
        "licenseConcluded": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "licenseDeclared": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "copyrightText": "NOASSERTION",
        "externalRefs": [{"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": pypi_pkg_purl(a)}],
    }
    if metadata:
        if metadata.package_file_name:
            package["packageFileName"] = metadata.package_file_name
        if metadata.homepage:
            package["homepage"] = metadata.homepage
        if metadata.supplier:
            package["supplier"] = metadata.supplier
    return package


def enrich_pkg_with_pypi_metadata(pkg: dict[str, Any], artifact: PyPIArtifact, metadata: PyPIPackageMetadata, findings: list[PackageValidationFinding]) -> None:
    spdx_id = pkg.get("SPDXID")
    if not isinstance(spdx_id, str):
        spdx_id = pypi_pkg_spdxid(artifact)
        pkg["SPDXID"] = spdx_id
    artifact_id = pypi_pkg_key(artifact)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "packageFileName", metadata.package_file_name, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "downloadLocation", metadata.download_url, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "homepage", metadata.homepage, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "supplier", metadata.supplier, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseDeclared", metadata.license_declared, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseConcluded", metadata.license_declared, findings)
    checksums = pkg.setdefault("checksums", [])
    if metadata.checksum_sha256 and not any(isinstance(c, dict) and c.get("algorithm") == "SHA256" and c.get("checksumValue") == metadata.checksum_sha256 for c in checksums):
        checksums.append({"algorithm": "SHA256", "checksumValue": metadata.checksum_sha256})
        findings.append(PackageValidationFinding(artifact=artifact_id, spdx_id=spdx_id, field="checksums.SHA256", action="filled", old_value=None, new_value=metadata.checksum_sha256, notes="Fetched from PyPI release file digests."))
    refs = pkg.setdefault("externalRefs", [])
    wanted_purl = pypi_pkg_purl(artifact)
    wanted_identity = pypi_identity(artifact.name, artifact.version)
    has_equivalent_purl = False
    for ref in refs:
        if not (isinstance(ref, dict) and ref.get("referenceType") == "purl"):
            continue
        loc = ref.get("referenceLocator")
        if not (isinstance(loc, str) and loc.startswith("pkg:pypi/") and "@" in loc):
            continue
        body = loc[len("pkg:pypi/"):].split("?", 1)[0]
        name, version = body.rsplit("@", 1)
        if pypi_identity(name, version) == wanted_identity:
            has_equivalent_purl = True
            break
    if not has_equivalent_purl:
        refs.append({"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": wanted_purl})
        findings.append(PackageValidationFinding(artifact=artifact_id, spdx_id=spdx_id, field="externalRefs.purl", action="filled", old_value=None, new_value=wanted_purl))


def resolve_pypi_transitives(
    roots: list[PyPIArtifact],
    max_depth: int,
    max_artifacts: int | None = None,
) -> tuple[dict[str, PyPIArtifact], list[DependencyEdge], list[ResolutionIssue], list[SkippedArtifact]]:
    discovered: dict[str, PyPIArtifact] = {}
    edges: list[DependencyEdge] = []
    issues: list[ResolutionIssue] = []
    skipped: list[SkippedArtifact] = []
    queue: list[tuple[PyPIArtifact, int]] = [(PyPIArtifact(canonical_pypi_name(a.name), a.version, a.scope, a.source, a.requested), 0) for a in roots]
    processed: set[str] = set()
    while queue:
        if len(processed) and len(processed) % 100 == 0:
            print(f"[PYPI] processed={len(processed)} discovered={len(discovered)} queued={len(queue)} issues={len(issues)} skipped={len(skipped)}")
        if max_artifacts is not None and len(processed) >= max_artifacts:
            issues.append(ResolutionIssue("pkg:pypi/MAX_ARTIFACT_LIMIT@UNKNOWN", f"Stopped PyPI traversal after reaching --pypi-max-artifacts={max_artifacts}; remaining queue={len(queue)}"))
            break
        current, depth = queue.pop(0)
        key = pypi_pkg_key(current)
        if key not in discovered:
            discovered[key] = current
        if key in processed:
            continue
        processed.add(key)
        if depth >= max_depth:
            continue
        children, child_issues, child_skipped = resolve_pypi_pkg(current)
        issues.extend(child_issues)
        skipped.extend(child_skipped)
        for child in children:
            child = PyPIArtifact(canonical_pypi_name(child.name), child.version, child.scope, child.source, child.requested)
            child_key = pypi_pkg_key(child)
            edges.append(DependencyEdge(parent=key, child=child_key))
            if child_key not in discovered:
                discovered[child_key] = child
                queue.append((child, depth + 1))
    return discovered, edges, issues, skipped


def add_pypi_transitives(sbom_data: dict[str, Any], discovered: dict[str, PyPIArtifact], edges: list[DependencyEdge]) -> tuple[dict[str, Any], list[PackageValidationFinding], list[ResolutionIssue]]:
    sbom = sbom_data.get("sbom", sbom_data)
    sbom.setdefault("packages", [])
    sbom.setdefault("relationships", [])
    findings: list[PackageValidationFinding] = []
    metadata_issues: list[ResolutionIssue] = []
    identity_to_spdxid = build_pypi_id_to_spdxid(sbom_data)
    identity_to_package = build_pypi_id_to_pkg(sbom_data)
    for key, artifact in discovered.items():
        metadata, issues = get_pypi_metadata_from_registry(artifact)
        metadata_issues.extend(issues)
        if key in identity_to_spdxid:
            existing_spdx = identity_to_spdxid[key]
            existing_pkg = identity_to_package.get(key)
            findings.append(PackageValidationFinding(artifact=key, spdx_id=existing_spdx, field="package", action="existed", old_value=pypi_pkg_purl(artifact), new_value=pypi_pkg_purl(artifact), notes="PyPI package was already present in the input SBOM; enrichment/validation was attempted."))
            if existing_pkg is not None:
                enrich_pkg_with_pypi_metadata(existing_pkg, artifact, metadata, findings)
            continue
        package = pypi_pkg_to_spdx_pkg(artifact, metadata)
        sbom["packages"].append(package)
        identity_to_spdxid[key] = package["SPDXID"]
        identity_to_package[key] = package
        findings.append(PackageValidationFinding(artifact=key, spdx_id=package["SPDXID"], field="package", action="added", old_value=None, new_value=pypi_pkg_purl(artifact), notes="Package added from PyPI transitive resolution."))
    for edge in edges:
        parent_spdxid = identity_to_spdxid.get(edge.parent)
        child_spdxid = identity_to_spdxid.get(edge.child)
        if not parent_spdxid or not child_spdxid:
            continue
        if has_relationship(sbom_data, parent_spdxid, child_spdxid, "DEPENDS_ON"):
            continue
        sbom["relationships"].append({"spdxElementId": parent_spdxid, "relatedSpdxElement": child_spdxid, "relationshipType": "DEPENDS_ON"})
    return sbom_data, findings, metadata_issues


# -------------------------
# Go module helpers
# -------------------------

GO_PROXY = "https://proxy.golang.org"
GO_MODULE_CACHE: dict[str, dict[str, Any]] = {}
GO_MOD_CACHE: dict[str, str] = {}


@dataclass(frozen=True)
class GoArtifact:
    module: str
    version: str
    scope: str = "runtime"
    source: str | None = None
    requested: str | None = None


@dataclass(frozen=True)
class GoPackageMetadata:
    artifact: str
    module_url: str | None = None
    mod_url: str | None = None
    zip_url: str | None = None
    info_url: str | None = None
    package_file_name: str | None = None
    homepage: str | None = None
    license_declared: str | None = None
    checksum_sha256: str | None = None
    time: str | None = None


_GO_VERSION_RE = re.compile(r"^v\d+\.\d+\.\d+(?:[-+][0-9A-Za-z_.-]+)?(?:\+incompatible)?$")
_GO_BARE_SEMVER_RE = re.compile(r"^(\d+\.\d+\.\d+(?:[-+][0-9A-Za-z_.-]+)?(?:\+incompatible)?)$")
_GO_MAJOR_RE = re.compile(r"^v?(\d+)\.")


def normalize_go_ver(version: str | None) -> str:
    value = urllib.parse.unquote((version or "").strip())
    if not value:
        return value
    if value.startswith("v"):
        return value
    if _GO_BARE_SEMVER_RE.match(value):
        return "v" + value
    if re.match(r"^\d+\.\d+\.\d+-", value):
        return "v" + value
    return value


def go_module_major_suffix(module: str) -> int | None:
    module = normalize_go_module(module)
    m = re.search(r"(?:/v|\.v)(\d+)$", module)
    if m:
        try:
            return int(m.group(1))
        except ValueError:
            return None
    return None


def go_major_ver(version: str) -> int | None:
    m = _GO_MAJOR_RE.match(normalize_go_ver(version))
    if not m:
        return None
    try:
        return int(m.group(1))
    except ValueError:
        return None


def go_ver_candidates(module: str, version: str) -> list[str]:
    original = urllib.parse.unquote((version or "").strip())
    normalized = normalize_go_ver(original)
    candidates: list[str] = []
    for candidate in (normalized, original):
        if candidate and candidate not in candidates:
            candidates.append(candidate)

    major = go_major_ver(normalized)
    module_major = go_module_major_suffix(module)
    if major and major >= 2 and module_major is None and "+incompatible" not in normalized:
        incompatible = normalized + "+incompatible"
        if incompatible not in candidates:
            candidates.append(incompatible)

    return candidates


def unescape_go_proxy_path(module: str) -> str:
    def repl(match: re.Match[str]) -> str:
        return match.group(1)

    return re.sub(r"!([a-z])", repl, module)


def normalize_go_module(module: str) -> str:
    module = urllib.parse.unquote((module or "").strip())
    module = module.strip().strip('"').strip("'")
    if module.startswith("pkg:golang/"):
        body = module[len("pkg:golang/"):].split("?", 1)[0]
        if "@" in body:
            body = body.rsplit("@", 1)[0]
        module = body
    module = unescape_go_proxy_path(module)
    return module.strip().strip("/").strip('"').strip("'")


def go_id_key(module: str, version: str) -> str:
    return go_purl(normalize_go_module(module).lower(), normalize_go_ver(version))

def go_pkg_key(a: GoArtifact) -> str:
    return go_id_key(a.module, a.version)

def go_pkg_purl(a: GoArtifact) -> str:
    return go_purl(a.module, normalize_go_ver(a.version))


def go_pkg_spdxid(a: GoArtifact) -> str:
    safe = re.sub(r"[^A-Za-z0-9.-]+", "-", f"golang-{a.module}-{normalize_go_ver(a.version)}").strip("-")
    return f"SPDXRef-transitive-{safe}"


def go_purl(module: str, version: str) -> str:
    module = normalize_go_module(module)
    version = normalize_go_ver(version)
    return f"pkg:golang/{urllib.parse.quote(module, safe='/')}@{urllib.parse.quote(version, safe='')}"


def escape_go_proxy_path(module: str) -> str:
    module = normalize_go_module(module)
    out: list[str] = []
    for ch in module:
        if "A" <= ch <= "Z":
            out.append("!" + ch.lower())
        else:
            out.append(ch)
    return urllib.parse.quote("".join(out), safe="/!")


def go_proxy_url(module: str, version: str, suffix: str) -> str:
    return f"{GO_PROXY}/{escape_go_proxy_path(module)}/@v/{urllib.parse.quote(normalize_go_ver(version), safe='')}.{suffix}"


def github_go_mod_url(module: str, version: str) -> str | None:
    normalized_module = normalize_go_module(module)
    parts = normalized_module.split("/")
    if len(parts) < 3 or parts[0].lower() != "github.com":
        return None

    owner = parts[1]
    repo = parts[2]
    subdir = "/".join(parts[3:])
    canonical_version = normalize_go_ver(version)
    raw_path = f"{subdir}/go.mod" if subdir else "go.mod"
    return (
        "https://raw.githubusercontent.com/"
        f"{urllib.parse.quote(owner, safe='')}/"
        f"{urllib.parse.quote(repo, safe='')}/"
        f"{urllib.parse.quote(canonical_version, safe='')}/"
        f"{urllib.parse.quote(raw_path, safe='/')}"
    )


def get_github_go_mod(module: str, version: str) -> tuple[str | None, list[ResolutionIssue]]:
    normalized_module = normalize_go_module(module)
    canonical_version = normalize_go_ver(version)
    url = github_go_mod_url(normalized_module, canonical_version)
    if not url:
        return None, [ResolutionIssue(go_purl(normalized_module, canonical_version), "Direct GitHub go.mod fallback is only available for github.com modules.")]

    try:
        text = get_text(url)
        return text, []
    except urllib.error.HTTPError as e:
        return None, [ResolutionIssue(go_purl(normalized_module, canonical_version), f"GitHub raw go.mod fallback failed: HTTP {e.code} at {url}")]
    except Exception as e:
        return None, [ResolutionIssue(go_purl(normalized_module, canonical_version), f"GitHub raw go.mod fallback failed: {type(e).__name__}: {e}")]


def get_go_info(module: str, version: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    normalized_module = normalize_go_module(module)
    issues_accum: list[ResolutionIssue] = []

    for candidate_version in go_ver_candidates(normalized_module, version):
        canonical_candidate = normalize_go_ver(candidate_version)
        key = f"{normalized_module}@{canonical_candidate}"
        if key in GO_MODULE_CACHE:
            return GO_MODULE_CACHE[key], []

        url = go_proxy_url(normalized_module, candidate_version, "info")
        try:
            data = get_json(url)
            GO_MODULE_CACHE[key] = data
            return data, []
        except urllib.error.HTTPError as e:
            issues_accum.append(ResolutionIssue(go_purl(normalized_module, candidate_version), f"Go proxy JSON fetch failed: HTTP {e.code}"))
        except Exception as e:
            issues_accum.append(ResolutionIssue(go_purl(normalized_module, candidate_version), f"Go proxy JSON fetch failed: {type(e).__name__}: {e}"))

    fallback_text, fallback_issues = get_github_go_mod(normalized_module, version)
    if fallback_text is not None:
        canonical_version = normalize_go_ver(version)
        key = f"{normalized_module}@{canonical_version}"
        data = {"Version": canonical_version}
        GO_MODULE_CACHE[key] = data
        return data, []

    issues_accum.extend(fallback_issues)
    return None, [ResolutionIssue(go_purl(normalized_module, version), "Go proxy .info fetch failed for all version candidates: " + "; ".join(i.reason for i in issues_accum[:6]))]


def get_go_mod(module: str, version: str) -> tuple[str | None, list[ResolutionIssue]]:
    normalized_module = normalize_go_module(module)
    issues_accum: list[ResolutionIssue] = []

    for candidate_version in go_ver_candidates(normalized_module, version):
        canonical_candidate = normalize_go_ver(candidate_version)
        key = f"{normalized_module}@{canonical_candidate}"
        if key in GO_MOD_CACHE:
            return GO_MOD_CACHE[key], []

        url = go_proxy_url(normalized_module, candidate_version, "mod")
        try:
            text = get_text(url)
            GO_MOD_CACHE[key] = text
            return text, []
        except urllib.error.HTTPError as e:
            issues_accum.append(ResolutionIssue(go_purl(normalized_module, candidate_version), f"HTTP {e.code} at {url}"))
        except Exception as e:
            issues_accum.append(ResolutionIssue(go_purl(normalized_module, candidate_version), f"{type(e).__name__}: {e}"))

    fallback_text, fallback_issues = get_github_go_mod(normalized_module, version)
    if fallback_text is not None:
        canonical_version = normalize_go_ver(version)
        key = f"{normalized_module}@{canonical_version}"
        GO_MOD_CACHE[key] = fallback_text
        return fallback_text, []

    issues_accum.extend(fallback_issues)
    return None, [ResolutionIssue(go_purl(normalized_module, version), "Go proxy .mod fetch failed for all version candidates: " + "; ".join(i.reason for i in issues_accum[:6]))]

def parse_go_requires(mod_text: str, parent: GoArtifact) -> tuple[list[GoArtifact], list[ResolutionIssue]]:
    deps: list[GoArtifact] = []
    issues: list[ResolutionIssue] = []
    in_require_block = False

    for raw_line in mod_text.splitlines():
        line = raw_line.strip()
        if not line:
            continue

        if "//" in line:
            line = line.split("//", 1)[0].strip()
        if not line:
            continue

        if line == "require (":
            in_require_block = True
            continue
        if in_require_block and line == ")":
            in_require_block = False
            continue

        if line.startswith("require "):
            rest = line[len("require "):].strip()
        elif in_require_block:
            rest = line
        else:
            continue

        parts = rest.split()
        if len(parts) < 2:
            issues.append(ResolutionIssue(go_pkg_key(parent), f"Could not parse Go require line: {raw_line.strip()}"))
            continue

        module = normalize_go_module(parts[0])
        version = normalize_go_ver((parts[1] or "").strip().strip('"').strip("'"))
        if not module or not version:
            continue
        if version.startswith("(") or module in {"(", ")"}:
            continue

        deps.append(GoArtifact(module=module, version=version, source=go_pkg_key(parent), requested=version))

    return deps, issues

def resolve_go_pkg(artifact: GoArtifact) -> tuple[list[GoArtifact], list[ResolutionIssue]]:
    mod_text, issues = get_go_mod(artifact.module, artifact.version)
    if mod_text is None:
        return [], issues
    deps, parse_issues = parse_go_requires(mod_text, artifact)
    return deps, [*issues, *parse_issues]


def get_go_metadata_from_proxy(artifact: GoArtifact) -> tuple[GoPackageMetadata, list[ResolutionIssue]]:
    key = go_pkg_key(artifact)
    info, issues = get_go_info(artifact.module, artifact.version)
    normalized_version = normalize_go_ver(artifact.version)
    normalized_module = normalize_go_module(artifact.module)
    escaped_module_filename = re.sub(r"[^A-Za-z0-9._-]+", "-", normalized_module).strip("-") or "module"
    metadata = GoPackageMetadata(
        artifact=key,
        module_url=f"https://pkg.go.dev/{normalized_module}",
        mod_url=go_proxy_url(normalized_module, normalized_version, "mod"),
        zip_url=go_proxy_url(normalized_module, normalized_version, "zip"),
        info_url=go_proxy_url(normalized_module, normalized_version, "info"),
        package_file_name=f"{escaped_module_filename}-{normalized_version}.zip",
        homepage=f"https://pkg.go.dev/{normalized_module}",
        license_declared=None,
        checksum_sha256=None,
        time=str(info.get("Time")) if isinstance(info, dict) and info.get("Time") else None,
    )
    return metadata, issues


def get_go_pkgs(sbom_data: dict[str, Any]) -> list[GoArtifact]:
    sbom = sbom_data.get("sbom", sbom_data)
    artifacts: list[GoArtifact] = []

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        for ref in pkg.get("externalRefs", []) or []:
            loc = ref.get("referenceLocator")
            if not isinstance(loc, str) or not loc.startswith("pkg:golang/") or "@" not in loc:
                continue
            body = loc[len("pkg:golang/"):].split("?", 1)[0]
            module_part, version = body.rsplit("@", 1)
            module = normalize_go_module(module_part)
            version = normalize_go_ver(version)
            if module and version:
                artifacts.append(GoArtifact(module, version, source="surface_sbom"))

    seen: set[str] = set()
    out: list[GoArtifact] = []
    for artifact in artifacts:
        key = go_pkg_key(artifact)
        if key in seen:
            continue
        seen.add(key)
        out.append(artifact)
    return out


def parse_go_purl(locator: str) -> tuple[str, str] | None:
    if not isinstance(locator, str) or not locator.startswith("pkg:golang/") or "@" not in locator:
        return None
    body = locator[len("pkg:golang/"):].split("?", 1)[0]
    module_part, version_part = body.rsplit("@", 1)
    module = normalize_go_module(module_part)
    version = normalize_go_ver(version_part)
    if not module or not version:
        return None
    return module, version

def get_go_id(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        loc = ref.get("referenceLocator") if isinstance(ref, dict) else None
        parsed = parse_go_purl(loc) if isinstance(loc, str) else None
        if parsed:
            module, version = parsed
            return go_id_key(module, version)
    return None

def build_go_id_to_spdxid(sbom_data: dict[str, Any]) -> dict[str, str]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, str] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_go_id(pkg)
        spdx_id = pkg.get("SPDXID")
        if identity and isinstance(spdx_id, str):
            out[identity] = spdx_id
    return out


def build_go_id_to_pkg(sbom_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, dict[str, Any]] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_go_id(pkg)
        if identity:
            out[identity] = pkg
    return out


def go_pkg_to_spdx_pkg(a: GoArtifact, metadata: GoPackageMetadata | None = None) -> dict[str, Any]:
    package = {
        "name": a.module,
        "SPDXID": go_pkg_spdxid(a),
        "versionInfo": normalize_go_ver(a.version),
        "downloadLocation": metadata.zip_url if metadata and metadata.zip_url else "NOASSERTION",
        "filesAnalyzed": False,
        "checksums": [],
        "licenseConcluded": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "licenseDeclared": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "copyrightText": "NOASSERTION",
        "externalRefs": [{"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": go_pkg_purl(a)}],
    }
    if metadata:
        if metadata.package_file_name:
            package["packageFileName"] = metadata.package_file_name
        if metadata.homepage:
            package["homepage"] = metadata.homepage
    return package

def dedupe_pkg_external_refs(pkg: dict[str, Any]) -> int:
    refs = pkg.get("externalRefs")
    if not isinstance(refs, list):
        return 0

    seen: set[str] = set()
    deduped: list[Any] = []
    removed = 0
    for ref in refs:
        if isinstance(ref, dict):
            key = json.dumps(ref, sort_keys=True)
            if key in seen:
                removed += 1
                continue
            seen.add(key)
        deduped.append(ref)

    if removed:
        pkg["externalRefs"] = deduped
    return removed

def enrich_pkg_with_go_metadata(pkg: dict[str, Any], artifact: GoArtifact, metadata: GoPackageMetadata, findings: list[PackageValidationFinding]) -> None:
    spdx_id = pkg.get("SPDXID")
    if not isinstance(spdx_id, str):
        spdx_id = go_pkg_spdxid(artifact)
        pkg["SPDXID"] = spdx_id

    artifact_id = go_pkg_key(artifact)
    normalized_version = normalize_go_ver(artifact.version)

    old_version = pkg.get("versionInfo")
    if isinstance(old_version, str) and old_version and old_version != normalized_version:
        normalized_old_version = normalize_go_ver(old_version)
        if normalized_old_version == normalized_version:
            pkg["versionInfo"] = normalized_version
            findings.append(PackageValidationFinding(
                artifact=artifact_id,
                spdx_id=spdx_id,
                field="versionInfo",
                action="normalized",
                old_value=old_version,
                new_value=normalized_version,
                notes="Normalized Go module version to canonical v-prefixed form.",
            ))

    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "packageFileName", metadata.package_file_name, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "downloadLocation", metadata.zip_url, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "homepage", metadata.homepage, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseDeclared", metadata.license_declared, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseConcluded", metadata.license_declared, findings)

    refs = pkg.setdefault("externalRefs", [])
    wanted_purl = go_pkg_purl(artifact)
    has_purl = False
    replaced_equivalent_purl = False

    for ref in refs:
        if not isinstance(ref, dict) or ref.get("referenceType") != "purl":
            continue
        loc = ref.get("referenceLocator")
        if loc == wanted_purl:
            has_purl = True
            continue
        if isinstance(loc, str) and loc.startswith("pkg:golang/") and "@" in loc:
            try:
                body = loc[len("pkg:golang/"):].split("?", 1)[0]
                module_part, version_part = body.rsplit("@", 1)
                if go_id_key(module_part, version_part) == artifact_id:
                    ref["referenceLocator"] = wanted_purl
                    has_purl = True
                    replaced_equivalent_purl = True
                    findings.append(PackageValidationFinding(
                        artifact=artifact_id,
                        spdx_id=spdx_id,
                        field="externalRefs.purl",
                        action="normalized",
                        old_value=loc,
                        new_value=wanted_purl,
                        notes="Normalized existing Go purl to canonical module version/casing form.",
                    ))
            except Exception:
                continue

    if not has_purl:
        refs.append({"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": wanted_purl})
        findings.append(PackageValidationFinding(artifact=artifact_id, spdx_id=spdx_id, field="externalRefs.purl", action="filled", old_value=None, new_value=wanted_purl))

    dedupe_pkg_external_refs(pkg)


def resolve_go_transitives(
    roots: list[GoArtifact],
    max_depth: int,
    max_artifacts: int | None = 2000,
) -> tuple[dict[str, GoArtifact], list[DependencyEdge], list[ResolutionIssue], list[SkippedArtifact]]:
    discovered: dict[str, GoArtifact] = {}
    edges: list[DependencyEdge] = []
    issues: list[ResolutionIssue] = []
    skipped: list[SkippedArtifact] = []
    queue: list[tuple[GoArtifact, int]] = [(a, 0) for a in roots]
    processed: set[str] = set()

    while queue:
        if max_artifacts is not None and len(discovered) >= max_artifacts:
            issues.append(ResolutionIssue("go:artifact-limit", f"Stopped Go traversal after reaching --go-max-artifacts={max_artifacts}; remaining queue={len(queue)}"))
            break

        current, depth = queue.pop(0)
        key = go_pkg_key(current)
        if key not in discovered:
            discovered[key] = current
        if key in processed:
            continue
        processed.add(key)
        if depth >= max_depth:
            continue

        children, child_issues = resolve_go_pkg(current)
        issues.extend(child_issues)
        for child in children:
            child_key = go_pkg_key(child)
            edges.append(DependencyEdge(parent=key, child=child_key))
            if child_key not in discovered:
                discovered[child_key] = child
                queue.append((child, depth + 1))

        if len(processed) and len(processed) % 100 == 0:
            print(f"[GO] processed={len(processed)} discovered={len(discovered)} queued={len(queue)} issues={len(issues)} skipped={len(skipped)}")

    return discovered, edges, issues, skipped


def merge_missing_pkg_fields(target: dict[str, Any], duplicate: dict[str, Any]) -> None:
    for field_name, value in duplicate.items():
        if field_name in {"SPDXID", "name", "externalRefs"}:
            continue
        if field_name not in target or missing_or_noassert(target.get(field_name)):
            target[field_name] = value

    target_refs = target.setdefault("externalRefs", [])
    existing_refs = {json.dumps(ref, sort_keys=True) for ref in target_refs if isinstance(ref, dict)}
    for ref in duplicate.get("externalRefs", []) or []:
        if not isinstance(ref, dict):
            continue
        key = json.dumps(ref, sort_keys=True)
        if key not in existing_refs:
            target_refs.append(ref)
            existing_refs.add(key)


def normalize_go_pkgs(sbom_data: dict[str, Any], findings: list[PackageValidationFinding]) -> None:
    sbom = sbom_data.get("sbom", sbom_data)
    packages = sbom.get("packages", []) or []
    canonical_by_identity: dict[str, dict[str, Any]] = {}
    duplicate_spdx_to_canonical: dict[str, str] = {}
    packages_to_remove: set[str] = set()

    for pkg in packages:
        if not isinstance(pkg, dict):
            continue

        go_refs = [
            ref for ref in pkg.get("externalRefs", []) or []
            if isinstance(ref, dict)
            and ref.get("referenceType") == "purl"
            and isinstance(ref.get("referenceLocator"), str)
            and ref.get("referenceLocator", "").startswith("pkg:golang/")
        ]
        if not go_refs:
            continue

        first_parsed = parse_go_purl(go_refs[0].get("referenceLocator"))
        if not first_parsed:
            continue
        module, normalized_version = first_parsed
        identity = go_id_key(module, normalized_version)
        wanted_purl = go_purl(module, normalized_version)
        spdx_id = pkg.get("SPDXID") if isinstance(pkg.get("SPDXID"), str) else "NOASSERTION"

        old_version = pkg.get("versionInfo")
        if isinstance(old_version, str) and old_version and normalize_go_ver(old_version) == normalized_version and old_version != normalized_version:
            pkg["versionInfo"] = normalized_version
            findings.append(PackageValidationFinding(
                artifact=identity,
                spdx_id=spdx_id,
                field="versionInfo",
                action="normalized",
                old_value=old_version,
                new_value=normalized_version,
                notes="Normalized existing Go package version before identity mapping.",
            ))

        new_refs: list[dict[str, Any]] = []
        kept_go_purl = False
        seen_ref_keys: set[str] = set()
        for ref in pkg.get("externalRefs", []) or []:
            if not isinstance(ref, dict):
                continue
            loc = ref.get("referenceLocator")
            parsed = parse_go_purl(loc) if isinstance(loc, str) else None
            if parsed and go_id_key(parsed[0], parsed[1]) == identity:
                if not kept_go_purl:
                    old_loc = loc
                    ref = dict(ref)
                    ref["referenceLocator"] = wanted_purl
                    new_refs.append(ref)
                    kept_go_purl = True
                    if old_loc != wanted_purl:
                        findings.append(PackageValidationFinding(
                            artifact=identity,
                            spdx_id=spdx_id,
                            field="externalRefs.purl",
                            action="normalized",
                            old_value=old_loc if isinstance(old_loc, str) else None,
                            new_value=wanted_purl,
                            notes="Normalized existing Go purl before identity mapping.",
                        ))
                continue

            ref_key = json.dumps(ref, sort_keys=True)
            if ref_key not in seen_ref_keys:
                new_refs.append(ref)
                seen_ref_keys.add(ref_key)
        pkg["externalRefs"] = new_refs

        existing = canonical_by_identity.get(identity)
        if existing is None:
            canonical_by_identity[identity] = pkg
            continue

        existing_spdx = existing.get("SPDXID")
        dup_spdx = pkg.get("SPDXID")
        if isinstance(existing_spdx, str) and isinstance(dup_spdx, str) and existing_spdx != dup_spdx:
            merge_missing_pkg_fields(existing, pkg)
            duplicate_spdx_to_canonical[dup_spdx] = existing_spdx
            packages_to_remove.add(dup_spdx)
            findings.append(PackageValidationFinding(
                artifact=identity,
                spdx_id=existing_spdx,
                field="package",
                action="deduped",
                old_value=dup_spdx,
                new_value=existing_spdx,
                notes="Removed semantic duplicate Go package after normalizing purl/version.",
            ))

    if duplicate_spdx_to_canonical:
        for rel in sbom.get("relationships", []) or []:
            if not isinstance(rel, dict):
                continue
            src = rel.get("spdxElementId")
            dst = rel.get("relatedSpdxElement")
            if isinstance(src, str) and src in duplicate_spdx_to_canonical:
                rel["spdxElementId"] = duplicate_spdx_to_canonical[src]
            if isinstance(dst, str) and dst in duplicate_spdx_to_canonical:
                rel["relatedSpdxElement"] = duplicate_spdx_to_canonical[dst]

        sbom["packages"] = [pkg for pkg in packages if not (isinstance(pkg, dict) and isinstance(pkg.get("SPDXID"), str) and pkg.get("SPDXID") in packages_to_remove)]

        seen_relationships: set[tuple[str, str, str]] = set()
        deduped_relationships: list[dict[str, Any]] = []
        for rel in sbom.get("relationships", []) or []:
            if not isinstance(rel, dict):
                continue
            key = (str(rel.get("spdxElementId")), str(rel.get("relatedSpdxElement")), str(rel.get("relationshipType")))
            if key in seen_relationships:
                continue
            seen_relationships.add(key)
            deduped_relationships.append(rel)
        sbom["relationships"] = deduped_relationships

def dedupe_external_refs(sbom_data: dict[str, Any], findings: list[PackageValidationFinding]) -> None:
    sbom = sbom_data.get("sbom", sbom_data)
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        removed = dedupe_pkg_external_refs(pkg)
        if removed:
            findings.append(PackageValidationFinding(
                artifact=str(pkg.get("name") or pkg.get("SPDXID") or "package"),
                spdx_id=str(pkg.get("SPDXID") or "NOASSERTION"),
                field="externalRefs",
                action="deduped",
                old_value=str(removed),
                new_value="0 duplicate refs",
                notes="Removed duplicate externalRefs within a single package.",
            ))

def add_go_transitives(
    sbom_data: dict[str, Any],
    discovered: dict[str, GoArtifact],
    edges: list[DependencyEdge],
) -> tuple[dict[str, Any], list[PackageValidationFinding], list[ResolutionIssue]]:
    sbom = sbom_data.get("sbom", sbom_data)
    sbom.setdefault("packages", [])
    sbom.setdefault("relationships", [])

    findings: list[PackageValidationFinding] = []
    metadata_issues: list[ResolutionIssue] = []

    normalize_go_pkgs(sbom_data, findings)
    dedupe_external_refs(sbom_data, findings)
    identity_to_spdxid = build_go_id_to_spdxid(sbom_data)
    identity_to_package = build_go_id_to_pkg(sbom_data)

    for key, artifact in discovered.items():
        metadata, issues = get_go_metadata_from_proxy(artifact)
        metadata_issues.extend(issues)
        if key in identity_to_spdxid:
            existing_spdx = identity_to_spdxid[key]
            existing_pkg = identity_to_package.get(key)
            findings.append(PackageValidationFinding(
                artifact=key,
                spdx_id=existing_spdx,
                field="package",
                action="existed",
                old_value=go_pkg_purl(artifact),
                new_value=go_pkg_purl(artifact),
                notes="Go module was already present in the input SBOM; enrichment/validation was attempted.",
            ))
            if existing_pkg is not None:
                enrich_pkg_with_go_metadata(existing_pkg, artifact, metadata, findings)
            continue

        package = go_pkg_to_spdx_pkg(artifact, metadata)
        sbom["packages"].append(package)
        identity_to_spdxid[key] = package["SPDXID"]
        identity_to_package[key] = package
        findings.append(PackageValidationFinding(
            artifact=key,
            spdx_id=package["SPDXID"],
            field="package",
            action="added",
            old_value=None,
            new_value=go_pkg_purl(artifact),
            notes="Package added from Go module proxy transitive resolution.",
        ))

    for edge in edges:
        parent_spdxid = identity_to_spdxid.get(edge.parent)
        child_spdxid = identity_to_spdxid.get(edge.child)
        if not parent_spdxid or not child_spdxid:
            continue
        if has_relationship(sbom_data, parent_spdxid, child_spdxid, "DEPENDS_ON"):
            continue
        sbom["relationships"].append({"spdxElementId": parent_spdxid, "relatedSpdxElement": child_spdxid, "relationshipType": "DEPENDS_ON"})

    dedupe_external_refs(sbom_data, findings)
    return sbom_data, findings, metadata_issues


# -------------------------
# Rust / crates.io helpers
# -------------------------

CRATES_IO_API = "https://crates.io/api/v1"
CRATES_IO_CACHE: dict[str, dict[str, Any]] = {}
CRATES_IO_DEP_CACHE: dict[str, dict[str, Any]] = {}
CRATES_IO_VERSION_CACHE: dict[str, dict[str, Any]] = {}


@dataclass(frozen=True)
class RustArtifact:
    name: str
    version: str
    scope: str = "runtime"
    source: str | None = None
    requested: str | None = None


@dataclass(frozen=True)
class RustPackageMetadata:
    artifact: str
    registry_url: str | None = None
    crate_url: str | None = None
    download_url: str | None = None
    package_file_name: str | None = None
    homepage: str | None = None
    repository: str | None = None
    supplier: str | None = None
    license_declared: str | None = None
    checksum_sha256: str | None = None
    description: str | None = None

RUST_EXCLUDED_TRANSITIVE_KINDS: set[str] = set()

def canonical_rust_name(name: str) -> str:
    value = urllib.parse.unquote((name or "").strip())
    if value.startswith("pkg:cargo/"):
        body = value[len("pkg:cargo/"):].split("?", 1)[0]
        if "@" in body:
            body = body.rsplit("@", 1)[0]
        value = body
    return value.strip()


def rust_purl(name: str, version: str) -> str:
    return f"pkg:cargo/{urllib.parse.quote(canonical_rust_name(name), safe='')}@{urllib.parse.quote((version or '').strip(), safe='')}"


def rust_pkg_key(a: RustArtifact) -> str:
    return rust_purl(a.name.lower(), a.version)


def rust_pkg_purl(a: RustArtifact) -> str:
    return rust_purl(a.name, a.version)


def rust_pkg_spdxid(a: RustArtifact) -> str:
    safe = re.sub(r"[^A-Za-z0-9.-]+", "-", f"cargo-{a.name}-{a.version}").strip("-")
    return f"SPDXRef-transitive-{safe}"


def crates_io_url(crate_name: str, *parts: str) -> str:
    encoded_name = urllib.parse.quote(canonical_rust_name(crate_name), safe="")
    suffix = "/".join(urllib.parse.quote(str(p), safe="") for p in parts if p is not None)
    return f"{CRATES_IO_API}/crates/{encoded_name}" + (f"/{suffix}" if suffix else "")


def get_crates_json(url: str) -> dict[str, Any]:
    request = urllib.request.Request(url, headers={"User-Agent": "RestoreSBOM research prototype (SBOM transitive dependency validation)", "Accept": "application/json"})
    with urllib.request.urlopen(request, timeout=20) as response:
        return json.loads(response.read().decode("utf-8", errors="replace"))


def get_crates_json_or_none(url: str, artifact_id: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    try:
        return get_crates_json(url), []
    except urllib.error.HTTPError as e:
        return None, [ResolutionIssue(artifact_id, f"crates.io fetch failed: HTTP {e.code} at {url}")]
    except Exception as e:
        return None, [ResolutionIssue(artifact_id, f"crates.io fetch failed: {type(e).__name__}: {e}")]


def rust_issue_is_crates_io_404(issue: ResolutionIssue) -> bool:
    return "crates.io fetch failed: HTTP 404" in issue.reason


def rust_issues_are_crates_io_404_only(issues: list[ResolutionIssue]) -> bool:
    return bool(issues) and all(rust_issue_is_crates_io_404(issue) for issue in issues)


def get_crate_packument(crate_name: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    name = canonical_rust_name(crate_name)
    key = name.lower()
    if key in CRATES_IO_CACHE:
        return CRATES_IO_CACHE[key], []
    url = crates_io_url(name)
    data, issues = get_crates_json_or_none(url, rust_purl(name, "latest"))
    if data is not None:
        CRATES_IO_CACHE[key] = data
    return data, issues


def get_crate_version_metadata(crate_name: str, version: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    name = canonical_rust_name(crate_name)
    version = (version or "").strip()
    artifact_id = rust_purl(name, version or "NOASSERTION")
    if not name or not version:
        return None, [ResolutionIssue(artifact_id, "Missing crate name or version for crates.io version metadata lookup")]

    cache_key = f"{name.lower()}@{version}"
    if cache_key in CRATES_IO_VERSION_CACHE:
        return CRATES_IO_VERSION_CACHE[cache_key], []

    packument, packument_issues = get_crate_packument(name)
    if isinstance(packument, dict):
        crate_obj = packument.get("crate") if isinstance(packument.get("crate"), dict) else {}
        versions = packument.get("versions")
        if isinstance(versions, list):
            for item in versions:
                if isinstance(item, dict) and item.get("num") == version:
                    data = {"crate": crate_obj, "version": item}
                    CRATES_IO_VERSION_CACHE[cache_key] = data
                    return data, []

    data, version_issues = get_crates_json_or_none(crates_io_url(name, version), artifact_id)
    if isinstance(data, dict):
        version_obj = data.get("version") if isinstance(data.get("version"), dict) else {}
        crate_obj = data.get("crate") if isinstance(data.get("crate"), dict) else {}
        if isinstance(version_obj, dict) and version_obj.get("num") == version:
            out = {"crate": crate_obj, "version": version_obj}
            CRATES_IO_VERSION_CACHE[cache_key] = out
            return out, []

    issues = [*packument_issues, *version_issues]

    if rust_issues_are_crates_io_404_only(issues):
        return None, []

    issues.append(ResolutionIssue(artifact_id, "Exact crate version was not confirmed by crates.io; metadata fields were left unchanged/NOASSERTION."))
    return None, issues


def get_crate_dependencies(crate_name: str, version: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    name = canonical_rust_name(crate_name)
    version = (version or "").strip()
    key = f"{name.lower()}@{version}"
    if key in CRATES_IO_DEP_CACHE:
        return CRATES_IO_DEP_CACHE[key], []
    url = crates_io_url(name, version, "dependencies")
    data, issues = get_crates_json_or_none(url, rust_purl(name, version))
    if data is not None:
        CRATES_IO_DEP_CACHE[key] = data
    return data, issues


def parse_rust_ver(version: str) -> tuple[int, int, int, str] | None:
    m = re.match(r"^v?(\d+)\.(\d+)\.(\d+)([-+].*)?$", (version or "").strip())
    if not m:
        return None
    return int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4) or ""


def rust_ver_key(version: str) -> tuple[int, int, int, int, list[Any]]:
    parsed = parse_rust_ver(version)
    if not parsed:
        return (-1, -1, -1, -1, [version])
    major, minor, patch, suffix = parsed
    stable = 1 if not suffix.startswith("-") else 0
    prerelease_key: list[Any] = []
    if suffix.startswith("-"):
        prerelease = suffix[1:].split("+", 1)[0]
        for part in re.split(r"[.-]", prerelease):
            prerelease_key.append((0, int(part)) if part.isdigit() else (1, part))
    return major, minor, patch, stable, prerelease_key


def compare_rust_ver(a: str, b: str) -> int:
    ka = rust_ver_key(a)
    kb = rust_ver_key(b)
    return (ka > kb) - (ka < kb)


def normalize_partial_rust_ver(version: str) -> str:
    value = (version or "").strip().lstrip("v")
    if re.match(r"^\d+$", value):
        return f"{value}.0.0"
    if re.match(r"^\d+\.\d+$", value):
        return f"{value}.0"
    return value


def rust_ver_parts(version: str) -> int:
    value = (version or "").strip().lstrip("v")
    value = value.split("-", 1)[0].split("+", 1)[0]
    return len([part for part in value.split(".") if part != ""])


def is_rust_prerelease(version: str) -> bool:
    parsed = parse_rust_ver(version)
    return bool(parsed and parsed[3].startswith("-"))


def rust_req_has_prerelease(req: str | None) -> bool:
    return bool(req and re.search(r"\d+\.\d+\.\d+-[0-9A-Za-z]", str(req)))


def rust_expand_caret(version: str) -> list[str]:
    original_raw = (version or "").strip().lstrip("v")
    part_count = rust_ver_parts(original_raw)
    original = normalize_partial_rust_ver(original_raw)
    parsed = parse_rust_ver(original)
    if not parsed:
        return [version]

    major, minor, patch, _suffix = parsed
    lower = f">={original}"

    if major > 0:
        upper = f"<{major + 1}.0.0"
    elif part_count <= 1:
        upper = "<1.0.0"
    elif minor > 0:
        upper = f"<0.{minor + 1}.0"
    elif part_count <= 2:
        upper = "<0.1.0"
    else:
        upper = f"<0.0.{patch + 1}"

    return [lower, upper]


def rust_expand_tilde(version: str) -> list[str]:
    original_raw = (version or "").strip().lstrip("v")
    part_count = rust_ver_parts(original_raw)
    original = normalize_partial_rust_ver(original_raw)
    parsed = parse_rust_ver(original)
    if not parsed:
        return [version]

    major, minor, _patch, _suffix = parsed
    lower = f">={original}"

    if part_count <= 1:
        upper = f"<{major + 1}.0.0"
    else:
        upper = f"<{major}.{minor + 1}.0"

    return [lower, upper]


def is_non_registry_rust_dep(req: str | None) -> bool:
    if not req:
        return False
    value = req.strip().lower()
    return value.startswith(("git+", "git://", "http://", "https://", "path:", "file:"))


def normalize_rust_ranges(req: str | None) -> list[list[str]]:
    if req is None or not str(req).strip() or str(req).strip() in {"*", "x", "X"}:
        return [["*"]]

    spec = str(req).strip()
    spec = re.sub(r"(>=|<=|>|<|=)\s+(?=\d|v)", r"\1", spec)
    groups: list[list[str]] = []

    for raw_group in spec.split("||"):
        raw_group = raw_group.strip()
        if not raw_group:
            continue
        comparators: list[str] = []
        for token in re.split(r"\s*,\s*|\s+", raw_group):
            token = token.strip()
            if not token:
                continue
            if token.startswith("^"):
                comparators.extend(rust_expand_caret(token[1:]))
            elif token.startswith("~"):
                comparators.extend(rust_expand_tilde(token[1:]))
            elif re.match(r"^\d+$", token):
                major = int(token)
                comparators.extend([f">={major}.0.0", f"<{major + 1}.0.0"])
            elif re.match(r"^\d+\.\d+$", token):
                major, minor = token.split(".")
                comparators.extend([f">={major}.{minor}.0", f"<{major}.{int(minor) + 1}.0"])
            elif re.match(r"^\d+\.\d+\.\d+(?:[-+].*)?$", token):
                comparators.extend(rust_expand_caret(token))
            else:
                comparators.append(token)
        groups.append(comparators or ["*"])
    return groups or [["*"]]


def rust_ver_matches_comparator(version: str, comparator: str) -> bool:
    comp = (comparator or "").strip()
    if not comp or comp in {"*", "x", "X"}:
        return True

    if re.search(r"(^|\.)(x|X|\*)($|\.)", comp):
        target = comp.lstrip("=").strip()
        parts = target.split(".")
        parsed = parse_rust_ver(version)
        if not parsed:
            return False
        vmaj, vmin, _vpatch, _suffix = parsed
        try:
            major = int(parts[0]) if parts[0] not in {"x", "X", "*"} else None
            minor = int(parts[1]) if len(parts) > 1 and parts[1] not in {"x", "X", "*"} else None
        except ValueError:
            return False
        if major is None:
            return True
        if vmaj != major:
            return False
        if minor is None:
            return True
        return vmin == minor

    m = re.match(r"^(>=|<=|>|<|=)?\s*v?([^\s]+)$", comp)
    if not m:
        return False
    op = m.group(1) or "="
    target = normalize_partial_rust_ver(m.group(2))
    if not parse_rust_ver(target):
        return False
    cmp = compare_rust_ver(version, target)
    if op == "=":
        raw_target = m.group(2).strip().lstrip("v")
        if rust_ver_parts(raw_target) < 3:
            return rust_ver_matches_range(version, raw_target)
        return cmp == 0
    if op == ">=":
        return cmp >= 0
    if op == "<=":
        return cmp <= 0
    if op == ">":
        return cmp > 0
    if op == "<":
        return cmp < 0
    return False


def rust_ver_matches_range(version: str, req: str | None) -> bool:
    if req is None or not str(req).strip() or str(req).strip() in {"*", "x", "X"}:
        return True
    if is_non_registry_rust_dep(str(req)):
        return False
    return any(all(rust_ver_matches_comparator(version, comp) for comp in group) for group in normalize_rust_ranges(str(req)))


def resolve_rust_ver(crate_name: str, req: str | None) -> tuple[str | None, list[ResolutionIssue]]:
    name = canonical_rust_name(crate_name)
    requested = str(req or "*").strip()

    if is_non_registry_rust_dep(req):
        return None, [ResolutionIssue(rust_purl(name, "NOASSERTION"), f"Skipped non-registry Cargo dependency requirement: {req}")]

    packument, issues = get_crate_packument(name)
    if not packument:
        return None, issues

    versions = packument.get("versions")
    if not isinstance(versions, list) or not versions:
        return None, [*issues, ResolutionIssue(rust_purl(name, "NOASSERTION"), "crates.io response contained no versions")]

    allow_prerelease = rust_req_has_prerelease(requested)

    non_yanked: list[str] = []
    yanked: list[str] = []
    for version_obj in versions:
        if not isinstance(version_obj, dict):
            continue
        num = version_obj.get("num")
        if not isinstance(num, str) or not parse_rust_ver(num):
            continue
        if is_rust_prerelease(num) and not allow_prerelease:
            continue
        if version_obj.get("yanked") is True:
            yanked.append(num)
        else:
            non_yanked.append(num)

    def choose(candidates: list[str]) -> str | None:
        satisfying = [v for v in candidates if rust_ver_matches_range(v, requested)]
        return sorted(satisfying, key=rust_ver_key)[-1] if satisfying else None

    selected = choose(non_yanked)
    if selected:
        return selected, issues

    selected_yanked = choose(yanked)
    if selected_yanked:
        return selected_yanked, issues

    available = non_yanked + yanked
    if not available:
        return None, [*issues, ResolutionIssue(rust_purl(name, "NOASSERTION"), f"No semver versions available for requirement {requested}")]

    return None, [*issues, ResolutionIssue(rust_purl(name, "NOASSERTION"), f"Could not resolve Cargo version requirement: {requested}")]

def rust_scope_from_dep_kind(kind: Any) -> str:
    if isinstance(kind, str) and kind.strip():
        return kind.strip().lower()
    return "runtime"


def should_include_rust_dep(dep_obj: dict[str, Any]) -> tuple[bool, str | None]:
    kind = rust_scope_from_dep_kind(dep_obj.get("kind"))
    optional = dep_obj.get("optional") is True

    if kind in RUST_EXCLUDED_TRANSITIVE_KINDS:
        return False, f"Excluded Cargo transitive kind: {kind}"
    if optional:
        return False, "Excluded optional Cargo dependency because activating Cargo features is outside current resolver scope."
    return True, None


def resolve_rust_pkg(artifact: RustArtifact) -> tuple[list[RustArtifact], list[ResolutionIssue], list[SkippedArtifact]]:
    data, issues = get_crate_dependencies(artifact.name, artifact.version)
    if data is None:
        if rust_issues_are_crates_io_404_only(issues):
            return [], [], [SkippedArtifact(
                artifact=rust_pkg_key(artifact),
                source=artifact.source,
                scope=artifact.scope,
                reason="Cargo package was not found on crates.io; treated as a workspace/path/private non-registry crate candidate, so no registry metadata was guessed.",
            )]
        return [], issues, []

    raw_deps = data.get("dependencies")
    if not isinstance(raw_deps, list):
        return [], issues, []

    children: list[RustArtifact] = []
    skipped: list[SkippedArtifact] = []

    for dep in raw_deps:
        if not isinstance(dep, dict):
            continue
        dep_name = dep.get("crate_id") or dep.get("name")
        req = dep.get("req")
        if not isinstance(dep_name, str) or not dep_name.strip():
            issues.append(ResolutionIssue(rust_pkg_key(artifact), f"Cargo dependency missing crate_id/name: {dep}"))
            continue

        include, reason = should_include_rust_dep(dep)
        dep_scope = rust_scope_from_dep_kind(dep.get("kind"))
        if not include:
            skipped.append(SkippedArtifact(
                artifact=rust_purl(dep_name, str(req or "NOASSERTION")),
                source=rust_pkg_key(artifact),
                scope=dep_scope,
                reason=reason or "Excluded Cargo dependency",
            ))
            continue

        dep_version, version_issues = resolve_rust_ver(dep_name, str(req or "*"))
        issues.extend(version_issues)
        if not dep_version:
            continue

        children.append(RustArtifact(name=dep_name, version=dep_version, scope=dep_scope, source=rust_pkg_key(artifact), requested=str(req) if req is not None else None))

    return children, issues, skipped


def get_rust_metadata_from_crates_io(artifact: RustArtifact) -> tuple[RustPackageMetadata, list[ResolutionIssue]]:
    key = rust_pkg_key(artifact)
    name = canonical_rust_name(artifact.name)
    version = (artifact.version or "").strip()

    version_data, issues = get_crate_version_metadata(name, version)
    if not isinstance(version_data, dict):
        return RustPackageMetadata(artifact=key), issues

    crate_obj = version_data.get("crate") if isinstance(version_data.get("crate"), dict) else {}
    version_obj = version_data.get("version") if isinstance(version_data.get("version"), dict) else {}

    homepage = None
    for field_name in ("homepage", "repository", "documentation"):
        value = crate_obj.get(field_name) or version_obj.get(field_name)
        if isinstance(value, str) and value.strip():
            homepage = value.strip()
            break

    repository = crate_obj.get("repository") if isinstance(crate_obj.get("repository"), str) and crate_obj.get("repository").strip() else None
    license_value = version_obj.get("license") or crate_obj.get("license")
    license_declared = license_name_to_spdx(license_value) if isinstance(license_value, str) and license_value.strip() else None
    checksum = version_obj.get("checksum") if isinstance(version_obj.get("checksum"), str) and version_obj.get("checksum").strip() else None
    description = crate_obj.get("description") if isinstance(crate_obj.get("description"), str) else None

    metadata = RustPackageMetadata(
        artifact=key,
        registry_url=crates_io_url(name, version),
        crate_url=f"https://crates.io/crates/{urllib.parse.quote(name, safe='')}/{urllib.parse.quote(version, safe='')}",
        download_url=f"https://crates.io/api/v1/crates/{urllib.parse.quote(name, safe='')}/{urllib.parse.quote(version, safe='')}/download",
        package_file_name=f"{name}-{version}.crate",
        homepage=homepage,
        repository=repository,
        supplier=None,
        license_declared=license_declared,
        checksum_sha256=checksum,
        description=description,
    )

    missing: list[str] = []
    if not metadata.license_declared:
        missing.append("license")
    if not metadata.checksum_sha256:
        missing.append("checksum")
    if missing:
        issues.append(ResolutionIssue(key, "crates.io confirmed the exact version, but did not provide: " + ", ".join(missing)))

    return metadata, issues


def parse_rust_purl(locator: str) -> tuple[str, str | None] | None:
    if not isinstance(locator, str) or not locator.startswith("pkg:cargo/"):
        return None

    body = locator[len("pkg:cargo/"):].split("?", 1)[0]
    version = None
    if "@" in body:
        name_part, version = body.rsplit("@", 1)
        version = urllib.parse.unquote(version).strip()
    else:
        name_part = body

    name = canonical_rust_name(name_part)
    if not name:
        return None
    return name, version


def is_exact_rust_req(value: str | None) -> bool:
    return bool(value and parse_rust_ver(str(value).strip()))


def normalize_rust_pkg_ver(crate_name: str, version_or_requirement: str | None) -> tuple[str | None, list[ResolutionIssue]]:
    value = (version_or_requirement or "").strip()
    if not value or value == "NOASSERTION":
        return None, []

    if is_exact_rust_req(value):
        return value, []

    return resolve_rust_ver(crate_name, value)


def get_rust_pkgs(sbom_data: dict[str, Any]) -> list[RustArtifact]:
    sbom = sbom_data.get("sbom", sbom_data)
    artifacts: list[RustArtifact] = []

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        cargo_refs = []
        for ref in pkg.get("externalRefs", []) or []:
            if not isinstance(ref, dict):
                continue
            loc = ref.get("referenceLocator")
            parsed = parse_rust_purl(loc) if isinstance(loc, str) else None
            if parsed:
                cargo_refs.append(parsed)

        for name, purl_version in cargo_refs:
            version_candidate = purl_version
            if not version_candidate:
                version_info = pkg.get("versionInfo")
                version_candidate = version_info if isinstance(version_info, str) else None

            resolved_version, _issues = normalize_rust_pkg_ver(name, version_candidate)
            if resolved_version:
                artifacts.append(RustArtifact(name=name, version=resolved_version, source="surface_sbom", requested=version_candidate if version_candidate != resolved_version else None))

    return dedupe_rust_pkgs(artifacts)

def dedupe_rust_pkgs(artifacts: list[RustArtifact]) -> list[RustArtifact]:
    out: list[RustArtifact] = []
    seen: set[str] = set()
    for artifact in artifacts:
        key = rust_pkg_key(artifact)
        if key in seen:
            continue
        seen.add(key)
        out.append(artifact)
    return out


def get_rust_id(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        if not isinstance(ref, dict):
            continue
        loc = ref.get("referenceLocator")
        parsed = parse_rust_purl(loc) if isinstance(loc, str) else None
        if parsed:
            name, version = parsed
            if version and is_exact_rust_req(version):
                return rust_purl(canonical_rust_name(name).lower(), version)

    name = pkg.get("name")
    version = pkg.get("versionInfo")
    if (isinstance(name, str) and isinstance(version, str) and version and version != "NOASSERTION" and is_exact_rust_req(version)):
        return rust_purl(canonical_rust_name(name).lower(), version)
    return None


def normalize_rust_pkgs(sbom_data: dict[str, Any], discovered: dict[str, RustArtifact]) -> tuple[list[PackageValidationFinding], list[ResolutionIssue]]:
    sbom = sbom_data.get("sbom", sbom_data)
    findings: list[PackageValidationFinding] = []
    issues: list[ResolutionIssue] = []

    discovered_by_name: dict[str, list[RustArtifact]] = {}
    for artifact in discovered.values():
        discovered_by_name.setdefault(canonical_rust_name(artifact.name).lower(), []).append(artifact)

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        refs = pkg.get("externalRefs", []) or []
        parsed_refs: list[tuple[dict[str, Any], str, str | None]] = []
        for ref in refs:
            if not isinstance(ref, dict):
                continue
            loc = ref.get("referenceLocator")
            parsed = parse_rust_purl(loc) if isinstance(loc, str) else None
            if parsed:
                parsed_refs.append((ref, parsed[0], parsed[1]))

        if not parsed_refs:
            continue

        ref, name, purl_version = parsed_refs[0]
        current_version = pkg.get("versionInfo") if isinstance(pkg.get("versionInfo"), str) else None
        requirement = purl_version or current_version

        resolved_version: str | None = None
        local_issues: list[ResolutionIssue] = []

        if requirement and is_exact_rust_req(requirement):
            resolved_version = requirement.strip()
        else:
            resolved_version, local_issues = normalize_rust_pkg_ver(name, requirement)
            if not resolved_version:
                same_name = discovered_by_name.get(canonical_rust_name(name).lower(), [])
                unique_versions = sorted({a.version for a in same_name})
                if len(unique_versions) == 1:
                    resolved_version = unique_versions[0]
                else:
                    if rust_issues_are_crates_io_404_only(local_issues):
                        findings.append(PackageValidationFinding(
                            artifact=rust_purl(name, requirement or "NOASSERTION"),
                            spdx_id=str(pkg.get("SPDXID") or "NOASSERTION"),
                            field="versionInfo/externalRefs.referenceLocator",
                            action="skipped",
                            old_value=f"versionInfo={current_version}; purl={ref.get('referenceLocator')}",
                            new_value=None,
                            notes="Cargo package was not found on crates.io; treated as a workspace/path/private non-registry crate candidate. Existing SBOM identity was preserved and no metadata was guessed.",
                        ))
                    else:
                        issues.extend(local_issues)
                        findings.append(PackageValidationFinding(
                            artifact=rust_purl(name, requirement or "NOASSERTION"),
                            spdx_id=str(pkg.get("SPDXID") or "NOASSERTION"),
                            field="versionInfo/externalRefs.referenceLocator",
                            action="unresolved",
                            old_value=f"versionInfo={current_version}; purl={ref.get('referenceLocator')}",
                            new_value=None,
                            notes="Could not resolve Cargo surface requirement to one exact crates.io version.",
                        ))
                    continue

        wanted_purl = rust_purl(name, resolved_version)
        old_version = pkg.get("versionInfo")
        old_locator = ref.get("referenceLocator")
        pkg["versionInfo"] = resolved_version

        first = True
        new_refs: list[dict[str, Any]] = []
        for existing_ref in refs:
            if not isinstance(existing_ref, dict):
                new_refs.append(existing_ref)
                continue
            loc = existing_ref.get("referenceLocator")
            if isinstance(loc, str) and loc.startswith("pkg:cargo/"):
                if first:
                    existing_ref = dict(existing_ref)
                    existing_ref["referenceCategory"] = "PACKAGE-MANAGER"
                    existing_ref["referenceType"] = "purl"
                    existing_ref["referenceLocator"] = wanted_purl
                    new_refs.append(existing_ref)
                    first = False
                continue
            new_refs.append(existing_ref)
        if first:
            new_refs.append({"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": wanted_purl})
        pkg["externalRefs"] = new_refs
        dedupe_pkg_external_refs(pkg)

        if old_version != resolved_version or old_locator != wanted_purl:
            findings.append(PackageValidationFinding(
                artifact=rust_purl(name, resolved_version),
                spdx_id=str(pkg.get("SPDXID") or rust_pkg_spdxid(RustArtifact(name, resolved_version))),
                field="versionInfo/externalRefs.referenceLocator",
                action="filled",
                old_value=f"versionInfo={old_version}; purl={old_locator}",
                new_value=f"versionInfo={resolved_version}; purl={wanted_purl}",
                notes="Normalized Cargo surface package to an exact crates.io version before enrichment.",
            ))

    return findings, issues


def dedupe_rust_pkgs_by_id(sbom_data: dict[str, Any]) -> list[PackageValidationFinding]:
    sbom = sbom_data.get("sbom", sbom_data)
    packages = sbom.get("packages", []) or []
    findings: list[PackageValidationFinding] = []
    identity_to_pkg: dict[str, dict[str, Any]] = {}
    spdx_rewrite: dict[str, str] = {}
    kept: list[dict[str, Any]] = []

    for pkg in packages:
        if not isinstance(pkg, dict):
            kept.append(pkg)
            continue
        identity = get_rust_id(pkg)
        if not identity:
            kept.append(pkg)
            continue
        if identity not in identity_to_pkg:
            identity_to_pkg[identity] = pkg
            kept.append(pkg)
            continue

        retained = identity_to_pkg[identity]
        old_spdx = pkg.get("SPDXID")
        new_spdx = retained.get("SPDXID")
        if isinstance(old_spdx, str) and isinstance(new_spdx, str) and old_spdx != new_spdx:
            spdx_rewrite[old_spdx] = new_spdx
            findings.append(PackageValidationFinding(
                artifact=identity,
                spdx_id=new_spdx,
                field="package",
                action="deduped",
                old_value=old_spdx,
                new_value=new_spdx,
                notes="Removed duplicate Cargo package after exact identity normalization.",
            ))

    if spdx_rewrite:
        for rel in sbom.get("relationships", []) or []:
            if not isinstance(rel, dict):
                continue
            src = rel.get("spdxElementId")
            dst = rel.get("relatedSpdxElement")
            if isinstance(src, str) and src in spdx_rewrite:
                rel["spdxElementId"] = spdx_rewrite[src]
            if isinstance(dst, str) and dst in spdx_rewrite:
                rel["relatedSpdxElement"] = spdx_rewrite[dst]

    sbom["packages"] = kept

    seen_rels: set[tuple[str, str, str]] = set()
    deduped_rels: list[dict[str, Any]] = []
    for rel in sbom.get("relationships", []) or []:
        if not isinstance(rel, dict):
            deduped_rels.append(rel)
            continue
        key = (str(rel.get("spdxElementId")), str(rel.get("relatedSpdxElement")), str(rel.get("relationshipType")))
        if key in seen_rels:
            continue
        seen_rels.add(key)
        deduped_rels.append(rel)
    sbom["relationships"] = deduped_rels

    return findings

def build_rust_id_to_spdxid(sbom_data: dict[str, Any]) -> dict[str, str]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, str] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_rust_id(pkg)
        spdx_id = pkg.get("SPDXID")
        if identity and isinstance(spdx_id, str):
            out[identity] = spdx_id
    return out


def build_rust_id_to_pkg(sbom_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, dict[str, Any]] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_rust_id(pkg)
        if identity:
            out[identity] = pkg
    return out


def rust_pkg_to_spdx_pkg(a: RustArtifact, metadata: RustPackageMetadata | None = None) -> dict[str, Any]:
    package = {
        "name": a.name,
        "SPDXID": rust_pkg_spdxid(a),
        "versionInfo": a.version,
        "downloadLocation": metadata.download_url if metadata and metadata.download_url else "NOASSERTION",
        "filesAnalyzed": False,
        "checksums": ([{"algorithm": "SHA256", "checksumValue": metadata.checksum_sha256}] if metadata and metadata.checksum_sha256 else []),
        "licenseConcluded": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "licenseDeclared": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "copyrightText": "NOASSERTION",
        "externalRefs": [{"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": rust_pkg_purl(a)}],
    }
    if metadata:
        if metadata.package_file_name:
            package["packageFileName"] = metadata.package_file_name
        if metadata.homepage:
            package["homepage"] = metadata.homepage
        if metadata.repository:
            package.setdefault("externalRefs", []).append({"referenceCategory": "OTHER", "referenceType": "website", "referenceLocator": metadata.repository})
    return package


def enrich_pkg_with_rust_metadata(pkg: dict[str, Any], artifact: RustArtifact, metadata: RustPackageMetadata, findings: list[PackageValidationFinding]) -> None:
    spdx_id = pkg.get("SPDXID")
    if not isinstance(spdx_id, str):
        spdx_id = rust_pkg_spdxid(artifact)
        pkg["SPDXID"] = spdx_id

    artifact_id = rust_pkg_key(artifact)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "versionInfo", artifact.version, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "packageFileName", metadata.package_file_name, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "downloadLocation", metadata.download_url, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "homepage", metadata.homepage, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseDeclared", metadata.license_declared, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseConcluded", metadata.license_declared, findings)

    checksums = pkg.setdefault("checksums", [])
    if metadata.checksum_sha256 and not any(isinstance(c, dict) and c.get("algorithm") == "SHA256" and c.get("checksumValue") == metadata.checksum_sha256 for c in checksums):
        checksums.append({"algorithm": "SHA256", "checksumValue": metadata.checksum_sha256})
        findings.append(PackageValidationFinding(
            artifact=artifact_id,
            spdx_id=spdx_id,
            field="checksums.SHA256",
            action="filled",
            old_value=None,
            new_value=metadata.checksum_sha256,
            notes="Fetched from crates.io version metadata.",
        ))

    refs = pkg.setdefault("externalRefs", [])
    wanted_purl = rust_pkg_purl(artifact)
    has_purl = any(isinstance(ref, dict) and ref.get("referenceType") == "purl" and ref.get("referenceLocator") == wanted_purl for ref in refs)
    if not has_purl:
        refs.append({"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": wanted_purl})
        findings.append(PackageValidationFinding(artifact=artifact_id, spdx_id=spdx_id, field="externalRefs.purl", action="filled", old_value=None, new_value=wanted_purl))

    if metadata.repository:
        has_repo = any(isinstance(ref, dict) and ref.get("referenceLocator") == metadata.repository for ref in refs)
        if not has_repo:
            refs.append({"referenceCategory": "OTHER", "referenceType": "website", "referenceLocator": metadata.repository})
            findings.append(PackageValidationFinding(artifact=artifact_id, spdx_id=spdx_id, field="externalRefs.repository", action="filled", old_value=None, new_value=metadata.repository))


def resolve_rust_transitives(
    roots: list[RustArtifact],
    max_depth: int,
    max_artifacts: int | None = 3000,
) -> tuple[dict[str, RustArtifact], list[DependencyEdge], list[ResolutionIssue], list[SkippedArtifact]]:
    discovered: dict[str, RustArtifact] = {}
    edges: list[DependencyEdge] = []
    issues: list[ResolutionIssue] = []
    skipped: list[SkippedArtifact] = []
    queue: list[tuple[RustArtifact, int]] = [(a, 0) for a in roots]
    processed: set[str] = set()

    while queue:
        if max_artifacts is not None and len(processed) >= max_artifacts:
            issues.append(ResolutionIssue("cargo", f"Stopped Rust traversal after reaching --rust-max-artifacts={max_artifacts}; remaining queue={len(queue)}"))
            break

        current, depth = queue.pop(0)
        key = rust_pkg_key(current)
        discovered.setdefault(key, current)

        if key in processed:
            continue
        processed.add(key)

        if max_depth > 0 and depth >= max_depth:
            continue

        children, child_issues, child_skipped = resolve_rust_pkg(current)
        issues.extend(child_issues)
        skipped.extend(child_skipped)

        for child in children:
            child_key = rust_pkg_key(child)
            edges.append(DependencyEdge(parent=key, child=child_key))
            if child_key not in discovered:
                discovered[child_key] = child
                queue.append((child, depth + 1))

        if len(processed) % 100 == 0:
            print(f"[RUST] processed={len(processed)} discovered={len(discovered)} queued={len(queue)} issues={len(issues)} skipped={len(skipped)}")

    return discovered, edges, issues, skipped


def enrich_exact_rust_pkgs(sbom_data: dict[str, Any], findings: list[PackageValidationFinding]) -> list[ResolutionIssue]:
    sbom = sbom_data.get("sbom", sbom_data)
    issues: list[ResolutionIssue] = []
    seen: set[str] = set()

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue

        identity = get_rust_id(pkg)
        if not identity or identity in seen:
            continue
        seen.add(identity)

        parsed: tuple[str, str] | None = None
        for ref in pkg.get("externalRefs", []) or []:
            if not isinstance(ref, dict):
                continue
            loc = ref.get("referenceLocator")
            parsed_loc = parse_rust_purl(loc) if isinstance(loc, str) else None
            if parsed_loc and parsed_loc[1] and is_exact_rust_req(parsed_loc[1]):
                parsed = (parsed_loc[0], parsed_loc[1])
                break

        if not parsed:
            continue

        artifact = RustArtifact(parsed[0], parsed[1], source="existing_sbom")
        metadata, metadata_issues = get_rust_metadata_from_crates_io(artifact)
        issues.extend(metadata_issues)
        enrich_pkg_with_rust_metadata(pkg, artifact, metadata, findings)
        dedupe_pkg_external_refs(pkg)

    return dedupe_issues(issues)


def add_rust_transitives(
    sbom_data: dict[str, Any],
    discovered: dict[str, RustArtifact],
    edges: list[DependencyEdge],
) -> tuple[dict[str, Any], list[PackageValidationFinding], list[ResolutionIssue]]:
    sbom = sbom_data.get("sbom", sbom_data)
    sbom.setdefault("packages", [])
    sbom.setdefault("relationships", [])

    findings: list[PackageValidationFinding] = []
    metadata_issues: list[ResolutionIssue] = []

    surface_findings, surface_issues = normalize_rust_pkgs(sbom_data, discovered)
    findings.extend(surface_findings)
    metadata_issues.extend(surface_issues)

    identity_to_spdxid = build_rust_id_to_spdxid(sbom_data)
    identity_to_package = build_rust_id_to_pkg(sbom_data)

    for key, artifact in discovered.items():
        metadata, issues = get_rust_metadata_from_crates_io(artifact)
        metadata_issues.extend(issues)

        if key in identity_to_spdxid:
            existing_spdx = identity_to_spdxid[key]
            existing_pkg = identity_to_package.get(key)
            findings.append(PackageValidationFinding(
                artifact=key,
                spdx_id=existing_spdx,
                field="package",
                action="existed",
                old_value=rust_pkg_purl(artifact),
                new_value=rust_pkg_purl(artifact),
                notes="Cargo package was already present in the input SBOM; enrichment/validation was attempted.",
            ))
            if existing_pkg is not None:
                enrich_pkg_with_rust_metadata(existing_pkg, artifact, metadata, findings)
                dedupe_pkg_external_refs(existing_pkg)
            continue

        package = rust_pkg_to_spdx_pkg(artifact, metadata)
        dedupe_pkg_external_refs(package)
        sbom["packages"].append(package)
        identity_to_spdxid[key] = package["SPDXID"]
        identity_to_package[key] = package
        findings.append(PackageValidationFinding(
            artifact=key,
            spdx_id=package["SPDXID"],
            field="package",
            action="added",
            old_value=None,
            new_value=rust_pkg_purl(artifact),
            notes="Package added from crates.io transitive resolution.",
        ))

    for edge in edges:
        parent_spdxid = identity_to_spdxid.get(edge.parent)
        child_spdxid = identity_to_spdxid.get(edge.child)
        if not parent_spdxid or not child_spdxid:
            continue
        if has_relationship(sbom_data, parent_spdxid, child_spdxid, "DEPENDS_ON"):
            continue
        sbom["relationships"].append({"spdxElementId": parent_spdxid, "relatedSpdxElement": child_spdxid, "relationshipType": "DEPENDS_ON"})

    findings.extend(dedupe_rust_pkgs_by_id(sbom_data))

    metadata_issues.extend(enrich_exact_rust_pkgs(sbom_data, findings))

    for pkg in sbom.get("packages", []) or []:
        if isinstance(pkg, dict):
            dedupe_pkg_external_refs(pkg)

    return sbom_data, findings, dedupe_issues(metadata_issues)

# -------------------------
# Graph resolution
# -------------------------

def resolve_transitives(roots: list[Artifact], max_depth: int) -> tuple[dict[str, Artifact], list[DependencyEdge], list[ResolutionIssue], list[SkippedArtifact], dict[str, list[str]]]:
    discovered: dict[str, Artifact] = {}
    edges: list[DependencyEdge] = []
    issues: list[ResolutionIssue] = []
    skipped: list[SkippedArtifact] = []
    repositories_by_artifact: dict[str, list[str]] = {}
    queue: list[tuple[Artifact, int, list[str]]] = [(a, 0, DEFAULT_MAVEN_REPOSITORIES) for a in roots]
    processed: set[str] = set()

    while queue:
        current, depth, repositories = queue.pop(0)
        key = coord_key(current)

        if key not in discovered:
            discovered[key] = current

        if key in processed:
            continue

        processed.add(key)

        if depth >= max_depth:
            continue

        children, child_issues, resolved_repositories = resolve_maven_coord(current, repositories)
        issues.extend(child_issues)
        repositories_by_artifact[key] = resolved_repositories

        for child in children:
            child_key = coord_key(child)

            if exclusion_matches(child, current.exclusions):
                skipped.append(SkippedArtifact(artifact=child_key, source=key, scope=child.scope, reason="Excluded by Maven <exclusions> inherited from parent dependency path."))
                continue

            include, reason = maven_recurse(child)
            if not include:
                skipped.append(SkippedArtifact(artifact=child_key, source=key, scope=child.scope, reason=reason or "Excluded Maven transitive dependency"))
                continue

            combined_exclusions = frozenset(set(current.exclusions) | set(child.exclusions))
            child_for_queue = Artifact(group=child.group, artifact=child.artifact, version=child.version, scope=child.scope, source=key, exclusions=combined_exclusions)

            edges.append(DependencyEdge(parent=key, child=child_key))

            if child_key not in discovered:
                discovered[child_key] = child_for_queue
                queue.append((child_for_queue, depth + 1, resolved_repositories))

    for root in roots:
        repositories_by_artifact.setdefault(coord_key(root), DEFAULT_MAVEN_REPOSITORIES)

    return discovered, edges, issues, skipped, repositories_by_artifact

def dedupe_issues(issues: list[ResolutionIssue]) -> list[ResolutionIssue]:
    seen: set[tuple[str, str]] = set()
    out: list[ResolutionIssue] = []
    for issue in issues:
        key = (issue.artifact, issue.reason)
        if key in seen:
            continue
        seen.add(key)
        out.append(issue)
    return out


def suppress_expected_rust_issues(issues: list[ResolutionIssue]) -> list[ResolutionIssue]:
    out: list[ResolutionIssue] = []
    for issue in issues:
        if issue.artifact.startswith("pkg:cargo/") and rust_issue_is_crates_io_404(issue):
            continue
        if issue.artifact.startswith("pkg:cargo/") and issue.reason == "Exact crate version was not confirmed by crates.io; metadata fields were left unchanged/NOASSERTION.":
            continue
        out.append(issue)
    return out


def make_json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): make_json_safe(v) for k, v in value.items()}

    if isinstance(value, (list, tuple)):
        return [make_json_safe(v) for v in value]

    if isinstance(value, (set, frozenset)):
        return [make_json_safe(v) for v in sorted(value, key=str)]

    if isinstance(value, Path):
        return str(value)

    return value


# -------------------------
# PHP / Composer helpers
# -------------------------

PACKAGIST_P2 = "https://repo.packagist.org/p2"
PACKAGIST_CACHE: dict[str, dict[str, Any]] = {}


@dataclass(frozen=True)
class ComposerArtifact:
    name: str
    version: str
    scope: str = "runtime"
    source: str | None = None
    requested: str | None = None


@dataclass(frozen=True)
class ComposerPackageMetadata:
    artifact: str
    registry_url: str | None = None
    download_url: str | None = None
    package_file_name: str | None = None
    homepage: str | None = None
    repository: str | None = None
    supplier: str | None = None
    license_declared: str | None = None
    checksum_sha1: str | None = None
    description: str | None = None


COMPOSER_NON_REGISTRY_PREFIXES = ("path:", "vcs:", "git:", "git+", "git://", "github:", "http://", "https://")


COMPOSER_PLATFORM_NAMES = {
    "php",
    "hhvm",
    "composer",
    "composer-plugin-api",
    "composer-runtime-api",
}


def canonical_composer_name(name: str) -> str:
    value = urllib.parse.unquote((name or "").strip())
    if value.startswith("pkg:composer/"):
        body = value[len("pkg:composer/"):].split("?", 1)[0]
        if "@" in body:
            body = body.rsplit("@", 1)[0]
        value = body
    return value.lower().strip()


def composer_ver_text(version: str | None) -> str:
    value = urllib.parse.unquote((version or "").strip())
    if value.startswith("v") and len(value) > 1 and value[1].isdigit():
        return value[1:]
    return value


def composer_purl(name: str, version: str) -> str:
    return ("pkg:composer/" + urllib.parse.quote(canonical_composer_name(name), safe="/") + "@" + urllib.parse.quote(composer_ver_text(version), safe=""))


def composer_pkg_key(a: ComposerArtifact) -> str:
    return composer_purl(a.name, a.version)


def composer_pkg_purl(a: ComposerArtifact) -> str:
    return composer_purl(a.name, a.version)


def composer_pkg_spdxid(a: ComposerArtifact) -> str:
    safe = re.sub(r"[^A-Za-z0-9.-]+", "-", f"composer-{canonical_composer_name(a.name)}-{composer_ver_text(a.version)}").strip("-")
    return f"SPDXRef-transitive-{safe}"


def is_composer_platform_pkg(name: str) -> bool:
    n = canonical_composer_name(name)
    return n in COMPOSER_PLATFORM_NAMES or n.startswith(("ext-", "lib-"))


def is_non_registry_composer_constraint(constraint: str | None) -> bool:
    if not constraint:
        return False
    c = constraint.strip().lower()
    return c.startswith(COMPOSER_NON_REGISTRY_PREFIXES) or c in {"self.version", "@self.version"}


def is_composer_branch_or_dev(constraint: str | None) -> bool:
    if not constraint:
        return False
    c = constraint.strip().lower()
    if " as " in c:
        return True
    c_no_hash = c.split("#", 1)[0].strip()
    return bool(re.fullmatch(r"dev-[a-z0-9_.\/-]+", c_no_hash) or re.fullmatch(r"[0-9]+(?:\.[0-9x*]+)*-dev", c_no_hash) or c_no_hash in {"@dev", "dev"})


def is_non_reproducible_composer_dev(version: str | None) -> bool:
    v = composer_ver_text(version).strip().lower()
    if not v:
        return False
    return bool(
        v.startswith("dev-")
        or v.endswith("-dev")
        or re.fullmatch(r"\d+(?:\.\d+)*-dev(?:\.\d+)?", v)
        or re.fullmatch(r"\d+(?:\.x)+-dev(?:\.\d+)?", v)
        or v in {"9999999-dev", "9999999-dev.0"}
    )


COMPOSER_KNOWN_TEST_NON_PACKAGIST = {
    "guzzle/client-integration-tests",
    "guzzlehttp/test-server",
    "yaml/yaml-test-suite",
}


def is_expected_non_packagist(name: str) -> bool:
    canonical = canonical_composer_name(name)
    if canonical in COMPOSER_KNOWN_TEST_NON_PACKAGIST:
        return True
    tail = canonical.rsplit("/", 1)[-1]
    return bool(tail in {"test-server", "test-suite", "client-integration-tests", "integration-tests"} or tail.endswith("-test-suite") or tail.endswith("-integration-tests"))

def composer_min_stability(constraint: str | None) -> int:
    c = (constraint or "").lower()
    if "@dev" in c or re.search(r"(^|[.-])dev($|[.-])", c):
        return 0
    if "@alpha" in c or "-alpha" in c or re.search(r"(^|[.-])a\d+", c):
        return 1
    if "@beta" in c or "-beta" in c or re.search(r"(^|[.-])b\d+", c):
        return 2
    if "@rc" in c or "-rc" in c:
        return 3
    return 4


def composer_has_explicit_unstable(constraint: str | None) -> bool:
    c = (constraint or "").lower()
    return bool(re.search(r"(?i)(@dev|@alpha|@beta|@rc|alpha|beta|rc)", c))


def strip_composer_stability(constraint: str) -> str:
    value = (constraint or "").split("#", 1)[0]
    return re.sub(r"@[A-Za-z-]+", "", value).strip()


def packagist_p2_url(package_name: str) -> str:
    return f"{PACKAGIST_P2}/{urllib.parse.quote(canonical_composer_name(package_name), safe='/')}.json"


def get_packagist_package(package_name: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    name = canonical_composer_name(package_name)
    if name in PACKAGIST_CACHE:
        return PACKAGIST_CACHE[name], []

    url = packagist_p2_url(name)
    request = urllib.request.Request(url, headers={"User-Agent": "RestoreSBOM research prototype (Composer transitive dependency validation)", "Accept": "application/json"})
    try:
        with urllib.request.urlopen(request, timeout=20) as response:
            data = json.loads(response.read().decode("utf-8", errors="replace"))
        PACKAGIST_CACHE[name] = data
        return data, []
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None, [ResolutionIssue(f"pkg:composer/{name}", f"Composer package not found on Packagist: HTTP 404 at {url}")]
        return None, [ResolutionIssue(f"pkg:composer/{name}", f"Packagist fetch failed: HTTP {e.code} at {url}")]
    except Exception as e:
        return None, [ResolutionIssue(f"pkg:composer/{name}", f"Packagist fetch failed: {type(e).__name__}: {e}")]


def get_composer_pkg_versions(package_name: str) -> tuple[list[dict[str, Any]], list[ResolutionIssue]]:
    data, issues = get_packagist_package(package_name)
    if not data:
        return [], issues

    packages = data.get("packages")
    if not isinstance(packages, dict):
        return [], [*issues, ResolutionIssue(f"pkg:composer/{canonical_composer_name(package_name)}", "Packagist p2 response had no packages map")]

    canonical = canonical_composer_name(package_name)
    versions = packages.get(canonical)
    if not isinstance(versions, list):
        versions = next((v for k, v in packages.items() if str(k).lower() == canonical and isinstance(v, list)), [])

    return [v for v in versions if isinstance(v, dict)], issues


def composer_ver_label(version_metadata: dict[str, Any]) -> str | None:
    version = version_metadata.get("version")
    if isinstance(version, str) and version:
        return composer_ver_text(version)
    normalized = version_metadata.get("version_normalized")
    if isinstance(normalized, str) and normalized:
        nums = normalized.split("-")[0].split(".")
        if len(nums) >= 4 and nums[3] == "0":
            normalized = ".".join(nums[:3])
        return composer_ver_text(normalized)
    return None


def composer_ver_stability(version: str | None) -> int:
    value = (version or "").lower()
    if value.startswith("dev-") or value.endswith("-dev"):
        return 0
    if "alpha" in value or re.search(r"(^|[.-])a\d*", value):
        return 1
    if "beta" in value or re.search(r"(^|[.-])b\d*", value):
        return 2
    if "rc" in value:
        return 3
    return 4


def composer_ver_key(version: str | None) -> tuple[int, int, int, int, int, str]:
    if not version:
        return (-1, -1, -1, -1, -1, "")
    raw = composer_ver_text(version)
    lower = raw.lower()
    if lower.startswith("dev-"):
        return (-1, -1, -1, -1, composer_ver_stability(raw), raw)

    core = raw.split("+", 1)[0]
    nums = re.findall(r"\d+", core.split("-", 1)[0])[:4]
    while len(nums) < 4:
        nums.append("0")
    major, minor, patch, extra = [int(n) for n in nums]
    return (major, minor, patch, extra, composer_ver_stability(raw), raw)


def compare_composer_vers(a: str, b: str) -> int:
    ka = composer_ver_key(a)[:5]
    kb = composer_ver_key(b)[:5]
    return (ka > kb) - (ka < kb)


def composer_partial_bounds(token: str) -> list[str]:
    raw = strip_composer_stability(token).strip().lstrip("v")
    wildcard = bool(re.search(r"(?i)(^|[.])(x|\*)($|[.])", raw))
    nums = [int(x) for x in re.findall(r"\d+", raw)]

    if not nums:
        return ["*"]

    if wildcard:
        if len(nums) == 1:
            major = nums[0]
            return [f">={major}.0.0", f"<{major + 1}.0.0"]
        major, minor = nums[:2]
        return [f">={major}.{minor}.0", f"<{major}.{minor + 1}.0"]

    if len(nums) == 1:
        major = nums[0]
        return [f">={major}.0.0", f"<{major + 1}.0.0"]
    if len(nums) == 2:
        major, minor = nums[:2]
        return [f">={major}.{minor}.0", f"<{major + 1}.0.0"]

    return ["=" + ".".join(str(n) for n in nums[:3])]


def composer_expand_caret(version: str, minimum_stability: int = 4) -> list[str]:
    cleaned = strip_composer_stability(version).strip().lstrip("v")
    parts = [int(p) for p in re.findall(r"\d+", cleaned)[:3]]
    original_len = len(parts)
    while len(parts) < 3:
        parts.append(0)
    major, minor, patch = parts[:3]

    suffix = ""
    if minimum_stability == 1:
        suffix = "-alpha0"
    elif minimum_stability == 2:
        suffix = "-beta0"
    elif minimum_stability == 3:
        suffix = "-RC0"
    lower = f">={major}.{minor}.{patch}{suffix}"

    if major > 0:
        upper = f"<{major + 1}.0.0"
    elif original_len <= 1:
        upper = "<1.0.0"
    elif minor > 0:
        upper = f"<0.{minor + 1}.0"
    else:
        upper = f"<0.0.{patch + 1}"
    return [lower, upper]


def composer_expand_tilde(version: str, minimum_stability: int = 4) -> list[str]:
    cleaned = strip_composer_stability(version).strip().lstrip("v")
    parts = [int(p) for p in re.findall(r"\d+", cleaned)[:3]]
    original_len = len(parts)
    while len(parts) < 3:
        parts.append(0)
    major, minor, patch = parts[:3]

    suffix = ""
    if minimum_stability == 1:
        suffix = "-alpha0"
    elif minimum_stability == 2:
        suffix = "-beta0"
    elif minimum_stability == 3:
        suffix = "-RC0"
    lower = f">={major}.{minor}.{patch}{suffix}"

    if original_len <= 1:
        upper = f"<{major + 1}.0.0"
    elif original_len == 2:
        upper = f"<{major + 1}.0.0"
    else:
        upper = f"<{major}.{minor + 1}.0"
    return [lower, upper]


def composer_token_comparators(token: str, minimum_stability: int = 4) -> list[str]:
    token = strip_composer_stability(token).strip()
    if not token:
        return []
    token = re.sub(r"~>\s*", "~", token)
    token = re.sub(r"^(>=|<=|>|<|=|==|!=)\s+(?=v?\d)", r"\1", token)

    if token in {"*", "x", "X"}:
        return ["*"]
    if re.match(r"^v?\d+(?:\.\d+){0,3}-(?:alpha|beta|RC|rc|a|b)\d*$", token):
        return ["=" + token.lstrip("v")]
    if token.startswith("^"):
        return composer_expand_caret(token[1:], minimum_stability)
    if token.startswith("~"):
        return composer_expand_tilde(token[1:], minimum_stability)

    comp_match = re.match(r"^(>=|<=|>|<|=|==|!=)(.+)$", token)
    if comp_match:
        op = comp_match.group(1)
        value = strip_composer_stability(comp_match.group(2).strip())
        if re.search(r"(?i)(^|[.])(x|\*)($|[.])", value):
            bounds = composer_partial_bounds(value)
            if op in {">", ">="}:
                return [bounds[0]]
            if op in {"<", "<="} and len(bounds) > 1:
                return [bounds[1]]
        return [op + value.lstrip("v")]

    if re.match(r"^v?\d+(?:\.\d+){0,2}(?:\.(?:x|X|\*))?$", token) or re.match(r"^v?\d+(?:\.(?:x|X|\*))$", token):
        return composer_partial_bounds(token)
    if re.match(r"^v?\d+\.\d+\.\d+(?:[-+][A-Za-z0-9_.-]+)?$", token):
        return ["=" + token.lstrip("v")]
    return [token]


def combine_composer_constraint_groups(left: list[list[str]], right: list[list[str]]) -> list[list[str]]:
    return [a + b for a in left for b in right]


def normalize_composer_constraints(constraint: str) -> list[list[str]]:
    c = (constraint or "").strip()
    if not c or c in {"*", "x", "X"}:
        return [["*"]]

    c = re.sub(r"~>\s*", "~", c)
    c = re.sub(r"(>=|<=|>|<|=|==|!=)\s+(?=v?\d)", r"\1", c)
    minimum_stability = composer_min_stability(c)
    c = strip_composer_stability(c)

    comma_segments = [seg.strip() for seg in c.split(",") if seg.strip()]
    if len(comma_segments) > 1:
        combined: list[list[str]] = [["*"]]
        for seg in comma_segments:
            seg_groups = normalize_composer_constraints(seg)
            if combined == [["*"]]:
                combined = seg_groups
            else:
                combined = combine_composer_constraint_groups(combined, seg_groups)
        return combined or [["*"]]

    groups: list[list[str]] = []
    for raw_group in re.split(r"\s*\|\|?\s*", c):
        raw_group = raw_group.strip()
        if not raw_group:
            continue

        hyphen = re.match(r"^v?([0-9][^\s]*)\s+-\s+v?([0-9][^\s]*)$", raw_group)
        if hyphen:
            groups.append([f">={hyphen.group(1)}", f"<={hyphen.group(2)}"])
            continue

        comparators: list[str] = []
        for token in re.split(r"\s+", raw_group):
            comparators.extend(composer_token_comparators(token, minimum_stability))
        groups.append(comparators or ["*"])

    return groups or [["*"]]

def composer_ver_matches_comparator(version: str, comparator: str) -> bool:
    comp = comparator.strip()
    if not comp or comp == "*":
        return True
    if comp.startswith("!="):
        return True

    m = re.match(r"^(>=|<=|>|<|=|==)?\s*v?([^\s]+)$", comp)
    if not m:
        return False
    op = m.group(1) or "="
    if op == "==":
        op = "="
    target = composer_ver_text(m.group(2))

    cmp = compare_composer_vers(composer_ver_text(version), target)
    if op == "=":
        return cmp == 0
    if op == ">=":
        return cmp >= 0
    if op == "<=":
        return cmp <= 0
    if op == ">":
        return cmp > 0
    if op == "<":
        return cmp < 0
    return False


def composer_ver_matches_constraint(version: str, constraint: str | None) -> bool:
    if is_non_registry_composer_constraint(constraint):
        return False
    c = (constraint or "*").strip()
    for group in normalize_composer_constraints(c):
        if all(composer_ver_matches_comparator(version, token) for token in group):
            return True
    return False


def resolve_composer_ver(package_name: str, constraint: str | None) -> tuple[str | None, list[ResolutionIssue]]:
    requested = (constraint or "*").strip()
    canonical = canonical_composer_name(package_name)

    if is_composer_platform_pkg(canonical):
        return None, []
    if is_non_registry_composer_constraint(requested):
        return None, [ResolutionIssue(f"pkg:composer/{canonical}", f"Skipped non-registry Composer dependency constraint: {requested}")]
    if is_composer_branch_or_dev(requested):
        return None, [ResolutionIssue(f"pkg:composer/{canonical}", f"Skipped Composer branch/alias dev constraint that cannot be resolved without Composer: {requested}")]

    versions, issues = get_composer_pkg_versions(canonical)
    if not versions:
        return None, issues

    labels: list[tuple[str, dict[str, Any]]] = []
    for metadata in versions:
        label = composer_ver_label(metadata)
        if label:
            labels.append((label, metadata))

    if not labels:
        return None, [*issues, ResolutionIssue(f"pkg:composer/{canonical}", "Packagist returned no usable versions")]

    for label, _metadata in labels:
        if label == composer_ver_text(requested) or label.lower() == requested.lower():
            if is_non_reproducible_composer_dev(label):
                return None, [*issues, ResolutionIssue(f"pkg:composer/{canonical}", f"Skipped Composer dev pseudo-version without a reproducible release artifact: {requested}")]
            return label, issues

    satisfying = [(label, metadata) for label, metadata in labels if composer_ver_matches_constraint(label, requested) and composer_ver_stability(label) == 4]
    if not satisfying and composer_has_explicit_unstable(requested):
        min_stability = composer_min_stability(requested)
        satisfying = [(label, metadata) for label, metadata in labels if composer_ver_matches_constraint(label, requested) and min_stability <= composer_ver_stability(label) < 4]

    if satisfying:
        return sorted(satisfying, key=lambda item: composer_ver_key(item[0]))[-1][0], issues

    if composer_has_explicit_unstable(requested):
        return None, [*issues, ResolutionIssue(f"pkg:composer/{canonical}", f"Skipped Composer unstable/stability constraint without a reproducible release artifact: {requested}")]

    return None, [*issues, ResolutionIssue(f"pkg:composer/{canonical}", f"No Packagist release satisfies Composer constraint: {requested}")]


def get_composer_metadata_for_version(package_name: str, version: str) -> tuple[dict[str, Any] | None, list[ResolutionIssue]]:
    versions, issues = get_composer_pkg_versions(package_name)
    wanted = composer_ver_text(version)
    for metadata in versions:
        label = composer_ver_label(metadata)
        normalized = metadata.get("version_normalized")
        raw_version = metadata.get("version")
        if (label == wanted or composer_ver_text(str(raw_version or "")) == wanted or composer_ver_text(str(normalized or "")) == wanted):
            return metadata, issues
    return None, [*issues, ResolutionIssue(composer_purl(package_name, version), "Packagist did not confirm exact package version")]


def get_composer_metadata_from_packagist(artifact: ComposerArtifact) -> tuple[ComposerPackageMetadata, list[ResolutionIssue]]:
    key = composer_pkg_key(artifact)
    metadata, issues = get_composer_metadata_for_version(artifact.name, artifact.version)
    if metadata is None:
        return ComposerPackageMetadata(artifact=key, registry_url=packagist_p2_url(artifact.name)), issues

    dist = metadata.get("dist") if isinstance(metadata.get("dist"), dict) else {}
    source = metadata.get("source") if isinstance(metadata.get("source"), dict) else {}
    authors = metadata.get("authors") if isinstance(metadata.get("authors"), list) else []
    supplier = None
    if authors and isinstance(authors[0], dict):
        name = authors[0].get("name")
        email = authors[0].get("email")
        if isinstance(name, str) and isinstance(email, str):
            supplier = f"Person: {name} ({email})"
        elif isinstance(name, str):
            supplier = f"Person: {name}"

    licenses = metadata.get("license") if isinstance(metadata.get("license"), list) else []
    license_declared = " OR ".join(str(x) for x in licenses if isinstance(x, str)) or None
    download_url = dist.get("url") if isinstance(dist.get("url"), str) else None
    shasum = dist.get("shasum") if isinstance(dist.get("shasum"), str) and re.fullmatch(r"[0-9a-fA-F]{40}", dist.get("shasum")) else None
    repo = source.get("url") if isinstance(source.get("url"), str) else None
    homepage = metadata.get("homepage") if isinstance(metadata.get("homepage"), str) else None
    if not homepage:
        homepage = repo

    file_name = None
    if download_url:
        parsed_path = urllib.parse.urlparse(download_url).path
        candidate = Path(parsed_path).name
        if candidate:
            file_name = candidate
    if not file_name:
        safe_name = canonical_composer_name(artifact.name).replace("/", "-")
        file_name = f"{safe_name}-{composer_ver_text(artifact.version)}.zip"

    return ComposerPackageMetadata(
        artifact=key,
        registry_url=packagist_p2_url(artifact.name),
        download_url=download_url,
        package_file_name=file_name,
        homepage=homepage,
        repository=repo,
        supplier=supplier,
        license_declared=license_name_to_spdx(license_declared),
        checksum_sha1=shasum.lower() if isinstance(shasum, str) else None,
        description=metadata.get("description") if isinstance(metadata.get("description"), str) else None,
    ), issues


def get_composer_pkgs(sbom_data: dict[str, Any]) -> list[ComposerArtifact]:
    sbom = sbom_data.get("sbom", sbom_data)
    artifacts: list[ComposerArtifact] = []
    seen: set[str] = set()

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        purl_name = None
        purl_version = None
        for ref in pkg.get("externalRefs", []) or []:
            if not isinstance(ref, dict):
                continue
            loc = ref.get("referenceLocator")
            if not isinstance(loc, str) or not loc.startswith("pkg:composer/"):
                continue
            body = loc[len("pkg:composer/"):].split("?", 1)[0]
            if "@" in body:
                purl_name, purl_version = body.rsplit("@", 1)
            else:
                purl_name = body
            break
        if not purl_name:
            continue

        name = canonical_composer_name(purl_name)
        if is_composer_platform_pkg(name):
            continue

        version = composer_ver_text(purl_version) if purl_version else None
        version_info = pkg.get("versionInfo")
        requested = str(version_info).strip() if isinstance(version_info, str) and version_info.strip() else None

        if version and not re.search(r"[<>=~^*|]", version):
            artifact = ComposerArtifact(name, version, source="surface_sbom", requested=requested if requested != version else None)
        else:
            resolved, _issues = resolve_composer_ver(name, requested or version or "*")
            if not resolved:
                continue
            artifact = ComposerArtifact(name, resolved, source="surface_sbom", requested=requested or version)

        key = composer_pkg_key(artifact)
        if key not in seen:
            seen.add(key)
            artifacts.append(artifact)

    return artifacts


def get_composer_id(pkg: dict[str, Any]) -> str | None:
    for ref in pkg.get("externalRefs", []) or []:
        if not isinstance(ref, dict):
            continue
        loc = ref.get("referenceLocator")
        if isinstance(loc, str) and loc.startswith("pkg:composer/") and "@" in loc:
            body = loc[len("pkg:composer/"):].split("?", 1)[0]
            name, version = body.rsplit("@", 1)
            if is_composer_platform_pkg(name):
                return None
            return composer_purl(name, urllib.parse.unquote(version))
    return None


def build_composer_id_to_spdxid(sbom_data: dict[str, Any]) -> dict[str, str]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, str] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_composer_id(pkg)
        spdx_id = pkg.get("SPDXID")
        if identity and isinstance(spdx_id, str):
            out[identity] = spdx_id
    return out


def build_composer_id_to_pkg(sbom_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    sbom = sbom_data.get("sbom", sbom_data)
    out: dict[str, dict[str, Any]] = {}
    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        identity = get_composer_id(pkg)
        if identity:
            out[identity] = pkg
    return out


def composer_pkg_to_spdx_pkg(a: ComposerArtifact, metadata: ComposerPackageMetadata | None = None) -> dict[str, Any]:
    package = {
        "name": canonical_composer_name(a.name),
        "SPDXID": composer_pkg_spdxid(a),
        "versionInfo": composer_ver_text(a.version),
        "downloadLocation": metadata.download_url if metadata and metadata.download_url else "NOASSERTION",
        "filesAnalyzed": False,
        "checksums": ([{"algorithm": "SHA1", "checksumValue": metadata.checksum_sha1}] if metadata and metadata.checksum_sha1 else []),
        "licenseConcluded": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "licenseDeclared": metadata.license_declared if metadata and metadata.license_declared else "NOASSERTION",
        "copyrightText": "NOASSERTION",
        "externalRefs": [{"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": composer_pkg_purl(a)}],
    }
    if metadata:
        if metadata.package_file_name:
            package["packageFileName"] = metadata.package_file_name
        if metadata.homepage:
            package["homepage"] = metadata.homepage
        if metadata.supplier:
            package["supplier"] = metadata.supplier
        if metadata.repository:
            refs = package.setdefault("externalRefs", [])
            if not any(isinstance(ref, dict) and ref.get("referenceLocator") == metadata.repository for ref in refs):
                refs.append({"referenceCategory": "OTHER", "referenceType": "website", "referenceLocator": metadata.repository})
    return package


def enrich_pkg_with_composer_metadata(pkg: dict[str, Any], artifact: ComposerArtifact, metadata: ComposerPackageMetadata, findings: list[PackageValidationFinding]) -> None:
    spdx_id = pkg.get("SPDXID")
    if not isinstance(spdx_id, str):
        spdx_id = composer_pkg_spdxid(artifact)
        pkg["SPDXID"] = spdx_id

    artifact_id = composer_pkg_key(artifact)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "versionInfo", composer_ver_text(artifact.version), findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "packageFileName", metadata.package_file_name, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "downloadLocation", metadata.download_url, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "homepage", metadata.homepage, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "supplier", metadata.supplier, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseDeclared", metadata.license_declared, findings)
    set_pkg_field_from_registry(pkg, spdx_id, artifact_id, "licenseConcluded", metadata.license_declared, findings)

    checksums = pkg.setdefault("checksums", [])
    if metadata.checksum_sha1 and not any(isinstance(c, dict) and c.get("algorithm") == "SHA1" and c.get("checksumValue") == metadata.checksum_sha1 for c in checksums):
        checksums.append({"algorithm": "SHA1", "checksumValue": metadata.checksum_sha1})
        findings.append(PackageValidationFinding(
            artifact=artifact_id,
            spdx_id=spdx_id,
            field="checksums.SHA1",
            action="filled",
            old_value=None,
            new_value=metadata.checksum_sha1,
            notes="Fetched from Packagist dist.shasum.",
        ))

    refs = pkg.setdefault("externalRefs", [])
    wanted_purl = composer_pkg_purl(artifact)
    replaced = False
    for ref in refs:
        if isinstance(ref, dict) and ref.get("referenceType") == "purl":
            loc = ref.get("referenceLocator")
            if isinstance(loc, str) and loc.startswith("pkg:composer/"):
                if loc != wanted_purl:
                    old = loc
                    ref["referenceLocator"] = wanted_purl
                    findings.append(PackageValidationFinding(artifact=artifact_id, spdx_id=spdx_id, field="externalRefs.purl", action="filled", old_value=old, new_value=wanted_purl))
                replaced = True
                break
    if not replaced:
        refs.append({"referenceCategory": "PACKAGE-MANAGER", "referenceType": "purl", "referenceLocator": wanted_purl})
    if metadata.repository and not any(isinstance(ref, dict) and ref.get("referenceLocator") == metadata.repository for ref in refs):
        refs.append({"referenceCategory": "OTHER", "referenceType": "website", "referenceLocator": metadata.repository})


def normalize_composer_pkgs(sbom_data: dict[str, Any], discovered: dict[str, ComposerArtifact]) -> tuple[list[PackageValidationFinding], list[ResolutionIssue]]:
    sbom = sbom_data.get("sbom", sbom_data)
    findings: list[PackageValidationFinding] = []
    issues: list[ResolutionIssue] = []
    exact_versions: dict[str, str] = {}
    for art in discovered.values():
        exact_versions.setdefault(canonical_composer_name(art.name), art.version)

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            continue
        for ref in pkg.get("externalRefs", []) or []:
            if not isinstance(ref, dict):
                continue
            loc = ref.get("referenceLocator")
            if not isinstance(loc, str) or not loc.startswith("pkg:composer/"):
                continue

            body = loc[len("pkg:composer/"):].split("?", 1)[0]
            if "@" in body:
                name, version = body.rsplit("@", 1)
                version = composer_ver_text(version)
            else:
                name, version = body, None
            canonical = canonical_composer_name(name)
            if is_composer_platform_pkg(canonical):
                continue

            version_info = pkg.get("versionInfo")
            requested = str(version_info).strip() if isinstance(version_info, str) and version_info.strip() else None
            resolved = version if version and not re.search(r"[<>=~^*|]", version) else exact_versions.get(canonical)
            if not resolved and requested:
                resolved, resolve_issues = resolve_composer_ver(canonical, requested)
                issues.extend(resolve_issues)
            if not resolved:
                continue

            old_loc = loc
            new_loc = composer_purl(canonical, resolved)
            ref["referenceLocator"] = new_loc
            old_version = pkg.get("versionInfo")
            pkg["versionInfo"] = composer_ver_text(resolved)
            findings.append(PackageValidationFinding(
                artifact=new_loc,
                spdx_id=pkg.get("SPDXID") if isinstance(pkg.get("SPDXID"), str) else "NOASSERTION",
                field="versionInfo/externalRefs.referenceLocator",
                action="filled" if old_loc != new_loc or old_version != resolved else "verified",
                old_value=f"versionInfo={old_version}; purl={old_loc}",
                new_value=f"versionInfo={composer_ver_text(resolved)}; purl={new_loc}",
                notes="Normalized Composer package identity using Packagist/discovered exact version.",
            ))
            break

    return findings, issues


def dedupe_composer_pkgs_and_rels(sbom_data: dict[str, Any]) -> list[PackageValidationFinding]:
    sbom = sbom_data.get("sbom", sbom_data)
    findings: list[PackageValidationFinding] = []
    identity_to_pkg: dict[str, dict[str, Any]] = {}
    spdx_rewrite: dict[str, str] = {}
    new_packages: list[dict[str, Any]] = []

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            new_packages.append(pkg)
            continue
        identity = get_composer_id(pkg)
        spdx_id = pkg.get("SPDXID")
        if identity and isinstance(spdx_id, str) and identity in identity_to_pkg:
            kept = identity_to_pkg[identity]
            kept_id = kept.get("SPDXID")
            if isinstance(kept_id, str):
                spdx_rewrite[spdx_id] = kept_id
                findings.append(PackageValidationFinding(
                    artifact=identity,
                    spdx_id=kept_id,
                    field="package",
                    action="deduplicated",
                    old_value=spdx_id,
                    new_value=kept_id,
                    notes="Removed duplicate Composer package with same purl identity.",
                ))
            continue
        if identity:
            identity_to_pkg[identity] = pkg
        new_packages.append(pkg)

    sbom["packages"] = new_packages
    if spdx_rewrite:
        for rel in sbom.get("relationships", []) or []:
            if rel.get("spdxElementId") in spdx_rewrite:
                rel["spdxElementId"] = spdx_rewrite[rel["spdxElementId"]]
            if rel.get("relatedSpdxElement") in spdx_rewrite:
                rel["relatedSpdxElement"] = spdx_rewrite[rel["relatedSpdxElement"]]

    seen_rels: set[tuple[str, str, str]] = set()
    deduped_rels: list[dict[str, Any]] = []
    for rel in sbom.get("relationships", []) or []:
        if not isinstance(rel, dict):
            deduped_rels.append(rel)
            continue
        key = (str(rel.get("spdxElementId")), str(rel.get("relatedSpdxElement")), str(rel.get("relationshipType")))
        if key in seen_rels:
            continue
        seen_rels.add(key)
        deduped_rels.append(rel)
    sbom["relationships"] = deduped_rels
    return findings


def resolve_composer_pkg(artifact: ComposerArtifact) -> tuple[list[ComposerArtifact], list[ResolutionIssue], list[SkippedArtifact]]:
    metadata, issues = get_composer_metadata_for_version(artifact.name, artifact.version)
    if metadata is None:
        return [], issues, []

    children: list[ComposerArtifact] = []
    skipped: list[SkippedArtifact] = []
    seen_children: set[str] = set()

    for field_name, scope in (("require", "runtime"),):
        deps = metadata.get(field_name)
        if not isinstance(deps, dict):
            continue
        for dep_name, dep_constraint in deps.items():
            if not isinstance(dep_name, str):
                continue
            canonical = canonical_composer_name(dep_name)
            requested = str(dep_constraint).strip() if dep_constraint is not None else "*"
            if is_composer_platform_pkg(canonical):
                skipped.append(SkippedArtifact(
                    artifact=f"pkg:composer/{canonical}@{requested}",
                    source=composer_pkg_key(artifact),
                    scope=scope,
                    reason="Skipped Composer platform requirement (php/ext/lib/hhvm/composer API).",
                ))
                continue
            if is_non_registry_composer_constraint(requested):
                skipped.append(SkippedArtifact(
                    artifact=f"pkg:composer/{canonical}@{requested}",
                    source=composer_pkg_key(artifact),
                    scope=scope,
                    reason="Skipped non-registry Composer dependency constraint.",
                ))
                continue
            if is_composer_branch_or_dev(requested):
                skipped.append(SkippedArtifact(
                    artifact=f"pkg:composer/{canonical}@{requested}",
                    source=composer_pkg_key(artifact),
                    scope=scope,
                    reason="Skipped Composer branch/alias dev constraint that cannot be resolved without running Composer.",
                ))
                continue

            dep_version, dep_issues = resolve_composer_ver(canonical, requested)
            no_satisfying_release = any(isinstance(issue.reason, str) and "no packagist release satisfies composer constraint" in issue.reason.lower() for issue in dep_issues)
            issues.extend(dep_issues)
            if not dep_version and no_satisfying_release:
                skipped.append(SkippedArtifact(
                    artifact=f"pkg:composer/{canonical}@{requested}",
                    source=composer_pkg_key(artifact),
                    scope=scope,
                    reason="Skipped Composer dependency because Packagist did not expose a stable release satisfying the declared constraint; no metadata was guessed.",
                ))
            if dep_version and is_non_reproducible_composer_dev(dep_version):
                skipped.append(SkippedArtifact(
                    artifact=f"pkg:composer/{canonical}@{dep_version}",
                    source=composer_pkg_key(artifact),
                    scope=scope,
                    reason="Skipped Composer dev pseudo-version because it is not a reproducible Packagist release artifact.",
                ))
                continue
            if dep_version:
                child = ComposerArtifact(name=canonical, version=dep_version, scope=scope, source=composer_pkg_key(artifact), requested=requested)
                child_key = composer_pkg_key(child)
                if child_key not in seen_children:
                    seen_children.add(child_key)
                    children.append(child)

    return children, issues, skipped


def resolve_composer_transitives(
    roots: list[ComposerArtifact],
    max_depth: int,
    max_artifacts: int | None = None,
) -> tuple[dict[str, ComposerArtifact], list[DependencyEdge], list[ResolutionIssue], list[SkippedArtifact]]:
    discovered: dict[str, ComposerArtifact] = {}
    edges: list[DependencyEdge] = []
    issues: list[ResolutionIssue] = []
    skipped: list[SkippedArtifact] = []
    queue: list[tuple[ComposerArtifact, int]] = [(a, 0) for a in roots]
    processed: set[str] = set()

    while queue:
        if max_artifacts is not None and len(discovered) >= max_artifacts:
            issues.append(ResolutionIssue("pkg:composer", f"Stopped Composer traversal after reaching --php-max-artifacts={max_artifacts}; remaining queue={len(queue)}"))
            break
        current, depth = queue.pop(0)
        key = composer_pkg_key(current)
        if key not in discovered:
            discovered[key] = current
        if key in processed:
            continue
        processed.add(key)
        if max_depth > 0 and depth >= max_depth:
            continue

        children, child_issues, child_skipped = resolve_composer_pkg(current)
        issues.extend(child_issues)
        skipped.extend(child_skipped)
        for child in children:
            child_key = composer_pkg_key(child)
            edges.append(DependencyEdge(parent=key, child=child_key))
            if child_key not in discovered:
                discovered[child_key] = child
                queue.append((child, depth + 1))

    return discovered, edges, issues, skipped


def remove_composer_platform_pkgs(sbom_data: dict[str, Any]) -> list[PackageValidationFinding]:
    sbom = sbom_data.get("sbom", sbom_data)
    findings: list[PackageValidationFinding] = []
    remove_ids: set[str] = set()
    new_packages: list[Any] = []

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            new_packages.append(pkg)
            continue
        is_platform = False
        platform_name = None
        for ref in pkg.get("externalRefs", []) or []:
            if not isinstance(ref, dict):
                continue
            loc = ref.get("referenceLocator")
            if isinstance(loc, str) and loc.startswith("pkg:composer/"):
                body = loc[len("pkg:composer/"):].split("?", 1)[0]
                name = body.rsplit("@", 1)[0] if "@" in body else body
                if is_composer_platform_pkg(name):
                    is_platform = True
                    platform_name = canonical_composer_name(name)
                    break
        if is_platform:
            spdx_id = pkg.get("SPDXID")
            if isinstance(spdx_id, str):
                remove_ids.add(spdx_id)
                findings.append(PackageValidationFinding(
                    artifact=f"pkg:composer/{platform_name}",
                    spdx_id=spdx_id,
                    field="package",
                    action="removed",
                    old_value=platform_name,
                    new_value=None,
                    notes="Removed Composer platform requirement from package graph; it is an environment constraint, not a Packagist package.",
                ))
            continue
        new_packages.append(pkg)

    if remove_ids:
        sbom["packages"] = new_packages
        sbom["relationships"] = [
            rel for rel in (sbom.get("relationships", []) or [])
            if not (isinstance(rel, dict) and (rel.get("spdxElementId") in remove_ids or rel.get("relatedSpdxElement") in remove_ids))
        ]
    return findings


def remove_non_reproducible_composer_pkgs(sbom_data: dict[str, Any]) -> list[PackageValidationFinding]:
    sbom = sbom_data.get("sbom", sbom_data)
    findings: list[PackageValidationFinding] = []
    remove_ids: set[str] = set()
    new_packages: list[Any] = []

    for pkg in sbom.get("packages", []) or []:
        if not isinstance(pkg, dict):
            new_packages.append(pkg)
            continue
        spdx_id = pkg.get("SPDXID")
        composer_name = None
        composer_version = None
        for ref in pkg.get("externalRefs", []) or []:
            if not isinstance(ref, dict):
                continue
            loc = ref.get("referenceLocator")
            if not isinstance(loc, str) or not loc.startswith("pkg:composer/"):
                continue
            body = loc[len("pkg:composer/"):].split("?", 1)[0]
            if "@" in body:
                name_part, version_part = body.rsplit("@", 1)
                composer_name = canonical_composer_name(urllib.parse.unquote(name_part))
                composer_version = urllib.parse.unquote(version_part)
            else:
                composer_name = canonical_composer_name(urllib.parse.unquote(body))
                composer_version = str(pkg.get("versionInfo") or "")
            break

        remove_reason = None
        if composer_name and composer_version and is_non_reproducible_composer_dev(composer_version):
            remove_reason = "Removed Composer dev pseudo-version from package graph; it is not a reproducible Packagist release artifact."
        elif composer_name and is_expected_non_packagist(composer_name) and pkg.get("downloadLocation") in {None, "NOASSERTION", ""}:
            remove_reason = "Removed Composer test/integration pseudo-package that Packagist does not expose as a normal release artifact."

        if remove_reason and isinstance(spdx_id, str):
            remove_ids.add(spdx_id)
            findings.append(PackageValidationFinding(
                artifact=f"pkg:composer/{composer_name}@{composer_version}" if composer_name and composer_version else "pkg:composer",
                spdx_id=spdx_id,
                field="package",
                action="removed",
                old_value=composer_version,
                new_value=None,
                notes=remove_reason,
            ))
            continue
        new_packages.append(pkg)

    if remove_ids:
        sbom["packages"] = new_packages
        sbom["relationships"] = [
            rel for rel in (sbom.get("relationships", []) or [])
            if not (isinstance(rel, dict) and (rel.get("spdxElementId") in remove_ids or rel.get("relatedSpdxElement") in remove_ids))
        ]
    return findings

def is_expected_composer_issue(issue: ResolutionIssue) -> bool:
    if not issue.artifact.startswith("pkg:composer/"):
        return False
    reason = issue.reason.lower()
    return any(
        marker in reason
        for marker in (
            "composer package not found on packagist: http 404",
            "packagist did not confirm exact package version",
            "skipped composer branch/alias dev constraint",
            "skipped non-registry composer dependency constraint",
            "skipped composer unstable/stability constraint without a reproducible release artifact",
            "no packagist release satisfies composer constraint",
        )
    )


def suppress_expected_composer_issues(issues: list[ResolutionIssue]) -> list[ResolutionIssue]:
    return [issue for issue in issues if not is_expected_composer_issue(issue)]


def add_composer_transitives(
    sbom_data: dict[str, Any],
    discovered: dict[str, ComposerArtifact],
    edges: list[DependencyEdge],
) -> tuple[dict[str, Any], list[PackageValidationFinding], list[ResolutionIssue]]:
    sbom = sbom_data.get("sbom", sbom_data)
    sbom.setdefault("packages", [])
    sbom.setdefault("relationships", [])

    findings: list[PackageValidationFinding] = []
    metadata_issues: list[ResolutionIssue] = []
    findings.extend(remove_composer_platform_pkgs(sbom_data))
    normalize_findings, normalize_issues = normalize_composer_pkgs(sbom_data, discovered)
    findings.extend(normalize_findings)
    metadata_issues.extend(normalize_issues)

    identity_to_spdxid = build_composer_id_to_spdxid(sbom_data)
    identity_to_package = build_composer_id_to_pkg(sbom_data)

    for key, artifact in discovered.items():
        metadata, issues = get_composer_metadata_from_packagist(artifact)
        if is_non_reproducible_composer_dev(artifact.version):
            findings.append(PackageValidationFinding(
                artifact=key,
                spdx_id=None,
                field="package",
                action="skipped",
                old_value=composer_pkg_purl(artifact),
                new_value=None,
                notes="Skipped Composer dev pseudo-version; it is not a reproducible Packagist release artifact.",
            ))
            continue
        if metadata.download_url is None and is_expected_non_packagist(artifact.name):
            findings.append(PackageValidationFinding(
                artifact=key,
                spdx_id=None,
                field="package",
                action="skipped",
                old_value=composer_pkg_purl(artifact),
                new_value=None,
                notes="Skipped Composer test/integration package that Packagist does not expose as a normal release artifact.",
            ))
            continue
        metadata_issues.extend(issues)
        if key in identity_to_spdxid:
            existing_spdx = identity_to_spdxid[key]
            existing_pkg = identity_to_package.get(key)
            findings.append(PackageValidationFinding(
                artifact=key,
                spdx_id=existing_spdx,
                field="package",
                action="existed",
                old_value=composer_pkg_purl(artifact),
                new_value=composer_pkg_purl(artifact),
                notes="Composer package was already present in the input SBOM; enrichment/validation was attempted.",
            ))
            if existing_pkg is not None:
                enrich_pkg_with_composer_metadata(existing_pkg, artifact, metadata, findings)
            continue

        package = composer_pkg_to_spdx_pkg(artifact, metadata)
        sbom["packages"].append(package)
        identity_to_spdxid[key] = package["SPDXID"]
        identity_to_package[key] = package
        findings.append(PackageValidationFinding(
            artifact=key,
            spdx_id=package["SPDXID"],
            field="package",
            action="added",
            old_value=None,
            new_value=composer_pkg_purl(artifact),
            notes="Package added from Packagist Composer transitive resolution.",
        ))

    for edge in edges:
        parent_spdxid = identity_to_spdxid.get(edge.parent)
        child_spdxid = identity_to_spdxid.get(edge.child)
        if not parent_spdxid or not child_spdxid:
            continue
        if has_relationship(sbom_data, parent_spdxid, child_spdxid, "DEPENDS_ON"):
            continue
        sbom["relationships"].append({"spdxElementId": parent_spdxid, "relatedSpdxElement": child_spdxid, "relationshipType": "DEPENDS_ON"})

    findings.extend(remove_non_reproducible_composer_pkgs(sbom_data))
    findings.extend(dedupe_composer_pkgs_and_rels(sbom_data))
    findings.extend(remove_composer_platform_pkgs(sbom_data))
    findings.extend(remove_non_reproducible_composer_pkgs(sbom_data))
    return sbom_data, findings, metadata_issues


# -------------------------
# Main
# -------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description="Java-first transitive dependency finder for SPDX SBOMs.")
    parser.add_argument("sbom", help="Path to surface-level SPDX SBOM JSON")
    parser.add_argument("--max-depth", type=int, default=10)
    parser.add_argument("--pypi-max-depth", type=int, default=4, help="PyPI-only max recursion depth. Default 4 to avoid Python registry explosion.")
    parser.add_argument("--pypi-root-mode", choices=["direct", "all"], default="direct", help="Use only project direct PyPI dependencies when relationships exist, or all PyPI packages in the input SBOM.")
    parser.add_argument("--pypi-max-artifacts", type=int, default=2000, help="Safety cap for PyPI traversal. Use 0 for no cap.")
    parser.add_argument("--go-max-depth", type=int, default=10, help="Go module max recursion depth. Default 10.")
    parser.add_argument("--go-max-artifacts", type=int, default=10000, help="Safety cap for Go module traversal. Use 0 for no cap. Default 10000.")
    parser.add_argument("--rust-max-depth", type=int, default=0, help="Rust/Cargo max recursion depth. Use 0 for no depth limit. Default 0.")
    parser.add_argument("--rust-max-artifacts", type=int, default=0, help="Safety cap for Rust/Cargo traversal. Use 0 for no cap. Default 0.")
    parser.add_argument("--php-max-depth", type=int, default=0, help="PHP/Composer max recursion depth. Use 0 for no depth limit. Default 0.")
    parser.add_argument("--php-max-artifacts", type=int, default=0, help="Safety cap for PHP/Composer traversal. Use 0 for no cap. Default 0.")
    parser.add_argument("--log", action="store_true")
    args = parser.parse_args()

    sbom_path = Path(args.sbom).resolve()
    sbom_data = json.loads(sbom_path.read_text(encoding="utf-8"))

    maven_roots = get_maven_coords(sbom_data)
    npm_roots = get_npm_pkgs(sbom_data)
    all_pypi_roots_for_context = get_all_pypi_pkgs(sbom_data)
    direct_pypi_roots_for_context = get_direct_pypi_pkgs(sbom_data)
    pypi_roots = get_pypi_pkgs(sbom_data, args.pypi_root_mode)
    go_roots = get_go_pkgs(sbom_data)
    rust_roots = get_rust_pkgs(sbom_data)
    composer_roots = get_composer_pkgs(sbom_data)

    print(f"[START] Roots: Maven={len(maven_roots)} npm={len(npm_roots)} PyPI={len(pypi_roots)} Go={len(go_roots)} Rust={len(rust_roots)} PHP={len(composer_roots)}")
    print(f"[START] PyPI root mode={args.pypi_root_mode}; direct_roots={len(direct_pypi_roots_for_context)} all_pypi_packages_in_input={len(all_pypi_roots_for_context)}")

    maven_discovered, maven_edges, maven_issues, maven_skipped, repositories_by_artifact = resolve_transitives(maven_roots, args.max_depth)
    output_data, maven_validation_findings, maven_metadata_issues = add_maven_transitives(sbom_data, maven_discovered, maven_edges, repositories_by_artifact)

    npm_discovered, npm_edges, npm_issues, npm_skipped = resolve_npm_transitives(npm_roots, args.max_depth)
    output_data, npm_validation_findings, npm_metadata_issues = add_npm_transitives(output_data, npm_discovered, npm_edges)

    pypi_depth = args.pypi_max_depth if args.pypi_max_depth is not None else args.max_depth
    pypi_max_artifacts = None if args.pypi_max_artifacts == 0 else args.pypi_max_artifacts
    pypi_discovered, pypi_edges, pypi_issues, pypi_skipped = resolve_pypi_transitives(pypi_roots, pypi_depth, pypi_max_artifacts)
    output_data, pypi_validation_findings, pypi_metadata_issues = add_pypi_transitives(output_data, pypi_discovered, pypi_edges)

    go_max_artifacts = None if args.go_max_artifacts == 0 else args.go_max_artifacts
    go_discovered, go_edges, go_issues, go_skipped = resolve_go_transitives(go_roots, args.go_max_depth, go_max_artifacts)
    output_data, go_validation_findings, go_metadata_issues = add_go_transitives(output_data, go_discovered, go_edges)

    rust_max_artifacts = None if args.rust_max_artifacts == 0 else args.rust_max_artifacts
    rust_discovered, rust_edges, rust_issues, rust_skipped = resolve_rust_transitives(rust_roots, args.rust_max_depth, rust_max_artifacts)
    output_data, rust_validation_findings, rust_metadata_issues = add_rust_transitives(output_data, rust_discovered, rust_edges)

    php_max_artifacts = None if args.php_max_artifacts == 0 else args.php_max_artifacts
    composer_discovered, composer_edges, composer_issues, composer_skipped = resolve_composer_transitives(composer_roots, args.php_max_depth, php_max_artifacts)
    output_data, composer_validation_findings, composer_metadata_issues = add_composer_transitives(output_data, composer_discovered, composer_edges)

    issues = dedupe_issues(suppress_expected_composer_issues(suppress_expected_rust_issues([*maven_issues, *maven_metadata_issues, *npm_issues, *npm_metadata_issues, *pypi_issues, *pypi_metadata_issues, *go_issues, *go_metadata_issues, *rust_issues, *rust_metadata_issues, *composer_issues, *composer_metadata_issues])))
    validation_findings = [*maven_validation_findings, *npm_validation_findings, *pypi_validation_findings, *go_validation_findings, *rust_validation_findings, *composer_validation_findings]
    skipped = [*maven_skipped, *npm_skipped, *pypi_skipped, *go_skipped, *rust_skipped, *composer_skipped]

    output_path = sbom_path.with_name(f"transitive_{sbom_path.name}")
    output_path.write_text(json.dumps(output_data, indent=2), encoding="utf-8")

    print(f"+ Root Maven artifacts found: {len(maven_roots)}")
    print(f"+ Total Maven artifacts discovered: {len(maven_discovered)}")
    print(f"+ Maven dependency relationships discovered: {len(maven_edges)}")
    print(f"+ Root npm artifacts found: {len(npm_roots)}")
    print(f"+ Total npm artifacts discovered: {len(npm_discovered)}")
    print(f"+ npm dependency relationships discovered: {len(npm_edges)}")
    print(f"+ Root PyPI artifacts found: {len(pypi_roots)}")
    print(f"+ Total PyPI artifacts discovered: {len(pypi_discovered)}")
    print(f"+ PyPI dependency relationships discovered: {len(pypi_edges)}")
    print(f"+ Root Go modules found: {len(go_roots)}")
    print(f"+ Total Go modules discovered: {len(go_discovered)}")
    print(f"+ Go dependency relationships discovered: {len(go_edges)}")
    print(f"+ Root Rust crates found: {len(rust_roots)}")
    print(f"+ Total Rust crates discovered: {len(rust_discovered)}")
    print(f"+ Rust dependency relationships discovered: {len(rust_edges)}")
    print(f"+ Root PHP/Composer packages found: {len(composer_roots)}")
    print(f"+ Total PHP/Composer packages discovered: {len(composer_discovered)}")
    print(f"+ PHP/Composer dependency relationships discovered: {len(composer_edges)}")
    print(f"+ Package validation/enrichment findings: {len(validation_findings)}")
    print(f"+ Resolution issues: {len(issues)}")
    print(f"+ Skipped transitives: {len(skipped)}")
    print(f"+ Transitive SBOM written to: {output_path}")

    if args.log:
        logs_dir = sbom_path.parent / "logs"
        logs_dir.mkdir(parents=True, exist_ok=True)
        log_path = logs_dir / "transitive_report.json"
        log_data = {
            "input_sbom": str(sbom_path),
            "output_sbom": str(output_path),
            "root_maven_artifacts": [asdict(a) for a in maven_roots],
            "root_npm_artifacts": [asdict(a) for a in npm_roots],
            "root_pypi_artifacts": [asdict(a) for a in pypi_roots],
            "root_go_artifacts": [asdict(a) for a in go_roots],
            "root_rust_artifacts": [asdict(a) for a in rust_roots],
            "root_composer_artifacts": [asdict(a) for a in composer_roots],
            "pypi_root_mode": args.pypi_root_mode,
            "direct_pypi_roots_detected": [asdict(a) for a in direct_pypi_roots_for_context],
            "all_pypi_packages_in_input": [asdict(a) for a in all_pypi_roots_for_context],
            "root_artifacts": [asdict(a) for a in maven_roots],
            "discovered_artifacts": [asdict(a) for a in maven_discovered.values()],
            "discovered_maven_artifacts": [asdict(a) for a in maven_discovered.values()],
            "discovered_npm_artifacts": [asdict(a) for a in npm_discovered.values()],
            "discovered_pypi_artifacts": [asdict(a) for a in pypi_discovered.values()],
            "discovered_go_artifacts": [asdict(a) for a in go_discovered.values()],
            "discovered_rust_artifacts": [asdict(a) for a in rust_discovered.values()],
            "discovered_composer_artifacts": [asdict(a) for a in composer_discovered.values()],
            "issues": [asdict(i) for i in issues],
            "skipped_artifacts": [asdict(s) for s in skipped],
            "dependency_edges": [asdict(e) for e in [*maven_edges, *npm_edges, *pypi_edges, *go_edges, *rust_edges, *composer_edges]],
            "maven_dependency_edges": [asdict(e) for e in maven_edges],
            "npm_dependency_edges": [asdict(e) for e in npm_edges],
            "pypi_dependency_edges": [asdict(e) for e in pypi_edges],
            "go_dependency_edges": [asdict(e) for e in go_edges],
            "rust_dependency_edges": [asdict(e) for e in rust_edges],
            "composer_dependency_edges": [asdict(e) for e in composer_edges],
            "package_validation_findings": [asdict(f) for f in validation_findings],
            "repositories_by_artifact": repositories_by_artifact,
        }

        log_path.write_text(json.dumps(make_json_safe(log_data), indent=2), encoding="utf-8")
        print(f"+ Transitive log written to: {log_path}")


if __name__ == "__main__":
    main()
