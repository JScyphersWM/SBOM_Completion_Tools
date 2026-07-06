from __future__ import annotations
import argparse
import json
import os
import subprocess
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import urlparse

import requests


@dataclass
class RepoInfo:
    url: str
    owner: str
    name: str
    local_path: Path

def get_url(repo_url: str, workspace: Path) -> RepoInfo:
    repo_url = repo_url.strip()

    if "/" in repo_url and not repo_url.startswith("http"):
        owner, name = repo_url.split("/", 1)
        name = name.removesuffix(".git")
        return RepoInfo(
            url=f"https://github.com/{owner}/{name}",
            owner =owner,
            name = name,
            local_path=workspace / owner / name,
        )

    parsed = urlparse(repo_url)
    if parsed.netloc.lower() != "github.com":
        raise ValueError(f"Only GitHub URLs are currently supported: {repo_url}")

    parts = parsed.path.strip("/").split("/")
    if len(parts) < 2:
        raise ValueError(f"Invalid GitHub repo URL: {repo_url}")

    owner = parts[0]
    name = parts[1].removesuffix(".git")

    return RepoInfo(url=f"https://github.com/{owner}/{name}", owner=owner, name=name, local_path=workspace / owner / name,
    )


def run_command(command: list[str], cwd: Path | None = None) -> None:
    print(f"\nRUN: {' '.join(command)}")
    subprocess.run(command, cwd=cwd, check=True)

# Clones repo locally for the surface_scanner.py to use
def clone_repo(repo_url: str, workspace_dir: str = "workspace") -> RepoInfo:
    workspace = Path(workspace_dir).resolve()
    workspace.mkdir(parents=True, exist_ok=True)
    repo = get_url(repo_url, workspace)

    if repo.local_path.exists():
        print(f"Repo already exists: {repo.local_path}")
    else:
        print(f"CLONE: {repo.url} -> {repo.local_path}")
        run_command(["git", "clone", "--depth", "1", repo.url, str(repo.local_path)])

    return repo

# Grabs SBOM from github to use as a baseline
def download_sbom(repo: RepoInfo, output_dir: str = "generated_sboms") -> Path:
    api_url = f"https://api.github.com/repos/{repo.owner}/{repo.name}/dependency-graph/sbom"
    headers = {
        "Accept": "application/vnd.github+json",
    }
    token = os.getenv("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"

    print(f"GitHub SBOM Requesting: {api_url}")

    response = requests.get(api_url, headers=headers, timeout=30)
    if response.status_code != 200:
        raise RuntimeError(
            f"GitHub SBOM request failed.\n"
            f"Status: {response.status_code}\n"
            f"Response: {response.text}\n\n"
            f"Possible private repo, try to set GITHUB_TOKEN with your token in the settings, and if that doesn't work then use a different SBOM generator."
        )

    output_path = Path(output_dir).resolve()
    output_path.mkdir(parents=True, exist_ok=True)
    sbom_json= response.json()
    repo_dir = output_path / f"{repo.owner}_{repo.name}"
    repo_dir.mkdir(parents=True, exist_ok=True)
    final_path = repo_dir / "github.spdx.json"

    with final_path.open("w", encoding="utf-8") as f:
        json.dump(sbom_json, f, indent=2)

    print(f"GitHub SBOM saved to: {final_path}")
    return final_path


def load_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


# Generate the SBOM and return it for surface scanner processing
def generate_baseline(repo_url: str) -> Path:
    repo = clone_repo(repo_url)
    return download_sbom(repo)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Clone a GitHub repository and download its GitHub SBOM."
    )

    parser.add_argument(
        "repo",
        help="GitHub repository URL/shorthand, example: https://github.com/owner/repo or owner/repo for this tool to use",
    )

    args = parser.parse_args()

    repo = clone_repo(args.repo)
    download_sbom(repo)


if __name__ == "__main__":
    main()

# TODO:
# 1. Download GitHub SBOM - done
# 2. Scan repository for missing surface-level dependencies - done, surface_scanner.py
# 3. Add missing dependencies to baseline SBOM - done, surface_scanner.py, surface_builder.py merged into scanner, only supports core 6 from code pulled from main files
# 4. Enrich transitive/test/platform dependencies - ongoing but core 6 languages pulled out of main file for thesis phase, transitive_finder.py
# 5. Validate completed SBOM - done but not perfect (manual review required to ensure 100% accuracy), compare_sboms.py
