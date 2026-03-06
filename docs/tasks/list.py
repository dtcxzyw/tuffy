#!/usr/bin/env python3
"""List incomplete tasks from docs/tasks/, sorted by creation date."""

import os
import re
from pathlib import Path
from datetime import datetime

def parse_task(path):
    """Extract status and created date from task file."""
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()

    status_match = re.search(r'Status:\s*(.+)', content)
    created_match = re.search(r'Created:\s*(\d{4}-\d{2}-\d{2})', content)
    title_match = re.search(r'#\s+(.+)', content)

    status = status_match.group(1).strip() if status_match else 'Unknown'
    created = created_match.group(1) if created_match else '9999-99-99'
    title = title_match.group(1).strip() if title_match else path.name

    return status, created, title

def main():
    tasks_dir = Path(__file__).parent
    tasks = []

    for md_file in tasks_dir.rglob('*.md'):
        if md_file.name in ['template.md', 'README.md']:
            continue

        status, created, title = parse_task(md_file)

        if status.lower() not in ['completed', 'cancelled', 'abandoned']:
            rel_path = md_file.relative_to(tasks_dir)
            tasks.append((created, status, title, rel_path))

    tasks.sort()

    print(f"Incomplete Tasks ({len(tasks)}):\n")
    for created, status, title, path in tasks:
        print(f"[{status}] {created} - {title}")
        print(f"  {path}\n")

if __name__ == '__main__':
    main()
