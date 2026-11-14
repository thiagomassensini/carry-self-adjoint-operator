#!/usr/bin/env python3
"""Find Lean trust-escape tokens while ignoring line and block comments."""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
TOKEN_PATTERN = re.compile(r"(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)")
CHAR_LITERAL = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|.)|[^'\\\r\n])'")


def _blank_non_newlines(chars: list[str], start: int, end: int) -> None:
    for index in range(start, end):
        if chars[index] not in "\r\n":
            chars[index] = " "


def strip_comments(source: str) -> str:
    """Mask Lean line/nested block comments, preserving strings and line numbers."""
    chars = list(source)
    index = 0
    depth = 0
    in_line_comment = False
    in_string = False

    while index < len(source):
        if in_line_comment:
            if source[index] in "\r\n":
                in_line_comment = False
            else:
                chars[index] = " "
            index += 1
            continue

        if depth:
            if source.startswith("/-", index):
                _blank_non_newlines(chars, index, index + 2)
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                _blank_non_newlines(chars, index, index + 2)
                depth -= 1
                index += 2
            else:
                if source[index] not in "\r\n":
                    chars[index] = " "
                index += 1
            continue

        if in_string:
            if source[index] == "\\":
                index = min(index + 2, len(source))
            elif source[index] == '"':
                in_string = False
                index += 1
            else:
                index += 1
            continue

        if source.startswith("--", index):
            chars[index] = chars[index + 1] = " "
            in_line_comment = True
            index += 2
        elif source.startswith("/-", index):
            _blank_non_newlines(chars, index, index + 2)
            depth = 1
            index += 2
        elif source[index] == "'" and (char_match := CHAR_LITERAL.match(source, index)):
            index = char_match.end()
        elif source[index] == '"':
            in_string = True
            index += 1
        else:
            index += 1

    return "".join(chars)


def lean_files() -> list[Path]:
    files = sorted((ROOT / "CarrySelfAdjointOperator").rglob("*.lean"))
    root_aggregator = ROOT / "CarrySelfAdjointOperator.lean"
    if root_aggregator.is_file():
        files.append(root_aggregator)
    return files


def main() -> int:
    findings = 0
    for path in lean_files():
        source = path.read_text(encoding="utf-8")
        code = strip_comments(source)
        for match in TOKEN_PATTERN.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            print(f"{path.relative_to(ROOT)}:{line}: trust escape token {match.group(2)}")
            findings += 1

    if findings:
        return 1
    print("Lean trust-escape scan passed (comments ignored)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
