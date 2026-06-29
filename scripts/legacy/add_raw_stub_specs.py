#!/usr/bin/env python3
"""Add raw-level stub specifications to HumanEval markdown sources."""

from __future__ import annotations

import re
import textwrap
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
RAW_HUMANEVAL = ROOT / "raw" / "humaneval"


SPEC_TEXT = {
    "malloc_int_array_struct": textwrap.dedent(
        """
        ### `malloc_int_array_struct`

        Allocates a fresh `IntArray` header object.

        Contract shape:

        ```c
        IntArray *malloc_int_array_struct()
        /*@ Require emp
            Ensure __return != 0 &&
                   undef_data_at(&(__return -> data)) *
                   undef_data_at(&(__return -> size))
        */;
        ```
        """
    ).strip(),
    "malloc_int_array": textwrap.dedent(
        """
        ### `malloc_int_array`

        Allocates a fresh writable integer array with unspecified contents.

        Contract shape:

        ```c
        int *malloc_int_array(int size)
        /*@ Require size >= 0 && size < INT_MAX
            Ensure __return != 0 && IntArray::undef_full(__return, size)
        */;
        ```
        """
    ).strip(),
    "malloc_char_array": textwrap.dedent(
        """
        ### `malloc_char_array`

        Allocates a fresh writable character array with unspecified contents.

        Contract shape:

        ```c
        char *malloc_char_array(int n)
        /*@ Require n > 0 && n < INT_MAX
            Ensure __return != 0 && CharArray::undef_full(__return, n)
        */;
        ```
        """
    ).strip(),
    "strlen": textwrap.dedent(
        """
        ### `strlen`

        Coq model: represent strings as a list `l : list Z` of nonzero byte values followed by a zero terminator in memory.

        Contract shape:

        ```c
        int strlen(char *s)
        /*@ With l n
            Require 0 <= n && n < INT_MAX &&
                    Zlength(l) == n &&
                    (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
                    CharArray::full(s, n + 1, app(l, cons(0, nil)))
            Ensure __return == n &&
                   CharArray::full(s, n + 1, app(l, cons(0, nil)))
        */;
        ```
        """
    ).strip(),
    "strchr": textwrap.dedent(
        """
        ### `strchr`

        Coq model: define a relation over the input character list, searched byte `c`, and result pointer. The result is `0` iff `c` does not occur before the terminator; otherwise it points to an occurrence of `c` inside the owned string.

        Contract shape:

        ```c
        char *strchr(char *s, int c)
        /*@ With l n
            Require 0 <= n && n < INT_MAX &&
                    Zlength(l) == n &&
                    CharArray::full(s, n + 1, app(l, cons(0, nil)))
            Ensure CharArray::full(s, n + 1, app(l, cons(0, nil))) &&
                   strchr_spec(s, l, c, __return)
        */;
        ```
        """
    ).strip(),
    "free_int_array": textwrap.dedent(
        """
        ### `free_int_array`

        Consumes ownership of a previously allocated integer array.

        Contract shape:

        ```c
        void free_int_array(int *array, int size)
        /*@ With l
            Require size >= 0 && Zlength(l) == size &&
                    IntArray::full(array, size, l)
            Ensure emp
        */;
        ```
        """
    ).strip(),
    "free_char_array": textwrap.dedent(
        """
        ### `free_char_array`

        Consumes ownership of a previously allocated character array.

        Contract shape:

        ```c
        void free_char_array(char *p, int init_size, int size)
        /*@ With l
            Require size >= 0 && init_size >= size && Zlength(l) == size &&
                    CharArray::full(p, size, l)
            Ensure emp
        */;
        ```
        """
    ).strip(),
    "sort_int_array": textwrap.dedent(
        """
        ### `sort_int_array`

        Coq model: define a relation stating that the output list is sorted in the requested direction and is a permutation of the input list.

        Contract shape:

        ```c
        void sort_int_array(int *array, int init_size, int size, int ascending)
        /*@ With l
            Require 0 <= size && size <= init_size && Zlength(l) == init_size &&
                    IntArray::full(array, init_size, l)
            Ensure exists out_l,
                   sort_int_array_spec(l, size, ascending, out_l) &&
                   IntArray::full(array, init_size, out_l)
        */;
        ```
        """
    ).strip(),
    "sort_char_array": textwrap.dedent(
        """
        ### `sort_char_array`

        Coq model: define a relation stating that the output character list is sorted and is a permutation of the input character list.

        Contract shape:

        ```c
        void sort_char_array(char *p, int n)
        /*@ With l
            Require 0 <= n && Zlength(l) == n &&
                    CharArray::full(p, n, l)
            Ensure exists out_l,
                   sort_char_array_spec(l, out_l) &&
                   CharArray::full(p, n, out_l)
        */;
        ```
        """
    ).strip(),
    "copy_char_array": textwrap.dedent(
        """
        ### `copy_char_array`

        Coq model: define a relation describing the destination list after copying `len` bytes from `src` into `dst + off`, preserving all other destination positions.

        Contract shape:

        ```c
        void copy_char_array(char *dst, int off, char *src, int len, int cap)
        /*@ With dst_l src_l
            Require 0 <= off && 0 <= len && off + len <= cap &&
                    Zlength(dst_l) == cap && Zlength(src_l) == len &&
                    CharArray::full(dst, cap, dst_l) *
                    CharArray::full(src, len, src_l)
            Ensure exists out_l,
                   copy_char_array_spec(dst_l, src_l, off, out_l) &&
                   CharArray::full(dst, cap, out_l) *
                   CharArray::full(src, len, src_l)
        */;
        ```
        """
    ).strip(),
    "abs": textwrap.dedent(
        """
        ### `abs`

        Coq model:

        ```coq
        Definition he_abs_spec (x r : Z) : Prop :=
          r = Z.abs x.
        ```

        Contract shape:

        ```c
        int abs(int x)
        /*@ Require INT_MIN < x && x <= INT_MAX
            Ensure he_abs_spec(x, __return)
        */;
        ```
        """
    ).strip(),
    "he_external_round": textwrap.dedent(
        """
        ### `he_external_round`

        Coq model: define nearest-integer rounding with ties away from zero, matching the HumanEval statement when used for closest-integer tasks.

        Contract shape:

        ```c
        int he_external_round(double x)
        /*@ Require emp
            Ensure he_round_spec(x, __return)
        */;
        ```
        """
    ).strip(),
    "he_external_ceil": textwrap.dedent(
        """
        ### `he_external_ceil`

        Coq model: define the least integer greater than or equal to the input value.

        Contract shape:

        ```c
        int he_external_ceil(double x)
        /*@ Require emp
            Ensure he_ceil_spec(x, __return)
        */;
        ```
        """
    ).strip(),
    "he_external_pow": textwrap.dedent(
        """
        ### `he_external_pow`

        Coq model: define the mathematical power needed by the task. For integer exponents use repeated multiplication; for exponent `0.5`, use the square-root relation.

        Contract shape:

        ```c
        double he_external_pow(double x, double y)
        /*@ Require emp
            Ensure he_pow_spec(x, y, __return)
        */;
        ```
        """
    ).strip(),
    "he_external_fabs": textwrap.dedent(
        """
        ### `he_external_fabs`

        Coq model: define nonnegative absolute value over the chosen real-number model.

        Contract shape:

        ```c
        double he_external_fabs(double x)
        /*@ Require emp
            Ensure he_fabs_spec(x, __return)
        */;
        ```
        """
    ).strip(),
    "he_external_strtod": textwrap.dedent(
        """
        ### `he_external_strtod`

        Coq model: define decimal-string parsing for the accepted input grammar in the task statement.

        Contract shape:

        ```c
        double he_external_strtod(const char *s)
        /*@ With l n
            Require 0 <= n && n < INT_MAX &&
                    Zlength(l) == n &&
                    CharArray::full(s, n + 1, app(l, cons(0, nil)))
            Ensure CharArray::full(s, n + 1, app(l, cons(0, nil))) &&
                   he_strtod_spec(l, __return)
        */;
        ```
        """
    ).strip(),
}


ORDER = [
    "malloc_int_array_struct",
    "malloc_int_array",
    "malloc_char_array",
    "strlen",
    "strchr",
    "free_int_array",
    "free_char_array",
    "sort_int_array",
    "sort_char_array",
    "copy_char_array",
    "abs",
    "he_external_round",
    "he_external_ceil",
    "he_external_pow",
    "he_external_fabs",
    "he_external_strtod",
]


PROTOTYPES = {
    "he_external_round": "int he_external_round(double x);",
    "he_external_ceil": "int he_external_ceil(double x);",
    "he_external_pow": "double he_external_pow(double x, double y);",
    "he_external_fabs": "double he_external_fabs(double x);",
    "he_external_strtod": "double he_external_strtod(const char *s);",
}

EXTERNAL_PROTO_RE = re.compile(
    r"^\s*(?:int|double)\s+he_external_(?:round|ceil|pow|fabs|strtod)\s*\([^;\n]*\);\n?",
    flags=re.M,
)


def remove_existing_section(text: str) -> str:
    text = re.sub(
        r"\n+## Stub Function Specifications\n\n.*?(?=\n+## Reference Implementation\n)",
        "\n\n",
        text,
        flags=re.S,
    )
    return normalize_reference_spacing(text)


def normalize_reference_spacing(text: str) -> str:
    return re.sub(r"\n{3,}(?=## Reference Implementation\n)", "\n\n", text)


def first_c_block(text: str) -> tuple[str, str, str] | None:
    match = re.search(r"```c\n(.*?)\n```", text, flags=re.S)
    if not match:
        return None
    return text[: match.start(1)], match.group(1), text[match.end(1) :]


def protect_non_code(code: str) -> tuple[str, list[str]]:
    protected: list[str] = []

    def save(match: re.Match[str]) -> str:
        protected.append(match.group(0))
        return f"__HE_PROTECTED_{len(protected) - 1}__"

    pattern = r"/\*.*?\*/|//[^\n]*|\"(?:\\.|[^\"\\])*\"|'(?:\\.|[^'\\])*'"
    return re.sub(pattern, save, code, flags=re.S), protected


def restore_non_code(code: str, protected: list[str]) -> str:
    for index, original in enumerate(protected):
        code = code.replace(f"__HE_PROTECTED_{index}__", original)
    return code


def transform_external_calls(code: str) -> tuple[str, set[str]]:
    specs: set[str] = set()
    code = EXTERNAL_PROTO_RE.sub("", code)
    search_code, protected = protect_non_code(code)
    replacements = [
        (r"(?<!he_external_)\bround\s*\(", "he_external_round(", "he_external_round"),
        (r"(?<!he_external_)\bceil\s*\(", "he_external_ceil(", "he_external_ceil"),
        (r"(?<!he_external_)\bpow\s*\(", "he_external_pow(", "he_external_pow"),
        (r"(?<!he_external_)\bfabs\s*\(", "he_external_fabs(", "he_external_fabs"),
    ]
    for pattern, repl, spec in replacements:
        if re.search(pattern, search_code):
            search_code = re.sub(pattern, repl, search_code)
            specs.add(spec)
    if re.search(r"\bstrtod\s*\(", search_code):
        search_code = re.sub(r"\bstrtod\s*\(([^,\n]+),\s*NULL\s*\)", r"he_external_strtod(\1)", search_code)
        specs.add("he_external_strtod")
    for spec in PROTOTYPES:
        if re.search(rf"\b{spec}\s*\(", search_code):
            specs.add(spec)
    code = restore_non_code(search_code, protected)
    prototypes = [PROTOTYPES[name] for name in ORDER if name in specs and name in PROTOTYPES]
    if prototypes:
        code = "\n".join(prototypes) + "\n" + code
    return code, specs


def detect_specs(code: str, external_specs: set[str]) -> list[str]:
    specs = set(external_specs)
    search_code, _ = protect_non_code(code)
    checks = {
        "malloc_int_array_struct": r"\bmalloc_int_array_struct\s*\(",
        "malloc_int_array": r"\bmalloc_int_array\s*\(",
        "malloc_char_array": r"\bmalloc_char_array\s*\(",
        "strlen": r"\bstrlen\s*\(",
        "strchr": r"\bstrchr\s*\(",
        "free_int_array": r"\bfree_int_array\s*\(",
        "free_char_array": r"\bfree_char_array\s*\(",
        "sort_int_array": r"\bsort_int_array\s*\(",
        "sort_char_array": r"\bsort_char_array\s*\(",
        "copy_char_array": r"\bcopy_char_array\s*\(",
    }
    for name, pattern in checks.items():
        if re.search(pattern, search_code):
            specs.add(name)
    if re.search(r"^\s*int\s+abs\s*\(\s*int\s+x\s*\)", search_code, flags=re.M):
        specs.add("abs")
    return [name for name in ORDER if name in specs]


def build_section(spec_names: list[str]) -> str:
    if not spec_names:
        return ""
    body = "\n\n".join(SPEC_TEXT[name] for name in spec_names)
    return (
        "## Stub Function Specifications\n\n"
        "Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.\n\n"
        f"{body}\n\n"
    )


def process_file(path: Path) -> bool:
    original = path.read_text()
    text = remove_existing_section(original)
    parts = first_c_block(text)
    if parts is None:
        return False
    before_code, code, after_code = parts
    code, external_specs = transform_external_calls(code)
    spec_names = detect_specs(code, external_specs)
    section = build_section(spec_names)
    before_code = normalize_reference_spacing(before_code)
    if section and "## Reference Implementation\n" in before_code:
        before_code = before_code.replace("## Reference Implementation\n", section + "## Reference Implementation\n", 1)
    new_text = before_code + code + after_code
    if new_text != original:
        path.write_text(new_text)
        return True
    return False


def main() -> int:
    changed = 0
    for path in sorted(RAW_HUMANEVAL.glob("*.md")):
        if process_file(path):
            changed += 1
    print(f"updated {changed} HumanEval raw files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
