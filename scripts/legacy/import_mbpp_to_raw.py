#!/usr/bin/env python3
"""Import a C-friendly MBPP validation subset into raw/mbpp.

The importer uses two MBPP sources:

* Google Research full mbpp.jsonl: prompt, Python reference implementation, tests.
* datasets/mbpp-typed/*.py: function name and type signature, but body is pass.

This script joins them by task id and translates the Python reference
implementation for the C raw format used by this repository. The common
scalar/list-of-int subset is translated mechanically; validation tasks outside
that subset use explicit manual C translations. By default, it only considers
the official MBPP validation task id range 511..600. Unsupported or missing
problems are recorded in an import report instead of emitting placeholder C.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import subprocess
import tempfile
import textwrap
import urllib.request
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

import mbpp_validation_manual


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MULTIPLE = (
    Path("/home/yangfp/CAV/OS/CAV/.tools/benchmark_sources/MultiPL-E/datasets")
)
DEFAULT_JSONL = DEFAULT_MULTIPLE / "mbpp.jsonl"
DEFAULT_JSONL_URL = (
    "https://raw.githubusercontent.com/google-research/google-research/master/mbpp/mbpp.jsonl"
)
DEFAULT_TYPED = DEFAULT_MULTIPLE / "mbpp-typed"
DEFAULT_OUT = ROOT / "raw" / "mbpp"
DEFAULT_TASK_ID_MIN = 511
DEFAULT_TASK_ID_MAX = 600

EXCLUDED_VALIDATION_TASKS = {
    512: "multi-function source: flatten + count_element_freq; nested tuple helper is a separate exposed top-level function",
    520: "multi-function source: find_lcm + get_lcm; gcd/lcm helper logic is exposed as a separate top-level function",
    541: "multi-function source: get_sum + check_abundant",
    545: "multi-function source: take_L_and_F_set_bits + toggle_F_and_L_bits",
    550: "overlaps HumanEval p035_max_element: maximum element of an integer array",
    557: "overlaps HumanEval p027_filp_case: toggle character case in a string",
    567: "overlaps HumanEval p126_is_sorted: sorted-list predicate",
    580: "multi-function source: even_ele + extract_even; nested tuple traversal helper is a separate exposed top-level function",
    592: "multi-function source: binomial_Coeff + sum_Of_product",
    599: "overlaps HumanEval p060_sum_to_n: sum of first n natural numbers is a primary returned component",
}

C_KEYWORDS = {
    "auto",
    "break",
    "case",
    "char",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extern",
    "float",
    "for",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "register",
    "restrict",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "struct",
    "switch",
    "typedef",
    "union",
    "unsigned",
    "void",
    "volatile",
    "while",
}


class Unsupported(Exception):
    """Raised when a Python construct has no conservative C translation here."""


@dataclass(frozen=True)
class Arg:
    name: str
    annotation: str


@dataclass(frozen=True)
class TypedProblem:
    task_id: int
    path: Path
    function_name: str
    args: tuple[Arg, ...]
    returns: str


def c_name(name: str) -> str:
    if name in C_KEYWORDS:
        return f"{name}_var"
    return name


def unparse(node: ast.AST | None) -> str:
    if node is None:
        return ""
    return ast.unparse(node)


def supported_annotation(annotation: str, *, is_return: bool) -> bool:
    if annotation in {"int", "bool", "float"}:
        return True
    if not is_return and annotation == "List[int]":
        return True
    return False


def annotation_to_c(annotation: str, *, is_return: bool) -> str:
    if annotation in {"int", "bool"}:
        return "int"
    if annotation == "float":
        return "double"
    if not is_return and annotation == "List[int]":
        return "int_array"
    raise Unsupported(f"unsupported type annotation: {annotation}")


class FunctionTranslator:
    def __init__(
        self,
        name: str,
        args: tuple[Arg, ...],
        returns: str,
        helper_names: set[str],
        *,
        helper_defaults_to_int: bool = False,
        name_overrides: dict[str, str] | None = None,
    ) -> None:
        self.name = name
        self.args = args
        self.returns = returns
        self.helper_names = helper_names | {name}
        self.helper_defaults_to_int = helper_defaults_to_int
        self.name_overrides = name_overrides or {}
        self.declared: set[str] = set()
        self.list_sizes: dict[str, str] = {}
        self.var_types: dict[str, str] = {}
        self.needs_math = False
        self.external_calls: set[str] = set()
        self.needs_pow = False
        self.needs_abs = False
        self.needs_max = False
        self.needs_min = False
        self._loop_counter = 0

    def c_return_type(self) -> str:
        if self.helper_defaults_to_int:
            return "int"
        return annotation_to_c(self.returns, is_return=True)

    def c_params(self) -> list[str]:
        out: list[str] = []
        for arg in self.args:
            if self.helper_defaults_to_int:
                out.append(f"int {c_name(arg.name)}")
                self.declared.add(arg.name)
                self.var_types[arg.name] = "int"
                continue
            c_type = annotation_to_c(arg.annotation, is_return=False)
            if c_type == "int_array":
                out.append(f"int *{c_name(arg.name)}")
                size_name = f"{arg.name}_size"
                out.append(f"int {c_name(size_name)}")
                self.list_sizes[arg.name] = size_name
                self.declared.add(arg.name)
                self.declared.add(size_name)
                self.var_types[arg.name] = "int_array"
                self.var_types[size_name] = "int"
            else:
                out.append(f"{c_type} {c_name(arg.name)}")
                self.declared.add(arg.name)
                self.var_types[arg.name] = c_type
        return out

    def translate(self, node: ast.FunctionDef) -> tuple[str, set[str]]:
        params = ", ".join(self.c_params())
        function_name = self.name_overrides.get(self.name, self.name)
        lines = [f"{self.c_return_type()} {c_name(function_name)}({params}) {{"]
        for stmt in node.body:
            if (
                isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)
                and isinstance(stmt.value.value, str)
            ):
                continue
            lines.extend(self.stmt(stmt, 1))
        lines.append("}")
        needs = set()
        needs |= {f"external:{name}" for name in self.external_calls}
        if self.needs_pow:
            needs.add("pow")
        if self.needs_abs:
            needs.add("abs")
        if self.needs_max:
            needs.add("max")
        if self.needs_min:
            needs.add("min")
        return "\n".join(lines), needs

    def indent(self, level: int, line: str) -> str:
        return "    " * level + line

    def stmt_block(self, stmts: list[ast.stmt], level: int) -> list[str]:
        if not stmts:
            return [self.indent(level, "")]
        out: list[str] = []
        for stmt in stmts:
            out.extend(self.stmt(stmt, level))
        return out

    def stmt(self, node: ast.stmt, level: int) -> list[str]:
        if isinstance(node, ast.Assign):
            if len(node.targets) != 1:
                raise Unsupported("multi-target assignment")
            return self.assign(node.targets[0], node.value, level)
        if isinstance(node, ast.AnnAssign):
            if node.value is None:
                raise Unsupported("annotation without value")
            return self.assign(node.target, node.value, level)
        if isinstance(node, ast.AugAssign):
            return [self.indent(level, f"{self.target(node.target)} {self.augop(node.op)}= {self.expr(node.value)};")]
        if isinstance(node, ast.If):
            cond = self.expr(node.test)
            out = [self.indent(level, f"if ({cond}) {{")]
            out.extend(self.stmt_block(node.body, level + 1))
            if node.orelse:
                out.append(self.indent(level, "} else {"))
                out.extend(self.stmt_block(node.orelse, level + 1))
            out.append(self.indent(level, "}"))
            return out
        if isinstance(node, ast.While):
            cond = self.expr(node.test)
            out = [self.indent(level, f"while ({cond}) {{")]
            out.extend(self.stmt_block(node.body, level + 1))
            out.append(self.indent(level, "}"))
            return out
        if isinstance(node, ast.For):
            return self.for_stmt(node, level)
        if isinstance(node, ast.Return):
            if node.value is None:
                raise Unsupported("bare return")
            return [self.indent(level, f"return {self.expr(node.value)};")]
        if isinstance(node, ast.Break):
            return [self.indent(level, "break;")]
        if isinstance(node, ast.Continue):
            return [self.indent(level, "continue;")]
        if isinstance(node, ast.Pass):
            return []
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            return [self.indent(level, f"{self.expr(node.value)};")]
        raise Unsupported(f"unsupported statement: {node.__class__.__name__}")

    def assign(self, target: ast.expr, value: ast.expr, level: int) -> list[str]:
        if isinstance(target, ast.Name):
            rhs = self.expr(value)
            name = target.id
            if name in self.declared:
                return [self.indent(level, f"{c_name(name)} = {rhs};")]
            typ = self.infer_expr_type(value)
            self.declared.add(name)
            self.var_types[name] = typ
            return [self.indent(level, f"{typ} {c_name(name)} = {rhs};")]
        if isinstance(target, ast.Subscript):
            return [self.indent(level, f"{self.target(target)} = {self.expr(value)};")]
        raise Unsupported(f"unsupported assignment target: {target.__class__.__name__}")

    def for_stmt(self, node: ast.For, level: int) -> list[str]:
        if not isinstance(node.target, ast.Name):
            raise Unsupported("non-name for-loop target")
        target = node.target.id
        if isinstance(node.iter, ast.Call) and self.call_name(node.iter.func) == "range":
            start, stop, step = self.range_parts(node.iter)
            if target not in self.declared:
                decl = [self.indent(level, f"int {c_name(target)};")]
                self.declared.add(target)
                self.var_types[target] = "int"
            else:
                decl = []
            step_text = self.expr(step)
            step_const = self.constant_int(step)
            if step_const is not None and step_const < 0:
                cond = f"{c_name(target)} > {self.expr(stop)}"
            else:
                cond = f"{c_name(target)} < {self.expr(stop)}"
            update = self.loop_update(c_name(target), step)
            out = decl + [self.indent(level, f"for ({c_name(target)} = {self.expr(start)}; {cond}; {update}) {{")]
            out.extend(self.stmt_block(node.body, level + 1))
            out.append(self.indent(level, "}"))
            return out
        if isinstance(node.iter, ast.Name) and node.iter.id in self.list_sizes:
            arr = node.iter.id
            idx = f"__mbpp_i{self._loop_counter}"
            self._loop_counter += 1
            decl: list[str] = []
            if target not in self.declared:
                decl.append(self.indent(level, f"int {c_name(target)};"))
                self.declared.add(target)
                self.var_types[target] = "int"
            out = decl + [
                self.indent(level, f"for (int {idx} = 0; {idx} < {c_name(self.list_sizes[arr])}; {idx}++) {{"),
                self.indent(level + 1, f"{c_name(target)} = {c_name(arr)}[{idx}];"),
            ]
            out.extend(self.stmt_block(node.body, level + 1))
            out.append(self.indent(level, "}"))
            return out
        raise Unsupported("unsupported for-loop iterator")

    def range_parts(self, node: ast.Call) -> tuple[ast.expr, ast.expr, ast.expr]:
        if node.keywords:
            raise Unsupported("range keyword arguments")
        if len(node.args) == 1:
            return ast.Constant(0), node.args[0], ast.Constant(1)
        if len(node.args) == 2:
            return node.args[0], node.args[1], ast.Constant(1)
        if len(node.args) == 3:
            return node.args[0], node.args[1], node.args[2]
        raise Unsupported("range arity")

    def loop_update(self, name: str, step: ast.expr) -> str:
        step_const = self.constant_int(step)
        if step_const == 1:
            return f"{name}++"
        if step_const == -1:
            return f"{name}--"
        if step_const is not None and step_const > 0:
            return f"{name} += {step_const}"
        if step_const is not None and step_const < 0:
            return f"{name} -= {-step_const}"
        return f"{name} += {self.expr(step)}"

    def target(self, node: ast.expr) -> str:
        if isinstance(node, ast.Name):
            return c_name(node.id)
        if isinstance(node, ast.Subscript):
            if not isinstance(node.value, ast.Name):
                raise Unsupported("non-name subscript base")
            return f"{c_name(node.value.id)}[{self.expr(node.slice)}]"
        raise Unsupported(f"unsupported target expression: {node.__class__.__name__}")

    def expr(self, node: ast.expr) -> str:
        if isinstance(node, ast.Constant):
            value = node.value
            if isinstance(value, bool):
                return "1" if value else "0"
            if isinstance(value, (int, float)):
                return repr(value)
            raise Unsupported(f"unsupported constant: {value!r}")
        if isinstance(node, ast.Name):
            return c_name(node.id)
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                return self.pow_expr(node.left, node.right)
            return f"({self.expr(node.left)} {self.binop(node.op)} {self.expr(node.right)})"
        if isinstance(node, ast.UnaryOp):
            return f"({self.unaryop(node.op)}{self.expr(node.operand)})"
        if isinstance(node, ast.BoolOp):
            sep = " && " if isinstance(node.op, ast.And) else " || "
            return "(" + sep.join(self.expr(v) for v in node.values) + ")"
        if isinstance(node, ast.Compare):
            return self.compare_expr(node)
        if isinstance(node, ast.Call):
            return self.call_expr(node)
        if isinstance(node, ast.Subscript):
            if not isinstance(node.value, ast.Name):
                raise Unsupported("non-name subscript base")
            return f"{c_name(node.value.id)}[{self.expr(node.slice)}]"
        raise Unsupported(f"unsupported expression: {node.__class__.__name__}")

    def pow_expr(self, left: ast.expr, right: ast.expr) -> str:
        exp = self.constant_int(right)
        if exp == 0:
            return "1"
        if exp == 1:
            return self.expr(left)
        if exp is not None and 2 <= exp <= 4:
            base = self.expr(left)
            return "(" + " * ".join(base for _ in range(exp)) + ")"
        self.needs_pow = True
        return f"__mbpp_pow_int({self.expr(left)}, {self.expr(right)})"

    def compare_expr(self, node: ast.Compare) -> str:
        parts: list[str] = []
        left = node.left
        for op, right in zip(node.ops, node.comparators):
            parts.append(f"({self.expr(left)} {self.cmpop(op)} {self.expr(right)})")
            left = right
        if len(parts) == 1:
            return parts[0]
        return "(" + " && ".join(parts) + ")"

    def call_expr(self, node: ast.Call) -> str:
        name = self.call_name(node.func)
        if node.keywords:
            raise Unsupported("keyword call arguments")
        if name == "len":
            if len(node.args) != 1 or not isinstance(node.args[0], ast.Name):
                raise Unsupported("unsupported len argument")
            arg = node.args[0].id
            if arg not in self.list_sizes:
                raise Unsupported("len of non-array value")
            return c_name(self.list_sizes[arg])
        if name == "int":
            if len(node.args) != 1:
                raise Unsupported("int arity")
            sqrt_arg = self.sqrt_call_arg(node.args[0])
            if sqrt_arg is not None:
                self.external_calls.add("isqrt")
                return f"mbpp_external_isqrt({self.expr(sqrt_arg)})"
            return f"((int)({self.expr(node.args[0])}))"
        if name == "abs":
            if len(node.args) != 1:
                raise Unsupported("abs arity")
            self.needs_abs = True
            return f"__mbpp_abs_int({self.expr(node.args[0])})"
        if name == "max":
            if len(node.args) != 2:
                raise Unsupported("max arity")
            self.needs_max = True
            return f"__mbpp_max_int({self.expr(node.args[0])}, {self.expr(node.args[1])})"
        if name == "min":
            if len(node.args) != 2:
                raise Unsupported("min arity")
            self.needs_min = True
            return f"__mbpp_min_int({self.expr(node.args[0])}, {self.expr(node.args[1])})"
        if name in {"math.sqrt", "sqrt"}:
            if len(node.args) != 1:
                raise Unsupported("sqrt arity")
            self.external_calls.add("sqrt")
            return f"mbpp_external_sqrt({self.expr(node.args[0])})"
        if name in {"math.floor", "floor"}:
            if len(node.args) != 1:
                raise Unsupported("floor arity")
            sqrt_arg = self.sqrt_call_arg(node.args[0])
            if sqrt_arg is not None:
                self.external_calls.add("isqrt")
                return f"mbpp_external_isqrt({self.expr(sqrt_arg)})"
            self.external_calls.add("floor")
            return f"mbpp_external_floor({self.expr(node.args[0])})"
        if name in {"math.ceil", "ceil"}:
            if len(node.args) != 1:
                raise Unsupported("ceil arity")
            self.external_calls.add("ceil")
            return f"mbpp_external_ceil({self.expr(node.args[0])})"
        if name in {"round", "math.round"}:
            if len(node.args) != 1:
                raise Unsupported("round arity")
            self.external_calls.add("round")
            return f"mbpp_external_round({self.expr(node.args[0])})"
        if name in self.helper_names:
            function_name = self.name_overrides.get(name, name)
            return f"{c_name(function_name)}(" + ", ".join(self.expr(arg) for arg in node.args) + ")"
        raise Unsupported(f"unsupported call: {name}")

    def sqrt_call_arg(self, node: ast.expr) -> ast.expr | None:
        if not isinstance(node, ast.Call):
            return None
        try:
            name = self.call_name(node.func)
        except Unsupported:
            return None
        if name not in {"math.sqrt", "sqrt"} or len(node.args) != 1 or node.keywords:
            return None
        return node.args[0]

    def call_name(self, node: ast.expr) -> str:
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            return f"{node.value.id}.{node.attr}"
        raise Unsupported("unsupported callee")

    def infer_expr_type(self, node: ast.expr) -> str:
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            return "double"
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Div):
                return "double"
            left = self.infer_expr_type(node.left)
            right = self.infer_expr_type(node.right)
            if "double" in {left, right}:
                return "double"
        if isinstance(node, ast.Call):
            name = self.call_name(node.func)
            if name in {"math.floor", "floor", "math.ceil", "ceil", "round", "math.round"}:
                return "int"
            if name in {"math.sqrt", "sqrt"}:
                return "double"
        return "int"

    def constant_int(self, node: ast.expr) -> int | None:
        if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
            return int(node.value)
        if (
            isinstance(node, ast.UnaryOp)
            and isinstance(node.op, ast.USub)
            and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, int)
        ):
            return -int(node.operand.value)
        return None

    def binop(self, op: ast.operator) -> str:
        if isinstance(op, ast.Add):
            return "+"
        if isinstance(op, ast.Sub):
            return "-"
        if isinstance(op, ast.Mult):
            return "*"
        if isinstance(op, (ast.Div, ast.FloorDiv)):
            return "/"
        if isinstance(op, ast.Mod):
            return "%"
        if isinstance(op, ast.BitAnd):
            return "&"
        if isinstance(op, ast.BitOr):
            return "|"
        if isinstance(op, ast.BitXor):
            return "^"
        if isinstance(op, ast.LShift):
            return "<<"
        if isinstance(op, ast.RShift):
            return ">>"
        raise Unsupported(f"unsupported binary operator: {op.__class__.__name__}")

    def augop(self, op: ast.operator) -> str:
        return self.binop(op)

    def unaryop(self, op: ast.unaryop) -> str:
        if isinstance(op, ast.Not):
            return "!"
        if isinstance(op, ast.USub):
            return "-"
        if isinstance(op, ast.UAdd):
            return "+"
        if isinstance(op, ast.Invert):
            return "~"
        raise Unsupported(f"unsupported unary operator: {op.__class__.__name__}")

    def cmpop(self, op: ast.cmpop) -> str:
        if isinstance(op, ast.Eq):
            return "=="
        if isinstance(op, ast.NotEq):
            return "!="
        if isinstance(op, ast.Lt):
            return "<"
        if isinstance(op, ast.LtE):
            return "<="
        if isinstance(op, ast.Gt):
            return ">"
        if isinstance(op, ast.GtE):
            return ">="
        raise Unsupported(f"unsupported comparison operator: {op.__class__.__name__}")


def helper_text(needs: set[str]) -> str:
    out: list[str] = []
    external_prototypes = {
        "isqrt": "int mbpp_external_isqrt(int x);",
        "sqrt": "double mbpp_external_sqrt(double x);",
        "floor": "int mbpp_external_floor(double x);",
        "ceil": "int mbpp_external_ceil(double x);",
        "round": "int mbpp_external_round(double x);",
    }
    for name in ("isqrt", "sqrt", "floor", "ceil", "round"):
        if f"external:{name}" in needs:
            out.append(external_prototypes[name])
    if "abs" in needs:
        out.append(
            textwrap.dedent(
                """
                static int __mbpp_abs_int(int x) {
                    if (x < 0) {
                        return -x;
                    }
                    return x;
                }
                """
            ).strip()
        )
    if "max" in needs:
        out.append(
            textwrap.dedent(
                """
                static int __mbpp_max_int(int a, int b) {
                    if (a > b) {
                        return a;
                    }
                    return b;
                }
                """
            ).strip()
        )
    if "min" in needs:
        out.append(
            textwrap.dedent(
                """
                static int __mbpp_min_int(int a, int b) {
                    if (a < b) {
                        return a;
                    }
                    return b;
                }
                """
            ).strip()
        )
    if "pow" in needs:
        out.append(
            textwrap.dedent(
                """
                static int __mbpp_pow_int(int base, int exp) {
                    int result = 1;
                    while (exp > 0) {
                        result = result * base;
                        exp = exp - 1;
                    }
                    return result;
                }
                """
            ).strip()
        )
    return "\n\n".join(out)


def parse_typed(path: Path) -> TypedProblem:
    match = re.match(r"mbpp_(\d+)_", path.name)
    if not match:
        raise ValueError(f"bad MBPP typed filename: {path}")
    mod = ast.parse(path.read_text())
    func = next(
        (node for node in mod.body if isinstance(node, ast.FunctionDef) and node.name != "check"),
        None,
    )
    if func is None:
        raise ValueError(f"no target function in {path}")
    args = tuple(Arg(arg.arg, unparse(arg.annotation)) for arg in func.args.args)
    returns = unparse(func.returns)
    return TypedProblem(int(match.group(1)), path, func.name, args, returns)


def infer_literal_annotation(node: ast.AST) -> str:
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            return "bool"
        if isinstance(node.value, int):
            return "int"
        if isinstance(node.value, float):
            return "float"
        if isinstance(node.value, str):
            return "str"
        if node.value is None:
            return "None"
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return infer_literal_annotation(node.operand)
    if isinstance(node, ast.List):
        types = {infer_literal_annotation(item) for item in node.elts}
        if types <= {"int"}:
            return "List[int]"
        if types <= {"int", "float"}:
            return "List[float]"
        if types <= {"str"}:
            return "List[str]"
        return "List[Any]"
    if isinstance(node, ast.Tuple):
        types = [infer_literal_annotation(item) for item in node.elts]
        return "Tuple[" + ", ".join(types) + "]"
    if isinstance(node, ast.Dict):
        return "Dict[Any, Any]"
    if isinstance(node, ast.Set):
        return "Set[Any]"
    return "Any"


def parse_assert_signature(test: str) -> tuple[str, list[str], str]:
    module = ast.parse(test)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.Assert):
        raise Unsupported("unsupported test statement")
    expr = module.body[0].test
    if not isinstance(expr, ast.Compare) or not expr.comparators:
        raise Unsupported("unsupported test expression")
    call = expr.left
    if not isinstance(call, ast.Call) or not isinstance(call.func, ast.Name):
        raise Unsupported("unsupported candidate call in test")
    return (
        call.func.id,
        [infer_literal_annotation(arg) for arg in call.args],
        infer_literal_annotation(expr.comparators[0]),
    )


def merge_test_annotations(annotations: list[str], *, is_return: bool) -> str:
    types = set(annotations)
    if types <= {"int"}:
        return "int"
    if types <= {"bool"}:
        return "bool"
    if types <= {"int", "float"}:
        return "float"
    if not is_return and types <= {"List[int]"}:
        return "List[int]"
    raise Unsupported("unsupported inferred type: " + " | ".join(sorted(types)))


def problem_stub(task_id: int, item: dict | None, reason_name: str = "unknown") -> TypedProblem:
    function_name = reason_name
    if item is not None:
        try:
            defs = find_function_defs(ast.parse(item["code"]))
            if defs:
                function_name = defs[-1].name
        except (KeyError, SyntaxError):
            pass
    return TypedProblem(task_id, Path("<mbpp.jsonl>"), function_name, tuple(), "int")


def infer_problem_from_item(item: dict) -> TypedProblem:
    task_id = int(item["task_id"])
    parsed_tests = [parse_assert_signature(test) for test in item["test_list"]]
    names = {name for name, _, _ in parsed_tests}
    if len(names) != 1:
        raise Unsupported("inconsistent candidate names in tests")
    function_name = next(iter(names))
    arities = {len(args) for _, args, _ in parsed_tests}
    if len(arities) != 1:
        raise Unsupported("inconsistent candidate arities in tests")

    module = ast.parse(item["code"])
    defs = find_function_defs(module)
    fn = next((node for node in defs if node.name == function_name), None)
    if fn is None:
        raise Unsupported("target function missing from Python code")
    arity = next(iter(arities))
    if len(fn.args.args) != arity:
        raise Unsupported(
            f"code/test arity mismatch: code has {len(fn.args.args)}, tests have {arity}"
        )

    args: list[Arg] = []
    for index, arg in enumerate(fn.args.args):
        annotation = merge_test_annotations(
            [test_args[index] for _, test_args, _ in parsed_tests],
            is_return=False,
        )
        if not supported_annotation(annotation, is_return=False):
            raise Unsupported(f"unsupported inferred parameter type: {annotation}")
        args.append(Arg(arg.arg, annotation))
    returns = merge_test_annotations([ret for _, _, ret in parsed_tests], is_return=True)
    if not supported_annotation(returns, is_return=True):
        raise Unsupported(f"unsupported inferred return type: {returns}")
    return TypedProblem(task_id, Path("<mbpp.jsonl>"), function_name, tuple(args), returns)


def find_function_defs(module: ast.Module) -> list[ast.FunctionDef]:
    return [node for node in module.body if isinstance(node, ast.FunctionDef)]


def translate_problem(problem: TypedProblem, code: str) -> str:
    for arg in problem.args:
        if not supported_annotation(arg.annotation, is_return=False):
            raise Unsupported(f"unsupported parameter type: {arg.annotation}")
    if not supported_annotation(problem.returns, is_return=True):
        raise Unsupported(f"unsupported return type: {problem.returns}")

    module = ast.parse(code)
    defs = find_function_defs(module)
    if not any(fn.name == problem.function_name for fn in defs):
        raise Unsupported("target function missing from Python code")

    helper_names = {fn.name for fn in defs}
    translated: list[str] = []
    needs: set[str] = set()
    c_entry = f"mbpp_{problem.task_id}_{problem.function_name}"
    name_overrides = {problem.function_name: c_entry}
    for fn in defs:
        if fn.name == problem.function_name:
            tr = FunctionTranslator(
                fn.name,
                problem.args,
                problem.returns,
                helper_names,
                name_overrides=name_overrides,
            )
        else:
            helper_args = tuple(Arg(arg.arg, "int") for arg in fn.args.args)
            tr = FunctionTranslator(
                fn.name,
                helper_args,
                "int",
                helper_names,
                helper_defaults_to_int=True,
                name_overrides=name_overrides,
            )
        c_func, fn_needs = tr.translate(fn)
        translated.append(c_func)
        needs |= fn_needs

    helpers = helper_text(needs)
    return "\n\n".join(part for part in [helpers, *translated] if part).strip() + "\n"


def check_c_syntax(code: str) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "mbpp_check.c"
        path.write_text(code + "\nint main(void) { return 0; }\n")
        proc = subprocess.run(
            ["gcc", "-std=c99", "-fsyntax-only", "-Wall", str(path)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    if proc.returncode == 0:
        return True, ""
    detail = "\n".join((proc.stdout + proc.stderr).splitlines()[:6])
    return False, detail


def external_calls_from_c(code: str) -> list[str]:
    found = set(re.findall(r"\bmbpp_external_(isqrt|sqrt|floor|ceil|round|atan2)\s*\(", code))
    return [name for name in ("isqrt", "sqrt", "floor", "ceil", "round", "atan2") if name in found]


def external_stub_section(code: str) -> str:
    calls = external_calls_from_c(code)
    if not calls:
        return ""
    signatures = {
        "isqrt": "`int mbpp_external_isqrt(int x);`",
        "sqrt": "`double mbpp_external_sqrt(double x);`",
        "floor": "`int mbpp_external_floor(double x);`",
        "ceil": "`int mbpp_external_ceil(double x);`",
        "round": "`int mbpp_external_round(double x);`",
        "atan2": "`double mbpp_external_atan2(double y, double x);`",
    }
    bullets = "\n".join(f"- {signatures[name]}" for name in calls)
    specs: list[str] = []
    if "isqrt" in calls:
        specs.append(
            textwrap.dedent(
                """
                ### `mbpp_external_isqrt`

                Coq model:

                ```coq
                Definition mbpp_isqrt_spec (x r : Z) : Prop :=
                  0 <= x /\\ 0 <= r /\\ r * r <= x /\\ x < (r + 1) * (r + 1).
                ```

                Function contract shape:

                ```c
                int mbpp_external_isqrt(int x)
                /*@ Require 0 <= x && x < INT_MAX
                    Ensure mbpp_isqrt_spec(x, __return)
                */;
                ```
                """
            ).strip()
        )
    if "sqrt" in calls:
        specs.append(
            textwrap.dedent(
                """
                ### `mbpp_external_sqrt`

                Coq model: define a pure relation/function for the mathematical square root required by this task. The relation must at least state that the result is nonnegative and its square equals the input in the chosen numeric model.

                Function contract shape:

                ```c
                double mbpp_external_sqrt(double x)
                /*@ Require x >= 0
                    Ensure mbpp_sqrt_spec(x, __return)
                */;
                ```
                """
            ).strip()
        )
    if any(name in calls for name in ("floor", "ceil", "round")):
        specs.append(
            textwrap.dedent(
                """
                ### Rounding stubs

                Coq model: define the corresponding integer rounding relation for every rounding stub used here. For floor, the returned integer `r` should satisfy `r <= x < r + 1` in the chosen numeric model; define analogous relations for ceil/round if they appear.

                Function contract shape:

                ```c
                int mbpp_external_floor(double x)
                /*@ Require emp
                    Ensure mbpp_floor_spec(x, __return)
                */;
                ```
                """
            ).strip()
        )
    if "atan2" in calls:
        specs.append(
            textwrap.dedent(
                """
                ### `mbpp_external_atan2`

                Coq model: define the polar angle relation for the chosen real-number model.

                Function contract shape:

                ```c
                double mbpp_external_atan2(double y, double x)
                /*@ Require emp
                    Ensure mbpp_atan2_spec(y, x, __return)
                */;
                ```
                """
            ).strip()
        )
    spec_text = "\n\n".join(specs)
    if spec_text:
        spec_text += "\n\n"
    return (
        "## Stub Function Specifications\n\n"
        "The C reference intentionally uses external stubs instead of libc/math.h:\n\n"
        f"{bullets}\n\n"
        "Contract-stage requirements:\n\n"
        "- Keep these as explicit C stub declarations or stub functions; do not replace them with libc calls.\n"
        "- Give every stub a function contract in `mid/<dataset>/<name>.c` before verifying the caller.\n"
        "- Implement the mathematical meaning in the companion `mid/<dataset>/<name>.v` with definition-only Coq definitions/relations, then expose them with `Extern Coq` / `Import Coq` annotations from the C file.\n"
        "- Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for the external semantics.\n"
        "\n"
        f"{spec_text}"
    )


def markdown(
    problem: TypedProblem,
    item: dict,
    c_code: str,
    *,
    source_name: str,
    translation_note: str,
) -> str:
    title = problem.function_name.replace("_", " ").title()
    args = ", ".join(f"{a.name}: {a.annotation}" for a in problem.args)
    tests = "\n".join(f"- `{test}`" for test in item["test_list"])
    external_section = external_stub_section(c_code)
    prompt = item.get("prompt") or item.get("text") or ""
    return (
        f"# MBPP {problem.task_id} {title}\n\n"
        "## Problem\n\n"
        f"{prompt.strip()}\n\n"
        "## Signature\n\n"
        f"- Python: `{problem.function_name}({args}) -> {problem.returns}`\n"
        f"- C entrypoint: `mbpp_{problem.task_id}_{problem.function_name}`\n"
        "- C translation: scalar Python `int`/`bool` values use C `int`, "
        "`float` uses `double`, `List[int]` parameters are represented as "
        "`int *name, int name_size`, and non-scalar Python containers use "
        "the explicit structs shown in the C code.\n\n"
        "## Tests\n\n"
        f"{tests}\n\n"
        "## Source\n\n"
        f"- Source: {source_name}.\n"
        f"- Task id: {problem.task_id}.\n"
        f"- Translation note: {translation_note}\n\n"
        f"{external_section}"
        "## Original Python Implementation\n\n"
        f"```python\n{item['code'].rstrip()}\n```\n\n"
        "## Reference Implementation\n\n"
        f"```c\n{c_code.rstrip()}\n```\n"
    )


def read_task_source(path: Path, url: str) -> tuple[str, str]:
    if path.exists():
        return path.read_text(), f"Google Research full MBPP source from `{path}`"
    with urllib.request.urlopen(url, timeout=30) as response:
        text = response.read().decode("utf-8")
    return text, f"Google Research full MBPP source from `{url}`"


def load_tasks_by_id(path: Path, url: str) -> tuple[dict[int, dict], str]:
    text, source_name = read_task_source(path, url)
    stripped = text.lstrip()
    if stripped.startswith("["):
        data = json.loads(text)
    else:
        data = [json.loads(line) for line in text.splitlines() if line.strip()]
    return {int(item["task_id"]): item for item in data}, source_name


def write_report(
    out_dir: Path,
    imported: list[TypedProblem],
    skipped: list[tuple[TypedProblem, str]],
    excluded: list[tuple[int, str]],
    *,
    task_id_min: int | None,
    task_id_max: int | None,
    source_typed_count: int,
    source_task_count: int,
    source_name: str,
    selected_typed_count: int,
    selected_source_count: int,
    missing_typed_ids: list[int],
    missing_source_ids: list[int],
) -> None:
    def reason_key(reason: str) -> str:
        for prefix in ("inferred: ", "typed: "):
            if reason.startswith(prefix):
                reason = reason[len(prefix) :]
                break
        return reason.split(":", 1)[0]

    reasons = Counter(reason_key(reason) for _, reason in skipped)
    selected_count = 0
    if task_id_min is not None and task_id_max is not None:
        selected_count = task_id_max - task_id_min + 1
    lines = [
        "# MBPP Import Report",
        "",
        "## Selection",
        "",
        (
            f"- Task id range: {task_id_min}-{task_id_max} "
            f"({selected_count} ids)"
            if task_id_min is not None and task_id_max is not None
            else "- Task id range: all typed tasks"
        ),
        f"- Source typed tasks: {source_typed_count}",
        f"- Source MBPP tasks: {source_task_count}",
        f"- Source: {source_name}",
        f"- Selected typed tasks present locally before exclusion: {selected_typed_count}",
        f"- Selected MBPP source tasks present before exclusion: {selected_source_count}",
        "",
        "## Results",
        "",
        f"- Imported: {len(imported)}",
        f"- Excluded: {len(excluded)}",
        f"- Skipped: {len(skipped)}",
        "",
        "## Missing Source Tasks",
        "",
        "- Missing from local typed source: "
        + (", ".join(str(task_id) for task_id in missing_typed_ids) if missing_typed_ids else "none"),
        "- Missing from MBPP source: "
        + (", ".join(str(task_id) for task_id in missing_source_ids) if missing_source_ids else "none"),
        "",
    ]
    if excluded:
        lines.extend(["## Excluded Problems", ""])
        for task_id, reason in excluded:
            lines.append(f"- `mbpp_{task_id}`: {reason}")
        lines.append("")
    lines.extend(["## Skipped Reason Counts", ""])
    for reason, count in reasons.most_common():
        lines.append(f"- `{reason}`: {count}")
    lines.extend(["", "## Skipped Problems", ""])
    for problem, reason in skipped:
        lines.append(f"- `mbpp_{problem.task_id}_{problem.function_name}`: {reason}")
    (out_dir / "_import_report.md").write_text("\n".join(lines) + "\n")


def clean_output(out_dir: Path) -> None:
    if not out_dir.exists():
        return
    for path in out_dir.glob("mbpp_*.md"):
        path.unlink()
    report = out_dir / "_import_report.md"
    if report.exists():
        report.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--jsonl",
        type=Path,
        default=DEFAULT_JSONL,
        help="Full MBPP JSONL path. If missing, the official Google Research URL is used.",
    )
    parser.add_argument("--jsonl-url", default=DEFAULT_JSONL_URL)
    parser.add_argument("--typed-dir", type=Path, default=DEFAULT_TYPED)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--task-id-min",
        type=int,
        default=DEFAULT_TASK_ID_MIN,
        help="Minimum MBPP task id to import. Defaults to the official validation split start.",
    )
    parser.add_argument(
        "--task-id-max",
        type=int,
        default=DEFAULT_TASK_ID_MAX,
        help="Maximum MBPP task id to import. Defaults to the official validation split end.",
    )
    parser.add_argument("--clean", action="store_true", help="Remove previous generated raw/mbpp files first.")
    args = parser.parse_args()
    if args.task_id_min > args.task_id_max:
        parser.error("--task-id-min must be <= --task-id-max")

    if args.clean:
        clean_output(args.out_dir)
    args.out_dir.mkdir(parents=True, exist_ok=True)

    json_by_id, source_name = load_tasks_by_id(args.jsonl, args.jsonl_url)
    typed_all = [parse_typed(path) for path in sorted(args.typed_dir.glob("mbpp_*.py"))]
    selected_ids = set(range(args.task_id_min, args.task_id_max + 1))
    typed = [problem for problem in typed_all if problem.task_id in selected_ids]
    typed_by_id = {problem.task_id: problem for problem in typed_all}
    typed_ids = {problem.task_id for problem in typed_all}
    json_ids = set(json_by_id)
    missing_typed_ids = sorted(selected_ids - typed_ids)
    missing_source_ids = sorted(selected_ids - json_ids)

    imported: list[TypedProblem] = []
    skipped: list[tuple[TypedProblem, str]] = []
    excluded = [
        (task_id, EXCLUDED_VALIDATION_TASKS[task_id])
        for task_id in sorted(selected_ids & set(EXCLUDED_VALIDATION_TASKS))
    ]
    for task_id in sorted(selected_ids):
        if task_id in EXCLUDED_VALIDATION_TASKS:
            continue
        item = json_by_id.get(task_id)
        if item is None:
            skipped.append((typed_by_id.get(task_id) or problem_stub(task_id, item), "missing MBPP source item"))
            continue

        manual = mbpp_validation_manual.manual_translation(task_id)
        if manual is not None:
            manual_args = tuple(Arg(str(name), str(annotation)) for name, annotation in manual["args"])
            problem = TypedProblem(
                task_id,
                Path("<manual>"),
                str(manual["function_name"]),
                manual_args,
                str(manual["returns"]),
            )
            c_code = str(manual["code"])
            ok, detail = check_c_syntax(c_code)
            if not ok:
                skipped.append((problem, "manual C syntax check failed: " + detail.replace("\n", " ")))
                continue
            name = f"mbpp_{problem.task_id}_{problem.function_name}.md"
            (args.out_dir / name).write_text(
                markdown(
                    problem,
                    item,
                    c_code,
                    source_name=source_name,
                    translation_note=(
                        "Manual C reference translation for the official validation "
                        "task; Python containers and library values are represented "
                        "with explicit C structs."
                    ),
                )
            )
            imported.append(problem)
            continue

        candidates: list[tuple[str, TypedProblem]] = []
        infer_error: str | None = None
        try:
            candidates.append(("inferred", infer_problem_from_item(item)))
        except (SyntaxError, Unsupported) as exc:
            infer_error = str(exc).replace("\n", " ")
        typed_problem = typed_by_id.get(task_id)
        if typed_problem is not None and all(problem.task_id != task_id for _, problem in candidates):
            candidates.append(("typed", typed_problem))
        if not candidates:
            skipped.append((problem_stub(task_id, item), infer_error or "missing typed signature"))
            continue

        failure_reasons: list[str] = []
        for label, problem in candidates:
            try:
                c_code = translate_problem(problem, item["code"])
                ok, detail = check_c_syntax(c_code)
                if not ok:
                    raise Unsupported("C syntax check failed: " + detail)
            except (SyntaxError, Unsupported) as exc:
                failure_reasons.append(f"{label}: {str(exc).replace(chr(10), ' ')}")
                continue
            name = f"mbpp_{problem.task_id}_{problem.function_name}.md"
            if label == "inferred":
                translation_note = (
                    "C reference generated from the official Python implementation "
                    "using a signature inferred from official tests."
                )
            else:
                translation_note = (
                    "C reference generated from the official Python implementation "
                    "using the local typed MBPP signature."
                )
            (args.out_dir / name).write_text(
                markdown(
                    problem,
                    item,
                    c_code,
                    source_name=source_name,
                    translation_note=translation_note,
                )
            )
            imported.append(problem)
            break
        else:
            skipped.append((candidates[0][1], "; ".join(failure_reasons)))

    write_report(
        args.out_dir,
        imported,
        skipped,
        excluded,
        task_id_min=args.task_id_min,
        task_id_max=args.task_id_max,
        source_typed_count=len(typed_all),
        source_task_count=len(json_by_id),
        source_name=source_name,
        selected_typed_count=len(typed),
        selected_source_count=len(selected_ids & json_ids),
        missing_typed_ids=missing_typed_ids,
        missing_source_ids=missing_source_ids,
    )
    print(f"imported {len(imported)} MBPP raw files into {args.out_dir}")
    print(
        f"selected MBPP task ids {args.task_id_min}-{args.task_id_max}; "
        f"typed present {len(typed)}/{len(selected_ids)}, "
        f"source present {len(selected_ids & json_ids)}/{len(selected_ids)}"
    )
    print(
        f"excluded {len(excluded)} overlapping or multi-function MBPP files; "
        f"skipped {len(skipped)} unsupported MBPP files; see {args.out_dir / '_import_report.md'}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
