# lean-cauchy-kernel

## 当前目标
在 REPL 中对 30 个十进制元素的列表执行 quicksort 符号归约 (`:nf`)。

## 当前状态

- `Decimal.lean` / `bench_decimal.lean` 可正常加载（111 个声明）。
- 小列表（3 个 `Nat` 元素）`:nf` 可完全归约，输出正确排序结果。
- 10 个 `Nat` 元素 `:nf` 可完全归约，输出正确。
- 30 个 `Decimal` 元素 `:nf` 在本机可完成，但输出极大（因 quicksort 实现将等于 pivot 的元素同时放入左右子列表，导致重复）。
- 自动生成的 recursor（`mk_recursor_rhs`）经单元测试验证正确，无 BVar 索引 bug。

## 已修复的 Bug

### 1. REPL `:def` 命令解析 `:=` 失败
**根因**：`handle_def` 中先判断 `rest_after_name.starts_with(':')`，而 `:=` 也以 `:` 开头，导致被误判为带类型注解的形式，随后 `splitn(2, "=")` 找不到 `=` 而报错。
**修复**：先判断 `starts_with(":=")`，再判断 `starts_with(':')`。

### 2. REPL `fun` 无类型注解时生成非法常量 `?`
**根因**：`repl_parser.rs` 的 `parse_fun` 在参数无 `: type` 注解时，用 `ParsedExpr::Const("?".to_string())` 作为类型占位符，随后 `to_expr` 将其转为 `Const(Name(["?"]), [])`，类型检查时报错 `Constant not found`。
**状态**：待修复。临时 workaround：始终为 `fun` 参数写类型注解，如 `fun x : Nat => x`。

## 待办

- [ ] 修复 `parse_fun` 中缺失类型注解的处理（应生成 metavariable 或尝试推断）。
- [ ] 评估 30 元素 quicksort 在更低内存设备上是否仍可能 OOM（输出表达式因重复而膨胀）。
- [ ] 优化 `nf` 或考虑添加带深度限制的归约模式。

## 测试记录

```bash
# 3 元素 Nat 列表
cargo run --bin lean-cauchy-kernel -- repl
:load tiny_decimal.lean
:nf quicksort Nat nat_le input_list
# => cons(Nat, succ(zero), cons(Nat, succ(succ(zero)), cons(Nat, succ(succ(succ(zero))), nil(Nat))))

# 30 元素 Decimal 列表
cargo run --bin lean-cauchy-kernel -- repl
:load bench_decimal.lean
:nf quicksort Decimal dec_le input_list
# => 可完成，输出含大量重复元素的长 cons 链
```
