# lean-cauchy-kernel

一个基于 Rust 实现的 Lean 4 风格依赖类型论内核，支持归纳类型、自动 recursor 生成、类型检查、弱头归约/完全归约、轻量级 tactic 引擎和交互式 REPL。

## 项目结构

### Rust 内核源码 (`src/`)

| 文件 | 职责 |
|------|------|
| `main.rs` | CLI 入口。子命令：`lean-check`（内核演示）、`repl`（交互式 REPL）、`check-files <file>...`（批量检查 .lean 文件）、`tui <target> [deps...]`（交互式目标查看器）。 |
| `lib.rs` | 库入口，导出所有公共模块。 |
| `expr.rs` | 表达式 AST：BVar（de Bruijn 索引）、FVar（自由变量）、MVar（元变量）、Const、App、Lambda、Pi、Let 等。提供 `instantiate`、`lift_loose_bvars`、`abstract_fvar` 等 de Bruijn 运算。 |
| `declaration.rs` | 声明类型：Axiom、Definition、Theorem、Inductive、Quot，以及对应的 Value 结构（ConstantVal、InductiveVal、RecursorVal、ConstructorVal 等）。 |
| `environment.rs` | 全局环境 `Environment`，存储所有常量声明；支持归纳类型的自动 recursor / constructor 注册、嵌套归纳类型的辅助类型生成、universe level 参数管理。 |
| `local_ctx.rs` | 局部上下文 `LocalCtx`，管理局部声明（CDecl/LDecl），提供 BVar 与 FVar 的互相转换、基于局部上下文的类型推断辅助。 |
| `type_checker.rs` | 类型检查器：类型推断 `infer`、类型检查 `check`、弱头归约 `whnf`、完全归约 `nf`、定义等价 `is_def_eq`。支持 universe level 约束、let-binding 归约、元变量（MVar）的分配与延迟替换。 |
| `tactic.rs` | 轻量级 tactic 引擎 `TacticEngine`，当前支持的 tactic：`intro`（引入变量）、`exact`（精确证明项）、`apply`（应用函数）、`rw [h1, ←h2]`（链式/反向重写）、`rfl`（自反性）、`assumption`（从假设求解）、`induction`（归纳）、`have`（局部 let 绑定）。 |
| `repl.rs` | 交互式 REPL，支持 `:load`、`:def`、`:theorem`、`:inductive`、`:infer`、`:reduce`、`:nf`、`:defeq`、`:solve` 等命令；处理 `import` 和 `section`/`end` 作用域。 |
| `repl_parser.rs` | Lean 风格语法解析器。支持表达式（lambda、pi、let、have、match、calc、forall、exists、中缀运算符）和顶层声明（def/theorem/inductive/structure/mutual/variable/notation/infix/section/import）。 |
| `tui.rs` | 基于 `crossterm` 的交互式 TUI，用于查看当前证明目标、局部上下文和可用假设。 |
| `test_auto_rec.rs` | 自动 recursor 生成的单元测试。 |

### Lean 标准库/示例 (`lib/`)

| 文件 | 内容 |
|------|------|
| `Nat.lean` | 自然数归纳定义（zero/succ）及中缀 `+` 映射到 `nat_add`。 |
| `Eq.lean` | 相等类型 `Eq A a b` 及其公理：`refl`、`eq_sym`、`eq_trans`、`eq_subst`。 |
| `Order.lean` | `le`（小于等于）及其基本引理：`le_zero`、`le_succ`、`le_refl`、`le_trans`。 |
| `True.lean` | `True` 类型（命题中的 unit）。 |
| `Int.lean` | 整数定义（`ofNat`/`negSucc`）及四则运算、recursor。 |
| `IntOrder.lean` | 整数序关系。 |
| `Frac.lean` | 分数定义（`mk n d`）及四则运算、绝对值、倒数。 |
| `FracArith.lean` | 分数算术引理：整数/分数的交换律、自减为零、零小于正分数、柯西序列距离引理等。 |
| `NatProof.lean` | 自然数算术引理：`nat_add_comm`、`nat_mul_comm`、`nat_add_assoc` 等。 |
| `Real.lean` | 实数定义为柯西序列的商类型。 |
| `Cauchy.lean` | 柯西序列定义。 |
| `Complete.lean` | 完备性证明框架。 |
| `Algebra.lean` | 代数结构示例。 |
| `Exists.lean` | `Exists` 类型。 |
| `WellFounded.lean` | 良基递归相关定义。 |
| `QuadraticFormula.lean` / `QuadraticChain.lean` | 一元二次方程求根公式及其证明链。 |
| `Decimal.lean` | 十进制数定义及 quicksort 实现（用于性能测试）。 |
| `Derivation.lean` | 推导示例。 |
| `MetaVarDemo.lean` | 元变量（MVar）使用演示。 |
| `Tests.lean` | 测试集合。 |
| `Proof.lean` | 证明示例。 |

### 测试/基准文件

| 文件 | 用途 |
|------|------|
| `test.lean` | 基础 REPL 加载测试。 |
| `test_rw.lean` / `test_rw2.lean` | `rw` tactic 的链式/反向重写测试。 |
| `test_notation.lean` | 自定义 notation 测试。 |
| `tiny_decimal.lean` / `bench_decimal.lean` | 3 元素 / 30 元素 quicksort 基准测试。 |

## 构建与运行

```bash
# 构建
cargo build --release

# 运行内核演示（类型检查、WHNF、归约、定义等价）
cargo run --bin lean-cauchy-kernel -- lean-check

# 启动交互式 REPL
cargo run --bin lean-cauchy-kernel -- repl

# 批量检查 .lean 文件
cargo run --bin lean-cauchy-kernel -- check-files lib/Nat.lean lib/Eq.lean lib/NatProof.lean

# 启动 TUI 查看器
cargo run --bin lean-cauchy-kernel -- tui lib/Decimal.lean lib/Nat.lean lib/Order.lean
```

## REPL 常用命令

```
:load <file.lean>              加载 .lean 文件（支持 import）
:def <name> : <ty> := <val>    添加定义
:theorem <name> : <ty> := <pf> 添加定理（支持 by tactic 块）
:inductive <name> | <c>:<t>    添加归纳类型
:infer <expr>                  推断表达式类型
:reduce <expr>                 弱头归约 (WHNF)
:nf <expr>                     完全归约
:defeq <e1> = <e2>             检查定义等价
:solve <name> : <ty> := <expr> 允许元变量的求解模式
:env                           查看当前环境
:help                          显示帮助
:quit                          退出
```

## Tactic 语法示例

```lean
theorem test_rw_chain : forall (a b c d : Nat), Eq Nat a b -> Eq Nat b c -> Eq Nat c d -> Eq Nat a d := by
  intro a b c d h1 h2 h3
  rw [h1, h2, h3]
  rfl

theorem test_rw_rev : forall (a b : Nat), Eq Nat a b -> Eq Nat b a := by
  intro a b h
  rw [←h]
  rfl
```
